// Bounded source build. Proofs are checked by Lean, never by native_decide.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import os from 'node:os';
import {fileURLToPath} from 'node:url';
import {spawn,spawnSync} from 'node:child_process';
import {atomicJson} from './atomic-json.mjs';
const repo=process.env.CHEN_REPO||path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
const bin=path.join(process.env.ELAN_HOME||path.join(os.homedir(),'.elan'),'toolchains','leanprover--lean4---v4.34.1','bin');
const lean=path.join(bin,process.platform==='win32'?'lean.exe':'lean');
const lake=path.join(bin,process.platform==='win32'?'lake.exe':'lake');
const rootNames=process.argv.slice(2);
if(!rootNames.length)throw Error('Supply target module names');
const build=path.join(repo,'.lake/build-434/lib/lean');
const logs=path.join(repo,'.lake/build-434/source-build-logs');
const tag=process.env.CHEN_BUILD_TAG?'-'+process.env.CHEN_BUILD_TAG:'';
const ledgerPath=path.join(logs,'ledger'+tag+'.json');if(process.env.CHEN_GRAPH_ONLY!=='1')fs.mkdirSync(logs,{recursive:true});
const hash=s=>crypto.createHash('sha256').update(s).digest('hex');
const configurationHash=hash(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
// Many campaigns contain the same checked parent records. Retain one copy
// per complete artifact signature, without changing any reuse validation.
const ledger={},candidates=new Map(),canonicalRecords=new Map();
function insertRecord(name,value){
 const signature={...value};delete signature.seconds;
 const key=hash(JSON.stringify(signature));
 if(!canonicalRecords.has(name))canonicalRecords.set(name,new Map());
 const pool=canonicalRecords.get(name);let record=pool.get(key);
 if(!record){
  // Detach retained strings from the large input snapshot as well.
  record=JSON.parse(JSON.stringify(value));pool.set(key,record);
  if(!candidates.has(name))candidates.set(name,[]);candidates.get(name).push(record);
 }
 ledger[name]=record;return record;
}
if(fs.existsSync(logs))for(const file of fs.readdirSync(logs).filter(n=>/^ledger(?:-[a-z]+)?\.json$/.test(n))){
 let snapshot=JSON.parse(fs.readFileSync(path.join(logs,file)));
 for(const [name,value]of Object.entries(snapshot))insertRecord(name,value);
 snapshot=null;global.gc?.();
}
let ownLedger=fs.existsSync(ledgerPath)?JSON.parse(fs.readFileSync(ledgerPath)):{};
for(const name of Object.keys(ownLedger))ownLedger[name]=insertRecord(name,ownLedger[name]);
canonicalRecords.clear();global.gc?.();
if(process.env.CHEN_TRACE_LEDGER_MEMORY==='1')console.log(JSON.stringify({ledgerModules:Object.keys(ledger).length,candidateVersions:[...candidates.values()].reduce((n,rs)=>n+rs.length,0),heapMB:Math.round(process.memoryUsage().heapUsed/1024**2)}));
const searchRoots=[repo,path.join(repo,'OpenAI','wrappers'),path.join(repo,'OpenAI','grouped'),path.join(repo,'OpenAI'),path.join(repo,'research/chen-platt'),path.join(repo,'research/chen-platt/Calr3'),...['chen-effective','chen-dusart','chen-bjs-study','chen-numerical-study'].map(s=>path.join(repo,'research',s))];
const graph=new Map();
function strip(s){let out='',depth=0,line=false,str=false;for(let i=0;i<s.length;i++){const c=s[i],n=s[i+1];if(line){if(c==='\n'){line=false;out+='\n';}continue;}if(depth){if(c==='/'&&n==='-'){depth++;i++;}else if(c==='-'&&n==='/'){depth--;i++;}else if(c==='\n')out+='\n';continue;}if(str){if(c==='\\')i++;else if(c==='"')str=false;else if(c==='\n')out+='\n';continue;}if(c==='-'&&n==='-'){line=true;i++;}else if(c==='/'&&n==='-'){depth=1;i++;}else if(c==='"')str=true;else out+=c;}return out;}
function visit(n){
 if(graph.has(n))return;
 const rel=n.replaceAll('.','/')+'.lean';
 const srcRoot=searchRoots.find(r=>fs.existsSync(path.join(r,rel)));
 if(!srcRoot)return; // external dependency supplied by the pinned Lake environment
 const file=path.join(srcRoot,rel),source=fs.readFileSync(file,'utf8'),code=strip(source);
 const imports=[...code.matchAll(/^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\n\r]+)/gm)].flatMap(m=>m[1].trim().split(/\s+/).map(n=>Buffer.from(n,'utf8').toString('utf8')));
 const obj=path.join(build,n.replaceAll('.','/')+'.olean');
 graph.set(n,{name:n,srcRoot,file,sourceHash:hash(source),imports,obj,status:'pending'});
 imports.forEach(visit);
}
rootNames.forEach(visit);
for(const r of rootNames)if(!graph.has(r))throw Error('Missing root source '+r);
if(process.env.CHEN_GRAPH_ONLY==='1'){
 const counts={};for(const n of graph.keys()){const k=n.split('.')[0];counts[k]=(counts[k]||0)+1;}
 console.log(JSON.stringify({roots:rootNames,total:graph.size,counts,...(process.env.CHEN_GRAPH_MODULES==='1'?{modules:[...graph.keys()]}:{})},null,2));process.exit(0);
}
const envResult=spawnSync(lake,['env','node','-p','process.env.LEAN_PATH'],{cwd:repo,encoding:'utf8',windowsHide:true,maxBuffer:5e6});
if(envResult.status!==0)throw Error(envResult.stderr||envResult.stdout);
const env={...process.env,LEAN_PATH:build+path.delimiter+envResult.stdout.trim(),LEAN_NUM_THREADS:'1'};
let running=0,failed=false,complete=0,cached=0;
const concurrency=Number(process.env.CHEN_BUILD_JOBS||2);
const exclusive=n=>n==='BJSLayerTableChecks'||/(^|\.)Audit/.test(n);
function state(){return {roots:rootNames,total:graph.size,complete,cached,running,failed,remaining:graph.size-complete-cached-running,at:new Date().toISOString()};}
function recordNativePid(pid){
 const file=process.env.CHEN_BUILD_LEASE_FILE;
 if(!file)return;
 const record=JSON.parse(fs.readFileSync(file,'utf8'));
 record.nativePid=pid;atomicJson(file,record);
}
function save(){
 const saved=process.env.CHEN_BUILD_COMPACT_LEDGER==='1'?
  Object.assign(ownLedger,Object.fromEntries([...graph.keys()].filter(n=>ledger[n]).map(n=>[n,ledger[n]]))):ledger;
 atomicJson(ledgerPath,saved);atomicJson(path.join(logs,'status'+tag+'.json'),state());
}
function depHashes(v){return Object.fromEntries(v.imports.filter(n=>graph.has(n)).map(n=>[n,ledger[n]?.objectHash]));}
// Object hashes alone do not invalidate an opaque downstream proof when an
// imported theorem keeps its exported shape but changes its axiom ancestry.
// New checked artifacts therefore retain recursive provenance. Legacy data
// certificates remain reusable until a dependency is freshly checked.
function recordSignature(r){return r?.buildSignature||hash(JSON.stringify({configurationHash:r?.configurationHash,sourceHash:r?.sourceHash,objectHash:r?.objectHash,dependencies:r?.dependencies}));}
function depSignatures(v){return Object.fromEntries(v.imports.filter(n=>graph.has(n)).map(n=>[n,recordSignature(ledger[n])]));}
function ready(v){return v.imports.every(n=>!graph.has(n)||graph.get(n).status==='done');}
function reuse(v){
 const deps=depHashes(v),signatures=depSignatures(v),hasFreshDependency=v.imports.some(n=>graph.has(n)&&ledger[n]?.buildSignature);
 const matches=[ledger[v.name],...(candidates.get(v.name)||[])].filter(r=>r?.configurationHash===configurationHash&&r?.sourceHash===v.sourceHash&&JSON.stringify(deps)===JSON.stringify(r.dependencies)&&
  (r.dependencySignatures?JSON.stringify(signatures)===JSON.stringify(r.dependencySignatures):!hasFreshDependency));
 if(!matches.length||!fs.existsSync(v.obj))return false;
 const actualObjectHash=hash(fs.readFileSync(v.obj)),old=matches.find(r=>r.objectHash===actualObjectHash);
 if(!old)return false;ledger[v.name]=old;v.status='done';cached++;return true;
}
function launch(v){
 if(process.env.CHEN_BUILD_CACHE_ONLY_DEPS==='1'&&!rootNames.includes(v.name)){
  failed=true;v.status='failed';
  console.log(JSON.stringify({failed:v.name,reason:'Shared dependency is not currently cached. Stop section workers and build this dependency once before resuming.'}));
  return;
 }
 v.status='running';running++;
 const deps=depHashes(v),dependencySignatures=depSignatures(v);
 fs.mkdirSync(path.dirname(v.obj),{recursive:true});
 const log=path.join(logs,v.name+'.log'),fd=fs.openSync(log,'w');
 const memory=process.env.CHEN_LEAN_MEMORY_MB||(exclusive(v.name)?'8192':v.name.startsWith('OpenAIGrouped.')?'6144':'4096');
 const args=['-j'+(process.env.CHEN_LEAN_THREADS||'1'),'-M'+memory,'-DmaxErrors=12','-DmaxHeartbeats=3000000','-DmaxRecDepth=4096'];
 if(v.name.startsWith('OAI.')||v.name.startsWith('OpenAIGrouped.'))args.push('-DautoImplicit=false');
 args.push('-R',v.srcRoot,'-o',v.obj,v.file);
 const start=Date.now();
 const p=spawn(lean,args,{cwd:repo,env,stdio:['ignore',fd,fd],windowsHide:true});
 recordNativePid(p.pid??null);
 p.on('error',e=>{fs.appendFileSync(log,'\n'+e.stack);});
 p.on('close',code=>{
  recordNativePid(null);
  fs.closeSync(fd);running--;
  const content=fs.readFileSync(log,'utf8');
  if(code!==0||content.includes('declaration uses `sorry`')||content.includes('sorryAx')){
   failed=true;v.status='failed';console.log(JSON.stringify({failed:v.name,code,log,tail:content.slice(-10000)}));
  }else{
   complete++;v.status='done';const objectHash=hash(fs.readFileSync(v.obj));
   const buildSignature=hash(JSON.stringify({configurationHash,sourceHash:v.sourceHash,objectHash,dependencySignatures}));
   ledger[v.name]={configurationHash,sourceHash:v.sourceHash,objectHash,dependencies:deps,dependencySignatures,buildSignature,seconds:(Date.now()-start)/1000};
   console.log(JSON.stringify({verified:v.name,seconds:ledger[v.name].seconds,completed:complete,cached,total:graph.size}));
  }
  save();pump();
 });
}
function pump(){
 const cacheBefore=cached;
 if(!failed){
  let progress;
  do{progress=false;for(const v of graph.values())if(v.status==='pending'&&ready(v)&&reuse(v))progress=true;}while(progress);
  const tableActive=[...graph.values()].some(v=>exclusive(v.name)&&v.status==='running');
  if(!tableActive)for(const v of graph.values()){
   if(running>=concurrency)break;
   if(v.status==='pending'&&ready(v)){
    if(exclusive(v.name)&&running)continue;
    if(running&&os.freemem()<1.5*1024**3)break;
    launch(v);
    if(exclusive(v.name))break;
   }
  }
 }
 save();
 if(!running){
  if(failed){console.log(JSON.stringify(state()));process.exitCode=1;return;}
  if([...graph.values()].some(v=>v.status!=='done')){
   if(cached>cacheBefore){pump();return;}
   console.log(JSON.stringify({blocked:'dependency cycle or incomplete source resolution',...state()}));process.exitCode=2;return;
  }
  console.log(JSON.stringify({success:true,...state()}));
 }
}
console.log(JSON.stringify({start:true,jobs:concurrency,...state()}));pump();
