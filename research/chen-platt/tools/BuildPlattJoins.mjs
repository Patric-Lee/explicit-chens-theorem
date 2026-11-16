// Ordinary Lean kernel builds against already checked certificate boundaries.
// This does not regenerate or re-evaluate the completed sieve certificates.
import fs from 'node:fs';import path from 'node:path';import os from 'node:os';import crypto from 'node:crypto';
import {spawn,spawnSync} from 'node:child_process';import {pathToFileURL} from 'node:url';
const repo=process.argv[2],targets=process.argv.slice(3),root=path.join(repo,'research/chen-platt'),base=path.join(repo,'.lake/build-434'),build=path.join(base,'lib/lean'),logs=path.join(base,'source-build-logs');
const {atomicJson}=await import(pathToFileURL(path.join(repo,'OpenAI/tools/atomic-json.mjs')).href);
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const tag=process.env.CHEN_BUILD_TAG||'joins',ledgerFile=path.join(logs,'ledger-'+tag+'.json');
let ledger=fs.existsSync(ledgerFile)?JSON.parse(fs.readFileSync(ledgerFile)):{};
const allRecords=new Map();
for(const f of fs.readdirSync(logs).filter(x=>/^ledger(?:-[a-z]+)?\.json$/.test(x))){
 for(const [m,r]of Object.entries(JSON.parse(fs.readFileSync(path.join(logs,f))))){
  if((!m.startsWith('Platt')&&m!=='TernaryGoldbach.Statement')||m.startsWith('PlattCertificates.')||m.startsWith('PlattAssembly.'))continue;
  if(!allRecords.has(m))allRecords.set(m,[]);allRecords.get(m).push(r);
 }
 global.gc?.();
}
const object=m=>path.join(build,m.replaceAll('.','/'))+'.olean';
const sourceRoots=[root,path.join(root,'Calr3')];
const source=m=>{const rel=m.replaceAll('.','/')+'.lean',r=sourceRoots.find(r=>fs.existsSync(path.join(r,rel)));if(!r)throw Error('Missing local source '+m);return path.join(r,rel);};
const boundaries=new Map(),boundaryRecords=new Map(),graph=new Map();
function boundary(m){
 if(boundaries.has(m))return boundaries.get(m);
 const file=source(m),sourceHash=sha(fs.readFileSync(file)),objectHash=sha(fs.readFileSync(object(m)));
 let ok=false,record;
 const match=m.match(/^PlattAssembly\.(Prefix|Totals|Grid)\.S(\d)\.(B\d+)$/);
 const manual=m.match(/^PlattCertificates\.(Log256|Count131072)\.(C\d+)$/);
 if(match){const receipt=JSON.parse(fs.readFileSync(path.join(base,'assembly-certificates',match[1],'S'+match[2],match[3]+'.json'))),r=receipt.checked;record=r;ok=receipt.sourceHash===sourceHash&&r.configurationHash===configurationHash&&r.sourceHash===sourceHash&&r.objectHash===objectHash;}
 else if(manual){const receipt=JSON.parse(fs.readFileSync(path.join(base,'manual-certificates',manual[1],manual[2]+'.json'))),r=receipt.checked;record=r;ok=receipt.sourceHash===sourceHash&&r.configurationHash===configurationHash&&r.sourceHash===sourceHash&&r.objectHash===objectHash;}
 else {const matches=[ledger[m],...(allRecords.get(m)||[])].filter(r=>r?.configurationHash===configurationHash&&r.sourceHash===sourceHash&&r.objectHash===objectHash);record=matches.find(r=>r.buildSignature)||matches[0];ok=!!record;}
 if(!ok)throw Error('Unchecked/mismatched parent boundary '+m);
 boundaries.set(m,objectHash);boundaryRecords.set(m,record);return objectHash;
}
function visit(m){
 if(graph.has(m))return;
 const file=source(m),s=fs.readFileSync(file,'utf8');
 const imports=[...s.matchAll(/^import ([^\r\n]+)/gm)].map(x=>x[1].trim());
 const v={name:m,file,sourceHash:sha(s),imports,status:'pending'};graph.set(m,v);
 for(const p of imports){if(p.startsWith('PlattPointPackets.')||p.startsWith('PlattGlobalGrid.')||p.startsWith('PlattPointCovers.')||p.startsWith('PlattPointTransports.')||targets.includes(p))visit(p);else boundary(p);}
}
targets.forEach(visit);
const bin=path.join(os.homedir(),'.elan/toolchains/leanprover--lean4---v4.34.1/bin');
const envResult=spawnSync(path.join(bin,'lake.exe'),['env',process.execPath,'-p','process.env.LEAN_PATH'],{cwd:repo,encoding:'utf8',windowsHide:true});
if(envResult.status!==0)throw Error(envResult.stderr||envResult.stdout);
const env={...process.env,LEAN_PATH:build+path.delimiter+envResult.stdout.trim(),LEAN_NUM_THREADS:'1'};
let running=0,complete=0,cached=0,failed=false;
const jobs=Number(process.env.CHEN_BUILD_JOBS||4);
const state=()=>({roots:targets,total:graph.size,complete,cached,running,failed,remaining:graph.size-complete-cached-running,at:new Date().toISOString()});
const save=()=>{atomicJson(ledgerFile,ledger);atomicJson(path.join(logs,'status-'+tag+'.json'),state());};
const deps=v=>Object.fromEntries(v.imports.map(m=>[m,graph.has(m)?ledger[m]?.objectHash:boundaries.get(m)]));
const recordSignature=r=>r?.buildSignature||sha(JSON.stringify({configurationHash:r?.configurationHash,sourceHash:r?.sourceHash,objectHash:r?.objectHash,dependencies:r?.dependencies}));
const parentRecord=m=>graph.has(m)?ledger[m]:boundaryRecords.get(m);
const depSignatures=v=>Object.fromEntries(v.imports.map(m=>[m,recordSignature(parentRecord(m))]));
function pump(){
 for(const v of graph.values()){
  if(failed||running>=jobs)break;
  if(v.status!=='pending'||v.imports.some(m=>graph.has(m)&&graph.get(m).status!=='done'))continue;
  const big=/\.L[12]B/.test(v.name)||v.name==='PlattGlobalPointCover'||v.name.startsWith('PlattPointTransports.');
  if(big&&running)continue;
  const dependencies=deps(v),dependencySignatures=depSignatures(v),hasFreshDependency=v.imports.some(m=>parentRecord(m)?.buildSignature);
  const candidates=[ledger[v.name],...(allRecords.get(v.name)||[])].filter(r=>r?.configurationHash===configurationHash&&r.sourceHash===v.sourceHash&&JSON.stringify(r.dependencies)===JSON.stringify(dependencies)&&
   (r.dependencySignatures?JSON.stringify(r.dependencySignatures)===JSON.stringify(dependencySignatures):!hasFreshDependency));
  if(candidates.length&&fs.existsSync(object(v.name))){const actual=sha(fs.readFileSync(object(v.name))),r=candidates.find(r=>r.objectHash===actual);if(r){ledger[v.name]=r;v.status='done';cached++;continue;}}
  v.status='running';running++;fs.mkdirSync(path.dirname(object(v.name)),{recursive:true});
  const logfile=path.join(logs,v.name+'.log'),fd=fs.openSync(logfile,'w'),start=Date.now();
  const p=spawn(path.join(bin,'lean.exe'),['-j1','-M'+(big?8192:(process.env.CHEN_LEAN_MEMORY_MB||3072)),'-DmaxHeartbeats=3000000','-DmaxRecDepth=100000','-R',root,'-o',object(v.name),v.file],{cwd:repo,windowsHide:true,env,stdio:['ignore',fd,fd]});
  p.on('error',e=>fs.appendFileSync(logfile,String(e)));
  p.on('close',code=>{fs.closeSync(fd);running--;const log=fs.readFileSync(logfile,'utf8');
   if(code!==0||/sorryAx|declaration uses `sorry`/.test(log)){v.status='failed';failed=true;console.log(JSON.stringify({failed:v.name,code,tail:log.slice(-7000)}));}
   else{v.status='done';complete++;const objectHash=sha(fs.readFileSync(object(v.name))),buildSignature=sha(JSON.stringify({configurationHash,sourceHash:v.sourceHash,objectHash,dependencySignatures}));ledger[v.name]={configurationHash,sourceHash:v.sourceHash,objectHash,dependencies,dependencySignatures,buildSignature,seconds:(Date.now()-start)/1000};console.log(JSON.stringify({verified:v.name,seconds:ledger[v.name].seconds,complete,cached,total:graph.size}));}
   save();pump();
  });
  if(big)break;
 }
 save();
 if(!running){const pending=[...graph.values()].some(v=>v.status==='pending');if(failed){process.exitCode=1;return;}if(pending)return pump();console.log(JSON.stringify({success:true,...state()}));}
}
console.log(JSON.stringify({start:true,...state(),boundaries:boundaries.size}));pump();
