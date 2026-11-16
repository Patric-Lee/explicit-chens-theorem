import fs from 'node:fs';import path from 'node:path';import zlib from 'node:zlib';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
import {prepareAssembly,batchPlan,kinds,title,sha} from './AssemblyPlan.mjs';
import {atomicJson,acquireRangeLock} from './CertificateSections.mjs';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..'),repo=path.resolve(root,'../..');
const args=process.argv.slice(2),command=args.shift()??'help',options={};
while(args.length){const key=args.shift();if(!key.startsWith('--')||!args.length)throw Error('Use --option value');
 const values=[args.shift()];if(key==='--sections')while(args.length&&!args[0].startsWith('--'))values.push(args.shift());options[key.slice(2)]=values.join(',');}
const allowed=new Set(['kind','section','sections','chunks','jobs','memory-mb']);
for(const k of Object.keys(options))if(!allowed.has(k))throw Error('Unknown option --'+k);
const integer=(k,f,min=1,max=Number.MAX_SAFE_INTEGER)=>{const n=Number(options[k]??f);if(!Number.isSafeInteger(n)||n<min||n>max)throw Error('Invalid --'+k);return n;};
if(command==='help'){
 console.log(`AssemblyChunks prepare|status|run [--kind prefix|totals|grid] [--section 1..8 | --sections 1,2,...,8]
Options: --chunks N (unfinished BATCH attempts per section; omit to finish)
         --jobs N (simultaneous sections; default 4, grid default 8), --memory-mb 2048
prepare builds shared proposals once; it does not certify them. run kernel-checks leaves.
Failures are recorded and later batches continue. Resume retries gaps and reuses checked leaves.
The full cumulative tree/window join and final Chen axiom replacement remain separate.`);process.exit(0);
}
if(!['prepare','status','run'].includes(command))throw Error('Unknown command');
if(command==='prepare'){
 const manifest=prepareAssembly(repo);console.log(JSON.stringify({prepared:true,counts:manifest.counts,points:manifest.points,cells:manifest.cells,files:manifest.files.length}));process.exit(0);
}
const kind=options.kind??'prefix';if(!kinds.includes(kind))throw Error('Invalid --kind');
const memory=integer('memory-mb',2048,512),jobs=integer('jobs',kind==='grid'?8:4,1,8);
if(options.sections!==undefined){
 if(options.section!==undefined)throw Error('Use either --section or --sections');
 const sections=options.sections.split(',').map(Number);
 if(!sections.length||new Set(sections).size!==sections.length||sections.some(s=>!Number.isInteger(s)||s<1||s>8))throw Error('Use distinct sections 1..8');
 const childArgs=[command,...Object.entries(options).filter(([k])=>!['sections','jobs'].includes(k)).flatMap(([k,v])=>['--'+k,v])];
 let next=0;const exits=[];
 await Promise.all(Array.from({length:Math.min(jobs,sections.length)},async()=>{
  while(next<sections.length){const s=sections[next++];
   const code=await new Promise((resolve,reject)=>{const p=spawn(process.execPath,[fileURLToPath(import.meta.url),...childArgs,'--section',String(s)],{cwd:repo,windowsHide:true,stdio:'inherit'});p.on('error',reject);p.on('close',c=>resolve(c??1));});
   exits.push(code);
  }
 }));process.exitCode=exits.some(c=>c!==0)?1:0;
}else{
const dataDir=path.join(root,'PlattAssemblyData'),manifest=JSON.parse(fs.readFileSync(path.join(dataDir,'manifest.json')));
const configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
if(manifest.schema!==1||manifest.configurationHash!==configurationHash)throw Error('Assembly proposals/configuration changed; rerun prepare with workers stopped');
const manifestHash=sha(fs.readFileSync(path.join(dataDir,'manifest.json')));
const section=options.section===undefined?null:integer('section',null,1,8);
const total=kind==='grid'?manifest.cells:manifest.counts;
const stageDir=path.join(repo,'.lake/build-434/assembly-certificates',title(kind));
const name=i=>'B'+String(i).padStart(6,'0');
function status(s){const plan=batchPlan(kind,s,total),dir=path.join(stageDir,'S'+s);
 const receipts=new Set(fs.existsSync(dir)?fs.readdirSync(dir).filter(n=>/^B\d+\.json$/.test(n)):[]);
 const fdir=path.join(dir,'failures'),failed=fs.existsSync(fdir)?fs.readdirSync(fdir).filter(n=>/^B\d+\.json$/.test(n)).map(n=>JSON.parse(fs.readFileSync(path.join(fdir,n)))).filter(r=>r.status==='FAILED'):[];
 const bad=new Set(failed.map(f=>f.index));let next=0;while(next<plan.length&&receipts.has(name(next)+'.json')&&!bad.has(next))next++;
 return {section:s,totalBatches:plan.length,batchSizes:[...new Set(plan.map(p=>p.end-p.start))],recordedSuccessfulBatches:plan.filter(p=>receipts.has(name(p.index)+'.json')&&!bad.has(p.index)).length,
  nextPendingBatch:next<plan.length?next:null,unresolvedFailedBatches:[...bad]};
}
if(command==='status'){console.log(JSON.stringify({kind,sections:(section===null?Array.from({length:8},(_,i)=>i+1):[section]).map(status),note:'Receipts are historical; run validates source/object/dependency hashes. No final-window completeness claim.'},null,2));process.exit(0);}
if(section===null)throw Error('run requires --section or --sections');
const plan=batchPlan(kind,section,total),limit=integer('chunks',plan.length);
const entry=manifest.files.find(f=>f.kind===kind&&f.section===section);
if(!entry)throw Error('Stage proposals missing; rerun prepare with workers stopped');
const bytes=fs.readFileSync(path.join(dataDir,entry.file));if(sha(bytes)!==entry.hash)throw Error('Assembly data hash mismatch');
const payload=JSON.parse(zlib.gunzipSync(bytes));
const records=payload.records.map((r,i)=>({...r,index:kind==='grid'?payload.start+i:r.index}));
const receipts=path.join(stageDir,'S'+section),failures=path.join(receipts,'failures');fs.mkdirSync(receipts,{recursive:true});
const lock=acquireRangeLock(path.join(stageDir,'locks'),section-1,section);
const tag='assembly'+kind+'section'+String.fromCharCode(96+section),logDir=path.join(repo,'.lake/build-434/source-build-logs');
const object=m=>path.join(repo,'.lake/build-434/lib/lean',m.replaceAll('.','/'))+'.olean';
const roots=[repo,path.join(repo,'OpenAI/wrappers'),path.join(repo,'OpenAI/grouped'),path.join(repo,'OpenAI'),root,path.join(root,'Calr3')];
const objectCache=new Map(),freshCache=new Map();let ledgers;
const objectHash=m=>{if(!objectCache.has(m))objectCache.set(m,sha(fs.readFileSync(object(m))));return objectCache.get(m);};
function fresh(m){if(freshCache.has(m))return freshCache.get(m);
 if(!ledgers)ledgers=fs.readdirSync(logDir).filter(n=>/^ledger(?:-[a-z]+)?\.json$/.test(n)).map(n=>JSON.parse(fs.readFileSync(path.join(logDir,n))));
 const src=roots.map(r=>path.join(r,m.replaceAll('.','/')+'.lean')).find(f=>fs.existsSync(f));if(!src)return false;
 const sourceHash=sha(fs.readFileSync(src));
 const ok=ledgers.some(l=>{const r=l[m];return r&&r.configurationHash===configurationHash&&r.sourceHash===sourceHash&&r.objectHash===objectHash(m)&&Object.entries(r.dependencies).every(([d,h])=>objectHash(d)===h&&fresh(d));});
 freshCache.set(m,ok);return ok;
}
let attempted=0,reused=0,succeeded=0;const failed=[];
try{
 const {generateBatch}=await import('./AssemblyPlan.mjs');
 for(const p of plan){
  if(attempted>=limit)break;
  const generated=generateBatch(kind,section,p,records,manifest),m=generated.module;
  const src=path.join(root,m.replaceAll('.','/')+'.lean'),receiptFile=path.join(receipts,name(p.index)+'.json'),failureFile=path.join(failures,name(p.index)+'.json');
  const sourceHash=sha(generated.source);
  function resolveFailure(){if(fs.existsSync(failureFile)){const f=JSON.parse(fs.readFileSync(failureFile));if(f.status==='FAILED')atomicJson(failureFile,{...f,status:'RESOLVED',resolvedAt:new Date().toISOString()});}}
  let reusable=false;
  if(fs.existsSync(receiptFile))try{const r=JSON.parse(fs.readFileSync(receiptFile));reusable=r.classification==='LEAN_KERNEL_CHECKED_ASSEMBLY_LEAF_NOT_FINAL_WINDOW'&&r.kind===kind&&r.section===section&&r.index===p.index&&r.manifestHash===manifestHash&&r.sourceHash===sourceHash&&
   sha(fs.readFileSync(src))===sourceHash&&r.checked.sourceHash===sourceHash&&r.checked.configurationHash===configurationHash&&r.checked.objectHash===objectHash(m)&&Object.entries(r.checked.dependencies).every(([d,h])=>objectHash(d)===h&&fresh(d));}catch{}
  if(reusable){resolveFailure();reused++;continue;}
  attempted++;let step='generate';
  try{
   fs.mkdirSync(path.dirname(src),{recursive:true});if(!fs.existsSync(src)||fs.readFileSync(src,'utf8')!==generated.source)fs.writeFileSync(src,generated.source);
   console.log(JSON.stringify({assemblyBatch:m,kind,section,index:p.index,...generated.metadata}));step='build-or-ledger';
   const exit=await new Promise((resolve,reject)=>{
    const child=spawn(process.execPath,[path.join(repo,'OpenAI/tools/build-source.mjs'),m],{cwd:repo,windowsHide:true,stdio:'inherit',env:{...process.env,CHEN_REPO:repo,CHEN_BUILD_TAG:tag,CHEN_BUILD_JOBS:'1',CHEN_LEAN_THREADS:'1',CHEN_LEAN_MEMORY_MB:String(memory),CHEN_BUILD_CACHE_ONLY_DEPS:'1',CHEN_BUILD_COMPACT_LEDGER:'1',CHEN_BUILD_LEASE_FILE:lock.file}});
    lock.setChild(child.pid??null);child.on('error',reject);child.on('close',code=>{lock.setChild(null);resolve(code);});
   });
   if(exit!==0)throw Error('Leaf build or ledger save failed');step='verify-and-save-receipt';
   const checked=JSON.parse(fs.readFileSync(path.join(logDir,'ledger-'+tag+'.json')))[m];
   if(!checked||checked.sourceHash!==sourceHash||checked.configurationHash!==configurationHash||checked.objectHash!==sha(fs.readFileSync(object(m))))throw Error('Current checked object missing');
   atomicJson(receiptFile,{classification:'LEAN_KERNEL_CHECKED_ASSEMBLY_LEAF_NOT_FINAL_WINDOW',kind,section,index:p.index,module:m,manifestHash,sourceHash,metadata:generated.metadata,checkedAt:new Date().toISOString(),checked});
   objectCache.delete(m);resolveFailure();succeeded++;
   console.log(JSON.stringify({assemblyChecked:m,seconds:checked.seconds}));
  }catch(error){fs.mkdirSync(failures,{recursive:true});const old=fs.existsSync(failureFile)?JSON.parse(fs.readFileSync(failureFile)):{};
   atomicJson(failureFile,{kind,section,index:p.index,module:m,status:'FAILED',attempts:(old.attempts??0)+1,failedAt:new Date().toISOString(),step,error:error.message,log:path.join(logDir,m+'.log')});failed.push(p.index);
   console.error(JSON.stringify({assemblyFailed:m,continuing:true,error:error.message}));
  }
 }
 console.log(JSON.stringify({assemblyFinished:true,kind,section,attempted,reused,succeeded,failedBatches:failed,successful:failed.length===0}));if(failed.length)process.exitCode=1;
}finally{lock.release();}
}
