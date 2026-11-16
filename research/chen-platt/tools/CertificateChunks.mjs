// Generate/check finite certificates in bounded, restartable chunks.
// JavaScript produces proposals. Lean's kernel establishes each certificate.
import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
import {spawn} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {sectionRange, acquireRangeLock, atomicJson} from './CertificateSections.mjs';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const repo=path.resolve(root,'../..');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const args=process.argv.slice(2),command=args.shift()||'help',options={};
while(args.length){
 const k=args.shift();if(!k.startsWith('--')||!args.length)throw Error('Use --option value');
 const values=[args.shift()];
 if(k==='--sections')while(args.length&&!args[0].startsWith('--'))values.push(args.shift());
 options[k.slice(2)]=values.join(',');
}
const allowed=new Set(['kind','start','chunks','points-per-chunk','integers-per-chunk','memory-mb','section','sections']);
for(const k of Object.keys(options))if(!allowed.has(k))throw Error('Unknown option --'+k);
function integer(k,fallback,min=0){const n=Number(options[k]??fallback);if(!Number.isSafeInteger(n)||n<min)throw Error('Invalid '+k);return n;}
if(command==='help'){
 console.log(`Usage: node research/chen-platt/tools/CertificateChunks.mjs COMMAND [OPTIONS]
Commands: status, prepare, run
Options: --kind logs|counts --start 0 --chunks 1
         --section 1..8 --chunks N (resume up to N unfinished chunks in this section)
         --sections 3,7 (run these sections concurrently; --chunks applies per section)
         --points-per-chunk 256 --integers-per-chunk 131072 --memory-mb 4096
Examples:
  node research/chen-platt/tools/CertificateChunks.mjs status
  node research/chen-platt/tools/CertificateChunks.mjs run --kind logs --start 0 --chunks 1
  node research/chen-platt/tools/CertificateChunks.mjs run --kind counts --start 0 --chunks 1
  node research/chen-platt/tools/CertificateChunks.mjs run --kind counts --section 3 --chunks 100
  node research/chen-platt/tools/CertificateChunks.mjs run --kind counts --sections 3,7 --chunks 100
No full Chen audit is run here. Rerunning the same range uses hash-aware Lean caching.
Chunk failures are recorded and the worker continues. Resume retries gaps;
--chunks counts attempts, and a run with failures returns a nonzero exit code.
Only counts + per-chunk reciprocal arithmetic, or logarithm rows, are certified.
Full grid coverage, global prefix/seam assembly, and final H30 proof remain separate.`);
 process.exit(0);
}
if(!['status','prepare','run'].includes(command))throw Error('Unknown command '+command);
const kind=options.kind||'logs';if(!['logs','counts'].includes(kind))throw Error('Invalid kind');
const memory=integer('memory-mb',4096,512);
const pointsPerChunk=integer('points-per-chunk',256,1);
const integersPerChunk=integer('integers-per-chunk',131072,2);
if(integersPerChunk%2)throw Error('integers-per-chunk must be even');
const rawGrid=fs.readFileSync(path.join(root,'block-relative-1e10.grid.json.gz'));
const data=JSON.parse(zlib.gunzipSync(rawGrid));
const summary=JSON.parse(fs.readFileSync(path.join(root,'block-relative-1e10.json'),'utf8'));
const groups=data.groups;
if(data.U!==4000000||data.R!==10000000000||data.grid[0].x!==data.U||data.grid.at(-1).x!==data.R)
 throw Error('Unexpected finite scan range');
const countPlans=[];
for(let g=0;g<groups.length;g++){
 const group=groups[g],end=groups[g+1]?.offset??summary.blocks,W=2**group.w;
 const cap=Math.floor(integersPerChunk/(2*W));
 if(cap<1)throw Error('Count chunk too small for group width');
 for(let offset=group.offset;offset<end;offset+=cap){
  const B=Math.min(cap,end-offset),lo=group.lo+2*W*(offset-group.offset);
  countPlans.push({offset,w:group.w,W,B,lo,hi:lo+2*W*B-1});
 }
}
const total=kind==='logs'?Math.ceil(data.grid.length/pointsPerChunk):countPlans.length;
const variant=kind==='logs'?'Log'+pointsPerChunk:'Count'+integersPerChunk;
const generated=path.join(root,'PlattCertificates',variant);
const receipts=path.join(repo,'.lake/build-434/manual-certificates',variant);
const failures=path.join(receipts,'failures');
const failureFile=index=>path.join(failures,'C'+String(index).padStart(6,'0')+'.json');
function failureRecords(){
 if(!fs.existsSync(failures))return [];
 return fs.readdirSync(failures).filter(n=>/^C\d+\.json$/.test(n))
  .map(n=>JSON.parse(fs.readFileSync(path.join(failures,n),'utf8')))
  .filter(r=>r.status==='FAILED');
}
function resolveFailure(index){
 const file=failureFile(index);if(!fs.existsSync(file))return;
 const old=JSON.parse(fs.readFileSync(file,'utf8'));
 if(old.status==='FAILED')atomicJson(file,{...old,status:'RESOLVED',resolvedAt:new Date().toISOString()});
}
const dataHash=sha(rawGrid);
const section=options.section===undefined?null:integer('section',null,1);
const range=section===null?{start:0,end:total}:sectionRange(total,section);
if(options.sections!==undefined){
 if(options.section!==undefined||options.start!==undefined)throw Error('--sections cannot be combined with --section or --start');
 const sections=options.sections.split(',').map(Number);
 if(!sections.length||new Set(sections).size!==sections.length)throw Error('Supply distinct section numbers');
 sections.forEach(s=>sectionRange(total,s));
 const childArgs=[command,...Object.entries(options).filter(([k])=>k!=='sections').flatMap(([k,v])=>['--'+k,v])];
 const exits=await Promise.all(sections.map(s=>new Promise((resolve,reject)=>{
  const child=spawn(process.execPath,[fileURLToPath(import.meta.url),...childArgs,'--section',String(s)],
   {cwd:repo,windowsHide:true,stdio:'inherit'});
  child.on('error',reject);child.on('close',code=>resolve(code??1));
 })));
 process.exitCode=exits.some(code=>code!==0)?1:0;
}else{
if(command==='status'){
 const names=new Set(fs.existsSync(receipts)?fs.readdirSync(receipts).filter(n=>/^C\d+\.json$/.test(n)):[]);
 const failed=failureRecords(),failedIndices=new Set(failed.map(r=>r.index));
 const recordedIn=(a,b)=>{let n=0;for(let i=a;i<b;i++)if(names.has('C'+String(i).padStart(6,'0')+'.json')&&!failedIndices.has(i))n++;return n;};
 const sections=Array.from({length:Math.ceil(total/10000)},(_,i)=>{
  const r=sectionRange(total,i+1);let next=r.start;
  while(next<r.end&&names.has('C'+String(next).padStart(6,'0')+'.json')&&!failedIndices.has(next))next++;
  return {...r,lastChunk:r.end-1,totalChunks:r.end-r.start,recordedSuccessfulChunks:recordedIn(r.start,r.end),
   unresolvedFailedChunks:failed.filter(f=>r.start<=f.index&&f.index<r.end).map(f=>f.index),
   nextUnrecordedChunk:next<r.end?next:null,nextPendingChunk:next<r.end?next:null};
 });
 const recorded=recordedIn(range.start,range.end);
 console.log(JSON.stringify({kind,variant,totalChunks:total,recordedSuccessfulChunks:recorded,
  section,sections:section===null?sections:sections.filter(s=>s.section===section),gridPoints:data.grid.length,countBlocks:summary.blocks,
  unresolvedFailures:failed.filter(f=>range.start<=f.index&&f.index<range.end).map(f=>({index:f.index,module:f.module,stage:f.stage,error:f.error,failedAt:f.failedAt})),
  note:'Recorded receipts are historical. Run rechecks current source/dependency hashes; final audit remains separate.'},null,2));
 process.exit(0);
}
const start=integer('start',range.start),chunks=integer('chunks',section===null?1:range.end-start,1);
if(start<range.start||start>=range.end)throw Error('start is outside selected section/range');
const end=section===null?Math.min(total,start+chunks):range.end;
fs.mkdirSync(generated,{recursive:true});fs.mkdirSync(receipts,{recursive:true});
// Legacy mode takes an exclusive campaign lock: two legacy runs share a tag.
const lock=acquireRangeLock(path.join(repo,'.lake/build-434/manual-certificates/locks',variant),
 section===null?0:range.start,section===null?total:range.end);
try{
const S=1n<<48n;
function unit(n,d){if(d<=0n||n<d||n>2n*d)throw Error('Bad normalized logarithm');let q=0n;
 for(let i=0n;i<16n;i++)q+=S*(n-d)**(2n*i+1n)/((2n*i+1n)*(n+d)**(2n*i+1n));
 return [2n*q,2n*q+33n];}
const ln2=unit(2n,1n);
function bounds(n,d){let k=0n,dd=d;while(n>=2n*dd){dd*=2n;k++;}const u=unit(n,dd);return {k,L:k*ln2[0]+u[0],U:k*ln2[1]+u[1]};}
let counts;
if(kind==='counts'){
 counts=zlib.gunzipSync(fs.readFileSync(path.join(root,'block-relative-1e10.counts.bin.gz')));
 if(counts.length!==2*summary.blocks||sha(counts)!==data.countSha256||data.countSha256!==summary.countSha256)
  throw Error('Count input hash/length mismatch');
}
const driverHash=sha(fs.readFileSync(fileURLToPath(import.meta.url)));
const logDir=path.join(repo,'.lake/build-434/source-build-logs');
const configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const objectFile=m=>path.join(repo,'.lake/build-434/lib/lean',m.replaceAll('.','/'))+'.olean';
const objectHashes=new Map(),moduleFreshness=new Map();
const hashObject=m=>{if(!objectHashes.has(m))objectHashes.set(m,sha(fs.readFileSync(objectFile(m))));return objectHashes.get(m);};
let candidates;
function freshDependency(m){
 if(moduleFreshness.has(m))return moduleFreshness.get(m);
 if(!candidates)candidates=fs.readdirSync(logDir).filter(n=>/^ledger(?:-[a-z]+)?\.json$/.test(n))
  .map(n=>JSON.parse(fs.readFileSync(path.join(logDir,n),'utf8')));
 const rel=m.replaceAll('.','/')+'.lean';
 const sourceFile=[repo,path.join(repo,'OpenAI/wrappers'),path.join(repo,'OpenAI/grouped'),path.join(repo,'OpenAI'),
  root,path.join(root,'Calr3'),...['chen-effective','chen-dusart','chen-bjs-study','chen-numerical-study'].map(s=>path.join(repo,'research',s))]
  .map(p=>path.join(p,rel)).find(p=>fs.existsSync(p));
 if(!sourceFile)return false;
 const sourceHash=sha(fs.readFileSync(sourceFile));
 const valid=candidates.some(l=>{const r=l[m];return r&&r.configurationHash===configurationHash&&r.sourceHash===sourceHash&&
  r.objectHash===hashObject(m)&&Object.entries(r.dependencies).every(([d,h])=>hashObject(d)===h&&freshDependency(d));});
 moduleFreshness.set(m,valid);return valid;
}
function reusable(index){
 const name='C'+String(index).padStart(6,'0'),receiptFile=path.join(receipts,name+'.json');
 if(!fs.existsSync(receiptFile))return false;
 try{
  const r=JSON.parse(fs.readFileSync(receiptFile,'utf8')),m='PlattCertificates.'+variant+'.'+name;
  const sourceHash=sha(fs.readFileSync(path.join(generated,name+'.lean'))),c=r.checked;
  return r.classification==='LEAN_KERNEL_CHECKED_COMPONENT_NOT_FINAL_H30'&&r.kind===kind&&r.variant===variant&&
   r.index===index&&r.module===m&&r.gridInputHash===dataHash&&r.sourceHash===sourceHash&&c&&
   c.sourceHash===sourceHash&&c.configurationHash===configurationHash&&c.objectHash===hashObject(m)&&
   Object.entries(c.dependencies).every(([d,h])=>hashObject(d)===h&&freshDependency(d));
 }catch{return false;}
}
let attempted=0,reused=0,succeeded=0;
const failedThisRun=[];
for(let index=start;index<end;index++){
 if(section!==null&&attempted>=chunks)break;
 if(section!==null&&reusable(index)){resolveFailure(index);reused++;continue;}
 attempted++;
 const name='C'+String(index).padStart(6,'0'),moduleName='PlattCertificates.'+variant+'.'+name;
 const file=path.join(generated,name+'.lean');
 let stage='generate';
 try{
 let source,metadata;
 if(kind==='logs'){
  const a=index*pointsPerChunk,b=Math.min(data.grid.length,a+pointsPerChunk);
  const rows=data.grid.slice(a,b).map(p=>{const x=BigInt(p.x),h=bounds(x,1n),l=bounds(h.L,S),u=bounds(h.U,S);
   return `⟨${x},${h.k},${h.L},${h.U},${l.k},${u.k},${l.L},${u.U}⟩`;});
  source=`import PlattLogRows\nnamespace ChenEffective.PlattWindow.Manual.${variant}.${name}\nopen LogCertificate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef rows : List LogRow := [${rows.join(',\n')} ]\ntheorem checked : rows.all checkRow = true := by\n  decide +kernel\nend ChenEffective.PlattWindow.Manual.${variant}.${name}\n`;
  metadata={rowStart:a,rowEndExclusive:b,firstX:data.grid[a].x,lastX:data.grid[b-1].x};
 }else{
  const p=countPlans[index];let packed=0n,Qlo=0n,Qhi=0n;
  for(let k=0;k<p.B;k++){
   const c=BigInt(counts.readUInt16LE(2*(p.offset+k))),A=BigInt(p.lo-1+2*p.W*k);
   if(c>BigInt(p.W))throw Error('Invalid count proposal');
   packed+=c<<BigInt(p.W*k);
   Qlo+=S*c/(A+BigInt(2*p.W));Qhi+=S*c/A+1n;
  }
  source=`import PlattReciprocalKernel\nnamespace ChenEffective.PlattWindow.Manual.${variant}.${name}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef packed : Nat := ${packed}\ntheorem count_checked : Nat.beq (segmentCounts ${p.lo} ${p.w} ${p.B}) packed = true := by\n  decide +kernel\ntheorem arithmetic_checked :\n    (Nat.beq (segmentFixed (2^48) ${p.lo} ${p.w} packed ${p.B}).1 ${Qlo} &&\n     Nat.beq (segmentFixed (2^48) ${p.lo} ${p.w} packed ${p.B}).2 ${Qhi}) = true := by\n  decide +kernel\nend ChenEffective.PlattWindow.Manual.${variant}.${name}\n`;
  metadata={...p,lower:Qlo.toString(),upper:Qhi.toString(),countSha256:data.countSha256};
 }
 const sourceHash=sha(source);
 if(!fs.existsSync(file)||fs.readFileSync(file,'utf8')!==source)fs.writeFileSync(file,source);
 const record={kind,variant,index,module:moduleName,sourceHash,gridInputHash:dataHash,driverHash,metadata,
  classification:'GENERATED_NOT_CHECKED'};
 atomicJson(path.join(generated,name+'.json'),record);
 console.log(JSON.stringify({generated:moduleName,...metadata}));
 if(command==='prepare')continue;
 const tag=(kind==='logs'?'manuallogs':'manualcounts')+(section===null?'':'section'+String.fromCharCode(96+section));
 const buildScript=path.join(repo,'OpenAI/tools/build-source.mjs');
 stage='build-or-ledger-save';
 const exitCode=await new Promise((resolve,reject)=>{
  const child=spawn(process.execPath,[buildScript,moduleName],{cwd:repo,windowsHide:true,stdio:'inherit',
   env:{...process.env,CHEN_REPO:repo,CHEN_BUILD_TAG:tag,CHEN_BUILD_JOBS:'1',CHEN_LEAN_THREADS:'1',CHEN_LEAN_MEMORY_MB:String(memory),
    CHEN_BUILD_COMPACT_LEDGER:section===null?'0':'1',CHEN_BUILD_CACHE_ONLY_DEPS:section===null?'0':'1',CHEN_BUILD_LEASE_FILE:lock.file}});
  lock.setChild(child.pid??null);child.on('error',reject);child.on('close',code=>{lock.setChild(null);resolve(code);});
 });
 if(exitCode!==0)throw Error('Certificate build or ledger save failed; no new success receipt written: '+moduleName);
 stage='validate-checked-object';
 const logs=path.join(repo,'.lake/build-434/source-build-logs');
 const ledger=JSON.parse(fs.readFileSync(path.join(logs,'ledger-'+tag+'.json'),'utf8'));
 const checked=ledger[moduleName],object=path.join(repo,'.lake/build-434/lib/lean',moduleName.replaceAll('.','/')+'.olean');
 if(!checked||checked.sourceHash!==sourceHash||!fs.existsSync(object)||checked.objectHash!==sha(fs.readFileSync(object)))
  throw Error('Current source/object check record missing');
 stage='write-success-receipt';
 atomicJson(path.join(receipts,name+'.json'),{...record,
  classification:'LEAN_KERNEL_CHECKED_COMPONENT_NOT_FINAL_H30',checkedAt:new Date().toISOString(),checked});
 resolveFailure(index);succeeded++;
 console.log(JSON.stringify({checked:moduleName,seconds:checked.seconds,receipt:path.join(receipts,name+'.json')}));
 }catch(error){
  fs.mkdirSync(failures,{recursive:true});
  const failurePath=failureFile(index);
  const old=fs.existsSync(failurePath)?JSON.parse(fs.readFileSync(failurePath,'utf8')):{};
  const failure={kind,variant,index,module:moduleName,section,status:'FAILED',stage,
   attempts:(old.attempts??0)+1,firstFailedAt:old.firstFailedAt??new Date().toISOString(),
   failedAt:new Date().toISOString(),gridInputHash:dataHash,configurationHash,
   error:error.message,stack:error.stack,
   leanLog:path.join(logDir,moduleName+'.log'),
   buildStatus:path.join(logDir,'status-'+(kind==='logs'?'manuallogs':'manualcounts')+
    (section===null?'':'section'+String.fromCharCode(96+section))+'.json')};
  // If even the failure record cannot be saved, stop rather than silently lose it.
  atomicJson(failurePath,failure);
  failedThisRun.push(index);
  console.error(JSON.stringify({chunkFailed:moduleName,index,stage,failureRecord:failurePath,
   error:error.message,continuing:true}));
 }
}
if(failedThisRun.length)process.exitCode=1;
console.log(JSON.stringify({finished:true,section,attempted,succeeded,reused,failed:failedThisRun.length,
 failedChunks:failedThisRun,successful:failedThisRun.length===0,requestedChunks:chunks,
 note:'Chunk limits count attempts. Failures remain pending and are retried on the next resume; later successes never skip a gap.'}));
}finally{lock.release();}
}
