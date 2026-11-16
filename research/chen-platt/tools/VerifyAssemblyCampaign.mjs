// Verify existing artifacts without regenerating or recompiling certificates.
import fs from 'node:fs';import path from 'node:path';import zlib from 'node:zlib';import crypto from 'node:crypto';
import {batchPlan,generateBatch,kinds,title,sha} from './AssemblyPlan.mjs';
const repo=process.argv[2];if(!repo)throw Error('Usage: node VerifyAssemblyCampaign.mjs REPO [REPORT.json]');
const root=path.join(repo,'research/chen-platt'),build=path.join(repo,'.lake/build-434'),dataDir=path.join(root,'PlattAssemblyData');
const rawManifest=fs.readFileSync(path.join(dataDir,'manifest.json')),manifest=JSON.parse(rawManifest),manifestHash=sha(rawManifest);
const configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const insist=(b,m)=>{if(!b)throw Error(m);};
insist(manifest.schema===1&&manifest.configurationHash===configurationHash,'Stale assembly proposals/configuration');
const logDir=path.join(build,'source-build-logs');
const ledgers=fs.readdirSync(logDir).filter(n=>/^ledger(?:-[a-z]+)?\.json$/.test(n)).map(n=>JSON.parse(fs.readFileSync(path.join(logDir,n))));
const roots=[repo,path.join(repo,'OpenAI/wrappers'),path.join(repo,'OpenAI/grouped'),path.join(repo,'OpenAI'),root,path.join(root,'Calr3')];
const object=m=>path.join(build,'lib/lean',m.replaceAll('.','/'))+'.olean';
const objectHashes=new Map(),validated=new Map();
function objectHash(m){if(!objectHashes.has(m))objectHashes.set(m,sha(fs.readFileSync(object(m))));return objectHashes.get(m);}
function dependency(m){
 if(validated.has(m))return validated.get(m);
 const file=roots.map(r=>path.join(r,m.replaceAll('.','/')+'.lean')).find(f=>fs.existsSync(f));insist(file,'Missing dependency source '+m);
 const sourceHash=sha(fs.readFileSync(file)),objectHashValue=objectHash(m);
 const r=ledgers.map(l=>l[m]).find(r=>r&&r.configurationHash===configurationHash&&r.sourceHash===sourceHash&&r.objectHash===objectHashValue&&
  Object.entries(r.dependencies).every(([d,h])=>dependency(d).objectHash===h));
 insist(r,'No matching checked dependency '+m);validated.set(m,r);return r;
}
const start=Date.now(),stages=[],artifactManifest=crypto.createHash('sha256');let checked=0;
for(const kind of kinds){
 const stage={kind,batches:0,recordedLeanSeconds:0,sections:[]};const total=kind==='grid'?manifest.cells:manifest.counts;let previous=0;
 for(let section=1;section<=8;section++){
  const entry=manifest.files.find(f=>f.kind===kind&&f.section===section),bytes=fs.readFileSync(path.join(dataDir,entry.file));
  insist(sha(bytes)===entry.hash,'Proposal file hash mismatch '+entry.file);
  const payload=JSON.parse(zlib.gunzipSync(bytes)),records=payload.records.map((r,i)=>({...r,index:kind==='grid'?payload.start+i:r.index}));
  const plan=batchPlan(kind,section,total),dir=path.join(build,'assembly-certificates',title(kind),'S'+section);
  for(const p of plan){
   insist(p.start===previous,'Plan gap/overlap '+kind+':'+section+':'+p.index);previous=p.end;
   const g=generateBatch(kind,section,p,records,manifest),m=g.module,name='B'+String(p.index).padStart(6,'0');
   const receipt=JSON.parse(fs.readFileSync(path.join(dir,name+'.json'))),c=receipt.checked;
   insist(receipt.classification==='LEAN_KERNEL_CHECKED_ASSEMBLY_LEAF_NOT_FINAL_WINDOW'&&receipt.kind===kind&&receipt.section===section&&receipt.index===p.index&&receipt.module===m&&receipt.manifestHash===manifestHash,'Receipt identity mismatch '+m);
   const file=path.join(root,m.replaceAll('.','/')+'.lean'),source=fs.readFileSync(file);
   insist(source.toString()===g.source,'Current generator/source mismatch '+m);
   const sourceHash=sha(source),objHash=objectHash(m);
   insist(receipt.sourceHash===sourceHash&&c?.sourceHash===sourceHash&&c.objectHash===objHash&&c.configurationHash===configurationHash,'Receipt source/object/config mismatch '+m);
   insist(JSON.stringify(receipt.metadata)===JSON.stringify(g.metadata),'Receipt metadata mismatch '+m);
   for(const [d,h] of Object.entries(c.dependencies))insist(dependency(d).objectHash===h,'Dependency mismatch '+m+' -> '+d);
   const failure=path.join(dir,'failures',name+'.json');if(fs.existsSync(failure))insist(JSON.parse(fs.readFileSync(failure)).status==='RESOLVED','Unresolved failure '+m);
   artifactManifest.update(JSON.stringify([m,sourceHash,objHash])+'\n');checked++;stage.batches++;stage.recordedLeanSeconds+=c.seconds;
   if(checked%250===0)console.log(JSON.stringify({verifiedAssemblyBatches:checked,kind,seconds:(Date.now()-start)/1000}));
  }
  stage.sections.push({section,batches:plan.length,first:plan[0].start,lastExclusive:plan.at(-1).end});
 }
 insist(previous===total,'Incomplete stage '+kind);stages.push(stage);
}
// Every original count chunk must occur in the cumulative/prefix dependencies.
const countManifest=crypto.createHash('sha256');
for(let i=0;i<manifest.counts;i++){
 const m='PlattCertificates.Count131072.C'+String(i).padStart(6,'0'),r=dependency(m);
 countManifest.update(JSON.stringify([m,r.sourceHash,r.objectHash])+'\n');
}
insist(countManifest.digest('hex')===manifest.countVerificationManifest,'Original count campaign changed');
const logSources=[];
for(let i=0;i<Math.ceil(manifest.points/256);i++){
 const m='PlattCertificates.Log256.C'+String(i).padStart(6,'0'),r=dependency(m);logSources.push([m,r.sourceHash]);
}
insist(sha(JSON.stringify(logSources))===manifest.logSourcesHash,'Original log campaign changed');
const report={classification:'ASSEMBLY_LEAVES_AND_TRANSITIVE_LOCAL_ARTIFACTS_VERIFIED_NOT_FINAL_CHEN',checkedAt:new Date().toISOString(),
 configurationHash,manifestHash,batches:checked,stages,dependenciesChecked:validated.size,
 countChunks:manifest.counts,logChunks:logSources.length,points:manifest.points,cells:manifest.cells,
 sourceObjectManifestHash:artifactManifest.digest('hex'),verificationSeconds:(Date.now()-start)/1000,
 remaining:['Kernel-level global cumulative offsets/tree','Global point/grid/log joins and section coverage','Platt analytic-window integration','Temporary prefix axiom replacement and final Chen audit']};
if(process.argv[3])fs.writeFileSync(process.argv[3],JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report,null,2));
