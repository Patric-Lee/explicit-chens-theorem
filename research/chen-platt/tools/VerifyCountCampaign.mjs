import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import zlib from 'node:zlib';
const repo=process.argv[2];
if(!repo)throw Error('Usage: node VerifyCountCampaign.mjs REPO [REPORT.json]');
const root=path.join(repo,'research/chen-platt'),build=path.join(repo,'.lake/build-434');
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const raw=fs.readFileSync(path.join(root,'block-relative-1e10.grid.json.gz'));
const data=JSON.parse(zlib.gunzipSync(raw)),summary=JSON.parse(fs.readFileSync(path.join(root,'block-relative-1e10.json')));
const gridInputHash=sha(raw),configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const insist=(b,m)=>{if(!b)throw Error(m);};
const variant='Count131072',dir=path.join(root,'PlattCertificates',variant),receipts=path.join(build,'manual-certificates',variant);
const countRaw=zlib.gunzipSync(fs.readFileSync(path.join(root,'block-relative-1e10.counts.bin.gz')));
insist(countRaw.length===2*summary.blocks&&sha(countRaw)===data.countSha256&&summary.countSha256===data.countSha256,'Count input mismatch');
const candidates=fs.readdirSync(path.join(build,'source-build-logs')).filter(n=>/^ledger(?:-[a-z]+)?\.json$/.test(n))
 .map(n=>JSON.parse(fs.readFileSync(path.join(build,'source-build-logs',n))));
const dependencyHashes=new Map();
function dependency(m){
 if(dependencyHashes.has(m))return dependencyHashes.get(m);
 const rel=m.replaceAll('.','/'),src=[root,path.join(root,'Calr3')].map(r=>path.join(r,rel+'.lean')).find(f=>fs.existsSync(f));
 insist(src,'Missing dependency source '+m);
 const sourceHash=sha(fs.readFileSync(src)),objectHash=sha(fs.readFileSync(path.join(build,'lib/lean',rel+'.olean')));
 const r=candidates.map(l=>l[m]).find(r=>r&&r.configurationHash===configurationHash&&r.sourceHash===sourceHash&&r.objectHash===objectHash&&
  Object.entries(r.dependencies).every(([d,h])=>dependency(d)===h));
 insist(r,'No current checked dependency '+m);dependencyHashes.set(m,objectHash);return objectHash;
}
dependency('PlattReciprocalKernel');
const start=Date.now(),manifest=crypto.createHash('sha256');
let index=0,previous=data.U,summedSeconds=0;
for(let g=0;g<data.groups.length;g++){
 const group=data.groups[g],end=data.groups[g+1]?.offset??summary.blocks,W=2**group.w,cap=Math.floor(131072/(2*W));
 for(let offset=group.offset;offset<end;offset+=cap,index++){
  const B=Math.min(cap,end-offset),lo=group.lo+2*W*(offset-group.offset),name='C'+String(index).padStart(6,'0'),m=`PlattCertificates.${variant}.${name}`;
  const r=JSON.parse(fs.readFileSync(path.join(receipts,name+'.json'))),p=r.metadata,c=r.checked;
  insist(r.kind==='counts'&&r.variant===variant&&r.index===index&&r.module===m&&r.gridInputHash===gridInputHash&&
   r.classification==='LEAN_KERNEL_CHECKED_COMPONENT_NOT_FINAL_H30','Invalid receipt '+name);
  insist(p.offset===offset&&p.w===group.w&&p.W===W&&p.B===B&&p.lo===lo&&p.hi===lo+2*W*B-1&&p.countSha256===data.countSha256,'Metadata mismatch '+name);
  insist(previous===lo-1,'Chunk seam mismatch '+name);previous=lo-1+2*W*B;
  const source=fs.readFileSync(path.join(dir,name+'.lean'),'utf8'),packed=source.match(/def packed : Nat := (\d+)\n/);
  insist(packed,'Packed certificate missing '+name);
  const expected=`import PlattReciprocalKernel\nnamespace ChenEffective.PlattWindow.Manual.${variant}.${name}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef packed : Nat := ${packed[1]}\ntheorem count_checked : Nat.beq (segmentCounts ${lo} ${group.w} ${B}) packed = true := by\n  decide +kernel\ntheorem arithmetic_checked :\n    (Nat.beq (segmentFixed (2^48) ${lo} ${group.w} packed ${B}).1 ${p.lower} &&\n     Nat.beq (segmentFixed (2^48) ${lo} ${group.w} packed ${B}).2 ${p.upper}) = true := by\n  decide +kernel\nend ChenEffective.PlattWindow.Manual.${variant}.${name}\n`;
  insist(source===expected,'Unexpected checked statement/template '+name);
  const sourceHash=sha(source),objectHash=sha(fs.readFileSync(path.join(build,'lib/lean',m.replaceAll('.','/')+'.olean')));
  insist(c&&r.sourceHash===sourceHash&&c.sourceHash===sourceHash&&c.objectHash===objectHash&&c.configurationHash===configurationHash,'Source/object/config mismatch '+name);
  insist(Object.keys(c.dependencies).length===1&&c.dependencies.PlattReciprocalKernel===dependency('PlattReciprocalKernel'),'Dependency mismatch '+name);
  const fail=path.join(receipts,'failures',name+'.json');
  if(fs.existsSync(fail))insist(JSON.parse(fs.readFileSync(fail)).status==='RESOLVED','Unresolved failure '+name);
  manifest.update(JSON.stringify([m,sourceHash,objectHash])+'\n');summedSeconds+=c.seconds;
  if((index+1)%5000===0)console.log(JSON.stringify({verifiedChunks:index+1,seconds:(Date.now()-start)/1000}));
 }
}
insist(index===76265&&previous===data.R,'Incomplete campaign coverage');
const report={classification:'COUNT_RECEIPTS_SOURCES_OBJECTS_AND_PLAN_VERIFIED_NOT_FINAL_CHEN',checkedAt:new Date().toISOString(),
 chunks:index,blocks:summary.blocks,first:data.U,last:previous,gridInputHash,countInputHash:data.countSha256,configurationHash,
 sourceObjectManifestHash:manifest.digest('hex'),summedRecordedLeanSeconds:summedSeconds,verificationSeconds:(Date.now()-start)/1000,
 remaining:'Kernel-level cumulative/grid assembly and final Chen axiom replacement/audit'};
if(process.argv[3])fs.writeFileSync(process.argv[3],JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report,null,2));
