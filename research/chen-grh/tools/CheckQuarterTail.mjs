// Verify the checked component campaign and preserve its exact scope.
import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const root=path.resolve(process.argv[2]||process.cwd()),dir=path.join(root,'research/chen-grh');
const logs=path.join(root,'.lake/build-434/source-build-logs'),obj=path.join(root,'.lake/build-434/lib/lean');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const config=sha(fs.readFileSync(path.join(root,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(root,'lake-manifest.json'),'utf8'));
const manifest=JSON.parse(fs.readFileSync(path.join(root,'lake-manifest.json')));
if(fs.readFileSync(path.join(root,'lean-toolchain'),'utf8').trim()!=='leanprover/lean4:v4.34.1'||
 manifest.packages.find(p=>p.name==='mathlib')?.rev!=='d13f23b723b8a846827a245b89c10fc7d3f11612'||
 JSON.stringify(manifest.packages.filter(p=>!p.inherited).map(p=>p.name).sort())!==JSON.stringify(['LeanArchitect','mathlib']))throw Error('Changed pinned environment or direct dependencies');
const data=JSON.parse(fs.readFileSync(path.join(dir,'GRHQuarterMomentData.json')));
const ledger=JSON.parse(fs.readFileSync(path.join(logs,'ledger-quarterassembly.json')));
const status=JSON.parse(fs.readFileSync(path.join(logs,'status-quarterassembly.json')));
if(status.failed||status.remaining!==0||status.running!==0)throw Error('Assembly campaign is incomplete');
const baseline=JSON.parse(fs.readFileSync(path.join(dir,'FINAL_GRHSub12_CHEN_AUDIT.json')));
let end=2,total=0n;
for(const r of data.rows){
 if(r.lo!==end+1||r.upper!==r.lo+2*(2**r.w*r.B)-1)throw Error('Broken finite interval coverage');
 end=r.upper;total+=BigInt(r.numerator);
 const src=fs.readFileSync(path.join(dir,r.module.replaceAll('.','/')+'.lean'));
 if(sha(src)!==r.sourceHash)throw Error('Changed finite certificate '+r.module);
}
if(end<4000000||data.rows.length!==508||total!==BigInt(data.numerator)||total*100n>1799n*BigInt(data.denominator))throw Error('Invalid cap total');
// Match the source builder's precedence: wrappers shadow the original OAI tree.
const roots=[root,path.join(root,'OpenAI/wrappers'),path.join(root,'OpenAI/grouped'),path.join(root,'OpenAI'),path.join(root,'research/chen-platt'),path.join(root,'research/chen-platt/Calr3'),...['chen-effective','chen-dusart','chen-bjs-study','chen-numerical-study','chen-grh'].map(n=>path.join(root,'research',n))];
const checked=new Map();
function visit(name){
 if(checked.has(name))return;
 const r=ledger[name];if(!r)throw Error('Missing provenance '+name);
 const rel=name.replaceAll('.','/');const base=roots.find(b=>fs.existsSync(path.join(b,rel+'.lean')));
 if(!base||r.configurationHash!==config||r.sourceHash!==sha(fs.readFileSync(path.join(base,rel+'.lean')))||r.objectHash!==sha(fs.readFileSync(path.join(obj,rel+'.olean'))))throw Error('Stale proof provenance '+name);
 checked.set(name,{module:name,sourceHash:r.sourceHash,objectHash:r.objectHash,seconds:r.seconds});
 for(const [n,h] of Object.entries(r.dependencies)){
  if(h!==sha(fs.readFileSync(path.join(obj,n.replaceAll('.','/')+'.olean'))))throw Error('Stale imported object '+n);
  visit(n);
 }
}
visit('AuditGRHQuarterTail');
const audit=fs.readFileSync(path.join(logs,'AuditGRHQuarterTail.log'),'utf8');
const m=audit.match(/audit passed: (\d+) transitive constants/);
if(!m||/sorryAx|error:|Unexpected axioms|Unlisted axiom|Unsafe proof dependency/.test(audit))throw Error('Missing or failed transitive audit');
const auditSource=path.join(dir,'AuditGRHQuarterTail.lean'),auditObj=path.join(obj,'AuditGRHQuarterTail.olean');
if(!fs.existsSync(auditObj)||fs.statSync(auditObj).mtimeMs<fs.statSync(auditSource).mtimeMs)throw Error('Stale audit object');
const proofManifest=[...checked.values()].map(({module,sourceHash,objectHash})=>({module,sourceHash,objectHash})).sort((a,b)=>a.module.localeCompare(b.module));
const toolHashes=Object.fromEntries(['GenerateQuarterMoments','AssembleQuarterMoments','StudyQuarterTailTargets','CheckQuarterTail'].map(n=>[n,sha(fs.readFileSync(path.join(dir,'tools',n+'.mjs')))]));
const report={classification:'QUARTER_MOMENTS_AND_ACTUAL_SOURCE_TAIL_KERNEL_CHECKED_H10_UNPROVED',
 sourceObjectManifestHash:sha(JSON.stringify(proofManifest)),toolHashes,
 baselineManifest:baseline.sourceObjectManifestHash,baselineH:11.97853684901941,
 endpoint:4000000,certifiedLogCap:'1799/100',integerEnvelopeNumerator:data.numerator,denominator:data.denominator,
 shards:508,transitiveConstants:Number(m[1]),newAxioms:0,nativeDecide:false,newDependencies:0,
 toolchain:fs.readFileSync(path.join(root,'lean-toolchain'),'utf8').trim(),manifestHash:sha(fs.readFileSync(path.join(root,'lake-manifest.json'))),
 actualSourceTail:'11 N exp(17.99) (1+log D)^2 / C^(1/4)',
 actualMediumTail:'25.41 N exp(17.99) (1+log N)^2 / C^(1/4)',
 normalizedMediumTail:'(N/L^2) * 26 L^4 exp(17.99) / C^(1/4), L=log N>=2400',
 remaining:['The sharper tail targets 16 L and the alternative 0.05 L^2 remain unproved.','Specialized weighted convolution/QD distribution at the H10 range is unproved.','Source and Selberg-denominator thresholds, full counting inequalities, band pasting, and final Chen audit remain.'],
 auditSourceHash:sha(fs.readFileSync(auditSource)),auditObjectHash:sha(fs.readFileSync(auditObj)),auditLogHash:sha(Buffer.from(audit)),
 modules:[...checked.values()]};
fs.writeFileSync(path.join(dir,'QUARTER_TAIL_COMPONENT_CHECK.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({passed:true,shards:508,checkedModules:checked.size,transitiveConstants:Number(m[1]),certifiedLogCap:17.99,H10Proved:false}));
