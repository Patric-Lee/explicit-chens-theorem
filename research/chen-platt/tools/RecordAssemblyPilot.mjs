import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt'),build=path.join(repo,'.lake/build-434');
const hash=b=>crypto.createHash('sha256').update(b).digest('hex');
const config=hash(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const logs=path.join(build,'source-build-logs'),candidates=fs.readdirSync(logs).filter(n=>/^ledger(?:-[a-z]+)?\.json$/.test(n)).map(n=>JSON.parse(fs.readFileSync(path.join(logs,n))));
const modules=['PlattAssemblyKernel','PlattIncrementKernel','PlattSegmentPacket','PlattAssemblySoundness',
 ...['C000000','C000001','C010000','C070000','C000000Sound','Grid0N16',...Array.from({length:8},(_,i)=>`Grid${256*i}N256`),'Grid10000N256','Grid239500N256',
 'SealedTotals0N8','SealedTotals0N32','SealedTotals10000N32','SealedTotals9992N16','SealedTotals0N256','VerifiedPilot','NegativeControls'].map(n=>'PlattAssemblyPilot.'+n)];
const records=modules.map(m=>{
 const rel=m.replaceAll('.','/'),source=fs.readFileSync(path.join(root,rel+'.lean'));
 const sourceHash=hash(source),objectHash=hash(fs.readFileSync(path.join(build,'lib/lean',rel+'.olean')));
 if(/\b(sorry|admit|native_decide)\b|^\s*axiom\s/m.test(source.toString()))throw Error('Forbidden source token '+m);
 const r=candidates.map(c=>c[m]).find(r=>r&&r.sourceHash===sourceHash&&r.objectHash===objectHash&&r.configurationHash===config&&
  Object.entries(r.dependencies).every(([d,h])=>hash(fs.readFileSync(path.join(build,'lib/lean',d.replaceAll('.','/')+'.olean')))===h));
 if(!r)throw Error('Current checked root missing '+m);
 return {module:m,...r};
});
for(const m of ['PlattAssemblySoundness','PlattAssemblyPilot.VerifiedPilot','PlattAssemblyPilot.C000000Sound']){
 const log=fs.readFileSync(path.join(logs,m+'.log'),'utf8');
 if(log.includes('sorryAx')||!log.includes('depends on axioms'))throw Error('Unexpected axiom log '+m);
}
const count=JSON.parse(fs.readFileSync(path.join(root,'COUNT_CAMPAIGN_VERIFIED.json')));
const report={classification:'KERNEL_CHECKED_SMALL_ASSEMBLY_PILOT_NOT_COMPLETE_FINITE_WINDOW',checkedAt:new Date().toISOString(),
 countCampaign:count,independentPrefixFeasibility:JSON.parse(fs.readFileSync(path.join(root,'PlattAssemblyPilot/pilot-proposals.json'))).independentPrefixBudget,
 measuredCumulativeBatches:JSON.parse(fs.readFileSync(path.join(root,'PlattAssemblyPilot/benchmark-cumulative.json'))),
 measuredEightWorkerGrid:JSON.parse(fs.readFileSync(path.join(root,'PlattAssemblyPilot/benchmark-grid-eight.json'))),
 checkedRoots:records,
 limits:['Unsealed dense 256-chunk batch exceeded 2 GiB; sealed variant passed but took about 103 seconds.',
 'Only small assembly batches are kernel certified; all-grid independent-prefix budget is a JavaScript feasibility check.',
 'Full cumulative/checkpoint certificate tree and final reference-bound integration remain to be generated and checked.',
 'The H30 temporary prefix axiom remains; no new axiom or dependency has been added.']};
const target=path.join(root,'ASSEMBLY_PILOT_REPORT.json');fs.writeFileSync(target,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({report:target,checkedRoots:records.length,countChunks:count.chunks,eightWorkerGridSeconds:report.measuredEightWorkerGrid.wallSeconds},null,2));
