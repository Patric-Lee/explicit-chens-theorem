import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt'),logs=path.join(repo,'.lake/build-434/source-build-logs');
const hash=b=>crypto.createHash('sha256').update(b).digest('hex');
const configurationHash=hash(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const campaign=JSON.parse(fs.readFileSync(path.join(root,'ASSEMBLY_CAMPAIGN_VERIFIED.json')));
const plan=JSON.parse(fs.readFileSync(path.join(root,'PlattGlobalTotals/plan.json')));
const totalsLedger=JSON.parse(fs.readFileSync(path.join(logs,'ledger-globaltotals.json')));
const object=m=>path.join(repo,'.lake/build-434/lib/lean',m.replaceAll('.','/'))+'.olean';
const checked=[];
for(const m of [...plan.levels.flat(),'PlattGlobalBoundSoundness','PlattGlobalReference','PlattPointPacketKernel']){
 const tag=m==='PlattGlobalBoundSoundness'?'globalboundsound':m==='PlattGlobalReference'?'globalreference':m==='PlattPointPacketKernel'?'pointpacket':'globaltotals';
 const r=tag==='globaltotals'?totalsLedger[m]:JSON.parse(fs.readFileSync(path.join(logs,'ledger-'+tag+'.json')))[m];
 if(!r||r.configurationHash!==configurationHash||r.sourceHash!==hash(fs.readFileSync(path.join(root,m.replaceAll('.','/')+'.lean')))||r.objectHash!==hash(fs.readFileSync(object(m))))throw Error('Missing current checked artifact '+m);
 for(const [d,h] of Object.entries(r.dependencies))if(hash(fs.readFileSync(object(d)))!==h)throw Error('Dependency mismatch '+m+' -> '+d);
 checked.push({module:m,...r});
}
const ax=fs.readFileSync(path.join(logs,'PlattGlobalReference.log'),'utf8').match(/depends on axioms:\s*\[([^\]]*)\]/s);
const axioms=ax?ax[1].split(',').map(s=>s.trim()).sort():[];
if(JSON.stringify(axioms)!==JSON.stringify(['Classical.choice','Quot.sound','propext'].sort()))throw Error('Unexpected reference axioms');
const report={classification:'ALL_FINITE_CAMPAIGNS_AND_GLOBAL_TOTALS_CHECKED_NOT_FULL_CHEN',checkedAt:new Date().toISOString(),configurationHash,
 campaign,globalTotalRoot:plan.root,referenceTheorem:'ChenEffective.PlattWindow.global_reference_reciprocal_bounds',axioms,checked,
 remaining:['Point-chain semantic proof and global prefix-point carries','Global grid/point/log alignment and all-real coverage','Platt analytic-window integration','Replace temporary prefix axiom and rerun final Chen audit'],
 manualAction:'No further counting or existing assembly run is needed.'};
fs.writeFileSync(path.join(root,'ASSEMBLY_COMPLETION_REPORT.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({batches:campaign.batches,globalSumNodes:plan.modules,referenceTheorem:report.referenceTheorem,axioms},null,2));
