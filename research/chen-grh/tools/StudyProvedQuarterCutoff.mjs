// The search is untrusted; Lean checks the resulting count bounds and minimum.
import fs from 'node:fs';import path from 'node:path';
const root=path.resolve(process.argv[2]||process.cwd());
const candidates=[];
for(let r=1;r<=5000;r++){
 const sourceAccuracyPaid=62500n<=21n*BigInt(r);
 if(!sourceAccuracyPaid)continue;
 const exponent=40*r+1,logLower=Math.floor(439*exponent/400);
 if(exponent<110010||logLower<130690)continue;
 candidates.push({r,exponent,logLower,H:Math.log(exponent*Math.log(3))});
}
if(candidates[0]?.r!==2977||candidates[0]?.exponent!==119081)throw Error('Search mismatch');
const auditFile=path.join(root,'research/chen-grh/FINAL_GRH_QUARTER_CHEN_AUDIT.json');
const audit=fs.existsSync(auditFile)?JSON.parse(fs.readFileSync(auditFile)):null;
const checked=audit?.classification==='GRH_ONLY_QUARTER_MOMENT_COMPLETE_CHEN_KERNEL_CHECKED'&&audit.cutoff==='3^119081';
const report={classification:checked?'FIXED_PACKAGE_SEARCH_WITH_SEPARATE_KERNEL_CERTIFIED_IMPLEMENTATION':'FIXED_PROVED_BOUND_PACKAGE_SEARCH_CANDIDATE_REQUIRES_CHEN_AUDIT',
 scope:'Minimum within the displayed source-accuracy/counting package, not global optimality over Chen methods.',
 selected:candidates[0],candidates:candidates.length,
 parameters:{sigma:'1/4',momentLogCap:'1799/100',presieveStart:4000000,
  truncationExponent:'13/2500',epsilon:'9/2500',distributionExponent:'1241/2500',
  sourceUpperAllowance:'21/1000',sourceLowerParameter:20000000,
  lowerCoefficient:'2.00825',tripleCoefficient:'4.015',representationMargin:'3/4000',
  K:'8059/1000',pairMain:'0.498',mediumLoss:'1139/1000'},
 constraints:{sourceAccuracy:'62500 <= 21*r',sourceExponent:'E >= 40*r+1',
  sourceLowerExponent:110010,uniformLogLower:130690},
 formalMinimum:'ChenEffective.GRHQuarterChen.source_accuracy_exponent_minimal',
 formalChen:'ChenEffective.GRHQuarterChen.chen_explicit',
 formalH:'ChenEffective.GRHQuarterChen.chen_of_double_exp_11782',
 separateAuditRecord:checked?'FINAL_GRH_QUARTER_CHEN_AUDIT.json':null,
 unprovedH10TargetsUsed:false,newAxioms:0,newDependencies:0,nativeDecide:false};
fs.writeFileSync(path.join(root,'research/chen-grh/PROVED_QUARTER_CUTOFF_SEARCH.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({selected:report.selected,scope:report.scope}));
