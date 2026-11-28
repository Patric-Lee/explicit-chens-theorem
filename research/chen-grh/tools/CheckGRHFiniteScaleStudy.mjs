// Checks provenance and the limited scope of the study, not analytic truth.
import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2]||process.cwd(),dir=path.join(repo,'research/chen-grh');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const report=JSON.parse(fs.readFileSync(path.join(dir,'SPECIALIZED_FINITE_SCALE_STUDY.json')));
const record=JSON.parse(fs.readFileSync(path.join(dir,'FINITE_SCALE_ARITHMETIC_CHECK.json')));
const baseline=JSON.parse(fs.readFileSync(path.join(dir,'FINAL_GRHSub12_CHEN_AUDIT.json')));
if(report.baseline.manifest!==baseline.sourceObjectManifestHash||baseline.cutoff!=='3^145000')throw Error('Changed baseline');
if(report.numericalStudyScriptHash!==sha(fs.readFileSync(path.join(dir,'tools/StudyGRHFiniteScaleBudget.mjs'))))throw Error('Changed study generator');
if(record.classification!=='LEAN_ARITHMETIC_CONTRACTS_ONLY_CHECKED_NOT_ANALYTIC_ESTIMATES')throw Error('Unexpected verification scope');
if(record.sourceHash!==sha(fs.readFileSync(path.join(dir,'GRHFiniteScaleBudget.lean')))||record.objectHash!==sha(fs.readFileSync(path.join(repo,'.lake/build-434/lib/lean/GRHFiniteScaleBudget.olean'))))throw Error('Changed checked arithmetic');
if(record.toolchain!==fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8').trim()||record.manifestHash!==sha(fs.readFileSync(path.join(repo,'lake-manifest.json'))))throw Error('Changed dependencies');
for(const [file,hash]of Object.entries(report.sourceHashes))if(hash!==sha(fs.readFileSync(path.join(dir,file))))throw Error('Changed study source '+file);
if(report.comparisons.length!==48||report.contracts.length!==4||report.moments.length!==40)throw Error('Incomplete parameter coverage');
if(report.moments.some(m=>m.certified)||report.comparisons.some(c=>c.certifiedFeasible))throw Error('Numerical proposal mislabelled certified');
if(report.recommendedH10.H!==10||report.recommendedH10.z!==4000000||!report.recommendedH10.modelPositive||report.recommendedH10.inheritedSourceAndDenominatorGatesDischarged)throw Error('Incorrect H10 scope');
if(report.comparisons.some(c=>c.H<=9&&c.bestPositive!==null))throw Error('Unexpected low-scale candidate; review claims');
for(const c of report.contracts){
 const L=BigInt(c.logLower),cube=L**3n,t=BigInt(c.tripleCap.split('/')[0]);
 if(39897n*cube+10000n*(60000000n+38n*L*L)>10n*t*cube)throw Error('Invalid exact triple contract');
 if(c.margin!==(8051n-2n*t)+'/4000')throw Error('Invalid exact margin');
}
const docs=['README.md','research/chen-grh/README.md','research/chen-grh/SPECIALIZED_FINITE_SCALE_STUDY.md'];let links=0;
for(const rel of docs){const file=path.join(repo,rel),s=fs.readFileSync(file,'utf8');
 if(/^.*[ \t]+$/m.test(s))throw Error('Trailing whitespace '+rel);
 for(const m of s.matchAll(/\]\(([^)]+)\)/g)){const dest=m[1];if(/^(https?:|#)/.test(dest))continue;if(!fs.existsSync(path.resolve(path.dirname(file),dest.split('#')[0])))throw Error('Missing link '+rel+' -> '+dest);links++;}
 for(const m of s.matchAll(/\$\$([\s\S]*?)\$\$|\$([^$\n]+)\$/g)){const math=m[1]??m[2];let d=0;for(let i=0;i<math.length;i++){if(i&&math[i-1]==='\\')continue;if(math[i]==='{')d++;if(math[i]==='}')d--;if(d<0)throw Error('Unbalanced math '+rel);}if(d)throw Error('Unbalanced math '+rel);}
}
console.log(JSON.stringify({passed:true,arithmeticContracts:4,parameterRows:48,momentProposals:40,documents:docs.length,localLinks:links,
 newChenCutoffProved:false,currentCheckedH:baseline.HApproximate}));
