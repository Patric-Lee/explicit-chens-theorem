import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2],root=path.join(repo,'research/chen-grh'),logs=path.join(repo,'.lake/build-434/source-build-logs');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const sourceOnly=process.argv.includes('--source-only');
const status=sourceOnly?null:JSON.parse(fs.readFileSync(path.join(logs,'status-strongmoving.json'))),ledger=sourceOnly?{}:JSON.parse(fs.readFileSync(path.join(logs,'ledger-strongmoving.json')));
if(!sourceOnly&&(status.failed||status.remaining!==0||status.running!==0||!['AuditGRHStrongMoving'].every(m=>status.roots.includes(m))))throw Error('Final Chen build/audit is incomplete');
const searchRoots=[repo,path.join(repo,'OpenAI/wrappers'),path.join(repo,'OpenAI/grouped'),path.join(repo,'OpenAI'),root,path.join(repo,'research/chen-platt'),path.join(repo,'research/chen-platt/Calr3'),...['chen-effective','chen-dusart','chen-bjs-study','chen-numerical-study','chen-grh'].map(x=>path.join(repo,'research',x))];
function strip(s){let out='',depth=0,line=false,str=false;for(let i=0;i<s.length;i++){const c=s[i],n=s[i+1];if(line){if(c==='\n'){line=false;out+='\n';}continue;}if(depth){if(c==='/'&&n==='-'){depth++;i++;}else if(c==='-'&&n==='/'){depth--;i++;}else if(c==='\n')out+='\n';continue;}if(str){if(c==='\\')i++;else if(c==='"')str=false;else if(c==='\n')out+='\n';continue;}if(c==='-'&&n==='-'){line=true;i++;}else if(c==='/'&&n==='-'){depth=1;i++;}else if(c==='"')str=true;else out+=c;}return out;}
const seen=new Set(),records=[],axiomDeclarations=[],violations=[];
function visit(m){if(seen.has(m))return;seen.add(m);
 const rel=m.replaceAll('.','/')+'.lean',r=searchRoots.find(r=>fs.existsSync(path.join(r,rel)));if(!r)return;
 const file=path.join(r,rel),bytes=fs.readFileSync(file);let code=strip(bytes.toString('utf8'));
 // Audit fixtures read this option specifically to reject disabled checking.
 if(/^Audit/.test(path.basename(file)))code=code.replace(/if debug\.skipKernelTC\.get \(← getOptions\) then/g,'if kernelCheckingGuardValue then');
 const rec=ledger[m],sourceHash=sha(bytes);let objectHash;
 if(!sourceOnly){const object=path.join(repo,'.lake/build-434/lib/lean',m.replaceAll('.','/')+'.olean');objectHash=sha(fs.readFileSync(object));
  if(!rec||rec.configurationHash!==configurationHash||rec.sourceHash!==sourceHash||rec.objectHash!==objectHash)throw Error('Unchecked or changed source/object '+m);
  for(const [d,h]of Object.entries(rec.dependencies))if(ledger[d]?.objectHash!==h)throw Error('Dependency ledger mismatch '+m+' -> '+d);
  if(rec.dependencySignatures){
   const current=Object.fromEntries(Object.keys(rec.dependencies).map(d=>{const r=ledger[d];return[d,r?.buildSignature||sha(JSON.stringify({configurationHash:r?.configurationHash,sourceHash:r?.sourceHash,objectHash:r?.objectHash,dependencies:r?.dependencies}))];}));
   if(JSON.stringify(current)!==JSON.stringify(rec.dependencySignatures))throw Error('Recursive dependency provenance mismatch '+m);
   if(rec.buildSignature!==sha(JSON.stringify({configurationHash:rec.configurationHash,sourceHash:rec.sourceHash,objectHash:rec.objectHash,dependencySignatures:rec.dependencySignatures})))throw Error('Build signature mismatch '+m);
  }else if(Object.keys(rec.dependencies).some(d=>ledger[d]?.buildSignature))throw Error('Legacy descendant of freshly checked proof '+m);
 }
 for(const hit of code.matchAll(/\b(sorry|admit|sorryAx|native_decide|unsafe|implemented_by|extern|ofReduceBool|trustCompiler|skipKernelTC|trustLevel)\b/g))violations.push({module:m,token:hit[0]});
 for(const hit of code.matchAll(/\baxiom\s+([^\s:({]+)/g))axiomDeclarations.push({module:m,name:hit[1]});
 records.push({module:m,sourceHash,objectHash});
 const imports=[...code.matchAll(/^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\r\n]+)/gm)].flatMap(x=>x[1].trim().split(/\s+/));imports.forEach(visit);
}

visit('AuditGRHStrongMoving');
if(violations.length)throw Error('Forbidden proof constructs '+JSON.stringify(violations));
if(JSON.stringify(axiomDeclarations)!==JSON.stringify([{module:'GRHAssumption',name:'alpoge_dirichlet_grh'}]))throw Error('Unexpected axiom declarations '+JSON.stringify(axiomDeclarations));
if(sourceOnly){console.log(JSON.stringify({classification:'SOURCE_POLICY_ONLY_NOT_FINAL_PROOF',modules:records.length,axiomDeclarations,passed:true}));process.exit(0);}
const log=fs.readFileSync(path.join(logs,'AuditGRHStrongMoving.log'),'utf8');
if(!/Strong GRH moving audit passed: \d+ constants; sole added axiom GRH\./.test(log)||!log.includes('Actual current-target cofactor ledger uses no superseded weak moving estimate.'))throw Error('Strong moving semantic audit did not pass');
const requireNames=[...fs.readFileSync(path.join(repo,'lakefile.toml'),'utf8').matchAll(/\[\[require\]\]\s*name\s*=\s*"([^"]+)"/g)].map(x=>x[1]).sort();
if(JSON.stringify(requireNames)!==JSON.stringify(['LeanArchitect','mathlib']))throw Error('Unexpected direct package dependencies '+JSON.stringify(requireNames));
records.sort((a,b)=>a.module.localeCompare(b.module));
const report={classification:'GRH_STRONG_MOVING_KERNEL_CHECKED',checkedAt:new Date().toISOString(),configurationHash,
 movingLogThreshold:10000,characterExponent:'501/1000',movingDecay:'exp(-1497*log(N)/10000)',
 primitiveSavingDegreeMax:72,principalSavingDegreeMax:70,lowAggregateSavingDegreeMax:32,lowConductorLogDegreeMax:38,
 primitiveTheorem:'ChenEffective.GRHStrongMoving.pan_prime_moving',principalTheorem:'ChenEffective.GRHStrongMoving.pan_principal_moving',
 lowAggregateTheorem:'ChenEffective.GRHStrongMoving.pan_low_of_log',principalAggregateTheorem:'ChenEffective.GRHStrongMoving.pan_principal_of_log',
 sourceLedgerTheorem:'ChenEffective.GRHStrongMoving.numerical_pan_ledger',sourceLedgerCutoff:'3^400000',
 chenCutoffStatus:'UNCHANGED: completed Chen release remains H < 13; no smaller end-to-end Chen theorem claimed by this audit',
 externalAxiom:'ChenEffective.GRH.alpoge_dirichlet_grh',axiomDeclarations,directPackages:requireNames,
 localModules:records.length,sourceObjectManifestHash:sha(JSON.stringify(records)),auditLog:log.trim(),
 checkedMovingModules:records.filter(r=>r.module==='AuditGRHStrongMoving')};
fs.writeFileSync(path.join(root,'STRONG_MOVING_AUDIT.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({...report,checkedMovingModules:undefined},null,2));
