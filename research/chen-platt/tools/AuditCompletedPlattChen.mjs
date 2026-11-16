import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt'),logs=path.join(repo,'.lake/build-434/source-build-logs');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
// Module grouping is only a compilation optimization: authenticate the
// retained source bodies and the exact checked group/wrappers independently.
const groupDir=path.join(repo,'research/chen-numerical-study/proof-sources/H30Conditional');
const group=JSON.parse(fs.readFileSync(path.join(groupDir,'manifest.json')));
const numericalDir=path.join(repo,'research/chen-numerical-study');
const groupedText=fs.readFileSync(path.join(numericalDir,group.target+'.lean'),'utf8');
const lf=x=>x.replaceAll('\r\n','\n');
if(sha(group.normalizedGroupHash?lf(groupedText):groupedText)!==(group.normalizedGroupHash||group.groupHash))throw Error('Grouped Chen source changed');
for(const r of group.sources){
 const original=fs.readFileSync(path.join(groupDir,r.module+'.lean'),'utf8');
 const body=original.replace(/^import\s+[^\r\n]+[\r\n]+/gm,'');
 if(sha(r.normalizedSourceHash?lf(original):original)!==(r.normalizedSourceHash||r.sourceHash)||sha(r.normalizedBodyHash?lf(body):body)!==(r.normalizedBodyHash||r.bodyHash))throw Error('Original grouped source changed '+r.module);
 const exact=`section ${r.section}\n${body}\n${'end\n'.repeat(r.closedScopes)}end ${r.section}\n`;
 if(!lf(groupedText).includes(lf(exact)))throw Error('Original proof body not retained '+r.module);
}
for(const [m,h]of Object.entries(group.normalizedWrappers||group.wrappers)){const s=fs.readFileSync(path.join(numericalDir,m+'.lean'),'utf8');if(sha(group.normalizedWrappers?lf(s):s)!==h)throw Error('Grouped wrapper changed '+m);}
const configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const sourceOnly=process.argv.includes('--source-only');
const status=sourceOnly?null:JSON.parse(fs.readFileSync(path.join(logs,'status-finalplatt.json'))),ledger=sourceOnly?{}:JSON.parse(fs.readFileSync(path.join(logs,'ledger-finalplatt.json')));
if(!sourceOnly&&(status.failed||status.remaining!==0||status.running!==0||!['AuditBJSH30Conditional','AuditBJSTightBudget','OAI.AuditChenIntegration'].every(m=>status.roots.includes(m))))throw Error('Final Chen build/audit is incomplete');
const searchRoots=[repo,path.join(repo,'OpenAI/wrappers'),path.join(repo,'OpenAI/grouped'),path.join(repo,'OpenAI'),root,path.join(root,'Calr3'),...['chen-effective','chen-dusart','chen-bjs-study','chen-numerical-study'].map(x=>path.join(repo,'research',x))];
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
visit('AuditBJSH30Conditional');
if(violations.length)throw Error('Forbidden proof constructs '+JSON.stringify(violations));
if(JSON.stringify(axiomDeclarations)!==JSON.stringify([{module:'PlattAssumption',name:'platt_modulus_one_finite_RH'}]))throw Error('Unexpected local axiom declarations '+JSON.stringify(axiomDeclarations));
if(sourceOnly){console.log(JSON.stringify({classification:'SOURCE_POLICY_ONLY_NOT_FINAL_PROOF',modules:records.length,axiomDeclarations,violations,passed:true}));process.exit(0);}
const log=fs.readFileSync(path.join(logs,'AuditBJSH30Conditional.log'),'utf8');
if(!/Platt H30 Chen audit passed: \d+ transitive constants/.test(log)||!log.includes('Exactly Platt modulus-one finite RH through 1e8 and standard Lean axioms'))throw Error('Final semantic audit did not pass');
const integrationLog=fs.readFileSync(path.join(logs,'OAI.AuditChenIntegration.log'),'utf8');
if(!integrationLog.includes('Chen integration audit passed: Dirichlet is proved; both literal old Chen statements recovered.'))throw Error('Combined Chen integration audit did not pass');
const integrationModule='OAI.AuditChenIntegration',integrationRecord=ledger[integrationModule];
if(!integrationRecord||integrationRecord.configurationHash!==configurationHash||integrationRecord.sourceHash!==sha(fs.readFileSync(path.join(repo,'OpenAI/wrappers/OAI/AuditChenIntegration.lean')))||integrationRecord.objectHash!==sha(fs.readFileSync(path.join(repo,'.lake/build-434/lib/lean/OAI/AuditChenIntegration.olean'))))throw Error('Combined audit source/object mismatch');
const requireNames=[...fs.readFileSync(path.join(repo,'lakefile.toml'),'utf8').matchAll(/\[\[require\]\]\s*name\s*=\s*"([^"]+)"/g)].map(x=>x[1]).sort();
if(JSON.stringify(requireNames)!==JSON.stringify(['LeanArchitect','mathlib']))throw Error('Unexpected direct package dependency '+requireNames);
records.sort((a,b)=>a.module.localeCompare(b.module));
const report={classification:'PLATT_ONLY_H30_CHEN_KERNEL_CHECKED',checkedAt:new Date().toISOString(),configurationHash,
 cutoff:'3^(10^13)',H:30.02765403654,theorem:'ChenEffective.H30Conditional.chen',original:'ChenEffective.H30Conditional.original_chen',
 externalAxiom:'ChenEffective.PlattWindow.platt_modulus_one_finite_RH',finiteRHHeight:100000000,
 finiteWindow:[4000000,10000000000],finiteAllowance:'1/20000',prefixAllowance:'1/9000',
 localModules:records.length,sourceObjectManifestHash:sha(JSON.stringify(records)),axiomDeclarations,directPackages:requireNames,
 groupedProofSources:{manifestHash:sha(fs.readFileSync(path.join(groupDir,'manifest.json'))),sourceModules:group.sources.length,bodyPreservationChecked:true},
 auditLog:log.trim(),integrationAudit:{module:integrationModule,sourceHash:integrationRecord.sourceHash,objectHash:integrationRecord.objectHash,log:integrationLog.trim()},records};
fs.writeFileSync(path.join(root,'FINAL_CHEN_AUDIT.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({...report,records:undefined},null,2));
