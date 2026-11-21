import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2],root=path.join(repo,'research/chen-grh'),logs=path.join(repo,'.lake/build-434/source-build-logs');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const sourceOnly=process.argv.includes('--source-only');
const status=sourceOnly?null:JSON.parse(fs.readFileSync(path.join(logs,'status-grhstrip.json'))),ledger=sourceOnly?{}:JSON.parse(fs.readFileSync(path.join(logs,'ledger-grhstrip.json')));
if(!sourceOnly&&(status.failed||status.remaining!==0||status.running!==0||!['AuditGRH14NumericalLower'].every(m=>status.roots.includes(m))))throw Error('Final Chen build/audit is incomplete');
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

visit('AuditGRH14NumericalLower');
if(violations.length)throw Error('Forbidden proof constructs '+JSON.stringify(violations));
if(JSON.stringify(axiomDeclarations)!==JSON.stringify([{module:'GRHAssumption',name:'alpoge_dirichlet_grh'}]))throw Error('Unexpected axiom declarations '+JSON.stringify(axiomDeclarations));
if(sourceOnly){console.log(JSON.stringify({classification:'SOURCE_POLICY_ONLY_NOT_FINAL_PROOF',modules:records.length,axiomDeclarations,passed:true}));process.exit(0);}
const log=fs.readFileSync(path.join(logs,'AuditGRH14NumericalLower.log'),'utf8');
if(!/GRH H14 numerical lower audit passed: \d+ transitive constants/.test(log)||!log.includes('Actual weighted Chen lower count at 3^1000000; sole added axiom is full Dirichlet GRH.'))throw Error('Semantic numerical lower audit did not pass');
const requireNames=[...fs.readFileSync(path.join(repo,'lakefile.toml'),'utf8').matchAll(/\[\[require\]\]\s*name\s*=\s*"([^"]+)"/g)].map(x=>x[1]).sort();
if(JSON.stringify(requireNames)!==JSON.stringify(['LeanArchitect','mathlib']))throw Error('Unexpected direct package dependencies '+JSON.stringify(requireNames));
records.sort((a,b)=>a.module.localeCompare(b.module));
const report={classification:'GRH_ONLY_H14_NUMERICAL_LOWER_KERNEL_CHECKED',checkedAt:new Date().toISOString(),configurationHash,
 theorem:'ChenEffective.GRH14.weighted_lower',cutoff:'3^1000000',coefficient:'2.02575',HUpperStrict:14,
 baseLoss:'3/50',mediumLoss:'111/100',endpointLoss:'1/20000',presieveStart:4000000,presieveTruncation:'floor(N^(1/200))',distributionLevel:'N^(249/500)',
 externalAxiom:'ChenEffective.GRH.alpoge_dirichlet_grh',axiomDeclarations,directPackages:requireNames,
 H14ExistenceStatus:'NOT_PROVED: the complete Selberg-square estimate remains separate',
 localModules:records.length,sourceObjectManifestHash:sha(JSON.stringify(records)),auditLog:log.trim(),
 numericalLowerModules:records.filter(r=>r.module.startsWith('GRH14')||r.module.startsWith('GRHLower')||r.module==='AuditGRH14NumericalLower')};
fs.writeFileSync(path.join(root,'FINAL_GRH14_LOWER_AUDIT.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({...report,numericalLowerModules:undefined},null,2));
