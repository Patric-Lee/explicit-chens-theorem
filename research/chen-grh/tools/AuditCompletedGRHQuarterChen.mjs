// Record a successful direct Lean campaign and verify every imported local artifact.
import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=path.resolve(process.argv[2]||process.cwd()),root=path.join(repo,'research/chen-grh');
const logs=path.join(repo,'.lake/build-434/source-build-logs'),objects=path.join(repo,'.lake/build-434/lib/lean');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const configurationHash=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const auditLog=fs.readFileSync(path.join(logs,'AuditGRHQuarterChen.log'),'utf8');
const match=auditLog.match(/Quarter Chen full audit passed: (\d+) transitive constants/);
if(!match||/error:|sorryAx|Unexpected|Unlisted|Forbidden proof dependency|Unsafe proof dependency/.test(auditLog)||!auditLog.includes('Literal original Chen recovery checked'))throw Error('The full semantic Chen audit has not passed');
const searchRoots=[repo,path.join(repo,'OpenAI/wrappers'),path.join(repo,'OpenAI/grouped'),path.join(repo,'OpenAI'),path.join(repo,'research/chen-platt'),path.join(repo,'research/chen-platt/Calr3'),...['chen-effective','chen-dusart','chen-bjs-study','chen-numerical-study','chen-grh'].map(s=>path.join(repo,'research',s))];
const locate=m=>{const rel=m.replaceAll('.','/')+'.lean';const r=searchRoots.find(r=>fs.existsSync(path.join(r,rel)));return r&&path.join(r,rel)};
function strip(s){let out='',depth=0,line=false,str=false;for(let i=0;i<s.length;i++){const c=s[i],n=s[i+1];if(line){if(c==='\n'){line=false;out+='\n';}continue;}if(depth){if(c==='/'&&n==='-'){depth++;i++;}else if(c==='-'&&n==='/'){depth--;i++;}else if(c==='\n')out+='\n';continue;}if(str){if(c==='\\')i++;else if(c==='"')str=false;else if(c==='\n')out+='\n';continue;}if(c==='-'&&n==='-'){line=true;i++;}else if(c==='/'&&n==='-'){depth=1;i++;}else if(c==='"')str=true;else out+=c;}if(depth||str)throw Error('Unterminated source string/comment');return out;}
const imports=s=>[...strip(s).matchAll(/^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\r\n]+)/gm)].flatMap(m=>m[1].trim().split(/\s+/));
const primary=fs.existsSync(path.join(logs,'ledger-grhquarterchen.json'))?'ledger-grhquarterchen.json':'ledger-grhsubtwelve.json';
const ledger=JSON.parse(fs.readFileSync(path.join(logs,primary)));
for(const tag of ['grhquarter','quarterassembly']){
 if(!fs.existsSync(path.join(logs,'ledger-'+tag+'.json')))continue;
 const rows=JSON.parse(fs.readFileSync(path.join(logs,'ledger-'+tag+'.json')));
 for(const [n,r]of Object.entries(rows))if(!ledger[n])ledger[n]=r;
}
const fresh=['GRHQuarterTruncatedBounds','GRHQuarterChenCore','GRHQuarterChenLower','GRHQuarterChenPair','GRHQuarterChenPan','GRHQuarterChenAnalytic','GRHQuarterChenEndpoint','AuditGRHQuarterChen'];
const fallback=r=>sha(JSON.stringify({configurationHash:r.configurationHash,sourceHash:r.sourceHash,objectHash:r.objectHash,dependencies:r.dependencies}));
for(const m of fresh){
 const source=locate(m),object=path.join(objects,m.replaceAll('.','/')+'.olean');
 const log=fs.readFileSync(path.join(logs,m+'.log'),'utf8');
 if(/error:|sorryAx|declaration uses `sorry`/.test(log)||fs.statSync(object).mtimeMs<fs.statSync(source).mtimeMs)throw Error('Failed or stale direct check '+m);
 const dependencies=Object.fromEntries(imports(fs.readFileSync(source,'utf8')).filter(locate).map(d=>[d,sha(fs.readFileSync(path.join(objects,d.replaceAll('.','/')+'.olean')))]));
 const dependencySignatures=Object.fromEntries(Object.keys(dependencies).map(d=>{const r=ledger[d];if(!r||r.objectHash!==dependencies[d])throw Error('Missing checked direct parent '+m+' -> '+d);return[d,r.buildSignature||fallback(r)]}));
 const sourceHash=sha(fs.readFileSync(source)),objectHash=sha(fs.readFileSync(object));
 ledger[m]={configurationHash,sourceHash,objectHash,dependencies,dependencySignatures,
  buildSignature:sha(JSON.stringify({configurationHash,sourceHash,objectHash,dependencySignatures})),
  verification:'direct pinned Lean kernel check; final complete transitive audit',logHash:sha(log)};
}
const seen=new Set(),records=[],axiomDeclarations=[];
function visit(m){
 if(seen.has(m))return;seen.add(m);const file=locate(m);if(!file)return;
 const bytes=fs.readFileSync(file),sourceHash=sha(bytes),objectHash=sha(fs.readFileSync(path.join(objects,m.replaceAll('.','/')+'.olean'))),rec=ledger[m];
 if(!rec||rec.configurationHash!==configurationHash||rec.sourceHash!==sourceHash||rec.objectHash!==objectHash)throw Error('Unchecked or changed source/object '+m);
 for(const [d,h]of Object.entries(rec.dependencies))if(ledger[d]?.objectHash!==h)throw Error('Dependency mismatch '+m+' -> '+d);
 if(rec.dependencySignatures){
  const current=Object.fromEntries(Object.keys(rec.dependencies).map(d=>[d,ledger[d].buildSignature||fallback(ledger[d])]));
  if(JSON.stringify(current)!==JSON.stringify(rec.dependencySignatures)||rec.buildSignature!==sha(JSON.stringify({configurationHash,sourceHash,objectHash,dependencySignatures:current})))throw Error('Recursive provenance mismatch '+m);
 }else if(Object.keys(rec.dependencies).some(d=>ledger[d]?.buildSignature))throw Error('Legacy descendant of a new proof '+m);
 let code=strip(bytes.toString('utf8'));if(/^Audit/.test(path.basename(file)))code=code.replace(/if debug\.skipKernelTC\.get \(← getOptions\) then/g,'if kernelCheckingGuardValue then');
 const bad=code.match(/\b(sorry|admit|sorryAx|native_decide|unsafe|implemented_by|extern|ofReduceBool|trustCompiler|skipKernelTC|trustLevel)\b/);if(bad)throw Error('Forbidden source construct '+m+': '+bad[0]);
 for(const hit of code.matchAll(/\baxiom\s+([^\s:({]+)/g))axiomDeclarations.push({module:m,name:hit[1]});
 records.push({module:m,sourceHash,objectHash});
 for(const d of imports(bytes.toString('utf8')))visit(d);
}
visit('AuditGRHQuarterChen');
if(JSON.stringify(axiomDeclarations)!==JSON.stringify([{module:'GRHAssumption',name:'alpoge_dirichlet_grh'}]))throw Error('Unexpected source axioms');
const manifest=JSON.parse(fs.readFileSync(path.join(repo,'lake-manifest.json')));
const directPackages=manifest.packages.filter(p=>!p.inherited).map(p=>p.name).sort();
if(JSON.stringify(directPackages)!==JSON.stringify(['LeanArchitect','mathlib'])||manifest.packages.find(p=>p.name==='mathlib').rev!=='d13f23b723b8a846827a245b89c10fc7d3f11612'||fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8').trim()!=='leanprover/lean4:v4.34.1')throw Error('Pinned dependencies changed');
records.sort((a,b)=>a.module.localeCompare(b.module));
const quarterData=JSON.parse(fs.readFileSync(path.join(root,'GRHQuarterMomentData.json')));
const quarterCertificates=records.filter(r=>r.module.startsWith('GRHQuarterCertificates.'));
if(quarterCertificates.length!==508)throw Error('Missing quarter certificates');
for(const r of quarterData.rows)if(quarterCertificates.find(c=>c.module===r.module)?.sourceHash!==r.sourceHash)throw Error('Changed finite proposal data '+r.module);
const report={classification:'GRH_ONLY_QUARTER_MOMENT_COMPLETE_CHEN_KERNEL_CHECKED',checkedAt:new Date().toISOString(),configurationHash,
 theorem:'ChenEffective.GRHQuarterChen.chen_explicit',lowerTheorem:'ChenEffective.GRHQuarterChen.weighted_lower',tripleTheorem:'ChenEffective.GRHQuarterChen.triple_upper',originalTheorem:'ChenEffective.GRHQuarterChen.original_chen',
 cutoff:'3^119081',HUpperStrict:'5891/500',HApproximate:Math.log(119081*Math.log(3)),logLowerBound:130690,
 lowerCoefficient:'2.00825',tripleCoefficient:'4.015',representationMargin:'3/4000',
 momentLogCap:'1799/100',momentCertificateCount:508,rankinExponent:'1/4',presieveStart:4000000,presieveTruncation:'floor(N^(13/2500))',distributionLevel:'N^(1241/2500)',
 sourceUpperParameter:2977,sourceUpperAllowance:'21/1000',sourceLowerParameter:20000000,
 selbergCoefficient:'8.059',pairProxyCoefficient:'0.49674',pairMainCoefficient:'0.498',squareAllowance:'1/1000',tripleResidualAllowance:'1/3000',
 baseLoss:'63/1000',mediumLoss:'1139/1000',endpointLoss:'1/20000',
 minimumScope:'Certified minimum within the displayed source-accuracy/counting package; no global optimality claim.',
 minimumTheorem:'ChenEffective.GRHQuarterChen.source_accuracy_exponent_minimal',unprovedH10TargetsUsed:false,
 externalAxiom:'ChenEffective.GRH.alpoge_dirichlet_grh',axiomDeclarations,directPackages,
 transitiveConstants:Number(match[1]),localModules:records.length,sourceObjectManifestHash:sha(JSON.stringify(records)),
 auditLog,numericalModules:records.filter(r=>fresh.includes(r.module)),quarterCertificates,
 predecessorManifest:'97f53dc5e455a510a078050be2ce10dec838bba36fbd6e3adb52cea7c399efa8'};
fs.writeFileSync(path.join(root,'FINAL_GRH_QUARTER_CHEN_AUDIT.json'),JSON.stringify(report,null,2)+'\n');
fs.writeFileSync(path.join(logs,'ledger-grhquarterchen.json'),JSON.stringify(ledger,null,2)+'\n');
console.log(JSON.stringify({passed:true,cutoff:report.cutoff,HApproximate:report.HApproximate,HUpperStrict:11.782,localModules:records.length,transitiveConstants:report.transitiveConstants,newAxioms:0,nativeDecide:false}));
