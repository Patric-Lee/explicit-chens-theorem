// Only module boundaries/imports are reorganized. Every proof body is retained
// and subsequently typechecked by Lean; no generator output is trusted.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {fileURLToPath} from 'node:url';
const repo=process.env.CHEN_REPO||path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
const base=path.join(repo,'OpenAI'),size=Number(process.argv[2]||40);
const manifests=['source-manifest.json','rellich-source-manifest.json'].map(n=>JSON.parse(fs.readFileSync(path.join(base,n))));
const originals=Object.assign({},...manifests.map(m=>m.modules));
// Grouping exposes extra sibling declarations. Resolve the intended existing
// alias locally; retain every original proof body byte-for-byte.
const localNameResolutions={
 'OAI.NumberTheory.DirichletL.PrimeRows.Character':{PrimeIdeal:'OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal'}
};
const qualifiedNames={
 'OAI.NumberTheory.DirichletL.Detector.HighRowsRegion':{sourceRowSeries:'OAI.SevenEighths.ProbeEuler.sourceRowSeries'},
 'OAI.NumberTheory.DirichletL.PrimeRows.Ramified':{sourceRowSeries:'OAI.SevenEighths.ProbeEuler.sourceRowSeries'}
};
const nodes=new Map(),seen=new Set(),active=new Set(),order=[];
const digest=s=>crypto.createHash('sha256').update(s).digest('hex');
function scopeBalance(source){
 let code='',depth=0,line=false,str=false;
 for(let i=0;i<source.length;i++){const c=source[i],n=source[i+1];if(line){if(c==='\n'){line=false;code+='\n';}continue;}if(depth){if(c==='/'&&n==='-'){depth++;i++;}else if(c==='-'&&n==='/'){depth--;i++;}else if(c==='\n')code+='\n';continue;}if(str){if(c==='\\')i++;else if(c==='"')str=false;else if(c==='\n')code+='\n';continue;}if(c==='-'&&n==='-'){line=true;i++;}else if(c==='/'&&n==='-'){depth=1;i++;}else if(c==='"')str=true;else code+=c;}
 let balance=0;for(const l of code.split('\n')){if(/^\s*(?:namespace\s|(?:noncomputable\s+)?section(?:\s|$))/.test(l))balance++;else if(/^\s*end(?:\s|$)/.test(l))balance--;if(balance<0)throw Error('Unbalanced source scope');}return balance;
}
function visit(n){if(seen.has(n)||!originals[n])return;if(active.has(n))throw Error('cycle '+n);active.add(n);
 const source=fs.readFileSync(path.join(base,originals[n].path),'utf8');
 const imports=[...source.matchAll(/^import\s+([^\r\n]+)/gm)].map(m=>m[1].trim());
 nodes.set(n,{name:n,source,imports,sha256:digest(source)});
 imports.forEach(visit);active.delete(n);seen.add(n);order.push(n);
}
visit('OAI.NumberTheory.DirichletL.Nonvanishing');
const groupOf=new Map(order.map((n,i)=>[n,Math.floor(i/size)]));
const root=path.join(base,'grouped'),units=[];
for(let start=0;start<order.length;start+=size){
 const i=start/size,name='OpenAIGrouped.Unit'+String(i).padStart(3,'0'),names=order.slice(start,start+size),imports=new Set();
 let body='';
 for(let j=0;j<names.length;j++){
  const v=nodes.get(names[j]);
  for(const dep of v.imports){if(groupOf.has(dep)){const k=groupOf.get(dep);if(k!==i)imports.add('OpenAIGrouped.Unit'+String(k).padStart(3,'0'));}else imports.add(dep);}
  let source=v.source.replace(/^import\s+[^\r\n]+[\r\n]+/gm,'');
  for(const [short,full] of Object.entries(qualifiedNames[v.name]||{}))
    source=source.replace(new RegExp('(?<![\\w.])'+short+'(?![\\w])','gu'),full);
  if(start+j>=1062 && /\bPrimeIdeal\b/.test(source) && !/\b(?:abbrev|def|structure|class|inductive) PrimeIdeal\b/.test(source))
    localNameResolutions[v.name]={...localNameResolutions[v.name],PrimeIdeal:'OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal'};
  const resolutions=Object.entries(localNameResolutions[v.name]||{}).map(([short,full])=>`local notation "${short}" => ${full}\n`).join('');
  body+=`\n/- Original source: ${originals[v.name].path}; sha256: ${v.sha256} -/\nsection Source${start+j}\n${resolutions}${source}\n${'end\n'.repeat(scopeBalance(source))}end Source${start+j}\n`;
 }
 const text=[...imports].map(n=>'import '+n).join('\n')+'\n\nset_option autoImplicit false\nset_option maxHeartbeats 3000000\n'+body;
 const rel=name.replaceAll('.','/')+'.lean',file=path.join(root,rel);fs.mkdirSync(path.dirname(file),{recursive:true});fs.writeFileSync(file,text);
 units.push({module:name,path:rel,sha256:digest(text),sourceModules:names,imports:[...imports]});
}
const wrappers=path.join(base,'wrappers','OAI');fs.mkdirSync(path.join(wrappers,'NumberTheory','DirichletL'),{recursive:true});
fs.writeFileSync(path.join(wrappers,'NumberTheory','DirichletL','Nonvanishing.lean'),
 `/- The original proof bodies are kernel-checked in the generated units. -/\nimport ${units.at(-1).module}\n`);
for(const n of ['ChenDirichlet','AuditChenDirichlet'])fs.copyFileSync(path.join(base,'OAI',n+'.lean'),path.join(wrappers,n+'.lean'));
fs.writeFileSync(path.join(base,'grouped-manifest.json'),JSON.stringify({format:1,groupSize:size,sourceModuleCount:order.length,localNameResolutions,qualifiedNames,units,
 sourceHashes:Object.fromEntries(order.map(n=>[n,nodes.get(n).sha256])),root:units.at(-1).module},null,2)+'\n');
let lake=fs.readFileSync(path.join(repo,'lakefile.toml'),'utf8');
lake=lake.replace('name = "OAI"\nsrcDir = "OpenAI"','name = "OAI"\nsrcDir = "OpenAI/wrappers"');
if(!lake.includes('name = "OpenAIGrouped"'))lake+=`\n[[lean_lib]]\nname = "OpenAIGrouped"\nsrcDir = "OpenAI/grouped"\nroots = ["${units.at(-1).module}"]\nglobs = ["OpenAIGrouped.+"]\nleanOptions = { autoImplicit = false }\n`;
fs.writeFileSync(path.join(repo,'lakefile.toml'),lake);
console.log(JSON.stringify({sourceModules:order.length,units:units.length,root:units.at(-1).module}));
