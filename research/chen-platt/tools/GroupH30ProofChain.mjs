// Source-only module-boundary optimization. Lean still checks every proof.
import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2],dir=path.join(repo,'research/chen-numerical-study');
const names=['Geometry','Goldbach','MediumPrimeGrid','MediumPrimeSum','MediumPrimeShift','MediumReciprocal','Base','Medium','Aggregate','Chen'].map(x=>'BJSH30Conditional'+x);
const members=new Set(names),target=names.at(-1),backup=path.join(dir,'proof-sources/H30Conditional');
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const lf=x=>x.replaceAll('\r\n','\n');
function strip(s){let out='',depth=0,line=false,str=false;for(let i=0;i<s.length;i++){const c=s[i],n=s[i+1];if(line){if(c==='\n'){line=false;out+='\n';}continue;}if(depth){if(c==='/'&&n==='-'){depth++;i++;}else if(c==='-'&&n==='/'){depth--;i++;}else if(c==='\n')out+='\n';continue;}if(str){if(c==='\\')i++;else if(c==='"')str=false;else if(c==='\n')out+='\n';continue;}if(c==='-'&&n==='-'){line=true;i++;}else if(c==='/'&&n==='-'){depth=1;i++;}else if(c==='"')str=true;else out+=c;}return out;}
const imports=s=>[...strip(s).matchAll(/^\s*import\s+([^\r\n]+)/gm)].flatMap(m=>m[1].trim().split(/\s+/));
const sources=names.map(name=>({name,source:fs.readFileSync(path.join(dir,name+'.lean'),'utf8')}));
if(fs.existsSync(backup))throw Error('Backup already exists; refuse to overwrite originals');
const roots=[repo,path.join(repo,'OpenAI/wrappers'),path.join(repo,'OpenAI/grouped'),path.join(repo,'OpenAI'),path.join(repo,'research/chen-platt'),path.join(repo,'research/chen-platt/Calr3'),...['chen-effective','chen-dusart','chen-bjs-study','chen-numerical-study'].map(x=>path.join(repo,'research',x))];
const external=[...new Set(sources.flatMap(x=>imports(x.source)).filter(x=>!members.has(x)))];
const seen=new Set();function visit(n){if(members.has(n))throw Error('External dependency imports grouped member '+n);if(seen.has(n))return;seen.add(n);const rel=n.replaceAll('.','/')+'.lean',r=roots.find(r=>fs.existsSync(path.join(r,rel)));if(r)imports(fs.readFileSync(path.join(r,rel),'utf8')).forEach(visit);}
external.forEach(visit);
let combined=external.map(n=>'import '+n).join('\n')+'\n\n/- The original proof bodies below are rechecked together to avoid repeated\nlarge certificate imports. Source mapping: proof-sources/H30Conditional/manifest.json. -/\n';
const records=[];
for(let i=0;i<sources.length;i++){
 const {name,source}=sources[i];
 for(const dep of imports(source))if(members.has(dep)&&names.indexOf(dep)>=i)throw Error('Not topological '+name+' -> '+dep);
 const body=source.replace(/^import\s+[^\r\n]+[\r\n]+/gm,'');let balance=0;
 for(const l of strip(body).split('\n')){if(/^\s*(?:namespace\s|(?:noncomputable\s+)?section(?:\s|$))/.test(l))balance++;else if(/^\s*end(?:\s|$)/.test(l))balance--;if(balance<0)throw Error('Scope underflow '+name);}
 const section='H30ProofUnit'+i;
 combined+=`\n/- Original module ${name}; sha256 ${sha(source)}. -/\nsection ${section}\n${body}\n${'end\n'.repeat(balance)}end ${section}\n`;
 records.push({module:name,sourceHash:sha(source),bodyHash:sha(body),normalizedSourceHash:sha(lf(source)),normalizedBodyHash:sha(lf(body)),closedScopes:balance,section});
}
fs.mkdirSync(backup,{recursive:true});
for(const {name,source}of sources)fs.writeFileSync(path.join(backup,name+'.lean'),source);
fs.writeFileSync(path.join(dir,target+'.lean'),combined);
for(const name of names.slice(0,-1))fs.writeFileSync(path.join(dir,name+'.lean'),`/- Original source retained in proof-sources/H30Conditional/${name}.lean.\nIts unchanged proof body is checked in the shared compilation unit. -/\nimport ${target}\n`);
const manifest={format:2,reason:'Fresh kernel checking of the complete downstream chain after replacing the prefix axiom; bounded repeated imports.',target,externalImports:external,preflightModules:seen.size,groupHash:sha(combined),normalizedGroupHash:sha(lf(combined)),sources:records,wrappers:Object.fromEntries(names.slice(0,-1).map(n=>[n,sha(fs.readFileSync(path.join(dir,n+'.lean')))])),normalizedWrappers:Object.fromEntries(names.slice(0,-1).map(n=>[n,sha(lf(fs.readFileSync(path.join(dir,n+'.lean'),'utf8')))]))};
fs.writeFileSync(path.join(backup,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');
console.log(JSON.stringify({grouped:names,externalImports:external.length,preflightModules:seen.size,bytes:combined.length,hash:manifest.groupHash}));
