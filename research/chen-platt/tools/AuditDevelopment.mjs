// Static/provenance audit. Compilation ledgers remain separate evidence.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {fileURLToPath} from 'node:url';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const sha=s=>crypto.createHash('sha256').update(s).digest('hex');
function strip(s){let out='',depth=0,line=false,str=false;for(let i=0;i<s.length;i++){
 const c=s[i],n=s[i+1];
 if(line){if(c==='\n'){line=false;out+='\n';}continue;}
 if(depth){if(c==='/'&&n==='-'){depth++;i++;}else if(c==='-'&&n==='/'){depth--;i++;}continue;}
 if(str){if(c==='\\')i++;else if(c===String.fromCharCode(34))str=false;continue;}
 if(c==='-'&&n==='-'){line=true;i++;}else if(c==='/'&&n==='-'){depth=1;i++;}
 else if(c===String.fromCharCode(34))str=true;else out+=c;
 }return out;}
const manifest=JSON.parse(fs.readFileSync(path.join(root,'source-manifest.json'),'utf8'));
const invalid=[];for(const r of manifest.modules){
 const p=path.join(root,r.adaptedPath),actual=sha(fs.readFileSync(p));
 if(actual!==r.adaptedHash)invalid.push(r.module);
}
const failures=[],sources=[];
function walk(dir){for(const e of fs.readdirSync(dir,{withFileTypes:true})){
 const p=path.join(dir,e.name);if(e.isDirectory())walk(p);else if(e.name.endsWith('.lean')){
  const code=strip(fs.readFileSync(p,'utf8'));sources.push({path:path.relative(root,p).replaceAll('\\','/'),sha256:sha(fs.readFileSync(p))});
  const bad=code.match(/\b(?:axiom|sorry|admit|sorryAx|native_decide|unsafe|implemented_by|ofReduceBool|skipKernelTC)\b/g);
  if(bad)failures.push({file:path.relative(root,p),tokens:[...new Set(bad)]});
 }
}}
walk(root);
const report={scope:'PLATT_DEVELOPMENT_ONLY_NOT_FINAL_CHEN_AUDIT',
 timestamp:new Date().toISOString(),sources:sources.length,portedSources:manifest.modules.length,
 provenanceValid:invalid.length===0,invalid,forbiddenCode:failures,
 pass:invalid.length===0&&failures.length===0,
 mathematicalStatus:'Prefix theorem and final axiom replacement remain unfinished.',
 sourceSnapshot:sources};
fs.writeFileSync(path.join(root,'DEVELOPMENT_AUDIT.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({...report,sourceSnapshot:undefined},null,2));
if(!report.pass)process.exitCode=1;
