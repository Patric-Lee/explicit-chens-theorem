import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const repo=process.env.CHEN_REPO||path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
function strip(s){let out='',depth=0,line=false,str=false;for(let i=0;i<s.length;i++){const c=s[i],n=s[i+1];if(line){if(c==='\n'){line=false;out+='\n';}continue;}if(depth){if(c==='/'&&n==='-'){depth++;i++;}else if(c==='-'&&n==='/'){depth--;i++;}else if(c==='\n')out+='\n';continue;}if(str){if(c==='\\')i++;else if(c==='"')str=false;else if(c==='\n')out+='\n';continue;}if(c==='-'&&n==='-'){line=true;i++;out+=' ';}else if(c==='/'&&n==='-'){depth=1;i++;out+=' ';}else if(c==='"'){str=true;out+=' ';}else out+=c;}if(depth||str)throw Error('Unterminated comment/string');return out;}
const roots=['research/chen-effective','research/chen-dusart','research/chen-bjs-study','research/chen-numerical-study','OpenAI'];
const bad=/\b(sorry|admit|sorryAx|native_decide|unsafe|implemented_by|extern|ofReduceBool|trustCompiler|skipKernelTC|trustLevel)\b/g;
let files=0;const axioms=[];const failures=[];
// The audit fixtures READ this option and reject disabled kernel checking.
// Mask that exact getter only in the scan copy; never change any Lean source.
function scan(dir){for(const e of fs.readdirSync(dir,{withFileTypes:true})){const p=path.join(dir,e.name);if(e.isDirectory()){if(!e.name.startsWith('.')&&!e.name.startsWith('hybrid-pilot'))scan(p);}else if(e.name.endsWith('.lean')){files++;let code=strip(fs.readFileSync(p,'utf8'));if(/^Audit/.test(e.name))code=code.replace(/if debug\.skipKernelTC\.get \(← getOptions\) then/g,'if kernelCheckingGuardValue then');for(const m of code.matchAll(bad))failures.push({file:path.relative(repo,p),token:m[0]});for(const m of code.matchAll(/\baxiom\s+(\S+)/g))axioms.push({file:path.relative(repo,p),name:m[1]});}}}
roots.forEach(r=>scan(path.join(repo,r)));
const expected=process.argv.includes('--dirichlet-proved')?['temporary_reciprocal_prefix_window']:['dirichlet_seven_eighths','temporary_reciprocal_prefix_window'];
for(const a of axioms)if(!expected.includes(a.name))failures.push(a);
for(const n of expected)if(axioms.filter(a=>a.name===n).length!==1)failures.push({missingOrDuplicate:n});
console.log(JSON.stringify({files,axioms,failures,passed:failures.length===0},null,2));
if(failures.length)process.exitCode=1;
