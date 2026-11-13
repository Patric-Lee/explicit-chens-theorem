import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {fileURLToPath} from 'node:url';
const here=path.dirname(fileURLToPath(import.meta.url));
const repo=process.env.CHEN_REPO||path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
const base=path.join(repo,'OpenAI');
const hash=s=>crypto.createHash('sha256').update(s).digest('hex');
const original=JSON.parse(fs.readFileSync(path.join(base,'source-manifest.json')));
const rellich=JSON.parse(fs.readFileSync(path.join(base,'rellich-source-manifest.json')));
const grouped=JSON.parse(fs.readFileSync(path.join(base,'grouped-manifest.json')));
let pinned=0,bodyCount=0;
for(const v of Object.values(original.modules)){
 if(hash(fs.readFileSync(path.join(base,v.path)))!==v.sha256)throw Error('Pinned OAI source drift: '+v.path);
 pinned++;
}
const all={...original.modules,...rellich.modules};
for(const u of grouped.units){
 const text=fs.readFileSync(path.join(base,'grouped',u.path),'utf8');
 if(hash(text)!==u.sha256)throw Error('Generated unit drift: '+u.path);
 for(const n of u.sourceModules){
  const source=fs.readFileSync(path.join(base,all[n].path),'utf8');
  if(hash(source)!==grouped.sourceHashes[n])throw Error('Source-map drift: '+n);
  let body=source.replace(/^import\s+[^\r\n]+[\r\n]+/gm,'');
  for(const [short,full] of Object.entries(grouped.qualifiedNames?.[n]||{}))
    body=body.replace(new RegExp('(?<![\\w.])'+short+'(?![\\w])','gu'),full);
  if(!text.includes(body))throw Error('Original proof body absent: '+n);
  bodyCount++;
 }
}
if(bodyCount!==grouped.sourceModuleCount)throw Error('Incomplete grouped closure');
for(const n of ['ChenDirichlet','AuditChenDirichlet'])if(
 fs.readFileSync(path.join(base,'OAI',n+'.lean'),'utf8')!==fs.readFileSync(path.join(base,'wrappers','OAI',n+'.lean'),'utf8'))throw Error('Adapter/audit wrapper drift: '+n);
console.log(JSON.stringify({verified:true,pinnedRevision:original.revision,pinnedOAIModules:pinned,retainedProofBodies:bodyCount,generatedUnits:grouped.units.length,doesNotReplaceKernelAudit:true}));
