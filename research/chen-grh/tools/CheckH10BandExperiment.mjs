// Component provenance and research-scope checks. Not a final Chen audit.
import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2]||process.cwd(),dir=path.join(repo,'research/chen-grh'),sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const r=JSON.parse(fs.readFileSync(path.join(dir,'H10_FINITE_BAND_EXPERIMENT.json')));
const checked=JSON.parse(fs.readFileSync(path.join(dir,'H10_BAND_COMPONENT_CHECK.json')));
const baseline=JSON.parse(fs.readFileSync(path.join(dir,'FINAL_GRHSub12_CHEN_AUDIT.json')));
if(r.classification!=='H10_FINITE_BAND_EXPERIMENT_NOT_A_CHEN_PROOF'||r.baselineManifest!==baseline.sourceObjectManifestHash)throw Error('Changed experiment scope or baseline');
if(r.generatorHash!==sha(fs.readFileSync(path.join(dir,'tools/ExperimentH10Bands.mjs')))||r.studyHash!==sha(fs.readFileSync(path.join(dir,'SPECIALIZED_FINITE_SCALE_STUDY.json'))))throw Error('Stale numerical experiment');
if(r.bandCount!==199||r.endpoints.length!==200||r.endpoints[0]!==22026||r.endpoints.at(-1)!==159500)throw Error('Incomplete cover');
for(let i=0;i<r.bandCount;i++)if(r.endpoints[i+1]!==Math.min(159500,Math.ceil(r.endpoints[i]*101/100)))throw Error('Broken band boundary '+i);
if(r.bands.some((b,i)=>b.index!==i||b.lowerLog!==r.endpoints[i]||b.upperLog!==r.endpoints[i+1]||b.candidates.some(c=>c.certifiedChenBand)))throw Error('Incorrect band metadata or false proof claim');
if(r.summary.some(s=>s.provedInteriorBands!==0))throw Error('Unsupported claim of a new Chen band');
const picks=r.bands.map(b=>b.candidates.find(c=>c.package==='H10_keep_existing_endpoint'));
if(picks.some(p=>!p.positiveModel||!p.best||p.best.margin<=0||p.best.actualCountEstimatesProved||!Object.values(p.best.monotonic).every(Boolean)))throw Error('Incomplete conditional numerical fit');
const cover=fs.readFileSync(path.join(dir,'GRHH10BandCover.lean'),'utf8');
const getArray=(s,name)=>{const m=s.match(new RegExp('def '+name+' : Array ℕ := #\\[([^\\]]*)\\]'));if(!m)throw Error('Missing data '+name);return m[1].split(',').map(Number)};
if(JSON.stringify(getArray(cover,'bandEndpoints'))!==JSON.stringify(r.endpoints))throw Error('Lean cover data mismatch');
const budget=fs.readFileSync(path.join(dir,'GRHH10BandBudget.lean'),'utf8');
for(const [name,key]of[['baseNumerators','baseLoss'],['mediumNumerators','mediumLoss'],['radiusNumerators','K'],['pairNumerators','pair']])if(JSON.stringify(getArray(budget,name))!==JSON.stringify(picks.map(p=>Math.round(p.best[key]*1e6))))throw Error('Lean coefficient data mismatch '+name);
if(checked.modules.length!==5||checked.classification!=='H10_BAND_COMPONENTS_KERNEL_CHECKED_INTERIOR_CHEN_UNPROVED')throw Error('Incomplete component verification');
if(checked.manifestHash!==sha(fs.readFileSync(path.join(repo,'lake-manifest.json')))||checked.toolchain!==fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8').trim())throw Error('Changed dependencies');
for(const m of checked.modules){
 const file=path.join(dir,m.module+'.lean');
 if(m.sourceHash!==sha(fs.readFileSync(file))||m.objectHash!==sha(fs.readFileSync(path.join(repo,'.lake/build-434/lib/lean',m.module+'.olean'))))throw Error('Changed checked component '+m.module);
 if(m.axiomSets.some(a=>a.some(x=>!['propext','Classical.choice','Quot.sound'].includes(x))))throw Error('Unexpected component axiom');
 for(const dep of m.importedObjects)if(dep.objectHash!==sha(fs.readFileSync(path.join(repo,'.lake/build-434/lib/lean',dep.module.replaceAll('.','/')+'.olean'))))throw Error('Changed component import '+dep.module);
 const code=fs.readFileSync(file,'utf8').replace(/\/-[\s\S]*?-\//g,'').replace(/--[^\r\n]*/g,'');
 if(/\b(sorry|admit|axiom|native_decide|sorryAx|unsafe|implemented_by|extern|skipKernelTC|trustCompiler)\b/.test(code))throw Error('Forbidden component construct '+m.module);
}
let links=0;
for(const rel of['README.md','research/chen-grh/README.md','research/chen-grh/H10_FINITE_BAND_EXPERIMENT.md']){
 const file=path.join(repo,rel),s=fs.readFileSync(file,'utf8');if(/^.*[ \t]+$/m.test(s))throw Error('Trailing whitespace '+rel);
 for(const m of s.matchAll(/\]\(([^)]+)\)/g)){if(/^(https?:|#)/.test(m[1]))continue;if(!fs.existsSync(path.resolve(path.dirname(file),m[1].split('#')[0])))throw Error('Broken link '+rel+' '+m[1]);links++;}
 for(const m of s.matchAll(/\$\$([\s\S]*?)\$\$|\$([^$\n]+)\$/g)){const t=m[1]??m[2];let n=0;for(let i=0;i<t.length;i++){if(i&&t[i-1]==='\\')continue;if(t[i]==='{')n++;if(t[i]==='}')n--;if(n<0)throw Error('Broken math '+rel);}if(n)throw Error('Broken math '+rel);}
}
console.log(JSON.stringify({passed:true,checkedComponents:5,coveredBands:199,conditionalPositiveBudgets:picks.length,provedInteriorChenBands:0,currentChenH:baseline.HApproximate,localLinks:links}));
