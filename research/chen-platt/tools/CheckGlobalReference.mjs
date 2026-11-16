// Check the final semantic wrapper against the two just-checked parent roots.
// This avoids reparsing 76,265 unchanged sources for a second graph traversal.
import fs from 'node:fs';import path from 'node:path';import os from 'node:os';import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';
import {pathToFileURL} from 'node:url';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt'),build=path.join(repo,'.lake/build-434'),logs=path.join(build,'source-build-logs');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const {atomicJson}=await import(pathToFileURL(path.join(repo,'OpenAI/tools/atomic-json.mjs')).href);
const config=sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8'));
const object=m=>path.join(build,'lib/lean',m.replaceAll('.','/'))+'.olean';
const parents=[['PlattGlobalBoundSoundness','globalboundsound'],['PlattGlobalTotals.L2B0000','globaltotals']];
const dependencies={};
for(const [m,tag] of parents){
 const state=JSON.parse(fs.readFileSync(path.join(logs,'status-'+tag+'.json'))),r=JSON.parse(fs.readFileSync(path.join(logs,'ledger-'+tag+'.json')))[m];
 if(state.failed||state.remaining!==0||state.running!==0||!state.roots.includes(m))throw Error('Parent source build not complete '+m);
 if(!r||r.configurationHash!==config||r.sourceHash!==sha(fs.readFileSync(path.join(root,m.replaceAll('.','/')+'.lean')))||r.objectHash!==sha(fs.readFileSync(object(m))))throw Error('Parent hash mismatch '+m);
 dependencies[m]=r.objectHash;
}
const bin=path.join(process.env.ELAN_HOME||path.join(os.homedir(),'.elan'),'toolchains/leanprover--lean4---v4.34.1/bin');
const executable=n=>path.join(bin,n+(process.platform==='win32'?'.exe':''));
const envResult=spawnSync(executable('lake'),['env','node','-p','process.env.LEAN_PATH'],{cwd:repo,windowsHide:true,encoding:'utf8'});
if(envResult.status!==0)throw Error(envResult.stderr||envResult.stdout);
const m='PlattGlobalReference',file=path.join(root,m+'.lean'),sourceHash=sha(fs.readFileSync(file));
console.log(JSON.stringify({checking:m,parents:Object.keys(dependencies),mode:'ordinary Lean kernel against checked parent artifacts'}));
const start=Date.now();
const result=spawnSync(executable('lean'),['-j1','-M8192','-DmaxHeartbeats=3000000','-DmaxRecDepth=4096','-R',root,'-o',object(m),file],
 {cwd:repo,windowsHide:true,encoding:'utf8',maxBuffer:10000000,env:{...process.env,LEAN_PATH:path.join(build,'lib/lean')+path.delimiter+envResult.stdout.trim(),LEAN_NUM_THREADS:'1'}});
const log=(result.stdout??'')+(result.stderr??'');fs.writeFileSync(path.join(logs,m+'.log'),log);
if(result.error||result.status!==0||/sorryAx|declaration uses `sorry`/.test(log))throw Error(log||String(result.error||result.status));
const match=log.match(/depends on axioms:\s*\[([^\]]*)\]/s);
const axioms=match?match[1].split(',').map(s=>s.trim()).sort():[];
if(JSON.stringify(axioms)!==JSON.stringify(['Classical.choice','Quot.sound','propext'].sort()))throw Error('Unexpected axiom report: '+JSON.stringify(axioms));
const r={configurationHash:config,sourceHash,objectHash:sha(fs.readFileSync(object(m))),dependencies,seconds:(Date.now()-start)/1000};
atomicJson(path.join(logs,'ledger-globalreference.json'),{[m]:r});
atomicJson(path.join(logs,'status-globalreference.json'),{roots:[m],complete:1,cached:0,running:0,failed:false,remaining:0});
console.log(log.trim());console.log(JSON.stringify({verified:m,seconds:r.seconds,objectHash:r.objectHash}));
