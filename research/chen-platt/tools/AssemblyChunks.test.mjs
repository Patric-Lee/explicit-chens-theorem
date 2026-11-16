import test from 'node:test';import assert from 'node:assert/strict';
import fs from 'node:fs';import os from 'node:os';import path from 'node:path';import zlib from 'node:zlib';import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';import {fileURLToPath} from 'node:url';
import {batchPlan,generateBatch} from './AssemblyPlan.mjs';
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
test('all stage plans cover their domains without a gap or overlap',()=>{
 for(const [kind,total] of [['prefix',76265],['totals',76265],['grid',239865]]){
  let cursor=0;
  for(let s=1;s<=8;s++)for(const p of batchPlan(kind,s,total)){assert.equal(p.start,cursor);assert.ok(p.end>p.start);cursor=p.end;}
  assert.equal(cursor,total);
 }
});
test('grid batch links the shared endpoint logs from both existing chunks',()=>{
 const records=[{index:255,x:1000,lower:'0',upper:'1',logLower:'5',logUpper:'6',logChunk:0,logRow:255},
  {index:256,x:1002,lower:'1',upper:'2',logLower:'6',logUpper:'7',logChunk:1,logRow:0}];
 const g=generateBatch('grid',1,{index:0,start:255,end:256},records,{reference:{lower:'0',upper:'2',logLower:'6',logUpper:'7'}});
 assert.deepEqual(g.metadata.logChunks,[0,1]);assert.match(g.source,/C000000\.rows\.drop 255/);assert.match(g.source,/C000001\.rows\.drop 0/);
});
// This fixture tests orchestration only; its fake objects are never used in
// the production tree or presented as mathematical certificates.
test('a failed assembly batch remains pending while later success is reused',()=>{
 const sourceTools=path.dirname(fileURLToPath(import.meta.url)),sourceRepo=path.resolve(sourceTools,'../../..');
 const tmp=fs.realpathSync(os.tmpdir()),repo=fs.mkdtempSync(path.join(tmp,'chen-assembly-test-'));
 try{
  const root=path.join(repo,'research/chen-platt'),tools=path.join(root,'tools'),build=path.join(repo,'OpenAI/tools'),dataDir=path.join(root,'PlattAssemblyData');
  for(const d of [tools,build,dataDir])fs.mkdirSync(d,{recursive:true});
  for(const n of ['AssemblyPlan.mjs','AssemblyChunks.mjs','CertificateSections.mjs'])fs.copyFileSync(path.join(sourceTools,n),path.join(tools,n));
  fs.copyFileSync(path.join(sourceRepo,'OpenAI/tools/atomic-json.mjs'),path.join(build,'atomic-json.mjs'));
  fs.writeFileSync(path.join(repo,'lean-toolchain'),'TEST');fs.writeFileSync(path.join(repo,'lake-manifest.json'),'{}');
  const records=Array.from({length:12},(_,i)=>({index:i,lo:1001+16*i,hi:1016+16*i,w:3,W:8,B:1,lower:'0',upper:'1',cuts:[{k:1,lower:'0',upper:'1'}]}));
  const bytes=zlib.gzipSync(JSON.stringify({start:0,end:12,records}));fs.writeFileSync(path.join(dataDir,'prefix-s1.json.gz'),bytes);
  fs.writeFileSync(path.join(dataDir,'manifest.json'),JSON.stringify({schema:1,counts:12,cells:2,configurationHash:sha('TEST{}'),files:[{kind:'prefix',section:1,file:'prefix-s1.json.gz',hash:sha(bytes)}]}));
  fs.writeFileSync(path.join(repo,'fail-middle'),'1');
  fs.writeFileSync(path.join(build,'build-source.mjs'),`import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.env.CHEN_REPO,m=process.argv[2],sha=b=>crypto.createHash('sha256').update(b).digest('hex');
if(m.endsWith('B000001')&&fs.existsSync(path.join(repo,'fail-middle')))process.exit(2);
const src=path.join(repo,'research/chen-platt',m.replaceAll('.','/')+'.lean');const obj=path.join(repo,'.lake/build-434/lib/lean',m.replaceAll('.','/')+'.olean');
fs.mkdirSync(path.dirname(obj),{recursive:true});fs.writeFileSync(obj,'TEST ONLY '+m);
const logs=path.join(repo,'.lake/build-434/source-build-logs');fs.mkdirSync(logs,{recursive:true});const f=path.join(logs,'ledger-'+process.env.CHEN_BUILD_TAG+'.json');const l=fs.existsSync(f)?JSON.parse(fs.readFileSync(f)):{};
l[m]={sourceHash:sha(fs.readFileSync(src)),objectHash:sha(fs.readFileSync(obj)),configurationHash:sha('TEST{}'),dependencies:{},seconds:0};fs.writeFileSync(f,JSON.stringify(l));`);
  const run=(command,...args)=>spawnSync(process.execPath,[path.join(tools,'AssemblyChunks.mjs'),command,'--kind','prefix',...args],{cwd:repo,windowsHide:true,encoding:'utf8'});
  const first=run('run','--section','1','--chunks','3');assert.equal(first.status,1,first.stderr);
  const dir=path.join(repo,'.lake/build-434/assembly-certificates/Prefix/S1');
  assert.ok(fs.existsSync(path.join(dir,'B000000.json')));assert.ok(!fs.existsSync(path.join(dir,'B000001.json')));assert.ok(fs.existsSync(path.join(dir,'B000002.json')));
  const last=fs.readFileSync(path.join(dir,'B000002.json'),'utf8');
  let status=JSON.parse(run('status').stdout);assert.equal(status.sections[0].nextPendingBatch,1);assert.deepEqual(status.sections[0].unresolvedFailedBatches,[1]);
  fs.unlinkSync(path.join(repo,'fail-middle'));
  const resumed=run('run','--section','1','--chunks','1');assert.equal(resumed.status,0,resumed.stderr);
  assert.equal(fs.readFileSync(path.join(dir,'B000002.json'),'utf8'),last);
  assert.equal(JSON.parse(fs.readFileSync(path.join(dir,'failures/B000001.json'))).status,'RESOLVED');
  status=JSON.parse(run('status').stdout);assert.equal(status.sections[0].nextPendingBatch,null);
  const done=run('run','--section','1','--chunks','3');assert.equal(done.status,0,done.stderr);const summary=JSON.parse(done.stdout.trim().split('\n').at(-1));assert.equal(summary.reused,3);assert.equal(summary.attempted,0);
 }finally{assert.equal(path.dirname(fs.realpathSync(repo)),tmp);fs.rmSync(repo,{recursive:true,force:true});}
});
