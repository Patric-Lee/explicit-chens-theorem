// Orchestration-only test: the isolated fixture uses a mock builder and fake
// objects. It never writes to the production certificate tree or checks Lean.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import zlib from 'node:zlib';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';

test('failed middle chunk is recorded; later chunks finish; resume fills the gap', () => {
  const sourceTools = path.dirname(fileURLToPath(import.meta.url));
  const sourceRepo = path.resolve(sourceTools, '../../..');
  const temp = fs.realpathSync(os.tmpdir());
  const repo = fs.mkdtempSync(path.join(temp, 'chen-failure-fixture-'));
  try {
    const root = path.join(repo, 'research/chen-platt');
    const tools = path.join(root, 'tools');
    const buildTools = path.join(repo, 'OpenAI/tools');
    fs.mkdirSync(tools, {recursive: true}); fs.mkdirSync(buildTools, {recursive: true});
    for (const name of ['CertificateChunks.mjs','CertificateSections.mjs'])
      fs.copyFileSync(path.join(sourceTools, name), path.join(tools, name));
    fs.copyFileSync(path.join(sourceRepo, 'OpenAI/tools/atomic-json.mjs'), path.join(buildTools, 'atomic-json.mjs'));
    fs.writeFileSync(path.join(repo, 'lean-toolchain'), 'TEST-ONLY');
    fs.writeFileSync(path.join(repo, 'lake-manifest.json'), '{}');
    const counts = Buffer.alloc(6), hash = crypto.createHash('sha256').update(counts).digest('hex');
    const grid = {U: 4000000, R: 10000000000, countSha256: hash,
      groups: [{lo: 4000001, w: 1, offset: 0}], grid: [{x:4000000},{x:10000000000}]};
    fs.writeFileSync(path.join(root, 'block-relative-1e10.grid.json.gz'), zlib.gzipSync(JSON.stringify(grid)));
    fs.writeFileSync(path.join(root, 'block-relative-1e10.counts.bin.gz'), zlib.gzipSync(counts));
    fs.writeFileSync(path.join(root, 'block-relative-1e10.json'), JSON.stringify({blocks:3,countSha256:hash}));
    fs.writeFileSync(path.join(repo, 'fail-middle'), 'yes');
    fs.writeFileSync(path.join(buildTools, 'build-source.mjs'), `
import fs from 'node:fs'; import path from 'node:path'; import crypto from 'node:crypto';
const repo=process.env.CHEN_REPO, m=process.argv[2];
if(m.endsWith('C000001')&&fs.existsSync(path.join(repo,'fail-middle')))process.exit(2);
const hash=b=>crypto.createHash('sha256').update(b).digest('hex');
const src=path.join(repo,'research/chen-platt',m.replaceAll('.','/')+'.lean');
const out=path.join(repo,'.lake/build-434/lib/lean',m.replaceAll('.','/')+'.olean');
fs.mkdirSync(path.dirname(out),{recursive:true});fs.writeFileSync(out,'TEST-ONLY FAKE OBJECT '+m);
const logs=path.join(repo,'.lake/build-434/source-build-logs');fs.mkdirSync(logs,{recursive:true});
const f=path.join(logs,'ledger-'+process.env.CHEN_BUILD_TAG+'.json');
const ledger=fs.existsSync(f)?JSON.parse(fs.readFileSync(f)):{};
ledger[m]={sourceHash:hash(fs.readFileSync(src)),objectHash:hash(fs.readFileSync(out)),
configurationHash:hash(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8')),dependencies:{},seconds:0};
fs.writeFileSync(f,JSON.stringify(ledger));
`);
    const run = (command, ...args) => spawnSync(process.execPath,
      [path.join(tools, 'CertificateChunks.mjs'),command,'--kind','counts','--integers-per-chunk','4',...args],
      {cwd:repo,encoding:'utf8',windowsHide:true});
    const first = run('run','--section','1','--chunks','3');
    assert.equal(first.status, 1, first.stderr);
    const receipts = path.join(repo,'.lake/build-434/manual-certificates/Count4');
    assert.ok(fs.existsSync(path.join(receipts,'C000000.json')));
    assert.ok(!fs.existsSync(path.join(receipts,'C000001.json')));
    assert.ok(fs.existsSync(path.join(receipts,'C000002.json')));
    const lastReceipt = fs.readFileSync(path.join(receipts,'C000002.json'),'utf8');
    const failureFile = path.join(receipts,'failures/C000001.json');
    assert.equal(JSON.parse(fs.readFileSync(failureFile)).status, 'FAILED');
    const status1 = JSON.parse(run('status').stdout);
    assert.equal(status1.sections[0].nextUnrecordedChunk, 1);
    assert.equal(status1.sections[0].nextPendingChunk, 1);
    assert.deepEqual(status1.sections[0].unresolvedFailedChunks, [1]);
    assert.equal(status1.recordedSuccessfulChunks, 2);
    // A stale historical receipt must not hide an explicitly failed chunk.
    fs.copyFileSync(path.join(receipts,'C000000.json'),path.join(receipts,'C000001.json'));
    const staleStatus=JSON.parse(run('status').stdout);
    assert.equal(staleStatus.sections[0].nextPendingChunk, 1);
    assert.equal(staleStatus.sections[0].nextUnrecordedChunk, 1);
    assert.equal(staleStatus.recordedSuccessfulChunks, 2);
    fs.unlinkSync(path.join(repo,'fail-middle'));
    const resumed = run('run','--section','1','--chunks','1');
    assert.equal(resumed.status, 0, resumed.stderr);
    assert.equal(JSON.parse(fs.readFileSync(failureFile)).status, 'RESOLVED');
    assert.equal(fs.readFileSync(path.join(receipts,'C000002.json'),'utf8'), lastReceipt);
    const status2 = JSON.parse(run('status').stdout);
    assert.equal(status2.recordedSuccessfulChunks, 3);
    assert.equal(status2.sections[0].nextPendingChunk, null);
    assert.deepEqual(status2.unresolvedFailures, []);
    const final = run('run','--section','1','--chunks','3');
    assert.equal(final.status, 0, final.stderr);
    const summary = JSON.parse(final.stdout.trim().split('\n').at(-1));
    assert.equal(summary.reused, 3); assert.equal(summary.attempted, 0);
  } finally {
    assert.equal(path.dirname(fs.realpathSync(repo)), temp);
    fs.rmSync(repo,{recursive:true,force:true});
  }
});
