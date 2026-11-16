import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {atomicJson} from './atomic-json.mjs';

function fixture(run) {
  const root = fs.realpathSync(os.tmpdir());
  const dir = fs.mkdtempSync(path.join(root, 'chen-atomic-'));
  try { run(path.join(dir, 'ledger.json'), dir); }
  finally {
    assert.equal(path.dirname(fs.realpathSync(dir)), root);
    fs.rmSync(dir, {recursive: true, force: true});
  }
}
test('transient Windows replacement failures retry without removing old data', () => fixture(file => {
  fs.writeFileSync(file, 'old');
  let calls = 0, waits = 0;
  atomicJson(file, {checked: true}, {
    rename(from, to) {
      if (calls++ < 3) {
        assert.equal(fs.readFileSync(to, 'utf8'), 'old');
        throw Object.assign(Error('sharing violation'), {code: ['EPERM','EACCES','EBUSY'][calls - 1]});
      }
      fs.renameSync(from, to);
    }, sleep() { waits++; },
  });
  assert.equal(calls, 4); assert.equal(waits, 3);
  assert.deepEqual(JSON.parse(fs.readFileSync(file)), {checked: true});
}));
test('permanent errors preserve original and pending JSON', () => fixture((file, dir) => {
  fs.writeFileSync(file, 'old');
  assert.throws(() => atomicJson(file, {checked: true}, {
    rename() { throw Object.assign(Error('I/O error'), {code: 'EIO'}); },
  }), /pending JSON retained/);
  assert.equal(fs.readFileSync(file, 'utf8'), 'old');
  const pending = fs.readdirSync(dir).find(n => n.endsWith('.tmp'));
  assert.deepEqual(JSON.parse(fs.readFileSync(path.join(dir, pending))), {checked: true});
}));
test('retry timeout remains bounded and preserves recovery data', () => fixture(file => {
  fs.writeFileSync(file, 'old');
  assert.throws(() => atomicJson(file, {checked: true}, {
    timeoutMs: 0,
    rename() { throw Object.assign(Error('blocked'), {code: 'EPERM'}); },
  }), /pending JSON retained/);
  assert.equal(fs.readFileSync(file, 'utf8'), 'old');
}));
