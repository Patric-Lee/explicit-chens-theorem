import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {sectionRange, acquireRangeLock, atomicJson} from './CertificateSections.mjs';

test('eight sections partition the campaign without gaps or overlaps', () => {
  const ranges = Array.from({length: 8}, (_, i) => sectionRange(76265, i + 1));
  assert.equal(ranges[0].start, 0);
  assert.equal(ranges[7].end, 76265);
  for (let i = 0; i < 7; i++) {
    assert.equal(ranges[i].end - ranges[i].start, 10000);
    assert.equal(ranges[i].end, ranges[i + 1].start);
  }
  assert.equal(ranges[7].end - ranges[7].start, 6265);
  for (const s of [0, 9, 1.5, NaN]) assert.throws(() => sectionRange(76265, s));
});

test('overlapping workers are refused; disjoint sections and resume are allowed', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'chen-sections-'));
  try {
    const first = acquireRangeLock(dir, 0, 10000);
    assert.throws(() => acquireRangeLock(dir, 0, 10000), /Overlapping/);
    assert.throws(() => acquireRangeLock(dir, 9999, 20000), /Overlapping/);
    assert.throws(() => acquireRangeLock(dir, 0, 76265), /Overlapping/);
    const second = acquireRangeLock(dir, 10000, 20000);
    second.release(); first.release();
    const resumed = acquireRangeLock(dir, 0, 10000);
    resumed.release();
    assert.deepEqual(fs.readdirSync(dir), []);
  } finally { fs.rmSync(dir, {recursive: true, force: true}); }
});

test('live build children keep interrupted driver ranges locked', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'chen-section-child-'));
  try {
    const file = path.join(dir, 'range-0-10000.json');
    atomicJson(file, {pid: 0, childPid: process.pid, start: 0, end: 10000});
    assert.throws(() => acquireRangeLock(dir, 0, 10000), /Overlapping/);
    atomicJson(file, {pid: 0, childPid: 0, nativePid: process.pid, start: 0, end: 10000});
    assert.throws(() => acquireRangeLock(dir, 0, 10000), /Overlapping/);
    atomicJson(file, {pid: 0, childPid: 0, start: 0, end: 10000});
    const resumed = acquireRangeLock(dir, 0, 10000);
    resumed.release();
  } finally { fs.rmSync(dir, {recursive: true, force: true}); }
});
