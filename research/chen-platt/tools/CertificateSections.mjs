// Scheduling and process locks only. No mathematical claims are checked here.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
export {atomicJson} from '../../../OpenAI/tools/atomic-json.mjs';
import {atomicJson} from '../../../OpenAI/tools/atomic-json.mjs';

export function sectionRange(total, section, size = 10000) {
  if (!Number.isSafeInteger(section) || section < 1 || section > Math.ceil(total / size))
    throw Error(`section must be between 1 and ${Math.ceil(total / size)}`);
  return {section, start: (section - 1) * size, end: Math.min(total, section * size)};
}
export function processAlive(pid) {
  if (!Number.isSafeInteger(pid) || pid < 1) return false;
  try { process.kill(pid, 0); return true; }
  catch (e) { return e.code !== 'ESRCH'; }
}

// All updated runners participate, including the old --start/--chunks mode.
// An overlapping run is refused. An interrupted child's lock remains effective
// until both the driver and its build child have exited.
export function acquireRangeLock(dir, start, end) {
  fs.mkdirSync(dir, {recursive: true});
  const gate = path.join(dir, 'registry.guard');
  let gateFd;
  for (let i = 0; i < 250; i++) {
    try { gateFd = fs.openSync(gate, 'wx'); break; }
    catch (e) {
      if (e.code !== 'EEXIST') throw e;
      Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 20);
    }
  }
  if (gateFd === undefined) throw Error(`Lock registry busy: ${gate}. Retry after other runners finish starting.`);
  const file = path.join(dir, `range-${start}-${end}.json`);
  const record = {pid: process.pid, childPid: null, start, end, token: crypto.randomUUID()};
  try {
    for (const name of fs.readdirSync(dir).filter(n => /^range-.*\.json$/.test(n))) {
      const p = path.join(dir, name), old = JSON.parse(fs.readFileSync(p, 'utf8'));
      if (!processAlive(old.pid) && !processAlive(old.childPid) && !processAlive(old.nativePid)) { fs.unlinkSync(p); continue; }
      if (start < old.end && old.start < end)
        throw Error(`Overlapping runner is active for chunks ${old.start}..${old.end - 1} (PID ${old.pid}).`);
    }
    atomicJson(file, record);
  } finally { fs.closeSync(gateFd); fs.unlinkSync(gate); }
  return {
    file,
    setChild(pid) {
      const current = JSON.parse(fs.readFileSync(file, 'utf8'));
      current.childPid = pid; atomicJson(file, current);
    },
    release() {
      if (!fs.existsSync(file)) return;
      const current = JSON.parse(fs.readFileSync(file, 'utf8'));
      if (!processAlive(current.childPid) && !processAlive(current.nativePid) &&
          current.token === record.token) fs.unlinkSync(file);
    }
  };
}
