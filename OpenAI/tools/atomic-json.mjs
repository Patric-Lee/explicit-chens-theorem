// Windows readers/scanners can temporarily deny replacement of an open file.
// Keep the destination intact and retry rename; never delete it as a fallback.
import fs from 'node:fs';
import crypto from 'node:crypto';

export function atomicJson(file, value, {
  rename = fs.renameSync,
  sleep = ms => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms),
  timeoutMs = 10000,
} = {}) {
  const temporary = `${file}.${process.pid}.${crypto.randomUUID()}.tmp`;
  fs.writeFileSync(temporary, JSON.stringify(value, null, 2) + '\n');
  const deadline = Date.now() + timeoutMs;
  let attempts = 0;
  for (;;) {
    try { rename(temporary, file); return; }
    catch (error) {
      if (!['EPERM', 'EACCES', 'EBUSY'].includes(error.code) || Date.now() >= deadline) {
        error.message += `; original destination preserved; pending JSON retained at ${temporary}`;
        throw error;
      }
      sleep(Math.min(250, 25 * 2 ** Math.min(attempts++, 4)));
    }
  }
}
