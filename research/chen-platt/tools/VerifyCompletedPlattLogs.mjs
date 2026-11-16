import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import zlib from 'node:zlib';

// Read-only verification of completed receipts, not a replacement for Lean or
// the final grid-coverage, prime-sum assembly, and Chen axiom audit.
const repo = process.argv[2];
if (!repo) throw Error('Usage: node VerifyCompletedPlattLogs.mjs REPO [REPORT.json]');
const root = path.join(repo, 'research/chen-platt');
const build = path.join(repo, '.lake/build-434');
const sha = b => crypto.createHash('sha256').update(b).digest('hex');
const json = p => JSON.parse(fs.readFileSync(p, 'utf8'));
const insist = (b, message) => { if (!b) throw Error(message); };
const raw = fs.readFileSync(path.join(root, 'block-relative-1e10.grid.json.gz'));
const grid = JSON.parse(zlib.gunzipSync(raw)).grid;
const inputHash = sha(raw);
const configurationHash = sha(fs.readFileSync(path.join(repo, 'lean-toolchain'), 'utf8') +
  fs.readFileSync(path.join(repo, 'lake-manifest.json'), 'utf8'));
const ledger = json(path.join(build, 'source-build-logs/ledger-manuallogs.json'));
const object = m => path.join(build, 'lib/lean', ...m.split('.')) + '.olean';
const objectHashes = new Map();
function objectHash(m) {
  if (!objectHashes.has(m)) objectHashes.set(m, sha(fs.readFileSync(object(m))));
  return objectHashes.get(m);
}
function checkRecord(m, record, sourceHash) {
  insist(record && record.sourceHash === sourceHash, `Source mismatch: ${m}`);
  insist(record.configurationHash === configurationHash, `Configuration mismatch: ${m}`);
  insist(record.objectHash === objectHash(m), `Object mismatch: ${m}`);
  for (const [dep, hash] of Object.entries(record.dependencies))
    insist(objectHash(dep) === hash, `Dependency mismatch: ${m} -> ${dep}`);
}
const total = Math.ceil(grid.length / 256);
let covered = 0, seconds = 0;
const chunks = [];
for (let i = 0; i < total; i++) {
  const name = 'C' + String(i).padStart(6, '0');
  const m = `PlattCertificates.Log256.${name}`;
  const source = fs.readFileSync(path.join(root, 'PlattCertificates/Log256', name + '.lean'), 'utf8');
  const receipt = json(path.join(build, 'manual-certificates/Log256', name + '.json'));
  const a = i * 256, b = Math.min(grid.length, a + 256);
  insist(receipt.classification === 'LEAN_KERNEL_CHECKED_COMPONENT_NOT_FINAL_H30', `Unchecked: ${m}`);
  insist(receipt.module === m && receipt.kind === 'logs' && receipt.variant === 'Log256' &&
    receipt.index === i && receipt.gridInputHash === inputHash, `Identity mismatch: ${m}`);
  const md = receipt.metadata;
  insist(md.rowStart === a && md.rowEndExclusive === b && md.firstX === grid[a].x &&
    md.lastX === grid[b - 1].x, `Coverage metadata mismatch: ${m}`);
  const rows = [...source.matchAll(/⟨(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+)⟩/g)];
  insist(rows.length === b - a, `Row count mismatch: ${m}`);
  for (let j = 0; j < rows.length; j++)
    insist(BigInt(rows[j][1]) === BigInt(grid[a + j].x), `Grid coordinate mismatch: ${m}:${j}`);
  const exactSource = `import PlattLogRows\nnamespace ChenEffective.PlattWindow.Manual.Log256.${name}\nopen LogCertificate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef rows : List LogRow := [${rows.map(r => r[0]).join(',\n')} ]\ntheorem checked : rows.all checkRow = true := by\n  decide +kernel\nend ChenEffective.PlattWindow.Manual.Log256.${name}\n`;
  insist(source === exactSource, `Unexpected proof template: ${m}`);
  const sourceHash = sha(source);
  insist(receipt.sourceHash === sourceHash, `Receipt source mismatch: ${m}`);
  checkRecord(m, receipt.checked, sourceHash);
  covered += rows.length;
  seconds += receipt.checked.seconds;
  chunks.push({module: m, sourceHash, objectHash: receipt.checked.objectHash});
}
for (let i = 1; i < grid.length; i++)
  insist(grid[i - 1].x < grid[i].x, `Unordered grid: ${i}`);
insist(grid[0].x === 4000000 && grid.at(-1).x === 10000000000, 'Unexpected range');
// Check the arithmetic and analytic soundness components against their current
// sources and recorded dependency objects, without rerunning the campaign.
const logDir = path.join(build, 'source-build-logs');
const ledgers = fs.readdirSync(logDir).filter(n => /^ledger(?:-[a-z]+)?\.json$/.test(n))
  .map(n => json(path.join(logDir, n)));
for (const m of ['PlattLogKernel', 'PlattLogRows', 'PlattLogSoundness', 'PlattLogRowSoundness']) {
  const sourceHash = sha(fs.readFileSync(path.join(root, m + '.lean')));
  const candidates = ledgers.map(l => l[m]).filter(Boolean);
  const record = candidates.find(r => r.configurationHash === configurationHash &&
    r.sourceHash === sourceHash && r.objectHash === objectHash(m) &&
    Object.entries(r.dependencies).every(([d, h]) => objectHash(d) === h));
  insist(record, `Current checked soundness component missing: ${m}`);
  checkRecord(m, record, sourceHash);
}
const report = {classification: 'LOG_RECEIPT_AND_GRID_ALIGNMENT_VERIFIED_NOT_FINAL_H30',
  checkedAt: new Date().toISOString(), inputHash, configurationHash,
  chunks: total, points: covered, firstX: grid[0].x, lastX: grid.at(-1).x,
  summedRecordedLeanSeconds: seconds,
  certificateManifestHash: sha(JSON.stringify(chunks)),
  remaining: ['Kernel-level full grid coverage and seam assembly',
    'Completed prime-count certificates and global reciprocal-sum bounds',
    'Analytic source theorem for the proposed 2e9 reduction',
    'Final H30 theorem replacement and axiom audit']};
if (process.argv[3]) fs.writeFileSync(process.argv[3], JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify(report, null, 2));
