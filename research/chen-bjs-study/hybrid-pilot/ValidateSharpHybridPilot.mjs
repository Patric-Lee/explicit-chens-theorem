import fs from 'node:fs';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
const read=p=>JSON.parse(fs.readFileSync(p));
for(const [stem,scan] of [['hybrid-grid-scan-1e8','hybrid-prime-scan-1e8.json'],
    ['hybrid-grid-scan-2e10','hybrid-prime-scan-2e10.json'],['hybrid-grid-scan-1e10','hybrid-prime-scan-1e10.json']]) {
  const d=read(stem+'.json'),r=read(scan);
  assert.equal(d.primeCount,r.primeCount);
  assert.equal(d.integerReciprocalSum,r.integerReciprocalSum);
  const raw=zlib.gunzipSync(fs.readFileSync(stem+'.certificate.json.gz'));
  assert.equal(crypto.createHash('sha256').update(raw).digest('hex'),d.certificateSha256);
  const c=JSON.parse(raw),S=BigInt(c.scale),g=c.grid;
  assert.equal(g[0].x,d.U);assert.equal(g.at(-1).x,d.X);
  assert.equal(g.length,d.gridPoints);
  const Bhi=(S*26151n+99999n)/100000n,Blo=S*26149n/100000n;
  let min=null,max=null;
  for(let i=0;i<g.length;i++) {
    const a=g[i],lo=BigInt(a.llLower),hi=BigInt(a.llUpper);
    assert(lo<=hi);
    const floatingReference=Math.log(Math.log(a.x));
    assert(Number(lo)/Number(S)<=floatingReference+2e-15);
    assert(floatingReference<=Number(hi)/Number(S)+2e-15);
    if(!i)continue;
    const p=g[i-1];
    assert(a.x>p.x&&a.x-p.x<=Math.floor(p.x/4000));
    assert(a.count>=p.count&&BigInt(a.qsum)>=BigInt(p.qsum));
    const lower=BigInt(p.qsum)-hi-Bhi;
    const upper=BigInt(a.qsum)+BigInt(a.count)-BigInt(p.llLower)-Blo;
    if(min===null||lower<min)min=lower;
    if(max===null||upper>max)max=upper;
  }
  assert.equal(min.toString(),d.errorLowerUnits);
  assert.equal(max.toString(),d.errorUpperUnits);
  assert(min*9000n>=-S&&max*9000n<=S);
}
const m=read('hybrid-moment-scan.json');
const h=m.snapshots.find(x=>x.positiveZeros===500000);
assert(h.headDerivativeCap<=19);
assert(h.headMomentLower>=.0461796);
assert(1.5*(.046192-.0461796)<=19e-6);
const study=read('hybrid-product-pilot.json');
const p=study.roundedCandidates.find(x=>x.name==='half_million_improved_kernel_margin');
assert(p.envelope.total<1/9000);
assert(p.envelope.smoothingGate);
assert(p.productExcess<1/4000);
assert(p.classification.includes('NOT_A_THEOREM'));
console.log('Hybrid pilot consistency checks passed. Numerical feasibility only; no zero table, sieve certificate, constant enclosure or analytic bridge was promoted to a Lean theorem.');
