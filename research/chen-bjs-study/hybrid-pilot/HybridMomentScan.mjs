// Untrusted zero ordinates propose candidate disjoint critical-line boxes.
// No zero existence, RH, distinctness or completeness is asserted here.
import fs from 'node:fs';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
const raw=fs.readFileSync('hybrid-odlyzko-zeros6.gz');
const zeros=zlib.gunzipSync(raw).toString().trim().split(/\s+/).map(Number);
const PI=Math.PI, Cref=2+0.577215664901532860606512090082402431-Math.log(4*PI);
const Ccap=0.04619142, radius=1e-6;
let K=0,Kc=0,A=0,Ac=0,previous=0,minGap=Infinity;
const snapshots=[], marks=new Set([29,100,1000,10000,100000,250000,500000,1000000,1500000,zeros.length]);
function addK(x){const y=x-Kc,t=K+y;Kc=(t-K)-y;K=t;}
function addA(x){const y=x-Ac,t=A+y;Ac=(t-A)-y;A=t;}
for(let i=0;i<zeros.length;i++) {
  const t=zeros[i];
  if(!(t>previous+2*radius)) throw Error('proposed zero boxes overlap or are unordered');
  if(i) minGap=Math.min(minGap,t-previous);
  // Contributions from the positive ordinate and its conjugate.
  addK(2/(.25+(t+radius)**2));
  addA(2/(t-radius));
  previous=t;
  if(marks.has(i+1)) snapshots.push({positiveZeros:i+1,lastOrdinate:t,
    proposedBoxRadius:radius,headMomentLower:K,headDerivativeCap:A,
    residualCap:2*(Ccap-K),sharperResidualCap:1.5*(Ccap-K),momentConstantCap:Ccap,
    classification:'UNPROVED_ZERO_BOX_CANDIDATES_AND_UNPROVED_CONSTANT_CAP'});
}
const result={classification:'NUMERICAL_PILOT_NOT_A_PROOF',
  source:'https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros6.gz',
  compressedSha256:crypto.createHash('sha256').update(raw).digest('hex'),
  advertisedSourceAccuracy:4e-9,proposedBoxRadius:radius,
  positiveZeroRows:zeros.length,minAdjacentGap:minGap,
  momentConstantReference:Cref,momentConstantCap:Ccap,momentConstantCapProved:false,
  snapshots,
  proofObligations:['actual critical-line zero in every selected interval',
    'distinctness and embedding into divisor-zero indices',
    'rational interval certification of the scalar head sums',
    'precise upper enclosure of 2+gamma-log(4*pi)',
    'head/remaining decomposition in the psi1 explicit formula',
    'finite-difference and integrated psi1-to-Mertens analytic bridges']};
fs.writeFileSync('hybrid-moment-scan.json',JSON.stringify(result,null,2)+'\n');
console.table(snapshots.map(s=>({zeros:s.positiveZeros,T:s.lastOrdinate,A:s.headDerivativeCap,W:s.residualCap})));
