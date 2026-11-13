// Independent numerical cross-check. This is NOT a Lean certificate.
import fs from 'node:fs';
import zlib from 'node:zlib';
import assert from 'node:assert/strict';
const zeroPath=process.argv[2]||'hybrid-odlyzko-zeros6.gz';
const gridPath=fs.existsSync('hybrid-grid-scan-1e10.json')?'hybrid-grid-scan-1e10.json':
  '../chen-bjs-study/hybrid-pilot/hybrid-grid-scan-1e10.json';
const zeros=zlib.gunzipSync(fs.readFileSync(zeroPath)).toString().trim().split(/\s+/).map(Number).slice(0,400000);
// Sum in reverse order, independently of the pilot's forward compensated sum.
let moment=0,derivative=0;
for(let i=zeros.length-1;i>=0;i--){
  const t=zeros[i];
  if(i)assert(t-zeros[i-1]>2e-6);
  moment+=2/(.25+(t+1e-6)**2);
  derivative+=2/(t-1e-6);
}
assert(moment>.0461772+1e-10);
assert(derivative<18-1e-6);
const gamma=.577215664901532860606512090082402431;
const completedMoment=2+gamma-Math.log(4*Math.PI);
assert(completedMoment<.046192-1e-9);
const W=22.2e-6,A=18,X=1e10,L=Math.log(X);
assert(1.5*(.046192-.0461772)<W);
const delta=2.02*Math.sqrt(W)*X**(-1/16),h=delta*X;
const weight=x=>(Math.log(x)+1)/(x*Math.log(x))**2;
// These are the actual envelope definitions in BJSHybridAnalyticBridge,
// rather than the optimized approximations used in HybridProductPilot.
const theta=(h/2+2+A*Math.sqrt(X+h)+W*((X+h)**(15/8)+X**(15/8))/h+2/h+2*Math.sqrt(X))/(X*L);
const raw=((3/25)*X**1.5+W*X**(15/8)+2*X+1e9)*weight(X);
const integral=(2/L+3/L**2+2/L**3)*((6/25)*X**(-.5)+8*W*X**(-1/8)+2/X+5e8/X**2);
const primePowers=4*(1/L+1/L**2)*X**(-.5);
// Use terminal b=3^10000. All its power-decaying contributions are tiny;
// reserve 1e-10 for those contributions, separately from the Dusart endpoint.
const terminalLog=10000*Math.log(3);
const terminal=1/(2*terminalLog**2)+1e-10;
const total=theta+raw+integral+primePowers+terminal;
assert(delta<.01&&X-h>1);
assert(total<1/9000-1e-6);
function envelopeAt(logx){
  const x=Math.exp(logx),d=2.02*Math.sqrt(W)*x**(-1/16),step=d*x;
  const endpoint=(step/2+2+A*Math.sqrt(x+step)+W*((x+step)**(15/8)+x**(15/8))/step+2/step+2*Math.sqrt(x))/(x*logx);
  const primitive=((3/25)*x**1.5+W*x**(15/8)+2*x+1e9)*weight(x);
  const integrated=(2/logx+3/logx**2+2/logx**3)*((6/25)*x**(-.5)+8*W*x**(-1/8)+2/x+5e8/x**2);
  return endpoint+primitive+integrated+4*(1/logx+1/logx**2)*x**(-.5)+terminal;
}
let previous=total;
for(let i=1;i<=10000;i++){
  const e=envelopeAt(L+(120*Math.log(3)-L)*i/10000);
  assert(e<=previous*(1+1e-12));
  assert(e<1/9000);
  previous=e;
}
assert(Math.expm1(2/9000+24/3999999)<1/4000);
const scan=JSON.parse(fs.readFileSync(gridPath));
assert(scan.X>=X);
assert(scan.errorLower>-1/9000&&scan.errorUpper<1/9000);
const report={classification:'NUMERICAL_SUPPORT_FOR_TEMPORARY_ASSUMPTION_NOT_KERNEL_CERTIFIED',
 positiveZeroCandidates:zeros.length,lastOrdinate:zeros.at(-1),caps:{A,W,momentCap:.046192,headMomentLower:.0461772,primePowerCoefficient:2},moment,derivative,completedMoment,
 finiteGrid:{lower:scan.errorLower,upper:scan.errorUpper},
 actualBridgeAtX:{X,delta,theta,raw,integral,primePowers,terminal,total,target:1/9000},
 tailSampling:{points:10001,from:X,to:'3^120',decreasing:true},
 cutoff:{base:3,exponent:'10^13',H:Math.log(1e13*Math.log(3))},
 qualifications:['Zero ordinates are trusted numerical table data, not certified zero boxes.',
  'The all-real window and scalar monotonicity are assumed, not proved by this script.',
  'No claim that the new Chen theorem has only the Dirichlet axiom.']};
fs.writeFileSync('sharp-hybrid-numerical-check.json',JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report,null,2));
