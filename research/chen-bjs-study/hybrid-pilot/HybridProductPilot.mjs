// Numerical feasibility study only. None of the analytic or zero-table
// hypotheses evaluated here are asserted as Lean theorems.
import fs from 'node:fs';
const PI = Math.PI, U = 4_000_000, C = 1e9;
const strictTarget = 1 / 17000;
const productLogBudget = Math.log1p(1 / 4000) - 24 / (U - 1);
const directTarget = productLogBudget / 2;

function inputs(T) {
  if (!T) return {T:0, A:0, a:0, b:3/25,
    status:'global_moment_proved; endpoint_unsmoothing_and_integrated_bridge_to_be_proved'};
  const l = Math.log(T);
  return {T, A:(l*l/2+l)/PI + 1, a:3/25,
    b:2*(l+1)/(PI*T),
    status:'MISSING: finite_RH_through_T; head_sum_cap; explicit_zero_count_tail_cap'};
}

// f(t)=(log(t)+1)/(t^2 log(t)^2). If |F(t)|<=c*t^r,
// integrating f*F' by parts gives this coefficient for the absolute bound.
function kernelCoefficient(L,r) {
  return 1/L+1/L**2+(2/L+3/L**2+2/L**3)/(2-r);
}

function envelope(L,p,gap=17) {
  const x = Math.exp(L);
  const d = 2.02*Math.sqrt(p.b)*Math.exp(-L/16);
  const pointLow = 1.005*p.A*Math.exp(-L/2)/L;
  const pointHigh = 2.02*Math.sqrt(p.b)*Math.exp(-L/16)/L;
  const pointResidue = (2/x+2/(d*x*x))/L;
  const integralLow = p.a*kernelCoefficient(L,1.5)*Math.exp(-L/2);
  const integralHigh = p.b*kernelCoefficient(L,15/8)*Math.exp(-L/8);
  const integralLinear = 2*kernelCoefficient(L,1)*Math.exp(-L);
  const integralConstant = C*kernelCoefficient(L,0)*Math.exp(-2*L);
  // For |psi-theta|<=c sqrt(x), pay its endpoint plus its integrated tail.
  // The log-gap case uses the currently available 2 sqrt(x) log(x) bound.
  const primePowers = gap === 'log' ? (6+4/L)*Math.exp(-L/2) :
    gap*(3/L+2/L**2)*Math.exp(-L/2);
  const pieces = {pointLow,pointHigh,pointResidue,integralLow,integralHigh,
    integralLinear,integralConstant,primePowers};
  return {L,x,delta:d,pieces,total:Object.values(pieces).reduce((a,b)=>a+b,0),
    smoothingGate:d<=.01 && x*(1-d)>1};
}

function cutoff(p,gap,target) {
  let lo=Math.log(U), hi=200;
  for(let k=0;k<100;k++) {
    const m=(lo+hi)/2, e=envelope(m,p,gap);
    if(e.total<=target && e.smoothingGate) hi=m; else lo=m;
  }
  return envelope(hi,p,gap);
}

const rows=[];
for(const T of [0,100,1000,1e4,1e5,2e5,3e5,5e5,1e6,1894438.5122,1e7,1e8,1e9]) {
  const p=inputs(T);
  for(const gap of [17,2,'log']) rows.push({inputs:p,primePowerGap:gap,
    primePowerStatus:gap===17?'kernel_checked_BJSHybridPrimePowers':
      gap===2?'unproved_sharpened_target':'existing_mathlib_log_gap',
    strict:cutoff(p,gap,strictTarget),direct:cutoff(p,gap,directTarget)});
}
if(fs.existsSync('hybrid-moment-scan.json')) {
  const d=JSON.parse(fs.readFileSync('hybrid-moment-scan.json'));
  for(const h of d.snapshots) for(const gap of [17,2,'log']) {
    const p={T:h.lastOrdinate,A:h.headDerivativeCap,a:3/25,b:h.residualCap,
      positiveZeroCandidates:h.positiveZeros,
      status:'MISSING: certified selected critical-line zeros and scalar moment enclosure; NO completeness premise'};
    rows.push({inputs:p,primePowerGap:gap,headSource:'finite_positive_moment_subtraction',
      strict:cutoff(p,gap,strictTarget),direct:cutoff(p,gap,directTarget)});
  }
  for(const h of d.snapshots) for(const gap of [17,2]) {
    const p={T:h.lastOrdinate,A:h.headDerivativeCap,a:3/25,b:h.sharperResidualCap,
      positiveZeroCandidates:h.positiveZeros,
      status:'MISSING: certified selected critical-line zeros and scalar moment enclosure; NO completeness premise'};
    rows.push({inputs:p,primePowerGap:gap,headSource:'improved_finite_positive_moment_subtraction',
      strict:cutoff(p,gap,strictTarget),direct:cutoff(p,gap,directTarget)});
  }
}
const result={classification:'NUMERICAL_PILOT_NOT_A_PROOF',
  targets:{U,strictTarget,directTarget,productLogBudget},
  notes:[
    'Head/tail caps are explicit proposed hypotheses; no finite RH or zero-count theorem is established by this script.',
    'Integrated bound is derived from the existing psi1 formula by integration by parts, not the sharper incomplete-gamma formula.',
    'Low zero finite-difference bound uses critical-line information; high zero terms use the existing 7/8 strip.',
    'For x>=X each displayed positive envelope term decreases; delta also decreases.',
    'Direct target requires a sharper exponential conversion than the existing factor-two estimate.',
    'No computed cutoff is a proved Chen cutoff.'
  ],rows,
  roundedCandidates:[
    {name:'half_million_improved_kernel',positiveZeroCandidates:5e5,A:19,a:3/25,b:19/1e6,
      proposedMomentConstantCap:.046192,proposedHeadMomentLower:.0461796,X:1e10,gap:17},
    {name:'half_million_improved_kernel_margin',positiveZeroCandidates:5e5,A:19,a:3/25,b:19/1e6,
      proposedMomentConstantCap:.046192,proposedHeadMomentLower:.0461796,X:2e10,gap:17},
    {name:'one_million_head_coarse_gap',positiveZeroCandidates:1e6,A:21,a:3/25,b:1/65000,
      proposedMomentConstantCap:.046192,X:1e10,gap:17},
    {name:'half_million_head_sharper_gap',positiveZeroCandidates:5e5,A:19,a:3/25,b:1/40000,
      proposedMomentConstantCap:.04619142,X:1e10,gap:2},
    {name:'two_million_head_coarse_gap',positiveZeroCandidates:2001052,A:24,a:3/25,b:1/130000,
      proposedMomentConstantCap:.04619142,X:1e10,gap:17}
  ].map(c=>{
    const e=envelope(Math.log(c.X),c,c.gap);
    return {...c,envelope:e,productExcess:Math.expm1(2*e.total+24/(U-1)),
      scalarProductBudgetPass:2*e.total+24/(U-1)<Math.log1p(1/4000),
      classification:'CONDITIONAL_NUMERICAL_CANDIDATE_NOT_A_THEOREM'};
  })};
const out=process.argv[2]||'hybrid-product-pilot.json';
fs.writeFileSync(out,JSON.stringify(result,null,2)+'\n');
console.table(rows.filter(r=>r.primePowerGap===17).map(r=>({T:r.inputs.T,head:r.inputs.positiveZeroCandidates,
  W:r.inputs.b,A:r.inputs.A,strictX:r.strict.x,directX:r.direct.x,delta:r.direct.delta})));
