import fs from 'node:fs';
import zlib from 'node:zlib';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..')+'/';
const out=root+'studies/rh-height-budget/',report=JSON.parse(fs.readFileSync(out+'comparison.json','utf8'));
const original=JSON.parse(zlib.gunzipSync(fs.readFileSync(root+'block-relative-1e10.grid.json.gz')));
const S=2**48;
function bruteFinite(R){
 // Independent direct per-cell scan, using the original (tighter) log/ceil
 // proposals. Compare to new outward arithmetic with a conservative tolerance.
 const gs=original.grid,j=gs.findIndex(g=>g.x>=R),end=gs[j];let low=0n,high=0n;
 for(let i=1;i<=j;i++){
  const a=gs[i-1],b=gs[i];
  const l=-(BigInt(end.upper)-BigInt(a.upper))-BigInt(b.llUpper)+BigInt(end.llLower);
  const u=-(BigInt(end.lower)-BigInt(b.lower))-BigInt(a.llLower)+BigInt(end.llUpper);
  if(l<low)low=l;if(u>high)high=u;
 }
 return {reference:end.x,finite:Math.max(Number(-low),Number(high))/S};
}
function simpson(f,a,b){const N=8192,h=(b-a)/N;let sum=f(a)+f(b);for(let i=1;i<N;i++)sum+=(i%2?4:2)*f(a+h*i);return sum*h/3;}
const ends=[3.2e6,1e7,3.2e7,1e8,3.2e8,1e9,3.2e9,1e10,3.2e10,1e11,3.2e11,1e12,3.2e12,1e13,3.2e13,1e14,3.2e14,1e15,3.2e15,1e16,3.2e16,1e17];
const cs=[34.84,33.88,33.48,33.35,33.66,34.16,35.06,36.1,37.44,38.94,40.72,42.61,44.82,47.08,49.58,52.27,56.89,63.38,75.3,96.25,134.5,201];
function quadrature(R,route){let a=R,sum=0;
 if(route.mode!=='checked-profile'){
  const b=report.heights.find(h=>h.T===route.T).safeX,sharp=route.mode==='buthe-sharp';
  sum+=simpson(u=>Math.exp(-u/2)/(8*Math.PI)*(u+1)*(1-(sharp?2/u:0))+
   0.5*Math.exp(-u)*(u+1)/u,Math.log(a),Math.log(b));a=b;
 }
 for(let i=0;i<ends.length;i++)if(ends[i]>a){
  sum+=simpson(u=>cs[i]*Math.exp(-u/2)*(u+1)/u**2,Math.log(a),Math.log(ends[i]));a=ends[i];
 }
 sum+=simpson(u=>(1/2e6+1147*Math.exp(-u/2)+42e9*Math.exp(-u))*(u+1)/u**2,
  Math.log(Math.max(a,1e17)),512*Math.log(3));
 return sum;
}
const validations=[];
for(const route of report.routes){
 const row=route.candidates.find(r=>r.countingEnd===2e9),q=quadrature(2e9,route);
 const budgetedIntegral=row.integral+row.farTail-report.budget.farErrorPlusEndpoint;
 if(q>budgetedIntegral+1e-13)throw Error('Envelope quadrature check failed: '+route.id);
 validations.push({route:route.id,quadratureIntegral:q,budgetedIntegral,pass:true});
}
for(const R of [1e9,1.75e9,2.5e9,3e9,5e9,1e10]){
 const b=bruteFinite(R),row=report.routes[0].candidates.find(r=>r.countingEnd===b.reference);
 if(!row||Math.abs(row.finite-b.finite)>1e-10)throw Error('Finite extrema cross-check failed at '+R);
 validations.push({directFiniteScan:R,reference:b.reference,difference:row.finite-b.finite,pass:true});
}
for(const h of report.heights){const required=4.92*Math.sqrt(h.safeX/Math.log(h.safeX));
 if(required>h.T)throw Error('RH range condition failed');validations.push({height:h.T,safeX:h.safeX,requiredHeight:required,pass:true});}
function countChunks(blocks){let count=0;for(let i=0;i<original.groups.length;i++){
 const g=original.groups[i],end=Math.min(blocks,original.groups[i+1]?.offset??8886581);
 if(end<=g.offset)continue;const cap=Math.floor(131072/(2*2**g.w));count+=Math.ceil((end-g.offset)/cap);
 }return count;}
for(const route of report.routes){
 for(const row of [...route.candidates,route.fixedFirstPassingExistingGridPoint,route.jointFirstPassingExistingGridPoint])
  if(row){row.plannedCountChunks=countChunks(row.blocks);row.plannedLogChunks=Math.ceil(row.gridPoints/256);}
}
const current=report.routes[0],old=report.routes.find(r=>r.id==='schoenfeld-100000000'),
 newer=report.routes.find(r=>r.id==='schoenfeld-3000000000000');
const round=old.candidates.find(r=>r.countingEnd===2e9),practical=current.candidates.find(r=>r.countingEnd===6.4e9);
const fixedHeightSaving=1-newer.fixedFirstPassingExistingGridPoint.countingEnd/old.fixedFirstPassingExistingGridPoint.countingEnd;
const jointHeightSaving=1-newer.jointFirstPassingExistingGridPoint.countingEnd/old.jointFirstPassingExistingGridPoint.countingEnd;
const summary={classification:'NUMERICAL_STUDY_NOT_LEAN_CHECKED',validations,
 recommendation:'Keep RH height1e8. First retarget existing bounds near6.4e9; study/formalize coarse finite-RH Schoenfeld bridge toward2e9. Stronger axiom not justified by this model alone.',
 practicalExistingInputs:practical,proposedAfterBridge:round,
 additionalEndpointSavingFromHeight:{fixed:fixedHeightSaving,joint:jointHeightSaving},
 proposedExactAllocation:{analyticNumerator:65,finiteNumerator:46,denominator:1000000,
  totalBelowOneOver9000:111n*9000n<=1000000n},
 formalizationCaution:'Buthe sharp theta proof uses separate numerical theta bound through1e11; not an available sole-RH-height theorem in this repo. Coarse theta can instead follow from psi log(log-3) + checked2sqrt prime-power gap on our entire candidate range.'};
fs.writeFileSync(out+'validation.json',JSON.stringify(summary,null,2)+'\n');
fs.writeFileSync(out+'comparison.json',JSON.stringify(report,null,2)+'\n');
const fmt=x=>(x/1e9).toFixed(3),micro=x=>(x*1e6).toFixed(3);
const rows=report.routes.map(r=>`| ${r.id} | ${fmt(r.fixedFirstPassingExistingGridPoint.countingEnd)} billion | ${fmt(r.jointFirstPassingExistingGridPoint.countingEnd)} billion |`).join('\n');
fs.writeFileSync(out+'README.md',String.raw`# RH-height / finite-endpoint budget comparison

This is a numerical feasibility study, NOT a Lean proof. It reuses the
existing untrusted prime-count data; no new sieve campaign was run. No axiom,
production theorem, original certificate input, or checker core was changed.
The existing checked analytic assembly is still at R=10^10.

## Main result

Keep RH height T=10^8 for now. Existing checked analytic inputs, with a newly
retargeted piecewise budget, suggest R=6.4e9. A coarse finite-RH Schoenfeld
bridge suggests R=2e9 with a joint error allocation. The larger T=3e12 gives
only about${(100*fixedHeightSaving).toFixed(1)}% extra endpoint saving at the
fixed allocation, or${(100*jointHeightSaving).toFixed(1)}% at a jointly optimized
allocation, when compared using the SAME analytic bridge.

## Envelope and finite data

Let E(x)=sum_{p<=x}1/p-log(log x)-B1. The final window requires
|E(x)|<=1/9000 on[4e6,3^120]. For each trial R we recompute the finite
relative bound F(R) for |E(x)-E(R)| on[4e6,R] using all prior grid cells.
The Mertens constant cancels. We use the proved log checker's outward
33-unit tail at scale2^48 and floor+1 reciprocal rounding, matching the
segment checker. Counts and arithmetic are still untrusted study proposals.
Two exact count-block boundaries,2e9 and6.4e9, were added only to the
in-memory study grid; no original dataset was overwritten.

The analytic bound A(R) includes the theta endpoint uniformly for x>=R,
the full error-kernel integral from R to B=3^512, and2e-8 for the existing
proved far-anchor/error endpoint allocations. Past the finite-RH range,
we retain our already-checked piecewise theta and plateau bounds:

$$
|\theta(t)-t|\le t/2000000+1147\sqrt t+42\cdot10^9

\qquad(t\ge10^{17}).
$$

The candidate literature bridge uses

$$
|\theta(t)-t|\le\frac{\sqrt t\log^2t}{8\pi},
\qquad4.92\sqrt{t/\log t}\le T.
$$

The two T values allow this through approximately1.540e16 and2.169e25.
We deliberately use the convenient smaller caps1e16 and1e25. The
normalized-theta endpoint convention is handled conservatively with an
additional(log t)/2 in theta error, including its endpoint/integral cost.
The main resulting envelope behaves as(3 log R+6)/(8 pi sqrt R).

Sources: [Büthe, Theorem2 and its proof](https://arxiv.org/pdf/1410.7015),
[Platt–Trudgian](https://arxiv.org/pdf/2004.09765).

## Endpoint results

The entries are the first numerically passing points of the chosen study
grid and chosen envelopes. They are NOT global optimality claims or
certified cutoffs. Fixed means A<=59e-6 and F<=50e-6. Joint means A+F<=1/9000.

| Route / RH height | Fixed allocation | Joint allocation |
| --- | ---: | ---: |
${rows}

Checked-profile means all analytic INPUT bounds/lemmas are already proved;
the newly retargeted assembly and finite replay still need Lean checking.
Both Schoenfeld routes need a new formal analytic bridge. Buthe-sharp uses
theta<=sqrt(t)log(t)(log(t)-2)/(8pi) and discards only a negative kernel
term. The published proof also uses numerical theta bounds through1e11;
that route needs new certificates or an alternative derivation. It is not
currently a cheap drop-in consequence of our local Platt hypothesis.

The coarser Schoenfeld route can avoid that theta computation: Büthe's
psi<=sqrt(t)log(t)(log(t)-3)/(8pi) error, combined with our proved
psi-theta<=2sqrt(t), suffices once log(t)>=16pi/3. Every candidate range
here meets that condition. The psi bridge still requires formalizing its
analytic kernel estimates and finite parameter tables; accepting the paper
without that proof would introduce an additional unproved input.

## Recommended targets and allocation

With current inputs at R=6.4e9:
A=${micro(practical.analytic)}e-6, F=${micro(practical.finite)}e-6,
total=${micro(practical.total)}e-6 <111.111...e-6.
There are${practical.plannedCountChunks} planned count chunks versus76265
at the original endpoint. This is the lower-formalization-cost candidate.

With the coarser bridge and unchanged RH height1e8 at R=2e9:
A=${micro(round.analytic)}e-6, F=${micro(round.finite)}e-6,
total=${micro(round.total)}e-6. The convenient prospective allocation is

$$
A\le65/10^6,\quad F\le46/10^6,
\qquad111/10^6<1/9000.
$$

This leaves${micro(round.slack)}e-6 actual numerical slack in the study.
The finite counting RANGE is${(100*(1-1/round.countRangeReduction)).toFixed(1)}%
smaller, with${round.blocks} count blocks and approximately
${round.plannedCountChunks} count chunks of at most131072 integers.
The log grid has${round.gridPoints} points /${round.plannedLogChunks} chunks;
the logarithm workload declines much less than the counting range.
These are volume estimates, not measured full-campaign runtime guarantees.

## Validation, limits, and next step

comparison.json records candidates, rounding, source/input hashes and
all budget contributions. validation.json independently checks finite
extrema against a direct per-cell scan, checks integral upper envelopes
against numerical quadrature, and checks both finite-RH range conditions.
This does not replace kernel verification.

Do not change the axiom on the strength of this comparison. First Lean-check
the6.4e9 retarget if minimizing immediate work, or pilot the coarse psi-to-
Schoenfeld bridge if a roughly5-fold smaller counting range justifies the
analytic formalization. Do not claim the2e9 endpoint until that bridge and
the finite certificate/global coverage are checked. H around30 is retained;
no smaller Chen H has been proved by this study. Existing manual results
remain reusable. The current manual runner still describes the original
R=1e10 dataset and is intentionally unchanged.

To reproduce the numerical scan:

~~~powershell
node research/chen-platt/tools/CompareRhHeights.mjs
node research/chen-platt/tools/SummarizeRhHeightBudget.mjs
~~~
`);
console.log(JSON.stringify({validationCases:validations.length,proposed:round,practical,fixedHeightSaving,jointHeightSaving},null,2));

