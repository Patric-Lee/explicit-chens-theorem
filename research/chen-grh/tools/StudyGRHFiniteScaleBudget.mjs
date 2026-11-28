// Research planning only: floating calculations propose analytic requirements.
// No result of this script is an axiom or an input to the Chen theorem.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
const repo=process.cwd(),dir=path.join(repo,'research/chen-grh');
const output=process.argv.indexOf('--output');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const audit=JSON.parse(fs.readFileSync(path.join(dir,'FINAL_GRHSub12_CHEN_AUDIT.json')));
if(audit.cutoff!=='3^145000'||audit.rootMomentCap!==340||audit.densityMomentExponent!==350)throw Error('Unexpected baseline');
const sourceFiles=['GRHSub12Analytic.lean','GRHSub12Moments.lean','GRHTruncatedPreSieve.lean','GRHFiniteScaleBudget.lean'];
const sourceHashes=Object.fromEntries(sourceFiles.map(f=>[f,sha(fs.readFileSync(path.join(dir,f)))]));
const ceil=(x,d=1e6)=>Math.ceil(x*d)/d;
const logBudget=(C,p,L,rate)=>Math.log(C)+p*Math.log(L)-rate*L;
const targets=[{H:11,L:59874,t:3991},{H:10,L:22026,t:3992},{H:9,L:8103,t:3995},{H:8,L:2980,t:4005}];
// Exact rational arithmetic checks of the four standalone positivity contracts.
// K=8.06, pair coefficient=.495, lower coefficient=2.01275.
const contracts=targets.map(({H,L,t})=>{
 const l=BigInt(L),cube=l**3n;
 const costNumerator=39897n*cube+10000n*(60000000n+38n*l*l);
 if(costNumerator*1000n>BigInt(t)*10000n*cube)throw Error('Failed exact residual contract');
 const marginNumerator=8051n-2n*BigInt(t);
 if(marginNumerator<=0n)throw Error('Nonpositive exact margin');
 return{H,logLower:L,baseLoss:'17/250',mediumLoss:'28/25',endpointLoss:'1/20000',
  lower:'8051/4000',K:'403/50',pair:'99/200',C5:'30000000',
  normalizedSquare:'60000000/L^3',normalizedComplement:'38/L',tripleCap:t+'/1000',
  margin:marginNumerator+'/4000',status:'EXACT_ARITHMETIC_CONTRACT_ANALYTIC_PREMISES_NOT_PROVED'};
});
// Existing theta estimate plus partial summation gives this proposed sharper
// interval bridge. Its transfer to the actual Lean prime carriers is NOT proved.
const intervalPower=L=>(135/L+1200/L**2)*Math.exp(-L/160);
function mesh(L,eta){
 const medN=Math.max(1,Math.min(1e7,Math.ceil(Math.sqrt(196/(192*eta)))));
 const pairN=Math.max(1,Math.min(1e7,Math.ceil(Math.sqrt(759/(30*eta)))));
 return{mediumGrid:medN,mediumError:196/medN+192*medN*eta,
  pairGrid:pairN,pairError:759/pairN+30*pairN*eta+5*pairN**2*eta**2};
}
function profileCaps(g,eta){
 const w=7/1920;let kernel=0,hat=0;
 for(let i=0;i<64;i++){
  const a=.1+w*i,s=5-10*(a+w)-g,u=s-2;
  if(s<=0)return null;
  const P=1+u+u*u/2+u**3/6+u**4/24+u**5/120+u**6/720;
  kernel+=w/(a*s*s);
  hat+=w/a*(s<=2?1:(s<=3?1:3/s)/P);
 }
 return{kernel:ceil(kernel+64*eta),hat:ceil(hat+64*eta)};
}
const current=targets.map(({H,L})=>{
 const inv=mesh(L,1/L**2),sharp=mesh(L,intervalPower(L));
 return{H,L,legacyPanMinimumGap:39*Math.log(L)/L,
  legacyPanMinimumShiftEvenWithNoTruncation:390*Math.log(L)/L,
  presieveLogError:logBudget(336,6,L,.0029)+350+Math.log(2)/2,
  weightedAPLogError:logBudget(3.2e17,7,L,.002),
  inverseLogInterval:1/L**2,powerInterval:intervalPower(L),inverseLogMeshes:inv,powerMeshes:sharp,
  currentC5Normalized:6e7/L**3,complementNormalized:38/L,
  denominatorAAllowed:(1/64-.003/4)*L-Math.log(20)-Math.log(2)/2,
  denominatorLogErrorWithLinearSingularCap:Math.log(20)+1096+Math.log(10*L)+Math.log(2)/2-(1/16-.003/4)*L,
  mediumPrimeReciprocalCurrentMajorant:4*L**2,
  mediumPrimeReciprocalProposedMajorant:Math.log(10/3)+intervalPower(L),
  inheritedThresholdFailures:[
   ['lowerSourceProduct',110010*Math.log(3)],['upperSourceMass',132001*Math.log(3)],
   ['floorReserveCoarse',150000],['genericLogCutoffDegree90',132496*Math.log(3)],
   ['LiRemainderAllocatedAs1over3000',135000]
  ].filter(([,v])=>L<v).map(([name,logThreshold])=>({name,logThreshold})),
  finalCutoffProved:false};
});
// Uniform local majorant from goldbach_root_prime_tight, after division by sqrt p.
// Covers both density and reciprocal moments, for primes >2. This experiment
// uses a generated JS sieve; NO Euler-product proposal here is a certificate.
const composite=new Uint8Array(4000001),primes=[];
for(let p=2;p*p<=4000000;p++)if(!composite[p])for(let n=p*p;n<=4000000;n+=p)composite[n]=1;
for(let p=3;p<4000000;p++)if(!composite[p])primes.push(p);
const sigmas=Array.from({length:20},(_,i)=>(i+1)/40),moments=[];
for(const z of[4000000,300000])for(const sigma of sigmas){
 let logMoment=0;
 for(const p of primes){if(p>=z)break;
  const nu=(1.01+(p<=100?.25:0))/p+(p===3?1/Math.sqrt(p):0);
  logMoment+=Math.log1p(Math.exp(sigma*Math.log(p))*nu);
 }
 moments.push({z,sigma,logMomentApproximate:logMoment,proposedLogCap:ceil(logMoment,100),certified:false});
}
const profiles=[
 {id:'qsum_cleanup_retaining_Pan',tailC:102,tailP:4,apC:3.2e17,apP:7,kappa:.001,tau:1e-4,retainPan:true},
 {id:'variable_rankin_existing_powers',tailC:336,tailP:6,apC:3.2e17,apP:7,kappa:.001,tau:1e-6},
 {id:'linear_tail_existing_AP',tailC:336,tailP:1,apC:3.2e17,apP:7,kappa:.001,tau:1e-6},
 {id:'linear_tail_sharp_distribution',tailC:16,tailP:1,apC:10,apP:4,kappa:0,tau:1e-4},
 {id:'quadratic_tail_sharp_distribution',tailC:16,tailP:2,apC:10,apP:4,kappa:0,tau:1e-4},
 {id:'optimistic_stress_test',tailC:1,tailP:0,apC:1,apP:2,kappa:0,tau:1e-4},
];
function evaluate(target,mo,p){
 const {L,H}=target,{z,sigma}=mo,M=mo.proposedLogCap,tau=p.tau;
 const theta=ceil((M+Math.log(p.tailC)+p.tailP*Math.log(L)+Math.log(1/tau)+sigma*Math.log(2))/(sigma*L),1e5);
 const delta=ceil(Math.max(p.kappa+(Math.log(p.apC)+p.apP*Math.log(L)+Math.log(1/tau))/L,
  p.retainPan?39*Math.log(L)/L:0),1e5);
 const g=ceil(10*(theta+delta)+10*Math.log(2)/L,1000);
 const eta=intervalPower(L),grids=mesh(L,eta),caps=profileCaps(g,eta);
 const radiusDenominator=1/8-delta/4-1.5/L;
 if(!caps||radiusDenominator<=0)return null;
 const K=ceil(1/radiusDenominator,1e4),pair=ceil(.49254+grids.pairError+45/L);
 const base=ceil(.41*g+12.5*.055/28+.001+10*tau);
 const medium=ceil(3*.02+12.52*grids.mediumError+40*g*1.02*caps.kernel+.6886*caps.hat+.002+10*tau);
 const lower=2.6408-base-medium/2-.00005,square=6e7/L**3,complement=38/L;
 const triple=K*pair+square+complement,margin=lower-triple/2;
 const tailLog=logBudget(p.tailC,p.tailP,L,sigma*theta)+M+sigma*Math.log(2);
 const apLog=logBudget(p.apC,p.apP,L,delta-p.kappa);
 const tests={geometry:g<=.1,mediumSourceRatio:5/3-g>=1.5,
  truncation:tailLog<=Math.log(tau)+1e-10,distribution:apLog<=Math.log(tau)+1e-10,
  tailMonotone:sigma*theta>=p.tailP/L,distributionMonotone:delta-p.kappa>=p.apP/L,
  powerThetaEndpoint:L/10>=120*Math.log(3),positive:margin>0};
 return{H,L,z,sigma,proposedMomentLogCap:M,profile:p.id,theta,delta,g,K,pair,base,medium,lower,triple,margin,
  eta,grids,caps,square,complement,tailLog,apLog,tests,
  modelPositive:Object.values(tests).every(Boolean),status:'UNPROVED_ANALYTIC_PACKAGE_NOT_A_CHEN_THEOREM',
  requiredDenominatorA:(1/64-delta/4)*L-Math.log(20)-Math.log(2)/2,
  denominatorLogErrorWithLinearSingularCap:Math.log(20)+1096+Math.log(10*L)+Math.log(2)/2-(1/16-delta/4)*L,
  inheritedSourceAndDenominatorGatesDischarged:false,
  requiresSmallerProductWindow:z<4000000};
}
const comparisons=[];
for(const target of targets)for(const p of profiles)for(const z of[4000000,300000]){
 const rows=moments.filter(m=>m.z===z).map(m=>evaluate(target,m,p)).filter(Boolean);
 const positive=rows.filter(r=>r.modelPositive).sort((a,b)=>b.margin-a.margin);
 const geometric=rows.filter(r=>r.tests.geometry).sort((a,b)=>b.margin-a.margin);
 const leastShift=[...rows].sort((a,b)=>a.g-b.g)[0];
 comparisons.push({H:target.H,z,profile:p.id,sigmaCandidates:rows.length,positiveCandidates:positive.length,
  bestPositive:positive[0]??null,bestWithinGeometry:geometric[0]??null,
  leastShift:leastShift?{sigma:leastShift.sigma,g:leastShift.g,
   marginWithinSupportedGeometry:leastShift.tests.geometry?leastShift.margin:null}:null,
  certifiedFeasible:false});
}
// Inverted requirements for a fixed g=.1 and sigma=.3. This is necessary for
// the envelope/range model, not sufficient for positivity or a full theorem.
const frontiers=targets.map(({H,L})=>{
 const sigma=.3,tau=1e-4,delta=(2*Math.log(L)+Math.log(1/tau))/L;
 const thetaAvailable=.01-Math.log(2)/L-delta;
 const maxMoment=sigma*thetaAvailable*L-sigma*Math.log(2)-Math.log(1/tau);
 const actual=moments.find(m=>m.z===300000&&m.sigma===sigma).proposedLogCap;
 return{H,L,scenario:'optimistic_stress_test',sigma,geometryCap:.1,deltaMinimum:delta,thetaAvailable,
  maximumAllowedLogMoment:maxMoment,proposed300kLogMoment:actual,
  requiredMomentLogReduction:Math.max(0,actual-maxMoment),
  maximumAllowedAtAnySigmaUpToOne:Math.max(0,thetaAvailable*L-Math.log(2))-Math.log(1/tau),
  emptyProductImpossibleForSigmaUpToOne:Math.max(0,thetaAvailable*L-Math.log(2))-Math.log(1/tau)<0};
});
const recommended=comparisons.filter(r=>r.H===10&&r.profile==='linear_tail_sharp_distribution'&&r.z===4000000)[0].bestPositive;
const alternative=comparisons.filter(r=>r.H===10&&r.profile==='quadratic_tail_sharp_distribution'&&r.z===300000)[0].bestPositive;
if(!recommended||!alternative)throw Error('Expected H10 research package disappeared');
if(current.filter(r=>r.H<=10).some(r=>r.legacyPanMinimumShiftEvenWithNoTruncation<=.1))throw Error('Legacy Pan gate should exclude H10, H9 and H8');
if(comparisons.some(r=>r.certifiedFeasible))throw Error('Study must never report a new proved cutoff');
const report={classification:'SPECIALIZED_FINITE_SCALE_BUDGET_STUDY_NOT_A_LEAN_CHEN_PROOF',
 assumptionsPolicy:{soleAllowedExternalAxiom:'ChenEffective.GRH.alpoge_dirichlet_grh',newAxioms:0,nativeDecide:false,newDependencies:0,
  note:'Proposed analytic bounds below are research obligations, not axioms or imported facts.'},
 baseline:{cutoff:audit.cutoff,H:audit.HApproximate,manifest:audit.sourceObjectManifestHash},sourceHashes,
 numericalStudyScriptHash:sha(fs.readFileSync(new URL(import.meta.url))),
 equations:{tail:'Ct L^pt exp(Msigma + sigma log 2 - sigma theta L) <= tau',
  distribution:'Cd L^pd exp(-(delta-kappa)L) <= tau',geometry:'g >= 10(theta+delta)+10 log(2)/L; g <= .1',
  primeInterval:'eta(L)=(135/L+1200/L^2) exp(-L/160)',
  mediumMesh:'196/n+192 n eta',pairMesh:'759/n+30 n eta+5 n^2 eta^2',
  lower:'2.6408-baseLoss-mediumLoss/2-endpointLoss',triple:'K pair + 2 C5/L^3 + 38/L',
  margin:'lower-triple/2 > 0',
  frontier:'(log Ct+pt log L+Msigma+log(1/tau))/sigma + log Cd+pd log L+log(1/tau)+kappa L+2 log 2 <= g L/10'},
 analyticObligations:[
  'Prove variable-sigma Rankin tail for the actual base and conditioned source remainders, with the proposed polynomial prefactor.',
  'Kernel-certify finite Euler-product log caps; the JavaScript sieve and floating sums are only proposals.',
  'Retain the power-decaying theta interval error and prove it for the actual rpowFloor prime carriers and all grid boundaries.',
  'Prove the sharp weighted distribution envelope for the actual sources; a pointwise AP theorem alone is insufficient.',
  'Replace the Pan 39-log-level interface and prove the full weighted convolution/QD Selberg remainder with C5 <= 30000000 at the target.',
  'Pay source lower/upper mass with the stated losses at the target; current thresholds remain far larger.',
  'Replace the expanded singular-series cap by S(N) <= 10 log N (or an equally strong bound), and retune the floor reserve. This already pays the existing exp(1096) kernel prefactor at H10 in the numerical model.',
  'Prove actual medium and pair inequalities and all-real uniformity for every L >= L0, not only at the endpoint.',
  'If z=300000, prove the relative Goldbach product bound at the same sieve tolerance; small prime moments alone do not justify it.'
 ],contracts,current,moments,profiles,comparisons,frontiers,recommendedH10:recommended,alternativeH10:alternative,
 selfChecks:{exactRationalContracts:4,legacyPanExcludesH10H9H8:true,noNewCutoffClaim:true}};
if(output>=0){if(!process.argv[output+1])throw Error('Missing output path');fs.writeFileSync(process.argv[output+1],JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify({classification:report.classification,baseline:report.baseline,
 contracts,frontiers,recommendedH10:recommended,alternativeH10:alternative,selfChecks:report.selfChecks},null,2));
