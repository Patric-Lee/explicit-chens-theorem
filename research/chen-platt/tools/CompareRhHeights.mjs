// Numerical feasibility study ONLY. Does not modify axioms or certificate inputs.
import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
import {fileURLToPath} from 'node:url';
const root=process.env.CHEN_PLATT_ROOT||path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const out=path.join(root,'studies/rh-height-budget');fs.mkdirSync(out,{recursive:true});
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const gridFile=fs.readFileSync(path.join(root,'block-relative-1e10.grid.json.gz'));
const countFile=fs.readFileSync(path.join(root,'block-relative-1e10.counts.bin.gz'));
const data=JSON.parse(zlib.gunzipSync(gridFile)),counts=zlib.gunzipSync(countFile),grid=data.grid;
if(sha(counts)!==data.countSha256||data.U!==4000000||data.R!==1e10)throw Error('Unexpected inputs');
const S=1n<<48n;
function unit(n,d){let q=0n;for(let i=0n;i<16n;i++)q+=S*(n-d)**(2n*i+1n)/((2n*i+1n)*(n+d)**(2n*i+1n));return [2n*q,2n*q+33n];}
const ln2=unit(2n,1n);
function logRat(n,d){let k=0n;while(n>=2n*d){d*=2n;k++;}const a=unit(n,d);return [k*ln2[0]+a[0],k*ln2[1]+a[1]];}
function loglog(n){const a=logRat(BigInt(n),1n);return [logRat(a[0],S)[0],logRat(a[1],S)[1]];}
// Convert original ceil rounding to the proven segment kernel's floor+1.
let gi=0,A=data.U,correction=0n,point=1;
grid[0].correction=0n;grid[0].blocks=0;
for(let i=0;i<counts.length/2;i++){
 if(gi+1<data.groups.length&&i===data.groups[gi+1].offset)gi++;
 const W=2**data.groups[gi].w,c=BigInt(counts.readUInt16LE(2*i));
 if(S*c%BigInt(A)===0n)correction++;
 A+=2*W;
 if(point<grid.length&&A===grid[point].x){grid[point].correction=correction;grid[point].blocks=i+1;point++;}
}
if(A!==data.R||point!==grid.length)throw Error('Counting/group/grid seams inconsistent');
console.log(JSON.stringify({phase:'Reusing all existing counts; no sieve run',points:grid.length,extraUpperUnits:correction.toString()}));
// Add an exact round candidate only to this in-memory study. It is already
// a count-block boundary; no source certificate data or existing file changes.
const insertedStudyPoints=[];
for(const target of [2000000000,6400000000]){
 const index=grid.findIndex(g=>g.x>=target);if(grid[index].x===target)continue;
 const a=grid[index-1];let at=a.x,offset=a.blocks,ql=BigInt(a.lower),qh=BigInt(a.upper)+a.correction;
 let group=0;while(group+1<data.groups.length&&data.groups[group+1].offset<=offset)group++;
 while(at<target){
  if(group+1<data.groups.length&&offset===data.groups[group+1].offset)group++;
  const W=2**data.groups[group].w,c=BigInt(counts.readUInt16LE(2*offset)),b=at+2*W;
  if(b>target)throw Error('Study target is not a count-block boundary');
  ql+=S*c/BigInt(b);qh+=S*c/BigInt(at)+1n;at=b;offset++;
 }
 grid.splice(index,0,{x:target,lower:ql.toString(),upper:qh.toString(),correction:0n,blocks:offset});
 insertedStudyPoints.push(target);
}
let minBase=null,maxBase=null;
for(let i=0;i<grid.length;i++){
 const g=grid[i],[lo,hi]=loglog(g.x);g.llLo=lo;g.llHi=hi;
 g.qLo=BigInt(g.lower);g.qHi=BigInt(g.upper)+g.correction;
 if(i){const a=grid[i-1],l=a.qHi-hi,u=g.qLo-a.llLo;
  if(minBase===null||l<minBase)minBase=l;if(maxBase===null||u>maxBase)maxBase=u;
  const lower=minBase-g.qHi+lo,upper=maxBase-g.qLo+hi;
  g.finite=Math.max(Number(-lower),Number(upper))/Number(S);
 }else g.finite=0;
 if(i&&i%60000===0)console.log(JSON.stringify({phase:'Outward log replay (JavaScript study only)',points:i}));
}
const source=fs.readFileSync(path.join(root,'Calr3/TernaryGoldbach/Explicit/PsiRanges1e8.lean'),'utf8');
const body=source.slice(source.indexOf('noncomputable def cW8'),source.indexOf('theorem psi_mid8'));
const profile=[...body.matchAll(/if x ≤ \((\d+) : ℝ\) then \((\d+)(?:\s*\/\s*(\d+))? : ℝ\)/g)]
 .map(m=>({end:Number(m[1]),C:Number(m[2])/Number(m[3]||1)+2}));
if(profile.length!==21)throw Error('Unexpected cW8 shape: '+profile.length);
profile.push({end:1e17,C:201});
const logB=512*Math.log(3),invRootB=Math.exp(-logB/2),invBlogB=Math.exp(-logB)/logB;
const budget=1/9000,far=2e-8,delta=1/2000000,Asqrt=1147,Bconstant=42e9;
function plateauIntegral(a){const l=Math.log(a);return delta*(Math.log(logB/l)+1/l-1/logB)
 +2*Asqrt*(l+1)/l**2*(1/Math.sqrt(a)-invRootB)+Bconstant*(1/(a*l)-invBlogB);}
function plateauEndpoint(a){const l=Math.log(a);return delta/l+Asqrt/(Math.sqrt(a)*l)+Bconstant/(a*l);}
function cIntegral(a,b,C){const l=Math.log(a);return 2*C*(l+1)/l**2*(1/Math.sqrt(a)-1/Math.sqrt(b));}
function schIntegral(a,b,sharp){const la=Math.log(a),lb=Math.log(b),c=1/(8*Math.PI),j=sharp?1:3;
 // For sharp log(log-2), discard only the negative -2/log(t) term.
 // Add endpoint-convention correction: normalized theta differs by <=log(t)/2.
 return 2*c*((la+j)/Math.sqrt(a)-(lb+j)/Math.sqrt(b))
  +0.5*(1+1/la)*(1/a-1/b);}
function schEndpoint(a,sharp){return (Math.log(a)-(sharp?2:0))/(8*Math.PI*Math.sqrt(a))+0.5/a;}
function maxX(T){let lo=10,hi=100;const target=2*Math.log(T/4.92);for(let i=0;i<100;i++){const m=(lo+hi)/2;if(m-Math.log(m)<target)lo=m;else hi=m;}return Math.exp(lo);}
const heights=[1e8,3e12],caps=heights.map(T=>({T,maxX:maxX(T),safeX:T===1e8?1e16:1e25}));
function analytic(r,mode,T=1e8){
 let ep=0,inte=0,a=r;const cap=caps.find(h=>h.T===T)?.safeX;
 if(mode!=='checked-profile'){
  const b=cap;ep=schEndpoint(a,mode==='buthe-sharp');inte+=schIntegral(a,b,mode==='buthe-sharp');a=b;
 }
 for(const p of profile){if(p.end<=a)continue;ep=Math.max(ep,p.C/(Math.sqrt(a)*Math.log(a)));inte+=cIntegral(a,p.end,p.C);a=p.end;}
 const start=Math.max(a,1e17);ep=Math.max(ep,plateauEndpoint(start));
 const tail=plateauIntegral(start)+far;
 return {endpoint:ep,integral:inte,tail,total:ep+inte+tail};
}
const routes=[{id:'checked-profile',mode:'checked-profile',T:1e8,status:'Uses already checked theta inputs and integral lemmas, but this retargeted assembly is NOT Lean-checked.'},
 ...heights.flatMap(T=>['schoenfeld','buthe-sharp'].map(mode=>({id:mode+'-'+T,mode,T,
  status:mode==='buthe-sharp'?
   'Conditional feasibility calculation. Strong theta bridge NOT formalized. Published proof also uses numerical theta bounds through 1e11; these need certification or an alternative proof.':
   'Conditional feasibility calculation. Buthe finite-RH bridge NOT formalized. Can avoid its separate theta computation by deriving the coarse theta bound from its psi log(log-3) bound and our proved 2sqrt(x) prime-power gap.'})))];
function work(g){return {countingEnd:g.x,gridPoints:grid.indexOf(g)+1,blocks:g.blocks,
 physicalCountChunksLowerEstimate:Math.ceil((g.x-data.U)/131072),countRangeReduction:(data.R-data.U)/(g.x-data.U)};}
const targets=[1e9,1.5e9,1.75e9,2e9,2.25e9,2.5e9,3e9,4e9,5e9,6e9,6.4e9,7e9,8e9,1e10];
for(const route of routes){
 route.candidates=targets.map(target=>{const g=grid.find(g=>g.x>=target),a=analytic(g.x,route.mode,route.T);
  return {...work(g),analytic:a.total,endpoint:a.endpoint,integral:a.integral,farTail:a.tail,
   finite:g.finite,total:a.total+g.finite,slack:budget-a.total-g.finite,fixedAllocationPass:a.total<=59e-6&&g.finite<=50e-6};});
 for(const allocation of ['fixed','joint']){
  let best;
  for(const g of grid){if(g.x<3**16)continue;const a=analytic(g.x,route.mode,route.T);
   if(allocation==='fixed'?a.total<=59e-6&&g.finite<=50e-6:a.total+g.finite<=budget){best={...work(g),analytic:a.total,finite:g.finite,total:a.total+g.finite,slack:budget-a.total-g.finite};break;}}
  route[allocation+'FirstPassingExistingGridPoint']=best||null;
 }
}
const report={classification:'NUMERICAL_STUDY_NOT_A_LEAN_PROOF',timestamp:new Date().toISOString(),
 scope:'No axiom, theorem, original data, checker core, or manual campaign changed. Existing untrusted scan reused; no sieve or full Lean campaign run.',
 sources:{buthe:'https://arxiv.org/pdf/1410.7015',plattTrudgian:'https://arxiv.org/pdf/2004.09765',
  butheSharp:'Theorem 2 proof, equations (7.3)-(7.4); normalized theta convention corrected.'},
 inputs:{gridSha256:sha(gridFile),countCompressedSha256:sha(countFile),countSha256:data.countSha256,thetaSourceSha256:sha(source),insertedStudyPoints},
 heights:caps,budget:{total:budget,fixedAnalytic:59e-6,fixedFinite:50e-6,farErrorPlusEndpoint:far},
 rounding:{scale:S.toString(),logarithmTail:'32 rounding units + 1 geometric-tail unit',
  reciprocalUpper:'floor+1, matching PlattReciprocalKernel',extraUpperUnits:correction.toString()},routes};
fs.writeFileSync(path.join(out,'comparison.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({heights:caps,results:routes.map(r=>({id:r.id,fixed:r.fixedFirstPassingExistingGridPoint,joint:r.jointFirstPassingExistingGridPoint}))},null,2));
