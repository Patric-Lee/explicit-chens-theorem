// Exact-integer pilot certificate generator; NOT a Lean proof. In particular,
// the segmented sieve and log-interval algorithm still need verified checkers,
// and 0.26149 <= B1 <= 0.26151 is an explicit outstanding obligation.
import fs from 'node:fs';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
const X=Number(process.argv[2]||20_000_000_000),U=4_000_000;
if(!Number.isSafeInteger(X)||X<U||X>1e11) throw Error('unsupported range');
const SB=1n<<48n,S=Number(SB),N=16;
const ceilDiv=(a,b)=>(a+b-1n)/b;
function logUnit(n,d) {
  // 1 <= n/d <= 2. atanh series with a geometric remainder.
  const a=n-d,b=n+d;
  let ap=a,bp=b,sum=0n;
  const a2=a*a,b2=b*b;
  for(let j=0;j<N;j++) {
    sum+=SB*ap/(BigInt(2*j+1)*bp);
    ap*=a2;bp*=b2;
  }
  const tail=ceilDiv(2n*SB*ap*b2,BigInt(2*N+1)*bp*(b2-a2));
  return [2n*sum,2n*(sum+BigInt(N))+tail];
}
const ln2=logUnit(2n,1n);
function logRational(n,d) {
  if(n<d) throw Error('log arguments below one are not needed');
  let k=0n;
  while(n>=2n*d){d*=2n;k++;}
  const q=logUnit(n,d);
  return [k*ln2[0]+q[0],k*ln2[1]+q[1]];
}
function loglogInteger(n) {
  const L=logRational(BigInt(n),1n);
  return [logRational(L[0],SB)[0],logRational(L[1],SB)[1]];
}
const Blow=SB*26149n/100000n,Bhigh=ceilDiv(SB*26151n,100000n);
const root=Math.floor(Math.sqrt(X))+1,base=new Uint8Array(root+1),primes=[];
for(let p=2;p<=root;p++) if(!base[p]) {
  primes.push(p);
  if(p*p<=root) for(let j=p*p;j<=root;j+=p)base[j]=1;
}
let count=0,qsum=0,next=U,previous=null,min=null,max=null,minWitness,maxWitness;
const grid=[];
const start=Date.now();
function record(t) {
  const ll=loglogInteger(t),Q=BigInt(qsum),C=BigInt(count);
  const row={x:t,qsum:qsum.toString(),count,llLower:ll[0].toString(),llUpper:ll[1].toString()};
  if(previous) {
    const lower=BigInt(previous.qsum)-ll[1]-Bhigh;
    const upper=Q+C-BigInt(previous.llLower)-Blow;
    if(min===null||lower<min){min=lower;minWitness={a:previous.x,b:t,units:lower.toString()};}
    if(max===null||upper>max){max=upper;maxWitness={a:previous.x,b:t,units:upper.toString()};}
  }
  previous=row;grid.push(row);
}
function drain(before) {
  while(next<=X && next<before) {
    record(next);
    if(next===X){next=X+1;break;}
    next=Math.min(X,next+Math.floor(next/4000));
  }
}
function addPrime(p) {
  drain(p);
  let q=Math.floor(S/p);
  if(q*p>S)q--;
  if((q+1)*p<=S)q++;
  if(!(q*p<=S && (q+1)*p>S))throw Error('integer reciprocal floor');
  count++;qsum+=q;
  if(!Number.isSafeInteger(qsum+count))throw Error('sum overflow');
}
addPrime(2);
const width=4_000_000;
for(let lo=3;lo<=X;lo+=width) {
  const hi=Math.min(lo+width-2,X),size=Math.floor((hi-lo)/2)+1;
  const composite=new Uint8Array(size);
  for(const p of primes) {
    if(p===2)continue;
    if(p*p>hi)break;
    let first=Math.max(p*p,Math.ceil(lo/p)*p);
    if(first%2===0)first+=p;
    for(let j=(first-lo)/2;j<size;j+=p)composite[j]=1;
  }
  for(let j=0;j<size;j++)if(!composite[j])addPrime(lo+2*j);
  if((lo-3)%2_000_000_000===0)console.log(JSON.stringify({through:Math.min(lo+width-1,X),count,seconds:(Date.now()-start)/1000}));
}
drain(X+1);
const serialized=JSON.stringify({scale:SB.toString(),B1Lower:[26149,100000],
  B1Upper:[26151,100000],logSeriesTerms:N,grid});
const out=process.argv[3]||'hybrid-grid-scan';
fs.writeFileSync(out+'.certificate.json.gz',zlib.gzipSync(serialized));
const result={classification:'EXACT_INTEGER_PILOT_NOT_LEAN_VERIFIED',X,U,
  primeCount:count,integerReciprocalSum:qsum,reciprocalRoundingWidth:count/S,
  gridPoints:grid.length,scale:SB.toString(),logSeriesTerms:N,
  B1Enclosure:{lower:'26149/100000',upper:'26151/100000',proved:false},
  errorLowerUnits:min.toString(),errorUpperUnits:max.toString(),
  errorLower:Number(min)/S,errorUpper:Number(max)/S,minWitness,maxWitness,
  scalarPrefixBudgetPass: min*9000n>=-SB && max*9000n<=SB,
  certificateSha256:crypto.createHash('sha256').update(serialized).digest('hex'),
  seconds:(Date.now()-start)/1000,
  unresolved:['verified segmented sieve / reciprocal-sum checker',
    'Lean proof of the rational log interval algorithm','B1 enclosure theorem',
    'kernel checking of these grid rows']};
fs.writeFileSync(out+'.json',JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
