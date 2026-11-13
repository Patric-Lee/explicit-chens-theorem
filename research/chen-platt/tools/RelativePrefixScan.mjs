// Untrusted exact-integer feasibility scan, NOT a Lean certificate.
import fs from 'node:fs';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
const X=Number(process.argv[2]||10_000_000_000),U=4_000_000;
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
const spacing=Number(process.argv[4]||32000);
if(!Number.isSafeInteger(spacing)||spacing<4000)throw Error("invalid spacing");
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
  previous=row;grid.push(row);
}
function drain(before) {
  while(next<=X && next<before) {
    record(next);
    if(next===X){next=X+1;break;}
    next=Math.min(X,next+Math.max(1,Math.floor(next/spacing)));
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
// Correlated suffix rounding: P(x)-P(R) is the negative suffix.
const last=grid.at(-1),QR=BigInt(last.qsum),CR=BigInt(last.count);
for(let i=1;i<grid.length;i++){
  const a=grid[i-1],b=grid[i];
  const lower=BigInt(a.qsum)-QR-(CR-BigInt(a.count))-BigInt(b.llUpper)+BigInt(last.llLower);
  const upper=BigInt(b.qsum)-QR-BigInt(a.llLower)+BigInt(last.llUpper);
  if(min===null||lower<min){min=lower;minWitness={a:a.x,b:b.x,units:lower.toString()};}
  if(max===null||upper>max){max=upper;maxWitness={a:a.x,b:b.x,units:upper.toString()};}
}
const serialized=JSON.stringify({scale:SB.toString(),logSeriesTerms:N,spacing,grid});
const out=process.argv[3]||'platt-relative-prefix';
fs.writeFileSync(out+'.certificate.json.gz',zlib.gzipSync(serialized));
const result={classification:'UNTRUSTED_FEASIBILITY_SCAN_NOT_A_LEAN_PROOF',X,U,
  anchor:X,spacing,gridPoints:grid.length,primeCount:count,scale:SB.toString(),
  logSeriesTerms:N,lower:Number(min)/S,upper:Number(max)/S,minWitness,maxWitness,
  finiteAllowance:'1/20000',pass:min*20000n>=-SB && max*20000n<=SB,
  certificateSha256:crypto.createHash('sha256').update(serialized).digest('hex'),
  seconds:(Date.now()-start)/1000,
  unresolved:['Lean verification of sieve completeness and reciprocal sums',
    'Lean verification of rational logarithm bounds','kernel checking all rows']};
fs.writeFileSync(out+'.json',JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
