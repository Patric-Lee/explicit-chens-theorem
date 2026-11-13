// Exploratory exact fixed-point reciprocal-prime sums, with floating log
// endpoint evaluation. NOT a Lean certificate: sieve completeness, logarithm
// intervals and the numerical B1 enclosure still need independent proofs.
import fs from 'node:fs';
const X=Number(process.argv[2]||100_000_000), U=4_000_000;
if(!Number.isSafeInteger(X)||X<U||X>100_000_000_000) throw Error('unsupported pilot range');
const S=2**48, B=0.261497212847642783755426838608695859;
const root=Math.floor(Math.sqrt(X))+1;
const base=new Uint8Array(root+1), primes=[];
for(let p=2;p<=root;p++) if(!base[p]) {
  primes.push(p);
  if(p*p<=root) for(let j=p*p;j<=root;j+=p) base[j]=1;
}
let qsum=0,count=0,min=Infinity,max=-Infinity,minAt=null,maxAt=null;
let previous=2, previousE=null;
const blocks=[], width=4_000_000;
const addPrime=p=>{
  let q=Math.floor(S/p);
  if(q*p>S) q--;
  if((q+1)*p<=S) q++;
  if(!(q*p<=S && (q+1)*p>S)) throw Error('quotient floor check');
  if(p>=U) {
    // Left limit includes all earlier primes, but excludes the current prime.
    const e=qsum/S-Math.log(Math.log(p))-B;
    if(e<min){min=e;minAt={x:p,side:'left_limit'};}
    const upper=(qsum+count)/S-Math.log(Math.log(p))-B;
    if(upper>max){max=upper;maxAt={x:p,side:'left_limit'};}
  }
  qsum+=q;count++;
  if(!Number.isSafeInteger(qsum+count)) throw Error('fixed point sum overflow');
  if(p>=U) {
    const lower=qsum/S-Math.log(Math.log(p))-B;
    const upper=(qsum+count)/S-Math.log(Math.log(p))-B;
    if(lower<min){min=lower;minAt={x:p,side:'inclusive'};}
    if(upper>max){max=upper;maxAt={x:p,side:'inclusive'};}
  }
  previous=p;
};
addPrime(2);
const start=Date.now();
for(let lo=3;lo<=X;lo+=width) {
  const hi=Math.min(lo+width-2,X), size=Math.floor((hi-lo)/2)+1;
  const composite=new Uint8Array(size);
  for(const p of primes) {
    if(p===2) continue;
    if(p*p>hi) break;
    let first=Math.max(p*p,Math.ceil(lo/p)*p);
    if(first%2===0) first+=p;
    for(let j=(first-lo)/2;j<size;j+=p) composite[j]=1;
  }
  for(let j=0;j<size;j++) if(!composite[j]) addPrime(lo+2*j);
  if(hi>=U) {
    const endpoint=Math.min(lo+width-1,X);
    const lower=qsum/S-Math.log(Math.log(endpoint))-B;
    const upper=(qsum+count)/S-Math.log(Math.log(endpoint))-B;
    if(lower<min){min=lower;minAt={x:endpoint,side:'endpoint'};}
    if(upper>max){max=upper;maxAt={x:endpoint,side:'endpoint'};}
    blocks.push({endpoint,count,qsum,lower,upper});
  }
  if(lo===3 || (lo-3)%200_000_000===0) console.log(JSON.stringify({through:Math.min(lo+width-1,X),count,seconds:(Date.now()-start)/1000}));
}
// Also evaluate U; the first prime >= U left limit is a valid lower extreme,
// but U can be the upper extreme on the initial prime gap. Recompute its
// prefix from the saved block containing U (the first block ends at 4000002,
// which is composite; no prime lies in [4000000,4000002]).
const first=blocks[0];
if(first.endpoint!==4000002) throw Error('initial block contract changed');
const atU={lower:first.qsum/S-Math.log(Math.log(U))-B,
  upper:(first.qsum+first.count)/S-Math.log(Math.log(U))-B};
if(atU.lower<min){min=atU.lower;minAt={x:U,side:'endpoint'};}
if(atU.upper>max){max=atU.upper;maxAt={x:U,side:'endpoint'};}
const result={classification:'EXPLORATORY_NOT_LEAN_VERIFIED',X,U,primeCount:count,
  scale:S,integerReciprocalSum:qsum,reciprocalRoundingWidth:count/S,
  b1Reference:B,b1ReferenceFormallyCertified:false,
  finiteErrorLower:min,finiteErrorUpper:max,minAt,maxAt,atU,
  seconds:(Date.now()-start)/1000,blocks,
  unresolved:['sieve completeness proof','log-log interval certificates',
    'B1 enclosure proof','kernel checking of the fixed-point certificate']};
fs.writeFileSync(process.argv[3]||'hybrid-prime-scan.json',JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify({...result,blocks:undefined},null,2));
