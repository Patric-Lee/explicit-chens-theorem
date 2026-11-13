// Untrusted feasibility data; the Lean checker must replay every segment.
import fs from 'node:fs';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
const U=4000000,R=Number(process.argv[2]||10000000000),spacing=32000;
if(!Number.isSafeInteger(R)||R<=U||R%2)throw Error('invalid endpoint');
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

const primes=[],marked=new Uint8Array(Math.floor(Math.sqrt(R))+1);
for(let p=2;p<marked.length;p++)if(!marked[p]){
  primes.push(p);for(let n=p*p;n<marked.length;n+=p)marked[n]=1;
}
const start=Date.now(),counts=[],groups=[],grid=[];
let A=U,w,W,h,c=0,Qlo=0n,Qhi=0n,next=U,lastW=null;
function setWidth(){
  w=Math.max(0,Math.floor(Math.log2(Math.sqrt(A)))-6); W=2**w;
  while(2*W>R-A){w--;W/=2;}h=2*W;
  if(w<0)throw Error('odd remainder');
  if(w!==lastW){groups.push({lo:A+1,w,offset:counts.length});lastW=w;}
}
function record(){
 const ll=loglogInteger(A);grid.push({x:A,lower:Qlo.toString(),upper:Qhi.toString(),
  llLower:ll[0].toString(),llUpper:ll[1].toString()});
 next=A+Math.max(1,Math.floor(A/spacing));
}
setWidth();record();
function finish(){
 const cb=BigInt(c),a=BigInt(A),b=BigInt(A+h);
 Qlo+=SB*cb/b;Qhi+=ceilDiv(SB*cb,a);counts.push(c);c=0;A+=h;
 if(A>=next||A===R)record();
 if(A<R)setWidth();
}
const slab=4000000;
for(let lo=U+1;lo<R;lo+=slab){
 const hi=Math.min(R-1,lo+slab-2),len=(hi-lo)/2+1,bits=new Uint8Array(len);
 for(const p of primes){if(p===2)continue;if(p*p>hi)break;
  let first=Math.max(p*p,Math.ceil(lo/p)*p);if(first%2===0)first+=p;
  for(let i=(first-lo)/2;i<len;i+=p)bits[i]=1;
 }
 for(let i=0;i<len;i++)if(!bits[i]){
  const p=lo+2*i;while(p>A+h)finish();c++;
 }
}
while(A<R)finish();
const end=grid.at(-1);let low=0n,high=0n,minWitness,maxWitness;
for(let i=1;i<grid.length;i++){
 const a=grid[i-1],b=grid[i];
 // Negative suffix: the two independently accumulated interval components
 // cancel exactly, retaining only uncertainty after the grid endpoint.
 const l=-(Qhi-BigInt(a.upper))-BigInt(b.llUpper)+BigInt(end.llLower);
 const u=-(Qlo-BigInt(b.lower))-BigInt(a.llLower)+BigInt(end.llUpper);
 if(l<low){low=l;minWitness={a:a.x,b:b.x};}
 if(u>high){high=u;maxWitness={a:a.x,b:b.x};}
}
const out=process.argv[3]||'platt-block-relative';
const raw=Buffer.alloc(2*counts.length);for(let i=0;i<counts.length;i++)raw.writeUInt16LE(counts[i],2*i);
const data={scale:SB.toString(),U,R,groups,grid,countEncoding:'uint16-le',
 countSha256:crypto.createHash('sha256').update(raw).digest('hex')};
fs.writeFileSync(out+'.counts.bin.gz',zlib.gzipSync(raw));
fs.writeFileSync(out+'.grid.json.gz',zlib.gzipSync(JSON.stringify(data)));
const result={classification:'UNTRUSTED_BLOCK_SCAN_NOT_LEAN_VERIFIED',U,R,
 blocks:counts.length,groups:groups.length,points:grid.length,
 lower:Number(low)/S,upper:Number(high)/S,minWitness,maxWitness,
 totalReciprocalUncertainty:Number(Qhi-Qlo)/S,
 pass:low*20000n>=-SB&&high*20000n<=SB,seconds:(Date.now()-start)/1000,
 ...{countSha256:data.countSha256}};
fs.writeFileSync(out+'.json',JSON.stringify(result,null,2)+'\n');console.log(result);
