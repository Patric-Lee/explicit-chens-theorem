import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
const N=Number(process.argv[2]??100000), shardSize=Number(process.argv[3]??8192), out=process.argv[4]??fileURLToPath(new URL('./benchmarks/',import.meta.url));
if(!Number.isSafeInteger(N)||N<1||N>1000000||!Number.isSafeInteger(shardSize)||shardSize<1||shardSize>10000)throw Error('Invalid bounded benchmark size');
const chunk=128,S=1n<<48n,B=1n<<64n,qq=String.fromCharCode(96,96);
const composite=new Uint8Array(N+1);for(let p=2;p*p<=N;p++)if(!composite[p])for(let j=p*p;j<=N;j+=p)composite[j]=1;
const prime=p=>p>=2&&!composite[p];
const parts=[]; const modules=[];
function emitAssembly(lines,arr,root,begin,len){
 let total=0n;
 for(let j=arr.length-1;j>=0;j--){const c=arr[j];total+=c.packed;
  lines.push(`private theorem ${root}Tail${j} : packedRange bits${N} ${S} ${c.start} ${begin+len-c.start}=${total} := by`);
  if(j===arr.length-1)lines.push(`  exact ${c.name}`);else lines.push(`  exact packedRange_join (bits:=bits${N}) (scale:=${S}) (start:=${c.start}) (len:=${begin+len-c.start})\n    (a:=${c.len}) (b:=${begin+len-c.start-c.len}) (qA:=${c.packed}) (qB:=${total-c.packed})\n    (by decide) ${c.name} ${root}Tail${j+1}`);
 }
 return total;
}
for(let start=0,i=0;start<=N;start+=shardSize,i++){
 const len=Math.min(shardSize,N+1-start),m=`BJSHybridSieveShard${N}P${i}`,ns=`Shard${N}P${i}`;
 const lines=[`import BJSHybridSieveData${N}`,'import BJSHybridSievePacked',`namespace ChenEffective.HybridProduct.SieveBench.${ns}`,'open ChenEffective.HybridProduct.BitSieve',`open ChenEffective.HybridProduct.SieveBench`,'set_option maxRecDepth 100000','set_option maxHeartbeats 2000000'];
 const checks=[];let Q=0n,C=0;
 for(let a=start,j=0;a<start+len;a+=chunk,j++){
  const k=Math.min(chunk,start+len-a);let q=0n,c=0;for(let p=a;p<a+k;p++)if(prime(p)){q+=S/BigInt(p);c++;}Q+=q;C+=c;
  const z=q*B+BigInt(c),name='step'+j;
  lines.push(`private theorem check${j} : (packedRange bits${N} ${S} ${a} ${k}).beq ${z} := by decide +kernel`,
   `private theorem ${name} : packedRange bits${N} ${S} ${a} ${k}=${z} := Nat.beq_eq.mp check${j}`);
  checks.push({start:a,len:k,packed:z,name});
 }
 const packed=emitAssembly(lines,checks,'sum',start,len);
 lines.push(`theorem checked : packedRange bits${N} ${S} ${start} ${len}=${packed} := sumTail0`,'#print axioms checked',`end ChenEffective.HybridProduct.SieveBench.${ns}`);
 fs.writeFileSync(path.join(out,m+'.lean'),lines.join('\n')+'\n');modules.push(m);parts.push({start,len,Q:Q.toString(),C,packed:packed.toString(),module:m,name:`${ns}.checked`});
}
const finalModule=`BJSHybridSieveShardedBench${N}`;
const lines=[...modules.map(m=>'import '+m),'import Lean.Util.CollectAxioms','namespace ChenEffective.HybridProduct.SieveBench','open ChenEffective.HybridProduct.BitSieve','set_option maxRecDepth 100000','set_option maxHeartbeats 2000000'];
const total=emitAssembly(lines,parts.map(p=>({...p,packed:BigInt(p.packed)})),'all',0,N+1);
const Q=parts.reduce((a,p)=>a+BigInt(p.Q),0n),C=parts.reduce((a,p)=>a+p.C,0);
if(total!==Q*B+BigInt(C))throw Error('Packing mismatch');
lines.push(`theorem shardedPrefix${N} : packedRange bits${N} ${S} 0 ${N+1}=${total} := allTail0`,
 `theorem shardedReciprocal${N} : (${Q}:ℝ)/${S} ≤ AnalyticNumberTheory.Mertens.primeReciprocalSum ${N} ∧\n    AnalyticNumberTheory.Mertens.primeReciprocalSum ${N} ≤ ((${Q}:ℝ)+${C})/${S} := by\n  simpa only [Nat.cast_ofNat] using reciprocal_prefix_of_packed_certificate (Q:=${Q}) (count:=${C}) sieveIs${N} (by decide) (by decide) (by decide) shardedPrefix${N}`,
 `#print axioms shardedReciprocal${N}`,'open Lean Meta in','run_elab do',`  let axs ← Lean.collectAxioms ${qq}shardedReciprocal${N}`,`  unless axs.all (#[${qq}propext,${qq}Classical.choice,${qq}Quot.sound]).contains do`,'    throwError "Unexpected sharded certificate axiom: {axs}"','end ChenEffective.HybridProduct.SieveBench');
fs.writeFileSync(path.join(out,finalModule+'.lean'),lines.join('\n')+'\n');
const meta={N,shardSize,chunk,scale:S.toString(),packingBase:B.toString(),Q:Q.toString(),primeCount:C,parts,modules:[...modules,finalModule]};
fs.writeFileSync(path.join(out,'sieve-shards-'+N+'.json'),JSON.stringify(meta,null,2)+'\n');
console.log(JSON.stringify({N,shards:parts.length,Q:Q.toString(),primeCount:C,modules:meta.modules}));
