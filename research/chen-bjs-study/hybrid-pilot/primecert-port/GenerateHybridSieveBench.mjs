import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
const args=process.argv.slice(2); let out=fileURLToPath(new URL('./benchmarks/',import.meta.url)), sumChunk=128, sieveChunk=8; const bounds=[];
for(let i=0;i<args.length;i++){
 if(args[i]==='--out') out=args[++i];
 else if(args[i]==='--sum-chunk') sumChunk=Number(args[++i]);
 else if(args[i]==='--sieve-chunk') sieveChunk=Number(args[++i]);
 else bounds.push(Number(args[i]));
}
if(!bounds.length) bounds.push(1000);
for(const x of [sumChunk,sieveChunk]) if(!Number.isSafeInteger(x)||x<1)throw Error('Invalid batch size');
fs.mkdirSync(out,{recursive:true}); const S=1n<<48n;
const idx=n=>Math.floor(Math.max(0,n-1)/3), val=k=>3*k+1+k%2;
const qq=String.fromCharCode(96,96); const rows=[];
for(const N of bounds){
 if(!Number.isSafeInteger(N)||N<0||N>1000000)throw Error('Small benchmark bounds must lie in [0,1000000]');
 const sq=Math.ceil(Math.sqrt(N)), M=idx(N), fuel=idx(sq);
 let bits=(1n<<BigInt(M+1))-2n; const states=[];
 for(let start=1;start<=fuel;start+=sieveChunk){
  const count=Math.min(sieveChunk,fuel-start+1), before=bits;
  for(let j=start;j<start+count;j++)if((bits>>BigInt(j))&1n){
   const p=val(j); let mask=(1n<<BigInt(idx(p*5)))|(1n<<BigInt(idx(p*7)));
   for(let k=0;k<32;k++){const shift=BigInt(p)<<BigInt(k+1);if(shift<=M)mask|=mask<<shift;}
   bits-=bits&mask;
  }
  states.push({start,count,before,after:bits});
 }
 const comp=new Uint8Array(N+1); for(let p=2;p*p<=N;p++)if(!comp[p])for(let m=p*p;m<=N;m+=p)comp[m]=1;
 const prime=n=>n>=2&&!comp[n];
 for(let n=0;n<=N;n++){
  const read=n<5?(n===2||n===3):((n%6===1||n%6===5)&&!!((bits>>BigInt(idx(n)))&1n));
  if(read!==prime(n))throw Error('Independent generator cross-check failed at '+n);
 }
 const dataName='BJSHybridSieveData'+N, sumName='BJSHybridSieveSum'+N;
 const lines=['import BJSHybridSieveCorrect','namespace ChenEffective.HybridProduct.SieveBench','open ChenEffective.HybridProduct.BitSieve','set_option maxRecDepth 100000','set_option maxHeartbeats 2000000',`def bits${N} : Nat := ${bits}`];
 states.forEach((st,i)=>{const prev=i===0?`(initK ${M})`:`state${N}_${i}`;const next=i+1===states.length?`bits${N}`:`state${N}_${i+1}`;
  if(i+1!==states.length)lines.push(`private def ${next} : Nat := ${st.after}`);
  lines.push(`private theorem sieveStep${N}_${i+1} : (sieveLoopK ${M} ${prev} ${st.start} ${st.count}).beq ${next} := by decide +kernel`);
 });
 lines.push(`theorem sieveData${N} : sieveK ${N} ${sq} = bits${N} := by`);
 if(!states.length)lines.push('  rfl');else{
  lines.push(`  have h0 : sieveK ${N} ${sq} = sieveLoopK ${M} (initK ${M}) 1 ${fuel} := rfl`);
  states.forEach((st,i)=>{if(i+1===states.length)lines.push(`  exact sieveLoopK_last h${i} sieveStep${N}_${i+1}`);else lines.push(`  have h${i+1} : sieveK ${N} ${sq} = sieveLoopK ${M} state${N}_${i+1} ${st.start+st.count} ${fuel-(st.start-1)-st.count} := sieveLoopK_chain (len:=${st.count}) (rest:=${fuel-(st.start-1)-st.count}) h${i} sieveStep${N}_${i+1}`);});
 }
 lines.push(`theorem sieveIs${N} : IsSieve ${N} bits${N} := isSieve_of_sieveK_eq sieveData${N} (by decide) (by decide)`,`#print axioms sieveIs${N}`,'end ChenEffective.HybridProduct.SieveBench');
 fs.writeFileSync(path.join(out,dataName+'.lean'),lines.join('\n')+'\n');
 const chunks=[];let totalQ=0n,totalCount=0;
 for(let start=0;start<=N;start+=sumChunk){let Q=0n,C=0;const len=Math.min(sumChunk,N+1-start);for(let p=start;p<start+len;p++)if(prime(p)){Q+=S/BigInt(p);C++;}chunks.push({start,len,Q,C});totalQ+=Q;totalCount+=C;}
 const sl=[`import ${dataName}`,'import BJSHybridSieveSums','import Lean.Util.CollectAxioms','namespace ChenEffective.HybridProduct.SieveBench','open ChenEffective.HybridProduct.BitSieve','set_option maxRecDepth 100000','set_option maxHeartbeats 2000000'];
 chunks.forEach((c,i)=>sl.push(`private theorem sumStep${N}_${i} : fixedSieveRange bits${N} ${S} ${c.start} ${c.len} = (${c.Q},${c.C}) := by decide +kernel`));
 let qTail=0n,cTail=0;
 for(let i=chunks.length-1;i>=0;i--){const c=chunks[i];qTail+=c.Q;cTail+=c.C;sl.push(`private theorem sumTail${N}_${i} : fixedSieveRange bits${N} ${S} ${c.start} ${N+1-c.start} = (${qTail},${cTail}) := by`);
  if(i===chunks.length-1)sl.push(`  exact sumStep${N}_${i}`);else sl.push(`  calc\n    _ = ((fixedSieveRange bits${N} ${S} ${c.start} ${c.len}).1+(fixedSieveRange bits${N} ${S} ${c.start+c.len} ${N+1-c.start-c.len}).1,\n         (fixedSieveRange bits${N} ${S} ${c.start} ${c.len}).2+(fixedSieveRange bits${N} ${S} ${c.start+c.len} ${N+1-c.start-c.len}).2) := fixedSieveRange_add _ _ _ ${c.len} ${N+1-c.start-c.len}\n    _ = _ := by rw [sumStep${N}_${i},sumTail${N}_${i+1}]; rfl`);
 }
 sl.push(`theorem prefix${N} : fixedSieveRange bits${N} ${S} 0 ${N+1}=(${totalQ},${totalCount}) := sumTail${N}_0`,
 `theorem reciprocal${N} : (${totalQ}:ℝ)/${S} ≤ AnalyticNumberTheory.Mertens.primeReciprocalSum ${N} ∧\n    AnalyticNumberTheory.Mertens.primeReciprocalSum ${N} ≤ ((${totalQ}:ℝ)+${totalCount})/${S} := by\n  simpa only [Nat.cast_ofNat] using reciprocal_prefix_of_sieve_certificate sieveIs${N} (by decide) prefix${N}`,
 `#print axioms reciprocal${N}`,'open Lean Meta in','run_elab do',`  let axs ← Lean.collectAxioms ${qq}reciprocal${N}`,`  unless axs.all (#[${qq}propext,${qq}Classical.choice,${qq}Quot.sound]).contains do`, '    throwError "Unexpected sieve certificate axiom: {axs}"','end ChenEffective.HybridProduct.SieveBench');
 fs.writeFileSync(path.join(out,sumName+'.lean'),sl.join('\n')+'\n');
 const bad=[`import ${dataName}`,'import BJSHybridSieveSums','open ChenEffective.HybridProduct.BitSieve ChenEffective.HybridProduct.SieveBench','set_option maxRecDepth 100000',`example : fixedSieveRange bits${N} ${S} ${chunks[0].start} ${chunks[0].len}=(${chunks[0].Q+1n},${chunks[0].C}) := by decide +kernel`];
 fs.writeFileSync(path.join(out,'BJSHybridSieveBadSum'+N+'.lean'),bad.join('\n')+'\n');
 if(states.length){const st=states[0]; fs.writeFileSync(path.join(out,'BJSHybridSieveBadData'+N+'.lean'),`import BJSHybridSieveCorrect\nopen ChenEffective.HybridProduct.BitSieve\nexample : (sieveLoopK ${M} (initK ${M}) 1 ${st.count}).beq ${st.after^2n} := by decide +kernel\n`);}
 const B=1n<<64n, packedName='BJSHybridSievePackedBench'+N;
 const pl=[`import ${dataName}`,'import BJSHybridSievePacked','import Lean.Util.CollectAxioms',
  'namespace ChenEffective.HybridProduct.SieveBench','open ChenEffective.HybridProduct.BitSieve',
  'set_option maxRecDepth 100000','set_option maxHeartbeats 2000000'];
 chunks.forEach((c,i)=>pl.push(`private theorem packedStep${N}_${i} : packedRange bits${N} ${S} ${c.start} ${c.len} = ${c.Q*B+BigInt(c.C)} := by decide +kernel`));
 let pq=0n, pc=0;
 for(let i=chunks.length-1;i>=0;i--){const c=chunks[i];pq+=c.Q;pc+=c.C;
  pl.push(`private theorem packedTail${N}_${i} : packedRange bits${N} ${S} ${c.start} ${N+1-c.start} = ${pq*B+BigInt(pc)} := by`);
  if(i===chunks.length-1)pl.push(`  exact packedStep${N}_${i}`);
  else pl.push(`  exact packedRange_join (bits:=bits${N}) (scale:=${S}) (start:=${c.start}) (len:=${N+1-c.start})\n    (a:=${c.len}) (b:=${N+1-c.start-c.len}) (qA:=${c.Q*B+BigInt(c.C)}) (qB:=${(pq-c.Q)*B+BigInt(pc-c.C)})\n    (by decide) packedStep${N}_${i} packedTail${N}_${i+1}`);
 }
 pl.push(`theorem packedPrefix${N} : packedRange bits${N} ${S} 0 ${N+1}=${totalQ*B+BigInt(totalCount)} := packedTail${N}_0`,
  `theorem packedReciprocal${N} : (${totalQ}:ℝ)/${S} ≤ AnalyticNumberTheory.Mertens.primeReciprocalSum ${N} ∧\n    AnalyticNumberTheory.Mertens.primeReciprocalSum ${N} ≤ ((${totalQ}:ℝ)+${totalCount})/${S} := by\n  simpa only [Nat.cast_ofNat] using reciprocal_prefix_of_packed_certificate (Q:=${totalQ}) (count:=${totalCount}) sieveIs${N} (by decide) (by decide) (by decide) packedPrefix${N}`,
  `#print axioms packedReciprocal${N}`,'open Lean Meta in','run_elab do',`  let axs ← Lean.collectAxioms ${qq}packedReciprocal${N}`,
  `  unless axs.all (#[${qq}propext,${qq}Classical.choice,${qq}Quot.sound]).contains do`,
  '    throwError "Unexpected packed certificate axiom: {axs}"','end ChenEffective.HybridProduct.SieveBench');
 fs.writeFileSync(path.join(out,packedName+'.lean'),pl.join('\n')+'\n');
 // Boolean batch equations follow PrimeCert's replay interface directly.
 // Translate each accepted Boolean equation to Nat equality without asking
 // the kernel to run DecidableEq on the large packed result itself.
 let boolText=pl.join('\n').replaceAll('packedStep','boolPackedStep')
  .replaceAll('packedTail','boolPackedTail').replaceAll('packedPrefix','boolPackedPrefix')
  .replaceAll('packedReciprocal','boolPackedReciprocal');
 for(let i=0;i<chunks.length;i++){
  const c=chunks[i], z=c.Q*B+BigInt(c.C);
  boolText=boolText.replace(
   `private theorem boolPackedStep${N}_${i} : packedRange bits${N} ${S} ${c.start} ${c.len} = ${z} := by decide +kernel`,
   `private theorem boolPackedCheck${N}_${i} : (packedRange bits${N} ${S} ${c.start} ${c.len}).beq ${z} := by decide +kernel\nprivate theorem boolPackedStep${N}_${i} : packedRange bits${N} ${S} ${c.start} ${c.len} = ${z} := Nat.beq_eq.mp boolPackedCheck${N}_${i}`);
 }
 fs.writeFileSync(path.join(out,'BJSHybridSieveBoolBench'+N+'.lean'),boolText+'\n');
 const serialText=boolText.replaceAll('boolPacked','serialPacked')
  .replace('namespace ChenEffective.HybridProduct.SieveBench',
    'set_option Elab.async false\nnamespace ChenEffective.HybridProduct.SieveBench');
 fs.writeFileSync(path.join(out,'BJSHybridSieveSerialBench'+N+'.lean'),serialText+'\n');
 fs.writeFileSync(path.join(out,'BJSHybridSieveBadPacked'+N+'.lean'),`import ${dataName}\nimport BJSHybridSievePacked\nopen ChenEffective.HybridProduct.BitSieve ChenEffective.HybridProduct.SieveBench\nexample : (packedRange bits${N} ${S} 0 ${chunks[0].len}).beq ${chunks[0].Q*B+BigInt(chunks[0].C)+1n} := by\n  unfold packedRange\n  decide +kernel\n`);
 rows.push({N,scale:S.toString(),sqrtBound:sq,wheelBits:M+1,sieveChunk,sieveBatches:states.length,sumChunk,sumBatches:chunks.length,Q:totalQ.toString(),primeCount:totalCount,dataModule:dataName,sumModule:sumName});
}
fs.writeFileSync(path.join(out,'sieve-benchmark-generation.json'),JSON.stringify(rows,null,2)+'\n');
console.log(JSON.stringify(rows));


