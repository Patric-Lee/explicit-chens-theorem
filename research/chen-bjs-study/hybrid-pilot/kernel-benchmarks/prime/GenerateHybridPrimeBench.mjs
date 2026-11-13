import fs from 'node:fs';
const S=1n<<48n;
const qq=String.fromCharCode(96,96);
for(const N of process.argv.slice(2).map(Number)){
 const a=new Uint8Array(N+1);let Q=0n,C=0;
 for(let p=2;p<=N;p++)if(!a[p]){
   Q+=S/BigInt(p);C++;
   if(p*p<=N)for(let j=p*p;j<=N;j+=p)a[j]=1;
 }
 const name='BJSHybridPrimeBatch'+N;
 fs.writeFileSync(new URL(name+'.lean',import.meta.url),`import BJSHybridPrimeCertificate
import Lean.Util.CollectAxioms
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ChenEffective.HybridProduct
theorem batch_${N} : fixedPrimePrefix (2^48) ${N}=(${Q},${C}) := by decide +kernel
theorem batch_${N}_actual :
    (${Q}:ℝ)/(2^48) ≤ AnalyticNumberTheory.Mertens.primeReciprocalSum ${N} ∧
    AnalyticNumberTheory.Mertens.primeReciprocalSum ${N} ≤ ((${Q}:ℝ)+${C})/(2^48) :=
  by simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero] using prime_prefix_of_certificate (by norm_num) batch_${N}
#print axioms batch_${N}_actual
open Lean Meta in
run_elab do
  let axs ← Lean.collectAxioms ${qq}batch_${N}_actual
  unless axs.all (#[${qq}propext,${qq}Classical.choice,${qq}Quot.sound]).contains do
    throwError "Unexpected prime certificate axiom: {axs}"
end ChenEffective.HybridProduct
`);
 console.log(JSON.stringify({N,Q:Q.toString(),C,module:name}));
}



