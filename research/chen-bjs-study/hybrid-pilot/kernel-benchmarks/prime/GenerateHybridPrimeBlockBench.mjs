import fs from 'node:fs';
const lo=900, hi=1001, S=1n<<48n; let Q=0n,C=0;
for(let n=lo;n<hi;n++){let p=n>1;for(let d=2;d*d<=n;d++)if(n%d===0){p=false;break}if(p){Q+=S/BigInt(n);C++}}
const qq=String.fromCharCode(96,96);
fs.writeFileSync(new URL('BJSHybridPrimeBlock900.lean',import.meta.url),`import BJSHybridPrimeBlock
import Lean.Util.CollectAxioms
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ChenEffective.HybridProduct
theorem block900 : fixedPrimeBlock (2^48) 900 1001=(${Q},${C}) := by decide +kernel
theorem block900_actual : (${Q}:ℝ)/(2^48) ≤ ∑ p ∈ blockPrimes 900 1001,1/(p:ℝ) ∧
  (∑ p ∈ blockPrimes 900 1001,1/(p:ℝ)) ≤ ((${Q}:ℝ)+${C})/(2^48) := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using prime_block_of_certificate (by norm_num) block900
#print axioms block900_actual
open Lean Meta in
run_elab do
  let axs ← Lean.collectAxioms ${qq}block900_actual
  unless axs.all (#[${qq}propext,${qq}Classical.choice,${qq}Quot.sound]).contains do
    throwError "Unexpected certificate axiom: {axs}"
end ChenEffective.HybridProduct
`);
console.log(JSON.stringify({lo,hi,Q:Q.toString(),C}));

