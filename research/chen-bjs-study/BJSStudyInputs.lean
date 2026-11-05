import BJSIntervalOrder

/-! PROVISIONAL: user-authorized BJS assumptions, excluded from production.
The density declarations are adapters of Theorem 6 at epsilon=1/2000,
rounding both Table 1 constants up to 110. A factor-two product slack
preserves the paper's strict product hypothesis. These adapters still
require proofs on the project's exact Rosser weights.
The interval declaration is the finite-subset consequence of Lemma 21.
Reference: https://arxiv.org/html/2207.09452v6
-/
noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false

axiom bjsStudy_interval (s : Finset ℕ) (a b : ℝ) (ha : 1 < a) (hb : 286 ≤ b)
    (hab : a ≤ b)
    (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p ∈ s, 1/(p : ℝ)) ≤ log (log b/log a)+1/(log a)^2

axiom bjsStudy_lower_density {S : BoundingSieve} {s : ℝ}
    (hrel : HasRelativeSieveProduct S (1/4000))
    (D z : ℕ) (hD : 1 < D) (hs4 : 4 ≤ s) (hs5 : s ≤ 5)
    (hz : z=⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
      (dimensionOneLowerLinearSieveFactor s-110*(1/2000 : ℝ)*exp 2*sieveHat s) ≤
        S.mainSum (lowerRosserWeight S.prodPrimes D)

axiom bjsStudy_upper_density {S : BoundingSieve} {s : ℝ}
    (hrel : HasRelativeSieveProduct S (1/4000))
    (D z : ℕ) (hD : 1 < D) (hslo : 3/2 ≤ s) (hshi : s ≤ 4)
    (hz : z=⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    S.mainSum (upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (jurkatRichertUpperLinearSieveFactor s+110*(1/2000 : ℝ)*exp 2*sieveHat s)

def bjsStudyBudget : ChenBudget := ⟨1/20,113/100,1/20000,3.94033,1/100⟩

theorem bjsStudy_budget_positive : 0 < bjsStudyBudget.margin := by
  norm_num [bjsStudyBudget,ChenBudget.margin,ChenBudget.weighted]

end ChenEffective
