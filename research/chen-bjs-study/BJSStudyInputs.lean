import BJSIntervalOrder
import BJSSharpDensity

/-! The density adapters are now proved for the exact project Rosser weights.
Their error is 220*(1/4000)=110*(1/2000), established by certified early
continuous layers, an analytic tail, discrete induction and parity sums.
The product input is supplied by BJSProvedProductProfile. No BJS axiom remains.
Reference: https://arxiv.org/html/2207.09452v6
-/
noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false

theorem bjsStudy_lower_density {S : BoundingSieve} {s : ℝ}
    (hrel : HasRelativeSieveProduct S (1/4000))
    (D z : ℕ) (hD : 1 < D) (hs4 : 4 ≤ s) (hs5 : s ≤ 5)
    (hz : z=⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
      (dimensionOneLowerLinearSieveFactor s-110*(1/2000 : ℝ)*exp 2*sieveHat s) ≤
        S.mainSum (lowerRosserWeight S.prodPrimes D) := by
  have hh := bjs_sharp_relative_lower_rosser_density (ε:=1/4000)
    (by norm_num) le_rfl hrel D z hD hs4 hs5 hz hzD hcut
  norm_num at hh ⊢
  exact hh

theorem bjsStudy_upper_density {S : BoundingSieve} {s : ℝ}
    (hrel : HasRelativeSieveProduct S (1/4000))
    (D z : ℕ) (hD : 1 < D) (hslo : 3/2 ≤ s) (hshi : s ≤ 4)
    (hz : z=⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    S.mainSum (upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (jurkatRichertUpperLinearSieveFactor s+110*(1/2000 : ℝ)*exp 2*sieveHat s) := by
  have hh := bjs_sharp_relative_upper_rosser_density (ε:=1/4000)
    (by norm_num) le_rfl hrel D z hD hslo hshi hz hzD hcut
  norm_num at hh ⊢
  exact hh

def bjsStudyBudget : ChenBudget := ⟨1/20,113/100,1/20000,3.94033,1/100⟩

theorem bjsStudy_budget_positive : 0 < bjsStudyBudget.margin := by
  norm_num [bjsStudyBudget,ChenBudget.margin,ChenBudget.weighted]

#print axioms bjsStudy_lower_density
#print axioms bjsStudy_upper_density
end ChenEffective
