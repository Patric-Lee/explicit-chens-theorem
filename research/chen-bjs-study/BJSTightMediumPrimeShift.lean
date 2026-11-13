/- Threshold-specialized companion to research/chen-effective/NumericalMediumPrimeShift.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.TightBudget. -/
import BJSTightMediumPrimeSum
import NumericalGoldbachProduct

noncomputable section
namespace ChenEffective.TightBudget
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def mediumPrimeBudget : ℕ := 1000000000000
def mediumPrimeEpsilon : ℝ := 1/(120*(mediumPrimeBudget : ℝ))
def mediumPrimeSumThreshold : ℕ := max primePairThreshold ((mediumPrimeBudget+2)^10)

theorem numerical_medium_epsilon : 0 < mediumPrimeEpsilon ∧ mediumPrimeEpsilon < 1/60 := by
  norm_num [mediumPrimeEpsilon,mediumPrimeBudget]

theorem numerical_medium_prime_reciprocal {N : ℕ} (hN : primePairThreshold ≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/((q : ℝ)-1)) ≤ 22 := by
  obtain ⟨h9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have he : (18000000000000 : ℝ)/Real.log (N : ℝ) ≤ 1 := (div_le_one (by linarith only [hlog])).mpr (by linarith only [hlog])
  have hm := numerical_prime_pair_interval hN (a := 1/10) (b := 1/3) (by norm_num) (by norm_num) (by norm_num)
  have hl := (numerical_prime_pair_log_mass (a := 1/10) (b := 1/3) (by norm_num) (by norm_num) (by norm_num)).2
  have hsum : (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/((q : ℝ)-1)) ≤
      2*PrimeReciprocalLogScale.primeReciprocalLogInterval N (1/10) (1/3) := by
    rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor (by omega : 1 ≤ N)]
    unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
    rw [← numerical_prime_interval_carrier,Finset.mul_sum]
    apply sum_le_sum
    intro q hq
    have hprime := (mem_filter.mp hq).2
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hprime.two_le
    have hq0 : (0 : ℝ) < q := by linarith only [hq2]
    have hqm : 0 < (q : ℝ)-1 := by linarith only [hq2]
    rw [show (2 : ℝ)*(1/(q : ℝ))=2/(q : ℝ) by ring,div_le_div_iff₀ hqm hq0]
    linarith only [hq2]
  linarith only [hsum,hm,hl,he]

theorem numerical_medium_prime_shifted {N : ℕ} (hN : mediumPrimeSumThreshold ≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1)) ≤
        mediumPrimeIntegral+1/10000000 := by
  have hPair : primePairThreshold ≤ N := (le_max_left _ _).trans hN
  obtain ⟨h9,_,_,_⟩ := numerical_prime_pair_parameters hPair
  let d : ℝ := 1/(mediumPrimeBudget : ℝ)
  have hd : 0 < d := by norm_num [d,mediumPrimeBudget]
  have hpert : 1/(1-6*mediumPrimeEpsilon) ≤ 1+d := by norm_num [mediumPrimeEpsilon,d,mediumPrimeBudget]
  have he0 := numerical_medium_epsilon.1
  have he := numerical_medium_epsilon.2
  have hcut : mediumPrimeBudget+1 ≤ jurkatRichertSourceZ N-1 := numerical_source_cutoff
    (by norm_num [mediumPrimeBudget]) ((le_max_right _ _).trans hN)
  have hroot : (mediumPrimeBudget : ℝ)+1 ≤ (N : ℝ)^(1/10 : ℝ) := by
    have hh : ((mediumPrimeBudget+1 : ℕ) : ℝ) ≤ (jurkatRichertSourceZ N-1 : ℕ) := by exact_mod_cast hcut
    have hfloor : ((jurkatRichertSourceZ N-1 : ℕ) : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) := by
      simpa only [jurkatRichertSourceZ,Nat.add_sub_cancel] using Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/10 : ℝ))
    simpa only [Nat.cast_add,Nat.cast_one] using hh.trans hfloor
  have hsum : (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1)) ≤
        (1+d)^2*MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3) := by
    have hterm (q : ℕ) (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
        jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)/((q : ℝ)-1) ≤
          (1+d)^2*(mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ))/(q : ℝ)) := by
      obtain ⟨_,hprime,hlo,_⟩ := mem_filter.mp hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hprime.pos
      have hq1 : (1 : ℝ) < q := by exact_mod_cast hprime.one_lt
      have hqm : 0 < (q : ℝ)-1 := by linarith only [hq1]
      have hqLarge : (mediumPrimeBudget : ℝ)+1 < q := hroot.trans_lt hlo
      have hinv : 1/((q : ℝ)-1) ≤ (1+d)/(q : ℝ) := by
        rw [div_le_div_iff₀ hqm hq0]
        norm_num [d,mediumPrimeBudget] at hqLarge ⊢
        have hqReal : (1000000000001 : ℝ) < q := by exact_mod_cast hqLarge
        linarith only [hqReal]
      have hlog := jurkatRichertSourceMediumPrime_log_mem (show 1 < N by omega) hq
      have hf0 := jurkatRichertUpperLinearSieveFactor_zeroEpsilon_nonneg hlog
      have hf := jurkatRichertUpperLinearSieveFactor_perturbation he0 he hlog
      have hratio : jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon =
          5-10*mediumPrimeEpsilon-10*(Real.log (q : ℝ)/Real.log (N : ℝ)) := by
        rw [jurkatRichertSourceUpperSieveRatio_eq_zero_sub (by omega : 1 < N) hprime.pos,
          jurkatRichertSourceUpperSieveRatio_zero (by omega : 1 < N) hprime.pos]
        ring
      rw [hratio]
      calc
        _ ≤ (1/(1-6*mediumPrimeEpsilon)*mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ)))/((q : ℝ)-1) := div_le_div_of_nonneg_right hf hqm.le
        _ ≤ ((1+d)*mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ)))/((q : ℝ)-1) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpert hf0) hqm.le
        _ = ((1+d)*mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ)))*(1/((q : ℝ)-1)) := by ring
        _ ≤ ((1+d)*mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ)))*((1+d)/(q : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (mul_nonneg (by positivity) hf0)
        _ = _ := by ring
    calc
      _ ≤ ∑ q ∈ jurkatRichertSourceMediumPrimes N, (1+d)^2*(mediumPrimeProfile (Real.log (q : ℝ)/Real.log (N : ℝ))/(q : ℝ)) := sum_le_sum hterm
      _ = _ := by
        rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor (by omega : 1 ≤ N)]
        unfold MertensTheorem.weightedPrimeReciprocalLogSum
        rw [Finset.mul_sum]
  have htransfer := hsum.trans (mul_le_mul_of_nonneg_left (numerical_medium_prime_unshifted hPair) (sq_nonneg (1+d)))
  have hcap := numerical_medium_integral_caps.2
  have hcoef : (1+d)^2*(mediumPrimeIntegral+1/100000000) ≤ mediumPrimeIntegral+1/10000000 := by
    norm_num [d,mediumPrimeBudget]
    linarith only [hcap]
  exact htransfer.trans hcoef

#print axioms numerical_medium_prime_reciprocal
#print axioms numerical_medium_prime_shifted
end ChenEffective.TightBudget
