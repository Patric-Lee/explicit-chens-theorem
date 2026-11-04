import NumericalUpperFactor
import NumericalPrimePairInterval
import MathlibNt.SieveTheory.Switching.SourceSieve
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace ChenEffective
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

theorem numerical_prime_interval_carrier (N : ℕ) (a b : ℝ) :
    (Finset.Ioc (MertensTheorem.rpowFloor N a) (MertensTheorem.rpowFloor N b)).filter Nat.Prime =
      (Finset.range (PrimeReciprocalLogScale.rpowFloor N b+1)).filter
        (fun p : ℕ => p.Prime ∧ (N : ℝ)^a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ)^b) := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_range,Nat.lt_succ_iff,MertensTheorem.rpowFloor,
    PrimeReciprocalLogScale.rpowFloor,Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) a),
    Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) b)]
  tauto

theorem numerical_medium_profile_integrable {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3) :
    IntervalIntegrable (fun x => mediumPrimeProfile x/x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply (show ContinuousOn mediumPrimeProfile (Icc (1/10 : ℝ) (1/3)) from
      jurkatRichertUpperLinearSieveFactor_zeroEpsilon_continuousOn).mono
    intro x hx
    exact ⟨ha.trans hx.1,hx.2.trans hb⟩
  · exact continuousOn_id
  · intro x hx
    linarith only [ha,hx.1]

/-- A quantitative one-dimensional logarithmic Darboux cell. -/
theorem numerical_medium_prime_cell {N : ℕ} (hN : primePairThreshold ≤ N) {a b : ℝ}
    (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b ≤
      (∫ x in a..b, mediumPrimeProfile x/x)+3600*(b-a)^2+
        192*(18000000000000/Real.log (N : ℝ)) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := ha0.trans_le hab
  let h := b-a
  let e := 18000000000000/Real.log (N : ℝ)
  have hh0 : 0 ≤ h := sub_nonneg.mpr hab
  have hh1 : h ≤ 1 := by dsimp [h]; linarith only [ha,hb]
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  obtain ⟨hf0,hf12,_⟩ := numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha,hab.trans hb⟩
  have htest : MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b ≤
      (mediumPrimeProfile a+180*h)*PrimeReciprocalLogScale.primeReciprocalLogInterval N a b := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
    rw [← numerical_prime_interval_carrier,Finset.mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpc,hprime⟩ := mem_filter.mp hp
    obtain ⟨hpa,hpb⟩ := MertensTheorem.mem_Ioc_rpowFloor_iff.mp hpc
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have halog := Real.log_le_log (Real.rpow_pos_of_pos hN0 a) hpa.le
    have hblog := Real.log_le_log hp0 hpb
    rw [Real.log_rpow hN0] at halog hblog
    have hpinterval : Real.log (p : ℝ)/Real.log (N : ℝ) ∈ Icc a b :=
      ⟨(le_div_iff₀ hL).mpr (by nlinarith only [halog]),(div_le_iff₀ hL).mpr hblog⟩
    have hdiff := (numerical_medium_profile
      ⟨ha.trans hpinterval.1,hpinterval.2.trans hb⟩ ⟨ha,hab.trans hb⟩).2.2
    have habs : |Real.log (p : ℝ)/Real.log (N : ℝ)-a| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hpinterval.1)]
      dsimp [h]
      linarith only [hpinterval.2]
    have hf : mediumPrimeProfile (Real.log (p : ℝ)/Real.log (N : ℝ)) ≤ mediumPrimeProfile a+180*h := by
      have h := (le_abs_self _).trans hdiff
      linarith only [h,habs]
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hf hp0.le
  have hmass := numerical_prime_pair_interval hN ha hab (by linarith only [hb] : b ≤ 1)
  have htest' := htest.trans (mul_le_mul_of_nonneg_left hmass (show 0 ≤ mediumPrimeProfile a+180*h by positivity))
  have hlog0 : 0 ≤ Real.log (b/a) := Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using hab))
  have hlog10 : Real.log (b/a) ≤ 10*h := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have heq : b/a-1 = h/a := by dsimp [h]; field_simp
    apply hh.trans
    rw [heq]
    apply (div_le_iff₀ ha0).mpr
    nlinarith only [ha,mul_nonneg hh0 (sub_nonneg.mpr ha)]
  have hone : IntervalIntegrable (fun x : ℝ => 1/x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id (by intro x hx; linarith only [ha,hx.1])
  have hIntegral : (mediumPrimeProfile a-180*h)*Real.log (b/a) ≤ ∫ x in a..b, mediumPrimeProfile x/x := by
    have hc := intervalIntegral.integral_mono_on hab (hone.const_mul (mediumPrimeProfile a-180*h))
      (numerical_medium_profile_integrable ha hab hb) (fun x hx => ?_)
    · rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos ha0 hb0] at hc
      exact hc
    · have hdiff := (numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha.trans hx.1,hx.2.trans hb⟩).2.2
      have habs : |a-x| ≤ h := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx.1)]
        dsimp [h]
        linarith only [hx.2]
      have hf : mediumPrimeProfile a-180*h ≤ mediumPrimeProfile x := by
        have hh := (le_abs_self _).trans hdiff
        linarith only [hh,habs]
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hf (show 0 ≤ x by linarith only [ha,hx.1])
  have hmesh := mul_le_mul_of_nonneg_left hlog10 (show 0 ≤ 360*h by positivity)
  have he := mul_le_mul_of_nonneg_right (show mediumPrimeProfile a+180*h ≤ 192 by linarith only [hf12,hh1]) he0
  change _ ≤ _+3600*h^2+192*e
  change _ ≤ (mediumPrimeProfile a+180*h)*(Real.log (b/a)+e) at htest'
  nlinarith only [htest',hIntegral,hmesh,he]

def mediumPrimeGridPoint (n i : ℕ) : ℝ := 1/10+(7/30 : ℝ)*(i : ℝ)/n

theorem mediumPrimeGridPoint_mono {n : ℕ} (hn : 0 < n) : Monotone (mediumPrimeGridPoint n) := by
  intro i j hij
  unfold mediumPrimeGridPoint
  gcongr

theorem weightedPrimeLogSum_add {N : ℕ} {a b c : ℝ} (hN : 1 ≤ N) (hab : a ≤ b) (hbc : b ≤ c) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b+
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N b c =
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a c := by
  unfold MertensTheorem.weightedPrimeReciprocalLogSum
  simp only [Finset.sum_filter]
  apply Finset.sum_Ioc_consecutive
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hbc)

theorem numerical_medium_grid_partition {N n : ℕ} (hN : 1 ≤ N) (hn : 0 < n) (k : ℕ) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
      (mediumPrimeGridPoint n 0) (mediumPrimeGridPoint n k) =
        ∑ i ∈ range k, MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
          (mediumPrimeGridPoint n i) (mediumPrimeGridPoint n (i+1)) := by
  induction k with
  | zero => simp [MertensTheorem.weightedPrimeReciprocalLogSum]
  | succ k ih =>
    rw [sum_range_succ,← ih]
    exact (weightedPrimeLogSum_add hN (mediumPrimeGridPoint_mono hn (Nat.zero_le k))
      (mediumPrimeGridPoint_mono hn (Nat.le_succ k))).symm

#print axioms numerical_medium_prime_cell
end ChenEffective
