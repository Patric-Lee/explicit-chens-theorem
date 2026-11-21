import GRH14PrimeIntervals
import GRH14ErrorBudget
import NumericalUpperFactor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

section
noncomputable section
namespace ChenEffective.GRH14
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
def primePairThreshold : ℕ := targetCutoff

theorem numerical_prime_pair_parameters {N : ℕ} (hN : primePairThreshold  ≤  N) :
    9  ≤  N ∧ (1000000:ℝ)  ≤  log (N:ℝ) ∧
      (logPowerCutoff 2:ℝ)  ≤  (N:ℝ)^(1/10:ℝ) ∧
      (logPowerCutoff 2:ℝ)  ≤  (N:ℝ)^(1/10:ℝ) :=
  lower_prime_parameters_of_log (by have h := target_log_lower hN; linarith only [h])

theorem numerical_prime_pair_interval {N : ℕ} (hN : primePairThreshold  ≤  N)
    {a b : ℝ} (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1) :
    PrimeReciprocalLogScale.primeReciprocalLogInterval N a b  ≤ 
      log (b/a)+100/log (N:ℝ)^2 :=
  lower_prime_interval_of_log (numerical_prime_pair_parameters hN).2.1 ha hab hb


theorem numerical_prime_interval_carrier (N : ℕ) (a b : ℝ) :
    (Finset.Ioc (MertensTheorem.rpowFloor N a) (MertensTheorem.rpowFloor N b)).filter Nat.Prime =
      (Finset.range (PrimeReciprocalLogScale.rpowFloor N b+1)).filter
        (fun p : ℕ => p.Prime ∧ (N : ℝ)^a < (p : ℝ) ∧ (p : ℝ)  ≤  (N : ℝ)^b) := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_range,Nat.lt_succ_iff,MertensTheorem.rpowFloor,
    PrimeReciprocalLogScale.rpowFloor,Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) a),
    Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) b)]
  tauto

theorem numerical_medium_profile_integrable {a b : ℝ} (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1/3) :
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
theorem numerical_medium_prime_cell {N : ℕ} (hN : primePairThreshold  ≤  N) {a b : ℝ}
    (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1/3) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b  ≤ 
      (∫ x in a..b, mediumPrimeProfile x/x)+3600*(b-a)^2+
        192*(100/Real.log (N : ℝ)^2) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := ha0.trans_le hab
  let h := b-a
  let e := 100/Real.log (N : ℝ)^2
  have hh0 : 0  ≤  h := sub_nonneg.mpr hab
  have hh1 : h  ≤  1 := by dsimp [h]; linarith only [ha,hb]
  have he0 : 0  ≤  e := by dsimp [e]; positivity
  obtain ⟨hf0,hf12,_⟩ := numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha,hab.trans hb⟩
  have htest : MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b  ≤ 
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
    have habs : |Real.log (p : ℝ)/Real.log (N : ℝ)-a|  ≤  h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hpinterval.1)]
      dsimp [h]
      linarith only [hpinterval.2]
    have hf : mediumPrimeProfile (Real.log (p : ℝ)/Real.log (N : ℝ))  ≤  mediumPrimeProfile a+180*h := by
      have h := (le_abs_self _).trans hdiff
      linarith only [h,habs]
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hf hp0.le
  have hmass := numerical_prime_pair_interval hN ha hab (by linarith only [hb] : b  ≤  1)
  have htest' := htest.trans (mul_le_mul_of_nonneg_left hmass (show 0  ≤  mediumPrimeProfile a+180*h by positivity))
  have hlog0 : 0  ≤  Real.log (b/a) := Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using hab))
  have hlog10 : Real.log (b/a)  ≤  10*h := by
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
  have hIntegral : (mediumPrimeProfile a-180*h)*Real.log (b/a)  ≤  ∫ x in a..b, mediumPrimeProfile x/x := by
    have hc := intervalIntegral.integral_mono_on hab (hone.const_mul (mediumPrimeProfile a-180*h))
      (numerical_medium_profile_integrable ha hab hb) (fun x hx => ?_)
    · rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos ha0 hb0] at hc
      exact hc
    · have hdiff := (numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha.trans hx.1,hx.2.trans hb⟩).2.2
      have habs : |a-x|  ≤  h := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx.1)]
        dsimp [h]
        linarith only [hx.2]
      have hf : mediumPrimeProfile a-180*h  ≤  mediumPrimeProfile x := by
        have hh := (le_abs_self _).trans hdiff
        linarith only [hh,habs]
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hf (show 0  ≤  x by linarith only [ha,hx.1])
  have hmesh := mul_le_mul_of_nonneg_left hlog10 (show 0  ≤  360*h by positivity)
  have he := mul_le_mul_of_nonneg_right (show mediumPrimeProfile a+180*h  ≤  192 by linarith only [hf12,hh1]) he0
  change _  ≤  _+3600*h^2+192*e
  change _  ≤  (mediumPrimeProfile a+180*h)*(Real.log (b/a)+e) at htest'
  nlinarith only [htest',hIntegral,hmesh,he]

def mediumPrimeGridPoint (n i : ℕ) : ℝ := 1/10+(7/30 : ℝ)*(i : ℝ)/n

theorem mediumPrimeGridPoint_mono {n : ℕ} (hn : 0 < n) : Monotone (mediumPrimeGridPoint n) := by
  intro i j hij
  unfold mediumPrimeGridPoint
  gcongr

theorem weightedPrimeLogSum_add {N : ℕ} {a b c : ℝ} (hN : 1  ≤  N) (hab : a  ≤  b) (hbc : b  ≤  c) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b+
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N b c =
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a c := by
  unfold MertensTheorem.weightedPrimeReciprocalLogSum
  simp only [Finset.sum_filter]
  apply Finset.sum_Ioc_consecutive
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hbc)

theorem numerical_medium_grid_partition {N n : ℕ} (hN : 1  ≤  N) (hn : 0 < n) (k : ℕ) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
      (mediumPrimeGridPoint n 0) (mediumPrimeGridPoint n k) =
        ∑ i ∈ range k, MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
          (mediumPrimeGridPoint n i) (mediumPrimeGridPoint n (i+1)) := by
  induction k with
  | zero => simp [MertensTheorem.weightedPrimeReciprocalLogSum]
  | succ k ih =>
    rw [Finset.sum_range_succ,← ih]
    exact (weightedPrimeLogSum_add hN (mediumPrimeGridPoint_mono hn (Nat.zero_le k))
      (mediumPrimeGridPoint_mono hn (Nat.le_succ k))).symm

#print axioms numerical_medium_prime_cell
end ChenEffective.GRH14

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalMediumPrimeSum.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-effective/NumericalMediumPrimeSum.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.GRH14. -/

noncomputable section
namespace ChenEffective.GRH14
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

def mediumPrimeIntegral : ℝ := ∫ a in (1/10 : ℝ)..(1/3 : ℝ), mediumPrimeProfile a/a

theorem numerical_medium_integral_caps : 0  ≤  mediumPrimeIntegral ∧ mediumPrimeIntegral  ≤  120 := by
  have hf (a : ℝ) (ha : a ∈ Icc (1/10 : ℝ) (1/3)) :
      0  ≤  mediumPrimeProfile a/a ∧ mediumPrimeProfile a/a  ≤  120 := by
    have hh := numerical_medium_profile ha ha
    have ha0 : 0 < a := by linarith only [ha.1]
    exact ⟨div_nonneg hh.1 ha0.le,(div_le_iff₀ ha0).mpr (by linarith only [hh.2.1,ha.1])⟩
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun a ha => (hf a ha).1)
  · unfold mediumPrimeIntegral
    calc
      _  ≤  ∫ _a in (1/10 : ℝ)..(1/3 : ℝ), (120 : ℝ) := intervalIntegral.integral_mono_on
        (by norm_num) (numerical_medium_profile_integrable (by norm_num) (by norm_num) (by norm_num))
        intervalIntegrable_const (fun a ha => (hf a ha).2)
      _  ≤  120 := by norm_num

theorem numerical_medium_integral_coefficient :
    jurkatRichertMertensFactor*mediumPrimeIntegral = jurkatRichertQ1MainCoefficient jurkatRichertK := by
  have hh : mediumPrimeIntegral = 2*Real.exp Real.eulerMascheroniConstant/5*(Real.log 8+jurkatRichertK/2) :=
    jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  rw [hh]
  unfold jurkatRichertMertensFactor jurkatRichertQ1MainCoefficient
  have he : Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant=1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  calc
    _ = 8*(Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant)*(Real.log 8+jurkatRichertK/2) := by ring
    _ = _ := by rw [he, mul_one]

theorem numerical_medium_prime_grid {N n : ℕ} (hN : primePairThreshold  ≤  N) (hn : 0 < n) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)  ≤ 
      mediumPrimeIntegral+196/(n : ℝ)+192*(n : ℝ)*(100/Real.log (N : ℝ)^2) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  let c := mediumPrimeGridPoint n
  let h : ℝ := (7/30 : ℝ)/n
  let e : ℝ := 100/Real.log (N : ℝ)^2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstart : c 0 = 1/10 := by simp [c,mediumPrimeGridPoint]
  have hend : c n = 1/3 := by dsimp [c,mediumPrimeGridPoint]; field_simp; ring
  have hmono : Monotone c := mediumPrimeGridPoint_mono hn
  have hc (i : ℕ) (hi : i  ≤  n) : c i ∈ Icc (1/10 : ℝ) (1/3) := by
    have h1 := hmono (Nat.zero_le i)
    have h2 := hmono hi
    rw [hstart] at h1
    rw [hend] at h2
    exact ⟨h1,h2⟩
  have hstep (i : ℕ) : c (i+1)-c i=h := by dsimp [c,h,mediumPrimeGridPoint]; push_cast; ring
  have hint (i : ℕ) (hi : i < n) : IntervalIntegrable (fun a => mediumPrimeProfile a/a) volume (c i) (c (i+1)) :=
    numerical_medium_profile_integrable (hc i (by omega)).1 (hmono (by omega)) (hc (i+1) (by omega)).2
  have hsum := Finset.sum_le_sum (s := range n) (fun i hi =>
    numerical_medium_prime_cell hN (hc i (by have h := mem_range.mp hi; omega)).1
      (hmono (by omega)) (hc (i+1) (by have h := mem_range.mp hi; omega)).2)
  have hpartition := numerical_medium_grid_partition (N := N) (by omega : 1  ≤  N) hn n
  have hI := intervalIntegral.sum_integral_adjacent_intervals hint
  change (∑ i ∈ range n, ∫ x in c i..c (i+1), mediumPrimeProfile x/x) = _ at hI
  rw [hstart,hend] at hI
  change _ = mediumPrimeIntegral at hI
  change MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (c 0) (c n) = _ at hpartition
  rw [hstart,hend] at hpartition
  rw [← hpartition] at hsum
  simp only [hstep,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  rw [hI] at hsum
  have heq : (n : ℝ)*(3600*h^2)=196/(n : ℝ) := by dsimp [h]; field_simp; ring
  simpa only [heq,mul_assoc,mul_left_comm,e] using hsum

theorem numerical_medium_prime_unshifted {N : ℕ} (hN : primePairThreshold  ≤  N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)  ≤ 
      mediumPrimeIntegral+1/250 := by
  have hh := numerical_medium_prime_grid (n := 100000) hN (by norm_num)
  have hL := (numerical_prime_pair_parameters hN).2.1
  have hl : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)  ≤  1000000) hL 2
  have he : (192:ℝ)*100000*(100/log (N:ℝ)^2)  ≤  1/500 := by
    rw [show (192:ℝ)*100000*(100/log (N:ℝ)^2) = (192*100000*100)/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    linarith only [hs]
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,he]

#print axioms numerical_medium_prime_unshifted
end ChenEffective.GRH14
end
end
