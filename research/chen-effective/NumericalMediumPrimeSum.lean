import NumericalMediumPrimeGrid

noncomputable section
namespace ChenEffective
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

def mediumPrimeIntegral : ℝ := ∫ a in (1/10 : ℝ)..(1/3 : ℝ), mediumPrimeProfile a/a

theorem numerical_medium_integral_caps : 0 ≤ mediumPrimeIntegral ∧ mediumPrimeIntegral ≤ 120 := by
  have hf (a : ℝ) (ha : a ∈ Icc (1/10 : ℝ) (1/3)) :
      0 ≤ mediumPrimeProfile a/a ∧ mediumPrimeProfile a/a ≤ 120 := by
    have hh := numerical_medium_profile ha ha
    have ha0 : 0 < a := by linarith only [ha.1]
    exact ⟨div_nonneg hh.1 ha0.le,(div_le_iff₀ ha0).mpr (by linarith only [hh.2.1,ha.1])⟩
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun a ha => (hf a ha).1)
  · unfold mediumPrimeIntegral
    calc
      _ ≤ ∫ _a in (1/10 : ℝ)..(1/3 : ℝ), (120 : ℝ) := intervalIntegral.integral_mono_on
        (by norm_num) (numerical_medium_profile_integrable (by norm_num) (by norm_num) (by norm_num))
        intervalIntegrable_const (fun a ha => (hf a ha).2)
      _ ≤ 120 := by norm_num

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

theorem numerical_medium_prime_grid {N n : ℕ} (hN : primePairThreshold ≤ N) (hn : 0 < n) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3) ≤
      mediumPrimeIntegral+196/(n : ℝ)+192*(n : ℝ)*(18000000000000/Real.log (N : ℝ)) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  let c := mediumPrimeGridPoint n
  let h : ℝ := (7/30 : ℝ)/n
  let e : ℝ := 18000000000000/Real.log (N : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstart : c 0 = 1/10 := by simp [c,mediumPrimeGridPoint]
  have hend : c n = 1/3 := by dsimp [c,mediumPrimeGridPoint]; field_simp; ring
  have hmono : Monotone c := mediumPrimeGridPoint_mono hn
  have hc (i : ℕ) (hi : i ≤ n) : c i ∈ Icc (1/10 : ℝ) (1/3) := by
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
  have hpartition := numerical_medium_grid_partition (N := N) (by omega : 1 ≤ N) hn n
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

theorem numerical_medium_prime_unshifted {N : ℕ} (hN : primePairThreshold ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3) ≤
      mediumPrimeIntegral+1/100000000 := by
  have hh := numerical_medium_prime_grid (n := 1000000000000) hN (by norm_num)
  obtain ⟨_,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hsmall : (192 : ℝ)*1000000000000*(18000000000000/Real.log (N : ℝ)) ≤ 1/1000000000 := by
    rw [show (192 : ℝ)*1000000000000*(18000000000000/Real.log (N : ℝ)) =
      (192*1000000000000*18000000000000)/Real.log (N : ℝ) by ring]
    apply (div_le_iff₀ hL).mpr
    linarith only [hlog]
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,hsmall]

#print axioms numerical_medium_prime_unshifted
end ChenEffective
