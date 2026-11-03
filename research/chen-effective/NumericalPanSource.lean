import NumericalPanWeighted
import ExplicitChenLower

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
theorem liuMainPanMaxL_eq_intervalMaxL
    (main : ℝ → ℝ) (N A₁ A₂ q : ℕ) (f : ℕ → ℝ)
    (h : ∀ l : ℕ,
      liuMainPanCoprimeSum main N N q l f =
        liuMainPanCoprimeIntervalSum main N A₁ A₂ q l f) :
    liuMainPanMaxL main N N q f =
      liuMainPanCoprimeIntervalMaxL main N A₁ A₂ q f := by
  unfold liuMainPanMaxL liuMainPanCoprimeIntervalMaxL
  dsimp only
  split <;> simp_all only

theorem liuMainPanEndpointWeightedSum_le_corollary230Sum
    (κ : ℝ) (N : ℕ) (B : ℝ)
    (hinterval : ∀ q l : ℕ,
      liuMainPanCoprimeSum (liuLogarithmicIntegral κ) N N q l
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
        liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral κ) N
          (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q l
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))
    (hcut : range (panModulusCutoff N (B + 1) + 1) ⊆
      range (panSourceStrictModulusCutoff N B)) :
    liuMainPanEndpointWeightedSum (liuLogarithmicIntegral κ) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (B + 1) ≤
      liuPanWangDingCorollary230Sum κ N B := by
  classical
  unfold liuMainPanEndpointWeightedSum liuPanWangDingCorollary230Sum
  calc
    (∑ q ∈ range (panModulusCutoff N (B + 1) + 1),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
        (3 : ℝ) ^ q.primeFactors.card *
          liuMainPanMaxL (liuLogarithmicIntegral κ) N N q
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) =
      ∑ q ∈ range (panModulusCutoff N (B + 1) + 1),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
            liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ) N
              (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [liuMainPanMaxL_eq_intervalMaxL
          (liuLogarithmicIntegral κ) N
          (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (hinterval q)]
    _ ≤ ∑ q ∈ range (panSourceStrictModulusCutoff N B),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
            liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral κ) N
              (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hcut
        intro q _ _
        rw [← liuMainPanMaxL_eq_intervalMaxL
          (liuLogarithmicIntegral κ) N
          (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) q
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (hinterval q)]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity))
          (liuMainPanMaxL_nonneg (liuLogarithmicIntegral κ) N N q
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)))


@[irreducible] def panSourceSupportThreshold (B : ℕ) : ℕ :=
  max (2^20) (logPowerCutoff (40*B))

theorem numerical_pan_source_support (B N : ℕ) (hN : panSourceSupportThreshold B ≤ N) :
    liuPanSourceIntervalLower N (B : ℝ) < liuSourceZ10 N := by
  have hn := hN
  unfold panSourceSupportThreshold at hn
  obtain ⟨hNpow, hNlog⟩ := max_le_iff.mp hn
  have hN9 := (logPowerCutoff_nine_le _).trans hNlog
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog := log_pow_le_rpow_inv_explicit (k := 2*B) (m := 20)
    (by norm_num) (by omega : 20*(2*B) ≤ 40*B) hNlog
  have htwo : (2 : ℝ) ≤ (N : ℝ)^(1/20 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2) hN0.le
      (by norm_num : (0 : ℝ) < 20)).mpr
    exact_mod_cast hNpow
  have hsquare : ((N : ℝ)^(1/20 : ℝ))^2 = (N : ℝ)^(1/10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hsum : Real.log (N : ℝ)^((2 : ℝ)*B)+2 ≤ (N : ℝ)^(1/10 : ℝ) := by
    rw [show (2 : ℝ)*B = ((2*B : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
    nlinarith only [hlog, htwo, hsquare]
  have hfloor := Nat.floor_mono hsum
  have hl0 : 0 ≤ Real.log (N : ℝ)^((2 : ℝ)*B) := Real.rpow_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hadd : ⌊Real.log (N : ℝ)^((2 : ℝ)*B)+2⌋₊ =
      ⌊Real.log (N : ℝ)^((2 : ℝ)*B)⌋₊+2 := by
    simpa using Nat.floor_add_natCast hl0 2
  rw [hadd] at hfloor
  unfold liuPanSourceIntervalLower liuSourceZ10
  omega

@[irreducible] def panSourceThreshold (A m : ℕ) : ℕ :=
  max (panWeightedThreshold A) (max (panSourceSupportThreshold (panWeightedCutoff A))
    (logPowerCutoff (m*(panWeightedCutoff A+1))))

theorem numerical_pan_source (A m N : ℕ) (hm : 0 < m) (hN : panSourceThreshold A m ≤ N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral (2/Real.log 2)) N (1/(m : ℝ))
      (A : ℝ) (panWeightedConstant A) := by
  have hn := hN
  unfold panSourceThreshold at hn
  obtain ⟨hNW, hNS, hNC⟩ := (max_le_iff.mp hn).imp_right max_le_iff.mp
  have hN9 := (logPowerCutoff_nine_le _).trans hNC
  have hl := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hlgt : 1 < Real.log (N : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (show (9 : ℝ) ≤ N by exact_mod_cast hN9)
    rw [show (9 : ℝ) = 3^2 by norm_num, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, one_le_log_three]
  have hbound := numerical_pan_weighted A N hNW
  rw [← Real.rpow_natCast] at hbound
  have hcut := explicit_source_modulus_in_BV (panWeightedCutoff A+1) m N hm hNC
  rw [Nat.cast_add, Nat.cast_one] at hcut
  apply liuPaperQCoprimeRBound_of_liuMainPanEndpointMeanValueAt
    (liuLogarithmicIntegral (2/Real.log 2)) N (1/(m : ℝ)) (A : ℝ)
    ((panWeightedCutoff A : ℝ)+1) (panWeightedConstant A) hcut
  apply (liuMainPanEndpointWeightedSum_le_corollary230Sum (2/Real.log 2) N
    (panWeightedCutoff A : ℝ) (fun _ _ =>
      liuMainPanCoprimeSum_eq_panSourceInterval _ (by omega)
        (numerical_pan_source_support _ N hNS))
    (range_panModulusCutoff_add_one_subset_sourceStrict N _ (by omega) hlgt)).trans hbound

#print axioms numerical_pan_source
end ChenEffective
