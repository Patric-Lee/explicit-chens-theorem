import NumericalPanEnvelope
import NumericalWeightedMass

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def panWeightedSaving (A : ℕ) : ℕ := 2*A+20
def panWeightedCutoff (A : ℕ) : ℕ := panWeightedSaving A+8
def panWeightedSquareConstant (A : ℕ) : ℝ :=
  2^20*panActualEnvelopeConstant (2/Real.log 2)*panUnweightedConstant (panWeightedSaving A)
def panWeightedConstant (A : ℕ) : ℝ := Real.sqrt (panWeightedSquareConstant A)+1
@[irreducible] def panWeightedThreshold (A : ℕ) : ℕ := panUnweightedThreshold (panWeightedSaving A)

theorem numerical_pan_weighted_square (κ : ℝ) (N : ℕ) (B : ℝ)
    (hN : 2 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B) :
    liuPanWangDingCorollary230Sum κ N B^2 ≤
      (1+Real.log (N : ℝ))^20 * (panActualEnvelopeConstant κ*N*
        liuPanUnweightedTheorem2Sum κ N B) := by
  let S := liuPanSquarefreeCarrier N B
  let E := liuPanActualError κ N B
  let X := panActualEnvelopeConstant κ*N*(1+Real.log (N : ℝ))^2
  have hX : 0 ≤ X := by dsimp [X]; positivity [panActualEnvelopeConstant_pos κ]
  have hsq : ∀ q ∈ S, Squarefree q := fun q hq => (mem_filter.mp hq).2
  have hpos : ∀ q ∈ S, 0 < q := fun q hq => Nat.pos_of_ne_zero (hsq q hq).ne_zero
  have hE : ∀ q ∈ S, 0 ≤ E q := fun q _ => liuPanActualError_nonneg κ N B q
  have hSN : S ⊆ Icc 1 N := by
    intro q hq
    exact mem_Icc.mpr ⟨hpos q hq,
      panSourceStrictModulusCutoff_mem_le (by omega) hlog hB (mem_filter.mp hq).1⟩
  have hc := numerical_totient_cauchy S
    (fun q => (3 : ℝ)^q.primeFactors.card) E X hpos hE (by
      intro q hq
      exact numerical_pan_envelope κ N _ _ q hN
        (hpos q hq) (mem_Icc.mp (hSN hq)).2)
  have hm : (∑ q ∈ S, ((3 : ℝ)^q.primeFactors.card)^2/q.totient) ≤
      (1+Real.log (N : ℝ))^18 := by
    calc
      _ = ∑ q ∈ S, (9 : ℝ)^q.primeFactors.card/q.totient := by
        apply sum_congr rfl
        intro q _
        rw [pow_two, ← mul_pow]
        norm_num
      _ ≤ _ := numerical_totient_nine_mass (by omega) S hSN hsq
  have ho : (∑ q ∈ S, E q) ≤ liuPanUnweightedTheorem2Sum κ N B :=
    liuPanSquarefreeErrorSum_le_unweighted κ N B
  rw [liuPanWeightedSum_eq_squarefree]
  calc
    _ ≤ (∑ q ∈ S, ((3 : ℝ)^q.primeFactors.card)^2/q.totient)*(X*∑ q ∈ S, E q) := hc
    _ ≤ (1+Real.log (N : ℝ))^18*(X*liuPanUnweightedTheorem2Sum κ N B) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left ho hX)
        (mul_nonneg hX (sum_nonneg hE)) (by positivity)
    _ = _ := by dsimp [X]; ring

theorem numerical_pan_weighted (A N : ℕ) (hN : panWeightedThreshold A ≤ N) :
    liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ) ≤
      panWeightedConstant A*N/Real.log (N : ℝ)^A := by
  have hn := hN
  unfold panWeightedThreshold panUnweightedThreshold at hn
  have hl := (le_max_left _ _).trans hn
  unfold panLedgerThreshold at hl
  have hhigh := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hlog : 1 ≤ Real.log (N : ℝ) := (numerical_pan_conductor_bounds _ N hhigh).1
  have hN2 : 2 ≤ N := by
    have hg := hhigh
    unfold NumericalPanHigh.panHighThreshold at hg
    have := (logPowerCutoff_nine_le _).trans hg
    omega
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hK := panUnweightedConstant_pos (panWeightedSaving A)
  have hsrc := numerical_pan_unweighted (panWeightedSaving A) N
    (by simpa only [panWeightedThreshold] using hN)
  rw [Real.rpow_natCast] at hsrc
  have hs := numerical_pan_weighted_square (2/Real.log 2) N (panWeightedCutoff A : ℝ)
    hN2 hlog (Nat.cast_nonneg _)
  have henv := panActualEnvelopeConstant_pos (2/Real.log 2)
  have hD : 0 ≤ panWeightedSquareConstant A := by unfold panWeightedSquareConstant; positivity
  have hmajor : liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ)^2 ≤
      panWeightedSquareConstant A*((N : ℝ)/Real.log (N : ℝ)^A)^2 := by
    calc
      _ ≤ (1+Real.log (N : ℝ))^20*(panActualEnvelopeConstant (2/Real.log 2)*N*
          (panUnweightedConstant (panWeightedSaving A)*N/Real.log (N : ℝ)^(panWeightedSaving A))) :=
        hs.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsrc (by positivity)) (by positivity))
      _ ≤ (2*Real.log (N : ℝ))^20*(panActualEnvelopeConstant (2/Real.log 2)*N*
          (panUnweightedConstant (panWeightedSaving A)*N/Real.log (N : ℝ)^(panWeightedSaving A))) := by
        gcongr
        linarith only [hlog]
      _ = _ := by
        unfold panWeightedSaving panWeightedSquareConstant
        rw [pow_add, pow_mul]
        field_simp [hl0.ne']
        simp only [panWeightedSaving, Nat.mul_comm]
        ring
  have hleft : 0 ≤ liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ) := by
    unfold liuPanWangDingCorollary230Sum
    exact sum_nonneg fun q _ => mul_nonneg (by positivity) (liuMainPanCoprimeIntervalMaxL_nonneg ..)
  have ht : 0 ≤ panWeightedConstant A*N/Real.log (N : ℝ)^A := by unfold panWeightedConstant; positivity
  have hDs : panWeightedSquareConstant A ≤ panWeightedConstant A^2 := by
    unfold panWeightedConstant
    nlinarith only [Real.sq_sqrt hD, Real.sqrt_nonneg (panWeightedSquareConstant A)]
  apply (sq_le_sq₀ hleft ht).mp
  exact hmajor.trans ((mul_le_mul_of_nonneg_right hDs (sq_nonneg _)).trans_eq (by ring))

#print axioms numerical_pan_weighted
end ChenEffective
