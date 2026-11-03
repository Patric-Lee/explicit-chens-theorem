import NumericalC1Scalar
import NumericalSigmaZeroCutoff
import NumericalErrorTransport

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

@[irreducible] def coreDecayLogCutoff : ℕ := logPowerCutoff 32
noncomputable def coreDecayCutoff (M : ℝ) : ℝ :=
  max (max 2 (Real.log 27))
    (max (coreDecayLogCutoff : ℝ)
      ((max 1 (128*M/(5*(1-(1/2 : ℝ)))) ) ^
        (1 / ((1-(1/2 : ℝ)) - (2/(7 : ℝ)+3/(16 : ℝ))))))

theorem numerical_caseII_core_decay (M : ℝ) (hM : 0 ≤ M) :
    ∃ C1min : ℝ, C1min = coreDecayCutoff M ∧ 1 ≤ C1min ∧
      ∀ (C1 K D : ℝ), C1min ≤ C1 → 2 ≤ K → 2 ≤ D →
        C1*K^(7 : ℝ) < Real.log D →
        M*K^2*sourceSigma D 16^2*(Real.log D)^((1/2 : ℝ)-1) ≤ 5*(1-(1/2 : ℝ))/32 := by
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  let Θ : ℝ := 7
  have hsrc : SuzukiClaim145SourceParameters d Δ Θ := by constructor <;> norm_num [d, Δ, Θ]
  let β : ℝ := 1 - Δ
  have hβ : 0 < β := sub_pos.mpr hsrc.hDelta_lt
  have hd : 0 < d := hsrc.d_pos
  have hΘ : 0 < Θ := hsrc.hTheta_pos
  let η : ℝ := β - (2 / Θ + 3 / d)
  have hη : 0 < η := by
    dsimp [η, β]
    linarith [hsrc.h14_4]
  let B : ℝ := max 1 (128 * M / (5 * β))
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  let Xpow : ℝ := B ^ (1 / η)
  have hXpow0 : 0 ≤ Xpow := Real.rpow_nonneg hB0.le _
  let Xlog : ℝ := coreDecayLogCutoff
  let C1min : ℝ := max (max 2 (Real.log 27)) (max Xlog Xpow)
  have hC1 : 1 ≤ C1min := by
    exact (show (1 : ℝ) ≤ 2 by norm_num).trans
      ((le_max_left 2 (Real.log 27)).trans (le_max_left _ _))
  refine ⟨C1min, rfl, hC1, ?_⟩
  intro C1 K D hC1C hK hD2 hlarge
  let x : ℝ := Real.log D
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKΘ1 : 1 ≤ K ^ Θ := Real.one_le_rpow hK1 hΘ.le
  have hxC1 : C1 < x := by
    calc
      C1 ≤ C1 * K ^ Θ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hKΘ1
          (zero_le_one.trans (hC1.trans hC1C))
      _ < x := by simpa [x, Θ] using hlarge
  have hxMin : C1min < x := hC1C.trans_lt hxC1
  have hx2 : 2 < x :=
    (le_max_left 2 (Real.log 27)).trans_lt
      ((le_max_left (max 2 (Real.log 27)) _).trans_lt hxMin)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog27x : Real.log 27 ≤ x :=
    (le_max_right 2 (Real.log 27)).trans
      ((le_max_left (max 2 (Real.log 27)) _).trans hxMin.le)
  have hD1 : 1 < D := by linarith
  have hD0 : 0 < D := zero_lt_one.trans hD1
  have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hD0)]
  have hinner_le : Real.log (27 * D) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hinner_pos : 0 < Real.log (27 * D) := by
    rw [hlog27D]
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hll_le : Real.log (Real.log (27 * D)) ≤ 2 * Real.log x := by
    have h := Real.strictMonoOn_log.monotoneOn hinner_pos
      (show 0 < 2 * x by positivity) hinner_le
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx0)] at h
    have hlog2 : Real.log 2 ≤ Real.log x :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hx0 hx2.le
    linarith
  have hlogdom : (Real.log x) ^ 2 ≤ x ^ (1 / d) := by
    have hXlogMin : Xlog ≤ C1min :=
      (le_max_left Xlog Xpow).trans (le_max_right _ _)
    have hxcut : (coreDecayLogCutoff : ℝ) ≤ x := hXlogMin.trans hxMin.le
    unfold coreDecayLogCutoff at hxcut
    simpa only [d, Nat.cast_ofNat] using real_log_pow_le_rpow_inv (k := 2) (m := 16) (t := 32) (x := x)
      (by norm_num) (by norm_num) hxcut
  have hll0 : 0 ≤ Real.log (Real.log (27 * D)) := by
    have hinner1 : 1 ≤ Real.log (27 * D) := by
      rw [hlog27D]
      have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
      linarith
    exact Real.log_nonneg hinner1
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hllsq : Real.log (Real.log (27 * D)) ^ 2 ≤
      4 * (Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (Real.log (27 * D)) - 2 * Real.log x)]
  have hsigSq : sourceSigma D d ^ 2 ≤ 4 * x ^ (3 / d) := by
    calc
      sourceSigma D d ^ 2 =
          (x ^ (1 / d)) ^ 2 * Real.log (Real.log (27 * D)) ^ 2 := by
        simp only [sourceSigma, x]
        ring
      _ ≤ (x ^ (1 / d)) ^ 2 * (4 * (Real.log x) ^ 2) := by
        gcongr
      _ ≤ (x ^ (1 / d)) ^ 2 * (4 * x ^ (1 / d)) := by
        gcongr
      _ = 4 * x ^ (3 / d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        calc
          x ^ (1 / d * (2 : ℝ)) * (4 * x ^ (1 / d)) =
              4 * (x ^ (1 / d * 2) * x ^ (1 / d)) := by ring
          _ = 4 * x ^ (1 / d * 2 + 1 / d) := by rw [Real.rpow_add hx0]
          _ = 4 * x ^ (3 / d) := by congr 2; ring
  have hKTheta : K ^ Θ < x := by
    calc
      K ^ Θ ≤ C1 * K ^ Θ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hC1.trans hC1C) (Real.rpow_nonneg hK0.le _)
      _ < x := by simpa [x, Θ] using hlarge
  have hKsq : K ^ 2 ≤ x ^ (2 / Θ) := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le Θ) hKTheta.le
      (show 0 ≤ 2 / Θ by positivity)
    calc
      K ^ 2 = (K ^ Θ) ^ (2 / Θ) := by
        rw [← Real.rpow_mul hK0.le]
        have : Θ * (2 / Θ) = 2 := by field_simp
        rw [this, Real.rpow_two]
      _ ≤ x ^ (2 / Θ) := hpow
  have hprod : K ^ 2 * sourceSigma D d ^ 2 ≤
      4 * x ^ (2 / Θ + 3 / d) := by
    calc
      K ^ 2 * sourceSigma D d ^ 2 ≤
          x ^ (2 / Θ) * (4 * x ^ (3 / d)) :=
        mul_le_mul hKsq hsigSq (sq_nonneg _) (Real.rpow_nonneg hx0.le _)
      _ = 4 * x ^ (2 / Θ + 3 / d) := by
        calc
          x ^ (2 / Θ) * (4 * x ^ (3 / d)) =
              4 * (x ^ (2 / Θ) * x ^ (3 / d)) := by ring
          _ = 4 * x ^ (2 / Θ + 3 / d) := by rw [Real.rpow_add hx0]
  have hdecay : x ^ (-η) ≤ 1 / B := by
    have hXpowMin : Xpow ≤ C1min :=
      (le_max_right Xlog Xpow).trans (le_max_right _ _)
    have hXpowx : Xpow ≤ x := hXpowMin.trans hxMin.le
    have hp := Real.rpow_le_rpow hXpow0 hXpowx hη.le
    have hpId : Xpow ^ η = B := by
      dsimp [Xpow]
      rw [← Real.rpow_mul hB0.le]
      have : (1 / η) * η = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [hpId] at hp
    have hxη : 0 < x ^ η := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_neg hx0.le]
    simpa only [one_div] using one_div_le_one_div_of_le hB0 hp
  have hpowid :
      x ^ (2 / Θ + 3 / d) * x ^ (Δ - 1) = x ^ (-η) := by
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp [η, β]
    ring
  have hMB : 4 * M / B ≤ 5 * β / 32 := by
    have hcoef : 128 * M / (5 * β) ≤ B := le_max_right _ _
    have hscaled := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ 5 * β / 32 by positivity)
    have hBpos : 0 < B := hB0
    apply (div_le_iff₀ hBpos).2
    calc
      4 * M = (128 * M / (5 * β)) * (5 * β / 32) := by
        field_simp
        ring
      _ ≤ B * (5 * β / 32) := hscaled
    nlinarith
  change M * K ^ 2 * sourceSigma D d ^ 2 * x ^ (Δ - 1) ≤ _
  calc
    M * K ^ 2 * sourceSigma D d ^ 2 * x ^ (Δ - 1) =
        M * (K ^ 2 * sourceSigma D d ^ 2) * x ^ (Δ - 1) := by ring
    _ ≤ M * (4 * x ^ (2 / Θ + 3 / d)) * x ^ (Δ - 1) := by
      gcongr
    _ = 4 * M * x ^ (-η) := by rw [← hpowid]; ring
    _ ≤ 4 * M * (1 / B) := by gcongr
    _ = 4 * M / B := by ring
    _ ≤ 5 * (1 - Δ) / 32 := by simpa [β] using hMB
#print axioms numerical_caseII_core_decay
end ChenEffective
