import NumericalSuzukiNormalization
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeLogPointwiseProducer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIEvenEndpointSourceLargeLogPointwise

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

/- The source proof constructs coefficient one. These strengthened interfaces
expose it while preserving the original threshold quantifiers. -/

theorem numerical_caseB_coefficient_one
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ S : BoundingSieve,
        Claim145CaseBClosed S H d Δ Θ C1min 1 := by
  rcases proposition131iiUniformQuantitativeLower_of_source hH with
    ⟨C, M, _hC, hM3, hprop⟩
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hd7 : 7 < d := by
    have hfrac : 7 ≤ 7 / (1 - Δ) := by
      rw [le_div_iff₀ hβ]
      nlinarith
    exact hfrac.trans_lt hd
  have hd0 : 0 < d := by linarith
  let a : ℝ := 1 / d
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ d by linarith)
    simpa using h
  have hdom : ∀ᶠ x : ℝ in atTop, 2 * (Real.log x) ^ 2 ≤ x ^ a := by
    simpa only [Real.rpow_two] using
      MathlibNt.Analysis.eventually_const_mul_log_rpow_le_rpow 2 2 ha
  obtain ⟨X, hX⟩ := eventually_atTop.1 hdom
  let r0 : ℝ := (C + 2 + Real.log 2) / (d - 4)
  let C_bound := |Real.log (1 + 1 / Real.log 2)| + 2 * |Real.log (Real.log 2)|
  let C_q0 := max 6 (max (C_bound + 2) (max (C_bound + 9) (Real.exp 1 + 2)))
  let C1min := max (Real.exp (max M (max (Real.exp r0) C_q0))) (max X (max 2 (Real.log 27)))
  have hC1min_pos : 0 < C1min := by
    dsimp [C1min]
    have : 0 < Real.exp (max M (max (Real.exp r0) C_q0)) := Real.exp_pos _
    exact this.trans_le (le_max_left _ _)
  refine ⟨C1min, hC1min_pos, ?_⟩
  intro S C1 K N D s hC1min_C1 hK hlocal hD hs hC1_K_Theta hsigma
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hD1 : 1 < D := by omega
  have hKpos : 0 < K := by linarith
  have hC145 : 0 ≤ (1 : ℝ) := zero_le_one
  have hDpos : 0 < (D : ℝ) := by linarith
  let D_real : ℝ := D
  let C145 : ℝ := 1
  let x : ℝ := Real.log D_real
  let q : ℝ := Real.log x
  let ell : ℝ := Real.log (Real.log (27 * D_real))
  let σ : ℝ := sourceSigma D_real d
  let L : ℝ := suzukiSourceL D_real K
  let u : ℝ := s / σ
  let b : ℝ := 1 + s ^ d / x

  have h_x_lower : C1min ≤ x := by
    have h_K_pow : 1 ≤ K ^ Θ := by
      have : (1:ℝ) ≤ K := by linarith
      exact Real.one_le_rpow this (by linarith)
    calc C1min ≤ C1min * 1 := by rw [mul_one]
      _ ≤ C1 * 1 := mul_le_mul_of_nonneg_right hC1min_C1 zero_le_one
      _ ≤ C1 * K ^ Θ := mul_le_mul_of_nonneg_left h_K_pow (hC1min_pos.le.trans hC1min_C1)
      _ ≤ x := hC1_K_Theta.le

  have hxX : X ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans h_x_lower)
  have hxrest : max 2 (Real.log 27) ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans h_x_lower)
  have hx2 : 2 ≤ x := (le_max_left 2 _).trans hxrest
  have hx27 : Real.log 27 ≤ x := (le_max_right 2 _).trans hxrest
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith

  have hq_lower : max M (max (Real.exp r0) C_q0) ≤ q := by
    have h_exp : Real.exp (max M (max (Real.exp r0) C_q0)) ≤ x := (le_max_left _ _).trans h_x_lower
    exact (Real.le_log_iff_exp_le hx).mpr h_exp

  have hMq : M ≤ q := (le_max_left _ _).trans hq_lower
  have hqM : max M 0 ≤ q := max_le hMq (by linarith [hM3])

  have hlog27D : Real.log (27 * D_real) = Real.log 27 + x := by
    dsimp [x, D_real]
    have : (27:ℝ) ≠ 0 := by norm_num
    have : (D_real:ℝ) ≠ 0 := by positivity
    rw [Real.log_mul (by norm_num) (by positivity)]

  have hinnerLower : x ≤ Real.log (27 * D_real) := by
    rw [hlog27D]
    exact le_add_of_nonneg_left (Real.log_nonneg (by norm_num))

  have hq_ell : q ≤ ell := by
    dsimp [q, ell]
    exact Real.log_le_log hx hinnerLower

  have hq : 0 < q := by
    exact (Real.exp_pos r0).trans_le
      ((le_max_left (Real.exp r0) C_q0).trans
        ((le_max_right M (max (Real.exp r0) C_q0)).trans hq_lower))
  have hr0_q : Real.exp r0 ≤ q := (le_max_left _ _).trans ((le_max_right _ _).trans hq_lower)
  have hr : r0 ≤ Real.log q := (Real.le_log_iff_exp_le hq).mpr hr0_q


  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := -Real.log (Real.log 2) + Real.log (1 + K / Real.log 2)
  let A : ℝ := (1 / Real.log 2) * (1 + K / Real.log 2)
  let Q : ℝ := 1 / A
  have hQ_pos : 0 < Q := by positivity
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  let q0 : ℝ := max 6 (max (|B| + 2) (max (9 + |Real.log Q|) (Real.exp 1 + 2)))

  have hB_bound : |B| ≤ Real.log K +
      (|Real.log (1 + 1 / Real.log 2)| + 2 * |Real.log (Real.log 2)|) := by
    simpa [B, add_assoc] using abs_B_bound K hK
  have hlogQ_bound : |Real.log Q| ≤ Real.log K +
      (|Real.log (1 + 1 / Real.log 2)| + 2 * |Real.log (Real.log 2)|) := by
    have hdenpos : 0 < 1 + K / Real.log 2 := by positivity
    change |Real.log (1 / ((1 / Real.log 2) *
      (1 + K / Real.log 2)))| ≤ _
    rw [show (1 / ((1 / Real.log 2) * (1 + K / Real.log 2)) : ℝ) =
      Real.log 2 / (1 + K / Real.log 2) by
        field_simp [ne_of_gt hlog2, ne_of_gt hdenpos] ]
    simpa [add_assoc] using abs_logQ_bound K hK
  have h_q0_bound : q0 ≤ Θ * Real.log K + C_q0 :=
    q0_bound K hK Θ hTheta hB_bound hlogQ_bound
  have h_Cq0_q : C_q0 ≤ q := (le_max_right (Real.exp r0) C_q0).trans ((le_max_right M (max (Real.exp r0) C_q0)).trans hq_lower)

  have hq_q0 : q0 ≤ q := by
    calc q0 ≤ Θ * Real.log K + C_q0 := h_q0_bound
      _ = Real.log (K ^ Θ) + C_q0 := by rw [Real.log_rpow (by linarith) Θ]
      _ ≤ Real.log (K ^ Θ) + Real.log C1 := by
        have : C_q0 ≤ Real.log C1min := by
          have h_exp : Real.exp C_q0 ≤ C1min := by
            calc Real.exp C_q0 ≤ Real.exp (max M (max (Real.exp r0) C_q0)) := Real.exp_le_exp.mpr ((le_max_right _ _).trans (le_max_right _ _))
              _ ≤ C1min := le_max_left _ _
          exact (Real.le_log_iff_exp_le hC1min_pos).mpr h_exp
        have : C_q0 ≤ Real.log C1 := this.trans (Real.log_le_log hC1min_pos hC1min_C1)
        linarith
      _ = Real.log (C1 * K ^ Θ) := by
        have hC1pos : 0 < C1 := hC1min_pos.trans_le hC1min_C1
        have hKpowpos : 0 < K ^ Θ := Real.rpow_pos_of_pos hKpos Θ
        rw [Real.log_mul (ne_of_gt hC1pos) (ne_of_gt hKpowpos)]
        ring
      _ ≤ Real.log x := by
        have hC1pos : 0 < C1 := hC1min_pos.trans_le hC1min_C1
        have hKpowpos : 0 < K ^ Θ := Real.rpow_pos_of_pos hKpos Θ
        exact Real.log_le_log (mul_pos hC1pos hKpowpos) hC1_K_Theta.le
      _ = q := rfl

  have hq4 : 4 ≤ q := by
    dsimp [q0] at hq_q0
    exact (show (4:ℝ) ≤ 6 by norm_num).trans ((le_max_left 6 _).trans hq_q0)
  have hqB : |B| + 2 ≤ q := (le_max_left _ _).trans ((le_max_right 6 _).trans hq_q0)
  have hqQ : 9 + |Real.log Q| ≤ q := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right 6 _).trans hq_q0))
  have hqe : Real.exp 1 + 2 ≤ q := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right 6 _).trans hq_q0))
  have hinnerUpper : Real.log (27 * D_real) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hinnerPos : 0 < Real.log (27 * D_real) := hx.trans_le hinnerLower
  have hellLower : q ≤ ell := hq_ell
  have hellUpper : ell ≤ 2 * q := by
    have h := Real.log_le_log hinnerPos hinnerUpper
    have hlog2leq : Real.log 2 ≤ q := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
    dsimp [q] at hlog2leq
    dsimp [ell, q]
    linarith
  have hell : 0 < ell := hq.trans_le hellLower
  have hxa1 : 1 ≤ x ^ a := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      hx1 ha.le
  have hxale : x ^ a ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 ha1
  -- Normalize the moving endpoint before transporting its bounds to `s ≥ σ`.
  have hσdef : σ = x ^ a * ell := by rfl
  have hσLower : x ^ a * q ≤ σ := by
    rw [hσdef]
    exact mul_le_mul_of_nonneg_left hellLower (Real.rpow_nonneg hx.le _)
  have hσUpper : σ ≤ 2 * x * q := by
    rw [hσdef]
    calc
      x ^ a * ell ≤ x * (2 * q) := mul_le_mul hxale hellUpper hell.le hx.le
      _ = 2 * x * q := by ring
  have hσ4 : 4 ≤ σ := by
    calc 4 ≤ q := hq4
      _ ≤ x ^ a * q := le_mul_of_one_le_left hq.le hxa1
      _ ≤ σ := hσLower
  have hσpos : 0 < σ := by linarith
  have hsigma : σ ≤ s := by simpa [σ] using hsigma
  have hs4 : 4 ≤ s := hσ4.trans hsigma
  have hspos : 0 < s := by linarith
  have hu1 : 1 ≤ u := by
    dsimp [u]
    exact (le_div_iff₀ hσpos).2 (by simpa using hsigma)
  have hupos : 0 < u := zero_lt_one.trans_le hu1
  have hsu : s = σ * u := by
    dsimp [u]
    field_simp [ne_of_gt hσpos]
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hlogu_le : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
  have hlogsSplit : Real.log s = Real.log σ + Real.log u := by
    rw [hsu, Real.log_mul (ne_of_gt hσpos) (ne_of_gt hupos)]
  have hLdef : L = q + B := by
    dsimp [L, q, x, B, suzukiSourceL]
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hlog2)]
    ring
  have hL : 1 ≤ L := by
    rw [hLdef]
    have hnegB : -|B| ≤ B := neg_abs_le B
    linarith
  have hLsq : L ≤ q ^ 2 := by
    rw [hLdef]
    have hBabs : B ≤ |B| := le_abs_self B
    nlinarith only [hqB, hBabs, sq_nonneg (q - 1)]
  have hdomx : 2 * q ^ 2 ≤ x ^ a := by
    simpa [q] using hX x hxX
  have habsorbσ : q ^ 2 + 9 * q + |Real.log Q| ≤ σ := by
    have htail : 9 * q + |Real.log Q| ≤ q ^ 2 := by
      have habs : 0 ≤ |Real.log Q| := abs_nonneg _
      nlinarith only [hqQ, hq4, habs]
    have hxa_le_σ : x ^ a ≤ σ := by
      calc
        x ^ a ≤ x ^ a * q :=
          le_mul_of_one_le_right (Real.rpow_nonneg hx.le a) (by linarith only [hq4])
        _ ≤ σ := hσLower
    calc
      q ^ 2 + 9 * q + |Real.log Q| ≤ 2 * q ^ 2 := by linarith only [htail]
      _ ≤ x ^ a := hdomx
      _ ≤ σ := hxa_le_σ
  have hsourceσ : Real.exp 1 * L ≤ σ - 2 := by
    have hsigStrong : Real.exp 1 * q ^ 2 + 2 ≤ 2 * q ^ 3 := by
      have hepos := Real.exp_pos 1
      nlinarith only [hq4, hepos, sq_nonneg q,
        mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hqe)]
    have htwoq3 : 2 * q ^ 3 ≤ σ := by
      have hmul := mul_le_mul_of_nonneg_right hdomx hq.le
      calc
        2 * q ^ 3 = (2 * q ^ 2) * q := by ring
        _ ≤ x ^ a * q := hmul
        _ ≤ σ := hσLower
    linarith only [hsigStrong, htwoq3,
      mul_le_mul_of_nonneg_left hLsq (Real.exp_pos 1).le]
  have hsource : Real.exp 1 * L ≤ s - 2 := by linarith only [hsourceσ, hsigma]
  have hlogsσ : Real.log σ ≤ 3 * q := by
    have hboundpos : 0 < 2 * x * q := by positivity
    have h := Real.log_le_log hσpos hσUpper
    rw [Real.log_mul (by positivity : (2 * x : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
    have hlog2le : Real.log 2 ≤ q := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
    have hlogqle : Real.log q ≤ q := (Real.log_le_sub_one_of_pos hq).trans (by linarith)
    dsimp [q] at hlog2le
    linarith
  have hloglog3σ : Real.log (Real.log (3 * σ)) ≤ 2 * Real.log q := by
    have hinner : Real.log (3 * σ) ≤ q ^ 2 := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hσpos.ne']
      have hlog3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      nlinarith only [hlogsσ, hlog3, hq4, sq_nonneg (q - 2)]
    have hinnerpos : 0 < Real.log (3 * σ) := Real.log_pos (by linarith only [hσ4])
    have hh := Real.log_le_log hinnerpos hinner
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlogL : Real.log L ≤ 2 * Real.log q := by
    have hq2pos : 0 < q ^ 2 := sq_pos_of_pos hq
    have h := Real.log_le_log (by linarith : 0 < L) hLsq
    rw [Real.log_pow] at h
    simpa using h
  have hconst : C + 2 + Real.log 2 ≤ (d - 4) * Real.log q := by
    have hd4 : 0 < d - 4 := by linarith
    have ht := mul_le_mul_of_nonneg_left hr hd4.le
    dsimp [r0] at ht
    field_simp [ne_of_gt hd4] at ht
    linarith
  -- The uniform threshold has supplied the same endpoint bounds as in CaseBAllS.
  have habsorb : L + 2 * Real.log s + 3 * q + |Real.log Q| ≤ s := by
    have hbase : L + 2 * Real.log σ + 3 * q + |Real.log Q| ≤ σ := by
      linarith only [hLsq, hlogsσ, habsorbσ]
    rw [hlogsSplit]
    have hlogtransport : 2 * Real.log u ≤ 2 * (u - 1) :=
      mul_le_mul_of_nonneg_left hlogu_le (by norm_num)
    have hscale : 2 * (u - 1) ≤ σ * (u - 1) :=
      mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ σ)
        (sub_nonneg.mpr hu1)
    have htransport : 2 * Real.log u ≤ s - σ := by
      calc
        2 * Real.log u ≤ 2 * (u - 1) := hlogtransport
        _ ≤ σ * (u - 1) := hscale
        _ = s - σ := by rw [hsu]; ring
    linarith only [hbase, htransport]
  have hqσ : q ≤ σ := by
    have hm := mul_le_mul_of_nonneg_right hxa1 hq.le
    have hm' : q ≤ x ^ a * q := by simpa [mul_comm] using hm
    exact hm'.trans hσLower
  have hAlog : 1 ≤ Real.log (3 * σ) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 3 * σ)).2
    calc
      Real.exp 1 ≤ q := by linarith [hqe]
      _ ≤ σ := hqσ
      _ ≤ 3 * σ := by linarith [hσpos]
  have hlog3s_mul : Real.log (3 * s) =
      Real.log (3 * σ) + Real.log u := by
    rw [hsu]
    rw [show 3 * (σ * u) = (3 * σ) * u by ring,
      Real.log_mul (by positivity : (3 * σ : ℝ) ≠ 0) (ne_of_gt hupos)]
  have hlog3s_le : Real.log (3 * s) ≤ u * Real.log (3 * σ) := by
    rw [hlog3s_mul]
    calc
      Real.log (3 * σ) + Real.log u ≤ Real.log (3 * σ) + (u - 1) :=
        by simpa [add_comm] using add_le_add_left hlogu_le (Real.log (3 * σ))
      _ ≤ Real.log (3 * σ) + (u - 1) * Real.log (3 * σ) := by
        have hm := mul_le_mul_of_nonneg_left hAlog (sub_nonneg.mpr hu1)
        simpa using hm
      _ = u * Real.log (3 * σ) := by ring
  have hloglog3s :
      Real.log (Real.log (3 * s)) ≤ 2 * Real.log q + Real.log u := by
    have hleftpos : 0 < Real.log (3 * s) := Real.log_pos (by linarith only [hs4])
    have hrightpos : 0 < u * Real.log (3 * σ) := mul_pos hupos (lt_of_lt_of_le zero_lt_one hAlog)
    have hh := Real.log_le_log hleftpos hlog3s_le
    rw [Real.log_mul (ne_of_gt hupos)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hAlog))] at hh
    linarith
  have hσPow : σ ^ d = x * ell ^ d := by
    rw [hσdef, Real.mul_rpow (Real.rpow_nonneg hx.le _) hell.le]
    have hxad : (x ^ a) ^ d = x := by
      rw [← Real.rpow_mul hx.le]
      have : a * d = 1 := by dsimp [a]; field_simp
      rw [this, Real.rpow_one]
    rw [hxad]
  have hsPow : s ^ d = u ^ d * (x * ell ^ d) := by
    rw [hsu, Real.mul_rpow hσpos.le hupos.le, hσPow]
    ring
  have hquot : s ^ d / x = u ^ d * ell ^ d := by
    rw [hsPow]
    field_simp [ne_of_gt hx]
  have hbpos : 0 < b := by
    dsimp [b]
    have : 0 ≤ s ^ d / x := div_nonneg (Real.rpow_nonneg hspos.le _) hx.le
    linarith
  have hblog : d * Real.log q + d * Real.log u ≤ Real.log b := by
    have hqpow : q ^ d ≤ ell ^ d := Real.rpow_le_rpow hq.le hellLower hd0.le
    have hupow : 0 ≤ u ^ d := Real.rpow_nonneg hupos.le _
    have hy_le : u ^ d * q ^ d ≤ b := by
      dsimp [b]
      rw [hquot]
      calc
        u ^ d * q ^ d ≤ u ^ d * ell ^ d :=
          mul_le_mul_of_nonneg_left hqpow hupow
        _ ≤ 1 + u ^ d * ell ^ d := le_add_of_nonneg_left zero_le_one
    have hypos : 0 < u ^ d * q ^ d := mul_pos (Real.rpow_pos_of_pos hupos _)
      (Real.rpow_pos_of_pos hq _)
    have hh := Real.log_le_log hypos hy_le
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hupos _))
      (ne_of_gt (Real.rpow_pos_of_pos hq _)),
      Real.log_rpow hupos d, Real.log_rpow hq d] at hh
    linarith
  have hgap : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
      Real.log b := by
    have hmid : Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 ≤
        d * Real.log q + d * Real.log u := by
      have hlogu_d : Real.log u ≤ d * Real.log u := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ d) hlogu0
      calc
        Real.log L + Real.log (Real.log (3 * s)) + C + 2 + Real.log 2 =
            (Real.log L + Real.log (Real.log (3 * s))) +
              (C + 2 + Real.log 2) := by ring
        _ ≤ (2 * Real.log q + (2 * Real.log q + Real.log u)) +
              ((d - 4) * Real.log q) :=
          add_le_add (add_le_add hlogL hloglog3s) hconst
        _ = d * Real.log q + Real.log u := by ring
        _ ≤ d * Real.log q + d * Real.log u :=
          add_le_add (le_refl (d * Real.log q)) hlogu_d
    exact hmid.trans hblog
  have hcore := claim145_caseB_scalar_exponent_comparison hx hq hL hs4 hQ_pos rfl
    habsorb hgap
  have hVedge := claim14_5VProduct_lower_of_localProduct
    (S := S) (D := D_real) (K := K) hDreal hlocal
  have hAform : (Real.log D_real / Real.log 2) * (1 + K / Real.log 2) = A * x := by
    dsimp [A, x]
    ring
  rw [hAform] at hVedge
  have hpowDelta : x ^ (-1 : ℝ) ≤ x ^ (-Δ) := by
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpref : Q / x ^ 3 ≤
      C145 * (claim14_5VProduct S D_real *
        (Real.exp (Real.sqrt K) / x)) * x ^ (-Δ) := by
    have hnonneg : 0 ≤ Q / x ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hVedge hnonneg
    have hVpos : 0 < claim14_5VProduct S D_real := by
      simpa [claim14_5VProduct, suzukiVProduct] using suzukiVProduct_pos S D_real
    calc
      Q / x ^ 3 ≤ (claim14_5VProduct S D_real * (A * x)) * (Q / x ^ 3) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      _ = C145 * (claim14_5VProduct S D_real * (1 / x)) *
          x ^ (-1 : ℝ) := by
            dsimp [Q, C145]
            rw [Real.rpow_neg_one]
            field_simp [ne_of_gt hx, ne_of_gt hApos]
      _ ≤ C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-1 : ℝ) := by
            have hexpK : 1 ≤ Real.exp (Real.sqrt K) :=
              Real.one_le_exp (Real.sqrt_nonneg K)
            gcongr
      _ ≤ C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) := by gcongr
  have hscalarCore :
      Real.exp (L + (s - 2) * (1 + Real.log L - Real.log (s - 2))) ≤
        C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) *
          Real.exp (s * Real.log b - s * Real.log s -
            s * Real.log (Real.log (3 * s)) - C * s) := by
    exact hcore.trans (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le)
  have hprofile :
      b ^ s * proposition131iiLowerProfile C s =
        Real.exp (s * Real.log b - s * Real.log s -
          s * Real.log (Real.log (3 * s)) - C * s) := by
    unfold proposition131iiLowerProfile
    rw [Real.rpow_def_of_pos hbpos, ← Real.exp_add]
    congr 1
    ring
  have h_cond1 : 0 < σ := hσpos
  have h_cond2 : M ≤ s := hMq.trans (hqσ.trans hsigma)
  have h_cond3 : Real.exp 1 * suzukiSourceL D_real K ≤ s - 2 := hsource
  have h_cond4 : Real.exp (suzukiSourceL D_real K + (s - 2) * (1 + Real.log (suzukiSourceL D_real K) - Real.log (s - 2))) ≤ 1 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / (Real.log D_real * σ)) * ((1 + s ^ d / Real.log D_real) ^ s * s * proposition131iiLowerProfile C s) * (Real.log D_real) ^ (-Δ)) := by
    rw [← hprofile] at hscalarCore
    have hVnonneg : 0 ≤ claim14_5VProduct S D_real := by
      simpa [claim14_5VProduct, suzukiVProduct] using (suzukiVProduct_pos S D_real).le
    have hprofnonneg : 0 ≤ proposition131iiLowerProfile C s := by
      unfold proposition131iiLowerProfile
      exact (Real.exp_pos _).le
    have hbpow : 0 ≤ b ^ s := Real.rpow_nonneg hbpos.le _
    have holdnonneg : 0 ≤
        C145 * (claim14_5VProduct S D_real * (Real.exp (Real.sqrt K) / x)) *
          x ^ (-Δ) * (b ^ s * proposition131iiLowerProfile C s) := by
      positivity
    convert hscalarCore.trans (le_mul_of_one_le_right holdnonneg hu1) using 1
    · rfl
    · dsimp [C145, b, x, u]
      field_simp [ne_of_gt hx, ne_of_gt hσpos]
  exact suzukiLemma14_3_le_claim145Scale_of_scalar_at S H hlocal hD h_cond1 hs h_cond2 hKpos hC145 hprop h_cond3 h_cond4



theorem numerical_sigma_zero_coefficient_one
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ S : BoundingSieve, ∀ (C1 C K : ℝ) (N D z : ℕ),
        C1min ≤ C1 → (1 : ℝ) ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → 2 ≤ N →
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
        suzukiSigmaZero S N D z
            ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
          (1 / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
  obtain ⟨C1B, hC1B, hcaseB⟩ :=
    numerical_caseB_coefficient_one H hΔ0 hΔ1 hd hTheta hH
  let CB : ℝ := 1
  have hCB : 0 < CB := zero_lt_one
  obtain ⟨D3, hD3, hsigma3⟩ :=
    exists_sourceSigma_three_threshold d (by
      have hden : 0 < 1 - Δ := sub_pos.mpr hΔ1
      have hfrac : 0 < 7 / (1 - Δ) := div_pos (by norm_num) hden
      linarith)
  let C1min : ℝ := max C1B (Real.log D3)
  have hC1min : 0 < C1min := hC1B.trans_le (le_max_left _ _)
  refine ⟨C1min, hC1min, ?_⟩
  intro S C1 C K N D z hC1 hCBC hK hlocal hD hlarge hN hz
  have hC1B' : C1B ≤ C1 := (le_max_left _ _).trans hC1
  have hlogD3 : Real.log D3 ≤ Real.log (D : ℝ) := by
    calc
      Real.log D3 ≤ C1min := le_max_right _ _
      _ ≤ C1 := hC1
      _ ≤ C1 * K ^ Θ := by
        have hC10 : 0 ≤ C1 := hC1min.le.trans hC1
        have hKpow : 1 ≤ K ^ Θ :=
          Real.one_le_rpow (by linarith) (by linarith)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hKpow hC10
      _ ≤ Real.log (D : ℝ) := hlarge.le
  have hD3D : D3 ≤ (D : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hlogD3
    rw [Real.exp_log (by linarith : 0 < D3),
      Real.exp_log (by positivity : 0 < (D : ℝ))] at hexp
    exact hexp
  have hσ3 : 3 ≤ sourceSigma (D : ℝ) d := hsigma3 _ hD3D
  have hendpoint : ActualClaim145BoundAt S H N D d Δ K
      (sourceSigma (D : ℝ) d) CB :=
    hcaseB S C1 K N D (sourceSigma (D : ℝ) d)
      hC1B' hK hlocal hD (by linarith [hσ3]) hlarge le_rfl
  have hDpos : 0 < D := by omega
  have hEq := suzukiSigmaZero_eq_actualT_sourceSigma_strict
    (S := S) (N := N) (D := D) (z := z) (d := d) hN hz (by
      intro _ p hp
      exact cube_lt_of_lt_natCeil_rpow hDpos hσ3 rfl hp)
  rw [hEq]
  unfold ActualClaim145BoundAt at hendpoint
  have hCpos : 0 < C := hCB.trans_le hCBC
  calc
    suzukiActualT S N D ⌈(D : ℝ) ^
          (1 / sourceSigma (D : ℝ) d)⌉₊ ≤
        CB * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := hendpoint
    _ = (CB / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
      field_simp [ne_of_gt hCpos]



theorem numerical_sigma_zero_even_coefficient_one
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hTheta : 1 ≤ Θ)
    (hH : Section13HatSourceContract H) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ S : BoundingSieve, ∀ (C1 C K : ℝ) (N D z : ℕ),
        C1min ≤ C1 → (1 : ℝ) ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → Even N → 2 ≤ N →
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
        suzukiSigmaZero S N D z
            ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
          (1 / C) * (C * claim14_5Scale S H N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) := by
  obtain ⟨C1min, hC1min, hstrict⟩ :=
    numerical_sigma_zero_coefficient_one H hΔ0 hΔ1 hd hTheta hH
  refine ⟨C1min, hC1min, ?_⟩
  intro S C1 C K N D z hC1 hCBC hK hlocal hD hlarge _hEven hN hz
  exact hstrict S C1 C K N D z hC1 hCBC hK hlocal hD hlarge hN hz



theorem numerical_caseI_coefficient_one
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (S : BoundingSieve) (C1 C K : ℝ) (M D : ℕ) (s : ℝ),
        C1min ≤ C1 → max 3 (1 : ℝ) ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K →
        2 ≤ M →
        s ∈ KappaOneModel.parityDomain 2 M →
        s - 1 ∈ KappaOneModel.parityDomain 2 (M - 1) →
        2 ≤ s → 2 + (ErrorSign.ofDepth M).epsilon ≤ s →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        s ≤ sourceSigma (D : ℝ) d →
        H.betaHat + (ErrorSign.ofDepth M).epsilon < s →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
        suzukiActualT S M D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
          suzukiVProduct S ⌈(D : ℝ) ^ (1 / s)⌉₊ *
            finiteSourceLayer 1 2 M s +
          sigma12InheritedBudget S H M D
            ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s := by
  have hd1 : 1 < d := by
    have hden : 0 < 1 - Δ := sub_pos.mpr hsrc.hDelta_lt
    have hdenlt : 1 - Δ < 1 := by linarith [hsrc.hDelta_pos]
    have hseven : 7 < 7 / (1 - Δ) := by
      apply (lt_div_iff₀ hden).2
      nlinarith
    linarith [hsrc.h14_1]
  obtain ⟨L, hL, hfinite⟩ :=
    finiteSourceLayer_pred_le_uniform_oppositeHat
      (lemma132_finiteLayerHatUniform_slack hH)
  obtain ⟨R, hR, hratio⟩ :=
    proposition131iii_uniform_reverse_adjacent_ratio_of_source hH
  let Amax : ℝ := 1 + 2 * L * R + 12 * R
  have hAmax : 0 ≤ Amax := by dsimp [Amax]; positivity
  obtain ⟨C1coef, hC1coef, hcoef⟩ :=
    exists_caseISourceOrderCoefficient_sourceLargeLog_uniform
      hAmax hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1 hsrc.hTheta_pos
  obtain ⟨C1scalar, hC1scalar, hscalar⟩ :=
    exists_caseI1423_sourceScalar_sourceLargeLog_uniform_of_source hsrc
  obtain ⟨C1B, hC1B, hcaseB⟩ :=
    numerical_sigma_zero_coefficient_one H hsrc.hDelta_pos
      hsrc.hDelta_lt hsrc.h14_1 hsrc.one_le_theta hH
  let CB : ℝ := 1
  have hCB : 0 < CB := zero_lt_one
  obtain ⟨D12, hD12pos, h12⟩ :=
    exists_sigmaTwelve_internal_contraction_binderUniform_in_S
      (H := H) hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨D146, hD146pos, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma
      hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨Dg, hDgpos, hg⟩ := exists_caseI_preThreshold_geometry_packet d hd1
  obtain ⟨Drec, hrec⟩ := eventually_atTop.1
    (eventually_recursiveCoordinate_le_quotient_sourceSigma_uniform hd1)
  obtain ⟨Derr, herr⟩ := eventually_atTop.1
    (eventually_caseI_errorEnvelope_transport_uniform_in_S
      H hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt)
  obtain ⟨Dpkt, hpkt⟩ := eventually_atTop.1
    (eventually_caseI_strict_pointwise_packet_uniform_in_S H hH hd1 hsrc.hDelta_pos
      (show 2 ≤ (2 : ℕ) by norm_num))
  let Dcut : ℝ := max 4 (max D12 (max D146 (max Dg
    (max (Drec : ℝ) (max (Derr : ℝ) (Dpkt : ℝ))))))
  have hDcut : 0 < Dcut := (by norm_num : (0 : ℝ) < 4).trans_le (le_max_left _ _)
  obtain ⟨C1cut, hC1cut, hcut⟩ :=
    exists_sourceLargeLog_fixedThreshold_of_source hsrc Dcut hDcut
  let C1min : ℝ := max 1 (max C1coef (max C1scalar (max C1B C1cut)))
  have hC1min : 1 ≤ C1min := le_max_left _ _
  refine ⟨C1min, hC1min, ?_⟩
  intro S C1 C K M D s hC1 hCcommon hK hlocal hM hsdom hspred hs hsLower
    hlarge hsσ hthreshold hglobal
  have hCBC : CB ≤ C := (le_max_right 3 CB).trans hCcommon
  have hC3 : (3 : ℝ) ≤ C := (le_max_left 3 CB).trans hCcommon
  have hCpos : 0 < C := by linarith
  obtain ⟨hC1one, hcoefC1, hscalarC1, hcaseBC1, hcutC1⟩ :
      1 ≤ C1 ∧ C1coef ≤ C1 ∧ C1scalar ≤ C1 ∧ C1B ≤ C1 ∧ C1cut ≤ C1 := by
    simpa only [C1min, max_le_iff] using hC1
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by
      by_contra hn
      have hD0 : D = 0 := by omega
      subst D
      norm_num at hlarge
      have hC10 : 0 ≤ C1 :=
        (show (0 : ℝ) ≤ 1 by norm_num).trans (hC1min.trans hC1)
      have hKpow : 0 ≤ K ^ Θ := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_nonneg hC10 hKpow])
  have hDcutD : Dcut < (D : ℝ) := hcut C1 K (D : ℝ) hcutC1 hK hDpos hlarge
  obtain ⟨hD4real, hD12, hD146, hDg, hDrecReal, hDerrReal, hDpktReal⟩ :
      (4 : ℝ) ≤ D ∧ D12 ≤ D ∧ D146 ≤ D ∧ Dg ≤ D ∧
        (Drec : ℝ) ≤ D ∧ (Derr : ℝ) ≤ D ∧ (Dpkt : ℝ) ≤ D := by
    simpa only [Dcut, max_le_iff] using hDcutD.le
  have hD4 : 4 ≤ D := by exact_mod_cast hD4real
  have hD3 : 3 ≤ D := by omega
  have hD2 : 2 ≤ D := by omega
  have hDrec : Drec ≤ D := by exact_mod_cast hDrecReal
  have hDerr : Derr ≤ D := by exact_mod_cast hDerrReal
  have hDpkt : Dpkt ≤ D := by exact_mod_cast hDpktReal
  have g := hg D M hDg s hs hsσ
  have hrecursiveD := hrec D hDrec S
  have hinheritedForError : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
      (sourceSigma (D : ℝ) d) s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp
    have hp' := hp
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    apply parityDomain_mono hspred
    exact (MathlibNt.SieveTheory.caseI_inheritedCoordinate_gt
      (Nat.prime_of_mem_primeFactors hp'.1).two_le (by omega)
      (by linarith) hp'.2.2).le
  have herrorD := herr D hDerr S
  have herror := herrorD M s hs hinheritedForError (hrecursiveD s hs)
  obtain ⟨hprime, hscale, hinherited, hsource, herror', hceil, hT, h1413⟩ :=
    hpkt D hDpkt S M s hM hspred hs herror
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊ := rfl
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hprimeZ : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp; exact hprime p (Finset.mem_filter.mp hp).1
  have toFull : ∀ p, p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s →
      p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ s := by
    intro p hp
    simpa only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] using
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
        (Finset.mem_filter.mp hp).2⟩
  have hscaleZ : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S z) D 2 σ s := by
    intro p hp; exact hscale p (toFull p hp)
  have hinheritedZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp; exact hinherited p (toFull p hp)
  have hsourceZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      finiteSourceLayer 1 2 (M - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (M - 1) (inheritedCoordinate D p) := by
    intro p hp; exact hsource p (toFull p hp)
  have herrorZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p) := by
    intro p hp; exact herror' p (toFull p hp)
  have hrecursiveZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
    intro p hp; exact hrecursiveD s hs p (toFull p hp)
  have hpoint : PointwiseInductionContract
      (suzukiSupportedBelow S z) (suzukiActualT S)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ M D σ s :=
    pointwiseInductionContract_of_movingDomainIH S H C K d Δ M D 2 σ s
      (by norm_num) hprimeZ hscaleZ hinheritedZ
      (by intro p _; exact (suzukiVProduct_pos S p).le) hCpos.le hsourceZ herrorZ
      hrecursiveZ hglobal
  have h10 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
    (suzukiActualT S) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) 2 C K Δ M D σ s
    (ne_of_gt (suzukiVProduct_pos S z))
    (by intro p hp; have hpS := (Finset.mem_filter.mp hp).1
        exact (S.nu_pos_of_prime p (hprimeZ p hpS)
          ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1)).le) hpoint
  have h149 : suzukiActualT S M D z =
      suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ)) ((D : ℝ) ^ (1 / s)) +
          suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / s)) := by
    by_cases hOddM : Odd M
    · have hs3 : 3 ≤ s := by
        norm_num [ErrorSign.ofDepth, hOddM, ErrorSign.epsilon] at hsLower
        exact hsLower
      exact suzuki_equation14_9_natCeil S hM (by omega) hs3 hz g.hpowerOrder
    · exact suzuki_equation14_9_strict S hM
        (by intro hodd; exact (hOddM hodd).elim) g.hpowerOrder
  have h11raw := caseI_sigmaEleven_le_finiteSourceLayer_add_endpoint
    (S := S) (β := (2 : ℝ)) (s := s) (τ := s) (σ := σ)
    (K := K) (N := M) (D := D) (z := z)
    (by norm_num) hsdom hspred le_rfl hsσ hDreal g.hpowerS g.hpowerS
      g.hpowerSigma g.hpowerOrder le_rfl hz hK hlocal
  have h11 : sigmaEleven (suzukiSupportedBelow S z) S.nu
      (fun p => suzukiVProduct S p) (suzukiVProduct S z) 2 M D σ s ≤
      suzukiVProduct S z * finiteSourceLayer 1 2 M s +
        caseI1423Sigma11Endpoint S M D z K s σ := by
    simpa [caseI1423Sigma11Endpoint, div_self (ne_of_gt (by linarith : 0 < s))] using h11raw
  obtain ⟨q12, hq12, _h12raw, h12q⟩ :=
    h12 S C K hK hlocal hCpos.le D M s z hD12 (by linarith) hsLower
      g.hsigma hsσ hDreal g.hpowerS g.hpowerSigma g.hpowerOrder hz
      hthreshold.le hceil hT h1413
  have hcarrier : sigmaOneCarrier (suzukiSupportedBelow S z) D σ s =
      sigmaOneCarrier S.prodPrimes.primeFactors D σ s := by
    ext p
    simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpS, _⟩, hpw, hpv⟩; exact ⟨hpS, hpw, hpv⟩
    · rintro ⟨hpS, hpw, hpv⟩
      exact ⟨⟨hpS, (nat_lt_natCeil_iff_lt_real
        (natCast_rpow_one_div_pos (by omega) s) hz).2 hpv⟩, hpw, hpv⟩
  have h12qSupported :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ M D σ s ≤
        q12.ρ * sigma12InheritedBudget S H M D z C K d Δ s +
          caseI1423Sigma12Endpoint S H M D z C K d Δ s σ := by
    rw [show suzukiSupportedBelow S z =
      S.prodPrimes.primeFactors.filter (fun p => p < z) from rfl]
    rw [sigmaTwelve_supportedBelow_eq_full S
      (fun p => suzukiVProduct S (p : ℝ))
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      (suzukiVProduct S (z : ℝ)) C K Δ M D z σ s (Nat.le_ceil _)]
    simpa [σ, caseI1423Sigma12Endpoint, sigma12EndpointRemainder,
      div_self (ne_of_gt (by linarith : 0 < s))] using h12q
  have hscalarD := hscalar C1 K (D : ℝ) hscalarC1 hK
    (by exact_mod_cast hD2) hlarge
  have hend := caseI1423EndpointSourceBounds_sharp_of_source
    S H C K d Δ L R hH hCpos hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1
      hL hfinite hR hratio D M s hD3 hscalarD hM hs hspred hsσ
  have hzσ : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) :=
    g.hpowerOrder.trans (Nat.le_ceil _)
  have hzeroRaw := hcaseB S C1 C K M D z hcaseBC1 hCBC hK hlocal hD2
    hlarge hM hzσ
  have hi := (h146 (D : ℝ) hD146).1
  have hEtransport : errorEnvelope H M (D : ℝ) d σ ≤
      errorEnvelope H M (D : ℝ) d s := by
    apply errorEnvelope_endpoint_le_of_claim14_6 hH.toSection13HatContract hDreal hi
    rw [hH.betaHat_eq]
    exact ⟨hsLower, by simpa [σ] using hsσ⟩
  have hzeroUnit : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      (CB / C) * caseI1423RemainderUnit
        (sigma12InheritedBudget S H M D z C K d Δ s) (D : ℝ) σ := by
    apply hzeroRaw.trans
    have hscale := caseI_claim145Scale_le_transported_remainderUnit S H
      (K := K) (Δ := Δ)
      hH hD3 hCpos hCB.le (by linarith : 1 ≤ s) hsσ hEtransport
    simpa only [← mul_assoc, div_mul_cancel₀ _ hCpos.ne'] using hscale
  have hAactual : 0 ≤ CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R := by positivity
  have hAupper : CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R ≤ Amax := by
    have hb := caseI_endpointCoefficient_le_commonScale
      (A := (1 : ℝ)) (C := C) (C145 := CB) (K := K) (L := L) (R := R)
      (by norm_num) hC3 (by simpa using hCBC) (by linarith [hL]) (by linarith [hR])
    norm_num at hb
    simpa [Amax, CB] using hb
  obtain ⟨qgap, hqgap, hcoefGap⟩ := hcoef C1 K (D : ℝ)
    (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R)
    hcoefC1 hK (by exact_mod_cast hD2) hAactual hAupper hlarge
  have hqrho : q12.ρ = qgap.ρ := by rw [hq12, hqgap]
  have hbudget : 0 ≤ sigma12InheritedBudget S H M D z C K d Δ s := by
    unfold sigma12InheritedBudget
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hCpos.le (Real.exp_pos _).le)
          (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _))
      (errorEnvelope_nonneg H M hDreal (by linarith)
        (hH.positive _ _ (by linarith)).le)
  have hside : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        caseI1423Sigma11Endpoint S M D z K s σ +
        caseI1423Sigma12Endpoint S H M D z C K d Δ s σ ≤
      (1 - q12.ρ) * sigma12InheritedBudget S H M D z C K d Δ s := by
    rw [hqrho]
    exact caseI_three_remainders_le_gap hbudget hzeroUnit hend.1 hend.2 hcoefGap
  have h2raw := lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (N := M) S hD4 hs hz
  have h2 : suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / s)) = 0 := by
    simpa [lemma144_realTau_eq_s_of_caseI hD4 hs] using h2raw
  have hmiddle : suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ))
      ((D : ℝ) ^ (1 / s)) ≤
      sigmaEleven (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S z) 2 M D σ s +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ M D σ s := by
    change sigmaOne (suzukiSupportedBelow S z) S.nu (suzukiActualT S) M D σ s ≤ _
    exact h10
  rw [h149, h2]
  linarith [hmiddle, h11, h12qSupported, hside]



theorem numerical_caseI_even_coefficient_one
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (S : BoundingSieve) (C1 C K : ℝ) (M D : ℕ),
        C1min ≤ C1 → max 3 (1 : ℝ) ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K →
        Even M → 2 ≤ M →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
        suzukiActualT S M D ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ ≤
          suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
            finiteSourceLayer 1 2 M 2 +
          sigma12InheritedBudget S H M D
            ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ C K d Δ 2 := by
  have hd1 : 1 < d := by
    have hden : 0 < 1 - Δ := sub_pos.mpr hsrc.hDelta_lt
    have hdenlt : 1 - Δ < 1 := by linarith [hsrc.hDelta_pos]
    have hseven : 7 < 7 / (1 - Δ) := by
      apply (lt_div_iff₀ hden).2
      nlinarith
    linarith [hsrc.h14_1]
  obtain ⟨L, hL, hfinite⟩ :=
    lemma132_finiteSourceLayer_evenEndpoint_uniform_sourceLargeConsumer hH
  obtain ⟨R, hR, _hratio⟩ :=
    proposition131iii_uniform_reverse_adjacent_ratio_of_source hH
  let Amax : ℝ := 1 + 2 * L * R + 12 * R
  have hAmax : 0 ≤ Amax := by dsimp [Amax]; positivity
  obtain ⟨C1coef, hC1coef, hcoef⟩ :=
    exists_caseISourceOrderCoefficient_sourceLargeLog_uniform
      hAmax hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1 hsrc.hTheta_pos
  obtain ⟨C1scalar, hC1scalar, hscalar⟩ :=
    exists_caseI1423_sourceScalar_sourceLargeLog_uniform_of_source hsrc
  obtain ⟨C1B, hC1B, hcaseB⟩ :=
    numerical_sigma_zero_even_coefficient_one H hsrc.hDelta_pos
      hsrc.hDelta_lt hsrc.h14_1 hsrc.one_le_theta hH
  let CB : ℝ := 1
  have hCB : 0 < CB := zero_lt_one
  obtain ⟨D12, hD12pos, h12⟩ :=
    exists_sigmaTwelve_internal_contraction_binderUniform_in_S
      (H := H) hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨D146, hD146pos, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma
      hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨Dg, hDgpos, hg⟩ := exists_caseI_preThreshold_geometry_packet d hd1
  obtain ⟨Dσ, hDσpos, hσlarge⟩ := exists_sourceSigma_three_threshold d hsrc.d_pos
  obtain ⟨Drec, hrec⟩ := eventually_atTop.1
    (eventually_recursiveCoordinate_le_quotient_sourceSigma_uniform hd1)
  obtain ⟨Derr, herr⟩ := eventually_atTop.1
    (eventually_caseI_errorEnvelope_transport_uniform_in_S
      H hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt)
  let Dcut : ℝ := max 4 (max D12 (max D146
    (max Dg (max Dσ (max (Drec : ℝ) (Derr : ℝ))))))
  have hDcut : 0 < Dcut := (by norm_num : (0 : ℝ) < 4).trans_le (le_max_left _ _)
  obtain ⟨C1cut, hC1cut, hcut⟩ :=
    exists_sourceLargeLog_fixedThreshold_of_source hsrc Dcut hDcut
  let C1min : ℝ := max 1 (max C1coef (max C1scalar (max C1B C1cut)))
  have hC1min : 1 ≤ C1min := le_max_left _ _
  refine ⟨C1min, hC1min, ?_⟩
  intro S C1 C K M D hC1 hCcommon hK hlocal hM hM2 hlarge hglobal
  have hCBC : CB ≤ C := (le_max_right 3 CB).trans hCcommon
  have hC3 : (3 : ℝ) ≤ C := (le_max_left 3 CB).trans hCcommon
  have hCpos : 0 < C := by linarith
  obtain ⟨hC1one, hcoefC1, hscalarC1, hcaseBC1, hcutC1⟩ :
      1 ≤ C1 ∧ C1coef ≤ C1 ∧ C1scalar ≤ C1 ∧ C1B ≤ C1 ∧ C1cut ≤ C1 := by
    simpa only [C1min, max_le_iff] using hC1
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by
      by_contra hn
      have hD0 : D = 0 := by omega
      subst D
      norm_num at hlarge
      have hC10 : 0 ≤ C1 :=
        (show (0 : ℝ) ≤ 1 by norm_num).trans (hC1min.trans hC1)
      have hKpow : 0 ≤ K ^ Θ := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_nonneg hC10 hKpow])
  have hDcutD : Dcut < (D : ℝ) := hcut C1 K (D : ℝ) hcutC1 hK hDpos hlarge
  obtain ⟨hD4real, hD12, hD146, hDg, hDσ, hDrecReal, hDerrReal⟩ :
      (4 : ℝ) ≤ D ∧ D12 ≤ D ∧ D146 ≤ D ∧ Dg ≤ D ∧ Dσ ≤ D ∧
        (Drec : ℝ) ≤ D ∧ (Derr : ℝ) ≤ D := by
    simpa only [Dcut, max_le_iff] using hDcutD.le
  have hD4 : 4 ≤ D := by exact_mod_cast hD4real
  have hD3 : 3 ≤ D := by omega
  have hD2 : 2 ≤ D := by omega
  have hDrec : Drec ≤ D := by exact_mod_cast hDrecReal
  have hDerr : Derr ≤ D := by exact_mod_cast hDerrReal
  have hσ3 : (3 : ℝ) ≤ sourceSigma (D : ℝ) d := hσlarge _ hDσ
  have h2σ : (2 : ℝ) ≤ sourceSigma (D : ℝ) d := by linarith
  have g := hg D M hDg 2 (by norm_num) h2σ
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
  have hz : z = ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ := rfl
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hprime : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have toFull : ∀ p, p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2 →
      p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
    intro p hp
    simpa only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] using
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
        (Finset.mem_filter.mp hp).2⟩
  have hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S z) D 2 σ 2 := by
    intro p hp
    exact evenEndpoint_carrier_scale S (by norm_num) (by norm_num [show 4 ≤ D from hD4])
      p (toFull p hp)
  have hrecursiveD := hrec D hDrec S
  have hrecursiveSigma : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
    intro p hp
    exact hrecursiveD 2 (by norm_num) p (toFull p hp)
  have hinheritedFull : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp
    apply lemma144_caseI_even_endpoint_inherited_domain S hM hM2 hD4 hz p
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp hp).1,
      (nat_lt_natCeil_iff_lt_real (natCast_rpow_one_div_pos (by omega) (2 : ℝ)) hz).2
        (Finset.mem_filter.mp hp).2.2⟩
  have herrorD := herr D hDerr S
  have herror : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p) := by
    intro p hp
    exact herrorD M 2 (by norm_num) hinheritedFull
      (hrecursiveD 2 (by norm_num)) p (toFull p hp)
  have hpoint := evenEndpoint_pointwiseContract_of_movingIH_sourceLargeConsumer
    S H C K d Δ M D 2 (by norm_num) hM hM2 hD4 hscale hrecursiveSigma herror
      (by
        have hC3' : (3 : ℝ) ≤ C := (le_max_left 3 CB).trans hCcommon
        linarith) hglobal
  have h10 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
    (suzukiActualT S) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) 2 C K Δ M D σ 2
    (ne_of_gt (suzukiVProduct_pos S z))
    (by intro p hp; have hpS := (Finset.mem_filter.mp hp).1
        exact (S.nu_pos_of_prime p (hprime p hpS)
          ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1)).le) hpoint
  have h149 : suzukiActualT S M D z =
      suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ)) ((D : ℝ) ^ (1 / (2 : ℝ))) +
          suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / (2 : ℝ))) := by
    simpa [σ] using suzuki_equation14_9_strict (D := D) (z := z) S hM2
      (fun hOdd => (Nat.not_even_iff_odd.mpr hOdd hM).elim) g.hpowerOrder
  have h11 := caseI_evenEndpointSigma11Edge S hM hM2 h2σ hDreal
    g.hpowerS g.hpowerSigma g.hpowerOrder hK hlocal
  have hceil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) → 2 ≤ p ∧ 2 * p ≤ D := by
    intro p hp hpw hpv
    have hpc : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpw, hpv⟩
    exact ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      evenEndpoint_carrier_scale S (by norm_num)
        (by norm_num [show 4 ≤ D from hD4]) p hpc⟩
  have hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) →
      0 ≤ H.T (ErrorSign.ofDepth (M - 1)) (inheritedCoordinate D p) := by
    intro p hp hpw hpv
    have hpc : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpw, hpv⟩
    have hcoord := hinheritedFull p hpc
    have hpred : (M - 1) % 2 = 1 := by
      have hm0 : M % 2 = 0 := Nat.even_iff.mp hM
      omega
    have hcoord0 : 0 < inheritedCoordinate D p := by
      simp only [KappaOneModel.parityDomain, hpred, if_pos, Set.mem_Ioi] at hcoord
      norm_num at hcoord
      linarith
    exact (hH.positive _ _ hcoord0).le
  have hEvenLower : 2 + (ErrorSign.ofDepth M).epsilon ≤ (2 : ℝ) := by
    have hnotOdd : ¬ Odd M := fun ho => (Nat.not_even_iff_odd.mpr ho) hM
    simp [ErrorSign.ofDepth, hnotOdd, ErrorSign.epsilon]
  have hthreshold : H.betaHat + (ErrorSign.ofDepth M).epsilon ≤ (2 : ℝ) := by
    rw [hH.betaHat_eq]
    exact hEvenLower
  obtain ⟨q12, hq12, _h12raw, h12q⟩ :=
    h12 S C K hK hlocal (by linarith [hCcommon]) D M 2 z hD12
      (by norm_num) hEvenLower (by linarith [hσ3]) h2σ hDreal
      g.hpowerS g.hpowerSigma g.hpowerOrder hz hthreshold hceil hT
      (by
        intro p hp hpw hpv
        have hcp := hceil p hp hpw hpv
        exact claim14_13_pointwise_carrier H (by omega) hcp.1 hcp.2 hd1
          hsrc.hDelta_pos (hT p hp hpw hpv))
  have h12qSupported :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ M D σ 2 ≤
        q12.ρ * sigma12InheritedBudget S H M D z C K d Δ 2 +
          caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ := by
    rw [show suzukiSupportedBelow S z =
      S.prodPrimes.primeFactors.filter (fun p => p < z) from rfl]
    rw [sigmaTwelve_supportedBelow_eq_full S
      (fun p => suzukiVProduct S (p : ℝ))
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      (suzukiVProduct S (z : ℝ)) C K Δ M D z σ 2
      (by dsimp [z]; exact Nat.le_ceil _)]
    simpa [sigma12EndpointRemainder, caseI1423Sigma12Endpoint] using h12q
  have hscalarD := hscalar C1 K (D : ℝ) hscalarC1 hK
    (by exact_mod_cast hD2) hlarge
  have hend := caseI1423EndpointSourceBounds_evenEndpoint_explicit
    S H C K d Δ L R hH hCpos hsrc.hDelta_pos
      hsrc.hDelta_lt hsrc.h14_1 hL hfinite hR _hratio
      D M hD3 hscalarD hM hM2 h2σ
  have hzσ : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) := by
    simpa [z, σ] using g.hpowerOrder.trans (Nat.le_ceil _)
  have hzeroRaw := hcaseB S C1 C K M D z hcaseBC1 hCBC hK hlocal hD2
    hlarge hM hM2 hzσ
  have hi := (h146 (D : ℝ) hD146).1
  have hEtransport : errorEnvelope H M (D : ℝ) d σ ≤
      errorEnvelope H M (D : ℝ) d 2 := by
    apply errorEnvelope_endpoint_le_of_claim14_6 hH.toSection13HatContract hDreal hi
    rw [hH.betaHat_eq]
    exact ⟨hEvenLower, by simpa [σ] using h2σ⟩
  have hzeroUnit : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      (CB / C) * caseI1423RemainderUnit
        (sigma12InheritedBudget S H M D z C K d Δ 2) (D : ℝ) σ := by
    apply hzeroRaw.trans
    have hscale := caseI_claim145Scale_le_transported_remainderUnit S H
      (K := K) (Δ := Δ)
      hH hD3 hCpos hCB.le (by norm_num : (1 : ℝ) ≤ 2) h2σ hEtransport
    simpa only [← mul_assoc, div_mul_cancel₀ _ hCpos.ne'] using hscale
  have hAactual : 0 ≤ CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R := by
    positivity
  have hAupper : CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R ≤ Amax := by
    have hb := caseI_endpointCoefficient_le_commonScale
      (A := (1 : ℝ)) (C := C) (C145 := CB) (K := K) (L := L) (R := R)
      (by norm_num) hC3 (by simpa using hCBC) (by linarith [hL]) (by linarith [hR])
    norm_num at hb
    simpa [Amax, CB] using hb
  obtain ⟨qgap, hqgap, hcoefGap⟩ := hcoef C1 K (D : ℝ)
    (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R)
    hcoefC1 hK (by exact_mod_cast hD2) hAactual hAupper hlarge
  have hqrho : q12.ρ = qgap.ρ := by rw [hq12, hqgap]
  have hbudget : 0 ≤ sigma12InheritedBudget S H M D z C K d Δ 2 := by
    unfold sigma12InheritedBudget
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hCpos.le (Real.exp_pos _).le)
          (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _))
      (errorEnvelope_nonneg H M hDreal (by norm_num)
        (hH.positive _ _ (by norm_num)).le)
  have hside : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiVProduct S z * (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
          Real.log ((D : ℝ) ^ (1 / σ))) +
        caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ ≤
      (1 - q12.ρ) * sigma12InheritedBudget S H M D z C K d Δ 2 := by
    rw [hqrho]
    exact caseI_three_remainders_le_gap hbudget hzeroUnit hend.1 hend.2 hcoefGap
  have h2raw := lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (N := M) S hD4 (by norm_num : (2 : ℝ) ≤ 2) hz
  have h2 : suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / (2 : ℝ))) = 0 := by
    simpa [lemma144_realTau_eq_s_of_caseI hD4 (by norm_num : (2 : ℝ) ≤ 2)] using h2raw
  have hmiddle : suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ))
      ((D : ℝ) ^ (1 / (2 : ℝ))) ≤
      sigmaEleven (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S z) 2 M D σ 2 +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ M D σ 2 := by
    change sigmaOne (suzukiSupportedBelow S z) S.nu (suzukiActualT S) M D σ 2 ≤ _
    exact h10
  dsimp [CaseIEvenEndpointSigma11Edge] at h11
  rw [h149, h2]
  linarith [hmiddle, h11, h12qSupported, hside]



#print axioms numerical_caseB_coefficient_one
#print axioms numerical_caseI_coefficient_one
#print axioms numerical_caseI_even_coefficient_one
end ChenEffective
