import ExplicitLogBounds
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVHighChosenUnconditional

/-! Finite chosen high-conductor BV estimates. Proof bodies adapted from
StandardBVHighChosenUnconditional in this repository (Apache-2.0).
All growth assumptions are discharged at the displayed numerical cutoff. -/
namespace ChenEffective
open AnalyticNumberTheory.LargeSieve
open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology
noncomputable section
set_option maxHeartbeats 2400000

theorem chosenTypeII_threshold_explicit (A N : ℕ) (hN : 9 ≤ N) :
      Real.log (N : ℝ) ^ (2 * (A + 49)) ≤
        (standardBVHighChosenUnconditionalTypeIICutoff A N : ℝ) := by
  let x : ℝ := Real.log (N : ℝ)
  let t : ℕ := A + 49
  have hx2 : 2 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have he10 : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
    have h9 : Real.exp 2 < (9 : ℝ) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    have hexp : Real.exp 2 < (N : ℝ) := h9.trans_le (by exact_mod_cast hN)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2 hexp |>.le
  have hx0 : 0 ≤ x := hx2.trans' (by norm_num)
  have hxpow2 : 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
  have hfloor := Nat.sub_one_lt_floor (x ^ (2 * (t + 1)))
  have hhalf : x ^ (2 * t) ≤ x ^ (2 * (t + 1)) - 1 := by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]
    have hbase : 1 ≤ x ^ (2 * t) := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg hx0 (2 * t)]
  have hcast : x ^ (2 * t) ≤ (Nat.floor (x ^ (2 * (t + 1))) : ℝ) :=
    hhalf.trans hfloor.le
  simpa [standardBVHighChosenUnconditionalTypeIICutoff,
    standardBVHighChosenUnconditionalTypeIIConductorExponent, standardBVHighChosenUnconditionalTypeIIExponent,
    logConductorThreshold, x, t, Nat.cast_ofNat] using hcast

theorem explicit_high_typeII (A N : ℕ) (hcut : logPowerCutoff (6 * A + 400) ≤ N) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let u : ℕ → ℕ := fun N => logConductorThreshold N C
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
            highConductorVaughanTypeIIMean N Q C (u N) (v N) ≤
          (1000000000000000000 : ℝ) * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  let K : ℝ := 1000000000000000000
  have hN : 9 ≤ N := (logPowerCutoff_nine_le _).trans hcut
  have hRlower := chosenTypeII_threshold_explicit A N hN
  have hQgrow := log_pow_le_sqrt_explicit_of_le (show 3 * A + 200 ≤ 6 * A + 400 by omega) hcut
  have hCgrow := log_pow_le_sqrt_explicit_of_le
    (show 2 * (3 * A + 200) ≤ 6 * A + 400 by omega) hcut
  clear hcut
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let R : ℕ := logConductorThreshold N C
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let x : ℝ := Real.log (N : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hRpow : x ^ (2 * (A + 49)) ≤ (R : ℝ) := by
    simpa [R, C, standardBVHighChosenUnconditionalTypeIICutoff,
      standardBVHighChosenUnconditionalTypeIIConductorExponent,
      standardBVHighChosenUnconditionalTypeIIExponent, x] using hRlower
  have hRpos : 0 < R := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos hx0 _) hRpow)
  have hsRpos : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hRpos)
  have hsR : x ^ (A + 49) ≤ Real.sqrt (R : ℝ) := by
    have hsRsq : Real.sqrt (R : ℝ) ^ 2 = R := Real.sq_sqrt (by positivity)
    have hp : (x ^ (A + 49)) ^ 2 = x ^ (2 * (A + 49)) := by
      rw [← pow_mul]
      congr 1
      omega
    have hp0 : 0 ≤ x ^ (A + 49) := pow_nonneg hx0.le _
    exact (sq_le_sq₀ hp0 hsRpos.le).mp (by simpa only [hp, hsRsq] using hRpow)
  have hQone : 1 ≤ Q := by
    dsimp [Q, MathlibNt.SieveTheory.LiuWeight.panModulusCutoff]
    have hden : 0 < x ^ B := pow_pos hx0 _
    have hgrow : x ^ B ≤ Real.sqrt N := by
      simpa [B, x] using hQgrow
    have hratio : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / x ^ B := by
      rw [← Real.sqrt_eq_rpow]
      exact (one_le_div₀ hden).2 hgrow
    exact Nat.le_floor (by
      simpa [x, Real.rpow_natCast] using hratio)
  have hQpos : 0 < Q := by omega
  have hQsq : Q ^ 2 ≤ N := by
    simpa [Q] using MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_sq_le
      N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
  have hQleN : Q ≤ N := by
    calc
      Q ≤ Q ^ 2 := by nlinarith
      _ ≤ N := hQsq
  have hQleHalf : Q ≤ N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    by_cases hQsmall : Q ≤ 1
    · omega
    · calc
        Q * 2 ≤ Q * Q := Nat.mul_le_mul_left Q (by omega)
        _ ≤ N := by simpa only [pow_two] using hQsq
  have hRltN : R < N := by
    have hRreal : (R : ℝ) ≤ Real.sqrt N := by
      calc
        (R : ℝ) ≤ Real.log (N : ℝ) ^ C := by
          dsimp [R, logConductorThreshold]
          exact Nat.floor_le (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
        _ ≤ Real.sqrt N := by
          have hpowmono : x ^ C ≤ x ^ (2 * (3 * A + 200)) := by
            apply pow_le_pow_right₀ hx1
            dsimp [C]
            omega
          exact hpowmono.trans (by simpa [x] using hCgrow)
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hslt : Real.sqrt N < (N : ℝ) := by
      nlinarith [Real.sqrt_nonneg (N : ℝ), show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega)]
    exact_mod_cast hRreal.trans_lt hslt
  have haggregate := apNormalizedVaughanTypeIIMeanOn_highConductor_le_allAspect_aggregate
    N Q C R R hN hRpos hQleHalf hRltN hRltN
  have hindexNat :
      (productionConductorBlockGeometry N Q C hRpos).index.card ≤ Nat.log2 N + 1 :=
    productionConductorBlockGeometry_index_card_le_log2 N Q C hRpos hQleN
  have hactiveNat :
      (vaughanTypeIIActiveCanonicalRectangles N R R).card ≤ (Nat.log2 N + 1) ^ 2 := by
    simpa [R, C, standardBVHighChosenUnconditionalTypeIICutoff,
      standardBVHighChosenUnconditionalTypeIIConductorExponent, standardBVHighChosenUnconditionalTypeIIExponent] using
      standardBVHighChosenUnconditionalTypeII_activeCard_le A N
  have hlog2 : (Nat.log2 N : ℝ) ≤ 2 * x := by
    simpa [x] using natLog2_cast_le_two_log (show 2 ≤ N by omega)
  have hlog2one : ((Nat.log2 N + 1 : ℕ) : ℝ) ≤ 3 * x := by
    push_cast
    linarith
  have hactive :
      ((vaughanTypeIIActiveCanonicalRectangles N R R).card : ℝ) ≤ 9 * x ^ 2 := by
    calc
      _ ≤ (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) := by exact_mod_cast hactiveNat
      _ ≤ (3 * x) ^ 2 := pow_le_pow_left₀ (by positivity) hlog2one 2
      _ = 9 * x ^ 2 := by ring
  have hindex :
      (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) ≤ 3 * x := by
    have hc : (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) ≤
        ((Nat.log2 N + 1 : ℕ) : ℝ) := by exact_mod_cast hindexNat
    exact hc.trans hlog2one
  have hlog4 : Real.log (4 * N + 4 : ℕ) ≤ 3 * x := by
    have hpoly : 4 * N + 4 ≤ N * N := by nlinarith
    calc
      Real.log (4 * N + 4 : ℕ) ≤ Real.log (N * N : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpoly)
      _ = 2 * x := by rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; ring
      _ ≤ 3 * x := by nlinarith
  have hQpay : (Q : ℝ) * Real.sqrt N ≤ (N : ℝ) / x ^ B := by
    have hq : (Q : ℝ) ≤ Real.sqrt N / x ^ B := by
      calc
        (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) :=
          Nat.floor_le (by positivity)
        _ = Real.sqrt N / x ^ B := by
          rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
    have hs : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    calc
      (Q : ℝ) * Real.sqrt N ≤ (Real.sqrt N / x ^ B) * Real.sqrt N :=
        mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg _)
      _ = (Real.sqrt N * Real.sqrt N) / x ^ B := by ring
      _ = (N : ℝ) / x ^ B := by rw [← pow_two, hs]
  have hRinv : (N : ℝ) / R ≤ (N : ℝ) / x ^ (A + 49) := by
    have hsRq : Real.sqrt (R : ℝ) ^ 2 = (R : ℝ) := Real.sq_sqrt (by positivity)
    have hsRleR : Real.sqrt (R : ℝ) ≤ (R : ℝ) := by
      nlinarith [Real.sqrt_nonneg (R : ℝ), show (1 : ℝ) ≤ R by exact_mod_cast hRpos]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _) (hsR.trans hsRleR)
  have hRsqrt : (N : ℝ) / Real.sqrt (R + 1 : ℕ) ≤
      (N : ℝ) / x ^ (A + 49) := by
    have hsmono : Real.sqrt (R : ℝ) ≤ Real.sqrt (R + 1 : ℕ) := Real.sqrt_le_sqrt (by norm_num)
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _) (hsR.trans hsmono)
  have hbracket :
      2 * (N : ℝ) / R +
          (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) *
            ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) +
          2 * (Q : ℝ) * Real.sqrt N ≤
        10 * (N : ℝ) / x ^ (A + 48) := by
    have hpow48 : x ^ (A + 48) ≤ x ^ (A + 49) :=
      pow_le_pow_right₀ hx1 (by omega)
    have hden49 : 0 < x ^ (A + 49) := pow_pos hx0 _
    have hden48 : 0 < x ^ (A + 48) := pow_pos hx0 _
    have hsmall : (N : ℝ) / x ^ (A + 49) ≤ (N : ℝ) / x ^ (A + 48) :=
      div_le_div_of_nonneg_left (by positivity) hden48 hpow48
    have hBden : x ^ (A + 48) ≤ x ^ B := by
      dsimp [B]
      exact pow_le_pow_right₀ hx1 (by omega)
    have hqsmall : (N : ℝ) / x ^ B ≤ (N : ℝ) / x ^ (A + 48) :=
      div_le_div_of_nonneg_left (by positivity) hden48 hBden
    let T : ℝ := (N : ℝ) / x ^ (A + 48)
    have hfirst : 2 * (N : ℝ) / R ≤ 2 * T := by
      dsimp [T]
      calc
        2 * (N : ℝ) / R = 2 * ((N : ℝ) / R) := by ring
        _ ≤ 2 * ((N : ℝ) / x ^ (A + 48)) :=
          mul_le_mul_of_nonneg_left (hRinv.trans hsmall) (by norm_num)
    have hsum : (N : ℝ) / Real.sqrt (R + 1 : ℕ) +
        (N : ℝ) / Real.sqrt (R + 1 : ℕ) ≤ 2 * ((N : ℝ) / x ^ (A + 49)) := by
      exact add_le_add hRsqrt hRsqrt |>.trans_eq (by ring)
    have hmiddle0 :
        (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) *
          ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) ≤
        (3 * x) * (2 * ((N : ℝ) / x ^ (A + 49))) := by
      exact mul_le_mul hindex hsum (by positivity) (by positivity)
    have hcancel : (3 * x) * (2 * ((N : ℝ) / x ^ (A + 49))) = 6 * T := by
      dsimp [T]
      rw [show A + 49 = (A + 48) + 1 by omega, pow_succ]
      field_simp
      ring
    have hmiddle :
        (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) *
          ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) ≤
        6 * T := hmiddle0.trans_eq hcancel
    have hthird : 2 * (Q : ℝ) * Real.sqrt N ≤ 2 * T := by
      dsimp [T]
      nlinarith [hQpay, hqsmall]
    calc
      2 * (N : ℝ) / R +
          (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) *
            ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) +
          2 * (Q : ℝ) * Real.sqrt N ≤ 2 * T + 6 * T + 2 * T :=
        add_le_add (add_le_add hfirst hmiddle) hthird
      _ = 10 * (N : ℝ) / x ^ (A + 48) := by dsimp [T]; ring
  have hmean : highConductorVaughanTypeIIMean N Q C R R ≤
      (9 * x ^ 2) * (1000000 * (3 * x) ^ 15) *
        (10 * (N : ℝ) / x ^ (A + 48)) := by
    change apNormalizedVaughanTypeIIMeanOn N R R (highConductorSet N Q C) ≤ _
    exact haggregate.trans (by gcongr)
  have houter :
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
        48 * x ^ 2 :=
    productionAbelConductorEnvelope_le_logPow_two B N (by omega)
  have hnonneg : 0 ≤ highConductorVaughanTypeIIMean N Q C R R := by
    unfold highConductorVaughanTypeIIMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd =>
      mul_nonneg (inv_nonneg.mpr (by positivity))
        (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  calc
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
        highConductorVaughanTypeIIMean N Q C R R ≤
      (48 * x ^ 2) * ((9 * x ^ 2) * (1000000 * (3 * x) ^ 15) *
        (10 * (N : ℝ) / x ^ (A + 48))) :=
      mul_le_mul houter hmean hnonneg (by positivity)
    _ ≤ K * (N : ℝ) / x ^ A := by
      dsimp [K]
      have hconst : (61987278240000000 : ℝ) ≤ 1000000000000000000 := by norm_num
      have hpow : x ^ A ≤ x ^ (A + 29) := pow_le_pow_right₀ hx1 (by omega)
      have hdiv : (N : ℝ) / x ^ (A + 29) ≤ (N : ℝ) / x ^ A :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 A) hpow
      calc
        (48 * x ^ 2) * (9 * x ^ 2 * (1000000 * (3 * x) ^ 15) *
            (10 * (N : ℝ) / x ^ (A + 48))) =
            61987278240000000 * ((N : ℝ) / x ^ (A + 29)) := by
              rw [show A + 48 = (A + 29) + 19 by omega, pow_add]
              field_simp
              ring
        _ ≤ 61987278240000000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ ≤ 1000000000000000000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = 1000000000000000000 * (N : ℝ) / x ^ A := by ring

theorem explicit_high_typeI (A N : ℕ) (hcut : logPowerCutoff (6 * A + 400) ≤ N) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let u : ℕ → ℕ := fun N => logConductorThreshold N C
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
            highConductorVaughanTypeIMean N Q C (u N) (v N) ≤
          (2000 : ℝ) * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  have hN : 9 ≤ N := (logPowerCutoff_nine_le _).trans hcut
  have hCgrow := log_pow_le_sqrt_explicit_of_le (show 2 * (A + 50) ≤ 6 * A + 400 by omega) hcut
  clear hcut
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let R : ℕ := logConductorThreshold N C
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let x : ℝ := Real.log (N : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hRcast : (R : ℝ) ≤ x ^ C := by
    dsimp [R, logConductorThreshold]
    exact Nat.floor_le (pow_nonneg hx0.le _)
  have hRC : (0 : ℝ) ≤ R := by positivity
  have hRleN : R ≤ N := by
    have hRsqrt : (R : ℝ) ≤ Real.sqrt N := hRcast.trans (by simpa [C, x] using hCgrow)
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hsle : Real.sqrt N ≤ (N : ℝ) := by
      nlinarith [Real.sqrt_nonneg (N : ℝ), show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)]
    exact_mod_cast hRsqrt.trans hsle
  have hlogN1 : Real.log (N + 1 : ℕ) ≤ 2 * x := by
    have hpoly : N + 1 ≤ N * N := by nlinarith
    calc
      Real.log (N + 1 : ℕ) ≤ Real.log (N * N : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpoly)
      _ = 2 * x := by rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; ring
  have hlogR1 : Real.log (R + 1 : ℕ) ≤ 2 * x := by
    exact (Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hRleN)).trans hlogN1
  have hRCone : (1 : ℝ) ≤ x ^ C := one_le_pow₀ hx1
  have hcore :
      (R : ℝ) * Real.log (N + 1 : ℕ) +
          (R : ℝ) * R * Real.log (R + 1 : ℕ) ≤
        4 * x ^ (2 * C + 1) := by
    have hRmajor : (R : ℝ) ≤ (x ^ C) ^ 2 :=
      hRcast.trans (by nlinarith only [hRCone])
    have hR2 : (R : ℝ) ^ 2 ≤ (x ^ C) ^ 2 :=
      pow_le_pow_left₀ hRC hRcast 2
    calc
      _ = (R : ℝ) * Real.log (N + 1 : ℕ) +
          (R : ℝ) ^ 2 * Real.log (R + 1 : ℕ) := by ring
      _ ≤ (x ^ C) ^ 2 * (2 * x) + (x ^ C) ^ 2 * (2 * x) := by
        apply add_le_add
        · exact mul_le_mul hRmajor hlogN1 (by positivity) (sq_nonneg _)
        · exact mul_le_mul hR2 hlogR1 (by positivity) (sq_nonneg _)
      _ = 4 * x ^ (2 * C + 1) := by
        rw [show 2 * C + 1 = C + C + 1 by omega, pow_succ, pow_add]
        ring
  have hQcast : (Q : ℝ) ≤ Real.sqrt N / x ^ B := by
    calc
      (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) :=
        Nat.floor_le (by positivity)
      _ = Real.sqrt N / x ^ B := by
        rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQsq : (Q : ℝ) ^ 2 ≤ (N : ℝ) / x ^ (2 * B) := by
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hden : 0 < x ^ B := pow_pos hx0 _
    have hsquared := pow_le_pow_left₀ hQ0 hQcast 2
    calc
      (Q : ℝ) ^ 2 ≤ (Real.sqrt N / x ^ B) ^ 2 := hsquared
      _ = (N : ℝ) / x ^ (2 * B) := by
        rw [div_pow, hsSq, ← pow_mul, show B * 2 = 2 * B by omega]
  have hmean := highConductorVaughanTypeIMean_le_elementaryCauchy N Q C R R
  have hmean' : highConductorVaughanTypeIMean N Q C R R ≤
      24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1) := by
    calc
      _ ≤ 6 * (Q : ℝ) ^ 2 *
          ((R : ℝ) * Real.log (N + 1 : ℕ) +
            (R : ℝ) * R * Real.log (R + 1 : ℕ)) := hmean
      _ ≤ 6 * ((N : ℝ) / x ^ (2 * B)) * (4 * x ^ (2 * C + 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQsq (by norm_num)) hcore
          (by positivity) (by positivity)
      _ = 24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1) := by ring
  have houter :
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
        48 * x ^ 2 :=
    productionAbelConductorEnvelope_le_logPow_two B N (by omega)
  have hscale : ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 3) ≤
      (N : ℝ) / x ^ A := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hx0 _) (pow_pos hx0 _)]
    have hexp : 2 * C + 3 + A ≤ 2 * B := by dsimp [B, C]; omega
    calc
      (N : ℝ) * x ^ (2 * C + 3) * x ^ A = (N : ℝ) * x ^ (2 * C + 3 + A) := by rw [pow_add]; ring
      _ ≤ (N : ℝ) * x ^ (2 * B) := by
        gcongr
  have hnonneg : 0 ≤ highConductorVaughanTypeIMean N Q C R R := by
    unfold highConductorVaughanTypeIMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd => mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  calc
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
        highConductorVaughanTypeIMean N Q C R R ≤
      (48 * x ^ 2) * (24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1)) :=
        mul_le_mul houter hmean' hnonneg (by positivity)
    _ = 1152 * (((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 3)) := by ring
    _ ≤ 2000 * (N : ℝ) / x ^ A := by
      calc
        _ ≤ 1152 * ((N : ℝ) / x ^ A) := mul_le_mul_of_nonneg_left hscale (by norm_num)
        _ ≤ 2000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = _ := by ring

theorem explicit_chosen_cutoff_balanced (A N : ℕ) (hcut : logPowerCutoff (6 * A + 400) ≤ N) :
      logConductorThreshold N (2 * (A + 50)) ≤
        standardBVBalancedSmallCutoff N := by
  have hN : 2 ≤ N := by have := (logPowerCutoff_nine_le _).trans hcut; omega
  have hlog := log_pow_le_sqrt_explicit_of_le (show 3 * (2 * (A + 50)) ≤ 6 * A + 400 by omega) hcut
  clear hcut
  let x : ℝ := Real.log (N : ℝ)
  let C : ℕ := 2 * (A + 50)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqrtSq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hN0
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hpow : x ^ (3 * C) ≤ Real.sqrt (N : ℝ) := by
    simpa [x, C] using hlog
  have hcub : (x ^ C) ^ 3 ≤ (N : ℝ) := by
    rw [← pow_mul]
    have heq : C * 3 = 3 * C := by omega
    rw [heq]
    exact hpow.trans hsqrt
  have hrpow : x ^ C ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    have hcub' : (x ^ C) ^ (3 : ℝ) ≤ (N : ℝ) := by
      simpa [Real.rpow_natCast] using hcub
    have h := (Real.le_rpow_inv_iff_of_pos
      (pow_nonneg hx0 C) hN0 (by norm_num : (0 : ℝ) < 3)).2 hcub'
    simpa [one_div] using h
  unfold logConductorThreshold standardBVBalancedSmallCutoff
  exact Nat.floor_mono (by simpa [x, C] using hrpow)


theorem explicit_small_square_payment
    (cutoff : ℕ → ℕ)
    (A κ B C N : ℕ)
    (hcut : cutoff N ≤ standardBVBalancedSmallCutoff N)
    (hN : 8 ≤ N)
    (hlogPay : Real.log (N : ℝ) ^ (10 + 2 * (A + κ)) ≤ Real.sqrt N)
    (hcutGrow : Real.log (N : ℝ) ^ B ≤ Real.sqrt N) :
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let R := logConductorThreshold N C
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        let X := (N : ℝ) / Real.log N ^ (A + κ)
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff
                (cutoff N)) N
              (highConductorSet N Q C)) ≤ ((10000 : ℝ) * X) ^ 2 := by
  let M : ℝ := 497664 * (15 + 4 / Real.log 2)
  let K₀ : ℝ := 10000
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : M ≤ K₀ ^ 2 := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiv : (4 : ℝ) / Real.log 2 ≤ 8 :=
      (div_le_iff₀ (by linarith)).mpr (by linarith)
    dsimp [M, K₀]
    nlinarith only [hdiv]
  dsimp only
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hQone : 1 ≤ Q := by
    dsimp [Q, MathlibNt.SieveTheory.LiuWeight.panModulusCutoff]
    have hdenPos : 0 < Real.log (N : ℝ) ^ (B : ℝ) := by
      simpa [Real.rpow_natCast] using pow_pos hlogPos B
    have hcutGrow' : Real.log (N : ℝ) ^ (B : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_natCast] using hcutGrow
    apply Nat.le_floor
    simpa only [Nat.cast_one] using (one_le_div₀ hdenPos).2 hcutGrow'
  have hQpos : 0 < Q := by omega
  have hQsq : Q ^ 2 ≤ N := by
    simpa [Q] using MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_sq_le
      N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
  have hvN := hcut.trans (standardBVBalancedSmallCutoff_le N)
  have hvSqrt : (cutoff N : ℝ) ≤ Real.sqrt N :=
    (Nat.cast_le.mpr hcut).trans (standardBVBalancedSmallCutoff_cast_le_sqrt N)
  have htop := standardBVSmall_weightedSquareLedger_le_log N Q
    (logConductorThreshold N C) C (cutoff N) hN hQpos hQsq hvN hvSqrt
  have hlogDiv : Real.log (N : ℝ) ^ 10 ≤
      Real.sqrt N / Real.log N ^ (2 * (A + κ)) := by
    apply (le_div_iff₀ (pow_pos hlogPos _)).2
    simpa only [pow_add] using hlogPay
  refine htop.trans ?_
  calc
    M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10
        ≤ M * (N : ℝ) * Real.sqrt N *
          (Real.sqrt N / Real.log N ^ (2 * (A + κ))) := by gcongr
    _ = M * ((N : ℝ) ^ 2 / Real.log N ^ (2 * (A + κ))) := by
      calc
        _ = M * ((N : ℝ) * (Real.sqrt N * Real.sqrt N) /
            Real.log N ^ (2 * (A + κ))) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]; ring
    _ ≤ K₀ ^ 2 * ((N : ℝ) ^ 2 / Real.log N ^ (2 * (A + κ))) := by gcongr
    _ = (K₀ * ((N : ℝ) / Real.log N ^ (A + κ))) ^ 2 := by ring


theorem explicit_high_small (A N : ℕ) (hcut : logPowerCutoff (6 * A + 400) ≤ N) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        P * highConductorVaughanSmallMean N Q C (v N) ≤
          (10000 : ℝ) * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let v : ℕ → ℕ := fun N => logConductorThreshold N C
  let K₀ : ℝ := 10000
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hcut
  have hv : v N ≤ standardBVBalancedSmallCutoff N := explicit_chosen_cutoff_balanced A N hcut
  have hsmallPay := explicit_small_square_payment v A 0 B C N hv (by omega)
    (log_pow_le_sqrt_explicit_of_le (show 10 + 2 * (A + 0) ≤ 6 * A + 400 by omega) hcut)
    (log_pow_le_sqrt_explicit_of_le (show B ≤ 6 * A + 400 by dsimp [B]; omega) hcut)
  clear hcut
  dsimp only at hsmallPay ⊢
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let R := logConductorThreshold N C
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  have hR : 0 < R := by
    dsimp [R, logConductorThreshold]
    have hlog : 1 < Real.log (N : ℝ) := by
      have h9 : Real.exp 1 < (9 : ℝ) := by
        nlinarith [Real.exp_one_lt_d9]
      exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
        (h9.trans_le (by exact_mod_cast hN9))
    have hpow : 1 < Real.log (N : ℝ) ^ C := by
      have hC : 0 < C := by dsimp [C]; omega
      exact one_lt_pow₀ hlog hC.ne'
    exact Nat.floor_pos.mpr hpow.le
  have hsmall : P * highConductorVaughanSmallMean N Q C (v N) ≤
      K₀ * ((N : ℝ) / Real.log N ^ A) := by
    apply apNormalizedPrimitiveMeanOn_high_le_of_square_payment
      _ N Q C P _ hR (by positivity)
    simpa only [Nat.add_zero] using hsmallPay
  calc
    P * highConductorVaughanSmallMean N Q C (v N) ≤
        K₀ * ((N : ℝ) / Real.log N ^ A) := hsmall
    _ = K₀ * (N : ℝ) / Real.log N ^ A := by ring



def highBVExponent (A : ℕ) : ℕ := 3 * A + 200
def highBVConductorExponent (A : ℕ) : ℕ := 2 * (A + 50)
def highBVThreshold (A : ℕ) : ℕ := logPowerCutoff (6 * A + 400)

/-- The complete high-conductor hybrid has an entirely numerical constant
and starting point. No low-conductor or PNT estimate is used. -/
theorem explicit_high_payment (A N : ℕ) (hcut : highBVThreshold A ≤ N) :
    let B := highBVExponent A
    let C := highBVConductorExponent A
    let R := logConductorThreshold N C
    let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
      (highConductorVaughanTypeIMean N Q C R R +
       highConductorVaughanTypeIIMean N Q C R R +
       highConductorVaughanSmallMean N Q C R) ≤
      (1000000000000012000 : ℝ) * (N : ℝ) / Real.log N ^ A := by
  have hI := explicit_high_typeI A N hcut
  have hII := explicit_high_typeII A N hcut
  have hsmall := explicit_high_small A N hcut
  dsimp only at hI hII hsmall
  dsimp only [highBVExponent, highBVConductorExponent]
  set Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N ((3 * A + 200 : ℕ) : ℝ)
  set C := 2 * (A + 50)
  set R := logConductorThreshold N C
  set P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  change P * (_ + _ + _) ≤ _
  calc
    _ = P * highConductorVaughanTypeIMean N Q C R R +
        P * highConductorVaughanTypeIIMean N Q C R R +
        P * highConductorVaughanSmallMean N Q C R := by ring
    _ ≤ 2000 * (N : ℝ) / Real.log N ^ A +
        1000000000000000000 * (N : ℝ) / Real.log N ^ A +
        10000 * (N : ℝ) / Real.log N ^ A := add_le_add (add_le_add hI hII) hsmall
    _ = _ := by ring

#print axioms explicit_high_typeI
#print axioms explicit_high_typeII
#print axioms explicit_high_small
#print axioms explicit_high_payment
end
end ChenEffective
