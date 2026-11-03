import NumericalMertensGlobal
import MathlibNt.SieveTheory.Switching.RosserSieveAsymptotics

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.MertensTheorem
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private lemma goldbach_local_factor_pos {p : ℕ} (hp2 : 2 < p) :
    0 < 1 - 1 / ((p : ℝ) - 1) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp2
  have hrec : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- For an odd prime, the logarithm of the inverse Goldbach local factor is
controlled by its reciprocal-prime main term and a summable error. -/
private lemma log_goldbach_inverse_factor_le {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    log (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
      1 / (p : ℝ) + 12 / (p : ℝ) ^ 2 := by
  have hp3 : 3 ≤ p := by omega
  have hpm1 : 0 < (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have ht : 0 < 1 / ((p : ℝ) - 1) := div_pos one_pos hpm1
  have htle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (2 : ℝ) ≤ (p : ℝ) - 1 := by
      have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    linarith
  have hlocal := AnalyticNumberTheory.Mertens.abs_log_one_sub_add_le ht htle
  have hlog :
      log (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        1 / ((p : ℝ) - 1) + 2 * (1 / ((p : ℝ) - 1)) ^ 2 := by
    rw [Real.log_inv]
    have := (abs_le.mp hlocal).1
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpm1
  have hmain :
      1 / ((p : ℝ) - 1) + 2 * (1 / ((p : ℝ) - 1)) ^ 2 ≤
        1 / (p : ℝ) + 12 / (p : ℝ) ^ 2 := by
    have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    field_simp [hp0, hpm1ne]
    nlinarith [sq_nonneg ((p : ℝ) - 3)]
  exact hlog.trans hmain

theorem goldbach_log_interval_of_mertens {B C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - (log (log (n : ℝ)) + B)| ≤ C / log (n : ℝ))
    (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ k < p ∧ p ≤ n) :
    log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log (log n / log k) + (2 * C + 24) / log k := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hlogk : 0 < log k := Real.log_pos hk1
  have hn2 : 2 ≤ n := le_trans hk hkn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < log n := Real.log_pos hn1
  let T := (Finset.Ioo k (n + 1)).filter Nat.Prime
  have hsub : s ⊆ T := by
    intro p hp
    rcases hs p hp with ⟨hpp, hkp, hpn⟩
    simp only [T, Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨hkp, by omega⟩, hpp⟩
  have hlogprod :
      log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) =
        ∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Real.log_prod
    intro p hp
    exact (inv_pos.mpr (goldbach_local_factor_pos
      (lt_of_le_of_lt hk (hs p hp).2.1))).ne'
  have hlocal :
      (∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
        (∑ p ∈ s, (1 / (p : ℝ) + 12 / (p : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact log_goldbach_inverse_factor_le (hs p hp).1
      (lt_of_le_of_lt hk (hs p hp).2.1)
  have hrecip :
      (∑ p ∈ s, 1 / (p : ℝ)) ≤
        primeReciprocalSum n - primeReciprocalSum k := by
    have hT :
        (∑ p ∈ T, 1 / (p : ℝ)) =
          primeReciprocalSum n - primeReciprocalSum k := by
      let Pn := (Finset.range (n + 1)).filter Nat.Prime
      let Pk := (Finset.range (k + 1)).filter Nat.Prime
      have hPk : Pk ⊆ Pn := by
        intro p hp
        simp only [Pk, Pn, Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨by omega, hp.2⟩
      have hTdiff : T = Pn \ Pk := by
        ext p
        simp only [T, Pn, Pk, Finset.mem_filter, Finset.mem_Ioo,
          Finset.mem_sdiff, Finset.mem_range]
        constructor
        · rintro ⟨⟨hkp, hpn⟩, hp⟩
          exact ⟨⟨hpn, hp⟩, by
            intro hpk
            omega⟩
        · rintro ⟨⟨hpn, hp⟩, hnot⟩
          refine ⟨⟨?_, hpn⟩, hp⟩
          by_contra hkp
          apply hnot
          exact ⟨Nat.lt_succ_iff.mpr (le_of_not_gt hkp), hp⟩
      rw [hTdiff, Finset.sum_sdiff_eq_sub hPk]
      rfl
    calc
      (∑ p ∈ s, 1 / (p : ℝ)) ≤ ∑ p ∈ T, 1 / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => div_nonneg zero_le_one (by positivity))
      _ = primeReciprocalSum n - primeReciprocalSum k := hT
  have hMrecip :
      primeReciprocalSum n - primeReciprocalSum k ≤
        log (log n / log k) + 2 * C / log k := by
    have hMn := hM n hn2
    have hMk := hM k hk
    have hupper :
        primeReciprocalSum n ≤ log (log n) + B + C / log n := by
      linarith [(abs_le.mp hMn).2]
    have hlower :
        log (log k) + B - C / log k ≤ primeReciprocalSum k := by
      linarith [(abs_le.mp hMk).1]
    have hCdiv : C / log n ≤ C / log k := by
      apply div_le_div_of_nonneg_left hC hlogk
      exact Real.log_le_log (by positivity) (by exact_mod_cast hkn)
    have hlogs :
        log (log n) - log (log k) = log (log n / log k) := by
      rw [← Real.log_div hlogn.ne' hlogk.ne']
    calc
      primeReciprocalSum n - primeReciprocalSum k ≤
          (log (log n) - log (log k)) + C / log n + C / log k := by
        linarith
      _ ≤ log (log n / log k) + 2 * C / log k := by
        rw [hlogs]
        have htwo : 2 * C / log k = C / log k + C / log k := by ring
        rw [htwo]
        linarith
  have hsq :
      (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤ 2 / (k : ℝ) := by
    calc
      (∑ p ∈ s, 1 / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Finset.Ioo k (n + 1), 1 / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => (Finset.mem_filter.mp (hsub hp)).1)
          (fun p _ _ => by positivity)
      _ ≤ 2 / ((k : ℝ) + 1) := by
        simpa only [one_div] using (sum_Ioo_inv_sq_le (α := ℝ) k (n + 1))
      _ ≤ 2 / (k : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num)
        positivity
        linarith
  have hloginv : 1 / (k : ℝ) ≤ 1 / log k := by
    apply one_div_le_one_div_of_le hlogk
    have := Real.log_le_sub_one_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hk) :
      0 < (k : ℝ))
    linarith
  calc
    log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) =
        ∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹ := hlogprod
    _ ≤ ∑ p ∈ s, (1 / (p : ℝ) + 12 / (p : ℝ) ^ 2) := hlocal
    _ = (∑ p ∈ s, 1 / (p : ℝ)) + 12 * (∑ p ∈ s, 1 / (p : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib]
      congr 1
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (primeReciprocalSum n - primeReciprocalSum k) +
        12 * (2 / (k : ℝ)) :=
      add_le_add (hrecip) (mul_le_mul_of_nonneg_left hsq (by norm_num))
    _ ≤ log (log n / log k) + (2 * C + 24) / log k := by
      have h24 : 24 / (k : ℝ) ≤ 24 / log k := by
        calc
          24 / (k : ℝ) = 24 * (1 / (k : ℝ)) := by ring
          _ ≤ 24 * (1 / log k) :=
            mul_le_mul_of_nonneg_left hloginv (by norm_num)
          _ = 24 / log k := by ring
      have htwentyfour : 12 * (2 / (k : ℝ)) = 24 / (k : ℝ) := by ring
      calc
        (primeReciprocalSum n - primeReciprocalSum k) + 12 * (2 / (k : ℝ)) ≤
            log (log n / log k) + 2 * C / log k + 24 / log k := by
              rw [htwentyfour]
              linarith
        _ = log (log n / log k) + (2 * C + 24) / log k := by ring

noncomputable def goldbachIntervalConstant (C : ℝ) : ℝ :=
  let D := 2 * (2 * C + 24) + 2 * log 2
  D * exp (D / log 2) + 2

theorem goldbach_interval_of_log_bound {C : ℝ} (hC : 0 ≤ C)
    (hinterval : ∀ k n : ℕ, 2 ≤ k → k ≤ n → ∀ s : Finset ℕ,
      (∀ p ∈ s, p.Prime ∧ k < p ∧ p ≤ n) →
      log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
        log (log n / log k) + (2 * C + 24) / log k)
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (z₁ z₂ : ℝ) (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log z₂ / log z₁ * (1 + goldbachIntervalConstant C / log z₁) := by
  let A : ℝ := 2 * C + 24
  let D : ℝ := 2 * A + 2 * log 2
  let K : ℝ := D * exp (D / log 2) + 2
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; linarith only [hC]
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 1 < K := by
    have : 0 < D * exp (D / log 2) := mul_pos hD (Real.exp_pos _)
    dsimp [K]
    linarith only [this]
  have hz₁pos : 0 < z₁ := by linarith only [hz₁]
  have hz₂pos : 0 < z₂ := hz₁pos.trans_le hz₁₂
  have hlogz₁ : 0 < log z₁ := Real.log_pos (by linarith only [hz₁])
  have hlogz₁₂ : log z₁ ≤ log z₂ := Real.log_le_log hz₁pos hz₁₂
  have hlogz₂ : 0 < log z₂ := hlogz₁.trans_le hlogz₁₂
  have hratio_pos : 0 < log z₂ / log z₁ := div_pos hlogz₂ hlogz₁
  -- One cutoff works on the entire real range, including z₁ = 2.
  -- The ceiling predecessor retains a prime at the closed lower endpoint;
  -- the maximum with 2 is harmless because every prime in s is odd.
  let k : ℕ := max 2 (Nat.ceil z₁ - 1)
  let n : ℕ := max k (Nat.floor z₂)
  have hk2 : 2 ≤ k := le_max_left _ _
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hceil1 : 1 ≤ Nat.ceil z₁ := by
    have := Nat.le_ceil z₁
    by_contra h
    have : Nat.ceil z₁ = 0 := by omega
    simp only [this, Nat.cast_zero] at *
    linarith
  have hpredcast : ((Nat.ceil z₁ - 1 : ℕ) : ℝ) = (Nat.ceil z₁ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil1, Nat.cast_one]
  have hklez₁ : (k : ℝ) ≤ z₁ := by
    dsimp [k]
    rw [Nat.cast_max, max_le_iff, hpredcast]
    exact ⟨hz₁, by linarith only [Nat.ceil_lt_add_one hz₁pos.le]⟩
  have hz₁lek : z₁ ≤ (k : ℝ) + 1 := by
    have hpred : (Nat.ceil z₁ : ℝ) - 1 ≤ (k : ℝ) := by
      rw [← hpredcast]
      exact_mod_cast (le_max_right 2 (Nat.ceil z₁ - 1))
    linarith [Nat.le_ceil z₁]
  have hkhalf : z₁ / 2 ≤ (k : ℝ) := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith only [this, hz₁lek]
  have hnlez₂ : (n : ℝ) ≤ z₂ := by
    dsimp [n]
    rw [Nat.cast_max, max_le_iff]
    exact ⟨hklez₁.trans hz₁₂, Nat.floor_le hz₂pos.le⟩
  have hkn : k ≤ n := le_max_left _ _
  have hlogk : 0 < log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hlogn : 0 < log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hbound := hinterval k n hk2 hkn s (by
    intro p hp
    refine ⟨(hs p hp).1, ?_, ?_⟩
    · have hceil : Nat.ceil z₁ ≤ p := Nat.ceil_le.mpr (hsinterval p hp).1
      have hp2 := (hs p hp).2
      dsimp [k]
      omega
    · exact (Nat.le_floor (hsinterval p hp).2.le).trans (le_max_right _ _))
  -- k ≥ 2 and z₁ ≤ k + 1 imply z₁ ≤ k², so the logarithmic
  -- comparison needs no large/small split or auxiliary exponential threshold.
  have hlogk_half : log z₁ / 2 ≤ log (k : ℝ) := by
    have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hz₁sq : z₁ ≤ (k : ℝ) ^ 2 := by nlinarith only [hk2r, hz₁lek]
    have h := Real.log_le_log hz₁pos hz₁sq
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  have hlogk_lower : log z₁ - log 2 ≤ log (k : ℝ) := by
    calc
      log z₁ - log 2 = log (z₁ / 2) :=
        (Real.log_div hz₁pos.ne' (by norm_num)).symm
      _ ≤ log (k : ℝ) := Real.log_le_log (by positivity) hkhalf
  have hAdiv : A / log (k : ℝ) ≤ 2 * A / log z₁ := by
    apply (div_le_div_iff₀ hlogk hlogz₁).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlogk_half hA]
  have hlogratio : log (log z₁ / log (k : ℝ)) ≤ 2 * log 2 / log z₁ := by
    calc
      log (log z₁ / log (k : ℝ)) ≤ log z₁ / log (k : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hlogz₁ hlogk)
      _ = (log z₁ - log (k : ℝ)) / log (k : ℝ) := by field_simp
      _ ≤ log 2 / log (k : ℝ) :=
        div_le_div_of_nonneg_right (by linarith only [hlogk_lower]) hlogk.le
      _ ≤ 2 * log 2 / log z₁ := by
        apply (div_le_div_iff₀ hlogk hlogz₁).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hlogk_half hlog2.le]
  have hinner : log (log (n : ℝ) / log (k : ℝ)) ≤
      log (log z₂ / log (k : ℝ)) :=
    Real.log_le_log (div_pos hlogn hlogk)
      (div_le_div_of_nonneg_right
        (Real.log_le_log (by positivity) hnlez₂) hlogk.le)
  have hsplit : log (log z₂ / log (k : ℝ)) =
      log (log z₂ / log z₁) + log (log z₁ / log (k : ℝ)) := by
    rw [Real.log_div hlogz₂.ne' hlogk.ne',
      Real.log_div hlogz₂.ne' hlogz₁.ne', Real.log_div hlogz₁.ne' hlogk.ne']
    ring
  have hlogprod : log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log (log z₂ / log z₁) + D / log z₁ := by
    calc
      log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
          log (log (n : ℝ) / log (k : ℝ)) + A / log (k : ℝ) := hbound
      _ ≤ log (log z₂ / log (k : ℝ)) + 2 * A / log z₁ :=
        add_le_add hinner hAdiv
      _ ≤ log (log z₂ / log z₁) +
          (2 * log 2 / log z₁ + 2 * A / log z₁) := by
        rw [hsplit]
        linarith only [hlogratio]
      _ = log (log z₂ / log z₁) + D / log z₁ := by dsimp [D]; ring
  -- Linearize exp on the fixed compact range 0 ≤ D/log z₁ ≤ D/log 2.
  -- Its tangent inequality at -x gives exp x ≤ 1 + x * exp x.
  have hx : 0 ≤ D / log z₁ := by positivity
  have hxupper : D / log z₁ ≤ D / log 2 :=
    div_le_div_of_nonneg_left hD.le hlog2
      (Real.log_le_log (by norm_num) hz₁)
  have hexp : exp (D / log z₁) ≤ 1 + K / log z₁ := by
    have htangent := mul_le_mul_of_nonneg_right
      (Real.add_one_le_exp (-(D / log z₁))) (Real.exp_pos (D / log z₁)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at htangent
    have hmul := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxupper) hx
    calc
      exp (D / log z₁) ≤ 1 + (D / log z₁) * exp (D / log 2) := by
        nlinarith only [htangent, hmul]
      _ ≤ 1 + K / log z₁ := by
        have hKdiv : K / log z₁ =
            (D / log z₁) * exp (D / log 2) + 2 / log z₁ := by
          dsimp only [K]
          ring
        rw [hKdiv]
        have hslack : 0 ≤ (2 : ℝ) / log z₁ := by positivity
        linarith only [hslack]
  have hprodpos : 0 < ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
    Finset.prod_pos (fun p hp => inv_pos.mpr (goldbach_local_factor_pos (hs p hp).2))
  have hprodexp := Real.exp_le_exp.mpr hlogprod
  rw [Real.exp_log hprodpos, Real.exp_add, Real.exp_log hratio_pos] at hprodexp
  exact hprodexp.trans (mul_le_mul_of_nonneg_left hexp hratio_pos.le)


noncomputable def intervalGoldbachConstant : ℝ := goldbachIntervalConstant globalMertensBudget

theorem numerical_goldbach_inverse_interval_bound (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (z₁ z₂ : ℝ) (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log z₂ / log z₁ * (1 + intervalGoldbachConstant / log z₁) := by
  exact goldbach_interval_of_log_bound (Nat.cast_nonneg globalMertensBudget)
    (goldbach_log_interval_of_mertens (Nat.cast_nonneg globalMertensBudget)
      (fun _ hn => numerical_mertens_all hn)) s hs z₁ z₂ hz₁ hz₁₂ hsinterval

#print axioms numerical_goldbach_inverse_interval_bound
end ChenEffective
