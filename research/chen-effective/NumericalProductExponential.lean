import NumericalGoldbachInterval
namespace ChenEffective
open Real Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem goldbach_factor_positive {p : ℕ} (hp : 2 < p) :
    0 < 1 - 1 / ((p : ℝ) - 1) := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [h3])
  linarith only [hh]

theorem goldbach_interval_exponential {C : ℝ} (hC : 0 ≤ C)
    (hinterval : ∀ k n : ℕ, 2 ≤ k → k ≤ n → ∀ s : Finset ℕ,
      (∀ p ∈ s, p.Prime ∧ k < p ∧ p ≤ n) →
      log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
        log (log n / log k) + (2 * C + 24) / log k)
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (z₁ z₂ : ℝ) (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log z₂ / log z₁ * exp ((2 * (2 * C + 24) + 2 * log 2) / log z₁) := by
  let A : ℝ := 2 * C + 24
  let D : ℝ := 2 * A + 2 * log 2
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; linarith only [hC]
  have hD : 0 < D := by dsimp [D]; positivity
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
  have hprodpos : 0 < ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
    Finset.prod_pos (fun p hp => inv_pos.mpr (goldbach_factor_positive (hs p hp).2))
  have hh := Real.exp_le_exp.mpr hlogprod
  rw [Real.exp_log hprodpos, Real.exp_add, Real.exp_log hratio_pos] at hh
  exact hh

end ChenEffective
