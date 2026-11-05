import NumericalMertensPower
import NumericalGoldbachInterval

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
open AnalyticNumberTheory.Mertens
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

theorem goldbach_log_interval_power {B C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 9 ≤ n →
      |primeReciprocalSum n - (log (log (n : ℝ)) + B)| ≤ C * (n : ℝ) ^ (-1 / 128 : ℝ))
    (k n : ℕ) (hk9 : 9 ≤ k) (hkn : k ≤ n)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ k < p ∧ p ≤ n) :
    log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log (log n / log k) + (2 * C + 24) * (k : ℝ) ^ (-1 / 128 : ℝ) := by
  have hk : 2 ≤ k := by omega
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
        log (log n / log k) + 2 * C * (k : ℝ) ^ (-1 / 128 : ℝ) := by
    have hMn := hM n (hk9.trans hkn)
    have hMk := hM k hk9
    have hdec : (n : ℝ) ^ (-1 / 128 : ℝ) ≤ (k : ℝ) ^ (-1 / 128 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hkn) (by norm_num)
    have hlogs :
        log (log n) - log (log k) = log (log n / log k) := by
      rw [← Real.log_div hlogn.ne' hlogk.ne']
    have hh := mul_le_mul_of_nonneg_left hdec hC
    have hu := (abs_le.mp hMn).2
    have hl := (abs_le.mp hMk).1
    rw [hlogs.symm]
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
  have hloginv : 1 / (k : ℝ) ≤ (k : ℝ) ^ (-1 / 128 : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ k by omega))
      (by norm_num)
  calc
    log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) =
        ∑ p ∈ s, log (1 - 1 / ((p : ℝ) - 1))⁻¹ := hlogprod
    _ ≤ ∑ p ∈ s, (1 / (p : ℝ) + 12 / (p : ℝ) ^ 2) := hlocal
    _ = (∑ p ∈ s, 1 / (p : ℝ)) + 12 * (∑ p ∈ s, 1 / (p : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (primeReciprocalSum n - primeReciprocalSum k) + 12 * (2 / (k : ℝ)) :=
      add_le_add hrecip (mul_le_mul_of_nonneg_left hsq (by norm_num))
    _ ≤ log (log n / log k) + (2 * C + 24) * (k : ℝ) ^ (-1 / 128 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hloginv (by norm_num : (0 : ℝ) ≤ 24)
      calc
        _ = (primeReciprocalSum n - primeReciprocalSum k) + 24 * (1 / (k : ℝ)) := by ring
        _ ≤ (log (log n / log k) + 2 * C * (k : ℝ) ^ (-1 / 128 : ℝ)) +
            24 * (k : ℝ) ^ (-1 / 128 : ℝ) := add_le_add hMrecip hh
        _ = _ := by ring

/-- Real interval endpoints, retaining the power saving also in the rounding
error. This applies to every subset of the odd primes in the interval. -/
theorem goldbach_interval_power (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ) (hu : 10 ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log z / log u * exp (130000000000000 * u ^ (-1 / 128 : ℝ)) := by
  let k := Nat.ceil u - 1
  let n := max k (Nat.floor z)
  have hu0 : 0 < u := by linarith
  have hk9 : 9 ≤ k := by
    have hh := Nat.le_ceil u
    have hh' : 10 ≤ Nat.ceil u := by exact_mod_cast (hu.trans hh)
    dsimp [k]; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkcast : (k : ℝ) = (Nat.ceil u : ℝ) - 1 := by
    dsimp [k]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hku : (k : ℝ) ≤ u := by
    rw [hkcast]
    linarith [Nat.ceil_lt_add_one hu0.le]
  have huk : u ≤ (k : ℝ) + 1 := by
    rw [hkcast]
    linarith [Nat.le_ceil u]
  have hkhalf : u / 2 ≤ (k : ℝ) := by
    have : (9 : ℝ) ≤ k := by exact_mod_cast hk9
    linarith
  have hkn : k ≤ n := le_max_left _ _
  have hnz : (n : ℝ) ≤ z := by
    dsimp [n]
    rw [Nat.cast_max, max_le_iff]
    exact ⟨hku.trans huz, Nat.floor_le (hu0.le.trans huz)⟩
  have hlk : 1 ≤ log (k : ℝ) := one_le_log_three.trans
    (log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ k by omega)))
  have hlk0 : 0 < log (k : ℝ) := by linarith
  have hlu : 0 < log u := log_pos (by linarith)
  have hln : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlz : 0 < log z := hlu.trans_le (log_le_log hu0 huz)
  have hb := goldbach_log_interval_power (B := mertensSecondConstant)
    (C := 30000000000000) (by norm_num) (fun m hm => by
      simpa only [Nat.floor_natCast] using numerical_mertens_power
        (show (9 : ℝ) ≤ m by exact_mod_cast hm)) k n hk9 hkn s (by
      intro p hp
      refine ⟨(hs p hp).1, ?_, ?_⟩
      · have hh : Nat.ceil u ≤ p := Nat.ceil_le.mpr (hinterval p hp).1
        dsimp [k]; omega
      · exact (Nat.le_floor (hinterval p hp).2.le).trans (le_max_right _ _))
  have hround : log (log u / log (k : ℝ)) ≤ 1 / (k : ℝ) := by
    have hd : log u - log (k : ℝ) ≤ 1 / (k : ℝ) := by
      calc
        _ = log (u / (k : ℝ)) := (log_div hu0.ne' hk0.ne').symm
        _ ≤ u / (k : ℝ) - 1 := log_le_sub_one_of_pos (by positivity)
        _ ≤ 1 / (k : ℝ) := by
          apply (le_div_iff₀ hk0).mpr
          field_simp
          linarith
    calc
      _ ≤ log u / log (k : ℝ) - 1 := log_le_sub_one_of_pos (by positivity)
      _ = (log u - log (k : ℝ)) / log (k : ℝ) := by field_simp
      _ ≤ (1 / (k : ℝ)) / log (k : ℝ) := div_le_div_of_nonneg_right hd hlk0.le
      _ ≤ 1 / (k : ℝ) := div_le_self (by positivity) hlk
  have hkp : 1 / (k : ℝ) ≤ (k : ℝ) ^ (-1 / 128 : ℝ) := by
    rw [one_div, ← rpow_neg_one]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ k by omega))
      (by norm_num)
  have hpow : (k : ℝ) ^ (-1 / 128 : ℝ) ≤ 2 * u ^ (-1 / 128 : ℝ) := by
    calc
      _ ≤ (u / 2) ^ (-1 / 128 : ℝ) :=
        rpow_le_rpow_of_nonpos (by positivity) hkhalf (by norm_num)
      _ = u ^ (-1 / 128 : ℝ) * 2 ^ (1 / 128 : ℝ) := by
        rw [div_rpow hu0.le (by norm_num), show (-1 / 128 : ℝ) = -(1 / 128) by ring,
          rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      _ ≤ u ^ (-1 / 128 : ℝ) * 2 := by
        gcongr
        exact (rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 128 : ℝ) ≤ 1)).trans_eq (rpow_one _)
      _ = _ := by ring
  have hinner : log (log (n : ℝ) / log (k : ℝ)) ≤
      log (log z / log u) + 1 / (k : ℝ) := by
    calc
      _ ≤ log (log z / log (k : ℝ)) := log_le_log (by positivity)
        (div_le_div_of_nonneg_right (log_le_log (by positivity) hnz) hlk0.le)
      _ = log (log z / log u) + log (log u / log (k : ℝ)) := by
        rw [log_div hlz.ne' hlk0.ne', log_div hlz.ne' hlu.ne',
          log_div hlu.ne' hlk0.ne']; ring
      _ ≤ _ := add_le_add_right hround _
  have hlogprod : log (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      log (log z / log u) + 130000000000000 * u ^ (-1 / 128 : ℝ) := by
    have hP := rpow_nonneg hu0.le (-1 / 128 : ℝ)
    norm_num only at hb
    nlinarith only [hb, hinner, hkp, hpow, hP]
  have hprod : 0 < ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
    prod_pos (fun p hp => inv_pos.mpr (goldbach_local_factor_pos (hs p hp).2))
  have hh := exp_le_exp.mpr hlogprod
  rwa [exp_log hprod, exp_add, exp_log (div_pos hlz hlu)] at hh

#print axioms goldbach_interval_power

/-- A convenient, deliberately rounded starting point. Expressed by a real
power to keep elaboration independent of the size of its natural numeral. -/
noncomputable def powerPresieveStart : ℝ := (3 : ℝ) ^ (5760 : ℝ)

theorem powerPresieveStart_ten : 10 ≤ powerPresieveStart := by
  calc
    (10 : ℝ) ≤ (3 : ℝ) ^ (3 : ℕ) := by norm_num
    _ = (3 : ℝ) ^ (3 : ℝ) := (rpow_natCast _ _).symm
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (3 : ℝ) ≤ 5760)

theorem powerPresieveStart_error {u : ℝ} (hu : powerPresieveStart ≤ u) :
    130000000000000 * u ^ (-1 / 128 : ℝ) ≤ 1 / 20000000 := by
  have hU : 0 < powerPresieveStart := by
    unfold powerPresieveStart; positivity
  have hh := rpow_le_rpow_of_nonpos hU hu (by norm_num : (-1 / 128 : ℝ) ≤ 0)
  have hid : powerPresieveStart ^ (-1 / 128 : ℝ) = ((3 : ℝ) ^ (45 : ℕ))⁻¹ := by
    unfold powerPresieveStart
    rw [← rpow_mul (by norm_num)]
    norm_num [rpow_neg]
  rw [hid] at hh
  have hb := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 130000000000000)
  exact hb.trans (by norm_num)

theorem goldbach_interval_small_error (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : powerPresieveStart ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      (1 + 1 / 10000000 : ℝ) * (log z / log u) := by
  have hu10 := powerPresieveStart_ten.trans hu
  have hu0 : 0 < u := by linarith
  have hl : 0 ≤ log z / log u := by
    apply div_nonneg <;> apply log_nonneg <;> linarith
  have hE := powerPresieveStart_error hu
  have hEn : 0 ≤ 130000000000000 * u ^ (-1 / 128 : ℝ) := by positivity
  have he := Real.abs_exp_sub_one_le (show |130000000000000 * u ^ (-1 / 128 : ℝ)| ≤ 1 by
    rw [abs_of_nonneg hEn]; linarith)
  rw [abs_of_nonneg hEn] at he
  have he' : exp (130000000000000 * u ^ (-1 / 128 : ℝ)) ≤ 1 + 1 / 10000000 := by
    have hh := (abs_le.mp he).2
    linarith
  exact (goldbach_interval_power s hs u z hu10 huz hinterval).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left he' hl)

/-- The uniform product condition after removing primes below the fixed
starting point, including the entire range 1 < u < starting point. -/
theorem goldbach_presieved_small_error (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hpresieve : ∀ p ∈ s, powerPresieveStart ≤ (p : ℝ))
    (u z : ℝ) (hu : 1 < u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      (1 + 1 / 10000000 : ℝ) * (log z / log u) := by
  by_cases hUu : powerPresieveStart ≤ u
  · exact goldbach_interval_small_error s hs u z hUu huz hinterval
  have huU : u ≤ powerPresieveStart := le_of_not_ge hUu
  have hlu : 0 < log u := log_pos hu
  have hlz : 0 < log z := log_pos (hu.trans_le huz)
  by_cases hzU : z ≤ powerPresieveStart
  · have hempty : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      linarith [hpresieve p hp, (hinterval p hp).2]
    rw [hempty, prod_empty]
    have hr : 1 ≤ log z / log u := (le_div_iff₀ hlu).mpr (by
      simpa using log_le_log (by linarith : 0 < u) huz)
    nlinarith
  have hUz : powerPresieveStart ≤ z := le_of_not_ge hzU
  have hb := goldbach_interval_small_error s hs powerPresieveStart z le_rfl hUz
    (fun p hp => ⟨hpresieve p hp, (hinterval p hp).2⟩)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact div_le_div_of_nonneg_left hlz.le hlu (log_le_log (by linarith : 0 < u) huU)

#print axioms goldbach_presieved_small_error

theorem numerical_presieved_source_product (N : ℕ) (u z : ℝ)
    (hu : 1 < u) (huz : u ≤ z) :
    (∏ p ∈ (jurkatRichertSourceSiftingProduct N).primeFactors.filter (fun p : ℕ => powerPresieveStart ≤ (p : ℝ) ∧
          u ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤
        (1 + 1 / 10000000 : ℝ) * (log z / log u) := by
  let s := (jurkatRichertSourceSiftingProduct N).primeFactors.filter (fun p : ℕ => powerPresieveStart ≤ (p : ℝ) ∧
      u ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' := (mem_filter.mp hp).1
    have hprime := Nat.prime_of_mem_primeFactors hp'
    have hdiv := Nat.dvd_of_mem_primeFactors hp'
    exact ⟨hprime, (prime_dvd_jurkatRichertSourceSiftingProduct hprime).mp hdiv |>.1⟩
  change (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤ _
  have heq : (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
      ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply prod_congr rfl
    intro p hp
    rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
  rw [heq]
  exact goldbach_presieved_small_error s hs (fun _ hp => (mem_filter.mp hp).2.1)
    u z hu huz (fun _ hp => (mem_filter.mp hp).2.2)

/-- Elementary primorial cost, valid also when some primes dividing N are
omitted. There is no numerical-prime-table input. -/
theorem presieve_log_cost (s : Finset ℕ) {U : ℝ} (hU : 0 ≤ U)
    (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ U) :
    log (∏ p ∈ s, (p : ℝ)) ≤ log 4 * U := by
  rw [log_prod (fun p hp => by exact_mod_cast (hs p hp).1.ne_zero)]
  apply le_trans _ (Chebyshev.theta_le_log4_mul_x hU)
  unfold Chebyshev.theta
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hs p hp).1.pos,
      Nat.le_floor (hs p hp).2⟩, (hs p hp).1⟩
  · intro p hp _
    exact log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le)

#print axioms numerical_presieved_source_product
#print axioms presieve_log_cost
end ChenEffective

