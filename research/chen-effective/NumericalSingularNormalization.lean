import NumericalGoldbachProduct

namespace ChenEffective
open Real
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.Internal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem numerical_singular_one_step (N m : ℕ) (hm : 3 ≤ m) :
    (1 - 1 / ((m : ℝ) - 1) ^ 2) *
        SingularSeries.singularSeriesTruncated N (m - 1) ≤
      SingularSeries.singularSeriesTruncated N m := by
  unfold SingularSeries.singularSeriesTruncated
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  simp only [Finset.prod_filter, Finset.prod_range_succ]
  have hprod : 0 ≤ ∏ x ∈ Finset.range m,
      if x.Prime then SingularSeries.localFactor x N else 1 := by
    apply Finset.prod_nonneg
    intro p hp
    split_ifs with hprime
    · exact (SingularSeries.localFactor_pos hprime).le
    · norm_num
  have hfactor : 1 - 1 / ((m : ℝ) - 1) ^ 2 ≤
      if m.Prime then SingularSeries.localFactor m N else 1 := by
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    by_cases hp : m.Prime
    · simp only [hp, if_true]
      by_cases hpdvd : m ∣ N
      · rw [SingularSeries.localFactor_of_dvd hp (by omega) hpdvd]
        field_simp [hm1.ne']
        nlinarith [show (0 : ℝ) ≤ m by positivity]
      · rw [SingularSeries.localFactor_of_not_dvd hp (by omega) hpdvd]
        field_simp [hm1.ne']
        ring_nf
        rfl
    · simp only [hp, if_false]
      have : 0 ≤ 1 / ((m : ℝ) - 1) ^ 2 := by positivity
      linarith
  calc
    (1 - 1 / ((m : ℝ) - 1) ^ 2) *
          (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) =
        (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) *
          (1 - 1 / ((m : ℝ) - 1) ^ 2) := by ring
    _ ≤ (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) *
          (if m.Prime then SingularSeries.localFactor m N else 1) :=
      mul_le_mul_of_nonneg_left hfactor hprod

theorem numerical_ten_factor {m : ℝ} (hm : 10 ≤ m) :
    (1 + 1 / m) ^ (10 : ℕ) ≤ 1 + 20 / m := by
  have hm0 : 0 < m := by linarith only [hm]
  have hu0 : 0 ≤ 10 / m := by positivity
  have hu1 : 10 / m ≤ 1 := (div_le_one hm0).mpr hm
  have he := Real.abs_exp_sub_one_le (show |10 / m| ≤ 1 by rwa [abs_of_nonneg hu0])
  have he' : Real.exp (10 / m) ≤ 1 + 20 / m := by
    rw [abs_of_nonneg hu0] at he
    have hh := le_abs_self (Real.exp (10 / m) - 1)
    simp only [div_eq_mul_inv] at he hh ⊢
    nlinarith only [he, hh]
  calc
    _ ≤ (Real.exp (1 / m)) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (by positivity) (by linarith only [Real.add_one_le_exp (1 / m)]) 10
    _ = Real.exp (10 / m) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := he'

def singularNormalizationThreshold (r : ℕ) : ℕ :=
  max (2 ^ 110 + 1) ((80 * r + 3) ^ 10)

/-- An explicit varying-N replacement for the qualitative singular-series transfer. -/
theorem numerical_source_singular_lower {N r : ℕ} (hr : 0 < r)
    (hN : singularNormalizationThreshold r ≤ N) (hEven : Even N) :
    2 * SingularSeries.liuSingularSeries N ≤
      (1 + 1 / (r : ℝ)) *
        SingularSeries.singularSeriesTruncated N (jurkatRichertSourceZ N - 1) := by
  have hNbig : 2 ^ 110 < N := by
    have hh := (le_max_left _ _).trans hN
    omega
  have hN2 : 2 ≤ N := by omega
  have hcut : 80 * r + 2 ≤ correctedChenZ N - 1 :=
    correctedChenZ_sub_one_ge_of_N_ge (by omega)
      ((le_max_right _ _).trans hN)
  have hz3 : 3 ≤ correctedChenZ N := by omega
  let m := correctedChenZ N - 1
  have hmR : 80 * (r : ℝ) + 2 ≤ m := by exact_mod_cast hcut
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm0 : (0 : ℝ) < m := by linarith only [hmR, hrR]
  have hmajorant : (1 + 1 / (m : ℝ)) ^ (10 : ℕ) ≤ 1 + 1 / (4 * (r : ℝ)) := by
    apply (numerical_ten_factor (by linarith only [hmR, hrR])).trans
    have hh : (20 : ℝ) / m ≤ 1 / (4 * (r : ℝ)) := by
      apply (div_le_div_iff₀ hm0 (by positivity : 0 < 4 * (r : ℝ))).mpr
      linarith only [hmR]
    linarith only [hh]
  have hsplit := singularSeries_eq_trunc_mul_tail N hN2 (by omega)
    (chenZ_le_N_add_one N hN2)
  have htail := chenZ_tail_prod_le_vanishing N hz3
  have hcount := chenZ_tail_prime_count_le N N hNbig (by omega) le_rfl
  have hbase : 1 ≤ 1 + 1 / (m : ℝ) := by
    have hh : 0 ≤ 1 / (m : ℝ) := by positivity
    linarith only [hh]
  have htail' := htail.trans (pow_le_pow_right₀ hbase hcount)
  have hSold := SingularSeries.singularSeriesTruncated_pos N m (by omega)
  have hold : 2 * SingularSeries.liuSingularSeries N ≤
      (1 + 1 / (4 * (r : ℝ))) * SingularSeries.singularSeriesTruncated N m := by
    calc
      _ ≤ SingularSeries.singularSeries N :=
        SingularSeries.two_mul_liuSingularSeries_le_singularSeries N hEven hN2
      _ = _ := hsplit
      _ ≤ SingularSeries.singularSeriesTruncated N m *
          (1 + 1 / (m : ℝ)) ^ (10 : ℕ) :=
        mul_le_mul_of_nonneg_left htail' hSold.le
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hmajorant hSold.le]
  have hstep := numerical_singular_one_step N (correctedChenZ N) hz3
  have hsource : jurkatRichertSourceZ N - 1 = correctedChenZ N := by
    unfold jurkatRichertSourceZ correctedChenZ at *
    omega
  have hstep' : (1 - 1 / (m : ℝ) ^ 2) * SingularSeries.singularSeriesTruncated N m ≤
      SingularSeries.singularSeriesTruncated N (jurkatRichertSourceZ N - 1) := by
    rw [hsource]
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ correctedChenZ N)]
    norm_num only [Nat.cast_one]
    exact hstep
  have hsmall : 1 / (m : ℝ) ^ 2 ≤ 1 / (4 * (r : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hmR, hrR, sq_nonneg ((m : ℝ) - (r : ℝ))]
  have hcoef : 1 + 1 / (4 * (r : ℝ)) ≤
      (1 + 1 / (r : ℝ)) * (1 - 1 / (m : ℝ) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 1 + 1 / (r : ℝ) by positivity)
    have hrr : 1 / (r : ℝ) ≤ 1 := div_le_self (by norm_num) hrR
    have heq : 1 / (4 * (r : ℝ)) = (1 / (r : ℝ)) / 4 := by ring
    rw [heq] at hh ⊢
    nlinarith only [hh, hrr, show 0 ≤ 1 / (r : ℝ) by positivity]
  calc
    _ ≤ _ := hold
    _ ≤ (1 + 1 / (r : ℝ)) * ((1 - 1 / (m : ℝ) ^ 2) *
        SingularSeries.singularSeriesTruncated N m) := by
      have hh := mul_le_mul_of_nonneg_right hcoef hSold.le
      nlinarith only [hh]
    _ ≤ _ := mul_le_mul_of_nonneg_left hstep' (by positivity)

#print axioms numerical_source_singular_lower

end ChenEffective
