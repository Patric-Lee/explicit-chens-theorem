import NumericalHatTail

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def perturbationCutoff (d p q : ℝ) : ℝ :=
  Real.exp (max 1 (2 * p^(d+1) / Real.log q))

theorem numerical_fixed_perturbation {d p q D : ℝ}
    (hp : 0 < p) (hq : 1 < q) (hD : perturbationCutoff d p q ≤ D) :
    perturbation D d 0 p < q := by
  have hDpos : 0 < D := (Real.exp_pos _).trans_le hD
  have hloglarge : max 1 (2*p^(d+1)/Real.log q) ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).mpr hD
  have hlog : 0 < Real.log D := zero_lt_one.trans_le ((le_max_left _ _).trans hloglarge)
  have hlogq := Real.log_pos hq
  have hpay : 2*p^(d+1) ≤ Real.log q * Real.log D :=
    by simpa only [mul_comm] using (div_le_iff₀ hlogq).mp ((le_max_right _ _).trans hloglarge)
  have hr : p^(d+1) / Real.log D ≤ Real.log q / 2 := by
    apply (div_le_iff₀ hlog).mpr
    nlinarith only [hpay]
  have hz : 0 ≤ p^d/Real.log D := div_nonneg (Real.rpow_nonneg hp.le _) hlog.le
  have hb : 0 < 1+p^d/Real.log D := by linarith only [hz]
  have hln : Real.log (1+p^d/Real.log D) ≤ p^d/Real.log D := by
    linarith only [Real.log_le_sub_one_of_pos hb]
  have he : p * Real.log (1+p^d/Real.log D) < Real.log q := by
    calc
      _ ≤ p*(p^d/Real.log D) := mul_le_mul_of_nonneg_left hln hp.le
      _ = p^(d+1) / Real.log D := by rw [Real.rpow_add hp, Real.rpow_one]; ring
      _ ≤ Real.log q/2 := hr
      _ < _ := by linarith only [hlogq]
  unfold perturbation
  simp only [add_zero]
  rw [Real.rpow_def_of_pos hb]
  exact (Real.exp_lt_exp.mpr (by simpa only [mul_comm] using he)).trans_eq
    (Real.exp_log (zero_lt_one.trans hq))

theorem numerical_source_weight {k σ : ℝ} (hk0 : 0 ≤ k) (hk : k < 1)
    (hσ : 2 / (1-k) ≤ σ) : k < (1-1/σ)^(1/2 : ℝ) := by
  have hg : 0 < 1-k := sub_pos.mpr hk
  have hσ0 : 0 < σ := (div_pos (by norm_num) hg).trans_le hσ
  have hinv : 1/σ ≤ (1-k)/2 := by
    apply (div_le_iff₀ hσ0).mpr
    have hh := (div_le_iff₀ hg).mp hσ
    nlinarith only [hh]
  have hb0 : 0 ≤ 1-1/σ := by linarith only [hinv, hk0]
  have hb1 : 1-1/σ ≤ 1 := by linarith only [show 0 ≤ 1/σ by positivity]
  exact (show k < 1-1/σ by linarith only [hinv, hk]).trans_le
    (Real.self_le_rpow_of_le_one hb0 hb1 (by norm_num))

#print axioms numerical_fixed_perturbation
#print axioms numerical_source_weight
end ChenEffective
