import BJSH30GoldbachProduct
import NumericalUniversalTail
import NumericalGenuineLiPointwise

noncomputable section
namespace ChenEffective.H30
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
attribute [local irreducible] logPowerCutoff mertensProductThreshold chenProductThreshold

def sourceUpperMassThreshold (r : ℕ) : ℕ :=
  max (chenProductThreshold r)
    (max ((2*r+1)^10) (max (3^(40*r+1)) (logPowerCutoff 2)))

theorem numerical_source_prime_product_upper {N r : ℕ} (hr : 0 < r)
    (hN : sourceUpperMassThreshold r ≤ N) :
    AnalyticNumberTheory.Mertens.primeProduct (jurkatRichertSourceZ N-1) ≤
      10*(1+1/(r : ℝ))^2*Real.exp (-Real.eulerMascheroniConstant)/Real.log (N : ℝ) := by
  let n := jurkatRichertSourceZ N-1
  have hM9 : 9 ≤ mertensProductThreshold r := by
    unfold mertensProductThreshold
    exact (logPowerCutoff_nine_le 2).trans (le_max_left _ _)
  have hn : mertensProductThreshold r ≤ n := numerical_source_cutoff (by omega)
    (by simpa only [chenProductThreshold] using (show chenProductThreshold r ≤ N from (le_max_left _ _).trans hN))
  have hnr : 2*r ≤ n := numerical_source_cutoff (by omega : 2 ≤ 2*r)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hn2 : 2 ≤ n := by omega
  have hL : 40*(r : ℝ) ≤ Real.log (N : ℝ) := by
    have hh := log_ge_power_three ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
    push_cast at hh
    linarith only [hh]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hNpos : 0 < N := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
    have h9 := (logPowerCutoff_nine_le 2).trans h
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hl0 : 0 < Real.log (N : ℝ) := by linarith only [hL,hr1]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hfloor : (N : ℝ)^(1/10 : ℝ) ≤ 2*(n : ℝ) := by
    have hh : (N : ℝ)^(1/10 : ℝ) < (n : ℝ)+1 := by
      simpa only [n,jurkatRichertSourceZ,Nat.add_sub_cancel] using Nat.lt_floor_add_one ((N : ℝ)^(1/10 : ℝ))
    linarith only [hh,hnR]
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hfloor
  rw [Real.log_rpow hN0,Real.log_mul (by norm_num) hn0.ne'] at hlog
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hcoef : Real.log (N : ℝ) ≤ 10*(1+1/(r : ℝ))*Real.log (n : ℝ) := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have he : (r : ℝ)*(1+1/(r : ℝ)) = (r : ℝ)+1 := by field_simp
    apply (mul_le_mul_iff_left₀ hr0).mp
    have hh := mul_le_mul_of_nonneg_left (show Real.log (N : ℝ)/10-1 ≤ Real.log (n : ℝ) by linarith only [hlog,hlog2])
      (show 0 ≤ (r : ℝ)+1 by positivity)
    rw [show 10*(1+1/(r : ℝ))*Real.log (n : ℝ)*(r : ℝ) = 10*((r : ℝ)*(1+1/(r : ℝ)))*Real.log (n : ℝ) by ring,he]
    nlinarith only [hh,hL,hr1]
  have hP0 := (AnalyticNumberTheory.Mertens.primeProduct_pos n).le
  have hupper := (abs_le.mp (numerical_mertens_product hr hn)).2
  have hmul := mul_le_mul_of_nonneg_left hcoef
    (show 0 ≤ AnalyticNumberTheory.Mertens.primeProduct n*Real.exp Real.eulerMascheroniConstant by positivity)
  have hExp : Real.exp Real.eulerMascheroniConstant*Real.exp (-Real.eulerMascheroniConstant)=1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hfirst : AnalyticNumberTheory.Mertens.primeProduct n*Real.log (N : ℝ)*Real.exp Real.eulerMascheroniConstant ≤
      10*(1+1/(r : ℝ))^2 := by
    have hh := mul_le_mul_of_nonneg_left (show
      AnalyticNumberTheory.Mertens.primeProduct n*Real.log (n : ℝ)*Real.exp Real.eulerMascheroniConstant ≤ 1+1/(r : ℝ) by linarith only [hupper])
      (show 0 ≤ 10*(1+1/(r : ℝ)) by positivity)
    nlinarith only [hh,hmul]
  apply (le_div_iff₀ hl0).mpr
  have hh := mul_le_mul_of_nonneg_right hfirst (Real.exp_pos (-Real.eulerMascheroniConstant)).le
  calc
    _ = (AnalyticNumberTheory.Mertens.primeProduct n*Real.log (N : ℝ)*Real.exp Real.eulerMascheroniConstant)*Real.exp (-Real.eulerMascheroniConstant) := by rw [mul_assoc, mul_assoc,hExp,mul_one]
    _ ≤ _ := hh

theorem numerical_liu_mass_upper {N r : ℕ} (hr : 0 < r)
    (hN : sourceUpperMassThreshold r ≤ N) :
    LiuWeight.liuLogarithmicIntegral (2/Real.log 2) N ≤ (1+1/(r : ℝ))*N/Real.log (N : ℝ) := by
  have hcut : logPowerCutoff 2 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have h9 := (logPowerCutoff_nine_le 2).trans hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL : 40*(r : ℝ) ≤ Real.log (N : ℝ) := by
    have hh := log_ge_power_three ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
    push_cast at hh
    linarith only [hh]
  have hh := (abs_le.mp (numerical_genuine_li_pointwise (x := (N : ℝ)) (by exact_mod_cast hcut))).2
  have heq : LiuWeight.liuLogarithmicIntegral (2/Real.log 2) N = LiuWeight.liuLogarithmicIntegral 2 N+(2/Real.log 2-2) := by
    unfold LiuWeight.liuLogarithmicIntegral
    ring
  have hconst : (2 : ℝ)/Real.log 2-2 ≤ 2 := by
    have h := Real.log_two_gt_d9
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hh : (2 : ℝ)/Real.log 2 ≤ 4 := (div_le_iff₀ hl2).mpr (by linarith only [h])
    linarith only [hh]
  have hscale : 1 ≤ (N : ℝ)/Real.log (N : ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl0)).mpr
    simpa only [one_mul] using (log_pow_le_sqrt_explicit hcut).trans (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))
  have hpay : 12/Real.log (N : ℝ) ≤ 1/(r : ℝ) := by
    apply (div_le_div_iff₀ hl0 (by exact_mod_cast hr : (0 : ℝ) < r)).mpr
    linarith only [hL]
  have hmul := mul_le_mul_of_nonneg_right hpay (div_nonneg hN0.le hl0.le)
  unfold LiuWeight.liuLogarithmicIntegralRemainder at hh
  rw [heq]
  simp only [div_eq_mul_inv,← inv_pow] at hh hscale hmul hconst ⊢
  nlinarith only [hh,hconst,hscale,hmul]

/-- Common density of every conditioned source, with a numerical relative budget. -/
theorem numerical_source_mass_upper {N r : ℕ} (hr : 0 < r)
    (hN : sourceUpperMassThreshold r ≤ N) (hEven : Even N) :
    (jurkatRichertSourceBoundingSieve N).totalMass*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ≤
      (jurkatRichertMertensFactor+300/(r : ℝ))*
        (SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  have hcut : logPowerCutoff 2 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have h9 := (logPowerCutoff_nine_le 2).trans hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let n := jurkatRichertSourceZ N-1
  have hn : 2*r ≤ n := numerical_source_cutoff (by omega : 2 ≤ 2*r)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hn2 : 2 ≤ n := by omega
  have hz3 : 3 ≤ jurkatRichertSourceZ N := by dsimp [n] at hn2; omega
  let t : ℝ := 1/(r : ℝ)
  let e := Real.exp (-Real.eulerMascheroniConstant)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := div_le_self (by norm_num) (by exact_mod_cast hr)
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [Real.one_half_lt_eulerMascheroniConstant])
  have hs := numerical_singular_truncated_upper (by omega : 0 < N) hr hn
  have htrunc : SingularSeries.singularSeriesTruncated N n ≤
      2*(1+t)*SingularSeries.liuSingularSeries N := by
    rw [SingularSeries.singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated N n hEven hn2]
    change _ ≤ 2*(1+1/(r : ℝ))*SingularSeries.liuSingularSeries N
    nlinarith only [hs]
  have hp := numerical_source_prime_product_upper hr hN
  have hprod : MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
      20*e*(1+t)^3*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) := by
    rw [MertensTheorem.sieveProduct_identity N _ (by omega : 2 ≤ jurkatRichertSourceZ N) hEven,MertensTheorem.primeProduct_eq_analyticNumberTheory]
    have hh := mul_le_mul hp htrunc (SingularSeries.singularSeriesTruncated_pos N n (by omega : 1 ≤ n)).le
      (show 0 ≤ 10*(1+1/(r : ℝ))^2*Real.exp (-Real.eulerMascheroniConstant)/Real.log (N : ℝ) by positivity)
    calc
      _ = AnalyticNumberTheory.Mertens.primeProduct (jurkatRichertSourceZ N-1)*SingularSeries.singularSeriesTruncated N n := by ring
      _ ≤ (10*(1+1/(r : ℝ))^2*Real.exp (-Real.eulerMascheroniConstant)/Real.log (N : ℝ))*
          (2*(1+t)*SingularSeries.liuSingularSeries N) := hh
      _ = _ := by dsimp [t,e]; ring
  have hli := numerical_liu_mass_upper hr hN
  have hV0 : 0 ≤ MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
    rw [← jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    exact prod_nonneg (fun p hp => sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le)
  have hh := mul_le_mul hli hprod hV0 (show 0 ≤ (1+1/(r : ℝ))*(N : ℝ)/Real.log (N : ℝ) by positivity)
  have h2 : t^2 ≤ t := by nlinarith only [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have h3 : t^3 ≤ t := by nlinarith only [mul_le_mul_of_nonneg_left h2 ht0,h2]
  have h4 : t^4 ≤ t := by nlinarith only [mul_le_mul_of_nonneg_left h3 ht0,h2]
  have hpoly : (1+t)^4 ≤ 1+15*t := by nlinarith only [h2,h3,h4]
  have hcoef : 20*e*(1+t)^4 ≤ jurkatRichertMertensFactor+300/(r : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 20*e by positivity)
    change _ ≤ 20*e+300/(r : ℝ)
    have he := mul_nonneg ht0 (sub_nonneg.mpr he1)
    rw [show (300 : ℝ)/(r : ℝ)=300*t by dsimp [t]; ring]
    nlinarith only [h,he]
  have hS0 := (SingularSeries.liuSingularSeries_pos N).le
  have hM : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 := by positivity
  have hpay := mul_le_mul_of_nonneg_right hcoef hM
  rw [jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
  change LiuWeight.liuLogarithmicIntegral (2/Real.log 2) N*_ ≤ _
  apply hh.trans
  calc
    _ = (20*e*(1+t)^4)*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by dsimp [t]; ring
    _ ≤ _ := hpay

#print axioms numerical_source_prime_product_upper
#print axioms numerical_liu_mass_upper
#print axioms numerical_source_mass_upper
end ChenEffective.H30
