import GRHLowerRemainderAggregate
import GRH14LowerGeometry

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem source_mass_absolute_cap {N : ℕ} (hN : targetCutoff ≤ N) :
    |(jurkatRichertSourceBoundingSieve N).totalMass| ≤ 10*(N:ℝ) := by
  have hlarge := (lower_endpoint_parameters hN).1
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hh := LiuWeight.liuLogarithmicIntegral_abs_le (2/log 2)
    (show (2:ℝ)≤N by exact_mod_cast (show 2≤N by omega))
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hκ : (2:ℝ)/log 2 ≤ 4 := (div_le_iff₀ hl2).mpr (by linarith only [log_two_gt_d9])
  have hκ0 : 0≤(2:ℝ)/log 2 := by positivity
  have hc : LiuWeight.liuLogarithmicIntegralUpperConstant (2/log 2) ≤ 10 := by
    unfold LiuWeight.liuLogarithmicIntegralUpperConstant
    rw [abs_of_nonneg hκ0]
    linarith only [hκ]
  apply hh.trans
  apply (div_le_iff₀ hl).mpr
  have hh := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)
  nlinarith only [hh,hL,mul_nonneg (Nat.cast_nonneg N) (show 0≤log (N:ℝ)-1 by linarith only [hL])]

theorem source_tail_paid_at_target {N D : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) (hD : 1≤D) (hDN : D≤N) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/
        sqrt (preSieveTruncation N:ℝ) ≤ (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  let L := log (N:ℝ)
  have hL : (1000000:ℝ)≤L := target_log_lower hN
  have hLp : 0<L := by linarith only [hL]
  have hm := source_mass_absolute_cap hN
  have hdecay := truncation_tail_at_target hN
  have hlogD : log (D:ℝ)≤L :=
    log_le_log (by exact_mod_cast (show 0<D by omega)) (by exact_mod_cast hDN)
  have hlogD0 : 0≤log (D:ℝ) := log_nonneg (by exact_mod_cast hD)
  have hpoly : (1+log (D:ℝ))^2 ≤ 4*L^2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+log (D:ℝ))
      (show 1+log (D:ℝ)≤2*L by linarith only [hlogD,hL]) 2
    nlinarith only [hh]
  have he : exp (1700:ℝ)≤exp 2126 := exp_le_exp.mpr (by norm_num)
  have hnum : (N:ℝ)*exp 1700+|(jurkatRichertSourceBoundingSieve N).totalMass| * exp 2126 ≤
      11*(N:ℝ)*exp 2126 := by
    have ha := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)
    have hb := mul_le_mul_of_nonneg_right hm (exp_pos (2126:ℝ)).le
    nlinarith only [ha,hb]
  have hpay := truncated_polynomial_payment hL (A:=(44000000:ℝ)) (by norm_num)
    (α:=(37/100000:ℝ)) (by norm_num) (k:=4) (by norm_num)
  have hpaySmall : (44:ℝ)*L^4*exp (-(37/100000:ℝ)*L) ≤ (1e-12:ℝ) := by
    nlinarith only [hpay]
  have hagg := GRH.source_tail_moment_aggregate (lower_endpoint_parameters hN).1 hEven hD
    (C:=preSieveTruncation N)
  apply hagg.trans
  calc
    _ ≤ (11*(N:ℝ)*exp 2126)*(4*L^2)/sqrt (preSieveTruncation N:ℝ) := by
      apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
      exact mul_le_mul hnum hpoly (sq_nonneg _) (by positivity)
    _ = (44*(N:ℝ)*L^2)*(exp 2126/sqrt (preSieveTruncation N:ℝ)) := by ring
    _ ≤ (44*(N:ℝ)*L^2)*exp (-(37/100000:ℝ)*L) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = ((44:ℝ)*L^4*exp (-(37/100000:ℝ)*L))*((N:ℝ)/L^2) := by
      field_simp [hLp.ne']
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) := mul_le_mul_of_nonneg_right hpaySmall (by positivity)
    _ = _ := by ring

#print axioms source_tail_paid_at_target
end ChenEffective.GRH14
