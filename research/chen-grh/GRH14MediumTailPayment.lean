import GRHLowerConditionedTail

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem conditioned_mass_absolute_cap {N q : ℕ} (hN : targetCutoff ≤ N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    |(jurkatRichertSourceConditionedBoundingSieve N q).totalMass| ≤ 20*(N:ℝ)/(q:ℝ) := by
  have hqp := (mem_filter.mp hq).2.1.two_le
  have hqR : (2:ℝ)≤q := by exact_mod_cast hqp
  have hqm : 0<(q:ℝ)-1 := by linarith only [hqR]
  have hq0 : (0:ℝ)<q := by linarith only [hqR]
  have hm := source_mass_absolute_cap hN
  change |(jurkatRichertSourceBoundingSieve N).totalMass/((q:ℝ)-1)| ≤ _
  rw [abs_div,abs_of_nonneg hqm.le]
  apply (div_le_div_of_nonneg_right hm hqm.le).trans
  apply (div_le_div_iff₀ hqm hq0).mpr
  nlinarith only [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hqR)]

theorem conditioned_tail_bound_at_target {N q D : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hD : 1≤D) (hDN : D≤N) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (preSieveTruncation N:ℝ) ≤
      (84:ℝ)*(N:ℝ)/(q:ℝ)*(log (N:ℝ))^2*exp (-(37/100000:ℝ)*log (N:ℝ)) := by
  have hL := target_log_lower hN
  have hm := conditioned_mass_absolute_cap hN hq
  rw [show (20:ℝ)*N/q=20*((N:ℝ)/(q:ℝ)) by ring] at hm
  have hdecay := truncation_tail_at_target hN
  have hlogD : log (D:ℝ)≤log (N:ℝ) :=
    log_le_log (by exact_mod_cast (show 0<D by omega)) (by exact_mod_cast hDN)
  have hpoly : (1+log (D:ℝ))^2≤4*(log (N:ℝ))^2 := by
    have hh := pow_le_pow_left₀
      (show 0≤1+log (D:ℝ) by have := log_nonneg (show (1:ℝ)≤D by exact_mod_cast hD); linarith)
      (show 1+log (D:ℝ)≤2*log (N:ℝ) by linarith only [hlogD,hL]) 2
    nlinarith only [hh]
  have he : exp (1700:ℝ)≤exp 2126 := exp_le_exp.mpr (by norm_num)
  have hnum : ((N:ℝ)/(q:ℝ))*exp 1700+
      |(jurkatRichertSourceConditionedBoundingSieve N q).totalMass| * exp 2126 ≤
        (21:ℝ)*((N:ℝ)/(q:ℝ))*exp 2126 := by
    have ha := mul_le_mul_of_nonneg_left he (show 0≤(N:ℝ)/(q:ℝ) by positivity)
    have hb := mul_le_mul_of_nonneg_right hm (exp_pos (2126:ℝ)).le
    nlinarith only [ha,hb]
  have hagg := GRH.conditioned_tail_moment_aggregate (lower_endpoint_parameters hN).1 hEven hq hD
    (C:=preSieveTruncation N)
  apply hagg.trans
  calc
    _ ≤ (21*((N:ℝ)/(q:ℝ))*exp 2126)*(4*(log (N:ℝ))^2)/sqrt (preSieveTruncation N:ℝ) := by
      apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
      exact mul_le_mul hnum hpoly (sq_nonneg _) (by positivity)
    _ = (84*((N:ℝ)/(q:ℝ))*(log (N:ℝ))^2)*(exp 2126/sqrt (preSieveTruncation N:ℝ)) := by ring
    _ ≤ (84*((N:ℝ)/(q:ℝ))*(log (N:ℝ))^2)*exp (-(37/100000:ℝ)*log (N:ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by ring

theorem medium_tail_paid_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (D : ℕ → ℕ) (hD : ∀ q ∈ jurkatRichertSourceMediumPrimes N, 1≤D q)
    (hDN : ∀ q ∈ jurkatRichertSourceMediumPrimes N, D q≤N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      let S := jurkatRichertSourceConditionedBoundingSieve N q
      let Q := smallSievePrimeProduct S 4000000
      let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D q)
      (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (preSieveTruncation N:ℝ)) ≤
      (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  let L := log (N:ℝ)
  have hL : (1000000:ℝ)≤L := target_log_lower hN
  have hLp : 0<L := by linarith only [hL]
  have hN1 : 1≤N := by have := (lower_endpoint_parameters hN).1; omega
  have hmass := numerical_totient_weight_mass 1 hN1 (jurkatRichertSourceMediumPrimes N)
    (by
      intro q hq
      exact mem_Icc.mpr ⟨(mem_filter.mp hq).2.1.one_lt.le,
        by have hh := mem_range.mp (mem_filter.mp hq).1; omega⟩)
    (fun q hq => (mem_filter.mp hq).2.1.squarefree)
  norm_num only [Nat.cast_one,one_pow,show 2*1=2 by norm_num] at hmass
  have hrec : (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q:ℝ)) ≤4*L^2 := by
    have hh : (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q:ℝ))≤(1+L)^2 := by
      apply le_trans _ hmass
      apply sum_le_sum
      intro q hq
      apply one_div_le_one_div_of_le
        (by exact_mod_cast Nat.totient_pos.mpr (mem_filter.mp hq).2.1.pos)
      exact_mod_cast Nat.totient_le q
    have hp := pow_le_pow_left₀ (by linarith only [hL] : (0:ℝ)≤1+L)
      (show 1+L≤2*L by linarith only [hL]) 2
    nlinarith only [hh,hp]
  have hp := truncated_polynomial_payment hL (A:=(336000000:ℝ)) (by norm_num)
    (α:=(37/100000:ℝ)) (by norm_num) (k:=6) (by norm_num)
  have hpay : (336:ℝ)*L^6*exp (-(37/100000:ℝ)*L) ≤ (1e-12:ℝ) := by nlinarith only [hp]
  calc
    _ ≤ ∑ q ∈ jurkatRichertSourceMediumPrimes N,
        (84:ℝ)*(N:ℝ)/(q:ℝ)*L^2*exp (-(37/100000:ℝ)*L) :=
      sum_le_sum (fun q hq => conditioned_tail_bound_at_target hN hEven hq (hD q hq) (hDN q hq))
    _ = (84*(N:ℝ)*L^2*exp (-(37/100000:ℝ)*L))*
        (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (84*(N:ℝ)*L^2*exp (-(37/100000:ℝ)*L))*(4*L^2) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = ((336:ℝ)*L^6*exp (-(37/100000:ℝ)*L))*((N:ℝ)/L^2) := by field_simp [hLp.ne'] <;> ring
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) := mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = _ := by ring

#print axioms medium_tail_paid_at_target
end ChenEffective.GRH14
