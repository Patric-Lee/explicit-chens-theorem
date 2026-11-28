import DusartPort.Application
import MathlibNt.SieveTheory.Arithmetic.PrimeReciprocalLogScale
import MathlibNt.SieveTheory.Switching.SourceSieve

/-! Retained power errors for the finite-band Chen experiment.
These are analytic theorems, not the unproved sharp-distribution or
truncation hypotheses in the numerical budget. -/
noncomputable section
namespace ChenEffective.H10Band
open Real Finset
open MathlibNt.SieveTheory PrimeReciprocalLogScale SwitchingPrinciple
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def prefixError (ell : ℝ) : ℝ :=
  ((51/4:ℝ)/ell+12/ell^2)*exp (-ell/16)

def intervalError (L : ℝ) : ℝ := 2*prefixError (L/10)

theorem prefixError_nonneg {ell : ℝ} (h : 0<ell) : 0≤prefixError ell := by
  unfold prefixError
  positivity

theorem prefixError_antitone {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    prefixError b≤prefixError a := by
  have hs : a^2≤b^2 := by gcongr
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤51/4) ha hab
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤12) (sq_pos_of_pos ha) hs
  have he : exp (-b/16)≤exp (-a/16) := exp_le_exp.mpr (by linarith only [hab])
  exact mul_le_mul (add_le_add h1 h2) he (exp_pos _).le (by positivity)

theorem retained_prefix {x : ℝ} (hx : (3:ℝ)^120≤x) :
    |primeReciprocalSum ⌊x⌋₊-(log (log x)+mertensSecondConstant)|≤
      prefixError (log x) := by
  have hx9 : (9:ℝ)≤x := (by norm_num : (9:ℝ)≤3^120).trans hx
  have hx0 : 0<x := lt_of_lt_of_le (by norm_num : (0:ℝ)<9) hx9
  have hl : 0<log x := log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ)<9) hx9)
  have hh := bjsStudy_mertens_of_theta_target hx9
    (fun _t ht => Dusart.numerical_theta_target (hx.trans ht))
  apply hh.trans_eq
  have hr : x^(-1/16:ℝ)=exp (-log x/16) := by
    rw [rpow_def_of_pos hx0]
    congr 1
    ring
  rw [hr]
  unfold prefixError
  field_simp
  <;> ring

theorem log_scale_positive {N : ℕ} (hL : (2400:ℝ)≤log (N:ℝ)) :
    1<N ∧ (0:ℝ)<N ∧ 0<log (N:ℝ) := by
  have hn : 0<N := by
    by_contra h
    have hz : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hh := log_le_sub_one_of_pos hnR
  exact ⟨by exact_mod_cast (by linarith only [hh,hL] : (1:ℝ)<N),hnR,by linarith only [hL]⟩

theorem retained_scaled_prefix {N : ℕ} (hL : (2400:ℝ)≤log (N:ℝ))
    {a : ℝ} (ha : 1/10≤a) :
    |MertensTheorem.primeReciprocalSum (rpowFloor N a)-
      (log a+log (log (N:ℝ))+mertensSecondConstant)|≤
      prefixError (log (N:ℝ)/10) := by
  obtain ⟨hN,hn,hlog⟩ := log_scale_positive hL
  have ha0 : 0<a := by linarith only [ha]
  have hmul : log (N:ℝ)/10≤a*log (N:ℝ) := by nlinarith only [ha,hlog]
  have hx : (3:ℝ)^120≤(N:ℝ)^a := by
    apply (log_le_log_iff (by positivity) (rpow_pos_of_pos hn _)).mp
    rw [log_pow,log_rpow hn]
    have hl3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num only [Nat.cast_ofNat] at *
    linarith only [hl3,hmul,hL]
  have hh := retained_prefix hx
  rw [log_rpow hn,log_mul ha0.ne' hlog.ne'] at hh
  rw [MertensTheorem.primeReciprocalSum_eq_analyticNumberTheory,rpowFloor]
  exact hh.trans (prefixError_antitone (by positivity) hmul)

theorem retained_interval {N : ℕ} (hL : (2400:ℝ)≤log (N:ℝ))
    {a b : ℝ} (ha : 1/10≤a) (hab : a≤b) :
    |primeReciprocalLogInterval N a b-log (b/a)|≤ intervalError (log (N:ℝ)) := by
  obtain ⟨hN,hn,hlog⟩ := log_scale_positive hL
  have ha0 : 0<a := by linarith only [ha]
  have hb0 : 0<b := ha0.trans_le hab
  have hpa := retained_scaled_prefix hL ha
  have hpb := retained_scaled_prefix hL (ha.trans hab)
  rw [primeReciprocalLogInterval_eq_sub N (by omega) hab]
  have hid :
      MertensTheorem.primeReciprocalSum (rpowFloor N b)-
        MertensTheorem.primeReciprocalSum (rpowFloor N a)-log (b/a) =
      (MertensTheorem.primeReciprocalSum (rpowFloor N b)-
        (log b+log (log (N:ℝ))+mertensSecondConstant))-
      (MertensTheorem.primeReciprocalSum (rpowFloor N a)-
        (log a+log (log (N:ℝ))+mertensSecondConstant)) := by
    rw [log_div hb0.ne' ha0.ne']
    ring
  rw [hid]
  exact (abs_sub _ _).trans ((add_le_add hpb hpa).trans_eq (by unfold intervalError; ring))

theorem intervalError_closed {L : ℝ} (hL : 0<L) :
    intervalError L=(255/L+2400/L^2)*exp (-L/160) := by
  unfold intervalError prefixError
  have he : -(L/10)/16=-L/160 := by ring
  rw [he]
  field_simp
  <;> ring

theorem intervalError_antitone {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    intervalError B≤ intervalError A := by
  unfold intervalError
  exact mul_le_mul_of_nonneg_left
    (prefixError_antitone (by positivity) (by linarith only [hAB])) (by norm_num)

theorem actual_medium_prime_mass {N : ℕ} (hL : (2400:ℝ)≤log (N:ℝ)) :
    (∑ q∈jurkatRichertSourceMediumPrimes N,1/(q:ℝ))≤
      log (10/3:ℝ)+intervalError (log (N:ℝ)) := by
  obtain ⟨hN,hn,hlog⟩ := log_scale_positive hL
  have hpow : (N:ℝ)^(1/3:ℝ)≤N := by
    have hh := rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1≤N by omega) : (1:ℝ)≤N)
      (by norm_num : (1/3:ℝ)≤1)
    simpa only [rpow_one] using hh
  have hcarrier : jurkatRichertSourceMediumPrimes N =
      ((range (rpowFloor N (1/3:ℝ)+1)).filter (fun p : ℕ =>
        p.Prime ∧ (N:ℝ)^(1/10:ℝ)<p ∧ (p:ℝ)≤(N:ℝ)^(1/3:ℝ))) := by
    ext q
    simp only [jurkatRichertSourceMediumPrimes,mem_filter,mem_range]
    constructor
    · rintro ⟨hq,hprime,hlo,hhi⟩
      have hf : q≤⌊(N:ℝ)^(1/3:ℝ)⌋₊ := Nat.le_floor hhi
      exact ⟨by unfold rpowFloor; omega,hprime,hlo,hhi⟩
    · rintro ⟨hq,hprime,hlo,hhi⟩
      have hqN : q≤N := by exact_mod_cast hhi.trans hpow
      exact ⟨by omega,hprime,hlo,hhi⟩
  have hh := (abs_le.mp (retained_interval hL (a:=1/10) (b:=1/3) (by norm_num) (by norm_num))).2
  rw [hcarrier]
  change primeReciprocalLogInterval N (1/10) (1/3)≤_
  norm_num only [show (1/3:ℝ)/(1/10)=10/3 by norm_num] at hh
  linarith only [hh]

#print axioms retained_prefix
#print axioms retained_scaled_prefix
#print axioms retained_interval
#print axioms actual_medium_prime_mass

theorem old_cutoff_log_cap : log ((3^145000:ℕ):ℝ)≤159500 := by
  have he := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤11/10) 7
  norm_num [Finset.sum_range_succ] at he
  have h3 : (3:ℝ)<exp (11/10:ℝ) := by linarith only [he]
  have hh := log_lt_log (by norm_num : (0:ℝ)<3) h3
  rw [log_exp] at hh
  rw [Nat.cast_pow,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hh]

theorem exp_ten_lower : (22026:ℝ)≤exp 10 := by
  have he : (2718281828/1000000000:ℝ)≤exp 1 := by linarith only [exp_one_gt_d9]
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718281828/1000000000) he 10
  rw [←exp_nat_mul] at hh
  norm_num at hh ⊢
  linarith only [hh]

theorem log_lower_of_double_exp_ten {N : ℕ}
    (hN : exp (exp (10:ℝ))≤N) : (22026:ℝ)≤log (N:ℝ) := by
  have hh := log_le_log (exp_pos _) hN
  rw [log_exp] at hh
  exact exp_ten_lower.trans hh

#print axioms old_cutoff_log_cap
#print axioms log_lower_of_double_exp_ten
end ChenEffective.H10Band
end
