import BJSSelbergSpecialization
import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt

/-! The signed logarithmic moment is computed by an Euler product in the
dual numbers. This retains cancellation before any absolute error bound. -/
noncomputable section
namespace ChenEffective
open Real Finset Filter
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def selbergJet (N n : ℕ) : TrivSqZeroExt ℝ ℝ :=
  ⟨liuSelbergCorrection N n,liuSelbergCorrection N n*log (n:ℝ)⟩

def selbergJetFunction (N : ℕ) : ArithmeticFunction (TrivSqZeroExt ℝ ℝ) :=
  ⟨selbergJet N,by ext <;> simp [selbergJet]⟩

theorem selberg_jet_multiplicative (N : ℕ) : (selbergJetFunction N).IsMultiplicative := by
  constructor
  · ext <;> simp [selbergJetFunction,selbergJet,liuSelbergCorrection_one]
  · intro m n hmn
    by_cases hm : m=0
    · subst m; simp [selbergJetFunction,selbergJet]
    by_cases hn : n=0
    · subst n; simp [selbergJetFunction,selbergJet]
    have hlog := log_mul (show (m:ℝ)≠0 by exact_mod_cast hm)
      (show (n:ℝ)≠0 by exact_mod_cast hn)
    ext <;> simp [selbergJetFunction,selbergJet,
      (liuSelbergCorrection_isMultiplicative N).map_mul_of_coprime hmn,
      Nat.cast_mul,hlog,TrivSqZeroExt.snd_mul]
    ring

theorem selberg_jet_summable {N : ℕ} (hEven : Even N) (hN : 0<N) :
    Summable (fun n => ‖selbergJet N n‖) := by
  have h := (summable_abs_liuSelbergCorrection hEven hN).add
    (summable_abs_liuSelbergCorrection_mul_log_nat hEven hN)
  convert h using 1
  ext n
  simp [TrivSqZeroExt.norm_def,selbergJet,Real.norm_eq_abs,
    abs_of_nonneg (log_natCast_nonneg n)]

def selbergJetRatio (N p : ℕ) : ℝ := if p∣N then -log (p:ℝ)/((p:ℝ)-1) else 0

theorem selberg_jet_local {N p : ℕ} (hEven : Even N) (hp : p.Prime) :
    (∑' e, selbergJet N (p^e)).snd =
      (∑' e, selbergJet N (p^e)).fst * selbergJetRatio N p := by
  have hsum : (∑' e, selbergJet N (p^e)) = ∑ e ∈ range 3, selbergJet N (p^e) := by
    apply tsum_eq_sum
    intro e he
    have he3 : 3≤e := by simpa using he
    unfold selbergJet
    by_cases hpd : p∣N
    · rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpd (by omega)]
      ext <;> simp
    · rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hpd he3]
      ext <;> simp
  rw [hsum]
  by_cases hpd : p∣N
  · simp only [Finset.sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one]
    change (liuSelbergCorrection N 1*log (1:ℕ)+liuSelbergCorrection N p*log (p:ℝ)+
      liuSelbergCorrection N (p^2)*log (p^2:ℕ)) =
      (liuSelbergCorrection N 1+liuSelbergCorrection N p+liuSelbergCorrection N (p^2))*selbergJetRatio N p
    simp only [liuSelbergCorrection_one,
      liuSelbergCorrection_prime_of_dvd hp hpd,
      liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpd (by norm_num : 2≤2),
      Nat.cast_one,log_one,mul_zero,zero_mul,zero_add,add_zero]
    unfold selbergJetRatio
    rw [if_pos hpd]
    have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
    have hp1 : (p:ℝ)-1≠0 := by
      have : (2:ℝ)≤p := by exact_mod_cast hp.two_le
      linarith
    field_simp
    ring
  · simp only [Finset.sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one]
    change (liuSelbergCorrection N 1*log (1:ℕ)+liuSelbergCorrection N p*log (p:ℝ)+
      liuSelbergCorrection N (p^2)*log (p^2:ℕ)) =
      (liuSelbergCorrection N 1+liuSelbergCorrection N p+liuSelbergCorrection N (p^2))*selbergJetRatio N p
    simp only [liuSelbergCorrection_one,
      liuSelbergCorrection_prime_of_not_dvd hEven hp hpd,
      liuSelbergCorrection_prime_sq_of_not_dvd hp hpd,
      Nat.cast_one,log_one,mul_zero,zero_add,
      selbergJetRatio,if_neg hpd,Nat.cast_pow,log_pow]
    norm_num only [Nat.cast_ofNat]
    ring

theorem selberg_jet_product (N : ℕ) (s : Finset ℕ)
    (hs : ∀ p∈s, p.Prime) (hEven : Even N) :
    (∏ p∈s, ∑' e, selbergJet N (p^e)).snd =
      (∏ p∈s, ∑' e, selbergJet N (p^e)).fst * ∑ p∈s,selbergJetRatio N p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha,sum_insert ha]
    rw [TrivSqZeroExt.snd_mul,TrivSqZeroExt.fst_mul,
      selberg_jet_local hEven (hs a (mem_insert_self _ _)),
      ih (fun p hp => hs p (mem_insert_of_mem hp))]
    change _*_+_*_= _
    simp only [MulOpposite.unop_op]
    ring

theorem selberg_jet_ratio_primesBelow {N z : ℕ} (hN : 0<N) (hz : N<z) :
    (∑ p∈z.primesBelow,selbergJetRatio N p) =
      -(∑ p∈N.primeFactors,log (p:ℝ)/((p:ℝ)-1)) := by
  have hsub : N.primeFactors ⊆ z.primesBelow := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpN : p≤N := Nat.le_of_dvd hN (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.mem_primesBelow.mpr ⟨hpN.trans_lt hz,hprime⟩
  rw [← Finset.sum_neg_distrib]
  calc
    _ = ∑ p∈N.primeFactors,selbergJetRatio N p := by
      symm
      apply Finset.sum_subset hsub
      intro p hp hpN
      unfold selbergJetRatio
      apply if_neg
      intro hd
      exact hpN (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesBelow.mp hp).2,hd,hN.ne'⟩)
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      simp only [selbergJetRatio,if_pos (Nat.dvd_of_mem_primeFactors hp),neg_div]

theorem selberg_signed_log_moment {N : ℕ} (hEven : Even N) (hN : 0<N) :
    (∑' d, liuSelbergCorrection N d*log (d:ℝ)) =
      -(1/(2*liuSingularSeries N))*
        ∑ p∈N.primeFactors,log (p:ℝ)/((p:ℝ)-1) := by
  have hsum := selberg_jet_summable hEven hN
  have heuler := (selberg_jet_multiplicative N).eulerProduct hsum
  have hfst := TrivSqZeroExt.continuous_fst.tendsto _ |>.comp heuler
  have hsnd := TrivSqZeroExt.continuous_snd.tendsto _ |>.comp heuler
  have hsum' : Summable (selbergJet N) := hsum.of_norm
  have hfm := (TrivSqZeroExt.hasSum_fst ℝ hsum'.hasSum).tsum_eq
  have hsm := (TrivSqZeroExt.hasSum_snd ℝ hsum'.hasSum).tsum_eq
  change (∑' n,liuSelbergCorrection N n)=(∑' n,selbergJet N n).fst at hfm
  change (∑' n,liuSelbergCorrection N n*log (n:ℝ))=(∑' n,selbergJet N n).snd at hsm
  rw [tsum_liuSelbergCorrection hEven hN] at hfm
  have hlimit := hfst.mul_const (-(∑ p∈N.primeFactors,log (p:ℝ)/((p:ℝ)-1)))
  have heq : ∀ᶠ z : ℕ in atTop,
      (∏ p∈z.primesBelow,∑' e,selbergJet N (p^e)).snd =
      (∏ p∈z.primesBelow,∑' e,selbergJet N (p^e)).fst *
        (-(∑ p∈N.primeFactors,log (p:ℝ)/((p:ℝ)-1))) := by
    filter_upwards [eventually_gt_atTop N] with z hz
    rw [selberg_jet_product N z.primesBelow
      (fun _ hp => Nat.prime_of_mem_primesBelow hp) hEven,
      selberg_jet_ratio_primesBelow hN hz]
  have heq' : (fun z : ℕ =>
      (∏ p∈z.primesBelow,∑' e,selbergJet N (p^e)).fst *
        (-(∑ p∈N.primeFactors,log (p:ℝ)/((p:ℝ)-1)))) =ᶠ[atTop]
      (fun z => (∏ p∈z.primesBelow,∑' e,selbergJet N (p^e)).snd) := by
    filter_upwards [heq] with z hz
    exact hz.symm
  have hsame := tendsto_nhds_unique hsnd (hlimit.congr' heq')
  change (∑' n,selbergJet N n).snd =
    (∑' n,selbergJet N n).fst * (-(∑ p∈N.primeFactors,log (p:ℝ)/((p:ℝ)-1))) at hsame
  rw [← hsm,← hfm] at hsame
  nlinarith only [hsame]

#print axioms selberg_signed_log_moment
end ChenEffective
