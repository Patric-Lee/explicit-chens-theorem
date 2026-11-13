import BJSSelbergCriticalKernel
import BJSSquareHarmonicMass
import Mathlib.Data.Nat.Factorization.Induction

noncomputable section
namespace ChenEffective
open Real Finset ArithmeticFunction
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def selbergSquareLocal (p k : ℕ) : ℝ :=
  if k=0 then 1 else if k=2 then -1/(p:ℝ)^2 else 0

def selbergSquareKernel : ArithmeticFunction ℝ := primePowerExtension selbergSquareLocal

theorem selberg_square_multiplicative : selbergSquareKernel.IsMultiplicative :=
  primePowerExtension_multiplicative _

theorem selberg_square_prime_pow {p k : ℕ} (hp : p.Prime) :
    selbergSquareKernel (p^k)=selbergSquareLocal p k :=
  primePowerExtension_prime_pow _ (by intro p; simp [selbergSquareLocal]) hp

theorem selberg_square_support (n : ℕ) :
    selbergSquareKernel n≠0 → ∃ a : ℕ,n=a^2 := by
  induction n using Nat.recOnPrimePow with
  | zero => simp
  | one => intro _; exact ⟨1,by norm_num⟩
  | prime_pow_mul a p k hp hpa hk ih =>
    rw [selberg_square_multiplicative.map_mul_of_coprime
      ((hp.coprime_iff_not_dvd.mpr hpa).pow_left k),selberg_square_prime_pow hp]
    intro hh
    have hk2 : k=2 := by
      by_contra hne
      simp [selbergSquareLocal,hk.ne',hne] at hh
    obtain ⟨b,hb⟩ := ih (right_ne_zero_of_mul hh)
    exact ⟨p*b,by rw [hk2,hb,mul_pow]⟩

theorem selberg_square_norm (n : ℕ) : |selbergSquareKernel n|≤1/(n:ℝ) := by
  induction n using Nat.recOnPrimePow with
  | zero => simp
  | one => simp [selberg_square_multiplicative.1]
  | prime_pow_mul a p k hp hpa hk ih =>
    rw [selberg_square_multiplicative.map_mul_of_coprime
      ((hp.coprime_iff_not_dvd.mpr hpa).pow_left k),abs_mul,Nat.cast_mul]
    have hl : |selbergSquareKernel (p^k)|≤1/((p^k:ℕ):ℝ) := by
      rw [selberg_square_prime_pow hp]
      by_cases hk2 : k=2
      · subst k
        simp [selbergSquareLocal,abs_div,abs_of_nonneg (sq_nonneg (p:ℝ))]
      · simp [selbergSquareLocal,hk.ne',hk2]
    exact (mul_le_mul hl ih (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem selberg_square_residual_mass {x : ℝ} (hx : 0<x) :
    Summable (fun d : ℕ => |selbergSquareKernel d*
      (realHarmonic (x/d)-log (x/d)-eulerMascheroniConstant)|) ∧
    (∑' d : ℕ,|selbergSquareKernel d*
      (realHarmonic (x/d)-log (x/d)-eulerMascheroniConstant)|) ≤ 20/sqrt x := by
  let f : ℕ → ℝ := fun d => |selbergSquareKernel d*
    (realHarmonic (x/d)-log (x/d)-eulerMascheroniConstant)|
  have hinj : Function.Injective (fun a : ℕ => a^2) := by
    intro a b hab
    nlinarith only [hab]
  have hcomp (a : ℕ) : f (a^2)≤|squareHarmonicResidual x a| := by
    by_cases ha : a=0
    · subst a; simp [f,squareHarmonicResidual]
    have haR : (0:ℝ)<a := by exact_mod_cast Nat.pos_of_ne_zero ha
    have hlog : log (x/((a^2:ℕ):ℝ))=log x-2*log (a:ℝ) := by
      rw [Nat.cast_pow,log_div hx.ne' (pow_ne_zero _ haR.ne'),log_pow]
      norm_num
    dsimp only [f,squareHarmonicResidual]
    rw [abs_mul,hlog,abs_div,abs_of_pos (sq_pos_of_pos haR)]
    have hh := mul_le_mul_of_nonneg_right (selberg_square_norm (a^2))
      (abs_nonneg (realHarmonic (x/((a^2:ℕ):ℝ))-(log x-2*log (a:ℝ)+eulerMascheroniConstant)))
    simpa only [Nat.cast_pow,sub_sub,one_div,mul_comm,div_eq_mul_inv,mul_one] using hh
  have hcomps : Summable (fun a => f (a^2)) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hcomp (square_harmonic_mass hx).1
  have hsupport : Function.support f ⊆ Set.range (fun a : ℕ => a^2) := by
    intro d hd
    have hne : selbergSquareKernel d≠0 := by
      intro he; exact hd (by simp [f,he])
    obtain ⟨a,ha⟩ := selberg_square_support d hne
    exact ⟨a,ha.symm⟩
  have hz : ∀ d,d∉Set.range (fun a : ℕ => a^2) → f d=0 := by
    intro d hd
    by_contra hn
    exact hd (hsupport hn)
  have hs : Summable f := (hinj.summable_iff hz).mp hcomps
  refine ⟨hs,?_⟩
  calc
    _ = ∑' a,f (a^2) := (hinj.tsum_eq hsupport).symm
    _ ≤ ∑' a,|squareHarmonicResidual x a| := hcomps.tsum_le_tsum hcomp (square_harmonic_mass hx).1
    _ ≤ 20/sqrt x := (square_harmonic_mass hx).2

end ChenEffective
