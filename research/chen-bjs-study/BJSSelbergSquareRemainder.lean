import BJSSelbergSquareConvolution
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
namespace ChenEffective
open Real Finset ArithmeticFunction
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- An explicit square-root remainder, uniform for all positive even N and
all integral R >= 1. The N dependence is bounded by exp(1096) * N^(1/16);
there is no logarithmic factor in R and no implicit analytic constant. -/
theorem selberg_two_term_sqrt_remainder {N R : ℕ}
    (hEven : Even N) (hN : 0<N) (hR : 1≤R) :
    |selbergTwoTermResidual N R| ≤
      (20/sqrt R)*exp (1096+log (N:ℝ)/16) := by
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hsR : 0<sqrt (R:ℝ) := sqrt_pos.mpr hRp
  let a := selbergCriticalCorrection N
  let b := selbergSquareKernel
  let e : ℝ → ℝ := fun x => realHarmonic x-log x-eulerMascheroniConstant
  let F : ℕ+ × ℕ+ → ℝ := fun z =>
    |a z.1*b z.2*e ((R:ℝ)/((z.1:ℝ)*(z.2:ℝ)))|
  have hrow (m : ℕ+) : Summable (fun n : ℕ+ => F (m,n)) ∧
      (∑' n : ℕ+,F (m,n))≤(20/sqrt R)*selbergCriticalHalfWeight N m := by
    have hm0 : (0:ℝ)<(m:ℕ) := by exact_mod_cast m.pos
    have hsm : 0<sqrt ((m:ℕ):ℝ) := sqrt_pos.mpr hm0
    let g : ℕ → ℝ := fun n => |b n*e (((R:ℝ)/m)/n)|
    have hg : Summable g := (selberg_square_residual_mass (div_pos hRp hm0)).1
    have hgb := (selberg_square_residual_mass (div_pos hRp hm0)).2
    have hf (n : ℕ+) : F (m,n)=|a m| *g n := by
      dsimp only [F,g,e]
      rw [div_div]
      simp only [abs_mul,mul_assoc]
    have hs : Summable (fun n : ℕ+ => F (m,n)) := by
      simp_rw [hf]
      exact (hg.comp_injective PNat.coe_injective).mul_left _
    refine ⟨hs,?_⟩
    have hgp : (∑' n : ℕ+,g n)=∑' n : ℕ,g n := by
      have hh := tsum_zero_pnat_eq_tsum_nat hg
      simpa [g,b] using hh
    simp_rw [hf]
    rw [tsum_mul_left,hgp]
    calc
      _ ≤ |a m| *(20/sqrt ((R:ℝ)/m)) := mul_le_mul_of_nonneg_left hgb (abs_nonneg _)
      _ = _ := by
        rw [sqrt_div hRp.le]
        dsimp only [selbergCriticalHalfWeight,a]
        field_simp
  have hweights := (selberg_critical_half_mass hEven hN).1.comp_injective PNat.coe_injective
  have hrows : Summable (fun m : ℕ+ => ∑' n : ℕ+,F (m,n)) :=
    Summable.of_nonneg_of_le (fun m => tsum_nonneg (fun n => abs_nonneg _))
      (fun m => (hrow m).2) (hweights.mul_left _)
  have hF : Summable F := (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
    ⟨fun m => (hrow m).1,hrows⟩
  have hSigma : Summable (F ∘ sigmaAntidiagonalEquivProd) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hF
  have hfiber (n : ℕ+) : |selbergTwoTermResidualTerm N R n|≤
      ∑' c : (n:ℕ).divisorsAntidiagonal,(F ∘ sigmaAntidiagonalEquivProd) ⟨n,c⟩ := by
    have hcorr : liuSelbergCorrection N=a*b := by
      simpa only [a,b,mul_comm] using selberg_correction_square_convolution hEven
    have hval : selbergTwoTermResidualTerm N R n=
        ∑ c∈(n:ℕ).divisorsAntidiagonal,a c.1*b c.2*e ((R:ℝ)/n) := by
      simp only [selbergTwoTermResidualTerm,hcorr,ArithmeticFunction.mul_apply,sum_mul,e]
    rw [hval]
    apply (abs_sum_le_sum_abs _ _).trans_eq
    rw [tsum_fintype,Finset.univ_eq_attach]
    symm
    refine sum_bij (fun c _ => (c:ℕ×ℕ)) ?_ ?_ ?_ ?_
    · intro c hc; exact c.2
    · intro c hc d hd hcd; exact Subtype.ext hcd
    · intro c hc; exact ⟨⟨c,hc⟩,by simp,rfl⟩
    · intro c hc
      have hm : (c.1.1:ℝ)*c.1.2=(n:ℝ) := by
        exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp c.2).1
      change |a c.1.1*b c.1.2*e ((R:ℝ)/((c.1.1:ℝ)*c.1.2))|=_
      rw [hm]
  have hres := selberg_two_term_residual_summable hEven hN hR
  have hresabs : Summable (fun d => |selbergTwoTermResidualTerm N R d|) := by
    simpa only [Real.norm_eq_abs] using hres.norm
  have hpnat : (∑' d : ℕ+,|selbergTwoTermResidualTerm N R d|)=
      ∑' d : ℕ,|selbergTwoTermResidualTerm N R d| := by
    simpa [selbergTwoTermResidualTerm] using tsum_zero_pnat_eq_tsum_nat hresabs
  have hwp : (∑' d : ℕ+,selbergCriticalHalfWeight N d)=∑' d,selbergCriticalHalfWeight N d := by
    simpa [selbergCriticalHalfWeight] using tsum_zero_pnat_eq_tsum_nat (selberg_critical_half_mass hEven hN).1
  calc
    _ ≤ ∑' d : ℕ,|selbergTwoTermResidualTerm N R d| := by
      simpa only [selbergTwoTermResidual,Real.norm_eq_abs] using norm_tsum_le_tsum_norm
        (f:=selbergTwoTermResidualTerm N R) (by simpa only [Real.norm_eq_abs] using hresabs)
    _ = ∑' d : ℕ+,|selbergTwoTermResidualTerm N R d| := hpnat.symm
    _ ≤ ∑' n : ℕ+,∑' c : (n:ℕ).divisorsAntidiagonal,
        (F ∘ sigmaAntidiagonalEquivProd) ⟨n,c⟩ :=
      (hresabs.comp_injective PNat.coe_injective).tsum_le_tsum hfiber hSigma.sigma
    _ = ∑' z : ℕ+ × ℕ+,F z := by rw [← hSigma.tsum_sigma]; exact sigmaAntidiagonalEquivProd.tsum_eq F
    _ = ∑' m : ℕ+,∑' n : ℕ+,F (m,n) := hF.tsum_prod
    _ ≤ ∑' m : ℕ+,(20/sqrt R)*selbergCriticalHalfWeight N m :=
      hrows.tsum_le_tsum (fun m => (hrow m).2) (hweights.mul_left _)
    _ = (20/sqrt R)*(∑' m,selbergCriticalHalfWeight N m) := by rw [tsum_mul_left,hwp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (selberg_critical_half_mass hEven hN).2 (by positivity)

/-- The actual squarefree Selberg denominator has the two terms
(log R + gamma + sum_{p|N} log(p)/(p-1))/(2*S(N)), with an explicit remainder.
This theorem is unconditional and does not use the local Dirichlet axiom. -/
theorem selberg_uniform_two_term_expansion {N R : ℕ}
    (hEven : Even N) (hN : 0<N) (hR : 1≤R) :
    |(∑ n∈Icc 1 R,liuSelbergArithmetic N n)-
      (log (R:ℝ)+selbergSpecializedSecondary N)/(2*liuSingularSeries N)| ≤
      (20/sqrt R)*exp (1096+log (N:ℝ)/16) := by
  rw [selberg_two_term_identity hEven hN hR,add_sub_cancel_left]
  exact selberg_two_term_sqrt_remainder hEven hN hR

#print axioms selberg_uniform_two_term_expansion
end ChenEffective
