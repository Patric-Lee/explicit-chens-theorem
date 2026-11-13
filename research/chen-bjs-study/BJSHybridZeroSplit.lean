import BJSHybridZeroReindex
import BJSHybridPrimePowers

noncomputable section
namespace ChenEffective.HybridProduct
open Complex Complex.Hadamard Set Finset
open DusartPort.Lab.ExplicitPsi1
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

def psiKernel (x : ℝ) (p : DusartXiZero) : ℂ :=
  (x:ℂ)*xiKernel x p
def headComplex (H : Finset DusartXiZero) (x : ℝ) : ℂ := ∑ p ∈ H, psiKernel x p
def tailComplex (H : Finset DusartXiZero) (x : ℝ) : ℂ :=
  ∑' p : {p : DusartXiZero // p ∉ H}, psiKernel x p
def headReal (H : Finset DusartXiZero) (x : ℝ) : ℝ := (headComplex H x).re
def tailReal (H : Finset DusartXiZero) (x : ℝ) : ℝ := (tailComplex H x).re

theorem summable_psi_kernel {x : ℝ} (hx : 1 ≤ x) : Summable (psiKernel x) :=
  (summable_xi_kernel hx).mul_left (x:ℂ)

theorem actual_zero_sum_split (H : Finset DusartXiZero) {x : ℝ} (hx : 1 ≤ x) :
    Dusart.Zreal x=headReal H x+tailReal H x := by
  have hh := (summable_psi_kernel hx).sum_add_tsum_subtype_compl H
  have he : (∑' p,psiKernel x p)=(x:ℂ)*∑' ρ : Zall,zterm x ρ := by
    change (∑' p,(x:ℂ)*xiKernel x p) = _
    rw [tsum_mul_left,xi_kernel_tsum_eq hx]
  rw [he] at hh
  have hr := congrArg Complex.re hh
  simpa only [Complex.add_re,headComplex,headReal,tailComplex,tailReal,Dusart.Zreal] using hr.symm

theorem psi_kernel_norm {x : ℝ} (hx : 1 ≤ x) (p : DusartXiZero) :
    ‖psiKernel x p‖ ≤ x^(15/8:ℝ)*absoluteXiWeight p := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  unfold psiKernel
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
  have hh := mul_le_mul_of_nonneg_left (xi_kernel_norm hx p) hx0.le
  have he : x*x^(7/8:ℝ)=x^(15/8:ℝ) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    norm_num
  simpa only [← mul_assoc,he] using hh

theorem tail_bound (H : Finset DusartXiZero) {x W : ℝ} (hx : 1 ≤ x)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |tailReal H x| ≤ W*x^(15/8:ℝ) := by
  have hw : Summable (fun p : {p : DusartXiZero // p ∉ H} => absoluteXiWeight p) :=
    dusart_xi_zero_absolute_moment.1.subtype _
  have hs : Summable (fun p : {p : DusartXiZero // p ∉ H} => psiKernel x p) :=
    (summable_psi_kernel hx).subtype _
  have hn := hs.norm.tsum_le_tsum (fun p : {p : DusartXiZero // p ∉ H} => psi_kernel_norm hx p.1)
    (hw.mul_left (x^(15/8:ℝ)))
  rw [tsum_mul_left] at hn
  have htNorm := norm_tsum_le_tsum_norm (f:=fun p : {p : DusartXiZero // p ∉ H} => psiKernel x p.1) hs.norm
  calc
    _ ≤ ‖tailComplex H x‖ := Complex.abs_re_le_norm (tailComplex H x)
    _ ≤ ∑' p : {p : DusartXiZero // p ∉ H},‖psiKernel x p‖ := htNorm
    _ ≤ x^(15/8:ℝ)*W := hn.trans (mul_le_mul_of_nonneg_left hW (by positivity))
    _ = _ := by ring

theorem psi_kernel_norm_on_line {x : ℝ} (hx : 1 ≤ x) (p : DusartXiZero)
    (hp : (divisorZeroIndex₀_val p).re=1/2) :
    ‖psiKernel x p‖=x^(3/2:ℝ)*absoluteXiWeight p := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  unfold psiKernel xiKernel absoluteXiWeight
  rw [norm_mul,norm_div,norm_cpow_eq_rpow_re_of_pos hx0,hp,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,norm_div,norm_one]
  have he : x*x^(1/2:ℝ)=x^(3/2:ℝ) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    norm_num
  rw [← mul_div_assoc,he]
  ring

theorem head_bound (H : Finset DusartXiZero) {x : ℝ} (hx : 1 ≤ x)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2) :
    |headReal H x| ≤ (3/25:ℝ)*x^(3/2:ℝ) := by
  have hw : (∑ p ∈ H,absoluteXiWeight p) ≤ 3/25 :=
    (dusart_xi_zero_absolute_moment.1.sum_le_tsum H (fun _ _ => norm_nonneg _)).trans
      dusart_xi_zero_absolute_moment.2
  calc
    _ ≤ ‖headComplex H x‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ p ∈ H,‖psiKernel x p‖ := norm_sum_le _ _
    _ = x^(3/2:ℝ)*∑ p ∈ H,absoluteXiWeight p := by
      rw [Finset.mul_sum]
      exact sum_congr rfl (fun p hp => psi_kernel_norm_on_line hx p (hline p hp))
    _ ≤ x^(3/2:ℝ)*(3/25) := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

/-- The actual psi1 envelope from the pilot, with only concrete finite-head
line and residual-moment bounds as inputs. No analytic error bound is assumed. -/
theorem actual_psi1_split_envelope (H : Finset DusartXiZero) {x W : ℝ} (hx : 1 < x)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |Dusart.psi1 x-x^2/2| ≤
      (3/25)*x^(3/2:ℝ)+W*x^(15/8:ℝ)+2*x+1000000000 := by
  have hh := head_bound H hx.le hline
  have ht := tail_bound H hx.le hW
  have hp := Dusart.psi1_formula hx
  rw [actual_zero_sum_split H hx.le] at hp
  have htriv := Dusart.y_tsum_tb_bounds hx.le
  have htriv2 : x*∑' n,Dusart.tb x n ≤ 2 := by
    nlinarith only [htriv.2,Real.pi_lt_d2,Real.pi_pos]
  have hlog0 : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog := mul_le_mul_of_nonneg_left DusartPort.Lab.ZetaZeros.log_two_pi_le (show 0 ≤ x by linarith)
  rw [hp]
  have hab := abs_add_le (headReal H x) (tailReal H x)
  have ha := abs_add_le (-(x*Real.log (2*Real.pi))-(headReal H x+tailReal H x))
    ((deriv riemannZeta (-1)/riemannZeta (-1)).re-x*∑' n,Dusart.tb x n)
  have hb := abs_sub (-(x*Real.log (2*Real.pi))) (headReal H x+tailReal H x)
  have hc := abs_sub (deriv riemannZeta (-1)/riemannZeta (-1)).re (x*∑' n,Dusart.tb x n)
  simp only [abs_neg,abs_mul,abs_of_pos (show 0 < x by linarith),abs_of_nonneg hlog0,
    abs_of_nonneg htriv.1] at ha hb hc
  have he : x^2/2-x*Real.log (2*Real.pi)-(headReal H x+tailReal H x)+
      (deriv riemannZeta (-1)/riemannZeta (-1)).re-x*∑' n,Dusart.tb x n-x^2/2 =
      (-(x*Real.log (2*Real.pi))-(headReal H x+tailReal H x))+
        ((deriv riemannZeta (-1)/riemannZeta (-1)).re-x*∑' n,Dusart.tb x n) := by ring
  rw [he]
  linarith only [ha,hb,hc,hab,hh,ht,hlog,htriv2,Dusart.numerical_residue_bound]

#print axioms actual_psi1_split_envelope
end ChenEffective.HybridProduct
