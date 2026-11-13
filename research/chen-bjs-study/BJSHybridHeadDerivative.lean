import BJSHybridZeroSplit

noncomputable section
namespace ChenEffective.HybridProduct
open Complex Complex.Hadamard Set Finset
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def headDerivative (H : Finset DusartXiZero) (x : ℝ) : ℂ :=
  ∑ p ∈ H,(x:ℂ)^(divisorZeroIndex₀_val p)/divisorZeroIndex₀_val p
def headDerivativeMass (H : Finset DusartXiZero) : ℝ :=
  ∑ p ∈ H,1/‖divisorZeroIndex₀_val p‖

theorem psi_kernel_hasDeriv {x : ℝ} (hx : 0 < x) (p : DusartXiZero) :
    HasDerivAt (fun y => psiKernel y p)
      ((x:ℂ)^(divisorZeroIndex₀_val p)/divisorZeroIndex₀_val p) x := by
  let z := divisorZeroIndex₀_val p
  have hz0 : z ≠ 0 := divisorZeroIndex₀_val_ne_zero p
  have hz1 : z+1 ≠ 0 := by
    intro h
    have hh := (dusart_xi_zero_strip (dusart_xi_index_zero p)).1
    have hr := congrArg Complex.re h
    change (1/8:ℝ) ≤ z.re at hh
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
    linarith only [hh,hr]
  have hxc : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hf : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have hg := (hasDerivAt_ofReal_cpow_const hx.ne' hz0).div_const (z*(z+1))
  have hd := hf.mul hg
  have he : (x:ℂ)*(x:ℂ)^(z-1)=(x:ℂ)^z := by
    nth_rw 1 [← Complex.cpow_one (x:ℂ)]
    rw [← Complex.cpow_add _ _ hxc]
    congr 1
    ring
  have he2 : (x:ℂ)*(z*(x:ℂ)^(z-1))=z*(x:ℂ)^z := by
    calc
      _ = z*((x:ℂ)*(x:ℂ)^(z-1)) := by ring
      _ = _ := by rw [he]
  have hval : 1*((x:ℂ)^z/(z*(z+1)))+(x:ℂ)*(z*(x:ℂ)^(z-1)/(z*(z+1)))=
      (x:ℂ)^z/z := by
    rw [← mul_div_assoc (x:ℂ) (z*(x:ℂ)^(z-1)) (z*(z+1)),he2]
    field_simp [hz0,hz1]
    ring
  rw [hval] at hd
  exact hd

theorem head_hasDeriv {x : ℝ} (hx : 0 < x) (H : Finset DusartXiZero) :
    HasDerivAt (headComplex H) (headDerivative H x) x :=
  HasDerivAt.fun_sum (fun p _ => psi_kernel_hasDeriv hx p)

theorem head_derivative_bound (H : Finset DusartXiZero) {x : ℝ} (hx : 0 < x)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2) :
    ‖headDerivative H x‖ ≤ headDerivativeMass H*Real.sqrt x := by
  unfold headDerivative headDerivativeMass
  calc
    _ ≤ ∑ p ∈ H,‖(x:ℂ)^(divisorZeroIndex₀_val p)/divisorZeroIndex₀_val p‖ := norm_sum_le _ _
    _ = (∑ p ∈ H,1/‖divisorZeroIndex₀_val p‖)*Real.sqrt x := by
      rw [Finset.sum_mul]
      apply sum_congr rfl
      intro p hp
      rw [norm_div,norm_cpow_eq_rpow_re_of_pos hx,hline p hp,Real.sqrt_eq_rpow]
      ring

theorem head_increment (H : Finset DusartXiZero) {a b A : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hA : headDerivativeMass H ≤ A) :
    |headReal H b-headReal H a| ≤ A*Real.sqrt b*(b-a) := by
  have hA0 : 0 ≤ A := (sum_nonneg (fun _ _ => by positivity)).trans hA
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt (headComplex H) (headDerivative H x) (Icc a b) x :=
    (head_hasDeriv (ha.trans_le hx.1) H).hasDerivWithinAt
  have hbnd (x : ℝ) (hx : x ∈ Ico a b) : ‖headDerivative H x‖ ≤ A*Real.sqrt b := by
    exact (head_derivative_bound H (ha.trans_le hx.1) hline).trans
      (mul_le_mul hA (Real.sqrt_le_sqrt hx.2.le) (Real.sqrt_nonneg x) hA0)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hbnd b (right_mem_Icc.mpr hab)
  have hr := Complex.abs_re_le_norm (headComplex H b-headComplex H a)
  rw [Complex.sub_re] at hr
  exact hr.trans hh

#print axioms head_increment
end ChenEffective.HybridProduct
