import BJSHybridMomentResidual
import DusartPort.Psi1Estimate

noncomputable section
namespace ChenEffective.HybridProduct
open Complex Complex.Hadamard Set
open DusartPort.Lab.ExplicitPsi1
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

abbrev ZetaCopy := Σ ρ : Zall, Fin (analyticOrderNatAt riemannZeta ρ)

theorem xi_index_zeta_zero (p : DusartXiZero) :
    riemannZeta (divisorZeroIndex₀_val p)=0 := by
  let z := divisorZeroIndex₀_val p
  have hz0 : z ≠ 0 := divisorZeroIndex₀_val_ne_zero p
  have hstrip := dusart_xi_zero_strip (dusart_xi_index_zero p)
  have hz1 : z ≠ 1 := by
    intro hh
    have hhi := hstrip.2
    change z.re ≤ 7/8 at hhi
    norm_num [hh] at hhi
  have hxi := dusart_xi_index_zero p
  change riemannXi z=0 at hxi
  rw [riemannXi_eq_mul_completedRiemannZeta hz0 hz1] at hxi
  have hc : completedRiemannZeta z=0 := by
    have hh := (div_eq_zero_iff).mp hxi
    have hprod : z*(z-1)*completedRiemannZeta z=0 := hh.resolve_right (by norm_num)
    exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hz0 (sub_ne_zero.mpr hz1))
  rw [riemannZeta_def_of_ne_zero hz0,hc,zero_div]

def copyToXi (p : ZetaCopy) : DusartXiZero :=
  ⟨⟨p.1,⟨p.2.val,by
    rw [dusart_zeta_zero_multiplicity p.1.property.1 p.1.property.2]
    exact p.2.isLt⟩⟩,(dusart_zeta_zero_endpoints p.1.property.1).1⟩

def xiToCopy (p : DusartXiZero) : ZetaCopy :=
  ⟨⟨divisorZeroIndex₀_val p,xi_index_zeta_zero p,by
      have hh := (dusart_xi_zero_strip (dusart_xi_index_zero p)).1
      linarith only [hh]⟩,⟨p.1.2.val,by
    rw [← dusart_zeta_zero_multiplicity (xi_index_zeta_zero p)
      (show (-1/2:ℝ) ≤ (divisorZeroIndex₀_val p).re by
        have hh := (dusart_xi_zero_strip (dusart_xi_index_zero p)).1
        linarith only [hh])]
    exact p.1.2.isLt⟩⟩

def zeroCopyEquiv : ZetaCopy ≃ DusartXiZero where
  toFun := copyToXi
  invFun := xiToCopy
  left_inv p := by
    rcases p with ⟨⟨z,hz⟩,⟨n,hn⟩⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨z,⟨n,hn⟩⟩,hz⟩
    rfl

def xiKernel (x : ℝ) (p : DusartXiZero) : ℂ :=
  (x:ℂ)^(divisorZeroIndex₀_val p)/(divisorZeroIndex₀_val p*(divisorZeroIndex₀_val p+1))

theorem xi_kernel_norm {x : ℝ} (hx : 1 ≤ x) (p : DusartXiZero) :
    ‖xiKernel x p‖ ≤ x^(7/8:ℝ)*absoluteXiWeight p := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hstrip := dusart_xi_zero_strip (dusart_xi_index_zero p)
  unfold xiKernel absoluteXiWeight
  rw [norm_div,norm_cpow_eq_rpow_re_of_pos hx0,norm_div,norm_one]
  calc
    _ ≤ x^(7/8:ℝ)/‖divisorZeroIndex₀_val p*(divisorZeroIndex₀_val p+1)‖ :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx hstrip.2) (norm_nonneg _)
    _ = _ := by ring

theorem summable_xi_kernel {x : ℝ} (hx : 1 ≤ x) : Summable (xiKernel x) :=
  Summable.of_norm_bounded (dusart_xi_zero_absolute_moment.1.mul_left (x^(7/8:ℝ)))
    (xi_kernel_norm hx)

theorem xi_kernel_tsum_eq {x : ℝ} (hx : 1 ≤ x) :
    (∑' p, xiKernel x p)=∑' ρ : Zall, zterm x ρ := by
  have hs : Summable (fun p : ZetaCopy => xiKernel x (zeroCopyEquiv p)) :=
    zeroCopyEquiv.summable_iff.mpr (summable_xi_kernel hx)
  rw [← zeroCopyEquiv.tsum_eq (xiKernel x),hs.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  apply tsum_congr
  intro ρ
  change (∑' _ : Fin (analyticOrderNatAt riemannZeta ρ),
      (x:ℂ)^(ρ:ℂ)/((ρ:ℂ)*(ρ+1))) = _
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,zterm]

#print axioms xi_kernel_tsum_eq

#print axioms zeroCopyEquiv
end ChenEffective.HybridProduct

