import BJSHybridHeadDerivative

noncomputable section
namespace ChenEffective.HybridProduct
open Complex Complex.Hadamard Set Real
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

def trivialReal (x : ℝ) : ℝ := x*∑' n,Dusart.tb x n

theorem trivial_real_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ trivialReal x ∧ trivialReal x ≤ 2 := by
  have hh := Dusart.y_tsum_tb_bounds hx
  exact ⟨hh.1,by dsimp [trivialReal]; nlinarith only [hh.2,pi_lt_d2,pi_pos]⟩

theorem centered_psi1_difference (H : Finset DusartXiZero) {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) :
    (Dusart.psi1 b-b^2/2)-(Dusart.psi1 a-a^2/2)=
      -(b-a)*Real.log (2*Real.pi)-(headReal H b-headReal H a)-
        (tailReal H b-tailReal H a)-(trivialReal b-trivialReal a) := by
  rw [Dusart.psi1_formula hb,Dusart.psi1_formula ha,
    actual_zero_sum_split H hb.le,actual_zero_sum_split H ha.le]
  unfold trivialReal
  ring

theorem centered_difference_bound (H : Finset DusartXiZero) {a b A W : ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hA : headDerivativeMass H ≤ A)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |(Dusart.psi1 b-b^2/2)-(Dusart.psi1 a-a^2/2)| ≤
      2*(b-a)+A*Real.sqrt b*(b-a)+W*(b^(15/8:ℝ)+a^(15/8:ℝ))+2 := by
  have hb : 1 < b := ha.trans_le hab
  have hhead := head_increment H (by linarith only [ha]) hab hline hA
  have hRa := tail_bound H ha.le hW
  have hRb := tail_bound H hb.le hW
  have hTa := trivial_real_bounds ha.le
  have hTb := trivial_real_bounds hb.le
  have hT : |trivialReal b-trivialReal a| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith only [hTa.1,hTa.2,hTb.1,hTb.2]
  have hR := abs_sub (tailReal H b) (tailReal H a)
  have hlog0 : 0 ≤ Real.log (2*Real.pi) := log_nonneg (by linarith [pi_gt_three])
  have hlog : |-(b-a)*Real.log (2*Real.pi)| ≤ 2*(b-a) := by
    rw [abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr hab),abs_of_nonneg hlog0]
    nlinarith only [DusartPort.Lab.ZetaZeros.log_two_pi_le,hab]
  rw [centered_psi1_difference H ha hb]
  have h1 := abs_sub (-(b-a)*Real.log (2*Real.pi)-(headReal H b-headReal H a)-
    (tailReal H b-tailReal H a)) (trivialReal b-trivialReal a)
  have h2 := abs_sub (-(b-a)*Real.log (2*Real.pi)-(headReal H b-headReal H a))
    (tailReal H b-tailReal H a)
  have h3 := abs_sub (-(b-a)*Real.log (2*Real.pi)) (headReal H b-headReal H a)
  nlinarith only [h1,h2,h3,hlog,hhead,hR,hRa,hRb,hT]

/-- Actual unsmoothing with a freely chosen positive step. The constant
residue has cancelled in centered_psi1_difference, so no 10^9/h loss occurs. -/
theorem actual_psi_step_bound (H : Finset DusartXiZero) {x h A W : ℝ}
    (hx : 1 < x-h) (hh : 0 < h)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hA : headDerivativeMass H ≤ A)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    h*|Chebyshev.psi x-x| ≤
      h^2/2+2*h+A*Real.sqrt (x+h)*h+W*((x+h)^(15/8:ℝ)+x^(15/8:ℝ))+2 := by
  have hx1 : 1 < x := by linarith only [hx,hh]
  have hA0 : 0 ≤ A := (Finset.sum_nonneg (fun _ _ => by positivity)).trans hA
  have hW0 : 0 ≤ W := (tsum_nonneg (fun _ => norm_nonneg _)).trans hW
  have hu := (abs_le.mp (centered_difference_bound H (b:=x+h) hx1 (by linarith only [hh]) hline hA hW)).2
  have hl := (abs_le.mp (centered_difference_bound H hx (by linarith only [hh]) hline hA hW)).1
  have hU := (Dusart.psi1_diff_bounds (show 0 ≤ x by linarith only [hx1]) hh).1
  have hD := (Dusart.psi1_diff_bounds (show 0 ≤ x-h by linarith only [hx]) hh).2
  rw [sub_add_cancel] at hD
  rw [Dusart.psiF_eq_chebyshev] at hU hD
  have hs : Real.sqrt x ≤ Real.sqrt (x+h) := Real.sqrt_le_sqrt (by linarith only [hh])
  have hp : (x-h)^(15/8:ℝ) ≤ (x+h)^(15/8:ℝ) :=
    rpow_le_rpow (by linarith only [hx]) (by linarith only [hh]) (by norm_num)
  have hsa := mul_le_mul_of_nonneg_left hs (mul_nonneg hA0 hh.le)
  have hpa := mul_le_mul_of_nonneg_left hp hW0
  have hup : h*(Chebyshev.psi x-x) ≤
      h^2/2+2*h+A*Real.sqrt (x+h)*h+W*((x+h)^(15/8:ℝ)+x^(15/8:ℝ))+2 := by
    nlinarith only [hu,hU]
  have hlo : -(h^2/2+2*h+A*Real.sqrt (x+h)*h+W*((x+h)^(15/8:ℝ)+x^(15/8:ℝ))+2) ≤
      h*(Chebyshev.psi x-x) := by
    nlinarith only [hl,hD,hsa,hpa]
  simpa only [abs_mul, abs_of_pos hh] using (abs_le.mpr ⟨hlo,hup⟩)

theorem actual_psi_bound (H : Finset DusartXiZero) {x h A W : ℝ}
    (hx : 1 < x-h) (hh : 0 < h)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hA : headDerivativeMass H ≤ A)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |Chebyshev.psi x-x| ≤ h/2+2+A*Real.sqrt (x+h)+
      W*((x+h)^(15/8:ℝ)+x^(15/8:ℝ))/h+2/h := by
  have hb := actual_psi_step_bound H hx hh hline hA hW
  have hs : |Chebyshev.psi x-x| ≤
      (h^2/2+2*h+A*Real.sqrt (x+h)*h+
        W*((x+h)^(15/8:ℝ)+x^(15/8:ℝ))+2)/h :=
    (le_div_iff₀ hh).mpr (by nlinarith only [hb])
  convert hs using 1
  field_simp

#print axioms actual_psi_step_bound
end ChenEffective.HybridProduct


