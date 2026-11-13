import BJSHarmonicKernel

/-! An explicit critical-exponent convolution transfer. The estimate is
valid for all positive real arguments of the base function, including empty
sums. This prevents a hidden tail loss at d>R. -/
noncomputable section
namespace ChenEffective
open Real Finset
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem square_root_convolution_transfer
    (a : ℕ → ℝ) (F : ℝ → ℝ) (A B C : ℝ)
    (ha0 : a 0=0) (_hC : 0≤C)
    (hsmall : ∀ x : ℝ, x<1 → F x=0)
    (hbase : ∀ x : ℝ, 0<x → |F x-(A*log x+B)| ≤ C/sqrt x)
    (ha : Summable a) (halog : Summable (fun d => a d*log (d:ℝ)))
    (hroot : Summable (fun d => |a d| *sqrt d))
    {R : ℕ} (hR : 1≤R) :
    |(∑ d∈Icc 1 R,a d*F ((R:ℝ)/d))-
      ((A*log (R:ℝ)+B)*(∑' d,a d)-A*(∑' d,a d*log (d:ℝ)))| ≤
      (C/sqrt R)*(∑' d,|a d| *sqrt d) := by
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hsRp : 0<sqrt (R:ℝ) := sqrt_pos.mpr hRp
  let e : ℕ → ℝ := fun d => a d*(F ((R:ℝ)/d)-(A*log ((R:ℝ)/d)+B))
  have heb (d : ℕ) : |e d| ≤ (C/sqrt R)*(|a d| *sqrt d) := by
    by_cases hd : d=0
    · subst d; simp [e,ha0]
    have hdp : (0:ℝ)<d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    have hsdp : 0<sqrt (d:ℝ) := sqrt_pos.mpr hdp
    have hh := mul_le_mul_of_nonneg_left (hbase ((R:ℝ)/d) (div_pos hRp hdp)) (abs_nonneg (a d))
    rw [← abs_mul] at hh
    change |e d| ≤ _ at hh
    apply hh.trans_eq
    rw [sqrt_div hRp.le]
    field_simp
  have heabs : Summable (fun d => |e d|) :=
    Summable.of_nonneg_of_le (fun d => abs_nonneg _) heb
      (hroot.mul_left (C/sqrt R))
  have hes : Summable e := Summable.of_norm (by simpa only [Real.norm_eq_abs] using heabs)
  have hetsum : |∑' d,e d| ≤ (C/sqrt R)*(∑' d,|a d| *sqrt d) := by
    calc
      _ ≤ ∑' d,|e d| := by simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f:=e) (by simpa only [Real.norm_eq_abs] using heabs)
      _ ≤ ∑' d,(C/sqrt R)*(|a d| *sqrt d) :=
        Summable.tsum_le_tsum heb heabs (hroot.mul_left _)
      _ = _ := tsum_mul_left
  have heq (d : ℕ) : a d*F ((R:ℝ)/d)=
      a d*(A*log (R:ℝ)+B)-A*(a d*log (d:ℝ))+e d := by
    by_cases hd : d=0
    · subst d; simp [ha0,e]
    have hdp : (0:ℝ)<d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    dsimp only [e]
    rw [log_div hRp.ne' hdp.ne']
    ring
  have hsum : (∑' d,a d*F ((R:ℝ)/d))=
      ((A*log (R:ℝ)+B)*(∑' d,a d)-A*(∑' d,a d*log (d:ℝ)))+∑' d,e d := by
    simp_rw [heq]
    rw [((ha.mul_right _).sub (halog.mul_left A)).tsum_add hes,
      (ha.mul_right _).tsum_sub (halog.mul_left A),tsum_mul_right,tsum_mul_left]
    ring
  have hfinite : (∑' d,a d*F ((R:ℝ)/d))=∑ d∈Icc 1 R,a d*F ((R:ℝ)/d) := by
    apply tsum_eq_sum
    intro d hd
    by_cases hd0 : d=0
    · subst d; simp [ha0]
    have hdp : (0:ℝ)<d := by exact_mod_cast (Nat.pos_of_ne_zero hd0)
    have hRd : R<d := by simp only [mem_Icc,not_and_or] at hd; omega
    have hratio : (R:ℝ)/d<1 := (div_lt_one hdp).mpr (by exact_mod_cast hRd)
    rw [hsmall _ hratio,mul_zero]
  rw [hfinite] at hsum
  have hdiff : (∑ d∈Icc 1 R,a d*F ((R:ℝ)/d))-
      ((A*log (R:ℝ)+B)*(∑' d,a d)-A*(∑' d,a d*log (d:ℝ)))=∑' d,e d := by
    linarith only [hsum]
  rw [hdiff]
  exact hetsum

#print axioms square_root_convolution_transfer
end ChenEffective
