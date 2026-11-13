import BJSHarmonicKernel
import NumericalSelbergEulerMajorant

noncomputable section
namespace ChenEffective
open Real Finset Set MeasureTheory
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem tsum_tail_indicator_shift (f : ℕ → ℝ) (q : ℕ) :
    (∑' n, if q<n then f n else 0)=∑' k, f (k+q+1) := by
  classical
  let e : ℕ ≃ ↑({n : ℕ | q<n}) :=
    { toFun := fun k => ⟨k+q+1,by change q<k+q+1; omega⟩
      invFun := fun n => n.1-q-1
      left_inv := by intro k; dsimp; omega
      right_inv := by
        intro n
        have hn := n.property
        change q<n.val at hn
        apply Subtype.ext
        dsimp
        omega }
  calc
    _ = ∑' n, ({n : ℕ | q<n}.indicator f) n := by
      apply tsum_congr
      intro n
      by_cases hn : q<n <;> simp [Set.indicator,hn]
    _ = ∑' n : ↑({n : ℕ | q<n}),f n.1 := (_root_.tsum_subtype _ _).symm
    _ = _ := by simpa only [e,Equiv.coe_fn_mk] using (e.tsum_eq (fun n => f n.1)).symm

theorem power_tail_bound {q : ℕ} (hq : 1≤q) {s : ℝ} (hs : 1<s) :
    (∑' n : ℕ,if q<n then (n:ℝ)^(-s) else 0) ≤ (q:ℝ)^(1-s)/(s-1) := by
  rw [tsum_tail_indicator_shift]
  have hqR : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have ha : AntitoneOn (fun x : ℝ => x^(-s)) (Ici (q:ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -s≤0)).mono
      (Ici_subset_Ioi.mpr hqR)
  have hh := AntitoneOn.tsum_comp_add_le_integral (f:=fun x : ℝ => x^(-s)) q ha
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) hqR)
    (fun t ht => rpow_nonneg (by linarith only [(mem_Ioi.mp ht),hqR] : 0≤t) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) hqR] at hh
  have he : -(q:ℝ)^(-s+1)/(-s+1)=(q:ℝ)^(1-s)/(s-1) := by
    calc
      _ = (q:ℝ)^(-s+1)/(s-1) := by rw [show -s+1= -(s-1) by ring,neg_div_neg_eq]
      _ = _ := by congr 1; ring
  simpa only [he] using hh

theorem inverse_square_tail {q : ℕ} (hq : 1≤q) :
    (∑' n : ℕ,if q<n then 1/(n:ℝ)^2 else 0) ≤ 1/(q:ℝ) := by
  have hh := power_tail_bound hq (by norm_num : (1:ℝ)<2)
  have hid (n : ℕ) : (n:ℝ)^(-(2:ℝ))=1/(n:ℝ)^2 := by
    rw [rpow_neg (Nat.cast_nonneg n),rpow_two,one_div]
  simp only [hid] at hh
  simpa only [show (1:ℝ)-2= -1 by norm_num,show (2:ℝ)-1=1 by norm_num,
    Real.rpow_neg_one,div_one,one_div] using hh

theorem inverse_three_halves_tail {q : ℕ} (hq : 1≤q) :
    (∑' n : ℕ,if q<n then 1/((n:ℝ)*sqrt n) else 0) ≤ 2/sqrt q := by
  have hh := power_tail_bound hq (by norm_num : (1:ℝ)<3/2)
  have hid (n : ℕ) : (n:ℝ)^(-(3/2:ℝ))=1/((n:ℝ)*sqrt n) := by
    by_cases hn : n=0
    · subst n; norm_num
    have hnR : (0:ℝ)<n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    rw [rpow_neg hnR.le,show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hnR,
      rpow_one,← sqrt_eq_rpow,one_div]
  simp only [hid] at hh
  have hqR : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have he : (q:ℝ)^((1:ℝ)-3/2)/((3/2:ℝ)-1)=2/sqrt q := by
    norm_num only [show (1:ℝ)-3/2= -(1/2) by norm_num,
      show (3/2:ℝ)-1=1/2 by norm_num]
    rw [rpow_neg hqR.le,← sqrt_eq_rpow]
    ring
  exact hh.trans_eq he

end ChenEffective
