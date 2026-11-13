import BJSSelbergSpecialization
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Explicit real-endpoint harmonic estimates used by the critical
squarefree convolution. Floors, including the empty range, are retained. -/
noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory.LiuWeight
set_option maxHeartbeats 3000000

def realHarmonic (x : ℝ) : ℝ := liuHarmonic ⌊x⌋₊

theorem harmonic_euler_error_nat {n : ℕ} (hn : 0 < n) :
    0 ≤ liuHarmonic n-log (n:ℝ)-eulerMascheroniConstant ∧
    liuHarmonic n-log (n:ℝ)-eulerMascheroniConstant ≤ 1/(n:ℝ) := by
  have hupper := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have hlower := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [eulerMascheroniSeq] at hupper
  rw [eulerMascheroniSeq',if_neg hn.ne'] at hlower
  rw [liuHarmonic_eq_harmonic]
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : log ((n:ℝ)+1)-log (n:ℝ) ≤ 1/(n:ℝ) := by
    rw [← log_div (by positivity) hnR.ne']
    have hh := log_le_sub_one_of_pos (show (0:ℝ)<((n:ℝ)+1)/(n:ℝ) by positivity)
    have he : ((n:ℝ)+1)/(n:ℝ)-1=1/(n:ℝ) := by field_simp; ring
    simpa only [he] using hh
  constructor <;> linarith

theorem real_harmonic_error_large {x : ℝ} (hx : 1 ≤ x) :
    |realHarmonic x-log x-eulerMascheroniConstant| ≤ 2/x := by
  let n := ⌊x⌋₊
  have hn : 1 ≤ n := Nat.le_floor (by simpa using hx)
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hx0 : 0<x := by linarith only [hx]
  have hnx : (n:ℝ) ≤ x := Nat.floor_le hx0.le
  have hxn : x < (n:ℝ)+1 := by simpa only [n] using Nat.lt_floor_add_one x
  obtain ⟨hlo,hhi⟩ := harmonic_euler_error_nat (show 0<n by omega)
  have hlog0 : 0 ≤ log x-log (n:ℝ) := sub_nonneg.mpr (log_le_log hnR hnx)
  have hlog1 : log x-log (n:ℝ) ≤ 1/(n:ℝ) := by
    have hh := log_le_sub_one_of_pos (div_pos hx0 hnR)
    rw [log_div hx0.ne' hnR.ne'] at hh
    have hc : x/(n:ℝ)-1 ≤ 1/(n:ℝ) := by
      apply (le_div_iff₀ hnR).mpr
      field_simp at *
      linarith only [hxn]
    exact hh.trans hc
  have habs : |realHarmonic x-log x-eulerMascheroniConstant| ≤ 1/(n:ℝ) := by
    unfold realHarmonic
    change |liuHarmonic n-log x-eulerMascheroniConstant| ≤ _
    apply abs_le.mpr
    constructor <;> linarith only [hlo,hhi,hlog0,hlog1]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  apply habs.trans
  apply (div_le_div_iff₀ hnR hx0).mpr
  linarith only [hxn,hn1]

theorem real_harmonic_zero_below_one {x : ℝ} (hx : x < 1) : realHarmonic x=0 := by
  unfold realHarmonic
  rw [Nat.floor_eq_zero.mpr hx,liuHarmonic_zero]

#print axioms real_harmonic_error_large
end ChenEffective
