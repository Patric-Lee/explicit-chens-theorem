import BJSLayerTwo

/-! A 64-cell, exact-rational certificate for the second continuous layer.
All exponential upper bounds are proved analytically; norm_num checks only
finite rational inequalities. No native evaluator is used.
-/
noncomputable section
namespace ChenEffective
open Real Set Finset MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

private theorem exp_grid_upper (i : ℕ) :
    exp ((i : ℝ)/32) ≤ (65/63 : ℝ)^i := by
  have he := exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ)≤1/32)
    (by norm_num : (1/32 : ℝ)<2)
  norm_num at he
  have hp := pow_le_pow_left₀ (exp_pos (1/32 : ℝ)).le he i
  rw [← exp_nat_mul] at hp
  simpa only [div_eq_mul_inv,one_mul] using hp

private theorem layer_two_cell (i : ℕ) (hi : i < 64) :
    layer 2 2 (2+(i : ℝ)/32) ≤
      2*exp 2*(7/20 : ℝ)*sieveHat (2+(i+1 : ℕ)/32) := by
  have hiR : (i : ℝ) ≤ 63 := by exact_mod_cast (show i ≤ 63 by omega)
  have hm : ((64-i : ℕ) : ℝ)=64-i := by rw [Nat.cast_sub (by omega)]; norm_num
  have hsi : (2 : ℝ) ≤ 2+(i : ℝ)/32 := le_add_of_nonneg_right (by positivity)
  have hq := bjsStudy_layer_successor_grid (n:=1) (m:=64-i)
    (s:=2+(i : ℝ)/32) (h:=1/32) (by omega)
    (by norm_num [closedDomain,eps]; positivity) (by norm_num)
    (by norm_num [eps]; linarith only [hiR])
    (by rw [hm]; norm_num only [eps, Nat.reduceMod, Nat.cast_zero, add_zero]; rw [max_eq_left hsi]; ring)
  let x : ℝ := 2+(i+1 : ℕ)/32
  let R : ℝ := (65/63 : ℝ)^(i+1)
  have hx : 2 ≤ x := le_add_of_nonneg_right (by positivity)
  have hR : 0 < R := by dsimp [R]; positivity
  have hex : exp (x-2) ≤ R := by
    simpa only [x, add_sub_cancel_left] using exp_grid_upper (i+1)
  have hhat : 6/(max 3 x*R) ≤ 2*exp 2*sieveHat x := by
    have hmpos : 0 < max 3 x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hinv := one_div_le_one_div_of_le (exp_pos (x-2)) hex
    have he : exp (2 : ℝ)*exp (-x)=1/exp (x-2) := by
      rw [← exp_add,one_div,← exp_neg]
      congr 1
      ring
    rw [sieveHat_max_formula, max_eq_right hx]
    have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 6/max 3 x by positivity)
    calc
      _ = (6/max 3 x)*(1/R) := by ring
      _ ≤ (6/max 3 x)*(1/exp (x-2)) := hh
      _ = _ := by rw [← he]; ring
  have hsum : ((1/32 : ℝ)/(2+(i : ℝ)/32))*
      (∑ j ∈ range (64-i), layer 2 1 (max (2+(i : ℝ)/32) (2+(eps 2 : ℝ))+j*(1/32)-1)) ≤
        (7/20 : ℝ)*(6/(max 3 x*R)) := by
    dsimp [x,R]
    interval_cases i <;>
      norm_num [layer,Finset.sum_range_succ,intervalIntegral.integral_const,smul_eq_mul,eps]
  apply hq.trans (hsum.trans ?_)
  have hh := mul_le_mul_of_nonneg_left hhat (by norm_num : (0 : ℝ)≤7/20)
  dsimp [x] at hh
  nlinarith only [hh]

theorem bjsStudy_layer_two_hat_sharp {s : ℝ} (hs : 2 ≤ s) :
    layer 2 2 s ≤ 2*exp 2*(7/20 : ℝ)*sieveHat s := by
  by_cases hs4 : 4 ≤ s
  · rw [bjsStudy_layer_zero (n:=2) (by norm_num; exact hs4)]
    have hh := (sieveHat_pos s).le
    positivity
  let i : ℕ := ⌊32*(s-2)⌋₊
  have hx0 : 0 ≤ 32*(s-2) := by linarith only [hs]
  have hfloor : (i : ℝ) ≤ 32*(s-2) := Nat.floor_le hx0
  have hnext : 32*(s-2) < (i+1 : ℕ) := by
    simpa only [i,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (32*(s-2))
  have hi : i < 64 := by
    have hr : (i : ℝ)<64 := by linarith only [hfloor,hs4]
    exact_mod_cast hr
  have hleft : 2+(i : ℝ)/32 ≤ s := by linarith only [hfloor]
  have hright : s ≤ 2+(i+1 : ℕ)/32 := by linarith only [hnext]
  have hd : 2+(i : ℝ)/32 ∈ closedDomain 2 2 := by norm_num [closedDomain,eps]; positivity
  have hds : s ∈ closedDomain 2 2 := by simpa [closedDomain,eps] using hs
  apply (bjsStudy_layer_antitone 2 hd hds hleft).trans
  apply (layer_two_cell i hi).trans
  exact mul_le_mul_of_nonneg_left (sieveHat_antitone hright) (by positivity)

#print axioms bjsStudy_layer_two_hat_sharp
end ChenEffective
