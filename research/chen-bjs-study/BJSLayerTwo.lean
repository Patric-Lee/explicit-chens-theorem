import BJSLayerQuadrature

/-! First checked numerical layer bounds, using exact rational Riemann sums.
No paper table entries or external analytic assumptions are imported.
-/
noncomputable section
namespace ChenEffective
open Real Set Finset MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

theorem bjsStudy_layer_two_at_two : layer 2 2 2 ≤ (7/10 : ℝ) := by
  have hq := bjsStudy_layer_successor_grid (n:=1) (m:=32) (s:=2) (h:=1/16)
    (by omega) (by norm_num [closedDomain,eps]) (by norm_num)
    (by norm_num [eps]) (by norm_num [eps])
  apply hq.trans
  norm_num [layer,Finset.sum_range_succ,intervalIntegral.integral_const,smul_eq_mul,eps]

theorem bjsStudy_layer_two_at_five_halves : layer 2 2 (5/2) ≤ (13/50 : ℝ) := by
  have hq := bjsStudy_layer_successor_grid (n:=1) (m:=24) (s:=5/2) (h:=1/16)
    (by omega) (by norm_num [closedDomain,eps]) (by norm_num)
    (by norm_num [eps]) (by norm_num [eps])
  apply hq.trans
  norm_num [layer,Finset.sum_range_succ,intervalIntegral.integral_const,smul_eq_mul,eps]

theorem bjsStudy_layer_two_at_three : layer 2 2 3 ≤ (2/25 : ℝ) := by
  have hq := bjsStudy_layer_successor_grid (n:=1) (m:=16) (s:=3) (h:=1/16)
    (by omega) (by norm_num [closedDomain,eps]) (by norm_num)
    (by norm_num [eps]) (by norm_num [eps])
  apply hq.trans
  norm_num [layer,Finset.sum_range_succ,intervalIntegral.integral_const,smul_eq_mul,eps]

/-- A complete hat envelope for layer two, sharper than the previous 0.964.
The coefficient 0.6 is deliberately loose; this is not the BJS 0.33 entry. -/
theorem bjsStudy_layer_two_hat {s : ℝ} (hs : 2 ≤ s) :
    layer 2 2 s ≤ 2*exp 2*(3/5 : ℝ)*sieveHat s := by
  have hd (x : ℝ) (hx : 2 ≤ x) : x ∈ closedDomain 2 2 := by simpa [closedDomain,eps] using hx
  have hE := (exp_pos (2 : ℝ)).le
  have hH := (sieveHat_pos s).le
  have hhalf : (3/5 : ℝ) ≤ exp (-(1/2 : ℝ)) := by
    have he := exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<2)
    rw [exp_neg,inv_eq_one_div]
    apply (le_div_iff₀ (exp_pos _)).mpr
    norm_num at he ⊢
    linarith only [he]
  have hminus : (1/3 : ℝ) ≤ exp (-1) := by linarith only [Real.exp_neg_one_gt_d9]
  have hminus2 : (1/9 : ℝ) ≤ exp (-2) := by
    have he : exp (-2 : ℝ)=exp (-1)*exp (-1) := by rw [← exp_add]; norm_num
    rw [he]
    nlinarith only [hminus,sq_nonneg (exp (-1)-1/3)]
  have hbound25 : (6/5 : ℝ) ≤ 2*exp 2*sieveHat (5/2) := by
    have he : exp (2 : ℝ)*exp (-(5/2 : ℝ))=exp (-(1/2 : ℝ)) := by rw [← exp_add]; norm_num
    norm_num [sieveHat] at he ⊢
    nlinarith only [he,hhalf]
  have hbound3 : (2/3 : ℝ) ≤ 2*exp 2*sieveHat 3 := by
    have he : exp (2 : ℝ)*exp (-3)=exp (-1) := by rw [← exp_add]; norm_num
    norm_num [sieveHat] at he ⊢
    nlinarith only [he,hminus]
  have hbound4 : (1/6 : ℝ) ≤ 2*exp 2*sieveHat 4 := by
    have he : exp (2 : ℝ)*exp (-4)=exp (-2) := by rw [← exp_add]; norm_num
    norm_num [sieveHat] at he ⊢
    nlinarith only [he,hminus2]
  by_cases hs4 : 4 ≤ s
  · rw [bjsStudy_layer_zero (n:=2) (by norm_num; exact hs4)]
    positivity
  by_cases hs25 : s ≤ 5/2
  · have hl := (bjsStudy_layer_antitone 2 (hd 2 le_rfl) (hd s hs) hs).trans bjsStudy_layer_two_at_two
    have hh := mul_le_mul_of_nonneg_left (sieveHat_antitone hs25) (show 0 ≤ 2*exp (2 : ℝ) by positivity)
    nlinarith only [hl,hh,hbound25]
  by_cases hs3 : s ≤ 3
  · have hl := (bjsStudy_layer_antitone 2 (hd (5/2) (by norm_num)) (hd s hs)
      (le_of_not_ge hs25)).trans bjsStudy_layer_two_at_five_halves
    have hh := mul_le_mul_of_nonneg_left (sieveHat_antitone hs3) (show 0 ≤ 2*exp (2 : ℝ) by positivity)
    nlinarith only [hl,hh,hbound3]
  · have hl := (bjsStudy_layer_antitone 2 (hd 3 (by norm_num)) (hd s hs)
      (le_of_not_ge hs3)).trans bjsStudy_layer_two_at_three
    have hh := mul_le_mul_of_nonneg_left (sieveHat_antitone (le_of_not_ge hs4))
      (show 0 ≤ 2*exp (2 : ℝ) by positivity)
    nlinarith only [hl,hh,hbound4]

#print axioms bjsStudy_layer_two_hat
end ChenEffective
