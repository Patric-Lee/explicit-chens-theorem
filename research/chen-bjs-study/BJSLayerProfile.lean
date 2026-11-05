import BJSLayerTableChecks
import BJSGridProfile
import BJSAnalyticTail

noncomputable section
namespace ChenEffective
open Real
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
theorem bjsGridSemantic1 : BJSGridBound 1 bjsGridRow1 := bjsStudy_grid_base bjsGridRow1 bjsGridBaseCheck
theorem bjsGridSemantic2 : BJSGridBound 2 bjsGridRow2 :=
 bjsStudy_grid_step (n:=1) (by omega) bjsGridRow1 bjsGridRow2 bjsGridTail2 bjsGridSemantic1 bjsGridStepCheck2
theorem bjsGridSemantic3 : BJSGridBound 3 bjsGridRow3 :=
 bjsStudy_grid_step (n:=2) (by omega) bjsGridRow2 bjsGridRow3 bjsGridTail3 bjsGridSemantic2 bjsGridStepCheck3
theorem bjsGridSemantic4 : BJSGridBound 4 bjsGridRow4 :=
 bjsStudy_grid_step (n:=3) (by omega) bjsGridRow3 bjsGridRow4 bjsGridTail4 bjsGridSemantic3 bjsGridStepCheck4
theorem bjsGridSemantic5 : BJSGridBound 5 bjsGridRow5 :=
 bjsStudy_grid_step (n:=4) (by omega) bjsGridRow4 bjsGridRow5 bjsGridTail5 bjsGridSemantic4 bjsGridStepCheck5
theorem bjsGridSemantic6 : BJSGridBound 6 bjsGridRow6 :=
 bjsStudy_grid_step (n:=5) (by omega) bjsGridRow5 bjsGridRow6 bjsGridTail6 bjsGridSemantic5 bjsGridStepCheck6
theorem bjsGridSemantic7 : BJSGridBound 7 bjsGridRow7 :=
 bjsStudy_grid_step (n:=6) (by omega) bjsGridRow6 bjsGridRow7 bjsGridTail7 bjsGridSemantic6 bjsGridStepCheck7
theorem bjsGridSemantic8 : BJSGridBound 8 bjsGridRow8 :=
 bjsStudy_grid_step (n:=7) (by omega) bjsGridRow7 bjsGridRow8 bjsGridTail8 bjsGridSemantic7 bjsGridStepCheck8
theorem bjsGridSemantic9 : BJSGridBound 9 bjsGridRow9 :=
 bjsStudy_grid_step (n:=8) (by omega) bjsGridRow8 bjsGridRow9 bjsGridTail9 bjsGridSemantic8 bjsGridStepCheck9
theorem bjsGridSemantic10 : BJSGridBound 10 bjsGridRow10 :=
 bjsStudy_grid_step (n:=9) (by omega) bjsGridRow9 bjsGridRow10 bjsGridTail10 bjsGridSemantic9 bjsGridStepCheck10
theorem bjsGridSemantic11 : BJSGridBound 11 bjsGridRow11 :=
 bjsStudy_grid_step (n:=10) (by omega) bjsGridRow10 bjsGridRow11 bjsGridTail11 bjsGridSemantic10 bjsGridStepCheck11
theorem bjsGridSemantic12 : BJSGridBound 12 bjsGridRow12 :=
 bjsStudy_grid_step (n:=11) (by omega) bjsGridRow11 bjsGridRow12 bjsGridTail12 bjsGridSemantic11 bjsGridStepCheck12
theorem bjsGridHat1 : ∀ s ∈ closedDomain 2 1, layer 2 1 s ≤
 2*exp 2*((bjsGridProfileNumerators[0]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 1 bjsGridRow1 bjsGridProfileNumerators[0]! bjsGridSemantic1 bjsGridProfileCheck1
theorem bjsGridHat2 : ∀ s ∈ closedDomain 2 2, layer 2 2 s ≤
 2*exp 2*((bjsGridProfileNumerators[1]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 2 bjsGridRow2 bjsGridProfileNumerators[1]! bjsGridSemantic2 bjsGridProfileCheck2
theorem bjsGridHat3 : ∀ s ∈ closedDomain 2 3, layer 2 3 s ≤
 2*exp 2*((bjsGridProfileNumerators[2]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 3 bjsGridRow3 bjsGridProfileNumerators[2]! bjsGridSemantic3 bjsGridProfileCheck3
theorem bjsGridHat4 : ∀ s ∈ closedDomain 2 4, layer 2 4 s ≤
 2*exp 2*((bjsGridProfileNumerators[3]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 4 bjsGridRow4 bjsGridProfileNumerators[3]! bjsGridSemantic4 bjsGridProfileCheck4
theorem bjsGridHat5 : ∀ s ∈ closedDomain 2 5, layer 2 5 s ≤
 2*exp 2*((bjsGridProfileNumerators[4]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 5 bjsGridRow5 bjsGridProfileNumerators[4]! bjsGridSemantic5 bjsGridProfileCheck5
theorem bjsGridHat6 : ∀ s ∈ closedDomain 2 6, layer 2 6 s ≤
 2*exp 2*((bjsGridProfileNumerators[5]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 6 bjsGridRow6 bjsGridProfileNumerators[5]! bjsGridSemantic6 bjsGridProfileCheck6
theorem bjsGridHat7 : ∀ s ∈ closedDomain 2 7, layer 2 7 s ≤
 2*exp 2*((bjsGridProfileNumerators[6]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 7 bjsGridRow7 bjsGridProfileNumerators[6]! bjsGridSemantic7 bjsGridProfileCheck7
theorem bjsGridHat8 : ∀ s ∈ closedDomain 2 8, layer 2 8 s ≤
 2*exp 2*((bjsGridProfileNumerators[7]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 8 bjsGridRow8 bjsGridProfileNumerators[7]! bjsGridSemantic8 bjsGridProfileCheck8
theorem bjsGridHat9 : ∀ s ∈ closedDomain 2 9, layer 2 9 s ≤
 2*exp 2*((bjsGridProfileNumerators[8]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 9 bjsGridRow9 bjsGridProfileNumerators[8]! bjsGridSemantic9 bjsGridProfileCheck9
theorem bjsGridHat10 : ∀ s ∈ closedDomain 2 10, layer 2 10 s ≤
 2*exp 2*((bjsGridProfileNumerators[9]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 10 bjsGridRow10 bjsGridProfileNumerators[9]! bjsGridSemantic10 bjsGridProfileCheck10
theorem bjsGridHat11 : ∀ s ∈ closedDomain 2 11, layer 2 11 s ≤
 2*exp 2*((bjsGridProfileNumerators[10]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 11 bjsGridRow11 bjsGridProfileNumerators[10]! bjsGridSemantic11 bjsGridProfileCheck11
theorem bjsGridHat12 : ∀ s ∈ closedDomain 2 12, layer 2 12 s ≤
 2*exp 2*((bjsGridProfileNumerators[11]! : ℝ)/1000000)*sieveHat s :=
 bjsStudy_grid_hat_profile 12 bjsGridRow12 bjsGridProfileNumerators[11]! bjsGridSemantic12 bjsGridProfileCheck12

def bjsSharpProfile (n : ℕ) : ℝ :=
  if n ≤ 12 then (bjsGridProfileNumerators[n-1]! : ℝ)/1000000
  else (7417/1000000 : ℝ)*(241/250 : ℝ)^(n-12)

theorem bjsSharpProfile_nonneg (n : ℕ) : 0 ≤ bjsSharpProfile n := by
  unfold bjsSharpProfile
  split <;> positivity

theorem bjsSharpProfile_step {n : ℕ} (hn : 12 ≤ n) :
    bjsSharpProfile (n+1)=bjsSharpProfile n*(241/250 : ℝ) := by
  by_cases he : n=12
  · subst n
    norm_num [bjsSharpProfile,bjsGridProfileNumerators]
  · have hgt : ¬n≤12 := by omega
    have hs : ¬n+1≤12 := by omega
    simp only [bjsSharpProfile,if_neg hgt,if_neg hs]
    rw [show n+1-12=(n-12)+1 by omega,pow_succ]
    ring

theorem bjsSharpProfile_early {n : ℕ} (hn : 1 ≤ n) (hu : n ≤ 12) :
    ∀ s ∈ closedDomain 2 n, layer 2 n s ≤ 2*exp 2*bjsSharpProfile n*sieveHat s := by
  interval_cases n
  · simpa [bjsSharpProfile] using bjsGridHat1
  · simpa [bjsSharpProfile] using bjsGridHat2
  · simpa [bjsSharpProfile] using bjsGridHat3
  · simpa [bjsSharpProfile] using bjsGridHat4
  · simpa [bjsSharpProfile] using bjsGridHat5
  · simpa [bjsSharpProfile] using bjsGridHat6
  · simpa [bjsSharpProfile] using bjsGridHat7
  · simpa [bjsSharpProfile] using bjsGridHat8
  · simpa [bjsSharpProfile] using bjsGridHat9
  · simpa [bjsSharpProfile] using bjsGridHat10
  · simpa [bjsSharpProfile] using bjsGridHat11
  · simpa [bjsSharpProfile] using bjsGridHat12

theorem bjsSharpProfile_bound (n : ℕ) :
    ∀ s ∈ closedDomain 2 n, layer 2 n s ≤ 2*exp 2*bjsSharpProfile n*sieveHat s := by
  induction n with
  | zero =>
    intro s _
    simp only [layer]
    have hh := (sieveHat_pos s).le
    have hp := bjsSharpProfile_nonneg 0
    positivity
  | succ n ih =>
    by_cases hn : n+1≤12
    · exact bjsSharpProfile_early (by omega) hn
    · have hn12 : 12≤n := by omega
      have hh := bjsStudy_layer_hat_step (by omega : 0<n) (bjsSharpProfile_nonneg n) ih
      simpa only [bjsSharpProfile_step hn12] using hh

#print axioms bjsSharpProfile_bound
end ChenEffective
