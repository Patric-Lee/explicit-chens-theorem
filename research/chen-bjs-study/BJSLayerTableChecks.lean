import BJSGridCertificate
namespace ChenEffective
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.KappaOneModel
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 512
theorem bjsGridBaseCheck : ∀ i : Fin 97, 32 ≤ i.val → 1000000000000*(96-i.val) ≤ i.val*bjsGridRow1[i.val]! := by decide
theorem bjsGridStepCheck2 : BJSGridStepChecks 1 bjsGridRow1 bjsGridRow2 bjsGridTail2 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck3 : BJSGridStepChecks 2 bjsGridRow2 bjsGridRow3 bjsGridTail3 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck4 : BJSGridStepChecks 3 bjsGridRow3 bjsGridRow4 bjsGridTail4 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck5 : BJSGridStepChecks 4 bjsGridRow4 bjsGridRow5 bjsGridTail5 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck6 : BJSGridStepChecks 5 bjsGridRow5 bjsGridRow6 bjsGridTail6 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck7 : BJSGridStepChecks 6 bjsGridRow6 bjsGridRow7 bjsGridTail7 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck8 : BJSGridStepChecks 7 bjsGridRow7 bjsGridRow8 bjsGridTail8 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck9 : BJSGridStepChecks 8 bjsGridRow8 bjsGridRow9 bjsGridTail9 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck10 : BJSGridStepChecks 9 bjsGridRow9 bjsGridRow10 bjsGridTail10 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck11 : BJSGridStepChecks 10 bjsGridRow10 bjsGridRow11 bjsGridTail11 := by unfold BJSGridStepChecks; decide
theorem bjsGridStepCheck12 : BJSGridStepChecks 11 bjsGridRow11 bjsGridRow12 bjsGridTail12 := by unfold BJSGridStepChecks; decide
theorem bjsGridProfileCheck1 : ∀ i : Fin 96, 32 ≤ i.val →
 bjsGridRow1[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[0]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck2 : ∀ i : Fin 128, 64 ≤ i.val →
 bjsGridRow2[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[1]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck3 : ∀ i : Fin 160, 32 ≤ i.val →
 bjsGridRow3[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[2]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck4 : ∀ i : Fin 192, 64 ≤ i.val →
 bjsGridRow4[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[3]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck5 : ∀ i : Fin 224, 32 ≤ i.val →
 bjsGridRow5[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[4]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck6 : ∀ i : Fin 256, 64 ≤ i.val →
 bjsGridRow6[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[5]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck7 : ∀ i : Fin 288, 32 ≤ i.val →
 bjsGridRow7[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[6]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck8 : ∀ i : Fin 320, 64 ≤ i.val →
 bjsGridRow8[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[7]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck9 : ∀ i : Fin 352, 32 ≤ i.val →
 bjsGridRow9[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[8]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck10 : ∀ i : Fin 384, 64 ≤ i.val →
 bjsGridRow10[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[9]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck11 : ∀ i : Fin 416, 32 ≤ i.val →
 bjsGridRow11[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[10]! * 63^(i.val+1-64) := by decide
theorem bjsGridProfileCheck12 : ∀ i : Fin 448, 64 ≤ i.val →
 bjsGridRow12[i.val]! * max 96 (i.val+1) * 65^(i.val+1-64) * 1000000 ≤
 6*32*1000000000000*bjsGridProfileNumerators[11]! * 63^(i.val+1-64) := by decide
end ChenEffective
