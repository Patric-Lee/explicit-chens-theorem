import PlattAssemblyKernel
import PlattCertificates.Count131072.C051504
import PlattCertificates.Count131072.C051505
import PlattCertificates.Count131072.C051506
import PlattCertificates.Count131072.C051507
import PlattCertificates.Count131072.C051508
import PlattCertificates.Count131072.C051509
import PlattCertificates.Count131072.C051510
import PlattCertificates.Count131072.C051511
import PlattCertificates.Count131072.C051512
import PlattCertificates.Count131072.C051513
import PlattCertificates.Count131072.C051514
import PlattCertificates.Count131072.C051515
import PlattCertificates.Count131072.C051516
import PlattCertificates.Count131072.C051517
import PlattCertificates.Count131072.C051518
import PlattCertificates.Count131072.C051519
import PlattCertificates.Count131072.C051520
import PlattCertificates.Count131072.C051521
import PlattCertificates.Count131072.C051522
import PlattCertificates.Count131072.C051523
import PlattCertificates.Count131072.C051524
import PlattCertificates.Count131072.C051525
import PlattCertificates.Count131072.C051526
import PlattCertificates.Count131072.C051527
import PlattCertificates.Count131072.C051528
import PlattCertificates.Count131072.C051529
import PlattCertificates.Count131072.C051530
import PlattCertificates.Count131072.C051531
import PlattCertificates.Count131072.C051532
import PlattCertificates.Count131072.C051533
import PlattCertificates.Count131072.C051534
import PlattCertificates.Count131072.C051535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51504 : List PrefixCut := [⟨64,241732210,241732350⟩]
theorem checked51504 : checkPrefixCuts (2^48) 6754664449 10 Manual.Count131072.C051504.packed 64 cuts51504 = true := by
 decide +kernel
def cuts51505 : List PrefixCut := [⟨35,133844558,133844633⟩,
⟨64,242435935,242436071⟩]
theorem checked51505 : checkPrefixCuts (2^48) 6754795521 10 Manual.Count131072.C051505.packed 64 cuts51505 = true := by
 decide +kernel
def pointBounds51505 : List (Nat × Nat × Nat) := [(6754867200,112025831282496,112026218614375)]
theorem point_links_checked51505 : (cuts51505.take 1).map (fun c => (6754795521-1+2*2^10*c.k,112025697437938+c.lower,112026084769742+c.upper)) = pointBounds51505 := by
 decide +kernel
def cuts51506 : List PrefixCut := [⟨64,237764275,237764413⟩]
theorem checked51506 : checkPrefixCuts (2^48) 6754926593 10 Manual.Count131072.C051506.packed 64 cuts51506 = true := by
 decide +kernel
def cuts51507 : List PrefixCut := [⟨11,41585357,41585381⟩,
⟨64,242218169,242218307⟩]
theorem checked51507 : checkPrefixCuts (2^48) 6755057665 10 Manual.Count131072.C051507.packed 64 cuts51507 = true := by
 decide +kernel
def pointBounds51507 : List (Nat × Nat × Nat) := [(6755080192,112026219223505,112026606555607)]
theorem point_links_checked51507 : (cuts51507.take 1).map (fun c => (6755057665-1+2*2^10*c.k,112026177638148+c.lower,112026564970226+c.upper)) = pointBounds51507 := by
 decide +kernel
def cuts51508 : List PrefixCut := [⟨51,194337843,194337955⟩,
⟨64,243380172,243380312⟩]
theorem checked51508 : checkPrefixCuts (2^48) 6755188737 10 Manual.Count131072.C051508.packed 64 cuts51508 = true := by
 decide +kernel
def pointBounds51508 : List (Nat × Nat × Nat) := [(6755293184,112026614194160,112027001526488)]
theorem point_links_checked51508 : (cuts51508.take 1).map (fun c => (6755188737-1+2*2^10*c.k,112026419856317+c.lower,112026807188533+c.upper)) = pointBounds51508 := by
 decide +kernel
def cuts51509 : List PrefixCut := [⟨64,241792099,241792237⟩]
theorem checked51509 : checkPrefixCuts (2^48) 6755319809 10 Manual.Count131072.C051509.packed 64 cuts51509 = true := by
 decide +kernel
def cuts51510 : List PrefixCut := [⟨27,99790465,99790524⟩,
⟨64,241204059,241204196⟩]
theorem checked51510 : checkPrefixCuts (2^48) 6755450881 10 Manual.Count131072.C051510.packed 64 cuts51510 = true := by
 decide +kernel
def pointBounds51510 : List (Nat × Nat × Nat) := [(6755506176,112027004819053,112027392151606)]
theorem point_links_checked51510 : (cuts51510.take 1).map (fun c => (6755450881-1+2*2^10*c.k,112026905028588+c.lower,112027292361082+c.upper)) = pointBounds51510 := by
 decide +kernel
def cuts51511 : List PrefixCut := [⟨64,241282752,241282887⟩]
theorem checked51511 : checkPrefixCuts (2^48) 6755581953 10 Manual.Count131072.C051511.packed 64 cuts51511 = true := by
 decide +kernel
def cuts51512 : List PrefixCut := [⟨3,11791110,11791116⟩,
⟨64,240736443,240736577⟩]
theorem checked51512 : checkPrefixCuts (2^48) 6755713025 10 Manual.Count131072.C051512.packed 64 cuts51512 = true := by
 decide +kernel
def pointBounds51512 : List (Nat × Nat × Nat) := [(6755719168,112027399306509,112027786639281)]
theorem point_links_checked51512 : (cuts51512.take 1).map (fun c => (6755713025-1+2*2^10*c.k,112027387515399+c.lower,112027774848165+c.upper)) = pointBounds51512 := by
 decide +kernel
def cuts51513 : List PrefixCut := [⟨43,164321398,164321491⟩,
⟨64,244356473,244356609⟩]
theorem checked51513 : checkPrefixCuts (2^48) 6755844097 10 Manual.Count131072.C051513.packed 64 cuts51513 = true := by
 decide +kernel
def pointBounds51513 : List (Nat × Nat × Nat) := [(6755932160,112027792573240,112028179906233)]
theorem point_links_checked51513 : (cuts51513.take 1).map (fun c => (6755844097-1+2*2^10*c.k,112027628251842+c.lower,112028015584742+c.upper)) = pointBounds51513 := by
 decide +kernel
def cuts51514 : List PrefixCut := [⟨64,244768358,244768495⟩]
theorem checked51514 : checkPrefixCuts (2^48) 6755975169 10 Manual.Count131072.C051514.packed 64 cuts51514 = true := by
 decide +kernel
def cuts51515 : List PrefixCut := [⟨19,70325753,70325791⟩,
⟨64,240180779,240180915⟩]
theorem checked51515 : checkPrefixCuts (2^48) 6756106241 10 Manual.Count131072.C051515.packed 64 cuts51515 = true := by
 decide +kernel
def pointBounds51515 : List (Nat × Nat × Nat) := [(6756145152,112028187702426,112028575035637)]
theorem point_links_checked51515 : (cuts51515.take 1).map (fun c => (6756106241-1+2*2^10*c.k,112028117376673+c.lower,112028504709846+c.upper)) = pointBounds51515 := by
 decide +kernel
def cuts51516 : List PrefixCut := [⟨59,223636882,223637005⟩,
⟨64,242175898,242176032⟩]
theorem checked51516 : checkPrefixCuts (2^48) 6756237313 10 Manual.Count131072.C051516.packed 64 cuts51516 = true := by
 decide +kernel
def pointBounds51516 : List (Nat × Nat × Nat) := [(6756358144,112028581194334,112028968527766)]
theorem point_links_checked51516 : (cuts51516.take 1).map (fun c => (6756237313-1+2*2^10*c.k,112028357557452+c.lower,112028744890761+c.upper)) = pointBounds51516 := by
 decide +kernel
def cuts51517 : List PrefixCut := [⟨64,239504941,239505075⟩]
theorem checked51517 : checkPrefixCuts (2^48) 6756368385 10 Manual.Count131072.C051517.packed 64 cuts51517 = true := by
 decide +kernel
def cuts51518 : List PrefixCut := [⟨35,129728146,129728220⟩,
⟨64,237875557,237875692⟩]
theorem checked51518 : checkPrefixCuts (2^48) 6756499457 10 Manual.Count131072.C051518.packed 64 cuts51518 = true := by
 decide +kernel
def pointBounds51518 : List (Nat × Nat × Nat) := [(6756571136,112028968966437,112029356300088)]
theorem point_links_checked51518 : (cuts51518.take 1).map (fun c => (6756499457-1+2*2^10*c.k,112028839238291+c.lower,112029226571868+c.upper)) = pointBounds51518 := by
 decide +kernel
def cuts51519 : List PrefixCut := [⟨64,244744629,244744764⟩]
theorem checked51519 : checkPrefixCuts (2^48) 6756630529 10 Manual.Count131072.C051519.packed 64 cuts51519 = true := by
 decide +kernel
def cuts51520 : List PrefixCut := [⟨11,42491352,42491375⟩,
⟨64,242615348,242615483⟩]
theorem checked51520 : checkPrefixCuts (2^48) 6756761601 10 Manual.Count131072.C051520.packed 64 cuts51520 = true := by
 decide +kernel
def pointBounds51520 : List (Nat × Nat × Nat) := [(6756784128,112029364349829,112029751683699)]
theorem point_links_checked51520 : (cuts51520.take 1).map (fun c => (6756761601-1+2*2^10*c.k,112029321858477+c.lower,112029709192324+c.upper)) = pointBounds51520 := by
 decide +kernel
def cuts51521 : List PrefixCut := [⟨51,189081675,189081785⟩,
⟨64,236861935,236862072⟩]
theorem checked51521 : checkPrefixCuts (2^48) 6756892673 10 Manual.Count131072.C051521.packed 64 cuts51521 = true := by
 decide +kernel
def pointBounds51521 : List (Nat × Nat × Nat) := [(6756997120,112029753555500,112030140889592)]
theorem point_links_checked51521 : (cuts51521.take 1).map (fun c => (6756892673-1+2*2^10*c.k,112029564473825+c.lower,112029951807807+c.upper)) = pointBounds51521 := by
 decide +kernel
def cuts51522 : List PrefixCut := [⟨64,242147677,242147815⟩]
theorem checked51522 : checkPrefixCuts (2^48) 6757023745 10 Manual.Count131072.C051522.packed 64 cuts51522 = true := by
 decide +kernel
def cuts51523 : List PrefixCut := [⟨27,101848092,101848147⟩,
⟨64,239643674,239643806⟩]
theorem checked51523 : checkPrefixCuts (2^48) 6757154817 10 Manual.Count131072.C051523.packed 64 cuts51523 = true := by
 decide +kernel
def pointBounds51523 : List (Nat × Nat × Nat) := [(6757210112,112030145331529,112030532665841)]
theorem point_links_checked51523 : (cuts51523.take 1).map (fun c => (6757154817-1+2*2^10*c.k,112030043483437+c.lower,112030430817694+c.upper)) = pointBounds51523 := by
 decide +kernel
def cuts51524 : List PrefixCut := [⟨64,236473286,236473423⟩]
theorem checked51524 : checkPrefixCuts (2^48) 6757285889 10 Manual.Count131072.C051524.packed 64 cuts51524 = true := by
 decide +kernel
def cuts51525 : List PrefixCut := [⟨3,10913400,10913406⟩,
⟨64,242341862,242342001⟩]
theorem checked51525 : checkPrefixCuts (2^48) 6757416961 10 Manual.Count131072.C051525.packed 64 cuts51525 = true := by
 decide +kernel
def pointBounds51525 : List (Nat × Nat × Nat) := [(6757423104,112030530513797,112030917848329)]
theorem point_links_checked51525 : (cuts51525.take 1).map (fun c => (6757416961-1+2*2^10*c.k,112030519600397+c.lower,112030906934923+c.upper)) = pointBounds51525 := by
 decide +kernel
def cuts51526 : List PrefixCut := [⟨43,162947058,162947151⟩,
⟨64,241212539,241212678⟩]
theorem checked51526 : checkPrefixCuts (2^48) 6757548033 10 Manual.Count131072.C051526.packed 64 cuts51526 = true := by
 decide +kernel
def pointBounds51526 : List (Nat × Nat × Nat) := [(6757636096,112030924889317,112031312224075)]
theorem point_links_checked51526 : (cuts51526.take 1).map (fun c => (6757548033-1+2*2^10*c.k,112030761942259+c.lower,112031149276924+c.upper)) = pointBounds51526 := by
 decide +kernel
def cuts51527 : List PrefixCut := [⟨64,242790633,242790773⟩]
theorem checked51527 : checkPrefixCuts (2^48) 6757679105 10 Manual.Count131072.C051527.packed 64 cuts51527 = true := by
 decide +kernel
def cuts51528 : List PrefixCut := [⟨19,70599580,70599618⟩,
⟨64,242036201,242036338⟩]
theorem checked51528 : checkPrefixCuts (2^48) 6757810177 10 Manual.Count131072.C051528.packed 64 cuts51528 = true := by
 decide +kernel
def pointBounds51528 : List (Nat × Nat × Nat) := [(6757849088,112031316545011,112031703879993)]
theorem point_links_checked51528 : (cuts51528.take 1).map (fun c => (6757810177-1+2*2^10*c.k,112031245945431+c.lower,112031633280375+c.upper)) = pointBounds51528 := by
 decide +kernel
def cuts51529 : List PrefixCut := [⟨59,222497558,222497688⟩,
⟨64,241281802,241281942⟩]
theorem checked51529 : checkPrefixCuts (2^48) 6757941249 10 Manual.Count131072.C051529.packed 64 cuts51529 = true := by
 decide +kernel
def pointBounds51529 : List (Nat × Nat × Nat) := [(6758062080,112031710479190,112032097814401)]
theorem point_links_checked51529 : (cuts51529.take 1).map (fun c => (6757941249-1+2*2^10*c.k,112031487981632+c.lower,112031875316713+c.upper)) = pointBounds51529 := by
 decide +kernel
def cuts51530 : List PrefixCut := [⟨64,240902301,240902442⟩]
theorem checked51530 : checkPrefixCuts (2^48) 6758072321 10 Manual.Count131072.C051530.packed 64 cuts51530 = true := by
 decide +kernel
def cuts51531 : List PrefixCut := [⟨35,129903693,129903766⟩,
⟨64,240147907,240148042⟩]
theorem checked51531 : checkPrefixCuts (2^48) 6758203393 10 Manual.Count131072.C051531.packed 64 cuts51531 = true := by
 decide +kernel
def pointBounds51531 : List (Nat × Nat × Nat) := [(6758275072,112032100069428,112032487404863)]
theorem point_links_checked51531 : (cuts51531.take 1).map (fun c => (6758203393-1+2*2^10*c.k,112031970165735+c.lower,112032357501097+c.upper)) = pointBounds51531 := by
 decide +kernel
def cuts51532 : List PrefixCut := [⟨64,242642157,242642292⟩]
theorem checked51532 : checkPrefixCuts (2^48) 6758334465 10 Manual.Count131072.C051532.packed 64 cuts51532 = true := by
 decide +kernel
def cuts51533 : List PrefixCut := [⟨11,40856378,40856400⟩,
⟨64,244469933,244470068⟩]
theorem checked51533 : checkPrefixCuts (2^48) 6758465537 10 Manual.Count131072.C051533.packed 64 cuts51533 = true := by
 decide +kernel
def pointBounds51533 : List (Nat × Nat × Nat) := [(6758488064,112032493812177,112032881147831)]
theorem point_links_checked51533 : (cuts51533.take 1).map (fun c => (6758465537-1+2*2^10*c.k,112032452955799+c.lower,112032840291431+c.upper)) = pointBounds51533 := by
 decide +kernel
def cuts51534 : List PrefixCut := [⟨51,192115863,192115972⟩,
⟨64,240800292,240800430⟩]
theorem checked51534 : checkPrefixCuts (2^48) 6758596609 10 Manual.Count131072.C051534.packed 64 cuts51534 = true := by
 decide +kernel
def pointBounds51534 : List (Nat × Nat × Nat) := [(6758701056,112032889541595,112033276877471)]
theorem point_links_checked51534 : (cuts51534.take 1).map (fun c => (6758596609-1+2*2^10*c.k,112032697425732+c.lower,112033084761499+c.upper)) = pointBounds51534 := by
 decide +kernel
def cuts51535 : List PrefixCut := [⟨64,241045496,241045633⟩]
theorem checked51535 : checkPrefixCuts (2^48) 6758727681 10 Manual.Count131072.C051535.packed 64 cuts51535 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000047
