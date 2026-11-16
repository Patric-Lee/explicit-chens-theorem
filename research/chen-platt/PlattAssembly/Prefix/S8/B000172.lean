import PlattAssemblyKernel
import PlattCertificates.Count131072.C075504
import PlattCertificates.Count131072.C075505
import PlattCertificates.Count131072.C075506
import PlattCertificates.Count131072.C075507
import PlattCertificates.Count131072.C075508
import PlattCertificates.Count131072.C075509
import PlattCertificates.Count131072.C075510
import PlattCertificates.Count131072.C075511
import PlattCertificates.Count131072.C075512
import PlattCertificates.Count131072.C075513
import PlattCertificates.Count131072.C075514
import PlattCertificates.Count131072.C075515
import PlattCertificates.Count131072.C075516
import PlattCertificates.Count131072.C075517
import PlattCertificates.Count131072.C075518
import PlattCertificates.Count131072.C075519
import PlattCertificates.Count131072.C075520
import PlattCertificates.Count131072.C075521
import PlattCertificates.Count131072.C075522
import PlattCertificates.Count131072.C075523
import PlattCertificates.Count131072.C075524
import PlattCertificates.Count131072.C075525
import PlattCertificates.Count131072.C075526
import PlattCertificates.Count131072.C075527
import PlattCertificates.Count131072.C075528
import PlattCertificates.Count131072.C075529
import PlattCertificates.Count131072.C075530
import PlattCertificates.Count131072.C075531
import PlattCertificates.Count131072.C075532
import PlattCertificates.Count131072.C075533
import PlattCertificates.Count131072.C075534
import PlattCertificates.Count131072.C075535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75504 : List PrefixCut := [⟨64,162167523,162167621⟩]
theorem checked75504 : checkPrefixCuts (2^48) 9900392449 10 Manual.Count131072.C075504.packed 64 cuts75504 = true := by
 decide +kernel
def cuts75505 : List PrefixCut := [⟨64,161767358,161767460⟩]
theorem checked75505 : checkPrefixCuts (2^48) 9900523521 10 Manual.Count131072.C075505.packed 64 cuts75505 = true := by
 decide +kernel
def cuts75506 : List PrefixCut := [⟨19,47790613,47790643⟩,
⟨64,162873973,162874074⟩]
theorem checked75506 : checkPrefixCuts (2^48) 9900654593 10 Manual.Count131072.C075506.packed 64 cuts75506 = true := by
 decide +kernel
def pointBounds75506 : List (Nat × Nat × Nat) := [(9900693504,116740986163621,116741376220439)]
theorem point_links_checked75506 : (cuts75506.take 1).map (fun c => (9900654593-1+2*2^10*c.k,116740938373008+c.lower,116741328429796+c.upper)) = pointBounds75506 := by
 decide +kernel
def cuts75507 : List PrefixCut := [⟨64,159602449,159602544⟩]
theorem checked75507 : checkPrefixCuts (2^48) 9900785665 10 Manual.Count131072.C075507.packed 64 cuts75507 = true := by
 decide +kernel
def cuts75508 : List PrefixCut := [⟨43,108286250,108286313⟩,
⟨64,161647219,161647318⟩]
theorem checked75508 : checkPrefixCuts (2^48) 9900916737 10 Manual.Count131072.C075508.packed 64 cuts75508 = true := by
 decide +kernel
def pointBounds75508 : List (Nat × Nat × Nat) := [(9901004800,116741369135680,116741759192727)]
theorem point_links_checked75508 : (cuts75508.take 1).map (fun c => (9900916737-1+2*2^10*c.k,116741260849430+c.lower,116741650906414+c.upper)) = pointBounds75508 := by
 decide +kernel
def cuts75509 : List PrefixCut := [⟨64,164345800,164345904⟩]
theorem checked75509 : checkPrefixCuts (2^48) 9901047809 10 Manual.Count131072.C075509.packed 64 cuts75509 = true := by
 decide +kernel
def cuts75510 : List PrefixCut := [⟨64,159397114,159397205⟩]
theorem checked75510 : checkPrefixCuts (2^48) 9901178881 10 Manual.Count131072.C075510.packed 64 cuts75510 = true := by
 decide +kernel
def cuts75511 : List PrefixCut := [⟨3,7703998,7704003⟩,
⟨64,163005339,163005438⟩]
theorem checked75511 : checkPrefixCuts (2^48) 9901309953 10 Manual.Count131072.C075511.packed 64 cuts75511 = true := by
 decide +kernel
def pointBounds75511 : List (Nat × Nat × Nat) := [(9901316096,116741753943561,116742144000844)]
theorem point_links_checked75511 : (cuts75511.take 1).map (fun c => (9901309953-1+2*2^10*c.k,116741746239563+c.lower,116742136296841+c.upper)) = pointBounds75511 := by
 decide +kernel
def cuts75512 : List PrefixCut := [⟨64,160615277,160615377⟩]
theorem checked75512 : checkPrefixCuts (2^48) 9901441025 10 Manual.Count131072.C075512.packed 64 cuts75512 = true := by
 decide +kernel
def cuts75513 : List PrefixCut := [⟨27,69589820,69589859⟩,
⟨64,161295403,161295495⟩]
theorem checked75513 : checkPrefixCuts (2^48) 9901572097 10 Manual.Count131072.C075513.packed 64 cuts75513 = true := by
 decide +kernel
def pointBounds75513 : List (Nat × Nat × Nat) := [(9901627392,116742139449999,116742529507515)]
theorem point_links_checked75513 : (cuts75513.take 1).map (fun c => (9901572097-1+2*2^10*c.k,116742069860179+c.lower,116742459917656+c.upper)) = pointBounds75513 := by
 decide +kernel
def cuts75514 : List PrefixCut := [⟨64,162430337,162430432⟩]
theorem checked75514 : checkPrefixCuts (2^48) 9901703169 10 Manual.Count131072.C075514.packed 64 cuts75514 = true := by
 decide +kernel
def cuts75515 : List PrefixCut := [⟨51,128998957,128999039⟩,
⟨64,161546959,161547061⟩]
theorem checked75515 : checkPrefixCuts (2^48) 9901834241 10 Manual.Count131072.C075515.packed 64 cuts75515 = true := by
 decide +kernel
def pointBounds75515 : List (Nat × Nat × Nat) := [(9901938688,116742522584876,116742912642622)]
theorem point_links_checked75515 : (cuts75515.take 1).map (fun c => (9901834241-1+2*2^10*c.k,116742393585919+c.lower,116742783643583+c.upper)) = pointBounds75515 := by
 decide +kernel
def cuts75516 : List PrefixCut := [⟨64,163506215,163506318⟩]
theorem checked75516 : checkPrefixCuts (2^48) 9901965313 10 Manual.Count131072.C075516.packed 64 cuts75516 = true := by
 decide +kernel
def cuts75517 : List PrefixCut := [⟨64,161969075,161969166⟩]
theorem checked75517 : checkPrefixCuts (2^48) 9902096385 10 Manual.Count131072.C075517.packed 64 cuts75517 = true := by
 decide +kernel
def cuts75518 : List PrefixCut := [⟨11,28226399,28226419⟩,
⟨64,160773065,160773159⟩]
theorem checked75518 : checkPrefixCuts (2^48) 9902227457 10 Manual.Count131072.C075518.packed 64 cuts75518 = true := by
 decide +kernel
def pointBounds75518 : List (Nat × Nat × Nat) := [(9902249984,116742908834567,116743298892547)]
theorem point_links_checked75518 : (cuts75518.take 1).map (fun c => (9902227457-1+2*2^10*c.k,116742880608168+c.lower,116743270666128+c.upper)) = pointBounds75518 := by
 decide +kernel
def cuts75519 : List PrefixCut := [⟨64,161225730,161225828⟩]
theorem checked75519 : checkPrefixCuts (2^48) 9902358529 10 Manual.Count131072.C075519.packed 64 cuts75519 = true := by
 decide +kernel
def cuts75520 : List PrefixCut := [⟨35,89622626,89622680⟩,
⟨64,163355439,163355535⟩]
theorem checked75520 : checkPrefixCuts (2^48) 9902489601 10 Manual.Count131072.C075520.packed 64 cuts75520 = true := by
 decide +kernel
def pointBounds75520 : List (Nat × Nat × Nat) := [(9902561280,116743292229589,116743682287795)]
theorem point_links_checked75520 : (cuts75520.take 1).map (fun c => (9902489601-1+2*2^10*c.k,116743202606963+c.lower,116743592665115+c.upper)) = pointBounds75520 := by
 decide +kernel
def cuts75521 : List PrefixCut := [⟨64,161249895,161249987⟩]
theorem checked75521 : checkPrefixCuts (2^48) 9902620673 10 Manual.Count131072.C075521.packed 64 cuts75521 = true := by
 decide +kernel
def cuts75522 : List PrefixCut := [⟨59,149736218,149736308⟩,
⟨64,162498391,162498487⟩]
theorem checked75522 : checkPrefixCuts (2^48) 9902751745 10 Manual.Count131072.C075522.packed 64 cuts75522 = true := by
 decide +kernel
def pointBounds75522 : List (Nat × Nat × Nat) := [(9902872576,116743676948515,116744067006945)]
theorem point_links_checked75522 : (cuts75522.take 1).map (fun c => (9902751745-1+2*2^10*c.k,116743527212297+c.lower,116743917270637+c.upper)) = pointBounds75522 := by
 decide +kernel
def cuts75523 : List PrefixCut := [⟨64,162951022,162951118⟩]
theorem checked75523 : checkPrefixCuts (2^48) 9902882817 10 Manual.Count131072.C075523.packed 64 cuts75523 = true := by
 decide +kernel
def cuts75524 : List PrefixCut := [⟨64,160675024,160675124⟩]
theorem checked75524 : checkPrefixCuts (2^48) 9903013889 10 Manual.Count131072.C075524.packed 64 cuts75524 = true := by
 decide +kernel
def cuts75525 : List PrefixCut := [⟨19,47238561,47238593⟩,
⟨64,159905491,159905590⟩]
theorem checked75525 : checkPrefixCuts (2^48) 9903144961 10 Manual.Count131072.C075525.packed 64 cuts75525 = true := by
 decide +kernel
def pointBounds75525 : List (Nat × Nat × Nat) := [(9903183872,116744060575295,116744450633959)]
theorem point_links_checked75525 : (cuts75525.take 1).map (fun c => (9903144961-1+2*2^10*c.k,116744013336734+c.lower,116744403395366+c.upper)) = pointBounds75525 := by
 decide +kernel
def cuts75526 : List PrefixCut := [⟨64,161495018,161495119⟩]
theorem checked75526 : checkPrefixCuts (2^48) 9903276033 10 Manual.Count131072.C075526.packed 64 cuts75526 = true := by
 decide +kernel
def cuts75527 : List PrefixCut := [⟨43,108742188,108742259⟩,
⟨64,161947634,161947735⟩]
theorem checked75527 : checkPrefixCuts (2^48) 9903407105 10 Manual.Count131072.C075527.packed 64 cuts75527 = true := by
 decide +kernel
def pointBounds75527 : List (Nat × Nat × Nat) := [(9903495168,116744443479431,116744833538334)]
theorem point_links_checked75527 : (cuts75527.take 1).map (fun c => (9903407105-1+2*2^10*c.k,116744334737243+c.lower,116744724796075+c.upper)) = pointBounds75527 := by
 decide +kernel
def cuts75528 : List PrefixCut := [⟨64,161888655,161888748⟩]
theorem checked75528 : checkPrefixCuts (2^48) 9903538177 10 Manual.Count131072.C075528.packed 64 cuts75528 = true := by
 decide +kernel
def cuts75529 : List PrefixCut := [⟨64,163222286,163222389⟩]
theorem checked75529 : checkPrefixCuts (2^48) 9903669249 10 Manual.Count131072.C075529.packed 64 cuts75529 = true := by
 decide +kernel
def cuts75530 : List PrefixCut := [⟨3,7190485,7190489⟩,
⟨64,160037001,160037094⟩]
theorem checked75530 : checkPrefixCuts (2^48) 9903800321 10 Manual.Count131072.C075530.packed 64 cuts75530 = true := by
 decide +kernel
def pointBounds75530 : List (Nat × Nat × Nat) := [(9903806464,116744828986303,116745219045436)]
theorem point_links_checked75530 : (cuts75530.take 1).map (fun c => (9903800321-1+2*2^10*c.k,116744821795818+c.lower,116745211854947+c.upper)) = pointBounds75530 := by
 decide +kernel
def cuts75531 : List PrefixCut := [⟨64,160347522,160347622⟩]
theorem checked75531 : checkPrefixCuts (2^48) 9903931393 10 Manual.Count131072.C075531.packed 64 cuts75531 = true := by
 decide +kernel
def cuts75532 : List PrefixCut := [⟨27,68264999,68265038⟩,
⟨64,160970636,160970732⟩]
theorem checked75532 : checkPrefixCuts (2^48) 9904062465 10 Manual.Count131072.C075532.packed 64 cuts75532 = true := by
 decide +kernel
def pointBounds75532 : List (Nat × Nat × Nat) := [(9904117760,116745210445340,116745600504701)]
theorem point_links_checked75532 : (cuts75532.take 1).map (fun c => (9904062465-1+2*2^10*c.k,116745142180341+c.lower,116745532239663+c.upper)) = pointBounds75532 := by
 decide +kernel
def cuts75533 : List PrefixCut := [⟨64,160059085,160059183⟩]
theorem checked75533 : checkPrefixCuts (2^48) 9904193537 10 Manual.Count131072.C075533.packed 64 cuts75533 = true := by
 decide +kernel
def cuts75534 : List PrefixCut := [⟨51,128312891,128312962⟩,
⟨64,161961052,161961143⟩]
theorem checked75534 : checkPrefixCuts (2^48) 9904324609 10 Manual.Count131072.C075534.packed 64 cuts75534 = true := by
 decide +kernel
def pointBounds75534 : List (Nat × Nat × Nat) := [(9904429056,116745591522953,116745981582540)]
theorem point_links_checked75534 : (cuts75534.take 1).map (fun c => (9904324609-1+2*2^10*c.k,116745463210062+c.lower,116745853269578+c.upper)) = pointBounds75534 := by
 decide +kernel
def cuts75535 : List PrefixCut := [⟨64,161276852,161276945⟩]
theorem checked75535 : checkPrefixCuts (2^48) 9904455681 10 Manual.Count131072.C075535.packed 64 cuts75535 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000172
