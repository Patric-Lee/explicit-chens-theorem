import PlattAssemblyKernel
import PlattCertificates.Count131072.C073520
import PlattCertificates.Count131072.C073521
import PlattCertificates.Count131072.C073522
import PlattCertificates.Count131072.C073523
import PlattCertificates.Count131072.C073524
import PlattCertificates.Count131072.C073525
import PlattCertificates.Count131072.C073526
import PlattCertificates.Count131072.C073527
import PlattCertificates.Count131072.C073528
import PlattCertificates.Count131072.C073529
import PlattCertificates.Count131072.C073530
import PlattCertificates.Count131072.C073531
import PlattCertificates.Count131072.C073532
import PlattCertificates.Count131072.C073533
import PlattCertificates.Count131072.C073534
import PlattCertificates.Count131072.C073535
import PlattCertificates.Count131072.C073536
import PlattCertificates.Count131072.C073537
import PlattCertificates.Count131072.C073538
import PlattCertificates.Count131072.C073539
import PlattCertificates.Count131072.C073540
import PlattCertificates.Count131072.C073541
import PlattCertificates.Count131072.C073542
import PlattCertificates.Count131072.C073543
import PlattCertificates.Count131072.C073544
import PlattCertificates.Count131072.C073545
import PlattCertificates.Count131072.C073546
import PlattCertificates.Count131072.C073547
import PlattCertificates.Count131072.C073548
import PlattCertificates.Count131072.C073549
import PlattCertificates.Count131072.C073550
import PlattCertificates.Count131072.C073551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73520 : List PrefixCut := [⟨64,166921510,166921610⟩]
theorem checked73520 : checkPrefixCuts (2^48) 9640345601 10 Manual.Count131072.C073520.packed 64 cuts73520 = true := by
 decide +kernel
def cuts73521 : List PrefixCut := [⟨64,166130912,166131011⟩]
theorem checked73521 : checkPrefixCuts (2^48) 9640476673 10 Manual.Count131072.C073521.packed 64 cuts73521 = true := by
 decide +kernel
def cuts73522 : List PrefixCut := [⟨6,15795457,15795468⟩,
⟨64,165836697,165836800⟩]
theorem checked73522 : checkPrefixCuts (2^48) 9640607745 10 Manual.Count131072.C073522.packed 64 cuts73522 = true := by
 decide +kernel
def pointBounds73522 : List (Nat × Nat × Nat) := [(9640620032,116415208676631,116415598538421)]
theorem point_links_checked73522 : (cuts73522.take 1).map (fun c => (9640607745-1+2*2^10*c.k,116415192881174+c.lower,116415582742953+c.upper)) = pointBounds73522 := by
 decide +kernel
def cuts73523 : List PrefixCut := [⟨64,167761391,167761492⟩]
theorem checked73523 : checkPrefixCuts (2^48) 9640738817 10 Manual.Count131072.C073523.packed 64 cuts73523 = true := by
 decide +kernel
def cuts73524 : List PrefixCut := [⟨26,67296606,67296648⟩,
⟨64,165248267,165248370⟩]
theorem checked73524 : checkPrefixCuts (2^48) 9640869889 10 Manual.Count131072.C073524.packed 64 cuts73524 = true := by
 decide +kernel
def pointBounds73524 : List (Nat × Nat × Nat) := [(9640923136,116415593775868,116415983637893)]
theorem point_links_checked73524 : (cuts73524.take 1).map (fun c => (9640869889-1+2*2^10*c.k,116415526479262+c.lower,116415916341245+c.upper)) = pointBounds73524 := by
 decide +kernel
def cuts73525 : List PrefixCut := [⟨64,163932225,163932320⟩]
theorem checked73525 : checkPrefixCuts (2^48) 9641000961 10 Manual.Count131072.C073525.packed 64 cuts73525 = true := by
 decide +kernel
def cuts73526 : List PrefixCut := [⟨46,120750804,120750876⟩,
⟨64,167842129,167842233⟩]
theorem checked73526 : checkPrefixCuts (2^48) 9641132033 10 Manual.Count131072.C073526.packed 64 cuts73526 = true := by
 decide +kernel
def pointBounds73526 : List (Nat × Nat × Nat) := [(9641226240,116415976410558,116416366272811)]
theorem point_links_checked73526 : (cuts73526.take 1).map (fun c => (9641132033-1+2*2^10*c.k,116415855659754+c.lower,116416245521935+c.upper)) = pointBounds73526 := by
 decide +kernel
def cuts73527 : List PrefixCut := [⟨64,165387504,165387610⟩]
theorem checked73527 : checkPrefixCuts (2^48) 9641263105 10 Manual.Count131072.C073527.packed 64 cuts73527 = true := by
 decide +kernel
def cuts73528 : List PrefixCut := [⟨64,165793978,165794077⟩]
theorem checked73528 : checkPrefixCuts (2^48) 9641394177 10 Manual.Count131072.C073528.packed 64 cuts73528 = true := by
 decide +kernel
def cuts73529 : List PrefixCut := [⟨2,4495878,4495881⟩,
⟨64,165645757,165645851⟩]
theorem checked73529 : checkPrefixCuts (2^48) 9641525249 10 Manual.Count131072.C073529.packed 64 cuts73529 = true := by
 decide +kernel
def pointBounds73529 : List (Nat × Nat × Nat) := [(9641529344,116416359179243,116416749041736)]
theorem point_links_checked73529 : (cuts73529.take 1).map (fun c => (9641525249-1+2*2^10*c.k,116416354683365+c.lower,116416744545855+c.upper)) = pointBounds73529 := by
 decide +kernel
def cuts73530 : List PrefixCut := [⟨64,166606891,166606985⟩]
theorem checked73530 : checkPrefixCuts (2^48) 9641656321 10 Manual.Count131072.C073530.packed 64 cuts73530 = true := by
 decide +kernel
def cuts73531 : List PrefixCut := [⟨22,57510522,57510559⟩,
⟨64,167159279,167159383⟩]
theorem checked73531 : checkPrefixCuts (2^48) 9641787393 10 Manual.Count131072.C073531.packed 64 cuts73531 = true := by
 decide +kernel
def pointBounds73531 : List (Nat × Nat × Nat) := [(9641832448,116416744446535,116417134309250)]
theorem point_links_checked73531 : (cuts73531.take 1).map (fun c => (9641787393-1+2*2^10*c.k,116416686936013+c.lower,116417076798691+c.upper)) = pointBounds73531 := by
 decide +kernel
def cuts73532 : List PrefixCut := [⟨64,165522233,165522330⟩]
theorem checked73532 : checkPrefixCuts (2^48) 9641918465 10 Manual.Count131072.C073532.packed 64 cuts73532 = true := by
 decide +kernel
def cuts73533 : List PrefixCut := [⟨42,110346910,110346975⟩,
⟨64,166804444,166804539⟩]
theorem checked73533 : checkPrefixCuts (2^48) 9642049537 10 Manual.Count131072.C073533.packed 64 cuts73533 = true := by
 decide +kernel
def pointBounds73533 : List (Nat × Nat × Nat) := [(9642135552,116417129964435,116417519827379)]
theorem point_links_checked73533 : (cuts73533.take 1).map (fun c => (9642049537-1+2*2^10*c.k,116417019617525+c.lower,116417409480404+c.upper)) = pointBounds73533 := by
 decide +kernel
def cuts73534 : List PrefixCut := [⟨64,166335089,166335195⟩]
theorem checked73534 : checkPrefixCuts (2^48) 9642180609 10 Manual.Count131072.C073534.packed 64 cuts73534 = true := by
 decide +kernel
def cuts73535 : List PrefixCut := [⟨62,160494579,160494671⟩,
⟨64,165603048,165603142⟩]
theorem checked73535 : checkPrefixCuts (2^48) 9642311681 10 Manual.Count131072.C073535.packed 64 cuts73535 = true := by
 decide +kernel
def pointBounds73535 : List (Nat × Nat × Nat) := [(9642438656,116417513251637,116417903114809)]
theorem point_links_checked73535 : (cuts73535.take 1).map (fun c => (9642311681-1+2*2^10*c.k,116417352757058+c.lower,116417742620138+c.upper)) = pointBounds73535 := by
 decide +kernel
def cuts73536 : List PrefixCut := [⟨64,167031155,167031254⟩]
theorem checked73536 : checkPrefixCuts (2^48) 9642442753 10 Manual.Count131072.C073536.packed 64 cuts73536 = true := by
 decide +kernel
def cuts73537 : List PrefixCut := [⟨64,166386693,166386799⟩]
theorem checked73537 : checkPrefixCuts (2^48) 9642573825 10 Manual.Count131072.C073537.packed 64 cuts73537 = true := by
 decide +kernel
def cuts73538 : List PrefixCut := [⟨18,46325152,46325183⟩,
⟨64,167639605,167639706⟩]
theorem checked73538 : checkPrefixCuts (2^48) 9642704897 10 Manual.Count131072.C073538.packed 64 cuts73538 = true := by
 decide +kernel
def pointBounds73538 : List (Nat × Nat × Nat) := [(9642741760,116417898103106,116418287966516)]
theorem point_links_checked73538 : (cuts73538.take 1).map (fun c => (9642704897-1+2*2^10*c.k,116417851777954+c.lower,116418241641333+c.upper)) = pointBounds73538 := by
 decide +kernel
def cuts73539 : List PrefixCut := [⟨64,166207027,166207132⟩]
theorem checked73539 : checkPrefixCuts (2^48) 9642835969 10 Manual.Count131072.C073539.packed 64 cuts73539 = true := by
 decide +kernel
def cuts73540 : List PrefixCut := [⟨38,98748216,98748271⟩,
⟨64,166204776,166204871⟩]
theorem checked73540 : checkPrefixCuts (2^48) 9642967041 10 Manual.Count131072.C073540.packed 64 cuts73540 = true := by
 decide +kernel
def pointBounds73540 : List (Nat × Nat × Nat) := [(9643044864,116418284372802,116418674236442)]
theorem point_links_checked73540 : (cuts73540.take 1).map (fun c => (9642967041-1+2*2^10*c.k,116418185624586+c.lower,116418575488171+c.upper)) = pointBounds73540 := by
 decide +kernel
def cuts73541 : List PrefixCut := [⟨64,165647931,165648026⟩]
theorem checked73541 : checkPrefixCuts (2^48) 9643098113 10 Manual.Count131072.C073541.packed 64 cuts73541 = true := by
 decide +kernel
def cuts73542 : List PrefixCut := [⟨58,149825503,149825589⟩,
⟨64,165324587,165324683⟩]
theorem checked73542 : checkPrefixCuts (2^48) 9643229185 10 Manual.Count131072.C073542.packed 64 cuts73542 = true := by
 decide +kernel
def pointBounds73542 : List (Nat × Nat × Nat) := [(9643347968,116418667302796,116419057166657)]
theorem point_links_checked73542 : (cuts73542.take 1).map (fun c => (9643229185-1+2*2^10*c.k,116418517477293+c.lower,116418907341068+c.upper)) = pointBounds73542 := by
 decide +kernel
def cuts73543 : List PrefixCut := [⟨64,167161213,167161306⟩]
theorem checked73543 : checkPrefixCuts (2^48) 9643360257 10 Manual.Count131072.C073543.packed 64 cuts73543 = true := by
 decide +kernel
def cuts73544 : List PrefixCut := [⟨64,165641159,165641266⟩]
theorem checked73544 : checkPrefixCuts (2^48) 9643491329 10 Manual.Count131072.C073544.packed 64 cuts73544 = true := by
 decide +kernel
def cuts73545 : List PrefixCut := [⟨14,34674902,34674926⟩,
⟨64,166018343,166018445⟩]
theorem checked73545 : checkPrefixCuts (2^48) 9643622401 10 Manual.Count131072.C073545.packed 64 cuts73545 = true := by
 decide +kernel
def pointBounds73545 : List (Nat × Nat × Nat) := [(9643651072,116419050279154,116419440143249)]
theorem point_links_checked73545 : (cuts73545.take 1).map (fun c => (9643622401-1+2*2^10*c.k,116419015604252+c.lower,116419405468323+c.upper)) = pointBounds73545 := by
 decide +kernel
def cuts73546 : List PrefixCut := [⟨64,168672130,168672227⟩]
theorem checked73546 : checkPrefixCuts (2^48) 9643753473 10 Manual.Count131072.C073546.packed 64 cuts73546 = true := by
 decide +kernel
def cuts73547 : List PrefixCut := [⟨34,87064146,87064194⟩,
⟨64,164525315,164525408⟩]
theorem checked73547 : checkPrefixCuts (2^48) 9643884545 10 Manual.Count131072.C073547.packed 64 cuts73547 = true := by
 decide +kernel
def pointBounds73547 : List (Nat × Nat × Nat) := [(9643954176,116419437358871,116419827223189)]
theorem point_links_checked73547 : (cuts73547.take 1).map (fun c => (9643884545-1+2*2^10*c.k,116419350294725+c.lower,116419740158995+c.upper)) = pointBounds73547 := by
 decide +kernel
def cuts73548 : List PrefixCut := [⟨64,167237405,167237496⟩]
theorem checked73548 : checkPrefixCuts (2^48) 9644015617 10 Manual.Count131072.C073548.packed 64 cuts73548 = true := by
 decide +kernel
def cuts73549 : List PrefixCut := [⟨54,140734496,140734579⟩,
⟨64,166651416,166651516⟩]
theorem checked73549 : checkPrefixCuts (2^48) 9644146689 10 Manual.Count131072.C073549.packed 64 cuts73549 = true := by
 decide +kernel
def pointBounds73549 : List (Nat × Nat × Nat) := [(9644257280,116419822791941,116420212656478)]
theorem point_links_checked73549 : (cuts73549.take 1).map (fun c => (9644146689-1+2*2^10*c.k,116419682057445+c.lower,116420071921899+c.upper)) = pointBounds73549 := by
 decide +kernel
def cuts73550 : List PrefixCut := [⟨64,167378803,167378899⟩]
theorem checked73550 : checkPrefixCuts (2^48) 9644277761 10 Manual.Count131072.C073550.packed 64 cuts73550 = true := by
 decide +kernel
def cuts73551 : List PrefixCut := [⟨64,164574744,164574848⟩]
theorem checked73551 : checkPrefixCuts (2^48) 9644408833 10 Manual.Count131072.C073551.packed 64 cuts73551 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000110
