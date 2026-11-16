import PlattAssemblyKernel
import PlattCertificates.Count131072.C068640
import PlattCertificates.Count131072.C068641
import PlattCertificates.Count131072.C068642
import PlattCertificates.Count131072.C068643
import PlattCertificates.Count131072.C068644
import PlattCertificates.Count131072.C068645
import PlattCertificates.Count131072.C068646
import PlattCertificates.Count131072.C068647
import PlattCertificates.Count131072.C068648
import PlattCertificates.Count131072.C068649
import PlattCertificates.Count131072.C068650
import PlattCertificates.Count131072.C068651
import PlattCertificates.Count131072.C068652
import PlattCertificates.Count131072.C068653
import PlattCertificates.Count131072.C068654
import PlattCertificates.Count131072.C068655
import PlattCertificates.Count131072.C068656
import PlattCertificates.Count131072.C068657
import PlattCertificates.Count131072.C068658
import PlattCertificates.Count131072.C068659
import PlattCertificates.Count131072.C068660
import PlattCertificates.Count131072.C068661
import PlattCertificates.Count131072.C068662
import PlattCertificates.Count131072.C068663
import PlattCertificates.Count131072.C068664
import PlattCertificates.Count131072.C068665
import PlattCertificates.Count131072.C068666
import PlattCertificates.Count131072.C068667
import PlattCertificates.Count131072.C068668
import PlattCertificates.Count131072.C068669
import PlattCertificates.Count131072.C068670
import PlattCertificates.Count131072.C068671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000270
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68640 : List PrefixCut := [⟨35,99665081,99665141⟩,
⟨64,179252715,179252821⟩]
theorem checked68640 : checkPrefixCuts (2^48) 9000714241 10 Manual.Count131072.C068640.packed 64 cuts68640 = true := by
 decide +kernel
def pointBounds68640 : List (Nat × Nat × Nat) := [(9000785920,115573111632025,115573500995908)]
theorem point_links_checked68640 : (cuts68640.take 1).map (fun c => (9000714241-1+2*2^10*c.k,115573011966944+c.lower,115573401330767+c.upper)) = pointBounds68640 := by
 decide +kernel
def cuts68641 : List PrefixCut := [⟨64,178186852,178186956⟩]
theorem checked68641 : checkPrefixCuts (2^48) 9000845313 10 Manual.Count131072.C068641.packed 64 cuts68641 = true := by
 decide +kernel
def cuts68642 : List PrefixCut := [⟨45,125304649,125304724⟩,
⟨64,176964684,176964788⟩]
theorem checked68642 : checkPrefixCuts (2^48) 9000976385 10 Manual.Count131072.C068642.packed 64 cuts68642 = true := by
 decide +kernel
def pointBounds68642 : List (Nat × Nat × Nat) := [(9001068544,115573494711160,115573884075268)]
theorem point_links_checked68642 : (cuts68642.take 1).map (fun c => (9000976385-1+2*2^10*c.k,115573369406511+c.lower,115573758770544+c.upper)) = pointBounds68642 := by
 decide +kernel
def cuts68643 : List PrefixCut := [⟨64,178994718,178994818⟩]
theorem checked68643 : checkPrefixCuts (2^48) 9001107457 10 Manual.Count131072.C068643.packed 64 cuts68643 = true := by
 decide +kernel
def cuts68644 : List PrefixCut := [⟨55,153225410,153225500⟩,
⟨64,178835754,178835860⟩]
theorem checked68644 : checkPrefixCuts (2^48) 9001238529 10 Manual.Count131072.C068644.packed 64 cuts68644 = true := by
 decide +kernel
def pointBounds68644 : List (Nat × Nat × Nat) := [(9001351168,115573878591323,115574267955650)]
theorem point_links_checked68644 : (cuts68644.take 1).map (fun c => (9001238529-1+2*2^10*c.k,115573725365913+c.lower,115574114730150+c.upper)) = pointBounds68644 := by
 decide +kernel
def cuts68645 : List PrefixCut := [⟨64,180584262,180584367⟩]
theorem checked68645 : checkPrefixCuts (2^48) 9001369601 10 Manual.Count131072.C068645.packed 64 cuts68645 = true := by
 decide +kernel
def cuts68646 : List PrefixCut := [⟨64,179018152,179018255⟩]
theorem checked68646 : checkPrefixCuts (2^48) 9001500673 10 Manual.Count131072.C068646.packed 64 cuts68646 = true := by
 decide +kernel
def cuts68647 : List PrefixCut := [⟨1,2626622,2626624⟩,
⟨64,179109347,179109448⟩]
theorem checked68647 : checkPrefixCuts (2^48) 9001631745 10 Manual.Count131072.C068647.packed 64 cuts68647 = true := by
 decide +kernel
def pointBounds68647 : List (Nat × Nat × Nat) := [(9001633792,115574266430703,115574655795256)]
theorem point_links_checked68647 : (cuts68647.take 1).map (fun c => (9001631745-1+2*2^10*c.k,115574263804081+c.lower,115574653168632+c.upper)) = pointBounds68647 := by
 decide +kernel
def cuts68648 : List PrefixCut := [⟨64,176386379,176386484⟩]
theorem checked68648 : checkPrefixCuts (2^48) 9001762817 10 Manual.Count131072.C068648.packed 64 cuts68648 = true := by
 decide +kernel
def cuts68649 : List PrefixCut := [⟨11,30674270,30674289⟩,
⟨64,178697656,178697761⟩]
theorem checked68649 : checkPrefixCuts (2^48) 9001893889 10 Manual.Count131072.C068649.packed 64 cuts68649 = true := by
 decide +kernel
def pointBounds68649 : List (Nat × Nat × Nat) := [(9001916416,115574649974077,115575039338853)]
theorem point_links_checked68649 : (cuts68649.take 1).map (fun c => (9001893889-1+2*2^10*c.k,115574619299807+c.lower,115575008664564+c.upper)) = pointBounds68649 := by
 decide +kernel
def cuts68650 : List PrefixCut := [⟨64,180539857,180539964⟩]
theorem checked68650 : checkPrefixCuts (2^48) 9002024961 10 Manual.Count131072.C068650.packed 64 cuts68650 = true := by
 decide +kernel
def cuts68651 : List PrefixCut := [⟨21,60502463,60502500⟩,
⟨64,180849892,180850001⟩]
theorem checked68651 : checkPrefixCuts (2^48) 9002156033 10 Manual.Count131072.C068651.packed 64 cuts68651 = true := by
 decide +kernel
def pointBounds68651 : List (Nat × Nat × Nat) := [(9002199040,115575039039783,115575428404789)]
theorem point_links_checked68651 : (cuts68651.take 1).map (fun c => (9002156033-1+2*2^10*c.k,115574978537320+c.lower,115575367902289+c.upper)) = pointBounds68651 := by
 decide +kernel
def cuts68652 : List PrefixCut := [⟨64,182441859,182441965⟩]
theorem checked68652 : checkPrefixCuts (2^48) 9002287105 10 Manual.Count131072.C068652.packed 64 cuts68652 = true := by
 decide +kernel
def cuts68653 : List PrefixCut := [⟨31,87296004,87296056⟩,
⟨64,180688295,180688395⟩]
theorem checked68653 : checkPrefixCuts (2^48) 9002418177 10 Manual.Count131072.C068653.packed 64 cuts68653 = true := by
 decide +kernel
def pointBounds68653 : List (Nat × Nat × Nat) := [(9002481664,115575429125075,115575818490311)]
theorem point_links_checked68653 : (cuts68653.take 1).map (fun c => (9002418177-1+2*2^10*c.k,115575341829071+c.lower,115575731194255+c.upper)) = pointBounds68653 := by
 decide +kernel
def cuts68654 : List PrefixCut := [⟨64,178653372,178653476⟩]
theorem checked68654 : checkPrefixCuts (2^48) 9002549249 10 Manual.Count131072.C068654.packed 64 cuts68654 = true := by
 decide +kernel
def cuts68655 : List PrefixCut := [⟨41,113118693,113118759⟩,
⟨64,177181299,177181404⟩]
theorem checked68655 : checkPrefixCuts (2^48) 9002680321 10 Manual.Count131072.C068655.packed 64 cuts68655 = true := by
 decide +kernel
def pointBounds68655 : List (Nat × Nat × Nat) := [(9002764288,115575814289431,115576203654885)]
theorem point_links_checked68655 : (cuts68655.take 1).map (fun c => (9002680321-1+2*2^10*c.k,115575701170738+c.lower,115576090536126+c.upper)) = pointBounds68655 := by
 decide +kernel
def cuts68656 : List PrefixCut := [⟨64,175615464,175615568⟩]
theorem checked68656 : checkPrefixCuts (2^48) 9002811393 10 Manual.Count131072.C068656.packed 64 cuts68656 = true := by
 decide +kernel
def cuts68657 : List PrefixCut := [⟨51,143316861,143316947⟩,
⟨64,180802825,180802934⟩]
theorem checked68657 : checkPrefixCuts (2^48) 9002942465 10 Manual.Count131072.C068657.packed 64 cuts68657 = true := by
 decide +kernel
def pointBounds68657 : List (Nat × Nat × Nat) := [(9003046912,115576197284362,115576586650045)]
theorem point_links_checked68657 : (cuts68657.take 1).map (fun c => (9002942465-1+2*2^10*c.k,115576053967501+c.lower,115576443333098+c.upper)) = pointBounds68657 := by
 decide +kernel
def cuts68658 : List PrefixCut := [⟨64,181300413,181300522⟩]
theorem checked68658 : checkPrefixCuts (2^48) 9003073537 10 Manual.Count131072.C068658.packed 64 cuts68658 = true := by
 decide +kernel
def cuts68659 : List PrefixCut := [⟨61,167729431,167729533⟩,
⟨64,176076762,176076868⟩]
theorem checked68659 : checkPrefixCuts (2^48) 9003204609 10 Manual.Count131072.C068659.packed 64 cuts68659 = true := by
 decide +kernel
def pointBounds68659 : List (Nat × Nat × Nat) := [(9003329536,115576583800170,115576973166087)]
theorem point_links_checked68659 : (cuts68659.take 1).map (fun c => (9003204609-1+2*2^10*c.k,115576416070739+c.lower,115576805436554+c.upper)) = pointBounds68659 := by
 decide +kernel
def cuts68660 : List PrefixCut := [⟨64,178825344,178825450⟩]
theorem checked68660 : checkPrefixCuts (2^48) 9003335681 10 Manual.Count131072.C068660.packed 64 cuts68660 = true := by
 decide +kernel
def cuts68661 : List PrefixCut := [⟨64,176040380,176040484⟩]
theorem checked68661 : checkPrefixCuts (2^48) 9003466753 10 Manual.Count131072.C068661.packed 64 cuts68661 = true := by
 decide +kernel
def cuts68662 : List PrefixCut := [⟨7,18820003,18820015⟩,
⟨64,180414515,180414617⟩]
theorem checked68662 : checkPrefixCuts (2^48) 9003597825 10 Manual.Count131072.C068662.packed 64 cuts68662 = true := by
 decide +kernel
def pointBounds68662 : List (Nat × Nat × Nat) := [(9003612160,115576965833228,115577355199371)]
theorem point_links_checked68662 : (cuts68662.take 1).map (fun c => (9003597825-1+2*2^10*c.k,115576947013225+c.lower,115577336379356+c.upper)) = pointBounds68662 := by
 decide +kernel
def cuts68663 : List PrefixCut := [⟨64,175878930,175879033⟩]
theorem checked68663 : checkPrefixCuts (2^48) 9003728897 10 Manual.Count131072.C068663.packed 64 cuts68663 = true := by
 decide +kernel
def cuts68664 : List PrefixCut := [⟨17,47705078,47705106⟩,
⟨64,176720435,176720537⟩]
theorem checked68664 : checkPrefixCuts (2^48) 9003859969 10 Manual.Count131072.C068664.packed 64 cuts68664 = true := by
 decide +kernel
def pointBounds68664 : List (Nat × Nat × Nat) := [(9003894784,115577351011748,115577740378112)]
theorem point_links_checked68664 : (cuts68664.take 1).map (fun c => (9003859969-1+2*2^10*c.k,115577303306670+c.lower,115577692673006+c.upper)) = pointBounds68664 := by
 decide +kernel
def cuts68665 : List PrefixCut := [⟨64,180125293,180125402⟩]
theorem checked68665 : checkPrefixCuts (2^48) 9003991041 10 Manual.Count131072.C068665.packed 64 cuts68665 = true := by
 decide +kernel
def cuts68666 : List PrefixCut := [⟨27,75775633,75775677⟩,
⟨64,179466205,179466312⟩]
theorem checked68666 : checkPrefixCuts (2^48) 9004122113 10 Manual.Count131072.C068666.packed 64 cuts68666 = true := by
 decide +kernel
def pointBounds68666 : List (Nat × Nat × Nat) := [(9004177408,115577735928031,115578125294622)]
theorem point_links_checked68666 : (cuts68666.take 1).map (fun c => (9004122113-1+2*2^10*c.k,115577660152398+c.lower,115578049518945+c.upper)) = pointBounds68666 := by
 decide +kernel
def cuts68667 : List PrefixCut := [⟨64,178525804,178525908⟩]
theorem checked68667 : checkPrefixCuts (2^48) 9004253185 10 Manual.Count131072.C068667.packed 64 cuts68667 = true := by
 decide +kernel
def cuts68668 : List PrefixCut := [⟨37,103094259,103094316⟩,
⟨64,178273120,178273219⟩]
theorem checked68668 : checkPrefixCuts (2^48) 9004384257 10 Manual.Count131072.C068668.packed 64 cuts68668 = true := by
 decide +kernel
def pointBounds68668 : List (Nat × Nat × Nat) := [(9004460032,115578121238666,115578510605481)]
theorem point_links_checked68668 : (cuts68668.take 1).map (fun c => (9004384257-1+2*2^10*c.k,115578018144407+c.lower,115578407511165+c.upper)) = pointBounds68668 := by
 decide +kernel
def cuts68669 : List PrefixCut := [⟨64,180489922,180490027⟩]
theorem checked68669 : checkPrefixCuts (2^48) 9004515329 10 Manual.Count131072.C068669.packed 64 cuts68669 = true := by
 decide +kernel
def cuts68670 : List PrefixCut := [⟨47,132349261,132349341⟩,
⟨64,180549798,180549906⟩]
theorem checked68670 : checkPrefixCuts (2^48) 9004646401 10 Manual.Count131072.C068670.packed 64 cuts68670 = true := by
 decide +kernel
def pointBounds68670 : List (Nat × Nat × Nat) := [(9004742656,115578509256710,115578898623752)]
theorem point_links_checked68670 : (cuts68670.take 1).map (fun c => (9004646401-1+2*2^10*c.k,115578376907449+c.lower,115578766274411+c.upper)) = pointBounds68670 := by
 decide +kernel
def cuts68671 : List PrefixCut := [⟨64,179546907,179547020⟩]
theorem checked68671 : checkPrefixCuts (2^48) 9004777473 10 Manual.Count131072.C068671.packed 64 cuts68671 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000270
