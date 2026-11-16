import PlattAssemblyKernel
import PlattCertificates.Count131072.C069632
import PlattCertificates.Count131072.C069633
import PlattCertificates.Count131072.C069634
import PlattCertificates.Count131072.C069635
import PlattCertificates.Count131072.C069636
import PlattCertificates.Count131072.C069637
import PlattCertificates.Count131072.C069638
import PlattCertificates.Count131072.C069639
import PlattCertificates.Count131072.C069640
import PlattCertificates.Count131072.C069641
import PlattCertificates.Count131072.C069642
import PlattCertificates.Count131072.C069643
import PlattCertificates.Count131072.C069644
import PlattCertificates.Count131072.C069645
import PlattCertificates.Count131072.C069646
import PlattCertificates.Count131072.C069647
import PlattCertificates.Count131072.C069648
import PlattCertificates.Count131072.C069649
import PlattCertificates.Count131072.C069650
import PlattCertificates.Count131072.C069651
import PlattCertificates.Count131072.C069652
import PlattCertificates.Count131072.C069653
import PlattCertificates.Count131072.C069654
import PlattCertificates.Count131072.C069655
import PlattCertificates.Count131072.C069656
import PlattCertificates.Count131072.C069657
import PlattCertificates.Count131072.C069658
import PlattCertificates.Count131072.C069659
import PlattCertificates.Count131072.C069660
import PlattCertificates.Count131072.C069661
import PlattCertificates.Count131072.C069662
import PlattCertificates.Count131072.C069663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000301
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69632 : List PrefixCut := [⟨64,175682827,175682931⟩]
theorem checked69632 : checkPrefixCuts (2^48) 9130737665 10 Manual.Count131072.C069632.packed 64 cuts69632 = true := by
 decide +kernel
def cuts69633 : List PrefixCut := [⟨64,176142712,176142818⟩]
theorem checked69633 : checkPrefixCuts (2^48) 9130868737 10 Manual.Count131072.C069633.packed 64 cuts69633 = true := by
 decide +kernel
def cuts69634 : List PrefixCut := [⟨2,5579558,5579562⟩,
⟨64,173828231,173828339⟩]
theorem checked69634 : checkPrefixCuts (2^48) 9130999809 10 Manual.Count131072.C069634.packed 64 cuts69634 = true := by
 decide +kernel
def pointBounds69634 : List (Nat × Nat × Nat) := [(9131003904,115749450806830,115749840274209)]
theorem point_links_checked69634 : (cuts69634.take 1).map (fun c => (9130999809-1+2*2^10*c.k,115749445227272+c.lower,115749834694647+c.upper)) = pointBounds69634 := by
 decide +kernel
def cuts69635 : List PrefixCut := [⟨64,177247385,177247489⟩]
theorem checked69635 : checkPrefixCuts (2^48) 9131130881 10 Manual.Count131072.C069635.packed 64 cuts69635 = true := by
 decide +kernel
def cuts69636 : List PrefixCut := [⟨14,38994081,38994103⟩,
⟨64,177707218,177707317⟩]
theorem checked69636 : checkPrefixCuts (2^48) 9131261953 10 Manual.Count131072.C069636.packed 64 cuts69636 = true := by
 decide +kernel
def pointBounds69636 : List (Nat × Nat × Nat) := [(9131290624,115749835296969,115750224764578)]
theorem point_links_checked69636 : (cuts69636.take 1).map (fun c => (9131261953-1+2*2^10*c.k,115749796302888+c.lower,115750185770475+c.upper)) = pointBounds69636 := by
 decide +kernel
def cuts69637 : List PrefixCut := [⟨64,176255886,176255991⟩]
theorem checked69637 : checkPrefixCuts (2^48) 9131393025 10 Manual.Count131072.C069637.packed 64 cuts69637 = true := by
 decide +kernel
def cuts69638 : List PrefixCut := [⟨26,72868966,72869008⟩,
⟨64,177455527,177455629⟩]
theorem checked69638 : checkPrefixCuts (2^48) 9131524097 10 Manual.Count131072.C069638.packed 64 cuts69638 = true := by
 decide +kernel
def pointBounds69638 : List (Nat × Nat × Nat) := [(9131577344,115750223134958,115750612602791)]
theorem point_links_checked69638 : (cuts69638.take 1).map (fun c => (9131524097-1+2*2^10*c.k,115750150265992+c.lower,115750539733783+c.upper)) = pointBounds69638 := by
 decide +kernel
def cuts69639 : List PrefixCut := [⟨64,176898137,176898239⟩]
theorem checked69639 : checkPrefixCuts (2^48) 9131655169 10 Manual.Count131072.C069639.packed 64 cuts69639 = true := by
 decide +kernel
def cuts69640 : List PrefixCut := [⟨38,106002048,106002113⟩,
⟨64,177049726,177049832⟩]
theorem checked69640 : checkPrefixCuts (2^48) 9131786241 10 Manual.Count131072.C069640.packed 64 cuts69640 = true := by
 decide +kernel
def pointBounds69640 : List (Nat × Nat × Nat) := [(9131864064,115750610621704,115751000089764)]
theorem point_links_checked69640 : (cuts69640.take 1).map (fun c => (9131786241-1+2*2^10*c.k,115750504619656+c.lower,115750894087651+c.upper)) = pointBounds69640 := by
 decide +kernel
def cuts69641 : List PrefixCut := [⟨64,177756114,177756215⟩]
theorem checked69641 : checkPrefixCuts (2^48) 9131917313 10 Manual.Count131072.C069641.packed 64 cuts69641 = true := by
 decide +kernel
def cuts69642 : List PrefixCut := [⟨50,138855730,138855814⟩,
⟨64,175688452,175688557⟩]
theorem checked69642 : checkPrefixCuts (2^48) 9132048385 10 Manual.Count131072.C069642.packed 64 cuts69642 = true := by
 decide +kernel
def pointBounds69642 : List (Nat × Nat × Nat) := [(9132150784,115750998281226,115751387749512)]
theorem point_links_checked69642 : (cuts69642.take 1).map (fun c => (9132048385-1+2*2^10*c.k,115750859425496+c.lower,115751248893698+c.upper)) = pointBounds69642 := by
 decide +kernel
def cuts69643 : List PrefixCut := [⟨64,174360569,174360674⟩]
theorem checked69643 : checkPrefixCuts (2^48) 9132179457 10 Manual.Count131072.C069643.packed 64 cuts69643 = true := by
 decide +kernel
def cuts69644 : List PrefixCut := [⟨62,170998552,170998652⟩,
⟨64,176731339,176731442⟩]
theorem checked69644 : checkPrefixCuts (2^48) 9132310529 10 Manual.Count131072.C069644.packed 64 cuts69644 = true := by
 decide +kernel
def pointBounds69644 : List (Nat × Nat × Nat) := [(9132437504,115751380473069,115751769941581)]
theorem point_links_checked69644 : (cuts69644.take 1).map (fun c => (9132310529-1+2*2^10*c.k,115751209474517+c.lower,115751598942929+c.upper)) = pointBounds69644 := by
 decide +kernel
def cuts69645 : List PrefixCut := [⟨64,176358951,176359059⟩]
theorem checked69645 : checkPrefixCuts (2^48) 9132441601 10 Manual.Count131072.C069645.packed 64 cuts69645 = true := by
 decide +kernel
def cuts69646 : List PrefixCut := [⟨64,178452222,178452325⟩]
theorem checked69646 : checkPrefixCuts (2^48) 9132572673 10 Manual.Count131072.C069646.packed 64 cuts69646 = true := by
 decide +kernel
def cuts69647 : List PrefixCut := [⟨10,28354868,28354884⟩,
⟨64,177617523,177617630⟩]
theorem checked69647 : checkPrefixCuts (2^48) 9132703745 10 Manual.Count131072.C069647.packed 64 cuts69647 = true := by
 decide +kernel
def pointBounds69647 : List (Nat × Nat × Nat) := [(9132724224,115751769371897,115752158840639)]
theorem point_links_checked69647 : (cuts69647.take 1).map (fun c => (9132703745-1+2*2^10*c.k,115751741017029+c.lower,115752130485755+c.upper)) = pointBounds69647 := by
 decide +kernel
def cuts69648 : List PrefixCut := [⟨64,177614971,177615079⟩]
theorem checked69648 : checkPrefixCuts (2^48) 9132834817 10 Manual.Count131072.C069648.packed 64 cuts69648 = true := by
 decide +kernel
def cuts69649 : List PrefixCut := [⟨22,61022773,61022812⟩,
⟨64,175978999,175979103⟩]
theorem checked69649 : checkPrefixCuts (2^48) 9132965889 10 Manual.Count131072.C069649.packed 64 cuts69649 = true := by
 decide +kernel
def pointBounds69649 : List (Nat × Nat × Nat) := [(9133010944,115752157272296,115752546741276)]
theorem point_links_checked69649 : (cuts69649.take 1).map (fun c => (9132965889-1+2*2^10*c.k,115752096249523+c.lower,115752485718464+c.upper)) = pointBounds69649 := by
 decide +kernel
def cuts69650 : List PrefixCut := [⟨64,176346291,176346399⟩]
theorem checked69650 : checkPrefixCuts (2^48) 9133096961 10 Manual.Count131072.C069650.packed 64 cuts69650 = true := by
 decide +kernel
def cuts69651 : List PrefixCut := [⟨34,93966083,93966139⟩,
⟨64,176621126,176621229⟩]
theorem checked69651 : checkPrefixCuts (2^48) 9133228033 10 Manual.Count131072.C069651.packed 64 cuts69651 = true := by
 decide +kernel
def pointBounds69651 : List (Nat × Nat × Nat) := [(9133297664,115752542540896,115752932010105)]
theorem point_links_checked69651 : (cuts69651.take 1).map (fun c => (9133228033-1+2*2^10*c.k,115752448574813+c.lower,115752838043966+c.upper)) = pointBounds69651 := by
 decide +kernel
def cuts69652 : List PrefixCut := [⟨64,176310410,176310516⟩]
theorem checked69652 : checkPrefixCuts (2^48) 9133359105 10 Manual.Count131072.C069652.packed 64 cuts69652 = true := by
 decide +kernel
def cuts69653 : List PrefixCut := [⟨46,126352699,126352772⟩,
⟨64,176400336,176400436⟩]
theorem checked69653 : checkPrefixCuts (2^48) 9133490177 10 Manual.Count131072.C069653.packed 64 cuts69653 = true := by
 decide +kernel
def pointBounds69653 : List (Nat × Nat × Nat) := [(9133584384,115752927859048,115753317328483)]
theorem point_links_checked69653 : (cuts69653.take 1).map (fun c => (9133490177-1+2*2^10*c.k,115752801506349+c.lower,115753190975711+c.upper)) = pointBounds69653 := by
 decide +kernel
def cuts69654 : List PrefixCut := [⟨64,175411638,175411741⟩]
theorem checked69654 : checkPrefixCuts (2^48) 9133621249 10 Manual.Count131072.C069654.packed 64 cuts69654 = true := by
 decide +kernel
def cuts69655 : List PrefixCut := [⟨58,159199609,159199700⟩,
⟨64,175686480,175686583⟩]
theorem checked69655 : checkPrefixCuts (2^48) 9133752321 10 Manual.Count131072.C069655.packed 64 cuts69655 = true := by
 decide +kernel
def pointBounds69655 : List (Nat × Nat × Nat) := [(9133871104,115753312517932,115753701987588)]
theorem point_links_checked69655 : (cuts69655.take 1).map (fun c => (9133752321-1+2*2^10*c.k,115753153318323+c.lower,115753542787888+c.upper)) = pointBounds69655 := by
 decide +kernel
def cuts69656 : List PrefixCut := [⟨64,177471309,177471411⟩]
theorem checked69656 : checkPrefixCuts (2^48) 9133883393 10 Manual.Count131072.C069656.packed 64 cuts69656 = true := by
 decide +kernel
def cuts69657 : List PrefixCut := [⟨64,176760003,176760105⟩]
theorem checked69657 : checkPrefixCuts (2^48) 9134014465 10 Manual.Count131072.C069657.packed 64 cuts69657 = true := by
 decide +kernel
def cuts69658 : List PrefixCut := [⟨6,16178220,16178231⟩,
⟨64,177096432,177096538⟩]
theorem checked69658 : checkPrefixCuts (2^48) 9134145537 10 Manual.Count131072.C069658.packed 64 cuts69658 = true := by
 decide +kernel
def pointBounds69658 : List (Nat × Nat × Nat) := [(9134157824,115753699414335,115754088884218)]
theorem point_links_checked69658 : (cuts69658.take 1).map (fun c => (9134145537-1+2*2^10*c.k,115753683236115+c.lower,115754072705987+c.upper)) = pointBounds69658 := by
 decide +kernel
def cuts69659 : List PrefixCut := [⟨64,177741004,177741106⟩]
theorem checked69659 : checkPrefixCuts (2^48) 9134276609 10 Manual.Count131072.C069659.packed 64 cuts69659 = true := by
 decide +kernel
def cuts69660 : List PrefixCut := [⟨18,47947723,47947752⟩,
⟨64,173886640,173886737⟩]
theorem checked69660 : checkPrefixCuts (2^48) 9134407681 10 Manual.Count131072.C069660.packed 64 cuts69660 = true := by
 decide +kernel
def pointBounds69660 : List (Nat × Nat × Nat) := [(9134444544,115754086021274,115754475491383)]
theorem point_links_checked69660 : (cuts69660.take 1).map (fun c => (9134407681-1+2*2^10*c.k,115754038073551+c.lower,115754427543631+c.upper)) = pointBounds69660 := by
 decide +kernel
def cuts69661 : List PrefixCut := [⟨64,175424852,175424952⟩]
theorem checked69661 : checkPrefixCuts (2^48) 9134538753 10 Manual.Count131072.C069661.packed 64 cuts69661 = true := by
 decide +kernel
def cuts69662 : List PrefixCut := [⟨30,79592061,79592109⟩,
⟨64,174220577,174220683⟩]
theorem checked69662 : checkPrefixCuts (2^48) 9134669825 10 Manual.Count131072.C069662.packed 64 cuts69662 = true := by
 decide +kernel
def pointBounds69662 : List (Nat × Nat × Nat) := [(9134731264,115754466977104,115754856447429)]
theorem point_links_checked69662 : (cuts69662.take 1).map (fun c => (9134669825-1+2*2^10*c.k,115754387385043+c.lower,115754776855320+c.upper)) = pointBounds69662 := by
 decide +kernel
def cuts69663 : List PrefixCut := [⟨64,177638361,177638466⟩]
theorem checked69663 : checkPrefixCuts (2^48) 9134800897 10 Manual.Count131072.C069663.packed 64 cuts69663 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000301
