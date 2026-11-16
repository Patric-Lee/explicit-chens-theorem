import PlattAssemblyKernel
import PlattCertificates.Count131072.C059632
import PlattCertificates.Count131072.C059633
import PlattCertificates.Count131072.C059634
import PlattCertificates.Count131072.C059635
import PlattCertificates.Count131072.C059636
import PlattCertificates.Count131072.C059637
import PlattCertificates.Count131072.C059638
import PlattCertificates.Count131072.C059639
import PlattCertificates.Count131072.C059640
import PlattCertificates.Count131072.C059641
import PlattCertificates.Count131072.C059642
import PlattCertificates.Count131072.C059643
import PlattCertificates.Count131072.C059644
import PlattCertificates.Count131072.C059645
import PlattCertificates.Count131072.C059646
import PlattCertificates.Count131072.C059647
import PlattCertificates.Count131072.C059648
import PlattCertificates.Count131072.C059649
import PlattCertificates.Count131072.C059650
import PlattCertificates.Count131072.C059651
import PlattCertificates.Count131072.C059652
import PlattCertificates.Count131072.C059653
import PlattCertificates.Count131072.C059654
import PlattCertificates.Count131072.C059655
import PlattCertificates.Count131072.C059656
import PlattCertificates.Count131072.C059657
import PlattCertificates.Count131072.C059658
import PlattCertificates.Count131072.C059659
import PlattCertificates.Count131072.C059660
import PlattCertificates.Count131072.C059661
import PlattCertificates.Count131072.C059662
import PlattCertificates.Count131072.C059663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000301
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59632 : List PrefixCut := [⟨64,206604707,206604827⟩]
theorem checked59632 : checkPrefixCuts (2^48) 7820017665 10 Manual.Count131072.C059632.packed 64 cuts59632 = true := by
 decide +kernel
def cuts59633 : List PrefixCut := [⟨7,23035849,23035863⟩,
⟨64,209336699,209336825⟩]
theorem checked59633 : checkPrefixCuts (2^48) 7820148737 10 Manual.Count131072.C059633.packed 64 cuts59633 = true := by
 decide +kernel
def pointBounds59633 : List (Nat × Nat × Nat) := [(7820163072,113841029223339,113841417587322)]
theorem point_links_checked59633 : (cuts59633.take 1).map (fun c => (7820148737-1+2*2^10*c.k,113841006187490+c.lower,113841394551459+c.upper)) = pointBounds59633 := by
 decide +kernel
def cuts59634 : List PrefixCut := [⟨63,201414848,201414967⟩,
⟨64,204510190,204510311⟩]
theorem checked59634 : checkPrefixCuts (2^48) 7820279809 10 Manual.Count131072.C059634.packed 64 cuts59634 = true := by
 decide +kernel
def pointBounds59634 : List (Nat × Nat × Nat) := [(7820408832,113841416939037,113841805303251)]
theorem point_links_checked59634 : (cuts59634.take 1).map (fun c => (7820279809-1+2*2^10*c.k,113841215524189+c.lower,113841603888284+c.upper)) = pointBounds59634 := by
 decide +kernel
def cuts59635 : List PrefixCut := [⟨64,206414343,206414459⟩]
theorem checked59635 : checkPrefixCuts (2^48) 7820410881 10 Manual.Count131072.C059635.packed 64 cuts59635 = true := by
 decide +kernel
def cuts59636 : List PrefixCut := [⟨55,178049854,178049954⟩,
⟨64,207202708,207202826⟩]
theorem checked59636 : checkPrefixCuts (2^48) 7820541953 10 Manual.Count131072.C059636.packed 64 cuts59636 = true := by
 decide +kernel
def pointBounds59636 : List (Nat × Nat × Nat) := [(7820654592,113841804498576,113842192863008)]
theorem point_links_checked59636 : (cuts59636.take 1).map (fun c => (7820541953-1+2*2^10*c.k,113841626448722+c.lower,113842014813054+c.upper)) = pointBounds59636 := by
 decide +kernel
def cuts59637 : List PrefixCut := [⟨64,205183744,205183864⟩]
theorem checked59637 : checkPrefixCuts (2^48) 7820673025 10 Manual.Count131072.C059637.packed 64 cuts59637 = true := by
 decide +kernel
def cuts59638 : List PrefixCut := [⟨47,152239010,152239096⟩,
⟨64,207123771,207123888⟩]
theorem checked59638 : checkPrefixCuts (2^48) 7820804097 10 Manual.Count131072.C059638.packed 64 cuts59638 = true := by
 decide +kernel
def pointBounds59638 : List (Nat × Nat × Nat) := [(7820900352,113842191074184,113842579438840)]
theorem point_links_checked59638 : (cuts59638.take 1).map (fun c => (7820804097-1+2*2^10*c.k,113842038835174+c.lower,113842427199744+c.upper)) = pointBounds59638 := by
 decide +kernel
def cuts59639 : List PrefixCut := [⟨64,207732138,207732259⟩]
theorem checked59639 : checkPrefixCuts (2^48) 7820935169 10 Manual.Count131072.C059639.packed 64 cuts59639 = true := by
 decide +kernel
def cuts59640 : List PrefixCut := [⟨39,128517226,128517297⟩,
⟨64,207332777,207332895⟩]
theorem checked59640 : checkPrefixCuts (2^48) 7821066241 10 Manual.Count131072.C059640.packed 64 cuts59640 = true := by
 decide +kernel
def pointBounds59640 : List (Nat × Nat × Nat) := [(7821146112,113842582208309,113842970573188)]
theorem point_links_checked59640 : (cuts59640.take 1).map (fun c => (7821066241-1+2*2^10*c.k,113842453691083+c.lower,113842842055891+c.upper)) = pointBounds59640 := by
 decide +kernel
def cuts59641 : List PrefixCut := [⟨64,209092709,209092826⟩]
theorem checked59641 : checkPrefixCuts (2^48) 7821197313 10 Manual.Count131072.C059641.packed 64 cuts59641 = true := by
 decide +kernel
def cuts59642 : List PrefixCut := [⟨31,99830638,99830697⟩,
⟨64,207793643,207793766⟩]
theorem checked59642 : checkPrefixCuts (2^48) 7821328385 10 Manual.Count131072.C059642.packed 64 cuts59642 = true := by
 decide +kernel
def pointBounds59642 : List (Nat × Nat × Nat) := [(7821391872,113842969947207,113843358312309)]
theorem point_links_checked59642 : (cuts59642.take 1).map (fun c => (7821328385-1+2*2^10*c.k,113842870116569+c.lower,113843258481612+c.upper)) = pointBounds59642 := by
 decide +kernel
def cuts59643 : List PrefixCut := [⟨64,207286360,207286482⟩]
theorem checked59643 : checkPrefixCuts (2^48) 7821459457 10 Manual.Count131072.C059643.packed 64 cuts59643 = true := by
 decide +kernel
def cuts59644 : List PrefixCut := [⟨23,77695510,77695552⟩,
⟨64,209010251,209010367⟩]
theorem checked59644 : checkPrefixCuts (2^48) 7821590529 10 Manual.Count131072.C059644.packed 64 cuts59644 = true := by
 decide +kernel
def pointBounds59644 : List (Nat × Nat × Nat) := [(7821637632,113843362892082,113843751257412)]
theorem point_links_checked59644 : (cuts59644.take 1).map (fun c => (7821590529-1+2*2^10*c.k,113843285196572+c.lower,113843673561860+c.upper)) = pointBounds59644 := by
 decide +kernel
def cuts59645 : List PrefixCut := [⟨64,206487724,206487840⟩]
theorem checked59645 : checkPrefixCuts (2^48) 7821721601 10 Manual.Count131072.C059645.packed 64 cuts59645 = true := by
 decide +kernel
def cuts59646 : List PrefixCut := [⟨15,49804120,49804149⟩,
⟨64,206664193,206664310⟩]
theorem checked59646 : checkPrefixCuts (2^48) 7821852673 10 Manual.Count131072.C059646.packed 64 cuts59646 = true := by
 decide +kernel
def pointBounds59646 : List (Nat × Nat × Nat) := [(7821883392,113843750498667,113844138864216)]
theorem point_links_checked59646 : (cuts59646.take 1).map (fun c => (7821852673-1+2*2^10*c.k,113843700694547+c.lower,113844089060067+c.upper)) = pointBounds59646 := by
 decide +kernel
def cuts59647 : List PrefixCut := [⟨64,206048966,206049085⟩]
theorem checked59647 : checkPrefixCuts (2^48) 7821983745 10 Manual.Count131072.C059647.packed 64 cuts59647 = true := by
 decide +kernel
def cuts59648 : List PrefixCut := [⟨7,22310370,22310384⟩,
⟨64,207053082,207053198⟩]
theorem checked59648 : checkPrefixCuts (2^48) 7822114817 10 Manual.Count131072.C059648.packed 64 cuts59648 = true := by
 decide +kernel
def pointBounds59648 : List (Nat × Nat × Nat) := [(7822129152,113844135718076,113844524083846)]
theorem point_links_checked59648 : (cuts59648.take 1).map (fun c => (7822114817-1+2*2^10*c.k,113844113407706+c.lower,113844501773462+c.upper)) = pointBounds59648 := by
 decide +kernel
def cuts59649 : List PrefixCut := [⟨63,206977677,206977793⟩,
⟨64,210719940,210720058⟩]
theorem checked59649 : checkPrefixCuts (2^48) 7822245889 10 Manual.Count131072.C059649.packed 64 cuts59649 = true := by
 decide +kernel
def pointBounds59649 : List (Nat × Nat × Nat) := [(7822374912,113844527438465,113844915804453)]
theorem point_links_checked59649 : (cuts59649.take 1).map (fun c => (7822245889-1+2*2^10*c.k,113844320460788+c.lower,113844708826660+c.upper)) = pointBounds59649 := by
 decide +kernel
def cuts59650 : List PrefixCut := [⟨64,209852821,209852939⟩]
theorem checked59650 : checkPrefixCuts (2^48) 7822376961 10 Manual.Count131072.C059650.packed 64 cuts59650 = true := by
 decide +kernel
def cuts59651 : List PrefixCut := [⟨55,176637775,176637873⟩,
⟨64,206035176,206035292⟩]
theorem checked59651 : checkPrefixCuts (2^48) 7822508033 10 Manual.Count131072.C059651.packed 64 cuts59651 = true := by
 decide +kernel
def pointBounds59651 : List (Nat × Nat × Nat) := [(7822620672,113844917671324,113845306037530)]
theorem point_links_checked59651 : (cuts59651.take 1).map (fun c => (7822508033-1+2*2^10*c.k,113844741033549+c.lower,113845129399657+c.upper)) = pointBounds59651 := by
 decide +kernel
def cuts59652 : List PrefixCut := [⟨64,207614912,207615028⟩]
theorem checked59652 : checkPrefixCuts (2^48) 7822639105 10 Manual.Count131072.C059652.packed 64 cuts59652 = true := by
 decide +kernel
def cuts59653 : List PrefixCut := [⟨47,152740476,152740565⟩,
⟨64,208618914,208619035⟩]
theorem checked59653 : checkPrefixCuts (2^48) 7822770177 10 Manual.Count131072.C059653.packed 64 cuts59653 = true := by
 decide +kernel
def pointBounds59653 : List (Nat × Nat × Nat) := [(7822866432,113845307424113,113845695790542)]
theorem point_links_checked59653 : (cuts59653.take 1).map (fun c => (7822770177-1+2*2^10*c.k,113845154683637+c.lower,113845543049977+c.upper)) = pointBounds59653 := by
 decide +kernel
def cuts59654 : List PrefixCut := [⟨64,207931795,207931914⟩]
theorem checked59654 : checkPrefixCuts (2^48) 7822901249 10 Manual.Count131072.C059654.packed 64 cuts59654 = true := by
 decide +kernel
def cuts59655 : List PrefixCut := [⟨39,125750442,125750509⟩,
⟨64,206525087,206525200⟩]
theorem checked59655 : checkPrefixCuts (2^48) 7823032321 10 Manual.Count131072.C059655.packed 64 cuts59655 = true := by
 decide +kernel
def pointBounds59655 : List (Nat × Nat × Nat) := [(7823112192,113845696984788,113846085351435)]
theorem point_links_checked59655 : (cuts59655.take 1).map (fun c => (7823032321-1+2*2^10*c.k,113845571234346+c.lower,113845959600926+c.upper)) = pointBounds59655 := by
 decide +kernel
def cuts59656 : List PrefixCut := [⟨64,208392551,208392662⟩]
theorem checked59656 : checkPrefixCuts (2^48) 7823163393 10 Manual.Count131072.C059656.packed 64 cuts59656 = true := by
 decide +kernel
def cuts59657 : List PrefixCut := [⟨31,102324073,102324131⟩,
⟨64,207093833,207093947⟩]
theorem checked59657 : checkPrefixCuts (2^48) 7823294465 10 Manual.Count131072.C059657.packed 64 cuts59657 = true := by
 decide +kernel
def pointBounds59657 : List (Nat × Nat × Nat) := [(7823357952,113846088476057,113846476842919)]
theorem point_links_checked59657 : (cuts59657.take 1).map (fun c => (7823294465-1+2*2^10*c.k,113845986151984+c.lower,113846374518788+c.upper)) = pointBounds59657 := by
 decide +kernel
def cuts59658 : List PrefixCut := [⟨64,207809924,207810039⟩]
theorem checked59658 : checkPrefixCuts (2^48) 7823425537 10 Manual.Count131072.C059658.packed 64 cuts59658 = true := by
 decide +kernel
def cuts59659 : List PrefixCut := [⟨23,76848496,76848540⟩,
⟨64,211692011,211692132⟩]
theorem checked59659 : checkPrefixCuts (2^48) 7823556609 10 Manual.Count131072.C059659.packed 64 cuts59659 = true := by
 decide +kernel
def pointBounds59659 : List (Nat × Nat × Nat) := [(7823603712,113846477904237,113846866271314)]
theorem point_links_checked59659 : (cuts59659.take 1).map (fun c => (7823556609-1+2*2^10*c.k,113846401055741+c.lower,113846789422774+c.upper)) = pointBounds59659 := by
 decide +kernel
def cuts59660 : List PrefixCut := [⟨64,209601795,209601911⟩]
theorem checked59660 : checkPrefixCuts (2^48) 7823687681 10 Manual.Count131072.C059660.packed 64 cuts59660 = true := by
 decide +kernel
def cuts59661 : List PrefixCut := [⟨15,49899537,49899565⟩,
⟨64,208554996,208555116⟩]
theorem checked59661 : checkPrefixCuts (2^48) 7823818753 10 Manual.Count131072.C059661.packed 64 cuts59661 = true := by
 decide +kernel
def pointBounds59661 : List (Nat × Nat × Nat) := [(7823849472,113846872249084,113847260616382)]
theorem point_links_checked59661 : (cuts59661.take 1).map (fun c => (7823818753-1+2*2^10*c.k,113846822349547+c.lower,113847210716817+c.upper)) = pointBounds59661 := by
 decide +kernel
def cuts59662 : List PrefixCut := [⟨64,201680121,201680239⟩]
theorem checked59662 : checkPrefixCuts (2^48) 7823949825 10 Manual.Count131072.C059662.packed 64 cuts59662 = true := by
 decide +kernel
def cuts59663 : List PrefixCut := [⟨7,22052936,22052948⟩,
⟨64,206893132,206893248⟩]
theorem checked59663 : checkPrefixCuts (2^48) 7824080897 10 Manual.Count131072.C059663.packed 64 cuts59663 = true := by
 decide +kernel
def pointBounds59663 : List (Nat × Nat × Nat) := [(7824095232,113847254637600,113847643005120)]
theorem point_links_checked59663 : (cuts59663.take 1).map (fun c => (7824080897-1+2*2^10*c.k,113847232584664+c.lower,113847620952172+c.upper)) = pointBounds59663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000301
