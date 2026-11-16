import PlattAssemblyKernel
import PlattCertificates.Count131072.C060704
import PlattCertificates.Count131072.C060705
import PlattCertificates.Count131072.C060706
import PlattCertificates.Count131072.C060707
import PlattCertificates.Count131072.C060708
import PlattCertificates.Count131072.C060709
import PlattCertificates.Count131072.C060710
import PlattCertificates.Count131072.C060711
import PlattCertificates.Count131072.C060712
import PlattCertificates.Count131072.C060713
import PlattCertificates.Count131072.C060714
import PlattCertificates.Count131072.C060715
import PlattCertificates.Count131072.C060716
import PlattCertificates.Count131072.C060717
import PlattCertificates.Count131072.C060718
import PlattCertificates.Count131072.C060719
import PlattCertificates.Count131072.C060720
import PlattCertificates.Count131072.C060721
import PlattCertificates.Count131072.C060722
import PlattCertificates.Count131072.C060723
import PlattCertificates.Count131072.C060724
import PlattCertificates.Count131072.C060725
import PlattCertificates.Count131072.C060726
import PlattCertificates.Count131072.C060727
import PlattCertificates.Count131072.C060728
import PlattCertificates.Count131072.C060729
import PlattCertificates.Count131072.C060730
import PlattCertificates.Count131072.C060731
import PlattCertificates.Count131072.C060732
import PlattCertificates.Count131072.C060733
import PlattCertificates.Count131072.C060734
import PlattCertificates.Count131072.C060735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60704 : List PrefixCut := [⟨12,39000727,39000750⟩,
⟨64,204336997,204337116⟩]
theorem checked60704 : checkPrefixCuts (2^48) 7960526849 10 Manual.Count131072.C060704.packed 64 cuts60704 = true := by
 decide +kernel
def pointBounds60704 : List (Nat × Nat × Nat) := [(7960551424,114060822363256,114061210852799)]
theorem point_links_checked60704 : (cuts60704.take 1).map (fun c => (7960526849-1+2*2^10*c.k,114060783362529+c.lower,114061171852049+c.upper)) = pointBounds60704 := by
 decide +kernel
def cuts60705 : List PrefixCut := [⟨64,205288294,205288411⟩]
theorem checked60705 : checkPrefixCuts (2^48) 7960657921 10 Manual.Count131072.C060705.packed 64 cuts60705 = true := by
 decide +kernel
def cuts60706 : List PrefixCut := [⟨6,18385969,18385981⟩,
⟨64,200935942,200936058⟩]
theorem checked60706 : checkPrefixCuts (2^48) 7960788993 10 Manual.Count131072.C060706.packed 64 cuts60706 = true := by
 decide +kernel
def pointBounds60706 : List (Nat × Nat × Nat) := [(7960801280,114061211373789,114061599863557)]
theorem point_links_checked60706 : (cuts60706.take 1).map (fun c => (7960788993-1+2*2^10*c.k,114061192987820+c.lower,114061581477576+c.upper)) = pointBounds60706 := by
 decide +kernel
def cuts60707 : List PrefixCut := [⟨64,202594410,202594526⟩]
theorem checked60707 : checkPrefixCuts (2^48) 7960920065 10 Manual.Count131072.C060707.packed 64 cuts60707 = true := by
 decide +kernel
def pointBounds60707 : List (Nat × Nat × Nat) := [(7961051136,114061596518172,114061985008160)]
theorem point_links_checked60707 : (cuts60707.take 1).map (fun c => (7960920065-1+2*2^10*c.k,114061393923762+c.lower,114061782413634+c.upper)) = pointBounds60707 := by
 decide +kernel
def cuts60708 : List PrefixCut := [⟨64,201247524,201247642⟩]
theorem checked60708 : checkPrefixCuts (2^48) 7961051137 10 Manual.Count131072.C060708.packed 64 cuts60708 = true := by
 decide +kernel
def cuts60709 : List PrefixCut := [⟨58,180667381,180667485⟩,
⟨64,199653210,199653325⟩]
theorem checked60709 : checkPrefixCuts (2^48) 7961182209 10 Manual.Count131072.C060709.packed 64 cuts60709 = true := by
 decide +kernel
def pointBounds60709 : List (Nat × Nat × Nat) := [(7961300992,114061978433077,114062366923287)]
theorem point_links_checked60709 : (cuts60709.take 1).map (fun c => (7961182209-1+2*2^10*c.k,114061797765696+c.lower,114062186255802+c.upper)) = pointBounds60709 := by
 decide +kernel
def cuts60710 : List PrefixCut := [⟨64,204705716,204705828⟩]
theorem checked60710 : checkPrefixCuts (2^48) 7961313281 10 Manual.Count131072.C060710.packed 64 cuts60710 = true := by
 decide +kernel
def cuts60711 : List PrefixCut := [⟨52,166342990,166343083⟩,
⟨64,203889179,203889291⟩]
theorem checked60711 : checkPrefixCuts (2^48) 7961444353 10 Manual.Count131072.C060711.packed 64 cuts60711 = true := by
 decide +kernel
def pointBounds60711 : List (Nat × Nat × Nat) := [(7961550848,114062368467612,114062756958038)]
theorem point_links_checked60711 : (cuts60711.take 1).map (fun c => (7961444353-1+2*2^10*c.k,114062202124622+c.lower,114062590614955+c.upper)) = pointBounds60711 := by
 decide +kernel
def cuts60712 : List PrefixCut := [⟨64,204981794,204981914⟩]
theorem checked60712 : checkPrefixCuts (2^48) 7961575425 10 Manual.Count131072.C060712.packed 64 cuts60712 = true := by
 decide +kernel
def cuts60713 : List PrefixCut := [⟨46,145726629,145726713⟩,
⟨64,203352162,203352278⟩]
theorem checked60713 : checkPrefixCuts (2^48) 7961706497 10 Manual.Count131072.C060713.packed 64 cuts60713 = true := by
 decide +kernel
def pointBounds60713 : List (Nat × Nat × Nat) := [(7961800704,114062756722224,114063145212873)]
theorem point_links_checked60713 : (cuts60713.take 1).map (fun c => (7961706497-1+2*2^10*c.k,114062610995595+c.lower,114062999486160+c.upper)) = pointBounds60713 := by
 decide +kernel
def cuts60714 : List PrefixCut := [⟨64,203879105,203879223⟩]
theorem checked60714 : checkPrefixCuts (2^48) 7961837569 10 Manual.Count131072.C060714.packed 64 cuts60714 = true := by
 decide +kernel
def cuts60715 : List PrefixCut := [⟨40,128823578,128823650⟩,
⟨64,205219145,205219259⟩]
theorem checked60715 : checkPrefixCuts (2^48) 7961968641 10 Manual.Count131072.C060715.packed 64 cuts60715 = true := by
 decide +kernel
def pointBounds60715 : List (Nat × Nat × Nat) := [(7962050560,114063147050440,114063535541311)]
theorem point_links_checked60715 : (cuts60715.take 1).map (fun c => (7961968641-1+2*2^10*c.k,114063018226862+c.lower,114063406717661+c.upper)) = pointBounds60715 := by
 decide +kernel
def cuts60716 : List PrefixCut := [⟨64,204932933,204933052⟩]
theorem checked60716 : checkPrefixCuts (2^48) 7962099713 10 Manual.Count131072.C060716.packed 64 cuts60716 = true := by
 decide +kernel
def cuts60717 : List PrefixCut := [⟨34,106017963,106018025⟩,
⟨64,202242877,202242994⟩]
theorem checked60717 : checkPrefixCuts (2^48) 7962230785 10 Manual.Count131072.C060717.packed 64 cuts60717 = true := by
 decide +kernel
def pointBounds60717 : List (Nat × Nat × Nat) := [(7962300416,114063534396903,114063922887997)]
theorem point_links_checked60717 : (cuts60717.take 1).map (fun c => (7962230785-1+2*2^10*c.k,114063428378940+c.lower,114063816869972+c.upper)) = pointBounds60717 := by
 decide +kernel
def cuts60718 : List PrefixCut := [⟨64,203759635,203759753⟩]
theorem checked60718 : checkPrefixCuts (2^48) 7962361857 10 Manual.Count131072.C060718.packed 64 cuts60718 = true := by
 decide +kernel
def cuts60719 : List PrefixCut := [⟨28,89294022,89294072⟩,
⟨64,202306941,202307057⟩]
theorem checked60719 : checkPrefixCuts (2^48) 7962492929 10 Manual.Count131072.C060719.packed 64 cuts60719 = true := by
 decide +kernel
def pointBounds60719 : List (Nat × Nat × Nat) := [(7962550272,114063923675474,114064312166791)]
theorem point_links_checked60719 : (cuts60719.take 1).map (fun c => (7962492929-1+2*2^10*c.k,114063834381452+c.lower,114064222872719+c.upper)) = pointBounds60719 := by
 decide +kernel
def cuts60720 : List PrefixCut := [⟨64,202268246,202268363⟩]
theorem checked60720 : checkPrefixCuts (2^48) 7962624001 10 Manual.Count131072.C060720.packed 64 cuts60720 = true := by
 decide +kernel
def cuts60721 : List PrefixCut := [⟨22,68894873,68894913⟩,
⟨64,203290037,203290152⟩]
theorem checked60721 : checkPrefixCuts (2^48) 7962755073 10 Manual.Count131072.C060721.packed 64 cuts60721 = true := by
 decide +kernel
def pointBounds60721 : List (Nat × Nat × Nat) := [(7962800128,114064307851512,114064696343052)]
theorem point_links_checked60721 : (cuts60721.take 1).map (fun c => (7962755073-1+2*2^10*c.k,114064238956639+c.lower,114064627448139+c.upper)) = pointBounds60721 := by
 decide +kernel
def cuts60722 : List PrefixCut := [⟨64,201908117,201908236⟩]
theorem checked60722 : checkPrefixCuts (2^48) 7962886145 10 Manual.Count131072.C060722.packed 64 cuts60722 = true := by
 decide +kernel
def cuts60723 : List PrefixCut := [⟨16,51925767,51925797⟩,
⟨64,203389407,203389524⟩]
theorem checked60723 : checkPrefixCuts (2^48) 7963017217 10 Manual.Count131072.C060723.packed 64 cuts60723 = true := by
 decide +kernel
def pointBounds60723 : List (Nat × Nat × Nat) := [(7963049984,114064696080560,114065084572324)]
theorem point_links_checked60723 : (cuts60723.take 1).map (fun c => (7963017217-1+2*2^10*c.k,114064644154793+c.lower,114065032646527+c.upper)) = pointBounds60723 := by
 decide +kernel
def cuts60724 : List PrefixCut := [⟨64,205188741,205188859⟩]
theorem checked60724 : checkPrefixCuts (2^48) 7963148289 10 Manual.Count131072.C060724.packed 64 cuts60724 = true := by
 decide +kernel
def cuts60725 : List PrefixCut := [⟨10,31882598,31882617⟩,
⟨64,204761198,204761318⟩]
theorem checked60725 : checkPrefixCuts (2^48) 7963279361 10 Manual.Count131072.C060725.packed 64 cuts60725 = true := by
 decide +kernel
def pointBounds60725 : List (Nat × Nat × Nat) := [(7963299840,114065084615539,114065473107527)]
theorem point_links_checked60725 : (cuts60725.take 1).map (fun c => (7963279361-1+2*2^10*c.k,114065052732941+c.lower,114065441224910+c.upper)) = pointBounds60725 := by
 decide +kernel
def cuts60726 : List PrefixCut := [⟨64,201046526,201046644⟩]
theorem checked60726 : checkPrefixCuts (2^48) 7963410433 10 Manual.Count131072.C060726.packed 64 cuts60726 = true := by
 decide +kernel
def cuts60727 : List PrefixCut := [⟨4,12936426,12936433⟩,
⟨64,205072569,205072682⟩]
theorem checked60727 : checkPrefixCuts (2^48) 7963541505 10 Manual.Count131072.C060727.packed 64 cuts60727 = true := by
 decide +kernel
def pointBounds60727 : List (Nat × Nat × Nat) := [(7963549696,114065471477091,114065859969305)]
theorem point_links_checked60727 : (cuts60727.take 1).map (fun c => (7963541505-1+2*2^10*c.k,114065458540665+c.lower,114065847032872+c.upper)) = pointBounds60727 := by
 decide +kernel
def cuts60728 : List PrefixCut := [⟨62,198141721,198141837⟩,
⟨64,204715759,204715878⟩]
theorem checked60728 : checkPrefixCuts (2^48) 7963672577 10 Manual.Count131072.C060728.packed 64 cuts60728 = true := by
 decide +kernel
def pointBounds60728 : List (Nat × Nat × Nat) := [(7963799552,114065861754955,114066250247391)]
theorem point_links_checked60728 : (cuts60728.take 1).map (fun c => (7963672577-1+2*2^10*c.k,114065663613234+c.lower,114066052105554+c.upper)) = pointBounds60728 := by
 decide +kernel
def cuts60729 : List PrefixCut := [⟨64,202768458,202768572⟩]
theorem checked60729 : checkPrefixCuts (2^48) 7963803649 10 Manual.Count131072.C060729.packed 64 cuts60729 = true := by
 decide +kernel
def cuts60730 : List PrefixCut := [⟨56,177742164,177742267⟩,
⟨64,201740163,201740281⟩]
theorem checked60730 : checkPrefixCuts (2^48) 7963934721 10 Manual.Count131072.C060730.packed 64 cuts60730 = true := by
 decide +kernel
def pointBounds60730 : List (Nat × Nat × Nat) := [(7964049408,114066248839615,114066637332271)]
theorem point_links_checked60730 : (cuts60730.take 1).map (fun c => (7963934721-1+2*2^10*c.k,114066071097451+c.lower,114066459590004+c.upper)) = pointBounds60730 := by
 decide +kernel
def cuts60731 : List PrefixCut := [⟨64,202302331,202302449⟩]
theorem checked60731 : checkPrefixCuts (2^48) 7964065793 10 Manual.Count131072.C060731.packed 64 cuts60731 = true := by
 decide +kernel
def cuts60732 : List PrefixCut := [⟨50,157202588,157202676⟩,
⟨64,201839553,201839666⟩]
theorem checked60732 : checkPrefixCuts (2^48) 7964196865 10 Manual.Count131072.C060732.packed 64 cuts60732 = true := by
 decide +kernel
def pointBounds60732 : List (Nat × Nat × Nat) := [(7964299264,114066632342533,114067020835410)]
theorem point_links_checked60732 : (cuts60732.take 1).map (fun c => (7964196865-1+2*2^10*c.k,114066475139945+c.lower,114066863632734+c.upper)) = pointBounds60732 := by
 decide +kernel
def cuts60733 : List PrefixCut := [⟨64,205335049,205335168⟩]
theorem checked60733 : checkPrefixCuts (2^48) 7964327937 10 Manual.Count131072.C060733.packed 64 cuts60733 = true := by
 decide +kernel
def cuts60734 : List PrefixCut := [⟨44,139314896,139314976⟩,
⟨64,203140526,203140645⟩]
theorem checked60734 : checkPrefixCuts (2^48) 7964459009 10 Manual.Count131072.C060734.packed 64 cuts60734 = true := by
 decide +kernel
def pointBounds60734 : List (Nat × Nat × Nat) := [(7964549120,114067021629443,114067410122544)]
theorem point_links_checked60734 : (cuts60734.take 1).map (fun c => (7964459009-1+2*2^10*c.k,114066882314547+c.lower,114067270807568+c.upper)) = pointBounds60734 := by
 decide +kernel
def cuts60735 : List PrefixCut := [⟨64,205186946,205187063⟩]
theorem checked60735 : checkPrefixCuts (2^48) 7964590081 10 Manual.Count131072.C060735.packed 64 cuts60735 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000022
