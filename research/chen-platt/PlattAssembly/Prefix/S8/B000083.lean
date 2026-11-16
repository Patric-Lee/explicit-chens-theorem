import PlattAssemblyKernel
import PlattCertificates.Count131072.C072656
import PlattCertificates.Count131072.C072657
import PlattCertificates.Count131072.C072658
import PlattCertificates.Count131072.C072659
import PlattCertificates.Count131072.C072660
import PlattCertificates.Count131072.C072661
import PlattCertificates.Count131072.C072662
import PlattCertificates.Count131072.C072663
import PlattCertificates.Count131072.C072664
import PlattCertificates.Count131072.C072665
import PlattCertificates.Count131072.C072666
import PlattCertificates.Count131072.C072667
import PlattCertificates.Count131072.C072668
import PlattCertificates.Count131072.C072669
import PlattCertificates.Count131072.C072670
import PlattCertificates.Count131072.C072671
import PlattCertificates.Count131072.C072672
import PlattCertificates.Count131072.C072673
import PlattCertificates.Count131072.C072674
import PlattCertificates.Count131072.C072675
import PlattCertificates.Count131072.C072676
import PlattCertificates.Count131072.C072677
import PlattCertificates.Count131072.C072678
import PlattCertificates.Count131072.C072679
import PlattCertificates.Count131072.C072680
import PlattCertificates.Count131072.C072681
import PlattCertificates.Count131072.C072682
import PlattCertificates.Count131072.C072683
import PlattCertificates.Count131072.C072684
import PlattCertificates.Count131072.C072685
import PlattCertificates.Count131072.C072686
import PlattCertificates.Count131072.C072687
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000083
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72656 : List PrefixCut := [⟨64,170176060,170176160⟩]
theorem checked72656 : checkPrefixCuts (2^48) 9527099393 10 Manual.Count131072.C072656.packed 64 cuts72656 = true := by
 decide +kernel
def cuts72657 : List PrefixCut := [⟨62,163260442,163260541⟩,
⟨64,168696510,168696613⟩]
theorem checked72657 : checkPrefixCuts (2^48) 9527230465 10 Manual.Count131072.C072657.packed 64 cuts72657 = true := by
 decide +kernel
def pointBounds72657 : List (Nat × Nat × Nat) := [(9527357440,116270460782800,116270850558215)]
theorem point_links_checked72657 : (cuts72657.take 1).map (fun c => (9527230465-1+2*2^10*c.k,116270297522358+c.lower,116270687297674+c.upper)) = pointBounds72657 := by
 decide +kernel
def cuts72658 : List PrefixCut := [⟨64,167571547,167571647⟩]
theorem checked72658 : checkPrefixCuts (2^48) 9527361537 10 Manual.Count131072.C072658.packed 64 cuts72658 = true := by
 decide +kernel
def cuts72659 : List PrefixCut := [⟨64,167096537,167096635⟩]
theorem checked72659 : checkPrefixCuts (2^48) 9527492609 10 Manual.Count131072.C072659.packed 64 cuts72659 = true := by
 decide +kernel
def cuts72660 : List PrefixCut := [⟨16,42630522,42630545⟩,
⟨64,167891902,167892000⟩]
theorem checked72660 : checkPrefixCuts (2^48) 9527623681 10 Manual.Count131072.C072660.packed 64 cuts72660 = true := by
 decide +kernel
def pointBounds72660 : List (Nat × Nat × Nat) := [(9527656448,116270843517474,116271233293114)]
theorem point_links_checked72660 : (cuts72660.take 1).map (fun c => (9527623681-1+2*2^10*c.k,116270800886952+c.lower,116271190662569+c.upper)) = pointBounds72660 := by
 decide +kernel
def cuts72661 : List PrefixCut := [⟨64,170400706,170400802⟩]
theorem checked72661 : checkPrefixCuts (2^48) 9527754753 10 Manual.Count131072.C072661.packed 64 cuts72661 = true := by
 decide +kernel
def cuts72662 : List PrefixCut := [⟨34,88094579,88094632⟩,
⟨64,167887274,167887371⟩]
theorem checked72662 : checkPrefixCuts (2^48) 9527885825 10 Manual.Count131072.C072662.packed 64 cuts72662 = true := by
 decide +kernel
def pointBounds72662 : List (Nat × Nat × Nat) := [(9527955456,116271227274139,116271617050003)]
theorem point_links_checked72662 : (cuts72662.take 1).map (fun c => (9527885825-1+2*2^10*c.k,116271139179560+c.lower,116271528955371+c.upper)) = pointBounds72662 := by
 decide +kernel
def cuts72663 : List PrefixCut := [⟨64,167264599,167264693⟩]
theorem checked72663 : checkPrefixCuts (2^48) 9528016897 10 Manual.Count131072.C072663.packed 64 cuts72663 = true := by
 decide +kernel
def cuts72664 : List PrefixCut := [⟨52,137544017,137544097⟩,
⟨64,169655125,169655225⟩]
theorem checked72664 : checkPrefixCuts (2^48) 9528147969 10 Manual.Count131072.C072664.packed 64 cuts72664 = true := by
 decide +kernel
def pointBounds72664 : List (Nat × Nat × Nat) := [(9528254464,116271611875450,116272001651532)]
theorem point_links_checked72664 : (cuts72664.take 1).map (fun c => (9528147969-1+2*2^10*c.k,116271474331433+c.lower,116271864107435+c.upper)) = pointBounds72664 := by
 decide +kernel
def cuts72665 : List PrefixCut := [⟨64,169711889,169711996⟩]
theorem checked72665 : checkPrefixCuts (2^48) 9528279041 10 Manual.Count131072.C072665.packed 64 cuts72665 = true := by
 decide +kernel
def cuts72666 : List PrefixCut := [⟨64,168409768,168409873⟩]
theorem checked72666 : checkPrefixCuts (2^48) 9528410113 10 Manual.Count131072.C072666.packed 64 cuts72666 = true := by
 decide +kernel
def cuts72667 : List PrefixCut := [⟨6,14858706,14858712⟩,
⟨64,168200655,168200751⟩]
theorem checked72667 : checkPrefixCuts (2^48) 9528541185 10 Manual.Count131072.C072667.packed 64 cuts72667 = true := by
 decide +kernel
def pointBounds72667 : List (Nat × Nat × Nat) := [(9528553472,116271996966921,116272386743241)]
theorem point_links_checked72667 : (cuts72667.take 1).map (fun c => (9528541185-1+2*2^10*c.k,116271982108215+c.lower,116272371884529+c.upper)) = pointBounds72667 := by
 decide +kernel
def cuts72668 : List PrefixCut := [⟨64,170118431,170118533⟩]
theorem checked72668 : checkPrefixCuts (2^48) 9528672257 10 Manual.Count131072.C072668.packed 64 cuts72668 = true := by
 decide +kernel
def cuts72669 : List PrefixCut := [⟨24,64484290,64484329⟩,
⟨64,168402826,168402931⟩]
theorem checked72669 : checkPrefixCuts (2^48) 9528803329 10 Manual.Count131072.C072669.packed 64 cuts72669 = true := by
 decide +kernel
def pointBounds72669 : List (Nat × Nat × Nat) := [(9528852480,116272384911591,116272774688142)]
theorem point_links_checked72669 : (cuts72669.take 1).map (fun c => (9528803329-1+2*2^10*c.k,116272320427301+c.lower,116272710203813+c.upper)) = pointBounds72669 := by
 decide +kernel
def cuts72670 : List PrefixCut := [⟨64,168518656,168518753⟩]
theorem checked72670 : checkPrefixCuts (2^48) 9528934401 10 Manual.Count131072.C072670.packed 64 cuts72670 = true := by
 decide +kernel
def cuts72671 : List PrefixCut := [⟨42,110769106,110769176⟩,
⟨64,169372947,169373050⟩]
theorem checked72671 : checkPrefixCuts (2^48) 9529065473 10 Manual.Count131072.C072671.packed 64 cuts72671 = true := by
 decide +kernel
def pointBounds72671 : List (Nat × Nat × Nat) := [(9529151488,116272768117889,116273157894673)]
theorem point_links_checked72671 : (cuts72671.take 1).map (fun c => (9529065473-1+2*2^10*c.k,116272657348783+c.lower,116273047125497+c.upper)) = pointBounds72671 := by
 decide +kernel
def cuts72672 : List PrefixCut := [⟨64,169636464,169636566⟩]
theorem checked72672 : checkPrefixCuts (2^48) 9529196545 10 Manual.Count131072.C072672.packed 64 cuts72672 = true := by
 decide +kernel
def cuts72673 : List PrefixCut := [⟨60,159030218,159030312⟩,
⟨64,169575054,169575154⟩]
theorem checked72673 : checkPrefixCuts (2^48) 9529327617 10 Manual.Count131072.C072673.packed 64 cuts72673 = true := by
 decide +kernel
def pointBounds72673 : List (Nat × Nat × Nat) := [(9529450496,116273155388412,116273545165425)]
theorem point_links_checked72673 : (cuts72673.take 1).map (fun c => (9529327617-1+2*2^10*c.k,116272996358194+c.lower,116273386135113+c.upper)) = pointBounds72673 := by
 decide +kernel
def cuts72674 : List PrefixCut := [⟨64,168243552,168243655⟩]
theorem checked72674 : checkPrefixCuts (2^48) 9529458689 10 Manual.Count131072.C072674.packed 64 cuts72674 = true := by
 decide +kernel
def cuts72675 : List PrefixCut := [⟨64,169511325,169511420⟩]
theorem checked72675 : checkPrefixCuts (2^48) 9529589761 10 Manual.Count131072.C072675.packed 64 cuts72675 = true := by
 decide +kernel
def cuts72676 : List PrefixCut := [⟨14,37245510,37245532⟩,
⟨64,170276923,170277021⟩]
theorem checked72676 : checkPrefixCuts (2^48) 9529720833 10 Manual.Count131072.C072676.packed 64 cuts72676 = true := by
 decide +kernel
def pointBounds72676 : List (Nat × Nat × Nat) := [(9529749504,116273540933635,116273930710874)]
theorem point_links_checked72676 : (cuts72676.take 1).map (fun c => (9529720833-1+2*2^10*c.k,116273503688125+c.lower,116273893465342+c.upper)) = pointBounds72676 := by
 decide +kernel
def cuts72677 : List PrefixCut := [⟨64,169477123,169477224⟩]
theorem checked72677 : checkPrefixCuts (2^48) 9529851905 10 Manual.Count131072.C072677.packed 64 cuts72677 = true := by
 decide +kernel
def cuts72678 : List PrefixCut := [⟨32,86627965,86628016⟩,
⟨64,170597142,170597245⟩]
theorem checked72678 : checkPrefixCuts (2^48) 9529982977 10 Manual.Count131072.C072678.packed 64 cuts72678 = true := by
 decide +kernel
def pointBounds72678 : List (Nat × Nat × Nat) := [(9530048512,116273930070136,116274319847603)]
theorem point_links_checked72678 : (cuts72678.take 1).map (fun c => (9529982977-1+2*2^10*c.k,116273843442171+c.lower,116274233219587+c.upper)) = pointBounds72678 := by
 decide +kernel
def cuts72679 : List PrefixCut := [⟨64,166253134,166253229⟩]
theorem checked72679 : checkPrefixCuts (2^48) 9530114049 10 Manual.Count131072.C072679.packed 64 cuts72679 = true := by
 decide +kernel
def cuts72680 : List PrefixCut := [⟨50,133024501,133024583⟩,
⟨64,168879437,168879542⟩]
theorem checked72680 : checkPrefixCuts (2^48) 9530245121 10 Manual.Count131072.C072680.packed 64 cuts72680 = true := by
 decide +kernel
def pointBounds72680 : List (Nat × Nat × Nat) := [(9530347520,116274313316948,116274703094644)]
theorem point_links_checked72680 : (cuts72680.take 1).map (fun c => (9530245121-1+2*2^10*c.k,116274180292447+c.lower,116274570070061+c.upper)) = pointBounds72680 := by
 decide +kernel
def cuts72681 : List PrefixCut := [⟨64,169526865,169526964⟩]
theorem checked72681 : checkPrefixCuts (2^48) 9530376193 10 Manual.Count131072.C072681.packed 64 cuts72681 = true := by
 decide +kernel
def cuts72682 : List PrefixCut := [⟨64,168608958,168609062⟩]
theorem checked72682 : checkPrefixCuts (2^48) 9530507265 10 Manual.Count131072.C072682.packed 64 cuts72682 = true := by
 decide +kernel
def cuts72683 : List PrefixCut := [⟨4,10809326,10809331⟩,
⟨64,167218587,167218687⟩]
theorem checked72683 : checkPrefixCuts (2^48) 9530638337 10 Manual.Count131072.C072683.packed 64 cuts72683 = true := by
 decide +kernel
def pointBounds72683 : List (Nat × Nat × Nat) := [(9530646528,116274698117033,116275087894960)]
theorem point_links_checked72683 : (cuts72683.take 1).map (fun c => (9530638337-1+2*2^10*c.k,116274687307707+c.lower,116275077085629+c.upper)) = pointBounds72683 := by
 decide +kernel
def cuts72684 : List PrefixCut := [⟨64,164646901,164646997⟩]
theorem checked72684 : checkPrefixCuts (2^48) 9530769409 10 Manual.Count131072.C072684.packed 64 cuts72684 = true := by
 decide +kernel
def cuts72685 : List PrefixCut := [⟨22,61516832,61516866⟩,
⟨64,170846525,170846622⟩]
theorem checked72685 : checkPrefixCuts (2^48) 9530900481 10 Manual.Count131072.C072685.packed 64 cuts72685 = true := by
 decide +kernel
def pointBounds72685 : List (Nat × Nat × Nat) := [(9530945536,116275080690027,116275470468179)]
theorem point_links_checked72685 : (cuts72685.take 1).map (fun c => (9530900481-1+2*2^10*c.k,116275019173195+c.lower,116275408951313+c.upper)) = pointBounds72685 := by
 decide +kernel
def cuts72686 : List PrefixCut := [⟨64,168274846,168274945⟩]
theorem checked72686 : checkPrefixCuts (2^48) 9531031553 10 Manual.Count131072.C072686.packed 64 cuts72686 = true := by
 decide +kernel
def cuts72687 : List PrefixCut := [⟨40,104159143,104159203⟩,
⟨64,167297989,167298088⟩]
theorem checked72687 : checkPrefixCuts (2^48) 9531162625 10 Manual.Count131072.C072687.packed 64 cuts72687 = true := by
 decide +kernel
def pointBounds72687 : List (Nat × Nat × Nat) := [(9531244544,116275462453709,116275852232083)]
theorem point_links_checked72687 : (cuts72687.take 1).map (fun c => (9531162625-1+2*2^10*c.k,116275358294566+c.lower,116275748072880+c.upper)) = pointBounds72687 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000083
