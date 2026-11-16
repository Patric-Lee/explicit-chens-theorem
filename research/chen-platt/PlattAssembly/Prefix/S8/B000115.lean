import PlattAssemblyKernel
import PlattCertificates.Count131072.C073680
import PlattCertificates.Count131072.C073681
import PlattCertificates.Count131072.C073682
import PlattCertificates.Count131072.C073683
import PlattCertificates.Count131072.C073684
import PlattCertificates.Count131072.C073685
import PlattCertificates.Count131072.C073686
import PlattCertificates.Count131072.C073687
import PlattCertificates.Count131072.C073688
import PlattCertificates.Count131072.C073689
import PlattCertificates.Count131072.C073690
import PlattCertificates.Count131072.C073691
import PlattCertificates.Count131072.C073692
import PlattCertificates.Count131072.C073693
import PlattCertificates.Count131072.C073694
import PlattCertificates.Count131072.C073695
import PlattCertificates.Count131072.C073696
import PlattCertificates.Count131072.C073697
import PlattCertificates.Count131072.C073698
import PlattCertificates.Count131072.C073699
import PlattCertificates.Count131072.C073700
import PlattCertificates.Count131072.C073701
import PlattCertificates.Count131072.C073702
import PlattCertificates.Count131072.C073703
import PlattCertificates.Count131072.C073704
import PlattCertificates.Count131072.C073705
import PlattCertificates.Count131072.C073706
import PlattCertificates.Count131072.C073707
import PlattCertificates.Count131072.C073708
import PlattCertificates.Count131072.C073709
import PlattCertificates.Count131072.C073710
import PlattCertificates.Count131072.C073711
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000115
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73680 : List PrefixCut := [⟨64,166384371,166384468⟩]
theorem checked73680 : checkPrefixCuts (2^48) 9661317121 10 Manual.Count131072.C073680.packed 64 cuts73680 = true := by
 decide +kernel
def cuts73681 : List PrefixCut := [⟨42,109222203,109222265⟩,
⟨64,166149047,166149143⟩]
theorem checked73681 : checkPrefixCuts (2^48) 9661448193 10 Manual.Count131072.C073681.packed 64 cuts73681 = true := by
 decide +kernel
def pointBounds73681 : List (Nat × Nat × Nat) := [(9661534208,116441752253887,116442142131489)]
theorem point_links_checked73681 : (cuts73681.take 1).map (fun c => (9661448193-1+2*2^10*c.k,116441643031684+c.lower,116442032909224+c.upper)) = pointBounds73681 := by
 decide +kernel
def cuts73682 : List PrefixCut := [⟨64,167749121,167749225⟩]
theorem checked73682 : checkPrefixCuts (2^48) 9661579265 10 Manual.Count131072.C073682.packed 64 cuts73682 = true := by
 decide +kernel
def cuts73683 : List PrefixCut := [⟨62,161512458,161512554⟩,
⟨64,166756334,166756432⟩]
theorem checked73683 : checkPrefixCuts (2^48) 9661710337 10 Manual.Count131072.C073683.packed 64 cuts73683 = true := by
 decide +kernel
def pointBounds73683 : List (Nat × Nat × Nat) := [(9661837312,116442138442310,116442528320146)]
theorem point_links_checked73683 : (cuts73683.take 1).map (fun c => (9661710337-1+2*2^10*c.k,116441976929852+c.lower,116442366807592+c.upper)) = pointBounds73683 := by
 decide +kernel
def cuts73684 : List PrefixCut := [⟨64,167307585,167307683⟩]
theorem checked73684 : checkPrefixCuts (2^48) 9661841409 10 Manual.Count131072.C073684.packed 64 cuts73684 = true := by
 decide +kernel
def cuts73685 : List PrefixCut := [⟨64,167013988,167014089⟩]
theorem checked73685 : checkPrefixCuts (2^48) 9661972481 10 Manual.Count131072.C073685.packed 64 cuts73685 = true := by
 decide +kernel
def cuts73686 : List PrefixCut := [⟨18,46261278,46261307⟩,
⟨64,163865512,163865613⟩]
theorem checked73686 : checkPrefixCuts (2^48) 9662103553 10 Manual.Count131072.C073686.packed 64 cuts73686 = true := by
 decide +kernel
def pointBounds73686 : List (Nat × Nat × Nat) := [(9662140416,116442524269037,116442914147103)]
theorem point_links_checked73686 : (cuts73686.take 1).map (fun c => (9662103553-1+2*2^10*c.k,116442478007759+c.lower,116442867885796+c.upper)) = pointBounds73686 := by
 decide +kernel
def cuts73687 : List PrefixCut := [⟨64,165290730,165290829⟩]
theorem checked73687 : checkPrefixCuts (2^48) 9662234625 10 Manual.Count131072.C073687.packed 64 cuts73687 = true := by
 decide +kernel
def cuts73688 : List PrefixCut := [⟨38,99569539,99569599⟩,
⟨64,166745026,166745126⟩]
theorem checked73688 : checkPrefixCuts (2^48) 9662365697 10 Manual.Count131072.C073688.packed 64 cuts73688 = true := by
 decide +kernel
def pointBounds73688 : List (Nat × Nat × Nat) := [(9662443520,116442906733540,116443296611837)]
theorem point_links_checked73688 : (cuts73688.take 1).map (fun c => (9662365697-1+2*2^10*c.k,116442807164001+c.lower,116443197042238+c.upper)) = pointBounds73688 := by
 decide +kernel
def cuts73689 : List PrefixCut := [⟨64,166742759,166742860⟩]
theorem checked73689 : checkPrefixCuts (2^48) 9662496769 10 Manual.Count131072.C073689.packed 64 cuts73689 = true := by
 decide +kernel
def cuts73690 : List PrefixCut := [⟨58,149466454,149466545⟩,
⟨64,164380956,164381056⟩]
theorem checked73690 : checkPrefixCuts (2^48) 9662627841 10 Manual.Count131072.C073690.packed 64 cuts73690 = true := by
 decide +kernel
def pointBounds73690 : List (Nat × Nat × Nat) := [(9662746624,116443290118240,116443679996769)]
theorem point_links_checked73690 : (cuts73690.take 1).map (fun c => (9662627841-1+2*2^10*c.k,116443140651786+c.lower,116443530530224+c.upper)) = pointBounds73690 := by
 decide +kernel
def cuts73691 : List PrefixCut := [⟨64,163737881,163737978⟩]
theorem checked73691 : checkPrefixCuts (2^48) 9662758913 10 Manual.Count131072.C073691.packed 64 cuts73691 = true := by
 decide +kernel
def cuts73692 : List PrefixCut := [⟨64,163298721,163298812⟩]
theorem checked73692 : checkPrefixCuts (2^48) 9662889985 10 Manual.Count131072.C073692.packed 64 cuts73692 = true := by
 decide +kernel
def cuts73693 : List PrefixCut := [⟨14,35886970,35886992⟩,
⟨64,165189885,165189979⟩]
theorem checked73693 : checkPrefixCuts (2^48) 9663021057 10 Manual.Count131072.C073693.packed 64 cuts73693 = true := by
 decide +kernel
def pointBounds73693 : List (Nat × Nat × Nat) := [(9663049728,116443667956314,116444057835062)]
theorem point_links_checked73693 : (cuts73693.take 1).map (fun c => (9663021057-1+2*2^10*c.k,116443632069344+c.lower,116444021948070+c.upper)) = pointBounds73693 := by
 decide +kernel
def cuts73694 : List PrefixCut := [⟨64,168187885,168187986⟩]
theorem checked73694 : checkPrefixCuts (2^48) 9663152129 10 Manual.Count131072.C073694.packed 64 cuts73694 = true := by
 decide +kernel
def cuts73695 : List PrefixCut := [⟨34,88345780,88345831⟩,
⟨64,166234013,166234109⟩]
theorem checked73695 : checkPrefixCuts (2^48) 9663283201 10 Manual.Count131072.C073695.packed 64 cuts73695 = true := by
 decide +kernel
def pointBounds73695 : List (Nat × Nat × Nat) := [(9663352832,116444053792894,116444443671866)]
theorem point_links_checked73695 : (cuts73695.take 1).map (fun c => (9663283201-1+2*2^10*c.k,116443965447114+c.lower,116444355326035+c.upper)) = pointBounds73695 := by
 decide +kernel
def cuts73696 : List PrefixCut := [⟨64,167338608,167338703⟩]
theorem checked73696 : checkPrefixCuts (2^48) 9663414273 10 Manual.Count131072.C073696.packed 64 cuts73696 = true := by
 decide +kernel
def cuts73697 : List PrefixCut := [⟨54,142869556,142869643⟩,
⟨64,169346121,169346223⟩]
theorem checked73697 : checkPrefixCuts (2^48) 9663545345 10 Manual.Count131072.C073697.packed 64 cuts73697 = true := by
 decide +kernel
def pointBounds73697 : List (Nat × Nat × Nat) := [(9663655936,116444441889291,116444831768490)]
theorem point_links_checked73697 : (cuts73697.take 1).map (fun c => (9663545345-1+2*2^10*c.k,116444299019735+c.lower,116444688898847+c.upper)) = pointBounds73697 := by
 decide +kernel
def cuts73698 : List PrefixCut := [⟨64,164450501,164450606⟩]
theorem checked73698 : checkPrefixCuts (2^48) 9663676417 10 Manual.Count131072.C073698.packed 64 cuts73698 = true := by
 decide +kernel
def cuts73699 : List PrefixCut := [⟨64,166574511,166574607⟩]
theorem checked73699 : checkPrefixCuts (2^48) 9663807489 10 Manual.Count131072.C073699.packed 64 cuts73699 = true := by
 decide +kernel
def cuts73700 : List PrefixCut := [⟨10,25951517,25951532⟩,
⟨64,168378062,168378160⟩]
theorem checked73700 : checkPrefixCuts (2^48) 9663938561 10 Manual.Count131072.C073700.packed 64 cuts73700 = true := by
 decide +kernel
def pointBounds73700 : List (Nat × Nat × Nat) := [(9663959040,116444825342385,116445215221815)]
theorem point_links_checked73700 : (cuts73700.take 1).map (fun c => (9663938561-1+2*2^10*c.k,116444799390868+c.lower,116445189270283+c.upper)) = pointBounds73700 := by
 decide +kernel
def cuts73701 : List PrefixCut := [⟨64,165026325,165026425⟩]
theorem checked73701 : checkPrefixCuts (2^48) 9664069633 10 Manual.Count131072.C073701.packed 64 cuts73701 = true := by
 decide +kernel
def cuts73702 : List PrefixCut := [⟨30,77852280,77852322⟩,
⟨64,166596862,166596960⟩]
theorem checked73702 : checkPrefixCuts (2^48) 9664200705 10 Manual.Count131072.C073702.packed 64 cuts73702 = true := by
 decide +kernel
def pointBounds73702 : List (Nat × Nat × Nat) := [(9664262144,116445210647535,116445600527190)]
theorem point_links_checked73702 : (cuts73702.take 1).map (fun c => (9664200705-1+2*2^10*c.k,116445132795255+c.lower,116445522674868+c.upper)) = pointBounds73702 := by
 decide +kernel
def cuts73703 : List PrefixCut := [⟨64,165196603,165196700⟩]
theorem checked73703 : checkPrefixCuts (2^48) 9664331777 10 Manual.Count131072.C073703.packed 64 cuts73703 = true := by
 decide +kernel
def cuts73704 : List PrefixCut := [⟨50,130186867,130186945⟩,
⟨64,166534095,166534194⟩]
theorem checked73704 : checkPrefixCuts (2^48) 9664462849 10 Manual.Count131072.C073704.packed 64 cuts73704 = true := by
 decide +kernel
def pointBounds73704 : List (Nat × Nat × Nat) := [(9664565248,116445594775587,116445984655473)]
theorem point_links_checked73704 : (cuts73704.take 1).map (fun c => (9664462849-1+2*2^10*c.k,116445464588720+c.lower,116445854468528+c.upper)) = pointBounds73704 := by
 decide +kernel
def cuts73705 : List PrefixCut := [⟨64,165978480,165978585⟩]
theorem checked73705 : checkPrefixCuts (2^48) 9664593921 10 Manual.Count131072.C073705.packed 64 cuts73705 = true := by
 decide +kernel
def cuts73706 : List PrefixCut := [⟨64,165131635,165131730⟩]
theorem checked73706 : checkPrefixCuts (2^48) 9664724993 10 Manual.Count131072.C073706.packed 64 cuts73706 = true := by
 decide +kernel
def cuts73707 : List PrefixCut := [⟨6,15406347,15406355⟩,
⟨64,168391212,168391311⟩]
theorem checked73707 : checkPrefixCuts (2^48) 9664856065 10 Manual.Count131072.C073707.packed 64 cuts73707 = true := by
 decide +kernel
def pointBounds73707 : List (Nat × Nat × Nat) := [(9664868352,116445977639277,116446367519392)]
theorem point_links_checked73707 : (cuts73707.take 1).map (fun c => (9664856065-1+2*2^10*c.k,116445962232930+c.lower,116446352113037+c.upper)) = pointBounds73707 := by
 decide +kernel
def cuts73708 : List PrefixCut := [⟨64,165680492,165680588⟩]
theorem checked73708 : checkPrefixCuts (2^48) 9664987137 10 Manual.Count131072.C073708.packed 64 cuts73708 = true := by
 decide +kernel
def cuts73709 : List PrefixCut := [⟨26,66632685,66632728⟩,
⟨64,165823849,165823950⟩]
theorem checked73709 : checkPrefixCuts (2^48) 9665118209 10 Manual.Count131072.C073709.packed 64 cuts73709 = true := by
 decide +kernel
def pointBounds73709 : List (Nat × Nat × Nat) := [(9665171456,116446362937319,116446752817664)]
theorem point_links_checked73709 : (cuts73709.take 1).map (fun c => (9665118209-1+2*2^10*c.k,116446296304634+c.lower,116446686184936+c.upper)) = pointBounds73709 := by
 decide +kernel
def cuts73710 : List PrefixCut := [⟨64,165559505,165559605⟩]
theorem checked73710 : checkPrefixCuts (2^48) 9665249281 10 Manual.Count131072.C073710.packed 64 cuts73710 = true := by
 decide +kernel
def cuts73711 : List PrefixCut := [⟨46,120768215,120768286⟩,
⟨64,168207349,168207448⟩]
theorem checked73711 : checkPrefixCuts (2^48) 9665380353 10 Manual.Count131072.C073711.packed 64 cuts73711 = true := by
 decide +kernel
def pointBounds73711 : List (Nat × Nat × Nat) := [(9665474560,116446748456203,116447138336777)]
theorem point_links_checked73711 : (cuts73711.take 1).map (fun c => (9665380353-1+2*2^10*c.k,116446627687988+c.lower,116447017568491+c.upper)) = pointBounds73711 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000115
