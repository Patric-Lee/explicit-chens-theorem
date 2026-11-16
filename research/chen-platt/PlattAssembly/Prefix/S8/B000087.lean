import PlattAssemblyKernel
import PlattCertificates.Count131072.C072784
import PlattCertificates.Count131072.C072785
import PlattCertificates.Count131072.C072786
import PlattCertificates.Count131072.C072787
import PlattCertificates.Count131072.C072788
import PlattCertificates.Count131072.C072789
import PlattCertificates.Count131072.C072790
import PlattCertificates.Count131072.C072791
import PlattCertificates.Count131072.C072792
import PlattCertificates.Count131072.C072793
import PlattCertificates.Count131072.C072794
import PlattCertificates.Count131072.C072795
import PlattCertificates.Count131072.C072796
import PlattCertificates.Count131072.C072797
import PlattCertificates.Count131072.C072798
import PlattCertificates.Count131072.C072799
import PlattCertificates.Count131072.C072800
import PlattCertificates.Count131072.C072801
import PlattCertificates.Count131072.C072802
import PlattCertificates.Count131072.C072803
import PlattCertificates.Count131072.C072804
import PlattCertificates.Count131072.C072805
import PlattCertificates.Count131072.C072806
import PlattCertificates.Count131072.C072807
import PlattCertificates.Count131072.C072808
import PlattCertificates.Count131072.C072809
import PlattCertificates.Count131072.C072810
import PlattCertificates.Count131072.C072811
import PlattCertificates.Count131072.C072812
import PlattCertificates.Count131072.C072813
import PlattCertificates.Count131072.C072814
import PlattCertificates.Count131072.C072815
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000087
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72784 : List PrefixCut := [⟨64,166042873,166042971⟩]
theorem checked72784 : checkPrefixCuts (2^48) 9543876609 10 Manual.Count131072.C072784.packed 64 cuts72784 = true := by
 decide +kernel
def cuts72785 : List PrefixCut := [⟨46,121950120,121950197⟩,
⟨64,167131815,167131919⟩]
theorem checked72785 : checkPrefixCuts (2^48) 9544007681 10 Manual.Count131072.C072785.packed 64 cuts72785 = true := by
 decide +kernel
def pointBounds72785 : List (Nat × Nat × Nat) := [(9544101888,116291968531172,116292358319379)]
theorem point_links_checked72785 : (cuts72785.take 1).map (fun c => (9544007681-1+2*2^10*c.k,116291846581052+c.lower,116292236369182+c.upper)) = pointBounds72785 := by
 decide +kernel
def cuts72786 : List PrefixCut := [⟨64,171435300,171435401⟩]
theorem checked72786 : checkPrefixCuts (2^48) 9544138753 10 Manual.Count131072.C072786.packed 64 cuts72786 = true := by
 decide +kernel
def cuts72787 : List PrefixCut := [⟨64,167510602,167510700⟩]
theorem checked72787 : checkPrefixCuts (2^48) 9544269825 10 Manual.Count131072.C072787.packed 64 cuts72787 = true := by
 decide +kernel
def pointBounds72787 : List (Nat × Nat × Nat) := [(9544400896,116292352658769,116292742447202)]
theorem point_links_checked72787 : (cuts72787.take 1).map (fun c => (9544269825-1+2*2^10*c.k,116292185148167+c.lower,116292574936502+c.upper)) = pointBounds72787 := by
 decide +kernel
def cuts72788 : List PrefixCut := [⟨64,166712052,166712154⟩]
theorem checked72788 : checkPrefixCuts (2^48) 9544400897 10 Manual.Count131072.C072788.packed 64 cuts72788 = true := by
 decide +kernel
def cuts72789 : List PrefixCut := [⟨64,167859888,167859994⟩]
theorem checked72789 : checkPrefixCuts (2^48) 9544531969 10 Manual.Count131072.C072789.packed 64 cuts72789 = true := by
 decide +kernel
def cuts72790 : List PrefixCut := [⟨18,48305006,48305031⟩,
⟨64,168476886,168476979⟩]
theorem checked72790 : checkPrefixCuts (2^48) 9544663041 10 Manual.Count131072.C072790.packed 64 cuts72790 = true := by
 decide +kernel
def pointBounds72790 : List (Nat × Nat × Nat) := [(9544699904,116292735535715,116293125324381)]
theorem point_links_checked72790 : (cuts72790.take 1).map (fun c => (9544663041-1+2*2^10*c.k,116292687230709+c.lower,116293077019350+c.upper)) = pointBounds72790 := by
 decide +kernel
def cuts72791 : List PrefixCut := [⟨64,168592518,168592615⟩]
theorem checked72791 : checkPrefixCuts (2^48) 9544794113 10 Manual.Count131072.C072791.packed 64 cuts72791 = true := by
 decide +kernel
def cuts72792 : List PrefixCut := [⟨36,93776186,93776241⟩,
⟨64,166142596,166142696⟩]
theorem checked72792 : checkPrefixCuts (2^48) 9544925185 10 Manual.Count131072.C072792.packed 64 cuts72792 = true := by
 decide +kernel
def pointBounds72792 : List (Nat × Nat × Nat) := [(9544998912,116293118076299,116293507865185)]
theorem point_links_checked72792 : (cuts72792.take 1).map (fun c => (9544925185-1+2*2^10*c.k,116293024300113+c.lower,116293414088944+c.upper)) = pointBounds72792 := by
 decide +kernel
def cuts72793 : List PrefixCut := [⟨64,168145551,168145649⟩]
theorem checked72793 : checkPrefixCuts (2^48) 9545056257 10 Manual.Count131072.C072793.packed 64 cuts72793 = true := by
 decide +kernel
def cuts72794 : List PrefixCut := [⟨54,143196165,143196252⟩,
⟨64,169234331,169234435⟩]
theorem checked72794 : checkPrefixCuts (2^48) 9545187329 10 Manual.Count131072.C072794.packed 64 cuts72794 = true := by
 decide +kernel
def pointBounds72794 : List (Nat × Nat × Nat) := [(9545297920,116293501784425,116293891573541)]
theorem point_links_checked72794 : (cuts72794.take 1).map (fun c => (9545187329-1+2*2^10*c.k,116293358588260+c.lower,116293748377289+c.upper)) = pointBounds72794 := by
 decide +kernel
def cuts72795 : List PrefixCut := [⟨64,167167829,167167930⟩]
theorem checked72795 : checkPrefixCuts (2^48) 9545318401 10 Manual.Count131072.C072795.packed 64 cuts72795 = true := by
 decide +kernel
def cuts72796 : List PrefixCut := [⟨64,167902740,167902839⟩]
theorem checked72796 : checkPrefixCuts (2^48) 9545449473 10 Manual.Count131072.C072796.packed 64 cuts72796 = true := by
 decide +kernel
def cuts72797 : List PrefixCut := [⟨8,22439936,22439948⟩,
⟨64,171055566,171055676⟩]
theorem checked72797 : checkPrefixCuts (2^48) 9545580545 10 Manual.Count131072.C072797.packed 64 cuts72797 = true := by
 decide +kernel
def pointBounds72797 : List (Nat × Nat × Nat) := [(9545596928,116293885333096,116294275122441)]
theorem point_links_checked72797 : (cuts72797.take 1).map (fun c => (9545580545-1+2*2^10*c.k,116293862893160+c.lower,116294252682493+c.upper)) = pointBounds72797 := by
 decide +kernel
def cuts72798 : List PrefixCut := [⟨64,169342970,169343071⟩]
theorem checked72798 : checkPrefixCuts (2^48) 9545711617 10 Manual.Count131072.C072798.packed 64 cuts72798 = true := by
 decide +kernel
def cuts72799 : List PrefixCut := [⟨26,69588294,69588334⟩,
⟨64,169458602,169458703⟩]
theorem checked72799 : checkPrefixCuts (2^48) 9545842689 10 Manual.Count131072.C072799.packed 64 cuts72799 = true := by
 decide +kernel
def pointBounds72799 : List (Nat × Nat × Nat) := [(9545895936,116294272879990,116294662669574)]
theorem point_links_checked72799 : (cuts72799.take 1).map (fun c => (9545842689-1+2*2^10*c.k,116294203291696+c.lower,116294593081240+c.upper)) = pointBounds72799 := by
 decide +kernel
def cuts72800 : List PrefixCut := [⟨64,169249869,169249974⟩]
theorem checked72800 : checkPrefixCuts (2^48) 9545973761 10 Manual.Count131072.C072800.packed 64 cuts72800 = true := by
 decide +kernel
def cuts72801 : List PrefixCut := [⟨44,116026224,116026296⟩,
⟨64,168274521,168274625⟩]
theorem checked72801 : checkPrefixCuts (2^48) 9546104833 10 Manual.Count131072.C072801.packed 64 cuts72801 = true := by
 decide +kernel
def pointBounds72801 : List (Nat × Nat × Nat) := [(9546194944,116294658026391,116295047816213)]
theorem point_links_checked72801 : (cuts72801.take 1).map (fun c => (9546104833-1+2*2^10*c.k,116294542000167+c.lower,116294931789917+c.upper)) = pointBounds72801 := by
 decide +kernel
def cuts72802 : List PrefixCut := [⟨64,169658005,169658103⟩]
theorem checked72802 : checkPrefixCuts (2^48) 9546235905 10 Manual.Count131072.C072802.packed 64 cuts72802 = true := by
 decide +kernel
def cuts72803 : List PrefixCut := [⟨62,162638325,162638422⟩,
⟨64,168151950,168152051⟩]
theorem checked72803 : checkPrefixCuts (2^48) 9546366977 10 Manual.Count131072.C072803.packed 64 cuts72803 = true := by
 decide +kernel
def pointBounds72803 : List (Nat × Nat × Nat) := [(9546493952,116295042571018,116295432361067)]
theorem point_links_checked72803 : (cuts72803.take 1).map (fun c => (9546366977-1+2*2^10*c.k,116294879932693+c.lower,116295269722645+c.upper)) = pointBounds72803 := by
 decide +kernel
def cuts72804 : List PrefixCut := [⟨64,166970277,166970381⟩]
theorem checked72804 : checkPrefixCuts (2^48) 9546498049 10 Manual.Count131072.C072804.packed 64 cuts72804 = true := by
 decide +kernel
def cuts72805 : List PrefixCut := [⟨64,166289855,166289957⟩]
theorem checked72805 : checkPrefixCuts (2^48) 9546629121 10 Manual.Count131072.C072805.packed 64 cuts72805 = true := by
 decide +kernel
def cuts72806 : List PrefixCut := [⟨16,42132297,42132320⟩,
⟨64,168734708,168734800⟩]
theorem checked72806 : checkPrefixCuts (2^48) 9546760193 10 Manual.Count131072.C072806.packed 64 cuts72806 = true := by
 decide +kernel
def pointBounds72806 : List (Nat × Nat × Nat) := [(9546792960,116295423477072,116295813267354)]
theorem point_links_checked72806 : (cuts72806.take 1).map (fun c => (9546760193-1+2*2^10*c.k,116295381344775+c.lower,116295771135034+c.upper)) = pointBounds72806 := by
 decide +kernel
def cuts72807 : List PrefixCut := [⟨64,166462186,166462283⟩]
theorem checked72807 : checkPrefixCuts (2^48) 9546891265 10 Manual.Count131072.C072807.packed 64 cuts72807 = true := by
 decide +kernel
def cuts72808 : List PrefixCut := [⟨34,90040767,90040819⟩,
⟨64,170823347,170823451⟩]
theorem checked72808 : checkPrefixCuts (2^48) 9547022337 10 Manual.Count131072.C072808.packed 64 cuts72808 = true := by
 decide +kernel
def pointBounds72808 : List (Nat × Nat × Nat) := [(9547091968,116295806582436,116296196372936)]
theorem point_links_checked72808 : (cuts72808.take 1).map (fun c => (9547022337-1+2*2^10*c.k,116295716541669+c.lower,116296106332117+c.upper)) = pointBounds72808 := by
 decide +kernel
def cuts72809 : List PrefixCut := [⟨64,166752425,166752528⟩]
theorem checked72809 : checkPrefixCuts (2^48) 9547153409 10 Manual.Count131072.C072809.packed 64 cuts72809 = true := by
 decide +kernel
def cuts72810 : List PrefixCut := [⟨52,137799002,137799084⟩,
⟨64,169698339,169698440⟩]
theorem checked72810 : checkPrefixCuts (2^48) 9547284481 10 Manual.Count131072.C072810.packed 64 cuts72810 = true := by
 decide +kernel
def pointBounds72810 : List (Nat × Nat × Nat) := [(9547390976,116296191916443,116296581707180)]
theorem point_links_checked72810 : (cuts72810.take 1).map (fun c => (9547284481-1+2*2^10*c.k,116296054117441+c.lower,116296443908096+c.upper)) = pointBounds72810 := by
 decide +kernel
def cuts72811 : List PrefixCut := [⟨64,167278533,167278630⟩]
theorem checked72811 : checkPrefixCuts (2^48) 9547415553 10 Manual.Count131072.C072811.packed 64 cuts72811 = true := by
 decide +kernel
def cuts72812 : List PrefixCut := [⟨64,165271503,165271604⟩]
theorem checked72812 : checkPrefixCuts (2^48) 9547546625 10 Manual.Count131072.C072812.packed 64 cuts72812 = true := by
 decide +kernel
def cuts72813 : List PrefixCut := [⟨6,15654390,15654399⟩,
⟨64,166595870,166595967⟩]
theorem checked72813 : checkPrefixCuts (2^48) 9547677697 10 Manual.Count131072.C072813.packed 64 cuts72813 = true := by
 decide +kernel
def pointBounds72813 : List (Nat × Nat × Nat) := [(9547689984,116296572020206,116296961811169)]
theorem point_links_checked72813 : (cuts72813.take 1).map (fun c => (9547677697-1+2*2^10*c.k,116296556365816+c.lower,116296946156770+c.upper)) = pointBounds72813 := by
 decide +kernel
def cuts72814 : List PrefixCut := [⟨64,166711507,166711614⟩]
theorem checked72814 : checkPrefixCuts (2^48) 9547808769 10 Manual.Count131072.C072814.packed 64 cuts72814 = true := by
 decide +kernel
def cuts72815 : List PrefixCut := [⟨24,61701837,61701877⟩,
⟨64,168507490,168507590⟩]
theorem checked72815 : checkPrefixCuts (2^48) 9547939841 10 Manual.Count131072.C072815.packed 64 cuts72815 = true := by
 decide +kernel
def pointBounds72815 : List (Nat × Nat × Nat) := [(9547988992,116296951375030,116297341166228)]
theorem point_links_checked72815 : (cuts72815.take 1).map (fun c => (9547939841-1+2*2^10*c.k,116296889673193+c.lower,116297279464351+c.upper)) = pointBounds72815 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000087
