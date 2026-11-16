import PlattAssemblyKernel
import PlattCertificates.Count131072.C057776
import PlattCertificates.Count131072.C057777
import PlattCertificates.Count131072.C057778
import PlattCertificates.Count131072.C057779
import PlattCertificates.Count131072.C057780
import PlattCertificates.Count131072.C057781
import PlattCertificates.Count131072.C057782
import PlattCertificates.Count131072.C057783
import PlattCertificates.Count131072.C057784
import PlattCertificates.Count131072.C057785
import PlattCertificates.Count131072.C057786
import PlattCertificates.Count131072.C057787
import PlattCertificates.Count131072.C057788
import PlattCertificates.Count131072.C057789
import PlattCertificates.Count131072.C057790
import PlattCertificates.Count131072.C057791
import PlattCertificates.Count131072.C057792
import PlattCertificates.Count131072.C057793
import PlattCertificates.Count131072.C057794
import PlattCertificates.Count131072.C057795
import PlattCertificates.Count131072.C057796
import PlattCertificates.Count131072.C057797
import PlattCertificates.Count131072.C057798
import PlattCertificates.Count131072.C057799
import PlattCertificates.Count131072.C057800
import PlattCertificates.Count131072.C057801
import PlattCertificates.Count131072.C057802
import PlattCertificates.Count131072.C057803
import PlattCertificates.Count131072.C057804
import PlattCertificates.Count131072.C057805
import PlattCertificates.Count131072.C057806
import PlattCertificates.Count131072.C057807
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000243
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57776 : List PrefixCut := [⟨64,211269252,211269376⟩]
theorem checked57776 : checkPrefixCuts (2^48) 7576748033 10 Manual.Count131072.C057776.packed 64 cuts57776 = true := by
 decide +kernel
def cuts57777 : List PrefixCut := [⟨12,41049785,41049808⟩,
⟨64,213568835,213568956⟩]
theorem checked57777 : checkPrefixCuts (2^48) 7576879105 10 Manual.Count131072.C057777.packed 64 cuts57777 = true := by
 decide +kernel
def pointBounds57777 : List (Nat × Nat × Nat) := [(7576903680,113450354843809,113450742984916)]
theorem point_links_checked57777 : (cuts57777.take 1).map (fun c => (7576879105-1+2*2^10*c.k,113450313794024+c.lower,113450701935108+c.upper)) = pointBounds57777 := by
 decide +kernel
def cuts57778 : List PrefixCut := [⟨64,211967761,211967884⟩]
theorem checked57778 : checkPrefixCuts (2^48) 7577010177 10 Manual.Count131072.C057778.packed 64 cuts57778 = true := by
 decide +kernel
def pointBounds57778 : List (Nat × Nat × Nat) := [(7577141248,113450739330620,113451127471948)]
theorem point_links_checked57778 : (cuts57778.take 1).map (fun c => (7577010177-1+2*2^10*c.k,113450527362859+c.lower,113450915504064+c.upper)) = pointBounds57778 := by
 decide +kernel
def cuts57779 : List PrefixCut := [⟨64,218056311,218056431⟩]
theorem checked57779 : checkPrefixCuts (2^48) 7577141249 10 Manual.Count131072.C057779.packed 64 cuts57779 = true := by
 decide +kernel
def cuts57780 : List PrefixCut := [⟨52,175370980,175371079⟩,
⟨64,214709310,214709433⟩]
theorem checked57780 : checkPrefixCuts (2^48) 7577272321 10 Manual.Count131072.C057780.packed 64 cuts57780 = true := by
 decide +kernel
def pointBounds57780 : List (Nat × Nat × Nat) := [(7577378816,113451132757911,113451520899458)]
theorem point_links_checked57780 : (cuts57780.take 1).map (fun c => (7577272321-1+2*2^10*c.k,113450957386931+c.lower,113451345528379+c.upper)) = pointBounds57780 := by
 decide +kernel
def cuts57781 : List PrefixCut := [⟨64,212848264,212848387⟩]
theorem checked57781 : checkPrefixCuts (2^48) 7577403393 10 Manual.Count131072.C057781.packed 64 cuts57781 = true := by
 decide +kernel
def cuts57782 : List PrefixCut := [⟨40,133130450,133130522⟩,
⟨64,214330409,214330527⟩]
theorem checked57782 : checkPrefixCuts (2^48) 7577534465 10 Manual.Count131072.C057782.packed 64 cuts57782 = true := by
 decide +kernel
def pointBounds57782 : List (Nat × Nat × Nat) := [(7577616384,113451518074955,113451906216721)]
theorem point_links_checked57782 : (cuts57782.take 1).map (fun c => (7577534465-1+2*2^10*c.k,113451384944505+c.lower,113451773086199+c.upper)) = pointBounds57782 := by
 decide +kernel
def cuts57783 : List PrefixCut := [⟨64,213620968,213621093⟩]
theorem checked57783 : checkPrefixCuts (2^48) 7577665537 10 Manual.Count131072.C057783.packed 64 cuts57783 = true := by
 decide +kernel
def cuts57784 : List PrefixCut := [⟨28,91709886,91709940⟩,
⟨64,209642805,209642923⟩]
theorem checked57784 : checkPrefixCuts (2^48) 7577796609 10 Manual.Count131072.C057784.packed 64 cuts57784 = true := by
 decide +kernel
def pointBounds57784 : List (Nat × Nat × Nat) := [(7577853952,113451904605768,113452292747759)]
theorem point_links_checked57784 : (cuts57784.take 1).map (fun c => (7577796609-1+2*2^10*c.k,113451812895882+c.lower,113452201037819+c.upper)) = pointBounds57784 := by
 decide +kernel
def cuts57785 : List PrefixCut := [⟨64,213502117,213502238⟩]
theorem checked57785 : checkPrefixCuts (2^48) 7577927681 10 Manual.Count131072.C057785.packed 64 cuts57785 = true := by
 decide +kernel
def cuts57786 : List PrefixCut := [⟨16,53263528,53263557⟩,
⟨64,213275577,213275700⟩]
theorem checked57786 : checkPrefixCuts (2^48) 7578058753 10 Manual.Count131072.C057786.packed 64 cuts57786 = true := by
 decide +kernel
def pointBounds57786 : List (Nat × Nat × Nat) := [(7578091520,113452289304332,113452677446537)]
theorem point_links_checked57786 : (cuts57786.take 1).map (fun c => (7578058753-1+2*2^10*c.k,113452236040804+c.lower,113452624182980+c.upper)) = pointBounds57786 := by
 decide +kernel
def cuts57787 : List PrefixCut := [⟨64,214423288,214423414⟩]
theorem checked57787 : checkPrefixCuts (2^48) 7578189825 10 Manual.Count131072.C057787.packed 64 cuts57787 = true := by
 decide +kernel
def cuts57788 : List PrefixCut := [⟨4,12999734,12999742⟩,
⟨64,216759518,216759639⟩]
theorem checked57788 : checkPrefixCuts (2^48) 7578320897 10 Manual.Count131072.C057788.packed 64 cuts57788 = true := by
 decide +kernel
def pointBounds57788 : List (Nat × Nat × Nat) := [(7578329088,113452676739403,113453064881836)]
theorem point_links_checked57788 : (cuts57788.take 1).map (fun c => (7578320897-1+2*2^10*c.k,113452663739669+c.lower,113453051882094+c.upper)) = pointBounds57788 := by
 decide +kernel
def cuts57789 : List PrefixCut := [⟨56,186634500,186634608⟩,
⟨64,213561633,213561757⟩]
theorem checked57789 : checkPrefixCuts (2^48) 7578451969 10 Manual.Count131072.C057789.packed 64 cuts57789 = true := by
 decide +kernel
def pointBounds57789 : List (Nat × Nat × Nat) := [(7578566656,113453067133687,113453455276341)]
theorem point_links_checked57789 : (cuts57789.take 1).map (fun c => (7578451969-1+2*2^10*c.k,113452880499187+c.lower,113453268641733+c.upper)) = pointBounds57789 := by
 decide +kernel
def cuts57790 : List PrefixCut := [⟨64,209398215,209398336⟩]
theorem checked57790 : checkPrefixCuts (2^48) 7578583041 10 Manual.Count131072.C057790.packed 64 cuts57790 = true := by
 decide +kernel
def cuts57791 : List PrefixCut := [⟨44,145365854,145365940⟩,
⟨64,212291503,212291627⟩]
theorem checked57791 : checkPrefixCuts (2^48) 7578714113 10 Manual.Count131072.C057791.packed 64 cuts57791 = true := by
 decide +kernel
def pointBounds57791 : List (Nat × Nat × Nat) := [(7578804224,113453448824889,113453836967766)]
theorem point_links_checked57791 : (cuts57791.take 1).map (fun c => (7578714113-1+2*2^10*c.k,113453303459035+c.lower,113453691601826+c.upper)) = pointBounds57791 := by
 decide +kernel
def cuts57792 : List PrefixCut := [⟨64,214664736,214664858⟩]
theorem checked57792 : checkPrefixCuts (2^48) 7578845185 10 Manual.Count131072.C057792.packed 64 cuts57792 = true := by
 decide +kernel
def cuts57793 : List PrefixCut := [⟨32,105993994,105994054⟩,
⟨64,211987058,211987179⟩]
theorem checked57793 : checkPrefixCuts (2^48) 7578976257 10 Manual.Count131072.C057793.packed 64 cuts57793 = true := by
 decide +kernel
def pointBounds57793 : List (Nat × Nat × Nat) := [(7579041792,113453836409268,113454224552365)]
theorem point_links_checked57793 : (cuts57793.take 1).map (fun c => (7578976257-1+2*2^10*c.k,113453730415274+c.lower,113454118558311+c.upper)) = pointBounds57793 := by
 decide +kernel
def cuts57794 : List PrefixCut := [⟨64,213171787,213171909⟩]
theorem checked57794 : checkPrefixCuts (2^48) 7579107329 10 Manual.Count131072.C057794.packed 64 cuts57794 = true := by
 decide +kernel
def cuts57795 : List PrefixCut := [⟨20,63987955,63987992⟩,
⟨64,211831160,211831282⟩]
theorem checked57795 : checkPrefixCuts (2^48) 7579238401 10 Manual.Count131072.C057795.packed 64 cuts57795 = true := by
 decide +kernel
def pointBounds57795 : List (Nat × Nat × Nat) := [(7579279360,113454219562074,113454607705391)]
theorem point_links_checked57795 : (cuts57795.take 1).map (fun c => (7579238401-1+2*2^10*c.k,113454155574119+c.lower,113454543717399+c.upper)) = pointBounds57795 := by
 decide +kernel
def cuts57796 : List PrefixCut := [⟨64,214389947,214390068⟩]
theorem checked57796 : checkPrefixCuts (2^48) 7579369473 10 Manual.Count131072.C057796.packed 64 cuts57796 = true := by
 decide +kernel
def cuts57797 : List PrefixCut := [⟨8,25921135,25921151⟩,
⟨64,214200533,214200655⟩]
theorem checked57797 : checkPrefixCuts (2^48) 7579500545 10 Manual.Count131072.C057797.packed 64 cuts57797 = true := by
 decide +kernel
def pointBounds57797 : List (Nat × Nat × Nat) := [(7579516928,113454607716361,113454995859900)]
theorem point_links_checked57797 : (cuts57797.take 1).map (fun c => (7579500545-1+2*2^10*c.k,113454581795226+c.lower,113454969938749+c.upper)) = pointBounds57797 := by
 decide +kernel
def cuts57798 : List PrefixCut := [⟨60,203204877,203204996⟩,
⟨64,215570857,215570982⟩]
theorem checked57798 : checkPrefixCuts (2^48) 7579631617 10 Manual.Count131072.C057798.packed 64 cuts57798 = true := by
 decide +kernel
def pointBounds57798 : List (Nat × Nat × Nat) := [(7579754496,113454999200636,113455387344400)]
theorem point_links_checked57798 : (cuts57798.take 1).map (fun c => (7579631617-1+2*2^10*c.k,113454795995759+c.lower,113455184139404+c.upper)) = pointBounds57798 := by
 decide +kernel
def cuts57799 : List PrefixCut := [⟨64,214935846,214935967⟩]
theorem checked57799 : checkPrefixCuts (2^48) 7579762689 10 Manual.Count131072.C057799.packed 64 cuts57799 = true := by
 decide +kernel
def cuts57800 : List PrefixCut := [⟨48,157486028,157486119⟩,
⟨64,211033039,211033161⟩]
theorem checked57800 : checkPrefixCuts (2^48) 7579893761 10 Manual.Count131072.C057800.packed 64 cuts57800 = true := by
 decide +kernel
def pointBounds57800 : List (Nat × Nat × Nat) := [(7579992064,113455383988490,113455772132472)]
theorem point_links_checked57800 : (cuts57800.take 1).map (fun c => (7579893761-1+2*2^10*c.k,113455226502462+c.lower,113455614646353+c.upper)) = pointBounds57800 := by
 decide +kernel
def cuts57801 : List PrefixCut := [⟨64,216265197,216265321⟩]
theorem checked57801 : checkPrefixCuts (2^48) 7580024833 10 Manual.Count131072.C057801.packed 64 cuts57801 = true := by
 decide +kernel
def cuts57802 : List PrefixCut := [⟨36,120385013,120385081⟩,
⟨64,214033489,214033611⟩]
theorem checked57802 : checkPrefixCuts (2^48) 7580155905 10 Manual.Count131072.C057802.packed 64 cuts57802 = true := by
 decide +kernel
def pointBounds57802 : List (Nat × Nat × Nat) := [(7580229632,113455774185711,113456162329916)]
theorem point_links_checked57802 : (cuts57802.take 1).map (fun c => (7580155905-1+2*2^10*c.k,113455653800698+c.lower,113456041944835+c.upper)) = pointBounds57802 := by
 decide +kernel
def cuts57803 : List PrefixCut := [⟨64,214475373,214475496⟩]
theorem checked57803 : checkPrefixCuts (2^48) 7580286977 10 Manual.Count131072.C057803.packed 64 cuts57803 = true := by
 decide +kernel
def cuts57804 : List PrefixCut := [⟨24,78719257,78719301⟩,
⟨64,211426881,211427000⟩]
theorem checked57804 : checkPrefixCuts (2^48) 7580418049 10 Manual.Count131072.C057804.packed 64 cuts57804 = true := by
 decide +kernel
def pointBounds57804 : List (Nat × Nat × Nat) := [(7580467200,113456161028817,113456549173243)]
theorem point_links_checked57804 : (cuts57804.take 1).map (fun c => (7580418049-1+2*2^10*c.k,113456082309560+c.lower,113456470453942+c.upper)) = pointBounds57804 := by
 decide +kernel
def cuts57805 : List PrefixCut := [⟨64,215173465,215173587⟩]
theorem checked57805 : checkPrefixCuts (2^48) 7580549121 10 Manual.Count131072.C057805.packed 64 cuts57805 = true := by
 decide +kernel
def cuts57806 : List PrefixCut := [⟨12,40026678,40026701⟩,
⟨64,214278601,214278726⟩]
theorem checked57806 : checkPrefixCuts (2^48) 7580680193 10 Manual.Count131072.C057806.packed 64 cuts57806 = true := by
 decide +kernel
def pointBounds57806 : List (Nat × Nat × Nat) := [(7580704768,113456548936584,113456937081230)]
theorem point_links_checked57806 : (cuts57806.take 1).map (fun c => (7580680193-1+2*2^10*c.k,113456508909906+c.lower,113456897054529+c.upper)) = pointBounds57806 := by
 decide +kernel
def cuts57807 : List PrefixCut := [⟨64,213866471,213866591⟩]
theorem checked57807 : checkPrefixCuts (2^48) 7580811265 10 Manual.Count131072.C057807.packed 64 cuts57807 = true := by
 decide +kernel
def pointBounds57807 : List (Nat × Nat × Nat) := [(7580942336,113456937054978,113457325199846)]
theorem point_links_checked57807 : (cuts57807.take 1).map (fun c => (7580811265-1+2*2^10*c.k,113456723188507+c.lower,113457111333255+c.upper)) = pointBounds57807 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000243
