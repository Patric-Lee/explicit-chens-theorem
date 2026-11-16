import PlattAssemblyKernel
import PlattCertificates.Count131072.C061760
import PlattCertificates.Count131072.C061761
import PlattCertificates.Count131072.C061762
import PlattCertificates.Count131072.C061763
import PlattCertificates.Count131072.C061764
import PlattCertificates.Count131072.C061765
import PlattCertificates.Count131072.C061766
import PlattCertificates.Count131072.C061767
import PlattCertificates.Count131072.C061768
import PlattCertificates.Count131072.C061769
import PlattCertificates.Count131072.C061770
import PlattCertificates.Count131072.C061771
import PlattCertificates.Count131072.C061772
import PlattCertificates.Count131072.C061773
import PlattCertificates.Count131072.C061774
import PlattCertificates.Count131072.C061775
import PlattCertificates.Count131072.C061776
import PlattCertificates.Count131072.C061777
import PlattCertificates.Count131072.C061778
import PlattCertificates.Count131072.C061779
import PlattCertificates.Count131072.C061780
import PlattCertificates.Count131072.C061781
import PlattCertificates.Count131072.C061782
import PlattCertificates.Count131072.C061783
import PlattCertificates.Count131072.C061784
import PlattCertificates.Count131072.C061785
import PlattCertificates.Count131072.C061786
import PlattCertificates.Count131072.C061787
import PlattCertificates.Count131072.C061788
import PlattCertificates.Count131072.C061789
import PlattCertificates.Count131072.C061790
import PlattCertificates.Count131072.C061791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61760 : List PrefixCut := [⟨64,200219289,200219399⟩]
theorem checked61760 : checkPrefixCuts (2^48) 8098938881 10 Manual.Count131072.C061760.packed 64 cuts61760 = true := by
 decide +kernel
def cuts61761 : List PrefixCut := [⟨24,74651322,74651362⟩,
⟨64,200911122,200911234⟩]
theorem checked61761 : checkPrefixCuts (2^48) 8099069953 10 Manual.Count131072.C061761.packed 64 cuts61761 = true := by
 decide +kernel
def pointBounds61761 : List (Nat × Nat × Nat) := [(8099119104,114273850315860,114274238927399)]
theorem point_links_checked61761 : (cuts61761.take 1).map (fun c => (8099069953-1+2*2^10*c.k,114273775664538+c.lower,114274164276037+c.upper)) = pointBounds61761 := by
 decide +kernel
def cuts61762 : List PrefixCut := [⟨64,203166809,203166926⟩]
theorem checked61762 : checkPrefixCuts (2^48) 8099201025 10 Manual.Count131072.C061762.packed 64 cuts61762 = true := by
 decide +kernel
def cuts61763 : List PrefixCut := [⟨20,62902506,62902539⟩,
⟨64,200904622,200904734⟩]
theorem checked61763 : checkPrefixCuts (2^48) 8099332097 10 Manual.Count131072.C061763.packed 64 cuts61763 = true := by
 decide +kernel
def pointBounds61763 : List (Nat × Nat × Nat) := [(8099373056,114274242644975,114274631256736)]
theorem point_links_checked61763 : (cuts61763.take 1).map (fun c => (8099332097-1+2*2^10*c.k,114274179742469+c.lower,114274568354197+c.upper)) = pointBounds61763 := by
 decide +kernel
def cuts61764 : List PrefixCut := [⟨64,199824060,199824176⟩]
theorem checked61764 : checkPrefixCuts (2^48) 8099463169 10 Manual.Count131072.C061764.packed 64 cuts61764 = true := by
 decide +kernel
def cuts61765 : List PrefixCut := [⟨16,50320398,50320427⟩,
⟨64,200203077,200203190⟩]
theorem checked61765 : checkPrefixCuts (2^48) 8099594241 10 Manual.Count131072.C061765.packed 64 cuts61765 = true := by
 decide +kernel
def pointBounds61765 : List (Nat × Nat × Nat) := [(8099627008,114274630791549,114275019403534)]
theorem point_links_checked61765 : (cuts61765.take 1).map (fun c => (8099594241-1+2*2^10*c.k,114274580471151+c.lower,114274969083107+c.upper)) = pointBounds61765 := by
 decide +kernel
def cuts61766 : List PrefixCut := [⟨64,201589883,201589999⟩]
theorem checked61766 : checkPrefixCuts (2^48) 8099725313 10 Manual.Count131072.C061766.packed 64 cuts61766 = true := by
 decide +kernel
def cuts61767 : List PrefixCut := [⟨12,36974584,36974606⟩,
⟨64,198737086,198737203⟩]
theorem checked61767 : checkPrefixCuts (2^48) 8099856385 10 Manual.Count131072.C061767.packed 64 cuts61767 = true := by
 decide +kernel
def pointBounds61767 : List (Nat × Nat × Nat) := [(8099880960,114275019238695,114275407850902)]
theorem point_links_checked61767 : (cuts61767.take 1).map (fun c => (8099856385-1+2*2^10*c.k,114274982264111+c.lower,114275370876296+c.upper)) = pointBounds61767 := by
 decide +kernel
def cuts61768 : List PrefixCut := [⟨64,199150868,199150980⟩]
theorem checked61768 : checkPrefixCuts (2^48) 8099987457 10 Manual.Count131072.C061768.packed 64 cuts61768 = true := by
 decide +kernel
def cuts61769 : List PrefixCut := [⟨8,25367093,25367109⟩,
⟨64,199460401,199460517⟩]
theorem checked61769 : checkPrefixCuts (2^48) 8100118529 10 Manual.Count131072.C061769.packed 64 cuts61769 = true := by
 decide +kernel
def pointBounds61769 : List (Nat × Nat × Nat) := [(8100134912,114275405519158,114275794131588)]
theorem point_links_checked61769 : (cuts61769.take 1).map (fun c => (8100118529-1+2*2^10*c.k,114275380152065+c.lower,114275768764479+c.upper)) = pointBounds61769 := by
 decide +kernel
def cuts61770 : List PrefixCut := [⟨64,199526655,199526762⟩]
theorem checked61770 : checkPrefixCuts (2^48) 8100249601 10 Manual.Count131072.C061770.packed 64 cuts61770 = true := by
 decide +kernel
def cuts61771 : List PrefixCut := [⟨4,12856885,12856892⟩,
⟨64,199905682,199905794⟩]
theorem checked61771 : checkPrefixCuts (2^48) 8100380673 10 Manual.Count131072.C061771.packed 64 cuts61771 = true := by
 decide +kernel
def pointBounds61771 : List (Nat × Nat × Nat) := [(8100388864,114275791996006,114276180608650)]
theorem point_links_checked61771 : (cuts61771.take 1).map (fun c => (8100380673-1+2*2^10*c.k,114275779139121+c.lower,114276167751758+c.upper)) = pointBounds61771 := by
 decide +kernel
def cuts61772 : List PrefixCut := [⟨64,199103232,199103349⟩]
theorem checked61772 : checkPrefixCuts (2^48) 8100511745 10 Manual.Count131072.C061772.packed 64 cuts61772 = true := by
 decide +kernel
def pointBounds61772 : List (Nat × Nat × Nat) := [(8100642816,114276178148035,114276566760901)]
theorem point_links_checked61772 : (cuts61772.take 1).map (fun c => (8100511745-1+2*2^10*c.k,114275979044803+c.lower,114276367657552+c.upper)) = pointBounds61772 := by
 decide +kernel
def cuts61773 : List PrefixCut := [⟨64,199378002,199378110⟩]
theorem checked61773 : checkPrefixCuts (2^48) 8100642817 10 Manual.Count131072.C061773.packed 64 cuts61773 = true := by
 decide +kernel
def cuts61774 : List PrefixCut := [⟨60,188777216,188777322⟩,
⟨64,200973104,200973218⟩]
theorem checked61774 : checkPrefixCuts (2^48) 8100773889 10 Manual.Count131072.C061774.packed 64 cuts61774 = true := by
 decide +kernel
def pointBounds61774 : List (Nat × Nat × Nat) := [(8100896768,114276566303253,114276954916333)]
theorem point_links_checked61774 : (cuts61774.take 1).map (fun c => (8100773889-1+2*2^10*c.k,114276377526037+c.lower,114276766139011+c.upper)) = pointBounds61774 := by
 decide +kernel
def cuts61775 : List PrefixCut := [⟨64,197078293,197078407⟩]
theorem checked61775 : checkPrefixCuts (2^48) 8100904961 10 Manual.Count131072.C061775.packed 64 cuts61775 = true := by
 decide +kernel
def cuts61776 : List PrefixCut := [⟨56,174907835,174907934⟩,
⟨64,198708170,198708284⟩]
theorem checked61776 : checkPrefixCuts (2^48) 8101036033 10 Manual.Count131072.C061776.packed 64 cuts61776 = true := by
 decide +kernel
def pointBounds61776 : List (Nat × Nat × Nat) := [(8101150720,114276950485269,114277339098570)]
theorem point_links_checked61776 : (cuts61776.take 1).map (fun c => (8101036033-1+2*2^10*c.k,114276775577434+c.lower,114277164190636+c.upper)) = pointBounds61776 := by
 decide +kernel
def cuts61777 : List PrefixCut := [⟨64,199851518,199851630⟩]
theorem checked61777 : checkPrefixCuts (2^48) 8101167105 10 Manual.Count131072.C061777.packed 64 cuts61777 = true := by
 decide +kernel
def cuts61778 : List PrefixCut := [⟨52,162984993,162985085⟩,
⟨64,200994830,200994945⟩]
theorem checked61778 : checkPrefixCuts (2^48) 8101298177 10 Manual.Count131072.C061778.packed 64 cuts61778 = true := by
 decide +kernel
def pointBounds61778 : List (Nat × Nat × Nat) := [(8101404672,114277337122115,114277725735635)]
theorem point_links_checked61778 : (cuts61778.take 1).map (fun c => (8101298177-1+2*2^10*c.k,114277174137122+c.lower,114277562750550+c.upper)) = pointBounds61778 := by
 decide +kernel
def cuts61779 : List PrefixCut := [⟨64,201860178,201860284⟩]
theorem checked61779 : checkPrefixCuts (2^48) 8101429249 10 Manual.Count131072.C061779.packed 64 cuts61779 = true := by
 decide +kernel
def cuts61780 : List PrefixCut := [⟨48,147623358,147623443⟩,
⟨64,198625793,198625907⟩]
theorem checked61780 : checkPrefixCuts (2^48) 8101560321 10 Manual.Count131072.C061780.packed 64 cuts61780 = true := by
 decide +kernel
def pointBounds61780 : List (Nat × Nat × Nat) := [(8101658624,114277724615488,114278113229222)]
theorem point_links_checked61780 : (cuts61780.take 1).map (fun c => (8101560321-1+2*2^10*c.k,114277576992130+c.lower,114277965605779+c.upper)) = pointBounds61780 := by
 decide +kernel
def cuts61781 : List PrefixCut := [⟨64,196155906,196156019⟩]
theorem checked61781 : checkPrefixCuts (2^48) 8101691393 10 Manual.Count131072.C061781.packed 64 cuts61781 = true := by
 decide +kernel
def cuts61782 : List PrefixCut := [⟨44,137300292,137300373⟩,
⟨64,200356473,200356591⟩]
theorem checked61782 : checkPrefixCuts (2^48) 8101822465 10 Manual.Count131072.C061782.packed 64 cuts61782 = true := by
 decide +kernel
def pointBounds61782 : List (Nat × Nat × Nat) := [(8101912576,114278109074121,114278497688078)]
theorem point_links_checked61782 : (cuts61782.take 1).map (fun c => (8101822465-1+2*2^10*c.k,114277971773829+c.lower,114278360387705+c.upper)) = pointBounds61782 := by
 decide +kernel
def cuts61783 : List PrefixCut := [⟨64,199762649,199762766⟩]
theorem checked61783 : checkPrefixCuts (2^48) 8101953537 10 Manual.Count131072.C061783.packed 64 cuts61783 = true := by
 decide +kernel
def cuts61784 : List PrefixCut := [⟨40,125657724,125657797⟩,
⟨64,200037325,200037443⟩]
theorem checked61784 : checkPrefixCuts (2^48) 8102084609 10 Manual.Count131072.C061784.packed 64 cuts61784 = true := by
 decide +kernel
def pointBounds61784 : List (Nat × Nat × Nat) := [(8102166528,114278497550675,114278886164859)]
theorem point_links_checked61784 : (cuts61784.take 1).map (fun c => (8102084609-1+2*2^10*c.k,114278371892951+c.lower,114278760507062+c.upper)) = pointBounds61784 := by
 decide +kernel
def cuts61785 : List PrefixCut := [⟨64,199686694,199686811⟩]
theorem checked61785 : checkPrefixCuts (2^48) 8102215681 10 Manual.Count131072.C061785.packed 64 cuts61785 = true := by
 decide +kernel
def cuts61786 : List PrefixCut := [⟨36,113494810,113494876⟩,
⟨64,201003567,201003681⟩]
theorem checked61786 : checkPrefixCuts (2^48) 8102346753 10 Manual.Count131072.C061786.packed 64 cuts61786 = true := by
 decide +kernel
def pointBounds61786 : List (Nat × Nat × Nat) := [(8102420480,114278885111780,114279273726192)]
theorem point_links_checked61786 : (cuts61786.take 1).map (fun c => (8102346753-1+2*2^10*c.k,114278771616970+c.lower,114279160231316+c.upper)) = pointBounds61786 := by
 decide +kernel
def cuts61787 : List PrefixCut := [⟨64,200896088,200896202⟩]
theorem checked61787 : checkPrefixCuts (2^48) 8102477825 10 Manual.Count131072.C061787.packed 64 cuts61787 = true := by
 decide +kernel
def cuts61788 : List PrefixCut := [⟨32,100707368,100707428⟩,
⟨64,202768725,202768842⟩]
theorem checked61788 : checkPrefixCuts (2^48) 8102608897 10 Manual.Count131072.C061788.packed 64 cuts61788 = true := by
 decide +kernel
def pointBounds61788 : List (Nat × Nat × Nat) := [(8102674432,114279274223993,114279662838627)]
theorem point_links_checked61788 : (cuts61788.take 1).map (fun c => (8102608897-1+2*2^10*c.k,114279173516625+c.lower,114279562131199+c.upper)) = pointBounds61788 := by
 decide +kernel
def cuts61789 : List PrefixCut := [⟨64,197867399,197867512⟩]
theorem checked61789 : checkPrefixCuts (2^48) 8102739969 10 Manual.Count131072.C061789.packed 64 cuts61789 = true := by
 decide +kernel
def cuts61790 : List PrefixCut := [⟨28,87191253,87191302⟩,
⟨64,199218948,199219063⟩]
theorem checked61790 : checkPrefixCuts (2^48) 8102871041 10 Manual.Count131072.C061790.packed 64 cuts61790 = true := by
 decide +kernel
def pointBounds61790 : List (Nat × Nat × Nat) := [(8102928384,114279661344002,114280049958855)]
theorem point_links_checked61790 : (cuts61790.take 1).map (fun c => (8102871041-1+2*2^10*c.k,114279574152749+c.lower,114279962767553+c.upper)) = pointBounds61790 := by
 decide +kernel
def cuts61791 : List PrefixCut := [⟨64,198347312,198347431⟩]
theorem checked61791 : checkPrefixCuts (2^48) 8103002113 10 Manual.Count131072.C061791.packed 64 cuts61791 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000055
