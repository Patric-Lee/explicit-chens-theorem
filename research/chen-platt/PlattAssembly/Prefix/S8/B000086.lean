import PlattAssemblyKernel
import PlattCertificates.Count131072.C072752
import PlattCertificates.Count131072.C072753
import PlattCertificates.Count131072.C072754
import PlattCertificates.Count131072.C072755
import PlattCertificates.Count131072.C072756
import PlattCertificates.Count131072.C072757
import PlattCertificates.Count131072.C072758
import PlattCertificates.Count131072.C072759
import PlattCertificates.Count131072.C072760
import PlattCertificates.Count131072.C072761
import PlattCertificates.Count131072.C072762
import PlattCertificates.Count131072.C072763
import PlattCertificates.Count131072.C072764
import PlattCertificates.Count131072.C072765
import PlattCertificates.Count131072.C072766
import PlattCertificates.Count131072.C072767
import PlattCertificates.Count131072.C072768
import PlattCertificates.Count131072.C072769
import PlattCertificates.Count131072.C072770
import PlattCertificates.Count131072.C072771
import PlattCertificates.Count131072.C072772
import PlattCertificates.Count131072.C072773
import PlattCertificates.Count131072.C072774
import PlattCertificates.Count131072.C072775
import PlattCertificates.Count131072.C072776
import PlattCertificates.Count131072.C072777
import PlattCertificates.Count131072.C072778
import PlattCertificates.Count131072.C072779
import PlattCertificates.Count131072.C072780
import PlattCertificates.Count131072.C072781
import PlattCertificates.Count131072.C072782
import PlattCertificates.Count131072.C072783
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000086
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72752 : List PrefixCut := [⟨64,166499455,166499562⟩]
theorem checked72752 : checkPrefixCuts (2^48) 9539682305 10 Manual.Count131072.C072752.packed 64 cuts72752 = true := by
 decide +kernel
def cuts72753 : List PrefixCut := [⟨50,130678190,130678271⟩,
⟨64,167234787,167234892⟩]
theorem checked72753 : checkPrefixCuts (2^48) 9539813377 10 Manual.Count131072.C072753.packed 64 cuts72753 = true := by
 decide +kernel
def pointBounds72753 : List (Nat × Nat × Nat) := [(9539915776,116286604258029,116286994043048)]
theorem point_links_checked72753 : (cuts72753.take 1).map (fun c => (9539813377-1+2*2^10*c.k,116286473579839+c.lower,116286863364777+c.upper)) = pointBounds72753 := by
 decide +kernel
def cuts72754 : List PrefixCut := [⟨64,168796248,168796344⟩]
theorem checked72754 : checkPrefixCuts (2^48) 9539944449 10 Manual.Count131072.C072754.packed 64 cuts72754 = true := by
 decide +kernel
def cuts72755 : List PrefixCut := [⟨64,169856075,169856179⟩]
theorem checked72755 : checkPrefixCuts (2^48) 9540075521 10 Manual.Count131072.C072755.packed 64 cuts72755 = true := by
 decide +kernel
def cuts72756 : List PrefixCut := [⟨4,10296914,10296922⟩,
⟨64,165398656,165398754⟩]
theorem checked72756 : checkPrefixCuts (2^48) 9540206593 10 Manual.Count131072.C072756.packed 64 cuts72756 = true := by
 decide +kernel
def pointBounds72756 : List (Nat × Nat × Nat) := [(9540214784,116286989763863,116287379549114)]
theorem point_links_checked72756 : (cuts72756.take 1).map (fun c => (9540206593-1+2*2^10*c.k,116286979466949+c.lower,116287369252192+c.upper)) = pointBounds72756 := by
 decide +kernel
def cuts72757 : List PrefixCut := [⟨64,168907292,168907398⟩]
theorem checked72757 : checkPrefixCuts (2^48) 9540337665 10 Manual.Count131072.C072757.packed 64 cuts72757 = true := by
 decide +kernel
def cuts72758 : List PrefixCut := [⟨22,57560719,57560751⟩,
⟨64,167931383,167931479⟩]
theorem checked72758 : checkPrefixCuts (2^48) 9540468737 10 Manual.Count131072.C072758.packed 64 cuts72758 = true := by
 decide +kernel
def pointBounds72758 : List (Nat × Nat × Nat) := [(9540513792,116287371333616,116287761119095)]
theorem point_links_checked72758 : (cuts72758.take 1).map (fun c => (9540468737-1+2*2^10*c.k,116287313772897+c.lower,116287703558344+c.upper)) = pointBounds72758 := by
 decide +kernel
def cuts72759 : List PrefixCut := [⟨64,168991175,168991281⟩]
theorem checked72759 : checkPrefixCuts (2^48) 9540599809 10 Manual.Count131072.C072759.packed 64 cuts72759 = true := by
 decide +kernel
def cuts72760 : List PrefixCut := [⟨40,105411781,105411842⟩,
⟨64,167779255,167779355⟩]
theorem checked72760 : checkPrefixCuts (2^48) 9540730881 10 Manual.Count131072.C072760.packed 64 cuts72760 = true := by
 decide +kernel
def pointBounds72760 : List (Nat × Nat × Nat) := [(9540812800,116287756107236,116288145892946)]
theorem point_links_checked72760 : (cuts72760.take 1).map (fun c => (9540730881-1+2*2^10*c.k,116287650695455+c.lower,116288040481104+c.upper)) = pointBounds72760 := by
 decide +kernel
def cuts72761 : List PrefixCut := [⟨64,167216415,167216514⟩]
theorem checked72761 : checkPrefixCuts (2^48) 9540861953 10 Manual.Count131072.C072761.packed 64 cuts72761 = true := by
 decide +kernel
def cuts72762 : List PrefixCut := [⟨58,153142037,153142124⟩,
⟨64,169013710,169013804⟩]
theorem checked72762 : checkPrefixCuts (2^48) 9540993025 10 Manual.Count131072.C072762.packed 64 cuts72762 = true := by
 decide +kernel
def pointBounds72762 : List (Nat × Nat × Nat) := [(9541111808,116288138833162,116288528619097)]
theorem point_links_checked72762 : (cuts72762.take 1).map (fun c => (9540993025-1+2*2^10*c.k,116287985691125+c.lower,116288375476973+c.upper)) = pointBounds72762 := by
 decide +kernel
def cuts72763 : List PrefixCut := [⟨64,168568866,168568967⟩]
theorem checked72763 : checkPrefixCuts (2^48) 9541124097 10 Manual.Count131072.C072763.packed 64 cuts72763 = true := by
 decide +kernel
def cuts72764 : List PrefixCut := [⟨64,169451563,169451658⟩]
theorem checked72764 : checkPrefixCuts (2^48) 9541255169 10 Manual.Count131072.C072764.packed 64 cuts72764 = true := by
 decide +kernel
def cuts72765 : List PrefixCut := [⟨12,30385391,30385413⟩,
⟨64,168121721,168121825⟩]
theorem checked72765 : checkPrefixCuts (2^48) 9541386241 10 Manual.Count131072.C072765.packed 64 cuts72765 = true := by
 decide +kernel
def pointBounds72765 : List (Nat × Nat × Nat) := [(9541410816,116288523110655,116288912896815)]
theorem point_links_checked72765 : (cuts72765.take 1).map (fun c => (9541386241-1+2*2^10*c.k,116288492725264+c.lower,116288882511402+c.upper)) = pointBounds72765 := by
 decide +kernel
def cuts72766 : List PrefixCut := [⟨64,168797925,168798026⟩]
theorem checked72766 : checkPrefixCuts (2^48) 9541517313 10 Manual.Count131072.C072766.packed 64 cuts72766 = true := by
 decide +kernel
def cuts72767 : List PrefixCut := [⟨30,79353689,79353738⟩,
⟨64,168677608,168677709⟩]
theorem checked72767 : checkPrefixCuts (2^48) 9541648385 10 Manual.Count131072.C072767.packed 64 cuts72767 = true := by
 decide +kernel
def pointBounds72767 : List (Nat × Nat × Nat) := [(9541709824,116288908998599,116289298784991)]
theorem point_links_checked72767 : (cuts72767.take 1).map (fun c => (9541648385-1+2*2^10*c.k,116288829644910+c.lower,116289219431253+c.upper)) = pointBounds72767 := by
 decide +kernel
def cuts72768 : List PrefixCut := [⟨64,167554325,167554429⟩]
theorem checked72768 : checkPrefixCuts (2^48) 9541779457 10 Manual.Count131072.C072768.packed 64 cuts72768 = true := by
 decide +kernel
def cuts72769 : List PrefixCut := [⟨48,127050661,127050740⟩,
⟨64,170118390,170118492⟩]
theorem checked72769 : checkPrefixCuts (2^48) 9541910529 10 Manual.Count131072.C072769.packed 64 cuts72769 = true := by
 decide +kernel
def pointBounds72769 : List (Nat × Nat × Nat) := [(9542008832,116289292927504,116289682714131)]
theorem point_links_checked72769 : (cuts72769.take 1).map (fun c => (9541910529-1+2*2^10*c.k,116289165876843+c.lower,116289555663391+c.upper)) = pointBounds72769 := by
 decide +kernel
def cuts72770 : List PrefixCut := [⟨64,167903706,167903811⟩]
theorem checked72770 : checkPrefixCuts (2^48) 9542041601 10 Manual.Count131072.C072770.packed 64 cuts72770 = true := by
 decide +kernel
def cuts72771 : List PrefixCut := [⟨64,166397008,166397105⟩]
theorem checked72771 : checkPrefixCuts (2^48) 9542172673 10 Manual.Count131072.C072771.packed 64 cuts72771 = true := by
 decide +kernel
def cuts72772 : List PrefixCut := [⟨2,5073584,5073586⟩,
⟨64,167515609,167515708⟩]
theorem checked72772 : checkPrefixCuts (2^48) 9542303745 10 Manual.Count131072.C072772.packed 64 cuts72772 = true := by
 decide +kernel
def pointBounds72772 : List (Nat × Nat × Nat) := [(9542307840,116289675369531,116290065156385)]
theorem point_links_checked72772 : (cuts72772.take 1).map (fun c => (9542303745-1+2*2^10*c.k,116289670295947+c.lower,116290060082799+c.upper)) = pointBounds72772 := by
 decide +kernel
def cuts72773 : List PrefixCut := [⟨64,166893885,166893983⟩]
theorem checked72773 : checkPrefixCuts (2^48) 9542434817 10 Manual.Count131072.C072773.packed 64 cuts72773 = true := by
 decide +kernel
def cuts72774 : List PrefixCut := [⟨20,52445147,52445178⟩,
⟨64,169369296,169369398⟩]
theorem checked72774 : checkPrefixCuts (2^48) 9542565889 10 Manual.Count131072.C072774.packed 64 cuts72774 = true := by
 decide +kernel
def pointBounds72774 : List (Nat × Nat × Nat) := [(9542606848,116290057150588,116290446937668)]
theorem point_links_checked72774 : (cuts72774.take 1).map (fun c => (9542565889-1+2*2^10*c.k,116290004705441+c.lower,116290394492490+c.upper)) = pointBounds72774 := by
 decide +kernel
def cuts72775 : List PrefixCut := [⟨64,168187136,168187239⟩]
theorem checked72775 : checkPrefixCuts (2^48) 9542696961 10 Manual.Count131072.C072775.packed 64 cuts72775 = true := by
 decide +kernel
def cuts72776 : List PrefixCut := [⟨38,100167883,100167938⟩,
⟨64,167801382,167801474⟩]
theorem checked72776 : checkPrefixCuts (2^48) 9542828033 10 Manual.Count131072.C072776.packed 64 cuts72776 = true := by
 decide +kernel
def pointBounds72776 : List (Nat × Nat × Nat) := [(9542905856,116290442429756,116290832217065)]
theorem point_links_checked72776 : (cuts72776.take 1).map (fun c => (9542828033-1+2*2^10*c.k,116290342261873+c.lower,116290732049127+c.upper)) = pointBounds72776 := by
 decide +kernel
def cuts72777 : List PrefixCut := [⟨64,167474626,167474724⟩]
theorem checked72777 : checkPrefixCuts (2^48) 9542959105 10 Manual.Count131072.C072777.packed 64 cuts72777 = true := by
 decide +kernel
def cuts72778 : List PrefixCut := [⟨56,148123759,148123848⟩,
⟨64,169153530,169153633⟩]
theorem checked72778 : checkPrefixCuts (2^48) 9543090177 10 Manual.Count131072.C072778.packed 64 cuts72778 = true := by
 decide +kernel
def pointBounds72778 : List (Nat × Nat × Nat) := [(9543204864,116290825661640,116291215449173)]
theorem point_links_checked72778 : (cuts72778.take 1).map (fun c => (9543090177-1+2*2^10*c.k,116290677537881+c.lower,116291067325325+c.upper)) = pointBounds72778 := by
 decide +kernel
def cuts72779 : List PrefixCut := [⟨64,166437713,166437809⟩]
theorem checked72779 : checkPrefixCuts (2^48) 9543221249 10 Manual.Count131072.C072779.packed 64 cuts72779 = true := by
 decide +kernel
def cuts72780 : List PrefixCut := [⟨64,166641882,166641978⟩]
theorem checked72780 : checkPrefixCuts (2^48) 9543352321 10 Manual.Count131072.C072780.packed 64 cuts72780 = true := by
 decide +kernel
def cuts72781 : List PrefixCut := [⟨10,26662490,26662507⟩,
⟨64,165813779,165813878⟩]
theorem checked72781 : checkPrefixCuts (2^48) 9543483393 10 Manual.Count131072.C072781.packed 64 cuts72781 = true := by
 decide +kernel
def pointBounds72781 : List (Nat × Nat × Nat) := [(9543503872,116291206433496,116291596221252)]
theorem point_links_checked72781 : (cuts72781.take 1).map (fun c => (9543483393-1+2*2^10*c.k,116291179771006+c.lower,116291569558745+c.upper)) = pointBounds72781 := by
 decide +kernel
def cuts72782 : List PrefixCut := [⟨64,165487059,165487157⟩]
theorem checked72782 : checkPrefixCuts (2^48) 9543614465 10 Manual.Count131072.C072782.packed 64 cuts72782 = true := by
 decide +kernel
def cuts72783 : List PrefixCut := [⟨28,73644115,73644155⟩,
⟨64,169466335,169466431⟩]
theorem checked72783 : checkPrefixCuts (2^48) 9543745537 10 Manual.Count131072.C072783.packed 64 cuts72783 = true := by
 decide +kernel
def pointBounds72783 : List (Nat × Nat × Nat) := [(9543802880,116291584715959,116291974503935)]
theorem point_links_checked72783 : (cuts72783.take 1).map (fun c => (9543745537-1+2*2^10*c.k,116291511071844+c.lower,116291900859780+c.upper)) = pointBounds72783 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000086
