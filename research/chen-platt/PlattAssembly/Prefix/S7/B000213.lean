import PlattAssemblyKernel
import PlattCertificates.Count131072.C066816
import PlattCertificates.Count131072.C066817
import PlattCertificates.Count131072.C066818
import PlattCertificates.Count131072.C066819
import PlattCertificates.Count131072.C066820
import PlattCertificates.Count131072.C066821
import PlattCertificates.Count131072.C066822
import PlattCertificates.Count131072.C066823
import PlattCertificates.Count131072.C066824
import PlattCertificates.Count131072.C066825
import PlattCertificates.Count131072.C066826
import PlattCertificates.Count131072.C066827
import PlattCertificates.Count131072.C066828
import PlattCertificates.Count131072.C066829
import PlattCertificates.Count131072.C066830
import PlattCertificates.Count131072.C066831
import PlattCertificates.Count131072.C066832
import PlattCertificates.Count131072.C066833
import PlattCertificates.Count131072.C066834
import PlattCertificates.Count131072.C066835
import PlattCertificates.Count131072.C066836
import PlattCertificates.Count131072.C066837
import PlattCertificates.Count131072.C066838
import PlattCertificates.Count131072.C066839
import PlattCertificates.Count131072.C066840
import PlattCertificates.Count131072.C066841
import PlattCertificates.Count131072.C066842
import PlattCertificates.Count131072.C066843
import PlattCertificates.Count131072.C066844
import PlattCertificates.Count131072.C066845
import PlattCertificates.Count131072.C066846
import PlattCertificates.Count131072.C066847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000213
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66816 : List PrefixCut := [⟨64,184529366,184529472⟩]
theorem checked66816 : checkPrefixCuts (2^48) 8761638913 10 Manual.Count131072.C066816.packed 64 cuts66816 = true := by
 decide +kernel
def cuts66817 : List PrefixCut := [⟨14,40863374,40863400⟩,
⟨64,183884114,183884223⟩]
theorem checked66817 : checkPrefixCuts (2^48) 8761769985 10 Manual.Count131072.C066817.packed 64 cuts66817 = true := by
 decide +kernel
def pointBounds66817 : List (Nat × Nat × Nat) := [(8761798656,115242446298989,115242835469794)]
theorem point_links_checked66817 : (cuts66817.take 1).map (fun c => (8761769985-1+2*2^10*c.k,115242405435615+c.lower,115242794606394+c.upper)) = pointBounds66817 := by
 decide +kernel
def cuts66818 : List PrefixCut := [⟨64,183849229,183849337⟩]
theorem checked66818 : checkPrefixCuts (2^48) 8761901057 10 Manual.Count131072.C066818.packed 64 cuts66818 = true := by
 decide +kernel
def cuts66819 : List PrefixCut := [⟨20,56860029,56860063⟩,
⟨64,183203987,183204099⟩]
theorem checked66819 : checkPrefixCuts (2^48) 8762032129 10 Manual.Count131072.C066819.packed 64 cuts66819 = true := by
 decide +kernel
def pointBounds66819 : List (Nat × Nat × Nat) := [(8762073088,115242830028987,115243219200017)]
theorem point_links_checked66819 : (cuts66819.take 1).map (fun c => (8762032129-1+2*2^10*c.k,115242773168958+c.lower,115243162339954+c.upper)) = pointBounds66819 := by
 decide +kernel
def cuts66820 : List PrefixCut := [⟨64,184711080,184711179⟩]
theorem checked66820 : checkPrefixCuts (2^48) 8762163201 10 Manual.Count131072.C066820.packed 64 cuts66820 = true := by
 decide +kernel
def cuts66821 : List PrefixCut := [⟨26,73433922,73433960⟩,
⟨64,181656597,181656697⟩]
theorem checked66821 : checkPrefixCuts (2^48) 8762294273 10 Manual.Count131072.C066821.packed 64 cuts66821 = true := by
 decide +kernel
def pointBounds66821 : List (Nat × Nat × Nat) := [(8762347520,115243214517947,115243603689192)]
theorem point_links_checked66821 : (cuts66821.take 1).map (fun c => (8762294273-1+2*2^10*c.k,115243141084025+c.lower,115243530255232+c.upper)) = pointBounds66821 := by
 decide +kernel
def cuts66822 : List PrefixCut := [⟨64,184063087,184063192⟩]
theorem checked66822 : checkPrefixCuts (2^48) 8762425345 10 Manual.Count131072.C066822.packed 64 cuts66822 = true := by
 decide +kernel
def cuts66823 : List PrefixCut := [⟨32,93476020,93476071⟩,
⟨64,184991888,184991991⟩]
theorem checked66823 : checkPrefixCuts (2^48) 8762556417 10 Manual.Count131072.C066823.packed 64 cuts66823 = true := by
 decide +kernel
def pointBounds66823 : List (Nat × Nat × Nat) := [(8762621952,115243600279729,115243989451192)]
theorem point_links_checked66823 : (cuts66823.take 1).map (fun c => (8762556417-1+2*2^10*c.k,115243506803709+c.lower,115243895975121+c.upper)) = pointBounds66823 := by
 decide +kernel
def cuts66824 : List PrefixCut := [⟨64,184346673,184346780⟩]
theorem checked66824 : checkPrefixCuts (2^48) 8762687489 10 Manual.Count131072.C066824.packed 64 cuts66824 = true := by
 decide +kernel
def cuts66825 : List PrefixCut := [⟨38,110658086,110658153⟩,
⟨64,186881502,186881613⟩]
theorem checked66825 : checkPrefixCuts (2^48) 8762818561 10 Manual.Count131072.C066825.packed 64 cuts66825 = true := by
 decide +kernel
def pointBounds66825 : List (Nat × Nat × Nat) := [(8762896384,115243986800356,115244375972045)]
theorem point_links_checked66825 : (cuts66825.take 1).map (fun c => (8762818561-1+2*2^10*c.k,115243876142270+c.lower,115244265313892+c.upper)) = pointBounds66825 := by
 decide +kernel
def cuts66826 : List PrefixCut := [⟨64,181964242,181964346⟩]
theorem checked66826 : checkPrefixCuts (2^48) 8762949633 10 Manual.Count131072.C066826.packed 64 cuts66826 = true := by
 decide +kernel
def cuts66827 : List PrefixCut := [⟨44,125108856,125108937⟩,
⟨64,183599623,183599741⟩]
theorem checked66827 : checkPrefixCuts (2^48) 8763080705 10 Manual.Count131072.C066827.packed 64 cuts66827 = true := by
 decide +kernel
def pointBounds66827 : List (Nat × Nat × Nat) := [(8763170816,115244370096870,115244759268788)]
theorem point_links_checked66827 : (cuts66827.take 1).map (fun c => (8763080705-1+2*2^10*c.k,115244244988014+c.lower,115244634159851+c.upper)) = pointBounds66827 := by
 decide +kernel
def cuts66828 : List PrefixCut := [⟨64,185106527,185106632⟩]
theorem checked66828 : checkPrefixCuts (2^48) 8763211777 10 Manual.Count131072.C066828.packed 64 cuts66828 = true := by
 decide +kernel
def cuts66829 : List PrefixCut := [⟨50,140811413,140811494⟩,
⟨64,179964660,179964764⟩]
theorem checked66829 : checkPrefixCuts (2^48) 8763342849 10 Manual.Count131072.C066829.packed 64 cuts66829 = true := by
 decide +kernel
def pointBounds66829 : List (Nat × Nat × Nat) := [(8763445248,115244754505577,115245143677718)]
theorem point_links_checked66829 : (cuts66829.take 1).map (fun c => (8763342849-1+2*2^10*c.k,115244613694164+c.lower,115245002866224+c.upper)) = pointBounds66829 := by
 decide +kernel
def cuts66830 : List PrefixCut := [⟨64,184554974,184555082⟩]
theorem checked66830 : checkPrefixCuts (2^48) 8763473921 10 Manual.Count131072.C066830.packed 64 cuts66830 = true := by
 decide +kernel
def cuts66831 : List PrefixCut := [⟨56,160270871,160270962⟩,
⟨64,182946298,182946402⟩]
theorem checked66831 : checkPrefixCuts (2^48) 8763604993 10 Manual.Count131072.C066831.packed 64 cuts66831 = true := by
 decide +kernel
def pointBounds66831 : List (Nat × Nat × Nat) := [(8763719680,115245138484669,115245527657032)]
theorem point_links_checked66831 : (cuts66831.take 1).map (fun c => (8763604993-1+2*2^10*c.k,115244978213798+c.lower,115245367386070+c.upper)) = pointBounds66831 := by
 decide +kernel
def cuts66832 : List PrefixCut := [⟨64,184035556,184035663⟩]
theorem checked66832 : checkPrefixCuts (2^48) 8763736065 10 Manual.Count131072.C066832.packed 64 cuts66832 = true := by
 decide +kernel
def cuts66833 : List PrefixCut := [⟨62,178091137,178091244⟩,
⟨64,184097051,184097161⟩]
theorem checked66833 : checkPrefixCuts (2^48) 8763867137 10 Manual.Count131072.C066833.packed 64 cuts66833 = true := by
 decide +kernel
def pointBounds66833 : List (Nat × Nat × Nat) := [(8763994112,115245523286789,115245912459379)]
theorem point_links_checked66833 : (cuts66833.take 1).map (fun c => (8763867137-1+2*2^10*c.k,115245345195652+c.lower,115245734368135+c.upper)) = pointBounds66833 := by
 decide +kernel
def cuts66834 : List PrefixCut := [⟨64,183997928,183998032⟩]
theorem checked66834 : checkPrefixCuts (2^48) 8763998209 10 Manual.Count131072.C066834.packed 64 cuts66834 = true := by
 decide +kernel
def cuts66835 : List PrefixCut := [⟨64,182967462,182967571⟩]
theorem checked66835 : checkPrefixCuts (2^48) 8764129281 10 Manual.Count131072.C066835.packed 64 cuts66835 = true := by
 decide +kernel
def cuts66836 : List PrefixCut := [⟨4,11369135,11369142⟩,
⟨64,186369018,186369124⟩]
theorem checked66836 : checkPrefixCuts (2^48) 8764260353 10 Manual.Count131072.C066836.packed 64 cuts66836 = true := by
 decide +kernel
def pointBounds66836 : List (Nat × Nat × Nat) := [(8764268544,115245907627228,115246296800041)]
theorem point_links_checked66836 : (cuts66836.take 1).map (fun c => (8764260353-1+2*2^10*c.k,115245896258093+c.lower,115246285430899+c.upper)) = pointBounds66836 := by
 decide +kernel
def cuts66837 : List PrefixCut := [⟨64,183668534,183668635⟩]
theorem checked66837 : checkPrefixCuts (2^48) 8764391425 10 Manual.Count131072.C066837.packed 64 cuts66837 = true := by
 decide +kernel
def cuts66838 : List PrefixCut := [⟨10,28004472,28004488⟩,
⟨64,181546187,181546294⟩]
theorem checked66838 : checkPrefixCuts (2^48) 8764522497 10 Manual.Count131072.C066838.packed 64 cuts66838 = true := by
 decide +kernel
def pointBounds66838 : List (Nat × Nat × Nat) := [(8764542976,115246294300117,115246683473146)]
theorem point_links_checked66838 : (cuts66838.take 1).map (fun c => (8764522497-1+2*2^10*c.k,115246266295645+c.lower,115246655468658+c.upper)) = pointBounds66838 := by
 decide +kernel
def cuts66839 : List PrefixCut := [⟨64,184562235,184562346⟩]
theorem checked66839 : checkPrefixCuts (2^48) 8764653569 10 Manual.Count131072.C066839.packed 64 cuts66839 = true := by
 decide +kernel
def cuts66840 : List PrefixCut := [⟨16,46180272,46180301⟩,
⟨64,182985901,182986009⟩]
theorem checked66840 : checkPrefixCuts (2^48) 8764784641 10 Manual.Count131072.C066840.packed 64 cuts66840 = true := by
 decide +kernel
def pointBounds66840 : List (Nat × Nat × Nat) := [(8764817408,115246678584339,115247067757599)]
theorem point_links_checked66840 : (cuts66840.take 1).map (fun c => (8764784641-1+2*2^10*c.k,115246632404067+c.lower,115247021577298+c.upper)) = pointBounds66840 := by
 decide +kernel
def cuts66841 : List PrefixCut := [⟨64,182951049,182951156⟩]
theorem checked66841 : checkPrefixCuts (2^48) 8764915713 10 Manual.Count131072.C066841.packed 64 cuts66841 = true := by
 decide +kernel
def cuts66842 : List PrefixCut := [⟨22,63006205,63006242⟩,
⟨64,183815365,183815468⟩]
theorem checked66842 : checkPrefixCuts (2^48) 8765046785 10 Manual.Count131072.C066842.packed 64 cuts66842 = true := by
 decide +kernel
def pointBounds66842 : List (Nat × Nat × Nat) := [(8765091840,115247061347222,115247450520705)]
theorem point_links_checked66842 : (cuts66842.take 1).map (fun c => (8765046785-1+2*2^10*c.k,115246998341017+c.lower,115247387514463+c.upper)) = pointBounds66842 := by
 decide +kernel
def cuts66843 : List PrefixCut := [⟨64,185482475,185482583⟩]
theorem checked66843 : checkPrefixCuts (2^48) 8765177857 10 Manual.Count131072.C066843.packed 64 cuts66843 = true := by
 decide +kernel
def cuts66844 : List PrefixCut := [⟨28,82753318,82753368⟩,
⟨64,182718070,182718180⟩]
theorem checked66844 : checkPrefixCuts (2^48) 8765308929 10 Manual.Count131072.C066844.packed 64 cuts66844 = true := by
 decide +kernel
def pointBounds66844 : List (Nat × Nat × Nat) := [(8765366272,115247450392175,115247839565882)]
theorem point_links_checked66844 : (cuts66844.take 1).map (fun c => (8765308929-1+2*2^10*c.k,115247367638857+c.lower,115247756812514+c.upper)) = pointBounds66844 := by
 decide +kernel
def cuts66845 : List PrefixCut := [⟨64,184770459,184770564⟩]
theorem checked66845 : checkPrefixCuts (2^48) 8765440001 10 Manual.Count131072.C066845.packed 64 cuts66845 = true := by
 decide +kernel
def cuts66846 : List PrefixCut := [⟨34,96494427,96494481⟩,
⟨64,182455701,182455805⟩]
theorem checked66846 : checkPrefixCuts (2^48) 8765571073 10 Manual.Count131072.C066846.packed 64 cuts66846 = true := by
 decide +kernel
def pointBounds66846 : List (Nat × Nat × Nat) := [(8765640704,115247831621813,115248220795739)]
theorem point_links_checked66846 : (cuts66846.take 1).map (fun c => (8765571073-1+2*2^10*c.k,115247735127386+c.lower,115248124301258+c.upper)) = pointBounds66846 := by
 decide +kernel
def cuts66847 : List PrefixCut := [⟨64,184636503,184636612⟩]
theorem checked66847 : checkPrefixCuts (2^48) 8765702145 10 Manual.Count131072.C066847.packed 64 cuts66847 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000213
