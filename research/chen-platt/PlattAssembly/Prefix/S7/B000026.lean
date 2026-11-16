import PlattAssemblyKernel
import PlattCertificates.Count131072.C060832
import PlattCertificates.Count131072.C060833
import PlattCertificates.Count131072.C060834
import PlattCertificates.Count131072.C060835
import PlattCertificates.Count131072.C060836
import PlattCertificates.Count131072.C060837
import PlattCertificates.Count131072.C060838
import PlattCertificates.Count131072.C060839
import PlattCertificates.Count131072.C060840
import PlattCertificates.Count131072.C060841
import PlattCertificates.Count131072.C060842
import PlattCertificates.Count131072.C060843
import PlattCertificates.Count131072.C060844
import PlattCertificates.Count131072.C060845
import PlattCertificates.Count131072.C060846
import PlattCertificates.Count131072.C060847
import PlattCertificates.Count131072.C060848
import PlattCertificates.Count131072.C060849
import PlattCertificates.Count131072.C060850
import PlattCertificates.Count131072.C060851
import PlattCertificates.Count131072.C060852
import PlattCertificates.Count131072.C060853
import PlattCertificates.Count131072.C060854
import PlattCertificates.Count131072.C060855
import PlattCertificates.Count131072.C060856
import PlattCertificates.Count131072.C060857
import PlattCertificates.Count131072.C060858
import PlattCertificates.Count131072.C060859
import PlattCertificates.Count131072.C060860
import PlattCertificates.Count131072.C060861
import PlattCertificates.Count131072.C060862
import PlattCertificates.Count131072.C060863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60832 : List PrefixCut := [⟨64,200696386,200696505⟩]
theorem checked60832 : checkPrefixCuts (2^48) 7977304065 10 Manual.Count131072.C060832.packed 64 cuts60832 = true := by
 decide +kernel
def cuts60833 : List PrefixCut := [⟨52,164774639,164774732⟩,
⟨64,203092368,203092481⟩]
theorem checked60833 : checkPrefixCuts (2^48) 7977435137 10 Manual.Count131072.C060833.packed 64 cuts60833 = true := by
 decide +kernel
def pointBounds60833 : List (Nat × Nat × Nat) := [(7977541632,114087144938418,114087533443014)]
theorem point_links_checked60833 : (cuts60833.take 1).map (fun c => (7977435137-1+2*2^10*c.k,114086980163779+c.lower,114087368668282+c.upper)) = pointBounds60833 := by
 decide +kernel
def cuts60834 : List PrefixCut := [⟨64,203230143,203230262⟩]
theorem checked60834 : checkPrefixCuts (2^48) 7977566209 10 Manual.Count131072.C060834.packed 64 cuts60834 = true := by
 decide +kernel
def cuts60835 : List PrefixCut := [⟨46,147128077,147128164⟩,
⟨64,202415323,202415442⟩]
theorem checked60835 : checkPrefixCuts (2^48) 7977697281 10 Manual.Count131072.C060835.packed 64 cuts60835 = true := by
 decide +kernel
def pointBounds60835 : List (Nat × Nat × Nat) := [(7977791488,114087533614367,114087922119189)]
theorem point_links_checked60835 : (cuts60835.take 1).map (fun c => (7977697281-1+2*2^10*c.k,114087386486290+c.lower,114087774991025+c.upper)) = pointBounds60835 := by
 decide +kernel
def cuts60836 : List PrefixCut := [⟨64,203717413,203717531⟩]
theorem checked60836 : checkPrefixCuts (2^48) 7977828353 10 Manual.Count131072.C060836.packed 64 cuts60836 = true := by
 decide +kernel
def cuts60837 : List PrefixCut := [⟨40,128177257,128177328⟩,
⟨64,203890480,203890597⟩]
theorem checked60837 : checkPrefixCuts (2^48) 7977959425 10 Manual.Count131072.C060837.packed 64 cuts60837 = true := by
 decide +kernel
def pointBounds60837 : List (Nat × Nat × Nat) := [(7978041344,114087920796283,114088309301326)]
theorem point_links_checked60837 : (cuts60837.take 1).map (fun c => (7977959425-1+2*2^10*c.k,114087792619026+c.lower,114088181123998+c.upper)) = pointBounds60837 := by
 decide +kernel
def cuts60838 : List PrefixCut := [⟨64,203781303,203781418⟩]
theorem checked60838 : checkPrefixCuts (2^48) 7978090497 10 Manual.Count131072.C060838.packed 64 cuts60838 = true := by
 decide +kernel
def cuts60839 : List PrefixCut := [⟨34,110427192,110427254⟩,
⟨64,206000609,206000725⟩]
theorem checked60839 : checkPrefixCuts (2^48) 7978221569 10 Manual.Count131072.C060839.packed 64 cuts60839 = true := by
 decide +kernel
def pointBounds60839 : List (Nat × Nat × Nat) := [(7978291200,114088310718001,114088699223267)]
theorem point_links_checked60839 : (cuts60839.take 1).map (fun c => (7978221569-1+2*2^10*c.k,114088200290809+c.lower,114088588796013+c.upper)) = pointBounds60839 := by
 decide +kernel
def cuts60840 : List PrefixCut := [⟨64,201234479,201234602⟩]
theorem checked60840 : checkPrefixCuts (2^48) 7978352641 10 Manual.Count131072.C060840.packed 64 cuts60840 = true := by
 decide +kernel
def cuts60841 : List PrefixCut := [⟨28,89961758,89961806⟩,
⟨64,204582678,204582792⟩]
theorem checked60841 : checkPrefixCuts (2^48) 7978483713 10 Manual.Count131072.C060841.packed 64 cuts60841 = true := by
 decide +kernel
def pointBounds60841 : List (Nat × Nat × Nat) := [(7978541056,114088697487655,114089085993146)]
theorem point_links_checked60841 : (cuts60841.take 1).map (fun c => (7978483713-1+2*2^10*c.k,114088607525897+c.lower,114088996031340+c.upper)) = pointBounds60841 := by
 decide +kernel
def cuts60842 : List PrefixCut := [⟨64,205708222,205708335⟩]
theorem checked60842 : checkPrefixCuts (2^48) 7978614785 10 Manual.Count131072.C060842.packed 64 cuts60842 = true := by
 decide +kernel
def cuts60843 : List PrefixCut := [⟨22,68968466,68968505⟩,
⟨64,200942340,200942452⟩]
theorem checked60843 : checkPrefixCuts (2^48) 7978745857 10 Manual.Count131072.C060843.packed 64 cuts60843 = true := by
 decide +kernel
def pointBounds60843 : List (Nat × Nat × Nat) := [(7978790912,114089086785263,114089475290972)]
theorem point_links_checked60843 : (cuts60843.take 1).map (fun c => (7978745857-1+2*2^10*c.k,114089017816797+c.lower,114089406322467+c.upper)) = pointBounds60843 := by
 decide +kernel
def cuts60844 : List PrefixCut := [⟨64,203690657,203690774⟩]
theorem checked60844 : checkPrefixCuts (2^48) 7978876929 10 Manual.Count131072.C060844.packed 64 cuts60844 = true := by
 decide +kernel
def cuts60845 : List PrefixCut := [⟨16,51786425,51786455⟩,
⟨64,204921998,204922110⟩]
theorem checked60845 : checkPrefixCuts (2^48) 7979008001 10 Manual.Count131072.C060845.packed 64 cuts60845 = true := by
 decide +kernel
def pointBounds60845 : List (Nat × Nat × Nat) := [(7979040768,114089474236219,114089862742148)]
theorem point_links_checked60845 : (cuts60845.take 1).map (fun c => (7979008001-1+2*2^10*c.k,114089422449794+c.lower,114089810955693+c.upper)) = pointBounds60845 := by
 decide +kernel
def cuts60846 : List PrefixCut := [⟨64,204460048,204460163⟩]
theorem checked60846 : checkPrefixCuts (2^48) 7979139073 10 Manual.Count131072.C060846.packed 64 cuts60846 = true := by
 decide +kernel
def cuts60847 : List PrefixCut := [⟨10,31007364,31007381⟩,
⟨64,202516525,202516640⟩]
theorem checked60847 : checkPrefixCuts (2^48) 7979270145 10 Manual.Count131072.C060847.packed 64 cuts60847 = true := by
 decide +kernel
def pointBounds60847 : List (Nat × Nat × Nat) := [(7979290624,114089862839204,114090251345347)]
theorem point_links_checked60847 : (cuts60847.take 1).map (fun c => (7979270145-1+2*2^10*c.k,114089831831840+c.lower,114090220337966+c.upper)) = pointBounds60847 := by
 decide +kernel
def cuts60848 : List PrefixCut := [⟨64,203253977,203254091⟩]
theorem checked60848 : checkPrefixCuts (2^48) 7979401217 10 Manual.Count131072.C060848.packed 64 cuts60848 = true := by
 decide +kernel
def cuts60849 : List PrefixCut := [⟨4,13016325,13016333⟩,
⟨64,201345832,201345947⟩]
theorem checked60849 : checkPrefixCuts (2^48) 7979532289 10 Manual.Count131072.C060849.packed 64 cuts60849 = true := by
 decide +kernel
def pointBounds60849 : List (Nat × Nat × Nat) := [(7979540480,114090250618667,114090639125030)]
theorem point_links_checked60849 : (cuts60849.take 1).map (fun c => (7979532289-1+2*2^10*c.k,114090237602342+c.lower,114090626108697+c.upper)) = pointBounds60849 := by
 decide +kernel
def cuts60850 : List PrefixCut := [⟨62,199155597,199155715⟩,
⟨64,205328453,205328575⟩]
theorem checked60850 : checkPrefixCuts (2^48) 7979663361 10 Manual.Count131072.C060850.packed 64 cuts60850 = true := by
 decide +kernel
def pointBounds60850 : List (Nat × Nat × Nat) := [(7979790336,114090638103771,114091026610359)]
theorem point_links_checked60850 : (cuts60850.take 1).map (fun c => (7979663361-1+2*2^10*c.k,114090438948174+c.lower,114090827454644+c.upper)) = pointBounds60850 := by
 decide +kernel
def cuts60851 : List PrefixCut := [⟨64,205007643,205007756⟩]
theorem checked60851 : checkPrefixCuts (2^48) 7979794433 10 Manual.Count131072.C060851.packed 64 cuts60851 = true := by
 decide +kernel
def cuts60852 : List PrefixCut := [⟨56,177844549,177844648⟩,
⟨64,203699168,203699282⟩]
theorem checked60852 : checkPrefixCuts (2^48) 7979925505 10 Manual.Count131072.C060852.packed 64 cuts60852 = true := by
 decide +kernel
def pointBounds60852 : List (Nat × Nat × Nat) := [(7980040192,114091027128819,114091415635623)]
theorem point_links_checked60852 : (cuts60852.take 1).map (fun c => (7979925505-1+2*2^10*c.k,114090849284270+c.lower,114091237790975+c.upper)) = pointBounds60852 := by
 decide +kernel
def cuts60853 : List PrefixCut := [⟨64,202002761,202002875⟩]
theorem checked60853 : checkPrefixCuts (2^48) 7980056577 10 Manual.Count131072.C060853.packed 64 cuts60853 = true := by
 decide +kernel
def cuts60854 : List PrefixCut := [⟨50,159074420,159074511⟩,
⟨64,203304502,203304619⟩]
theorem checked60854 : checkPrefixCuts (2^48) 7980187649 10 Manual.Count131072.C060854.packed 64 cuts60854 = true := by
 decide +kernel
def pointBounds60854 : List (Nat × Nat × Nat) := [(7980290048,114091414060619,114091802567643)]
theorem point_links_checked60854 : (cuts60854.take 1).map (fun c => (7980187649-1+2*2^10*c.k,114091254986199+c.lower,114091643493132+c.upper)) = pointBounds60854 := by
 decide +kernel
def cuts60855 : List PrefixCut := [⟨64,202525195,202525310⟩]
theorem checked60855 : checkPrefixCuts (2^48) 7980318721 10 Manual.Count131072.C060855.packed 64 cuts60855 = true := by
 decide +kernel
def cuts60856 : List PrefixCut := [⟨44,141716291,141716371⟩,
⟨64,205237680,205237797⟩]
theorem checked60856 : checkPrefixCuts (2^48) 7980449793 10 Manual.Count131072.C060856.packed 64 cuts60856 = true := by
 decide +kernel
def pointBounds60856 : List (Nat × Nat × Nat) := [(7980539904,114091802532187,114092191039432)]
theorem point_links_checked60856 : (cuts60856.take 1).map (fun c => (7980449793-1+2*2^10*c.k,114091660815896+c.lower,114092049323061+c.upper)) = pointBounds60856 := by
 decide +kernel
def cuts60857 : List PrefixCut := [⟨64,202518531,202518640⟩]
theorem checked60857 : checkPrefixCuts (2^48) 7980580865 10 Manual.Count131072.C060857.packed 64 cuts60857 = true := by
 decide +kernel
def cuts60858 : List PrefixCut := [⟨38,120620750,120620817⟩,
⟨64,203784896,203785010⟩]
theorem checked60858 : checkPrefixCuts (2^48) 7980711937 10 Manual.Count131072.C060858.packed 64 cuts60858 = true := by
 decide +kernel
def pointBounds60858 : List (Nat × Nat × Nat) := [(7980789760,114092189192857,114092577700315)]
theorem point_links_checked60858 : (cuts60858.take 1).map (fun c => (7980711937-1+2*2^10*c.k,114092068572107+c.lower,114092457079498+c.upper)) = pointBounds60858 := by
 decide +kernel
def cuts60859 : List PrefixCut := [⟨64,203605203,203605325⟩]
theorem checked60859 : checkPrefixCuts (2^48) 7980843009 10 Manual.Count131072.C060859.packed 64 cuts60859 = true := by
 decide +kernel
def cuts60860 : List PrefixCut := [⟨32,103194441,103194499⟩,
⟨64,204589377,204589495⟩]
theorem checked60860 : checkPrefixCuts (2^48) 7980974081 10 Manual.Count131072.C060860.packed 64 cuts60860 = true := by
 decide +kernel
def pointBounds60860 : List (Nat × Nat × Nat) := [(7981039616,114092579156647,114092967664332)]
theorem point_links_checked60860 : (cuts60860.take 1).map (fun c => (7980974081-1+2*2^10*c.k,114092475962206+c.lower,114092864469833+c.upper)) = pointBounds60860 := by
 decide +kernel
def cuts60861 : List PrefixCut := [⟨64,200565526,200565646⟩]
theorem checked60861 : checkPrefixCuts (2^48) 7981105153 10 Manual.Count131072.C060861.packed 64 cuts60861 = true := by
 decide +kernel
def cuts60862 : List PrefixCut := [⟨26,82242564,82242608⟩,
⟨64,203489388,203489502⟩]
theorem checked60862 : checkPrefixCuts (2^48) 7981236225 10 Manual.Count131072.C060862.packed 64 cuts60862 = true := by
 decide +kernel
def pointBounds60862 : List (Nat × Nat × Nat) := [(7981289472,114092963359673,114093351867582)]
theorem point_links_checked60862 : (cuts60862.take 1).map (fun c => (7981236225-1+2*2^10*c.k,114092881117109+c.lower,114093269624974+c.upper)) = pointBounds60862 := by
 decide +kernel
def cuts60863 : List PrefixCut := [⟨64,201652205,201652319⟩]
theorem checked60863 : checkPrefixCuts (2^48) 7981367297 10 Manual.Count131072.C060863.packed 64 cuts60863 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000026
