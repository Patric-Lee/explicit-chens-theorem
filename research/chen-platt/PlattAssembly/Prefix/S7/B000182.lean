import PlattAssemblyKernel
import PlattCertificates.Count131072.C065824
import PlattCertificates.Count131072.C065825
import PlattCertificates.Count131072.C065826
import PlattCertificates.Count131072.C065827
import PlattCertificates.Count131072.C065828
import PlattCertificates.Count131072.C065829
import PlattCertificates.Count131072.C065830
import PlattCertificates.Count131072.C065831
import PlattCertificates.Count131072.C065832
import PlattCertificates.Count131072.C065833
import PlattCertificates.Count131072.C065834
import PlattCertificates.Count131072.C065835
import PlattCertificates.Count131072.C065836
import PlattCertificates.Count131072.C065837
import PlattCertificates.Count131072.C065838
import PlattCertificates.Count131072.C065839
import PlattCertificates.Count131072.C065840
import PlattCertificates.Count131072.C065841
import PlattCertificates.Count131072.C065842
import PlattCertificates.Count131072.C065843
import PlattCertificates.Count131072.C065844
import PlattCertificates.Count131072.C065845
import PlattCertificates.Count131072.C065846
import PlattCertificates.Count131072.C065847
import PlattCertificates.Count131072.C065848
import PlattCertificates.Count131072.C065849
import PlattCertificates.Count131072.C065850
import PlattCertificates.Count131072.C065851
import PlattCertificates.Count131072.C065852
import PlattCertificates.Count131072.C065853
import PlattCertificates.Count131072.C065854
import PlattCertificates.Count131072.C065855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000182
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65824 : List PrefixCut := [⟨31,89611280,89611333⟩,
⟨64,187113359,187113466⟩]
theorem checked65824 : checkPrefixCuts (2^48) 8631615489 10 Manual.Count131072.C065824.packed 64 cuts65824 = true := by
 decide +kernel
def pointBounds65824 : List (Nat × Nat × Nat) := [(8631678976,115058471212951,115058860276912)]
theorem point_links_checked65824 : (cuts65824.take 1).map (fun c => (8631615489-1+2*2^10*c.k,115058381601671+c.lower,115058770665579+c.upper)) = pointBounds65824 := by
 decide +kernel
def cuts65825 : List PrefixCut := [⟨64,185675728,185675841⟩]
theorem checked65825 : checkPrefixCuts (2^48) 8631746561 10 Manual.Count131072.C065825.packed 64 cuts65825 = true := by
 decide +kernel
def cuts65826 : List PrefixCut := [⟨35,99684584,99684644⟩,
⟨64,184107690,184107800⟩]
theorem checked65826 : checkPrefixCuts (2^48) 8631877633 10 Manual.Count131072.C065826.packed 64 cuts65826 = true := by
 decide +kernel
def pointBounds65826 : List (Nat × Nat × Nat) := [(8631949312,115058854075342,115059243139530)]
theorem point_links_checked65826 : (cuts65826.take 1).map (fun c => (8631877633-1+2*2^10*c.k,115058754390758+c.lower,115059143454886+c.upper)) = pointBounds65826 := by
 decide +kernel
def cuts65827 : List PrefixCut := [⟨64,187235287,187235391⟩]
theorem checked65827 : checkPrefixCuts (2^48) 8632008705 10 Manual.Count131072.C065827.packed 64 cuts65827 = true := by
 decide +kernel
def cuts65828 : List PrefixCut := [⟨39,112757168,112757231⟩,
⟨64,187493278,187493385⟩]
theorem checked65828 : checkPrefixCuts (2^48) 8632139777 10 Manual.Count131072.C065828.packed 64 cuts65828 = true := by
 decide +kernel
def pointBounds65828 : List (Nat × Nat × Nat) := [(8632219648,115059238490903,115059627555308)]
theorem point_links_checked65828 : (cuts65828.take 1).map (fun c => (8632139777-1+2*2^10*c.k,115059125733735+c.lower,115059514798077+c.upper)) = pointBounds65828 := by
 decide +kernel
def cuts65829 : List PrefixCut := [⟨64,185370996,185371107⟩]
theorem checked65829 : checkPrefixCuts (2^48) 8632270849 10 Manual.Count131072.C065829.packed 64 cuts65829 = true := by
 decide +kernel
def cuts65830 : List PrefixCut := [⟨43,128763548,128763623⟩,
⟨64,189313583,189313693⟩]
theorem checked65830 : checkPrefixCuts (2^48) 8632401921 10 Manual.Count131072.C065830.packed 64 cuts65830 = true := by
 decide +kernel
def pointBounds65830 : List (Nat × Nat × Nat) := [(8632489984,115059627361557,115060016426192)]
theorem point_links_checked65830 : (cuts65830.take 1).map (fun c => (8632401921-1+2*2^10*c.k,115059498598009+c.lower,115059887662569+c.upper)) = pointBounds65830 := by
 decide +kernel
def cuts65831 : List PrefixCut := [⟨64,187712979,187713092⟩]
theorem checked65831 : checkPrefixCuts (2^48) 8632532993 10 Manual.Count131072.C065831.packed 64 cuts65831 = true := by
 decide +kernel
def cuts65832 : List PrefixCut := [⟨47,137334851,137334932⟩,
⟨64,186145088,186145196⟩]
theorem checked65832 : checkPrefixCuts (2^48) 8632664065 10 Manual.Count131072.C065832.packed 64 cuts65832 = true := by
 decide +kernel
def pointBounds65832 : List (Nat × Nat × Nat) := [(8632760320,115060012959422,115060402024286)]
theorem point_links_checked65832 : (cuts65832.take 1).map (fun c => (8632664065-1+2*2^10*c.k,115059875624571+c.lower,115060264689354+c.upper)) = pointBounds65832 := by
 decide +kernel
def cuts65833 : List PrefixCut := [⟨64,188294177,188294289⟩]
theorem checked65833 : checkPrefixCuts (2^48) 8632795137 10 Manual.Count131072.C065833.packed 64 cuts65833 = true := by
 decide +kernel
def cuts65834 : List PrefixCut := [⟨51,148709619,148709713⟩,
⟨64,187411000,187411114⟩]
theorem checked65834 : checkPrefixCuts (2^48) 8632926209 10 Manual.Count131072.C065834.packed 64 cuts65834 = true := by
 decide +kernel
def pointBounds65834 : List (Nat × Nat × Nat) := [(8633030656,115060398773455,115060787838552)]
theorem point_links_checked65834 : (cuts65834.take 1).map (fun c => (8632926209-1+2*2^10*c.k,115060250063836+c.lower,115060639128839+c.upper)) = pointBounds65834 := by
 decide +kernel
def cuts65835 : List PrefixCut := [⟨64,185060669,185060778⟩]
theorem checked65835 : checkPrefixCuts (2^48) 8633057281 10 Manual.Count131072.C065835.packed 64 cuts65835 = true := by
 decide +kernel
def cuts65836 : List PrefixCut := [⟨55,159040390,159040483⟩,
⟨64,186003364,186003474⟩]
theorem checked65836 : checkPrefixCuts (2^48) 8633188353 10 Manual.Count131072.C065836.packed 64 cuts65836 = true := by
 decide +kernel
def pointBounds65836 : List (Nat × Nat × Nat) := [(8633300992,115060781575895,115061170641214)]
theorem point_links_checked65836 : (cuts65836.take 1).map (fun c => (8633188353-1+2*2^10*c.k,115060622535505+c.lower,115061011600731+c.upper)) = pointBounds65836 := by
 decide +kernel
def cuts65837 : List PrefixCut := [⟨64,185804915,185805029⟩]
theorem checked65837 : checkPrefixCuts (2^48) 8633319425 10 Manual.Count131072.C065837.packed 64 cuts65837 = true := by
 decide +kernel
def cuts65838 : List PrefixCut := [⟨59,173445842,173445943⟩,
⟨64,187823480,187823589⟩]
theorem checked65838 : checkPrefixCuts (2^48) 8633450497 10 Manual.Count131072.C065838.packed 64 cuts65838 = true := by
 decide +kernel
def pointBounds65838 : List (Nat × Nat × Nat) := [(8633571328,115061167789626,115061556855177)]
theorem point_links_checked65838 : (cuts65838.take 1).map (fun c => (8633450497-1+2*2^10*c.k,115060994343784+c.lower,115061383409234+c.upper)) = pointBounds65838 := by
 decide +kernel
def cuts65839 : List PrefixCut := [⟨64,186320900,186321012⟩]
theorem checked65839 : checkPrefixCuts (2^48) 8633581569 10 Manual.Count131072.C065839.packed 64 cuts65839 = true := by
 decide +kernel
def cuts65840 : List PrefixCut := [⟨63,183677379,183677484⟩,
⟨64,186481095,186481201⟩]
theorem checked65840 : checkPrefixCuts (2^48) 8633712641 10 Manual.Count131072.C065840.packed 64 cuts65840 = true := by
 decide +kernel
def pointBounds65840 : List (Nat × Nat × Nat) := [(8633841664,115061552165543,115061941231319)]
theorem point_links_checked65840 : (cuts65840.take 1).map (fun c => (8633712641-1+2*2^10*c.k,115061368488164+c.lower,115061757553835+c.upper)) = pointBounds65840 := by
 decide +kernel
def cuts65841 : List PrefixCut := [⟨64,185435033,185435141⟩]
theorem checked65841 : checkPrefixCuts (2^48) 8633843713 10 Manual.Count131072.C065841.packed 64 cuts65841 = true := by
 decide +kernel
def cuts65842 : List PrefixCut := [⟨64,189116078,189116187⟩]
theorem checked65842 : checkPrefixCuts (2^48) 8633974785 10 Manual.Count131072.C065842.packed 64 cuts65842 = true := by
 decide +kernel
def cuts65843 : List PrefixCut := [⟨3,8736892,8736896⟩,
⟨64,186994205,186994312⟩]
theorem checked65843 : checkPrefixCuts (2^48) 8634105857 10 Manual.Count131072.C065843.packed 64 cuts65843 = true := by
 decide +kernel
def pointBounds65843 : List (Nat × Nat × Nat) := [(8634112000,115061938257262,115062327323260)]
theorem point_links_checked65843 : (cuts65843.take 1).map (fun c => (8634105857-1+2*2^10*c.k,115061929520370+c.lower,115062318586364+c.upper)) = pointBounds65843 := by
 decide +kernel
def cuts65844 : List PrefixCut := [⟨64,185524388,185524494⟩]
theorem checked65844 : checkPrefixCuts (2^48) 8634236929 10 Manual.Count131072.C065844.packed 64 cuts65844 = true := by
 decide +kernel
def cuts65845 : List PrefixCut := [⟨7,20244188,20244199⟩,
⟨64,185912756,185912866⟩]
theorem checked65845 : checkPrefixCuts (2^48) 8634368001 10 Manual.Count131072.C065845.packed 64 cuts65845 = true := by
 decide +kernel
def pointBounds65845 : List (Nat × Nat × Nat) := [(8634382336,115062322283151,115062711349369)]
theorem point_links_checked65845 : (cuts65845.take 1).map (fun c => (8634368001-1+2*2^10*c.k,115062302038963+c.lower,115062691105170+c.upper)) = pointBounds65845 := by
 decide +kernel
def cuts65846 : List PrefixCut := [⟨64,186855296,186855413⟩]
theorem checked65846 : checkPrefixCuts (2^48) 8634499073 10 Manual.Count131072.C065846.packed 64 cuts65846 = true := by
 decide +kernel
def cuts65847 : List PrefixCut := [⟨11,31750772,31750791⟩,
⟨64,186787259,186787369⟩]
theorem checked65847 : checkPrefixCuts (2^48) 8634630145 10 Manual.Count131072.C065847.packed 64 cuts65847 = true := by
 decide +kernel
def pointBounds65847 : List (Nat × Nat × Nat) := [(8634652672,115062706557787,115063095624240)]
theorem point_links_checked65847 : (cuts65847.take 1).map (fun c => (8634630145-1+2*2^10*c.k,115062674807015+c.lower,115063063873449+c.upper)) = pointBounds65847 := by
 decide +kernel
def cuts65848 : List PrefixCut := [⟨64,184926356,184926463⟩]
theorem checked65848 : checkPrefixCuts (2^48) 8634761217 10 Manual.Count131072.C065848.packed 64 cuts65848 = true := by
 decide +kernel
def cuts65849 : List PrefixCut := [⟨15,42083149,42083173⟩,
⟨64,185347316,185347422⟩]
theorem checked65849 : checkPrefixCuts (2^48) 8634892289 10 Manual.Count131072.C065849.packed 64 cuts65849 = true := by
 decide +kernel
def pointBounds65849 : List (Nat × Nat × Nat) := [(8634923008,115063088603779,115063477670454)]
theorem point_links_checked65849 : (cuts65849.take 1).map (fun c => (8634892289-1+2*2^10*c.k,115063046520630+c.lower,115063435587281+c.upper)) = pointBounds65849 := by
 decide +kernel
def cuts65850 : List PrefixCut := [⟨64,186517999,186518104⟩]
theorem checked65850 : checkPrefixCuts (2^48) 8635023361 10 Manual.Count131072.C065850.packed 64 cuts65850 = true := by
 decide +kernel
def cuts65851 : List PrefixCut := [⟨19,54533642,54533676⟩,
⟨64,185993610,185993720⟩]
theorem checked65851 : checkPrefixCuts (2^48) 8635154433 10 Manual.Count131072.C065851.packed 64 cuts65851 = true := by
 decide +kernel
def pointBounds65851 : List (Nat × Nat × Nat) := [(8635193344,115063472919587,115063861986483)]
theorem point_links_checked65851 : (cuts65851.take 1).map (fun c => (8635154433-1+2*2^10*c.k,115063418385945+c.lower,115063807452807+c.upper)) = pointBounds65851 := by
 decide +kernel
def cuts65852 : List PrefixCut := [⟨64,188631038,188631151⟩]
theorem checked65852 : checkPrefixCuts (2^48) 8635285505 10 Manual.Count131072.C065852.packed 64 cuts65852 = true := by
 decide +kernel
def cuts65853 : List PrefixCut := [⟨23,68352375,68352414⟩,
⟨64,188465204,188465313⟩]
theorem checked65853 : checkPrefixCuts (2^48) 8635416577 10 Manual.Count131072.C065853.packed 64 cuts65853 = true := by
 decide +kernel
def pointBounds65853 : List (Nat × Nat × Nat) := [(8635463680,115063861362968,115064250430092)]
theorem point_links_checked65853 : (cuts65853.take 1).map (fun c => (8635416577-1+2*2^10*c.k,115063793010593+c.lower,115064182077678+c.upper)) = pointBounds65853 := by
 decide +kernel
def cuts65854 : List PrefixCut := [⟨64,186441472,186441577⟩]
theorem checked65854 : checkPrefixCuts (2^48) 8635547649 10 Manual.Count131072.C065854.packed 64 cuts65854 = true := by
 decide +kernel
def cuts65855 : List PrefixCut := [⟨27,77802618,77802668⟩,
⟨64,186536417,186536528⟩]
theorem checked65855 : checkPrefixCuts (2^48) 8635678721 10 Manual.Count131072.C065855.packed 64 cuts65855 = true := by
 decide +kernel
def pointBounds65855 : List (Nat × Nat × Nat) := [(8635734016,115064245719887,115064634787236)]
theorem point_links_checked65855 : (cuts65855.take 1).map (fun c => (8635678721-1+2*2^10*c.k,115064167917269+c.lower,115064556984568+c.upper)) = pointBounds65855 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000182
