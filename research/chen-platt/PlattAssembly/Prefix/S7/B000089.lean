import PlattAssemblyKernel
import PlattCertificates.Count131072.C062848
import PlattCertificates.Count131072.C062849
import PlattCertificates.Count131072.C062850
import PlattCertificates.Count131072.C062851
import PlattCertificates.Count131072.C062852
import PlattCertificates.Count131072.C062853
import PlattCertificates.Count131072.C062854
import PlattCertificates.Count131072.C062855
import PlattCertificates.Count131072.C062856
import PlattCertificates.Count131072.C062857
import PlattCertificates.Count131072.C062858
import PlattCertificates.Count131072.C062859
import PlattCertificates.Count131072.C062860
import PlattCertificates.Count131072.C062861
import PlattCertificates.Count131072.C062862
import PlattCertificates.Count131072.C062863
import PlattCertificates.Count131072.C062864
import PlattCertificates.Count131072.C062865
import PlattCertificates.Count131072.C062866
import PlattCertificates.Count131072.C062867
import PlattCertificates.Count131072.C062868
import PlattCertificates.Count131072.C062869
import PlattCertificates.Count131072.C062870
import PlattCertificates.Count131072.C062871
import PlattCertificates.Count131072.C062872
import PlattCertificates.Count131072.C062873
import PlattCertificates.Count131072.C062874
import PlattCertificates.Count131072.C062875
import PlattCertificates.Count131072.C062876
import PlattCertificates.Count131072.C062877
import PlattCertificates.Count131072.C062878
import PlattCertificates.Count131072.C062879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62848 : List PrefixCut := [⟨40,121345613,121345679⟩,
⟨64,194569065,194569171⟩]
theorem checked62848 : checkPrefixCuts (2^48) 8241545217 10 Manual.Count131072.C062848.packed 64 cuts62848 = true := by
 decide +kernel
def pointBounds62848 : List (Nat × Nat × Nat) := [(8241627136,114488975442045,114489364177190)]
theorem point_links_checked62848 : (cuts62848.take 1).map (fun c => (8241545217-1+2*2^10*c.k,114488854096432+c.lower,114489242831511+c.upper)) = pointBounds62848 := by
 decide +kernel
def cuts62849 : List PrefixCut := [⟨64,191936242,191936351⟩]
theorem checked62849 : checkPrefixCuts (2^48) 8241676289 10 Manual.Count131072.C062849.packed 64 cuts62849 = true := by
 decide +kernel
def cuts62850 : List PrefixCut := [⟨38,116970330,116970401⟩,
⟨64,196065556,196065676⟩]
theorem checked62850 : checkPrefixCuts (2^48) 8241807361 10 Manual.Count131072.C062850.packed 64 cuts62850 = true := by
 decide +kernel
def pointBounds62850 : List (Nat × Nat × Nat) := [(8241885184,114489357572069,114489746307434)]
theorem point_links_checked62850 : (cuts62850.take 1).map (fun c => (8241807361-1+2*2^10*c.k,114489240601739+c.lower,114489629337033+c.upper)) = pointBounds62850 := by
 decide +kernel
def cuts62851 : List PrefixCut := [⟨64,197462637,197462750⟩]
theorem checked62851 : checkPrefixCuts (2^48) 8241938433 10 Manual.Count131072.C062851.packed 64 cuts62851 = true := by
 decide +kernel
def cuts62852 : List PrefixCut := [⟨36,108838747,108838812⟩,
⟨64,194454240,194454354⟩]
theorem checked62852 : checkPrefixCuts (2^48) 8242069505 10 Manual.Count131072.C062852.packed 64 cuts62852 = true := by
 decide +kernel
def pointBounds62852 : List (Nat × Nat × Nat) := [(8242143232,114489742968679,114490131704271)]
theorem point_links_checked62852 : (cuts62852.take 1).map (fun c => (8242069505-1+2*2^10*c.k,114489634129932+c.lower,114490022865459+c.upper)) = pointBounds62852 := by
 decide +kernel
def cuts62853 : List PrefixCut := [⟨64,197866165,197866286⟩]
theorem checked62853 : checkPrefixCuts (2^48) 8242200577 10 Manual.Count131072.C062853.packed 64 cuts62853 = true := by
 decide +kernel
def cuts62854 : List PrefixCut := [⟨34,103917740,103917801⟩,
⟨64,196872664,196872777⟩]
theorem checked62854 : checkPrefixCuts (2^48) 8242331649 10 Manual.Count131072.C062854.packed 64 cuts62854 = true := by
 decide +kernel
def pointBounds62854 : List (Nat × Nat × Nat) := [(8242401280,114490130368077,114490519103900)]
theorem point_links_checked62854 : (cuts62854.take 1).map (fun c => (8242331649-1+2*2^10*c.k,114490026450337+c.lower,114490415186099+c.upper)) = pointBounds62854 := by
 decide +kernel
def cuts62855 : List PrefixCut := [⟨64,199772223,199772332⟩]
theorem checked62855 : checkPrefixCuts (2^48) 8242462721 10 Manual.Count131072.C062855.packed 64 cuts62855 = true := by
 decide +kernel
def cuts62856 : List PrefixCut := [⟨32,98689715,98689773⟩,
⟨64,194202839,194202951⟩]
theorem checked62856 : checkPrefixCuts (2^48) 8242593793 10 Manual.Count131072.C062856.packed 64 cuts62856 = true := by
 decide +kernel
def pointBounds62856 : List (Nat × Nat × Nat) := [(8242659328,114490521784939,114490910520981)]
theorem point_links_checked62856 : (cuts62856.take 1).map (fun c => (8242593793-1+2*2^10*c.k,114490423095224+c.lower,114490811831208+c.upper)) = pointBounds62856 := by
 decide +kernel
def cuts62857 : List PrefixCut := [⟨64,195429069,195429182⟩]
theorem checked62857 : checkPrefixCuts (2^48) 8242724865 10 Manual.Count131072.C062857.packed 64 cuts62857 = true := by
 decide +kernel
def cuts62858 : List PrefixCut := [⟨30,90866797,90866847⟩,
⟨64,197816276,197816382⟩]
theorem checked62858 : checkPrefixCuts (2^48) 8242855937 10 Manual.Count131072.C062858.packed 64 cuts62858 = true := by
 decide +kernel
def pointBounds62858 : List (Nat × Nat × Nat) := [(8242917376,114490903593929,114491292330188)]
theorem point_links_checked62858 : (cuts62858.take 1).map (fun c => (8242855937-1+2*2^10*c.k,114490812727132+c.lower,114491201463341+c.upper)) = pointBounds62858 := by
 decide +kernel
def cuts62859 : List PrefixCut := [⟨64,195422859,195422962⟩]
theorem checked62859 : checkPrefixCuts (2^48) 8242987009 10 Manual.Count131072.C062859.packed 64 cuts62859 = true := by
 decide +kernel
def cuts62860 : List PrefixCut := [⟨28,86083415,86083462⟩,
⟨64,197844134,197844247⟩]
theorem checked62860 : checkPrefixCuts (2^48) 8243118081 10 Manual.Count131072.C062860.packed 64 cuts62860 = true := by
 decide +kernel
def pointBounds62860 : List (Nat × Nat × Nat) := [(8243175424,114491292049682,114491680786147)]
theorem point_links_checked62860 : (cuts62860.take 1).map (fun c => (8243118081-1+2*2^10*c.k,114491205966267+c.lower,114491594702685+c.upper)) = pointBounds62860 := by
 decide +kernel
def cuts62861 : List PrefixCut := [⟨64,195962966,195963076⟩]
theorem checked62861 : checkPrefixCuts (2^48) 8243249153 10 Manual.Count131072.C062861.packed 64 cuts62861 = true := by
 decide +kernel
def cuts62862 : List PrefixCut := [⟨26,79319899,79319942⟩,
⟨64,194628188,194628297⟩]
theorem checked62862 : checkPrefixCuts (2^48) 8243380225 10 Manual.Count131072.C062862.packed 64 cuts62862 = true := by
 decide +kernel
def pointBounds62862 : List (Nat × Nat × Nat) := [(8243433472,114491679093266,114492067829950)]
theorem point_links_checked62862 : (cuts62862.take 1).map (fun c => (8243380225-1+2*2^10*c.k,114491599773367+c.lower,114491988510008+c.upper)) = pointBounds62862 := by
 decide +kernel
def cuts62863 : List PrefixCut := [⟨64,199780956,199781072⟩]
theorem checked62863 : checkPrefixCuts (2^48) 8243511297 10 Manual.Count131072.C062863.packed 64 cuts62863 = true := by
 decide +kernel
def cuts62864 : List PrefixCut := [⟨24,74025019,74025063⟩,
⟨64,197251111,197251227⟩]
theorem checked62864 : checkPrefixCuts (2^48) 8243642369 10 Manual.Count131072.C062864.packed 64 cuts62864 = true := by
 decide +kernel
def pointBounds62864 : List (Nat × Nat × Nat) := [(8243691520,114492068207530,114492456944440)]
theorem point_links_checked62864 : (cuts62864.take 1).map (fun c => (8243642369-1+2*2^10*c.k,114491994182511+c.lower,114492382919377+c.upper)) = pointBounds62864 := by
 decide +kernel
def cuts62865 : List PrefixCut := [⟨64,195916372,195916483⟩]
theorem checked62865 : checkPrefixCuts (2^48) 8243773441 10 Manual.Count131072.C062865.packed 64 cuts62865 = true := by
 decide +kernel
def cuts62866 : List PrefixCut := [⟨22,67706170,67706208⟩,
⟨64,194786532,194786643⟩]
theorem checked62866 : checkPrefixCuts (2^48) 8243904513 10 Manual.Count131072.C062866.packed 64 cuts62866 = true := by
 decide +kernel
def pointBounds62866 : List (Nat × Nat × Nat) := [(8243949568,114492455056164,114492843793295)]
theorem point_links_checked62866 : (cuts62866.take 1).map (fun c => (8243904513-1+2*2^10*c.k,114492387349994+c.lower,114492776087087+c.upper)) = pointBounds62866 := by
 decide +kernel
def cuts62867 : List PrefixCut := [⟨64,193793293,193793402⟩]
theorem checked62867 : checkPrefixCuts (2^48) 8244035585 10 Manual.Count131072.C062867.packed 64 cuts62867 = true := by
 decide +kernel
def cuts62868 : List PrefixCut := [⟨20,60739020,60739056⟩,
⟨64,195907014,195907127⟩]
theorem checked62868 : checkPrefixCuts (2^48) 8244166657 10 Manual.Count131072.C062868.packed 64 cuts62868 = true := by
 decide +kernel
def pointBounds62868 : List (Nat × Nat × Nat) := [(8244207616,114492836668839,114493225406188)]
theorem point_links_checked62868 : (cuts62868.take 1).map (fun c => (8244166657-1+2*2^10*c.k,114492775929819+c.lower,114493164667132+c.upper)) = pointBounds62868 := by
 decide +kernel
def cuts62869 : List PrefixCut := [⟨64,196484306,196484418⟩]
theorem checked62869 : checkPrefixCuts (2^48) 8244297729 10 Manual.Count131072.C062869.packed 64 cuts62869 = true := by
 decide +kernel
def cuts62870 : List PrefixCut := [⟨18,54216141,54216173⟩,
⟨64,195081401,195081515⟩]
theorem checked62870 : checkPrefixCuts (2^48) 8244428801 10 Manual.Count131072.C062870.packed 64 cuts62870 = true := by
 decide +kernel
def pointBounds62870 : List (Nat × Nat × Nat) := [(8244465664,114493222537280,114493611274850)]
theorem point_links_checked62870 : (cuts62870.take 1).map (fun c => (8244428801-1+2*2^10*c.k,114493168321139+c.lower,114493557058677+c.upper)) = pointBounds62870 := by
 decide +kernel
def cuts62871 : List PrefixCut := [⟨64,197024306,197024420⟩]
theorem checked62871 : checkPrefixCuts (2^48) 8244559873 10 Manual.Count131072.C062871.packed 64 cuts62871 = true := by
 decide +kernel
def cuts62872 : List PrefixCut := [⟨16,49161704,49161732⟩,
⟨64,198420904,198421011⟩]
theorem checked62872 : checkPrefixCuts (2^48) 8244690945 10 Manual.Count131072.C062872.packed 64 cuts62872 = true := by
 decide +kernel
def pointBounds62872 : List (Nat × Nat × Nat) := [(8244723712,114493609588550,114493998326344)]
theorem point_links_checked62872 : (cuts62872.take 1).map (fun c => (8244690945-1+2*2^10*c.k,114493560426846+c.lower,114493949164612+c.upper)) = pointBounds62872 := by
 decide +kernel
def cuts62873 : List PrefixCut := [⟨64,193330996,193331105⟩]
theorem checked62873 : checkPrefixCuts (2^48) 8244822017 10 Manual.Count131072.C062873.packed 64 cuts62873 = true := by
 decide +kernel
def cuts62874 : List PrefixCut := [⟨14,43663772,43663800⟩,
⟨64,196775943,196776059⟩]
theorem checked62874 : checkPrefixCuts (2^48) 8244953089 10 Manual.Count131072.C062874.packed 64 cuts62874 = true := by
 decide +kernel
def pointBounds62874 : List (Nat × Nat × Nat) := [(8244981760,114493995842518,114494384580528)]
theorem point_links_checked62874 : (cuts62874.take 1).map (fun c => (8244953089-1+2*2^10*c.k,114493952178746+c.lower,114494340916728+c.upper)) = pointBounds62874 := by
 decide +kernel
def cuts62875 : List PrefixCut := [⟨64,193939331,193939441⟩]
theorem checked62875 : checkPrefixCuts (2^48) 8245084161 10 Manual.Count131072.C062875.packed 64 cuts62875 = true := by
 decide +kernel
def cuts62876 : List PrefixCut := [⟨12,37244468,37244491⟩,
⟨64,195199347,195199464⟩]
theorem checked62876 : checkPrefixCuts (2^48) 8245215233 10 Manual.Count131072.C062876.packed 64 cuts62876 = true := by
 decide +kernel
def pointBounds62876 : List (Nat × Nat × Nat) := [(8245239808,114494380138488,114494768876719)]
theorem point_links_checked62876 : (cuts62876.take 1).map (fun c => (8245215233-1+2*2^10*c.k,114494342894020+c.lower,114494731632228+c.upper)) = pointBounds62876 := by
 decide +kernel
def cuts62877 : List PrefixCut := [⟨64,197654139,197654251⟩]
theorem checked62877 : checkPrefixCuts (2^48) 8245346305 10 Manual.Count131072.C062877.packed 64 cuts62877 = true := by
 decide +kernel
def cuts62878 : List PrefixCut := [⟨10,30450062,30450080⟩,
⟨64,197036511,197036631⟩]
theorem checked62878 : checkPrefixCuts (2^48) 8245477377 10 Manual.Count131072.C062878.packed 64 cuts62878 = true := by
 decide +kernel
def pointBounds62878 : List (Nat × Nat × Nat) := [(8245497856,114494766197568,114495154936023)]
theorem point_links_checked62878 : (cuts62878.take 1).map (fun c => (8245477377-1+2*2^10*c.k,114494735747506+c.lower,114495124485943+c.upper)) = pointBounds62878 := by
 decide +kernel
def cuts62879 : List PrefixCut := [⟨64,198057464,198057575⟩]
theorem checked62879 : checkPrefixCuts (2^48) 8245608449 10 Manual.Count131072.C062879.packed 64 cuts62879 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000089
