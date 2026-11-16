import PlattAssemblyKernel
import PlattCertificates.Count131072.C066848
import PlattCertificates.Count131072.C066849
import PlattCertificates.Count131072.C066850
import PlattCertificates.Count131072.C066851
import PlattCertificates.Count131072.C066852
import PlattCertificates.Count131072.C066853
import PlattCertificates.Count131072.C066854
import PlattCertificates.Count131072.C066855
import PlattCertificates.Count131072.C066856
import PlattCertificates.Count131072.C066857
import PlattCertificates.Count131072.C066858
import PlattCertificates.Count131072.C066859
import PlattCertificates.Count131072.C066860
import PlattCertificates.Count131072.C066861
import PlattCertificates.Count131072.C066862
import PlattCertificates.Count131072.C066863
import PlattCertificates.Count131072.C066864
import PlattCertificates.Count131072.C066865
import PlattCertificates.Count131072.C066866
import PlattCertificates.Count131072.C066867
import PlattCertificates.Count131072.C066868
import PlattCertificates.Count131072.C066869
import PlattCertificates.Count131072.C066870
import PlattCertificates.Count131072.C066871
import PlattCertificates.Count131072.C066872
import PlattCertificates.Count131072.C066873
import PlattCertificates.Count131072.C066874
import PlattCertificates.Count131072.C066875
import PlattCertificates.Count131072.C066876
import PlattCertificates.Count131072.C066877
import PlattCertificates.Count131072.C066878
import PlattCertificates.Count131072.C066879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000214
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66848 : List PrefixCut := [⟨40,113991584,113991647⟩,
⟨64,182546574,182546678⟩]
theorem checked66848 : checkPrefixCuts (2^48) 8765833217 10 Manual.Count131072.C066848.packed 64 cuts66848 = true := by
 decide +kernel
def pointBounds66848 : List (Nat × Nat × Nat) := [(8765915136,115248216211174,115248605385322)]
theorem point_links_checked66848 : (cuts66848.take 1).map (fun c => (8765833217-1+2*2^10*c.k,115248102219590+c.lower,115248491393675+c.upper)) = pointBounds66848 := by
 decide +kernel
def cuts66849 : List PrefixCut := [⟨64,189254779,189254891⟩]
theorem checked66849 : checkPrefixCuts (2^48) 8765964289 10 Manual.Count131072.C066849.packed 64 cuts66849 = true := by
 decide +kernel
def cuts66850 : List PrefixCut := [⟨46,129721664,129721739⟩,
⟨64,181320959,181321063⟩]
theorem checked66850 : checkPrefixCuts (2^48) 8766095361 10 Manual.Count131072.C066850.packed 64 cuts66850 = true := by
 decide +kernel
def pointBounds66850 : List (Nat × Nat × Nat) := [(8766189568,115248603742607,115248992916983)]
theorem point_links_checked66850 : (cuts66850.take 1).map (fun c => (8766095361-1+2*2^10*c.k,115248474020943+c.lower,115248863195244+c.upper)) = pointBounds66850 := by
 decide +kernel
def cuts66851 : List PrefixCut := [⟨64,183951186,183951289⟩]
theorem checked66851 : checkPrefixCuts (2^48) 8766226433 10 Manual.Count131072.C066851.packed 64 cuts66851 = true := by
 decide +kernel
def cuts66852 : List PrefixCut := [⟨52,149014811,149014900⟩,
⟨64,184141072,184141182⟩]
theorem checked66852 : checkPrefixCuts (2^48) 8766357505 10 Manual.Count131072.C066852.packed 64 cuts66852 = true := by
 decide +kernel
def pointBounds66852 : List (Nat × Nat × Nat) := [(8766464000,115248988307899,115249377482496)]
theorem point_links_checked66852 : (cuts66852.take 1).map (fun c => (8766357505-1+2*2^10*c.k,115248839293088+c.lower,115249228467596+c.upper)) = pointBounds66852 := by
 decide +kernel
def cuts66853 : List PrefixCut := [⟨64,182147626,182147733⟩]
theorem checked66853 : checkPrefixCuts (2^48) 8766488577 10 Manual.Count131072.C066853.packed 64 cuts66853 = true := by
 decide +kernel
def cuts66854 : List PrefixCut := [⟨58,166187677,166187772⟩,
⟨64,184039234,184039339⟩]
theorem checked66854 : checkPrefixCuts (2^48) 8766619649 10 Manual.Count131072.C066854.packed 64 cuts66854 = true := by
 decide +kernel
def pointBounds66854 : List (Nat × Nat × Nat) := [(8766738432,115249371769463,115249760944283)]
theorem point_links_checked66854 : (cuts66854.take 1).map (fun c => (8766619649-1+2*2^10*c.k,115249205581786+c.lower,115249594756511+c.upper)) = pointBounds66854 := by
 decide +kernel
def cuts66855 : List PrefixCut := [⟨64,184903367,184903473⟩]
theorem checked66855 : checkPrefixCuts (2^48) 8766750721 10 Manual.Count131072.C066855.packed 64 cuts66855 = true := by
 decide +kernel
def cuts66856 : List PrefixCut := [⟨64,184451121,184451219⟩]
theorem checked66856 : checkPrefixCuts (2^48) 8766881793 10 Manual.Count131072.C066856.packed 64 cuts66856 = true := by
 decide +kernel
def pointBounds66856 : List (Nat × Nat × Nat) := [(8767012864,115249758975508,115250148150542)]
theorem point_links_checked66856 : (cuts66856.take 1).map (fun c => (8766881793-1+2*2^10*c.k,115249574524387+c.lower,115249963699323+c.upper)) = pointBounds66856 := by
 decide +kernel
def cuts66857 : List PrefixCut := [⟨64,182522013,182522114⟩]
theorem checked66857 : checkPrefixCuts (2^48) 8767012865 10 Manual.Count131072.C066857.packed 64 cuts66857 = true := by
 decide +kernel
def cuts66858 : List PrefixCut := [⟨64,184381402,184381514⟩]
theorem checked66858 : checkPrefixCuts (2^48) 8767143937 10 Manual.Count131072.C066858.packed 64 cuts66858 = true := by
 decide +kernel
def cuts66859 : List PrefixCut := [⟨6,16341523,16341533⟩,
⟨64,183030223,183030335⟩]
theorem checked66859 : checkPrefixCuts (2^48) 8767275009 10 Manual.Count131072.C066859.packed 64 cuts66859 = true := by
 decide +kernel
def pointBounds66859 : List (Nat × Nat × Nat) := [(8767287296,115250142220446,115250531395703)]
theorem point_links_checked66859 : (cuts66859.take 1).map (fun c => (8767275009-1+2*2^10*c.k,115250125878923+c.lower,115250515054170+c.upper)) = pointBounds66859 := by
 decide +kernel
def cuts66860 : List PrefixCut := [⟨64,186013213,186013320⟩]
theorem checked66860 : checkPrefixCuts (2^48) 8767406081 10 Manual.Count131072.C066860.packed 64 cuts66860 = true := by
 decide +kernel
def cuts66861 : List PrefixCut := [⟨12,32746253,32746273⟩,
⟨64,182800024,182800130⟩]
theorem checked66861 : checkPrefixCuts (2^48) 8767537153 10 Manual.Count131072.C066861.packed 64 cuts66861 = true := by
 decide +kernel
def pointBounds66861 : List (Nat × Nat × Nat) := [(8767561728,115250527668612,115250916844098)]
theorem point_links_checked66861 : (cuts66861.take 1).map (fun c => (8767537153-1+2*2^10*c.k,115250494922359+c.lower,115250884097825+c.upper)) = pointBounds66861 := by
 decide +kernel
def cuts66862 : List PrefixCut := [⟨64,185269267,185269373⟩]
theorem checked66862 : checkPrefixCuts (2^48) 8767668225 10 Manual.Count131072.C066862.packed 64 cuts66862 = true := by
 decide +kernel
def cuts66863 : List PrefixCut := [⟨18,52296093,52296124⟩,
⟨64,183500837,183500945⟩]
theorem checked66863 : checkPrefixCuts (2^48) 8767799297 10 Manual.Count131072.C066863.packed 64 cuts66863 = true := by
 decide +kernel
def pointBounds66863 : List (Nat × Nat × Nat) := [(8767836160,115250915287743,115251304463452)]
theorem point_links_checked66863 : (cuts66863.take 1).map (fun c => (8767799297-1+2*2^10*c.k,115250862991650+c.lower,115251252167328+c.upper)) = pointBounds66863 := by
 decide +kernel
def cuts66864 : List PrefixCut := [⟨64,185456343,185456456⟩]
theorem checked66864 : checkPrefixCuts (2^48) 8767930369 10 Manual.Count131072.C066864.packed 64 cuts66864 = true := by
 decide +kernel
def cuts66865 : List PrefixCut := [⟨24,68859230,68859269⟩,
⟨64,185581981,185582084⟩]
theorem checked66865 : checkPrefixCuts (2^48) 8768061441 10 Manual.Count131072.C066865.packed 64 cuts66865 = true := by
 decide +kernel
def pointBounds66865 : List (Nat × Nat × Nat) := [(8768110592,115251300808060,115251689983998)]
theorem point_links_checked66865 : (cuts66865.take 1).map (fun c => (8768061441-1+2*2^10*c.k,115251231948830+c.lower,115251621124729+c.upper)) = pointBounds66865 := by
 decide +kernel
def cuts66866 : List PrefixCut := [⟨64,182786364,182786464⟩]
theorem checked66866 : checkPrefixCuts (2^48) 8768192513 10 Manual.Count131072.C066866.packed 64 cuts66866 = true := by
 decide +kernel
def cuts66867 : List PrefixCut := [⟨30,86191787,86191838⟩,
⟨64,183329360,183329467⟩]
theorem checked66867 : checkPrefixCuts (2^48) 8768323585 10 Manual.Count131072.C066867.packed 64 cuts66867 = true := by
 decide +kernel
def pointBounds66867 : List (Nat × Nat × Nat) := [(8768385024,115251686508962,115252075685115)]
theorem point_links_checked66867 : (cuts66867.take 1).map (fun c => (8768323585-1+2*2^10*c.k,115251600317175+c.lower,115251989493277+c.upper)) = pointBounds66867 := by
 decide +kernel
def cuts66868 : List PrefixCut := [⟨64,183968637,183968745⟩]
theorem checked66868 : checkPrefixCuts (2^48) 8768454657 10 Manual.Count131072.C066868.packed 64 cuts66868 = true := by
 decide +kernel
def cuts66869 : List PrefixCut := [⟨36,101212060,101212121⟩,
⟨64,181590460,181590567⟩]
theorem checked66869 : checkPrefixCuts (2^48) 8768585729 10 Manual.Count131072.C066869.packed 64 cuts66869 = true := by
 decide +kernel
def pointBounds66869 : List (Nat × Nat × Nat) := [(8768659456,115252068827232,115252458003610)]
theorem point_links_checked66869 : (cuts66869.take 1).map (fun c => (8768585729-1+2*2^10*c.k,115251967615172+c.lower,115252356791489+c.upper)) = pointBounds66869 := by
 decide +kernel
def cuts66870 : List PrefixCut := [⟨64,182679129,182679232⟩]
theorem checked66870 : checkPrefixCuts (2^48) 8768716801 10 Manual.Count131072.C066870.packed 64 cuts66870 = true := by
 decide +kernel
def cuts66871 : List PrefixCut := [⟨42,119024043,119024114⟩,
⟨64,182323307,182323414⟩]
theorem checked66871 : checkPrefixCuts (2^48) 8768847873 10 Manual.Count131072.C066871.packed 64 cuts66871 = true := by
 decide +kernel
def pointBounds66871 : List (Nat × Nat × Nat) := [(8768933888,115252450908804,115252840085402)]
theorem point_links_checked66871 : (cuts66871.take 1).map (fun c => (8768847873-1+2*2^10*c.k,115252331884761+c.lower,115252721061288+c.upper)) = pointBounds66871 := by
 decide +kernel
def cuts66872 : List PrefixCut := [⟨64,181293449,181293555⟩]
theorem checked66872 : checkPrefixCuts (2^48) 8768978945 10 Manual.Count131072.C066872.packed 64 cuts66872 = true := by
 decide +kernel
def cuts66873 : List PrefixCut := [⟨48,138664551,138664630⟩,
⟨64,184243765,184243870⟩]
theorem checked66873 : checkPrefixCuts (2^48) 8769110017 10 Manual.Count131072.C066873.packed 64 cuts66873 = true := by
 decide +kernel
def pointBounds66873 : List (Nat × Nat × Nat) := [(8769208320,115252834166068,115253223342887)]
theorem point_links_checked66873 : (cuts66873.take 1).map (fun c => (8769110017-1+2*2^10*c.k,115252695501517+c.lower,115253084678257+c.upper)) = pointBounds66873 := by
 decide +kernel
def cuts66874 : List PrefixCut := [⟨64,182571931,182572041⟩]
theorem checked66874 : checkPrefixCuts (2^48) 8769241089 10 Manual.Count131072.C066874.packed 64 cuts66874 = true := by
 decide +kernel
def cuts66875 : List PrefixCut := [⟨54,157661915,157662001⟩,
⟨64,186099905,186100007⟩]
theorem checked66875 : checkPrefixCuts (2^48) 8769372161 10 Manual.Count131072.C066875.packed 64 cuts66875 = true := by
 decide +kernel
def pointBounds66875 : List (Nat × Nat × Nat) := [(8769482752,115253219979128,115253609156169)]
theorem point_links_checked66875 : (cuts66875.take 1).map (fun c => (8769372161-1+2*2^10*c.k,115253062317213+c.lower,115253451494168+c.upper)) = pointBounds66875 := by
 decide +kernel
def cuts66876 : List PrefixCut := [⟨64,184267592,184267701⟩]
theorem checked66876 : checkPrefixCuts (2^48) 8769503233 10 Manual.Count131072.C066876.packed 64 cuts66876 = true := by
 decide +kernel
def cuts66877 : List PrefixCut := [⟨60,172934930,172935034⟩,
⟨64,183494539,183494648⟩]
theorem checked66877 : checkPrefixCuts (2^48) 8769634305 10 Manual.Count131072.C066877.packed 64 cuts66877 = true := by
 decide +kernel
def pointBounds66877 : List (Nat × Nat × Nat) := [(8769757184,115253605619640,115253994796910)]
theorem point_links_checked66877 : (cuts66877.take 1).map (fun c => (8769634305-1+2*2^10*c.k,115253432684710+c.lower,115253821861876+c.upper)) = pointBounds66877 := by
 decide +kernel
def cuts66878 : List PrefixCut := [⟨64,182111673,182111780⟩]
theorem checked66878 : checkPrefixCuts (2^48) 8769765377 10 Manual.Count131072.C066878.packed 64 cuts66878 = true := by
 decide +kernel
def cuts66879 : List PrefixCut := [⟨64,184323524,184323639⟩]
theorem checked66879 : checkPrefixCuts (2^48) 8769896449 10 Manual.Count131072.C066879.packed 64 cuts66879 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000214
