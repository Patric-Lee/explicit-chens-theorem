import PlattAssemblyKernel
import PlattCertificates.Count131072.C072848
import PlattCertificates.Count131072.C072849
import PlattCertificates.Count131072.C072850
import PlattCertificates.Count131072.C072851
import PlattCertificates.Count131072.C072852
import PlattCertificates.Count131072.C072853
import PlattCertificates.Count131072.C072854
import PlattCertificates.Count131072.C072855
import PlattCertificates.Count131072.C072856
import PlattCertificates.Count131072.C072857
import PlattCertificates.Count131072.C072858
import PlattCertificates.Count131072.C072859
import PlattCertificates.Count131072.C072860
import PlattCertificates.Count131072.C072861
import PlattCertificates.Count131072.C072862
import PlattCertificates.Count131072.C072863
import PlattCertificates.Count131072.C072864
import PlattCertificates.Count131072.C072865
import PlattCertificates.Count131072.C072866
import PlattCertificates.Count131072.C072867
import PlattCertificates.Count131072.C072868
import PlattCertificates.Count131072.C072869
import PlattCertificates.Count131072.C072870
import PlattCertificates.Count131072.C072871
import PlattCertificates.Count131072.C072872
import PlattCertificates.Count131072.C072873
import PlattCertificates.Count131072.C072874
import PlattCertificates.Count131072.C072875
import PlattCertificates.Count131072.C072876
import PlattCertificates.Count131072.C072877
import PlattCertificates.Count131072.C072878
import PlattCertificates.Count131072.C072879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72848 : List PrefixCut := [⟨64,168725853,168725958⟩]
theorem checked72848 : checkPrefixCuts (2^48) 9552265217 10 Manual.Count131072.C072848.packed 64 cuts72848 = true := by
 decide +kernel
def cuts72849 : List PrefixCut := [⟨38,98859425,98859484⟩,
⟨64,167043970,167044071⟩]
theorem checked72849 : checkPrefixCuts (2^48) 9552396289 10 Manual.Count131072.C072849.packed 64 cuts72849 = true := by
 decide +kernel
def pointBounds72849 : List (Nat × Nat × Nat) := [(9552474112,116302707116153,116303096910758)]
theorem point_links_checked72849 : (cuts72849.take 1).map (fun c => (9552396289-1+2*2^10*c.k,116302608256728+c.lower,116302998051274+c.upper)) = pointBounds72849 := by
 decide +kernel
def cuts72850 : List PrefixCut := [⟨64,165921974,165922075⟩]
theorem checked72850 : checkPrefixCuts (2^48) 9552527361 10 Manual.Count131072.C072850.packed 64 cuts72850 = true := by
 decide +kernel
def cuts72851 : List PrefixCut := [⟨56,148181667,148181747⟩,
⟨64,168601071,168601163⟩]
theorem checked72851 : checkPrefixCuts (2^48) 9552658433 10 Manual.Count131072.C072851.packed 64 cuts72851 = true := by
 decide +kernel
def pointBounds72851 : List (Nat × Nat × Nat) := [(9552773120,116303089404339,116303479199167)]
theorem point_links_checked72851 : (cuts72851.take 1).map (fun c => (9552658433-1+2*2^10*c.k,116302941222672+c.lower,116303331017420+c.upper)) = pointBounds72851 := by
 decide +kernel
def cuts72852 : List PrefixCut := [⟨64,169806805,169806906⟩]
theorem checked72852 : checkPrefixCuts (2^48) 9552789505 10 Manual.Count131072.C072852.packed 64 cuts72852 = true := by
 decide +kernel
def cuts72853 : List PrefixCut := [⟨64,169333052,169333155⟩]
theorem checked72853 : checkPrefixCuts (2^48) 9552920577 10 Manual.Count131072.C072853.packed 64 cuts72853 = true := by
 decide +kernel
def cuts72854 : List PrefixCut := [⟨10,25162566,25162584⟩,
⟨64,165146806,165146916⟩]
theorem checked72854 : checkPrefixCuts (2^48) 9553051649 10 Manual.Count131072.C072854.packed 64 cuts72854 = true := by
 decide +kernel
def pointBounds72854 : List (Nat × Nat × Nat) := [(9553072128,116303474126166,116303863921228)]
theorem point_links_checked72854 : (cuts72854.take 1).map (fun c => (9553051649-1+2*2^10*c.k,116303448963600+c.lower,116303838758644+c.upper)) = pointBounds72854 := by
 decide +kernel
def cuts72855 : List PrefixCut := [⟨64,167236475,167236577⟩]
theorem checked72855 : checkPrefixCuts (2^48) 9553182721 10 Manual.Count131072.C072855.packed 64 cuts72855 = true := by
 decide +kernel
def cuts72856 : List PrefixCut := [⟨28,74130165,74130209⟩,
⟨64,168412715,168412817⟩]
theorem checked72856 : checkPrefixCuts (2^48) 9553313793 10 Manual.Count131072.C072856.packed 64 cuts72856 = true := by
 decide +kernel
def pointBounds72856 : List (Nat × Nat × Nat) := [(9553371136,116303855477046,116304245272346)]
theorem point_links_checked72856 : (cuts72856.take 1).map (fun c => (9553313793-1+2*2^10*c.k,116303781346881+c.lower,116304171142137+c.upper)) = pointBounds72856 := by
 decide +kernel
def cuts72857 : List PrefixCut := [⟨64,168616638,168616739⟩]
theorem checked72857 : checkPrefixCuts (2^48) 9553444865 10 Manual.Count131072.C072857.packed 64 cuts72857 = true := by
 decide +kernel
def cuts72858 : List PrefixCut := [⟨46,118822804,118822875⟩,
⟨64,166669793,166669893⟩]
theorem checked72858 : checkPrefixCuts (2^48) 9553575937 10 Manual.Count131072.C072858.packed 64 cuts72858 = true := by
 decide +kernel
def pointBounds72858 : List (Nat × Nat × Nat) := [(9553670144,116304237199038,116304626994568)]
theorem point_links_checked72858 : (cuts72858.take 1).map (fun c => (9553575937-1+2*2^10*c.k,116304118376234+c.lower,116304508171693+c.upper)) = pointBounds72858 := by
 decide +kernel
def cuts72859 : List PrefixCut := [⟨64,165017640,165017734⟩]
theorem checked72859 : checkPrefixCuts (2^48) 9553707009 10 Manual.Count131072.C072859.packed 64 cuts72859 = true := by
 decide +kernel
def cuts72860 : List PrefixCut := [⟨64,168521315,168521417⟩]
theorem checked72860 : checkPrefixCuts (2^48) 9553838081 10 Manual.Count131072.C072860.packed 64 cuts72860 = true := by
 decide +kernel
def pointBounds72860 : List (Nat × Nat × Nat) := [(9553969152,116304618584982,116305008380737)]
theorem point_links_checked72860 : (cuts72860.take 1).map (fun c => (9553838081-1+2*2^10*c.k,116304450063667+c.lower,116304839859320+c.upper)) = pointBounds72860 := by
 decide +kernel
def cuts72861 : List PrefixCut := [⟨64,166515631,166515731⟩]
theorem checked72861 : checkPrefixCuts (2^48) 9553969153 10 Manual.Count131072.C072861.packed 64 cuts72861 = true := by
 decide +kernel
def cuts72862 : List PrefixCut := [⟨64,168605091,168605185⟩]
theorem checked72862 : checkPrefixCuts (2^48) 9554100225 10 Manual.Count131072.C072862.packed 64 cuts72862 = true := by
 decide +kernel
def cuts72863 : List PrefixCut := [⟨18,46695212,46695236⟩,
⟨64,169044663,169044756⟩]
theorem checked72863 : checkPrefixCuts (2^48) 9554231297 10 Manual.Count131072.C072863.packed 64 cuts72863 = true := by
 decide +kernel
def pointBounds72863 : List (Nat × Nat × Nat) := [(9554268160,116305000400916,116305390196889)]
theorem point_links_checked72863 : (cuts72863.take 1).map (fun c => (9554231297-1+2*2^10*c.k,116304953705704+c.lower,116305343501653+c.upper)) = pointBounds72863 := by
 decide +kernel
def cuts72864 : List PrefixCut := [⟨64,167039056,167039160⟩]
theorem checked72864 : checkPrefixCuts (2^48) 9554362369 10 Manual.Count131072.C072864.packed 64 cuts72864 = true := by
 decide +kernel
def cuts72865 : List PrefixCut := [⟨36,94683913,94683969⟩,
⟨64,169334622,169334725⟩]
theorem checked72865 : checkPrefixCuts (2^48) 9554493441 10 Manual.Count131072.C072865.packed 64 cuts72865 = true := by
 decide +kernel
def pointBounds72865 : List (Nat × Nat × Nat) := [(9554567168,116305384473336,116305774269538)]
theorem point_links_checked72865 : (cuts72865.take 1).map (fun c => (9554493441-1+2*2^10*c.k,116305289789423+c.lower,116305679585569+c.upper)) = pointBounds72865 := by
 decide +kernel
def cuts72866 : List PrefixCut := [⟨64,168389603,168389706⟩]
theorem checked72866 : checkPrefixCuts (2^48) 9554624513 10 Manual.Count131072.C072866.packed 64 cuts72866 = true := by
 decide +kernel
def cuts72867 : List PrefixCut := [⟨54,138957956,138958044⟩,
⟨64,164999506,164999612⟩]
theorem checked72867 : checkPrefixCuts (2^48) 9554755585 10 Manual.Count131072.C072867.packed 64 cuts72867 = true := by
 decide +kernel
def pointBounds72867 : List (Nat × Nat × Nat) := [(9554866176,116305766471604,116306156268044)]
theorem point_links_checked72867 : (cuts72867.take 1).map (fun c => (9554755585-1+2*2^10*c.k,116305627513648+c.lower,116306017310000+c.upper)) = pointBounds72867 := by
 decide +kernel
def cuts72868 : List PrefixCut := [⟨64,166116669,166116775⟩]
theorem checked72868 : checkPrefixCuts (2^48) 9554886657 10 Manual.Count131072.C072868.packed 64 cuts72868 = true := by
 decide +kernel
def cuts72869 : List PrefixCut := [⟨64,167705131,167705229⟩]
theorem checked72869 : checkPrefixCuts (2^48) 9555017729 10 Manual.Count131072.C072869.packed 64 cuts72869 = true := by
 decide +kernel
def cuts72870 : List PrefixCut := [⟨8,19972458,19972471⟩,
⟨64,166259406,166259504⟩]
theorem checked72870 : checkPrefixCuts (2^48) 9555148801 10 Manual.Count131072.C072870.packed 64 cuts72870 = true := by
 decide +kernel
def pointBounds72870 : List (Nat × Nat × Nat) := [(9555165184,116306146307412,116306536104087)]
theorem point_links_checked72870 : (cuts72870.take 1).map (fun c => (9555148801-1+2*2^10*c.k,116306126334954+c.lower,116306516131616+c.upper)) = pointBounds72870 := by
 decide +kernel
def cuts72871 : List PrefixCut := [⟨64,166816807,166816907⟩]
theorem checked72871 : checkPrefixCuts (2^48) 9555279873 10 Manual.Count131072.C072871.packed 64 cuts72871 = true := by
 decide +kernel
def cuts72872 : List PrefixCut := [⟨26,68399244,68399283⟩,
⟨64,167433127,167433226⟩]
theorem checked72872 : checkPrefixCuts (2^48) 9555410945 10 Manual.Count131072.C072872.packed 64 cuts72872 = true := by
 decide +kernel
def pointBounds72872 : List (Nat × Nat × Nat) := [(9555464192,116306527810411,116306917607310)]
theorem point_links_checked72872 : (cuts72872.take 1).map (fun c => (9555410945-1+2*2^10*c.k,116306459411167+c.lower,116306849208027+c.upper)) = pointBounds72872 := by
 decide +kernel
def cuts72873 : List PrefixCut := [⟨64,168520714,168520817⟩]
theorem checked72873 : checkPrefixCuts (2^48) 9555542017 10 Manual.Count131072.C072873.packed 64 cuts72873 = true := by
 decide +kernel
def cuts72874 : List PrefixCut := [⟨44,116499169,116499242⟩,
⟨64,168606783,168606885⟩]
theorem checked72874 : checkPrefixCuts (2^48) 9555673089 10 Manual.Count131072.C072874.packed 64 cuts72874 = true := by
 decide +kernel
def pointBounds72874 : List (Nat × Nat × Nat) := [(9555763200,116306911864177,116307301661312)]
theorem point_links_checked72874 : (cuts72874.take 1).map (fun c => (9555673089-1+2*2^10*c.k,116306795365008+c.lower,116307185162070+c.upper)) = pointBounds72874 := by
 decide +kernel
def cuts72875 : List PrefixCut := [⟨64,167455684,167455787⟩]
theorem checked72875 : checkPrefixCuts (2^48) 9555804161 10 Manual.Count131072.C072875.packed 64 cuts72875 = true := by
 decide +kernel
def cuts72876 : List PrefixCut := [⟨62,161591829,161591925⟩,
⟨64,166805383,166805482⟩]
theorem checked72876 : checkPrefixCuts (2^48) 9555935233 10 Manual.Count131072.C072876.packed 64 cuts72876 = true := by
 decide +kernel
def pointBounds72876 : List (Nat × Nat × Nat) := [(9556062208,116307293019304,116307682816667)]
theorem point_links_checked72876 : (cuts72876.take 1).map (fun c => (9555935233-1+2*2^10*c.k,116307131427475+c.lower,116307521224742+c.upper)) = pointBounds72876 := by
 decide +kernel
def cuts72877 : List PrefixCut := [⟨64,167922371,167922474⟩]
theorem checked72877 : checkPrefixCuts (2^48) 9556066305 10 Manual.Count131072.C072877.packed 64 cuts72877 = true := by
 decide +kernel
def cuts72878 : List PrefixCut := [⟨64,166948076,166948177⟩]
theorem checked72878 : checkPrefixCuts (2^48) 9556197377 10 Manual.Count131072.C072878.packed 64 cuts72878 = true := by
 decide +kernel
def cuts72879 : List PrefixCut := [⟨16,41618842,41618868⟩,
⟨64,168654121,168654226⟩]
theorem checked72879 : checkPrefixCuts (2^48) 9556328449 10 Manual.Count131072.C072879.packed 64 cuts72879 = true := by
 decide +kernel
def pointBounds72879 : List (Nat × Nat × Nat) := [(9556361216,116307674722147,116308064519743)]
theorem point_links_checked72879 : (cuts72879.take 1).map (fun c => (9556328449-1+2*2^10*c.k,116307633103305+c.lower,116308022900875+c.upper)) = pointBounds72879 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000089
