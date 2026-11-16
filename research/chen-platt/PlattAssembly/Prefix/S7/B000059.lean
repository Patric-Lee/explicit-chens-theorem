import PlattAssemblyKernel
import PlattCertificates.Count131072.C061888
import PlattCertificates.Count131072.C061889
import PlattCertificates.Count131072.C061890
import PlattCertificates.Count131072.C061891
import PlattCertificates.Count131072.C061892
import PlattCertificates.Count131072.C061893
import PlattCertificates.Count131072.C061894
import PlattCertificates.Count131072.C061895
import PlattCertificates.Count131072.C061896
import PlattCertificates.Count131072.C061897
import PlattCertificates.Count131072.C061898
import PlattCertificates.Count131072.C061899
import PlattCertificates.Count131072.C061900
import PlattCertificates.Count131072.C061901
import PlattCertificates.Count131072.C061902
import PlattCertificates.Count131072.C061903
import PlattCertificates.Count131072.C061904
import PlattCertificates.Count131072.C061905
import PlattCertificates.Count131072.C061906
import PlattCertificates.Count131072.C061907
import PlattCertificates.Count131072.C061908
import PlattCertificates.Count131072.C061909
import PlattCertificates.Count131072.C061910
import PlattCertificates.Count131072.C061911
import PlattCertificates.Count131072.C061912
import PlattCertificates.Count131072.C061913
import PlattCertificates.Count131072.C061914
import PlattCertificates.Count131072.C061915
import PlattCertificates.Count131072.C061916
import PlattCertificates.Count131072.C061917
import PlattCertificates.Count131072.C061918
import PlattCertificates.Count131072.C061919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61888 : List PrefixCut := [⟨64,199978806,199978921⟩]
theorem checked61888 : checkPrefixCuts (2^48) 8115716097 10 Manual.Count131072.C061888.packed 64 cuts61888 = true := by
 decide +kernel
def cuts61889 : List PrefixCut := [⟨16,48762982,48763010⟩,
⟨64,198865732,198865848⟩]
theorem checked61889 : checkPrefixCuts (2^48) 8115847169 10 Manual.Count131072.C061889.packed 64 cuts61889 = true := by
 decide +kernel
def pointBounds61889 : List (Nat × Nat × Nat) := [(8115879936,114299348682570,114299737308702)]
theorem point_links_checked61889 : (cuts61889.take 1).map (fun c => (8115847169-1+2*2^10*c.k,114299299919588+c.lower,114299688545692+c.upper)) = pointBounds61889 := by
 decide +kernel
def cuts61890 : List PrefixCut := [⟨64,200735333,200735445⟩]
theorem checked61890 : checkPrefixCuts (2^48) 8115978241 10 Manual.Count131072.C061890.packed 64 cuts61890 = true := by
 decide +kernel
def cuts61891 : List PrefixCut := [⟨12,37698206,37698226⟩,
⟨64,198998055,198998169⟩]
theorem checked61891 : checkPrefixCuts (2^48) 8116109313 10 Manual.Count131072.C061891.packed 64 cuts61891 = true := by
 decide +kernel
def pointBounds61891 : List (Nat × Nat × Nat) := [(8116133888,114299737218859,114300125845211)]
theorem point_links_checked61891 : (cuts61891.take 1).map (fun c => (8116109313-1+2*2^10*c.k,114299699520653+c.lower,114300088146985+c.upper)) = pointBounds61891 := by
 decide +kernel
def cuts61892 : List PrefixCut := [⟨64,198266544,198266656⟩]
theorem checked61892 : checkPrefixCuts (2^48) 8116240385 10 Manual.Count131072.C061892.packed 64 cuts61892 = true := by
 decide +kernel
def cuts61893 : List PrefixCut := [⟨8,25246937,25246953⟩,
⟨64,198055273,198055389⟩]
theorem checked61893 : checkPrefixCuts (2^48) 8116371457 10 Manual.Count131072.C061893.packed 64 cuts61893 = true := by
 decide +kernel
def pointBounds61893 : List (Nat × Nat × Nat) := [(8116387840,114300122032189,114300510658763)]
theorem point_links_checked61893 : (cuts61893.take 1).map (fun c => (8116371457-1+2*2^10*c.k,114300096785252+c.lower,114300485411810+c.upper)) = pointBounds61893 := by
 decide +kernel
def cuts61894 : List PrefixCut := [⟨64,199161805,199161921⟩]
theorem checked61894 : checkPrefixCuts (2^48) 8116502529 10 Manual.Count131072.C061894.packed 64 cuts61894 = true := by
 decide +kernel
def cuts61895 : List PrefixCut := [⟨4,13143248,13143256⟩,
⟨64,199713452,199713565⟩]
theorem checked61895 : checkPrefixCuts (2^48) 8116633601 10 Manual.Count131072.C061895.packed 64 cuts61895 = true := by
 decide +kernel
def pointBounds61895 : List (Nat × Nat × Nat) := [(8116641792,114300507145578,114300895772376)]
theorem point_links_checked61895 : (cuts61895.take 1).map (fun c => (8116633601-1+2*2^10*c.k,114300494002330+c.lower,114300882629120+c.upper)) = pointBounds61895 := by
 decide +kernel
def cuts61896 : List PrefixCut := [⟨64,198669868,198669980⟩]
theorem checked61896 : checkPrefixCuts (2^48) 8116764673 10 Manual.Count131072.C061896.packed 64 cuts61896 = true := by
 decide +kernel
def pointBounds61896 : List (Nat × Nat × Nat) := [(8116895744,114300892385650,114301281012665)]
theorem point_links_checked61896 : (cuts61896.take 1).map (fun c => (8116764673-1+2*2^10*c.k,114300693715782+c.lower,114301082342685+c.upper)) = pointBounds61896 := by
 decide +kernel
def cuts61897 : List PrefixCut := [⟨64,198250545,198250659⟩]
theorem checked61897 : checkPrefixCuts (2^48) 8116895745 10 Manual.Count131072.C061897.packed 64 cuts61897 = true := by
 decide +kernel
def cuts61898 : List PrefixCut := [⟨60,185625082,185625187⟩,
⟨64,197969934,197970047⟩]
theorem checked61898 : checkPrefixCuts (2^48) 8117026817 10 Manual.Count131072.C061898.packed 64 cuts61898 = true := by
 decide +kernel
def pointBounds61898 : List (Nat × Nat × Nat) := [(8117149696,114301276261277,114301664888511)]
theorem point_links_checked61898 : (cuts61898.take 1).map (fun c => (8117026817-1+2*2^10*c.k,114301090636195+c.lower,114301479263324+c.upper)) = pointBounds61898 := by
 decide +kernel
def cuts61899 : List PrefixCut := [⟨64,197030474,197030590⟩]
theorem checked61899 : checkPrefixCuts (2^48) 8117157889 10 Manual.Count131072.C061899.packed 64 cuts61899 = true := by
 decide +kernel
def cuts61900 : List PrefixCut := [⟨56,177470378,177470480⟩,
⟨64,202159298,202159412⟩]
theorem checked61900 : checkPrefixCuts (2^48) 8117288961 10 Manual.Count131072.C061900.packed 64 cuts61900 = true := by
 decide +kernel
def pointBounds61900 : List (Nat × Nat × Nat) := [(8117403648,114301663106981,114302051734441)]
theorem point_links_checked61900 : (cuts61900.take 1).map (fun c => (8117288961-1+2*2^10*c.k,114301485636603+c.lower,114301874263961+c.upper)) = pointBounds61900 := by
 decide +kernel
def cuts61901 : List PrefixCut := [⟨64,200387595,200387711⟩]
theorem checked61901 : checkPrefixCuts (2^48) 8117420033 10 Manual.Count131072.C061901.packed 64 cuts61901 = true := by
 decide +kernel
def cuts61902 : List PrefixCut := [⟨52,164219038,164219133⟩,
⟨64,201008520,201008637⟩]
theorem checked61902 : checkPrefixCuts (2^48) 8117551105 10 Manual.Count131072.C061902.packed 64 cuts61902 = true := by
 decide +kernel
def pointBounds61902 : List (Nat × Nat × Nat) := [(8117657600,114302052402534,114302441030217)]
theorem point_links_checked61902 : (cuts61902.take 1).map (fun c => (8117551105-1+2*2^10*c.k,114301888183496+c.lower,114302276811084+c.upper)) = pointBounds61902 := by
 decide +kernel
def cuts61903 : List PrefixCut := [⟨64,198404690,198404807⟩]
theorem checked61903 : checkPrefixCuts (2^48) 8117682177 10 Manual.Count131072.C061903.packed 64 cuts61903 = true := by
 decide +kernel
def cuts61904 : List PrefixCut := [⟨48,150067016,150067103⟩,
⟨64,199407040,199407158⟩]
theorem checked61904 : checkPrefixCuts (2^48) 8117813249 10 Manual.Count131072.C061904.packed 64 cuts61904 = true := by
 decide +kernel
def pointBounds61904 : List (Nat × Nat × Nat) := [(8117911552,114302437663722,114302826291631)]
theorem point_links_checked61904 : (cuts61904.take 1).map (fun c => (8117813249-1+2*2^10*c.k,114302287596706+c.lower,114302676224528+c.upper)) = pointBounds61904 := by
 decide +kernel
def cuts61905 : List PrefixCut := [⟨64,200062595,200062712⟩]
theorem checked61905 : checkPrefixCuts (2^48) 8117944321 10 Manual.Count131072.C061905.packed 64 cuts61905 = true := by
 decide +kernel
def cuts61906 : List PrefixCut := [⟨44,135083754,135083831⟩,
⟨64,198845824,198845938⟩]
theorem checked61906 : checkPrefixCuts (2^48) 8118075393 10 Manual.Count131072.C061906.packed 64 cuts61906 = true := by
 decide +kernel
def pointBounds61906 : List (Nat × Nat × Nat) := [(8118165504,114302822150095,114303210778229)]
theorem point_links_checked61906 : (cuts61906.take 1).map (fun c => (8118075393-1+2*2^10*c.k,114302687066341+c.lower,114303075694398+c.upper)) = pointBounds61906 := by
 decide +kernel
def cuts61907 : List PrefixCut := [⟨64,201165636,201165751⟩]
theorem checked61907 : checkPrefixCuts (2^48) 8118206465 10 Manual.Count131072.C061907.packed 64 cuts61907 = true := by
 decide +kernel
def cuts61908 : List PrefixCut := [⟨40,124192665,124192735⟩,
⟨64,199220798,199220908⟩]
theorem checked61908 : checkPrefixCuts (2^48) 8118337537 10 Manual.Count131072.C061908.packed 64 cuts61908 = true := by
 decide +kernel
def pointBounds61908 : List (Nat × Nat × Nat) := [(8118419456,114303211270466,114303599898822)]
theorem point_links_checked61908 : (cuts61908.take 1).map (fun c => (8118337537-1+2*2^10*c.k,114303087077801+c.lower,114303475706087+c.upper)) = pointBounds61908 := by
 decide +kernel
def cuts61909 : List PrefixCut := [⟨64,198905549,198905666⟩]
theorem checked61909 : checkPrefixCuts (2^48) 8118468609 10 Manual.Count131072.C061909.packed 64 cuts61909 = true := by
 decide +kernel
def cuts61910 : List PrefixCut := [⟨36,114203700,114203764⟩,
⟨64,201017225,201017341⟩]
theorem checked61910 : checkPrefixCuts (2^48) 8118599681 10 Manual.Count131072.C061910.packed 64 cuts61910 = true := by
 decide +kernel
def pointBounds61910 : List (Nat × Nat × Nat) := [(8118673408,114303599407848,114303988036425)]
theorem point_links_checked61910 : (cuts61910.take 1).map (fun c => (8118599681-1+2*2^10*c.k,114303485204148+c.lower,114303873832661+c.upper)) = pointBounds61910 := by
 decide +kernel
def cuts61911 : List PrefixCut := [⟨64,197373651,197373761⟩]
theorem checked61911 : checkPrefixCuts (2^48) 8118730753 10 Manual.Count131072.C061911.packed 64 cuts61911 = true := by
 decide +kernel
def cuts61912 : List PrefixCut := [⟨32,100055064,100055120⟩,
⟨64,199277274,199277388⟩]
theorem checked61912 : checkPrefixCuts (2^48) 8118861825 10 Manual.Count131072.C061912.packed 64 cuts61912 = true := by
 decide +kernel
def pointBounds61912 : List (Nat × Nat × Nat) := [(8118927360,114303983650088,114304372278883)]
theorem point_links_checked61912 : (cuts61912.take 1).map (fun c => (8118861825-1+2*2^10*c.k,114303883595024+c.lower,114304272223763+c.upper)) = pointBounds61912 := by
 decide +kernel
def cuts61913 : List PrefixCut := [⟨64,199031389,199031501⟩]
theorem checked61913 : checkPrefixCuts (2^48) 8118992897 10 Manual.Count131072.C061913.packed 64 cuts61913 = true := by
 decide +kernel
def cuts61914 : List PrefixCut := [⟨28,86323356,86323403⟩,
⟨64,200657537,200657650⟩]
theorem checked61914 : checkPrefixCuts (2^48) 8119123969 10 Manual.Count131072.C061914.packed 64 cuts61914 = true := by
 decide +kernel
def pointBounds61914 : List (Nat × Nat × Nat) := [(8119181312,114304368227043,114304756856055)]
theorem point_links_checked61914 : (cuts61914.take 1).map (fun c => (8119123969-1+2*2^10*c.k,114304281903687+c.lower,114304670532652+c.upper)) = pointBounds61914 := by
 decide +kernel
def cuts61915 : List PrefixCut := [⟨64,199024950,199025059⟩]
theorem checked61915 : checkPrefixCuts (2^48) 8119255041 10 Manual.Count131072.C061915.packed 64 cuts61915 = true := by
 decide +kernel
def cuts61916 : List PrefixCut := [⟨24,74464530,74464572⟩,
⟨64,197392407,197392520⟩]
theorem checked61916 : checkPrefixCuts (2^48) 8119386113 10 Manual.Count131072.C061916.packed 64 cuts61916 = true := by
 decide +kernel
def pointBounds61916 : List (Nat × Nat × Nat) := [(8119435264,114304756050704,114305144679933)]
theorem point_links_checked61916 : (cuts61916.take 1).map (fun c => (8119386113-1+2*2^10*c.k,114304681586174+c.lower,114305070215361+c.upper)) = pointBounds61916 := by
 decide +kernel
def cuts61917 : List PrefixCut := [⟨64,198117211,198117321⟩]
theorem checked61917 : checkPrefixCuts (2^48) 8119517185 10 Manual.Count131072.C061917.packed 64 cuts61917 = true := by
 decide +kernel
def cuts61918 : List PrefixCut := [⟨20,63126447,63126482⟩,
⟨64,199569970,199570083⟩]
theorem checked61918 : checkPrefixCuts (2^48) 8119648257 10 Manual.Count131072.C061918.packed 64 cuts61918 = true := by
 decide +kernel
def pointBounds61918 : List (Nat × Nat × Nat) := [(8119689216,114305140222239,114305528851684)]
theorem point_links_checked61918 : (cuts61918.take 1).map (fun c => (8119648257-1+2*2^10*c.k,114305077095792+c.lower,114305465725202+c.upper)) = pointBounds61918 := by
 decide +kernel
def cuts61919 : List PrefixCut := [⟨64,201196010,201196124⟩]
theorem checked61919 : checkPrefixCuts (2^48) 8119779329 10 Manual.Count131072.C061919.packed 64 cuts61919 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000059
