import PlattAssemblyKernel
import PlattCertificates.Count131072.C043936
import PlattCertificates.Count131072.C043937
import PlattCertificates.Count131072.C043938
import PlattCertificates.Count131072.C043939
import PlattCertificates.Count131072.C043940
import PlattCertificates.Count131072.C043941
import PlattCertificates.Count131072.C043942
import PlattCertificates.Count131072.C043943
import PlattCertificates.Count131072.C043944
import PlattCertificates.Count131072.C043945
import PlattCertificates.Count131072.C043946
import PlattCertificates.Count131072.C043947
import PlattCertificates.Count131072.C043948
import PlattCertificates.Count131072.C043949
import PlattCertificates.Count131072.C043950
import PlattCertificates.Count131072.C043951
import PlattCertificates.Count131072.C043952
import PlattCertificates.Count131072.C043953
import PlattCertificates.Count131072.C043954
import PlattCertificates.Count131072.C043955
import PlattCertificates.Count131072.C043956
import PlattCertificates.Count131072.C043957
import PlattCertificates.Count131072.C043958
import PlattCertificates.Count131072.C043959
import PlattCertificates.Count131072.C043960
import PlattCertificates.Count131072.C043961
import PlattCertificates.Count131072.C043962
import PlattCertificates.Count131072.C043963
import PlattCertificates.Count131072.C043964
import PlattCertificates.Count131072.C043965
import PlattCertificates.Count131072.C043966
import PlattCertificates.Count131072.C043967
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000123
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43936 : List PrefixCut := [⟨64,286956284,286956447⟩]
theorem checked43936 : checkPrefixCuts (2^48) 5762711553 10 Manual.Count131072.C043936.packed 64 cuts43936 = true := by
 decide +kernel
def cuts43937 : List PrefixCut := [⟨14,63056242,63056277⟩,
⟨64,284312264,284312425⟩]
theorem checked43937 : checkPrefixCuts (2^48) 5762842625 10 Manual.Count131072.C043937.packed 64 cuts43937 = true := by
 decide +kernel
def pointBounds43937 : List (Nat × Nat × Nat) := [(5762871296,110043692331372,110044078527801)]
theorem point_links_checked43937 : (cuts43937.take 1).map (fun c => (5762842625-1+2*2^10*c.k,110043629275130+c.lower,110044015471524+c.upper)) = pointBounds43937 := by
 decide +kernel
def cuts43938 : List PrefixCut := [⟨38,172606301,172606397⟩,
⟨64,287822385,287822543⟩]
theorem checked43938 : checkPrefixCuts (2^48) 5762973697 10 Manual.Count131072.C043938.packed 64 cuts43938 = true := by
 decide +kernel
def pointBounds43938 : List (Nat × Nat × Nat) := [(5763051520,110044086193695,110044472390346)]
theorem point_links_checked43938 : (cuts43938.take 1).map (fun c => (5762973697-1+2*2^10*c.k,110043913587394+c.lower,110044299783949+c.upper)) = pointBounds43938 := by
 decide +kernel
def cuts43939 : List PrefixCut := [⟨62,275898899,275899049⟩,
⟨64,286399446,286399601⟩]
theorem checked43939 : checkPrefixCuts (2^48) 5763104769 10 Manual.Count131072.C043939.packed 64 cuts43939 = true := by
 decide +kernel
def pointBounds43939 : List (Nat × Nat × Nat) := [(5763231744,110044477308678,110044863505541)]
theorem point_links_checked43939 : (cuts43939.take 1).map (fun c => (5763104769-1+2*2^10*c.k,110044201409779+c.lower,110044587606492+c.upper)) = pointBounds43939 := by
 decide +kernel
def cuts43940 : List PrefixCut := [⟨64,283267213,283267376⟩]
theorem checked43940 : checkPrefixCuts (2^48) 5763235841 10 Manual.Count131072.C043940.packed 64 cuts43940 = true := by
 decide +kernel
def cuts43941 : List PrefixCut := [⟨22,96260547,96260599⟩,
⟨64,283163090,283163250⟩]
theorem checked43941 : checkPrefixCuts (2^48) 5763366913 10 Manual.Count131072.C043941.packed 64 cuts43941 = true := by
 decide +kernel
def pointBounds43941 : List (Nat × Nat × Nat) := [(5763411968,110044867336985,110045253534068)]
theorem point_links_checked43941 : (cuts43941.take 1).map (fun c => (5763366913-1+2*2^10*c.k,110044771076438+c.lower,110045157273469+c.upper)) = pointBounds43941 := by
 decide +kernel
def cuts43942 : List PrefixCut := [⟨46,203992614,203992733⟩,
⟨64,281398558,281398722⟩]
theorem checked43942 : checkPrefixCuts (2^48) 5763497985 10 Manual.Count131072.C043942.packed 64 cuts43942 = true := by
 decide +kernel
def pointBounds43942 : List (Nat × Nat × Nat) := [(5763592192,110045258232142,110045644429452)]
theorem point_links_checked43942 : (cuts43942.take 1).map (fun c => (5763497985-1+2*2^10*c.k,110045054239528+c.lower,110045440436719+c.upper)) = pointBounds43942 := by
 decide +kernel
def cuts43943 : List PrefixCut := [⟨64,288229134,288229304⟩]
theorem checked43943 : checkPrefixCuts (2^48) 5763629057 10 Manual.Count131072.C043943.packed 64 cuts43943 = true := by
 decide +kernel
def cuts43944 : List PrefixCut := [⟨6,26615205,26615220⟩,
⟨64,284462311,284462474⟩]
theorem checked43944 : checkPrefixCuts (2^48) 5763760129 10 Manual.Count131072.C043944.packed 64 cuts43944 = true := by
 decide +kernel
def pointBounds43944 : List (Nat × Nat × Nat) := [(5763772416,110045650482425,110046036679965)]
theorem point_links_checked43944 : (cuts43944.take 1).map (fun c => (5763760129-1+2*2^10*c.k,110045623867220+c.lower,110046010064745+c.upper)) = pointBounds43944 := by
 decide +kernel
def cuts43945 : List PrefixCut := [⟨30,131900414,131900491⟩,
⟨64,284455840,284456005⟩]
theorem checked43945 : checkPrefixCuts (2^48) 5763891201 10 Manual.Count131072.C043945.packed 64 cuts43945 = true := by
 decide +kernel
def pointBounds43945 : List (Nat × Nat × Nat) := [(5763952640,110046040229945,110046426427710)]
theorem point_links_checked43945 : (cuts43945.take 1).map (fun c => (5763891201-1+2*2^10*c.k,110045908329531+c.lower,110046294527219+c.upper)) = pointBounds43945 := by
 decide +kernel
def cuts43946 : List PrefixCut := [⟨54,238596085,238596221⟩,
⟨64,283716893,283717058⟩]
theorem checked43946 : checkPrefixCuts (2^48) 5764022273 10 Manual.Count131072.C043946.packed 64 cuts43946 = true := by
 decide +kernel
def pointBounds43946 : List (Nat × Nat × Nat) := [(5764132864,110046431381456,110046817579445)]
theorem point_links_checked43946 : (cuts43946.take 1).map (fun c => (5764022273-1+2*2^10*c.k,110046192785371+c.lower,110046578983224+c.upper)) = pointBounds43946 := by
 decide +kernel
def cuts43947 : List PrefixCut := [⟨64,282489690,282489852⟩]
theorem checked43947 : checkPrefixCuts (2^48) 5764153345 10 Manual.Count131072.C043947.packed 64 cuts43947 = true := by
 decide +kernel
def cuts43948 : List PrefixCut := [⟨14,61868530,61868564⟩,
⟨64,280481196,280481356⟩]
theorem checked43948 : checkPrefixCuts (2^48) 5764284417 10 Manual.Count131072.C043948.packed 64 cuts43948 = true := by
 decide +kernel
def pointBounds43948 : List (Nat × Nat × Nat) := [(5764313088,110046820860484,110047207058698)]
theorem point_links_checked43948 : (cuts43948.take 1).map (fun c => (5764284417-1+2*2^10*c.k,110046758991954+c.lower,110047145190134+c.upper)) = pointBounds43948 := by
 decide +kernel
def cuts43949 : List PrefixCut := [⟨38,167680195,167680288⟩,
⟨64,284088184,284088348⟩]
theorem checked43949 : checkPrefixCuts (2^48) 5764415489 10 Manual.Count131072.C043949.packed 64 cuts43949 = true := by
 decide +kernel
def pointBounds43949 : List (Nat × Nat × Nat) := [(5764493312,110047207153345,110047593351778)]
theorem point_links_checked43949 : (cuts43949.take 1).map (fun c => (5764415489-1+2*2^10*c.k,110047039473150+c.lower,110047425671490+c.upper)) = pointBounds43949 := by
 decide +kernel
def cuts43950 : List PrefixCut := [⟨62,278417751,278417914⟩,
⟨64,286474294,286474462⟩]
theorem checked43950 : checkPrefixCuts (2^48) 5764546561 10 Manual.Count131072.C043950.packed 64 cuts43950 = true := by
 decide +kernel
def pointBounds43950 : List (Nat × Nat × Nat) := [(5764673536,110047601979085,110047988177752)]
theorem point_links_checked43950 : (cuts43950.take 1).map (fun c => (5764546561-1+2*2^10*c.k,110047323561334+c.lower,110047709759838+c.upper)) = pointBounds43950 := by
 decide +kernel
def cuts43951 : List PrefixCut := [⟨64,280559716,280559881⟩]
theorem checked43951 : checkPrefixCuts (2^48) 5764677633 10 Manual.Count131072.C043951.packed 64 cuts43951 = true := by
 decide +kernel
def cuts43952 : List PrefixCut := [⟨22,97798910,97798967⟩,
⟨64,286705399,286705566⟩]
theorem checked43952 : checkPrefixCuts (2^48) 5764808705 10 Manual.Count131072.C043952.packed 64 cuts43952 = true := by
 decide +kernel
def pointBounds43952 : List (Nat × Nat × Nat) := [(5764853760,110047988394254,110048374593148)]
theorem point_links_checked43952 : (cuts43952.take 1).map (fun c => (5764808705-1+2*2^10*c.k,110047890595344+c.lower,110048276794181+c.upper)) = pointBounds43952 := by
 decide +kernel
def cuts43953 : List PrefixCut := [⟨46,201939752,201939871⟩,
⟨64,280742241,280742408⟩]
theorem checked43953 : checkPrefixCuts (2^48) 5764939777 10 Manual.Count131072.C043953.packed 64 cuts43953 = true := by
 decide +kernel
def pointBounds43953 : List (Nat × Nat × Nat) := [(5765033984,110048379240495,110048765439618)]
theorem point_links_checked43953 : (cuts43953.take 1).map (fun c => (5764939777-1+2*2^10*c.k,110048177300743+c.lower,110048563499747+c.upper)) = pointBounds43953 := by
 decide +kernel
def cuts43954 : List PrefixCut := [⟨64,285471743,285471914⟩]
theorem checked43954 : checkPrefixCuts (2^48) 5765070849 10 Manual.Count131072.C043954.packed 64 cuts43954 = true := by
 decide +kernel
def cuts43955 : List PrefixCut := [⟨6,25534442,25534456⟩,
⟨64,286392889,286393054⟩]
theorem checked43955 : checkPrefixCuts (2^48) 5765201921 10 Manual.Count131072.C043955.packed 64 cuts43955 = true := by
 decide +kernel
def pointBounds43955 : List (Nat × Nat × Nat) := [(5765214208,110048769049169,110049155248525)]
theorem point_links_checked43955 : (cuts43955.take 1).map (fun c => (5765201921-1+2*2^10*c.k,110048743514727+c.lower,110049129714069+c.upper)) = pointBounds43955 := by
 decide +kernel
def cuts43956 : List PrefixCut := [⟨30,133185608,133185685⟩,
⟨64,281601899,281602064⟩]
theorem checked43956 : checkPrefixCuts (2^48) 5765332993 10 Manual.Count131072.C043956.packed 64 cuts43956 = true := by
 decide +kernel
def pointBounds43956 : List (Nat × Nat × Nat) := [(5765394432,110049163093224,110049549292808)]
theorem point_links_checked43956 : (cuts43956.take 1).map (fun c => (5765332993-1+2*2^10*c.k,110049029907616+c.lower,110049416107123+c.upper)) = pointBounds43956 := by
 decide +kernel
def cuts43957 : List PrefixCut := [⟨54,239659282,239659417⟩,
⟨64,284524713,284524873⟩]
theorem checked43957 : checkPrefixCuts (2^48) 5765464065 10 Manual.Count131072.C043957.packed 64 cuts43957 = true := by
 decide +kernel
def pointBounds43957 : List (Nat × Nat × Nat) := [(5765574656,110049551168797,110049937368604)]
theorem point_links_checked43957 : (cuts43957.take 1).map (fun c => (5765464065-1+2*2^10*c.k,110049311509515+c.lower,110049697709187+c.upper)) = pointBounds43957 := by
 decide +kernel
def cuts43958 : List PrefixCut := [⟨64,279294593,279294756⟩]
theorem checked43958 : checkPrefixCuts (2^48) 5765595137 10 Manual.Count131072.C043958.packed 64 cuts43958 = true := by
 decide +kernel
def cuts43959 : List PrefixCut := [⟨14,63122342,63122379⟩,
⟨64,286171616,286171772⟩]
theorem checked43959 : checkPrefixCuts (2^48) 5765726209 10 Manual.Count131072.C043959.packed 64 cuts43959 = true := by
 decide +kernel
def pointBounds43959 : List (Nat × Nat × Nat) := [(5765754880,110049938451163,110050324651195)]
theorem point_links_checked43959 : (cuts43959.take 1).map (fun c => (5765726209-1+2*2^10*c.k,110049875328821+c.lower,110050261528816+c.upper)) = pointBounds43959 := by
 decide +kernel
def cuts43960 : List PrefixCut := [⟨38,168565783,168565880⟩,
⟨64,285676914,285677074⟩]
theorem checked43960 : checkPrefixCuts (2^48) 5765857281 10 Manual.Count131072.C043960.packed 64 cuts43960 = true := by
 decide +kernel
def pointBounds43960 : List (Nat × Nat × Nat) := [(5765935104,110050330066220,110050716266468)]
theorem point_links_checked43960 : (cuts43960.take 1).map (fun c => (5765857281-1+2*2^10*c.k,110050161500437+c.lower,110050547700588+c.upper)) = pointBounds43960 := by
 decide +kernel
def cuts43961 : List PrefixCut := [⟨62,274149975,274150130⟩,
⟨64,283376072,283376232⟩]
theorem checked43961 : checkPrefixCuts (2^48) 5765988353 10 Manual.Count131072.C043961.packed 64 cuts43961 = true := by
 decide +kernel
def pointBounds43961 : List (Nat × Nat × Nat) := [(5766115328,110050721327326,110051107527792)]
theorem point_links_checked43961 : (cuts43961.take 1).map (fun c => (5765988353-1+2*2^10*c.k,110050447177351+c.lower,110050833377662+c.upper)) = pointBounds43961 := by
 decide +kernel
def cuts43962 : List PrefixCut := [⟨64,284931694,284931859⟩]
theorem checked43962 : checkPrefixCuts (2^48) 5766119425 10 Manual.Count131072.C043962.packed 64 cuts43962 = true := by
 decide +kernel
def cuts43963 : List PrefixCut := [⟨22,99922271,99922329⟩,
⟨64,289806604,289806775⟩]
theorem checked43963 : checkPrefixCuts (2^48) 5766250497 10 Manual.Count131072.C043963.packed 64 cuts43963 = true := by
 decide +kernel
def pointBounds43963 : List (Nat × Nat × Nat) := [(5766295552,110051115407388,110051501608082)]
theorem point_links_checked43963 : (cuts43963.take 1).map (fun c => (5766250497-1+2*2^10*c.k,110051015485117+c.lower,110051401685753+c.upper)) = pointBounds43963 := by
 decide +kernel
def cuts43964 : List PrefixCut := [⟨46,206575299,206575420⟩,
⟨64,285748582,285748748⟩]
theorem checked43964 : checkPrefixCuts (2^48) 5766381569 10 Manual.Count131072.C043964.packed 64 cuts43964 = true := by
 decide +kernel
def pointBounds43964 : List (Nat × Nat × Nat) := [(5766475776,110051511867020,110051898067948)]
theorem point_links_checked43964 : (cuts43964.take 1).map (fun c => (5766381569-1+2*2^10*c.k,110051305291721+c.lower,110051691492528+c.upper)) = pointBounds43964 := by
 decide +kernel
def cuts43965 : List PrefixCut := [⟨64,288475524,288475691⟩]
theorem checked43965 : checkPrefixCuts (2^48) 5766512641 10 Manual.Count131072.C043965.packed 64 cuts43965 = true := by
 decide +kernel
def cuts43966 : List PrefixCut := [⟨6,26992381,26992398⟩,
⟨64,280512871,280513038⟩]
theorem checked43966 : checkPrefixCuts (2^48) 5766643713 10 Manual.Count131072.C043966.packed 64 cuts43966 = true := by
 decide +kernel
def pointBounds43966 : List (Nat × Nat × Nat) := [(5766656000,110051906508208,110052292709365)]
theorem point_links_checked43966 : (cuts43966.take 1).map (fun c => (5766643713-1+2*2^10*c.k,110051879515827+c.lower,110052265716967+c.upper)) = pointBounds43966 := by
 decide +kernel
def cuts43967 : List PrefixCut := [⟨30,132322555,132322627⟩,
⟨64,282117206,282117367⟩]
theorem checked43967 : checkPrefixCuts (2^48) 5766774785 10 Manual.Count131072.C043967.packed 64 cuts43967 = true := by
 decide +kernel
def pointBounds43967 : List (Nat × Nat × Nat) := [(5766836224,110052292351253,110052678552632)]
theorem point_links_checked43967 : (cuts43967.take 1).map (fun c => (5766774785-1+2*2^10*c.k,110052160028698+c.lower,110052546230005+c.upper)) = pointBounds43967 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000123
