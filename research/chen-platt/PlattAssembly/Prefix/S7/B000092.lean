import PlattAssemblyKernel
import PlattCertificates.Count131072.C062944
import PlattCertificates.Count131072.C062945
import PlattCertificates.Count131072.C062946
import PlattCertificates.Count131072.C062947
import PlattCertificates.Count131072.C062948
import PlattCertificates.Count131072.C062949
import PlattCertificates.Count131072.C062950
import PlattCertificates.Count131072.C062951
import PlattCertificates.Count131072.C062952
import PlattCertificates.Count131072.C062953
import PlattCertificates.Count131072.C062954
import PlattCertificates.Count131072.C062955
import PlattCertificates.Count131072.C062956
import PlattCertificates.Count131072.C062957
import PlattCertificates.Count131072.C062958
import PlattCertificates.Count131072.C062959
import PlattCertificates.Count131072.C062960
import PlattCertificates.Count131072.C062961
import PlattCertificates.Count131072.C062962
import PlattCertificates.Count131072.C062963
import PlattCertificates.Count131072.C062964
import PlattCertificates.Count131072.C062965
import PlattCertificates.Count131072.C062966
import PlattCertificates.Count131072.C062967
import PlattCertificates.Count131072.C062968
import PlattCertificates.Count131072.C062969
import PlattCertificates.Count131072.C062970
import PlattCertificates.Count131072.C062971
import PlattCertificates.Count131072.C062972
import PlattCertificates.Count131072.C062973
import PlattCertificates.Count131072.C062974
import PlattCertificates.Count131072.C062975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62944 : List PrefixCut := [⟨64,196318509,196318622⟩]
theorem checked62944 : checkPrefixCuts (2^48) 8254128129 10 Manual.Count131072.C062944.packed 64 cuts62944 = true := by
 decide +kernel
def cuts62945 : List PrefixCut := [⟨6,18482493,18482503⟩,
⟨64,191814165,191814281⟩]
theorem checked62945 : checkPrefixCuts (2^48) 8254259201 10 Manual.Count131072.C062945.packed 64 cuts62945 = true := by
 decide +kernel
def pointBounds62945 : List (Nat × Nat × Nat) := [(8254271488,114507876390204,114508265136205)]
theorem point_links_checked62945 : (cuts62945.take 1).map (fun c => (8254259201-1+2*2^10*c.k,114507857907711+c.lower,114508246653702+c.upper)) = pointBounds62945 := by
 decide +kernel
def cuts62946 : List PrefixCut := [⟨64,197642167,197642280⟩]
theorem checked62946 : checkPrefixCuts (2^48) 8254390273 10 Manual.Count131072.C062946.packed 64 cuts62946 = true := by
 decide +kernel
def cuts62947 : List PrefixCut := [⟨4,12514504,12514510⟩,
⟨64,191467061,191467167⟩]
theorem checked62947 : checkPrefixCuts (2^48) 8254521345 10 Manual.Count131072.C062947.packed 64 cuts62947 = true := by
 decide +kernel
def pointBounds62947 : List (Nat × Nat × Nat) := [(8254529536,114508259878547,114508648624773)]
theorem point_links_checked62947 : (cuts62947.take 1).map (fun c => (8254521345-1+2*2^10*c.k,114508247364043+c.lower,114508636110263+c.upper)) = pointBounds62947 := by
 decide +kernel
def cuts62948 : List PrefixCut := [⟨64,196919826,196919939⟩]
theorem checked62948 : checkPrefixCuts (2^48) 8254652417 10 Manual.Count131072.C062948.packed 64 cuts62948 = true := by
 decide +kernel
def cuts62949 : List PrefixCut := [⟨2,6308202,6308205⟩,
⟨64,195655060,195655170⟩]
theorem checked62949 : checkPrefixCuts (2^48) 8254783489 10 Manual.Count131072.C062949.packed 64 cuts62949 = true := by
 decide +kernel
def pointBounds62949 : List (Nat × Nat × Nat) := [(8254787584,114508642059132,114509030805574)]
theorem point_links_checked62949 : (cuts62949.take 1).map (fun c => (8254783489-1+2*2^10*c.k,114508635750930+c.lower,114509024497369+c.upper)) = pointBounds62949 := by
 decide +kernel
def cuts62950 : List PrefixCut := [⟨64,197663700,197663814⟩]
theorem checked62950 : checkPrefixCuts (2^48) 8254914561 10 Manual.Count131072.C062950.packed 64 cuts62950 = true := by
 decide +kernel
def pointBounds62950 : List (Nat × Nat × Nat) := [(8255045632,114509029069690,114509417816353)]
theorem point_links_checked62950 : (cuts62950.take 1).map (fun c => (8254914561-1+2*2^10*c.k,114508831405990+c.lower,114509220152539+c.upper)) = pointBounds62950 := by
 decide +kernel
def cuts62951 : List PrefixCut := [⟨64,195171474,195171587⟩]
theorem checked62951 : checkPrefixCuts (2^48) 8255045633 10 Manual.Count131072.C062951.packed 64 cuts62951 = true := by
 decide +kernel
def cuts62952 : List PrefixCut := [⟨62,190156236,190156341⟩,
⟨64,195543442,195543551⟩]
theorem checked62952 : checkPrefixCuts (2^48) 8255176705 10 Manual.Count131072.C062952.packed 64 cuts62952 = true := by
 decide +kernel
def pointBounds62952 : List (Nat × Nat × Nat) := [(8255303680,114509414397400,114509803144281)]
theorem point_links_checked62952 : (cuts62952.take 1).map (fun c => (8255176705-1+2*2^10*c.k,114509224241164+c.lower,114509612987940+c.upper)) = pointBounds62952 := by
 decide +kernel
def cuts62953 : List PrefixCut := [⟨64,195165290,195165402⟩]
theorem checked62953 : checkPrefixCuts (2^48) 8255307777 10 Manual.Count131072.C062953.packed 64 cuts62953 = true := by
 decide +kernel
def cuts62954 : List PrefixCut := [⟨60,183876690,183876798⟩,
⟨64,196048665,196048780⟩]
theorem checked62954 : checkPrefixCuts (2^48) 8255438849 10 Manual.Count131072.C062954.packed 64 cuts62954 = true := by
 decide +kernel
def pointBounds62954 : List (Nat × Nat × Nat) := [(8255561728,114509798826586,114510187573691)]
theorem point_links_checked62954 : (cuts62954.take 1).map (fun c => (8255438849-1+2*2^10*c.k,114509614949896+c.lower,114510003696893+c.upper)) = pointBounds62954 := by
 decide +kernel
def cuts62955 : List PrefixCut := [⟨64,193522547,193522662⟩]
theorem checked62955 : checkPrefixCuts (2^48) 8255569921 10 Manual.Count131072.C062955.packed 64 cuts62955 = true := by
 decide +kernel
def cuts62956 : List PrefixCut := [⟨58,178074863,178074968⟩,
⟨64,196962991,196963106⟩]
theorem checked62956 : checkPrefixCuts (2^48) 8255700993 10 Manual.Count131072.C062956.packed 64 cuts62956 = true := by
 decide +kernel
def pointBounds62956 : List (Nat × Nat × Nat) := [(8255819776,114510182595971,114510571343303)]
theorem point_links_checked62956 : (cuts62956.take 1).map (fun c => (8255700993-1+2*2^10*c.k,114510004521108+c.lower,114510393268335+c.upper)) = pointBounds62956 := by
 decide +kernel
def cuts62957 : List PrefixCut := [⟨64,196618936,196619048⟩]
theorem checked62957 : checkPrefixCuts (2^48) 8255832065 10 Manual.Count131072.C062957.packed 64 cuts62957 = true := by
 decide +kernel
def cuts62958 : List PrefixCut := [⟨56,169477743,169477845⟩,
⟨64,194570206,194570322⟩]
theorem checked62958 : checkPrefixCuts (2^48) 8255963137 10 Manual.Count131072.C062958.packed 64 cuts62958 = true := by
 decide +kernel
def pointBounds62958 : List (Nat × Nat × Nat) := [(8256077824,114510567580778,114510956328334)]
theorem point_links_checked62958 : (cuts62958.take 1).map (fun c => (8255963137-1+2*2^10*c.k,114510398103035+c.lower,114510786850489+c.upper)) = pointBounds62958 := by
 decide +kernel
def cuts62959 : List PrefixCut := [⟨64,195964924,195965040⟩]
theorem checked62959 : checkPrefixCuts (2^48) 8256094209 10 Manual.Count131072.C062959.packed 64 cuts62959 = true := by
 decide +kernel
def cuts62960 : List PrefixCut := [⟨54,166097268,166097367⟩,
⟨64,196370916,196371031⟩]
theorem checked62960 : checkPrefixCuts (2^48) 8256225281 10 Manual.Count131072.C062960.packed 64 cuts62960 = true := by
 decide +kernel
def pointBounds62960 : List (Nat × Nat × Nat) := [(8256335872,114510954735433,114511343483218)]
theorem point_links_checked62960 : (cuts62960.take 1).map (fun c => (8256225281-1+2*2^10*c.k,114510788638165+c.lower,114511177385851+c.upper)) = pointBounds62960 := by
 decide +kernel
def cuts62961 : List PrefixCut := [⟨64,198583740,198583848⟩]
theorem checked62961 : checkPrefixCuts (2^48) 8256356353 10 Manual.Count131072.C062961.packed 64 cuts62961 = true := by
 decide +kernel
def cuts62962 : List PrefixCut := [⟨52,160467008,160467101⟩,
⟨64,196126057,196126171⟩]
theorem checked62962 : checkPrefixCuts (2^48) 8256487425 10 Manual.Count131072.C062962.packed 64 cuts62962 = true := by
 decide +kernel
def pointBounds62962 : List (Nat × Nat × Nat) := [(8256593920,114511344059829,114511732807831)]
theorem point_links_checked62962 : (cuts62962.take 1).map (fun c => (8256487425-1+2*2^10*c.k,114511183592821+c.lower,114511572340730+c.upper)) = pointBounds62962 := by
 decide +kernel
def cuts62963 : List PrefixCut := [⟨64,194657037,194657144⟩]
theorem checked62963 : checkPrefixCuts (2^48) 8256618497 10 Manual.Count131072.C062963.packed 64 cuts62963 = true := by
 decide +kernel
def cuts62964 : List PrefixCut := [⟨50,151734890,151734977⟩,
⟨64,192881276,192881386⟩]
theorem checked62964 : checkPrefixCuts (2^48) 8256749569 10 Manual.Count131072.C062964.packed 64 cuts62964 = true := by
 decide +kernel
def pointBounds62964 : List (Nat × Nat × Nat) := [(8256851968,114511726110805,114512114859022)]
theorem point_links_checked62964 : (cuts62964.take 1).map (fun c => (8256749569-1+2*2^10*c.k,114511574375915+c.lower,114511963124045+c.upper)) = pointBounds62964 := by
 decide +kernel
def cuts62965 : List PrefixCut := [⟨64,195980342,195980458⟩]
theorem checked62965 : checkPrefixCuts (2^48) 8256880641 10 Manual.Count131072.C062965.packed 64 cuts62965 = true := by
 decide +kernel
def cuts62966 : List PrefixCut := [⟨48,146378146,146378233⟩,
⟨64,196249951,196250065⟩]
theorem checked62966 : checkPrefixCuts (2^48) 8257011713 10 Manual.Count131072.C062966.packed 64 cuts62966 = true := by
 decide +kernel
def pointBounds62966 : List (Nat × Nat × Nat) := [(8257110016,114512109615679,114512498364122)]
theorem point_links_checked62966 : (cuts62966.take 1).map (fun c => (8257011713-1+2*2^10*c.k,114511963237533+c.lower,114512351985889+c.upper)) = pointBounds62966 := by
 decide +kernel
def cuts62967 : List PrefixCut := [⟨64,198530739,198530853⟩]
theorem checked62967 : checkPrefixCuts (2^48) 8257142785 10 Manual.Count131072.C062967.packed 64 cuts62967 = true := by
 decide +kernel
def cuts62968 : List PrefixCut := [⟨46,141328517,141328595⟩,
⟨64,194573428,194573538⟩]
theorem checked62968 : checkPrefixCuts (2^48) 8257273857 10 Manual.Count131072.C062968.packed 64 cuts62968 = true := by
 decide +kernel
def pointBounds62968 : List (Nat × Nat × Nat) := [(8257368064,114512499346740,114512888095402)]
theorem point_links_checked62968 : (cuts62968.take 1).map (fun c => (8257273857-1+2*2^10*c.k,114512358018223+c.lower,114512746766807+c.upper)) = pointBounds62968 := by
 decide +kernel
def cuts62969 : List PrefixCut := [⟨64,196411060,196411169⟩]
theorem checked62969 : checkPrefixCuts (2^48) 8257404929 10 Manual.Count131072.C062969.packed 64 cuts62969 = true := by
 decide +kernel
def cuts62970 : List PrefixCut := [⟨44,132120620,132120696⟩,
⟨64,192999244,192999353⟩]
theorem checked62970 : checkPrefixCuts (2^48) 8257536001 10 Manual.Count131072.C062970.packed 64 cuts62970 = true := by
 decide +kernel
def pointBounds62970 : List (Nat × Nat × Nat) := [(8257626112,114512881123331,114513269872210)]
theorem point_links_checked62970 : (cuts62970.take 1).map (fun c => (8257536001-1+2*2^10*c.k,114512749002711+c.lower,114513137751514+c.upper)) = pointBounds62970 := by
 decide +kernel
def cuts62971 : List PrefixCut := [⟨64,197018365,197018481⟩]
theorem checked62971 : checkPrefixCuts (2^48) 8257667073 10 Manual.Count131072.C062971.packed 64 cuts62971 = true := by
 decide +kernel
def cuts62972 : List PrefixCut := [⟨43,130241719,130241796⟩,
⟨64,193027210,193027322⟩]
theorem checked62972 : checkPrefixCuts (2^48) 8257798145 10 Manual.Count131072.C062972.packed 64 cuts62972 = true := by
 decide +kernel
def pointBounds62972 : List (Nat × Nat × Nat) := [(8257886208,114513269262039,114513658011144)]
theorem point_links_checked62972 : (cuts62972.take 1).map (fun c => (8257798145-1+2*2^10*c.k,114513139020320+c.lower,114513527769348+c.upper)) = pointBounds62972 := by
 decide +kernel
def cuts62973 : List PrefixCut := [⟨64,195989552,195989665⟩]
theorem checked62973 : checkPrefixCuts (2^48) 8257929217 10 Manual.Count131072.C062973.packed 64 cuts62973 = true := by
 decide +kernel
def cuts62974 : List PrefixCut := [⟨42,126624622,126624696⟩,
⟨64,193259661,193259774⟩]
theorem checked62974 : checkPrefixCuts (2^48) 8258060289 10 Manual.Count131072.C062974.packed 64 cuts62974 = true := by
 decide +kernel
def pointBounds62974 : List (Nat × Nat × Nat) := [(8258146304,114513654661704,114514043411031)]
theorem point_links_checked62974 : (cuts62974.take 1).map (fun c => (8258060289-1+2*2^10*c.k,114513528037082+c.lower,114513916786335+c.upper)) = pointBounds62974 := by
 decide +kernel
def cuts62975 : List PrefixCut := [⟨64,199119059,199119173⟩]
theorem checked62975 : checkPrefixCuts (2^48) 8258191361 10 Manual.Count131072.C062975.packed 64 cuts62975 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000092
