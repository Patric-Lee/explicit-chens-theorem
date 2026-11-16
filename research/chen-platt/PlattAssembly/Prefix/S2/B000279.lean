import PlattAssemblyKernel
import PlattCertificates.Count131072.C018928
import PlattCertificates.Count131072.C018929
import PlattCertificates.Count131072.C018930
import PlattCertificates.Count131072.C018931
import PlattCertificates.Count131072.C018932
import PlattCertificates.Count131072.C018933
import PlattCertificates.Count131072.C018934
import PlattCertificates.Count131072.C018935
import PlattCertificates.Count131072.C018936
import PlattCertificates.Count131072.C018937
import PlattCertificates.Count131072.C018938
import PlattCertificates.Count131072.C018939
import PlattCertificates.Count131072.C018940
import PlattCertificates.Count131072.C018941
import PlattCertificates.Count131072.C018942
import PlattCertificates.Count131072.C018943
import PlattCertificates.Count131072.C018944
import PlattCertificates.Count131072.C018945
import PlattCertificates.Count131072.C018946
import PlattCertificates.Count131072.C018947
import PlattCertificates.Count131072.C018948
import PlattCertificates.Count131072.C018949
import PlattCertificates.Count131072.C018950
import PlattCertificates.Count131072.C018951
import PlattCertificates.Count131072.C018952
import PlattCertificates.Count131072.C018953
import PlattCertificates.Count131072.C018954
import PlattCertificates.Count131072.C018955
import PlattCertificates.Count131072.C018956
import PlattCertificates.Count131072.C018957
import PlattCertificates.Count131072.C018958
import PlattCertificates.Count131072.C018959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000279
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18928 : List PrefixCut := [⟨18,97077017,97077074⟩,
⟨94,507692350,507692657⟩,
⟨128,693229662,693230081⟩]
theorem checked18928 : checkPrefixCuts (2^48) 2484862977 9 Manual.Count131072.C018928.packed 128 cuts18928 = true := by
 decide +kernel
def pointBounds18928 : List (Nat × Nat × Nat) := [(2484881408,99306121158561,99306501104286),(2484959232,99306531773894,99306911719869)]
theorem point_links_checked18928 : (cuts18928.take 2).map (fun c => (2484862977-1+2*2^9*c.k,99306024081544+c.lower,99306404027212+c.upper)) = pointBounds18928 := by
 decide +kernel
def cuts18929 : List PrefixCut := [⟨42,228689854,228689991⟩,
⟨118,633389758,633390137⟩,
⟨128,687303472,687303884⟩]
theorem checked18929 : checkPrefixCuts (2^48) 2484994049 9 Manual.Count131072.C018929.packed 128 cuts18929 = true := by
 decide +kernel
def pointBounds18929 : List (Nat × Nat × Nat) := [(2485037056,99306946001060,99307325947284),(2485114880,99307350700964,99307730647430)]
theorem point_links_checked18929 : (cuts18929.take 2).map (fun c => (2484994049-1+2*2^9*c.k,99306717311206+c.lower,99307097257293+c.upper)) = pointBounds18929 := by
 decide +kernel
def cuts18930 : List PrefixCut := [⟨66,350320396,350320610⟩,
⟨128,677979673,677980090⟩]
theorem checked18930 : checkPrefixCuts (2^48) 2485125121 9 Manual.Count131072.C018930.packed 128 cuts18930 = true := by
 decide +kernel
def pointBounds18930 : List (Nat × Nat × Nat) := [(2485192704,99307754935074,99308134881787)]
theorem point_links_checked18930 : (cuts18930.take 1).map (fun c => (2485125121-1+2*2^9*c.k,99307404614678+c.lower,99307784561177+c.upper)) = pointBounds18930 := by
 decide +kernel
def cuts18931 : List PrefixCut := [⟨14,75203027,75203072⟩,
⟨90,489831308,489831599⟩,
⟨128,693346633,693347040⟩]
theorem checked18931 : checkPrefixCuts (2^48) 2485256193 9 Manual.Count131072.C018931.packed 128 cuts18931 = true := by
 decide +kernel
def pointBounds18931 : List (Nat × Nat × Nat) := [(2485270528,99308157797378,99308537744339),(2485348352,99308572425659,99308952372866)]
theorem point_links_checked18931 : (cuts18931.take 2).map (fun c => (2485256193-1+2*2^9*c.k,99308082594351+c.lower,99308462541267+c.upper)) = pointBounds18931 := by
 decide +kernel
def cuts18932 : List PrefixCut := [⟨38,194565311,194565430⟩,
⟨114,601127031,601127391⟩,
⟨128,677228525,677228931⟩]
theorem checked18932 : checkPrefixCuts (2^48) 2485387265 9 Manual.Count131072.C018932.packed 128 cuts18932 = true := by
 decide +kernel
def pointBounds18932 : List (Nat × Nat × Nat) := [(2485426176,99308970506295,99309350453737),(2485504000,99309377068015,99309757015698)]
theorem point_links_checked18932 : (cuts18932.take 2).map (fun c => (2485387265-1+2*2^9*c.k,99308775940984+c.lower,99309155888307+c.upper)) = pointBounds18932 := by
 decide +kernel
def cuts18933 : List PrefixCut := [⟨62,337015637,337015838⟩,
⟨128,685912773,685913177⟩]
theorem checked18933 : checkPrefixCuts (2^48) 2485518337 9 Manual.Count131072.C018933.packed 128 cuts18933 = true := by
 decide +kernel
def pointBounds18933 : List (Nat × Nat × Nat) := [(2485581824,99309790185146,99310170133076)]
theorem point_links_checked18933 : (cuts18933.take 1).map (fun c => (2485518337-1+2*2^9*c.k,99309453169509+c.lower,99309833117238+c.upper)) = pointBounds18933 := by
 decide +kernel
def cuts18934 : List PrefixCut := [⟨10,49825485,49825515⟩,
⟨86,455216563,455216839⟩,
⟨128,679761558,679761969⟩]
theorem checked18934 : checkPrefixCuts (2^48) 2485649409 9 Manual.Count131072.C018934.packed 128 cuts18934 = true := by
 decide +kernel
def pointBounds18934 : List (Nat × Nat × Nat) := [(2485659648,99310188907767,99310568855930),(2485737472,99310594298845,99310974247254)]
theorem point_links_checked18934 : (cuts18934.take 2).map (fun c => (2485649409-1+2*2^9*c.k,99310139082282+c.lower,99310519030415+c.upper)) = pointBounds18934 := by
 decide +kernel
def cuts18935 : List PrefixCut := [⟨34,181852543,181852651⟩,
⟨110,583708203,583708552⟩,
⟨128,681537588,681537997⟩]
theorem checked18935 : checkPrefixCuts (2^48) 2485780481 9 Manual.Count131072.C018935.packed 128 cuts18935 = true := by
 decide +kernel
def pointBounds18935 : List (Nat × Nat × Nat) := [(2485815296,99311000696383,99311380645035),(2485893120,99311402552043,99311782500936)]
theorem point_links_checked18935 : (cuts18935.take 2).map (fun c => (2485780481-1+2*2^9*c.k,99310818843840+c.lower,99311198792384+c.upper)) = pointBounds18935 := by
 decide +kernel
def cuts18936 : List PrefixCut := [⟨58,309674991,309675186⟩,
⟨128,681841296,681841717⟩]
theorem checked18936 : checkPrefixCuts (2^48) 2485911553 9 Manual.Count131072.C018936.packed 128 cuts18936 = true := by
 decide +kernel
def pointBounds18936 : List (Nat × Nat × Nat) := [(2485970944,99311810056419,99312190005567)]
theorem point_links_checked18936 : (cuts18936.take 1).map (fun c => (2485911553-1+2*2^9*c.k,99311500381428+c.lower,99311880330381+c.upper)) = pointBounds18936 := by
 decide +kernel
def cuts18937 : List PrefixCut := [⟨6,35098800,35098821⟩,
⟨82,440539684,440539950⟩,
⟨128,685088775,685089186⟩]
theorem checked18937 : checkPrefixCuts (2^48) 2486042625 9 Manual.Count131072.C018937.packed 128 cuts18937 = true := by
 decide +kernel
def pointBounds18937 : List (Nat × Nat × Nat) := [(2486048768,99312217321524,99312597270919),(2486126592,99312622762408,99313002712048)]
theorem point_links_checked18937 : (cuts18937.take 2).map (fun c => (2486042625-1+2*2^9*c.k,99312182222724+c.lower,99312562172098+c.upper)) = pointBounds18937 := by
 decide +kernel
def cuts18938 : List PrefixCut := [⟨30,162237674,162237774⟩,
⟨106,566294602,566294941⟩,
⟨128,680976994,680977404⟩]
theorem checked18938 : checkPrefixCuts (2^48) 2486173697 9 Manual.Count131072.C018938.packed 128 cuts18938 = true := by
 decide +kernel
def pointBounds18938 : List (Nat × Nat × Nat) := [(2486204416,99313029549173,99313409499058),(2486282240,99313433606101,99313813556225)]
theorem point_links_checked18938 : (cuts18938.take 2).map (fun c => (2486173697-1+2*2^9*c.k,99312867311499+c.lower,99313247261284+c.upper)) = pointBounds18938 := by
 decide +kernel
def cuts18939 : List PrefixCut := [⟨54,292305307,292305478⟩,
⟨128,688186286,688186697⟩]
theorem checked18939 : checkPrefixCuts (2^48) 2486304769 9 Manual.Count131072.C018939.packed 128 cuts18939 = true := by
 decide +kernel
def pointBounds18939 : List (Nat × Nat × Nat) := [(2486360064,99313840593800,99314220544166)]
theorem point_links_checked18939 : (cuts18939.take 1).map (fun c => (2486304769-1+2*2^9*c.k,99313548288493+c.lower,99313928238688+c.upper)) = pointBounds18939 := by
 decide +kernel
def cuts18940 : List PrefixCut := [⟨2,11433616,11433623⟩,
⟨78,418056300,418056551⟩,
⟨128,687923583,687923997⟩]
theorem checked18940 : checkPrefixCuts (2^48) 2486435841 9 Manual.Count131072.C018940.packed 128 cuts18940 = true := by
 decide +kernel
def pointBounds18940 : List (Nat × Nat × Nat) := [(2486437888,99314247908395,99314627859008),(2486515712,99314654531079,99315034481936)]
theorem point_links_checked18940 : (cuts18940.take 2).map (fun c => (2486435841-1+2*2^9*c.k,99314236474779+c.lower,99314616425385+c.upper)) = pointBounds18940 := by
 decide +kernel
def cuts18941 : List PrefixCut := [⟨26,134705132,134705216⟩,
⟨102,545830169,545830496⟩,
⟨128,686189295,686189706⟩]
theorem checked18941 : checkPrefixCuts (2^48) 2486566913 9 Manual.Count131072.C018941.packed 128 cuts18941 = true := by
 decide +kernel
def pointBounds18941 : List (Nat × Nat × Nat) := [(2486593536,99315059103494,99315439054598),(2486671360,99315470228531,99315850179878)]
theorem point_links_checked18941 : (cuts18941.take 2).map (fun c => (2486566913-1+2*2^9*c.k,99314924398362+c.lower,99315304349382+c.upper)) = pointBounds18941 := by
 decide +kernel
def cuts18942 : List PrefixCut := [⟨50,270187077,270187239⟩,
⟨126,678117062,678117466⟩,
⟨128,688869762,688870172⟩]
theorem checked18942 : checkPrefixCuts (2^48) 2486697985 9 Manual.Count131072.C018942.packed 128 cuts18942 = true := by
 decide +kernel
def pointBounds18942 : List (Nat × Nat × Nat) := [(2486749184,99315880774734,99316260726327),(2486827008,99316288704719,99316668656554)]
theorem point_links_checked18942 : (cuts18942.take 2).map (fun c => (2486697985-1+2*2^9*c.k,99315610587657+c.lower,99315990539088+c.upper)) = pointBounds18942 := by
 decide +kernel
def cuts18943 : List PrefixCut := [⟨74,393542692,393542926⟩,
⟨128,680571115,680571519⟩]
theorem checked18943 : checkPrefixCuts (2^48) 2486829057 9 Manual.Count131072.C018943.packed 128 cuts18943 = true := by
 decide +kernel
def pointBounds18943 : List (Nat × Nat × Nat) := [(2486904832,99316693000111,99317072952186)]
theorem point_links_checked18943 : (cuts18943.take 1).map (fun c => (2486829057-1+2*2^9*c.k,99316299457419+c.lower,99316679409260+c.upper)) = pointBounds18943 := by
 decide +kernel
def cuts18944 : List PrefixCut := [⟨22,118046520,118046592⟩,
⟨98,523335123,523335436⟩,
⟨128,680535231,680535641⟩]
theorem checked18944 : checkPrefixCuts (2^48) 2486960129 9 Manual.Count131072.C018944.packed 128 cuts18944 = true := by
 decide +kernel
def pointBounds18944 : List (Nat × Nat × Nat) := [(2486982656,99317098075054,99317478027371),(2487060480,99317503363657,99317883316215)]
theorem point_links_checked18944 : (cuts18944.take 2).map (fun c => (2486960129-1+2*2^9*c.k,99316980028534+c.lower,99317359980779+c.upper)) = pointBounds18944 := by
 decide +kernel
def cuts18945 : List PrefixCut := [⟨46,248302129,248302279⟩,
⟨122,648472711,648473103⟩,
⟨128,680499398,680499811⟩]
theorem checked18945 : checkPrefixCuts (2^48) 2487091201 9 Manual.Count131072.C018945.packed 128 cuts18945 = true := by
 decide +kernel
def pointBounds18945 : List (Nat × Nat × Nat) := [(2487138304,99317908865894,99318288818699),(2487216128,99318309036476,99318688989523)]
theorem point_links_checked18945 : (cuts18945.take 2).map (fun c => (2487091201-1+2*2^9*c.k,99317660563765+c.lower,99318040516420+c.upper)) = pointBounds18945 := by
 decide +kernel
def cuts18946 : List PrefixCut := [⟨70,380466590,380466820⟩,
⟨128,692006399,692006816⟩]
theorem checked18946 : checkPrefixCuts (2^48) 2487222273 9 Manual.Count131072.C018946.packed 128 cuts18946 = true := by
 decide +kernel
def pointBounds18946 : List (Nat × Nat × Nat) := [(2487293952,99318721529753,99319101483051)]
theorem point_links_checked18946 : (cuts18946.take 1).map (fun c => (2487222273-1+2*2^9*c.k,99318341063163+c.lower,99318721016231+c.upper)) = pointBounds18946 := by
 decide +kernel
def cuts18947 : List PrefixCut := [⟨18,97658799,97658857⟩,
⟨94,506391953,506392257⟩,
⟨128,687669838,687670250⟩]
theorem checked18947 : checkPrefixCuts (2^48) 2487353345 9 Manual.Count131072.C018947.packed 128 cuts18947 = true := by
 decide +kernel
def pointBounds18947 : List (Nat × Nat × Nat) := [(2487371776,99319130728361,99319510681904),(2487449600,99319539461515,99319919415304)]
theorem point_links_checked18947 : (cuts18947.take 2).map (fun c => (2487353345-1+2*2^9*c.k,99319033069562+c.lower,99319413023047+c.upper)) = pointBounds18947 := by
 decide +kernel
def cuts18948 : List PrefixCut := [⟨42,221105776,221105908⟩,
⟨118,630039727,630040106⟩,
⟨128,686275637,686276049⟩]
theorem checked18948 : checkPrefixCuts (2^48) 2487484417 9 Manual.Count131072.C018948.packed 128 cuts18948 = true := by
 decide +kernel
def pointBounds18948 : List (Nat × Nat × Nat) := [(2487527424,99319941845176,99320321799205),(2487605248,99320350779127,99320730733403)]
theorem point_links_checked18948 : (cuts18948.take 2).map (fun c => (2487484417-1+2*2^9*c.k,99319720739400+c.lower,99320100693297+c.upper)) = pointBounds18948 := by
 decide +kernel
def cuts18949 : List PrefixCut := [⟨66,353929917,353930124⟩,
⟨128,687710500,687710902⟩]
theorem checked18949 : checkPrefixCuts (2^48) 2487615489 9 Manual.Count131072.C018949.packed 128 cuts18949 = true := by
 decide +kernel
def pointBounds18949 : List (Nat × Nat × Nat) := [(2487683072,99320760944954,99321140899470)]
theorem point_links_checked18949 : (cuts18949.take 1).map (fun c => (2487615489-1+2*2^9*c.k,99320407015037+c.lower,99320786969346+c.upper)) = pointBounds18949 := by
 decide +kernel
def cuts18950 : List PrefixCut := [⟨14,72412287,72412331⟩,
⟨90,474519250,474519536⟩,
⟨128,679301664,679302072⟩]
theorem checked18950 : checkPrefixCuts (2^48) 2487746561 9 Manual.Count131072.C018950.packed 128 cuts18950 = true := by
 decide +kernel
def pointBounds18950 : List (Nat × Nat × Nat) := [(2487760896,99321167137824,99321547092579),(2487838720,99321569244787,99321949199784)]
theorem point_links_checked18950 : (cuts18950.take 2).map (fun c => (2487746561-1+2*2^9*c.k,99321094725537+c.lower,99321474680248+c.upper)) = pointBounds18950 := by
 decide +kernel
def cuts18951 : List PrefixCut := [⟨38,200593101,200593223⟩,
⟨114,615572349,615572717⟩,
⟨128,692729003,692729416⟩]
theorem checked18951 : checkPrefixCuts (2^48) 2487877633 9 Manual.Count131072.C018951.packed 128 cuts18951 = true := by
 decide +kernel
def pointBounds18951 : List (Nat × Nat × Nat) := [(2487916544,99321974620302,99322354575543),(2487994368,99322389599550,99322769555037)]
theorem point_links_checked18951 : (cuts18951.take 2).map (fun c => (2487877633-1+2*2^9*c.k,99321774027201+c.lower,99322153982320+c.upper)) = pointBounds18951 := by
 decide +kernel
def cuts18952 : List PrefixCut := [⟨62,324347016,324347214⟩,
⟨128,676854346,676854756⟩]
theorem checked18952 : checkPrefixCuts (2^48) 2488008705 9 Manual.Count131072.C018952.packed 128 cuts18952 = true := by
 decide +kernel
def pointBounds18952 : List (Nat × Nat × Nat) := [(2488072192,99322791103220,99323171058950)]
theorem point_links_checked18952 : (cuts18952.take 1).map (fun c => (2488008705-1+2*2^9*c.k,99322466756204+c.lower,99322846711736+c.upper)) = pointBounds18952 := by
 decide +kernel
def cuts18953 : List PrefixCut := [⟨10,55658192,55658226⟩,
⟨86,461096071,461096352⟩,
⟨128,681230805,681231218⟩]
theorem checked18953 : checkPrefixCuts (2^48) 2488139777 9 Manual.Count131072.C018953.packed 128 cuts18953 = true := by
 decide +kernel
def pointBounds18953 : List (Nat × Nat × Nat) := [(2488150016,99323199268742,99323579224718),(2488227840,99323604706621,99323984662844)]
theorem point_links_checked18953 : (cuts18953.take 2).map (fun c => (2488139777-1+2*2^9*c.k,99323143610550+c.lower,99323523566492+c.upper)) = pointBounds18953 := by
 decide +kernel
def cuts18954 : List PrefixCut := [⟨34,176580148,176580254⟩,
⟨110,582445089,582445439⟩,
⟨128,680063455,680063862⟩]
theorem checked18954 : checkPrefixCuts (2^48) 2488270849 9 Manual.Count131072.C018954.packed 128 cuts18954 = true := by
 decide +kernel
def pointBounds18954 : List (Nat × Nat × Nat) := [(2488305664,99324001421503,99324381377964),(2488383488,99324407286444,99324787243149)]
theorem point_links_checked18954 : (cuts18954.take 2).map (fun c => (2488270849-1+2*2^9*c.k,99323824841355+c.lower,99324204797710+c.upper)) = pointBounds18954 := by
 decide +kernel
def cuts18955 : List PrefixCut := [⟨58,303935652,303935837⟩,
⟨128,683420959,683421373⟩]
theorem checked18955 : checkPrefixCuts (2^48) 2488401921 9 Manual.Count131072.C018955.packed 128 cuts18955 = true := by
 decide +kernel
def pointBounds18955 : List (Nat × Nat × Nat) := [(2488461312,99324808840462,99325188797409)]
theorem point_links_checked18955 : (cuts18955.take 1).map (fun c => (2488401921-1+2*2^9*c.k,99324504904810+c.lower,99324884861572+c.upper)) = pointBounds18955 := by
 decide +kernel
def cuts18956 : List PrefixCut := [⟨6,33253935,33253955⟩,
⟨82,446545865,446546132⟩,
⟨128,691641937,691642356⟩]
theorem checked18956 : checkPrefixCuts (2^48) 2488532993 9 Manual.Count131072.C018956.packed 128 cuts18956 = true := by
 decide +kernel
def pointBounds18956 : List (Nat × Nat × Nat) := [(2488539136,99325221579704,99325601536900),(2488616960,99325634871634,99326014829077)]
theorem point_links_checked18956 : (cuts18956.take 2).map (fun c => (2488532993-1+2*2^9*c.k,99325188325769+c.lower,99325568282945+c.upper)) = pointBounds18956 := by
 decide +kernel
def cuts18957 : List PrefixCut := [⟨30,160831188,160831283⟩,
⟨106,570138795,570139132⟩,
⟨128,692623241,692623649⟩]
theorem checked18957 : checkPrefixCuts (2^48) 2488664065 9 Manual.Count131072.C018957.packed 128 cuts18957 = true := by
 decide +kernel
def pointBounds18957 : List (Nat × Nat × Nat) := [(2488694784,99326040798894,99326420756584),(2488772608,99326450106501,99326830064433)]
theorem point_links_checked18957 : (cuts18957.take 2).map (fun c => (2488664065-1+2*2^9*c.k,99325879967706+c.lower,99326259925301+c.upper)) = pointBounds18957 := by
 decide +kernel
def cuts18958 : List PrefixCut := [⟨54,288280680,288280854⟩,
⟨128,679920440,679920854⟩]
theorem checked18958 : checkPrefixCuts (2^48) 2488795137 9 Manual.Count131072.C018958.packed 128 cuts18958 = true := by
 decide +kernel
def pointBounds18958 : List (Nat × Nat × Nat) := [(2488850432,99326860871627,99327240829804)]
theorem point_links_checked18958 : (cuts18958.take 1).map (fun c => (2488795137-1+2*2^9*c.k,99326572590947+c.lower,99326952548950+c.upper)) = pointBounds18958 := by
 decide +kernel
def cuts18959 : List PrefixCut := [⟨2,10743631,10743637⟩,
⟨78,421709266,421709519⟩,
⟨128,692776638,692777056⟩]
theorem checked18959 : checkPrefixCuts (2^48) 2488926209 9 Manual.Count131072.C018959.packed 128 cuts18959 = true := by
 decide +kernel
def pointBounds18959 : List (Nat × Nat × Nat) := [(2488928256,99327263255018,99327643213441),(2489006080,99327674220653,99328054179323)]
theorem point_links_checked18959 : (cuts18959.take 2).map (fun c => (2488926209-1+2*2^9*c.k,99327252511387+c.lower,99327632469804+c.upper)) = pointBounds18959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000279
