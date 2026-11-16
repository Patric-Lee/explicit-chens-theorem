import PlattAssemblyKernel
import PlattCertificates.Count131072.C026944
import PlattCertificates.Count131072.C026945
import PlattCertificates.Count131072.C026946
import PlattCertificates.Count131072.C026947
import PlattCertificates.Count131072.C026948
import PlattCertificates.Count131072.C026949
import PlattCertificates.Count131072.C026950
import PlattCertificates.Count131072.C026951
import PlattCertificates.Count131072.C026952
import PlattCertificates.Count131072.C026953
import PlattCertificates.Count131072.C026954
import PlattCertificates.Count131072.C026955
import PlattCertificates.Count131072.C026956
import PlattCertificates.Count131072.C026957
import PlattCertificates.Count131072.C026958
import PlattCertificates.Count131072.C026959
import PlattCertificates.Count131072.C026960
import PlattCertificates.Count131072.C026961
import PlattCertificates.Count131072.C026962
import PlattCertificates.Count131072.C026963
import PlattCertificates.Count131072.C026964
import PlattCertificates.Count131072.C026965
import PlattCertificates.Count131072.C026966
import PlattCertificates.Count131072.C026967
import PlattCertificates.Count131072.C026968
import PlattCertificates.Count131072.C026969
import PlattCertificates.Count131072.C026970
import PlattCertificates.Count131072.C026971
import PlattCertificates.Count131072.C026972
import PlattCertificates.Count131072.C026973
import PlattCertificates.Count131072.C026974
import PlattCertificates.Count131072.C026975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000217
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26944 : List PrefixCut := [⟨48,177854367,177854466⟩,
⟨128,479978314,479978585⟩]
theorem checked26944 : checkPrefixCuts (2^48) 3535536129 9 Manual.Count131072.C026944.packed 128 cuts26944 = true := by
 decide +kernel
def pointBounds26944 : List (Nat × Nat × Nat) := [(3535585280,103857482595125,103857865148836)]
theorem point_links_checked26944 : (cuts26944.take 1).map (fun c => (3535536129-1+2*2^9*c.k,103857304740758+c.lower,103857687294370+c.upper)) = pointBounds26944 := by
 decide +kernel
def cuts26945 : List PrefixCut := [⟨28,104766496,104766553⟩,
⟨128,471760857,471761120⟩]
theorem checked26945 : checkPrefixCuts (2^48) 3535667201 9 Manual.Count131072.C026945.packed 128 cuts26945 = true := by
 decide +kernel
def pointBounds26945 : List (Nat × Nat × Nat) := [(3535695872,103857889485568,103858272039508)]
theorem point_links_checked26945 : (cuts26945.take 1).map (fun c => (3535667201-1+2*2^9*c.k,103857784719072+c.lower,103858167272955+c.upper)) = pointBounds26945 := by
 decide +kernel
def cuts26946 : List PrefixCut := [⟨8,28021690,28021706⟩,
⟨116,431622762,431623000⟩,
⟨128,476121598,476121861⟩]
theorem checked26946 : checkPrefixCuts (2^48) 3535798273 9 Manual.Count131072.C026946.packed 128 cuts26946 = true := by
 decide +kernel
def pointBounds26946 : List (Nat × Nat × Nat) := [(3535806464,103858284501619,103858667055781),(3535917056,103858688102691,103859070657075)]
theorem point_links_checked26946 : (cuts26946.take 2).map (fun c => (3535798273-1+2*2^9*c.k,103858256479929+c.lower,103858639034075+c.upper)) = pointBounds26946 := by
 decide +kernel
def cuts26947 : List PrefixCut := [⟨96,361318526,361318725⟩,
⟨128,478969747,478970013⟩]
theorem checked26947 : checkPrefixCuts (2^48) 3535929345 9 Manual.Count131072.C026947.packed 128 cuts26947 = true := by
 decide +kernel
def pointBounds26947 : List (Nat × Nat × Nat) := [(3536027648,103859093920053,103859476474661)]
theorem point_links_checked26947 : (cuts26947.take 1).map (fun c => (3535929345-1+2*2^9*c.k,103858732601527+c.lower,103859115155936+c.upper)) = pointBounds26947 := by
 decide +kernel
def cuts26948 : List PrefixCut := [⟨76,289745453,289745616⟩,
⟨128,479827653,479827922⟩]
theorem checked26948 : checkPrefixCuts (2^48) 3536060417 9 Manual.Count131072.C026948.packed 128 cuts26948 = true := by
 decide +kernel
def pointBounds26948 : List (Nat × Nat × Nat) := [(3536138240,103859501316727,103859883871565)]
theorem point_links_checked26948 : (cuts26948.take 1).map (fun c => (3536060417-1+2*2^9*c.k,103859211571274+c.lower,103859594125949+c.upper)) = pointBounds26948 := by
 decide +kernel
def cuts26949 : List PrefixCut := [⟨56,208386712,208386830⟩,
⟨128,478854621,478854889⟩]
theorem checked26949 : checkPrefixCuts (2^48) 3536191489 9 Manual.Count131072.C026949.packed 128 cuts26949 = true := by
 decide +kernel
def pointBounds26949 : List (Nat × Nat × Nat) := [(3536248832,103859899785639,103860282340701)]
theorem point_links_checked26949 : (cuts26949.take 1).map (fun c => (3536191489-1+2*2^9*c.k,103859691398927+c.lower,103860073953871+c.upper)) = pointBounds26949 := by
 decide +kernel
def cuts26950 : List PrefixCut := [⟨36,136744135,136744212⟩,
⟨128,470718360,470718626⟩]
theorem checked26950 : checkPrefixCuts (2^48) 3536322561 9 Manual.Count131072.C026950.packed 128 cuts26950 = true := by
 decide +kernel
def pointBounds26950 : List (Nat × Nat × Nat) := [(3536359424,103860306997683,103860689552972)]
theorem point_links_checked26950 : (cuts26950.take 1).map (fun c => (3536322561-1+2*2^9*c.k,103860170253548+c.lower,103860552808760+c.upper)) = pointBounds26950 := by
 decide +kernel
def cuts26951 : List PrefixCut := [⟨16,60569685,60569720⟩,
⟨124,462662477,462662735⟩,
⟨128,476670232,476670497⟩]
theorem checked26951 : checkPrefixCuts (2^48) 3536453633 9 Manual.Count131072.C026951.packed 128 cuts26951 = true := by
 decide +kernel
def pointBounds26951 : List (Nat × Nat × Nat) := [(3536470016,103860701541593,103861084097106),(3536580608,103861103634385,103861486190121)]
theorem point_links_checked26951 : (cuts26951.take 2).map (fun c => (3536453633-1+2*2^9*c.k,103860640971908+c.lower,103861023527386+c.upper)) = pointBounds26951 := by
 decide +kernel
def cuts26952 : List PrefixCut := [⟨104,380511484,380511696⟩,
⟨128,471160845,471161106⟩]
theorem checked26952 : checkPrefixCuts (2^48) 3536584705 9 Manual.Count131072.C026952.packed 128 cuts26952 = true := by
 decide +kernel
def pointBounds26952 : List (Nat × Nat × Nat) := [(3536691200,103861498153624,103861880709579)]
theorem point_links_checked26952 : (cuts26952.take 1).map (fun c => (3536584705-1+2*2^9*c.k,103861117642140+c.lower,103861500197883+c.upper)) = pointBounds26952 := by
 decide +kernel
def cuts26953 : List PrefixCut := [⟨84,312771233,312771401⟩,
⟨128,477112337,477112599⟩]
theorem checked26953 : checkPrefixCuts (2^48) 3536715777 9 Manual.Count131072.C026953.packed 128 cuts26953 = true := by
 decide +kernel
def pointBounds26953 : List (Nat × Nat × Nat) := [(3536801792,103861901574218,103862284130390)]
theorem point_links_checked26953 : (cuts26953.take 1).map (fun c => (3536715777-1+2*2^9*c.k,103861588802985+c.lower,103861971358989+c.upper)) = pointBounds26953 := by
 decide +kernel
def cuts26954 : List PrefixCut := [⟨64,237793516,237793651⟩,
⟨128,476139698,476139968⟩]
theorem checked26954 : checkPrefixCuts (2^48) 3536846849 9 Manual.Count131072.C026954.packed 128 cuts26954 = true := by
 decide +kernel
def pointBounds26954 : List (Nat × Nat × Nat) := [(3536912384,103862303708838,103862686265239)]
theorem point_links_checked26954 : (cuts26954.take 1).map (fun c => (3536846849-1+2*2^9*c.k,103862065915322+c.lower,103862448471588+c.upper)) = pointBounds26954 := by
 decide +kernel
def cuts26955 : List PrefixCut := [⟨44,163855458,163855553⟩,
⟨128,475405813,475406087⟩]
theorem checked26955 : checkPrefixCuts (2^48) 3536977921 9 Manual.Count131072.C026955.packed 128 cuts26955 = true := by
 decide +kernel
def pointBounds26955 : List (Nat × Nat × Nat) := [(3537022976,103862705910478,103863088467109)]
theorem point_links_checked26955 : (cuts26955.take 1).map (fun c => (3536977921-1+2*2^9*c.k,103862542055020+c.lower,103862924611556+c.upper)) = pointBounds26955 := by
 decide +kernel
def cuts26956 : List PrefixCut := [⟨24,88808371,88808423⟩,
⟨128,474035409,474035679⟩]
theorem checked26956 : checkPrefixCuts (2^48) 3537108993 9 Manual.Count131072.C026956.packed 128 cuts26956 = true := by
 decide +kernel
def pointBounds26956 : List (Nat × Nat × Nat) := [(3537133568,103863106269204,103863488826066)]
theorem point_links_checked26956 : (cuts26956.take 1).map (fun c => (3537108993-1+2*2^9*c.k,103863017460833+c.lower,103863400017643+c.upper)) = pointBounds26956 := by
 decide +kernel
def cuts26957 : List PrefixCut := [⟨4,14800890,14800898⟩,
⟨112,412588232,412588466⟩,
⟨128,471073621,471073887⟩]
theorem checked26957 : checkPrefixCuts (2^48) 3537240065 9 Manual.Count131072.C026957.packed 128 cuts26957 = true := by
 decide +kernel
def pointBounds26957 : List (Nat × Nat × Nat) := [(3537244160,103863506297132,103863888854220),(3537354752,103863904084474,103864286641788)]
theorem point_links_checked26957 : (cuts26957.take 2).map (fun c => (3537240065-1+2*2^9*c.k,103863491496242+c.lower,103863874053322+c.upper)) = pointBounds26957 := by
 decide +kernel
def cuts26958 : List PrefixCut := [⟨92,343029376,343029567⟩,
⟨128,472170257,472170522⟩]
theorem checked26958 : checkPrefixCuts (2^48) 3537371137 9 Manual.Count131072.C026958.packed 128 cuts26958 = true := by
 decide +kernel
def pointBounds26958 : List (Nat × Nat × Nat) := [(3537465344,103864305599239,103864688156776)]
theorem point_links_checked26958 : (cuts26958.take 1).map (fun c => (3537371137-1+2*2^9*c.k,103863962569863+c.lower,103864345127209+c.upper)) = pointBounds26958 := by
 decide +kernel
def cuts26959 : List PrefixCut := [⟨72,272759124,272759275⟩,
⟨128,480905147,480905417⟩]
theorem checked26959 : checkPrefixCuts (2^48) 3537502209 9 Manual.Count131072.C026959.packed 128 cuts26959 = true := by
 decide +kernel
def pointBounds26959 : List (Nat × Nat × Nat) := [(3537575936,103864707499244,103865090057006)]
theorem point_links_checked26959 : (cuts26959.take 1).map (fun c => (3537502209-1+2*2^9*c.k,103864434740120+c.lower,103864817297731+c.upper)) = pointBounds26959 := by
 decide +kernel
def cuts26960 : List PrefixCut := [⟨52,197799282,197799393⟩,
⟨128,482319425,482319691⟩]
theorem checked26960 : checkPrefixCuts (2^48) 3537633281 9 Manual.Count131072.C026960.packed 128 cuts26960 = true := by
 decide +kernel
def pointBounds26960 : List (Nat × Nat × Nat) := [(3537686528,103865113444549,103865496002541)]
theorem point_links_checked26960 : (cuts26960.take 1).map (fun c => (3537633281-1+2*2^9*c.k,103864915645267+c.lower,103865298203148+c.upper)) = pointBounds26960 := by
 decide +kernel
def cuts26961 : List PrefixCut := [⟨32,117275222,117275285⟩,
⟨128,473072422,473072685⟩]
theorem checked26961 : checkPrefixCuts (2^48) 3537764353 9 Manual.Count131072.C026961.packed 128 cuts26961 = true := by
 decide +kernel
def pointBounds26961 : List (Nat × Nat × Nat) := [(3537797120,103865515239914,103865897798124)]
theorem point_links_checked26961 : (cuts26961.take 1).map (fun c => (3537764353-1+2*2^9*c.k,103865397964692+c.lower,103865780522839+c.upper)) = pointBounds26961 := by
 decide +kernel
def cuts26962 : List PrefixCut := [⟨12,44235274,44235300⟩,
⟨120,443380106,443380352⟩,
⟨128,472020671,472020934⟩]
theorem checked26962 : checkPrefixCuts (2^48) 3537895425 9 Manual.Count131072.C026962.packed 128 cuts26962 = true := by
 decide +kernel
def pointBounds26962 : List (Nat × Nat × Nat) := [(3537907712,103865915272388,103866297830824),(3538018304,103866314417220,103866696975876)]
theorem point_links_checked26962 : (cuts26962.take 2).map (fun c => (3537895425-1+2*2^9*c.k,103865871037114+c.lower,103866253595524+c.upper)) = pointBounds26962 := by
 decide +kernel
def cuts26963 : List PrefixCut := [⟨100,368582398,368582609⟩,
⟨128,473196446,473196714⟩]
theorem checked26963 : checkPrefixCuts (2^48) 3538026497 9 Manual.Count131072.C026963.packed 128 cuts26963 = true := by
 decide +kernel
def pointBounds26963 : List (Nat × Nat × Nat) := [(3538128896,103866711640183,103867094199067)]
theorem point_links_checked26963 : (cuts26963.take 1).map (fun c => (3538026497-1+2*2^9*c.k,103866343057785+c.lower,103866725616458+c.upper)) = pointBounds26963 := by
 decide +kernel
def cuts26964 : List PrefixCut := [⟨80,296971986,296972152⟩,
⟨128,474372264,474372530⟩]
theorem checked26964 : checkPrefixCuts (2^48) 3538157569 9 Manual.Count131072.C026964.packed 128 cuts26964 = true := by
 decide +kernel
def pointBounds26964 : List (Nat × Nat × Nat) := [(3538239488,103867113226217,103867495785324)]
theorem point_links_checked26964 : (cuts26964.take 1).map (fun c => (3538157569-1+2*2^9*c.k,103866816254231+c.lower,103867198813172+c.upper)) = pointBounds26964 := by
 decide +kernel
def cuts26965 : List PrefixCut := [⟨60,226082383,226082505⟩,
⟨128,480241383,480241648⟩]
theorem checked26965 : checkPrefixCuts (2^48) 3538288641 9 Manual.Count131072.C026965.packed 128 cuts26965 = true := by
 decide +kernel
def pointBounds26965 : List (Nat × Nat × Nat) := [(3538350080,103867516708878,103867899268207)]
theorem point_links_checked26965 : (cuts26965.take 1).map (fun c => (3538288641-1+2*2^9*c.k,103867290626495+c.lower,103867673185702+c.upper)) = pointBounds26965 := by
 decide +kernel
def cuts26966 : List PrefixCut := [⟨40,143424570,143424650⟩,
⟨128,464871027,464871284⟩]
theorem checked26966 : checkPrefixCuts (2^48) 3538419713 9 Manual.Count131072.C026966.packed 128 cuts26966 = true := by
 decide +kernel
def pointBounds26966 : List (Nat × Nat × Nat) := [(3538460672,103867914292448,103868296852000)]
theorem point_links_checked26966 : (cuts26966.take 1).map (fun c => (3538419713-1+2*2^9*c.k,103867770867878+c.lower,103868153427350+c.upper)) = pointBounds26966 := by
 decide +kernel
def cuts26967 : List PrefixCut := [⟨20,76045036,76045079⟩,
⟨128,479012659,479012927⟩]
theorem checked26967 : checkPrefixCuts (2^48) 3538550785 9 Manual.Count131072.C026967.packed 128 cuts26967 = true := by
 decide +kernel
def pointBounds26967 : List (Nat × Nat × Nat) := [(3538571264,103868311783941,103868694343713),(3538681856,103868714751564,103869097311561)]
theorem point_links_checked26967 : (cuts26967.take 2).map (fun c => (3538550785-1+2*2^9*c.k,103868235738905+c.lower,103868618298634+c.upper)) = pointBounds26967 := by
 decide +kernel
def cuts26968 : List PrefixCut := [⟨108,400727857,400728082⟩,
⟨128,473427037,473427302⟩]
theorem checked26968 : checkPrefixCuts (2^48) 3538681857 9 Manual.Count131072.C026968.packed 128 cuts26968 = true := by
 decide +kernel
def pointBounds26968 : List (Nat × Nat × Nat) := [(3538792448,103869115479421,103869498039643)]
theorem point_links_checked26968 : (cuts26968.take 1).map (fun c => (3538681857-1+2*2^9*c.k,103868714751564+c.lower,103869097311561+c.upper)) = pointBounds26968 := by
 decide +kernel
def cuts26969 : List PrefixCut := [⟨88,327220693,327220873⟩,
⟨128,473727620,473727882⟩]
theorem checked26969 : checkPrefixCuts (2^48) 3538812929 9 Manual.Count131072.C026969.packed 128 cuts26969 = true := by
 decide +kernel
def pointBounds26969 : List (Nat × Nat × Nat) := [(3538903040,103869515399294,103869897959736)]
theorem point_links_checked26969 : (cuts26969.take 1).map (fun c => (3538812929-1+2*2^9*c.k,103869188178601+c.lower,103869570738863+c.upper)) = pointBounds26969 := by
 decide +kernel
def cuts26970 : List PrefixCut := [⟨68,251571169,251571305⟩,
⟨128,472755633,472755891⟩]
theorem checked26970 : checkPrefixCuts (2^48) 3538944001 9 Manual.Count131072.C026970.packed 128 cuts26970 = true := by
 decide +kernel
def pointBounds26970 : List (Nat × Nat × Nat) := [(3539013632,103869913477390,103870296038050)]
theorem point_links_checked26970 : (cuts26970.take 1).map (fun c => (3538944001-1+2*2^9*c.k,103869661906221+c.lower,103870044466745+c.upper)) = pointBounds26970 := by
 decide +kernel
def cuts26971 : List PrefixCut := [⟨49,180778292,180778391⟩,
⟨128,472022369,472022629⟩]
theorem checked26971 : checkPrefixCuts (2^48) 3539075073 9 Manual.Count131072.C026971.packed 128 cuts26971 = true := by
 decide +kernel
def pointBounds26971 : List (Nat × Nat × Nat) := [(3539125248,103870315440146,103870698001027)]
theorem point_links_checked26971 : (cuts26971.take 1).map (fun c => (3539075073-1+2*2^9*c.k,103870134661854+c.lower,103870517222636+c.upper)) = pointBounds26971 := by
 decide +kernel
def cuts26972 : List PrefixCut := [⟨30,109831176,109831238⟩,
⟨128,471050523,471050787⟩]
theorem checked26972 : checkPrefixCuts (2^48) 3539206145 9 Manual.Count131072.C026972.packed 128 cuts26972 = true := by
 decide +kernel
def pointBounds26972 : List (Nat × Nat × Nat) := [(3539236864,103870716515399,103871099076503)]
theorem point_links_checked26972 : (cuts26972.take 1).map (fun c => (3539206145-1+2*2^9*c.k,103870606684223+c.lower,103870989245265+c.upper)) = pointBounds26972 := by
 decide +kernel
def cuts26973 : List PrefixCut := [⟨11,41513325,41513349⟩,
⟨120,435167390,435167637⟩,
⟨128,464671060,464671322⟩]
theorem checked26973 : checkPrefixCuts (2^48) 3539337217 9 Manual.Count131072.C026973.packed 128 cuts26973 = true := by
 decide +kernel
def pointBounds26973 : List (Nat × Nat × Nat) := [(3539348480,103871119248071,103871501809401),(3539460096,103871512902136,103871895463689)]
theorem point_links_checked26973 : (cuts26973.take 2).map (fun c => (3539337217-1+2*2^9*c.k,103871077734746+c.lower,103871460296052+c.upper)) = pointBounds26973 := by
 decide +kernel
def cuts26974 : List PrefixCut := [⟨101,373919314,373919525⟩,
⟨128,472844678,472844945⟩]
theorem checked26974 : checkPrefixCuts (2^48) 3539468289 9 Manual.Count131072.C026974.packed 128 cuts26974 = true := by
 decide +kernel
def pointBounds26974 : List (Nat × Nat × Nat) := [(3539571712,103871916325120,103872298886899)]
theorem point_links_checked26974 : (cuts26974.take 1).map (fun c => (3539468289-1+2*2^9*c.k,103871542405806+c.lower,103871924967374+c.upper)) = pointBounds26974 := by
 decide +kernel
def cuts26975 : List PrefixCut := [⟨82,307268145,307268319⟩,
⟨128,480143020,480143288⟩]
theorem checked26975 : checkPrefixCuts (2^48) 3539599361 9 Manual.Count131072.C026975.packed 128 cuts26975 = true := by
 decide +kernel
def pointBounds26975 : List (Nat × Nat × Nat) := [(3539683328,103872322518629,103872705080638)]
theorem point_links_checked26975 : (cuts26975.take 1).map (fun c => (3539599361-1+2*2^9*c.k,103872015250484+c.lower,103872397812319+c.upper)) = pointBounds26975 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000217
