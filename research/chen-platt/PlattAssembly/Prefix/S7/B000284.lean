import PlattAssemblyKernel
import PlattCertificates.Count131072.C069088
import PlattCertificates.Count131072.C069089
import PlattCertificates.Count131072.C069090
import PlattCertificates.Count131072.C069091
import PlattCertificates.Count131072.C069092
import PlattCertificates.Count131072.C069093
import PlattCertificates.Count131072.C069094
import PlattCertificates.Count131072.C069095
import PlattCertificates.Count131072.C069096
import PlattCertificates.Count131072.C069097
import PlattCertificates.Count131072.C069098
import PlattCertificates.Count131072.C069099
import PlattCertificates.Count131072.C069100
import PlattCertificates.Count131072.C069101
import PlattCertificates.Count131072.C069102
import PlattCertificates.Count131072.C069103
import PlattCertificates.Count131072.C069104
import PlattCertificates.Count131072.C069105
import PlattCertificates.Count131072.C069106
import PlattCertificates.Count131072.C069107
import PlattCertificates.Count131072.C069108
import PlattCertificates.Count131072.C069109
import PlattCertificates.Count131072.C069110
import PlattCertificates.Count131072.C069111
import PlattCertificates.Count131072.C069112
import PlattCertificates.Count131072.C069113
import PlattCertificates.Count131072.C069114
import PlattCertificates.Count131072.C069115
import PlattCertificates.Count131072.C069116
import PlattCertificates.Count131072.C069117
import PlattCertificates.Count131072.C069118
import PlattCertificates.Count131072.C069119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000284
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69088 : List PrefixCut := [⟨64,175636355,175636461⟩]
theorem checked69088 : checkPrefixCuts (2^48) 9059434497 10 Manual.Count131072.C069088.packed 64 cuts69088 = true := by
 decide +kernel
def cuts69089 : List PrefixCut := [⟨58,161062498,161062595⟩,
⟨64,177404756,177404861⟩]
theorem checked69089 : checkPrefixCuts (2^48) 9059565569 10 Manual.Count131072.C069089.packed 64 cuts69089 = true := by
 decide +kernel
def pointBounds69089 : List (Nat × Nat × Nat) := [(9059684352,115653206647346,115653596058196)]
theorem point_links_checked69089 : (cuts69089.take 1).map (fun c => (9059565569-1+2*2^10*c.k,115653045584848+c.lower,115653434995601+c.upper)) = pointBounds69089 := by
 decide +kernel
def cuts69090 : List PrefixCut := [⟨64,178613875,178613980⟩]
theorem checked69090 : checkPrefixCuts (2^48) 9059696641 10 Manual.Count131072.C069090.packed 64 cuts69090 = true := by
 decide +kernel
def cuts69091 : List PrefixCut := [⟨64,177554955,177555063⟩]
theorem checked69091 : checkPrefixCuts (2^48) 9059827713 10 Manual.Count131072.C069091.packed 64 cuts69091 = true := by
 decide +kernel
def cuts69092 : List PrefixCut := [⟨5,13763121,13763129⟩,
⟨64,175470852,175470956⟩]
theorem checked69092 : checkPrefixCuts (2^48) 9059958785 10 Manual.Count131072.C069092.packed 64 cuts69092 = true := by
 decide +kernel
def pointBounds69092 : List (Nat × Nat × Nat) := [(9059969024,115653592921555,115653982332634)]
theorem point_links_checked69092 : (cuts69092.take 1).map (fun c => (9059958785-1+2*2^10*c.k,115653579158434+c.lower,115653968569505+c.upper)) = pointBounds69092 := by
 decide +kernel
def cuts69093 : List PrefixCut := [⟨64,173852795,173852900⟩]
theorem checked69093 : checkPrefixCuts (2^48) 9060089857 10 Manual.Count131072.C069093.packed 64 cuts69093 = true := by
 decide +kernel
def cuts69094 : List PrefixCut := [⟨16,44146284,44146311⟩,
⟨64,179069529,179069636⟩]
theorem checked69094 : checkPrefixCuts (2^48) 9060220929 10 Manual.Count131072.C069094.packed 64 cuts69094 = true := by
 decide +kernel
def pointBounds69094 : List (Nat × Nat × Nat) := [(9060253696,115653972628365,115654362039672)]
theorem point_links_checked69094 : (cuts69094.take 1).map (fun c => (9060220929-1+2*2^10*c.k,115653928482081+c.lower,115654317893361+c.upper)) = pointBounds69094 := by
 decide +kernel
def cuts69095 : List PrefixCut := [⟨64,178538826,178538935⟩]
theorem checked69095 : checkPrefixCuts (2^48) 9060352001 10 Manual.Count131072.C069095.packed 64 cuts69095 = true := by
 decide +kernel
def cuts69096 : List PrefixCut := [⟨27,75614935,75614975⟩,
⟨64,178567304,178567403⟩]
theorem checked69096 : checkPrefixCuts (2^48) 9060483073 10 Manual.Count131072.C069096.packed 64 cuts69096 = true := by
 decide +kernel
def pointBounds69096 : List (Nat × Nat × Nat) := [(9060538368,115654361705371,115654751116907)]
theorem point_links_checked69096 : (cuts69096.take 1).map (fun c => (9060483073-1+2*2^10*c.k,115654286090436+c.lower,115654675501932+c.upper)) = pointBounds69096 := by
 decide +kernel
def cuts69097 : List PrefixCut := [⟨64,179217092,179217198⟩]
theorem checked69097 : checkPrefixCuts (2^48) 9060614145 10 Manual.Count131072.C069097.packed 64 cuts69097 = true := by
 decide +kernel
def cuts69098 : List PrefixCut := [⟨38,105994402,105994461⟩,
⟨64,178065101,178065199⟩]
theorem checked69098 : checkPrefixCuts (2^48) 9060745217 10 Manual.Count131072.C069098.packed 64 cuts69098 = true := by
 decide +kernel
def pointBounds69098 : List (Nat × Nat × Nat) := [(9060823040,115654749869234,115655139280994)]
theorem point_links_checked69098 : (cuts69098.take 1).map (fun c => (9060745217-1+2*2^10*c.k,115654643874832+c.lower,115655033286533+c.upper)) = pointBounds69098 := by
 decide +kernel
def cuts69099 : List PrefixCut := [⟨64,175950125,175950229⟩]
theorem checked69099 : checkPrefixCuts (2^48) 9060876289 10 Manual.Count131072.C069099.packed 64 cuts69099 = true := by
 decide +kernel
def cuts69100 : List PrefixCut := [⟨49,135346901,135346983⟩,
⟨64,177065878,177065983⟩]
theorem checked69100 : checkPrefixCuts (2^48) 9061007361 10 Manual.Count131072.C069100.packed 64 cuts69100 = true := by
 decide +kernel
def pointBounds69100 : List (Nat × Nat × Nat) := [(9061107712,115655133236959,115655522648944)]
theorem point_links_checked69100 : (cuts69100.take 1).map (fun c => (9061007361-1+2*2^10*c.k,115654997890058+c.lower,115655387301961+c.upper)) = pointBounds69100 := by
 decide +kernel
def cuts69101 : List PrefixCut := [⟨64,179175663,179175764⟩]
theorem checked69101 : checkPrefixCuts (2^48) 9061138433 10 Manual.Count131072.C069101.packed 64 cuts69101 = true := by
 decide +kernel
def cuts69102 : List PrefixCut := [⟨60,165971242,165971339⟩,
⟨64,177682024,177682128⟩]
theorem checked69102 : checkPrefixCuts (2^48) 9061269505 10 Manual.Count131072.C069102.packed 64 cuts69102 = true := by
 decide +kernel
def pointBounds69102 : List (Nat × Nat × Nat) := [(9061392384,115655520102841,115655909515047)]
theorem point_links_checked69102 : (cuts69102.take 1).map (fun c => (9061269505-1+2*2^10*c.k,115655354131599+c.lower,115655743543708+c.upper)) = pointBounds69102 := by
 decide +kernel
def cuts69103 : List PrefixCut := [⟨64,175008062,175008163⟩]
theorem checked69103 : checkPrefixCuts (2^48) 9061400577 10 Manual.Count131072.C069103.packed 64 cuts69103 = true := by
 decide +kernel
def cuts69104 : List PrefixCut := [⟨64,177707950,177708052⟩]
theorem checked69104 : checkPrefixCuts (2^48) 9061531649 10 Manual.Count131072.C069104.packed 64 cuts69104 = true := by
 decide +kernel
def cuts69105 : List PrefixCut := [⟨7,19569151,19569162⟩,
⟨64,175996972,175997071⟩]
theorem checked69105 : checkPrefixCuts (2^48) 9061662721 10 Manual.Count131072.C069105.packed 64 cuts69105 = true := by
 decide +kernel
def pointBounds69105 : List (Nat × Nat × Nat) := [(9061677056,115655904098786,115656293511213)]
theorem point_links_checked69105 : (cuts69105.take 1).map (fun c => (9061662721-1+2*2^10*c.k,115655884529635+c.lower,115656273942051+c.upper)) = pointBounds69105 := by
 decide +kernel
def cuts69106 : List PrefixCut := [⟨64,178727841,178727946⟩]
theorem checked69106 : checkPrefixCuts (2^48) 9061793793 10 Manual.Count131072.C069106.packed 64 cuts69106 = true := by
 decide +kernel
def cuts69107 : List PrefixCut := [⟨18,50785072,50785102⟩,
⟨64,178041930,178042035⟩]
theorem checked69107 : checkPrefixCuts (2^48) 9061924865 10 Manual.Count131072.C069107.packed 64 cuts69107 = true := by
 decide +kernel
def pointBounds69107 : List (Nat × Nat × Nat) := [(9061961728,115656290039520,115656679452170)]
theorem point_links_checked69107 : (cuts69107.take 1).map (fun c => (9061924865-1+2*2^10*c.k,115656239254448+c.lower,115656628667068+c.upper)) = pointBounds69107 := by
 decide +kernel
def cuts69108 : List PrefixCut := [⟨64,180710541,180710651⟩]
theorem checked69108 : checkPrefixCuts (2^48) 9062055937 10 Manual.Count131072.C069108.packed 64 cuts69108 = true := by
 decide +kernel
def cuts69109 : List PrefixCut := [⟨29,81688510,81688559⟩,
⟨64,177974654,177974758⟩]
theorem checked69109 : checkPrefixCuts (2^48) 9062187009 10 Manual.Count131072.C069109.packed 64 cuts69109 = true := by
 decide +kernel
def pointBounds69109 : List (Nat × Nat × Nat) := [(9062246400,115656679695429,115657069108313)]
theorem point_links_checked69109 : (cuts69109.take 1).map (fun c => (9062187009-1+2*2^10*c.k,115656598006919+c.lower,115656987419754+c.upper)) = pointBounds69109 := by
 decide +kernel
def cuts69110 : List PrefixCut := [⟨64,178220539,178220648⟩]
theorem checked69110 : checkPrefixCuts (2^48) 9062318081 10 Manual.Count131072.C069110.packed 64 cuts69110 = true := by
 decide +kernel
def cuts69111 : List PrefixCut := [⟨40,109918981,109919045⟩,
⟨64,177472541,177472644⟩]
theorem checked69111 : checkPrefixCuts (2^48) 9062449153 10 Manual.Count131072.C069111.packed 64 cuts69111 = true := by
 decide +kernel
def pointBounds69111 : List (Nat × Nat × Nat) := [(9062531072,115657064121093,115657453534205)]
theorem point_links_checked69111 : (cuts69111.take 1).map (fun c => (9062449153-1+2*2^10*c.k,115656954202112+c.lower,115657343615160+c.upper)) = pointBounds69111 := by
 decide +kernel
def cuts69112 : List PrefixCut := [⟨64,178370695,178370795⟩]
theorem checked69112 : checkPrefixCuts (2^48) 9062580225 10 Manual.Count131072.C069112.packed 64 cuts69112 = true := by
 decide +kernel
def cuts69113 : List PrefixCut := [⟨51,141657348,141657432⟩,
⟨64,177778000,177778106⟩]
theorem checked69113 : checkPrefixCuts (2^48) 9062711297 10 Manual.Count131072.C069113.packed 64 cuts69113 = true := by
 decide +kernel
def pointBounds69113 : List (Nat × Nat × Nat) := [(9062815744,115657451702696,115657841116031)]
theorem point_links_checked69113 : (cuts69113.take 1).map (fun c => (9062711297-1+2*2^10*c.k,115657310045348+c.lower,115657699458599+c.upper)) = pointBounds69113 := by
 decide +kernel
def cuts69114 : List PrefixCut := [⟨64,178117061,178117166⟩]
theorem checked69114 : checkPrefixCuts (2^48) 9062842369 10 Manual.Count131072.C069114.packed 64 cuts69114 = true := by
 decide +kernel
def cuts69115 : List PrefixCut := [⟨62,172431019,172431120⟩,
⟨64,178487180,178487284⟩]
theorem checked69115 : checkPrefixCuts (2^48) 9062973441 10 Manual.Count131072.C069115.packed 64 cuts69115 = true := by
 decide +kernel
def pointBounds69115 : List (Nat × Nat × Nat) := [(9063100416,115657838371428,115658227784991)]
theorem point_links_checked69115 : (cuts69115.take 1).map (fun c => (9062973441-1+2*2^10*c.k,115657665940409+c.lower,115658055353871+c.upper)) = pointBounds69115 := by
 decide +kernel
def cuts69116 : List PrefixCut := [⟨64,172863281,172863380⟩]
theorem checked69116 : checkPrefixCuts (2^48) 9063104513 10 Manual.Count131072.C069116.packed 64 cuts69116 = true := by
 decide +kernel
def cuts69117 : List PrefixCut := [⟨64,179413699,179413801⟩]
theorem checked69117 : checkPrefixCuts (2^48) 9063235585 10 Manual.Count131072.C069117.packed 64 cuts69117 = true := by
 decide +kernel
def cuts69118 : List PrefixCut := [⟨9,23571728,23571744⟩,
⟨64,176647113,176647216⟩]
theorem checked69118 : checkPrefixCuts (2^48) 9063366657 10 Manual.Count131072.C069118.packed 64 cuts69118 = true := by
 decide +kernel
def pointBounds69118 : List (Nat × Nat × Nat) := [(9063385088,115658220276297,115658609690080)]
theorem point_links_checked69118 : (cuts69118.take 1).map (fun c => (9063366657-1+2*2^10*c.k,115658196704569+c.lower,115658586118336+c.upper)) = pointBounds69118 := by
 decide +kernel
def cuts69119 : List PrefixCut := [⟨64,175868163,175868263⟩]
theorem checked69119 : checkPrefixCuts (2^48) 9063497729 10 Manual.Count131072.C069119.packed 64 cuts69119 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000284
