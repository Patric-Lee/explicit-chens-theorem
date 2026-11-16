import PlattAssemblyKernel
import PlattCertificates.Count131072.C065120
import PlattCertificates.Count131072.C065121
import PlattCertificates.Count131072.C065122
import PlattCertificates.Count131072.C065123
import PlattCertificates.Count131072.C065124
import PlattCertificates.Count131072.C065125
import PlattCertificates.Count131072.C065126
import PlattCertificates.Count131072.C065127
import PlattCertificates.Count131072.C065128
import PlattCertificates.Count131072.C065129
import PlattCertificates.Count131072.C065130
import PlattCertificates.Count131072.C065131
import PlattCertificates.Count131072.C065132
import PlattCertificates.Count131072.C065133
import PlattCertificates.Count131072.C065134
import PlattCertificates.Count131072.C065135
import PlattCertificates.Count131072.C065136
import PlattCertificates.Count131072.C065137
import PlattCertificates.Count131072.C065138
import PlattCertificates.Count131072.C065139
import PlattCertificates.Count131072.C065140
import PlattCertificates.Count131072.C065141
import PlattCertificates.Count131072.C065142
import PlattCertificates.Count131072.C065143
import PlattCertificates.Count131072.C065144
import PlattCertificates.Count131072.C065145
import PlattCertificates.Count131072.C065146
import PlattCertificates.Count131072.C065147
import PlattCertificates.Count131072.C065148
import PlattCertificates.Count131072.C065149
import PlattCertificates.Count131072.C065150
import PlattCertificates.Count131072.C065151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000160
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65120 : List PrefixCut := [⟨64,187256456,187256566⟩]
theorem checked65120 : checkPrefixCuts (2^48) 8539340801 10 Manual.Count131072.C065120.packed 64 cuts65120 = true := by
 decide +kernel
def cuts65121 : List PrefixCut := [⟨50,148326440,148326521⟩,
⟨64,188604997,188605102⟩]
theorem checked65121 : checkPrefixCuts (2^48) 8539471873 10 Manual.Count131072.C065121.packed 64 cuts65121 = true := by
 decide +kernel
def pointBounds65121 : List (Nat × Nat × Nat) := [(8539574272,114926434346611,114926823334031)]
theorem point_links_checked65121 : (cuts65121.take 1).map (fun c => (8539471873-1+2*2^10*c.k,114926286020171+c.lower,114926675007510+c.upper)) = pointBounds65121 := by
 decide +kernel
def cuts65122 : List PrefixCut := [⟨64,190612705,190612813⟩]
theorem checked65122 : checkPrefixCuts (2^48) 8539602945 10 Manual.Count131072.C065122.packed 64 cuts65122 = true := by
 decide +kernel
def cuts65123 : List PrefixCut := [⟨53,158078107,158078202⟩,
⟨64,191137143,191137255⟩]
theorem checked65123 : checkPrefixCuts (2^48) 8539734017 10 Manual.Count131072.C065123.packed 64 cuts65123 = true := by
 decide +kernel
def pointBounds65123 : List (Nat × Nat × Nat) := [(8539842560,114926823315980,114927212303627)]
theorem point_links_checked65123 : (cuts65123.take 1).map (fun c => (8539734017-1+2*2^10*c.k,114926665237873+c.lower,114927054225425+c.upper)) = pointBounds65123 := by
 decide +kernel
def cuts65124 : List PrefixCut := [⟨64,190903495,190903598⟩]
theorem checked65124 : checkPrefixCuts (2^48) 8539865089 10 Manual.Count131072.C065124.packed 64 cuts65124 = true := by
 decide +kernel
def cuts65125 : List PrefixCut := [⟨56,165027624,165027720⟩,
⟨64,188791157,188791267⟩]
theorem checked65125 : checkPrefixCuts (2^48) 8539996161 10 Manual.Count131072.C065125.packed 64 cuts65125 = true := by
 decide +kernel
def pointBounds65125 : List (Nat × Nat × Nat) := [(8540110848,114927212306135,114927601293998)]
theorem point_links_checked65125 : (cuts65125.take 1).map (fun c => (8539996161-1+2*2^10*c.k,114927047278511+c.lower,114927436266278+c.upper)) = pointBounds65125 := by
 decide +kernel
def cuts65126 : List PrefixCut := [⟨64,188722357,188722463⟩]
theorem checked65126 : checkPrefixCuts (2^48) 8540127233 10 Manual.Count131072.C065126.packed 64 cuts65126 = true := by
 decide +kernel
def cuts65127 : List PrefixCut := [⟨59,175536234,175536339⟩,
⟨64,190103717,190103830⟩]
theorem checked65127 : checkPrefixCuts (2^48) 8540258305 10 Manual.Count131072.C065127.packed 64 cuts65127 = true := by
 decide +kernel
def pointBounds65127 : List (Nat × Nat × Nat) := [(8540379136,114927600328259,114927989316347)]
theorem point_links_checked65127 : (cuts65127.take 1).map (fun c => (8540258305-1+2*2^10*c.k,114927424792025+c.lower,114927813780008+c.upper)) = pointBounds65127 := by
 decide +kernel
def cuts65128 : List PrefixCut := [⟨64,188057406,188057518⟩]
theorem checked65128 : checkPrefixCuts (2^48) 8540389377 10 Manual.Count131072.C065128.packed 64 cuts65128 = true := by
 decide +kernel
def cuts65129 : List PrefixCut := [⟨62,181001678,181001785⟩,
⟨64,186406640,186406750⟩]
theorem checked65129 : checkPrefixCuts (2^48) 8540520449 10 Manual.Count131072.C065129.packed 64 cuts65129 = true := by
 decide +kernel
def pointBounds65129 : List (Nat × Nat × Nat) := [(8540647424,114927983954826,114928372943141)]
theorem point_links_checked65129 : (cuts65129.take 1).map (fun c => (8540520449-1+2*2^10*c.k,114927802953148+c.lower,114928191941356+c.upper)) = pointBounds65129 := by
 decide +kernel
def cuts65130 : List PrefixCut := [⟨64,186799259,186799366⟩]
theorem checked65130 : checkPrefixCuts (2^48) 8540651521 10 Manual.Count131072.C065130.packed 64 cuts65130 = true := by
 decide +kernel
def cuts65131 : List PrefixCut := [⟨64,189861347,189861451⟩]
theorem checked65131 : checkPrefixCuts (2^48) 8540782593 10 Manual.Count131072.C065131.packed 64 cuts65131 = true := by
 decide +kernel
def cuts65132 : List PrefixCut := [⟨1,2636485,2636486⟩,
⟨64,186958317,186958425⟩]
theorem checked65132 : checkPrefixCuts (2^48) 8540913665 10 Manual.Count131072.C065132.packed 64 cuts65132 = true := by
 decide +kernel
def pointBounds65132 : List (Nat × Nat × Nat) := [(8540915712,114928368656879,114928757645409)]
theorem point_links_checked65132 : (cuts65132.take 1).map (fun c => (8540913665-1+2*2^10*c.k,114928366020394+c.lower,114928755008923+c.upper)) = pointBounds65132 := by
 decide +kernel
def cuts65133 : List PrefixCut := [⟨64,191206683,191206792⟩]
theorem checked65133 : checkPrefixCuts (2^48) 8541044737 10 Manual.Count131072.C065133.packed 64 cuts65133 = true := by
 decide +kernel
def cuts65134 : List PrefixCut := [⟨4,12226318,12226325⟩,
⟨64,190643500,190643611⟩]
theorem checked65134 : checkPrefixCuts (2^48) 8541175809 10 Manual.Count131072.C065134.packed 64 cuts65134 = true := by
 decide +kernel
def pointBounds65134 : List (Nat × Nat × Nat) := [(8541184000,114928756411712,114929145400465)]
theorem point_links_checked65134 : (cuts65134.take 1).map (fun c => (8541175809-1+2*2^10*c.k,114928744185394+c.lower,114929133174140+c.upper)) = pointBounds65134 := by
 decide +kernel
def cuts65135 : List PrefixCut := [⟨64,189619006,189619114⟩]
theorem checked65135 : checkPrefixCuts (2^48) 8541306881 10 Manual.Count131072.C065135.packed 64 cuts65135 = true := by
 decide +kernel
def cuts65136 : List PrefixCut := [⟨7,20826936,20826948⟩,
⟨64,190275170,190275277⟩]
theorem checked65136 : checkPrefixCuts (2^48) 8541437953 10 Manual.Count131072.C065136.packed 64 cuts65136 = true := by
 decide +kernel
def pointBounds65136 : List (Nat × Nat × Nat) := [(8541452288,114929145274836,114929534263813)]
theorem point_links_checked65136 : (cuts65136.take 1).map (fun c => (8541437953-1+2*2^10*c.k,114929124447900+c.lower,114929513436865+c.upper)) = pointBounds65136 := by
 decide +kernel
def cuts65137 : List PrefixCut := [⟨64,187701897,187702007⟩]
theorem checked65137 : checkPrefixCuts (2^48) 8541569025 10 Manual.Count131072.C065137.packed 64 cuts65137 = true := by
 decide +kernel
def cuts65138 : List PrefixCut := [⟨10,29196347,29196366⟩,
⟨64,190005705,190005817⟩]
theorem checked65138 : checkPrefixCuts (2^48) 8541700097 10 Manual.Count131072.C065138.packed 64 cuts65138 = true := by
 decide +kernel
def pointBounds65138 : List (Nat × Nat × Nat) := [(8541720576,114929531621314,114929920610515)]
theorem point_links_checked65138 : (cuts65138.take 1).map (fun c => (8541700097-1+2*2^10*c.k,114929502424967+c.lower,114929891414149+c.upper)) = pointBounds65138 := by
 decide +kernel
def cuts65139 : List PrefixCut := [⟨64,186905272,186905379⟩]
theorem checked65139 : checkPrefixCuts (2^48) 8541831169 10 Manual.Count131072.C065139.packed 64 cuts65139 = true := by
 decide +kernel
def cuts65140 : List PrefixCut := [⟨13,38356089,38356110⟩,
⟨64,188418191,188418303⟩]
theorem checked65140 : checkPrefixCuts (2^48) 8541962241 10 Manual.Count131072.C065140.packed 64 cuts65140 = true := by
 decide +kernel
def pointBounds65140 : List (Nat × Nat × Nat) := [(8541988864,114929917692033,114930306681455)]
theorem point_links_checked65140 : (cuts65140.take 1).map (fun c => (8541962241-1+2*2^10*c.k,114929879335944+c.lower,114930268325345+c.upper)) = pointBounds65140 := by
 decide +kernel
def cuts65141 : List PrefixCut := [⟨64,186602986,186603094⟩]
theorem checked65141 : checkPrefixCuts (2^48) 8542093313 10 Manual.Count131072.C065141.packed 64 cuts65141 = true := by
 decide +kernel
def cuts65142 : List PrefixCut := [⟨16,47086899,47086927⟩,
⟨64,189203227,189203340⟩]
theorem checked65142 : checkPrefixCuts (2^48) 8542224385 10 Manual.Count131072.C065142.packed 64 cuts65142 = true := by
 decide +kernel
def pointBounds65142 : List (Nat × Nat × Nat) := [(8542257152,114930301444020,114930690433669)]
theorem point_links_checked65142 : (cuts65142.take 1).map (fun c => (8542224385-1+2*2^10*c.k,114930254357121+c.lower,114930643346742+c.upper)) = pointBounds65142 := by
 decide +kernel
def cuts65143 : List PrefixCut := [⟨64,189562780,189562889⟩]
theorem checked65143 : checkPrefixCuts (2^48) 8542355457 10 Manual.Count131072.C065143.packed 64 cuts65143 = true := by
 decide +kernel
def cuts65144 : List PrefixCut := [⟨19,56970415,56970447⟩,
⟨64,191306207,191306315⟩]
theorem checked65144 : checkPrefixCuts (2^48) 8542486529 10 Manual.Count131072.C065144.packed 64 cuts65144 = true := by
 decide +kernel
def pointBounds65144 : List (Nat × Nat × Nat) := [(8542525440,114930690093543,114931079083418)]
theorem point_links_checked65144 : (cuts65144.take 1).map (fun c => (8542486529-1+2*2^10*c.k,114930633123128+c.lower,114931022112971+c.upper)) = pointBounds65144 := by
 decide +kernel
def cuts65145 : List PrefixCut := [⟨64,189293365,189293482⟩]
theorem checked65145 : checkPrefixCuts (2^48) 8542617601 10 Manual.Count131072.C065145.packed 64 cuts65145 = true := by
 decide +kernel
def cuts65146 : List PrefixCut := [⟨22,63690220,63690255⟩,
⟨64,186951092,186951201⟩]
theorem checked65146 : checkPrefixCuts (2^48) 8542748673 10 Manual.Count131072.C065146.packed 64 cuts65146 = true := by
 decide +kernel
def pointBounds65146 : List (Nat × Nat × Nat) := [(8542793728,114931077412920,114931466403023)]
theorem point_links_checked65146 : (cuts65146.take 1).map (fun c => (8542748673-1+2*2^10*c.k,114931013722700+c.lower,114931402712768+c.upper)) = pointBounds65146 := by
 decide +kernel
def cuts65147 : List PrefixCut := [⟨64,188397946,188398058⟩]
theorem checked65147 : checkPrefixCuts (2^48) 8542879745 10 Manual.Count131072.C065147.packed 64 cuts65147 = true := by
 decide +kernel
def cuts65148 : List PrefixCut := [⟨25,73935031,73935071⟩,
⟨64,188230336,188230437⟩]
theorem checked65148 : checkPrefixCuts (2^48) 8543010817 10 Manual.Count131072.C065148.packed 64 cuts65148 = true := by
 decide +kernel
def pointBounds65148 : List (Nat × Nat × Nat) := [(8543062016,114931463006769,114931851997098)]
theorem point_links_checked65148 : (cuts65148.take 1).map (fun c => (8543010817-1+2*2^10*c.k,114931389071738+c.lower,114931778062027+c.upper)) = pointBounds65148 := by
 decide +kernel
def cuts65149 : List PrefixCut := [⟨64,189907758,189907864⟩]
theorem checked65149 : checkPrefixCuts (2^48) 8543141889 10 Manual.Count131072.C065149.packed 64 cuts65149 = true := by
 decide +kernel
def cuts65150 : List PrefixCut := [⟨28,83388484,83388532⟩,
⟨64,189674215,189674328⟩]
theorem checked65150 : checkPrefixCuts (2^48) 8543272961 10 Manual.Count131072.C065150.packed 64 cuts65150 = true := by
 decide +kernel
def pointBounds65150 : List (Nat × Nat × Nat) := [(8543330304,114931850598316,114932239588860)]
theorem point_links_checked65150 : (cuts65150.take 1).map (fun c => (8543272961-1+2*2^10*c.k,114931767209832+c.lower,114932156200328+c.upper)) = pointBounds65150 := by
 decide +kernel
def cuts65151 : List PrefixCut := [⟨64,189341841,189341946⟩]
theorem checked65151 : checkPrefixCuts (2^48) 8543404033 10 Manual.Count131072.C065151.packed 64 cuts65151 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000160
