import PlattAssemblyKernel
import PlattCertificates.Count131072.C062112
import PlattCertificates.Count131072.C062113
import PlattCertificates.Count131072.C062114
import PlattCertificates.Count131072.C062115
import PlattCertificates.Count131072.C062116
import PlattCertificates.Count131072.C062117
import PlattCertificates.Count131072.C062118
import PlattCertificates.Count131072.C062119
import PlattCertificates.Count131072.C062120
import PlattCertificates.Count131072.C062121
import PlattCertificates.Count131072.C062122
import PlattCertificates.Count131072.C062123
import PlattCertificates.Count131072.C062124
import PlattCertificates.Count131072.C062125
import PlattCertificates.Count131072.C062126
import PlattCertificates.Count131072.C062127
import PlattCertificates.Count131072.C062128
import PlattCertificates.Count131072.C062129
import PlattCertificates.Count131072.C062130
import PlattCertificates.Count131072.C062131
import PlattCertificates.Count131072.C062132
import PlattCertificates.Count131072.C062133
import PlattCertificates.Count131072.C062134
import PlattCertificates.Count131072.C062135
import PlattCertificates.Count131072.C062136
import PlattCertificates.Count131072.C062137
import PlattCertificates.Count131072.C062138
import PlattCertificates.Count131072.C062139
import PlattCertificates.Count131072.C062140
import PlattCertificates.Count131072.C062141
import PlattCertificates.Count131072.C062142
import PlattCertificates.Count131072.C062143
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62112 : List PrefixCut := [⟨64,196113226,196113342⟩]
theorem checked62112 : checkPrefixCuts (2^48) 8145076225 10 Manual.Count131072.C062112.packed 64 cuts62112 = true := by
 decide +kernel
def cuts62113 : List PrefixCut := [⟨13,40224421,40224444⟩,
⟨64,195107923,195108033⟩]
theorem checked62113 : checkPrefixCuts (2^48) 8145207297 10 Manual.Count131072.C062113.packed 64 cuts62113 = true := by
 decide +kernel
def pointBounds62113 : List (Nat × Nat × Nat) := [(8145233920,114343879382613,114344268034340)]
theorem point_links_checked62113 : (cuts62113.take 1).map (fun c => (8145207297-1+2*2^10*c.k,114343839158192+c.lower,114344227809896+c.upper)) = pointBounds62113 := by
 decide +kernel
def cuts62114 : List PrefixCut := [⟨64,197281826,197281944⟩]
theorem checked62114 : checkPrefixCuts (2^48) 8145338369 10 Manual.Count131072.C062114.packed 64 cuts62114 = true := by
 decide +kernel
def cuts62115 : List PrefixCut := [⟨10,31791485,31791503⟩,
⟨64,197209569,197209680⟩]
theorem checked62115 : checkPrefixCuts (2^48) 8145469441 10 Manual.Count131072.C062115.packed 64 cuts62115 = true := by
 decide +kernel
def pointBounds62115 : List (Nat × Nat × Nat) := [(8145489920,114344263339426,114344651991376)]
theorem point_links_checked62115 : (cuts62115.take 1).map (fun c => (8145469441-1+2*2^10*c.k,114344231547941+c.lower,114344620199873+c.upper)) = pointBounds62115 := by
 decide +kernel
def cuts62116 : List PrefixCut := [⟨64,197655577,197655693⟩]
theorem checked62116 : checkPrefixCuts (2^48) 8145600513 10 Manual.Count131072.C062116.packed 64 cuts62116 = true := by
 decide +kernel
def cuts62117 : List PrefixCut := [⟨7,22115114,22115125⟩,
⟨64,198205265,198205374⟩]
theorem checked62117 : checkPrefixCuts (2^48) 8145731585 10 Manual.Count131072.C062117.packed 64 cuts62117 = true := by
 decide +kernel
def pointBounds62117 : List (Nat × Nat × Nat) := [(8145745920,114344648528201,114345037180371)]
theorem point_links_checked62117 : (cuts62117.take 1).map (fun c => (8145731585-1+2*2^10*c.k,114344626413087+c.lower,114345015065246+c.upper)) = pointBounds62117 := by
 decide +kernel
def cuts62118 : List PrefixCut := [⟨64,196439837,196439946⟩]
theorem checked62118 : checkPrefixCuts (2^48) 8145862657 10 Manual.Count131072.C062118.packed 64 cuts62118 = true := by
 decide +kernel
def cuts62119 : List PrefixCut := [⟨4,12093818,12093825⟩,
⟨64,199615602,199615716⟩]
theorem checked62119 : checkPrefixCuts (2^48) 8145993729 10 Manual.Count131072.C062119.packed 64 cuts62119 = true := by
 decide +kernel
def pointBounds62119 : List (Nat × Nat × Nat) := [(8146001920,114345033152007,114345421804391)]
theorem point_links_checked62119 : (cuts62119.take 1).map (fun c => (8145993729-1+2*2^10*c.k,114345021058189+c.lower,114345409710566+c.upper)) = pointBounds62119 := by
 decide +kernel
def cuts62120 : List PrefixCut := [⟨64,199197737,199197848⟩]
theorem checked62120 : checkPrefixCuts (2^48) 8146124801 10 Manual.Count131072.C062120.packed 64 cuts62120 = true := by
 decide +kernel
def cuts62121 : List PrefixCut := [⟨1,3075187,3075189⟩,
⟨64,199851036,199851155⟩]
theorem checked62121 : checkPrefixCuts (2^48) 8146255873 10 Manual.Count131072.C062121.packed 64 cuts62121 = true := by
 decide +kernel
def pointBounds62121 : List (Nat × Nat × Nat) := [(8146257920,114345422946715,114345811599319)]
theorem point_links_checked62121 : (cuts62121.take 1).map (fun c => (8146255873-1+2*2^10*c.k,114345419871528+c.lower,114345808524130+c.upper)) = pointBounds62121 := by
 decide +kernel
def cuts62122 : List PrefixCut := [⟨62,189344108,189344223⟩,
⟨64,195908906,195909024⟩]
theorem checked62122 : checkPrefixCuts (2^48) 8146386945 10 Manual.Count131072.C062122.packed 64 cuts62122 = true := by
 decide +kernel
def pointBounds62122 : List (Nat × Nat × Nat) := [(8146513920,114345809066672,114346197719508)]
theorem point_links_checked62122 : (cuts62122.take 1).map (fun c => (8146386945-1+2*2^10*c.k,114345619722564+c.lower,114346008375285+c.upper)) = pointBounds62122 := by
 decide +kernel
def cuts62123 : List PrefixCut := [⟨64,195698466,195698579⟩]
theorem checked62123 : checkPrefixCuts (2^48) 8146518017 10 Manual.Count131072.C062123.packed 64 cuts62123 = true := by
 decide +kernel
def cuts62124 : List PrefixCut := [⟨59,183153511,183153618⟩,
⟨64,198286617,198286732⟩]
theorem checked62124 : checkPrefixCuts (2^48) 8146649089 10 Manual.Count131072.C062124.packed 64 cuts62124 = true := by
 decide +kernel
def pointBounds62124 : List (Nat × Nat × Nat) := [(8146769920,114346194483447,114346583136506)]
theorem point_links_checked62124 : (cuts62124.take 1).map (fun c => (8146649089-1+2*2^10*c.k,114346011329936+c.lower,114346399982888+c.upper)) = pointBounds62124 := by
 decide +kernel
def cuts62125 : List PrefixCut := [⟨64,201496589,201496703⟩]
theorem checked62125 : checkPrefixCuts (2^48) 8146780161 10 Manual.Count131072.C062125.packed 64 cuts62125 = true := by
 decide +kernel
def cuts62126 : List PrefixCut := [⟨56,174233876,174233976⟩,
⟨64,198418435,198418550⟩]
theorem checked62126 : checkPrefixCuts (2^48) 8146911233 10 Manual.Count131072.C062126.packed 64 cuts62126 = true := by
 decide +kernel
def pointBounds62126 : List (Nat × Nat × Nat) := [(8147025920,114346585347018,114346974000299)]
theorem point_links_checked62126 : (cuts62126.take 1).map (fun c => (8146911233-1+2*2^10*c.k,114346411113142+c.lower,114346799766323+c.upper)) = pointBounds62126 := by
 decide +kernel
def cuts62127 : List PrefixCut := [⟨64,196100441,196100554⟩]
theorem checked62127 : checkPrefixCuts (2^48) 8147042305 10 Manual.Count131072.C062127.packed 64 cuts62127 = true := by
 decide +kernel
def cuts62128 : List PrefixCut := [⟨53,164381993,164382088⟩,
⟨64,197721074,197721190⟩]
theorem checked62128 : checkPrefixCuts (2^48) 8147173377 10 Manual.Count131072.C062128.packed 64 cuts62128 = true := by
 decide +kernel
def pointBounds62128 : List (Nat × Nat × Nat) := [(8147281920,114346970014011,114347358667515)]
theorem point_links_checked62128 : (cuts62128.take 1).map (fun c => (8147173377-1+2*2^10*c.k,114346805632018+c.lower,114347194285427+c.upper)) = pointBounds62128 := by
 decide +kernel
def cuts62129 : List PrefixCut := [⟨64,199410752,199410871⟩]
theorem checked62129 : checkPrefixCuts (2^48) 8147304449 10 Manual.Count131072.C062129.packed 64 cuts62129 = true := by
 decide +kernel
def cuts62130 : List PrefixCut := [⟨50,155083508,155083592⟩,
⟨64,196229192,196229299⟩]
theorem checked62130 : checkPrefixCuts (2^48) 8147435521 10 Manual.Count131072.C062130.packed 64 cuts62130 = true := by
 decide +kernel
def pointBounds62130 : List (Nat × Nat × Nat) := [(8147537920,114347357847352,114347746501080)]
theorem point_links_checked62130 : (cuts62130.take 1).map (fun c => (8147435521-1+2*2^10*c.k,114347202763844+c.lower,114347591417488+c.upper)) = pointBounds62130 := by
 decide +kernel
def cuts62131 : List PrefixCut := [⟨64,198160630,198160745⟩]
theorem checked62131 : checkPrefixCuts (2^48) 8147566593 10 Manual.Count131072.C062131.packed 64 cuts62131 = true := by
 decide +kernel
def cuts62132 : List PrefixCut := [⟨47,145716506,145716594⟩,
⟨64,198364719,198364840⟩]
theorem checked62132 : checkPrefixCuts (2^48) 8147697665 10 Manual.Count131072.C062132.packed 64 cuts62132 = true := by
 decide +kernel
def pointBounds62132 : List (Nat × Nat × Nat) := [(8147793920,114347742870172,114348131524126)]
theorem point_links_checked62132 : (cuts62132.take 1).map (fun c => (8147697665-1+2*2^10*c.k,114347597153666+c.lower,114347985807532+c.upper)) = pointBounds62132 := by
 decide +kernel
def cuts62133 : List PrefixCut := [⟨64,200157922,200158035⟩]
theorem checked62133 : checkPrefixCuts (2^48) 8147828737 10 Manual.Count131072.C062133.packed 64 cuts62133 = true := by
 decide +kernel
def cuts62134 : List PrefixCut := [⟨44,137006475,137006550⟩,
⟨64,198254716,198254827⟩]
theorem checked62134 : checkPrefixCuts (2^48) 8147959809 10 Manual.Count131072.C062134.packed 64 cuts62134 = true := by
 decide +kernel
def pointBounds62134 : List (Nat × Nat × Nat) := [(8148049920,114348132682782,114348521336957)]
theorem point_links_checked62134 : (cuts62134.take 1).map (fun c => (8147959809-1+2*2^10*c.k,114347995676307+c.lower,114348384330407+c.upper)) = pointBounds62134 := by
 decide +kernel
def cuts62135 : List PrefixCut := [⟨64,198493333,198493451⟩]
theorem checked62135 : checkPrefixCuts (2^48) 8148090881 10 Manual.Count131072.C062135.packed 64 cuts62135 = true := by
 decide +kernel
def cuts62136 : List PrefixCut := [⟨41,126604329,126604399⟩,
⟨64,196901119,196901231⟩]
theorem checked62136 : checkPrefixCuts (2^48) 8148221953 10 Manual.Count131072.C062136.packed 64 cuts62136 = true := by
 decide +kernel
def pointBounds62136 : List (Nat × Nat × Nat) := [(8148305920,114348519028685,114348907683084)]
theorem point_links_checked62136 : (cuts62136.take 1).map (fun c => (8148221953-1+2*2^10*c.k,114348392424356+c.lower,114348781078685+c.upper)) = pointBounds62136 := by
 decide +kernel
def cuts62137 : List PrefixCut := [⟨64,201526781,201526897⟩]
theorem checked62137 : checkPrefixCuts (2^48) 8148353025 10 Manual.Count131072.C062137.packed 64 cuts62137 = true := by
 decide +kernel
def cuts62138 : List PrefixCut := [⟨38,117929998,117930063⟩,
⟨64,198103790,198103900⟩]
theorem checked62138 : checkPrefixCuts (2^48) 8148484097 10 Manual.Count131072.C062138.packed 64 cuts62138 = true := by
 decide +kernel
def pointBounds62138 : List (Nat × Nat × Nat) := [(8148561920,114348908782254,114349297436876)]
theorem point_links_checked62138 : (cuts62138.take 1).map (fun c => (8148484097-1+2*2^10*c.k,114348790852256+c.lower,114349179506813+c.upper)) = pointBounds62138 := by
 decide +kernel
def cuts62139 : List PrefixCut := [⟨64,197582478,197582592⟩]
theorem checked62139 : checkPrefixCuts (2^48) 8148615169 10 Manual.Count131072.C062139.packed 64 cuts62139 = true := by
 decide +kernel
def cuts62140 : List PrefixCut := [⟨35,107839993,107840056⟩,
⟨64,197095693,197095809⟩]
theorem checked62140 : checkPrefixCuts (2^48) 8148746241 10 Manual.Count131072.C062140.packed 64 cuts62140 = true := by
 decide +kernel
def pointBounds62140 : List (Nat × Nat × Nat) := [(8148817920,114349294378517,114349683033361)]
theorem point_links_checked62140 : (cuts62140.take 1).map (fun c => (8148746241-1+2*2^10*c.k,114349186538524+c.lower,114349575193305+c.upper)) = pointBounds62140 := by
 decide +kernel
def cuts62141 : List PrefixCut := [⟨64,200892066,200892178⟩]
theorem checked62141 : checkPrefixCuts (2^48) 8148877313 10 Manual.Count131072.C062141.packed 64 cuts62141 = true := by
 decide +kernel
def cuts62142 : List PrefixCut := [⟨32,100030332,100030387⟩,
⟨64,201683268,201683380⟩]
theorem checked62142 : checkPrefixCuts (2^48) 8149008385 10 Manual.Count131072.C062142.packed 64 cuts62142 = true := by
 decide +kernel
def pointBounds62142 : List (Nat × Nat × Nat) := [(8149073920,114349684556615,114350073211679)]
theorem point_links_checked62142 : (cuts62142.take 1).map (fun c => (8149008385-1+2*2^10*c.k,114349584526283+c.lower,114349973181292+c.upper)) = pointBounds62142 := by
 decide +kernel
def cuts62143 : List PrefixCut := [⟨64,196637167,196637276⟩]
theorem checked62143 : checkPrefixCuts (2^48) 8149139457 10 Manual.Count131072.C062143.packed 64 cuts62143 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000066
