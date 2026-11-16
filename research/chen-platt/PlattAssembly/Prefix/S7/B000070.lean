import PlattAssemblyKernel
import PlattCertificates.Count131072.C062240
import PlattCertificates.Count131072.C062241
import PlattCertificates.Count131072.C062242
import PlattCertificates.Count131072.C062243
import PlattCertificates.Count131072.C062244
import PlattCertificates.Count131072.C062245
import PlattCertificates.Count131072.C062246
import PlattCertificates.Count131072.C062247
import PlattCertificates.Count131072.C062248
import PlattCertificates.Count131072.C062249
import PlattCertificates.Count131072.C062250
import PlattCertificates.Count131072.C062251
import PlattCertificates.Count131072.C062252
import PlattCertificates.Count131072.C062253
import PlattCertificates.Count131072.C062254
import PlattCertificates.Count131072.C062255
import PlattCertificates.Count131072.C062256
import PlattCertificates.Count131072.C062257
import PlattCertificates.Count131072.C062258
import PlattCertificates.Count131072.C062259
import PlattCertificates.Count131072.C062260
import PlattCertificates.Count131072.C062261
import PlattCertificates.Count131072.C062262
import PlattCertificates.Count131072.C062263
import PlattCertificates.Count131072.C062264
import PlattCertificates.Count131072.C062265
import PlattCertificates.Count131072.C062266
import PlattCertificates.Count131072.C062267
import PlattCertificates.Count131072.C062268
import PlattCertificates.Count131072.C062269
import PlattCertificates.Count131072.C062270
import PlattCertificates.Count131072.C062271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62240 : List PrefixCut := [⟨10,31520748,31520766⟩,
⟨64,200193341,200193452⟩]
theorem checked62240 : checkPrefixCuts (2^48) 8161853441 10 Manual.Count131072.C062240.packed 64 cuts62240 = true := by
 decide +kernel
def pointBounds62240 : List (Nat × Nat × Nat) := [(8161873920,114369032272434,114369420938597)]
theorem point_links_checked62240 : (cuts62240.take 1).map (fun c => (8161853441-1+2*2^10*c.k,114369000751686+c.lower,114369389417831+c.upper)) = pointBounds62240 := by
 decide +kernel
def cuts62241 : List PrefixCut := [⟨64,198327883,198327996⟩]
theorem checked62241 : checkPrefixCuts (2^48) 8161984513 10 Manual.Count131072.C062241.packed 64 cuts62241 = true := by
 decide +kernel
def cuts62242 : List PrefixCut := [⟨7,21518953,21518965⟩,
⟨64,196290055,196290170⟩]
theorem checked62242 : checkPrefixCuts (2^48) 8162115585 10 Manual.Count131072.C062242.packed 64 cuts62242 = true := by
 decide +kernel
def pointBounds62242 : List (Nat × Nat × Nat) := [(8162129920,114369420791863,114369809458244)]
theorem point_links_checked62242 : (cuts62242.take 1).map (fun c => (8162115585-1+2*2^10*c.k,114369399272910+c.lower,114369787939279+c.upper)) = pointBounds62242 := by
 decide +kernel
def cuts62243 : List PrefixCut := [⟨64,196321406,196321517⟩]
theorem checked62243 : checkPrefixCuts (2^48) 8162246657 10 Manual.Count131072.C062243.packed 64 cuts62243 = true := by
 decide +kernel
def cuts62244 : List PrefixCut := [⟨4,12207480,12207487⟩,
⟨64,198766620,198766734⟩]
theorem checked62244 : checkPrefixCuts (2^48) 8162377729 10 Manual.Count131072.C062244.packed 64 cuts62244 = true := by
 decide +kernel
def pointBounds62244 : List (Nat × Nat × Nat) := [(8162385920,114369804091851,114370192758453)]
theorem point_links_checked62244 : (cuts62244.take 1).map (fun c => (8162377729-1+2*2^10*c.k,114369791884371+c.lower,114370180550966+c.upper)) = pointBounds62244 := by
 decide +kernel
def cuts62245 : List PrefixCut := [⟨64,198659985,198660101⟩]
theorem checked62245 : checkPrefixCuts (2^48) 8162508801 10 Manual.Count131072.C062245.packed 64 cuts62245 = true := by
 decide +kernel
def cuts62246 : List PrefixCut := [⟨1,3103498,3103500⟩,
⟨64,200001646,200001762⟩]
theorem checked62246 : checkPrefixCuts (2^48) 8162639873 10 Manual.Count131072.C062246.packed 64 cuts62246 = true := by
 decide +kernel
def pointBounds62246 : List (Nat × Nat × Nat) := [(8162641920,114370192414474,114370581081301)]
theorem point_links_checked62246 : (cuts62246.take 1).map (fun c => (8162639873-1+2*2^10*c.k,114370189310976+c.lower,114370577977801+c.upper)) = pointBounds62246 := by
 decide +kernel
def cuts62247 : List PrefixCut := [⟨62,191964048,191964157⟩,
⟨64,198205329,198205442⟩]
theorem checked62247 : checkPrefixCuts (2^48) 8162770945 10 Manual.Count131072.C062247.packed 64 cuts62247 = true := by
 decide +kernel
def pointBounds62247 : List (Nat × Nat × Nat) := [(8162897920,114370581276670,114370969943720)]
theorem point_links_checked62247 : (cuts62247.take 1).map (fun c => (8162770945-1+2*2^10*c.k,114370389312622+c.lower,114370777979563+c.upper)) = pointBounds62247 := by
 decide +kernel
def cuts62248 : List PrefixCut := [⟨64,197960770,197960879⟩]
theorem checked62248 : checkPrefixCuts (2^48) 8162902017 10 Manual.Count131072.C062248.packed 64 cuts62248 = true := by
 decide +kernel
def cuts62249 : List PrefixCut := [⟨59,183544498,183544606⟩,
⟨64,198026572,198026686⟩]
theorem checked62249 : checkPrefixCuts (2^48) 8163033089 10 Manual.Count131072.C062249.packed 64 cuts62249 = true := by
 decide +kernel
def pointBounds62249 : List (Nat × Nat × Nat) := [(8163153920,114370969023219,114371357690490)]
theorem point_links_checked62249 : (cuts62249.take 1).map (fun c => (8163033089-1+2*2^10*c.k,114370785478721+c.lower,114371174145884+c.upper)) = pointBounds62249 := by
 decide +kernel
def cuts62250 : List PrefixCut := [⟨64,198368198,198368315⟩]
theorem checked62250 : checkPrefixCuts (2^48) 8163164161 10 Manual.Count131072.C062250.packed 64 cuts62250 = true := by
 decide +kernel
def cuts62251 : List PrefixCut := [⟨56,170608553,170608655⟩,
⟨64,194296333,194296449⟩]
theorem checked62251 : checkPrefixCuts (2^48) 8163295233 10 Manual.Count131072.C062251.packed 64 cuts62251 = true := by
 decide +kernel
def pointBounds62251 : List (Nat × Nat × Nat) := [(8163409920,114371352482044,114371741149540)]
theorem point_links_checked62251 : (cuts62251.take 1).map (fun c => (8163295233-1+2*2^10*c.k,114371181873491+c.lower,114371570540885+c.upper)) = pointBounds62251 := by
 decide +kernel
def cuts62252 : List PrefixCut := [⟨64,202258026,202258145⟩]
theorem checked62252 : checkPrefixCuts (2^48) 8163426305 10 Manual.Count131072.C062252.packed 64 cuts62252 = true := by
 decide +kernel
def cuts62253 : List PrefixCut := [⟨53,163603854,163603951⟩,
⟨64,197289775,197289888⟩]
theorem checked62253 : checkPrefixCuts (2^48) 8163557377 10 Manual.Count131072.C062253.packed 64 cuts62253 = true := by
 decide +kernel
def pointBounds62253 : List (Nat × Nat × Nat) := [(8163665920,114371742031704,114372130699430)]
theorem point_links_checked62253 : (cuts62253.take 1).map (fun c => (8163557377-1+2*2^10*c.k,114371578427850+c.lower,114371967095479+c.upper)) = pointBounds62253 := by
 decide +kernel
def cuts62254 : List PrefixCut := [⟨64,197976195,197976311⟩]
theorem checked62254 : checkPrefixCuts (2^48) 8163688449 10 Manual.Count131072.C062254.packed 64 cuts62254 = true := by
 decide +kernel
def cuts62255 : List PrefixCut := [⟨50,155289448,155289535⟩,
⟨64,197938536,197938649⟩]
theorem checked62255 : checkPrefixCuts (2^48) 8163819521 10 Manual.Count131072.C062255.packed 64 cuts62255 = true := by
 decide +kernel
def pointBounds62255 : List (Nat × Nat × Nat) := [(8163921920,114372128983268,114372517651213)]
theorem point_links_checked62255 : (cuts62255.take 1).map (fun c => (8163819521-1+2*2^10*c.k,114371973693820+c.lower,114372362361678+c.upper)) = pointBounds62255 := by
 decide +kernel
def cuts62256 : List PrefixCut := [⟨64,201003852,201003970⟩]
theorem checked62256 : checkPrefixCuts (2^48) 8163950593 10 Manual.Count131072.C062256.packed 64 cuts62256 = true := by
 decide +kernel
def cuts62257 : List PrefixCut := [⟨47,146665256,146665338⟩,
⟨64,199311247,199311361⟩]
theorem checked62257 : checkPrefixCuts (2^48) 8164081665 10 Manual.Count131072.C062257.packed 64 cuts62257 = true := by
 decide +kernel
def pointBounds62257 : List (Nat × Nat × Nat) := [(8164177920,114372519301464,114372907969635)]
theorem point_links_checked62257 : (cuts62257.take 1).map (fun c => (8164081665-1+2*2^10*c.k,114372372636208+c.lower,114372761304297+c.upper)) = pointBounds62257 := by
 decide +kernel
def cuts62258 : List PrefixCut := [⟨64,195688021,195688137⟩]
theorem checked62258 : checkPrefixCuts (2^48) 8164212737 10 Manual.Count131072.C062258.packed 64 cuts62258 = true := by
 decide +kernel
def cuts62259 : List PrefixCut := [⟨44,131801476,131801555⟩,
⟨64,194926396,194926509⟩]
theorem checked62259 : checkPrefixCuts (2^48) 8164343809 10 Manual.Count131072.C062259.packed 64 cuts62259 = true := by
 decide +kernel
def pointBounds62259 : List (Nat × Nat × Nat) := [(8164433920,114372899436952,114373288105350)]
theorem point_links_checked62259 : (cuts62259.take 1).map (fun c => (8164343809-1+2*2^10*c.k,114372767635476+c.lower,114373156303795+c.upper)) = pointBounds62259 := by
 decide +kernel
def cuts62260 : List PrefixCut := [⟨64,198681098,198681212⟩]
theorem checked62260 : checkPrefixCuts (2^48) 8164474881 10 Manual.Count131072.C062260.packed 64 cuts62260 = true := by
 decide +kernel
def cuts62261 : List PrefixCut := [⟨41,128349810,128349883⟩,
⟨64,198677909,198678022⟩]
theorem checked62261 : checkPrefixCuts (2^48) 8164605953 10 Manual.Count131072.C062261.packed 64 cuts62261 = true := by
 decide +kernel
def pointBounds62261 : List (Nat × Nat × Nat) := [(8164689920,114373289592780,114373678261399)]
theorem point_links_checked62261 : (cuts62261.take 1).map (fun c => (8164605953-1+2*2^10*c.k,114373161242970+c.lower,114373549911516+c.upper)) = pointBounds62261 := by
 decide +kernel
def cuts62262 : List PrefixCut := [⟨64,197502596,197502711⟩]
theorem checked62262 : checkPrefixCuts (2^48) 8164737025 10 Manual.Count131072.C062262.packed 64 cuts62262 = true := by
 decide +kernel
def cuts62263 : List PrefixCut := [⟨38,117762296,117762371⟩,
⟨64,198430207,198430328⟩]
theorem checked62263 : checkPrefixCuts (2^48) 8164868097 10 Manual.Count131072.C062263.packed 64 cuts62263 = true := by
 decide +kernel
def pointBounds62263 : List (Nat × Nat × Nat) := [(8164945920,114373675185771,114374063854620)]
theorem point_links_checked62263 : (cuts62263.take 1).map (fun c => (8164868097-1+2*2^10*c.k,114373557423475+c.lower,114373946092249+c.upper)) = pointBounds62263 := by
 decide +kernel
def cuts62264 : List PrefixCut := [⟨64,198323597,198323710⟩]
theorem checked62264 : checkPrefixCuts (2^48) 8164999169 10 Manual.Count131072.C062264.packed 64 cuts62264 = true := by
 decide +kernel
def cuts62265 : List PrefixCut := [⟨35,107589131,107589191⟩,
⟨64,195769458,195769564⟩]
theorem checked62265 : checkPrefixCuts (2^48) 8165130241 10 Manual.Count131072.C062265.packed 64 cuts62265 = true := by
 decide +kernel
def pointBounds62265 : List (Nat × Nat × Nat) := [(8165201920,114374061766410,114374450435478)]
theorem point_links_checked62265 : (cuts62265.take 1).map (fun c => (8165130241-1+2*2^10*c.k,114373954177279+c.lower,114374342846287+c.upper)) = pointBounds62265 := by
 decide +kernel
def cuts62266 : List PrefixCut := [⟨64,199730580,199730703⟩]
theorem checked62266 : checkPrefixCuts (2^48) 8165261313 10 Manual.Count131072.C062266.packed 64 cuts62266 = true := by
 decide +kernel
def cuts62267 : List PrefixCut := [⟨32,98761002,98761058⟩,
⟨64,198314053,198314165⟩]
theorem checked62267 : checkPrefixCuts (2^48) 8165392385 10 Manual.Count131072.C062267.packed 64 cuts62267 = true := by
 decide +kernel
def pointBounds62267 : List (Nat × Nat × Nat) := [(8165457920,114374448438319,114374837107612)]
theorem point_links_checked62267 : (cuts62267.take 1).map (fun c => (8165392385-1+2*2^10*c.k,114374349677317+c.lower,114374738346554+c.upper)) = pointBounds62267 := by
 decide +kernel
def cuts62268 : List PrefixCut := [⟨64,199896536,199896653⟩]
theorem checked62268 : checkPrefixCuts (2^48) 8165523457 10 Manual.Count131072.C062268.packed 64 cuts62268 = true := by
 decide +kernel
def cuts62269 : List PrefixCut := [⟨29,90174722,90174776⟩,
⟨64,199376260,199376378⟩]
theorem checked62269 : checkPrefixCuts (2^48) 8165654529 10 Manual.Count131072.C062269.packed 64 cuts62269 = true := by
 decide +kernel
def pointBounds62269 : List (Nat × Nat × Nat) := [(8165713920,114374838062628,114375226732148)]
theorem point_links_checked62269 : (cuts62269.take 1).map (fun c => (8165654529-1+2*2^10*c.k,114374747887906+c.lower,114375136557372+c.upper)) = pointBounds62269 := by
 decide +kernel
def cuts62270 : List PrefixCut := [⟨64,196374202,196374313⟩]
theorem checked62270 : checkPrefixCuts (2^48) 8165785601 10 Manual.Count131072.C062270.packed 64 cuts62270 = true := by
 decide +kernel
def cuts62271 : List PrefixCut := [⟨26,80589376,80589426⟩,
⟨64,199094104,199094224⟩]
theorem checked62271 : checkPrefixCuts (2^48) 8165916673 10 Manual.Count131072.C062271.packed 64 cuts62271 = true := by
 decide +kernel
def pointBounds62271 : List (Nat × Nat × Nat) := [(8165969920,114375224227744,114375612897489)]
theorem point_links_checked62271 : (cuts62271.take 1).map (fun c => (8165916673-1+2*2^10*c.k,114375143638368+c.lower,114375532308063+c.upper)) = pointBounds62271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000070
