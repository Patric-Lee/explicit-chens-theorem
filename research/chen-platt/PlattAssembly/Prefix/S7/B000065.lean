import PlattAssemblyKernel
import PlattCertificates.Count131072.C062080
import PlattCertificates.Count131072.C062081
import PlattCertificates.Count131072.C062082
import PlattCertificates.Count131072.C062083
import PlattCertificates.Count131072.C062084
import PlattCertificates.Count131072.C062085
import PlattCertificates.Count131072.C062086
import PlattCertificates.Count131072.C062087
import PlattCertificates.Count131072.C062088
import PlattCertificates.Count131072.C062089
import PlattCertificates.Count131072.C062090
import PlattCertificates.Count131072.C062091
import PlattCertificates.Count131072.C062092
import PlattCertificates.Count131072.C062093
import PlattCertificates.Count131072.C062094
import PlattCertificates.Count131072.C062095
import PlattCertificates.Count131072.C062096
import PlattCertificates.Count131072.C062097
import PlattCertificates.Count131072.C062098
import PlattCertificates.Count131072.C062099
import PlattCertificates.Count131072.C062100
import PlattCertificates.Count131072.C062101
import PlattCertificates.Count131072.C062102
import PlattCertificates.Count131072.C062103
import PlattCertificates.Count131072.C062104
import PlattCertificates.Count131072.C062105
import PlattCertificates.Count131072.C062106
import PlattCertificates.Count131072.C062107
import PlattCertificates.Count131072.C062108
import PlattCertificates.Count131072.C062109
import PlattCertificates.Count131072.C062110
import PlattCertificates.Count131072.C062111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62080 : List PrefixCut := [⟨64,198945692,198945805⟩]
theorem checked62080 : checkPrefixCuts (2^48) 8140881921 10 Manual.Count131072.C062080.packed 64 cuts62080 = true := by
 decide +kernel
def cuts62081 : List PrefixCut := [⟨61,191647327,191647435⟩,
⟨64,200774963,200775076⟩]
theorem checked62081 : checkPrefixCuts (2^48) 8141012993 10 Manual.Count131072.C062081.packed 64 cuts62081 = true := by
 decide +kernel
def pointBounds62081 : List (Nat × Nat × Nat) := [(8141137920,114337665471030,114338054119201)]
theorem point_links_checked62081 : (cuts62081.take 1).map (fun c => (8141012993-1+2*2^10*c.k,114337473823703+c.lower,114337862471766+c.upper)) = pointBounds62081 := by
 decide +kernel
def cuts62082 : List PrefixCut := [⟨64,196622829,196622945⟩]
theorem checked62082 : checkPrefixCuts (2^48) 8141144065 10 Manual.Count131072.C062082.packed 64 cuts62082 = true := by
 decide +kernel
def cuts62083 : List PrefixCut := [⟨58,181165442,181165547⟩,
⟨64,199489280,199489395⟩]
theorem checked62083 : checkPrefixCuts (2^48) 8141275137 10 Manual.Count131072.C062083.packed 64 cuts62083 = true := by
 decide +kernel
def pointBounds62083 : List (Nat × Nat × Nat) := [(8141393920,114338052386937,114338441035334)]
theorem point_links_checked62083 : (cuts62083.take 1).map (fun c => (8141275137-1+2*2^10*c.k,114337871221495+c.lower,114338259869787+c.upper)) = pointBounds62083 := by
 decide +kernel
def cuts62084 : List PrefixCut := [⟨64,198379739,198379853⟩]
theorem checked62084 : checkPrefixCuts (2^48) 8141406209 10 Manual.Count131072.C062084.packed 64 cuts62084 = true := by
 decide +kernel
def cuts62085 : List PrefixCut := [⟨55,170787940,170788036⟩,
⟨64,199413704,199413816⟩]
theorem checked62085 : checkPrefixCuts (2^48) 8141537281 10 Manual.Count131072.C062085.packed 64 cuts62085 = true := by
 decide +kernel
def pointBounds62085 : List (Nat × Nat × Nat) := [(8141649920,114338439878454,114338828527071)]
theorem point_links_checked62085 : (cuts62085.take 1).map (fun c => (8141537281-1+2*2^10*c.k,114338269090514+c.lower,114338657739035+c.upper)) = pointBounds62085 := by
 decide +kernel
def cuts62086 : List PrefixCut := [⟨64,200413085,200413201⟩]
theorem checked62086 : checkPrefixCuts (2^48) 8141668353 10 Manual.Count131072.C062086.packed 64 cuts62086 = true := by
 decide +kernel
def cuts62087 : List PrefixCut := [⟨52,161413665,161413755⟩,
⟨64,198646717,198646828⟩]
theorem checked62087 : checkPrefixCuts (2^48) 8141799425 10 Manual.Count131072.C062087.packed 64 cuts62087 = true := by
 decide +kernel
def pointBounds62087 : List (Nat × Nat × Nat) := [(8141905920,114338830330968,114339218979807)]
theorem point_links_checked62087 : (cuts62087.take 1).map (fun c => (8141799425-1+2*2^10*c.k,114338668917303+c.lower,114339057566052+c.upper)) = pointBounds62087 := by
 decide +kernel
def cuts62088 : List PrefixCut := [⟨64,200648616,200648730⟩]
theorem checked62088 : checkPrefixCuts (2^48) 8141930497 10 Manual.Count131072.C062088.packed 64 cuts62088 = true := by
 decide +kernel
def cuts62089 : List PrefixCut := [⟨49,148029838,148029926⟩,
⟨64,194077050,194077165⟩]
theorem checked62089 : checkPrefixCuts (2^48) 8142061569 10 Manual.Count131072.C062089.packed 64 cuts62089 = true := by
 decide +kernel
def pointBounds62089 : List (Nat × Nat × Nat) := [(8142161920,114339216242474,114339604891536)]
theorem point_links_checked62089 : (cuts62089.take 1).map (fun c => (8142061569-1+2*2^10*c.k,114339068212636+c.lower,114339456861610+c.upper)) = pointBounds62089 := by
 decide +kernel
def cuts62090 : List PrefixCut := [⟨64,203062042,203062163⟩]
theorem checked62090 : checkPrefixCuts (2^48) 8142192641 10 Manual.Count131072.C062090.packed 64 cuts62090 = true := by
 decide +kernel
def cuts62091 : List PrefixCut := [⟨46,143980546,143980628⟩,
⟨64,200777216,200777329⟩]
theorem checked62091 : checkPrefixCuts (2^48) 8142323713 10 Manual.Count131072.C062091.packed 64 cuts62091 = true := by
 decide +kernel
def pointBounds62091 : List (Nat × Nat × Nat) := [(8142417920,114339609332274,114339997981566)]
theorem point_links_checked62091 : (cuts62091.take 1).map (fun c => (8142323713-1+2*2^10*c.k,114339465351728+c.lower,114339854000938+c.upper)) = pointBounds62091 := by
 decide +kernel
def cuts62092 : List PrefixCut := [⟨64,199252981,199253094⟩]
theorem checked62092 : checkPrefixCuts (2^48) 8142454785 10 Manual.Count131072.C062092.packed 64 cuts62092 = true := by
 decide +kernel
def cuts62093 : List PrefixCut := [⟨43,135126538,135126616⟩,
⟨64,201565812,201565926⟩]
theorem checked62093 : checkPrefixCuts (2^48) 8142585857 10 Manual.Count131072.C062093.packed 64 cuts62093 = true := by
 decide +kernel
def pointBounds62093 : List (Nat × Nat × Nat) := [(8142673920,114340000508463,114340389157977)]
theorem point_links_checked62093 : (cuts62093.take 1).map (fun c => (8142585857-1+2*2^10*c.k,114339865381925+c.lower,114340254031361+c.upper)) = pointBounds62093 := by
 decide +kernel
def cuts62094 : List PrefixCut := [⟨64,198347796,198347908⟩]
theorem checked62094 : checkPrefixCuts (2^48) 8142716929 10 Manual.Count131072.C062094.packed 64 cuts62094 = true := by
 decide +kernel
def cuts62095 : List PrefixCut := [⟨40,124199087,124199157⟩,
⟨64,198966811,198966926⟩]
theorem checked62095 : checkPrefixCuts (2^48) 8142848001 10 Manual.Count131072.C062095.packed 64 cuts62095 = true := by
 decide +kernel
def pointBounds62095 : List (Nat × Nat × Nat) := [(8142929920,114340389494620,114340778144352)]
theorem point_links_checked62095 : (cuts62095.take 1).map (fun c => (8142848001-1+2*2^10*c.k,114340265295533+c.lower,114340653945195+c.upper)) = pointBounds62095 := by
 decide +kernel
def cuts62096 : List PrefixCut := [⟨64,201728898,201729013⟩]
theorem checked62096 : checkPrefixCuts (2^48) 8142979073 10 Manual.Count131072.C062096.packed 64 cuts62096 = true := by
 decide +kernel
def cuts62097 : List PrefixCut := [⟨37,114482117,114482186⟩,
⟨64,197301247,197301362⟩]
theorem checked62097 : checkPrefixCuts (2^48) 8143110145 10 Manual.Count131072.C062097.packed 64 cuts62097 = true := by
 decide +kernel
def pointBounds62097 : List (Nat × Nat × Nat) := [(8143185920,114340780473359,114341169123320)]
theorem point_links_checked62097 : (cuts62097.take 1).map (fun c => (8143110145-1+2*2^10*c.k,114340665991242+c.lower,114341054641134+c.upper)) = pointBounds62097 := by
 decide +kernel
def cuts62098 : List PrefixCut := [⟨64,199095475,199095590⟩]
theorem checked62098 : checkPrefixCuts (2^48) 8143241217 10 Manual.Count131072.C062098.packed 64 cuts62098 = true := by
 decide +kernel
def cuts62099 : List PrefixCut := [⟨34,105387949,105388010⟩,
⟨64,199368772,199368889⟩]
theorem checked62099 : checkPrefixCuts (2^48) 8143372289 10 Manual.Count131072.C062099.packed 64 cuts62099 = true := by
 decide +kernel
def pointBounds62099 : List (Nat × Nat × Nat) := [(8143441920,114341167775913,114341556426096)]
theorem point_links_checked62099 : (cuts62099.take 1).map (fun c => (8143372289-1+2*2^10*c.k,114341062387964+c.lower,114341451038086+c.upper)) = pointBounds62099 := by
 decide +kernel
def cuts62100 : List PrefixCut := [⟨64,199780345,199780457⟩]
theorem checked62100 : checkPrefixCuts (2^48) 8143503361 10 Manual.Count131072.C062100.packed 64 cuts62100 = true := by
 decide +kernel
def cuts62101 : List PrefixCut := [⟨31,95983284,95983336⟩,
⟨64,200330131,200330242⟩]
theorem checked62101 : checkPrefixCuts (2^48) 8143634433 10 Manual.Count131072.C062101.packed 64 cuts62101 = true := by
 decide +kernel
def pointBounds62101 : List (Nat × Nat × Nat) := [(8143697920,114341557520365,114341946170768)]
theorem point_links_checked62101 : (cuts62101.take 1).map (fun c => (8143634433-1+2*2^10*c.k,114341461537081+c.lower,114341850187432+c.upper)) = pointBounds62101 := by
 decide +kernel
def cuts62102 : List PrefixCut := [⟨64,195418956,195419065⟩]
theorem checked62102 : checkPrefixCuts (2^48) 8143765505 10 Manual.Count131072.C062102.packed 64 cuts62102 = true := by
 decide +kernel
def cuts62103 : List PrefixCut := [⟨28,85818830,85818877⟩,
⟨64,197593248,197593358⟩]
theorem checked62103 : checkPrefixCuts (2^48) 8143896577 10 Manual.Count131072.C062103.packed 64 cuts62103 = true := by
 decide +kernel
def pointBounds62103 : List (Nat × Nat × Nat) := [(8143953920,114341943104998,114342331755616)]
theorem point_links_checked62103 : (cuts62103.take 1).map (fun c => (8143896577-1+2*2^10*c.k,114341857286168+c.lower,114342245936739+c.upper)) = pointBounds62103 := by
 decide +kernel
def cuts62104 : List PrefixCut := [⟨64,198730619,198730729⟩]
theorem checked62104 : checkPrefixCuts (2^48) 8144027649 10 Manual.Count131072.C062104.packed 64 cuts62104 = true := by
 decide +kernel
def cuts62105 : List PrefixCut := [⟨25,78834688,78834731⟩,
⟨64,200593732,200593845⟩]
theorem checked62105 : checkPrefixCuts (2^48) 8144158721 10 Manual.Count131072.C062105.packed 64 cuts62105 = true := by
 decide +kernel
def pointBounds62105 : List (Nat × Nat × Nat) := [(8144209920,114342332444723,114342721095557)]
theorem point_links_checked62105 : (cuts62105.take 1).map (fun c => (8144158721-1+2*2^10*c.k,114342253610035+c.lower,114342642260826+c.upper)) = pointBounds62105 := by
 decide +kernel
def cuts62106 : List PrefixCut := [⟨64,197963884,197963996⟩]
theorem checked62106 : checkPrefixCuts (2^48) 8144289793 10 Manual.Count131072.C062106.packed 64 cuts62106 = true := by
 decide +kernel
def cuts62107 : List PrefixCut := [⟨22,66252208,66252246⟩,
⟨64,194919388,194919500⟩]
theorem checked62107 : checkPrefixCuts (2^48) 8144420865 10 Manual.Count131072.C062107.packed 64 cuts62107 = true := by
 decide +kernel
def pointBounds62107 : List (Nat × Nat × Nat) := [(8144465920,114342718419859,114343107070913)]
theorem point_links_checked62107 : (cuts62107.take 1).map (fun c => (8144420865-1+2*2^10*c.k,114342652167651+c.lower,114343040818667+c.upper)) = pointBounds62107 := by
 decide +kernel
def cuts62108 : List PrefixCut := [⟨64,197197191,197197301⟩]
theorem checked62108 : checkPrefixCuts (2^48) 8144551937 10 Manual.Count131072.C062108.packed 64 cuts62108 = true := by
 decide +kernel
def cuts62109 : List PrefixCut := [⟨19,59752962,59752997⟩,
⟨64,200338904,200339019⟩]
theorem checked62109 : checkPrefixCuts (2^48) 8144683009 10 Manual.Count131072.C062109.packed 64 cuts62109 = true := by
 decide +kernel
def pointBounds62109 : List (Nat × Nat × Nat) := [(8144721920,114343104037192,114343492688465)]
theorem point_links_checked62109 : (cuts62109.take 1).map (fun c => (8144683009-1+2*2^10*c.k,114343044284230+c.lower,114343432935468+c.upper)) = pointBounds62109 := by
 decide +kernel
def cuts62110 : List PrefixCut := [⟨64,198884219,198884338⟩]
theorem checked62110 : checkPrefixCuts (2^48) 8144814081 10 Manual.Count131072.C062110.packed 64 cuts62110 = true := by
 decide +kernel
def cuts62111 : List PrefixCut := [⟨16,48934356,48934386⟩,
⟨64,199537613,199537729⟩]
theorem checked62111 : checkPrefixCuts (2^48) 8144945153 10 Manual.Count131072.C062111.packed 64 cuts62111 = true := by
 decide +kernel
def pointBounds62111 : List (Nat × Nat × Nat) := [(8144977920,114343492441709,114343881093211)]
theorem point_links_checked62111 : (cuts62111.take 1).map (fun c => (8144945153-1+2*2^10*c.k,114343443507353+c.lower,114343832158825+c.upper)) = pointBounds62111 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000065
