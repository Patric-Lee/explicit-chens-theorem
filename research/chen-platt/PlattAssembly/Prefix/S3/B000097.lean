import PlattAssemblyKernel
import PlattCertificates.Count131072.C023104
import PlattCertificates.Count131072.C023105
import PlattCertificates.Count131072.C023106
import PlattCertificates.Count131072.C023107
import PlattCertificates.Count131072.C023108
import PlattCertificates.Count131072.C023109
import PlattCertificates.Count131072.C023110
import PlattCertificates.Count131072.C023111
import PlattCertificates.Count131072.C023112
import PlattCertificates.Count131072.C023113
import PlattCertificates.Count131072.C023114
import PlattCertificates.Count131072.C023115
import PlattCertificates.Count131072.C023116
import PlattCertificates.Count131072.C023117
import PlattCertificates.Count131072.C023118
import PlattCertificates.Count131072.C023119
import PlattCertificates.Count131072.C023120
import PlattCertificates.Count131072.C023121
import PlattCertificates.Count131072.C023122
import PlattCertificates.Count131072.C023123
import PlattCertificates.Count131072.C023124
import PlattCertificates.Count131072.C023125
import PlattCertificates.Count131072.C023126
import PlattCertificates.Count131072.C023127
import PlattCertificates.Count131072.C023128
import PlattCertificates.Count131072.C023129
import PlattCertificates.Count131072.C023130
import PlattCertificates.Count131072.C023131
import PlattCertificates.Count131072.C023132
import PlattCertificates.Count131072.C023133
import PlattCertificates.Count131072.C023134
import PlattCertificates.Count131072.C023135
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000097
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23104 : List PrefixCut := [⟨56,244692276,244692416⟩,
⟨128,551850574,551850887⟩]
theorem checked23104 : checkPrefixCuts (2^48) 3032219649 9 Manual.Count131072.C023104.packed 128 cuts23104 = true := by
 decide +kernel
def pointBounds23104 : List (Nat × Nat × Nat) := [(3032276992,101884543540832,101884924985346)]
theorem point_links_checked23104 : (cuts23104.take 1).map (fun c => (3032219649-1+2*2^9*c.k,101884298848556+c.lower,101884680292930+c.upper)) = pointBounds23104 := by
 decide +kernel
def cuts23105 : List PrefixCut := [⟨21,91060002,91060051⟩,
⟨114,493164405,493164687⟩,
⟨128,556653420,556653735⟩]
theorem checked23105 : checkPrefixCuts (2^48) 3032350721 9 Manual.Count131072.C023105.packed 128 cuts23105 = true := by
 decide +kernel
def pointBounds23105 : List (Nat × Nat × Nat) := [(3032372224,101884941759132,101885323203868),(3032467456,101885343863535,101885725308504)]
theorem point_links_checked23105 : (cuts23105.take 2).map (fun c => (3032350721-1+2*2^9*c.k,101884850699130+c.lower,101885232143817+c.upper)) = pointBounds23105 := by
 decide +kernel
def cuts23106 : List PrefixCut := [⟨79,339623810,339624003⟩,
⟨128,556722185,556722501⟩]
theorem checked23106 : checkPrefixCuts (2^48) 3032481793 9 Manual.Count131072.C023106.packed 128 cuts23106 = true := by
 decide +kernel
def pointBounds23106 : List (Nat × Nat × Nat) := [(3032562688,101885746976360,101886128421555)]
theorem point_links_checked23106 : (cuts23106.take 1).map (fun c => (3032481793-1+2*2^9*c.k,101885407352550+c.lower,101885788797552+c.upper)) = pointBounds23106 := by
 decide +kernel
def cuts23107 : List PrefixCut := [⟨44,189621614,189621722⟩,
⟨128,557347764,557348082⟩]
theorem checked23107 : checkPrefixCuts (2^48) 3032612865 9 Manual.Count131072.C023107.packed 128 cuts23107 = true := by
 decide +kernel
def pointBounds23107 : List (Nat × Nat × Nat) := [(3032657920,101886153696349,101886535141775)]
theorem point_links_checked23107 : (cuts23107.take 1).map (fun c => (3032612865-1+2*2^9*c.k,101885964074735+c.lower,101886345520053+c.upper)) = pointBounds23107 := by
 decide +kernel
def cuts23108 : List PrefixCut := [⟨9,40651574,40651595⟩,
⟨102,445953792,445954045⟩,
⟨128,557045384,557045703⟩]
theorem checked23108 : checkPrefixCuts (2^48) 3032743937 9 Manual.Count131072.C023108.packed 128 cuts23108 = true := by
 decide +kernel
def pointBounds23108 : List (Nat × Nat × Nat) := [(3032753152,101886562074073,101886943519730),(3032848384,101886967376291,101887348822180)]
theorem point_links_checked23108 : (cuts23108.take 2).map (fun c => (3032743937-1+2*2^9*c.k,101886521422499+c.lower,101886902868135+c.upper)) = pointBounds23108 := by
 decide +kernel
def cuts23109 : List PrefixCut := [⟨67,293269808,293269979⟩,
⟨128,567044220,567044542⟩]
theorem checked23109 : checkPrefixCuts (2^48) 3032875009 9 Manual.Count131072.C023109.packed 128 cuts23109 = true := by
 decide +kernel
def pointBounds23109 : List (Nat × Nat × Nat) := [(3032943616,101887371737691,101887753183817)]
theorem point_links_checked23109 : (cuts23109.take 1).map (fun c => (3032875009-1+2*2^9*c.k,101887078467883+c.lower,101887459913838+c.upper)) = pointBounds23109 := by
 decide +kernel
def cuts23110 : List PrefixCut := [⟨32,136513851,136513930⟩,
⟨125,544469105,544469416⟩,
⟨128,556811501,556811819⟩]
theorem checked23110 : checkPrefixCuts (2^48) 3033006081 9 Manual.Count131072.C023110.packed 128 cuts23110 = true := by
 decide +kernel
def pointBounds23110 : List (Nat × Nat × Nat) := [(3033038848,101887782025954,101888163472310),(3033134080,101888189981208,101888571427796)]
theorem point_links_checked23110 : (cuts23110.take 2).map (fun c => (3033006081-1+2*2^9*c.k,101887645512103+c.lower,101888026958380+c.upper)) = pointBounds23110 := by
 decide +kernel
def cuts23111 : List PrefixCut := [⟨90,392537682,392537904⟩,
⟨128,556601907,556602219⟩]
theorem checked23111 : checkPrefixCuts (2^48) 3033137153 9 Manual.Count131072.C023111.packed 128 cuts23111 = true := by
 decide +kernel
def pointBounds23111 : List (Nat × Nat × Nat) := [(3033229312,101888594861286,101888976308103)]
theorem point_links_checked23111 : (cuts23111.take 1).map (fun c => (3033137153-1+2*2^9*c.k,101888202323604+c.lower,101888583770199+c.upper)) = pointBounds23111 := by
 decide +kernel
def cuts23112 : List PrefixCut := [⟨55,236905754,236905885⟩,
⟨128,547020125,547020432⟩]
theorem checked23112 : checkPrefixCuts (2^48) 3033268225 9 Manual.Count131072.C023112.packed 128 cuts23112 = true := by
 decide +kernel
def pointBounds23112 : List (Nat × Nat × Nat) := [(3033324544,101888995831265,101889377278303)]
theorem point_links_checked23112 : (cuts23112.take 1).map (fun c => (3033268225-1+2*2^9*c.k,101888758925511+c.lower,101889140372418+c.upper)) = pointBounds23112 := by
 decide +kernel
def cuts23113 : List PrefixCut := [⟨20,88523178,88523229⟩,
⟨113,491880528,491880798⟩,
⟨128,555904338,555904644⟩]
theorem checked23113 : checkPrefixCuts (2^48) 3033399297 9 Manual.Count131072.C023113.packed 128 cuts23113 = true := by
 decide +kernel
def pointBounds23113 : List (Nat × Nat × Nat) := [(3033419776,101889394468814,101889775916079),(3033515008,101889797826164,101890179273648)]
theorem point_links_checked23113 : (cuts23113.take 2).map (fun c => (3033399297-1+2*2^9*c.k,101889305945636+c.lower,101889687392850+c.upper)) = pointBounds23113 := by
 decide +kernel
def cuts23114 : List PrefixCut := [⟨78,344980791,344980992⟩,
⟨128,562004113,562004437⟩]
theorem checked23114 : checkPrefixCuts (2^48) 3033530369 9 Manual.Count131072.C023114.packed 128 cuts23114 = true := by
 decide +kernel
def pointBounds23114 : List (Nat × Nat × Nat) := [(3033610240,101890206830765,101890588278486)]
theorem point_links_checked23114 : (cuts23114.take 1).map (fun c => (3033530369-1+2*2^9*c.k,101889861849974+c.lower,101890243297494+c.upper)) = pointBounds23114 := by
 decide +kernel
def cuts23115 : List PrefixCut := [⟨43,184916948,184917053⟩,
⟨128,560031328,560031648⟩]
theorem checked23115 : checkPrefixCuts (2^48) 3033661441 9 Manual.Count131072.C023115.packed 128 cuts23115 = true := by
 decide +kernel
def pointBounds23115 : List (Nat × Nat × Nat) := [(3033705472,101890608771035,101890990218984)]
theorem point_links_checked23115 : (cuts23115.take 1).map (fun c => (3033661441-1+2*2^9*c.k,101890423854087+c.lower,101890805301931+c.upper)) = pointBounds23115 := by
 decide +kernel
def cuts23116 : List PrefixCut := [⟨8,37575801,37575822⟩,
⟨101,437171424,437171667⟩,
⟨128,556481740,556482054⟩]
theorem checked23116 : checkPrefixCuts (2^48) 3033792513 9 Manual.Count131072.C023116.packed 128 cuts23116 = true := by
 decide +kernel
def pointBounds23116 : List (Nat × Nat × Nat) := [(3033800704,101891021461216,101891402909401),(3033895936,101891421056839,101891802505246)]
theorem point_links_checked23116 : (cuts23116.take 2).map (fun c => (3033792513-1+2*2^9*c.k,101890983885415+c.lower,101891365333579+c.upper)) = pointBounds23116 := by
 decide +kernel
def cuts23117 : List PrefixCut := [⟨66,290385236,290385402⟩,
⟨128,561652984,561653306⟩]
theorem checked23117 : checkPrefixCuts (2^48) 3033923585 9 Manual.Count131072.C023117.packed 128 cuts23117 = true := by
 decide +kernel
def pointBounds23117 : List (Nat × Nat × Nat) := [(3033991168,101891830752391,101892212201035)]
theorem point_links_checked23117 : (cuts23117.take 1).map (fun c => (3033923585-1+2*2^9*c.k,101891540367155+c.lower,101891921815633+c.upper)) = pointBounds23117 := by
 decide +kernel
def cuts23118 : List PrefixCut := [⟨31,138785968,138786051⟩,
⟨124,546229379,546229683⟩,
⟨128,563948050,563948365⟩]
theorem checked23118 : checkPrefixCuts (2^48) 3034054657 9 Manual.Count131072.C023118.packed 128 cuts23118 = true := by
 decide +kernel
def pointBounds23118 : List (Nat × Nat × Nat) := [(3034086400,101892240806107,101892622254990),(3034181632,101892648249518,101893029698622)]
theorem point_links_checked23118 : (cuts23118.take 2).map (fun c => (3034054657-1+2*2^9*c.k,101892102020139+c.lower,101892483468939+c.upper)) = pointBounds23118 := by
 decide +kernel
def cuts23119 : List PrefixCut := [⟨89,391845520,391845746⟩,
⟨128,557708378,557708698⟩]
theorem checked23119 : checkPrefixCuts (2^48) 3034185729 9 Manual.Count131072.C023119.packed 128 cuts23119 = true := by
 decide +kernel
def pointBounds23119 : List (Nat × Nat × Nat) := [(3034276864,101893057813709,101893439263050)]
theorem point_links_checked23119 : (cuts23119.take 1).map (fun c => (3034185729-1+2*2^9*c.k,101892665968189+c.lower,101893047417304+c.upper)) = pointBounds23119 := by
 decide +kernel
def cuts23120 : List PrefixCut := [⟨54,231907497,231907629⟩,
⟨128,556199924,556200240⟩]
theorem checked23120 : checkPrefixCuts (2^48) 3034316801 9 Manual.Count131072.C023120.packed 128 cuts23120 = true := by
 decide +kernel
def pointBounds23120 : List (Nat × Nat × Nat) := [(3034372096,101893455584064,101893837033631)]
theorem point_links_checked23120 : (cuts23120.take 1).map (fun c => (3034316801-1+2*2^9*c.k,101893223676567+c.lower,101893605126002+c.upper)) = pointBounds23120 := by
 decide +kernel
def cuts23121 : List PrefixCut := [⟨19,80329765,80329811⟩,
⟨112,479188300,479188570⟩,
⟨128,548569851,548570160⟩]
theorem checked23121 : checkPrefixCuts (2^48) 3034447873 9 Manual.Count131072.C023121.packed 128 cuts23121 = true := by
 decide +kernel
def pointBounds23121 : List (Nat × Nat × Nat) := [(3034467328,101893860206256,101894241656053),(3034562560,101894259064791,101894640514812)]
theorem point_links_checked23121 : (cuts23121.take 2).map (fun c => (3034447873-1+2*2^9*c.k,101893779876491+c.lower,101894161326242+c.upper)) = pointBounds23121 := by
 decide +kernel
def cuts23122 : List PrefixCut := [⟨77,339760175,339760372⟩,
⟨128,559954902,559955219⟩]
theorem checked23122 : checkPrefixCuts (2^48) 3034578945 9 Manual.Count131072.C023122.packed 128 cuts23122 = true := by
 decide +kernel
def pointBounds23122 : List (Nat × Nat × Nat) := [(3034657792,101894668206517,101895049656774)]
theorem point_links_checked23122 : (cuts23122.take 1).map (fun c => (3034578945-1+2*2^9*c.k,101894328446342+c.lower,101894709896402+c.upper)) = pointBounds23122 := by
 decide +kernel
def cuts23123 : List PrefixCut := [⟨42,180401037,180401143⟩,
⟨128,557704637,557704957⟩]
theorem checked23123 : checkPrefixCuts (2^48) 3034710017 9 Manual.Count131072.C023123.packed 128 cuts23123 = true := by
 decide +kernel
def pointBounds23123 : List (Nat × Nat × Nat) := [(3034753024,101895068802281,101895450252764)]
theorem point_links_checked23123 : (cuts23123.take 1).map (fun c => (3034710017-1+2*2^9*c.k,101894888401244+c.lower,101895269851621+c.upper)) = pointBounds23123 := by
 decide +kernel
def cuts23124 : List PrefixCut := [⟨7,32647194,32647213⟩,
⟨100,435258194,435258444⟩,
⟨128,555825733,555826049⟩]
theorem checked23124 : checkPrefixCuts (2^48) 3034841089 9 Manual.Count131072.C023124.packed 128 cuts23124 = true := by
 decide +kernel
def pointBounds23124 : List (Nat × Nat × Nat) := [(3034848256,101895478753075,101895860203791),(3034943488,101895881364075,101896262815022)]
theorem point_links_checked23124 : (cuts23124.take 2).map (fun c => (3034841089-1+2*2^9*c.k,101895446105881+c.lower,101895827556578+c.upper)) = pointBounds23124 := by
 decide +kernel
def cuts23125 : List PrefixCut := [⟨65,283514706,283514869⟩,
⟨128,553575903,553576224⟩]
theorem checked23125 : checkPrefixCuts (2^48) 3034972161 9 Manual.Count131072.C023125.packed 128 cuts23125 = true := by
 decide +kernel
def pointBounds23125 : List (Nat × Nat × Nat) := [(3035038720,101896285446320,101896666897496)]
theorem point_links_checked23125 : (cuts23125.take 1).map (fun c => (3034972161-1+2*2^9*c.k,101896001931614+c.lower,101896383382627+c.upper)) = pointBounds23125 := by
 decide +kernel
def cuts23126 : List PrefixCut := [⟨30,129649599,129649674⟩,
⟨123,535654029,535654333⟩,
⟨128,557632434,557632750⟩]
theorem checked23126 : checkPrefixCuts (2^48) 3035103233 9 Manual.Count131072.C023126.packed 128 cuts23126 = true := by
 decide +kernel
def pointBounds23126 : List (Nat × Nat × Nat) := [(3035133952,101896685157116,101897066608525),(3035229184,101897091161546,101897472613184)]
theorem point_links_checked23126 : (cuts23126.take 2).map (fun c => (3035103233-1+2*2^9*c.k,101896555507517+c.lower,101896936958851+c.upper)) = pointBounds23126 := by
 decide +kernel
def cuts23127 : List PrefixCut := [⟨88,383735024,383735231⟩,
⟨128,553713570,553713872⟩]
theorem checked23127 : checkPrefixCuts (2^48) 3035234305 9 Manual.Count131072.C023127.packed 128 cuts23127 = true := by
 decide +kernel
def pointBounds23127 : List (Nat × Nat × Nat) := [(3035324416,101897496874975,101897878326832)]
theorem point_links_checked23127 : (cuts23127.take 1).map (fun c => (3035234305-1+2*2^9*c.k,101897113139951+c.lower,101897494591601+c.upper)) = pointBounds23127 := by
 decide +kernel
def cuts23128 : List PrefixCut := [⟨53,235443955,235444090⟩,
⟨128,564353657,564353979⟩]
theorem checked23128 : checkPrefixCuts (2^48) 3035365377 9 Manual.Count131072.C023128.packed 128 cuts23128 = true := by
 decide +kernel
def pointBounds23128 : List (Nat × Nat × Nat) := [(3035419648,101897902297476,101898283749563)]
theorem point_links_checked23128 : (cuts23128.take 1).map (fun c => (3035365377-1+2*2^9*c.k,101897666853521+c.lower,101898048305473+c.upper)) = pointBounds23128 := by
 decide +kernel
def cuts23129 : List PrefixCut := [⟨18,77427478,77427524⟩,
⟨111,481248258,481248541⟩,
⟨128,555705673,555705997⟩]
theorem checked23129 : checkPrefixCuts (2^48) 3035496449 9 Manual.Count131072.C023129.packed 128 cuts23129 = true := by
 decide +kernel
def pointBounds23129 : List (Nat × Nat × Nat) := [(3035514880,101898308634656,101898690086976),(3035610112,101898712455436,101899093907993)]
theorem point_links_checked23129 : (cuts23129.take 2).map (fun c => (3035496449-1+2*2^9*c.k,101898231207178+c.lower,101898612659452+c.upper)) = pointBounds23129 := by
 decide +kernel
def cuts23130 : List PrefixCut := [⟨76,326476246,326476426⟩,
⟨128,554105325,554105637⟩]
theorem checked23130 : checkPrefixCuts (2^48) 3035627521 9 Manual.Count131072.C023130.packed 128 cuts23130 = true := by
 decide +kernel
def pointBounds23130 : List (Nat × Nat × Nat) := [(3035705344,101899113389097,101899494841875)]
theorem point_links_checked23130 : (cuts23130.take 1).map (fun c => (3035627521-1+2*2^9*c.k,101898786912851+c.lower,101899168365449+c.upper)) = pointBounds23130 := by
 decide +kernel
def cuts23131 : List PrefixCut := [⟨41,175239188,175239284⟩,
⟨128,550558204,550558503⟩]
theorem checked23131 : checkPrefixCuts (2^48) 3035758593 9 Manual.Count131072.C023131.packed 128 cuts23131 = true := by
 decide +kernel
def pointBounds23131 : List (Nat × Nat × Nat) := [(3035800576,101899516257364,101899897710370)]
theorem point_links_checked23131 : (cuts23131.take 1).map (fun c => (3035758593-1+2*2^9*c.k,101899341018176+c.lower,101899722471086+c.upper)) = pointBounds23131 := by
 decide +kernel
def cuts23132 : List PrefixCut := [⟨6,26516689,26516703⟩,
⟨99,428988801,428989035⟩,
⟨128,556189981,556190286⟩]
theorem checked23132 : checkPrefixCuts (2^48) 3035889665 9 Manual.Count131072.C023132.packed 128 cuts23132 = true := by
 decide +kernel
def pointBounds23132 : List (Nat × Nat × Nat) := [(3035895808,101899918093069,101900299546292),(3035991040,101900320565181,101900702018624)]
theorem point_links_checked23132 : (cuts23132.take 2).map (fun c => (3035889665-1+2*2^9*c.k,101899891576380+c.lower,101900273029589+c.upper)) = pointBounds23132 := by
 decide +kernel
def cuts23133 : List PrefixCut := [⟨64,276741672,276741834⟩,
⟨128,549954443,549954759⟩]
theorem checked23133 : checkPrefixCuts (2^48) 3036020737 9 Manual.Count131072.C023133.packed 128 cuts23133 = true := by
 decide +kernel
def pointBounds23133 : List (Nat × Nat × Nat) := [(3036086272,101900724508033,101901105961709)]
theorem point_links_checked23133 : (cuts23133.take 1).map (fun c => (3036020737-1+2*2^9*c.k,101900447766361+c.lower,101900829219875+c.upper)) = pointBounds23133 := by
 decide +kernel
def cuts23134 : List PrefixCut := [⟨29,127287159,127287234⟩,
⟨122,534078555,534078859⟩,
⟨128,559850232,559850550⟩]
theorem checked23134 : checkPrefixCuts (2^48) 3036151809 9 Manual.Count131072.C023134.packed 128 cuts23134 = true := by
 decide +kernel
def pointBounds23134 : List (Nat × Nat × Nat) := [(3036181504,101901125007963,101901506461868),(3036276736,101901531799359,101901913253493)]
theorem point_links_checked23134 : (cuts23134.take 2).map (fun c => (3036151809-1+2*2^9*c.k,101900997720804+c.lower,101901379174634+c.upper)) = pointBounds23134 := by
 decide +kernel
def cuts23135 : List PrefixCut := [⟨87,374795844,374796053⟩,
⟨128,551297460,551297770⟩]
theorem checked23135 : checkPrefixCuts (2^48) 3036282881 9 Manual.Count131072.C023135.packed 128 cuts23135 = true := by
 decide +kernel
def pointBounds23135 : List (Nat × Nat × Nat) := [(3036371968,101901932366880,101902313821237)]
theorem point_links_checked23135 : (cuts23135.take 1).map (fun c => (3036282881-1+2*2^9*c.k,101901557571036+c.lower,101901939025184+c.upper)) = pointBounds23135 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000097
