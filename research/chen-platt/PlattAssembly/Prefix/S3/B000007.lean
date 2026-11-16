import PlattAssemblyKernel
import PlattCertificates.Count131072.C020224
import PlattCertificates.Count131072.C020225
import PlattCertificates.Count131072.C020226
import PlattCertificates.Count131072.C020227
import PlattCertificates.Count131072.C020228
import PlattCertificates.Count131072.C020229
import PlattCertificates.Count131072.C020230
import PlattCertificates.Count131072.C020231
import PlattCertificates.Count131072.C020232
import PlattCertificates.Count131072.C020233
import PlattCertificates.Count131072.C020234
import PlattCertificates.Count131072.C020235
import PlattCertificates.Count131072.C020236
import PlattCertificates.Count131072.C020237
import PlattCertificates.Count131072.C020238
import PlattCertificates.Count131072.C020239
import PlattCertificates.Count131072.C020240
import PlattCertificates.Count131072.C020241
import PlattCertificates.Count131072.C020242
import PlattCertificates.Count131072.C020243
import PlattCertificates.Count131072.C020244
import PlattCertificates.Count131072.C020245
import PlattCertificates.Count131072.C020246
import PlattCertificates.Count131072.C020247
import PlattCertificates.Count131072.C020248
import PlattCertificates.Count131072.C020249
import PlattCertificates.Count131072.C020250
import PlattCertificates.Count131072.C020251
import PlattCertificates.Count131072.C020252
import PlattCertificates.Count131072.C020253
import PlattCertificates.Count131072.C020254
import PlattCertificates.Count131072.C020255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20224 : List PrefixCut := [⟨20,102210210,102210272⟩,
⟨102,504893583,504893882⟩,
⟨128,632651175,632651548⟩]
theorem checked20224 : checkPrefixCuts (2^48) 2654732289 9 Manual.Count131072.C020224.packed 128 cuts20224 = true := by
 decide +kernel
def pointBounds20224 : List (Nat × Nat × Nat) := [(2654752768,100165201165885,100165581620343),(2654836736,100165603849258,100165984303953)]
theorem point_links_checked20224 : (cuts20224.take 2).map (fun c => (2654732289-1+2*2^9*c.k,100165098955675+c.lower,100165479410071+c.upper)) = pointBounds20224 := by
 decide +kernel
def cuts20225 : List PrefixCut := [⟨56,280744250,280744413⟩,
⟨128,645024189,645024564⟩]
theorem checked20225 : checkPrefixCuts (2^48) 2654863361 9 Manual.Count131072.C020225.packed 128 cuts20225 = true := by
 decide +kernel
def pointBounds20225 : List (Nat × Nat × Nat) := [(2654920704,100166012351100,100166392806032)]
theorem point_links_checked20225 : (cuts20225.take 1).map (fun c => (2654863361-1+2*2^9*c.k,100165731606850+c.lower,100166112061619+c.upper)) = pointBounds20225 := by
 decide +kernel
def cuts20226 : List PrefixCut := [⟨10,53856600,53856629⟩,
⟨92,464876912,464877183⟩,
⟨128,645522443,645522821⟩]
theorem checked20226 : checkPrefixCuts (2^48) 2654994433 9 Manual.Count131072.C020226.packed 128 cuts20226 = true := by
 decide +kernel
def pointBounds20226 : List (Nat × Nat × Nat) := [(2655004672,100166430487639,100166810942812),(2655088640,100166841507951,100167221963366)]
theorem point_links_checked20226 : (cuts20226.take 2).map (fun c => (2654994433-1+2*2^9*c.k,100166376631039+c.lower,100166757086183+c.upper)) = pointBounds20226 := by
 decide +kernel
def cuts20227 : List PrefixCut := [⟨46,231527917,231528054⟩,
⟨128,641038095,641038471⟩]
theorem checked20227 : checkPrefixCuts (2^48) 2655125505 9 Manual.Count131072.C020227.packed 128 cuts20227 = true := by
 decide +kernel
def pointBounds20227 : List (Nat × Nat × Nat) := [(2655172608,100167253681399,100167634137058),(2655256576,100167663191577,100168043647475)]
theorem point_links_checked20227 : (cuts20227.take 2).map (fun c => (2655125505-1+2*2^9*c.k,100167022153482+c.lower,100167402609004+c.upper)) = pointBounds20227 := by
 decide +kernel
def cuts20228 : List PrefixCut := [⟨82,413631546,413631781⟩,
⟨128,646730752,646731123⟩]
theorem checked20228 : checkPrefixCuts (2^48) 2655256577 9 Manual.Count131072.C020228.packed 128 cuts20228 = true := by
 decide +kernel
def pointBounds20228 : List (Nat × Nat × Nat) := [(2655340544,100168076823123,100168457279256)]
theorem point_links_checked20228 : (cuts20228.take 1).map (fun c => (2655256577-1+2*2^9*c.k,100167663191577+c.lower,100168043647475+c.upper)) = pointBounds20228 := by
 decide +kernel
def cuts20229 : List PrefixCut := [⟨36,182321189,182321292⟩,
⟨118,591050522,591050863⟩,
⟨128,640656835,640657205⟩]
theorem checked20229 : checkPrefixCuts (2^48) 2655387649 9 Manual.Count131072.C020229.packed 128 cuts20229 = true := by
 decide +kernel
def pointBounds20229 : List (Nat × Nat × Nat) := [(2655424512,100168492243518,100168872699890),(2655508480,100168900972851,100169281429461)]
theorem point_links_checked20229 : (cuts20229.take 2).map (fun c => (2655387649-1+2*2^9*c.k,100168309922329+c.lower,100168690378598+c.upper)) = pointBounds20229 := by
 decide +kernel
def cuts20230 : List PrefixCut := [⟨72,362819977,362820191⟩,
⟨128,639883336,639883714⟩]
theorem checked20230 : checkPrefixCuts (2^48) 2655518721 9 Manual.Count131072.C020230.packed 128 cuts20230 = true := by
 decide +kernel
def pointBounds20230 : List (Nat × Nat × Nat) := [(2655592448,100169313399141,100169693855994)]
theorem point_links_checked20230 : (cuts20230.take 1).map (fun c => (2655518721-1+2*2^9*c.k,100168950579164+c.lower,100169331035803+c.upper)) = pointBounds20230 := by
 decide +kernel
def cuts20231 : List PrefixCut := [⟨26,133653941,133654019⟩,
⟨108,548067887,548068208⟩,
⟨128,648648743,648649122⟩]
theorem checked20231 : checkPrefixCuts (2^48) 2655649793 9 Manual.Count131072.C020231.packed 128 cuts20231 = true := by
 decide +kernel
def pointBounds20231 : List (Nat × Nat × Nat) := [(2655676416,100169724116441,100170104573536),(2655760384,100170138530387,100170518987725)]
theorem point_links_checked20231 : (cuts20231.take 2).map (fun c => (2655649793-1+2*2^9*c.k,100169590462500+c.lower,100169970919517+c.upper)) = pointBounds20231 := by
 decide +kernel
def cuts20232 : List PrefixCut := [⟨62,312336218,312336401⟩,
⟨128,649252548,649252924⟩]
theorem checked20232 : checkPrefixCuts (2^48) 2655780865 9 Manual.Count131072.C020232.packed 128 cuts20232 = true := by
 decide +kernel
def pointBounds20232 : List (Nat × Nat × Nat) := [(2655844352,100170551447461,100170931905040)]
theorem point_links_checked20232 : (cuts20232.take 1).map (fun c => (2655780865-1+2*2^9*c.k,100170239111243+c.lower,100170619568639+c.upper)) = pointBounds20232 := by
 decide +kernel
def cuts20233 : List PrefixCut := [⟨16,74716023,74716067⟩,
⟨98,487395070,487395362⟩,
⟨128,638410705,638411088⟩]
theorem checked20233 : checkPrefixCuts (2^48) 2655911937 9 Manual.Count131072.C020233.packed 128 cuts20233 = true := by
 decide +kernel
def pointBounds20233 : List (Nat × Nat × Nat) := [(2655928320,100170963079814,100171343537630),(2656012288,100171375758861,100171756216925)]
theorem point_links_checked20233 : (cuts20233.take 2).map (fun c => (2655911937-1+2*2^9*c.k,100170888363791+c.lower,100171268821563+c.upper)) = pointBounds20233 := by
 decide +kernel
def cuts20234 : List PrefixCut := [⟨52,262922038,262922192⟩,
⟨128,646433264,646433640⟩]
theorem checked20234 : checkPrefixCuts (2^48) 2656043009 9 Manual.Count131072.C020234.packed 128 cuts20234 = true := by
 decide +kernel
def pointBounds20234 : List (Nat × Nat × Nat) := [(2656096256,100171789696534,100172170154843)]
theorem point_links_checked20234 : (cuts20234.take 1).map (fun c => (2656043009-1+2*2^9*c.k,100171526774496+c.lower,100171907232651+c.upper)) = pointBounds20234 := by
 decide +kernel
def cuts20235 : List PrefixCut := [⟨6,26598450,26598467⟩,
⟨88,436589053,436589312⟩,
⟨128,634003020,634003394⟩]
theorem checked20235 : checkPrefixCuts (2^48) 2656174081 9 Manual.Count131072.C020235.packed 128 cuts20235 = true := by
 decide +kernel
def pointBounds20235 : List (Nat × Nat × Nat) := [(2656180224,100172199806210,100172580264758),(2656264192,100172609796813,100172990255603)]
theorem point_links_checked20235 : (cuts20235.take 2).map (fun c => (2656174081-1+2*2^9*c.k,100172173207760+c.lower,100172553666291+c.upper)) = pointBounds20235 := by
 decide +kernel
def cuts20236 : List PrefixCut := [⟨42,212563683,212563810⟩,
⟨124,622846285,622846655⟩,
⟨128,643826301,643826683⟩]
theorem checked20236 : checkPrefixCuts (2^48) 2656305153 9 Manual.Count131072.C020236.packed 128 cuts20236 = true := by
 decide +kernel
def pointBounds20236 : List (Nat × Nat × Nat) := [(2656348160,100173019774463,100173400233495),(2656432128,100173430057065,100173810516340)]
theorem point_links_checked20236 : (cuts20236.take 2).map (fun c => (2656305153-1+2*2^9*c.k,100172807210780+c.lower,100173187669685+c.upper)) = pointBounds20236 := by
 decide +kernel
def cuts20237 : List PrefixCut := [⟨78,385475191,385475416⟩,
⟨128,637013252,637013622⟩]
theorem checked20237 : checkPrefixCuts (2^48) 2656436225 9 Manual.Count131072.C020237.packed 128 cuts20237 = true := by
 decide +kernel
def pointBounds20237 : List (Nat × Nat × Nat) := [(2656516096,100173836512272,100174216971784)]
theorem point_links_checked20237 : (cuts20237.take 1).map (fun c => (2656436225-1+2*2^9*c.k,100173451037081+c.lower,100173831496368+c.upper)) = pointBounds20237 := by
 decide +kernel
def cuts20238 : List PrefixCut := [⟨32,158506754,158506847⟩,
⟨114,566419500,566419834⟩,
⟨128,638994854,638995230⟩]
theorem checked20238 : checkPrefixCuts (2^48) 2656567297 9 Manual.Count131072.C020238.packed 128 cuts20238 = true := by
 decide +kernel
def pointBounds20238 : List (Nat × Nat × Nat) := [(2656600064,100174246557087,100174627016837),(2656684032,100174654469833,100175034929824)]
theorem point_links_checked20238 : (cuts20238.take 2).map (fun c => (2656567297-1+2*2^9*c.k,100174088050333+c.lower,100174468509990+c.upper)) = pointBounds20238 := by
 decide +kernel
def cuts20239 : List PrefixCut := [⟨68,336066279,336066475⟩,
⟨128,638009893,638010264⟩]
theorem checked20239 : checkPrefixCuts (2^48) 2656698369 9 Manual.Count131072.C020239.packed 128 cuts20239 = true := by
 decide +kernel
def pointBounds20239 : List (Nat × Nat × Nat) := [(2656768000,100175063111466,100175443571695)]
theorem point_links_checked20239 : (cuts20239.take 1).map (fun c => (2656698369-1+2*2^9*c.k,100174727045187+c.lower,100175107505220+c.upper)) = pointBounds20239 := by
 decide +kernel
def cuts20240 : List PrefixCut := [⟨22,112935726,112935792⟩,
⟨104,519856357,519856662⟩,
⟨128,640415130,640415506⟩]
theorem checked20240 : checkPrefixCuts (2^48) 2656829441 9 Manual.Count131072.C020240.packed 128 cuts20240 = true := by
 decide +kernel
def pointBounds20240 : List (Nat × Nat × Nat) := [(2656851968,100175477990806,100175858451276),(2656935936,100175884911437,100176265372146)]
theorem point_links_checked20240 : (cuts20240.take 2).map (fun c => (2656829441-1+2*2^9*c.k,100175365055080+c.lower,100175745515484+c.upper)) = pointBounds20240 := by
 decide +kernel
def cuts20241 : List PrefixCut := [⟨58,292281594,292281772⟩,
⟨128,651612773,651613161⟩]
theorem checked20241 : checkPrefixCuts (2^48) 2656960513 9 Manual.Count131072.C020241.packed 128 cuts20241 = true := by
 decide +kernel
def pointBounds20241 : List (Nat × Nat × Nat) := [(2657019904,100176297751804,100176678212762)]
theorem point_links_checked20241 : (cuts20241.take 1).map (fun c => (2656960513-1+2*2^9*c.k,100176005470210+c.lower,100176385930990+c.upper)) = pointBounds20241 := by
 decide +kernel
def cuts20242 : List PrefixCut := [⟨12,59110733,59110769⟩,
⟨94,465992795,465993071⟩,
⟨128,636644287,636644664⟩]
theorem checked20242 : checkPrefixCuts (2^48) 2657091585 9 Manual.Count131072.C020242.packed 128 cuts20242 = true := by
 decide +kernel
def pointBounds20242 : List (Nat × Nat × Nat) := [(2657103872,100176716193716,100177096654920),(2657187840,100177123075778,100177503537222)]
theorem point_links_checked20242 : (cuts20242.take 2).map (fun c => (2657091585-1+2*2^9*c.k,100176657082983+c.lower,100177037544151+c.upper)) = pointBounds20242 := by
 decide +kernel
def cuts20243 : List PrefixCut := [⟨48,244691951,244692093⟩,
⟨128,651336673,651337050⟩]
theorem checked20243 : checkPrefixCuts (2^48) 2657222657 9 Manual.Count131072.C020243.packed 128 cuts20243 = true := by
 decide +kernel
def pointBounds20243 : List (Nat × Nat × Nat) := [(2657271808,100177538419221,100177918880908)]
theorem point_links_checked20243 : (cuts20243.take 1).map (fun c => (2657222657-1+2*2^9*c.k,100177293727270+c.lower,100177674188815+c.upper)) = pointBounds20243 := by
 decide +kernel
def cuts20244 : List PrefixCut := [⟨2,9638990,9638995⟩,
⟨84,412245705,412245950⟩,
⟨128,632238803,632239178⟩]
theorem checked20244 : checkPrefixCuts (2^48) 2657353729 9 Manual.Count131072.C020244.packed 128 cuts20244 = true := by
 decide +kernel
def pointBounds20244 : List (Nat × Nat × Nat) := [(2657355776,100177954702933,100178335164860),(2657439744,100178357309648,100178737771815)]
theorem point_links_checked20244 : (cuts20244.take 2).map (fun c => (2657353729-1+2*2^9*c.k,100177945063943+c.lower,100178325525865+c.upper)) = pointBounds20244 := by
 decide +kernel
def cuts20245 : List PrefixCut := [⟨38,186731670,186731780⟩,
⟨120,595561854,595562201⟩,
⟨128,634749562,634749933⟩]
theorem checked20245 : checkPrefixCuts (2^48) 2657484801 9 Manual.Count131072.C020245.packed 128 cuts20245 = true := by
 decide +kernel
def pointBounds20245 : List (Nat × Nat × Nat) := [(2657523712,100178764034416,100179144496823),(2657607680,100179172864600,100179553327244)]
theorem point_links_checked20245 : (cuts20245.take 2).map (fun c => (2657484801-1+2*2^9*c.k,100178577302746+c.lower,100178957765043+c.upper)) = pointBounds20245 := by
 decide +kernel
def cuts20246 : List PrefixCut := [⟨74,371006366,371006583⟩,
⟨128,643191051,643191434⟩]
theorem checked20246 : checkPrefixCuts (2^48) 2657615873 9 Manual.Count131072.C020246.packed 128 cuts20246 = true := by
 decide +kernel
def pointBounds20246 : List (Nat × Nat × Nat) := [(2657691648,100179583058674,100179963521559)]
theorem point_links_checked20246 : (cuts20246.take 1).map (fun c => (2657615873-1+2*2^9*c.k,100179212052308+c.lower,100179592514976+c.upper)) = pointBounds20246 := by
 decide +kernel
def cuts20247 : List PrefixCut := [⟨28,133760253,133760333⟩,
⟨110,542339939,542340257⟩,
⟨128,631298011,631298381⟩]
theorem checked20247 : checkPrefixCuts (2^48) 2657746945 9 Manual.Count131072.C020247.packed 128 cuts20247 = true := by
 decide +kernel
def pointBounds20247 : List (Nat × Nat × Nat) := [(2657775616,100179989003612,100180369466743),(2657859584,100180397583298,100180778046667)]
theorem point_links_checked20247 : (cuts20247.take 2).map (fun c => (2657746945-1+2*2^9*c.k,100179855243359+c.lower,100180235706410+c.upper)) = pointBounds20247 := by
 decide +kernel
def cuts20248 : List PrefixCut := [⟨64,322256152,322256334⟩,
⟨128,637515097,637515467⟩]
theorem checked20248 : checkPrefixCuts (2^48) 2657878017 9 Manual.Count131072.C020248.packed 128 cuts20248 = true := by
 decide +kernel
def pointBounds20248 : List (Nat × Nat × Nat) := [(2657943552,100180808797522,100181189261125)]
theorem point_links_checked20248 : (cuts20248.take 1).map (fun c => (2657878017-1+2*2^9*c.k,100180486541370+c.lower,100180867004791+c.upper)) = pointBounds20248 := by
 decide +kernel
def cuts20249 : List PrefixCut := [⟨18,86941047,86941102⟩,
⟨100,490187189,490187484⟩,
⟨128,634941870,634942251⟩]
theorem checked20249 : checkPrefixCuts (2^48) 2658009089 9 Manual.Count131072.C020249.packed 128 cuts20249 = true := by
 decide +kernel
def pointBounds20249 : List (Nat × Nat × Nat) := [(2658027520,100181210997514,100181591461360),(2658111488,100181614243656,100181994707742)]
theorem point_links_checked20249 : (cuts20249.take 2).map (fun c => (2658009089-1+2*2^9*c.k,100181124056467+c.lower,100181504520258+c.upper)) = pointBounds20249 := by
 decide +kernel
def cuts20250 : List PrefixCut := [⟨54,272456455,272456615⟩,
⟨128,639040561,639040937⟩]
theorem checked20250 : checkPrefixCuts (2^48) 2658140161 9 Manual.Count131072.C020250.packed 128 cuts20250 = true := by
 decide +kernel
def pointBounds20250 : List (Nat × Nat × Nat) := [(2658195456,100182031454792,100182411919124)]
theorem point_links_checked20250 : (cuts20250.take 1).map (fun c => (2658140161-1+2*2^9*c.k,100181758998337+c.lower,100182139462509+c.upper)) = pointBounds20250 := by
 decide +kernel
def cuts20251 : List PrefixCut := [⟨8,37801404,37801426⟩,
⟨90,448527183,448527449⟩,
⟨128,636785364,636785741⟩]
theorem checked20251 : checkPrefixCuts (2^48) 2658271233 9 Manual.Count131072.C020251.packed 128 cuts20251 = true := by
 decide +kernel
def pointBounds20251 : List (Nat × Nat × Nat) := [(2658279424,100182435840302,100182816304872),(2658363392,100182846566081,100183227030895)]
theorem point_links_checked20251 : (cuts20251.take 2).map (fun c => (2658271233-1+2*2^9*c.k,100182398038898+c.lower,100182778503446+c.upper)) = pointBounds20251 := by
 decide +kernel
def cuts20252 : List PrefixCut := [⟨44,222560467,222560599⟩,
⟨126,634001452,634001824⟩,
⟨128,643000916,643001293⟩]
theorem checked20252 : checkPrefixCuts (2^48) 2658402305 9 Manual.Count131072.C020252.packed 128 cuts20252 = true := by
 decide +kernel
def pointBounds20252 : List (Nat × Nat × Nat) := [(2658447360,100183257384729,100183637849786),(2658531328,100183668825714,100184049291011)]
theorem point_links_checked20252 : (cuts20252.take 2).map (fun c => (2658402305-1+2*2^9*c.k,100183034824262+c.lower,100183415289187+c.upper)) = pointBounds20252 := by
 decide +kernel
def cuts20253 : List PrefixCut := [⟨80,395652547,395652777⟩,
⟨128,635557958,635558326⟩]
theorem checked20253 : checkPrefixCuts (2^48) 2658533377 9 Manual.Count131072.C020253.packed 128 cuts20253 = true := by
 decide +kernel
def pointBounds20253 : List (Nat × Nat × Nat) := [(2658615296,100184073477725,100184453943257)]
theorem point_links_checked20253 : (cuts20253.take 1).map (fun c => (2658533377-1+2*2^9*c.k,100183677825178+c.lower,100184058290480+c.upper)) = pointBounds20253 := by
 decide +kernel
def cuts20254 : List PrefixCut := [⟨34,170450836,170450937⟩,
⟨116,587887344,587887689⟩,
⟨128,644737290,644737667⟩]
theorem checked20254 : checkPrefixCuts (2^48) 2658664449 9 Manual.Count131072.C020254.packed 128 cuts20254 = true := by
 decide +kernel
def pointBounds20254 : List (Nat × Nat × Nat) := [(2658699264,100184483833972,100184864299743),(2658783232,100184901270480,100185281736495)]
theorem point_links_checked20254 : (cuts20254.take 2).map (fun c => (2658664449-1+2*2^9*c.k,100184313383136+c.lower,100184693848806+c.upper)) = pointBounds20254 := by
 decide +kernel
def cuts20255 : List PrefixCut := [⟨70,349881018,349881219⟩,
⟨128,641211941,641212312⟩]
theorem checked20255 : checkPrefixCuts (2^48) 2658795521 9 Manual.Count131072.C020255.packed 128 cuts20255 = true := by
 decide +kernel
def pointBounds20255 : List (Nat × Nat × Nat) := [(2658867200,100185308001444,100185688467692)]
theorem point_links_checked20255 : (cuts20255.take 1).map (fun c => (2658795521-1+2*2^9*c.k,100184958120426+c.lower,100185338586473+c.upper)) = pointBounds20255 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000007
