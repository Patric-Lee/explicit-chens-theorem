import PlattAssemblyKernel
import PlattCertificates.Count131072.C018224
import PlattCertificates.Count131072.C018225
import PlattCertificates.Count131072.C018226
import PlattCertificates.Count131072.C018227
import PlattCertificates.Count131072.C018228
import PlattCertificates.Count131072.C018229
import PlattCertificates.Count131072.C018230
import PlattCertificates.Count131072.C018231
import PlattCertificates.Count131072.C018232
import PlattCertificates.Count131072.C018233
import PlattCertificates.Count131072.C018234
import PlattCertificates.Count131072.C018235
import PlattCertificates.Count131072.C018236
import PlattCertificates.Count131072.C018237
import PlattCertificates.Count131072.C018238
import PlattCertificates.Count131072.C018239
import PlattCertificates.Count131072.C018240
import PlattCertificates.Count131072.C018241
import PlattCertificates.Count131072.C018242
import PlattCertificates.Count131072.C018243
import PlattCertificates.Count131072.C018244
import PlattCertificates.Count131072.C018245
import PlattCertificates.Count131072.C018246
import PlattCertificates.Count131072.C018247
import PlattCertificates.Count131072.C018248
import PlattCertificates.Count131072.C018249
import PlattCertificates.Count131072.C018250
import PlattCertificates.Count131072.C018251
import PlattCertificates.Count131072.C018252
import PlattCertificates.Count131072.C018253
import PlattCertificates.Count131072.C018254
import PlattCertificates.Count131072.C018255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000257
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18224 : List PrefixCut := [⟨56,315401156,315401351⟩,
⟨128,715259118,715259561⟩]
theorem checked18224 : checkPrefixCuts (2^48) 2392588289 9 Manual.Count131072.C018224.packed 128 cuts18224 = true := by
 decide +kernel
def pointBounds18224 : List (Nat × Nat × Nat) := [(2392645632,98813546174216,98813925822965)]
theorem point_links_checked18224 : (cuts18224.take 1).map (fun c => (2392588289-1+2*2^9*c.k,98813230773060+c.lower,98813610421614+c.upper)) = pointBounds18224 := by
 decide +kernel
def cuts18225 : List PrefixCut := [⟨2,11763802,11763809⟩,
⟨76,429019106,429019364⟩,
⟨128,716749227,716749662⟩]
theorem checked18225 : checkPrefixCuts (2^48) 2392719361 9 Manual.Count131072.C018225.packed 128 cuts18225 = true := by
 decide +kernel
def pointBounds18225 : List (Nat × Nat × Nat) := [(2392721408,98813957795980,98814337444984),(2392797184,98814375051284,98814754700539)]
theorem point_links_checked18225 : (cuts18225.take 2).map (fun c => (2392719361-1+2*2^9*c.k,98813946032178+c.lower,98814325681175+c.upper)) = pointBounds18225 := by
 decide +kernel
def cuts18226 : List PrefixCut := [⟨22,121395268,121395343⟩,
⟨96,533330769,533331097⟩,
⟨128,714945292,714945726⟩]
theorem checked18226 : checkPrefixCuts (2^48) 2392850433 9 Manual.Count131072.C018226.packed 128 cuts18226 = true := by
 decide +kernel
def pointBounds18226 : List (Nat × Nat × Nat) := [(2392872960,98814784176673,98815163826180),(2392948736,98815196112174,98815575761934)]
theorem point_links_checked18226 : (cuts18226.take 2).map (fun c => (2392850433-1+2*2^9*c.k,98814662781405+c.lower,98815042430837+c.upper)) = pointBounds18226 := by
 decide +kernel
def cuts18227 : List PrefixCut := [⟨42,237600741,237600882⟩,
⟨116,654450243,654450632⟩,
⟨128,721257862,721258294⟩]
theorem checked18227 : checkPrefixCuts (2^48) 2392981505 9 Manual.Count131072.C018227.packed 128 cuts18227 = true := by
 decide +kernel
def pointBounds18227 : List (Nat × Nat × Nat) := [(2393024512,98815615327438,98815994977445),(2393100288,98816032176940,98816411827195)]
theorem point_links_checked18227 : (cuts18227.take 2).map (fun c => (2392981505-1+2*2^9*c.k,98815377726697+c.lower,98815757376563+c.upper)) = pointBounds18227 := by
 decide +kernel
def cuts18228 : List PrefixCut := [⟨62,338972693,338972903⟩,
⟨128,705340211,705340650⟩]
theorem checked18228 : checkPrefixCuts (2^48) 2393112577 9 Manual.Count131072.C018228.packed 128 cuts18228 = true := by
 decide +kernel
def pointBounds18228 : List (Nat × Nat × Nat) := [(2393176064,98816437957252,98816817607760)]
theorem point_links_checked18228 : (cuts18228.take 1).map (fun c => (2393112577-1+2*2^9*c.k,98816098984559+c.lower,98816478634857+c.upper)) = pointBounds18228 := by
 decide +kernel
def cuts18229 : List PrefixCut := [⟨8,44810211,44810238⟩,
⟨82,469735207,469735487⟩,
⟨128,722943131,722943571⟩]
theorem checked18229 : checkPrefixCuts (2^48) 2393243649 9 Manual.Count131072.C018229.packed 128 cuts18229 = true := by
 decide +kernel
def pointBounds18229 : List (Nat × Nat × Nat) := [(2393251840,98816849134981,98817228785745),(2393327616,98817274059977,98817653710994)]
theorem point_links_checked18229 : (cuts18229.take 2).map (fun c => (2393243649-1+2*2^9*c.k,98816804324770+c.lower,98817183975507+c.upper)) = pointBounds18229 := by
 decide +kernel
def cuts18230 : List PrefixCut := [⟨28,151828251,151828344⟩,
⟨102,564495810,564496153⟩,
⟨128,705498314,705498743⟩]
theorem checked18230 : checkPrefixCuts (2^48) 2393374721 9 Manual.Count131072.C018230.packed 128 cuts18230 = true := by
 decide +kernel
def pointBounds18230 : List (Nat × Nat × Nat) := [(2393403392,98817679096152,98818058747422),(2393479168,98818091763711,98818471415231)]
theorem point_links_checked18230 : (cuts18230.take 2).map (fun c => (2393374721-1+2*2^9*c.k,98817527267901+c.lower,98817906919078+c.upper)) = pointBounds18230 := by
 decide +kernel
def cuts18231 : List PrefixCut := [⟨48,266242322,266242485⟩,
⟨122,681588378,681588788⟩,
⟨128,716395944,716396375⟩]
theorem checked18231 : checkPrefixCuts (2^48) 2393505793 9 Manual.Count131072.C018231.packed 128 cuts18231 = true := by
 decide +kernel
def pointBounds18231 : List (Nat × Nat × Nat) := [(2393554944,98818499008537,98818878660306),(2393630720,98818914354593,98819294006609)]
theorem point_links_checked18231 : (cuts18231.take 2).map (fun c => (2393505793-1+2*2^9*c.k,98818232766215+c.lower,98818612417821+c.upper)) = pointBounds18231 := by
 decide +kernel
def cuts18232 : List PrefixCut := [⟨68,371000402,371000630⟩,
⟨128,704362556,704362990⟩]
theorem checked18232 : checkPrefixCuts (2^48) 2393636865 9 Manual.Count131072.C018232.packed 128 cuts18232 = true := by
 decide +kernel
def pointBounds18232 : List (Nat × Nat × Nat) := [(2393706496,98819320162561,98819699814826)]
theorem point_links_checked18232 : (cuts18232.take 1).map (fun c => (2393636865-1+2*2^9*c.k,98818949162159+c.lower,98819328814196+c.upper)) = pointBounds18232 := by
 decide +kernel
def cuts18233 : List PrefixCut := [⟨14,75490335,75490379⟩,
⟨88,494441971,494442267⟩,
⟨128,714906528,714906957⟩]
theorem checked18233 : checkPrefixCuts (2^48) 2393767937 9 Manual.Count131072.C018233.packed 128 cuts18233 = true := by
 decide +kernel
def pointBounds18233 : List (Nat × Nat × Nat) := [(2393782272,98819729015050,98820108667565),(2393858048,98820147966686,98820527619453)]
theorem point_links_checked18233 : (cuts18233.take 2).map (fun c => (2393767937-1+2*2^9*c.k,98819653524715+c.lower,98820033177186+c.upper)) = pointBounds18233 := by
 decide +kernel
def cuts18234 : List PrefixCut := [⟨34,185422487,185422599⟩,
⟨108,599997330,599997695⟩,
⟨128,712750966,712751401⟩]
theorem checked18234 : checkPrefixCuts (2^48) 2393899009 9 Manual.Count131072.C018234.packed 128 cuts18234 = true := by
 decide +kernel
def pointBounds18234 : List (Nat × Nat × Nat) := [(2393933824,98820553853730,98820933506742),(2394009600,98820968428573,98821348081838)]
theorem point_links_checked18234 : (cuts18234.take 2).map (fun c => (2393899009-1+2*2^9*c.k,98820368431243+c.lower,98820748084143+c.upper)) = pointBounds18234 := by
 decide +kernel
def cuts18235 : List PrefixCut := [⟨54,299104006,299104184⟩,
⟨128,718002605,718003046⟩]
theorem checked18235 : checkPrefixCuts (2^48) 2394030081 9 Manual.Count131072.C018235.packed 128 cuts18235 = true := by
 decide +kernel
def pointBounds18235 : List (Nat × Nat × Nat) := [(2394085376,98821380286215,98821759939728),(2394161152,98821799184814,98822178838590)]
theorem point_links_checked18235 : (cuts18235.take 2).map (fun c => (2394030081-1+2*2^9*c.k,98821081182209+c.lower,98821460835544+c.upper)) = pointBounds18235 := by
 decide +kernel
def cuts18236 : List PrefixCut := [⟨74,420061098,420061347⟩,
⟨128,722666053,722666487⟩]
theorem checked18236 : checkPrefixCuts (2^48) 2394161153 9 Manual.Count131072.C018236.packed 128 cuts18236 = true := by
 decide +kernel
def pointBounds18236 : List (Nat × Nat × Nat) := [(2394236928,98822219245912,98822598899937)]
theorem point_links_checked18236 : (cuts18236.take 1).map (fun c => (2394161153-1+2*2^9*c.k,98821799184814+c.lower,98822178838590+c.upper)) = pointBounds18236 := by
 decide +kernel
def cuts18237 : List PrefixCut := [⟨20,113210559,113210625⟩,
⟨94,520783890,520784208⟩,
⟨128,706756242,706756675⟩]
theorem checked18237 : checkPrefixCuts (2^48) 2394292225 9 Manual.Count131072.C018237.packed 128 cuts18237 = true := by
 decide +kernel
def pointBounds18237 : List (Nat × Nat × Nat) := [(2394312704,98822635061426,98823014715702),(2394388480,98823042634757,98823422289285)]
theorem point_links_checked18237 : (cuts18237.take 2).map (fun c => (2394292225-1+2*2^9*c.k,98822521850867+c.lower,98822901505077+c.upper)) = pointBounds18237 := by
 decide +kernel
def cuts18238 : List PrefixCut := [⟨40,227113088,227113223⟩,
⟨114,638069556,638069946⟩,
⟨128,719060322,719060762⟩]
theorem checked18238 : checkPrefixCuts (2^48) 2394423297 9 Manual.Count131072.C018238.packed 128 cuts18238 = true := by
 decide +kernel
def pointBounds18238 : List (Nat × Nat × Nat) := [(2394464256,98823455720197,98823835374975),(2394540032,98823866676665,98824246331698)]
theorem point_links_checked18238 : (cuts18238.take 2).map (fun c => (2394423297-1+2*2^9*c.k,98823228607109+c.lower,98823608261752+c.upper)) = pointBounds18238 := by
 decide +kernel
def cuts18239 : List PrefixCut := [⟨60,329600142,329600337⟩,
⟨128,709499782,709500209⟩]
theorem checked18239 : checkPrefixCuts (2^48) 2394554369 9 Manual.Count131072.C018239.packed 128 cuts18239 = true := by
 decide +kernel
def pointBounds18239 : List (Nat × Nat × Nat) := [(2394615808,98824277267573,98824656922851)]
theorem point_links_checked18239 : (cuts18239.take 1).map (fun c => (2394554369-1+2*2^9*c.k,98823947667431+c.lower,98824327322514+c.upper)) = pointBounds18239 := by
 decide +kernel
def cuts18240 : List PrefixCut := [⟨6,32794031,32794052⟩,
⟨80,444769358,444769622⟩,
⟨128,715220280,715220710⟩]
theorem checked18240 : checkPrefixCuts (2^48) 2394685441 9 Manual.Count131072.C018240.packed 128 cuts18240 = true := by
 decide +kernel
def pointBounds18240 : List (Nat × Nat × Nat) := [(2394691584,98824689961244,98825069616775),(2394767360,98825101936571,98825481592345)]
theorem point_links_checked18240 : (cuts18240.take 2).map (fun c => (2394685441-1+2*2^9*c.k,98824657167213+c.lower,98825036822723+c.upper)) = pointBounds18240 := by
 decide +kernel
def cuts18241 : List PrefixCut := [⟨26,144449781,144449867⟩,
⟨100,546173766,546174100⟩,
⟨128,706483762,706484191⟩]
theorem checked18241 : checkPrefixCuts (2^48) 2394816513 9 Manual.Count131072.C018241.packed 128 cuts18241 = true := by
 decide +kernel
def pointBounds18241 : List (Nat × Nat × Nat) := [(2394843136,98825516837274,98825896493300),(2394918912,98825918561259,98826298217533)]
theorem point_links_checked18241 : (cuts18241.take 2).map (fun c => (2394816513-1+2*2^9*c.k,98825372387493+c.lower,98825752043433+c.upper)) = pointBounds18241 := by
 decide +kernel
def cuts18242 : List PrefixCut := [⟨46,257150118,257150276⟩,
⟨120,663197052,663197459⟩,
⟨128,709148308,709148742⟩]
theorem checked18242 : checkPrefixCuts (2^48) 2394947585 9 Manual.Count131072.C018242.packed 128 cuts18242 = true := by
 decide +kernel
def pointBounds18242 : List (Nat × Nat × Nat) := [(2394994688,98826336021373,98826715677900),(2395070464,98826742068307,98827121725083)]
theorem point_links_checked18242 : (cuts18242.take 2).map (fun c => (2394947585-1+2*2^9*c.k,98826078871255+c.lower,98826458527624+c.upper)) = pointBounds18242 := by
 decide +kernel
def cuts18243 : List PrefixCut := [⟨66,375008041,375008264⟩,
⟨128,714985654,714986084⟩]
theorem checked18243 : checkPrefixCuts (2^48) 2395078657 9 Manual.Count131072.C018243.packed 128 cuts18243 = true := by
 decide +kernel
def pointBounds18243 : List (Nat × Nat × Nat) := [(2395146240,98827163027604,98827542684630)]
theorem point_links_checked18243 : (cuts18243.take 1).map (fun c => (2395078657-1+2*2^9*c.k,98826788019563+c.lower,98827167676366+c.upper)) = pointBounds18243 := by
 decide +kernel
def cuts18244 : List PrefixCut := [⟨12,68158967,68159008⟩,
⟨86,482980854,482981151⟩,
⟨128,717296570,717297011⟩]
theorem checked18244 : checkPrefixCuts (2^48) 2395209729 9 Manual.Count131072.C018244.packed 128 cuts18244 = true := by
 decide +kernel
def pointBounds18244 : List (Nat × Nat × Nat) := [(2395222016,98827571164184,98827950821458),(2395297792,98827985986071,98828365643601)]
theorem point_links_checked18244 : (cuts18244.take 2).map (fun c => (2395209729-1+2*2^9*c.k,98827503005217+c.lower,98827882662450+c.upper)) = pointBounds18244 := by
 decide +kernel
def cuts18245 : List PrefixCut := [⟨32,178730479,178730589⟩,
⟨106,590353493,590353853⟩,
⟨128,714202130,714202567⟩]
theorem checked18245 : checkPrefixCuts (2^48) 2395340801 9 Manual.Count131072.C018245.packed 128 cuts18245 = true := by
 decide +kernel
def pointBounds18245 : List (Nat × Nat × Nat) := [(2395373568,98828399032266,98828778690050),(2395449344,98828810655280,98829190313314)]
theorem point_links_checked18245 : (cuts18245.take 2).map (fun c => (2395340801-1+2*2^9*c.k,98828220301787+c.lower,98828599959461+c.upper)) = pointBounds18245 := by
 decide +kernel
def cuts18246 : List PrefixCut := [⟨52,292226403,292226581⟩,
⟨126,708288250,708288684⟩,
⟨128,719332923,719333364⟩]
theorem checked18246 : checkPrefixCuts (2^48) 2395471873 9 Manual.Count131072.C018246.packed 128 cuts18246 = true := by
 decide +kernel
def pointBounds18246 : List (Nat × Nat × Nat) := [(2395525120,98829226730320,98829606388609),(2395600896,98829642792167,98830022450712)]
theorem point_links_checked18246 : (cuts18246.take 2).map (fun c => (2395471873-1+2*2^9*c.k,98828934503917+c.lower,98829314162028+c.upper)) = pointBounds18246 := by
 decide +kernel
def cuts18247 : List PrefixCut := [⟨72,392432162,392432406⟩,
⟨128,698732375,698732805⟩]
theorem checked18247 : checkPrefixCuts (2^48) 2395602945 9 Manual.Count131072.C018247.packed 128 cuts18247 = true := by
 decide +kernel
def pointBounds18247 : List (Nat × Nat × Nat) := [(2395676672,98830046269002,98830425927798)]
theorem point_links_checked18247 : (cuts18247.take 1).map (fun c => (2395602945-1+2*2^9*c.k,98829653836840+c.lower,98830033495392+c.upper)) = pointBounds18247 := by
 decide +kernel
def cuts18248 : List PrefixCut := [⟨18,100923552,100923613⟩,
⟨92,515066306,515066621⟩,
⟨128,713027736,713028169⟩]
theorem checked18248 : checkPrefixCuts (2^48) 2395734017 9 Manual.Count131072.C018248.packed 128 cuts18248 = true := by
 decide +kernel
def pointBounds18248 : List (Nat × Nat × Nat) := [(2395752448,98830453492767,98830833151810),(2395828224,98830867635521,98831247294818)]
theorem point_links_checked18248 : (cuts18248.take 2).map (fun c => (2395734017-1+2*2^9*c.k,98830352569215+c.lower,98830732228197+c.upper)) = pointBounds18248 := by
 decide +kernel
def cuts18249 : List PrefixCut := [⟨38,209941555,209941679⟩,
⟨112,628052333,628052710⟩,
⟨128,718392594,718393026⟩]
theorem checked18249 : checkPrefixCuts (2^48) 2395865089 9 Manual.Count131072.C018249.packed 128 cuts18249 = true := by
 decide +kernel
def pointBounds18249 : List (Nat × Nat × Nat) := [(2395904000,98831275538506,98831655198045),(2395979776,98831693649284,98832073309076)]
theorem point_links_checked18249 : (cuts18249.take 2).map (fun c => (2395865089-1+2*2^9*c.k,98831065596951+c.lower,98831445256366+c.upper)) = pointBounds18249 := by
 decide +kernel
def cuts18250 : List PrefixCut := [⟨58,317301960,317302152⟩,
⟨128,708720407,708720839⟩]
theorem checked18250 : checkPrefixCuts (2^48) 2395996161 9 Manual.Count131072.C018250.packed 128 cuts18250 = true := by
 decide +kernel
def pointBounds18250 : List (Nat × Nat × Nat) := [(2396055552,98832101291505,98832480951544)]
theorem point_links_checked18250 : (cuts18250.take 1).map (fun c => (2395996161-1+2*2^9*c.k,98831783989545+c.lower,98832163649392+c.upper)) = pointBounds18250 := by
 decide +kernel
def cuts18251 : List PrefixCut := [⟨4,21262188,21262202⟩,
⟨78,422652711,422652974⟩,
⟨128,705862300,705862736⟩]
theorem checked18251 : checkPrefixCuts (2^48) 2396127233 9 Manual.Count131072.C018251.packed 128 cuts18251 = true := by
 decide +kernel
def pointBounds18251 : List (Nat × Nat × Nat) := [(2396131328,98832513972140,98832893632433),(2396207104,98832915362663,98833295023205)]
theorem point_links_checked18251 : (cuts18251.take 2).map (fun c => (2396127233-1+2*2^9*c.k,98832492709952+c.lower,98832872370231+c.upper)) = pointBounds18251 := by
 decide +kernel
def cuts18252 : List PrefixCut := [⟨24,136140466,136140550⟩,
⟨98,542791311,542791645⟩,
⟨128,710404816,710405253⟩]
theorem checked18252 : checkPrefixCuts (2^48) 2396258305 9 Manual.Count131072.C018252.packed 128 cuts18252 = true := by
 decide +kernel
def pointBounds18252 : List (Nat × Nat × Nat) := [(2396282880,98833334712718,98833714373517),(2396358656,98833741363563,98834121024612)]
theorem point_links_checked18252 : (cuts18252.take 2).map (fun c => (2396258305-1+2*2^9*c.k,98833198572252+c.lower,98833578232967+c.upper)) = pointBounds18252 := by
 decide +kernel
def cuts18253 : List PrefixCut := [⟨44,238789658,238789805⟩,
⟨118,644240335,644240723⟩,
⟨128,700617171,700617594⟩]
theorem checked18253 : checkPrefixCuts (2^48) 2396389377 9 Manual.Count131072.C018253.packed 128 cuts18253 = true := by
 decide +kernel
def pointBounds18253 : List (Nat × Nat × Nat) := [(2396434432,98834147766726,98834527428025),(2396510208,98834553217403,98834932878943)]
theorem point_links_checked18253 : (cuts18253.take 2).map (fun c => (2396389377-1+2*2^9*c.k,98833908977068+c.lower,98834288638220+c.upper)) = pointBounds18253 := by
 decide +kernel
def cuts18254 : List PrefixCut := [⟨64,356108084,356108300⟩,
⟨128,708330671,708331099⟩]
theorem checked18254 : checkPrefixCuts (2^48) 2396520449 9 Manual.Count131072.C018254.packed 128 cuts18254 = true := by
 decide +kernel
def pointBounds18254 : List (Nat × Nat × Nat) := [(2396585984,98834965702323,98835345364114)]
theorem point_links_checked18254 : (cuts18254.take 1).map (fun c => (2396520449-1+2*2^9*c.k,98834609594239+c.lower,98834989255814+c.upper)) = pointBounds18254 := by
 decide +kernel
def cuts18255 : List PrefixCut := [⟨10,56138614,56138651⟩,
⟨84,472707879,472708168⟩,
⟨128,722384774,722385212⟩]
theorem checked18255 : checkPrefixCuts (2^48) 2396651521 9 Manual.Count131072.C018255.packed 128 cuts18255 = true := by
 decide +kernel
def pointBounds18255 : List (Nat × Nat × Nat) := [(2396661760,98835374063524,98835753725564),(2396737536,98835790632789,98836170295081)]
theorem point_links_checked18255 : (cuts18255.take 2).map (fun c => (2396651521-1+2*2^9*c.k,98835317924910+c.lower,98835697586913+c.upper)) = pointBounds18255 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000257
