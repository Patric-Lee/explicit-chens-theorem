import PlattAssemblyKernel
import PlattCertificates.Count131072.C031248
import PlattCertificates.Count131072.C031249
import PlattCertificates.Count131072.C031250
import PlattCertificates.Count131072.C031251
import PlattCertificates.Count131072.C031252
import PlattCertificates.Count131072.C031253
import PlattCertificates.Count131072.C031254
import PlattCertificates.Count131072.C031255
import PlattCertificates.Count131072.C031256
import PlattCertificates.Count131072.C031257
import PlattCertificates.Count131072.C031258
import PlattCertificates.Count131072.C031259
import PlattCertificates.Count131072.C031260
import PlattCertificates.Count131072.C031261
import PlattCertificates.Count131072.C031262
import PlattCertificates.Count131072.C031263
import PlattCertificates.Count131072.C031264
import PlattCertificates.Count131072.C031265
import PlattCertificates.Count131072.C031266
import PlattCertificates.Count131072.C031267
import PlattCertificates.Count131072.C031268
import PlattCertificates.Count131072.C031269
import PlattCertificates.Count131072.C031270
import PlattCertificates.Count131072.C031271
import PlattCertificates.Count131072.C031272
import PlattCertificates.Count131072.C031273
import PlattCertificates.Count131072.C031274
import PlattCertificates.Count131072.C031275
import PlattCertificates.Count131072.C031276
import PlattCertificates.Count131072.C031277
import PlattCertificates.Count131072.C031278
import PlattCertificates.Count131072.C031279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts31248 : List PrefixCut := [⟨39,123240403,123240470⟩,
⟨128,401505246,401505469⟩]
theorem checked31248 : checkPrefixCuts (2^48) 4099670017 9 Manual.Count131072.C031248.packed 128 cuts31248 = true := by
 decide +kernel
def pointBounds31248 : List (Nat × Nat × Nat) := [(4099709952,105746305097293,105746688710219)]
theorem point_links_checked31248 : (cuts31248.take 1).map (fun c => (4099670017-1+2*2^9*c.k,105746181856890+c.lower,105746565469749+c.upper)) = pointBounds31248 := by
 decide +kernel
def cuts31249 : List PrefixCut := [⟨37,116782891,116782956⟩,
⟨128,405886273,405886504⟩]
theorem checked31249 : checkPrefixCuts (2^48) 4099801089 9 Manual.Count131072.C031249.packed 128 cuts31249 = true := by
 decide +kernel
def pointBounds31249 : List (Nat × Nat × Nat) := [(4099838976,105746700145027,105747083758174)]
theorem point_links_checked31249 : (cuts31249.take 1).map (fun c => (4099801089-1+2*2^9*c.k,105746583362136+c.lower,105746966975218+c.upper)) = pointBounds31249 := by
 decide +kernel
def cuts31250 : List PrefixCut := [⟨35,114650925,114650989⟩,
⟨128,408688071,408688308⟩]
theorem checked31250 : checkPrefixCuts (2^48) 4099932161 9 Manual.Count131072.C031250.packed 128 cuts31250 = true := by
 decide +kernel
def pointBounds31250 : List (Nat × Nat × Nat) := [(4099968000,105747103899334,105747487512711)]
theorem point_links_checked31250 : (cuts31250.take 1).map (fun c => (4099932161-1+2*2^9*c.k,105746989248409+c.lower,105747372861722+c.upper)) = pointBounds31250 := by
 decide +kernel
def cuts31251 : List PrefixCut := [⟨33,101878182,101878240⟩,
⟨128,406203541,406203773⟩]
theorem checked31251 : checkPrefixCuts (2^48) 4100063233 9 Manual.Count131072.C031251.packed 128 cuts31251 = true := by
 decide +kernel
def pointBounds31251 : List (Nat × Nat × Nat) := [(4100097024,105747499814662,105747883428270)]
theorem point_links_checked31251 : (cuts31251.take 1).map (fun c => (4100063233-1+2*2^9*c.k,105747397936480+c.lower,105747781550030+c.upper)) = pointBounds31251 := by
 decide +kernel
def cuts31252 : List PrefixCut := [⟨31,98579815,98579871⟩,
⟨128,402414954,402415176⟩]
theorem checked31252 : checkPrefixCuts (2^48) 4100194305 9 Manual.Count131072.C031252.packed 128 cuts31252 = true := by
 decide +kernel
def pointBounds31252 : List (Nat × Nat × Nat) := [(4100226048,105747902719836,105748286333674)]
theorem point_links_checked31252 : (cuts31252.take 1).map (fun c => (4100194305-1+2*2^9*c.k,105747804140021+c.lower,105748187753803+c.upper)) = pointBounds31252 := by
 decide +kernel
def cuts31253 : List PrefixCut := [⟨29,92535773,92535825⟩,
⟨128,408442900,408443132⟩]
theorem checked31253 : checkPrefixCuts (2^48) 4100325377 9 Manual.Count131072.C031253.packed 128 cuts31253 = true := by
 decide +kernel
def pointBounds31253 : List (Nat × Nat × Nat) := [(4100355072,105748299090748,105748682704804)]
theorem point_links_checked31253 : (cuts31253.take 1).map (fun c => (4100325377-1+2*2^9*c.k,105748206554975+c.lower,105748590168979+c.upper)) = pointBounds31253 := by
 decide +kernel
def cuts31254 : List PrefixCut := [⟨27,83059892,83059942⟩,
⟨128,404723037,404723262⟩]
theorem checked31254 : checkPrefixCuts (2^48) 4100456449 9 Manual.Count131072.C031254.packed 128 cuts31254 = true := by
 decide +kernel
def pointBounds31254 : List (Nat × Nat × Nat) := [(4100484096,105748698057767,105749081672053)]
theorem point_links_checked31254 : (cuts31254.take 1).map (fun c => (4100456449-1+2*2^9*c.k,105748614997875+c.lower,105748998612111+c.upper)) = pointBounds31254 := by
 decide +kernel
def cuts31255 : List PrefixCut := [⟨25,80036992,80037040⟩,
⟨128,407867673,407867909⟩]
theorem checked31255 : checkPrefixCuts (2^48) 4100587521 9 Manual.Count131072.C031255.packed 128 cuts31255 = true := by
 decide +kernel
def pointBounds31255 : List (Nat × Nat × Nat) := [(4100613120,105749099757904,105749483372413)]
theorem point_links_checked31255 : (cuts31255.take 1).map (fun c => (4100587521-1+2*2^9*c.k,105749019720912+c.lower,105749403335373+c.upper)) = pointBounds31255 := by
 decide +kernel
def cuts31256 : List PrefixCut := [⟨23,73239080,73239121⟩,
⟨128,404834524,404834742⟩]
theorem checked31256 : checkPrefixCuts (2^48) 4100718593 9 Manual.Count131072.C031256.packed 128 cuts31256 = true := by
 decide +kernel
def pointBounds31256 : List (Nat × Nat × Nat) := [(4100742144,105749500827665,105749884442403)]
theorem point_links_checked31256 : (cuts31256.take 1).map (fun c => (4100718593-1+2*2^9*c.k,105749427588585+c.lower,105749811203282+c.upper)) = pointBounds31256 := by
 decide +kernel
def cuts31257 : List PrefixCut := [⟨21,67059334,67059371⟩,
⟨128,412852135,412852366⟩]
theorem checked31257 : checkPrefixCuts (2^48) 4100849665 9 Manual.Count131072.C031257.packed 128 cuts31257 = true := by
 decide +kernel
def pointBounds31257 : List (Nat × Nat × Nat) := [(4100871168,105749899482443,105750283097395)]
theorem point_links_checked31257 : (cuts31257.take 1).map (fun c => (4100849665-1+2*2^9*c.k,105749832423109+c.lower,105750216038024+c.upper)) = pointBounds31257 := by
 decide +kernel
def cuts31258 : List PrefixCut := [⟨19,59781813,59781848⟩,
⟨128,406799047,406799276⟩]
theorem checked31258 : checkPrefixCuts (2^48) 4100980737 9 Manual.Count131072.C031258.packed 128 cuts31258 = true := by
 decide +kernel
def pointBounds31258 : List (Nat × Nat × Nat) := [(4101000192,105750305057057,105750688672238)]
theorem point_links_checked31258 : (cuts31258.take 1).map (fun c => (4100980737-1+2*2^9*c.k,105750245275244+c.lower,105750628890390+c.upper)) = pointBounds31258 := by
 decide +kernel
def cuts31259 : List PrefixCut := [⟨17,52298844,52298875⟩,
⟨128,403079860,403080084⟩]
theorem checked31259 : checkPrefixCuts (2^48) 4101111809 9 Manual.Count131072.C031259.packed 128 cuts31259 = true := by
 decide +kernel
def pointBounds31259 : List (Nat × Nat × Nat) := [(4101129216,105750704373135,105751087988541)]
theorem point_links_checked31259 : (cuts31259.take 1).map (fun c => (4101111809-1+2*2^9*c.k,105750652074291+c.lower,105751035689666+c.upper)) = pointBounds31259 := by
 decide +kernel
def cuts31260 : List PrefixCut := [⟨15,47424354,47424383⟩,
⟨128,406841671,406841908⟩]
theorem checked31260 : checkPrefixCuts (2^48) 4101242881 9 Manual.Count131072.C031260.packed 128 cuts31260 = true := by
 decide +kernel
def pointBounds31260 : List (Nat × Nat × Nat) := [(4101258240,105751102578505,105751486194133)]
theorem point_links_checked31260 : (cuts31260.take 1).map (fun c => (4101242881-1+2*2^9*c.k,105751055154151+c.lower,105751438769750+c.upper)) = pointBounds31260 := by
 decide +kernel
def cuts31261 : List PrefixCut := [⟨13,42961945,42961969⟩,
⟨128,409711117,409711346⟩]
theorem checked31261 : checkPrefixCuts (2^48) 4101373953 9 Manual.Count131072.C031261.packed 128 cuts31261 = true := by
 decide +kernel
def pointBounds31261 : List (Nat × Nat × Nat) := [(4101387264,105751504957767,105751888573627)]
theorem point_links_checked31261 : (cuts31261.take 1).map (fun c => (4101373953-1+2*2^9*c.k,105751461995822+c.lower,105751845611658+c.upper)) = pointBounds31261 := by
 decide +kernel
def cuts31262 : List PrefixCut := [⟨11,36029245,36029264⟩,
⟨128,407364695,407364924⟩]
theorem checked31262 : checkPrefixCuts (2^48) 4101505025 9 Manual.Count131072.C031262.packed 128 cuts31262 = true := by
 decide +kernel
def pointBounds31262 : List (Nat × Nat × Nat) := [(4101516288,105751907736184,105752291352268)]
theorem point_links_checked31262 : (cuts31262.take 1).map (fun c => (4101505025-1+2*2^9*c.k,105751871706939+c.lower,105752255323004+c.upper)) = pointBounds31262 := by
 decide +kernel
def cuts31263 : List PrefixCut := [⟨9,26969607,26969623⟩,
⟨128,401861766,401862001⟩]
theorem checked31263 : checkPrefixCuts (2^48) 4101636097 9 Manual.Count131072.C031263.packed 128 cuts31263 = true := by
 decide +kernel
def pointBounds31263 : List (Nat × Nat × Nat) := [(4101645312,105752306041241,105752689657551)]
theorem point_links_checked31263 : (cuts31263.take 1).map (fun c => (4101636097-1+2*2^9*c.k,105752279071634+c.lower,105752662687928+c.upper)) = pointBounds31263 := by
 decide +kernel
def cuts31264 : List PrefixCut := [⟨7,20792700,20792712⟩,
⟨128,398417777,398418003⟩]
theorem checked31264 : checkPrefixCuts (2^48) 4101767169 9 Manual.Count131072.C031264.packed 128 cuts31264 = true := by
 decide +kernel
def pointBounds31264 : List (Nat × Nat × Nat) := [(4101774336,105752701726100,105753085342641)]
theorem point_links_checked31264 : (cuts31264.take 1).map (fun c => (4101767169-1+2*2^9*c.k,105752680933400+c.lower,105753064549929+c.upper)) = pointBounds31264 := by
 decide +kernel
def cuts31265 : List PrefixCut := [⟨5,15782739,15782746⟩,
⟨128,405747390,405747616⟩]
theorem checked31265 : checkPrefixCuts (2^48) 4101898241 9 Manual.Count131072.C031265.packed 128 cuts31265 = true := by
 decide +kernel
def pointBounds31265 : List (Nat × Nat × Nat) := [(4101903360,105753095133916,105753478750678)]
theorem point_links_checked31265 : (cuts31265.take 1).map (fun c => (4101898241-1+2*2^9*c.k,105753079351177+c.lower,105753462967932+c.upper)) = pointBounds31265 := by
 decide +kernel
def cuts31266 : List PrefixCut := [⟨3,9332105,9332111⟩,
⟨128,407312572,407312800⟩]
theorem checked31266 : checkPrefixCuts (2^48) 4102029313 9 Manual.Count131072.C031266.packed 128 cuts31266 = true := by
 decide +kernel
def pointBounds31266 : List (Nat × Nat × Nat) := [(4102032384,105753494430672,105753878047659)]
theorem point_links_checked31266 : (cuts31266.take 1).map (fun c => (4102029313-1+2*2^9*c.k,105753485098567+c.lower,105753868715548+c.upper)) = pointBounds31266 := by
 decide +kernel
def cuts31267 : List PrefixCut := [⟨1,2744650,2744652⟩,
⟨127,404898139,404898370⟩,
⟨128,408054386,408054619⟩]
theorem checked31267 : checkPrefixCuts (2^48) 4102160385 9 Manual.Count131072.C031267.packed 128 cuts31267 = true := by
 decide +kernel
def pointBounds31267 : List (Nat × Nat × Nat) := [(4102161408,105753895155789,105754278773000),(4102290432,105754297309278,105754680926718)]
theorem point_links_checked31267 : (cuts31267.take 2).map (fun c => (4102160385-1+2*2^9*c.k,105753892411139+c.lower,105754276028348+c.upper)) = pointBounds31267 := by
 decide +kernel
def cuts31268 : List PrefixCut := [⟨125,387526189,387526410⟩,
⟨128,397337691,397337918⟩]
theorem checked31268 : checkPrefixCuts (2^48) 4102291457 9 Manual.Count131072.C031268.packed 128 cuts31268 = true := by
 decide +kernel
def pointBounds31268 : List (Nat × Nat × Nat) := [(4102419456,105754687991714,105755071609377)]
theorem point_links_checked31268 : (cuts31268.take 1).map (fun c => (4102291457-1+2*2^9*c.k,105754300465525+c.lower,105754684082967+c.upper)) = pointBounds31268 := by
 decide +kernel
def cuts31269 : List PrefixCut := [⟨123,392934217,392934438⟩,
⟨128,409331941,409332172⟩]
theorem checked31269 : checkPrefixCuts (2^48) 4102422529 9 Manual.Count131072.C031269.packed 128 cuts31269 = true := by
 decide +kernel
def pointBounds31269 : List (Nat × Nat × Nat) := [(4102548480,105755090737433,105755474355323)]
theorem point_links_checked31269 : (cuts31269.take 1).map (fun c => (4102422529-1+2*2^9*c.k,105754697803216+c.lower,105755081420885+c.upper)) = pointBounds31269 := by
 decide +kernel
def cuts31270 : List PrefixCut := [⟨121,384825834,384826056⟩,
⟨128,405202276,405202511⟩]
theorem checked31270 : checkPrefixCuts (2^48) 4102553601 9 Manual.Count131072.C031270.packed 128 cuts31270 = true := by
 decide +kernel
def pointBounds31270 : List (Nat × Nat × Nat) := [(4102677504,105755491960991,105755875579113)]
theorem point_links_checked31270 : (cuts31270.take 1).map (fun c => (4102553601-1+2*2^9*c.k,105755107135157+c.lower,105755490753057+c.upper)) = pointBounds31270 := by
 decide +kernel
def cuts31271 : List PrefixCut := [⟨119,383784632,383784847⟩,
⟨128,411501203,411501434⟩]
theorem checked31271 : checkPrefixCuts (2^48) 4102684673 9 Manual.Count131072.C031271.packed 128 cuts31271 = true := by
 decide +kernel
def pointBounds31271 : List (Nat × Nat × Nat) := [(4102806528,105755896122065,105756279740415)]
theorem point_links_checked31271 : (cuts31271.take 1).map (fun c => (4102684673-1+2*2^9*c.k,105755512337433+c.lower,105755895955568+c.upper)) = pointBounds31271 := by
 decide +kernel
def cuts31272 : List PrefixCut := [⟨117,371835275,371835486⟩,
⟨128,407028716,407028946⟩]
theorem checked31272 : checkPrefixCuts (2^48) 4102815745 9 Manual.Count131072.C031272.packed 128 cuts31272 = true := by
 decide +kernel
def pointBounds31272 : List (Nat × Nat × Nat) := [(4102935552,105756295673911,105756679292488)]
theorem point_links_checked31272 : (cuts31272.take 1).map (fun c => (4102815745-1+2*2^9*c.k,105755923838636+c.lower,105756307457002+c.upper)) = pointBounds31272 := by
 decide +kernel
def cuts31273 : List PrefixCut := [⟨115,367501567,367501773⟩,
⟨128,408113376,408113603⟩]
theorem checked31273 : checkPrefixCuts (2^48) 4102946817 9 Manual.Count131072.C031273.packed 128 cuts31273 = true := by
 decide +kernel
def pointBounds31273 : List (Nat × Nat × Nat) := [(4103064576,105756698368919,105757081987721)]
theorem point_links_checked31273 : (cuts31273.take 1).map (fun c => (4102946817-1+2*2^9*c.k,105756330867352+c.lower,105756714485948+c.upper)) = pointBounds31273 := by
 decide +kernel
def cuts31274 : List PrefixCut := [⟨113,354593026,354593237⟩,
⟨128,401308842,401309082⟩]
theorem checked31274 : checkPrefixCuts (2^48) 4103077889 9 Manual.Count131072.C031274.packed 128 cuts31274 = true := by
 decide +kernel
def pointBounds31274 : List (Nat × Nat × Nat) := [(4103193600,105757093573754,105757477192788)]
theorem point_links_checked31274 : (cuts31274.take 1).map (fun c => (4103077889-1+2*2^9*c.k,105756738980728+c.lower,105757122599551+c.upper)) = pointBounds31274 := by
 decide +kernel
def cuts31275 : List PrefixCut := [⟨111,352043831,352044023⟩,
⟨128,405480642,405480862⟩]
theorem checked31275 : checkPrefixCuts (2^48) 4103208961 9 Manual.Count131072.C031275.packed 128 cuts31275 = true := by
 decide +kernel
def pointBounds31275 : List (Nat × Nat × Nat) := [(4103322624,105757492333401,105757875952656)]
theorem point_links_checked31275 : (cuts31275.take 1).map (fun c => (4103208961-1+2*2^9*c.k,105757140289570+c.lower,105757523908633+c.upper)) = pointBounds31275 := by
 decide +kernel
def cuts31276 : List PrefixCut := [⟨109,345858978,345859177⟩,
⟨128,407251056,407251290⟩]
theorem checked31276 : checkPrefixCuts (2^48) 4103340033 9 Manual.Count131072.C031276.packed 128 cuts31276 = true := by
 decide +kernel
def pointBounds31276 : List (Nat × Nat × Nat) := [(4103451648,105757891629190,105758275248672)]
theorem point_links_checked31276 : (cuts31276.take 1).map (fun c => (4103340033-1+2*2^9*c.k,105757545770212+c.lower,105757929389495+c.upper)) = pointBounds31276 := by
 decide +kernel
def cuts31277 : List PrefixCut := [⟨107,337959819,337960010⟩,
⟨128,406483556,406483784⟩]
theorem checked31277 : checkPrefixCuts (2^48) 4103471105 9 Manual.Count131072.C031277.packed 128 cuts31277 = true := by
 decide +kernel
def pointBounds31277 : List (Nat × Nat × Nat) := [(4103580672,105758290981087,105758674600795)]
theorem point_links_checked31277 : (cuts31277.take 1).map (fun c => (4103471105-1+2*2^9*c.k,105757953021268+c.lower,105758336640785+c.upper)) = pointBounds31277 := by
 decide +kernel
def cuts31278 : List PrefixCut := [⟨105,333559245,333559430⟩,
⟨128,405784687,405784914⟩]
theorem checked31278 : checkPrefixCuts (2^48) 4103602177 9 Manual.Count131072.C031278.packed 128 cuts31278 = true := by
 decide +kernel
def pointBounds31278 : List (Nat × Nat × Nat) := [(4103709696,105758693064069,105759076683999)]
theorem point_links_checked31278 : (cuts31278.take 1).map (fun c => (4103602177-1+2*2^9*c.k,105758359504824+c.lower,105758743124569+c.upper)) = pointBounds31278 := by
 decide +kernel
def cuts31279 : List PrefixCut := [⟨103,329296140,329296328⟩,
⟨128,409269727,409269961⟩]
theorem checked31279 : checkPrefixCuts (2^48) 4103733249 9 Manual.Count131072.C031279.packed 128 cuts31279 = true := by
 decide +kernel
def pointBounds31279 : List (Nat × Nat × Nat) := [(4103838720,105759094585651,105759478205811)]
theorem point_links_checked31279 : (cuts31279.take 1).map (fun c => (4103733249-1+2*2^9*c.k,105758765289511+c.lower,105759148909483+c.upper)) = pointBounds31279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000039
