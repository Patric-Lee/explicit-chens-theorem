import PlattAssemblyKernel
import PlattCertificates.Count131072.C072272
import PlattCertificates.Count131072.C072273
import PlattCertificates.Count131072.C072274
import PlattCertificates.Count131072.C072275
import PlattCertificates.Count131072.C072276
import PlattCertificates.Count131072.C072277
import PlattCertificates.Count131072.C072278
import PlattCertificates.Count131072.C072279
import PlattCertificates.Count131072.C072280
import PlattCertificates.Count131072.C072281
import PlattCertificates.Count131072.C072282
import PlattCertificates.Count131072.C072283
import PlattCertificates.Count131072.C072284
import PlattCertificates.Count131072.C072285
import PlattCertificates.Count131072.C072286
import PlattCertificates.Count131072.C072287
import PlattCertificates.Count131072.C072288
import PlattCertificates.Count131072.C072289
import PlattCertificates.Count131072.C072290
import PlattCertificates.Count131072.C072291
import PlattCertificates.Count131072.C072292
import PlattCertificates.Count131072.C072293
import PlattCertificates.Count131072.C072294
import PlattCertificates.Count131072.C072295
import PlattCertificates.Count131072.C072296
import PlattCertificates.Count131072.C072297
import PlattCertificates.Count131072.C072298
import PlattCertificates.Count131072.C072299
import PlattCertificates.Count131072.C072300
import PlattCertificates.Count131072.C072301
import PlattCertificates.Count131072.C072302
import PlattCertificates.Count131072.C072303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72272 : List PrefixCut := [⟨64,170723450,170723553⟩]
theorem checked72272 : checkPrefixCuts (2^48) 9476767745 10 Manual.Count131072.C072272.packed 64 cuts72272 = true := by
 decide +kernel
def cuts72273 : List PrefixCut := [⟨51,134248488,134248568⟩,
⟨64,167305470,167305568⟩]
theorem checked72273 : checkPrefixCuts (2^48) 9476898817 10 Manual.Count131072.C072273.packed 64 cuts72273 = true := by
 decide +kernel
def pointBounds72273 : List (Nat × Nat × Nat) := [(9477003264,116205541000322,116205930737111)]
theorem point_links_checked72273 : (cuts72273.take 1).map (fun c => (9476898817-1+2*2^10*c.k,116205406751834+c.lower,116205796488543+c.upper)) = pointBounds72273 := by
 decide +kernel
def cuts72274 : List PrefixCut := [⟨64,168758505,168758597⟩]
theorem checked72274 : checkPrefixCuts (2^48) 9477029889 10 Manual.Count131072.C072274.packed 64 cuts72274 = true := by
 decide +kernel
def cuts72275 : List PrefixCut := [⟨64,170508460,170508566⟩]
theorem checked72275 : checkPrefixCuts (2^48) 9477160961 10 Manual.Count131072.C072275.packed 64 cuts72275 = true := by
 decide +kernel
def cuts72276 : List PrefixCut := [⟨4,10870168,10870176⟩,
⟨64,169318121,169318224⟩]
theorem checked72276 : checkPrefixCuts (2^48) 9477292033 10 Manual.Count131072.C072276.packed 64 cuts72276 = true := by
 decide +kernel
def pointBounds72276 : List (Nat × Nat × Nat) := [(9477300224,116205924194437,116206313931450)]
theorem point_links_checked72276 : (cuts72276.take 1).map (fun c => (9477292033-1+2*2^10*c.k,116205913324269+c.lower,116206303061274+c.upper)) = pointBounds72276 := by
 decide +kernel
def cuts72277 : List PrefixCut := [⟨64,171275924,171276025⟩]
theorem checked72277 : checkPrefixCuts (2^48) 9477423105 10 Manual.Count131072.C072277.packed 64 cuts72277 = true := by
 decide +kernel
def cuts72278 : List PrefixCut := [⟨21,56695467,56695501⟩,
⟨64,168749169,168749266⟩]
theorem checked72278 : checkPrefixCuts (2^48) 9477554177 10 Manual.Count131072.C072278.packed 64 cuts72278 = true := by
 decide +kernel
def pointBounds72278 : List (Nat × Nat × Nat) := [(9477597184,116206310613781,116206700351024)]
theorem point_links_checked72278 : (cuts72278.take 1).map (fun c => (9477554177-1+2*2^10*c.k,116206253918314+c.lower,116206643655523+c.upper)) = pointBounds72278 := by
 decide +kernel
def cuts72279 : List PrefixCut := [⟨64,170617823,170617921⟩]
theorem checked72279 : checkPrefixCuts (2^48) 9477685249 10 Manual.Count131072.C072279.packed 64 cuts72279 = true := by
 decide +kernel
def cuts72280 : List PrefixCut := [⟨38,100617373,100617434⟩,
⟨64,170169989,170170091⟩]
theorem checked72280 : checkPrefixCuts (2^48) 9477816321 10 Manual.Count131072.C072280.packed 64 cuts72280 = true := by
 decide +kernel
def pointBounds72280 : List (Nat × Nat × Nat) := [(9477894144,116206693902679,116207083640144)]
theorem point_links_checked72280 : (cuts72280.take 1).map (fun c => (9477816321-1+2*2^10*c.k,116206593285306+c.lower,116206983022710+c.upper)) = pointBounds72280 := by
 decide +kernel
def cuts72281 : List PrefixCut := [⟨64,169603376,169603486⟩]
theorem checked72281 : checkPrefixCuts (2^48) 9477947393 10 Manual.Count131072.C072281.packed 64 cuts72281 = true := by
 decide +kernel
def cuts72282 : List PrefixCut := [⟨55,145783979,145784068⟩,
⟨64,169274371,169274474⟩]
theorem checked72282 : checkPrefixCuts (2^48) 9478078465 10 Manual.Count131072.C072282.packed 64 cuts72282 = true := by
 decide +kernel
def pointBounds72282 : List (Nat × Nat × Nat) := [(9478191104,116207078842650,116207468580355)]
theorem point_links_checked72282 : (cuts72282.take 1).map (fun c => (9478078465-1+2*2^10*c.k,116206933058671+c.lower,116207322796287+c.upper)) = pointBounds72282 := by
 decide +kernel
def cuts72283 : List PrefixCut := [⟨64,168084163,168084271⟩]
theorem checked72283 : checkPrefixCuts (2^48) 9478209537 10 Manual.Count131072.C072283.packed 64 cuts72283 = true := by
 decide +kernel
def cuts72284 : List PrefixCut := [⟨64,170457546,170457651⟩]
theorem checked72284 : checkPrefixCuts (2^48) 9478340609 10 Manual.Count131072.C072284.packed 64 cuts72284 = true := by
 decide +kernel
def cuts72285 : List PrefixCut := [⟨8,21440661,21440674⟩,
⟨64,171494554,171494651⟩]
theorem checked72285 : checkPrefixCuts (2^48) 9478471681 10 Manual.Count131072.C072285.packed 64 cuts72285 = true := by
 decide +kernel
def pointBounds72285 : List (Nat × Nat × Nat) := [(9478488064,116207462315412,116207852053357)]
theorem point_links_checked72285 : (cuts72285.take 1).map (fun c => (9478471681-1+2*2^10*c.k,116207440874751+c.lower,116207830612683+c.upper)) = pointBounds72285 := by
 decide +kernel
def cuts72286 : List PrefixCut := [⟨64,166800284,166800382⟩]
theorem checked72286 : checkPrefixCuts (2^48) 9478602753 10 Manual.Count131072.C072286.packed 64 cuts72286 = true := by
 decide +kernel
def cuts72287 : List PrefixCut := [⟨25,65240643,65240677⟩,
⟨64,166946440,166946538⟩]
theorem checked72287 : checkPrefixCuts (2^48) 9478733825 10 Manual.Count131072.C072287.packed 64 cuts72287 = true := by
 decide +kernel
def pointBounds72287 : List (Nat × Nat × Nat) := [(9478785024,116207844410232,116208234148393)]
theorem point_links_checked72287 : (cuts72287.take 1).map (fun c => (9478733825-1+2*2^10*c.k,116207779169589+c.lower,116208168907716+c.upper)) = pointBounds72287 := by
 decide +kernel
def cuts72288 : List PrefixCut := [⟨64,172229810,172229908⟩]
theorem checked72288 : checkPrefixCuts (2^48) 9478864897 10 Manual.Count131072.C072288.packed 64 cuts72288 = true := by
 decide +kernel
def cuts72289 : List PrefixCut := [⟨42,110819702,110819770⟩,
⟨64,169139211,169139313⟩]
theorem checked72289 : checkPrefixCuts (2^48) 9478995969 10 Manual.Count131072.C072289.packed 64 cuts72289 = true := by
 decide +kernel
def pointBounds72289 : List (Nat × Nat × Nat) := [(9479081984,116208229165541,116208618903932)]
theorem point_links_checked72289 : (cuts72289.take 1).map (fun c => (9478995969-1+2*2^10*c.k,116208118345839+c.lower,116208508084162+c.upper)) = pointBounds72289 := by
 decide +kernel
def cuts72290 : List PrefixCut := [⟨64,167711561,167711663⟩]
theorem checked72290 : checkPrefixCuts (2^48) 9479127041 10 Manual.Count131072.C072290.packed 64 cuts72290 = true := by
 decide +kernel
def cuts72291 : List PrefixCut := [⟨59,156782098,156782188⟩,
⟨64,169461168,169461267⟩]
theorem checked72291 : checkPrefixCuts (2^48) 9479258113 10 Manual.Count131072.C072291.packed 64 cuts72291 = true := by
 decide +kernel
def pointBounds72291 : List (Nat × Nat × Nat) := [(9479378944,116208611978709,116209001717326)]
theorem point_links_checked72291 : (cuts72291.take 1).map (fun c => (9479258113-1+2*2^10*c.k,116208455196611+c.lower,116208844935138+c.upper)) = pointBounds72291 := by
 decide +kernel
def cuts72292 : List PrefixCut := [⟨64,171388875,171388981⟩]
theorem checked72292 : checkPrefixCuts (2^48) 9479389185 10 Manual.Count131072.C072292.packed 64 cuts72292 = true := by
 decide +kernel
def cuts72293 : List PrefixCut := [⟨64,169278320,169278410⟩]
theorem checked72293 : checkPrefixCuts (2^48) 9479520257 10 Manual.Count131072.C072293.packed 64 cuts72293 = true := by
 decide +kernel
def cuts72294 : List PrefixCut := [⟨12,31978822,31978838⟩,
⟨64,169335379,169335477⟩]
theorem checked72294 : checkPrefixCuts (2^48) 9479651329 10 Manual.Count131072.C072294.packed 64 cuts72294 = true := by
 decide +kernel
def pointBounds72294 : List (Nat × Nat × Nat) := [(9479675904,116208997303796,116209387042634)]
theorem point_links_checked72294 : (cuts72294.take 1).map (fun c => (9479651329-1+2*2^10*c.k,116208965324974+c.lower,116209355063796+c.upper)) = pointBounds72294 := by
 decide +kernel
def cuts72295 : List PrefixCut := [⟨64,169600260,169600356⟩]
theorem checked72295 : checkPrefixCuts (2^48) 9479782401 10 Manual.Count131072.C072295.packed 64 cuts72295 = true := by
 decide +kernel
def cuts72296 : List PrefixCut := [⟨29,77732665,77732711⟩,
⟨64,170221428,170221528⟩]
theorem checked72296 : checkPrefixCuts (2^48) 9479913473 10 Manual.Count131072.C072296.packed 64 cuts72296 = true := by
 decide +kernel
def pointBounds72296 : List (Nat × Nat × Nat) := [(9479972864,116209381993278,116209771732340)]
theorem point_links_checked72296 : (cuts72296.take 1).map (fun c => (9479913473-1+2*2^10*c.k,116209304260613+c.lower,116209693999629+c.upper)) = pointBounds72296 := by
 decide +kernel
def cuts72297 : List PrefixCut := [⟨64,170426901,170427001⟩]
theorem checked72297 : checkPrefixCuts (2^48) 9480044545 10 Manual.Count131072.C072297.packed 64 cuts72297 = true := by
 decide +kernel
def cuts72298 : List PrefixCut := [⟨46,120722572,120722643⟩,
⟨64,169355678,169355779⟩]
theorem checked72298 : checkPrefixCuts (2^48) 9480175617 10 Manual.Count131072.C072298.packed 64 cuts72298 = true := by
 decide +kernel
def pointBounds72298 : List (Nat × Nat × Nat) := [(9480269824,116209765631514,116210155370801)]
theorem point_links_checked72298 : (cuts72298.take 1).map (fun c => (9480175617-1+2*2^10*c.k,116209644908942+c.lower,116210034648158+c.upper)) = pointBounds72298 := by
 decide +kernel
def cuts72299 : List PrefixCut := [⟨64,169056443,169056543⟩]
theorem checked72299 : checkPrefixCuts (2^48) 9480306689 10 Manual.Count131072.C072299.packed 64 cuts72299 = true := by
 decide +kernel
def cuts72300 : List PrefixCut := [⟨63,166500810,166500910⟩,
⟨64,169558846,169558947⟩]
theorem checked72300 : checkPrefixCuts (2^48) 9480437761 10 Manual.Count131072.C072300.packed 64 cuts72300 = true := by
 decide +kernel
def pointBounds72300 : List (Nat × Nat × Nat) := [(9480566784,116210149821873,116210539561390)]
theorem point_links_checked72300 : (cuts72300.take 1).map (fun c => (9480437761-1+2*2^10*c.k,116209983321063+c.lower,116210373060480+c.upper)) = pointBounds72300 := by
 decide +kernel
def cuts72301 : List PrefixCut := [⟨64,169111153,169111253⟩]
theorem checked72301 : checkPrefixCuts (2^48) 9480568833 10 Manual.Count131072.C072301.packed 64 cuts72301 = true := by
 decide +kernel
def cuts72302 : List PrefixCut := [⟨64,168485341,168485444⟩]
theorem checked72302 : checkPrefixCuts (2^48) 9480699905 10 Manual.Count131072.C072302.packed 64 cuts72302 = true := by
 decide +kernel
def cuts72303 : List PrefixCut := [⟨16,41267418,41267443⟩,
⟨64,169076783,169076884⟩]
theorem checked72303 : checkPrefixCuts (2^48) 9480830977 10 Manual.Count131072.C072303.packed 64 cuts72303 = true := by
 decide +kernel
def pointBounds72303 : List (Nat × Nat × Nat) := [(9480863744,116210531743821,116210921483567)]
theorem point_links_checked72303 : (cuts72303.take 1).map (fun c => (9480830977-1+2*2^10*c.k,116210490476403+c.lower,116210880216124+c.upper)) = pointBounds72303 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000071
