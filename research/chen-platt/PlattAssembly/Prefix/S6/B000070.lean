import PlattAssemblyKernel
import PlattCertificates.Count131072.C052240
import PlattCertificates.Count131072.C052241
import PlattCertificates.Count131072.C052242
import PlattCertificates.Count131072.C052243
import PlattCertificates.Count131072.C052244
import PlattCertificates.Count131072.C052245
import PlattCertificates.Count131072.C052246
import PlattCertificates.Count131072.C052247
import PlattCertificates.Count131072.C052248
import PlattCertificates.Count131072.C052249
import PlattCertificates.Count131072.C052250
import PlattCertificates.Count131072.C052251
import PlattCertificates.Count131072.C052252
import PlattCertificates.Count131072.C052253
import PlattCertificates.Count131072.C052254
import PlattCertificates.Count131072.C052255
import PlattCertificates.Count131072.C052256
import PlattCertificates.Count131072.C052257
import PlattCertificates.Count131072.C052258
import PlattCertificates.Count131072.C052259
import PlattCertificates.Count131072.C052260
import PlattCertificates.Count131072.C052261
import PlattCertificates.Count131072.C052262
import PlattCertificates.Count131072.C052263
import PlattCertificates.Count131072.C052264
import PlattCertificates.Count131072.C052265
import PlattCertificates.Count131072.C052266
import PlattCertificates.Count131072.C052267
import PlattCertificates.Count131072.C052268
import PlattCertificates.Count131072.C052269
import PlattCertificates.Count131072.C052270
import PlattCertificates.Count131072.C052271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52240 : List PrefixCut := [⟨64,235247193,235247324⟩]
theorem checked52240 : checkPrefixCuts (2^48) 6851133441 10 Manual.Count131072.C052240.packed 64 cuts52240 = true := by
 decide +kernel
def pointBounds52240 : List (Nat × Nat × Nat) := [(6851264512,112201995369201,112202382801217)]
theorem point_links_checked52240 : (cuts52240.take 1).map (fun c => (6851133441-1+2*2^10*c.k,112201760122008+c.lower,112202147553893+c.upper)) = pointBounds52240 := by
 decide +kernel
def cuts52241 : List PrefixCut := [⟨64,234831856,234831992⟩]
theorem checked52241 : checkPrefixCuts (2^48) 6851264513 10 Manual.Count131072.C052241.packed 64 cuts52241 = true := by
 decide +kernel
def cuts52242 : List PrefixCut := [⟨41,151307230,151307317⟩,
⟨64,236306329,236306464⟩]
theorem checked52242 : checkPrefixCuts (2^48) 6851395585 10 Manual.Count131072.C052242.packed 64 cuts52242 = true := by
 decide +kernel
def pointBounds52242 : List (Nat × Nat × Nat) := [(6851479552,112202381508287,112202768940526)]
theorem point_links_checked52242 : (cuts52242.take 1).map (fun c => (6851395585-1+2*2^10*c.k,112202230201057+c.lower,112202617633209+c.upper)) = pointBounds52242 := by
 decide +kernel
def cuts52243 : List PrefixCut := [⟨64,237657506,237657637⟩]
theorem checked52243 : checkPrefixCuts (2^48) 6851526657 10 Manual.Count131072.C052243.packed 64 cuts52243 = true := by
 decide +kernel
def cuts52244 : List PrefixCut := [⟨18,66839070,66839106⟩,
⟨64,237735123,237735257⟩]
theorem checked52244 : checkPrefixCuts (2^48) 6851657729 10 Manual.Count131072.C052244.packed 64 cuts52244 = true := by
 decide +kernel
def pointBounds52244 : List (Nat × Nat × Nat) := [(6851694592,112202771003962,112203158436416)]
theorem point_links_checked52244 : (cuts52244.take 1).map (fun c => (6851657729-1+2*2^10*c.k,112202704164892+c.lower,112203091597310+c.upper)) = pointBounds52244 := by
 decide +kernel
def cuts52245 : List PrefixCut := [⟨59,222941888,222942014⟩,
⟨64,240770496,240770632⟩]
theorem checked52245 : checkPrefixCuts (2^48) 6851788801 10 Manual.Count131072.C052245.packed 64 cuts52245 = true := by
 decide +kernel
def pointBounds52245 : List (Nat × Nat × Nat) := [(6851909632,112203164841903,112203552274581)]
theorem point_links_checked52245 : (cuts52245.take 1).map (fun c => (6851788801-1+2*2^10*c.k,112202941900015+c.lower,112203329332567+c.upper)) = pointBounds52245 := by
 decide +kernel
def cuts52246 : List PrefixCut := [⟨64,234028874,234029006⟩]
theorem checked52246 : checkPrefixCuts (2^48) 6851919873 10 Manual.Count131072.C052246.packed 64 cuts52246 = true := by
 decide +kernel
def cuts52247 : List PrefixCut := [⟨36,133095013,133095086⟩,
⟨64,239693233,239693370⟩]
theorem checked52247 : checkPrefixCuts (2^48) 6852050945 10 Manual.Count131072.C052247.packed 64 cuts52247 = true := by
 decide +kernel
def pointBounds52247 : List (Nat × Nat × Nat) := [(6852124672,112203549794398,112203937227291)]
theorem point_links_checked52247 : (cuts52247.take 1).map (fun c => (6852050945-1+2*2^10*c.k,112203416699385+c.lower,112203804132205+c.upper)) = pointBounds52247 := by
 decide +kernel
def cuts52248 : List PrefixCut := [⟨64,237141842,237141978⟩]
theorem checked52248 : checkPrefixCuts (2^48) 6852182017 10 Manual.Count131072.C052248.packed 64 cuts52248 = true := by
 decide +kernel
def cuts52249 : List PrefixCut := [⟨13,46992404,46992430⟩,
⟨64,237958816,237958949⟩]
theorem checked52249 : checkPrefixCuts (2^48) 6852313089 10 Manual.Count131072.C052249.packed 64 cuts52249 = true := by
 decide +kernel
def pointBounds52249 : List (Nat × Nat × Nat) := [(6852339712,112203940526864,112204327959983)]
theorem point_links_checked52249 : (cuts52249.take 1).map (fun c => (6852313089-1+2*2^10*c.k,112203893534460+c.lower,112204280967553+c.upper)) = pointBounds52249 := by
 decide +kernel
def cuts52250 : List PrefixCut := [⟨54,203409544,203409658⟩,
⟨64,240336730,240336864⟩]
theorem checked52250 : checkPrefixCuts (2^48) 6852444161 10 Manual.Count131072.C052250.packed 64 cuts52250 = true := by
 decide +kernel
def pointBounds52250 : List (Nat × Nat × Nat) := [(6852554752,112204334902820,112204722336160)]
theorem point_links_checked52250 : (cuts52250.take 1).map (fun c => (6852444161-1+2*2^10*c.k,112204131493276+c.lower,112204518926502+c.upper)) = pointBounds52250 := by
 decide +kernel
def cuts52251 : List PrefixCut := [⟨64,237580063,237580202⟩]
theorem checked52251 : checkPrefixCuts (2^48) 6852575233 10 Manual.Count131072.C052251.packed 64 cuts52251 = true := by
 decide +kernel
def cuts52252 : List PrefixCut := [⟨31,115173759,115173823⟩,
⟨64,236589735,236589868⟩]
theorem checked52252 : checkPrefixCuts (2^48) 6852706305 10 Manual.Count131072.C052252.packed 64 cuts52252 = true := by
 decide +kernel
def pointBounds52252 : List (Nat × Nat × Nat) := [(6852769792,112204724583828,112205112017391)]
theorem point_links_checked52252 : (cuts52252.take 1).map (fun c => (6852706305-1+2*2^10*c.k,112204609410069+c.lower,112204996843568+c.upper)) = pointBounds52252 := by
 decide +kernel
def cuts52253 : List PrefixCut := [⟨64,236913802,236913930⟩]
theorem checked52253 : checkPrefixCuts (2^48) 6852837377 10 Manual.Count131072.C052253.packed 64 cuts52253 = true := by
 decide +kernel
def cuts52254 : List PrefixCut := [⟨8,29449611,29449627⟩,
⟨64,239209339,239209477⟩]
theorem checked52254 : checkPrefixCuts (2^48) 6852968449 10 Manual.Count131072.C052254.packed 64 cuts52254 = true := by
 decide +kernel
def pointBounds52254 : List (Nat × Nat × Nat) := [(6852984832,112205112363217,112205499796993)]
theorem point_links_checked52254 : (cuts52254.take 1).map (fun c => (6852968449-1+2*2^10*c.k,112205082913606+c.lower,112205470347366+c.upper)) = pointBounds52254 := by
 decide +kernel
def cuts52255 : List PrefixCut := [⟨49,182196902,182197004⟩,
⟨64,237192240,237192373⟩]
theorem checked52255 : checkPrefixCuts (2^48) 6853099521 10 Manual.Count131072.C052255.packed 64 cuts52255 = true := by
 decide +kernel
def pointBounds52255 : List (Nat × Nat × Nat) := [(6853199872,112205504319847,112205891753847)]
theorem point_links_checked52255 : (cuts52255.take 1).map (fun c => (6853099521-1+2*2^10*c.k,112205322122945+c.lower,112205709556843+c.upper)) = pointBounds52255 := by
 decide +kernel
def cuts52256 : List PrefixCut := [⟨64,237516276,237516409⟩]
theorem checked52256 : checkPrefixCuts (2^48) 6853230593 10 Manual.Count131072.C052256.packed 64 cuts52256 = true := by
 decide +kernel
def cuts52257 : List PrefixCut := [⟨26,95325576,95325631⟩,
⟨64,236484954,236485087⟩]
theorem checked52257 : checkPrefixCuts (2^48) 6853361665 10 Manual.Count131072.C052257.packed 64 cuts52257 = true := by
 decide +kernel
def pointBounds52257 : List (Nat × Nat × Nat) := [(6853414912,112205892157037,112206279591256)]
theorem point_links_checked52257 : (cuts52257.take 1).map (fun c => (6853361665-1+2*2^10*c.k,112205796831461+c.lower,112206184265625+c.upper)) = pointBounds52257 := by
 decide +kernel
def cuts52258 : List PrefixCut := [⟨64,237466110,237466247⟩]
theorem checked52258 : checkPrefixCuts (2^48) 6853492737 10 Manual.Count131072.C052258.packed 64 cuts52258 = true := by
 decide +kernel
def cuts52259 : List PrefixCut := [⟨3,10472718,10472724⟩,
⟨64,234833152,234833286⟩]
theorem checked52259 : checkPrefixCuts (2^48) 6853623809 10 Manual.Count131072.C052259.packed 64 cuts52259 = true := by
 decide +kernel
def pointBounds52259 : List (Nat × Nat × Nat) := [(6853629952,112206281255243,112206668689683)]
theorem point_links_checked52259 : (cuts52259.take 1).map (fun c => (6853623809-1+2*2^10*c.k,112206270782525+c.lower,112206658216959+c.upper)) = pointBounds52259 := by
 decide +kernel
def cuts52260 : List PrefixCut := [⟨44,162754245,162754335⟩,
⟨64,237949849,237949982⟩]
theorem checked52260 : checkPrefixCuts (2^48) 6853754881 10 Manual.Count131072.C052260.packed 64 cuts52260 = true := by
 decide +kernel
def pointBounds52260 : List (Nat × Nat × Nat) := [(6853844992,112206668369922,112207055804580)]
theorem point_links_checked52260 : (cuts52260.take 1).map (fun c => (6853754881-1+2*2^10*c.k,112206505615677+c.lower,112206893050245+c.upper)) = pointBounds52260 := by
 decide +kernel
def cuts52261 : List PrefixCut := [⟨64,235152715,235152851⟩]
theorem checked52261 : checkPrefixCuts (2^48) 6853885953 10 Manual.Count131072.C052261.packed 64 cuts52261 = true := by
 decide +kernel
def cuts52262 : List PrefixCut := [⟨21,78602267,78602313⟩,
⟨64,241267158,241267293⟩]
theorem checked52262 : checkPrefixCuts (2^48) 6854017025 10 Manual.Count131072.C052262.packed 64 cuts52262 = true := by
 decide +kernel
def pointBounds52262 : List (Nat × Nat × Nat) := [(6854060032,112207057320508,112207444755391)]
theorem point_links_checked52262 : (cuts52262.take 1).map (fun c => (6854017025-1+2*2^10*c.k,112206978718241+c.lower,112207366153078+c.upper)) = pointBounds52262 := by
 decide +kernel
def cuts52263 : List PrefixCut := [⟨62,226478829,226478959⟩,
⟨64,233624241,233624375⟩]
theorem checked52263 : checkPrefixCuts (2^48) 6854148097 10 Manual.Count131072.C052263.packed 64 cuts52263 = true := by
 decide +kernel
def pointBounds52263 : List (Nat × Nat × Nat) := [(6854275072,112207446464228,112207833899330)]
theorem point_links_checked52263 : (cuts52263.take 1).map (fun c => (6854148097-1+2*2^10*c.k,112207219985399+c.lower,112207607420371+c.upper)) = pointBounds52263 := by
 decide +kernel
def cuts52264 : List PrefixCut := [⟨64,240354494,240354628⟩]
theorem checked52264 : checkPrefixCuts (2^48) 6854279169 10 Manual.Count131072.C052264.packed 64 cuts52264 = true := by
 decide +kernel
def cuts52265 : List PrefixCut := [⟨39,145245300,145245382⟩,
⟨64,237927100,237927233⟩]
theorem checked52265 : checkPrefixCuts (2^48) 6854410241 10 Manual.Count131072.C052265.packed 64 cuts52265 = true := by
 decide +kernel
def pointBounds52265 : List (Nat × Nat × Nat) := [(6854490112,112207839209434,112208226644756)]
theorem point_links_checked52265 : (cuts52265.take 1).map (fun c => (6854410241-1+2*2^10*c.k,112207693964134+c.lower,112208081399374+c.upper)) = pointBounds52265 := by
 decide +kernel
def cuts52266 : List PrefixCut := [⟨64,232132565,232132701⟩]
theorem checked52266 : checkPrefixCuts (2^48) 6854541313 10 Manual.Count131072.C052266.packed 64 cuts52266 = true := by
 decide +kernel
def cuts52267 : List PrefixCut := [⟨16,58761322,58761356⟩,
⟨64,235454225,235454358⟩]
theorem checked52267 : checkPrefixCuts (2^48) 6854672385 10 Manual.Count131072.C052267.packed 64 cuts52267 = true := by
 decide +kernel
def pointBounds52267 : List (Nat × Nat × Nat) := [(6854705152,112208222785121,112208610220664)]
theorem point_links_checked52267 : (cuts52267.take 1).map (fun c => (6854672385-1+2*2^10*c.k,112208164023799+c.lower,112208551459308+c.upper)) = pointBounds52267 := by
 decide +kernel
def cuts52268 : List PrefixCut := [⟨57,211757149,211757271⟩,
⟨64,236886902,236887038⟩]
theorem checked52268 : checkPrefixCuts (2^48) 6854803457 10 Manual.Count131072.C052268.packed 64 cuts52268 = true := by
 decide +kernel
def pointBounds52268 : List (Nat × Nat × Nat) := [(6854920192,112208611235173,112208998670937)]
theorem point_links_checked52268 : (cuts52268.take 1).map (fun c => (6854803457-1+2*2^10*c.k,112208399478024+c.lower,112208786913666+c.upper)) = pointBounds52268 := by
 decide +kernel
def cuts52269 : List PrefixCut := [⟨64,237744666,237744801⟩]
theorem checked52269 : checkPrefixCuts (2^48) 6854934529 10 Manual.Count131072.C052269.packed 64 cuts52269 = true := by
 decide +kernel
def cuts52270 : List PrefixCut := [⟨34,124988631,124988701⟩,
⟨64,237904352,237904484⟩]
theorem checked52270 : checkPrefixCuts (2^48) 6855065601 10 Manual.Count131072.C052270.packed 64 cuts52270 = true := by
 decide +kernel
def pointBounds52270 : List (Nat × Nat × Nat) := [(6855135232,112208999098223,112209386534206)]
theorem point_links_checked52270 : (cuts52270.take 1).map (fun c => (6855065601-1+2*2^10*c.k,112208874109592+c.lower,112209261545505+c.upper)) = pointBounds52270 := by
 decide +kernel
def cuts52271 : List PrefixCut := [⟨64,234368673,234368804⟩]
theorem checked52271 : checkPrefixCuts (2^48) 6855196673 10 Manual.Count131072.C052271.packed 64 cuts52271 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000070
