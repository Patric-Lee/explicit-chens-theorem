import PlattAssemblyKernel
import PlattCertificates.Count131072.C074256
import PlattCertificates.Count131072.C074257
import PlattCertificates.Count131072.C074258
import PlattCertificates.Count131072.C074259
import PlattCertificates.Count131072.C074260
import PlattCertificates.Count131072.C074261
import PlattCertificates.Count131072.C074262
import PlattCertificates.Count131072.C074263
import PlattCertificates.Count131072.C074264
import PlattCertificates.Count131072.C074265
import PlattCertificates.Count131072.C074266
import PlattCertificates.Count131072.C074267
import PlattCertificates.Count131072.C074268
import PlattCertificates.Count131072.C074269
import PlattCertificates.Count131072.C074270
import PlattCertificates.Count131072.C074271
import PlattCertificates.Count131072.C074272
import PlattCertificates.Count131072.C074273
import PlattCertificates.Count131072.C074274
import PlattCertificates.Count131072.C074275
import PlattCertificates.Count131072.C074276
import PlattCertificates.Count131072.C074277
import PlattCertificates.Count131072.C074278
import PlattCertificates.Count131072.C074279
import PlattCertificates.Count131072.C074280
import PlattCertificates.Count131072.C074281
import PlattCertificates.Count131072.C074282
import PlattCertificates.Count131072.C074283
import PlattCertificates.Count131072.C074284
import PlattCertificates.Count131072.C074285
import PlattCertificates.Count131072.C074286
import PlattCertificates.Count131072.C074287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000133
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74256 : List PrefixCut := [⟨64,165470084,165470179⟩]
theorem checked74256 : checkPrefixCuts (2^48) 9736814593 10 Manual.Count131072.C074256.packed 64 cuts74256 = true := by
 decide +kernel
def cuts74257 : List PrefixCut := [⟨5,13095283,13095291⟩,
⟨64,165583480,165583576⟩]
theorem checked74257 : checkPrefixCuts (2^48) 9736945665 10 Manual.Count131072.C074257.packed 64 cuts74257 = true := by
 decide +kernel
def pointBounds74257 : List (Nat × Nat × Nat) := [(9736955904,116536972811382,116537362745778)]
theorem point_links_checked74257 : (cuts74257.take 1).map (fun c => (9736945665-1+2*2^10*c.k,116536959716099+c.lower,116537349650487+c.upper)) = pointBounds74257 := by
 decide +kernel
def cuts74258 : List PrefixCut := [⟨64,164569495,164569588⟩]
theorem checked74258 : checkPrefixCuts (2^48) 9737076737 10 Manual.Count131072.C074258.packed 64 cuts74258 = true := by
 decide +kernel
def cuts74259 : List PrefixCut := [⟨26,66717509,66717554⟩,
⟨64,164364931,164365034⟩]
theorem checked74259 : checkPrefixCuts (2^48) 9737207809 10 Manual.Count131072.C074259.packed 64 cuts74259 = true := by
 decide +kernel
def pointBounds74259 : List (Nat × Nat × Nat) := [(9737261056,116537356586583,116537746521205)]
theorem point_links_checked74259 : (cuts74259.take 1).map (fun c => (9737207809-1+2*2^10*c.k,116537289869074+c.lower,116537679803651+c.upper)) = pointBounds74259 := by
 decide +kernel
def cuts74260 : List PrefixCut := [⟨64,165172109,165172204⟩]
theorem checked74260 : checkPrefixCuts (2^48) 9737338881 10 Manual.Count131072.C074260.packed 64 cuts74260 = true := by
 decide +kernel
def cuts74261 : List PrefixCut := [⟨47,119585054,119585125⟩,
⟨64,163348783,163348881⟩]
theorem checked74261 : checkPrefixCuts (2^48) 9737469953 10 Manual.Count131072.C074261.packed 64 cuts74261 = true := by
 decide +kernel
def pointBounds74261 : List (Nat × Nat × Nat) := [(9737566208,116537738991168,116538128926014)]
theorem point_links_checked74261 : (cuts74261.take 1).map (fun c => (9737469953-1+2*2^10*c.k,116537619406114+c.lower,116538009340889+c.upper)) = pointBounds74261 := by
 decide +kernel
def cuts74262 : List PrefixCut := [⟨64,166815285,166815382⟩]
theorem checked74262 : checkPrefixCuts (2^48) 9737601025 10 Manual.Count131072.C074262.packed 64 cuts74262 = true := by
 decide +kernel
def cuts74263 : List PrefixCut := [⟨64,164818561,164818661⟩]
theorem checked74263 : checkPrefixCuts (2^48) 9737732097 10 Manual.Count131072.C074263.packed 64 cuts74263 = true := by
 decide +kernel
def cuts74264 : List PrefixCut := [⟨4,10290247,10290254⟩,
⟨64,165625686,165625787⟩]
theorem checked74264 : checkPrefixCuts (2^48) 9737863169 10 Manual.Count131072.C074264.packed 64 cuts74264 = true := by
 decide +kernel
def pointBounds74264 : List (Nat × Nat × Nat) := [(9737871360,116538124678990,116538514614067)]
theorem point_links_checked74264 : (cuts74264.take 1).map (fun c => (9737863169-1+2*2^10*c.k,116538114388743+c.lower,116538504323813+c.upper)) = pointBounds74264 := by
 decide +kernel
def cuts74265 : List PrefixCut := [⟨64,164900837,164900939⟩]
theorem checked74265 : checkPrefixCuts (2^48) 9737994241 10 Manual.Count131072.C074265.packed 64 cuts74265 = true := by
 decide +kernel
def cuts74266 : List PrefixCut := [⟨25,64398884,64398923⟩,
⟨64,163684649,163684742⟩]
theorem checked74266 : checkPrefixCuts (2^48) 9738125313 10 Manual.Count131072.C074266.packed 64 cuts74266 = true := by
 decide +kernel
def pointBounds74266 : List (Nat × Nat × Nat) := [(9738176512,116538509314150,116538899249462)]
theorem point_links_checked74266 : (cuts74266.take 1).map (fun c => (9738125313-1+2*2^10*c.k,116538444915266+c.lower,116538834850539+c.upper)) = pointBounds74266 := by
 decide +kernel
def cuts74267 : List PrefixCut := [⟨64,165272160,165272256⟩]
theorem checked74267 : checkPrefixCuts (2^48) 9738256385 10 Manual.Count131072.C074267.packed 64 cuts74267 = true := by
 decide +kernel
def cuts74268 : List PrefixCut := [⟨46,120845560,120845627⟩,
⟨64,167697827,167697925⟩]
theorem checked74268 : checkPrefixCuts (2^48) 9738387457 10 Manual.Count131072.C074268.packed 64 cuts74268 = true := by
 decide +kernel
def pointBounds74268 : List (Nat × Nat × Nat) := [(9738481664,116538894717635,116539284653164)]
theorem point_links_checked74268 : (cuts74268.take 1).map (fun c => (9738387457-1+2*2^10*c.k,116538773872075+c.lower,116539163807537+c.upper)) = pointBounds74268 := by
 decide +kernel
def cuts74269 : List PrefixCut := [⟨64,164198292,164198388⟩]
theorem checked74269 : checkPrefixCuts (2^48) 9738518529 10 Manual.Count131072.C074269.packed 64 cuts74269 = true := by
 decide +kernel
def cuts74270 : List PrefixCut := [⟨64,163502417,163502521⟩]
theorem checked74270 : checkPrefixCuts (2^48) 9738649601 10 Manual.Count131072.C074270.packed 64 cuts74270 = true := by
 decide +kernel
def cuts74271 : List PrefixCut := [⟨3,8005985,8005988⟩,
⟨64,162517547,162517648⟩]
theorem checked74271 : checkPrefixCuts (2^48) 9738780673 10 Manual.Count131072.C074271.packed 64 cuts74271 = true := by
 decide +kernel
def pointBounds74271 : List (Nat × Nat × Nat) := [(9738786816,116539277276596,116539667212359)]
theorem point_links_checked74271 : (cuts74271.take 1).map (fun c => (9738780673-1+2*2^10*c.k,116539269270611+c.lower,116539659206371+c.upper)) = pointBounds74271 := by
 decide +kernel
def cuts74272 : List PrefixCut := [⟨64,163498012,163498117⟩]
theorem checked74272 : checkPrefixCuts (2^48) 9738911745 10 Manual.Count131072.C074272.packed 64 cuts74272 = true := by
 decide +kernel
def cuts74273 : List PrefixCut := [⟨24,63207856,63207894⟩,
⟨64,166125858,166125955⟩]
theorem checked74273 : checkPrefixCuts (2^48) 9739042817 10 Manual.Count131072.C074273.packed 64 cuts74273 = true := by
 decide +kernel
def pointBounds74273 : List (Nat × Nat × Nat) := [(9739091968,116539658494026,116540048430030)]
theorem point_links_checked74273 : (cuts74273.take 1).map (fun c => (9739042817-1+2*2^10*c.k,116539595286170+c.lower,116539985222136+c.upper)) = pointBounds74273 := by
 decide +kernel
def cuts74274 : List PrefixCut := [⟨64,165979124,165979217⟩]
theorem checked74274 : checkPrefixCuts (2^48) 9739173889 10 Manual.Count131072.C074274.packed 64 cuts74274 = true := by
 decide +kernel
def cuts74275 : List PrefixCut := [⟨45,115111824,115111895⟩,
⟨64,163635915,163636019⟩]
theorem checked74275 : checkPrefixCuts (2^48) 9739304961 10 Manual.Count131072.C074275.packed 64 cuts74275 = true := by
 decide +kernel
def pointBounds74275 : List (Nat × Nat × Nat) := [(9739397120,116540042502976,116540432439203)]
theorem point_links_checked74275 : (cuts74275.take 1).map (fun c => (9739304961-1+2*2^10*c.k,116539927391152+c.lower,116540317327308+c.upper)) = pointBounds74275 := by
 decide +kernel
def cuts74276 : List PrefixCut := [⟨64,162737799,162737894⟩]
theorem checked74276 : checkPrefixCuts (2^48) 9739436033 10 Manual.Count131072.C074276.packed 64 cuts74276 = true := by
 decide +kernel
def cuts74277 : List PrefixCut := [⟨64,165538912,165539014⟩]
theorem checked74277 : checkPrefixCuts (2^48) 9739567105 10 Manual.Count131072.C074277.packed 64 cuts74277 = true := by
 decide +kernel
def cuts74278 : List PrefixCut := [⟨2,5115256,5115259⟩,
⟨64,163542614,163542711⟩]
theorem checked74278 : checkPrefixCuts (2^48) 9739698177 10 Manual.Count131072.C074278.packed 64 cuts74278 = true := by
 decide +kernel
def pointBounds74278 : List (Nat × Nat × Nat) := [(9739702272,116540424419034,116540814355494)]
theorem point_links_checked74278 : (cuts74278.take 1).map (fun c => (9739698177-1+2*2^10*c.k,116540419303778+c.lower,116540809240235+c.upper)) = pointBounds74278 := by
 decide +kernel
def cuts74279 : List PrefixCut := [⟨64,163309223,163309322⟩]
theorem checked74279 : checkPrefixCuts (2^48) 9739829249 10 Manual.Count131072.C074279.packed 64 cuts74279 = true := by
 decide +kernel
def cuts74280 : List PrefixCut := [⟨23,58404693,58404727⟩,
⟨64,164578563,164578662⟩]
theorem checked74280 : checkPrefixCuts (2^48) 9739960321 10 Manual.Count131072.C074280.packed 64 cuts74280 = true := by
 decide +kernel
def pointBounds74280 : List (Nat × Nat × Nat) := [(9740007424,116540804560308,116541194496995)]
theorem point_links_checked74280 : (cuts74280.take 1).map (fun c => (9739960321-1+2*2^10*c.k,116540746155615+c.lower,116541136092268+c.upper)) = pointBounds74280 := by
 decide +kernel
def cuts74281 : List PrefixCut := [⟨64,164518559,164518653⟩]
theorem checked74281 : checkPrefixCuts (2^48) 9740091393 10 Manual.Count131072.C074281.packed 64 cuts74281 = true := by
 decide +kernel
def cuts74282 : List PrefixCut := [⟨44,113569402,113569466⟩,
⟨64,164603040,164603136⟩]
theorem checked74282 : checkPrefixCuts (2^48) 9740222465 10 Manual.Count131072.C074282.packed 64 cuts74282 = true := by
 decide +kernel
def pointBounds74282 : List (Nat × Nat × Nat) := [(9740312576,116541188822139,116541578759049)]
theorem point_links_checked74282 : (cuts74282.take 1).map (fun c => (9740222465-1+2*2^10*c.k,116541075252737+c.lower,116541465189583+c.upper)) = pointBounds74282 := by
 decide +kernel
def cuts74283 : List PrefixCut := [⟨64,165698932,165699034⟩]
theorem checked74283 : checkPrefixCuts (2^48) 9740353537 10 Manual.Count131072.C074283.packed 64 cuts74283 = true := by
 decide +kernel
def cuts74284 : List PrefixCut := [⟨64,162315718,162315819⟩]
theorem checked74284 : checkPrefixCuts (2^48) 9740484609 10 Manual.Count131072.C074284.packed 64 cuts74284 = true := by
 decide +kernel
def cuts74285 : List PrefixCut := [⟨1,2456248,2456249⟩,
⟨64,164596396,164596490⟩]
theorem checked74285 : checkPrefixCuts (2^48) 9740615681 10 Manual.Count131072.C074285.packed 64 cuts74285 = true := by
 decide +kernel
def pointBounds74285 : List (Nat × Nat × Nat) := [(9740617728,116541570326675,116541960263821)]
theorem point_links_checked74285 : (cuts74285.take 1).map (fun c => (9740615681-1+2*2^10*c.k,116541567870427+c.lower,116541957807572+c.upper)) = pointBounds74285 := by
 decide +kernel
def cuts74286 : List PrefixCut := [⟨64,164160735,164160834⟩]
theorem checked74286 : checkPrefixCuts (2^48) 9740746753 10 Manual.Count131072.C074286.packed 64 cuts74286 = true := by
 decide +kernel
def cuts74287 : List PrefixCut := [⟨22,56145293,56145325⟩,
⟨64,164476379,164476476⟩]
theorem checked74287 : checkPrefixCuts (2^48) 9740877825 10 Manual.Count131072.C074287.packed 64 cuts74287 = true := by
 decide +kernel
def pointBounds74287 : List (Nat × Nat × Nat) := [(9740922880,116541952772851,116542342710221)]
theorem point_links_checked74287 : (cuts74287.take 1).map (fun c => (9740877825-1+2*2^10*c.k,116541896627558+c.lower,116542286564896+c.upper)) = pointBounds74287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000133
