import PlattAssemblyKernel
import PlattCertificates.Count131072.C067264
import PlattCertificates.Count131072.C067265
import PlattCertificates.Count131072.C067266
import PlattCertificates.Count131072.C067267
import PlattCertificates.Count131072.C067268
import PlattCertificates.Count131072.C067269
import PlattCertificates.Count131072.C067270
import PlattCertificates.Count131072.C067271
import PlattCertificates.Count131072.C067272
import PlattCertificates.Count131072.C067273
import PlattCertificates.Count131072.C067274
import PlattCertificates.Count131072.C067275
import PlattCertificates.Count131072.C067276
import PlattCertificates.Count131072.C067277
import PlattCertificates.Count131072.C067278
import PlattCertificates.Count131072.C067279
import PlattCertificates.Count131072.C067280
import PlattCertificates.Count131072.C067281
import PlattCertificates.Count131072.C067282
import PlattCertificates.Count131072.C067283
import PlattCertificates.Count131072.C067284
import PlattCertificates.Count131072.C067285
import PlattCertificates.Count131072.C067286
import PlattCertificates.Count131072.C067287
import PlattCertificates.Count131072.C067288
import PlattCertificates.Count131072.C067289
import PlattCertificates.Count131072.C067290
import PlattCertificates.Count131072.C067291
import PlattCertificates.Count131072.C067292
import PlattCertificates.Count131072.C067293
import PlattCertificates.Count131072.C067294
import PlattCertificates.Count131072.C067295
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000227
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67264 : List PrefixCut := [⟨64,183811487,183811591⟩]
theorem checked67264 : checkPrefixCuts (2^48) 8820359169 10 Manual.Count131072.C067264.packed 64 cuts67264 = true := by
 decide +kernel
def cuts67265 : List PrefixCut := [⟨23,65450270,65450306⟩,
⟨64,185404303,185404409⟩]
theorem checked67265 : checkPrefixCuts (2^48) 8820490241 10 Manual.Count131072.C067265.packed 64 cuts67265 = true := by
 decide +kernel
def pointBounds67265 : List (Nat × Nat × Nat) := [(8820537344,115324595157860,115324984376464)]
theorem point_links_checked67265 : (cuts67265.take 1).map (fun c => (8820490241-1+2*2^10*c.k,115324529707590+c.lower,115324918926158+c.upper)) = pointBounds67265 := by
 decide +kernel
def cuts67266 : List PrefixCut := [⟨64,181029782,181029891⟩]
theorem checked67266 : checkPrefixCuts (2^48) 8820621313 10 Manual.Count131072.C067266.packed 64 cuts67266 = true := by
 decide +kernel
def cuts67267 : List PrefixCut := [⟨30,84466879,84466929⟩,
⟨64,180037881,180037987⟩]
theorem checked67267 : checkPrefixCuts (2^48) 8820752385 10 Manual.Count131072.C067267.packed 64 cuts67267 = true := by
 decide +kernel
def pointBounds67267 : List (Nat × Nat × Nat) := [(8820813824,115324980608554,115325369827387)]
theorem point_links_checked67267 : (cuts67267.take 1).map (fun c => (8820752385-1+2*2^10*c.k,115324896141675+c.lower,115325285360458+c.upper)) = pointBounds67267 := by
 decide +kernel
def cuts67268 : List PrefixCut := [⟨64,183481477,183481585⟩]
theorem checked67268 : checkPrefixCuts (2^48) 8820883457 10 Manual.Count131072.C067268.packed 64 cuts67268 = true := by
 decide +kernel
def cuts67269 : List PrefixCut := [⟨37,104471526,104471589⟩,
⟨64,180606899,180607003⟩]
theorem checked67269 : checkPrefixCuts (2^48) 8821014529 10 Manual.Count131072.C067269.packed 64 cuts67269 = true := by
 decide +kernel
def pointBounds67269 : List (Nat × Nat × Nat) := [(8821090304,115325364132559,115325753351619)]
theorem point_links_checked67269 : (cuts67269.take 1).map (fun c => (8821014529-1+2*2^10*c.k,115325259661033+c.lower,115325648880030+c.upper)) = pointBounds67269 := by
 decide +kernel
def cuts67270 : List PrefixCut := [⟨64,182391107,182391208⟩]
theorem checked67270 : checkPrefixCuts (2^48) 8821145601 10 Manual.Count131072.C067270.packed 64 cuts67270 = true := by
 decide +kernel
def cuts67271 : List PrefixCut := [⟨44,124921661,124921737⟩,
⟨64,183919985,183920097⟩]
theorem checked67271 : checkPrefixCuts (2^48) 8821276673 10 Manual.Count131072.C067271.packed 64 cuts67271 = true := by
 decide +kernel
def pointBounds67271 : List (Nat × Nat × Nat) := [(8821366784,115325747580700,115326136799978)]
theorem point_links_checked67271 : (cuts67271.take 1).map (fun c => (8821276673-1+2*2^10*c.k,115325622659039+c.lower,115326011878241+c.upper)) = pointBounds67271 := by
 decide +kernel
def cuts67272 : List PrefixCut := [⟨64,180535042,180535148⟩]
theorem checked67272 : checkPrefixCuts (2^48) 8821407745 10 Manual.Count131072.C067272.packed 64 cuts67272 = true := by
 decide +kernel
def cuts67273 : List PrefixCut := [⟨51,146678766,146678849⟩,
⟨64,182670155,182670256⟩]
theorem checked67273 : checkPrefixCuts (2^48) 8821538817 10 Manual.Count131072.C067273.packed 64 cuts67273 = true := by
 decide +kernel
def pointBounds67273 : List (Nat × Nat × Nat) := [(8821643264,115326133792832,115326523012335)]
theorem point_links_checked67273 : (cuts67273.take 1).map (fun c => (8821538817-1+2*2^10*c.k,115325987114066+c.lower,115326376333486+c.upper)) = pointBounds67273 := by
 decide +kernel
def cuts67274 : List PrefixCut := [⟨64,181742146,181742257⟩]
theorem checked67274 : checkPrefixCuts (2^48) 8821669889 10 Manual.Count131072.C067274.packed 64 cuts67274 = true := by
 decide +kernel
def cuts67275 : List PrefixCut := [⟨58,165594860,165594955⟩,
⟨64,182760443,182760547⟩]
theorem checked67275 : checkPrefixCuts (2^48) 8821800961 10 Manual.Count131072.C067275.packed 64 cuts67275 = true := by
 decide +kernel
def pointBounds67275 : List (Nat × Nat × Nat) := [(8821919744,115326517121227,115326906340954)]
theorem point_links_checked67275 : (cuts67275.take 1).map (fun c => (8821800961-1+2*2^10*c.k,115326351526367+c.lower,115326740745999+c.upper)) = pointBounds67275 := by
 decide +kernel
def cuts67276 : List PrefixCut := [⟨64,181704815,181704925⟩]
theorem checked67276 : checkPrefixCuts (2^48) 8821932033 10 Manual.Count131072.C067276.packed 64 cuts67276 = true := by
 decide +kernel
def cuts67277 : List PrefixCut := [⟨64,185243651,185243759⟩]
theorem checked67277 : checkPrefixCuts (2^48) 8822063105 10 Manual.Count131072.C067277.packed 64 cuts67277 = true := by
 decide +kernel
def cuts67278 : List PrefixCut := [⟨1,2935289,2935290⟩,
⟨64,180199897,180200006⟩]
theorem checked67278 : checkPrefixCuts (2^48) 8822194177 10 Manual.Count131072.C067278.packed 64 cuts67278 = true := by
 decide +kernel
def pointBounds67278 : List (Nat × Nat × Nat) := [(8822196224,115326904170565,115327293390520)]
theorem point_links_checked67278 : (cuts67278.take 1).map (fun c => (8822194177-1+2*2^10*c.k,115326901235276+c.lower,115327290455230+c.upper)) = pointBounds67278 := by
 decide +kernel
def cuts67279 : List PrefixCut := [⟨64,182111470,182111579⟩]
theorem checked67279 : checkPrefixCuts (2^48) 8822325249 10 Manual.Count131072.C067279.packed 64 cuts67279 = true := by
 decide +kernel
def cuts67280 : List PrefixCut := [⟨8,22875411,22875425⟩,
⟨64,183512556,183512662⟩]
theorem checked67280 : checkPrefixCuts (2^48) 8822456321 10 Manual.Count131072.C067280.packed 64 cuts67280 = true := by
 decide +kernel
def pointBounds67280 : List (Nat × Nat × Nat) := [(8822472704,115327286422054,115327675642240)]
theorem point_links_checked67280 : (cuts67280.take 1).map (fun c => (8822456321-1+2*2^10*c.k,115327263546643+c.lower,115327652766815+c.upper)) = pointBounds67280 := by
 decide +kernel
def cuts67281 : List PrefixCut := [⟨64,180989444,180989544⟩]
theorem checked67281 : checkPrefixCuts (2^48) 8822587393 10 Manual.Count131072.C067281.packed 64 cuts67281 = true := by
 decide +kernel
def cuts67282 : List PrefixCut := [⟨15,42622893,42622919⟩,
⟨64,181880041,181880155⟩]
theorem checked67282 : checkPrefixCuts (2^48) 8822718465 10 Manual.Count131072.C067282.packed 64 cuts67282 = true := by
 decide +kernel
def pointBounds67282 : List (Nat × Nat × Nat) := [(8822749184,115327670671536,115328059891940)]
theorem point_links_checked67282 : (cuts67282.take 1).map (fun c => (8822718465-1+2*2^10*c.k,115327628048643+c.lower,115328017269021+c.upper)) = pointBounds67282 := by
 decide +kernel
def cuts67283 : List PrefixCut := [⟨64,182355878,182355987⟩]
theorem checked67283 : checkPrefixCuts (2^48) 8822849537 10 Manual.Count131072.C067283.packed 64 cuts67283 = true := by
 decide +kernel
def cuts67284 : List PrefixCut := [⟨22,63549562,63549596⟩,
⟨64,180502852,180502956⟩]
theorem checked67284 : checkPrefixCuts (2^48) 8822980609 10 Manual.Count131072.C067284.packed 64 cuts67284 = true := by
 decide +kernel
def pointBounds67284 : List (Nat × Nat × Nat) := [(8823025664,115328055834124,115328445054759)]
theorem point_links_checked67284 : (cuts67284.take 1).map (fun c => (8822980609-1+2*2^10*c.k,115327992284562+c.lower,115328381505163+c.upper)) = pointBounds67284 := by
 decide +kernel
def cuts67285 : List PrefixCut := [⟨64,181871924,181872034⟩]
theorem checked67285 : checkPrefixCuts (2^48) 8823111681 10 Manual.Count131072.C067285.packed 64 cuts67285 = true := by
 decide +kernel
def cuts67286 : List PrefixCut := [⟨29,82369460,82369506⟩,
⟨64,182252052,182252157⟩]
theorem checked67286 : checkPrefixCuts (2^48) 8823242753 10 Manual.Count131072.C067286.packed 64 cuts67286 = true := by
 decide +kernel
def pointBounds67286 : List (Nat × Nat × Nat) := [(8823302144,115328437028798,115328826249659)]
theorem point_links_checked67286 : (cuts67286.take 1).map (fun c => (8823242753-1+2*2^10*c.k,115328354659338+c.lower,115328743880153+c.upper)) = pointBounds67286 := by
 decide +kernel
def cuts67287 : List PrefixCut := [⟨64,184322914,184323024⟩]
theorem checked67287 : checkPrefixCuts (2^48) 8823373825 10 Manual.Count131072.C067287.packed 64 cuts67287 = true := by
 decide +kernel
def cuts67288 : List PrefixCut := [⟨36,101156306,101156361⟩,
⟨64,180715421,180715520⟩]
theorem checked67288 : checkPrefixCuts (2^48) 8823504897 10 Manual.Count131072.C067288.packed 64 cuts67288 = true := by
 decide +kernel
def pointBounds67288 : List (Nat × Nat × Nat) := [(8823578624,115328822390610,115329211611695)]
theorem point_links_checked67288 : (cuts67288.take 1).map (fun c => (8823504897-1+2*2^10*c.k,115328721234304+c.lower,115329110455334+c.upper)) = pointBounds67288 := by
 decide +kernel
def cuts67289 : List PrefixCut := [⟨64,182977630,182977735⟩]
theorem checked67289 : checkPrefixCuts (2^48) 8823635969 10 Manual.Count131072.C067289.packed 64 cuts67289 = true := by
 decide +kernel
def cuts67290 : List PrefixCut := [⟨43,122366364,122366439⟩,
⟨64,182305024,182305135⟩]
theorem checked67290 : checkPrefixCuts (2^48) 8823767041 10 Manual.Count131072.C067290.packed 64 cuts67290 = true := by
 decide +kernel
def pointBounds67290 : List (Nat × Nat × Nat) := [(8823855104,115329207293719,115329596515028)]
theorem point_links_checked67290 : (cuts67290.take 1).map (fun c => (8823767041-1+2*2^10*c.k,115329084927355+c.lower,115329474148589+c.upper)) = pointBounds67290 := by
 decide +kernel
def cuts67291 : List PrefixCut := [⟨64,184056759,184056870⟩]
theorem checked67291 : checkPrefixCuts (2^48) 8823898113 10 Manual.Count131072.C067291.packed 64 cuts67291 = true := by
 decide +kernel
def cuts67292 : List PrefixCut := [⟨50,141884508,141884586⟩,
⟨64,181725433,181725535⟩]
theorem checked67292 : checkPrefixCuts (2^48) 8824029185 10 Manual.Count131072.C067292.packed 64 cuts67292 = true := by
 decide +kernel
def pointBounds67292 : List (Nat × Nat × Nat) := [(8824131584,115329593173646,115329982395180)]
theorem point_links_checked67292 : (cuts67292.take 1).map (fun c => (8824029185-1+2*2^10*c.k,115329451289138+c.lower,115329840510594+c.upper)) = pointBounds67292 := by
 decide +kernel
def cuts67293 : List PrefixCut := [⟨64,183221946,183222052⟩]
theorem checked67293 : checkPrefixCuts (2^48) 8824160257 10 Manual.Count131072.C067293.packed 64 cuts67293 = true := by
 decide +kernel
def cuts67294 : List PrefixCut := [⟨57,161273875,161273966⟩,
⟨64,181656240,181656343⟩]
theorem checked67294 : checkPrefixCuts (2^48) 8824291329 10 Manual.Count131072.C067294.packed 64 cuts67294 = true := by
 decide +kernel
def pointBounds67294 : List (Nat × Nat × Nat) := [(8824408064,115329977510392,115330366732147)]
theorem point_links_checked67294 : (cuts67294.take 1).map (fun c => (8824291329-1+2*2^10*c.k,115329816236517+c.lower,115330205458181+c.upper)) = pointBounds67294 := by
 decide +kernel
def cuts67295 : List PrefixCut := [⟨64,181525957,181526061⟩]
theorem checked67295 : checkPrefixCuts (2^48) 8824422401 10 Manual.Count131072.C067295.packed 64 cuts67295 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000227
