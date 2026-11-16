import PlattAssemblyKernel
import PlattCertificates.Count131072.C069280
import PlattCertificates.Count131072.C069281
import PlattCertificates.Count131072.C069282
import PlattCertificates.Count131072.C069283
import PlattCertificates.Count131072.C069284
import PlattCertificates.Count131072.C069285
import PlattCertificates.Count131072.C069286
import PlattCertificates.Count131072.C069287
import PlattCertificates.Count131072.C069288
import PlattCertificates.Count131072.C069289
import PlattCertificates.Count131072.C069290
import PlattCertificates.Count131072.C069291
import PlattCertificates.Count131072.C069292
import PlattCertificates.Count131072.C069293
import PlattCertificates.Count131072.C069294
import PlattCertificates.Count131072.C069295
import PlattCertificates.Count131072.C069296
import PlattCertificates.Count131072.C069297
import PlattCertificates.Count131072.C069298
import PlattCertificates.Count131072.C069299
import PlattCertificates.Count131072.C069300
import PlattCertificates.Count131072.C069301
import PlattCertificates.Count131072.C069302
import PlattCertificates.Count131072.C069303
import PlattCertificates.Count131072.C069304
import PlattCertificates.Count131072.C069305
import PlattCertificates.Count131072.C069306
import PlattCertificates.Count131072.C069307
import PlattCertificates.Count131072.C069308
import PlattCertificates.Count131072.C069309
import PlattCertificates.Count131072.C069310
import PlattCertificates.Count131072.C069311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000290
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69280 : List PrefixCut := [⟨64,175924409,175924509⟩]
theorem checked69280 : checkPrefixCuts (2^48) 9084600321 10 Manual.Count131072.C069280.packed 64 cuts69280 = true := by
 decide +kernel
def cuts69281 : List PrefixCut := [⟨2,5112242,5112245⟩,
⟨64,177935775,177935877⟩]
theorem checked69281 : checkPrefixCuts (2^48) 9084731393 10 Manual.Count131072.C069281.packed 64 cuts69281 = true := by
 decide +kernel
def pointBounds69281 : List (Nat × Nat × Nat) := [(9084735488,115687102886139,115687492316844)]
theorem point_links_checked69281 : (cuts69281.take 1).map (fun c => (9084731393-1+2*2^10*c.k,115687097773897+c.lower,115687487204599+c.upper)) = pointBounds69281 := by
 decide +kernel
def cuts69282 : List PrefixCut := [⟨64,177468466,177468565⟩]
theorem checked69282 : checkPrefixCuts (2^48) 9084862465 10 Manual.Count131072.C069282.packed 64 cuts69282 = true := by
 decide +kernel
def cuts69283 : List PrefixCut := [⟨13,34359429,34359451⟩,
⟨64,175421066,175421172⟩]
theorem checked69283 : checkPrefixCuts (2^48) 9084993537 10 Manual.Count131072.C069283.packed 64 cuts69283 = true := by
 decide +kernel
def pointBounds69283 : List (Nat × Nat × Nat) := [(9085020160,115687487537567,115687876968492)]
theorem point_links_checked69283 : (cuts69283.take 1).map (fun c => (9084993537-1+2*2^10*c.k,115687453178138+c.lower,115687842609041+c.upper)) = pointBounds69283 := by
 decide +kernel
def cuts69284 : List PrefixCut := [⟨64,177835129,177835233⟩]
theorem checked69284 : checkPrefixCuts (2^48) 9085124609 10 Manual.Count131072.C069284.packed 64 cuts69284 = true := by
 decide +kernel
def cuts69285 : List PrefixCut := [⟨24,67291646,67291684⟩,
⟨64,177956488,177956591⟩]
theorem checked69285 : checkPrefixCuts (2^48) 9085255681 10 Manual.Count131072.C069285.packed 64 cuts69285 = true := by
 decide +kernel
def pointBounds69285 : List (Nat × Nat × Nat) := [(9085304832,115687873725979,115688263157130)]
theorem point_links_checked69285 : (cuts69285.take 1).map (fun c => (9085255681-1+2*2^10*c.k,115687806434333+c.lower,115688195865446+c.upper)) = pointBounds69285 := by
 decide +kernel
def cuts69286 : List PrefixCut := [⟨64,179162164,179162273⟩]
theorem checked69286 : checkPrefixCuts (2^48) 9085386753 10 Manual.Count131072.C069286.packed 64 cuts69286 = true := by
 decide +kernel
def cuts69287 : List PrefixCut := [⟨35,97309713,97309773⟩,
⟨64,178013300,178013408⟩]
theorem checked69287 : checkPrefixCuts (2^48) 9085517825 10 Manual.Count131072.C069287.packed 64 cuts69287 = true := by
 decide +kernel
def pointBounds69287 : List (Nat × Nat × Nat) := [(9085589504,115688260862698,115688650294083)]
theorem point_links_checked69287 : (cuts69287.take 1).map (fun c => (9085517825-1+2*2^10*c.k,115688163552985+c.lower,115688552984310+c.upper)) = pointBounds69287 := by
 decide +kernel
def cuts69288 : List PrefixCut := [⟨64,178475433,178475537⟩]
theorem checked69288 : checkPrefixCuts (2^48) 9085648897 10 Manual.Count131072.C069288.packed 64 cuts69288 = true := by
 decide +kernel
def cuts69289 : List PrefixCut := [⟨46,126334640,126334711⟩,
⟨64,175932552,175932651⟩]
theorem checked69289 : checkPrefixCuts (2^48) 9085779969 10 Manual.Count131072.C069289.packed 64 cuts69289 = true := by
 decide +kernel
def pointBounds69289 : List (Nat × Nat × Nat) := [(9085874176,115688646376358,115689035807966)]
theorem point_links_checked69289 : (cuts69289.take 1).map (fun c => (9085779969-1+2*2^10*c.k,115688520041718+c.lower,115688909473255+c.upper)) = pointBounds69289 := by
 decide +kernel
def cuts69290 : List PrefixCut := [⟨64,179678464,179678571⟩]
theorem checked69290 : checkPrefixCuts (2^48) 9085911041 10 Manual.Count131072.C069290.packed 64 cuts69290 = true := by
 decide +kernel
def cuts69291 : List PrefixCut := [⟨57,157867067,157867167⟩,
⟨64,177569331,177569442⟩]
theorem checked69291 : checkPrefixCuts (2^48) 9086042113 10 Manual.Count131072.C069291.packed 64 cuts69291 = true := by
 decide +kernel
def pointBounds69291 : List (Nat × Nat × Nat) := [(9086158848,115689033519801,115689422951644)]
theorem point_links_checked69291 : (cuts69291.take 1).map (fun c => (9086042113-1+2*2^10*c.k,115688875652734+c.lower,115689265084477+c.upper)) = pointBounds69291 := by
 decide +kernel
def cuts69292 : List PrefixCut := [⟨64,177969494,177969592⟩]
theorem checked69292 : checkPrefixCuts (2^48) 9086173185 10 Manual.Count131072.C069292.packed 64 cuts69292 = true := by
 decide +kernel
def cuts69293 : List PrefixCut := [⟨64,175240888,175240993⟩]
theorem checked69293 : checkPrefixCuts (2^48) 9086304257 10 Manual.Count131072.C069293.packed 64 cuts69293 = true := by
 decide +kernel
def cuts69294 : List PrefixCut := [⟨4,11151889,11151895⟩,
⟨64,178088254,178088359⟩]
theorem checked69294 : checkPrefixCuts (2^48) 9086435329 10 Manual.Count131072.C069294.packed 64 cuts69294 = true := by
 decide +kernel
def pointBounds69294 : List (Nat × Nat × Nat) := [(9086443520,115689417584336,115689807016399)]
theorem point_links_checked69294 : (cuts69294.take 1).map (fun c => (9086435329-1+2*2^10*c.k,115689406432447+c.lower,115689795864504+c.upper)) = pointBounds69294 := by
 decide +kernel
def cuts69295 : List PrefixCut := [⟨64,175514628,175514728⟩]
theorem checked69295 : checkPrefixCuts (2^48) 9086566401 10 Manual.Count131072.C069295.packed 64 cuts69295 = true := by
 decide +kernel
def cuts69296 : List PrefixCut := [⟨15,39866802,39866828⟩,
⟨64,174737675,174737779⟩]
theorem checked69296 : checkPrefixCuts (2^48) 9086697473 10 Manual.Count131072.C069296.packed 64 cuts69296 = true := by
 decide +kernel
def pointBounds69296 : List (Nat × Nat × Nat) := [(9086728192,115689799902131,115690189334419)]
theorem point_links_checked69296 : (cuts69296.take 1).map (fun c => (9086697473-1+2*2^10*c.k,115689760035329+c.lower,115690149467591+c.upper)) = pointBounds69296 := by
 decide +kernel
def cuts69297 : List PrefixCut := [⟨64,176469800,176469903⟩]
theorem checked69297 : checkPrefixCuts (2^48) 9086828545 10 Manual.Count131072.C069297.packed 64 cuts69297 = true := by
 decide +kernel
def cuts69298 : List PrefixCut := [⟨26,71398769,71398813⟩,
⟨64,174701661,174701767⟩]
theorem checked69298 : checkPrefixCuts (2^48) 9086959617 10 Manual.Count131072.C069298.packed 64 cuts69298 = true := by
 decide +kernel
def pointBounds69298 : List (Nat × Nat × Nat) := [(9087012864,115690182641573,115690572074086)]
theorem point_links_checked69298 : (cuts69298.take 1).map (fun c => (9086959617-1+2*2^10*c.k,115690111242804+c.lower,115690500675273+c.upper)) = pointBounds69298 := by
 decide +kernel
def cuts69299 : List PrefixCut := [⟨64,176836423,176836535⟩]
theorem checked69299 : checkPrefixCuts (2^48) 9087090689 10 Manual.Count131072.C069299.packed 64 cuts69299 = true := by
 decide +kernel
def cuts69300 : List PrefixCut := [⟨37,103517364,103517428⟩,
⟨64,177608243,177608355⟩]
theorem checked69300 : checkPrefixCuts (2^48) 9087221761 10 Manual.Count131072.C069300.packed 64 cuts69300 = true := by
 decide +kernel
def pointBounds69300 : List (Nat × Nat × Nat) := [(9087297536,115690566298252,115690955731003)]
theorem point_links_checked69300 : (cuts69300.take 1).map (fun c => (9087221761-1+2*2^10*c.k,115690462780888+c.lower,115690852213575+c.upper)) = pointBounds69300 := by
 decide +kernel
def cuts69301 : List PrefixCut := [⟨64,177172027,177172130⟩]
theorem checked69301 : checkPrefixCuts (2^48) 9087352833 10 Manual.Count131072.C069301.packed 64 cuts69301 = true := by
 decide +kernel
def cuts69302 : List PrefixCut := [⟨48,132908328,132908401⟩,
⟨64,176921696,176921795⟩]
theorem checked69302 : checkPrefixCuts (2^48) 9087483905 10 Manual.Count131072.C069302.packed 64 cuts69302 = true := by
 decide +kernel
def pointBounds69302 : List (Nat × Nat × Nat) := [(9087582208,115690950469486,115691339902461)]
theorem point_links_checked69302 : (cuts69302.take 1).map (fun c => (9087483905-1+2*2^10*c.k,115690817561158+c.lower,115691206994060+c.upper)) = pointBounds69302 := by
 decide +kernel
def cuts69303 : List PrefixCut := [⟨64,176950118,176950220⟩]
theorem checked69303 : checkPrefixCuts (2^48) 9087614977 10 Manual.Count131072.C069303.packed 64 cuts69303 = true := by
 decide +kernel
def cuts69304 : List PrefixCut := [⟨59,162483366,162483460⟩,
⟨64,176947564,176947667⟩]
theorem checked69304 : checkPrefixCuts (2^48) 9087746049 10 Manual.Count131072.C069304.packed 64 cuts69304 = true := by
 decide +kernel
def pointBounds69304 : List (Nat × Nat × Nat) := [(9087866880,115691333916338,115691723349535)]
theorem point_links_checked69304 : (cuts69304.take 1).map (fun c => (9087746049-1+2*2^10*c.k,115691171432972+c.lower,115691560866075+c.upper)) = pointBounds69304 := by
 decide +kernel
def cuts69305 : List PrefixCut := [⟨64,178400706,178400806⟩]
theorem checked69305 : checkPrefixCuts (2^48) 9087877121 10 Manual.Count131072.C069305.packed 64 cuts69305 = true := by
 decide +kernel
def cuts69306 : List PrefixCut := [⟨64,175084132,175084238⟩]
theorem checked69306 : checkPrefixCuts (2^48) 9088008193 10 Manual.Count131072.C069306.packed 64 cuts69306 = true := by
 decide +kernel
def cuts69307 : List PrefixCut := [⟨6,16972467,16972476⟩,
⟨64,177435450,177435554⟩]
theorem checked69307 : checkPrefixCuts (2^48) 9088139265 10 Manual.Count131072.C069307.packed 64 cuts69307 = true := by
 decide +kernel
def pointBounds69307 : List (Nat × Nat × Nat) := [(9088151552,115691718837841,115692108271262)]
theorem point_links_checked69307 : (cuts69307.take 1).map (fun c => (9088139265-1+2*2^10*c.k,115691701865374+c.lower,115692091298786+c.upper)) = pointBounds69307 := by
 decide +kernel
def cuts69308 : List PrefixCut := [⟨64,178733661,178733769⟩]
theorem checked69308 : checkPrefixCuts (2^48) 9088270337 10 Manual.Count131072.C069308.packed 64 cuts69308 = true := by
 decide +kernel
def cuts69309 : List PrefixCut := [⟨17,48221415,48221443⟩,
⟨64,177894894,177894996⟩]
theorem checked69309 : checkPrefixCuts (2^48) 9088401409 10 Manual.Count131072.C069309.packed 64 cuts69309 = true := by
 decide +kernel
def pointBounds69309 : List (Nat × Nat × Nat) := [(9088436224,115692106255900,115692495689552)]
theorem point_links_checked69309 : (cuts69309.take 1).map (fun c => (9088401409-1+2*2^10*c.k,115692058034485+c.lower,115692447468109+c.upper)) = pointBounds69309 := by
 decide +kernel
def cuts69310 : List PrefixCut := [⟨64,176932250,176932352⟩]
theorem checked69310 : checkPrefixCuts (2^48) 9088532481 10 Manual.Count131072.C069310.packed 64 cuts69310 = true := by
 decide +kernel
def cuts69311 : List PrefixCut := [⟨28,78322599,78322646⟩,
⟨64,176681940,176682047⟩]
theorem checked69311 : checkPrefixCuts (2^48) 9088663553 10 Manual.Count131072.C069311.packed 64 cuts69311 = true := by
 decide +kernel
def pointBounds69311 : List (Nat × Nat × Nat) := [(9088720896,115692491184228,115692880618103)]
theorem point_links_checked69311 : (cuts69311.take 1).map (fun c => (9088663553-1+2*2^10*c.k,115692412861629+c.lower,115692802295457+c.upper)) = pointBounds69311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000290
