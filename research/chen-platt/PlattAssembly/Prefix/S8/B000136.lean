import PlattAssemblyKernel
import PlattCertificates.Count131072.C074352
import PlattCertificates.Count131072.C074353
import PlattCertificates.Count131072.C074354
import PlattCertificates.Count131072.C074355
import PlattCertificates.Count131072.C074356
import PlattCertificates.Count131072.C074357
import PlattCertificates.Count131072.C074358
import PlattCertificates.Count131072.C074359
import PlattCertificates.Count131072.C074360
import PlattCertificates.Count131072.C074361
import PlattCertificates.Count131072.C074362
import PlattCertificates.Count131072.C074363
import PlattCertificates.Count131072.C074364
import PlattCertificates.Count131072.C074365
import PlattCertificates.Count131072.C074366
import PlattCertificates.Count131072.C074367
import PlattCertificates.Count131072.C074368
import PlattCertificates.Count131072.C074369
import PlattCertificates.Count131072.C074370
import PlattCertificates.Count131072.C074371
import PlattCertificates.Count131072.C074372
import PlattCertificates.Count131072.C074373
import PlattCertificates.Count131072.C074374
import PlattCertificates.Count131072.C074375
import PlattCertificates.Count131072.C074376
import PlattCertificates.Count131072.C074377
import PlattCertificates.Count131072.C074378
import PlattCertificates.Count131072.C074379
import PlattCertificates.Count131072.C074380
import PlattCertificates.Count131072.C074381
import PlattCertificates.Count131072.C074382
import PlattCertificates.Count131072.C074383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000136
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74352 : List PrefixCut := [⟨34,86064157,86064207⟩,
⟨64,163639745,163639844⟩]
theorem checked74352 : checkPrefixCuts (2^48) 9749397505 10 Manual.Count131072.C074352.packed 64 cuts74352 = true := by
 decide +kernel
def pointBounds74352 : List (Nat × Nat × Nat) := [(9749467136,116552681652330,116553071596112)]
theorem point_links_checked74352 : (cuts74352.take 1).map (fun c => (9749397505-1+2*2^10*c.k,116552595588173+c.lower,116552985531905+c.upper)) = pointBounds74352 := by
 decide +kernel
def cuts74353 : List PrefixCut := [⟨64,164734636,164734734⟩]
theorem checked74353 : checkPrefixCuts (2^48) 9749528577 10 Manual.Count131072.C074353.packed 64 cuts74353 = true := by
 decide +kernel
def cuts74354 : List PrefixCut := [⟨55,143339864,143339950⟩,
⟨64,166204797,166204898⟩]
theorem checked74354 : checkPrefixCuts (2^48) 9749659649 10 Manual.Count131072.C074354.packed 64 cuts74354 = true := by
 decide +kernel
def pointBounds74354 : List (Nat × Nat × Nat) := [(9749772288,116553067302418,116553457246433)]
theorem point_links_checked74354 : (cuts74354.take 1).map (fun c => (9749659649-1+2*2^10*c.k,116552923962554+c.lower,116553313906483+c.upper)) = pointBounds74354 := by
 decide +kernel
def cuts74355 : List PrefixCut := [⟨64,165076636,165076728⟩]
theorem checked74355 : checkPrefixCuts (2^48) 9749790721 10 Manual.Count131072.C074355.packed 64 cuts74355 = true := by
 decide +kernel
def cuts74356 : List PrefixCut := [⟨64,162274089,162274189⟩]
theorem checked74356 : checkPrefixCuts (2^48) 9749921793 10 Manual.Count131072.C074356.packed 64 cuts74356 = true := by
 decide +kernel
def cuts74357 : List PrefixCut := [⟨12,30918729,30918747⟩,
⟨64,164061782,164061886⟩]
theorem checked74357 : checkPrefixCuts (2^48) 9750052865 10 Manual.Count131072.C074357.packed 64 cuts74357 = true := by
 decide +kernel
def pointBounds74357 : List (Nat × Nat × Nat) := [(9750077440,116553448436805,116553838381045)]
theorem point_links_checked74357 : (cuts74357.take 1).map (fun c => (9750052865-1+2*2^10*c.k,116553417518076+c.lower,116553807462298+c.upper)) = pointBounds74357 := by
 decide +kernel
def cuts74358 : List PrefixCut := [⟨64,165041099,165041198⟩]
theorem checked74358 : checkPrefixCuts (2^48) 9750183937 10 Manual.Count131072.C074358.packed 64 cuts74358 = true := by
 decide +kernel
def cuts74359 : List PrefixCut := [⟨33,84497177,84497230⟩,
⟨64,164346046,164346143⟩]
theorem checked74359 : checkPrefixCuts (2^48) 9750315009 10 Manual.Count131072.C074359.packed 64 cuts74359 = true := by
 decide +kernel
def pointBounds74359 : List (Nat × Nat × Nat) := [(9750382592,116553831118134,116554221062612)]
theorem point_links_checked74359 : (cuts74359.take 1).map (fun c => (9750315009-1+2*2^10*c.k,116553746620957+c.lower,116554136565382+c.upper)) = pointBounds74359 := by
 decide +kernel
def cuts74360 : List PrefixCut := [⟨64,165267613,165267713⟩]
theorem checked74360 : checkPrefixCuts (2^48) 9750446081 10 Manual.Count131072.C074360.packed 64 cuts74360 = true := by
 decide +kernel
def cuts74361 : List PrefixCut := [⟨54,137524050,137524123⟩,
⟨64,163417887,163417975⟩]
theorem checked74361 : checkPrefixCuts (2^48) 9750577153 10 Manual.Count131072.C074361.packed 64 cuts74361 = true := by
 decide +kernel
def pointBounds74361 : List (Nat × Nat × Nat) := [(9750687744,116554213758666,116554603703361)]
theorem point_links_checked74361 : (cuts74361.take 1).map (fun c => (9750577153-1+2*2^10*c.k,116554076234616+c.lower,116554466179238+c.upper)) = pointBounds74361 := by
 decide +kernel
def cuts74362 : List PrefixCut := [⟨64,165176561,165176656⟩]
theorem checked74362 : checkPrefixCuts (2^48) 9750708225 10 Manual.Count131072.C074362.packed 64 cuts74362 = true := by
 decide +kernel
def cuts74363 : List PrefixCut := [⟨64,164741341,164741439⟩]
theorem checked74363 : checkPrefixCuts (2^48) 9750839297 10 Manual.Count131072.C074363.packed 64 cuts74363 = true := by
 decide +kernel
def cuts74364 : List PrefixCut := [⟨11,27884858,27884873⟩,
⟨64,162343246,162343338⟩]
theorem checked74364 : checkPrefixCuts (2^48) 9750970369 10 Manual.Count131072.C074364.packed 64 cuts74364 = true := by
 decide +kernel
def pointBounds74364 : List (Nat × Nat × Nat) := [(9750992896,116554597455263,116554987400181)]
theorem point_links_checked74364 : (cuts74364.take 1).map (fun c => (9750970369-1+2*2^10*c.k,116554569570405+c.lower,116554959515308+c.upper)) = pointBounds74364 := by
 decide +kernel
def cuts74365 : List PrefixCut := [⟨64,164361668,164361763⟩]
theorem checked74365 : checkPrefixCuts (2^48) 9751101441 10 Manual.Count131072.C074365.packed 64 cuts74365 = true := by
 decide +kernel
def cuts74366 : List PrefixCut := [⟨32,81140845,81140892⟩,
⟨64,164417178,164417278⟩]
theorem checked74366 : checkPrefixCuts (2^48) 9751232513 10 Manual.Count131072.C074366.packed 64 cuts74366 = true := by
 decide +kernel
def pointBounds74366 : List (Nat × Nat × Nat) := [(9751298048,116554977416164,116555367361301)]
theorem point_links_checked74366 : (cuts74366.take 1).map (fun c => (9751232513-1+2*2^10*c.k,116554896275319+c.lower,116555286220409+c.upper)) = pointBounds74366 := by
 decide +kernel
def cuts74367 : List PrefixCut := [⟨64,165540715,165540814⟩]
theorem checked74367 : checkPrefixCuts (2^48) 9751363585 10 Manual.Count131072.C074367.packed 64 cuts74367 = true := by
 decide +kernel
def cuts74368 : List PrefixCut := [⟨53,137135874,137135952⟩,
⟨64,165538482,165538581⟩]
theorem checked74368 : checkPrefixCuts (2^48) 9751494657 10 Manual.Count131072.C074368.packed 64 cuts74368 = true := by
 decide +kernel
def pointBounds74368 : List (Nat × Nat × Nat) := [(9751603200,116555363369086,116555753314453)]
theorem point_links_checked74368 : (cuts74368.take 1).map (fun c => (9751494657-1+2*2^10*c.k,116555226233212+c.lower,116555616178501+c.upper)) = pointBounds74368 := by
 decide +kernel
def cuts74369 : List PrefixCut := [⟨64,166690837,166690937⟩]
theorem checked74369 : checkPrefixCuts (2^48) 9751625729 10 Manual.Count131072.C074369.packed 64 cuts74369 = true := by
 decide +kernel
def cuts74370 : List PrefixCut := [⟨64,163802199,163802303⟩]
theorem checked74370 : checkPrefixCuts (2^48) 9751756801 10 Manual.Count131072.C074370.packed 64 cuts74370 = true := by
 decide +kernel
def cuts74371 : List PrefixCut := [⟨10,24562924,24562940⟩,
⟨64,162674323,162674425⟩]
theorem checked74371 : checkPrefixCuts (2^48) 9751887873 10 Manual.Count131072.C074371.packed 64 cuts74371 = true := by
 decide +kernel
def pointBounds74371 : List (Nat × Nat × Nat) := [(9751908352,116555746827654,116556136773262)]
theorem point_links_checked74371 : (cuts74371.take 1).map (fun c => (9751887873-1+2*2^10*c.k,116555722264730+c.lower,116556112210322+c.upper)) = pointBounds74371 := by
 decide +kernel
def cuts74372 : List PrefixCut := [⟨64,162874198,162874291⟩]
theorem checked74372 : checkPrefixCuts (2^48) 9752018945 10 Manual.Count131072.C074372.packed 64 cuts74372 = true := by
 decide +kernel
def cuts74373 : List PrefixCut := [⟨31,78679889,78679939⟩,
⟨64,163102901,163103001⟩]
theorem checked74373 : checkPrefixCuts (2^48) 9752150017 10 Manual.Count131072.C074373.packed 64 cuts74373 = true := by
 decide +kernel
def pointBounds74373 : List (Nat × Nat × Nat) := [(9752213504,116556126493140,116556516438977)]
theorem point_links_checked74373 : (cuts74373.take 1).map (fun c => (9752150017-1+2*2^10*c.k,116556047813251+c.lower,116556437759038+c.upper)) = pointBounds74373 := by
 decide +kernel
def cuts74374 : List PrefixCut := [⟨64,164890166,164890266⟩]
theorem checked74374 : checkPrefixCuts (2^48) 9752281089 10 Manual.Count131072.C074374.packed 64 cuts74374 = true := by
 decide +kernel
def cuts74375 : List PrefixCut := [⟨52,135881932,135882012⟩,
⟨64,166388779,166388874⟩]
theorem checked74375 : checkPrefixCuts (2^48) 9752412161 10 Manual.Count131072.C074375.packed 64 cuts74375 = true := by
 decide +kernel
def pointBounds74375 : List (Nat × Nat × Nat) := [(9752518656,116556511688250,116556901634317)]
theorem point_links_checked74375 : (cuts74375.take 1).map (fun c => (9752412161-1+2*2^10*c.k,116556375806318+c.lower,116556765752305+c.upper)) = pointBounds74375 := by
 decide +kernel
def cuts74376 : List PrefixCut := [⟨64,166703994,166704094⟩]
theorem checked74376 : checkPrefixCuts (2^48) 9752543233 10 Manual.Count131072.C074376.packed 64 cuts74376 = true := by
 decide +kernel
def cuts74377 : List PrefixCut := [⟨64,167019245,167019337⟩]
theorem checked74377 : checkPrefixCuts (2^48) 9752674305 10 Manual.Count131072.C074377.packed 64 cuts74377 = true := by
 decide +kernel
def cuts74378 : List PrefixCut := [⟨9,23030990,23031003⟩,
⟨64,163322830,163322924⟩]
theorem checked74378 : checkPrefixCuts (2^48) 9752805377 10 Manual.Count131072.C074378.packed 64 cuts74378 = true := by
 decide +kernel
def pointBounds74378 : List (Nat × Nat × Nat) := [(9752823808,116556898949326,116557288895613)]
theorem point_links_checked74378 : (cuts74378.take 1).map (fun c => (9752805377-1+2*2^10*c.k,116556875918336+c.lower,116557265864610+c.upper)) = pointBounds74378 := by
 decide +kernel
def cuts74379 : List PrefixCut := [⟨64,164705930,164706025⟩]
theorem checked74379 : checkPrefixCuts (2^48) 9752936449 10 Manual.Count131072.C074379.packed 64 cuts74379 = true := by
 decide +kernel
def cuts74380 : List PrefixCut := [⟨30,76334831,76334879⟩,
⟨64,164905727,164905826⟩]
theorem checked74380 : checkPrefixCuts (2^48) 9753067521 10 Manual.Count131072.C074380.packed 64 cuts74380 = true := by
 decide +kernel
def pointBounds74380 : List (Nat × Nat × Nat) := [(9753128960,116557280281927,116557670228438)]
theorem point_links_checked74380 : (cuts74380.take 1).map (fun c => (9753067521-1+2*2^10*c.k,116557203947096+c.lower,116557593893559+c.upper)) = pointBounds74380 := by
 decide +kernel
def cuts74381 : List PrefixCut := [⟨64,163922285,163922385⟩]
theorem checked74381 : checkPrefixCuts (2^48) 9753198593 10 Manual.Count131072.C074381.packed 64 cuts74381 = true := by
 decide +kernel
def cuts74382 : List PrefixCut := [⟨51,131049662,131049750⟩,
⟨64,163660350,163660457⟩]
theorem checked74382 : checkPrefixCuts (2^48) 9753329665 10 Manual.Count131072.C074382.packed 64 cuts74382 = true := by
 decide +kernel
def pointBounds74382 : List (Nat × Nat × Nat) := [(9753434112,116557663824770,116558053771520)]
theorem point_links_checked74382 : (cuts74382.take 1).map (fun c => (9753329665-1+2*2^10*c.k,116557532775108+c.lower,116557922721770+c.upper)) = pointBounds74382 := by
 decide +kernel
def cuts74383 : List PrefixCut := [⟨64,164062179,164062278⟩]
theorem checked74383 : checkPrefixCuts (2^48) 9753460737 10 Manual.Count131072.C074383.packed 64 cuts74383 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000136
