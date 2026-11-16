import PlattAssemblyKernel
import PlattCertificates.Count131072.C062272
import PlattCertificates.Count131072.C062273
import PlattCertificates.Count131072.C062274
import PlattCertificates.Count131072.C062275
import PlattCertificates.Count131072.C062276
import PlattCertificates.Count131072.C062277
import PlattCertificates.Count131072.C062278
import PlattCertificates.Count131072.C062279
import PlattCertificates.Count131072.C062280
import PlattCertificates.Count131072.C062281
import PlattCertificates.Count131072.C062282
import PlattCertificates.Count131072.C062283
import PlattCertificates.Count131072.C062284
import PlattCertificates.Count131072.C062285
import PlattCertificates.Count131072.C062286
import PlattCertificates.Count131072.C062287
import PlattCertificates.Count131072.C062288
import PlattCertificates.Count131072.C062289
import PlattCertificates.Count131072.C062290
import PlattCertificates.Count131072.C062291
import PlattCertificates.Count131072.C062292
import PlattCertificates.Count131072.C062293
import PlattCertificates.Count131072.C062294
import PlattCertificates.Count131072.C062295
import PlattCertificates.Count131072.C062296
import PlattCertificates.Count131072.C062297
import PlattCertificates.Count131072.C062298
import PlattCertificates.Count131072.C062299
import PlattCertificates.Count131072.C062300
import PlattCertificates.Count131072.C062301
import PlattCertificates.Count131072.C062302
import PlattCertificates.Count131072.C062303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62272 : List PrefixCut := [⟨64,199332191,199332300⟩]
theorem checked62272 : checkPrefixCuts (2^48) 8166047745 10 Manual.Count131072.C062272.packed 64 cuts62272 = true := by
 decide +kernel
def cuts62273 : List PrefixCut := [⟨23,70453151,70453190⟩,
⟨64,197226440,197226549⟩]
theorem checked62273 : checkPrefixCuts (2^48) 8166178817 10 Manual.Count131072.C062273.packed 64 cuts62273 = true := by
 decide +kernel
def pointBounds62273 : List (Nat × Nat × Nat) := [(8166225920,114375612517814,114376001187777)]
theorem point_links_checked62273 : (cuts62273.take 1).map (fun c => (8166178817-1+2*2^10*c.k,114375542064663+c.lower,114375930734587+c.upper)) = pointBounds62273 := by
 decide +kernel
def cuts62274 : List PrefixCut := [⟨64,195672245,195672361⟩]
theorem checked62274 : checkPrefixCuts (2^48) 8166309889 10 Manual.Count131072.C062274.packed 64 cuts62274 = true := by
 decide +kernel
def cuts62275 : List PrefixCut := [⟨20,61110308,61110344⟩,
⟨64,197978386,197978503⟩]
theorem checked62275 : checkPrefixCuts (2^48) 8166440961 10 Manual.Count131072.C062275.packed 64 cuts62275 = true := by
 decide +kernel
def pointBounds62275 : List (Nat × Nat × Nat) := [(8166481920,114375996073656,114376384743841)]
theorem point_links_checked62275 : (cuts62275.take 1).map (fun c => (8166440961-1+2*2^10*c.k,114375934963348+c.lower,114376323633497+c.upper)) = pointBounds62275 := by
 decide +kernel
def cuts62276 : List PrefixCut := [⟨64,200870374,200870485⟩]
theorem checked62276 : checkPrefixCuts (2^48) 8166572033 10 Manual.Count131072.C062276.packed 64 cuts62276 = true := by
 decide +kernel
def cuts62277 : List PrefixCut := [⟨17,50113688,50113719⟩,
⟨64,194387565,194387684⟩]
theorem checked62277 : checkPrefixCuts (2^48) 8166703105 10 Manual.Count131072.C062277.packed 64 cuts62277 = true := by
 decide +kernel
def pointBounds62277 : List (Nat × Nat × Nat) := [(8166737920,114376383925796,114376772596204)]
theorem point_links_checked62277 : (cuts62277.take 1).map (fun c => (8166703105-1+2*2^10*c.k,114376333812108+c.lower,114376722482485+c.upper)) = pointBounds62277 := by
 decide +kernel
def cuts62278 : List PrefixCut := [⟨64,197382952,197383064⟩]
theorem checked62278 : checkPrefixCuts (2^48) 8166834177 10 Manual.Count131072.C062278.packed 64 cuts62278 = true := by
 decide +kernel
def cuts62279 : List PrefixCut := [⟨14,42908915,42908940⟩,
⟨64,199309806,199309918⟩]
theorem checked62279 : checkPrefixCuts (2^48) 8166965249 10 Manual.Count131072.C062279.packed 64 cuts62279 = true := by
 decide +kernel
def pointBounds62279 : List (Nat × Nat × Nat) := [(8166993920,114376768491540,114377157162173)]
theorem point_links_checked62279 : (cuts62279.take 1).map (fun c => (8166965249-1+2*2^10*c.k,114376725582625+c.lower,114377114253233+c.upper)) = pointBounds62279 := by
 decide +kernel
def cuts62280 : List PrefixCut := [⟨64,196446068,196446185⟩]
theorem checked62280 : checkPrefixCuts (2^48) 8167096321 10 Manual.Count131072.C062280.packed 64 cuts62280 = true := by
 decide +kernel
def cuts62281 : List PrefixCut := [⟨11,33946942,33946961⟩,
⟨64,197235592,197235703⟩]
theorem checked62281 : checkPrefixCuts (2^48) 8167227393 10 Manual.Count131072.C062281.packed 64 cuts62281 = true := by
 decide +kernel
def pointBounds62281 : List (Nat × Nat × Nat) := [(8167249920,114377155285441,114377543956297)]
theorem point_links_checked62281 : (cuts62281.take 1).map (fun c => (8167227393-1+2*2^10*c.k,114377121338499+c.lower,114377510009336+c.upper)) = pointBounds62281 := by
 decide +kernel
def cuts62282 : List PrefixCut := [⟨64,197611515,197611629⟩]
theorem checked62282 : checkPrefixCuts (2^48) 8167358465 10 Manual.Count131072.C062282.packed 64 cuts62282 = true := by
 decide +kernel
def cuts62283 : List PrefixCut := [⟨8,26019419,26019434⟩,
⟨64,199779493,199779607⟩]
theorem checked62283 : checkPrefixCuts (2^48) 8167489537 10 Manual.Count131072.C062283.packed 64 cuts62283 = true := by
 decide +kernel
def pointBounds62283 : List (Nat × Nat × Nat) := [(8167505920,114377542205025,114377930876102)]
theorem point_links_checked62283 : (cuts62283.take 1).map (fun c => (8167489537-1+2*2^10*c.k,114377516185606+c.lower,114377904856668+c.upper)) = pointBounds62283 := by
 decide +kernel
def cuts62284 : List PrefixCut := [⟨64,200120907,200121019⟩]
theorem checked62284 : checkPrefixCuts (2^48) 8167620609 10 Manual.Count131072.C062284.packed 64 cuts62284 = true := by
 decide +kernel
def cuts62285 : List PrefixCut := [⟨5,15232078,15232085⟩,
⟨64,199290615,199290730⟩]
theorem checked62285 : checkPrefixCuts (2^48) 8167751681 10 Manual.Count131072.C062285.packed 64 cuts62285 = true := by
 decide +kernel
def pointBounds62285 : List (Nat × Nat × Nat) := [(8167761920,114377931318084,114378319989379)]
theorem point_links_checked62285 : (cuts62285.take 1).map (fun c => (8167751681-1+2*2^10*c.k,114377916086006+c.lower,114378304757294+c.upper)) = pointBounds62285 := by
 decide +kernel
def cuts62286 : List PrefixCut := [⟨64,197633302,197633417⟩]
theorem checked62286 : checkPrefixCuts (2^48) 8167882753 10 Manual.Count131072.C062286.packed 64 cuts62286 = true := by
 decide +kernel
def cuts62287 : List PrefixCut := [⟨2,5720464,5720466⟩,
⟨64,199525441,199525553⟩]
theorem checked62287 : checkPrefixCuts (2^48) 8168013825 10 Manual.Count131072.C062287.packed 64 cuts62287 = true := by
 decide +kernel
def pointBounds62287 : List (Nat × Nat × Nat) := [(8168017920,114378318730387,114378707401907)]
theorem point_links_checked62287 : (cuts62287.take 1).map (fun c => (8168013825-1+2*2^10*c.k,114378313009923+c.lower,114378701681441+c.upper)) = pointBounds62287 := by
 decide +kernel
def cuts62288 : List PrefixCut := [⟨63,194525586,194525700⟩,
⟨64,197937079,197937195⟩]
theorem checked62288 : checkPrefixCuts (2^48) 8168144897 10 Manual.Count131072.C062288.packed 64 cuts62288 = true := by
 decide +kernel
def pointBounds62288 : List (Nat × Nat × Nat) := [(8168273920,114378707060950,114379095732694)]
theorem point_links_checked62288 : (cuts62288.take 1).map (fun c => (8168144897-1+2*2^10*c.k,114378512535364+c.lower,114378901206994+c.upper)) = pointBounds62288 := by
 decide +kernel
def cuts62289 : List PrefixCut := [⟨64,199691326,199691441⟩]
theorem checked62289 : checkPrefixCuts (2^48) 8168275969 10 Manual.Count131072.C062289.packed 64 cuts62289 = true := by
 decide +kernel
def cuts62290 : List PrefixCut := [⟨60,184802066,184802177⟩,
⟨64,197930730,197930847⟩]
theorem checked62290 : checkPrefixCuts (2^48) 8168407041 10 Manual.Count131072.C062290.packed 64 cuts62290 = true := by
 decide +kernel
def pointBounds62290 : List (Nat × Nat × Nat) := [(8168529920,114379094965835,114379483637807)]
theorem point_links_checked62290 : (cuts62290.take 1).map (fun c => (8168407041-1+2*2^10*c.k,114378910163769+c.lower,114379298835630+c.upper)) = pointBounds62290 := by
 decide +kernel
def cuts62291 : List PrefixCut := [⟨64,196962724,196962836⟩]
theorem checked62291 : checkPrefixCuts (2^48) 8168538113 10 Manual.Count131072.C062291.packed 64 cuts62291 = true := by
 decide +kernel
def cuts62292 : List PrefixCut := [⟨57,175423733,175423835⟩,
⟨64,196546083,196546196⟩]
theorem checked62292 : checkPrefixCuts (2^48) 8168669185 10 Manual.Count131072.C062292.packed 64 cuts62292 = true := by
 decide +kernel
def pointBounds62292 : List (Nat × Nat × Nat) := [(8168785920,114379480480956,114379869153148)]
theorem point_links_checked62292 : (cuts62292.take 1).map (fun c => (8168669185-1+2*2^10*c.k,114379305057223+c.lower,114379693729313+c.upper)) = pointBounds62292 := by
 decide +kernel
def cuts62293 : List PrefixCut := [⟨64,199954179,199954290⟩]
theorem checked62293 : checkPrefixCuts (2^48) 8168800257 10 Manual.Count131072.C062293.packed 64 cuts62293 = true := by
 decide +kernel
def cuts62294 : List PrefixCut := [⟨54,169870662,169870763⟩,
⟨64,201363673,201363793⟩]
theorem checked62294 : checkPrefixCuts (2^48) 8168931329 10 Manual.Count131072.C062294.packed 64 cuts62294 = true := by
 decide +kernel
def pointBounds62294 : List (Nat × Nat × Nat) := [(8169041920,114379871428147,114380260100562)]
theorem point_links_checked62294 : (cuts62294.take 1).map (fun c => (8168931329-1+2*2^10*c.k,114379701557485+c.lower,114380090229799+c.upper)) = pointBounds62294 := by
 decide +kernel
def cuts62295 : List PrefixCut := [⟨64,196433263,196433375⟩]
theorem checked62295 : checkPrefixCuts (2^48) 8169062401 10 Manual.Count131072.C062295.packed 64 cuts62295 = true := by
 decide +kernel
def cuts62296 : List PrefixCut := [⟨51,158184897,158184989⟩,
⟨64,199186533,199186647⟩]
theorem checked62296 : checkPrefixCuts (2^48) 8169193473 10 Manual.Count131072.C062296.packed 64 cuts62296 = true := by
 decide +kernel
def pointBounds62296 : List (Nat × Nat × Nat) := [(8169297920,114380257539318,114380646211956)]
theorem point_links_checked62296 : (cuts62296.take 1).map (fun c => (8169193473-1+2*2^10*c.k,114380099354421+c.lower,114380488026967+c.upper)) = pointBounds62296 := by
 decide +kernel
def cuts62297 : List PrefixCut := [⟨64,196289121,196289239⟩]
theorem checked62297 : checkPrefixCuts (2^48) 8169324545 10 Manual.Count131072.C062297.packed 64 cuts62297 = true := by
 decide +kernel
def cuts62298 : List PrefixCut := [⟨48,146258670,146258755⟩,
⟨64,194115366,194115478⟩]
theorem checked62298 : checkPrefixCuts (2^48) 8169455617 10 Manual.Count131072.C062298.packed 64 cuts62298 = true := by
 decide +kernel
def pointBounds62298 : List (Nat × Nat × Nat) := [(8169553920,114380641088745,114381029761608)]
theorem point_links_checked62298 : (cuts62298.take 1).map (fun c => (8169455617-1+2*2^10*c.k,114380494830075+c.lower,114380883502853+c.upper)) = pointBounds62298 := by
 decide +kernel
def cuts62299 : List PrefixCut := [⟨64,198625682,198625794⟩]
theorem checked62299 : checkPrefixCuts (2^48) 8169586689 10 Manual.Count131072.C062299.packed 64 cuts62299 = true := by
 decide +kernel
def cuts62300 : List PrefixCut := [⟨45,142601994,142602078⟩,
⟨64,200689704,200689821⟩]
theorem checked62300 : checkPrefixCuts (2^48) 8169717761 10 Manual.Count131072.C062300.packed 64 cuts62300 = true := by
 decide +kernel
def pointBounds62300 : List (Nat × Nat × Nat) := [(8169809920,114381030173117,114381418846203)]
theorem point_links_checked62300 : (cuts62300.take 1).map (fun c => (8169717761-1+2*2^10*c.k,114380887571123+c.lower,114381276244125+c.upper)) = pointBounds62300 := by
 decide +kernel
def cuts62301 : List PrefixCut := [⟨64,196862231,196862340⟩]
theorem checked62301 : checkPrefixCuts (2^48) 8169848833 10 Manual.Count131072.C062301.packed 64 cuts62301 = true := by
 decide +kernel
def cuts62302 : List PrefixCut := [⟨42,129850167,129850244⟩,
⟨64,197479205,197479321⟩]
theorem checked62302 : checkPrefixCuts (2^48) 8169979905 10 Manual.Count131072.C062302.packed 64 cuts62302 = true := by
 decide +kernel
def pointBounds62302 : List (Nat × Nat × Nat) := [(8170065920,114381414973225,114381803646530)]
theorem point_links_checked62302 : (cuts62302.take 1).map (fun c => (8169979905-1+2*2^10*c.k,114381285123058+c.lower,114381673796286+c.upper)) = pointBounds62302 := by
 decide +kernel
def cuts62303 : List PrefixCut := [⟨64,198923008,198923121⟩]
theorem checked62303 : checkPrefixCuts (2^48) 8170110977 10 Manual.Count131072.C062303.packed 64 cuts62303 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000071
