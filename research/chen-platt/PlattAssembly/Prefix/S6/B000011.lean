import PlattAssemblyKernel
import PlattCertificates.Count131072.C050352
import PlattCertificates.Count131072.C050353
import PlattCertificates.Count131072.C050354
import PlattCertificates.Count131072.C050355
import PlattCertificates.Count131072.C050356
import PlattCertificates.Count131072.C050357
import PlattCertificates.Count131072.C050358
import PlattCertificates.Count131072.C050359
import PlattCertificates.Count131072.C050360
import PlattCertificates.Count131072.C050361
import PlattCertificates.Count131072.C050362
import PlattCertificates.Count131072.C050363
import PlattCertificates.Count131072.C050364
import PlattCertificates.Count131072.C050365
import PlattCertificates.Count131072.C050366
import PlattCertificates.Count131072.C050367
import PlattCertificates.Count131072.C050368
import PlattCertificates.Count131072.C050369
import PlattCertificates.Count131072.C050370
import PlattCertificates.Count131072.C050371
import PlattCertificates.Count131072.C050372
import PlattCertificates.Count131072.C050373
import PlattCertificates.Count131072.C050374
import PlattCertificates.Count131072.C050375
import PlattCertificates.Count131072.C050376
import PlattCertificates.Count131072.C050377
import PlattCertificates.Count131072.C050378
import PlattCertificates.Count131072.C050379
import PlattCertificates.Count131072.C050380
import PlattCertificates.Count131072.C050381
import PlattCertificates.Count131072.C050382
import PlattCertificates.Count131072.C050383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50352 : List PrefixCut := [⟨7,26085867,26085882⟩,
⟨64,245639733,245639874⟩]
theorem checked50352 : checkPrefixCuts (2^48) 6603669505 10 Manual.Count131072.C050352.packed 64 cuts50352 = true := by
 decide +kernel
def pointBounds50352 : List (Nat × Nat × Nat) := [(6603683840,111744205128921,111744592300663)]
theorem point_links_checked50352 : (cuts50352.take 1).map (fun c => (6603669505-1+2*2^10*c.k,111744179043054+c.lower,111744566214781+c.upper)) = pointBounds50352 := by
 decide +kernel
def cuts50353 : List PrefixCut := [⟨44,169468556,169468650⟩,
⟨64,243546385,243546522⟩]
theorem checked50353 : checkPrefixCuts (2^48) 6603800577 10 Manual.Count131072.C050353.packed 64 cuts50353 = true := by
 decide +kernel
def pointBounds50353 : List (Nat × Nat × Nat) := [(6603890688,111744594151343,111744981323305)]
theorem point_links_checked50353 : (cuts50353.take 1).map (fun c => (6603800577-1+2*2^10*c.k,111744424682787+c.lower,111744811854655+c.upper)) = pointBounds50353 := by
 decide +kernel
def cuts50354 : List PrefixCut := [⟨64,247548005,247548147⟩]
theorem checked50354 : checkPrefixCuts (2^48) 6603931649 10 Manual.Count131072.C050354.packed 64 cuts50354 = true := by
 decide +kernel
def cuts50355 : List PrefixCut := [⟨17,65935250,65935287⟩,
⟨64,248054527,248054666⟩]
theorem checked50355 : checkPrefixCuts (2^48) 6604062721 10 Manual.Count131072.C050355.packed 64 cuts50355 = true := by
 decide +kernel
def pointBounds50355 : List (Nat × Nat × Nat) := [(6604097536,111744981712427,111745368884611)]
theorem point_links_checked50355 : (cuts50355.take 1).map (fun c => (6604062721-1+2*2^10*c.k,111744915777177+c.lower,111745302949324+c.upper)) = pointBounds50355 := by
 decide +kernel
def cuts50356 : List PrefixCut := [⟨54,206878800,206878919⟩,
⟨64,245151424,245151564⟩]
theorem checked50356 : checkPrefixCuts (2^48) 6604193793 10 Manual.Count131072.C050356.packed 64 cuts50356 = true := by
 decide +kernel
def pointBounds50356 : List (Nat × Nat × Nat) := [(6604304384,111745370710504,111745757882909)]
theorem point_links_checked50356 : (cuts50356.take 1).map (fun c => (6604193793-1+2*2^10*c.k,111745163831704+c.lower,111745551003990+c.upper)) = pointBounds50356 := by
 decide +kernel
def cuts50357 : List PrefixCut := [⟨64,246979202,246979341⟩]
theorem checked50357 : checkPrefixCuts (2^48) 6604324865 10 Manual.Count131072.C050357.packed 64 cuts50357 = true := by
 decide +kernel
def cuts50358 : List PrefixCut := [⟨27,103563586,103563645⟩,
⟨64,244587655,244587795⟩]
theorem checked50358 : checkPrefixCuts (2^48) 6604455937 10 Manual.Count131072.C050358.packed 64 cuts50358 = true := by
 decide +kernel
def pointBounds50358 : List (Nat × Nat × Nat) := [(6604511232,111745759525916,111746146698540)]
theorem point_links_checked50358 : (cuts50358.take 1).map (fun c => (6604455937-1+2*2^10*c.k,111745655962330+c.lower,111746043134895+c.upper)) = pointBounds50358 := by
 decide +kernel
def cuts50359 : List PrefixCut := [⟨64,247352951,247353092⟩]
theorem checked50359 : checkPrefixCuts (2^48) 6604587009 10 Manual.Count131072.C050359.packed 64 cuts50359 = true := by
 decide +kernel
def pointBounds50359 : List (Nat × Nat × Nat) := [(6604718080,111746147902936,111746535075782)]
theorem point_links_checked50359 : (cuts50359.take 1).map (fun c => (6604587009-1+2*2^10*c.k,111745900549985+c.lower,111746287722690+c.upper)) = pointBounds50359 := by
 decide +kernel
def cuts50360 : List PrefixCut := [⟨64,248413467,248413602⟩]
theorem checked50360 : checkPrefixCuts (2^48) 6604718081 10 Manual.Count131072.C050360.packed 64 cuts50360 = true := by
 decide +kernel
def cuts50361 : List PrefixCut := [⟨37,144383541,144383624⟩,
⟨64,247130070,247130213⟩]
theorem checked50361 : checkPrefixCuts (2^48) 6604849153 10 Manual.Count131072.C050361.packed 64 cuts50361 = true := by
 decide +kernel
def pointBounds50361 : List (Nat × Nat × Nat) := [(6604924928,111746540699944,111746927873008)]
theorem point_links_checked50361 : (cuts50361.take 1).map (fun c => (6604849153-1+2*2^10*c.k,111746396316403+c.lower,111746783489384+c.upper)) = pointBounds50361 := by
 decide +kernel
def cuts50362 : List PrefixCut := [⟨64,247082510,247082651⟩]
theorem checked50362 : checkPrefixCuts (2^48) 6604980225 10 Manual.Count131072.C050362.packed 64 cuts50362 = true := by
 decide +kernel
def cuts50363 : List PrefixCut := [⟨10,39461160,39461181⟩,
⟨64,244392954,244393093⟩]
theorem checked50363 : checkPrefixCuts (2^48) 6605111297 10 Manual.Count131072.C050363.packed 64 cuts50363 = true := by
 decide +kernel
def pointBounds50363 : List (Nat × Nat × Nat) := [(6605131776,111746929990143,111747317163429)]
theorem point_links_checked50363 : (cuts50363.take 1).map (fun c => (6605111297-1+2*2^10*c.k,111746890528983+c.lower,111747277702248+c.upper)) = pointBounds50363 := by
 decide +kernel
def cuts50364 : List PrefixCut := [⟨47,182556465,182556569⟩,
⟨64,245666510,245666649⟩]
theorem checked50364 : checkPrefixCuts (2^48) 6605242369 10 Manual.Count131072.C050364.packed 64 cuts50364 = true := by
 decide +kernel
def pointBounds50364 : List (Nat × Nat × Nat) := [(6605338624,111747317478402,111747704651910)]
theorem point_links_checked50364 : (cuts50364.take 1).map (fun c => (6605242369-1+2*2^10*c.k,111747134921937+c.lower,111747522095341+c.upper)) = pointBounds50364 := by
 decide +kernel
def cuts50365 : List PrefixCut := [⟨64,249795035,249795174⟩]
theorem checked50365 : checkPrefixCuts (2^48) 6605373441 10 Manual.Count131072.C050365.packed 64 cuts50365 = true := by
 decide +kernel
def cuts50366 : List PrefixCut := [⟨20,76744285,76744328⟩,
⟨64,244548840,244548977⟩]
theorem checked50366 : checkPrefixCuts (2^48) 6605504513 10 Manual.Count131072.C050366.packed 64 cuts50366 = true := by
 decide +kernel
def pointBounds50366 : List (Nat × Nat × Nat) := [(6605545472,111747707127767,111748094301492)]
theorem point_links_checked50366 : (cuts50366.take 1).map (fun c => (6605504513-1+2*2^10*c.k,111747630383482+c.lower,111748017557164+c.upper)) = pointBounds50366 := by
 decide +kernel
def cuts50367 : List PrefixCut := [⟨57,219318565,219318691⟩,
⟨64,246035365,246035507⟩]
theorem checked50367 : checkPrefixCuts (2^48) 6605635585 10 Manual.Count131072.C050367.packed 64 cuts50367 = true := by
 decide +kernel
def pointBounds50367 : List (Nat × Nat × Nat) := [(6605752320,111748094250887,111748481424832)]
theorem point_links_checked50367 : (cuts50367.take 1).map (fun c => (6605635585-1+2*2^10*c.k,111747874932322+c.lower,111748262106141+c.upper)) = pointBounds50367 := by
 decide +kernel
def cuts50368 : List PrefixCut := [⟨64,248203569,248203711⟩]
theorem checked50368 : checkPrefixCuts (2^48) 6605766657 10 Manual.Count131072.C050368.packed 64 cuts50368 = true := by
 decide +kernel
def cuts50369 : List PrefixCut := [⟨30,117218568,117218636⟩,
⟨64,251266541,251266684⟩]
theorem checked50369 : checkPrefixCuts (2^48) 6605897729 10 Manual.Count131072.C050369.packed 64 cuts50369 = true := by
 decide +kernel
def pointBounds50369 : List (Nat × Nat × Nat) := [(6605959168,111748486389824,111748873563995)]
theorem point_links_checked50369 : (cuts50369.take 1).map (fun c => (6605897729-1+2*2^10*c.k,111748369171256+c.lower,111748756345359+c.upper)) = pointBounds50369 := by
 decide +kernel
def cuts50370 : List PrefixCut := [⟨64,249386770,249386915⟩]
theorem checked50370 : checkPrefixCuts (2^48) 6606028801 10 Manual.Count131072.C050370.packed 64 cuts50370 = true := by
 decide +kernel
def cuts50371 : List PrefixCut := [⟨3,11589356,11589362⟩,
⟨64,246271482,246271623⟩]
theorem checked50371 : checkPrefixCuts (2^48) 6606159873 10 Manual.Count131072.C050371.packed 64 cuts50371 = true := by
 decide +kernel
def pointBounds50371 : List (Nat × Nat × Nat) := [(6606166016,111748881413923,111749268588320)]
theorem point_links_checked50371 : (cuts50371.take 1).map (fun c => (6606159873-1+2*2^10*c.k,111748869824567+c.lower,111749256998958+c.upper)) = pointBounds50371 := by
 decide +kernel
def cuts50372 : List PrefixCut := [⟨40,153640256,153640344⟩,
⟨64,246181384,246181529⟩]
theorem checked50372 : checkPrefixCuts (2^48) 6606290945 10 Manual.Count131072.C050372.packed 64 cuts50372 = true := by
 decide +kernel
def pointBounds50372 : List (Nat × Nat × Nat) := [(6606372864,111749269736305,111749656910925)]
theorem point_links_checked50372 : (cuts50372.take 1).map (fun c => (6606290945-1+2*2^10*c.k,111749116096049+c.lower,111749503270581+c.upper)) = pointBounds50372 := by
 decide +kernel
def cuts50373 : List PrefixCut := [⟨64,245026136,245026278⟩]
theorem checked50373 : checkPrefixCuts (2^48) 6606422017 10 Manual.Count131072.C050373.packed 64 cuts50373 = true := by
 decide +kernel
def cuts50374 : List PrefixCut := [⟨13,49166543,49166571⟩,
⟨64,247620176,247620311⟩]
theorem checked50374 : checkPrefixCuts (2^48) 6606553089 10 Manual.Count131072.C050374.packed 64 cuts50374 = true := by
 decide +kernel
def pointBounds50374 : List (Nat × Nat × Nat) := [(6606579712,111749656470112,111750043644959)]
theorem point_links_checked50374 : (cuts50374.take 1).map (fun c => (6606553089-1+2*2^10*c.k,111749607303569+c.lower,111749994478388+c.upper)) = pointBounds50374 := by
 decide +kernel
def cuts50375 : List PrefixCut := [⟨50,192145105,192145210⟩,
⟨64,246038924,246039060⟩]
theorem checked50375 : checkPrefixCuts (2^48) 6606684161 10 Manual.Count131072.C050375.packed 64 cuts50375 = true := by
 decide +kernel
def pointBounds50375 : List (Nat × Nat × Nat) := [(6606786560,111750047068850,111750434243909)]
theorem point_links_checked50375 : (cuts50375.take 1).map (fun c => (6606684161-1+2*2^10*c.k,111749854923745+c.lower,111750242098699+c.upper)) = pointBounds50375 := by
 decide +kernel
def cuts50376 : List PrefixCut := [⟨64,248888445,248888586⟩]
theorem checked50376 : checkPrefixCuts (2^48) 6606815233 10 Manual.Count131072.C050376.packed 64 cuts50376 = true := by
 decide +kernel
def cuts50377 : List PrefixCut := [⟨23,85674068,85674119⟩,
⟨64,243813802,243813945⟩]
theorem checked50377 : checkPrefixCuts (2^48) 6606946305 10 Manual.Count131072.C050377.packed 64 cuts50377 = true := by
 decide +kernel
def pointBounds50377 : List (Nat × Nat × Nat) := [(6606993408,111750435525182,111750822700464)]
theorem point_links_checked50377 : (cuts50377.take 1).map (fun c => (6606946305-1+2*2^10*c.k,111750349851114+c.lower,111750737026345+c.upper)) = pointBounds50377 := by
 decide +kernel
def cuts50378 : List PrefixCut := [⟨60,228600375,228600501⟩,
⟨64,244277620,244277755⟩]
theorem checked50378 : checkPrefixCuts (2^48) 6607077377 10 Manual.Count131072.C050378.packed 64 cuts50378 = true := by
 decide +kernel
def pointBounds50378 : List (Nat × Nat × Nat) := [(6607200256,111750822265291,111751209440791)]
theorem point_links_checked50378 : (cuts50378.take 1).map (fun c => (6607077377-1+2*2^10*c.k,111750593664916+c.lower,111750980840290+c.upper)) = pointBounds50378 := by
 decide +kernel
def cuts50379 : List PrefixCut := [⟨64,247510427,247510569⟩]
theorem checked50379 : checkPrefixCuts (2^48) 6607208449 10 Manual.Count131072.C050379.packed 64 cuts50379 = true := by
 decide +kernel
def cuts50380 : List PrefixCut := [⟨33,130952768,130952842⟩,
⟨64,246568345,246568486⟩]
theorem checked50380 : checkPrefixCuts (2^48) 6607339521 10 Manual.Count131072.C050380.packed 64 cuts50380 = true := by
 decide +kernel
def pointBounds50380 : List (Nat × Nat × Nat) := [(6607407104,111751216405731,111751603581456)]
theorem point_links_checked50380 : (cuts50380.take 1).map (fun c => (6607339521-1+2*2^10*c.k,111751085452963+c.lower,111751472628614+c.upper)) = pointBounds50380 := by
 decide +kernel
def cuts50381 : List PrefixCut := [⟨64,244902060,244902196⟩]
theorem checked50381 : checkPrefixCuts (2^48) 6607470593 10 Manual.Count131072.C050381.packed 64 cuts50381 = true := by
 decide +kernel
def cuts50382 : List PrefixCut := [⟨6,23131044,23131058⟩,
⟨64,244769407,244769553⟩]
theorem checked50382 : checkPrefixCuts (2^48) 6607601665 10 Manual.Count131072.C050382.packed 64 cuts50382 = true := by
 decide +kernel
def pointBounds50382 : List (Nat × Nat × Nat) := [(6607613952,111751600054412,111751987230354)]
theorem point_links_checked50382 : (cuts50382.take 1).map (fun c => (6607601665-1+2*2^10*c.k,111751576923368+c.lower,111751964099296+c.upper)) = pointBounds50382 := by
 decide +kernel
def cuts50383 : List PrefixCut := [⟨43,166428516,166428614⟩,
⟨64,248300136,248300283⟩]
theorem checked50383 : checkPrefixCuts (2^48) 6607732737 10 Manual.Count131072.C050383.packed 64 cuts50383 = true := by
 decide +kernel
def pointBounds50383 : List (Nat × Nat × Nat) := [(6607820800,111751988121291,111752375297463)]
theorem point_links_checked50383 : (cuts50383.take 1).map (fun c => (6607732737-1+2*2^10*c.k,111751821692775+c.lower,111752208868849+c.upper)) = pointBounds50383 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000011
