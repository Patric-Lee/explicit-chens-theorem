import PlattAssemblyKernel
import PlattCertificates.Count131072.C040352
import PlattCertificates.Count131072.C040353
import PlattCertificates.Count131072.C040354
import PlattCertificates.Count131072.C040355
import PlattCertificates.Count131072.C040356
import PlattCertificates.Count131072.C040357
import PlattCertificates.Count131072.C040358
import PlattCertificates.Count131072.C040359
import PlattCertificates.Count131072.C040360
import PlattCertificates.Count131072.C040361
import PlattCertificates.Count131072.C040362
import PlattCertificates.Count131072.C040363
import PlattCertificates.Count131072.C040364
import PlattCertificates.Count131072.C040365
import PlattCertificates.Count131072.C040366
import PlattCertificates.Count131072.C040367
import PlattCertificates.Count131072.C040368
import PlattCertificates.Count131072.C040369
import PlattCertificates.Count131072.C040370
import PlattCertificates.Count131072.C040371
import PlattCertificates.Count131072.C040372
import PlattCertificates.Count131072.C040373
import PlattCertificates.Count131072.C040374
import PlattCertificates.Count131072.C040375
import PlattCertificates.Count131072.C040376
import PlattCertificates.Count131072.C040377
import PlattCertificates.Count131072.C040378
import PlattCertificates.Count131072.C040379
import PlattCertificates.Count131072.C040380
import PlattCertificates.Count131072.C040381
import PlattCertificates.Count131072.C040382
import PlattCertificates.Count131072.C040383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40352 : List PrefixCut := [⟨17,84341962,84342012⟩,
⟨64,316784671,316784856⟩]
theorem checked40352 : checkPrefixCuts (2^48) 5292949505 10 Manual.Count131072.C040352.packed 64 cuts40352 = true := by
 decide +kernel
def pointBounds40352 : List (Nat × Nat × Nat) := [(5292984320,108976413199570,108976798770594)]
theorem point_links_checked40352 : (cuts40352.take 1).map (fun c => (5292949505-1+2*2^10*c.k,108976328857608+c.lower,108976714428582+c.upper)) = pointBounds40352 := by
 decide +kernel
def cuts40353 : List PrefixCut := [⟨34,167615622,167615718⟩,
⟨64,314490195,314490377⟩]
theorem checked40353 : checkPrefixCuts (2^48) 5293080577 10 Manual.Count131072.C040353.packed 64 cuts40353 = true := by
 decide +kernel
def pointBounds40353 : List (Nat × Nat × Nat) := [(5293150208,108976813257901,108977198829156)]
theorem point_links_checked40353 : (cuts40353.take 1).map (fun c => (5293080577-1+2*2^10*c.k,108976645642279+c.lower,108977031213438+c.upper)) = pointBounds40353 := by
 decide +kernel
def cuts40354 : List PrefixCut := [⟨51,247162287,247162432⟩,
⟨64,313206127,313206312⟩]
theorem checked40354 : checkPrefixCuts (2^48) 5293211649 10 Manual.Count131072.C040354.packed 64 cuts40354 = true := by
 decide +kernel
def pointBounds40354 : List (Nat × Nat × Nat) := [(5293316096,108977207294761,108977592866247)]
theorem point_links_checked40354 : (cuts40354.take 1).map (fun c => (5293211649-1+2*2^10*c.k,108976960132474+c.lower,108977345703815+c.upper)) = pointBounds40354 := by
 decide +kernel
def cuts40355 : List PrefixCut := [⟨64,315059534,315059722⟩]
theorem checked40355 : checkPrefixCuts (2^48) 5293342721 10 Manual.Count131072.C040355.packed 64 cuts40355 = true := by
 decide +kernel
def cuts40356 : List PrefixCut := [⟨4,20365605,20365617⟩,
⟨64,307767006,307767188⟩]
theorem checked40356 : checkPrefixCuts (2^48) 5293473793 10 Manual.Count131072.C040356.packed 64 cuts40356 = true := by
 decide +kernel
def pointBounds40356 : List (Nat × Nat × Nat) := [(5293481984,108977608763740,108977994335466)]
theorem point_links_checked40356 : (cuts40356.take 1).map (fun c => (5293473793-1+2*2^10*c.k,108977588398135+c.lower,108977973969849+c.upper)) = pointBounds40356 := by
 decide +kernel
def cuts40357 : List PrefixCut := [⟨21,105813110,105813170⟩,
⟨64,313129767,313129948⟩]
theorem checked40357 : checkPrefixCuts (2^48) 5293604865 10 Manual.Count131072.C040357.packed 64 cuts40357 = true := by
 decide +kernel
def pointBounds40357 : List (Nat × Nat × Nat) := [(5293647872,108978001978251,108978387550207)]
theorem point_links_checked40357 : (cuts40357.take 1).map (fun c => (5293604865-1+2*2^10*c.k,108977896165141+c.lower,108978281737037+c.upper)) = pointBounds40357 := by
 decide +kernel
def cuts40358 : List PrefixCut := [⟨38,185832389,185832499⟩,
⟨64,313228339,313228526⟩]
theorem checked40358 : checkPrefixCuts (2^48) 5293735937 10 Manual.Count131072.C040358.packed 64 cuts40358 = true := by
 decide +kernel
def pointBounds40358 : List (Nat × Nat × Nat) := [(5293813760,108978395127297,108978780699484)]
theorem point_links_checked40358 : (cuts40358.take 1).map (fun c => (5293735937-1+2*2^10*c.k,108978209294908+c.lower,108978594866985+c.upper)) = pointBounds40358 := by
 decide +kernel
def cuts40359 : List PrefixCut := [⟨55,266538359,266538515⟩,
⟨64,309711402,309711584⟩]
theorem checked40359 : checkPrefixCuts (2^48) 5293867009 10 Manual.Count131072.C040359.packed 64 cuts40359 = true := by
 decide +kernel
def pointBounds40359 : List (Nat × Nat × Nat) := [(5293979648,108978789061606,108979174634026)]
theorem point_links_checked40359 : (cuts40359.take 1).map (fun c => (5293867009-1+2*2^10*c.k,108978522523247+c.lower,108978908095511+c.upper)) = pointBounds40359 := by
 decide +kernel
def cuts40360 : List PrefixCut := [⟨64,308374550,308374737⟩]
theorem checked40360 : checkPrefixCuts (2^48) 5293998081 10 Manual.Count131072.C040360.packed 64 cuts40360 = true := by
 decide +kernel
def cuts40361 : List PrefixCut := [⟨8,38758949,38758971⟩,
⟨64,306984580,306984765⟩]
theorem checked40361 : checkPrefixCuts (2^48) 5294129153 10 Manual.Count131072.C040361.packed 64 cuts40361 = true := by
 decide +kernel
def pointBounds40361 : List (Nat × Nat × Nat) := [(5294145536,108979179368148,108979564940803)]
theorem point_links_checked40361 : (cuts40361.take 1).map (fun c => (5294129153-1+2*2^10*c.k,108979140609199+c.lower,108979526181832+c.upper)) = pointBounds40361 := by
 decide +kernel
def cuts40362 : List PrefixCut := [⟨25,124035785,124035861⟩,
⟨64,313356832,313357021⟩]
theorem checked40362 : checkPrefixCuts (2^48) 5294260225 10 Manual.Count131072.C040362.packed 64 cuts40362 = true := by
 decide +kernel
def pointBounds40362 : List (Nat × Nat × Nat) := [(5294311424,108979571629564,108979957202458)]
theorem point_links_checked40362 : (cuts40362.take 1).map (fun c => (5294260225-1+2*2^10*c.k,108979447593779+c.lower,108979833166597+c.upper)) = pointBounds40362 := by
 decide +kernel
def cuts40363 : List PrefixCut := [⟨42,205586352,205586474⟩,
⟨64,311807308,311807495⟩]
theorem checked40363 : checkPrefixCuts (2^48) 5294391297 10 Manual.Count131072.C040363.packed 64 cuts40363 = true := by
 decide +kernel
def pointBounds40363 : List (Nat × Nat × Nat) := [(5294477312,108979966536963,108980352110092)]
theorem point_links_checked40363 : (cuts40363.take 1).map (fun c => (5294391297-1+2*2^10*c.k,108979760950611+c.lower,108980146523618+c.upper)) = pointBounds40363 := by
 decide +kernel
def cuts40364 : List PrefixCut := [⟨59,284527366,284527534⟩,
⟨64,308025037,308025220⟩]
theorem checked40364 : checkPrefixCuts (2^48) 5294522369 10 Manual.Count131072.C040364.packed 64 cuts40364 = true := by
 decide +kernel
def pointBounds40364 : List (Nat × Nat × Nat) := [(5294643200,108980357285285,108980742858647)]
theorem point_links_checked40364 : (cuts40364.take 1).map (fun c => (5294522369-1+2*2^10*c.k,108980072757919+c.lower,108980458331113+c.upper)) = pointBounds40364 := by
 decide +kernel
def cuts40365 : List PrefixCut := [⟨64,310728621,310728808⟩]
theorem checked40365 : checkPrefixCuts (2^48) 5294653441 10 Manual.Count131072.C040365.packed 64 cuts40365 = true := by
 decide +kernel
def cuts40366 : List PrefixCut := [⟨12,58742528,58742563⟩,
⟨64,310720934,310721120⟩]
theorem checked40366 : checkPrefixCuts (2^48) 5294784513 10 Manual.Count131072.C040366.packed 64 cuts40366 = true := by
 decide +kernel
def pointBounds40366 : List (Nat × Nat × Nat) := [(5294809088,108980750254105,108981135827704)]
theorem point_links_checked40366 : (cuts40366.take 1).map (fun c => (5294784513-1+2*2^10*c.k,108980691511577+c.lower,108981077085141+c.upper)) = pointBounds40366 := by
 decide +kernel
def cuts40367 : List PrefixCut := [⟨29,139011232,139011313⟩,
⟨64,307311090,307311274⟩]
theorem checked40367 : checkPrefixCuts (2^48) 5294915585 10 Manual.Count131072.C040367.packed 64 cuts40367 = true := by
 decide +kernel
def pointBounds40367 : List (Nat × Nat × Nat) := [(5294974976,108981141243743,108981526817574)]
theorem point_links_checked40367 : (cuts40367.take 1).map (fun c => (5294915585-1+2*2^10*c.k,108981002232511+c.lower,108981387806261+c.upper)) = pointBounds40367 := by
 decide +kernel
def cuts40368 : List PrefixCut := [⟨46,224856968,224857104⟩,
⟨64,311396598,311396786⟩]
theorem checked40368 : checkPrefixCuts (2^48) 5295046657 10 Manual.Count131072.C040368.packed 64 cuts40368 = true := by
 decide +kernel
def pointBounds40368 : List (Nat × Nat × Nat) := [(5295140864,108981534400569,108981919974639)]
theorem point_links_checked40368 : (cuts40368.take 1).map (fun c => (5295046657-1+2*2^10*c.k,108981309543601+c.lower,108981695117535+c.upper)) = pointBounds40368 := by
 decide +kernel
def cuts40369 : List PrefixCut := [⟨63,311761037,311761218⟩,
⟨64,317076590,317076774⟩]
theorem checked40369 : checkPrefixCuts (2^48) 5295177729 10 Manual.Count131072.C040369.packed 64 cuts40369 = true := by
 decide +kernel
def pointBounds40369 : List (Nat × Nat × Nat) := [(5295306752,108981932701236,108982318275539)]
theorem point_links_checked40369 : (cuts40369.take 1).map (fun c => (5295177729-1+2*2^10*c.k,108981620940199+c.lower,108982006514321+c.upper)) = pointBounds40369 := by
 decide +kernel
def cuts40370 : List PrefixCut := [⟨64,311859585,311859773⟩]
theorem checked40370 : checkPrefixCuts (2^48) 5295308801 10 Manual.Count131072.C040370.packed 64 cuts40370 = true := by
 decide +kernel
def cuts40371 : List PrefixCut := [⟨16,81750914,81750962⟩,
⟨64,314243778,314243963⟩]
theorem checked40371 : checkPrefixCuts (2^48) 5295439873 10 Manual.Count131072.C040371.packed 64 cuts40371 = true := by
 decide +kernel
def pointBounds40371 : List (Nat × Nat × Nat) := [(5295472640,108982331627288,108982717201830)]
theorem point_links_checked40371 : (cuts40371.take 1).map (fun c => (5295439873-1+2*2^10*c.k,108982249876374+c.lower,108982635450868+c.upper)) = pointBounds40371 := by
 decide +kernel
def cuts40372 : List PrefixCut := [⟨33,162434184,162434278⟩,
⟨64,312428828,312429013⟩]
theorem checked40372 : checkPrefixCuts (2^48) 5295570945 10 Manual.Count131072.C040372.packed 64 cuts40372 = true := by
 decide +kernel
def pointBounds40372 : List (Nat × Nat × Nat) := [(5295638528,108982726554336,108983112129109)]
theorem point_links_checked40372 : (cuts40372.take 1).map (fun c => (5295570945-1+2*2^10*c.k,108982564120152+c.lower,108982949694831+c.upper)) = pointBounds40372 := by
 decide +kernel
def cuts40373 : List PrefixCut := [⟨50,242156241,242156390⟩,
⟨64,312155317,312155507⟩]
theorem checked40373 : checkPrefixCuts (2^48) 5295702017 10 Manual.Count131072.C040373.packed 64 cuts40373 = true := by
 decide +kernel
def pointBounds40373 : List (Nat × Nat × Nat) := [(5295804416,108983118705221,108983504280234)]
theorem point_links_checked40373 : (cuts40373.take 1).map (fun c => (5295702017-1+2*2^10*c.k,108982876548980+c.lower,108983262123844+c.upper)) = pointBounds40373 := by
 decide +kernel
def cuts40374 : List PrefixCut := [⟨64,310393648,310393829⟩]
theorem checked40374 : checkPrefixCuts (2^48) 5295833089 10 Manual.Count131072.C040374.packed 64 cuts40374 = true := by
 decide +kernel
def cuts40375 : List PrefixCut := [⟨3,13606122,13606131⟩,
⟨64,310545400,310545583⟩]
theorem checked40375 : checkPrefixCuts (2^48) 5295964161 10 Manual.Count131072.C040375.packed 64 cuts40375 = true := by
 decide +kernel
def pointBounds40375 : List (Nat × Nat × Nat) := [(5295970304,108983512704067,108983898279311)]
theorem point_links_checked40375 : (cuts40375.take 1).map (fun c => (5295964161-1+2*2^10*c.k,108983499097945+c.lower,108983884673180+c.upper)) = pointBounds40375 := by
 decide +kernel
def cuts40376 : List PrefixCut := [⟨20,98801054,98801117⟩,
⟨64,311069213,311069403⟩]
theorem checked40376 : checkPrefixCuts (2^48) 5296095233 10 Manual.Count131072.C040376.packed 64 cuts40376 = true := by
 decide +kernel
def pointBounds40376 : List (Nat × Nat × Nat) := [(5296136192,108983908444399,108984294019880)]
theorem point_links_checked40376 : (cuts40376.take 1).map (fun c => (5296095233-1+2*2^10*c.k,108983809643345+c.lower,108984195218763+c.upper)) = pointBounds40376 := by
 decide +kernel
def cuts40377 : List PrefixCut := [⟨37,176231911,176232020⟩,
⟨64,308085335,308085523⟩]
theorem checked40377 : checkPrefixCuts (2^48) 5296226305 10 Manual.Count131072.C040377.packed 64 cuts40377 = true := by
 decide +kernel
def pointBounds40377 : List (Nat × Nat × Nat) := [(5296302080,108984296944469,108984682520186)]
theorem point_links_checked40377 : (cuts40377.take 1).map (fun c => (5296226305-1+2*2^10*c.k,108984120712558+c.lower,108984506288166+c.upper)) = pointBounds40377 := by
 decide +kernel
def cuts40378 : List PrefixCut := [⟨54,261470640,261470798⟩,
⟨64,309884627,309884814⟩]
theorem checked40378 : checkPrefixCuts (2^48) 5296357377 10 Manual.Count131072.C040378.packed 64 cuts40378 = true := by
 decide +kernel
def pointBounds40378 : List (Nat × Nat × Nat) := [(5296467968,108984690268533,108985075844487)]
theorem point_links_checked40378 : (cuts40378.take 1).map (fun c => (5296357377-1+2*2^10*c.k,108984428797893+c.lower,108984814373689+c.upper)) = pointBounds40378 := by
 decide +kernel
def cuts40379 : List PrefixCut := [⟨64,306635244,306635424⟩]
theorem checked40379 : checkPrefixCuts (2^48) 5296488449 10 Manual.Count131072.C040379.packed 64 cuts40379 = true := by
 decide +kernel
def cuts40380 : List PrefixCut := [⟨7,35339626,35339647⟩,
⟨64,308062515,308062694⟩]
theorem checked40380 : checkPrefixCuts (2^48) 5296619521 10 Manual.Count131072.C040380.packed 64 cuts40380 = true := by
 decide +kernel
def pointBounds40380 : List (Nat × Nat × Nat) := [(5296633856,108985080657390,108985466233574)]
theorem point_links_checked40380 : (cuts40380.take 1).map (fun c => (5296619521-1+2*2^10*c.k,108985045317764+c.lower,108985430893927+c.upper)) = pointBounds40380 := by
 decide +kernel
def cuts40381 : List PrefixCut := [⟨24,119354251,119354320⟩,
⟨64,311402738,311402919⟩]
theorem checked40381 : checkPrefixCuts (2^48) 5296750593 10 Manual.Count131072.C040381.packed 64 cuts40381 = true := by
 decide +kernel
def pointBounds40381 : List (Nat × Nat × Nat) := [(5296799744,108985472734530,108985858310941)]
theorem point_links_checked40381 : (cuts40381.take 1).map (fun c => (5296750593-1+2*2^10*c.k,108985353380279+c.lower,108985738956621+c.upper)) = pointBounds40381 := by
 decide +kernel
def cuts40382 : List PrefixCut := [⟨41,199059889,199060004⟩,
⟨64,308950633,308950812⟩]
theorem checked40382 : checkPrefixCuts (2^48) 5296881665 10 Manual.Count131072.C040382.packed 64 cuts40382 = true := by
 decide +kernel
def pointBounds40382 : List (Nat × Nat × Nat) := [(5296965632,108985863842906,108986249419544)]
theorem point_links_checked40382 : (cuts40382.take 1).map (fun c => (5296881665-1+2*2^10*c.k,108985664783017+c.lower,108986050359540+c.upper)) = pointBounds40382 := by
 decide +kernel
def cuts40383 : List PrefixCut := [⟨58,285137596,285137765⟩,
⟨64,313565979,313566166⟩]
theorem checked40383 : checkPrefixCuts (2^48) 5297012737 10 Manual.Count131072.C040383.packed 64 cuts40383 = true := by
 decide +kernel
def pointBounds40383 : List (Nat × Nat × Nat) := [(5297131520,108986258871246,108986644448117)]
theorem point_links_checked40383 : (cuts40383.take 1).map (fun c => (5297012737-1+2*2^10*c.k,108985973733650+c.lower,108986359310352+c.upper)) = pointBounds40383 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000011
