import PlattAssemblyKernel
import PlattCertificates.Count131072.C060352
import PlattCertificates.Count131072.C060353
import PlattCertificates.Count131072.C060354
import PlattCertificates.Count131072.C060355
import PlattCertificates.Count131072.C060356
import PlattCertificates.Count131072.C060357
import PlattCertificates.Count131072.C060358
import PlattCertificates.Count131072.C060359
import PlattCertificates.Count131072.C060360
import PlattCertificates.Count131072.C060361
import PlattCertificates.Count131072.C060362
import PlattCertificates.Count131072.C060363
import PlattCertificates.Count131072.C060364
import PlattCertificates.Count131072.C060365
import PlattCertificates.Count131072.C060366
import PlattCertificates.Count131072.C060367
import PlattCertificates.Count131072.C060368
import PlattCertificates.Count131072.C060369
import PlattCertificates.Count131072.C060370
import PlattCertificates.Count131072.C060371
import PlattCertificates.Count131072.C060372
import PlattCertificates.Count131072.C060373
import PlattCertificates.Count131072.C060374
import PlattCertificates.Count131072.C060375
import PlattCertificates.Count131072.C060376
import PlattCertificates.Count131072.C060377
import PlattCertificates.Count131072.C060378
import PlattCertificates.Count131072.C060379
import PlattCertificates.Count131072.C060380
import PlattCertificates.Count131072.C060381
import PlattCertificates.Count131072.C060382
import PlattCertificates.Count131072.C060383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60352 : List PrefixCut := [⟨33,106089799,106089858⟩,
⟨64,205812677,205812796⟩]
theorem checked60352 : checkPrefixCuts (2^48) 7914389505 10 Manual.Count131072.C060352.packed 64 cuts60352 = true := by
 decide +kernel
def pointBounds60352 : List (Nat × Nat × Nat) := [(7914457088,113989124886992,113989513335536)]
theorem point_links_checked60352 : (cuts60352.take 1).map (fun c => (7914389505-1+2*2^10*c.k,113989018797193+c.lower,113989407245678+c.upper)) = pointBounds60352 := by
 decide +kernel
def cuts60353 : List PrefixCut := [⟨64,202679645,202679757⟩]
theorem checked60353 : checkPrefixCuts (2^48) 7914520577 10 Manual.Count131072.C060353.packed 64 cuts60353 = true := by
 decide +kernel
def cuts60354 : List PrefixCut := [⟨26,84961574,84961624⟩,
⟨64,204454469,204454591⟩]
theorem checked60354 : checkPrefixCuts (2^48) 7914651649 10 Manual.Count131072.C060354.packed 64 cuts60354 = true := by
 decide +kernel
def pointBounds60354 : List (Nat × Nat × Nat) := [(7914704896,113989512251089,113989900699855)]
theorem point_links_checked60354 : (cuts60354.take 1).map (fun c => (7914651649-1+2*2^10*c.k,113989427289515+c.lower,113989815738231+c.upper)) = pointBounds60354 := by
 decide +kernel
def cuts60355 : List PrefixCut := [⟨64,204024321,204024438⟩]
theorem checked60355 : checkPrefixCuts (2^48) 7914782721 10 Manual.Count131072.C060355.packed 64 cuts60355 = true := by
 decide +kernel
def cuts60356 : List PrefixCut := [⟨19,60242895,60242928⟩,
⟨64,203771985,203772104⟩]
theorem checked60356 : checkPrefixCuts (2^48) 7914913793 10 Manual.Count131072.C060356.packed 64 cuts60356 = true := by
 decide +kernel
def pointBounds60356 : List (Nat × Nat × Nat) := [(7914952704,113989896011200,113990284460188)]
theorem point_links_checked60356 : (cuts60356.take 1).map (fun c => (7914913793-1+2*2^10*c.k,113989835768305+c.lower,113990224217260+c.upper)) = pointBounds60356 := by
 decide +kernel
def cuts60357 : List PrefixCut := [⟨64,202523958,202524076⟩]
theorem checked60357 : checkPrefixCuts (2^48) 7915044865 10 Manual.Count131072.C060357.packed 64 cuts60357 = true := by
 decide +kernel
def cuts60358 : List PrefixCut := [⟨12,37837290,37837314⟩,
⟨64,201489345,201489464⟩]
theorem checked60358 : checkPrefixCuts (2^48) 7915175937 10 Manual.Count131072.C060358.packed 64 cuts60358 = true := by
 decide +kernel
def pointBounds60358 : List (Nat × Nat × Nat) := [(7915200512,113990279901538,113990668350754)]
theorem point_links_checked60358 : (cuts60358.take 1).map (fun c => (7915175937-1+2*2^10*c.k,113990242064248+c.lower,113990630513440+c.upper)) = pointBounds60358 := by
 decide +kernel
def cuts60359 : List PrefixCut := [⟨64,204117481,204117597⟩]
theorem checked60359 : checkPrefixCuts (2^48) 7915307009 10 Manual.Count131072.C060359.packed 64 cuts60359 = true := by
 decide +kernel
def cuts60360 : List PrefixCut := [⟨5,15788738,15788748⟩,
⟨64,204931972,204932090⟩]
theorem checked60360 : checkPrefixCuts (2^48) 7915438081 10 Manual.Count131072.C060360.packed 64 cuts60360 = true := by
 decide +kernel
def pointBounds60360 : List (Nat × Nat × Nat) := [(7915448320,113990663459812,113991051909249)]
theorem point_links_checked60360 : (cuts60360.take 1).map (fun c => (7915438081-1+2*2^10*c.k,113990647671074+c.lower,113991036120501+c.upper)) = pointBounds60360 := by
 decide +kernel
def cuts60361 : List PrefixCut := [⟨62,196145477,196145583⟩,
⟨64,202652787,202652897⟩]
theorem checked60361 : checkPrefixCuts (2^48) 7915569153 10 Manual.Count131072.C060361.packed 64 cuts60361 = true := by
 decide +kernel
def pointBounds60361 : List (Nat × Nat × Nat) := [(7915696128,113991048748523,113991437198174)]
theorem point_links_checked60361 : (cuts60361.take 1).map (fun c => (7915569153-1+2*2^10*c.k,113990852603046+c.lower,113991241052591+c.upper)) = pointBounds60361 := by
 decide +kernel
def cuts60362 : List PrefixCut := [⟨64,204391826,204391939⟩]
theorem checked60362 : checkPrefixCuts (2^48) 7915700225 10 Manual.Count131072.C060362.packed 64 cuts60362 = true := by
 decide +kernel
def cuts60363 : List PrefixCut := [⟨55,178573397,178573500⟩,
⟨64,207055300,207055417⟩]
theorem checked60363 : checkPrefixCuts (2^48) 7915831297 10 Manual.Count131072.C060363.packed 64 cuts60363 = true := by
 decide +kernel
def pointBounds60363 : List (Nat × Nat × Nat) := [(7915943936,113991438221056,113991826670927)]
theorem point_links_checked60363 : (cuts60363.take 1).map (fun c => (7915831297-1+2*2^10*c.k,113991259647659+c.lower,113991648097427+c.upper)) = pointBounds60363 := by
 decide +kernel
def cuts60364 : List PrefixCut := [⟨64,203282741,203282856⟩]
theorem checked60364 : checkPrefixCuts (2^48) 7915962369 10 Manual.Count131072.C060364.packed 64 cuts60364 = true := by
 decide +kernel
def cuts60365 : List PrefixCut := [⟨48,154779963,154780053⟩,
⟨64,203634983,203635100⟩]
theorem checked60365 : checkPrefixCuts (2^48) 7916093441 10 Manual.Count131072.C060365.packed 64 cuts60365 = true := by
 decide +kernel
def pointBounds60365 : List (Nat × Nat × Nat) := [(7916191744,113991824765663,113992213215753)]
theorem point_links_checked60365 : (cuts60365.take 1).map (fun c => (7916093441-1+2*2^10*c.k,113991669985700+c.lower,113992058435700+c.upper)) = pointBounds60365 := by
 decide +kernel
def cuts60366 : List PrefixCut := [⟨64,205231637,205231751⟩]
theorem checked60366 : checkPrefixCuts (2^48) 7916224513 10 Manual.Count131072.C060366.packed 64 cuts60366 = true := by
 decide +kernel
def cuts60367 : List PrefixCut := [⟨41,130952501,130952573⟩,
⟨64,205477119,205477234⟩]
theorem checked60367 : checkPrefixCuts (2^48) 7916355585 10 Manual.Count131072.C060367.packed 64 cuts60367 = true := by
 decide +kernel
def pointBounds60367 : List (Nat × Nat × Nat) := [(7916439552,113992209804821,113992598255124)]
theorem point_links_checked60367 : (cuts60367.take 1).map (fun c => (7916355585-1+2*2^10*c.k,113992078852320+c.lower,113992467302551+c.upper)) = pointBounds60367 := by
 decide +kernel
def cuts60368 : List PrefixCut := [⟨64,201455972,201456088⟩]
theorem checked60368 : checkPrefixCuts (2^48) 7916486657 10 Manual.Count131072.C060368.packed 64 cuts60368 = true := by
 decide +kernel
def cuts60369 : List PrefixCut := [⟨34,108690983,108691048⟩,
⟨64,204439232,204439348⟩]
theorem checked60369 : checkPrefixCuts (2^48) 7916617729 10 Manual.Count131072.C060369.packed 64 cuts60369 = true := by
 decide +kernel
def pointBounds60369 : List (Nat × Nat × Nat) := [(7916687360,113992594476394,113992982926921)]
theorem point_links_checked60369 : (cuts60369.take 1).map (fun c => (7916617729-1+2*2^10*c.k,113992485785411+c.lower,113992874235873+c.upper)) = pointBounds60369 := by
 decide +kernel
def cuts60370 : List PrefixCut := [⟨64,200702652,200702767⟩]
theorem checked60370 : checkPrefixCuts (2^48) 7916748801 10 Manual.Count131072.C060370.packed 64 cuts60370 = true := by
 decide +kernel
def cuts60371 : List PrefixCut := [⟨27,86715333,86715383⟩,
⟨64,206174576,206174694⟩]
theorem checked60371 : checkPrefixCuts (2^48) 7916879873 10 Manual.Count131072.C060371.packed 64 cuts60371 = true := by
 decide +kernel
def pointBounds60371 : List (Nat × Nat × Nat) := [(7916935168,113992977642628,113993366093371)]
theorem point_links_checked60371 : (cuts60371.take 1).map (fun c => (7916879873-1+2*2^10*c.k,113992890927295+c.lower,113993279377988+c.upper)) = pointBounds60371 := by
 decide +kernel
def cuts60372 : List PrefixCut := [⟨64,203931333,203931452⟩]
theorem checked60372 : checkPrefixCuts (2^48) 7917010945 10 Manual.Count131072.C060372.packed 64 cuts60372 = true := by
 decide +kernel
def cuts60373 : List PrefixCut := [⟨20,63852286,63852321⟩,
⟨64,206345520,206345637⟩]
theorem checked60373 : checkPrefixCuts (2^48) 7917142017 10 Manual.Count131072.C060373.packed 64 cuts60373 = true := by
 decide +kernel
def pointBounds60373 : List (Nat × Nat × Nat) := [(7917182976,113993364885490,113993753336455)]
theorem point_links_checked60373 : (cuts60373.take 1).map (fun c => (7917142017-1+2*2^10*c.k,113993301033204+c.lower,113993689484134+c.upper)) = pointBounds60373 := by
 decide +kernel
def cuts60374 : List PrefixCut := [⟨64,204315654,204315772⟩]
theorem checked60374 : checkPrefixCuts (2^48) 7917273089 10 Manual.Count131072.C060374.packed 64 cuts60374 = true := by
 decide +kernel
def cuts60375 : List PrefixCut := [⟨13,41026260,41026284⟩,
⟨64,204276719,204276833⟩]
theorem checked60375 : checkPrefixCuts (2^48) 7917404161 10 Manual.Count131072.C060375.packed 64 cuts60375 = true := by
 decide +kernel
def pointBounds60375 : List (Nat × Nat × Nat) := [(7917430784,113993752720638,113994141171827)]
theorem point_links_checked60375 : (cuts60375.take 1).map (fun c => (7917404161-1+2*2^10*c.k,113993711694378+c.lower,113994100145543+c.upper)) = pointBounds60375 := by
 decide +kernel
def cuts60376 : List PrefixCut := [⟨64,207224025,207224143⟩]
theorem checked60376 : checkPrefixCuts (2^48) 7917535233 10 Manual.Count131072.C060376.packed 64 cuts60376 = true := by
 decide +kernel
def cuts60377 : List PrefixCut := [⟨6,19197113,19197123⟩,
⟨64,202741321,202741432⟩]
theorem checked60377 : checkPrefixCuts (2^48) 7917666305 10 Manual.Count131072.C060377.packed 64 cuts60377 = true := by
 decide +kernel
def pointBounds60377 : List (Nat × Nat × Nat) := [(7917678592,113994142392235,113994530843642)]
theorem point_links_checked60377 : (cuts60377.take 1).map (fun c => (7917666305-1+2*2^10*c.k,113994123195122+c.lower,113994511646519+c.upper)) = pointBounds60377 := by
 decide +kernel
def cuts60378 : List PrefixCut := [⟨63,200569460,200569573⟩,
⟨64,203875523,203875638⟩]
theorem checked60378 : checkPrefixCuts (2^48) 7917797377 10 Manual.Count131072.C060378.packed 64 cuts60378 = true := by
 decide +kernel
def pointBounds60378 : List (Nat × Nat × Nat) := [(7917926400,113994526505903,113994914957524)]
theorem point_links_checked60378 : (cuts60378.take 1).map (fun c => (7917797377-1+2*2^10*c.k,113994325936443+c.lower,113994714387951+c.upper)) = pointBounds60378 := by
 decide +kernel
def cuts60379 : List PrefixCut := [⟨64,201845884,201845999⟩]
theorem checked60379 : checkPrefixCuts (2^48) 7917928449 10 Manual.Count131072.C060379.packed 64 cuts60379 = true := by
 decide +kernel
def cuts60380 : List PrefixCut := [⟨56,176674606,176674710⟩,
⟨64,202482394,202482513⟩]
theorem checked60380 : checkPrefixCuts (2^48) 7918059521 10 Manual.Count131072.C060380.packed 64 cuts60380 = true := by
 decide +kernel
def pointBounds60380 : List (Nat × Nat × Nat) := [(7918174208,113994908332456,113995296784298)]
theorem point_links_checked60380 : (cuts60380.take 1).map (fun c => (7918059521-1+2*2^10*c.k,113994731657850+c.lower,113995120109588+c.upper)) = pointBounds60380 := by
 decide +kernel
def cuts60381 : List PrefixCut := [⟨64,202585703,202585817⟩]
theorem checked60381 : checkPrefixCuts (2^48) 7918190593 10 Manual.Count131072.C060381.packed 64 cuts60381 = true := by
 decide +kernel
def cuts60382 : List PrefixCut := [⟨49,156620384,156620472⟩,
⟨64,205177276,205177392⟩]
theorem checked60382 : checkPrefixCuts (2^48) 7918321665 10 Manual.Count131072.C060382.packed 64 cuts60382 = true := by
 decide +kernel
def pointBounds60382 : List (Nat × Nat × Nat) := [(7918422016,113995293346331,113995681798390)]
theorem point_links_checked60382 : (cuts60382.take 1).map (fun c => (7918321665-1+2*2^10*c.k,113995136725947+c.lower,113995525177918+c.upper)) = pointBounds60382 := by
 decide +kernel
def cuts60383 : List PrefixCut := [⟨64,205849255,205849365⟩]
theorem checked60383 : checkPrefixCuts (2^48) 7918452737 10 Manual.Count131072.C060383.packed 64 cuts60383 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000011
