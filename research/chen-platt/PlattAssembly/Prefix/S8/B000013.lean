import PlattAssemblyKernel
import PlattCertificates.Count131072.C070416
import PlattCertificates.Count131072.C070417
import PlattCertificates.Count131072.C070418
import PlattCertificates.Count131072.C070419
import PlattCertificates.Count131072.C070420
import PlattCertificates.Count131072.C070421
import PlattCertificates.Count131072.C070422
import PlattCertificates.Count131072.C070423
import PlattCertificates.Count131072.C070424
import PlattCertificates.Count131072.C070425
import PlattCertificates.Count131072.C070426
import PlattCertificates.Count131072.C070427
import PlattCertificates.Count131072.C070428
import PlattCertificates.Count131072.C070429
import PlattCertificates.Count131072.C070430
import PlattCertificates.Count131072.C070431
import PlattCertificates.Count131072.C070432
import PlattCertificates.Count131072.C070433
import PlattCertificates.Count131072.C070434
import PlattCertificates.Count131072.C070435
import PlattCertificates.Count131072.C070436
import PlattCertificates.Count131072.C070437
import PlattCertificates.Count131072.C070438
import PlattCertificates.Count131072.C070439
import PlattCertificates.Count131072.C070440
import PlattCertificates.Count131072.C070441
import PlattCertificates.Count131072.C070442
import PlattCertificates.Count131072.C070443
import PlattCertificates.Count131072.C070444
import PlattCertificates.Count131072.C070445
import PlattCertificates.Count131072.C070446
import PlattCertificates.Count131072.C070447
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70416 : List PrefixCut := [⟨64,175861555,175861654⟩]
theorem checked70416 : checkPrefixCuts (2^48) 9233498113 10 Manual.Count131072.C070416.packed 64 cuts70416 = true := by
 decide +kernel
def cuts70417 : List PrefixCut := [⟨64,175249366,175249472⟩]
theorem checked70417 : checkPrefixCuts (2^48) 9233629185 10 Manual.Count131072.C070417.packed 64 cuts70417 = true := by
 decide +kernel
def cuts70418 : List PrefixCut := [⟨9,23868350,23868364⟩,
⟨64,175551696,175551795⟩]
theorem checked70418 : checkPrefixCuts (2^48) 9233760257 10 Manual.Count131072.C070418.packed 64 cuts70418 = true := by
 decide +kernel
def pointBounds70418 : List (Nat × Nat × Nat) := [(9233778688,115886768254616,115887157802800)]
theorem point_links_checked70418 : (cuts70418.take 1).map (fun c => (9233760257-1+2*2^10*c.k,115886744386266+c.lower,115887133934436+c.upper)) = pointBounds70418 := by
 decide +kernel
def cuts70419 : List PrefixCut := [⟨64,175427291,175427400⟩]
theorem checked70419 : checkPrefixCuts (2^48) 9233891329 10 Manual.Count131072.C070419.packed 64 cuts70419 = true := by
 decide +kernel
def cuts70420 : List PrefixCut := [⟨22,61360864,61360899⟩,
⟨64,175973483,175973579⟩]
theorem checked70420 : checkPrefixCuts (2^48) 9234022401 10 Manual.Count131072.C070420.packed 64 cuts70420 = true := by
 decide +kernel
def pointBounds70420 : List (Nat × Nat × Nat) := [(9234067456,115887156726117,115887546274530)]
theorem point_links_checked70420 : (cuts70420.take 1).map (fun c => (9234022401-1+2*2^10*c.k,115887095365253+c.lower,115887484913631+c.upper)) = pointBounds70420 := by
 decide +kernel
def cuts70421 : List PrefixCut := [⟨64,173989672,173989775⟩]
theorem checked70421 : checkPrefixCuts (2^48) 9234153473 10 Manual.Count131072.C070421.packed 64 cuts70421 = true := by
 decide +kernel
def cuts70422 : List PrefixCut := [⟨35,94522783,94522841⟩,
⟨64,173225165,173225267⟩]
theorem checked70422 : checkPrefixCuts (2^48) 9234284545 10 Manual.Count131072.C070422.packed 64 cuts70422 = true := by
 decide +kernel
def pointBounds70422 : List (Nat × Nat × Nat) := [(9234356224,115887539851191,115887929399826)]
theorem point_links_checked70422 : (cuts70422.take 1).map (fun c => (9234284545-1+2*2^10*c.k,115887445328408+c.lower,115887834876985+c.upper)) = pointBounds70422 := by
 decide +kernel
def cuts70423 : List PrefixCut := [⟨64,173466543,173466650⟩]
theorem checked70423 : checkPrefixCuts (2^48) 9234415617 10 Manual.Count131072.C070423.packed 64 cuts70423 = true := by
 decide +kernel
def cuts70424 : List PrefixCut := [⟨48,130243079,130243156⟩,
⟨64,173067848,173067946⟩]
theorem checked70424 : checkPrefixCuts (2^48) 9234546689 10 Manual.Count131072.C070424.packed 64 cuts70424 = true := by
 decide +kernel
def pointBounds70424 : List (Nat × Nat × Nat) := [(9234644992,115887922263195,115888311812058)]
theorem point_links_checked70424 : (cuts70424.take 1).map (fun c => (9234546689-1+2*2^10*c.k,115887792020116+c.lower,115888181568902+c.upper)) = pointBounds70424 := by
 decide +kernel
def cuts70425 : List PrefixCut := [⟨64,173583550,173583659⟩]
theorem checked70425 : checkPrefixCuts (2^48) 9234677761 10 Manual.Count131072.C070425.packed 64 cuts70425 = true := by
 decide +kernel
def cuts70426 : List PrefixCut := [⟨61,167149955,167150047⟩,
⟨64,175287942,175288039⟩]
theorem checked70426 : checkPrefixCuts (2^48) 9234808833 10 Manual.Count131072.C070426.packed 64 cuts70426 = true := by
 decide +kernel
def pointBounds70426 : List (Nat × Nat × Nat) := [(9234933760,115888305821469,115888695370554)]
theorem point_links_checked70426 : (cuts70426.take 1).map (fun c => (9234808833-1+2*2^10*c.k,115888138671514+c.lower,115888528220507+c.upper)) = pointBounds70426 := by
 decide +kernel
def cuts70427 : List PrefixCut := [⟨64,174310113,174310221⟩]
theorem checked70427 : checkPrefixCuts (2^48) 9234939905 10 Manual.Count131072.C070427.packed 64 cuts70427 = true := by
 decide +kernel
def cuts70428 : List PrefixCut := [⟨64,175100095,175100192⟩]
theorem checked70428 : checkPrefixCuts (2^48) 9235070977 10 Manual.Count131072.C070428.packed 64 cuts70428 = true := by
 decide +kernel
def cuts70429 : List PrefixCut := [⟨10,26821031,26821045⟩,
⟨64,175310962,175311057⟩]
theorem checked70429 : checkPrefixCuts (2^48) 9235202049 10 Manual.Count131072.C070429.packed 64 cuts70429 = true := by
 decide +kernel
def pointBounds70429 : List (Nat × Nat × Nat) := [(9235222528,115888690190695,115889079740004)]
theorem point_links_checked70429 : (cuts70429.take 1).map (fun c => (9235202049-1+2*2^10*c.k,115888663369664+c.lower,115889052918959+c.upper)) = pointBounds70429 := by
 decide +kernel
def cuts70430 : List PrefixCut := [⟨64,169609097,169609194⟩]
theorem checked70430 : checkPrefixCuts (2^48) 9235333121 10 Manual.Count131072.C070430.packed 64 cuts70430 = true := by
 decide +kernel
def cuts70431 : List PrefixCut := [⟨23,62570376,62570414⟩,
⟨64,176281254,176281361⟩]
theorem checked70431 : checkPrefixCuts (2^48) 9235464193 10 Manual.Count131072.C070431.packed 64 cuts70431 = true := by
 decide +kernel
def pointBounds70431 : List (Nat × Nat × Nat) := [(9235511296,115889070860099,115889460409624)]
theorem point_links_checked70431 : (cuts70431.take 1).map (fun c => (9235464193-1+2*2^10*c.k,115889008289723+c.lower,115889397839210+c.upper)) = pointBounds70431 := by
 decide +kernel
def cuts70432 : List PrefixCut := [⟨64,174023453,174023560⟩]
theorem checked70432 : checkPrefixCuts (2^48) 9235595265 10 Manual.Count131072.C070432.packed 64 cuts70432 = true := by
 decide +kernel
def cuts70433 : List PrefixCut := [⟨36,96763277,96763340⟩,
⟨64,173990500,173990611⟩]
theorem checked70433 : checkPrefixCuts (2^48) 9235726337 10 Manual.Count131072.C070433.packed 64 cuts70433 = true := by
 decide +kernel
def pointBounds70433 : List (Nat × Nat × Nat) := [(9235800064,115889455357707,115889844907471)]
theorem point_links_checked70433 : (cuts70433.take 1).map (fun c => (9235726337-1+2*2^10*c.k,115889358594430+c.lower,115889748144131+c.upper)) = pointBounds70433 := by
 decide +kernel
def cuts70434 : List PrefixCut := [⟨64,175664222,175664331⟩]
theorem checked70434 : checkPrefixCuts (2^48) 9235857409 10 Manual.Count131072.C070434.packed 64 cuts70434 = true := by
 decide +kernel
def cuts70435 : List PrefixCut := [⟨49,132721743,132721819⟩,
⟨64,172766549,172766651⟩]
theorem checked70435 : checkPrefixCuts (2^48) 9235988481 10 Manual.Count131072.C070435.packed 64 cuts70435 = true := by
 decide +kernel
def pointBounds70435 : List (Nat × Nat × Nat) := [(9236088832,115889840970895,115890230520892)]
theorem point_links_checked70435 : (cuts70435.take 1).map (fun c => (9235988481-1+2*2^10*c.k,115889708249152+c.lower,115890097799073+c.upper)) = pointBounds70435 := by
 decide +kernel
def cuts70436 : List PrefixCut := [⟨64,175171633,175171744⟩]
theorem checked70436 : checkPrefixCuts (2^48) 9236119553 10 Manual.Count131072.C070436.packed 64 cuts70436 = true := by
 decide +kernel
def cuts70437 : List PrefixCut := [⟨62,166270540,166270636⟩,
⟨64,171877865,171877964⟩]
theorem checked70437 : checkPrefixCuts (2^48) 9236250625 10 Manual.Count131072.C070437.packed 64 cuts70437 = true := by
 decide +kernel
def pointBounds70437 : List (Nat × Nat × Nat) := [(9236377600,115890222457874,115890612008104)]
theorem point_links_checked70437 : (cuts70437.take 1).map (fun c => (9236250625-1+2*2^10*c.k,115890056187334+c.lower,115890445737468+c.upper)) = pointBounds70437 := by
 decide +kernel
def cuts70438 : List PrefixCut := [⟨64,174861928,174862031⟩]
theorem checked70438 : checkPrefixCuts (2^48) 9236381697 10 Manual.Count131072.C070438.packed 64 cuts70438 = true := by
 decide +kernel
def cuts70439 : List PrefixCut := [⟨64,173366225,173366326⟩]
theorem checked70439 : checkPrefixCuts (2^48) 9236512769 10 Manual.Count131072.C070439.packed 64 cuts70439 = true := by
 decide +kernel
def cuts70440 : List PrefixCut := [⟨11,30260367,30260386⟩,
⟨64,172906653,172906756⟩]
theorem checked70440 : checkPrefixCuts (2^48) 9236643841 10 Manual.Count131072.C070440.packed 64 cuts70440 = true := by
 decide +kernel
def pointBounds70440 : List (Nat × Nat × Nat) := [(9236666368,115890606553719,115890996104175)]
theorem point_links_checked70440 : (cuts70440.take 1).map (fun c => (9236643841-1+2*2^10*c.k,115890576293352+c.lower,115890965843789+c.upper)) = pointBounds70440 := by
 decide +kernel
def cuts70441 : List PrefixCut := [⟨64,174275505,174275599⟩]
theorem checked70441 : checkPrefixCuts (2^48) 9236774913 10 Manual.Count131072.C070441.packed 64 cuts70441 = true := by
 decide +kernel
def cuts70442 : List PrefixCut := [⟨24,66857271,66857307⟩,
⟨64,175888080,175888184⟩]
theorem checked70442 : checkPrefixCuts (2^48) 9236905985 10 Manual.Count131072.C070442.packed 64 cuts70442 = true := by
 decide +kernel
def pointBounds70442 : List (Nat × Nat × Nat) := [(9236955136,115890990332781,115891379883451)]
theorem point_links_checked70442 : (cuts70442.take 1).map (fun c => (9236905985-1+2*2^10*c.k,115890923475510+c.lower,115891313026144+c.upper)) = pointBounds70442 := by
 decide +kernel
def cuts70443 : List PrefixCut := [⟨64,174392429,174392529⟩]
theorem checked70443 : checkPrefixCuts (2^48) 9237037057 10 Manual.Count131072.C070443.packed 64 cuts70443 = true := by
 decide +kernel
def cuts70444 : List PrefixCut := [⟨37,100953289,100953349⟩,
⟨64,175029869,175029968⟩]
theorem checked70444 : checkPrefixCuts (2^48) 9237168129 10 Manual.Count131072.C070444.packed 64 cuts70444 = true := by
 decide +kernel
def pointBounds70444 : List (Nat × Nat × Nat) := [(9237243904,115891374709308,115891764260206)]
theorem point_links_checked70444 : (cuts70444.take 1).map (fun c => (9237168129-1+2*2^10*c.k,115891273756019+c.lower,115891663306857+c.upper)) = pointBounds70444 := by
 decide +kernel
def cuts70445 : List PrefixCut := [⟨64,172193560,172193655⟩]
theorem checked70445 : checkPrefixCuts (2^48) 9237299201 10 Manual.Count131072.C070445.packed 64 cuts70445 = true := by
 decide +kernel
def cuts70446 : List PrefixCut := [⟨50,139221796,139221877⟩,
⟨64,177249281,177249384⟩]
theorem checked70446 : checkPrefixCuts (2^48) 9237430273 10 Manual.Count131072.C070446.packed 64 cuts70446 = true := by
 decide +kernel
def pointBounds70446 : List (Nat × Nat × Nat) := [(9237532672,115891760201244,115892149752357)]
theorem point_links_checked70446 : (cuts70446.take 1).map (fun c => (9237430273-1+2*2^10*c.k,115891620979448+c.lower,115892010530480+c.upper)) = pointBounds70446 := by
 decide +kernel
def cuts70447 : List PrefixCut := [⟨64,173895011,173895116⟩]
theorem checked70447 : checkPrefixCuts (2^48) 9237561345 10 Manual.Count131072.C070447.packed 64 cuts70447 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000013
