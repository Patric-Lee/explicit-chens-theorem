import PlattAssemblyKernel
import PlattCertificates.Count131072.C069440
import PlattCertificates.Count131072.C069441
import PlattCertificates.Count131072.C069442
import PlattCertificates.Count131072.C069443
import PlattCertificates.Count131072.C069444
import PlattCertificates.Count131072.C069445
import PlattCertificates.Count131072.C069446
import PlattCertificates.Count131072.C069447
import PlattCertificates.Count131072.C069448
import PlattCertificates.Count131072.C069449
import PlattCertificates.Count131072.C069450
import PlattCertificates.Count131072.C069451
import PlattCertificates.Count131072.C069452
import PlattCertificates.Count131072.C069453
import PlattCertificates.Count131072.C069454
import PlattCertificates.Count131072.C069455
import PlattCertificates.Count131072.C069456
import PlattCertificates.Count131072.C069457
import PlattCertificates.Count131072.C069458
import PlattCertificates.Count131072.C069459
import PlattCertificates.Count131072.C069460
import PlattCertificates.Count131072.C069461
import PlattCertificates.Count131072.C069462
import PlattCertificates.Count131072.C069463
import PlattCertificates.Count131072.C069464
import PlattCertificates.Count131072.C069465
import PlattCertificates.Count131072.C069466
import PlattCertificates.Count131072.C069467
import PlattCertificates.Count131072.C069468
import PlattCertificates.Count131072.C069469
import PlattCertificates.Count131072.C069470
import PlattCertificates.Count131072.C069471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000295
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69440 : List PrefixCut := [⟨64,180465178,180465273⟩]
theorem checked69440 : checkPrefixCuts (2^48) 9105571841 10 Manual.Count131072.C069440.packed 64 cuts69440 = true := by
 decide +kernel
def cuts69441 : List PrefixCut := [⟨48,132549663,132549738⟩,
⟨64,176536791,176536892⟩]
theorem checked69441 : checkPrefixCuts (2^48) 9105702913 10 Manual.Count131072.C069441.packed 64 cuts69441 = true := by
 decide +kernel
def pointBounds69441 : List (Nat × Nat × Nat) := [(9105801216,115715540533543,115715929980995)]
theorem point_links_checked69441 : (cuts69441.take 1).map (fun c => (9105702913-1+2*2^10*c.k,115715407983880+c.lower,115715797431257+c.upper)) = pointBounds69441 := by
 decide +kernel
def cuts69442 : List PrefixCut := [⟨64,174030434,174030544⟩]
theorem checked69442 : checkPrefixCuts (2^48) 9105833985 10 Manual.Count131072.C069442.packed 64 cuts69442 = true := by
 decide +kernel
def cuts69443 : List PrefixCut := [⟨59,163580165,163580260⟩,
⟨64,177551764,177551869⟩]
theorem checked69443 : checkPrefixCuts (2^48) 9105965057 10 Manual.Count131072.C069443.packed 64 cuts69443 = true := by
 decide +kernel
def pointBounds69443 : List (Nat × Nat × Nat) := [(9106085888,115715922131270,115716311578953)]
theorem point_links_checked69443 : (cuts69443.take 1).map (fun c => (9105965057-1+2*2^10*c.k,115715758551105+c.lower,115716147998693+c.upper)) = pointBounds69443 := by
 decide +kernel
def cuts69444 : List PrefixCut := [⟨64,179156555,179156658⟩]
theorem checked69444 : checkPrefixCuts (2^48) 9106096129 10 Manual.Count131072.C069444.packed 64 cuts69444 = true := by
 decide +kernel
def cuts69445 : List PrefixCut := [⟨64,175444769,175444870⟩]
theorem checked69445 : checkPrefixCuts (2^48) 9106227201 10 Manual.Count131072.C069445.packed 64 cuts69445 = true := by
 decide +kernel
def cuts69446 : List PrefixCut := [⟨6,16443953,16443964⟩,
⟨64,175318607,175318705⟩]
theorem checked69446 : checkPrefixCuts (2^48) 9106358273 10 Manual.Count131072.C069446.packed 64 cuts69446 = true := by
 decide +kernel
def pointBounds69446 : List (Nat × Nat × Nat) := [(9106370560,115716307148146,115716696596054)]
theorem point_links_checked69446 : (cuts69446.take 1).map (fun c => (9106358273-1+2*2^10*c.k,115716290704193+c.lower,115716680152090+c.upper)) = pointBounds69446 := by
 decide +kernel
def cuts69447 : List PrefixCut := [⟨64,175099724,175099832⟩]
theorem checked69447 : checkPrefixCuts (2^48) 9106489345 10 Manual.Count131072.C069447.packed 64 cuts69447 = true := by
 decide +kernel
def cuts69448 : List PrefixCut := [⟨17,46734045,46734074⟩,
⟨64,176055370,176055472⟩]
theorem checked69448 : checkPrefixCuts (2^48) 9106620417 10 Manual.Count131072.C069448.packed 64 cuts69448 = true := by
 decide +kernel
def pointBounds69448 : List (Nat × Nat × Nat) := [(9106655232,115716687856569,115717077304701)]
theorem point_links_checked69448 : (cuts69448.take 1).map (fun c => (9106620417-1+2*2^10*c.k,115716641122524+c.lower,115717030570627+c.upper)) = pointBounds69448 := by
 decide +kernel
def cuts69449 : List PrefixCut := [⟨64,177289171,177289271⟩]
theorem checked69449 : checkPrefixCuts (2^48) 9106751489 10 Manual.Count131072.C069449.packed 64 cuts69449 = true := by
 decide +kernel
def cuts69450 : List PrefixCut := [⟨28,76682339,76682384⟩,
⟨64,175679425,175679521⟩]
theorem checked69450 : checkPrefixCuts (2^48) 9106882561 10 Manual.Count131072.C069450.packed 64 cuts69450 = true := by
 decide +kernel
def pointBounds69450 : List (Nat × Nat × Nat) := [(9106939904,115717071149404,115717460597754)]
theorem point_links_checked69450 : (cuts69450.take 1).map (fun c => (9106882561-1+2*2^10*c.k,115716994467065+c.lower,115717383915370+c.upper)) = pointBounds69450 := by
 decide +kernel
def cuts69451 : List PrefixCut := [⟨64,178242178,178242286⟩]
theorem checked69451 : checkPrefixCuts (2^48) 9107013633 10 Manual.Count131072.C069451.packed 64 cuts69451 = true := by
 decide +kernel
def cuts69452 : List PrefixCut := [⟨39,104959844,104959912⟩,
⟨64,173819936,173820043⟩]
theorem checked69452 : checkPrefixCuts (2^48) 9107144705 10 Manual.Count131072.C069452.packed 64 cuts69452 = true := by
 decide +kernel
def pointBounds69452 : List (Nat × Nat × Nat) := [(9107224576,115717453348512,115717842797089)]
theorem point_links_checked69452 : (cuts69452.take 1).map (fun c => (9107144705-1+2*2^10*c.k,115717348388668+c.lower,115717737837177+c.upper)) = pointBounds69452 := by
 decide +kernel
def cuts69453 : List PrefixCut := [⟨64,178020712,178020812⟩]
theorem checked69453 : checkPrefixCuts (2^48) 9107275777 10 Manual.Count131072.C069453.packed 64 cuts69453 = true := by
 decide +kernel
def cuts69454 : List PrefixCut := [⟨50,138675110,138675194⟩,
⟨64,177090963,177091071⟩]
theorem checked69454 : checkPrefixCuts (2^48) 9107406849 10 Manual.Count131072.C069454.packed 64 cuts69454 = true := by
 decide +kernel
def pointBounds69454 : List (Nat × Nat × Nat) := [(9107509248,115717838904426,115718228353226)]
theorem point_links_checked69454 : (cuts69454.take 1).map (fun c => (9107406849-1+2*2^10*c.k,115717700229316+c.lower,115718089678032+c.upper)) = pointBounds69454 := by
 decide +kernel
def cuts69455 : List PrefixCut := [⟨64,177521100,177521198⟩]
theorem checked69455 : checkPrefixCuts (2^48) 9107537921 10 Manual.Count131072.C069455.packed 64 cuts69455 = true := by
 decide +kernel
def cuts69456 : List PrefixCut := [⟨61,167938048,167938151⟩,
⟨64,176344162,176344268⟩]
theorem checked69456 : checkPrefixCuts (2^48) 9107668993 10 Manual.Count131072.C069456.packed 64 cuts69456 = true := by
 decide +kernel
def pointBounds69456 : List (Nat × Nat × Nat) := [(9107793920,115718222779427,115718612228452)]
theorem point_links_checked69456 : (cuts69456.take 1).map (fun c => (9107668993-1+2*2^10*c.k,115718054841379+c.lower,115718444290301+c.upper)) = pointBounds69456 := by
 decide +kernel
def cuts69457 : List PrefixCut := [⟨64,175167231,175167336⟩]
theorem checked69457 : checkPrefixCuts (2^48) 9107800065 10 Manual.Count131072.C069457.packed 64 cuts69457 = true := by
 decide +kernel
def cuts69458 : List PrefixCut := [⟨64,177729765,177729872⟩]
theorem checked69458 : checkPrefixCuts (2^48) 9107931137 10 Manual.Count131072.C069458.packed 64 cuts69458 = true := by
 decide +kernel
def cuts69459 : List PrefixCut := [⟨8,21478209,21478224⟩,
⟨64,174296886,174296990⟩]
theorem checked69459 : checkPrefixCuts (2^48) 9108062209 10 Manual.Count131072.C069459.packed 64 cuts69459 = true := by
 decide +kernel
def pointBounds69459 : List (Nat × Nat × Nat) := [(9108078592,115718605560746,115718995010001)]
theorem point_links_checked69459 : (cuts69459.take 1).map (fun c => (9108062209-1+2*2^10*c.k,115718584082537+c.lower,115718973531777+c.upper)) = pointBounds69459 := by
 decide +kernel
def cuts69460 : List PrefixCut := [⟨64,175932255,175932361⟩]
theorem checked69460 : checkPrefixCuts (2^48) 9108193281 10 Manual.Count131072.C069460.packed 64 cuts69460 = true := by
 decide +kernel
def cuts69461 : List PrefixCut := [⟨19,52689569,52689601⟩,
⟨64,176393279,176393381⟩]
theorem checked69461 : checkPrefixCuts (2^48) 9108324353 10 Manual.Count131072.C069461.packed 64 cuts69461 = true := by
 decide +kernel
def pointBounds69461 : List (Nat × Nat × Nat) := [(9108363264,115718987001247,115719376450729)]
theorem point_links_checked69461 : (cuts69461.take 1).map (fun c => (9108324353-1+2*2^10*c.k,115718934311678+c.lower,115719323761128+c.upper)) = pointBounds69461 := by
 decide +kernel
def cuts69462 : List PrefixCut := [⟨64,175741784,175741889⟩]
theorem checked69462 : checkPrefixCuts (2^48) 9108455425 10 Manual.Count131072.C069462.packed 64 cuts69462 = true := by
 decide +kernel
def cuts69463 : List PrefixCut := [⟨30,82971985,82972034⟩,
⟨64,177871481,177871588⟩]
theorem checked69463 : checkPrefixCuts (2^48) 9108586497 10 Manual.Count131072.C069463.packed 64 cuts69463 = true := by
 decide +kernel
def pointBounds69463 : List (Nat × Nat × Nat) := [(9108647936,115719369418726,115719758868432)]
theorem point_links_checked69463 : (cuts69463.take 1).map (fun c => (9108586497-1+2*2^10*c.k,115719286446741+c.lower,115719675896398+c.upper)) = pointBounds69463 := by
 decide +kernel
def cuts69464 : List PrefixCut := [⟨64,175118695,175118797⟩]
theorem checked69464 : checkPrefixCuts (2^48) 9108717569 10 Manual.Count131072.C069464.packed 64 cuts69464 = true := by
 decide +kernel
def cuts69465 : List PrefixCut := [⟨41,114056024,114056091⟩,
⟨64,176537634,176537736⟩]
theorem checked69465 : checkPrefixCuts (2^48) 9108848641 10 Manual.Count131072.C069465.packed 64 cuts69465 = true := by
 decide +kernel
def pointBounds69465 : List (Nat × Nat × Nat) := [(9108932608,115719753492941,115720142942874)]
theorem point_links_checked69465 : (cuts69465.take 1).map (fun c => (9108848641-1+2*2^10*c.k,115719639436917+c.lower,115720028886783+c.upper)) = pointBounds69465 := by
 decide +kernel
def cuts69466 : List PrefixCut := [⟨64,176071580,176071682⟩]
theorem checked69466 : checkPrefixCuts (2^48) 9108979713 10 Manual.Count131072.C069466.packed 64 cuts69466 = true := by
 decide +kernel
def cuts69467 : List PrefixCut := [⟨52,139885160,139885247⟩,
⟨64,173133526,173133633⟩]
theorem checked69467 : checkPrefixCuts (2^48) 9109110785 10 Manual.Count131072.C069467.packed 64 cuts69467 = true := by
 decide +kernel
def pointBounds69467 : List (Nat × Nat × Nat) := [(9109217280,115720131931291,115720521381448)]
theorem point_links_checked69467 : (cuts69467.take 1).map (fun c => (9109110785-1+2*2^10*c.k,115719992046131+c.lower,115720381496201+c.upper)) = pointBounds69467 := by
 decide +kernel
def cuts69468 : List PrefixCut := [⟨64,179156470,179156577⟩]
theorem checked69468 : checkPrefixCuts (2^48) 9109241857 10 Manual.Count131072.C069468.packed 64 cuts69468 = true := by
 decide +kernel
def cuts69469 : List PrefixCut := [⟨63,172325177,172325278⟩,
⟨64,174951595,174951698⟩]
theorem checked69469 : checkPrefixCuts (2^48) 9109372929 10 Manual.Count131072.C069469.packed 64 cuts69469 = true := by
 decide +kernel
def pointBounds69469 : List (Nat × Nat × Nat) := [(9109501952,115720516661304,115720906111689)]
theorem point_links_checked69469 : (cuts69469.take 1).map (fun c => (9109372929-1+2*2^10*c.k,115720344336127+c.lower,115720733786411+c.upper)) = pointBounds69469 := by
 decide +kernel
def cuts69470 : List PrefixCut := [⟨64,175814251,175814355⟩]
theorem checked69470 : checkPrefixCuts (2^48) 9109504001 10 Manual.Count131072.C069470.packed 64 cuts69470 = true := by
 decide +kernel
def cuts69471 : List PrefixCut := [⟨64,175070161,175070269⟩]
theorem checked69471 : checkPrefixCuts (2^48) 9109635073 10 Manual.Count131072.C069471.packed 64 cuts69471 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000295
