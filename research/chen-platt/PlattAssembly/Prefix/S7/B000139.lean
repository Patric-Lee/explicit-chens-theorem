import PlattAssemblyKernel
import PlattCertificates.Count131072.C064448
import PlattCertificates.Count131072.C064449
import PlattCertificates.Count131072.C064450
import PlattCertificates.Count131072.C064451
import PlattCertificates.Count131072.C064452
import PlattCertificates.Count131072.C064453
import PlattCertificates.Count131072.C064454
import PlattCertificates.Count131072.C064455
import PlattCertificates.Count131072.C064456
import PlattCertificates.Count131072.C064457
import PlattCertificates.Count131072.C064458
import PlattCertificates.Count131072.C064459
import PlattCertificates.Count131072.C064460
import PlattCertificates.Count131072.C064461
import PlattCertificates.Count131072.C064462
import PlattCertificates.Count131072.C064463
import PlattCertificates.Count131072.C064464
import PlattCertificates.Count131072.C064465
import PlattCertificates.Count131072.C064466
import PlattCertificates.Count131072.C064467
import PlattCertificates.Count131072.C064468
import PlattCertificates.Count131072.C064469
import PlattCertificates.Count131072.C064470
import PlattCertificates.Count131072.C064471
import PlattCertificates.Count131072.C064472
import PlattCertificates.Count131072.C064473
import PlattCertificates.Count131072.C064474
import PlattCertificates.Count131072.C064475
import PlattCertificates.Count131072.C064476
import PlattCertificates.Count131072.C064477
import PlattCertificates.Count131072.C064478
import PlattCertificates.Count131072.C064479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000139
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64448 : List PrefixCut := [⟨29,85895016,85895064⟩,
⟨64,188342107,188342210⟩]
theorem checked64448 : checkPrefixCuts (2^48) 8451260417 10 Manual.Count131072.C064448.packed 64 cuts64448 = true := by
 decide +kernel
def pointBounds64448 : List (Nat × Nat × Nat) := [(8451319808,114798537424668,114798926338105)]
theorem point_links_checked64448 : (cuts64448.take 1).map (fun c => (8451260417-1+2*2^10*c.k,114798451529652+c.lower,114798840443041+c.upper)) = pointBounds64448 := by
 decide +kernel
def cuts64449 : List PrefixCut := [⟨64,192102635,192102742⟩]
theorem checked64449 : checkPrefixCuts (2^48) 8451391489 10 Manual.Count131072.C064449.packed 64 cuts64449 = true := by
 decide +kernel
def cuts64450 : List PrefixCut := [⟨30,89122887,89122937⟩,
⟨64,189968178,189968285⟩]
theorem checked64450 : checkPrefixCuts (2^48) 8451522561 10 Manual.Count131072.C064450.packed 64 cuts64450 = true := by
 decide +kernel
def pointBounds64450 : List (Nat × Nat × Nat) := [(8451584000,114798921097281,114799310010930)]
theorem point_links_checked64450 : (cuts64450.take 1).map (fun c => (8451522561-1+2*2^10*c.k,114798831974394+c.lower,114799220887993+c.upper)) = pointBounds64450 := by
 decide +kernel
def cuts64451 : List PrefixCut := [⟨64,190331566,190331680⟩]
theorem checked64451 : checkPrefixCuts (2^48) 8451653633 10 Manual.Count131072.C064451.packed 64 cuts64451 = true := by
 decide +kernel
def cuts64452 : List PrefixCut := [⟨31,92150728,92150784⟩,
⟨64,190295316,190295426⟩]
theorem checked64452 : checkPrefixCuts (2^48) 8451784705 10 Manual.Count131072.C064452.packed 64 cuts64452 = true := by
 decide +kernel
def pointBounds64452 : List (Nat × Nat × Nat) := [(8451848192,114799304424866,114799693338742)]
theorem point_links_checked64452 : (cuts64452.take 1).map (fun c => (8451784705-1+2*2^10*c.k,114799212274138+c.lower,114799601187958+c.upper)) = pointBounds64452 := by
 decide +kernel
def cuts64453 : List PrefixCut := [⟨64,189726225,189726337⟩]
theorem checked64453 : checkPrefixCuts (2^48) 8451915777 10 Manual.Count131072.C064453.packed 64 cuts64453 = true := by
 decide +kernel
def cuts64454 : List PrefixCut := [⟨32,96144150,96144205⟩,
⟨64,191088683,191088794⟩]
theorem checked64454 : checkPrefixCuts (2^48) 8452046849 10 Manual.Count131072.C064454.packed 64 cuts64454 = true := by
 decide +kernel
def pointBounds64454 : List (Nat × Nat × Nat) := [(8452112384,114799688439829,114800077353926)]
theorem point_links_checked64454 : (cuts64454.take 1).map (fun c => (8452046849-1+2*2^10*c.k,114799592295679+c.lower,114799981209721+c.upper)) = pointBounds64454 := by
 decide +kernel
def cuts64455 : List PrefixCut := [⟨64,195381655,195381762⟩]
theorem checked64455 : checkPrefixCuts (2^48) 8452177921 10 Manual.Count131072.C064455.packed 64 cuts64455 = true := by
 decide +kernel
def cuts64456 : List PrefixCut := [⟨33,96607380,96607435⟩,
⟨64,190216907,190217013⟩]
theorem checked64456 : checkPrefixCuts (2^48) 8452308993 10 Manual.Count131072.C064456.packed 64 cuts64456 = true := by
 decide +kernel
def pointBounds64456 : List (Nat × Nat × Nat) := [(8452376576,114800075373397,114800464287712)]
theorem point_links_checked64456 : (cuts64456.take 1).map (fun c => (8452308993-1+2*2^10*c.k,114799978766017+c.lower,114800367680277+c.upper)) = pointBounds64456 := by
 decide +kernel
def cuts64457 : List PrefixCut := [⟨64,191512694,191512812⟩]
theorem checked64457 : checkPrefixCuts (2^48) 8452440065 10 Manual.Count131072.C064457.packed 64 cuts64457 = true := by
 decide +kernel
def cuts64458 : List PrefixCut := [⟨34,100866821,100866875⟩,
⟨64,189178714,189178822⟩]
theorem checked64458 : checkPrefixCuts (2^48) 8452571137 10 Manual.Count131072.C064458.packed 64 cuts64458 = true := by
 decide +kernel
def pointBounds64458 : List (Nat × Nat × Nat) := [(8452640768,114800461362439,114800850276977)]
theorem point_links_checked64458 : (cuts64458.take 1).map (fun c => (8452571137-1+2*2^10*c.k,114800360495618+c.lower,114800749410102+c.upper)) = pointBounds64458 := by
 decide +kernel
def cuts64459 : List PrefixCut := [⟨64,189741862,189741972⟩]
theorem checked64459 : checkPrefixCuts (2^48) 8452702209 10 Manual.Count131072.C064459.packed 64 cuts64459 = true := by
 decide +kernel
def cuts64460 : List PrefixCut := [⟨35,105159292,105159355⟩,
⟨64,191137498,191137612⟩]
theorem checked64460 : checkPrefixCuts (2^48) 8452833281 10 Manual.Count131072.C064460.packed 64 cuts64460 = true := by
 decide +kernel
def pointBounds64460 : List (Nat × Nat × Nat) := [(8452904960,114800844575486,114801233490251)]
theorem point_links_checked64460 : (cuts64460.take 1).map (fun c => (8452833281-1+2*2^10*c.k,114800739416194+c.lower,114801128330896+c.upper)) = pointBounds64460 := by
 decide +kernel
def cuts64461 : List PrefixCut := [⟨64,192233383,192233495⟩]
theorem checked64461 : checkPrefixCuts (2^48) 8452964353 10 Manual.Count131072.C064461.packed 64 cuts64461 = true := by
 decide +kernel
def cuts64462 : List PrefixCut := [⟨36,106887529,106887590⟩,
⟨64,189799648,189799753⟩]
theorem checked64462 : checkPrefixCuts (2^48) 8453095425 10 Manual.Count131072.C064462.packed 64 cuts64462 = true := by
 decide +kernel
def pointBounds64462 : List (Nat × Nat × Nat) := [(8453169152,114801229674604,114801618589593)]
theorem point_links_checked64462 : (cuts64462.take 1).map (fun c => (8453095425-1+2*2^10*c.k,114801122787075+c.lower,114801511702003+c.upper)) = pointBounds64462 := by
 decide +kernel
def cuts64463 : List PrefixCut := [⟨64,192560392,192560501⟩]
theorem checked64463 : checkPrefixCuts (2^48) 8453226497 10 Manual.Count131072.C064463.packed 64 cuts64463 = true := by
 decide +kernel
def cuts64464 : List PrefixCut := [⟨37,110813273,110813335⟩,
⟨64,189926949,189927056⟩]
theorem checked64464 : checkPrefixCuts (2^48) 8453357569 10 Manual.Count131072.C064464.packed 64 cuts64464 = true := by
 decide +kernel
def pointBounds64464 : List (Nat × Nat × Nat) := [(8453433344,114801615960388,114802004875592)]
theorem point_links_checked64464 : (cuts64464.take 1).map (fun c => (8453357569-1+2*2^10*c.k,114801505147115+c.lower,114801894062257+c.upper)) = pointBounds64464 := by
 decide +kernel
def cuts64465 : List PrefixCut := [⟨64,191522235,191522344⟩]
theorem checked64465 : checkPrefixCuts (2^48) 8453488641 10 Manual.Count131072.C064465.packed 64 cuts64465 = true := by
 decide +kernel
def cuts64466 : List PrefixCut := [⟨38,113007380,113007446⟩,
⟨64,190020945,190021054⟩]
theorem checked64466 : checkPrefixCuts (2^48) 8453619713 10 Manual.Count131072.C064466.packed 64 cuts64466 = true := by
 decide +kernel
def pointBounds64466 : List (Nat × Nat × Nat) := [(8453697536,114801999603679,114802388519103)]
theorem point_links_checked64466 : (cuts64466.take 1).map (fun c => (8453619713-1+2*2^10*c.k,114801886596299+c.lower,114802275511657+c.upper)) = pointBounds64466 := by
 decide +kernel
def cuts64467 : List PrefixCut := [⟨64,191416411,191416518⟩]
theorem checked64467 : checkPrefixCuts (2^48) 8453750785 10 Manual.Count131072.C064467.packed 64 cuts64467 = true := by
 decide +kernel
def cuts64468 : List PrefixCut := [⟨39,116866100,116866167⟩,
⟨64,192612059,192612169⟩]
theorem checked64468 : checkPrefixCuts (2^48) 8453881857 10 Manual.Count131072.C064468.packed 64 cuts64468 = true := by
 decide +kernel
def pointBounds64468 : List (Nat × Nat × Nat) := [(8453961728,114802384899755,114802773815396)]
theorem point_links_checked64468 : (cuts64468.take 1).map (fun c => (8453881857-1+2*2^10*c.k,114802268033655+c.lower,114802656949229+c.upper)) = pointBounds64468 := by
 decide +kernel
def cuts64469 : List PrefixCut := [⟨64,191044235,191044339⟩]
theorem checked64469 : checkPrefixCuts (2^48) 8454012929 10 Manual.Count131072.C064469.packed 64 cuts64469 = true := by
 decide +kernel
def cuts64470 : List PrefixCut := [⟨40,119059873,119059938⟩,
⟨64,191540675,191540781⟩]
theorem checked64470 : checkPrefixCuts (2^48) 8454144001 10 Manual.Count131072.C064470.packed 64 cuts64470 = true := by
 decide +kernel
def pointBounds64470 : List (Nat × Nat × Nat) := [(8454225920,114802770749822,114803159665675)]
theorem point_links_checked64470 : (cuts64470.take 1).map (fun c => (8454144001-1+2*2^10*c.k,114802651689949+c.lower,114803040605737+c.upper)) = pointBounds64470 := by
 decide +kernel
def cuts64471 : List PrefixCut := [⟨64,190738671,190738783⟩]
theorem checked64471 : checkPrefixCuts (2^48) 8454275073 10 Manual.Count131072.C064471.packed 64 cuts64471 = true := by
 decide +kernel
def cuts64472 : List PrefixCut := [⟨42,122784985,122785056⟩,
⟨64,188704829,188704940⟩]
theorem checked64472 : checkPrefixCuts (2^48) 8454406145 10 Manual.Count131072.C064472.packed 64 cuts64472 = true := by
 decide +kernel
def pointBounds64472 : List (Nat × Nat × Nat) := [(8454492160,114803156754280,114803545670357)]
theorem point_links_checked64472 : (cuts64472.take 1).map (fun c => (8454406145-1+2*2^10*c.k,114803033969295+c.lower,114803422885301+c.upper)) = pointBounds64472 := by
 decide +kernel
def cuts64473 : List PrefixCut := [⟨64,191764824,191764932⟩]
theorem checked64473 : checkPrefixCuts (2^48) 8454537217 10 Manual.Count131072.C064473.packed 64 cuts64473 = true := by
 decide +kernel
def cuts64474 : List PrefixCut := [⟨44,130871118,130871196⟩,
⟨64,190330291,190330405⟩]
theorem checked64474 : checkPrefixCuts (2^48) 8454668289 10 Manual.Count131072.C064474.packed 64 cuts64474 = true := by
 decide +kernel
def pointBounds64474 : List (Nat × Nat × Nat) := [(8454758400,114803545310066,114803934226369)]
theorem point_links_checked64474 : (cuts64474.take 1).map (fun c => (8454668289-1+2*2^10*c.k,114803414438948+c.lower,114803803355173+c.upper)) = pointBounds64474 := by
 decide +kernel
def cuts64475 : List PrefixCut := [⟨64,192358101,192358215⟩]
theorem checked64475 : checkPrefixCuts (2^48) 8454799361 10 Manual.Count131072.C064475.packed 64 cuts64475 = true := by
 decide +kernel
def cuts64476 : List PrefixCut := [⟨46,137125744,137125822⟩,
⟨64,189924908,189925013⟩]
theorem checked64476 : checkPrefixCuts (2^48) 8454930433 10 Manual.Count131072.C064476.packed 64 cuts64476 = true := by
 decide +kernel
def pointBounds64476 : List (Nat × Nat × Nat) := [(8455024640,114803934253084,114804323169615)]
theorem point_links_checked64476 : (cuts64476.take 1).map (fun c => (8454930433-1+2*2^10*c.k,114803797127340+c.lower,114804186043793+c.upper)) = pointBounds64476 := by
 decide +kernel
def cuts64477 : List PrefixCut := [⟨64,191819509,191819618⟩]
theorem checked64477 : checkPrefixCuts (2^48) 8455061505 10 Manual.Count131072.C064477.packed 64 cuts64477 = true := by
 decide +kernel
def cuts64478 : List PrefixCut := [⟨48,143280103,143280185⟩,
⟨64,190518231,190518339⟩]
theorem checked64478 : checkPrefixCuts (2^48) 8455192577 10 Manual.Count131072.C064478.packed 64 cuts64478 = true := by
 decide +kernel
def pointBounds64478 : List (Nat × Nat × Nat) := [(8455290880,114804322151860,114804711068609)]
theorem point_links_checked64478 : (cuts64478.take 1).map (fun c => (8455192577-1+2*2^10*c.k,114804178871757+c.lower,114804567788424+c.upper)) = pointBounds64478 := by
 decide +kernel
def cuts64479 : List PrefixCut := [⟨64,189716326,189716435⟩]
theorem checked64479 : checkPrefixCuts (2^48) 8455323649 10 Manual.Count131072.C064479.packed 64 cuts64479 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000139
