import PlattAssemblyKernel
import PlattCertificates.Count131072.C072560
import PlattCertificates.Count131072.C072561
import PlattCertificates.Count131072.C072562
import PlattCertificates.Count131072.C072563
import PlattCertificates.Count131072.C072564
import PlattCertificates.Count131072.C072565
import PlattCertificates.Count131072.C072566
import PlattCertificates.Count131072.C072567
import PlattCertificates.Count131072.C072568
import PlattCertificates.Count131072.C072569
import PlattCertificates.Count131072.C072570
import PlattCertificates.Count131072.C072571
import PlattCertificates.Count131072.C072572
import PlattCertificates.Count131072.C072573
import PlattCertificates.Count131072.C072574
import PlattCertificates.Count131072.C072575
import PlattCertificates.Count131072.C072576
import PlattCertificates.Count131072.C072577
import PlattCertificates.Count131072.C072578
import PlattCertificates.Count131072.C072579
import PlattCertificates.Count131072.C072580
import PlattCertificates.Count131072.C072581
import PlattCertificates.Count131072.C072582
import PlattCertificates.Count131072.C072583
import PlattCertificates.Count131072.C072584
import PlattCertificates.Count131072.C072585
import PlattCertificates.Count131072.C072586
import PlattCertificates.Count131072.C072587
import PlattCertificates.Count131072.C072588
import PlattCertificates.Count131072.C072589
import PlattCertificates.Count131072.C072590
import PlattCertificates.Count131072.C072591
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72560 : List PrefixCut := [⟨64,167324426,167324527⟩]
theorem checked72560 : checkPrefixCuts (2^48) 9514516481 10 Manual.Count131072.C072560.packed 64 cuts72560 = true := by
 decide +kernel
def cuts72561 : List PrefixCut := [⟨64,169067522,169067616⟩]
theorem checked72561 : checkPrefixCuts (2^48) 9514647553 10 Manual.Count131072.C072561.packed 64 cuts72561 = true := by
 decide +kernel
def cuts72562 : List PrefixCut := [⟨10,26654179,26654193⟩,
⟨64,166284428,166284524⟩]
theorem checked72562 : checkPrefixCuts (2^48) 9514778625 10 Manual.Count131072.C072562.packed 64 cuts72562 = true := by
 decide +kernel
def pointBounds72562 : List (Nat × Nat × Nat) := [(9514799104,116254298179610,116254687945400)]
theorem point_links_checked72562 : (cuts72562.take 1).map (fun c => (9514778625-1+2*2^10*c.k,116254271525431+c.lower,116254661291207+c.upper)) = pointBounds72562 := by
 decide +kernel
def cuts72563 : List PrefixCut := [⟨64,169329109,169329203⟩]
theorem checked72563 : checkPrefixCuts (2^48) 9514909697 10 Manual.Count131072.C072563.packed 64 cuts72563 = true := by
 decide +kernel
def cuts72564 : List PrefixCut := [⟨28,74517089,74517134⟩,
⟨64,170125496,170125593⟩]
theorem checked72564 : checkPrefixCuts (2^48) 9515040769 10 Manual.Count131072.C072564.packed 64 cuts72564 = true := by
 decide +kernel
def pointBounds72564 : List (Nat × Nat × Nat) := [(9515098112,116254681656057,116255071422068)]
theorem point_links_checked72564 : (cuts72564.take 1).map (fun c => (9515040769-1+2*2^10*c.k,116254607138968+c.lower,116254996904934+c.upper)) = pointBounds72564 := by
 decide +kernel
def cuts72565 : List PrefixCut := [⟨64,169028627,169028721⟩]
theorem checked72565 : checkPrefixCuts (2^48) 9515171841 10 Manual.Count131072.C072565.packed 64 cuts72565 = true := by
 decide +kernel
def cuts72566 : List PrefixCut := [⟨46,120957284,120957357⟩,
⟨64,169026305,169026407⟩]
theorem checked72566 : checkPrefixCuts (2^48) 9515302913 10 Manual.Count131072.C072566.packed 64 cuts72566 = true := by
 decide +kernel
def pointBounds72566 : List (Nat × Nat × Nat) := [(9515397120,116255067250375,116255457016605)]
theorem point_links_checked72566 : (cuts72566.take 1).map (fun c => (9515302913-1+2*2^10*c.k,116254946293091+c.lower,116255336059248+c.upper)) = pointBounds72566 := by
 decide +kernel
def cuts72567 : List PrefixCut := [⟨64,167160391,167160488⟩]
theorem checked72567 : checkPrefixCuts (2^48) 9515433985 10 Manual.Count131072.C072567.packed 64 cuts72567 = true := by
 decide +kernel
def cuts72568 : List PrefixCut := [⟨64,168696252,168696350⟩]
theorem checked72568 : checkPrefixCuts (2^48) 9515565057 10 Manual.Count131072.C072568.packed 64 cuts72568 = true := by
 decide +kernel
def pointBounds72568 : List (Nat × Nat × Nat) := [(9515696128,116255451176039,116255840942493)]
theorem point_links_checked72568 : (cuts72568.take 1).map (fun c => (9515565057-1+2*2^10*c.k,116255282479787+c.lower,116255672246143+c.upper)) = pointBounds72568 := by
 decide +kernel
def cuts72569 : List PrefixCut := [⟨64,168989740,168989841⟩]
theorem checked72569 : checkPrefixCuts (2^48) 9515696129 10 Manual.Count131072.C072569.packed 64 cuts72569 = true := by
 decide +kernel
def cuts72570 : List PrefixCut := [⟨64,168543712,168543807⟩]
theorem checked72570 : checkPrefixCuts (2^48) 9515827201 10 Manual.Count131072.C072570.packed 64 cuts72570 = true := by
 decide +kernel
def cuts72571 : List PrefixCut := [⟨18,46439330,46439357⟩,
⟨64,169458340,169458438⟩]
theorem checked72571 : checkPrefixCuts (2^48) 9515958273 10 Manual.Count131072.C072571.packed 64 cuts72571 = true := by
 decide +kernel
def pointBounds72571 : List (Nat × Nat × Nat) := [(9515995136,116255835148821,116256224915498)]
theorem point_links_checked72571 : (cuts72571.take 1).map (fun c => (9515958273-1+2*2^10*c.k,116255788709491+c.lower,116256178476141+c.upper)) = pointBounds72571 := by
 decide +kernel
def cuts72572 : List PrefixCut := [⟨64,170106737,170106834⟩]
theorem checked72572 : checkPrefixCuts (2^48) 9516089345 10 Manual.Count131072.C072572.packed 64 cuts72572 = true := by
 decide +kernel
def cuts72573 : List PrefixCut := [⟨36,94621044,94621098⟩,
⟨64,167324050,167324153⟩]
theorem checked72573 : checkPrefixCuts (2^48) 9516220417 10 Manual.Count131072.C072573.packed 64 cuts72573 = true := by
 decide +kernel
def pointBounds72573 : List (Nat × Nat × Nat) := [(9516294144,116256222895612,116256612662511)]
theorem point_links_checked72573 : (cuts72573.take 1).map (fun c => (9516220417-1+2*2^10*c.k,116256128274568+c.lower,116256518041413+c.upper)) = pointBounds72573 := by
 decide +kernel
def cuts72574 : List PrefixCut := [⟨64,167499202,167499302⟩]
theorem checked72574 : checkPrefixCuts (2^48) 9516351489 10 Manual.Count131072.C072574.packed 64 cuts72574 = true := by
 decide +kernel
def cuts72575 : List PrefixCut := [⟨54,140936534,140936620⟩,
⟨64,168354640,168354740⟩]
theorem checked72575 : checkPrefixCuts (2^48) 9516482561 10 Manual.Count131072.C072575.packed 64 cuts72575 = true := by
 decide +kernel
def pointBounds72575 : List (Nat × Nat × Nat) := [(9516593152,116256604034354,116256993801488)]
theorem point_links_checked72575 : (cuts72575.take 1).map (fun c => (9516482561-1+2*2^10*c.k,116256463097820+c.lower,116256852864868+c.upper)) = pointBounds72575 := by
 decide +kernel
def cuts72576 : List PrefixCut := [⟨64,169742444,169742549⟩]
theorem checked72576 : checkPrefixCuts (2^48) 9516613633 10 Manual.Count131072.C072576.packed 64 cuts72576 = true := by
 decide +kernel
def cuts72577 : List PrefixCut := [⟨64,170656984,170657083⟩]
theorem checked72577 : checkPrefixCuts (2^48) 9516744705 10 Manual.Count131072.C072577.packed 64 cuts72577 = true := by
 decide +kernel
def cuts72578 : List PrefixCut := [⟨8,20733036,20733050⟩,
⟨64,167371671,167371768⟩]
theorem checked72578 : checkPrefixCuts (2^48) 9516875777 10 Manual.Count131072.C072578.packed 64 cuts72578 = true := by
 decide +kernel
def pointBounds72578 : List (Nat × Nat × Nat) := [(9516892160,116256992584924,116257382352290)]
theorem point_links_checked72578 : (cuts72578.take 1).map (fun c => (9516875777-1+2*2^10*c.k,116256971851888+c.lower,116257361619240+c.upper)) = pointBounds72578 := by
 decide +kernel
def cuts72579 : List PrefixCut := [⟨64,167901738,167901833⟩]
theorem checked72579 : checkPrefixCuts (2^48) 9517006849 10 Manual.Count131072.C072579.packed 64 cuts72579 = true := by
 decide +kernel
def cuts72580 : List PrefixCut := [⟨26,70567143,70567184⟩,
⟨64,168727551,168727657⟩]
theorem checked72580 : checkPrefixCuts (2^48) 9517137921 10 Manual.Count131072.C072580.packed 64 cuts72580 = true := by
 decide +kernel
def pointBounds72580 : List (Nat × Nat × Nat) := [(9517191168,116257377692440,116257767460025)]
theorem point_links_checked72580 : (cuts72580.take 1).map (fun c => (9517137921-1+2*2^10*c.k,116257307125297+c.lower,116257696892841+c.upper)) = pointBounds72580 := by
 decide +kernel
def cuts72581 : List PrefixCut := [⟨64,168961808,168961913⟩]
theorem checked72581 : checkPrefixCuts (2^48) 9517268993 10 Manual.Count131072.C072581.packed 64 cuts72581 = true := by
 decide +kernel
def cuts72582 : List PrefixCut := [⟨44,114631255,114631321⟩,
⟨64,167244157,167244250⟩]
theorem checked72582 : checkPrefixCuts (2^48) 9517400065 10 Manual.Count131072.C072582.packed 64 cuts72582 = true := by
 decide +kernel
def pointBounds72582 : List (Nat × Nat × Nat) := [(9517490176,116257759445911,116258149213732)]
theorem point_links_checked72582 : (cuts72582.take 1).map (fun c => (9517400065-1+2*2^10*c.k,116257644814656+c.lower,116258034582411+c.upper)) = pointBounds72582 := by
 decide +kernel
def cuts72583 : List PrefixCut := [⟨64,166058897,166058995⟩]
theorem checked72583 : checkPrefixCuts (2^48) 9517531137 10 Manual.Count131072.C072583.packed 64 cuts72583 = true := by
 decide +kernel
def cuts72584 : List PrefixCut := [⟨62,163099271,163099364⟩,
⟨64,168363363,168363460⟩]
theorem checked72584 : checkPrefixCuts (2^48) 9517662209 10 Manual.Count131072.C072584.packed 64 cuts72584 = true := by
 decide +kernel
def pointBounds72584 : List (Nat × Nat × Nat) := [(9517789184,116258141216981,116258530985020)]
theorem point_links_checked72584 : (cuts72584.take 1).map (fun c => (9517662209-1+2*2^10*c.k,116257978117710+c.lower,116258367885656+c.upper)) = pointBounds72584 := by
 decide +kernel
def cuts72585 : List PrefixCut := [⟨64,168863790,168863886⟩]
theorem checked72585 : checkPrefixCuts (2^48) 9517793281 10 Manual.Count131072.C072585.packed 64 cuts72585 = true := by
 decide +kernel
def cuts72586 : List PrefixCut := [⟨64,166052026,166052125⟩]
theorem checked72586 : checkPrefixCuts (2^48) 9517924353 10 Manual.Count131072.C072586.packed 64 cuts72586 = true := by
 decide +kernel
def cuts72587 : List PrefixCut := [⟨16,42643805,42643830⟩,
⟨64,169361865,169361965⟩]
theorem checked72587 : checkPrefixCuts (2^48) 9518055425 10 Manual.Count131072.C072587.packed 64 cuts72587 = true := by
 decide +kernel
def pointBounds72587 : List (Nat × Nat × Nat) := [(9518088192,116258524040694,116258913808957)]
theorem point_links_checked72587 : (cuts72587.take 1).map (fun c => (9518055425-1+2*2^10*c.k,116258481396889+c.lower,116258871165127+c.upper)) = pointBounds72587 := by
 decide +kernel
def cuts72588 : List PrefixCut := [⟨64,169241242,169241342⟩]
theorem checked72588 : checkPrefixCuts (2^48) 9518186497 10 Manual.Count131072.C072588.packed 64 cuts72588 = true := by
 decide +kernel
def cuts72589 : List PrefixCut := [⟨34,90667164,90667221⟩,
⟨64,167878623,167878724⟩]
theorem checked72589 : checkPrefixCuts (2^48) 9518317569 10 Manual.Count131072.C072589.packed 64 cuts72589 = true := by
 decide +kernel
def pointBounds72589 : List (Nat × Nat × Nat) := [(9518387200,116258910667160,116259300435655)]
theorem point_links_checked72589 : (cuts72589.take 1).map (fun c => (9518317569-1+2*2^10*c.k,116258819999996+c.lower,116259209768434+c.upper)) = pointBounds72589 := by
 decide +kernel
def cuts72590 : List PrefixCut := [⟨64,171986707,171986814⟩]
theorem checked72590 : checkPrefixCuts (2^48) 9518448641 10 Manual.Count131072.C072590.packed 64 cuts72590 = true := by
 decide +kernel
def cuts72591 : List PrefixCut := [⟨52,139012976,139013057⟩,
⟨64,171481640,171481741⟩]
theorem checked72591 : checkPrefixCuts (2^48) 9518579713 10 Manual.Count131072.C072591.packed 64 cuts72591 = true := by
 decide +kernel
def pointBounds72591 : List (Nat × Nat × Nat) := [(9518686208,116259298878302,116259688647029)]
theorem point_links_checked72591 : (cuts72591.take 1).map (fun c => (9518579713-1+2*2^10*c.k,116259159865326+c.lower,116259549633972+c.upper)) = pointBounds72591 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000080
