import PlattAssemblyKernel
import PlattCertificates.Count131072.C074544
import PlattCertificates.Count131072.C074545
import PlattCertificates.Count131072.C074546
import PlattCertificates.Count131072.C074547
import PlattCertificates.Count131072.C074548
import PlattCertificates.Count131072.C074549
import PlattCertificates.Count131072.C074550
import PlattCertificates.Count131072.C074551
import PlattCertificates.Count131072.C074552
import PlattCertificates.Count131072.C074553
import PlattCertificates.Count131072.C074554
import PlattCertificates.Count131072.C074555
import PlattCertificates.Count131072.C074556
import PlattCertificates.Count131072.C074557
import PlattCertificates.Count131072.C074558
import PlattCertificates.Count131072.C074559
import PlattCertificates.Count131072.C074560
import PlattCertificates.Count131072.C074561
import PlattCertificates.Count131072.C074562
import PlattCertificates.Count131072.C074563
import PlattCertificates.Count131072.C074564
import PlattCertificates.Count131072.C074565
import PlattCertificates.Count131072.C074566
import PlattCertificates.Count131072.C074567
import PlattCertificates.Count131072.C074568
import PlattCertificates.Count131072.C074569
import PlattCertificates.Count131072.C074570
import PlattCertificates.Count131072.C074571
import PlattCertificates.Count131072.C074572
import PlattCertificates.Count131072.C074573
import PlattCertificates.Count131072.C074574
import PlattCertificates.Count131072.C074575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000142
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74544 : List PrefixCut := [⟨64,162066583,162066683⟩]
theorem checked74544 : checkPrefixCuts (2^48) 9774563329 10 Manual.Count131072.C074544.packed 64 cuts74544 = true := by
 decide +kernel
def cuts74545 : List PrefixCut := [⟨64,165059207,165059298⟩]
theorem checked74545 : checkPrefixCuts (2^48) 9774694401 10 Manual.Count131072.C074545.packed 64 cuts74545 = true := by
 decide +kernel
def cuts74546 : List PrefixCut := [⟨17,43510528,43510555⟩,
⟨64,163070088,163070186⟩]
theorem checked74546 : checkPrefixCuts (2^48) 9774825473 10 Manual.Count131072.C074546.packed 64 cuts74546 = true := by
 decide +kernel
def pointBounds74546 : List (Nat × Nat × Nat) := [(9774860288,116584513104436,116584903067284)]
theorem point_links_checked74546 : (cuts74546.take 1).map (fun c => (9774825473-1+2*2^10*c.k,116584469593908+c.lower,116584859556729+c.upper)) = pointBounds74546 := by
 decide +kernel
def cuts74547 : List PrefixCut := [⟨64,163557417,163557517⟩]
theorem checked74547 : checkPrefixCuts (2^48) 9774956545 10 Manual.Count131072.C074547.packed 64 cuts74547 = true := by
 decide +kernel
def cuts74548 : List PrefixCut := [⟨39,99313986,99314043⟩,
⟨64,162748966,162749061⟩]
theorem checked74548 : checkPrefixCuts (2^48) 9775087617 10 Manual.Count131072.C074548.packed 64 cuts74548 = true := by
 decide +kernel
def pointBounds74548 : List (Nat × Nat × Nat) := [(9775167488,116584895535399,116585285498475)]
theorem point_links_checked74548 : (cuts74548.take 1).map (fun c => (9775087617-1+2*2^10*c.k,116584796221413+c.lower,116585186184432+c.upper)) = pointBounds74548 := by
 decide +kernel
def cuts74549 : List PrefixCut := [⟨64,165568651,165568749⟩]
theorem checked74549 : checkPrefixCuts (2^48) 9775218689 10 Manual.Count131072.C074549.packed 64 cuts74549 = true := by
 decide +kernel
def cuts74550 : List PrefixCut := [⟨61,156582696,156582785⟩,
⟨64,164443452,164443546⟩]
theorem checked74550 : checkPrefixCuts (2^48) 9775349761 10 Manual.Count131072.C074550.packed 64 cuts74550 = true := by
 decide +kernel
def pointBounds74550 : List (Nat × Nat × Nat) := [(9775474688,116585281121726,116585671085027)]
theorem point_links_checked74550 : (cuts74550.take 1).map (fun c => (9775349761-1+2*2^10*c.k,116585124539030+c.lower,116585514502242+c.upper)) = pointBounds74550 := by
 decide +kernel
def cuts74551 : List PrefixCut := [⟨64,163721416,163721518⟩]
theorem checked74551 : checkPrefixCuts (2^48) 9775480833 10 Manual.Count131072.C074551.packed 64 cuts74551 = true := by
 decide +kernel
def cuts74552 : List PrefixCut := [⟨64,160811091,160811195⟩]
theorem checked74552 : checkPrefixCuts (2^48) 9775611905 10 Manual.Count131072.C074552.packed 64 cuts74552 = true := by
 decide +kernel
def cuts74553 : List PrefixCut := [⟨19,49696961,49696987⟩,
⟨64,165444601,165444703⟩]
theorem checked74553 : checkPrefixCuts (2^48) 9775742977 10 Manual.Count131072.C074553.packed 64 cuts74553 = true := by
 decide +kernel
def pointBounds74553 : List (Nat × Nat × Nat) := [(9775781888,116585663211950,116586053175488)]
theorem point_links_checked74553 : (cuts74553.take 1).map (fun c => (9775742977-1+2*2^10*c.k,116585613514989+c.lower,116586003478501+c.upper)) = pointBounds74553 := by
 decide +kernel
def cuts74554 : List PrefixCut := [⟨64,163455693,163455792⟩]
theorem checked74554 : checkPrefixCuts (2^48) 9775874049 10 Manual.Count131072.C074554.packed 64 cuts74554 = true := by
 decide +kernel
def cuts74555 : List PrefixCut := [⟨41,104343295,104343361⟩,
⟨64,163338322,163338424⟩]
theorem checked74555 : checkPrefixCuts (2^48) 9776005121 10 Manual.Count131072.C074555.packed 64 cuts74555 = true := by
 decide +kernel
def pointBounds74555 : List (Nat × Nat × Nat) := [(9776089088,116586046758578,116586436722357)]
theorem point_links_checked74555 : (cuts74555.take 1).map (fun c => (9776005121-1+2*2^10*c.k,116585942415283+c.lower,116586332378996+c.upper)) = pointBounds74555 := by
 decide +kernel
def cuts74556 : List PrefixCut := [⟨64,162213255,162213350⟩]
theorem checked74556 : checkPrefixCuts (2^48) 9776136193 10 Manual.Count131072.C074556.packed 64 cuts74556 = true := by
 decide +kernel
def cuts74557 : List PrefixCut := [⟨63,162009570,162009659⟩,
⟨64,164888697,164888788⟩]
theorem checked74557 : checkPrefixCuts (2^48) 9776267265 10 Manual.Count131072.C074557.packed 64 cuts74557 = true := by
 decide +kernel
def pointBounds74557 : List (Nat × Nat × Nat) := [(9776396288,116586429976430,116586819940429)]
theorem point_links_checked74557 : (cuts74557.take 1).map (fun c => (9776267265-1+2*2^10*c.k,116586267966860+c.lower,116586657930770+c.upper)) = pointBounds74557 := by
 decide +kernel
def cuts74558 : List PrefixCut := [⟨64,166613943,166614043⟩]
theorem checked74558 : checkPrefixCuts (2^48) 9776398337 10 Manual.Count131072.C074558.packed 64 cuts74558 = true := by
 decide +kernel
def cuts74559 : List PrefixCut := [⟨64,165460072,165460178⟩]
theorem checked74559 : checkPrefixCuts (2^48) 9776529409 10 Manual.Count131072.C074559.packed 64 cuts74559 = true := by
 decide +kernel
def cuts74560 : List PrefixCut := [⟨21,55651903,55651938⟩,
⟨64,166263991,166264087⟩]
theorem checked74560 : checkPrefixCuts (2^48) 9776660481 10 Manual.Count131072.C074560.packed 64 cuts74560 = true := by
 decide +kernel
def pointBounds74560 : List (Nat × Nat × Nat) := [(9776703488,116586820581475,116587210545717)]
theorem point_links_checked74560 : (cuts74560.take 1).map (fun c => (9776660481-1+2*2^10*c.k,116586764929572+c.lower,116587154893779+c.upper)) = pointBounds74560 := by
 decide +kernel
def cuts74561 : List PrefixCut := [⟨64,166463280,166463379⟩]
theorem checked74561 : checkPrefixCuts (2^48) 9776791553 10 Manual.Count131072.C074561.packed 64 cuts74561 = true := by
 decide +kernel
def cuts74562 : List PrefixCut := [⟨43,112308207,112308271⟩,
⟨64,165280704,165280799⟩]
theorem checked74562 : checkPrefixCuts (2^48) 9776922625 10 Manual.Count131072.C074562.packed 64 cuts74562 = true := by
 decide +kernel
def pointBounds74562 : List (Nat × Nat × Nat) := [(9777010688,116587209965050,116587599929516)]
theorem point_links_checked74562 : (cuts74562.take 1).map (fun c => (9776922625-1+2*2^10*c.k,116587097656843+c.lower,116587487621245+c.upper)) = pointBounds74562 := by
 decide +kernel
def cuts74563 : List PrefixCut := [⟨64,165537577,165537676⟩]
theorem checked74563 : checkPrefixCuts (2^48) 9777053697 10 Manual.Count131072.C074563.packed 64 cuts74563 = true := by
 decide +kernel
def cuts74564 : List PrefixCut := [⟨64,163462575,163462674⟩]
theorem checked74564 : checkPrefixCuts (2^48) 9777184769 10 Manual.Count131072.C074564.packed 64 cuts74564 = true := by
 decide +kernel
def cuts74565 : List PrefixCut := [⟨1,2706125,2706126⟩,
⟨64,161186092,161186193⟩]
theorem checked74565 : checkPrefixCuts (2^48) 9777315841 10 Manual.Count131072.C074565.packed 64 cuts74565 = true := by
 decide +kernel
def pointBounds74565 : List (Nat × Nat × Nat) := [(9777317888,116587594643824,116587984608520)]
theorem point_links_checked74565 : (cuts74565.take 1).map (fun c => (9777315841-1+2*2^10*c.k,116587591937699+c.lower,116587981902394+c.upper)) = pointBounds74565 := by
 decide +kernel
def cuts74566 : List PrefixCut := [⟨64,163371819,163371918⟩]
theorem checked74566 : checkPrefixCuts (2^48) 9777446913 10 Manual.Count131072.C074566.packed 64 cuts74566 = true := by
 decide +kernel
def cuts74567 : List PrefixCut := [⟨23,58755747,58755780⟩,
⟨64,164175678,164175777⟩]
theorem checked74567 : checkPrefixCuts (2^48) 9777577985 10 Manual.Count131072.C074567.packed 64 cuts74567 = true := by
 decide +kernel
def pointBounds74567 : List (Nat × Nat × Nat) := [(9777625088,116587975251357,116588365216285)]
theorem point_links_checked74567 : (cuts74567.take 1).map (fun c => (9777577985-1+2*2^10*c.k,116587916495610+c.lower,116588306460505+c.upper)) = pointBounds74567 := by
 decide +kernel
def cuts74568 : List PrefixCut := [⟨64,164921949,164922047⟩]
theorem checked74568 : checkPrefixCuts (2^48) 9777709057 10 Manual.Count131072.C074568.packed 64 cuts74568 = true := by
 decide +kernel
def cuts74569 : List PrefixCut := [⟨45,115147541,115147610⟩,
⟨64,162933453,162933549⟩]
theorem checked74569 : checkPrefixCuts (2^48) 9777840129 10 Manual.Count131072.C074569.packed 64 cuts74569 = true := by
 decide +kernel
def pointBounds74569 : List (Nat × Nat × Nat) := [(9777932288,116588360740778,116588750705939)]
theorem point_links_checked74569 : (cuts74569.take 1).map (fun c => (9777840129-1+2*2^10*c.k,116588245593237+c.lower,116588635558329+c.upper)) = pointBounds74569 := by
 decide +kernel
def cuts74570 : List PrefixCut := [⟨64,163478204,163478299⟩]
theorem checked74570 : checkPrefixCuts (2^48) 9777971201 10 Manual.Count131072.C074570.packed 64 cuts74570 = true := by
 decide +kernel
def cuts74571 : List PrefixCut := [⟨64,162756359,162756459⟩]
theorem checked74571 : checkPrefixCuts (2^48) 9778102273 10 Manual.Count131072.C074571.packed 64 cuts74571 = true := by
 decide +kernel
def cuts74572 : List PrefixCut := [⟨3,7657037,7657042⟩,
⟨64,163675313,163675417⟩]
theorem checked74572 : checkPrefixCuts (2^48) 9778233345 10 Manual.Count131072.C074572.packed 64 cuts74572 = true := by
 decide +kernel
def pointBounds74572 : List (Nat × Nat × Nat) := [(9778239488,116588742418290,116589132383678)]
theorem point_links_checked74572 : (cuts74572.take 1).map (fun c => (9778233345-1+2*2^10*c.k,116588734761253+c.lower,116589124726636+c.upper)) = pointBounds74572 := by
 decide +kernel
def cuts74573 : List PrefixCut := [⟨64,164392767,164392868⟩]
theorem checked74573 : checkPrefixCuts (2^48) 9778364417 10 Manual.Count131072.C074573.packed 64 cuts74573 = true := by
 decide +kernel
def cuts74574 : List PrefixCut := [⟨25,64161806,64161842⟩,
⟨64,164448132,164448229⟩]
theorem checked74574 : checkPrefixCuts (2^48) 9778495489 10 Manual.Count131072.C074574.packed 64 cuts74574 = true := by
 decide +kernel
def pointBounds74574 : List (Nat × Nat × Nat) := [(9778546688,116589126991139,116589516956763)]
theorem point_links_checked74574 : (cuts74574.take 1).map (fun c => (9778495489-1+2*2^10*c.k,116589062829333+c.lower,116589452794921+c.upper)) = pointBounds74574 := by
 decide +kernel
def cuts74575 : List PrefixCut := [⟨64,160963001,160963098⟩]
theorem checked74575 : checkPrefixCuts (2^48) 9778626561 10 Manual.Count131072.C074575.packed 64 cuts74575 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000142
