import PlattAssemblyKernel
import PlattCertificates.Count131072.C071568
import PlattCertificates.Count131072.C071569
import PlattCertificates.Count131072.C071570
import PlattCertificates.Count131072.C071571
import PlattCertificates.Count131072.C071572
import PlattCertificates.Count131072.C071573
import PlattCertificates.Count131072.C071574
import PlattCertificates.Count131072.C071575
import PlattCertificates.Count131072.C071576
import PlattCertificates.Count131072.C071577
import PlattCertificates.Count131072.C071578
import PlattCertificates.Count131072.C071579
import PlattCertificates.Count131072.C071580
import PlattCertificates.Count131072.C071581
import PlattCertificates.Count131072.C071582
import PlattCertificates.Count131072.C071583
import PlattCertificates.Count131072.C071584
import PlattCertificates.Count131072.C071585
import PlattCertificates.Count131072.C071586
import PlattCertificates.Count131072.C071587
import PlattCertificates.Count131072.C071588
import PlattCertificates.Count131072.C071589
import PlattCertificates.Count131072.C071590
import PlattCertificates.Count131072.C071591
import PlattCertificates.Count131072.C071592
import PlattCertificates.Count131072.C071593
import PlattCertificates.Count131072.C071594
import PlattCertificates.Count131072.C071595
import PlattCertificates.Count131072.C071596
import PlattCertificates.Count131072.C071597
import PlattCertificates.Count131072.C071598
import PlattCertificates.Count131072.C071599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71568 : List PrefixCut := [⟨64,171952199,171952301⟩]
theorem checked71568 : checkPrefixCuts (2^48) 9384493057 10 Manual.Count131072.C071568.packed 64 cuts71568 = true := by
 decide +kernel
def cuts71569 : List PrefixCut := [⟨46,122641569,122641642⟩,
⟨64,170630111,170630213⟩]
theorem checked71569 : checkPrefixCuts (2^48) 9384624129 10 Manual.Count131072.C071569.packed 64 cuts71569 = true := by
 decide +kernel
def pointBounds71569 : List (Nat × Nat × Nat) := [(9384718336,116085607617579,116085997283276)]
theorem point_links_checked71569 : (cuts71569.take 1).map (fun c => (9384624129-1+2*2^10*c.k,116085484976010+c.lower,116085874641634+c.upper)) = pointBounds71569 := by
 decide +kernel
def cuts71570 : List PrefixCut := [⟨64,167568479,167568576⟩]
theorem checked71570 : checkPrefixCuts (2^48) 9384755201 10 Manual.Count131072.C071570.packed 64 cuts71570 = true := by
 decide +kernel
def cuts71571 : List PrefixCut := [⟨62,168196027,168196122⟩,
⟨64,173624570,173624668⟩]
theorem checked71571 : checkPrefixCuts (2^48) 9384886273 10 Manual.Count131072.C071571.packed 64 cuts71571 = true := by
 decide +kernel
def pointBounds71571 : List (Nat × Nat × Nat) := [(9385013248,116085991370627,116086381036545)]
theorem point_links_checked71571 : (cuts71571.take 1).map (fun c => (9384886273-1+2*2^10*c.k,116085823174600+c.lower,116086212840423+c.upper)) = pointBounds71571 := by
 decide +kernel
def cuts71572 : List PrefixCut := [⟨64,170862899,170863001⟩]
theorem checked71572 : checkPrefixCuts (2^48) 9385017345 10 Manual.Count131072.C071572.packed 64 cuts71572 = true := by
 decide +kernel
def cuts71573 : List PrefixCut := [⟨64,172570020,172570117⟩]
theorem checked71573 : checkPrefixCuts (2^48) 9385148417 10 Manual.Count131072.C071573.packed 64 cuts71573 = true := by
 decide +kernel
def cuts71574 : List PrefixCut := [⟨14,36769037,36769060⟩,
⟨64,170018371,170018475⟩]
theorem checked71574 : checkPrefixCuts (2^48) 9385279489 10 Manual.Count131072.C071574.packed 64 cuts71574 = true := by
 decide +kernel
def pointBounds71574 : List (Nat × Nat × Nat) := [(9385308160,116086377001126,116086766667269)]
theorem point_links_checked71574 : (cuts71574.take 1).map (fun c => (9385279489-1+2*2^10*c.k,116086340232089+c.lower,116086729898209+c.upper)) = pointBounds71574 := by
 decide +kernel
def cuts71575 : List PrefixCut := [⟨64,169806090,169806185⟩]
theorem checked71575 : checkPrefixCuts (2^48) 9385410561 10 Manual.Count131072.C071575.packed 64 cuts71575 = true := by
 decide +kernel
def cuts71576 : List PrefixCut := [⟨30,80523602,80523649⟩,
⟨64,171603106,171603209⟩]
theorem checked71576 : checkPrefixCuts (2^48) 9385541633 10 Manual.Count131072.C071576.packed 64 cuts71576 = true := by
 decide +kernel
def pointBounds71576 : List (Nat × Nat × Nat) := [(9385603072,116086760580152,116087150246518)]
theorem point_links_checked71576 : (cuts71576.take 1).map (fun c => (9385541633-1+2*2^10*c.k,116086680056550+c.lower,116087069722869+c.upper)) = pointBounds71576 := by
 decide +kernel
def cuts71577 : List PrefixCut := [⟨64,171000920,171001021⟩]
theorem checked71577 : checkPrefixCuts (2^48) 9385672705 10 Manual.Count131072.C071577.packed 64 cuts71577 = true := by
 decide +kernel
def cuts71578 : List PrefixCut := [⟨46,122326257,122326330⟩,
⟨64,170998517,170998619⟩]
theorem checked71578 : checkPrefixCuts (2^48) 9385803777 10 Manual.Count131072.C071578.packed 64 cuts71578 = true := by
 decide +kernel
def pointBounds71578 : List (Nat × Nat × Nat) := [(9385897984,116087144986833,116087534653429)]
theorem point_links_checked71578 : (cuts71578.take 1).map (fun c => (9385803777-1+2*2^10*c.k,116087022660576+c.lower,116087412327099+c.upper)) = pointBounds71578 := by
 decide +kernel
def cuts71579 : List PrefixCut := [⟨64,171655888,171655989⟩]
theorem checked71579 : checkPrefixCuts (2^48) 9385934849 10 Manual.Count131072.C071579.packed 64 cuts71579 = true := by
 decide +kernel
def cuts71580 : List PrefixCut := [⟨62,166195665,166195755⟩,
⟨64,171803454,171803548⟩]
theorem checked71580 : checkPrefixCuts (2^48) 9386065921 10 Manual.Count131072.C071580.packed 64 cuts71580 = true := by
 decide +kernel
def pointBounds71580 : List (Nat × Nat × Nat) := [(9386192896,116087531510646,116087921177462)]
theorem point_links_checked71580 : (cuts71580.take 1).map (fun c => (9386065921-1+2*2^10*c.k,116087365314981+c.lower,116087754981707+c.upper)) = pointBounds71580 := by
 decide +kernel
def cuts71581 : List PrefixCut := [⟨64,170811440,170811544⟩]
theorem checked71581 : checkPrefixCuts (2^48) 9386196993 10 Manual.Count131072.C071581.packed 64 cuts71581 = true := by
 decide +kernel
def cuts71582 : List PrefixCut := [⟨64,172338410,172338514⟩]
theorem checked71582 : checkPrefixCuts (2^48) 9386328065 10 Manual.Count131072.C071582.packed 64 cuts71582 = true := by
 decide +kernel
def cuts71583 : List PrefixCut := [⟨14,37933920,37933941⟩,
⟨64,169397280,169397379⟩]
theorem checked71583 : checkPrefixCuts (2^48) 9386459137 10 Manual.Count131072.C071583.packed 64 cuts71583 = true := by
 decide +kernel
def pointBounds71583 : List (Nat × Nat × Nat) := [(9386487808,116087918202205,116088307869254)]
theorem point_links_checked71583 : (cuts71583.take 1).map (fun c => (9386459137-1+2*2^10*c.k,116087880268285+c.lower,116088269935313+c.upper)) = pointBounds71583 := by
 decide +kernel
def cuts71584 : List PrefixCut := [⟨64,170624368,170624465⟩]
theorem checked71584 : checkPrefixCuts (2^48) 9386590209 10 Manual.Count131072.C071584.packed 64 cuts71584 = true := by
 decide +kernel
def cuts71585 : List PrefixCut := [⟨30,79254054,79254099⟩,
⟨64,169542474,169542574⟩]
theorem checked71585 : checkPrefixCuts (2^48) 9386721281 10 Manual.Count131072.C071585.packed 64 cuts71585 = true := by
 decide +kernel
def pointBounds71585 : List (Nat × Nat × Nat) := [(9386782720,116088299543987,116088689211256)]
theorem point_links_checked71585 : (cuts71585.take 1).map (fun c => (9386721281-1+2*2^10*c.k,116088220289933+c.lower,116088609957157+c.upper)) = pointBounds71585 := by
 decide +kernel
def cuts71586 : List PrefixCut := [⟨64,171369244,171369343⟩]
theorem checked71586 : checkPrefixCuts (2^48) 9386852353 10 Manual.Count131072.C071586.packed 64 cuts71586 = true := by
 decide +kernel
def cuts71587 : List PrefixCut := [⟨46,123480321,123480394⟩,
⟨64,173135977,173136080⟩]
theorem checked71587 : checkPrefixCuts (2^48) 9386983425 10 Manual.Count131072.C071587.packed 64 cuts71587 = true := by
 decide +kernel
def pointBounds71587 : List (Nat × Nat × Nat) := [(9387077632,116088684681972,116089074349468)]
theorem point_links_checked71587 : (cuts71587.take 1).map (fun c => (9386983425-1+2*2^10*c.k,116088561201651+c.lower,116088950869074+c.upper)) = pointBounds71587 := by
 decide +kernel
def cuts71588 : List PrefixCut := [⟨64,170854706,170854803⟩]
theorem checked71588 : checkPrefixCuts (2^48) 9387114497 10 Manual.Count131072.C071588.packed 64 cuts71588 = true := by
 decide +kernel
def cuts71589 : List PrefixCut := [⟨62,163746018,163746113⟩,
⟨64,168453570,168453668⟩]
theorem checked71589 : checkPrefixCuts (2^48) 9387245569 10 Manual.Count131072.C071589.packed 64 cuts71589 = true := by
 decide +kernel
def pointBounds71589 : List (Nat × Nat × Nat) := [(9387372544,116089068938352,116089458606070)]
theorem point_links_checked71589 : (cuts71589.take 1).map (fun c => (9387245569-1+2*2^10*c.k,116088905192334+c.lower,116089294859957+c.upper)) = pointBounds71589 := by
 decide +kernel
def cuts71590 : List PrefixCut := [⟨64,169710545,169710644⟩]
theorem checked71590 : checkPrefixCuts (2^48) 9387376641 10 Manual.Count131072.C071590.packed 64 cuts71590 = true := by
 decide +kernel
def cuts71591 : List PrefixCut := [⟨64,171267327,171267432⟩]
theorem checked71591 : checkPrefixCuts (2^48) 9387507713 10 Manual.Count131072.C071591.packed 64 cuts71591 = true := by
 decide +kernel
def cuts71592 : List PrefixCut := [⟨14,38588792,38588814⟩,
⟨64,174113361,174113465⟩]
theorem checked71592 : checkPrefixCuts (2^48) 9387638785 10 Manual.Count131072.C071592.packed 64 cuts71592 = true := by
 decide +kernel
def pointBounds71592 : List (Nat × Nat × Nat) := [(9387667456,116089453212568,116089842880515)]
theorem point_links_checked71592 : (cuts71592.take 1).map (fun c => (9387638785-1+2*2^10*c.k,116089414623776+c.lower,116089804291701+c.upper)) = pointBounds71592 := by
 decide +kernel
def cuts71593 : List PrefixCut := [⟨64,168204295,168204394⟩]
theorem checked71593 : checkPrefixCuts (2^48) 9387769857 10 Manual.Count131072.C071593.packed 64 cuts71593 = true := by
 decide +kernel
def cuts71594 : List PrefixCut := [⟨30,80683260,80683307⟩,
⟨64,172429476,172429572⟩]
theorem checked71594 : checkPrefixCuts (2^48) 9387900929 10 Manual.Count131072.C071594.packed 64 cuts71594 = true := by
 decide +kernel
def pointBounds71594 : List (Nat × Nat × Nat) := [(9387962368,116089837624692,116090227292867)]
theorem point_links_checked71594 : (cuts71594.take 1).map (fun c => (9387900929-1+2*2^10*c.k,116089756941432+c.lower,116090146609560+c.upper)) = pointBounds71594 := by
 decide +kernel
def cuts71595 : List PrefixCut := [⟨64,172786856,172786955⟩]
theorem checked71595 : checkPrefixCuts (2^48) 9388032001 10 Manual.Count131072.C071595.packed 64 cuts71595 = true := by
 decide +kernel
def cuts71596 : List PrefixCut := [⟨46,125833368,125833441⟩,
⟨64,173533986,173534085⟩]
theorem checked71596 : checkPrefixCuts (2^48) 9388163073 10 Manual.Count131072.C071596.packed 64 cuts71596 = true := by
 decide +kernel
def pointBounds71596 : List (Nat × Nat × Nat) := [(9388257280,116090227991132,116090617659528)]
theorem point_links_checked71596 : (cuts71596.take 1).map (fun c => (9388163073-1+2*2^10*c.k,116090102157764+c.lower,116090491826087+c.upper)) = pointBounds71596 := by
 decide +kernel
def cuts71597 : List PrefixCut := [⟨64,171672722,171672818⟩]
theorem checked71597 : checkPrefixCuts (2^48) 9388294145 10 Manual.Count131072.C071597.packed 64 cuts71597 = true := by
 decide +kernel
def cuts71598 : List PrefixCut := [⟨62,164385011,164385111⟩,
⟨64,169691585,169691688⟩]
theorem checked71598 : checkPrefixCuts (2^48) 9388425217 10 Manual.Count131072.C071598.packed 64 cuts71598 = true := by
 decide +kernel
def pointBounds71598 : List (Nat × Nat × Nat) := [(9388552192,116090611749483,116091001418101)]
theorem point_links_checked71598 : (cuts71598.take 1).map (fun c => (9388425217-1+2*2^10*c.k,116090447364472+c.lower,116090837032990+c.upper)) = pointBounds71598 := by
 decide +kernel
def cuts71599 : List PrefixCut := [⟨64,174216256,174216361⟩]
theorem checked71599 : checkPrefixCuts (2^48) 9388556289 10 Manual.Count131072.C071599.packed 64 cuts71599 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000049
