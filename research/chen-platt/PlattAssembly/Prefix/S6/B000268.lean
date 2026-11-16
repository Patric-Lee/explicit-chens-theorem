import PlattAssemblyKernel
import PlattCertificates.Count131072.C058576
import PlattCertificates.Count131072.C058577
import PlattCertificates.Count131072.C058578
import PlattCertificates.Count131072.C058579
import PlattCertificates.Count131072.C058580
import PlattCertificates.Count131072.C058581
import PlattCertificates.Count131072.C058582
import PlattCertificates.Count131072.C058583
import PlattCertificates.Count131072.C058584
import PlattCertificates.Count131072.C058585
import PlattCertificates.Count131072.C058586
import PlattCertificates.Count131072.C058587
import PlattCertificates.Count131072.C058588
import PlattCertificates.Count131072.C058589
import PlattCertificates.Count131072.C058590
import PlattCertificates.Count131072.C058591
import PlattCertificates.Count131072.C058592
import PlattCertificates.Count131072.C058593
import PlattCertificates.Count131072.C058594
import PlattCertificates.Count131072.C058595
import PlattCertificates.Count131072.C058596
import PlattCertificates.Count131072.C058597
import PlattCertificates.Count131072.C058598
import PlattCertificates.Count131072.C058599
import PlattCertificates.Count131072.C058600
import PlattCertificates.Count131072.C058601
import PlattCertificates.Count131072.C058602
import PlattCertificates.Count131072.C058603
import PlattCertificates.Count131072.C058604
import PlattCertificates.Count131072.C058605
import PlattCertificates.Count131072.C058606
import PlattCertificates.Count131072.C058607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000268
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58576 : List PrefixCut := [⟨64,211243462,211243579⟩]
theorem checked58576 : checkPrefixCuts (2^48) 7681605633 10 Manual.Count131072.C058576.packed 64 cuts58576 = true := by
 decide +kernel
def cuts58577 : List PrefixCut := [⟨8,25979215,25979231⟩,
⟨64,210433730,210433853⟩]
theorem checked58577 : checkPrefixCuts (2^48) 7681736705 10 Manual.Count131072.C058577.packed 64 cuts58577 = true := by
 decide +kernel
def pointBounds58577 : List (Nat × Nat × Nat) := [(7681753088,113620296524499,113620684762512)]
theorem point_links_checked58577 : (cuts58577.take 1).map (fun c => (7681736705-1+2*2^10*c.k,113620270545284+c.lower,113620658783281+c.upper)) = pointBounds58577 := by
 decide +kernel
def cuts58578 : List PrefixCut := [⟨62,205813407,205813523⟩,
⟨64,213031655,213031775⟩]
theorem checked58578 : checkPrefixCuts (2^48) 7681867777 10 Manual.Count131072.C058578.packed 64 cuts58578 = true := by
 decide +kernel
def pointBounds58578 : List (Nat × Nat × Nat) := [(7681994752,113620686792421,113621075030657)]
theorem point_links_checked58578 : (cuts58578.take 1).map (fun c => (7681867777-1+2*2^10*c.k,113620480979014+c.lower,113620869217134+c.upper)) = pointBounds58578 := by
 decide +kernel
def cuts58579 : List PrefixCut := [⟨64,207934993,207935113⟩]
theorem checked58579 : checkPrefixCuts (2^48) 7681998849 10 Manual.Count131072.C058579.packed 64 cuts58579 = true := by
 decide +kernel
def cuts58580 : List PrefixCut := [⟨52,170852149,170852243⟩,
⟨64,211009204,211009321⟩]
theorem checked58580 : checkPrefixCuts (2^48) 7682129921 10 Manual.Count131072.C058580.packed 64 cuts58580 = true := by
 decide +kernel
def pointBounds58580 : List (Nat × Nat × Nat) := [(7682236416,113621072797811,113621461036265)]
theorem point_links_checked58580 : (cuts58580.take 1).map (fun c => (7682129921-1+2*2^10*c.k,113620901945662+c.lower,113621290184022+c.upper)) = pointBounds58580 := by
 decide +kernel
def cuts58581 : List PrefixCut := [⟨64,211775024,211775146⟩]
theorem checked58581 : checkPrefixCuts (2^48) 7682260993 10 Manual.Count131072.C058581.packed 64 cuts58581 = true := by
 decide +kernel
def cuts58582 : List PrefixCut := [⟨42,138311318,138311396⟩,
⟨64,210672254,210672372⟩]
theorem checked58582 : checkPrefixCuts (2^48) 7682392065 10 Manual.Count131072.C058582.packed 64 cuts58582 = true := by
 decide +kernel
def pointBounds58582 : List (Nat × Nat × Nat) := [(7682478080,113621463041208,113621851279885)]
theorem point_links_checked58582 : (cuts58582.take 1).map (fun c => (7682392065-1+2*2^10*c.k,113621324729890+c.lower,113621712968489+c.upper)) = pointBounds58582 := by
 decide +kernel
def cuts58583 : List PrefixCut := [⟨64,209276411,209276528⟩]
theorem checked58583 : checkPrefixCuts (2^48) 7682523137 10 Manual.Count131072.C058583.packed 64 cuts58583 = true := by
 decide +kernel
def cuts58584 : List PrefixCut := [⟨32,104820050,104820112⟩,
⟨64,211361161,211361285⟩]
theorem checked58584 : checkPrefixCuts (2^48) 7682654209 10 Manual.Count131072.C058584.packed 64 cuts58584 = true := by
 decide +kernel
def pointBounds58584 : List (Nat × Nat × Nat) := [(7682719744,113621849498605,113622237737501)]
theorem point_links_checked58584 : (cuts58584.take 1).map (fun c => (7682654209-1+2*2^10*c.k,113621744678555+c.lower,113622132917389+c.upper)) = pointBounds58584 := by
 decide +kernel
def cuts58585 : List PrefixCut := [⟨64,210111929,210112046⟩]
theorem checked58585 : checkPrefixCuts (2^48) 7682785281 10 Manual.Count131072.C058585.packed 64 cuts58585 = true := by
 decide +kernel
def cuts58586 : List PrefixCut := [⟨22,72356807,72356848⟩,
⟨64,208826083,208826202⟩]
theorem checked58586 : checkPrefixCuts (2^48) 7682916353 10 Manual.Count131072.C058586.packed 64 cuts58586 = true := by
 decide +kernel
def pointBounds58586 : List (Nat × Nat × Nat) := [(7682961408,113622238508452,113622626747568)]
theorem point_links_checked58586 : (cuts58586.take 1).map (fun c => (7682916353-1+2*2^10*c.k,113622166151645+c.lower,113622554390720+c.upper)) = pointBounds58586 := by
 decide +kernel
def cuts58587 : List PrefixCut := [⟨64,209884933,209885051⟩]
theorem checked58587 : checkPrefixCuts (2^48) 7683047425 10 Manual.Count131072.C058587.packed 64 cuts58587 = true := by
 decide +kernel
def cuts58588 : List PrefixCut := [⟨12,38613458,38613480⟩,
⟨64,211017038,211017157⟩]
theorem checked58588 : checkPrefixCuts (2^48) 7683178497 10 Manual.Count131072.C058588.packed 64 cuts58588 = true := by
 decide +kernel
def pointBounds58588 : List (Nat × Nat × Nat) := [(7683203072,113622623476119,113623011715453)]
theorem point_links_checked58588 : (cuts58588.take 1).map (fun c => (7683178497-1+2*2^10*c.k,113622584862661+c.lower,113622973101973+c.upper)) = pointBounds58588 := by
 decide +kernel
def cuts58589 : List PrefixCut := [⟨64,210170847,210170968⟩]
theorem checked58589 : checkPrefixCuts (2^48) 7683309569 10 Manual.Count131072.C058589.packed 64 cuts58589 = true := by
 decide +kernel
def cuts58590 : List PrefixCut := [⟨2,6191139,6191142⟩,
⟨64,206320716,206320834⟩]
theorem checked58590 : checkPrefixCuts (2^48) 7683440641 10 Manual.Count131072.C058590.packed 64 cuts58590 = true := by
 decide +kernel
def pointBounds58590 : List (Nat × Nat × Nat) := [(7683444736,113623012241685,113623400481240)]
theorem point_links_checked58590 : (cuts58590.take 1).map (fun c => (7683440641-1+2*2^10*c.k,113623006050546+c.lower,113623394290098+c.upper)) = pointBounds58590 := by
 decide +kernel
def cuts58591 : List PrefixCut := [⟨56,187414770,187414878⟩,
⟨64,212874535,212874659⟩]
theorem checked58591 : checkPrefixCuts (2^48) 7683571713 10 Manual.Count131072.C058591.packed 64 cuts58591 = true := by
 decide +kernel
def pointBounds58591 : List (Nat × Nat × Nat) := [(7683686400,113623399786032,113623788025810)]
theorem point_links_checked58591 : (cuts58591.take 1).map (fun c => (7683571713-1+2*2^10*c.k,113623212371262+c.lower,113623600610932+c.upper)) = pointBounds58591 := by
 decide +kernel
def cuts58592 : List PrefixCut := [⟨64,210526418,210526541⟩]
theorem checked58592 : checkPrefixCuts (2^48) 7683702785 10 Manual.Count131072.C058592.packed 64 cuts58592 = true := by
 decide +kernel
def cuts58593 : List PrefixCut := [⟨46,153340998,153341086⟩,
⟨64,213233590,213233711⟩]
theorem checked58593 : checkPrefixCuts (2^48) 7683833857 10 Manual.Count131072.C058593.packed 64 cuts58593 = true := by
 decide +kernel
def pointBounds58593 : List (Nat × Nat × Nat) := [(7683928064,113623789113213,113624177353218)]
theorem point_links_checked58593 : (cuts58593.take 1).map (fun c => (7683833857-1+2*2^10*c.k,113623635772215+c.lower,113624024012132+c.upper)) = pointBounds58593 := by
 decide +kernel
def cuts58594 : List PrefixCut := [⟨64,211654789,211654905⟩]
theorem checked58594 : checkPrefixCuts (2^48) 7683964929 10 Manual.Count131072.C058594.packed 64 cuts58594 = true := by
 decide +kernel
def cuts58595 : List PrefixCut := [⟨36,119159555,119159627⟩,
⟨64,211101739,211101863⟩]
theorem checked58595 : checkPrefixCuts (2^48) 7684096001 10 Manual.Count131072.C058595.packed 64 cuts58595 = true := by
 decide +kernel
def pointBounds58595 : List (Nat × Nat × Nat) := [(7684169728,113624179820149,113624568060375)]
theorem point_links_checked58595 : (cuts58595.take 1).map (fun c => (7684096001-1+2*2^10*c.k,113624060660594+c.lower,113624448900748+c.upper)) = pointBounds58595 := by
 decide +kernel
def cuts58596 : List PrefixCut := [⟨64,209742837,209742959⟩]
theorem checked58596 : checkPrefixCuts (2^48) 7684227073 10 Manual.Count131072.C058596.packed 64 cuts58596 = true := by
 decide +kernel
def cuts58597 : List PrefixCut := [⟨26,86482165,86482215⟩,
⟨64,211021279,211021404⟩]
theorem checked58597 : checkPrefixCuts (2^48) 7684358145 10 Manual.Count131072.C058597.packed 64 cuts58597 = true := by
 decide +kernel
def pointBounds58597 : List (Nat × Nat × Nat) := [(7684411392,113624567987335,113624956227785)]
theorem point_links_checked58597 : (cuts58597.take 1).map (fun c => (7684358145-1+2*2^10*c.k,113624481505170+c.lower,113624869745570+c.upper)) = pointBounds58597 := by
 decide +kernel
def cuts58598 : List PrefixCut := [⟨64,211054299,211054421⟩]
theorem checked58598 : checkPrefixCuts (2^48) 7684489217 10 Manual.Count131072.C058598.packed 64 cuts58598 = true := by
 decide +kernel
def cuts58599 : List PrefixCut := [⟨16,53843549,53843579⟩,
⟨64,214603620,214603741⟩]
theorem checked58599 : checkPrefixCuts (2^48) 7684620289 10 Manual.Count131072.C058599.packed 64 cuts58599 = true := by
 decide +kernel
def pointBounds58599 : List (Nat × Nat × Nat) := [(7684653056,113624957424297,113625345664974)]
theorem point_links_checked58599 : (cuts58599.take 1).map (fun c => (7684620289-1+2*2^10*c.k,113624903580748+c.lower,113625291821395+c.upper)) = pointBounds58599 := by
 decide +kernel
def cuts58600 : List PrefixCut := [⟨64,210717466,210717585⟩]
theorem checked58600 : checkPrefixCuts (2^48) 7684751361 10 Manual.Count131072.C058600.packed 64 cuts58600 = true := by
 decide +kernel
def cuts58601 : List PrefixCut := [⟨6,19925122,19925134⟩,
⟨64,209541801,209541923⟩]
theorem checked58601 : checkPrefixCuts (2^48) 7684882433 10 Manual.Count131072.C058601.packed 64 cuts58601 = true := by
 decide +kernel
def pointBounds58601 : List (Nat × Nat × Nat) := [(7684894720,113625348826956,113625737067855)]
theorem point_links_checked58601 : (cuts58601.take 1).map (fun c => (7684882433-1+2*2^10*c.k,113625328901834+c.lower,113625717142721+c.upper)) = pointBounds58601 := by
 decide +kernel
def cuts58602 : List PrefixCut := [⟨60,197488338,197488450⟩,
⟨64,210527144,210527264⟩]
theorem checked58602 : checkPrefixCuts (2^48) 7685013505 10 Manual.Count131072.C058602.packed 64 cuts58602 = true := by
 decide +kernel
def pointBounds58602 : List (Nat × Nat × Nat) := [(7685136384,113625735931973,113626124173094)]
theorem point_links_checked58602 : (cuts58602.take 1).map (fun c => (7685013505-1+2*2^10*c.k,113625538443635+c.lower,113625926684644+c.upper)) = pointBounds58602 := by
 decide +kernel
def cuts58603 : List PrefixCut := [⟨64,213123974,213124094⟩]
theorem checked58603 : checkPrefixCuts (2^48) 7685144577 10 Manual.Count131072.C058603.packed 64 cuts58603 = true := by
 decide +kernel
def cuts58604 : List PrefixCut := [⟨50,162065508,162065601⟩,
⟨64,208359080,208359198⟩]
theorem checked58604 : checkPrefixCuts (2^48) 7685275649 10 Manual.Count131072.C058604.packed 64 cuts58604 = true := by
 decide +kernel
def pointBounds58604 : List (Nat × Nat × Nat) := [(7685378048,113626124160261,113626512401603)]
theorem point_links_checked58604 : (cuts58604.take 1).map (fun c => (7685275649-1+2*2^10*c.k,113625962094753+c.lower,113626350336002+c.upper)) = pointBounds58604 := by
 decide +kernel
def cuts58605 : List PrefixCut := [⟨64,210443108,210443227⟩]
theorem checked58605 : checkPrefixCuts (2^48) 7685406721 10 Manual.Count131072.C058605.packed 64 cuts58605 = true := by
 decide +kernel
def cuts58606 : List PrefixCut := [⟨40,133640152,133640231⟩,
⟨64,212050980,212051106⟩]
theorem checked58606 : checkPrefixCuts (2^48) 7685537793 10 Manual.Count131072.C058606.packed 64 cuts58606 = true := by
 decide +kernel
def pointBounds58606 : List (Nat × Nat × Nat) := [(7685619712,113626514537093,113626902778658)]
theorem point_links_checked58606 : (cuts58606.take 1).map (fun c => (7685537793-1+2*2^10*c.k,113626380896941+c.lower,113626769138427+c.upper)) = pointBounds58606 := by
 decide +kernel
def cuts58607 : List PrefixCut := [⟨64,211607867,211607988⟩]
theorem checked58607 : checkPrefixCuts (2^48) 7685668865 10 Manual.Count131072.C058607.packed 64 cuts58607 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000268
