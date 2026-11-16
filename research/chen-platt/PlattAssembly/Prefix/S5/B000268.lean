import PlattAssemblyKernel
import PlattCertificates.Count131072.C048576
import PlattCertificates.Count131072.C048577
import PlattCertificates.Count131072.C048578
import PlattCertificates.Count131072.C048579
import PlattCertificates.Count131072.C048580
import PlattCertificates.Count131072.C048581
import PlattCertificates.Count131072.C048582
import PlattCertificates.Count131072.C048583
import PlattCertificates.Count131072.C048584
import PlattCertificates.Count131072.C048585
import PlattCertificates.Count131072.C048586
import PlattCertificates.Count131072.C048587
import PlattCertificates.Count131072.C048588
import PlattCertificates.Count131072.C048589
import PlattCertificates.Count131072.C048590
import PlattCertificates.Count131072.C048591
import PlattCertificates.Count131072.C048592
import PlattCertificates.Count131072.C048593
import PlattCertificates.Count131072.C048594
import PlattCertificates.Count131072.C048595
import PlattCertificates.Count131072.C048596
import PlattCertificates.Count131072.C048597
import PlattCertificates.Count131072.C048598
import PlattCertificates.Count131072.C048599
import PlattCertificates.Count131072.C048600
import PlattCertificates.Count131072.C048601
import PlattCertificates.Count131072.C048602
import PlattCertificates.Count131072.C048603
import PlattCertificates.Count131072.C048604
import PlattCertificates.Count131072.C048605
import PlattCertificates.Count131072.C048606
import PlattCertificates.Count131072.C048607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000268
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48576 : List PrefixCut := [⟨64,257619317,257619464⟩]
theorem checked48576 : checkPrefixCuts (2^48) 6370885633 10 Manual.Count131072.C048576.packed 64 cuts48576 = true := by
 decide +kernel
def cuts48577 : List PrefixCut := [⟨4,16611869,16611878⟩,
⟨64,255802634,255802783⟩]
theorem checked48577 : checkPrefixCuts (2^48) 6371016705 10 Manual.Count131072.C048577.packed 64 cuts48577 = true := by
 decide +kernel
def pointBounds48577 : List (Nat × Nat × Nat) := [(6371024896,111297349315811,111297736232788)]
theorem point_links_checked48577 : (cuts48577.take 1).map (fun c => (6371016705-1+2*2^10*c.k,111297332703942+c.lower,111297719620910+c.upper)) = pointBounds48577 := by
 decide +kernel
def cuts48578 : List PrefixCut := [⟨38,149370375,149370462⟩,
⟨64,253676754,253676905⟩]
theorem checked48578 : checkPrefixCuts (2^48) 6371147777 10 Manual.Count131072.C048578.packed 64 cuts48578 = true := by
 decide +kernel
def pointBounds48578 : List (Nat × Nat × Nat) := [(6371225600,111297737876951,111298124794155)]
theorem point_links_checked48578 : (cuts48578.take 1).map (fun c => (6371147777-1+2*2^10*c.k,111297588506576+c.lower,111297975423693+c.upper)) = pointBounds48578 := by
 decide +kernel
def cuts48579 : List PrefixCut := [⟨64,260916782,260916931⟩]
theorem checked48579 : checkPrefixCuts (2^48) 6371278849 10 Manual.Count131072.C048579.packed 64 cuts48579 = true := by
 decide +kernel
def cuts48580 : List PrefixCut := [⟨8,31852156,31852173⟩,
⟨64,256405333,256405479⟩]
theorem checked48580 : checkPrefixCuts (2^48) 6371409921 10 Manual.Count131072.C048580.packed 64 cuts48580 = true := by
 decide +kernel
def pointBounds48580 : List (Nat × Nat × Nat) := [(6371426304,111298134952268,111298521869702)]
theorem point_links_checked48580 : (cuts48580.take 1).map (fun c => (6371409921-1+2*2^10*c.k,111298103100112+c.lower,111298490017529+c.upper)) = pointBounds48580 := by
 decide +kernel
def cuts48581 : List PrefixCut := [⟨42,165220481,165220576⟩,
⟨64,254721343,254721490⟩]
theorem checked48581 : checkPrefixCuts (2^48) 6371540993 10 Manual.Count131072.C048581.packed 64 cuts48581 = true := by
 decide +kernel
def pointBounds48581 : List (Nat × Nat × Nat) := [(6371627008,111298524725926,111298911643584)]
theorem point_links_checked48581 : (cuts48581.take 1).map (fun c => (6371540993-1+2*2^10*c.k,111298359505445+c.lower,111298746423008+c.upper)) = pointBounds48581 := by
 decide +kernel
def cuts48582 : List PrefixCut := [⟨64,256218083,256218230⟩]
theorem checked48582 : checkPrefixCuts (2^48) 6371672065 10 Manual.Count131072.C048582.packed 64 cuts48582 = true := by
 decide +kernel
def cuts48583 : List PrefixCut := [⟨12,46383743,46383769⟩,
⟨64,254004059,254004208⟩]
theorem checked48583 : checkPrefixCuts (2^48) 6371803137 10 Manual.Count131072.C048583.packed 64 cuts48583 = true := by
 decide +kernel
def pointBounds48583 : List (Nat × Nat × Nat) := [(6371827712,111298916828614,111299303746497)]
theorem point_links_checked48583 : (cuts48583.take 1).map (fun c => (6371803137-1+2*2^10*c.k,111298870444871+c.lower,111299257362728+c.upper)) = pointBounds48583 := by
 decide +kernel
def cuts48584 : List PrefixCut := [⟨46,183453966,183454073⟩,
⟨64,252496968,252497115⟩]
theorem checked48584 : checkPrefixCuts (2^48) 6371934209 10 Manual.Count131072.C048584.packed 64 cuts48584 = true := by
 decide +kernel
def pointBounds48584 : List (Nat × Nat × Nat) := [(6372028416,111299307902896,111299694821009)]
theorem point_links_checked48584 : (cuts48584.take 1).map (fun c => (6371934209-1+2*2^10*c.k,111299124448930+c.lower,111299511366936+c.upper)) = pointBounds48584 := by
 decide +kernel
def cuts48585 : List PrefixCut := [⟨64,256290628,256290770⟩]
theorem checked48585 : checkPrefixCuts (2^48) 6372065281 10 Manual.Count131072.C048585.packed 64 cuts48585 = true := by
 decide +kernel
def cuts48586 : List PrefixCut := [⟨16,63033785,63033821⟩,
⟨64,256859582,256859730⟩]
theorem checked48586 : checkPrefixCuts (2^48) 6372196353 10 Manual.Count131072.C048586.packed 64 cuts48586 = true := by
 decide +kernel
def pointBounds48586 : List (Nat × Nat × Nat) := [(6372229120,111299696270311,111300083188642)]
theorem point_links_checked48586 : (cuts48586.take 1).map (fun c => (6372196353-1+2*2^10*c.k,111299633236526+c.lower,111300020154821+c.upper)) = pointBounds48586 := by
 decide +kernel
def cuts48587 : List PrefixCut := [⟨50,202612785,202612898⟩,
⟨64,256810150,256810296⟩]
theorem checked48587 : checkPrefixCuts (2^48) 6372327425 10 Manual.Count131072.C048587.packed 64 cuts48587 = true := by
 decide +kernel
def pointBounds48587 : List (Nat × Nat × Nat) := [(6372429824,111300092708893,111300479627449)]
theorem point_links_checked48587 : (cuts48587.take 1).map (fun c => (6372327425-1+2*2^10*c.k,111299890096108+c.lower,111300277014551+c.upper)) = pointBounds48587 := by
 decide +kernel
def cuts48588 : List PrefixCut := [⟨64,255347255,255347405⟩]
theorem checked48588 : checkPrefixCuts (2^48) 6372458497 10 Manual.Count131072.C048588.packed 64 cuts48588 = true := by
 decide +kernel
def cuts48589 : List PrefixCut := [⟨20,78047482,78047526⟩,
⟨64,255297806,255297950⟩]
theorem checked48589 : checkPrefixCuts (2^48) 6372589569 10 Manual.Count131072.C048589.packed 64 cuts48589 = true := by
 decide +kernel
def pointBounds48589 : List (Nat × Nat × Nat) := [(6372630528,111300480300995,111300867219778)]
theorem point_links_checked48589 : (cuts48589.take 1).map (fun c => (6372589569-1+2*2^10*c.k,111300402253513+c.lower,111300789172252+c.upper)) = pointBounds48589 := by
 decide +kernel
def cuts48590 : List PrefixCut := [⟨54,215276468,215276593⟩,
⟨64,256308429,256308575⟩]
theorem checked48590 : checkPrefixCuts (2^48) 6372720641 10 Manual.Count131072.C048590.packed 64 cuts48590 = true := by
 decide +kernel
def pointBounds48590 : List (Nat × Nat × Nat) := [(6372831232,111300872827787,111301259746795)]
theorem point_links_checked48590 : (cuts48590.take 1).map (fun c => (6372720641-1+2*2^10*c.k,111300657551319+c.lower,111301044470202+c.upper)) = pointBounds48590 := by
 decide +kernel
def cuts48591 : List PrefixCut := [⟨64,252372284,252372426⟩]
theorem checked48591 : checkPrefixCuts (2^48) 6372851713 10 Manual.Count131072.C048591.packed 64 cuts48591 = true := by
 decide +kernel
def cuts48592 : List PrefixCut := [⟨24,95576806,95576862⟩,
⟨64,257225397,257225546⟩]
theorem checked48592 : checkPrefixCuts (2^48) 6372982785 10 Manual.Count131072.C048592.packed 64 cuts48592 = true := by
 decide +kernel
def pointBounds48592 : List (Nat × Nat × Nat) := [(6373031936,111301261808838,111301648728065)]
theorem point_links_checked48592 : (cuts48592.take 1).map (fun c => (6372982785-1+2*2^10*c.k,111301166232032+c.lower,111301553151203+c.upper)) = pointBounds48592 := by
 decide +kernel
def cuts48593 : List PrefixCut := [⟨58,231648457,231648589⟩,
⟨64,255497624,255497770⟩]
theorem checked48593 : checkPrefixCuts (2^48) 6373113857 10 Manual.Count131072.C048593.packed 64 cuts48593 = true := by
 decide +kernel
def pointBounds48593 : List (Nat × Nat × Nat) := [(6373232640,111301655105886,111302042025338)]
theorem point_links_checked48593 : (cuts48593.take 1).map (fun c => (6373113857-1+2*2^10*c.k,111301423457429+c.lower,111301810376749+c.upper)) = pointBounds48593 := by
 decide +kernel
def cuts48594 : List PrefixCut := [⟨64,256861464,256861608⟩]
theorem checked48594 : checkPrefixCuts (2^48) 6373244929 10 Manual.Count131072.C048594.packed 64 cuts48594 = true := by
 decide +kernel
def cuts48595 : List PrefixCut := [⟨28,112838961,112839028⟩,
⟨64,258755241,258755390⟩]
theorem checked48595 : checkPrefixCuts (2^48) 6373376001 10 Manual.Count131072.C048595.packed 64 cuts48595 = true := by
 decide +kernel
def pointBounds48595 : List (Nat × Nat × Nat) := [(6373433344,111302048655478,111302435575155)]
theorem point_links_checked48595 : (cuts48595.take 1).map (fun c => (6373376001-1+2*2^10*c.k,111301935816517+c.lower,111302322736127+c.upper)) = pointBounds48595 := by
 decide +kernel
def cuts48596 : List PrefixCut := [⟨62,247223491,247223638⟩,
⟨64,255570180,255570331⟩]
theorem checked48596 : checkPrefixCuts (2^48) 6373507073 10 Manual.Count131072.C048596.packed 64 cuts48596 = true := by
 decide +kernel
def pointBounds48596 : List (Nat × Nat × Nat) := [(6373634048,111302441795249,111302828715155)]
theorem point_links_checked48596 : (cuts48596.take 1).map (fun c => (6373507073-1+2*2^10*c.k,111302194571758+c.lower,111302581491517+c.upper)) = pointBounds48596 := by
 decide +kernel
def cuts48597 : List PrefixCut := [⟨64,260378574,260378723⟩]
theorem checked48597 : checkPrefixCuts (2^48) 6373638145 10 Manual.Count131072.C048597.packed 64 cuts48597 = true := by
 decide +kernel
def cuts48598 : List PrefixCut := [⟨32,127449297,127449371⟩,
⟨64,254411499,254411643⟩]
theorem checked48598 : checkPrefixCuts (2^48) 6373769217 10 Manual.Count131072.C048598.packed 64 cuts48598 = true := by
 decide +kernel
def pointBounds48598 : List (Nat × Nat × Nat) := [(6373834752,111302837969809,111303224889942)]
theorem point_links_checked48598 : (cuts48598.take 1).map (fun c => (6373769217-1+2*2^10*c.k,111302710520512+c.lower,111303097440571+c.upper)) = pointBounds48598 := by
 decide +kernel
def cuts48599 : List PrefixCut := [⟨64,258115707,258115858⟩]
theorem checked48599 : checkPrefixCuts (2^48) 6373900289 10 Manual.Count131072.C048599.packed 64 cuts48599 = true := by
 decide +kernel
def cuts48600 : List PrefixCut := [⟨2,8699445,8699450⟩,
⟨64,255063438,255063586⟩]
theorem checked48600 : checkPrefixCuts (2^48) 6374031361 10 Manual.Count131072.C048600.packed 64 cuts48600 = true := by
 decide +kernel
def pointBounds48600 : List (Nat × Nat × Nat) := [(6374035456,111303231747163,111303618667522)]
theorem point_links_checked48600 : (cuts48600.take 1).map (fun c => (6374031361-1+2*2^10*c.k,111303223047718+c.lower,111303609968072+c.upper)) = pointBounds48600 := by
 decide +kernel
def cuts48601 : List PrefixCut := [⟨36,146252854,146252938⟩,
⟨64,258149282,258149429⟩]
theorem checked48601 : checkPrefixCuts (2^48) 6374162433 10 Manual.Count131072.C048601.packed 64 cuts48601 = true := by
 decide +kernel
def pointBounds48601 : List (Nat × Nat × Nat) := [(6374236160,111303624364010,111304011284596)]
theorem point_links_checked48601 : (cuts48601.take 1).map (fun c => (6374162433-1+2*2^10*c.k,111303478111156+c.lower,111303865031658+c.upper)) = pointBounds48601 := by
 decide +kernel
def cuts48602 : List PrefixCut := [⟨64,254346409,254346558⟩]
theorem checked48602 : checkPrefixCuts (2^48) 6374293505 10 Manual.Count131072.C048602.packed 64 cuts48602 = true := by
 decide +kernel
def cuts48603 : List PrefixCut := [⟨6,24551218,24551233⟩,
⟨64,256593192,256593340⟩]
theorem checked48603 : checkPrefixCuts (2^48) 6374424577 10 Manual.Count131072.C048603.packed 64 cuts48603 = true := by
 decide +kernel
def pointBounds48603 : List (Nat × Nat × Nat) := [(6374436864,111304015158065,111304402078878)]
theorem point_links_checked48603 : (cuts48603.take 1).map (fun c => (6374424577-1+2*2^10*c.k,111303990606847+c.lower,111304377527645+c.upper)) = pointBounds48603 := by
 decide +kernel
def cuts48604 : List PrefixCut := [⟨40,162625527,162625616⟩,
⟨64,257868430,257868573⟩]
theorem checked48604 : checkPrefixCuts (2^48) 6374555649 10 Manual.Count131072.C048604.packed 64 cuts48604 = true := by
 decide +kernel
def pointBounds48604 : List (Nat × Nat × Nat) := [(6374637568,111304409825566,111304796746601)]
theorem point_links_checked48604 : (cuts48604.take 1).map (fun c => (6374555649-1+2*2^10*c.k,111304247200039+c.lower,111304634120985+c.upper)) = pointBounds48604 := by
 decide +kernel
def cuts48605 : List PrefixCut := [⟨64,255876149,255876293⟩]
theorem checked48605 : checkPrefixCuts (2^48) 6374686721 10 Manual.Count131072.C048605.packed 64 cuts48605 = true := by
 decide +kernel
def cuts48606 : List PrefixCut := [⟨10,40312709,40312730⟩,
⟨64,253707363,253707507⟩]
theorem checked48606 : checkPrefixCuts (2^48) 6374817793 10 Manual.Count131072.C048606.packed 64 cuts48606 = true := by
 decide +kernel
def pointBounds48606 : List (Nat × Nat × Nat) := [(6374838272,111304801257327,111305188178581)]
theorem point_links_checked48606 : (cuts48606.take 1).map (fun c => (6374817793-1+2*2^10*c.k,111304760944618+c.lower,111305147865851+c.upper)) = pointBounds48606 := by
 decide +kernel
def cuts48607 : List PrefixCut := [⟨44,177318310,177318412⟩,
⟨64,259309528,259309677⟩]
theorem checked48607 : checkPrefixCuts (2^48) 6374948865 10 Manual.Count131072.C048607.packed 64 cuts48607 = true := by
 decide +kernel
def pointBounds48607 : List (Nat × Nat × Nat) := [(6375038976,111305191970291,111305578891770)]
theorem point_links_checked48607 : (cuts48607.take 1).map (fun c => (6374948865-1+2*2^10*c.k,111305014651981+c.lower,111305401573358+c.upper)) = pointBounds48607 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000268
