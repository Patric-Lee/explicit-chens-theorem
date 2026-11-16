import PlattAssemblyKernel
import PlattCertificates.Count131072.C060448
import PlattCertificates.Count131072.C060449
import PlattCertificates.Count131072.C060450
import PlattCertificates.Count131072.C060451
import PlattCertificates.Count131072.C060452
import PlattCertificates.Count131072.C060453
import PlattCertificates.Count131072.C060454
import PlattCertificates.Count131072.C060455
import PlattCertificates.Count131072.C060456
import PlattCertificates.Count131072.C060457
import PlattCertificates.Count131072.C060458
import PlattCertificates.Count131072.C060459
import PlattCertificates.Count131072.C060460
import PlattCertificates.Count131072.C060461
import PlattCertificates.Count131072.C060462
import PlattCertificates.Count131072.C060463
import PlattCertificates.Count131072.C060464
import PlattCertificates.Count131072.C060465
import PlattCertificates.Count131072.C060466
import PlattCertificates.Count131072.C060467
import PlattCertificates.Count131072.C060468
import PlattCertificates.Count131072.C060469
import PlattCertificates.Count131072.C060470
import PlattCertificates.Count131072.C060471
import PlattCertificates.Count131072.C060472
import PlattCertificates.Count131072.C060473
import PlattCertificates.Count131072.C060474
import PlattCertificates.Count131072.C060475
import PlattCertificates.Count131072.C060476
import PlattCertificates.Count131072.C060477
import PlattCertificates.Count131072.C060478
import PlattCertificates.Count131072.C060479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60448 : List PrefixCut := [⟨60,190998735,190998845⟩,
⟨64,203746082,203746200⟩]
theorem checked60448 : checkPrefixCuts (2^48) 7926972417 10 Manual.Count131072.C060448.packed 64 cuts60448 = true := by
 decide +kernel
def pointBounds60448 : List (Nat × Nat × Nat) := [(7927095296,114008809071311,114009197531108)]
theorem point_links_checked60448 : (cuts60448.take 1).map (fun c => (7926972417-1+2*2^10*c.k,114008618072576+c.lower,114009006532263+c.upper)) = pointBounds60448 := by
 decide +kernel
def cuts60449 : List PrefixCut := [⟨64,205695645,205695761⟩]
theorem checked60449 : checkPrefixCuts (2^48) 7927103489 10 Manual.Count131072.C060449.packed 64 cuts60449 = true := by
 decide +kernel
def cuts60450 : List PrefixCut := [⟨53,171570215,171570313⟩,
⟨64,207148019,207148134⟩]
theorem checked60450 : checkPrefixCuts (2^48) 7927234561 10 Manual.Count131072.C060450.packed 64 cuts60450 = true := by
 decide +kernel
def pointBounds60450 : List (Nat × Nat × Nat) := [(7927343104,114009199084518,114009587544537)]
theorem point_links_checked60450 : (cuts60450.take 1).map (fun c => (7927234561-1+2*2^10*c.k,114009027514303+c.lower,114009415974224+c.upper)) = pointBounds60450 := by
 decide +kernel
def cuts60451 : List PrefixCut := [⟨64,203593962,203594075⟩]
theorem checked60451 : checkPrefixCuts (2^48) 7927365633 10 Manual.Count131072.C060451.packed 64 cuts60451 = true := by
 decide +kernel
def cuts60452 : List PrefixCut := [⟨46,145148295,145148378⟩,
⟨64,203129017,203129133⟩]
theorem checked60452 : checkPrefixCuts (2^48) 7927496705 10 Manual.Count131072.C060452.packed 64 cuts60452 = true := by
 decide +kernel
def pointBounds60452 : List (Nat × Nat × Nat) := [(7927590912,114009583404579,114009971864811)]
theorem point_links_checked60452 : (cuts60452.take 1).map (fun c => (7927496705-1+2*2^10*c.k,114009438256284+c.lower,114009826716433+c.upper)) = pointBounds60452 := by
 decide +kernel
def cuts60453 : List PrefixCut := [⟨64,203835749,203835870⟩]
theorem checked60453 : checkPrefixCuts (2^48) 7927627777 10 Manual.Count131072.C060453.packed 64 cuts60453 = true := by
 decide +kernel
def cuts60454 : List PrefixCut := [⟨39,126077527,126077601⟩,
⟨64,205146057,205146177⟩]
theorem checked60454 : checkPrefixCuts (2^48) 7927758849 10 Manual.Count131072.C060454.packed 64 cuts60454 = true := by
 decide +kernel
def pointBounds60454 : List (Nat × Nat × Nat) := [(7927838720,114009971298577,114010359759037)]
theorem point_links_checked60454 : (cuts60454.take 1).map (fun c => (7927758849-1+2*2^10*c.k,114009845221050+c.lower,114010233681436+c.upper)) = pointBounds60454 := by
 decide +kernel
def cuts60455 : List PrefixCut := [⟨64,203509488,203509603⟩]
theorem checked60455 : checkPrefixCuts (2^48) 7927889921 10 Manual.Count131072.C060455.packed 64 cuts60455 = true := by
 decide +kernel
def cuts60456 : List PrefixCut := [⟨32,101220922,101220983⟩,
⟨64,203080071,203080189⟩]
theorem checked60456 : checkPrefixCuts (2^48) 7928020993 10 Manual.Count131072.C060456.packed 64 cuts60456 = true := by
 decide +kernel
def pointBounds60456 : List (Nat × Nat × Nat) := [(7928086528,114010355097517,114010743558199)]
theorem point_links_checked60456 : (cuts60456.take 1).map (fun c => (7928020993-1+2*2^10*c.k,114010253876595+c.lower,114010642337216+c.upper)) = pointBounds60456 := by
 decide +kernel
def cuts60457 : List PrefixCut := [⟨64,206023456,206023574⟩]
theorem checked60457 : checkPrefixCuts (2^48) 7928152065 10 Manual.Count131072.C060457.packed 64 cuts60457 = true := by
 decide +kernel
def cuts60458 : List PrefixCut := [⟨25,79987165,79987210⟩,
⟨64,200836725,200836840⟩]
theorem checked60458 : checkPrefixCuts (2^48) 7928283137 10 Manual.Count131072.C060458.packed 64 cuts60458 = true := by
 decide +kernel
def pointBounds60458 : List (Nat × Nat × Nat) := [(7928334336,114010742967287,114011131428189)]
theorem point_links_checked60458 : (cuts60458.take 1).map (fun c => (7928283137-1+2*2^10*c.k,114010662980122+c.lower,114011051440979+c.upper)) = pointBounds60458 := by
 decide +kernel
def cuts60459 : List PrefixCut := [⟨64,205235604,205235721⟩]
theorem checked60459 : checkPrefixCuts (2^48) 7928414209 10 Manual.Count131072.C060459.packed 64 cuts60459 = true := by
 decide +kernel
def cuts60460 : List PrefixCut := [⟨18,57796236,57796268⟩,
⟨64,204451197,204451314⟩]
theorem checked60460 : checkPrefixCuts (2^48) 7928545281 10 Manual.Count131072.C060460.packed 64 cuts60460 = true := by
 decide +kernel
def pointBounds60460 : List (Nat × Nat × Nat) := [(7928582144,114011126848687,114011515309808)]
theorem point_links_checked60460 : (cuts60460.take 1).map (fun c => (7928545281-1+2*2^10*c.k,114011069052451+c.lower,114011457513540+c.upper)) = pointBounds60460 := by
 decide +kernel
def cuts60461 : List PrefixCut := [⟨64,200755744,200755857⟩]
theorem checked60461 : checkPrefixCuts (2^48) 7928676353 10 Manual.Count131072.C060461.packed 64 cuts60461 = true := by
 decide +kernel
def cuts60462 : List PrefixCut := [⟨11,35216230,35216250⟩,
⟨64,207213436,207213549⟩]
theorem checked60462 : checkPrefixCuts (2^48) 7928807425 10 Manual.Count131072.C060462.packed 64 cuts60462 = true := by
 decide +kernel
def pointBounds60462 : List (Nat × Nat × Nat) := [(7928829952,114011509475622,114011897936961)]
theorem point_links_checked60462 : (cuts60462.take 1).map (fun c => (7928807425-1+2*2^10*c.k,114011474259392+c.lower,114011862720711+c.upper)) = pointBounds60462 := by
 decide +kernel
def cuts60463 : List PrefixCut := [⟨64,204015085,204015192⟩]
theorem checked60463 : checkPrefixCuts (2^48) 7928938497 10 Manual.Count131072.C060463.packed 64 cuts60463 = true := by
 decide +kernel
def cuts60464 : List PrefixCut := [⟨4,12815171,12815178⟩,
⟨64,203656706,203656824⟩]
theorem checked60464 : checkPrefixCuts (2^48) 7929069569 10 Manual.Count131072.C060464.packed 64 cuts60464 = true := by
 decide +kernel
def pointBounds60464 : List (Nat × Nat × Nat) := [(7929077760,114011898303084,114012286764630)]
theorem point_links_checked60464 : (cuts60464.take 1).map (fun c => (7929069569-1+2*2^10*c.k,114011885487913+c.lower,114012273949452+c.upper)) = pointBounds60464 := by
 decide +kernel
def cuts60465 : List PrefixCut := [⟨61,196518249,196518358⟩,
⟨64,205534727,205534841⟩]
theorem checked60465 : checkPrefixCuts (2^48) 7929200641 10 Manual.Count131072.C060465.packed 64 cuts60465 = true := by
 decide +kernel
def pointBounds60465 : List (Nat × Nat × Nat) := [(7929325568,114012285662868,114012674124634)]
theorem point_links_checked60465 : (cuts60465.take 1).map (fun c => (7929200641-1+2*2^10*c.k,114012089144619+c.lower,114012477606276+c.upper)) = pointBounds60465 := by
 decide +kernel
def cuts60466 : List PrefixCut := [⟨64,202478541,202478659⟩]
theorem checked60466 : checkPrefixCuts (2^48) 7929331713 10 Manual.Count131072.C060466.packed 64 cuts60466 = true := by
 decide +kernel
def cuts60467 : List PrefixCut := [⟨54,171557484,171557582⟩,
⟨64,203575602,203575717⟩]
theorem checked60467 : checkPrefixCuts (2^48) 7929462785 10 Manual.Count131072.C060467.packed 64 cuts60467 = true := by
 decide +kernel
def pointBounds60467 : List (Nat × Nat × Nat) := [(7929573376,114012668715371,114013057177358)]
theorem point_links_checked60467 : (cuts60467.take 1).map (fun c => (7929462785-1+2*2^10*c.k,114012497157887+c.lower,114012885619776+c.upper)) = pointBounds60467 := by
 decide +kernel
def cuts60468 : List PrefixCut := [⟨64,205702016,205702127⟩]
theorem checked60468 : checkPrefixCuts (2^48) 7929593857 10 Manual.Count131072.C060468.packed 64 cuts60468 = true := by
 decide +kernel
def cuts60469 : List PrefixCut := [⟨47,148231121,148231207⟩,
⟨64,203355889,203356007⟩]
theorem checked60469 : checkPrefixCuts (2^48) 7929724929 10 Manual.Count131072.C060469.packed 64 cuts60469 = true := by
 decide +kernel
def pointBounds60469 : List (Nat × Nat × Nat) := [(7929821184,114013054666626,114013443128827)]
theorem point_links_checked60469 : (cuts60469.take 1).map (fun c => (7929724929-1+2*2^10*c.k,114012906435505+c.lower,114013294897620+c.upper)) = pointBounds60469 := by
 decide +kernel
def cuts60470 : List PrefixCut := [⟨64,206263164,206263287⟩]
theorem checked60470 : checkPrefixCuts (2^48) 7929856001 10 Manual.Count131072.C060470.packed 64 cuts60470 = true := by
 decide +kernel
def cuts60471 : List PrefixCut := [⟨40,128704207,128704280⟩,
⟨64,206614684,206614803⟩]
theorem checked60471 : checkPrefixCuts (2^48) 7929987073 10 Manual.Count131072.C060471.packed 64 cuts60471 = true := by
 decide +kernel
def pointBounds60471 : List (Nat × Nat × Nat) := [(7930068992,114013444758765,114013833221194)]
theorem point_links_checked60471 : (cuts60471.take 1).map (fun c => (7929987073-1+2*2^10*c.k,114013316054558+c.lower,114013704516914+c.upper)) = pointBounds60471 := by
 decide +kernel
def cuts60472 : List PrefixCut := [⟨64,202884405,202884523⟩]
theorem checked60472 : checkPrefixCuts (2^48) 7930118145 10 Manual.Count131072.C060472.packed 64 cuts60472 = true := by
 decide +kernel
def cuts60473 : List PrefixCut := [⟨34,108646131,108646192⟩,
⟨64,203165000,203165114⟩]
theorem checked60473 : checkPrefixCuts (2^48) 7930249217 10 Manual.Count131072.C060473.packed 64 cuts60473 = true := by
 decide +kernel
def pointBounds60473 : List (Nat × Nat × Nat) := [(7930318848,114013834199778,114014222662432)]
theorem point_links_checked60473 : (cuts60473.take 1).map (fun c => (7930249217-1+2*2^10*c.k,114013725553647+c.lower,114014114016240+c.upper)) = pointBounds60473 := by
 decide +kernel
def cuts60474 : List PrefixCut := [⟨64,201351476,201351596⟩]
theorem checked60474 : checkPrefixCuts (2^48) 7930380289 10 Manual.Count131072.C060474.packed 64 cuts60474 = true := by
 decide +kernel
def cuts60475 : List PrefixCut := [⟨28,90044539,90044592⟩,
⟨64,203690660,203690779⟩]
theorem checked60475 : checkPrefixCuts (2^48) 7930511361 10 Manual.Count131072.C060475.packed 64 cuts60475 = true := by
 decide +kernel
def pointBounds60475 : List (Nat × Nat × Nat) := [(7930568704,114014220114662,114014608577542)]
theorem point_links_checked60475 : (cuts60475.take 1).map (fun c => (7930511361-1+2*2^10*c.k,114014130070123+c.lower,114014518532950+c.upper)) = pointBounds60475 := by
 decide +kernel
def cuts60476 : List PrefixCut := [⟨64,201557779,201557894⟩]
theorem checked60476 : checkPrefixCuts (2^48) 7930642433 10 Manual.Count131072.C060476.packed 64 cuts60476 = true := by
 decide +kernel
def cuts60477 : List PrefixCut := [⟨22,69705066,69705109⟩,
⟨64,206274767,206274887⟩]
theorem checked60477 : checkPrefixCuts (2^48) 7930773505 10 Manual.Count131072.C060477.packed 64 cuts60477 = true := by
 decide +kernel
def pointBounds60477 : List (Nat × Nat × Nat) := [(7930818560,114014605023628,114014993486732)]
theorem point_links_checked60477 : (cuts60477.take 1).map (fun c => (7930773505-1+2*2^10*c.k,114014535318562+c.lower,114014923781623+c.upper)) = pointBounds60477 := by
 decide +kernel
def cuts60478 : List PrefixCut := [⟨64,207194129,207194250⟩]
theorem checked60478 : checkPrefixCuts (2^48) 7930904577 10 Manual.Count131072.C060478.packed 64 cuts60478 = true := by
 decide +kernel
def cuts60479 : List PrefixCut := [⟨16,49402405,49402435⟩,
⟨64,200766996,200767113⟩]
theorem checked60479 : checkPrefixCuts (2^48) 7931035649 10 Manual.Count131072.C060479.packed 64 cuts60479 = true := by
 decide +kernel
def pointBounds60479 : List (Nat × Nat × Nat) := [(7931068416,114014998189863,114015386653195)]
theorem point_links_checked60479 : (cuts60479.take 1).map (fun c => (7931035649-1+2*2^10*c.k,114014948787458+c.lower,114015337250760+c.upper)) = pointBounds60479 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000014
