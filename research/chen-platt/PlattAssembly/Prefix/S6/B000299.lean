import PlattAssemblyKernel
import PlattCertificates.Count131072.C059568
import PlattCertificates.Count131072.C059569
import PlattCertificates.Count131072.C059570
import PlattCertificates.Count131072.C059571
import PlattCertificates.Count131072.C059572
import PlattCertificates.Count131072.C059573
import PlattCertificates.Count131072.C059574
import PlattCertificates.Count131072.C059575
import PlattCertificates.Count131072.C059576
import PlattCertificates.Count131072.C059577
import PlattCertificates.Count131072.C059578
import PlattCertificates.Count131072.C059579
import PlattCertificates.Count131072.C059580
import PlattCertificates.Count131072.C059581
import PlattCertificates.Count131072.C059582
import PlattCertificates.Count131072.C059583
import PlattCertificates.Count131072.C059584
import PlattCertificates.Count131072.C059585
import PlattCertificates.Count131072.C059586
import PlattCertificates.Count131072.C059587
import PlattCertificates.Count131072.C059588
import PlattCertificates.Count131072.C059589
import PlattCertificates.Count131072.C059590
import PlattCertificates.Count131072.C059591
import PlattCertificates.Count131072.C059592
import PlattCertificates.Count131072.C059593
import PlattCertificates.Count131072.C059594
import PlattCertificates.Count131072.C059595
import PlattCertificates.Count131072.C059596
import PlattCertificates.Count131072.C059597
import PlattCertificates.Count131072.C059598
import PlattCertificates.Count131072.C059599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000299
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59568 : List PrefixCut := [⟨64,206105915,206106024⟩]
theorem checked59568 : checkPrefixCuts (2^48) 7811629057 10 Manual.Count131072.C059568.packed 64 cuts59568 = true := by
 decide +kernel
def cuts59569 : List PrefixCut := [⟨23,73793721,73793764⟩,
⟨64,203508159,203508278⟩]
theorem checked59569 : checkPrefixCuts (2^48) 7811760129 10 Manual.Count131072.C059569.packed 64 cuts59569 = true := by
 decide +kernel
def pointBounds59569 : List (Nat × Nat × Nat) := [(7811807232,113827813958469,113828202314919)]
theorem point_links_checked59569 : (cuts59569.take 1).map (fun c => (7811760129-1+2*2^10*c.k,113827740164748+c.lower,113828128521155+c.upper)) = pointBounds59569 := by
 decide +kernel
def cuts59570 : List PrefixCut := [⟨64,208404990,208405105⟩]
theorem checked59570 : checkPrefixCuts (2^48) 7811891201 10 Manual.Count131072.C059570.packed 64 cuts59570 = true := by
 decide +kernel
def cuts59571 : List PrefixCut := [⟨15,47236537,47236562⟩,
⟨64,205735224,205735340⟩]
theorem checked59571 : checkPrefixCuts (2^48) 7812022273 10 Manual.Count131072.C059571.packed 64 cuts59571 = true := by
 decide +kernel
def pointBounds59571 : List (Nat × Nat × Nat) := [(7812052992,113828199314434,113828587671100)]
theorem point_links_checked59571 : (cuts59571.take 1).map (fun c => (7812022273-1+2*2^10*c.k,113828152077897+c.lower,113828540434538+c.upper)) = pointBounds59571 := by
 decide +kernel
def cuts59572 : List PrefixCut := [⟨64,207569311,207569428⟩]
theorem checked59572 : checkPrefixCuts (2^48) 7812153345 10 Manual.Count131072.C059572.packed 64 cuts59572 = true := by
 decide +kernel
def cuts59573 : List PrefixCut := [⟨7,21906086,21906098⟩,
⟨64,203890798,203890914⟩]
theorem checked59573 : checkPrefixCuts (2^48) 7812284417 10 Manual.Count131072.C059573.packed 64 cuts59573 = true := by
 decide +kernel
def pointBounds59573 : List (Nat × Nat × Nat) := [(7812298752,113828587288518,113828975645404)]
theorem point_links_checked59573 : (cuts59573.take 1).map (fun c => (7812284417-1+2*2^10*c.k,113828565382432+c.lower,113828953739306+c.upper)) = pointBounds59573 := by
 decide +kernel
def cuts59574 : List PrefixCut := [⟨63,205076384,205076497⟩,
⟨64,208246899,208247014⟩]
theorem checked59574 : checkPrefixCuts (2^48) 7812415489 10 Manual.Count131072.C059574.packed 64 cuts59574 = true := by
 decide +kernel
def pointBounds59574 : List (Nat × Nat × Nat) := [(7812544512,113828974349614,113829362706717)]
theorem point_links_checked59574 : (cuts59574.take 1).map (fun c => (7812415489-1+2*2^10*c.k,113828769273230+c.lower,113829157630220+c.upper)) = pointBounds59574 := by
 decide +kernel
def cuts59575 : List PrefixCut := [⟨64,209144120,209144237⟩]
theorem checked59575 : checkPrefixCuts (2^48) 7812546561 10 Manual.Count131072.C059575.packed 64 cuts59575 = true := by
 decide +kernel
def cuts59576 : List PrefixCut := [⟨55,177940847,177940950⟩,
⟨64,207303183,207303303⟩]
theorem checked59576 : checkPrefixCuts (2^48) 7812677633 10 Manual.Count131072.C059576.packed 64 cuts59576 = true := by
 decide +kernel
def pointBounds59576 : List (Nat × Nat × Nat) := [(7812790272,113829364605096,113829752962421)]
theorem point_links_checked59576 : (cuts59576.take 1).map (fun c => (7812677633-1+2*2^10*c.k,113829186664249+c.lower,113829575021471+c.upper)) = pointBounds59576 := by
 decide +kernel
def cuts59577 : List PrefixCut := [⟨64,206831359,206831473⟩]
theorem checked59577 : checkPrefixCuts (2^48) 7812808705 10 Manual.Count131072.C059577.packed 64 cuts59577 = true := by
 decide +kernel
def cuts59578 : List PrefixCut := [⟨47,152536360,152536451⟩,
⟨64,208052787,208052911⟩]
theorem checked59578 : checkPrefixCuts (2^48) 7812939777 10 Manual.Count131072.C059578.packed 64 cuts59578 = true := by
 decide +kernel
def pointBounds59578 : List (Nat × Nat × Nat) := [(7813036032,113829753335151,113830141692698)]
theorem point_links_checked59578 : (cuts59578.take 1).map (fun c => (7812939777-1+2*2^10*c.k,113829600798791+c.lower,113829989156247+c.upper)) = pointBounds59578 := by
 decide +kernel
def cuts59579 : List PrefixCut := [⟨64,205275297,205275416⟩]
theorem checked59579 : checkPrefixCuts (2^48) 7813070849 10 Manual.Count131072.C059579.packed 64 cuts59579 = true := by
 decide +kernel
def cuts59580 : List PrefixCut := [⟨39,128430427,128430503⟩,
⟨64,208009792,208009916⟩]
theorem checked59580 : checkPrefixCuts (2^48) 7813201921 10 Manual.Count131072.C059580.packed 64 cuts59580 = true := by
 decide +kernel
def pointBounds59580 : List (Nat × Nat × Nat) := [(7813281792,113830142557302,113830530915077)]
theorem point_links_checked59580 : (cuts59580.take 1).map (fun c => (7813201921-1+2*2^10*c.k,113830014126875+c.lower,113830402484574+c.upper)) = pointBounds59580 := by
 decide +kernel
def cuts59581 : List PrefixCut := [⟨64,209123049,209123166⟩]
theorem checked59581 : checkPrefixCuts (2^48) 7813332993 10 Manual.Count131072.C059581.packed 64 cuts59581 = true := by
 decide +kernel
def cuts59582 : List PrefixCut := [⟨31,100471478,100471537⟩,
⟨64,207570508,207570629⟩]
theorem checked59582 : checkPrefixCuts (2^48) 7813464065 10 Manual.Count131072.C059582.packed 64 cuts59582 = true := by
 decide +kernel
def pointBounds59582 : List (Nat × Nat × Nat) := [(7813527552,113830531731194,113830920089193)]
theorem point_links_checked59582 : (cuts59582.take 1).map (fun c => (7813464065-1+2*2^10*c.k,113830431259716+c.lower,113830819617656+c.upper)) = pointBounds59582 := by
 decide +kernel
def cuts59583 : List PrefixCut := [⟨64,208647731,208647850⟩]
theorem checked59583 : checkPrefixCuts (2^48) 7813595137 10 Manual.Count131072.C059583.packed 64 cuts59583 = true := by
 decide +kernel
def cuts59584 : List PrefixCut := [⟨23,74099363,74099405⟩,
⟨64,206374797,206374916⟩]
theorem checked59584 : checkPrefixCuts (2^48) 7813726209 10 Manual.Count131072.C059584.packed 64 cuts59584 = true := by
 decide +kernel
def pointBounds59584 : List (Nat × Nat × Nat) := [(7813773312,113830921577318,113831309935540)]
theorem point_links_checked59584 : (cuts59584.take 1).map (fun c => (7813726209-1+2*2^10*c.k,113830847477955+c.lower,113831235836135+c.upper)) = pointBounds59584 := by
 decide +kernel
def cuts59585 : List PrefixCut := [⟨64,205903046,205903163⟩]
theorem checked59585 : checkPrefixCuts (2^48) 7813857281 10 Manual.Count131072.C059585.packed 64 cuts59585 = true := by
 decide +kernel
def cuts59586 : List PrefixCut := [⟨15,50142420,50142448⟩,
⟨64,212491543,212491665⟩]
theorem checked59586 : checkPrefixCuts (2^48) 7813988353 10 Manual.Count131072.C059586.packed 64 cuts59586 = true := by
 decide +kernel
def pointBounds59586 : List (Nat × Nat × Nat) := [(7814019072,113831309898218,113831698256662)]
theorem point_links_checked59586 : (cuts59586.take 1).map (fun c => (7813988353-1+2*2^10*c.k,113831259755798+c.lower,113831648114214+c.upper)) = pointBounds59586 := by
 decide +kernel
def cuts59587 : List PrefixCut := [⟨64,207228918,207229040⟩]
theorem checked59587 : checkPrefixCuts (2^48) 7814119425 10 Manual.Count131072.C059587.packed 64 cuts59587 = true := by
 decide +kernel
def cuts59588 : List PrefixCut := [⟨7,22584968,22584981⟩,
⟨64,206577086,206577201⟩]
theorem checked59588 : checkPrefixCuts (2^48) 7814250497 10 Manual.Count131072.C059588.packed 64 cuts59588 = true := by
 decide +kernel
def pointBounds59588 : List (Nat × Nat × Nat) := [(7814264832,113831702061227,113832090419900)]
theorem point_links_checked59588 : (cuts59588.take 1).map (fun c => (7814250497-1+2*2^10*c.k,113831679476259+c.lower,113832067834919+c.upper)) = pointBounds59588 := by
 decide +kernel
def cuts59589 : List PrefixCut := [⟨63,205997304,205997428⟩,
⟨64,209094982,209095108⟩]
theorem checked59589 : checkPrefixCuts (2^48) 7814381569 10 Manual.Count131072.C059589.packed 64 cuts59589 = true := by
 decide +kernel
def pointBounds59589 : List (Nat × Nat × Nat) := [(7814510592,113832092050649,113832480409548)]
theorem point_links_checked59589 : (cuts59589.take 1).map (fun c => (7814381569-1+2*2^10*c.k,113831886053345+c.lower,113832274412120+c.upper)) = pointBounds59589 := by
 decide +kernel
def cuts59590 : List PrefixCut := [⟨64,207794790,207794907⟩]
theorem checked59590 : checkPrefixCuts (2^48) 7814512641 10 Manual.Count131072.C059590.packed 64 cuts59590 = true := by
 decide +kernel
def cuts59591 : List PrefixCut := [⟨55,177319779,177319881⟩,
⟨64,205486123,205486240⟩]
theorem checked59591 : checkPrefixCuts (2^48) 7814643713 10 Manual.Count131072.C059591.packed 64 cuts59591 = true := by
 decide +kernel
def pointBounds59591 : List (Nat × Nat × Nat) := [(7814756352,113832480262896,113832868622016)]
theorem point_links_checked59591 : (cuts59591.take 1).map (fun c => (7814643713-1+2*2^10*c.k,113832302943117+c.lower,113832691302135+c.upper)) = pointBounds59591 := by
 decide +kernel
def cuts59592 : List PrefixCut := [⟨64,208003944,208004063⟩]
theorem checked59592 : checkPrefixCuts (2^48) 7814774785 10 Manual.Count131072.C059592.packed 64 cuts59592 = true := by
 decide +kernel
def cuts59593 : List PrefixCut := [⟨47,153578515,153578602⟩,
⟨64,210233525,210233645⟩]
theorem checked59593 : checkPrefixCuts (2^48) 7814905857 10 Manual.Count131072.C059593.packed 64 cuts59593 = true := by
 decide +kernel
def pointBounds59593 : List (Nat × Nat × Nat) := [(7815002112,113832870011699,113833258371040)]
theorem point_links_checked59593 : (cuts59593.take 1).map (fun c => (7814905857-1+2*2^10*c.k,113832716433184+c.lower,113833104792438+c.upper)) = pointBounds59593 := by
 decide +kernel
def cuts59594 : List PrefixCut := [⟨64,207168577,207168695⟩]
theorem checked59594 : checkPrefixCuts (2^48) 7815036929 10 Manual.Count131072.C059594.packed 64 cuts59594 = true := by
 decide +kernel
def cuts59595 : List PrefixCut := [⟨39,124004138,124004210⟩,
⟨64,205220217,205220335⟩]
theorem checked59595 : checkPrefixCuts (2^48) 7815168001 10 Manual.Count131072.C059595.packed 64 cuts59595 = true := by
 decide +kernel
def pointBounds59595 : List (Nat × Nat × Nat) := [(7815247872,113833257839424,113833646198988)]
theorem point_links_checked59595 : (cuts59595.take 1).map (fun c => (7815168001-1+2*2^10*c.k,113833133835286+c.lower,113833522194778+c.upper)) = pointBounds59595 := by
 decide +kernel
def cuts59596 : List PrefixCut := [⟨64,203560071,203560192⟩]
theorem checked59596 : checkPrefixCuts (2^48) 7815299073 10 Manual.Count131072.C059596.packed 64 cuts59596 = true := by
 decide +kernel
def cuts59597 : List PrefixCut := [⟨31,100986436,100986492⟩,
⟨64,208310621,208310740⟩]
theorem checked59597 : checkPrefixCuts (2^48) 7815430145 10 Manual.Count131072.C059597.packed 64 cuts59597 = true := by
 decide +kernel
def pointBounds59597 : List (Nat × Nat × Nat) := [(7815493632,113833643602010,113834031961797)]
theorem point_links_checked59597 : (cuts59597.take 1).map (fun c => (7815430145-1+2*2^10*c.k,113833542615574+c.lower,113833930975305+c.upper)) = pointBounds59597 := by
 decide +kernel
def cuts59598 : List PrefixCut := [⟨64,207874955,207875071⟩]
theorem checked59598 : checkPrefixCuts (2^48) 7815561217 10 Manual.Count131072.C059598.packed 64 cuts59598 = true := by
 decide +kernel
def cuts59599 : List PrefixCut := [⟨23,73576522,73576562⟩,
⟨64,206322874,206322986⟩]
theorem checked59599 : checkPrefixCuts (2^48) 7815692289 10 Manual.Count131072.C059599.packed 64 cuts59599 = true := by
 decide +kernel
def pointBounds59599 : List (Nat × Nat × Nat) := [(7815739392,113834032377672,113834420737678)]
theorem point_links_checked59599 : (cuts59599.take 1).map (fun c => (7815692289-1+2*2^10*c.k,113833958801150+c.lower,113834347161116+c.upper)) = pointBounds59599 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000299
