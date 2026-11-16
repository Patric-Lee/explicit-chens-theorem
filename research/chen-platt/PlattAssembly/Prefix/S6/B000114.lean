import PlattAssemblyKernel
import PlattCertificates.Count131072.C053648
import PlattCertificates.Count131072.C053649
import PlattCertificates.Count131072.C053650
import PlattCertificates.Count131072.C053651
import PlattCertificates.Count131072.C053652
import PlattCertificates.Count131072.C053653
import PlattCertificates.Count131072.C053654
import PlattCertificates.Count131072.C053655
import PlattCertificates.Count131072.C053656
import PlattCertificates.Count131072.C053657
import PlattCertificates.Count131072.C053658
import PlattCertificates.Count131072.C053659
import PlattCertificates.Count131072.C053660
import PlattCertificates.Count131072.C053661
import PlattCertificates.Count131072.C053662
import PlattCertificates.Count131072.C053663
import PlattCertificates.Count131072.C053664
import PlattCertificates.Count131072.C053665
import PlattCertificates.Count131072.C053666
import PlattCertificates.Count131072.C053667
import PlattCertificates.Count131072.C053668
import PlattCertificates.Count131072.C053669
import PlattCertificates.Count131072.C053670
import PlattCertificates.Count131072.C053671
import PlattCertificates.Count131072.C053672
import PlattCertificates.Count131072.C053673
import PlattCertificates.Count131072.C053674
import PlattCertificates.Count131072.C053675
import PlattCertificates.Count131072.C053676
import PlattCertificates.Count131072.C053677
import PlattCertificates.Count131072.C053678
import PlattCertificates.Count131072.C053679
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53648 : List PrefixCut := [⟨64,233237258,233237391⟩]
theorem checked53648 : checkPrefixCuts (2^48) 7035682817 10 Manual.Count131072.C053648.packed 64 cuts53648 = true := by
 decide +kernel
def cuts53649 : List PrefixCut := [⟨41,150661765,150661850⟩,
⟨64,232432816,232432948⟩]
theorem checked53649 : checkPrefixCuts (2^48) 7035813889 10 Manual.Count131072.C053649.packed 64 cuts53649 = true := by
 decide +kernel
def pointBounds53649 : List (Nat × Nat × Nat) := [(7035897856,112532283120838,112532670740428)]
theorem point_links_checked53649 : (cuts53649.take 1).map (fun c => (7035813889-1+2*2^10*c.k,112532132459073+c.lower,112532520078578+c.upper)) = pointBounds53649 := by
 decide +kernel
def cuts53650 : List PrefixCut := [⟨64,228868035,228868164⟩]
theorem checked53650 : checkPrefixCuts (2^48) 7035944961 10 Manual.Count131072.C053650.packed 64 cuts53650 = true := by
 decide +kernel
def cuts53651 : List PrefixCut := [⟨21,76208396,76208438⟩,
⟨64,227943690,227943819⟩]
theorem checked53651 : checkPrefixCuts (2^48) 7036076033 10 Manual.Count131072.C053651.packed 64 cuts53651 = true := by
 decide +kernel
def pointBounds53651 : List (Nat × Nat × Nat) := [(7036119040,112532669968320,112533057588128)]
theorem point_links_checked53651 : (cuts53651.take 1).map (fun c => (7036076033-1+2*2^10*c.k,112532593759924+c.lower,112532981379690+c.upper)) = pointBounds53651 := by
 decide +kernel
def cuts53652 : List PrefixCut := [⟨64,230819649,230819784⟩]
theorem checked53652 : checkPrefixCuts (2^48) 7036207105 10 Manual.Count131072.C053652.packed 64 cuts53652 = true := by
 decide +kernel
def cuts53653 : List PrefixCut := [⟨1,3640276,3640278⟩,
⟨64,230975386,230975516⟩]
theorem checked53653 : checkPrefixCuts (2^48) 7036338177 10 Manual.Count131072.C053653.packed 64 cuts53653 = true := by
 decide +kernel
def pointBounds53653 : List (Nat × Nat × Nat) := [(7036340224,112533056163539,112533443783571)]
theorem point_links_checked53653 : (cuts53653.take 1).map (fun c => (7036338177-1+2*2^10*c.k,112533052523263+c.lower,112533440143293+c.upper)) = pointBounds53653 := by
 decide +kernel
def cuts53654 : List PrefixCut := [⟨45,162088232,162088324⟩,
⟨64,231731119,231731249⟩]
theorem checked53654 : checkPrefixCuts (2^48) 7036469249 10 Manual.Count131072.C053654.packed 64 cuts53654 = true := by
 decide +kernel
def pointBounds53654 : List (Nat × Nat × Nat) := [(7036561408,112533445586881,112533833207133)]
theorem point_links_checked53654 : (cuts53654.take 1).map (fun c => (7036469249-1+2*2^10*c.k,112533283498649+c.lower,112533671118809+c.upper)) = pointBounds53654 := by
 decide +kernel
def cuts53655 : List PrefixCut := [⟨64,229486730,229486859⟩]
theorem checked53655 : checkPrefixCuts (2^48) 7036600321 10 Manual.Count131072.C053655.packed 64 cuts53655 = true := by
 decide +kernel
def cuts53656 : List PrefixCut := [⟨25,90721490,90721540⟩,
⟨64,232642496,232642625⟩]
theorem checked53656 : checkPrefixCuts (2^48) 7036731393 10 Manual.Count131072.C053656.packed 64 cuts53656 = true := by
 decide +kernel
def pointBounds53656 : List (Nat × Nat × Nat) := [(7036782592,112533835437988,112534223058457)]
theorem point_links_checked53656 : (cuts53656.take 1).map (fun c => (7036731393-1+2*2^10*c.k,112533744716498+c.lower,112534132336917+c.upper)) = pointBounds53656 := by
 decide +kernel
def cuts53657 : List PrefixCut := [⟨64,225958220,225958354⟩]
theorem checked53657 : checkPrefixCuts (2^48) 7036862465 10 Manual.Count131072.C053657.packed 64 cuts53657 = true := by
 decide +kernel
def cuts53658 : List PrefixCut := [⟨5,17959679,17959689⟩,
⟨64,236033746,236033878⟩]
theorem checked53658 : checkPrefixCuts (2^48) 7036993537 10 Manual.Count131072.C053658.packed 64 cuts53658 = true := by
 decide +kernel
def pointBounds53658 : List (Nat × Nat × Nat) := [(7037003776,112534221276893,112534608897585)]
theorem point_links_checked53658 : (cuts53658.take 1).map (fun c => (7036993537-1+2*2^10*c.k,112534203317214+c.lower,112534590937896+c.upper)) = pointBounds53658 := by
 decide +kernel
def cuts53659 : List PrefixCut := [⟨49,174632493,174632594⟩,
⟨64,229349636,229349767⟩]
theorem checked53659 : checkPrefixCuts (2^48) 7037124609 10 Manual.Count131072.C053659.packed 64 cuts53659 = true := by
 decide +kernel
def pointBounds53659 : List (Nat × Nat × Nat) := [(7037224960,112534613983453,112535001604368)]
theorem point_links_checked53659 : (cuts53659.take 1).map (fun c => (7037124609-1+2*2^10*c.k,112534439350960+c.lower,112534826971774+c.upper)) = pointBounds53659 := by
 decide +kernel
def cuts53660 : List PrefixCut := [⟨64,230305303,230305434⟩]
theorem checked53660 : checkPrefixCuts (2^48) 7037255681 10 Manual.Count131072.C053660.packed 64 cuts53660 = true := by
 decide +kernel
def cuts53661 : List PrefixCut := [⟨29,105071873,105071935⟩,
⟨64,233300767,233300901⟩]
theorem checked53661 : checkPrefixCuts (2^48) 7037386753 10 Manual.Count131072.C053661.packed 64 cuts53661 = true := by
 decide +kernel
def pointBounds53661 : List (Nat × Nat × Nat) := [(7037446144,112535004077772,112535391698910)]
theorem point_links_checked53661 : (cuts53661.take 1).map (fun c => (7037386753-1+2*2^10*c.k,112534899005899+c.lower,112535286626975+c.upper)) = pointBounds53661 := by
 decide +kernel
def cuts53662 : List PrefixCut := [⟨64,229416835,229416967⟩]
theorem checked53662 : checkPrefixCuts (2^48) 7037517825 10 Manual.Count131072.C053662.packed 64 cuts53662 = true := by
 decide +kernel
def cuts53663 : List PrefixCut := [⟨9,31876439,31876458⟩,
⟨64,231012353,231012483⟩]
theorem checked53663 : checkPrefixCuts (2^48) 7037648897 10 Manual.Count131072.C053663.packed 64 cuts53663 = true := by
 decide +kernel
def pointBounds53663 : List (Nat × Nat × Nat) := [(7037667328,112535393599940,112535781221301)]
theorem point_links_checked53663 : (cuts53663.take 1).map (fun c => (7037648897-1+2*2^10*c.k,112535361723501+c.lower,112535749344843+c.upper)) = pointBounds53663 := by
 decide +kernel
def cuts53664 : List PrefixCut := [⟨53,189414104,189414211⟩,
⟨64,229168301,229168431⟩]
theorem checked53664 : checkPrefixCuts (2^48) 7037779969 10 Manual.Count131072.C053664.packed 64 cuts53664 = true := by
 decide +kernel
def pointBounds53664 : List (Nat × Nat × Nat) := [(7037888512,112535782149958,112536169771537)]
theorem point_links_checked53664 : (cuts53664.take 1).map (fun c => (7037779969-1+2*2^10*c.k,112535592735854+c.lower,112535980357326+c.upper)) = pointBounds53664 := by
 decide +kernel
def cuts53665 : List PrefixCut := [⟨64,228404139,228404267⟩]
theorem checked53665 : checkPrefixCuts (2^48) 7037911041 10 Manual.Count131072.C053665.packed 64 cuts53665 = true := by
 decide +kernel
def cuts53666 : List PrefixCut := [⟨33,119419578,119419644⟩,
⟨64,231039449,231039577⟩]
theorem checked53666 : checkPrefixCuts (2^48) 7038042113 10 Manual.Count131072.C053666.packed 64 cuts53666 = true := by
 decide +kernel
def pointBounds53666 : List (Nat × Nat × Nat) := [(7038109696,112536169727872,112536557349668)]
theorem point_links_checked53666 : (cuts53666.take 1).map (fun c => (7038042113-1+2*2^10*c.k,112536050308294+c.lower,112536437930024+c.upper)) = pointBounds53666 := by
 decide +kernel
def cuts53667 : List PrefixCut := [⟨64,229035533,229035667⟩]
theorem checked53667 : checkPrefixCuts (2^48) 7038173185 10 Manual.Count131072.C053667.packed 64 cuts53667 = true := by
 decide +kernel
def cuts53668 : List PrefixCut := [⟨13,48110120,48110147⟩,
⟨64,230870886,230871016⟩]
theorem checked53668 : checkPrefixCuts (2^48) 7038304257 10 Manual.Count131072.C053668.packed 64 cuts53668 = true := by
 decide +kernel
def pointBounds53668 : List (Nat × Nat × Nat) := [(7038330880,112536558493396,112536946115415)]
theorem point_links_checked53668 : (cuts53668.take 1).map (fun c => (7038304257-1+2*2^10*c.k,112536510383276+c.lower,112536898005268+c.upper)) = pointBounds53668 := by
 decide +kernel
def cuts53669 : List PrefixCut := [⟨57,207712144,207712264⟩,
⟨64,233825884,233826019⟩]
theorem checked53669 : checkPrefixCuts (2^48) 7038435329 10 Manual.Count131072.C053669.packed 64 cuts53669 = true := by
 decide +kernel
def pointBounds53669 : List (Nat × Nat × Nat) := [(7038552064,112536948966306,112537336588548)]
theorem point_links_checked53669 : (cuts53669.take 1).map (fun c => (7038435329-1+2*2^10*c.k,112536741254162+c.lower,112537128876284+c.upper)) = pointBounds53669 := by
 decide +kernel
def cuts53670 : List PrefixCut := [⟨64,232301917,232302047⟩]
theorem checked53670 : checkPrefixCuts (2^48) 7038566401 10 Manual.Count131072.C053670.packed 64 cuts53670 = true := by
 decide +kernel
def cuts53671 : List PrefixCut := [⟨37,131645150,131645226⟩,
⟨64,228618576,228618711⟩]
theorem checked53671 : checkPrefixCuts (2^48) 7038697473 10 Manual.Count131072.C053671.packed 64 cuts53671 = true := by
 decide +kernel
def pointBounds53671 : List (Nat × Nat × Nat) := [(7038773248,112537339027113,112537726649576)]
theorem point_links_checked53671 : (cuts53671.take 1).map (fun c => (7038697473-1+2*2^10*c.k,112537207381963+c.lower,112537595004350+c.upper)) = pointBounds53671 := by
 decide +kernel
def cuts53672 : List PrefixCut := [⟨64,233692846,233692979⟩]
theorem checked53672 : checkPrefixCuts (2^48) 7038828545 10 Manual.Count131072.C053672.packed 64 cuts53672 = true := by
 decide +kernel
def cuts53673 : List PrefixCut := [⟨17,61621571,61621605⟩,
⟨64,229449808,229449938⟩]
theorem checked53673 : checkPrefixCuts (2^48) 7038959617 10 Manual.Count131072.C053673.packed 64 cuts53673 = true := by
 decide +kernel
def pointBounds53673 : List (Nat × Nat × Nat) := [(7038994432,112537731314956,112538118937645)]
theorem point_links_checked53673 : (cuts53673.take 1).map (fun c => (7038959617-1+2*2^10*c.k,112537669693385+c.lower,112538057316040+c.upper)) = pointBounds53673 := by
 decide +kernel
def cuts53674 : List PrefixCut := [⟨61,219808755,219808880⟩,
⟨64,230405222,230405353⟩]
theorem checked53674 : checkPrefixCuts (2^48) 7039090689 10 Manual.Count131072.C053674.packed 64 cuts53674 = true := by
 decide +kernel
def pointBounds53674 : List (Nat × Nat × Nat) := [(7039215616,112538118951948,112538506574858)]
theorem point_links_checked53674 : (cuts53674.take 1).map (fun c => (7039090689-1+2*2^10*c.k,112537899143193+c.lower,112538286765978+c.upper)) = pointBounds53674 := by
 decide +kernel
def cuts53675 : List PrefixCut := [⟨64,232920066,232920197⟩]
theorem checked53675 : checkPrefixCuts (2^48) 7039221761 10 Manual.Count131072.C053675.packed 64 cuts53675 = true := by
 decide +kernel
def cuts53676 : List PrefixCut := [⟨41,148866635,148866717⟩,
⟨64,230756513,230756643⟩]
theorem checked53676 : checkPrefixCuts (2^48) 7039352833 10 Manual.Count131072.C053676.packed 64 cuts53676 = true := by
 decide +kernel
def pointBounds53676 : List (Nat × Nat × Nat) := [(7039436800,112538511335116,112538898958245)]
theorem point_links_checked53676 : (cuts53676.take 1).map (fun c => (7039352833-1+2*2^10*c.k,112538362468481+c.lower,112538750091528+c.upper)) = pointBounds53676 := by
 decide +kernel
def cuts53677 : List PrefixCut := [⟨64,229632649,229632782⟩]
theorem checked53677 : checkPrefixCuts (2^48) 7039483905 10 Manual.Count131072.C053677.packed 64 cuts53677 = true := by
 decide +kernel
def cuts53678 : List PrefixCut := [⟨21,75130485,75130526⟩,
⟨64,232107362,232107491⟩]
theorem checked53678 : checkPrefixCuts (2^48) 7039614977 10 Manual.Count131072.C053678.packed 64 cuts53678 = true := by
 decide +kernel
def pointBounds53678 : List (Nat × Nat × Nat) := [(7039657984,112538897988128,112539285611479)]
theorem point_links_checked53678 : (cuts53678.take 1).map (fun c => (7039614977-1+2*2^10*c.k,112538822857643+c.lower,112539210480953+c.upper)) = pointBounds53678 := by
 decide +kernel
def cuts53679 : List PrefixCut := [⟨64,232422909,232423038⟩]
theorem checked53679 : checkPrefixCuts (2^48) 7039746049 10 Manual.Count131072.C053679.packed 64 cuts53679 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000114
