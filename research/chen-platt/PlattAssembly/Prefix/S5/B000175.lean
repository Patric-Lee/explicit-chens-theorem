import PlattAssemblyKernel
import PlattCertificates.Count131072.C045600
import PlattCertificates.Count131072.C045601
import PlattCertificates.Count131072.C045602
import PlattCertificates.Count131072.C045603
import PlattCertificates.Count131072.C045604
import PlattCertificates.Count131072.C045605
import PlattCertificates.Count131072.C045606
import PlattCertificates.Count131072.C045607
import PlattCertificates.Count131072.C045608
import PlattCertificates.Count131072.C045609
import PlattCertificates.Count131072.C045610
import PlattCertificates.Count131072.C045611
import PlattCertificates.Count131072.C045612
import PlattCertificates.Count131072.C045613
import PlattCertificates.Count131072.C045614
import PlattCertificates.Count131072.C045615
import PlattCertificates.Count131072.C045616
import PlattCertificates.Count131072.C045617
import PlattCertificates.Count131072.C045618
import PlattCertificates.Count131072.C045619
import PlattCertificates.Count131072.C045620
import PlattCertificates.Count131072.C045621
import PlattCertificates.Count131072.C045622
import PlattCertificates.Count131072.C045623
import PlattCertificates.Count131072.C045624
import PlattCertificates.Count131072.C045625
import PlattCertificates.Count131072.C045626
import PlattCertificates.Count131072.C045627
import PlattCertificates.Count131072.C045628
import PlattCertificates.Count131072.C045629
import PlattCertificates.Count131072.C045630
import PlattCertificates.Count131072.C045631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45600 : List PrefixCut := [⟨64,275597700,275597859⟩]
theorem checked45600 : checkPrefixCuts (2^48) 5980815361 10 Manual.Count131072.C045600.packed 64 cuts45600 = true := by
 decide +kernel
def cuts45601 : List PrefixCut := [⟨22,92805784,92805835⟩,
⟨64,271873792,271873945⟩]
theorem checked45601 : checkPrefixCuts (2^48) 5980946433 10 Manual.Count131072.C045601.packed 64 cuts45601 = true := by
 decide +kernel
def pointBounds45601 : List (Nat × Nat × Nat) := [(5980991488,110508543478227,110508929943179)]
theorem point_links_checked45601 : (cuts45601.take 1).map (fun c => (5980946433-1+2*2^10*c.k,110508450672443+c.lower,110508837137344+c.upper)) = pointBounds45601 := by
 decide +kernel
def cuts45602 : List PrefixCut := [⟨50,214595848,214595973⟩,
⟨64,273985544,273985705⟩]
theorem checked45602 : checkPrefixCuts (2^48) 5981077505 10 Manual.Count131072.C045602.packed 64 cuts45602 = true := by
 decide +kernel
def pointBounds45602 : List (Nat × Nat × Nat) := [(5981179904,110508937142083,110509323607262)]
theorem point_links_checked45602 : (cuts45602.take 1).map (fun c => (5981077505-1+2*2^10*c.k,110508722546235+c.lower,110509109011289+c.upper)) = pointBounds45602 := by
 decide +kernel
def cuts45603 : List PrefixCut := [⟨64,278685508,278685663⟩]
theorem checked45603 : checkPrefixCuts (2^48) 5981208577 10 Manual.Count131072.C045603.packed 64 cuts45603 = true := by
 decide +kernel
def cuts45604 : List PrefixCut := [⟨14,59341052,59341086⟩,
⟨64,275008822,275008983⟩]
theorem checked45604 : checkPrefixCuts (2^48) 5981339649 10 Manual.Count131072.C045604.packed 64 cuts45604 = true := by
 decide +kernel
def pointBounds45604 : List (Nat × Nat × Nat) := [(5981368320,110509334558339,110509721023743)]
theorem point_links_checked45604 : (cuts45604.take 1).map (fun c => (5981339649-1+2*2^10*c.k,110509275217287+c.lower,110509661682657+c.upper)) = pointBounds45604 := by
 decide +kernel
def cuts45605 : List PrefixCut := [⟨42,178018404,178018507⟩,
⟨64,273073443,273073602⟩]
theorem checked45605 : checkPrefixCuts (2^48) 5981470721 10 Manual.Count131072.C045605.packed 64 cuts45605 = true := by
 decide +kernel
def pointBounds45605 : List (Nat × Nat × Nat) := [(5981556736,110509728244513,110510114710147)]
theorem point_links_checked45605 : (cuts45605.take 1).map (fun c => (5981470721-1+2*2^10*c.k,110509550226109+c.lower,110509936691640+c.upper)) = pointBounds45605 := by
 decide +kernel
def cuts45606 : List PrefixCut := [⟨64,271749868,271750020⟩]
theorem checked45606 : checkPrefixCuts (2^48) 5981601793 10 Manual.Count131072.C045606.packed 64 cuts45606 = true := by
 decide +kernel
def cuts45607 : List PrefixCut := [⟨6,24704242,24704255⟩,
⟨64,270332299,270332450⟩]
theorem checked45607 : checkPrefixCuts (2^48) 5981732865 10 Manual.Count131072.C045607.packed 64 cuts45607 = true := by
 decide +kernel
def pointBounds45607 : List (Nat × Nat × Nat) := [(5981745152,110510119753662,110510506219517)]
theorem point_links_checked45607 : (cuts45607.take 1).map (fun c => (5981732865-1+2*2^10*c.k,110510095049420+c.lower,110510481515262+c.upper)) = pointBounds45607 := by
 decide +kernel
def cuts45608 : List PrefixCut := [⟨34,148692036,148692122⟩,
⟨64,278466759,278466919⟩]
theorem checked45608 : checkPrefixCuts (2^48) 5981863937 10 Manual.Count131072.C045608.packed 64 cuts45608 = true := by
 decide +kernel
def pointBounds45608 : List (Nat × Nat × Nat) := [(5981933568,110510514073755,110510900539834)]
theorem point_links_checked45608 : (cuts45608.take 1).map (fun c => (5981863937-1+2*2^10*c.k,110510365381719+c.lower,110510751847712+c.upper)) = pointBounds45608 := by
 decide +kernel
def cuts45609 : List PrefixCut := [⟨62,269755899,269756060⟩,
⟨64,278225379,278225546⟩]
theorem checked45609 : checkPrefixCuts (2^48) 5981995009 10 Manual.Count131072.C045609.packed 64 cuts45609 = true := by
 decide +kernel
def pointBounds45609 : List (Nat × Nat × Nat) := [(5982121984,110510913604377,110511300070691)]
theorem point_links_checked45609 : (cuts45609.take 1).map (fun c => (5981995009-1+2*2^10*c.k,110510643848478+c.lower,110511030314631+c.upper)) = pointBounds45609 := by
 decide +kernel
def cuts45610 : List PrefixCut := [⟨64,275207937,275208090⟩]
theorem checked45610 : checkPrefixCuts (2^48) 5982126081 10 Manual.Count131072.C045610.packed 64 cuts45610 = true := by
 decide +kernel
def cuts45611 : List PrefixCut := [⟨26,109959145,109959208⟩,
⟨64,272519999,272520155⟩]
theorem checked45611 : checkPrefixCuts (2^48) 5982257153 10 Manual.Count131072.C045611.packed 64 cuts45611 = true := by
 decide +kernel
def pointBounds45611 : List (Nat × Nat × Nat) := [(5982310400,110511307240939,110511693707475)]
theorem point_links_checked45611 : (cuts45611.take 1).map (fun c => (5982257153-1+2*2^10*c.k,110511197281794+c.lower,110511583748267+c.upper)) = pointBounds45611 := by
 decide +kernel
def cuts45612 : List PrefixCut := [⟨54,229416578,229416708⟩,
⟨64,272090601,272090755⟩]
theorem checked45612 : checkPrefixCuts (2^48) 5982388225 10 Manual.Count131072.C045612.packed 64 cuts45612 = true := by
 decide +kernel
def pointBounds45612 : List (Nat × Nat × Nat) := [(5982498816,110511699218371,110512085685130)]
theorem point_links_checked45612 : (cuts45612.take 1).map (fun c => (5982388225-1+2*2^10*c.k,110511469801793+c.lower,110511856268422+c.upper)) = pointBounds45612 := by
 decide +kernel
def cuts45613 : List PrefixCut := [⟨64,274766407,274766570⟩]
theorem checked45613 : checkPrefixCuts (2^48) 5982519297 10 Manual.Count131072.C045613.packed 64 cuts45613 = true := by
 decide +kernel
def cuts45614 : List PrefixCut := [⟨18,77676883,77676925⟩,
⟨64,276924598,276924752⟩]
theorem checked45614 : checkPrefixCuts (2^48) 5982650369 10 Manual.Count131072.C045614.packed 64 cuts45614 = true := by
 decide +kernel
def pointBounds45614 : List (Nat × Nat × Nat) := [(5982687232,110512094335684,110512480802672)]
theorem point_links_checked45614 : (cuts45614.take 1).map (fun c => (5982650369-1+2*2^10*c.k,110512016658801+c.lower,110512403125747+c.upper)) = pointBounds45614 := by
 decide +kernel
def cuts45615 : List PrefixCut := [⟨46,198021363,198021481⟩,
⟨64,273954593,273954757⟩]
theorem checked45615 : checkPrefixCuts (2^48) 5982781441 10 Manual.Count131072.C045615.packed 64 cuts45615 = true := by
 decide +kernel
def pointBounds45615 : List (Nat × Nat × Nat) := [(5982875648,110512491604762,110512878071980)]
theorem point_links_checked45615 : (cuts45615.take 1).map (fun c => (5982781441-1+2*2^10*c.k,110512293583399+c.lower,110512680050499+c.upper)) = pointBounds45615 := by
 decide +kernel
def cuts45616 : List PrefixCut := [⟨64,271690408,271690557⟩]
theorem checked45616 : checkPrefixCuts (2^48) 5982912513 10 Manual.Count131072.C045616.packed 64 cuts45616 = true := by
 decide +kernel
def cuts45617 : List PrefixCut := [⟨10,43799230,43799251⟩,
⟨64,279070491,279070650⟩]
theorem checked45617 : checkPrefixCuts (2^48) 5983043585 10 Manual.Count131072.C045617.packed 64 cuts45617 = true := by
 decide +kernel
def pointBounds45617 : List (Nat × Nat × Nat) := [(5983064064,110512883027630,110513269495064)]
theorem point_links_checked45617 : (cuts45617.take 1).map (fun c => (5983043585-1+2*2^10*c.k,110512839228400+c.lower,110513225695813+c.upper)) = pointBounds45617 := by
 decide +kernel
def cuts45618 : List PrefixCut := [⟨38,160749695,160749787⟩,
⟨64,270690548,270690705⟩]
theorem checked45618 : checkPrefixCuts (2^48) 5983174657 10 Manual.Count131072.C045618.packed 64 cuts45618 = true := by
 decide +kernel
def pointBounds45618 : List (Nat × Nat × Nat) := [(5983252480,110513279048586,110513665516250)]
theorem point_links_checked45618 : (cuts45618.take 1).map (fun c => (5983174657-1+2*2^10*c.k,110513118298891+c.lower,110513504766463+c.upper)) = pointBounds45618 := by
 decide +kernel
def cuts45619 : List PrefixCut := [⟨64,273271990,273272148⟩]
theorem checked45619 : checkPrefixCuts (2^48) 5983305729 10 Manual.Count131072.C045619.packed 64 cuts45619 = true := by
 decide +kernel
def cuts45620 : List PrefixCut := [⟨2,8326492,8326497⟩,
⟨64,276652985,276653143⟩]
theorem checked45620 : checkPrefixCuts (2^48) 5983436801 10 Manual.Count131072.C045620.packed 64 cuts45620 = true := by
 decide +kernel
def pointBounds45620 : List (Nat × Nat × Nat) := [(5983440896,110513670587921,110514057055813)]
theorem point_links_checked45620 : (cuts45620.take 1).map (fun c => (5983436801-1+2*2^10*c.k,110513662261429+c.lower,110514048729316+c.upper)) = pointBounds45620 := by
 decide +kernel
def cuts45621 : List PrefixCut := [⟨30,129927450,129927527⟩,
⟨64,277775920,277776080⟩]
theorem checked45621 : checkPrefixCuts (2^48) 5983567873 10 Manual.Count131072.C045621.packed 64 cuts45621 = true := by
 decide +kernel
def pointBounds45621 : List (Nat × Nat × Nat) := [(5983629312,110514068841864,110514455309986)]
theorem point_links_checked45621 : (cuts45621.take 1).map (fun c => (5983567873-1+2*2^10*c.k,110513938914414+c.lower,110514325382459+c.upper)) = pointBounds45621 := by
 decide +kernel
def cuts45622 : List PrefixCut := [⟨58,247476469,247476606⟩,
⟨64,273818478,273818630⟩]
theorem checked45622 : checkPrefixCuts (2^48) 5983698945 10 Manual.Count131072.C045622.packed 64 cuts45622 = true := by
 decide +kernel
def pointBounds45622 : List (Nat × Nat × Nat) := [(5983817728,110514464166803,110514850635145)]
theorem point_links_checked45622 : (cuts45622.take 1).map (fun c => (5983698945-1+2*2^10*c.k,110514216690334+c.lower,110514603158539+c.upper)) = pointBounds45622 := by
 decide +kernel
def cuts45623 : List PrefixCut := [⟨64,275317736,275317890⟩]
theorem checked45623 : checkPrefixCuts (2^48) 5983830017 10 Manual.Count131072.C045623.packed 64 cuts45623 = true := by
 decide +kernel
def cuts45624 : List PrefixCut := [⟨22,95816498,95816555⟩,
⟨64,275452811,275452969⟩]
theorem checked45624 : checkPrefixCuts (2^48) 5983961089 10 Manual.Count131072.C045624.packed 64 cuts45624 = true := by
 decide +kernel
def pointBounds45624 : List (Nat × Nat × Nat) := [(5984006144,110514861643046,110515248111614)]
theorem point_links_checked45624 : (cuts45624.take 1).map (fun c => (5983961089-1+2*2^10*c.k,110514765826548+c.lower,110515152295059+c.upper)) = pointBounds45624 := by
 decide +kernel
def cuts45625 : List PrefixCut := [⟨50,213217777,213217902⟩,
⟨64,273518283,273518444⟩]
theorem checked45625 : checkPrefixCuts (2^48) 5984092161 10 Manual.Count131072.C045625.packed 64 cuts45625 = true := by
 decide +kernel
def pointBounds45625 : List (Nat × Nat × Nat) := [(5984194560,110515254497136,110515640965930)]
theorem point_links_checked45625 : (cuts45625.take 1).map (fun c => (5984092161-1+2*2^10*c.k,110515041279359+c.lower,110515427748028+c.upper)) = pointBounds45625 := by
 decide +kernel
def cuts45626 : List PrefixCut := [⟨64,277322175,277322332⟩]
theorem checked45626 : checkPrefixCuts (2^48) 5984223233 10 Manual.Count131072.C045626.packed 64 cuts45626 = true := by
 decide +kernel
def cuts45627 : List PrefixCut := [⟨14,59781512,59781545⟩,
⟨64,277127962,277128127⟩]
theorem checked45627 : checkPrefixCuts (2^48) 5984354305 10 Manual.Count131072.C045627.packed 64 cuts45627 = true := by
 decide +kernel
def pointBounds45627 : List (Nat × Nat × Nat) := [(5984382976,110515651901329,110516038370349)]
theorem point_links_checked45627 : (cuts45627.take 1).map (fun c => (5984354305-1+2*2^10*c.k,110515592119817+c.lower,110515978588804+c.upper)) = pointBounds45627 := by
 decide +kernel
def cuts45628 : List PrefixCut := [⟨42,177223215,177223320⟩,
⟨64,270584213,270584375⟩]
theorem checked45628 : checkPrefixCuts (2^48) 5984485377 10 Manual.Count131072.C045628.packed 64 cuts45628 = true := by
 decide +kernel
def pointBounds45628 : List (Nat × Nat × Nat) := [(5984571392,110516046470994,110516432940251)]
theorem point_links_checked45628 : (cuts45628.take 1).map (fun c => (5984485377-1+2*2^10*c.k,110515869247779+c.lower,110516255716931+c.upper)) = pointBounds45628 := by
 decide +kernel
def cuts45629 : List PrefixCut := [⟨64,274340887,274341051⟩]
theorem checked45629 : checkPrefixCuts (2^48) 5984616449 10 Manual.Count131072.C045629.packed 64 cuts45629 = true := by
 decide +kernel
def cuts45630 : List PrefixCut := [⟨6,25303213,25303228⟩,
⟨64,269208462,269208618⟩]
theorem checked45630 : checkPrefixCuts (2^48) 5984747521 10 Manual.Count131072.C045630.packed 64 cuts45630 = true := by
 decide +kernel
def pointBounds45630 : List (Nat × Nat × Nat) := [(5984759808,110516439476092,110516825945585)]
theorem point_links_checked45630 : (cuts45630.take 1).map (fun c => (5984747521-1+2*2^10*c.k,110516414172879+c.lower,110516800642357+c.upper)) = pointBounds45630 := by
 decide +kernel
def cuts45631 : List PrefixCut := [⟨34,146829961,146830046⟩,
⟨64,276351198,276351359⟩]
theorem checked45631 : checkPrefixCuts (2^48) 5984878593 10 Manual.Count131072.C045631.packed 64 cuts45631 = true := by
 decide +kernel
def pointBounds45631 : List (Nat × Nat × Nat) := [(5984948224,110516830211302,110517216681021)]
theorem point_links_checked45631 : (cuts45631.take 1).map (fun c => (5984878593-1+2*2^10*c.k,110516683381341+c.lower,110517069850975+c.upper)) = pointBounds45631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000175
