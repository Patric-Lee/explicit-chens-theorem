import PlattAssemblyKernel
import PlattCertificates.Count131072.C064640
import PlattCertificates.Count131072.C064641
import PlattCertificates.Count131072.C064642
import PlattCertificates.Count131072.C064643
import PlattCertificates.Count131072.C064644
import PlattCertificates.Count131072.C064645
import PlattCertificates.Count131072.C064646
import PlattCertificates.Count131072.C064647
import PlattCertificates.Count131072.C064648
import PlattCertificates.Count131072.C064649
import PlattCertificates.Count131072.C064650
import PlattCertificates.Count131072.C064651
import PlattCertificates.Count131072.C064652
import PlattCertificates.Count131072.C064653
import PlattCertificates.Count131072.C064654
import PlattCertificates.Count131072.C064655
import PlattCertificates.Count131072.C064656
import PlattCertificates.Count131072.C064657
import PlattCertificates.Count131072.C064658
import PlattCertificates.Count131072.C064659
import PlattCertificates.Count131072.C064660
import PlattCertificates.Count131072.C064661
import PlattCertificates.Count131072.C064662
import PlattCertificates.Count131072.C064663
import PlattCertificates.Count131072.C064664
import PlattCertificates.Count131072.C064665
import PlattCertificates.Count131072.C064666
import PlattCertificates.Count131072.C064667
import PlattCertificates.Count131072.C064668
import PlattCertificates.Count131072.C064669
import PlattCertificates.Count131072.C064670
import PlattCertificates.Count131072.C064671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64640 : List PrefixCut := [⟨64,192664305,192664417⟩]
theorem checked64640 : checkPrefixCuts (2^48) 8476426241 10 Manual.Count131072.C064640.packed 64 cuts64640 = true := by
 decide +kernel
def cuts64641 : List PrefixCut := [⟨16,47684121,47684145⟩,
⟨64,193690705,193690815⟩]
theorem checked64641 : checkPrefixCuts (2^48) 8476557313 10 Manual.Count131072.C064641.packed 64 cuts64641 = true := by
 decide +kernel
def pointBounds64641 : List (Nat × Nat × Nat) := [(8476590080,114835284376113,114835673310706)]
theorem point_links_checked64641 : (cuts64641.take 1).map (fun c => (8476557313-1+2*2^10*c.k,114835236691992+c.lower,114835625626561+c.upper)) = pointBounds64641 := by
 decide +kernel
def cuts64642 : List PrefixCut := [⟨64,192591925,192592034⟩]
theorem checked64642 : checkPrefixCuts (2^48) 8476688385 10 Manual.Count131072.C064642.packed 64 cuts64642 = true := by
 decide +kernel
def cuts64643 : List PrefixCut := [⟨18,52198535,52198568⟩,
⟨64,192356501,192356614⟩]
theorem checked64643 : checkPrefixCuts (2^48) 8476819457 10 Manual.Count131072.C064643.packed 64 cuts64643 = true := by
 decide +kernel
def pointBounds64643 : List (Nat × Nat × Nat) := [(8476856320,114835675173157,114836064107978)]
theorem point_links_checked64643 : (cuts64643.take 1).map (fun c => (8476819457-1+2*2^10*c.k,114835622974622+c.lower,114836011909410+c.upper)) = pointBounds64643 := by
 decide +kernel
def cuts64644 : List PrefixCut := [⟨64,190361268,190361379⟩]
theorem checked64644 : checkPrefixCuts (2^48) 8476950529 10 Manual.Count131072.C064644.packed 64 cuts64644 = true := by
 decide +kernel
def cuts64645 : List PrefixCut := [⟨20,58472493,58472526⟩,
⟨64,188764540,188764645⟩]
theorem checked64645 : checkPrefixCuts (2^48) 8477081601 10 Manual.Count131072.C064645.packed 64 cuts64645 = true := by
 decide +kernel
def pointBounds64645 : List (Nat × Nat × Nat) := [(8477122560,114836064164884,114836453099929)]
theorem point_links_checked64645 : (cuts64645.take 1).map (fun c => (8477081601-1+2*2^10*c.k,114836005692391+c.lower,114836394627403+c.upper)) = pointBounds64645 := by
 decide +kernel
def cuts64646 : List PrefixCut := [⟨64,187333872,187333985⟩]
theorem checked64646 : checkPrefixCuts (2^48) 8477212673 10 Manual.Count131072.C064646.packed 64 cuts64646 = true := by
 decide +kernel
def cuts64647 : List PrefixCut := [⟨22,64380824,64380861⟩,
⟨64,187330967,187331082⟩]
theorem checked64647 : checkPrefixCuts (2^48) 8477343745 10 Manual.Count131072.C064647.packed 64 cuts64647 = true := by
 decide +kernel
def pointBounds64647 : List (Nat × Nat × Nat) := [(8477388800,114836446171627,114836835106894)]
theorem point_links_checked64647 : (cuts64647.take 1).map (fun c => (8477343745-1+2*2^10*c.k,114836381790803+c.lower,114836770726033+c.upper)) = pointBounds64647 := by
 decide +kernel
def cuts64648 : List PrefixCut := [⟨64,191212759,191212873⟩]
theorem checked64648 : checkPrefixCuts (2^48) 8477474817 10 Manual.Count131072.C064648.packed 64 cuts64648 = true := by
 decide +kernel
def cuts64649 : List PrefixCut := [⟨24,70886422,70886464⟩,
⟨64,189948130,189948236⟩]
theorem checked64649 : checkPrefixCuts (2^48) 8477605889 10 Manual.Count131072.C064649.packed 64 cuts64649 = true := by
 decide +kernel
def pointBounds64649 : List (Nat × Nat × Nat) := [(8477655040,114836831220951,114837220156452)]
theorem point_links_checked64649 : (cuts64649.take 1).map (fun c => (8477605889-1+2*2^10*c.k,114836760334529+c.lower,114837149269988+c.upper)) = pointBounds64649 := by
 decide +kernel
def cuts64650 : List PrefixCut := [⟨64,190609227,190609335⟩]
theorem checked64650 : checkPrefixCuts (2^48) 8477736961 10 Manual.Count131072.C064650.packed 64 cuts64650 = true := by
 decide +kernel
def cuts64651 : List PrefixCut := [⟨26,77258815,77258859⟩,
⟨64,191237087,191237200⟩]
theorem checked64651 : checkPrefixCuts (2^48) 8477868033 10 Manual.Count131072.C064651.packed 64 cuts64651 = true := by
 decide +kernel
def pointBounds64651 : List (Nat × Nat × Nat) := [(8477921280,114837218150701,114837607086418)]
theorem point_links_checked64651 : (cuts64651.take 1).map (fun c => (8477868033-1+2*2^10*c.k,114837140891886+c.lower,114837529827559+c.upper)) = pointBounds64651 := by
 decide +kernel
def cuts64652 : List PrefixCut := [⟨64,191001741,191001855⟩]
theorem checked64652 : checkPrefixCuts (2^48) 8477999105 10 Manual.Count131072.C064652.packed 64 cuts64652 = true := by
 decide +kernel
def cuts64653 : List PrefixCut := [⟨28,84792810,84792856⟩,
⟨64,191164799,191164907⟩]
theorem checked64653 : checkPrefixCuts (2^48) 8478130177 10 Manual.Count131072.C064653.packed 64 cuts64653 = true := by
 decide +kernel
def pointBounds64653 : List (Nat × Nat × Nat) := [(8478187520,114837607923524,114837996859470)]
theorem point_links_checked64653 : (cuts64653.take 1).map (fun c => (8478130177-1+2*2^10*c.k,114837523130714+c.lower,114837912066614+c.upper)) = pointBounds64653 := by
 decide +kernel
def cuts64654 : List PrefixCut := [⟨64,189302675,189302784⟩]
theorem checked64654 : checkPrefixCuts (2^48) 8478261249 10 Manual.Count131072.C064654.packed 64 cuts64654 = true := by
 decide +kernel
def cuts64655 : List PrefixCut := [⟨30,91396763,91396813⟩,
⟨64,192254446,192254556⟩]
theorem checked64655 : checkPrefixCuts (2^48) 8478392321 10 Manual.Count131072.C064655.packed 64 cuts64655 = true := by
 decide +kernel
def pointBounds64655 : List (Nat × Nat × Nat) := [(8478453760,114837994994951,114838383931118)]
theorem point_links_checked64655 : (cuts64655.take 1).map (fun c => (8478392321-1+2*2^10*c.k,114837903598188+c.lower,114838292534305+c.upper)) = pointBounds64655 := by
 decide +kernel
def cuts64656 : List PrefixCut := [⟨64,193015026,193015139⟩]
theorem checked64656 : checkPrefixCuts (2^48) 8478523393 10 Manual.Count131072.C064656.packed 64 cuts64656 = true := by
 decide +kernel
def cuts64657 : List PrefixCut := [⟨32,94116145,94116196⟩,
⟨64,189659058,189659161⟩]
theorem checked64657 : checkPrefixCuts (2^48) 8478654465 10 Manual.Count131072.C064657.packed 64 cuts64657 = true := by
 decide +kernel
def pointBounds64657 : List (Nat × Nat × Nat) := [(8478720000,114838382983805,114838771920196)]
theorem point_links_checked64657 : (cuts64657.take 1).map (fun c => (8478654465-1+2*2^10*c.k,114838288867660+c.lower,114838677804000+c.upper)) = pointBounds64657 := by
 decide +kernel
def cuts64658 : List PrefixCut := [⟨64,188726606,188726718⟩]
theorem checked64658 : checkPrefixCuts (2^48) 8478785537 10 Manual.Count131072.C064658.packed 64 cuts64658 = true := by
 decide +kernel
def cuts64659 : List PrefixCut := [⟨34,101648911,101648968⟩,
⟨64,192939673,192939782⟩]
theorem checked64659 : checkPrefixCuts (2^48) 8478916609 10 Manual.Count131072.C064659.packed 64 cuts64659 = true := by
 decide +kernel
def pointBounds64659 : List (Nat × Nat × Nat) := [(8478986240,114838768902235,114839157838847)]
theorem point_links_checked64659 : (cuts64659.take 1).map (fun c => (8478916609-1+2*2^10*c.k,114838667253324+c.lower,114839056189879+c.upper)) = pointBounds64659 := by
 decide +kernel
def cuts64660 : List PrefixCut := [⟨64,188587983,188588090⟩]
theorem checked64660 : checkPrefixCuts (2^48) 8479047681 10 Manual.Count131072.C064660.packed 64 cuts64660 = true := by
 decide +kernel
def cuts64661 : List PrefixCut := [⟨36,107222647,107222707⟩,
⟨64,188784257,188784364⟩]
theorem checked64661 : checkPrefixCuts (2^48) 8479178753 10 Manual.Count131072.C064661.packed 64 cuts64661 = true := by
 decide +kernel
def pointBounds64661 : List (Nat × Nat × Nat) := [(8479252480,114839156003627,114839544940458)]
theorem point_links_checked64661 : (cuts64661.take 1).map (fun c => (8479178753-1+2*2^10*c.k,114839048780980+c.lower,114839437717751+c.upper)) = pointBounds64661 := by
 decide +kernel
def cuts64662 : List PrefixCut := [⟨64,189943166,189943276⟩]
theorem checked64662 : checkPrefixCuts (2^48) 8479309825 10 Manual.Count131072.C064662.packed 64 cuts64662 = true := by
 decide +kernel
def cuts64663 : List PrefixCut := [⟨38,113161165,113161232⟩,
⟨64,191599941,191600055⟩]
theorem checked64663 : checkPrefixCuts (2^48) 8479440897 10 Manual.Count131072.C064663.packed 64 cuts64663 = true := by
 decide +kernel
def pointBounds64663 : List (Nat × Nat × Nat) := [(8479518720,114839540669568,114839929606623)]
theorem point_links_checked64663 : (cuts64663.take 1).map (fun c => (8479440897-1+2*2^10*c.k,114839427508403+c.lower,114839816445391+c.upper)) = pointBounds64663 := by
 decide +kernel
def cuts64664 : List PrefixCut := [⟨64,191165469,191165580⟩]
theorem checked64664 : checkPrefixCuts (2^48) 8479571969 10 Manual.Count131072.C064664.packed 64 cuts64664 = true := by
 decide +kernel
def cuts64665 : List PrefixCut := [⟨40,116941739,116941810⟩,
⟨64,189137687,189137798⟩]
theorem checked64665 : checkPrefixCuts (2^48) 8479703041 10 Manual.Count131072.C064665.packed 64 cuts64665 = true := by
 decide +kernel
def pointBounds64665 : List (Nat × Nat × Nat) := [(8479784960,114839927215552,114840316152836)]
theorem point_links_checked64665 : (cuts64665.take 1).map (fun c => (8479703041-1+2*2^10*c.k,114839810273813+c.lower,114840199211026+c.upper)) = pointBounds64665 := by
 decide +kernel
def cuts64666 : List PrefixCut := [⟨64,191292340,191292444⟩]
theorem checked64666 : checkPrefixCuts (2^48) 8479834113 10 Manual.Count131072.C064666.packed 64 cuts64666 = true := by
 decide +kernel
def cuts64667 : List PrefixCut := [⟨42,124970746,124970818⟩,
⟨64,189961674,189961782⟩]
theorem checked64667 : checkPrefixCuts (2^48) 8479965185 10 Manual.Count131072.C064667.packed 64 cuts64667 = true := by
 decide +kernel
def pointBounds64667 : List (Nat × Nat × Nat) := [(8480051200,114840315674586,114840704612086)]
theorem point_links_checked64667 : (cuts64667.take 1).map (fun c => (8479965185-1+2*2^10*c.k,114840190703840+c.lower,114840579641268+c.upper)) = pointBounds64667 := by
 decide +kernel
def cuts64668 : List PrefixCut := [⟨64,189095735,189095844⟩]
theorem checked64668 : checkPrefixCuts (2^48) 8480096257 10 Manual.Count131072.C064668.packed 64 cuts64668 = true := by
 decide +kernel
def cuts64669 : List PrefixCut := [⟨44,131870738,131870814⟩,
⟨64,191349853,191349962⟩]
theorem checked64669 : checkPrefixCuts (2^48) 8480227329 10 Manual.Count131072.C064669.packed 64 cuts64669 = true := by
 decide +kernel
def pointBounds64669 : List (Nat × Nat × Nat) := [(8480317440,114840701631987,114841090569708)]
theorem point_links_checked64669 : (cuts64669.take 1).map (fun c => (8480227329-1+2*2^10*c.k,114840569761249+c.lower,114840958698894+c.upper)) = pointBounds64669 := by
 decide +kernel
def cuts64670 : List PrefixCut := [⟨64,190085637,190085751⟩]
theorem checked64670 : checkPrefixCuts (2^48) 8480358401 10 Manual.Count131072.C064670.packed 64 cuts64670 = true := by
 decide +kernel
def cuts64671 : List PrefixCut := [⟨46,137542234,137542314⟩,
⟨64,191941359,191941470⟩]
theorem checked64671 : checkPrefixCuts (2^48) 8480489473 10 Manual.Count131072.C064671.packed 64 cuts64671 = true := by
 decide +kernel
def pointBounds64671 : List (Nat × Nat × Nat) := [(8480583680,114841088738973,114841477676921)]
theorem point_links_checked64671 : (cuts64671.take 1).map (fun c => (8480489473-1+2*2^10*c.k,114840951196739+c.lower,114841340134607+c.upper)) = pointBounds64671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000145
