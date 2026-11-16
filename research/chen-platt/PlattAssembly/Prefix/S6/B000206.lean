import PlattAssemblyKernel
import PlattCertificates.Count131072.C056592
import PlattCertificates.Count131072.C056593
import PlattCertificates.Count131072.C056594
import PlattCertificates.Count131072.C056595
import PlattCertificates.Count131072.C056596
import PlattCertificates.Count131072.C056597
import PlattCertificates.Count131072.C056598
import PlattCertificates.Count131072.C056599
import PlattCertificates.Count131072.C056600
import PlattCertificates.Count131072.C056601
import PlattCertificates.Count131072.C056602
import PlattCertificates.Count131072.C056603
import PlattCertificates.Count131072.C056604
import PlattCertificates.Count131072.C056605
import PlattCertificates.Count131072.C056606
import PlattCertificates.Count131072.C056607
import PlattCertificates.Count131072.C056608
import PlattCertificates.Count131072.C056609
import PlattCertificates.Count131072.C056610
import PlattCertificates.Count131072.C056611
import PlattCertificates.Count131072.C056612
import PlattCertificates.Count131072.C056613
import PlattCertificates.Count131072.C056614
import PlattCertificates.Count131072.C056615
import PlattCertificates.Count131072.C056616
import PlattCertificates.Count131072.C056617
import PlattCertificates.Count131072.C056618
import PlattCertificates.Count131072.C056619
import PlattCertificates.Count131072.C056620
import PlattCertificates.Count131072.C056621
import PlattCertificates.Count131072.C056622
import PlattCertificates.Count131072.C056623
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000206
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56592 : List PrefixCut := [⟨64,219138270,219138393⟩]
theorem checked56592 : checkPrefixCuts (2^48) 7421558785 10 Manual.Count131072.C056592.packed 64 cuts56592 = true := by
 decide +kernel
def cuts56593 : List PrefixCut := [⟨46,159136422,159136512⟩,
⟨64,220461808,220461933⟩]
theorem checked56593 : checkPrefixCuts (2^48) 7421689857 10 Manual.Count131072.C056593.packed 64 cuts56593 = true := by
 decide +kernel
def pointBounds56593 : List (Nat × Nat × Nat) := [(7421784064,113194318167601,113194706163085)]
theorem point_links_checked56593 : (cuts56593.take 1).map (fun c => (7421689857-1+2*2^10*c.k,113194159031179+c.lower,113194547026573+c.upper)) = pointBounds56593 := by
 decide +kernel
def cuts56594 : List PrefixCut := [⟨64,218637524,218637650⟩]
theorem checked56594 : checkPrefixCuts (2^48) 7421820929 10 Manual.Count131072.C056594.packed 64 cuts56594 = true := by
 decide +kernel
def cuts56595 : List PrefixCut := [⟨32,110056834,110056898⟩,
⟨64,219430060,219430186⟩]
theorem checked56595 : checkPrefixCuts (2^48) 7421952001 10 Manual.Count131072.C056595.packed 64 cuts56595 = true := by
 decide +kernel
def pointBounds56595 : List (Nat × Nat × Nat) := [(7422017536,113194708187345,113195096183054)]
theorem point_links_checked56595 : (cuts56595.take 1).map (fun c => (7421952001-1+2*2^10*c.k,113194598130511+c.lower,113194986126156+c.upper)) = pointBounds56595 := by
 decide +kernel
def cuts56596 : List PrefixCut := [⟨64,214647817,214647940⟩]
theorem checked56596 : checkPrefixCuts (2^48) 7422083073 10 Manual.Count131072.C056596.packed 64 cuts56596 = true := by
 decide +kernel
def cuts56597 : List PrefixCut := [⟨18,61814835,61814871⟩,
⟨64,218322562,218322688⟩]
theorem checked56597 : checkPrefixCuts (2^48) 7422214145 10 Manual.Count131072.C056597.packed 64 cuts56597 = true := by
 decide +kernel
def pointBounds56597 : List (Nat × Nat × Nat) := [(7422251008,113195094023223,113195482019153)]
theorem point_links_checked56597 : (cuts56597.take 1).map (fun c => (7422214145-1+2*2^10*c.k,113195032208388+c.lower,113195420204282+c.upper)) = pointBounds56597 := by
 decide +kernel
def cuts56598 : List PrefixCut := [⟨64,220745718,220745843⟩]
theorem checked56598 : checkPrefixCuts (2^48) 7422345217 10 Manual.Count131072.C056598.packed 64 cuts56598 = true := by
 decide +kernel
def cuts56599 : List PrefixCut := [⟨4,13007228,13007235⟩,
⟨64,216873809,216873933⟩]
theorem checked56599 : checkPrefixCuts (2^48) 7422476289 10 Manual.Count131072.C056599.packed 64 cuts56599 = true := by
 decide +kernel
def pointBounds56599 : List (Nat × Nat × Nat) := [(7422484480,113195484283896,113195872280048)]
theorem point_links_checked56599 : (cuts56599.take 1).map (fun c => (7422476289-1+2*2^10*c.k,113195471276668+c.lower,113195859272813+c.upper)) = pointBounds56599 := by
 decide +kernel
def cuts56600 : List PrefixCut := [⟨54,184258209,184258315⟩,
⟨64,219069394,219069519⟩]
theorem checked56600 : checkPrefixCuts (2^48) 7422607361 10 Manual.Count131072.C056600.packed 64 cuts56600 = true := by
 decide +kernel
def pointBounds56600 : List (Nat × Nat × Nat) := [(7422717952,113195872408686,113196260405061)]
theorem point_links_checked56600 : (cuts56600.take 1).map (fun c => (7422607361-1+2*2^10*c.k,113195688150477+c.lower,113196076146746+c.upper)) = pointBounds56600 := by
 decide +kernel
def cuts56601 : List PrefixCut := [⟨64,216714470,216714593⟩]
theorem checked56601 : checkPrefixCuts (2^48) 7422738433 10 Manual.Count131072.C056601.packed 64 cuts56601 = true := by
 decide +kernel
def cuts56602 : List PrefixCut := [⟨40,134084234,134084311⟩,
⟨64,215838485,215838608⟩]
theorem checked56602 : checkPrefixCuts (2^48) 7422869505 10 Manual.Count131072.C056602.packed 64 cuts56602 = true := by
 decide +kernel
def pointBounds56602 : List (Nat × Nat × Nat) := [(7422951424,113196258018575,113196646015169)]
theorem point_links_checked56602 : (cuts56602.take 1).map (fun c => (7422869505-1+2*2^10*c.k,113196123934341+c.lower,113196511930858+c.upper)) = pointBounds56602 := by
 decide +kernel
def cuts56603 : List PrefixCut := [⟨64,219399084,219399209⟩]
theorem checked56603 : checkPrefixCuts (2^48) 7423000577 10 Manual.Count131072.C056603.packed 64 cuts56603 = true := by
 decide +kernel
def cuts56604 : List PrefixCut := [⟨26,88843008,88843060⟩,
⟨64,217044267,217044391⟩]
theorem checked56604 : checkPrefixCuts (2^48) 7423131649 10 Manual.Count131072.C056604.packed 64 cuts56604 = true := by
 decide +kernel
def pointBounds56604 : List (Nat × Nat × Nat) := [(7423184896,113196648014918,113197036011735)]
theorem point_links_checked56604 : (cuts56604.take 1).map (fun c => (7423131649-1+2*2^10*c.k,113196559171910+c.lower,113196947168675+c.upper)) = pointBounds56604 := by
 decide +kernel
def cuts56605 : List PrefixCut := [⟨64,219922164,219922285⟩]
theorem checked56605 : checkPrefixCuts (2^48) 7423262721 10 Manual.Count131072.C056605.packed 64 cuts56605 = true := by
 decide +kernel
def cuts56606 : List PrefixCut := [⟨12,42770621,42770645⟩,
⟨64,220676625,220676749⟩]
theorem checked56606 : checkPrefixCuts (2^48) 7423393793 10 Manual.Count131072.C056606.packed 64 cuts56606 = true := by
 decide +kernel
def pointBounds56606 : List (Nat × Nat × Nat) := [(7423418368,113197038908962,113197426905996)]
theorem point_links_checked56606 : (cuts56606.take 1).map (fun c => (7423393793-1+2*2^10*c.k,113196996138341+c.lower,113197384135351+c.upper)) = pointBounds56606 := by
 decide +kernel
def cuts56607 : List PrefixCut := [⟨62,212862021,212862142⟩,
⟨64,220255631,220255756⟩]
theorem checked56607 : checkPrefixCuts (2^48) 7423524865 10 Manual.Count131072.C056607.packed 64 cuts56607 = true := by
 decide +kernel
def pointBounds56607 : List (Nat × Nat × Nat) := [(7423651840,113197429676987,113197817674242)]
theorem point_links_checked56607 : (cuts56607.take 1).map (fun c => (7423524865-1+2*2^10*c.k,113197216814966+c.lower,113197604812100+c.upper)) = pointBounds56607 := by
 decide +kernel
def cuts56608 : List PrefixCut := [⟨64,217483917,217484040⟩]
theorem checked56608 : checkPrefixCuts (2^48) 7423655937 10 Manual.Count131072.C056608.packed 64 cuts56608 = true := by
 decide +kernel
def cuts56609 : List PrefixCut := [⟨48,163830794,163830890⟩,
⟨64,218845004,218845132⟩]
theorem checked56609 : checkPrefixCuts (2^48) 7423787009 10 Manual.Count131072.C056609.packed 64 cuts56609 = true := by
 decide +kernel
def pointBounds56609 : List (Nat × Nat × Nat) := [(7423885312,113197818385308,113198206382786)]
theorem point_links_checked56609 : (cuts56609.take 1).map (fun c => (7423787009-1+2*2^10*c.k,113197654554514+c.lower,113198042551896+c.upper)) = pointBounds56609 := by
 decide +kernel
def cuts56610 : List PrefixCut := [⟨64,217779538,217779662⟩]
theorem checked56610 : checkPrefixCuts (2^48) 7423918081 10 Manual.Count131072.C056610.packed 64 cuts56610 = true := by
 decide +kernel
def cuts56611 : List PrefixCut := [⟨34,115371555,115371622⟩,
⟨64,218913107,218913232⟩]
theorem checked56611 : checkPrefixCuts (2^48) 7424049153 10 Manual.Count131072.C056611.packed 64 cuts56611 = true := by
 decide +kernel
def pointBounds56611 : List (Nat × Nat × Nat) := [(7424118784,113198206550611,113198594548312)]
theorem point_links_checked56611 : (cuts56611.take 1).map (fun c => (7424049153-1+2*2^10*c.k,113198091179056+c.lower,113198479176690+c.upper)) = pointBounds56611 := by
 decide +kernel
def cuts56612 : List PrefixCut := [⟨64,220008712,220008837⟩]
theorem checked56612 : checkPrefixCuts (2^48) 7424180225 10 Manual.Count131072.C056612.packed 64 cuts56612 = true := by
 decide +kernel
def cuts56613 : List PrefixCut := [⟨20,66536415,66536453⟩,
⟨64,220042718,220042843⟩]
theorem checked56613 : checkPrefixCuts (2^48) 7424311297 10 Manual.Count131072.C056613.packed 64 cuts56613 = true := by
 decide +kernel
def pointBounds56613 : List (Nat × Nat × Nat) := [(7424352256,113198596637290,113198984635212)]
theorem point_links_checked56613 : (cuts56613.take 1).map (fun c => (7424311297-1+2*2^10*c.k,113198530100875+c.lower,113198918098759+c.upper)) = pointBounds56613 := by
 decide +kernel
def cuts56614 : List PrefixCut := [⟨64,219697671,219697794⟩]
theorem checked56614 : checkPrefixCuts (2^48) 7424442369 10 Manual.Count131072.C056614.packed 64 cuts56614 = true := by
 decide +kernel
def cuts56615 : List PrefixCut := [⟨6,21116551,21116562⟩,
⟨64,217153762,217153884⟩]
theorem checked56615 : checkPrefixCuts (2^48) 7424573441 10 Manual.Count131072.C056615.packed 64 cuts56615 = true := by
 decide +kernel
def pointBounds56615 : List (Nat × Nat × Nat) := [(7424585728,113198990957815,113199378955958)]
theorem point_links_checked56615 : (cuts56615.take 1).map (fun c => (7424573441-1+2*2^10*c.k,113198969841264+c.lower,113199357839396+c.upper)) = pointBounds56615 := by
 decide +kernel
def cuts56616 : List PrefixCut := [⟨56,191257424,191257532⟩,
⟨64,218628415,218628538⟩]
theorem checked56616 : checkPrefixCuts (2^48) 7424704513 10 Manual.Count131072.C056616.packed 64 cuts56616 = true := by
 decide +kernel
def pointBounds56616 : List (Nat × Nat × Nat) := [(7424819200,113199378252450,113199766250812)]
theorem point_links_checked56616 : (cuts56616.take 1).map (fun c => (7424704513-1+2*2^10*c.k,113199186995026+c.lower,113199574993280+c.upper)) = pointBounds56616 := by
 decide +kernel
def cuts56617 : List PrefixCut := [⟨64,218776198,218776322⟩]
theorem checked56617 : checkPrefixCuts (2^48) 7424835585 10 Manual.Count131072.C056617.packed 64 cuts56617 = true := by
 decide +kernel
def cuts56618 : List PrefixCut := [⟨42,143334039,143334120⟩,
⟨64,218544889,218545012⟩]
theorem checked56618 : checkPrefixCuts (2^48) 7424966657 10 Manual.Count131072.C056618.packed 64 cuts56618 = true := by
 decide +kernel
def pointBounds56618 : List (Nat × Nat × Nat) := [(7425052672,113199767733678,113200155732260)]
theorem point_links_checked56618 : (cuts56618.take 1).map (fun c => (7424966657-1+2*2^10*c.k,113199624399639+c.lower,113200012398140+c.upper)) = pointBounds56618 := by
 decide +kernel
def cuts56619 : List PrefixCut := [⟨64,219905737,219905863⟩]
theorem checked56619 : checkPrefixCuts (2^48) 7425097729 10 Manual.Count131072.C056619.packed 64 cuts56619 = true := by
 decide +kernel
def cuts56620 : List PrefixCut := [⟨28,96664802,96664855⟩,
⟨64,219029979,219030102⟩]
theorem checked56620 : checkPrefixCuts (2^48) 7425228801 10 Manual.Count131072.C056620.packed 64 cuts56620 = true := by
 decide +kernel
def pointBounds56620 : List (Nat × Nat × Nat) := [(7425286144,113200159515067,113200547513870)]
theorem point_links_checked56620 : (cuts56620.take 1).map (fun c => (7425228801-1+2*2^10*c.k,113200062850265+c.lower,113200450849015+c.upper)) = pointBounds56620 := by
 decide +kernel
def cuts56621 : List PrefixCut := [⟨64,220277035,220277161⟩]
theorem checked56621 : checkPrefixCuts (2^48) 7425359873 10 Manual.Count131072.C056621.packed 64 cuts56621 = true := by
 decide +kernel
def cuts56622 : List PrefixCut := [⟨14,48520316,48520344⟩,
⟨64,218529459,218529583⟩]
theorem checked56622 : checkPrefixCuts (2^48) 7425490945 10 Manual.Count131072.C056622.packed 64 cuts56622 = true := by
 decide +kernel
def pointBounds56622 : List (Nat × Nat × Nat) := [(7425519616,113200550677595,113200938676622)]
theorem point_links_checked56622 : (cuts56622.take 1).map (fun c => (7425490945-1+2*2^10*c.k,113200502157279+c.lower,113200890156278+c.upper)) = pointBounds56622 := by
 decide +kernel
def cuts56623 : List PrefixCut := [⟨64,217502137,217502260⟩]
theorem checked56623 : checkPrefixCuts (2^48) 7425622017 10 Manual.Count131072.C056623.packed 64 cuts56623 = true := by
 decide +kernel
def pointBounds56623 : List (Nat × Nat × Nat) := [(7425753088,113200938188875,113201326188121)]
theorem point_links_checked56623 : (cuts56623.take 1).map (fun c => (7425622017-1+2*2^10*c.k,113200720686738+c.lower,113201108685861+c.upper)) = pointBounds56623 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000206
