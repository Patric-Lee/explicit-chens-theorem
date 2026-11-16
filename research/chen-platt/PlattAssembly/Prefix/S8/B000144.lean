import PlattAssemblyKernel
import PlattCertificates.Count131072.C074608
import PlattCertificates.Count131072.C074609
import PlattCertificates.Count131072.C074610
import PlattCertificates.Count131072.C074611
import PlattCertificates.Count131072.C074612
import PlattCertificates.Count131072.C074613
import PlattCertificates.Count131072.C074614
import PlattCertificates.Count131072.C074615
import PlattCertificates.Count131072.C074616
import PlattCertificates.Count131072.C074617
import PlattCertificates.Count131072.C074618
import PlattCertificates.Count131072.C074619
import PlattCertificates.Count131072.C074620
import PlattCertificates.Count131072.C074621
import PlattCertificates.Count131072.C074622
import PlattCertificates.Count131072.C074623
import PlattCertificates.Count131072.C074624
import PlattCertificates.Count131072.C074625
import PlattCertificates.Count131072.C074626
import PlattCertificates.Count131072.C074627
import PlattCertificates.Count131072.C074628
import PlattCertificates.Count131072.C074629
import PlattCertificates.Count131072.C074630
import PlattCertificates.Count131072.C074631
import PlattCertificates.Count131072.C074632
import PlattCertificates.Count131072.C074633
import PlattCertificates.Count131072.C074634
import PlattCertificates.Count131072.C074635
import PlattCertificates.Count131072.C074636
import PlattCertificates.Count131072.C074637
import PlattCertificates.Count131072.C074638
import PlattCertificates.Count131072.C074639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000144
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74608 : List PrefixCut := [⟨64,161841305,161841399⟩]
theorem checked74608 : checkPrefixCuts (2^48) 9782951937 10 Manual.Count131072.C074608.packed 64 cuts74608 = true := by
 decide +kernel
def cuts74609 : List PrefixCut := [⟨35,89968449,89968499⟩,
⟨64,164313474,164313572⟩]
theorem checked74609 : checkPrefixCuts (2^48) 9783083009 10 Manual.Count131072.C074609.packed 64 cuts74609 = true := by
 decide +kernel
def pointBounds74609 : List (Nat × Nat × Nat) := [(9783154688,116594878709096,116595268678128)]
theorem point_links_checked74609 : (cuts74609.take 1).map (fun c => (9783083009-1+2*2^10*c.k,116594788740647+c.lower,116595178709629+c.upper)) = pointBounds74609 := by
 decide +kernel
def cuts74610 : List PrefixCut := [⟨64,166843123,166843223⟩]
theorem checked74610 : checkPrefixCuts (2^48) 9783214081 10 Manual.Count131072.C074610.packed 64 cuts74610 = true := by
 decide +kernel
def cuts74611 : List PrefixCut := [⟨57,144486212,144486299⟩,
⟨64,163244551,163244649⟩]
theorem checked74611 : checkPrefixCuts (2^48) 9783345153 10 Manual.Count131072.C074611.packed 64 cuts74611 = true := by
 decide +kernel
def pointBounds74611 : List (Nat × Nat × Nat) := [(9783461888,116595264383456,116595654352723)]
theorem point_links_checked74611 : (cuts74611.take 1).map (fun c => (9783345153-1+2*2^10*c.k,116595119897244+c.lower,116595509866424+c.upper)) = pointBounds74611 := by
 decide +kernel
def cuts74612 : List PrefixCut := [⟨64,162666975,162667067⟩]
theorem checked74612 : checkPrefixCuts (2^48) 9783476225 10 Manual.Count131072.C074612.packed 64 cuts74612 = true := by
 decide +kernel
def cuts74613 : List PrefixCut := [⟨64,166002082,166002182⟩]
theorem checked74613 : checkPrefixCuts (2^48) 9783607297 10 Manual.Count131072.C074613.packed 64 cuts74613 = true := by
 decide +kernel
def cuts74614 : List PrefixCut := [⟨15,39471920,39471945⟩,
⟨64,165424483,165424581⟩]
theorem checked74614 : checkPrefixCuts (2^48) 9783738369 10 Manual.Count131072.C074614.packed 64 cuts74614 = true := by
 decide +kernel
def pointBounds74614 : List (Nat × Nat × Nat) := [(9783769088,116595651282772,116596041252267)]
theorem point_links_checked74614 : (cuts74614.take 1).map (fun c => (9783738369-1+2*2^10*c.k,116595611810852+c.lower,116596001780322+c.upper)) = pointBounds74614 := by
 decide +kernel
def cuts74615 : List PrefixCut := [⟨64,165048269,165048368⟩]
theorem checked74615 : checkPrefixCuts (2^48) 9783869441 10 Manual.Count131072.C074615.packed 64 cuts74615 = true := by
 decide +kernel
def cuts74616 : List PrefixCut := [⟨37,96260357,96260416⟩,
⟨64,165621433,165621533⟩]
theorem checked74616 : checkPrefixCuts (2^48) 9784000513 10 Manual.Count131072.C074616.packed 64 cuts74616 = true := by
 decide +kernel
def pointBounds74616 : List (Nat × Nat × Nat) := [(9784076288,116596038543961,116596428513687)]
theorem point_links_checked74616 : (cuts74616.take 1).map (fun c => (9784000513-1+2*2^10*c.k,116595942283604+c.lower,116596332253271+c.upper)) = pointBounds74616 := by
 decide +kernel
def cuts74617 : List PrefixCut := [⟨64,164123253,164123359⟩]
theorem checked74617 : checkPrefixCuts (2^48) 9784131585 10 Manual.Count131072.C074617.packed 64 cuts74617 = true := by
 decide +kernel
def cuts74618 : List PrefixCut := [⟨59,148845355,148845444⟩,
⟨64,162423735,162423831⟩]
theorem checked74618 : checkPrefixCuts (2^48) 9784262657 10 Manual.Count131072.C074618.packed 64 cuts74618 = true := by
 decide +kernel
def pointBounds74618 : List (Nat × Nat × Nat) := [(9784383488,116596420873645,116596810843607)]
theorem point_links_checked74618 : (cuts74618.take 1).map (fun c => (9784262657-1+2*2^10*c.k,116596272028290+c.lower,116596661998163+c.upper)) = pointBounds74618 := by
 decide +kernel
def cuts74619 : List PrefixCut := [⟨64,164981883,164981983⟩]
theorem checked74619 : checkPrefixCuts (2^48) 9784393729 10 Manual.Count131072.C074619.packed 64 cuts74619 = true := by
 decide +kernel
def cuts74620 : List PrefixCut := [⟨64,163196106,163196205⟩]
theorem checked74620 : checkPrefixCuts (2^48) 9784524801 10 Manual.Count131072.C074620.packed 64 cuts74620 = true := by
 decide +kernel
def cuts74621 : List PrefixCut := [⟨17,42546271,42546298⟩,
⟨64,163567884,163567986⟩]
theorem checked74621 : checkPrefixCuts (2^48) 9784655873 10 Manual.Count131072.C074621.packed 64 cuts74621 = true := by
 decide +kernel
def pointBounds74621 : List (Nat × Nat × Nat) := [(9784690688,116596805176285,116597195146480)]
theorem point_links_checked74621 : (cuts74621.take 1).map (fun c => (9784655873-1+2*2^10*c.k,116596762630014+c.lower,116597152600182+c.upper)) = pointBounds74621 := by
 decide +kernel
def cuts74622 : List PrefixCut := [⟨64,164054726,164054822⟩]
theorem checked74622 : checkPrefixCuts (2^48) 9784786945 10 Manual.Count131072.C074622.packed 64 cuts74622 = true := by
 decide +kernel
def cuts74623 : List PrefixCut := [⟨39,99703239,99703299⟩,
⟨64,164225128,164225227⟩]
theorem checked74623 : checkPrefixCuts (2^48) 9784918017 10 Manual.Count131072.C074623.packed 64 cuts74623 = true := by
 decide +kernel
def pointBounds74623 : List (Nat × Nat × Nat) := [(9784997888,116597189955863,116597579926289)]
theorem point_links_checked74623 : (cuts74623.take 1).map (fun c => (9784918017-1+2*2^10*c.k,116597090252624+c.lower,116597480222990+c.upper)) = pointBounds74623 := by
 decide +kernel
def cuts74624 : List PrefixCut := [⟨64,164510566,164510665⟩]
theorem checked74624 : checkPrefixCuts (2^48) 9785049089 10 Manual.Count131072.C074624.packed 64 cuts74624 = true := by
 decide +kernel
def cuts74625 : List PrefixCut := [⟨61,154411824,154411913⟩,
⟨64,162149622,162149717⟩]
theorem checked74625 : checkPrefixCuts (2^48) 9785180161 10 Manual.Count131072.C074625.packed 64 cuts74625 = true := by
 decide +kernel
def pointBounds74625 : List (Nat × Nat × Nat) := [(9785305088,116597573400142,116597963370795)]
theorem point_links_checked74625 : (cuts74625.take 1).map (fun c => (9785180161-1+2*2^10*c.k,116597418988318+c.lower,116597808958882+c.upper)) = pointBounds74625 := by
 decide +kernel
def cuts74626 : List PrefixCut := [⟨64,164477415,164477509⟩]
theorem checked74626 : checkPrefixCuts (2^48) 9785311233 10 Manual.Count131072.C074626.packed 64 cuts74626 = true := by
 decide +kernel
def cuts74627 : List PrefixCut := [⟨64,164849141,164849242⟩]
theorem checked74627 : checkPrefixCuts (2^48) 9785442305 10 Manual.Count131072.C074627.packed 64 cuts74627 = true := by
 decide +kernel
def cuts74628 : List PrefixCut := [⟨19,48755343,48755373⟩,
⟨64,163984016,163984119⟩]
theorem checked74628 : checkPrefixCuts (2^48) 9785573377 10 Manual.Count131072.C074628.packed 64 cuts74628 = true := by
 decide +kernel
def pointBounds74628 : List (Nat × Nat × Nat) := [(9785612288,116597959219839,116598349190723)]
theorem point_links_checked74628 : (cuts74628.take 1).map (fun c => (9785573377-1+2*2^10*c.k,116597910464496+c.lower,116598300435350+c.upper)) = pointBounds74628 := by
 decide +kernel
def cuts74629 : List PrefixCut := [⟨64,164442039,164442141⟩]
theorem checked74629 : checkPrefixCuts (2^48) 9785704449 10 Manual.Count131072.C074629.packed 64 cuts74629 = true := by
 decide +kernel
def cuts74630 : List PrefixCut := [⟨41,103778274,103778336⟩,
⟨64,162282594,162282690⟩]
theorem checked74630 : checkPrefixCuts (2^48) 9785835521 10 Manual.Count131072.C074630.packed 64 cuts74630 = true := by
 decide +kernel
def pointBounds74630 : List (Nat × Nat × Nat) := [(9785919488,116598342668825,116598732639946)]
theorem point_links_checked74630 : (cuts74630.take 1).map (fun c => (9785835521-1+2*2^10*c.k,116598238890551+c.lower,116598628861610+c.upper)) = pointBounds74630 := by
 decide +kernel
def cuts74631 : List PrefixCut := [⟨64,162194125,162194225⟩]
theorem checked74631 : checkPrefixCuts (2^48) 9785966593 10 Manual.Count131072.C074631.packed 64 cuts74631 = true := by
 decide +kernel
def cuts74632 : List PrefixCut := [⟨63,161961866,161961969⟩,
⟨64,164924388,164924493⟩]
theorem checked74632 : checkPrefixCuts (2^48) 9786097665 10 Manual.Count131072.C074632.packed 64 cuts74632 = true := by
 decide +kernel
def pointBounds74632 : List (Nat × Nat × Nat) := [(9786226688,116598725329136,116599115300494)]
theorem point_links_checked74632 : (cuts74632.take 1).map (fun c => (9786097665-1+2*2^10*c.k,116598563367270+c.lower,116598953338525+c.upper)) = pointBounds74632 := by
 decide +kernel
def cuts74633 : List PrefixCut := [⟨64,165468669,165468765⟩]
theorem checked74633 : checkPrefixCuts (2^48) 9786228737 10 Manual.Count131072.C074633.packed 64 cuts74633 = true := by
 decide +kernel
def cuts74634 : List PrefixCut := [⟨64,161037141,161037236⟩]
theorem checked74634 : checkPrefixCuts (2^48) 9786359809 10 Manual.Count131072.C074634.packed 64 cuts74634 = true := by
 decide +kernel
def cuts74635 : List PrefixCut := [⟨21,54388020,54388054⟩,
⟨64,165377948,165378051⟩]
theorem checked74635 : checkPrefixCuts (2^48) 9786490881 10 Manual.Count131072.C074635.packed 64 cuts74635 = true := by
 decide +kernel
def pointBounds74635 : List (Nat × Nat × Nat) := [(9786533888,116599109185488,116599499157073)]
theorem point_links_checked74635 : (cuts74635.take 1).map (fun c => (9786490881-1+2*2^10*c.k,116599054797468+c.lower,116599444769019+c.upper)) = pointBounds74635 := by
 decide +kernel
def cuts74636 : List PrefixCut := [⟨64,163707596,163707699⟩]
theorem checked74636 : checkPrefixCuts (2^48) 9786621953 10 Manual.Count131072.C074636.packed 64 cuts74636 = true := by
 decide +kernel
def cuts74637 : List PrefixCut := [⟨43,110527278,110527346⟩,
⟨64,164481943,164482044⟩]
theorem checked74637 : checkPrefixCuts (2^48) 9786753025 10 Manual.Count131072.C074637.packed 64 cuts74637 = true := by
 decide +kernel
def pointBounds74637 : List (Nat × Nat × Nat) := [(9786841088,116599494410290,116599884382115)]
theorem point_links_checked74637 : (cuts74637.take 1).map (fun c => (9786753025-1+2*2^10*c.k,116599383883012+c.lower,116599773854769+c.upper)) = pointBounds74637 := by
 decide +kernel
def cuts74638 : List PrefixCut := [⟨64,165083712,165083809⟩]
theorem checked74638 : checkPrefixCuts (2^48) 9786884097 10 Manual.Count131072.C074638.packed 64 cuts74638 = true := by
 decide +kernel
def cuts74639 : List PrefixCut := [⟨64,166318166,166318267⟩]
theorem checked74639 : checkPrefixCuts (2^48) 9787015169 10 Manual.Count131072.C074639.packed 64 cuts74639 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000144
