import PlattAssemblyKernel
import PlattCertificates.Count131072.C060672
import PlattCertificates.Count131072.C060673
import PlattCertificates.Count131072.C060674
import PlattCertificates.Count131072.C060675
import PlattCertificates.Count131072.C060676
import PlattCertificates.Count131072.C060677
import PlattCertificates.Count131072.C060678
import PlattCertificates.Count131072.C060679
import PlattCertificates.Count131072.C060680
import PlattCertificates.Count131072.C060681
import PlattCertificates.Count131072.C060682
import PlattCertificates.Count131072.C060683
import PlattCertificates.Count131072.C060684
import PlattCertificates.Count131072.C060685
import PlattCertificates.Count131072.C060686
import PlattCertificates.Count131072.C060687
import PlattCertificates.Count131072.C060688
import PlattCertificates.Count131072.C060689
import PlattCertificates.Count131072.C060690
import PlattCertificates.Count131072.C060691
import PlattCertificates.Count131072.C060692
import PlattCertificates.Count131072.C060693
import PlattCertificates.Count131072.C060694
import PlattCertificates.Count131072.C060695
import PlattCertificates.Count131072.C060696
import PlattCertificates.Count131072.C060697
import PlattCertificates.Count131072.C060698
import PlattCertificates.Count131072.C060699
import PlattCertificates.Count131072.C060700
import PlattCertificates.Count131072.C060701
import PlattCertificates.Count131072.C060702
import PlattCertificates.Count131072.C060703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60672 : List PrefixCut := [⟨64,205682920,205683035⟩]
theorem checked60672 : checkPrefixCuts (2^48) 7956332545 10 Manual.Count131072.C060672.packed 64 cuts60672 = true := by
 decide +kernel
def cuts60673 : List PrefixCut := [⟨44,140657700,140657782⟩,
⟨64,205113487,205113603⟩]
theorem checked60673 : checkPrefixCuts (2^48) 7956463617 10 Manual.Count131072.C060673.packed 64 cuts60673 = true := by
 decide +kernel
def pointBounds60673 : List (Nat × Nat × Nat) := [(7956553728,114054613509245,114055001995233)]
theorem point_links_checked60673 : (cuts60673.take 1).map (fun c => (7956463617-1+2*2^10*c.k,114054472851545+c.lower,114054861337451+c.upper)) = pointBounds60673 := by
 decide +kernel
def cuts60674 : List PrefixCut := [⟨64,203871938,203872061⟩]
theorem checked60674 : checkPrefixCuts (2^48) 7956594689 10 Manual.Count131072.C060674.packed 64 cuts60674 = true := by
 decide +kernel
def cuts60675 : List PrefixCut := [⟨38,120347607,120347680⟩,
⟨64,201746070,201746190⟩]
theorem checked60675 : checkPrefixCuts (2^48) 7956725761 10 Manual.Count131072.C060675.packed 64 cuts60675 = true := by
 decide +kernel
def pointBounds60675 : List (Nat × Nat × Nat) := [(7956803584,114055002184577,114055390670795)]
theorem point_links_checked60675 : (cuts60675.take 1).map (fun c => (7956725761-1+2*2^10*c.k,114054881836970+c.lower,114055270323115+c.upper)) = pointBounds60675 := by
 decide +kernel
def cuts60676 : List PrefixCut := [⟨64,203263849,203263967⟩]
theorem checked60676 : checkPrefixCuts (2^48) 7956856833 10 Manual.Count131072.C060676.packed 64 cuts60676 = true := by
 decide +kernel
def cuts60677 : List PrefixCut := [⟨32,102939521,102939582⟩,
⟨64,206267312,206267433⟩]
theorem checked60677 : checkPrefixCuts (2^48) 7956987905 10 Manual.Count131072.C060677.packed 64 cuts60677 = true := by
 decide +kernel
def pointBounds60677 : List (Nat × Nat × Nat) := [(7957053440,114055389786410,114055778272854)]
theorem point_links_checked60677 : (cuts60677.take 1).map (fun c => (7956987905-1+2*2^10*c.k,114055286846889+c.lower,114055675333272+c.upper)) = pointBounds60677 := by
 decide +kernel
def cuts60678 : List PrefixCut := [⟨64,201877571,201877688⟩]
theorem checked60678 : checkPrefixCuts (2^48) 7957118977 10 Manual.Count131072.C060678.packed 64 cuts60678 = true := by
 decide +kernel
def cuts60679 : List PrefixCut := [⟨26,82207483,82207530⟩,
⟨64,203112328,203112446⟩]
theorem checked60679 : checkPrefixCuts (2^48) 7957250049 10 Manual.Count131072.C060679.packed 64 cuts60679 = true := by
 decide +kernel
def pointBounds60679 : List (Nat × Nat × Nat) := [(7957303296,114055777199255,114056165685923)]
theorem point_links_checked60679 : (cuts60679.take 1).map (fun c => (7957250049-1+2*2^10*c.k,114055694991772+c.lower,114056083478393+c.upper)) = pointBounds60679 := by
 decide +kernel
def cuts60680 : List PrefixCut := [⟨64,202932108,202932226⟩]
theorem checked60680 : checkPrefixCuts (2^48) 7957381121 10 Manual.Count131072.C060680.packed 64 cuts60680 = true := by
 decide +kernel
def cuts60681 : List PrefixCut := [⟨20,64801744,64801783⟩,
⟨64,202681176,202681296⟩]
theorem checked60681 : checkPrefixCuts (2^48) 7957512193 10 Manual.Count131072.C060681.packed 64 cuts60681 = true := by
 decide +kernel
def pointBounds60681 : List (Nat × Nat × Nat) := [(7957553152,114056165837952,114056554324848)]
theorem point_links_checked60681 : (cuts60681.take 1).map (fun c => (7957512193-1+2*2^10*c.k,114056101036208+c.lower,114056489523065+c.upper)) = pointBounds60681 := by
 decide +kernel
def cuts60682 : List PrefixCut := [⟨64,202854696,202854813⟩]
theorem checked60682 : checkPrefixCuts (2^48) 7957643265 10 Manual.Count131072.C060682.packed 64 cuts60682 = true := by
 decide +kernel
def cuts60683 : List PrefixCut := [⟨14,46265259,46265285⟩,
⟨64,206459170,206459280⟩]
theorem checked60683 : checkPrefixCuts (2^48) 7957774337 10 Manual.Count131072.C060683.packed 64 cuts60683 = true := by
 decide +kernel
def pointBounds60683 : List (Nat × Nat × Nat) := [(7957803008,114056552837339,114056941324459)]
theorem point_links_checked60683 : (cuts60683.take 1).map (fun c => (7957774337-1+2*2^10*c.k,114056506572080+c.lower,114056895059174+c.upper)) = pointBounds60683 := by
 decide +kernel
def cuts60684 : List PrefixCut := [⟨64,206137422,206137540⟩]
theorem checked60684 : checkPrefixCuts (2^48) 7957905409 10 Manual.Count131072.C060684.packed 64 cuts60684 = true := by
 decide +kernel
def cuts60685 : List PrefixCut := [⟨8,25324818,25324830⟩,
⟨64,204224077,204224190⟩]
theorem checked60685 : checkPrefixCuts (2^48) 7958036481 10 Manual.Count131072.C060685.packed 64 cuts60685 = true := by
 decide +kernel
def pointBounds60685 : List (Nat × Nat × Nat) := [(7958052864,114056944493490,114057332980824)]
theorem point_links_checked60685 : (cuts60685.take 1).map (fun c => (7958036481-1+2*2^10*c.k,114056919168672+c.lower,114057307655994+c.upper)) = pointBounds60685 := by
 decide +kernel
def cuts60686 : List PrefixCut := [⟨64,202027827,202027938⟩]
theorem checked60686 : checkPrefixCuts (2^48) 7958167553 10 Manual.Count131072.C060686.packed 64 cuts60686 = true := by
 decide +kernel
def cuts60687 : List PrefixCut := [⟨2,6578582,6578585⟩,
⟨64,206233349,206233466⟩]
theorem checked60687 : checkPrefixCuts (2^48) 7958298625 10 Manual.Count131072.C060687.packed 64 cuts60687 = true := by
 decide +kernel
def pointBounds60687 : List (Nat × Nat × Nat) := [(7958302720,114057331999158,114057720486707)]
theorem point_links_checked60687 : (cuts60687.take 1).map (fun c => (7958298625-1+2*2^10*c.k,114057325420576+c.lower,114057713908122+c.upper)) = pointBounds60687 := by
 decide +kernel
def cuts60688 : List PrefixCut := [⟨60,191517028,191517136⟩,
⟨64,204885974,204886090⟩]
theorem checked60688 : checkPrefixCuts (2^48) 7958429697 10 Manual.Count131072.C060688.packed 64 cuts60688 = true := by
 decide +kernel
def pointBounds60688 : List (Nat × Nat × Nat) := [(7958552576,114057723170953,114058111658724)]
theorem point_links_checked60688 : (cuts60688.take 1).map (fun c => (7958429697-1+2*2^10*c.k,114057531653925+c.lower,114057920141588+c.upper)) = pointBounds60688 := by
 decide +kernel
def cuts60689 : List PrefixCut := [⟨64,204917975,204918090⟩]
theorem checked60689 : checkPrefixCuts (2^48) 7958560769 10 Manual.Count131072.C060689.packed 64 cuts60689 = true := by
 decide +kernel
def cuts60690 : List PrefixCut := [⟨54,171917699,171917801⟩,
⟨64,202297475,202297592⟩]
theorem checked60690 : checkPrefixCuts (2^48) 7958691841 10 Manual.Count131072.C060690.packed 64 cuts60690 = true := by
 decide +kernel
def pointBounds60690 : List (Nat × Nat × Nat) := [(7958802432,114058113375573,114058501863569)]
theorem point_links_checked60690 : (cuts60690.take 1).map (fun c => (7958691841-1+2*2^10*c.k,114057941457874+c.lower,114058329945768+c.upper)) = pointBounds60690 := by
 decide +kernel
def cuts60691 : List PrefixCut := [⟨64,204062433,204062551⟩]
theorem checked60691 : checkPrefixCuts (2^48) 7958822913 10 Manual.Count131072.C060691.packed 64 cuts60691 = true := by
 decide +kernel
def cuts60692 : List PrefixCut := [⟨48,151294032,151294117⟩,
⟨64,202255436,202255551⟩]
theorem checked60692 : checkPrefixCuts (2^48) 7958953985 10 Manual.Count131072.C060692.packed 64 cuts60692 = true := by
 decide +kernel
def pointBounds60692 : List (Nat × Nat × Nat) := [(7959052288,114058499111814,114058887600028)]
theorem point_links_checked60692 : (cuts60692.take 1).map (fun c => (7958953985-1+2*2^10*c.k,114058347817782+c.lower,114058736305911+c.upper)) = pointBounds60692 := by
 decide +kernel
def cuts60693 : List PrefixCut := [⟨64,205894694,205894813⟩]
theorem checked60693 : checkPrefixCuts (2^48) 7959085057 10 Manual.Count131072.C060693.packed 64 cuts60693 = true := by
 decide +kernel
def cuts60694 : List PrefixCut := [⟨42,131166781,131166856⟩,
⟨64,200834190,200834306⟩]
theorem checked60694 : checkPrefixCuts (2^48) 7959216129 10 Manual.Count131072.C060694.packed 64 cuts60694 = true := by
 decide +kernel
def pointBounds60694 : List (Nat × Nat × Nat) := [(7959302144,114058887134693,114059275623131)]
theorem point_links_checked60694 : (cuts60694.take 1).map (fun c => (7959216129-1+2*2^10*c.k,114058755967912+c.lower,114059144456275+c.upper)) = pointBounds60694 := by
 decide +kernel
def cuts60695 : List PrefixCut := [⟨64,204084362,204084477⟩]
theorem checked60695 : checkPrefixCuts (2^48) 7959347201 10 Manual.Count131072.C060695.packed 64 cuts60695 = true := by
 decide +kernel
def cuts60696 : List PrefixCut := [⟨36,112455368,112455433⟩,
⟨64,202489640,202489756⟩]
theorem checked60696 : checkPrefixCuts (2^48) 7959478273 10 Manual.Count131072.C060696.packed 64 cuts60696 = true := by
 decide +kernel
def pointBounds60696 : List (Nat × Nat × Nat) := [(7959552000,114059273341832,114059661830491)]
theorem point_links_checked60696 : (cuts60696.take 1).map (fun c => (7959478273-1+2*2^10*c.k,114059160886464+c.lower,114059549375058+c.upper)) = pointBounds60696 := by
 decide +kernel
def cuts60697 : List PrefixCut := [⟨64,205350686,205350807⟩]
theorem checked60697 : checkPrefixCuts (2^48) 7959609345 10 Manual.Count131072.C060697.packed 64 cuts60697 = true := by
 decide +kernel
def cuts60698 : List PrefixCut := [⟨30,93320807,93320863⟩,
⟨64,200644150,200644267⟩]
theorem checked60698 : checkPrefixCuts (2^48) 7959740417 10 Manual.Count131072.C060698.packed 64 cuts60698 = true := by
 decide +kernel
def pointBounds60698 : List (Nat × Nat × Nat) := [(7959801856,114059662047597,114060050536484)]
theorem point_links_checked60698 : (cuts60698.take 1).map (fun c => (7959740417-1+2*2^10*c.k,114059568726790+c.lower,114059957215621+c.upper)) = pointBounds60698 := by
 decide +kernel
def cuts60699 : List PrefixCut := [⟨64,204070930,204071042⟩]
theorem checked60699 : checkPrefixCuts (2^48) 7959871489 10 Manual.Count131072.C060699.packed 64 cuts60699 = true := by
 decide +kernel
def cuts60700 : List PrefixCut := [⟨24,76627389,76627432⟩,
⟨64,202900648,202900764⟩]
theorem checked60700 : checkPrefixCuts (2^48) 7960002561 10 Manual.Count131072.C060700.packed 64 cuts60700 = true := by
 decide +kernel
def pointBounds60700 : List (Nat × Nat × Nat) := [(7960051712,114060050069259,114060438558362)]
theorem point_links_checked60700 : (cuts60700.take 1).map (fun c => (7960002561-1+2*2^10*c.k,114059973441870+c.lower,114060361930930+c.upper)) = pointBounds60700 := by
 decide +kernel
def cuts60701 : List PrefixCut := [⟨64,203003374,203003491⟩]
theorem checked60701 : checkPrefixCuts (2^48) 7960133633 10 Manual.Count131072.C060701.packed 64 cuts60701 = true := by
 decide +kernel
def cuts60702 : List PrefixCut := [⟨18,57601296,57601329⟩,
⟨64,203070777,203070890⟩]
theorem checked60702 : checkPrefixCuts (2^48) 7960264705 10 Manual.Count131072.C060702.packed 64 cuts60702 = true := by
 decide +kernel
def pointBounds60702 : List (Nat × Nat × Nat) := [(7960301568,114060436947188,114060825436514)]
theorem point_links_checked60702 : (cuts60702.take 1).map (fun c => (7960264705-1+2*2^10*c.k,114060379345892+c.lower,114060767835185+c.upper)) = pointBounds60702 := by
 decide +kernel
def cuts60703 : List PrefixCut := [⟨64,200945860,200945974⟩]
theorem checked60703 : checkPrefixCuts (2^48) 7960395777 10 Manual.Count131072.C060703.packed 64 cuts60703 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000021
