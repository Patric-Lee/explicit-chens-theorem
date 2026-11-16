import PlattAssemblyKernel
import PlattCertificates.Count131072.C064672
import PlattCertificates.Count131072.C064673
import PlattCertificates.Count131072.C064674
import PlattCertificates.Count131072.C064675
import PlattCertificates.Count131072.C064676
import PlattCertificates.Count131072.C064677
import PlattCertificates.Count131072.C064678
import PlattCertificates.Count131072.C064679
import PlattCertificates.Count131072.C064680
import PlattCertificates.Count131072.C064681
import PlattCertificates.Count131072.C064682
import PlattCertificates.Count131072.C064683
import PlattCertificates.Count131072.C064684
import PlattCertificates.Count131072.C064685
import PlattCertificates.Count131072.C064686
import PlattCertificates.Count131072.C064687
import PlattCertificates.Count131072.C064688
import PlattCertificates.Count131072.C064689
import PlattCertificates.Count131072.C064690
import PlattCertificates.Count131072.C064691
import PlattCertificates.Count131072.C064692
import PlattCertificates.Count131072.C064693
import PlattCertificates.Count131072.C064694
import PlattCertificates.Count131072.C064695
import PlattCertificates.Count131072.C064696
import PlattCertificates.Count131072.C064697
import PlattCertificates.Count131072.C064698
import PlattCertificates.Count131072.C064699
import PlattCertificates.Count131072.C064700
import PlattCertificates.Count131072.C064701
import PlattCertificates.Count131072.C064702
import PlattCertificates.Count131072.C064703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000146
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64672 : List PrefixCut := [⟨64,187988756,187988866⟩]
theorem checked64672 : checkPrefixCuts (2^48) 8480620545 10 Manual.Count131072.C064672.packed 64 cuts64672 = true := by
 decide +kernel
def cuts64673 : List PrefixCut := [⟨48,142848288,142848376⟩,
⟨64,189446213,189446329⟩]
theorem checked64673 : checkPrefixCuts (2^48) 8480751617 10 Manual.Count131072.C064673.packed 64 cuts64673 = true := by
 decide +kernel
def pointBounds64673 : List (Nat × Nat × Nat) := [(8480849920,114841473975142,114841862913319)]
theorem point_links_checked64673 : (cuts64673.take 1).map (fun c => (8480751617-1+2*2^10*c.k,114841331126854+c.lower,114841720064943+c.upper)) = pointBounds64673 := by
 decide +kernel
def cuts64674 : List PrefixCut := [⟨64,193260038,193260147⟩]
theorem checked64674 : checkPrefixCuts (2^48) 8480882689 10 Manual.Count131072.C064674.packed 64 cuts64674 = true := by
 decide +kernel
def cuts64675 : List PrefixCut := [⟨50,149149702,149149785⟩,
⟨64,190070962,190071068⟩]
theorem checked64675 : checkPrefixCuts (2^48) 8481013761 10 Manual.Count131072.C064675.packed 64 cuts64675 = true := by
 decide +kernel
def pointBounds64675 : List (Nat × Nat × Nat) := [(8481116160,114841862982807,114842251921204)]
theorem point_links_checked64675 : (cuts64675.take 1).map (fun c => (8481013761-1+2*2^10*c.k,114841713833105+c.lower,114842102771419+c.upper)) = pointBounds64675 := by
 decide +kernel
def cuts64676 : List PrefixCut := [⟨64,191461899,191462011⟩]
theorem checked64676 : checkPrefixCuts (2^48) 8481144833 10 Manual.Count131072.C064676.packed 64 cuts64676 = true := by
 decide +kernel
def cuts64677 : List PrefixCut := [⟨52,154654175,154654264⟩,
⟨64,190098250,190098359⟩]
theorem checked64677 : checkPrefixCuts (2^48) 8481275905 10 Manual.Count131072.C064677.packed 64 cuts64677 = true := by
 decide +kernel
def pointBounds64677 : List (Nat × Nat × Nat) := [(8481382400,114842250020141,114842638958762)]
theorem point_links_checked64677 : (cuts64677.take 1).map (fun c => (8481275905-1+2*2^10*c.k,114842095365966+c.lower,114842484304498+c.upper)) = pointBounds64677 := by
 decide +kernel
def cuts64678 : List PrefixCut := [⟨64,190725876,190725987⟩]
theorem checked64678 : checkPrefixCuts (2^48) 8481406977 10 Manual.Count131072.C064678.packed 64 cuts64678 = true := by
 decide +kernel
def cuts64679 : List PrefixCut := [⟨54,162315457,162315553⟩,
⟨64,192514992,192515105⟩]
theorem checked64679 : checkPrefixCuts (2^48) 8481538049 10 Manual.Count131072.C064679.packed 64 cuts64679 = true := by
 decide +kernel
def pointBounds64679 : List (Nat × Nat × Nat) := [(8481648640,114842638505549,114843027444397)]
theorem point_links_checked64679 : (cuts64679.take 1).map (fun c => (8481538049-1+2*2^10*c.k,114842476190092+c.lower,114842865128844+c.upper)) = pointBounds64679 := by
 decide +kernel
def cuts64680 : List PrefixCut := [⟨64,189392554,189392660⟩]
theorem checked64680 : checkPrefixCuts (2^48) 8481669121 10 Manual.Count131072.C064680.packed 64 cuts64680 = true := by
 decide +kernel
def cuts64681 : List PrefixCut := [⟨56,167354611,167354709⟩,
⟨64,191082078,191082189⟩]
theorem checked64681 : checkPrefixCuts (2^48) 8481800193 10 Manual.Count131072.C064681.packed 64 cuts64681 = true := by
 decide +kernel
def pointBounds64681 : List (Nat × Nat × Nat) := [(8481914880,114843025452249,114843414391318)]
theorem point_links_checked64681 : (cuts64681.take 1).map (fun c => (8481800193-1+2*2^10*c.k,114842858097638+c.lower,114843247036609+c.upper)) = pointBounds64681 := by
 decide +kernel
def cuts64682 : List PrefixCut := [⟨64,191410951,191411063⟩]
theorem checked64682 : checkPrefixCuts (2^48) 8481931265 10 Manual.Count131072.C064682.packed 64 cuts64682 = true := by
 decide +kernel
def cuts64683 : List PrefixCut := [⟨58,171663372,171663471⟩,
⟨64,189981070,189981180⟩]
theorem checked64683 : checkPrefixCuts (2^48) 8482062337 10 Manual.Count131072.C064683.packed 64 cuts64683 = true := by
 decide +kernel
def pointBounds64683 : List (Nat × Nat × Nat) := [(8482181120,114843412254039,114843801193332)]
theorem point_links_checked64683 : (cuts64683.take 1).map (fun c => (8482062337-1+2*2^10*c.k,114843240590667+c.lower,114843629529861+c.upper)) = pointBounds64683 := by
 decide +kernel
def cuts64684 : List PrefixCut := [⟨64,191537786,191537893⟩]
theorem checked64684 : checkPrefixCuts (2^48) 8482193409 10 Manual.Count131072.C064684.packed 64 cuts64684 = true := by
 decide +kernel
def cuts64685 : List PrefixCut := [⟨60,176071426,176071528⟩,
⟨64,188017379,188017487⟩]
theorem checked64685 : checkPrefixCuts (2^48) 8482324481 10 Manual.Count131072.C064685.packed 64 cuts64685 = true := by
 decide +kernel
def pointBounds64685 : List (Nat × Nat × Nat) := [(8482447360,114843798180949,114844187120462)]
theorem point_links_checked64685 : (cuts64685.take 1).map (fun c => (8482324481-1+2*2^10*c.k,114843622109523+c.lower,114844011048934+c.upper)) = pointBounds64685 := by
 decide +kernel
def cuts64686 : List PrefixCut := [⟨64,189175866,189175978⟩]
theorem checked64686 : checkPrefixCuts (2^48) 8482455553 10 Manual.Count131072.C064686.packed 64 cuts64686 = true := by
 decide +kernel
def cuts64687 : List PrefixCut := [⟨62,184925656,184925765⟩,
⟨64,190832082,190832195⟩]
theorem checked64687 : checkPrefixCuts (2^48) 8482586625 10 Manual.Count131072.C064687.packed 64 cuts64687 = true := by
 decide +kernel
def pointBounds64687 : List (Nat × Nat × Nat) := [(8482713600,114844184228424,114844573168164)]
theorem point_links_checked64687 : (cuts64687.take 1).map (fun c => (8482586625-1+2*2^10*c.k,114843999302768+c.lower,114844388242399+c.upper)) = pointBounds64687 := by
 decide +kernel
def cuts64688 : List PrefixCut := [⟨64,190596853,190596968⟩]
theorem checked64688 : checkPrefixCuts (2^48) 8482717697 10 Manual.Count131072.C064688.packed 64 cuts64688 = true := by
 decide +kernel
def cuts64689 : List PrefixCut := [⟨64,190892544,190892650⟩]
theorem checked64689 : checkPrefixCuts (2^48) 8482848769 10 Manual.Count131072.C064689.packed 64 cuts64689 = true := by
 decide +kernel
def pointBounds64689 : List (Nat × Nat × Nat) := [(8482979840,114844571624247,114844960564212)]
theorem point_links_checked64689 : (cuts64689.take 1).map (fun c => (8482848769-1+2*2^10*c.k,114844380731703+c.lower,114844769671562+c.upper)) = pointBounds64689 := by
 decide +kernel
def cuts64690 : List PrefixCut := [⟨64,188301483,188301600⟩]
theorem checked64690 : checkPrefixCuts (2^48) 8482979841 10 Manual.Count131072.C064690.packed 64 cuts64690 = true := by
 decide +kernel
def cuts64691 : List PrefixCut := [⟨64,194370590,194370705⟩]
theorem checked64691 : checkPrefixCuts (2^48) 8483110913 10 Manual.Count131072.C064691.packed 64 cuts64691 = true := by
 decide +kernel
def cuts64692 : List PrefixCut := [⟨2,5673797,5673801⟩,
⟨64,194068959,194069073⟩]
theorem checked64692 : checkPrefixCuts (2^48) 8483241985 10 Manual.Count131072.C064692.packed 64 cuts64692 = true := by
 decide +kernel
def pointBounds64692 : List (Nat × Nat × Nat) := [(8483246080,114844959970117,114845348910318)]
theorem point_links_checked64692 : (cuts64692.take 1).map (fun c => (8483241985-1+2*2^10*c.k,114844954296320+c.lower,114845343236517+c.upper)) = pointBounds64692 := by
 decide +kernel
def cuts64693 : List PrefixCut := [⟨64,189653100,189653211⟩]
theorem checked64693 : checkPrefixCuts (2^48) 8483373057 10 Manual.Count131072.C064693.packed 64 cuts64693 = true := by
 decide +kernel
def cuts64694 : List PrefixCut := [⟨4,11679031,11679038⟩,
⟨64,190346925,190347039⟩]
theorem checked64694 : checkPrefixCuts (2^48) 8483504129 10 Manual.Count131072.C064694.packed 64 cuts64694 = true := by
 decide +kernel
def pointBounds64694 : List (Nat × Nat × Nat) := [(8483512320,114845349697410,114845738637839)]
theorem point_links_checked64694 : (cuts64694.take 1).map (fun c => (8483504129-1+2*2^10*c.k,114845338018379+c.lower,114845726958801+c.upper)) = pointBounds64694 := by
 decide +kernel
def cuts64695 : List PrefixCut := [⟨64,192102432,192102545⟩]
theorem checked64695 : checkPrefixCuts (2^48) 8483635201 10 Manual.Count131072.C064695.packed 64 cuts64695 = true := by
 decide +kernel
def cuts64696 : List PrefixCut := [⟨6,17982495,17982505⟩,
⟨64,188947591,188947705⟩]
theorem checked64696 : checkPrefixCuts (2^48) 8483766273 10 Manual.Count131072.C064696.packed 64 cuts64696 = true := by
 decide +kernel
def pointBounds64696 : List (Nat × Nat × Nat) := [(8483778560,114845738450231,114846127390890)]
theorem point_links_checked64696 : (cuts64696.take 1).map (fun c => (8483766273-1+2*2^10*c.k,114845720467736+c.lower,114846109408385+c.upper)) = pointBounds64696 := by
 decide +kernel
def cuts64697 : List PrefixCut := [⟨64,191731552,191731664⟩]
theorem checked64697 : checkPrefixCuts (2^48) 8483897345 10 Manual.Count131072.C064697.packed 64 cuts64697 = true := by
 decide +kernel
def cuts64698 : List PrefixCut := [⟨8,23522494,23522507⟩,
⟨64,186353958,186354068⟩]
theorem checked64698 : checkPrefixCuts (2^48) 8484028417 10 Manual.Count131072.C064698.packed 64 cuts64698 = true := by
 decide +kernel
def pointBounds64698 : List (Nat × Nat × Nat) := [(8484044800,114846124669373,114846513610261)]
theorem point_links_checked64698 : (cuts64698.take 1).map (fun c => (8484028417-1+2*2^10*c.k,114846101146879+c.lower,114846490087754+c.upper)) = pointBounds64698 := by
 decide +kernel
def cuts64699 : List PrefixCut := [⟨64,190730336,190730449⟩]
theorem checked64699 : checkPrefixCuts (2^48) 8484159489 10 Manual.Count131072.C064699.packed 64 cuts64699 = true := by
 decide +kernel
def cuts64700 : List PrefixCut := [⟨10,29228028,29228046⟩,
⟨64,189201304,189201414⟩]
theorem checked64700 : checkPrefixCuts (2^48) 8484290561 10 Manual.Count131072.C064700.packed 64 cuts64700 = true := by
 decide +kernel
def pointBounds64700 : List (Nat × Nat × Nat) := [(8484311040,114846507459201,114846896400317)]
theorem point_links_checked64700 : (cuts64700.take 1).map (fun c => (8484290561-1+2*2^10*c.k,114846478231173+c.lower,114846867172271+c.upper)) = pointBounds64700 := by
 decide +kernel
def cuts64701 : List PrefixCut := [⟨64,191023022,191023127⟩]
theorem checked64701 : checkPrefixCuts (2^48) 8484421633 10 Manual.Count131072.C064701.packed 64 cuts64701 = true := by
 decide +kernel
def cuts64702 : List PrefixCut := [⟨12,35994806,35994826⟩,
⟨64,191749925,191750040⟩]
theorem checked64702 : checkPrefixCuts (2^48) 8484552705 10 Manual.Count131072.C064702.packed 64 cuts64702 = true := by
 decide +kernel
def pointBounds64702 : List (Nat × Nat × Nat) := [(8484577280,114846894450305,114847283391638)]
theorem point_links_checked64702 : (cuts64702.take 1).map (fun c => (8484552705-1+2*2^10*c.k,114846858455499+c.lower,114847247396812+c.upper)) = pointBounds64702 := by
 decide +kernel
def cuts64703 : List PrefixCut := [⟨64,188993507,188993611⟩]
theorem checked64703 : checkPrefixCuts (2^48) 8484683777 10 Manual.Count131072.C064703.packed 64 cuts64703 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000146
