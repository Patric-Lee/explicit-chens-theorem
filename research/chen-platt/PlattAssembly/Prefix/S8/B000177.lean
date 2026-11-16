import PlattAssemblyKernel
import PlattCertificates.Count131072.C075664
import PlattCertificates.Count131072.C075665
import PlattCertificates.Count131072.C075666
import PlattCertificates.Count131072.C075667
import PlattCertificates.Count131072.C075668
import PlattCertificates.Count131072.C075669
import PlattCertificates.Count131072.C075670
import PlattCertificates.Count131072.C075671
import PlattCertificates.Count131072.C075672
import PlattCertificates.Count131072.C075673
import PlattCertificates.Count131072.C075674
import PlattCertificates.Count131072.C075675
import PlattCertificates.Count131072.C075676
import PlattCertificates.Count131072.C075677
import PlattCertificates.Count131072.C075678
import PlattCertificates.Count131072.C075679
import PlattCertificates.Count131072.C075680
import PlattCertificates.Count131072.C075681
import PlattCertificates.Count131072.C075682
import PlattCertificates.Count131072.C075683
import PlattCertificates.Count131072.C075684
import PlattCertificates.Count131072.C075685
import PlattCertificates.Count131072.C075686
import PlattCertificates.Count131072.C075687
import PlattCertificates.Count131072.C075688
import PlattCertificates.Count131072.C075689
import PlattCertificates.Count131072.C075690
import PlattCertificates.Count131072.C075691
import PlattCertificates.Count131072.C075692
import PlattCertificates.Count131072.C075693
import PlattCertificates.Count131072.C075694
import PlattCertificates.Count131072.C075695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000177
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75664 : List PrefixCut := [⟨64,160519708,160519799⟩]
theorem checked75664 : checkPrefixCuts (2^48) 9921363969 10 Manual.Count131072.C075664.packed 64 cuts75664 = true := by
 decide +kernel
def cuts75665 : List PrefixCut := [⟨27,69620304,69620340⟩,
⟨64,165567453,165567544⟩]
theorem checked75665 : checkPrefixCuts (2^48) 9921495041 10 Manual.Count131072.C075665.packed 64 cuts75665 = true := by
 decide +kernel
def pointBounds75665 : List (Nat × Nat × Nat) := [(9921550336,116766712663052,116767102735348)]
theorem point_links_checked75665 : (cuts75665.take 1).map (fun c => (9921495041-1+2*2^10*c.k,116766643042748+c.lower,116767033115008+c.upper)) = pointBounds75665 := by
 decide +kernel
def cuts75666 : List PrefixCut := [⟨64,160288507,160288610⟩]
theorem checked75666 : checkPrefixCuts (2^48) 9921626113 10 Manual.Count131072.C075666.packed 64 cuts75666 = true := by
 decide +kernel
def cuts75667 : List PrefixCut := [⟨51,129846335,129846415⟩,
⟨64,162272241,162272343⟩]
theorem checked75667 : checkPrefixCuts (2^48) 9921757185 10 Manual.Count131072.C075667.packed 64 cuts75667 = true := by
 decide +kernel
def pointBounds75667 : List (Nat × Nat × Nat) := [(9921861632,116767098745043,116767488817577)]
theorem point_links_checked75667 : (cuts75667.take 1).map (fun c => (9921757185-1+2*2^10*c.k,116766968898708+c.lower,116767358971162+c.upper)) = pointBounds75667 := by
 decide +kernel
def cuts75668 : List PrefixCut := [⟨64,160170791,160170892⟩]
theorem checked75668 : checkPrefixCuts (2^48) 9921888257 10 Manual.Count131072.C075668.packed 64 cuts75668 = true := by
 decide +kernel
def cuts75669 : List PrefixCut := [⟨64,160367267,160367368⟩]
theorem checked75669 : checkPrefixCuts (2^48) 9922019329 10 Manual.Count131072.C075669.packed 64 cuts75669 = true := by
 decide +kernel
def cuts75670 : List PrefixCut := [⟨11,28112989,28113006⟩,
⟨64,160677190,160677286⟩]
theorem checked75670 : checkPrefixCuts (2^48) 9922150401 10 Manual.Count131072.C075670.packed 64 cuts75670 = true := by
 decide +kernel
def pointBounds75670 : List (Nat × Nat × Nat) := [(9922172928,116767479821996,116767869894771)]
theorem point_links_checked75670 : (cuts75670.take 1).map (fun c => (9922150401-1+2*2^10*c.k,116767451709007+c.lower,116767841781765+c.upper)) = pointBounds75670 := by
 decide +kernel
def cuts75671 : List PrefixCut := [⟨64,160334658,160334749⟩]
theorem checked75671 : checkPrefixCuts (2^48) 9922281473 10 Manual.Count131072.C075671.packed 64 cuts75671 = true := by
 decide +kernel
def cuts75672 : List PrefixCut := [⟨35,87371848,87371900⟩,
⟨64,161580696,161580789⟩]
theorem checked75672 : checkPrefixCuts (2^48) 9922412545 10 Manual.Count131072.C075672.packed 64 cuts75672 = true := by
 decide +kernel
def pointBounds75672 : List (Nat × Nat × Nat) := [(9922484224,116767860092703,116768250165700)]
theorem point_links_checked75672 : (cuts75672.take 1).map (fun c => (9922412545-1+2*2^10*c.k,116767772720855+c.lower,116768162793800+c.upper)) = pointBounds75672 := by
 decide +kernel
def cuts75673 : List PrefixCut := [⟨64,160926126,160926218⟩]
theorem checked75673 : checkPrefixCuts (2^48) 9922543617 10 Manual.Count131072.C075673.packed 64 cuts75673 = true := by
 decide +kernel
def cuts75674 : List PrefixCut := [⟨59,148329276,148329371⟩,
⟨64,160186464,160186565⟩]
theorem checked75674 : checkPrefixCuts (2^48) 9922674689 10 Manual.Count131072.C075674.packed 64 cuts75674 = true := by
 decide +kernel
def pointBounds75674 : List (Nat × Nat × Nat) := [(9922795520,116768243556953,116768633630178)]
theorem point_links_checked75674 : (cuts75674.take 1).map (fun c => (9922674689-1+2*2^10*c.k,116768095227677+c.lower,116768485300807+c.upper)) = pointBounds75674 := by
 decide +kernel
def cuts75675 : List PrefixCut := [⟨64,161914693,161914791⟩]
theorem checked75675 : checkPrefixCuts (2^48) 9922805761 10 Manual.Count131072.C075675.packed 64 cuts75675 = true := by
 decide +kernel
def cuts75676 : List PrefixCut := [⟨64,161487069,161487161⟩]
theorem checked75676 : checkPrefixCuts (2^48) 9922936833 10 Manual.Count131072.C075676.packed 64 cuts75676 = true := by
 decide +kernel
def cuts75677 : List PrefixCut := [⟨19,45611977,45612006⟩,
⟨64,159556064,159556161⟩]
theorem checked75677 : checkPrefixCuts (2^48) 9923067905 10 Manual.Count131072.C075677.packed 64 cuts75677 = true := by
 decide +kernel
def pointBounds75677 : List (Nat × Nat × Nat) := [(9923106816,116768624427880,116769014501330)]
theorem point_links_checked75677 : (cuts75677.take 1).map (fun c => (9923067905-1+2*2^10*c.k,116768578815903+c.lower,116768968889324+c.upper)) = pointBounds75677 := by
 decide +kernel
def cuts75678 : List PrefixCut := [⟨64,161511163,161511262⟩]
theorem checked75678 : checkPrefixCuts (2^48) 9923198977 10 Manual.Count131072.C075678.packed 64 cuts75678 = true := by
 decide +kernel
def cuts75679 : List PrefixCut := [⟨43,110112295,110112362⟩,
⟨64,163267648,163267747⟩]
theorem checked75679 : checkPrefixCuts (2^48) 9923330049 10 Manual.Count131072.C075679.packed 64 cuts75679 = true := by
 decide +kernel
def pointBounds75679 : List (Nat × Nat × Nat) := [(9923418112,116769009995425,116769400069109)]
theorem point_links_checked75679 : (cuts75679.take 1).map (fun c => (9923330049-1+2*2^10*c.k,116768899883130+c.lower,116769289956747+c.upper)) = pointBounds75679 := by
 decide +kernel
def cuts75680 : List PrefixCut := [⟨64,163038575,163038671⟩]
theorem checked75680 : checkPrefixCuts (2^48) 9923461121 10 Manual.Count131072.C075680.packed 64 cuts75680 = true := by
 decide +kernel
def cuts75681 : List PrefixCut := [⟨64,161930234,161930325⟩]
theorem checked75681 : checkPrefixCuts (2^48) 9923592193 10 Manual.Count131072.C075681.packed 64 cuts75681 = true := by
 decide +kernel
def cuts75682 : List PrefixCut := [⟨3,7913508,7913514⟩,
⟨64,161644455,161644556⟩]
theorem checked75682 : checkPrefixCuts (2^48) 9923723265 10 Manual.Count131072.C075682.packed 64 cuts75682 = true := by
 decide +kernel
def pointBounds75682 : List (Nat × Nat × Nat) := [(9923729408,116769396033095,116769786107004)]
theorem point_links_checked75682 : (cuts75682.take 1).map (fun c => (9923723265-1+2*2^10*c.k,116769388119587+c.lower,116769778193490+c.upper)) = pointBounds75682 := by
 decide +kernel
def cuts75683 : List PrefixCut := [⟨64,161358682,161358776⟩]
theorem checked75683 : checkPrefixCuts (2^48) 9923854337 10 Manual.Count131072.C075683.packed 64 cuts75683 = true := by
 decide +kernel
def cuts75684 : List PrefixCut := [⟨27,68298127,68298167⟩,
⟨64,161186377,161186468⟩]
theorem checked75684 : checkPrefixCuts (2^48) 9923985409 10 Manual.Count131072.C075684.packed 64 cuts75684 = true := by
 decide +kernel
def pointBounds75684 : List (Nat × Nat × Nat) := [(9924040704,116769779420851,116770169494989)]
theorem point_links_checked75684 : (cuts75684.take 1).map (fun c => (9923985409-1+2*2^10*c.k,116769711122724+c.lower,116770101196822+c.upper)) = pointBounds75684 := by
 decide +kernel
def cuts75685 : List PrefixCut := [⟨64,163878699,163878794⟩]
theorem checked75685 : checkPrefixCuts (2^48) 9924116481 10 Manual.Count131072.C075685.packed 64 cuts75685 = true := by
 decide +kernel
def cuts75686 : List PrefixCut := [⟨51,128253832,128253907⟩,
⟨64,161522462,161522557⟩]
theorem checked75686 : checkPrefixCuts (2^48) 9924247553 10 Manual.Count131072.C075686.packed 64 cuts75686 = true := by
 decide +kernel
def pointBounds75686 : List (Nat × Nat × Nat) := [(9924352000,116770164441632,116770554515991)]
theorem point_links_checked75686 : (cuts75686.take 1).map (fun c => (9924247553-1+2*2^10*c.k,116770036187800+c.lower,116770426262084+c.upper)) = pointBounds75686 := by
 decide +kernel
def cuts75687 : List PrefixCut := [⟨64,161974109,161974207⟩]
theorem checked75687 : checkPrefixCuts (2^48) 9924378625 10 Manual.Count131072.C075687.packed 64 cuts75687 = true := by
 decide +kernel
def cuts75688 : List PrefixCut := [⟨64,161971973,161972076⟩]
theorem checked75688 : checkPrefixCuts (2^48) 9924509697 10 Manual.Count131072.C075688.packed 64 cuts75688 = true := by
 decide +kernel
def cuts75689 : List PrefixCut := [⟨11,27623793,27623812⟩,
⟨64,157885855,157885950⟩]
theorem checked75689 : checkPrefixCuts (2^48) 9924640769 10 Manual.Count131072.C075689.packed 64 cuts75689 = true := by
 decide +kernel
def pointBounds75689 : List (Nat × Nat × Nat) := [(9924663296,116770549280137,116770939354736)]
theorem point_links_checked75689 : (cuts75689.take 1).map (fun c => (9924640769-1+2*2^10*c.k,116770521656344+c.lower,116770911730924+c.upper)) = pointBounds75689 := by
 decide +kernel
def cuts75690 : List PrefixCut := [⟨64,162137866,162137966⟩]
theorem checked75690 : checkPrefixCuts (2^48) 9924771841 10 Manual.Count131072.C075690.packed 64 cuts75690 = true := by
 decide +kernel
def cuts75691 : List PrefixCut := [⟨35,87605174,87605221⟩,
⟨64,160802798,160802890⟩]
theorem checked75691 : checkPrefixCuts (2^48) 9924902913 10 Manual.Count131072.C075691.packed 64 cuts75691 = true := by
 decide +kernel
def pointBounds75691 : List (Nat × Nat × Nat) := [(9924974592,116770929285239,116771319360061)]
theorem point_links_checked75691 : (cuts75691.take 1).map (fun c => (9924902913-1+2*2^10*c.k,116770841680065+c.lower,116771231754840+c.upper)) = pointBounds75691 := by
 decide +kernel
def cuts75692 : List PrefixCut := [⟨64,160205108,160205205⟩]
theorem checked75692 : checkPrefixCuts (2^48) 9925033985 10 Manual.Count131072.C075692.packed 64 cuts75692 = true := by
 decide +kernel
def cuts75693 : List PrefixCut := [⟨59,149993644,149993735⟩,
⟨64,162982230,162982330⟩]
theorem checked75693 : checkPrefixCuts (2^48) 9925165057 10 Manual.Count131072.C075693.packed 64 cuts75693 = true := by
 decide +kernel
def pointBounds75693 : List (Nat × Nat × Nat) := [(9925285888,116771312681615,116771702756670)]
theorem point_links_checked75693 : (cuts75693.take 1).map (fun c => (9925165057-1+2*2^10*c.k,116771162687971+c.lower,116771552762935+c.upper)) = pointBounds75693 := by
 decide +kernel
def cuts75694 : List PrefixCut := [⟨64,160682989,160683087⟩]
theorem checked75694 : checkPrefixCuts (2^48) 9925296129 10 Manual.Count131072.C075694.packed 64 cuts75694 = true := by
 decide +kernel
def cuts75695 : List PrefixCut := [⟨64,158780832,158780925⟩]
theorem checked75695 : checkPrefixCuts (2^48) 9925427201 10 Manual.Count131072.C075695.packed 64 cuts75695 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000177
