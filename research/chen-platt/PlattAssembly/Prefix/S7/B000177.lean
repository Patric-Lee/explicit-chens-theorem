import PlattAssemblyKernel
import PlattCertificates.Count131072.C065664
import PlattCertificates.Count131072.C065665
import PlattCertificates.Count131072.C065666
import PlattCertificates.Count131072.C065667
import PlattCertificates.Count131072.C065668
import PlattCertificates.Count131072.C065669
import PlattCertificates.Count131072.C065670
import PlattCertificates.Count131072.C065671
import PlattCertificates.Count131072.C065672
import PlattCertificates.Count131072.C065673
import PlattCertificates.Count131072.C065674
import PlattCertificates.Count131072.C065675
import PlattCertificates.Count131072.C065676
import PlattCertificates.Count131072.C065677
import PlattCertificates.Count131072.C065678
import PlattCertificates.Count131072.C065679
import PlattCertificates.Count131072.C065680
import PlattCertificates.Count131072.C065681
import PlattCertificates.Count131072.C065682
import PlattCertificates.Count131072.C065683
import PlattCertificates.Count131072.C065684
import PlattCertificates.Count131072.C065685
import PlattCertificates.Count131072.C065686
import PlattCertificates.Count131072.C065687
import PlattCertificates.Count131072.C065688
import PlattCertificates.Count131072.C065689
import PlattCertificates.Count131072.C065690
import PlattCertificates.Count131072.C065691
import PlattCertificates.Count131072.C065692
import PlattCertificates.Count131072.C065693
import PlattCertificates.Count131072.C065694
import PlattCertificates.Count131072.C065695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000177
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65664 : List PrefixCut := [⟨64,188255561,188255668⟩]
theorem checked65664 : checkPrefixCuts (2^48) 8610643969 10 Manual.Count131072.C065664.packed 64 cuts65664 = true := by
 decide +kernel
def cuts65665 : List PrefixCut := [⟨43,125981541,125981612⟩,
⟨64,185931824,185931931⟩]
theorem checked65665 : checkPrefixCuts (2^48) 8610775041 10 Manual.Count131072.C065665.packed 64 cuts65665 = true := by
 decide +kernel
def pointBounds65665 : List (Nat × Nat × Nat) := [(8610863104,115028772513980,115029161560682)]
theorem point_links_checked65665 : (cuts65665.take 1).map (fun c => (8610775041-1+2*2^10*c.k,115028646532439+c.lower,115029035579070+c.upper)) = pointBounds65665 := by
 decide +kernel
def cuts65666 : List PrefixCut := [⟨64,186451983,186452095⟩]
theorem checked65666 : checkPrefixCuts (2^48) 8610906113 10 Manual.Count131072.C065666.packed 64 cuts65666 = true := by
 decide +kernel
def cuts65667 : List PrefixCut := [⟨47,137777824,137777902⟩,
⟨64,187070208,187070315⟩]
theorem checked65667 : checkPrefixCuts (2^48) 8611037185 10 Manual.Count131072.C065667.packed 64 cuts65667 = true := by
 decide +kernel
def pointBounds65667 : List (Nat × Nat × Nat) := [(8611133440,115029156694070,115029545740998)]
theorem point_links_checked65667 : (cuts65667.take 1).map (fun c => (8611037185-1+2*2^10*c.k,115029018916246+c.lower,115029407963096+c.upper)) = pointBounds65667 := by
 decide +kernel
def cuts65668 : List PrefixCut := [⟨64,184615846,184615951⟩]
theorem checked65668 : checkPrefixCuts (2^48) 8611168257 10 Manual.Count131072.C065668.packed 64 cuts65668 = true := by
 decide +kernel
def cuts65669 : List PrefixCut := [⟨51,148037130,148037213⟩,
⟨64,185332138,185332241⟩]
theorem checked65669 : checkPrefixCuts (2^48) 8611299329 10 Manual.Count131072.C065669.packed 64 cuts65669 = true := by
 decide +kernel
def pointBounds65669 : List (Nat × Nat × Nat) := [(8611403776,115029538639430,115029927686575)]
theorem point_links_checked65669 : (cuts65669.take 1).map (fun c => (8611299329-1+2*2^10*c.k,115029390602300+c.lower,115029779649362+c.upper)) = pointBounds65669 := by
 decide +kernel
def cuts65670 : List PrefixCut := [⟨64,183923828,183923935⟩]
theorem checked65670 : checkPrefixCuts (2^48) 8611430401 10 Manual.Count131072.C065670.packed 64 cuts65670 = true := by
 decide +kernel
def cuts65671 : List PrefixCut := [⟨55,161433617,161433708⟩,
⟨64,188791158,188791265⟩]
theorem checked65671 : checkPrefixCuts (2^48) 8611561473 10 Manual.Count131072.C065671.packed 64 cuts65671 = true := by
 decide +kernel
def pointBounds65671 : List (Nat × Nat × Nat) := [(8611674112,115029921291883,115030310339246)]
theorem point_links_checked65671 : (cuts65671.take 1).map (fun c => (8611561473-1+2*2^10*c.k,115029759858266+c.lower,115030148905538+c.upper)) = pointBounds65671 := by
 decide +kernel
def cuts65672 : List PrefixCut := [⟨64,188265326,188265435⟩]
theorem checked65672 : checkPrefixCuts (2^48) 8611692545 10 Manual.Count131072.C065672.packed 64 cuts65672 = true := by
 decide +kernel
def cuts65673 : List PrefixCut := [⟨59,174633150,174633248⟩,
⟨64,189471788,189471895⟩]
theorem checked65673 : checkPrefixCuts (2^48) 8611823617 10 Manual.Count131072.C065673.packed 64 cuts65673 = true := by
 decide +kernel
def pointBounds65673 : List (Nat × Nat × Nat) := [(8611944448,115030311547900,115030700595486)]
theorem point_links_checked65673 : (cuts65673.take 1).map (fun c => (8611823617-1+2*2^10*c.k,115030136914750+c.lower,115030525962238+c.upper)) = pointBounds65673 := by
 decide +kernel
def cuts65674 : List PrefixCut := [⟨64,189011332,189011442⟩]
theorem checked65674 : checkPrefixCuts (2^48) 8611954689 10 Manual.Count131072.C065674.packed 64 cuts65674 = true := by
 decide +kernel
def cuts65675 : List PrefixCut := [⟨63,181556634,181556744⟩,
⟨64,185445937,185446049⟩]
theorem checked65675 : checkPrefixCuts (2^48) 8612085761 10 Manual.Count131072.C065675.packed 64 cuts65675 = true := by
 decide +kernel
def pointBounds65675 : List (Nat × Nat × Nat) := [(8612214784,115030696954504,115031086002319)]
theorem point_links_checked65675 : (cuts65675.take 1).map (fun c => (8612085761-1+2*2^10*c.k,115030515397870+c.lower,115030904445575+c.upper)) = pointBounds65675 := by
 decide +kernel
def cuts65676 : List PrefixCut := [⟨64,187600192,187600305⟩]
theorem checked65676 : checkPrefixCuts (2^48) 8612216833 10 Manual.Count131072.C065676.packed 64 cuts65676 = true := by
 decide +kernel
def cuts65677 : List PrefixCut := [⟨64,187989522,187989636⟩]
theorem checked65677 : checkPrefixCuts (2^48) 8612347905 10 Manual.Count131072.C065677.packed 64 cuts65677 = true := by
 decide +kernel
def cuts65678 : List PrefixCut := [⟨3,8726148,8726154⟩,
⟨64,185666247,185666362⟩]
theorem checked65678 : checkPrefixCuts (2^48) 8612478977 10 Manual.Count131072.C065678.packed 64 cuts65678 = true := by
 decide +kernel
def pointBounds65678 : List (Nat × Nat × Nat) := [(8612485120,115031085159669,115031474207719)]
theorem point_links_checked65678 : (cuts65678.take 1).map (fun c => (8612478977-1+2*2^10*c.k,115031076433521+c.lower,115031465481565+c.upper)) = pointBounds65678 := by
 decide +kernel
def cuts65679 : List PrefixCut := [⟨64,183865942,183866050⟩]
theorem checked65679 : checkPrefixCuts (2^48) 8612610049 10 Manual.Count131072.C065679.packed 64 cuts65679 = true := by
 decide +kernel
def cuts65680 : List PrefixCut := [⟨7,21340819,21340833⟩,
⟨64,188111676,188111787⟩]
theorem checked65680 : checkPrefixCuts (2^48) 8612741121 10 Manual.Count131072.C065680.packed 64 cuts65680 = true := by
 decide +kernel
def pointBounds65680 : List (Nat × Nat × Nat) := [(8612755456,115031467306529,115031856354810)]
theorem point_links_checked65680 : (cuts65680.take 1).map (fun c => (8612741121-1+2*2^10*c.k,115031445965710+c.lower,115031835013977+c.upper)) = pointBounds65680 := by
 decide +kernel
def cuts65681 : List PrefixCut := [⟨64,186703562,186703678⟩]
theorem checked65681 : checkPrefixCuts (2^48) 8612872193 10 Manual.Count131072.C065681.packed 64 cuts65681 = true := by
 decide +kernel
def cuts65682 : List PrefixCut := [⟨11,32418741,32418762⟩,
⟨64,188563469,188563572⟩]
theorem checked65682 : checkPrefixCuts (2^48) 8613003265 10 Manual.Count131072.C065682.packed 64 cuts65682 = true := by
 decide +kernel
def pointBounds65682 : List (Nat × Nat × Nat) := [(8613025792,115031853199689,115032242248204)]
theorem point_links_checked65682 : (cuts65682.take 1).map (fun c => (8613003265-1+2*2^10*c.k,115031820780948+c.lower,115032209829442+c.upper)) = pointBounds65682 := by
 decide +kernel
def cuts65683 : List PrefixCut := [⟨64,186273034,186273140⟩]
theorem checked65683 : checkPrefixCuts (2^48) 8613134337 10 Manual.Count131072.C065683.packed 64 cuts65683 = true := by
 decide +kernel
def cuts65684 : List PrefixCut := [⟨15,45489411,45489436⟩,
⟨64,189374707,189374816⟩]
theorem checked65684 : checkPrefixCuts (2^48) 8613265409 10 Manual.Count131072.C065684.packed 64 cuts65684 = true := by
 decide +kernel
def pointBounds65684 : List (Nat × Nat × Nat) := [(8613296128,115032241106862,115032630155590)]
theorem point_links_checked65684 : (cuts65684.take 1).map (fun c => (8613265409-1+2*2^10*c.k,115032195617451+c.lower,115032584666154+c.upper)) = pointBounds65684 := by
 decide +kernel
def cuts65685 : List PrefixCut := [⟨64,187999324,187999433⟩]
theorem checked65685 : checkPrefixCuts (2^48) 8613396481 10 Manual.Count131072.C065685.packed 64 cuts65685 = true := by
 decide +kernel
def cuts65686 : List PrefixCut := [⟨19,55520198,55520231⟩,
⟨64,186329895,186330002⟩]
theorem checked65686 : checkPrefixCuts (2^48) 8613527553 10 Manual.Count131072.C065686.packed 64 cuts65686 = true := by
 decide +kernel
def pointBounds65686 : List (Nat × Nat × Nat) := [(8613566464,115032628511680,115033017560634)]
theorem point_links_checked65686 : (cuts65686.take 1).map (fun c => (8613527553-1+2*2^10*c.k,115032572991482+c.lower,115032962040403+c.upper)) = pointBounds65686 := by
 decide +kernel
def cuts65687 : List PrefixCut := [⟨64,186849893,186849996⟩]
theorem checked65687 : checkPrefixCuts (2^48) 8613658625 10 Manual.Count131072.C065687.packed 64 cuts65687 = true := by
 decide +kernel
def cuts65688 : List PrefixCut := [⟨23,66759426,66759464⟩,
⟨64,188317509,188317620⟩]
theorem checked65688 : checkPrefixCuts (2^48) 8613789697 10 Manual.Count131072.C065688.packed 64 cuts65688 = true := by
 decide +kernel
def pointBounds65688 : List (Nat × Nat × Nat) := [(8613836800,115033012930696,115033401979865)]
theorem point_links_checked65688 : (cuts65688.take 1).map (fun c => (8613789697-1+2*2^10*c.k,115032946171270+c.lower,115033335220401+c.upper)) = pointBounds65688 := by
 decide +kernel
def cuts65689 : List PrefixCut := [⟨64,185765889,185765996⟩]
theorem checked65689 : checkPrefixCuts (2^48) 8613920769 10 Manual.Count131072.C065689.packed 64 cuts65689 = true := by
 decide +kernel
def cuts65690 : List PrefixCut := [⟨27,78259358,78259409⟩,
⟨64,189553457,189553571⟩]
theorem checked65690 : checkPrefixCuts (2^48) 8614051841 10 Manual.Count131072.C065690.packed 64 cuts65690 = true := by
 decide +kernel
def pointBounds65690 : List (Nat × Nat × Nat) := [(8614107136,115033398514026,115033787563426)]
theorem point_links_checked65690 : (cuts65690.take 1).map (fun c => (8614051841-1+2*2^10*c.k,115033320254668+c.lower,115033709304017+c.upper)) = pointBounds65690 := by
 decide +kernel
def cuts65691 : List PrefixCut := [⟨64,183244228,183244341⟩]
theorem checked65691 : checkPrefixCuts (2^48) 8614182913 10 Manual.Count131072.C065691.packed 64 cuts65691 = true := by
 decide +kernel
def cuts65692 : List PrefixCut := [⟨31,90379423,90379472⟩,
⟨64,188240703,188240809⟩]
theorem checked65692 : checkPrefixCuts (2^48) 8614313985 10 Manual.Count131072.C065692.packed 64 cuts65692 = true := by
 decide +kernel
def pointBounds65692 : List (Nat × Nat × Nat) := [(8614377472,115033783431776,115034172481401)]
theorem point_links_checked65692 : (cuts65692.take 1).map (fun c => (8614313985-1+2*2^10*c.k,115033693052353+c.lower,115034082101929+c.upper)) = pointBounds65692 := by
 decide +kernel
def cuts65693 : List PrefixCut := [⟨64,189806208,189806321⟩]
theorem checked65693 : checkPrefixCuts (2^48) 8614445057 10 Manual.Count131072.C065693.packed 64 cuts65693 = true := by
 decide +kernel
def cuts65694 : List PrefixCut := [⟨35,102923489,102923548⟩,
⟨64,187581498,187581606⟩]
theorem checked65694 : checkPrefixCuts (2^48) 8614576129 10 Manual.Count131072.C065694.packed 64 cuts65694 = true := by
 decide +kernel
def pointBounds65694 : List (Nat × Nat × Nat) := [(8614647808,115034174022753,115034563072607)]
theorem point_links_checked65694 : (cuts65694.take 1).map (fun c => (8614576129-1+2*2^10*c.k,115034071099264+c.lower,115034460149059+c.upper)) = pointBounds65694 := by
 decide +kernel
def cuts65695 : List PrefixCut := [⟨64,186631097,186631204⟩]
theorem checked65695 : checkPrefixCuts (2^48) 8614707201 10 Manual.Count131072.C065695.packed 64 cuts65695 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000177
