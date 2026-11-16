import PlattAssemblyKernel
import PlattCertificates.Count131072.C070736
import PlattCertificates.Count131072.C070737
import PlattCertificates.Count131072.C070738
import PlattCertificates.Count131072.C070739
import PlattCertificates.Count131072.C070740
import PlattCertificates.Count131072.C070741
import PlattCertificates.Count131072.C070742
import PlattCertificates.Count131072.C070743
import PlattCertificates.Count131072.C070744
import PlattCertificates.Count131072.C070745
import PlattCertificates.Count131072.C070746
import PlattCertificates.Count131072.C070747
import PlattCertificates.Count131072.C070748
import PlattCertificates.Count131072.C070749
import PlattCertificates.Count131072.C070750
import PlattCertificates.Count131072.C070751
import PlattCertificates.Count131072.C070752
import PlattCertificates.Count131072.C070753
import PlattCertificates.Count131072.C070754
import PlattCertificates.Count131072.C070755
import PlattCertificates.Count131072.C070756
import PlattCertificates.Count131072.C070757
import PlattCertificates.Count131072.C070758
import PlattCertificates.Count131072.C070759
import PlattCertificates.Count131072.C070760
import PlattCertificates.Count131072.C070761
import PlattCertificates.Count131072.C070762
import PlattCertificates.Count131072.C070763
import PlattCertificates.Count131072.C070764
import PlattCertificates.Count131072.C070765
import PlattCertificates.Count131072.C070766
import PlattCertificates.Count131072.C070767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70736 : List PrefixCut := [⟨64,175035953,175036056⟩]
theorem checked70736 : checkPrefixCuts (2^48) 9275441153 10 Manual.Count131072.C070736.packed 64 cuts70736 = true := by
 decide +kernel
def cuts70737 : List PrefixCut := [⟨17,47187667,47187699⟩,
⟨64,175640397,175640510⟩]
theorem checked70737 : checkPrefixCuts (2^48) 9275572225 10 Manual.Count131072.C070737.packed 64 cuts70737 = true := by
 decide +kernel
def pointBounds70737 : List (Nat × Nat × Nat) := [(9275607040,115942237123430,115942626704281)]
theorem point_links_checked70737 : (cuts70737.take 1).map (fun c => (9275572225-1+2*2^10*c.k,115942189935763+c.lower,115942579516582+c.upper)) = pointBounds70737 := by
 decide +kernel
def cuts70738 : List PrefixCut := [⟨64,176184131,176184240⟩]
theorem checked70738 : checkPrefixCuts (2^48) 9275703297 10 Manual.Count131072.C070738.packed 64 cuts70738 = true := by
 decide +kernel
def cuts70739 : List PrefixCut := [⟨31,83023544,83023591⟩,
⟨64,174057495,174057600⟩]
theorem checked70739 : checkPrefixCuts (2^48) 9275834369 10 Manual.Count131072.C070739.packed 64 cuts70739 = true := by
 decide +kernel
def pointBounds70739 : List (Nat × Nat × Nat) := [(9275897856,115942624783835,115943014364923)]
theorem point_links_checked70739 : (cuts70739.take 1).map (fun c => (9275834369-1+2*2^10*c.k,115942541760291+c.lower,115942931341332+c.upper)) = pointBounds70739 := by
 decide +kernel
def cuts70740 : List PrefixCut := [⟨64,171324054,171324155⟩]
theorem checked70740 : checkPrefixCuts (2^48) 9275965441 10 Manual.Count131072.C070740.packed 64 cuts70740 = true := by
 decide +kernel
def cuts70741 : List PrefixCut := [⟨45,122407534,122407605⟩,
⟨64,173142276,173142376⟩]
theorem checked70741 : checkPrefixCuts (2^48) 9276096513 10 Manual.Count131072.C070741.packed 64 cuts70741 = true := by
 decide +kernel
def pointBounds70741 : List (Nat × Nat × Nat) := [(9276188672,115943009549374,115943399130692)]
theorem point_links_checked70741 : (cuts70741.take 1).map (fun c => (9276096513-1+2*2^10*c.k,115942887141840+c.lower,115943276723087+c.upper)) = pointBounds70741 := by
 decide +kernel
def cuts70742 : List PrefixCut := [⟨64,171744007,171744108⟩]
theorem checked70742 : checkPrefixCuts (2^48) 9276227585 10 Manual.Count131072.C070742.packed 64 cuts70742 = true := by
 decide +kernel
def cuts70743 : List PrefixCut := [⟨59,157389438,157389525⟩,
⟨64,170345830,170345926⟩]
theorem checked70743 : checkPrefixCuts (2^48) 9276358657 10 Manual.Count131072.C070743.packed 64 cuts70743 = true := by
 decide +kernel
def pointBounds70743 : List (Nat × Nat × Nat) := [(9276479488,115943389417561,115943778999096)]
theorem point_links_checked70743 : (cuts70743.take 1).map (fun c => (9276358657-1+2*2^10*c.k,115943232028123+c.lower,115943621609571+c.upper)) = pointBounds70743 := by
 decide +kernel
def cuts70744 : List PrefixCut := [⟨64,174257609,174257711⟩]
theorem checked70744 : checkPrefixCuts (2^48) 9276489729 10 Manual.Count131072.C070744.packed 64 cuts70744 = true := by
 decide +kernel
def cuts70745 : List PrefixCut := [⟨64,172131184,172131287⟩]
theorem checked70745 : checkPrefixCuts (2^48) 9276620801 10 Manual.Count131072.C070745.packed 64 cuts70745 = true := by
 decide +kernel
def cuts70746 : List PrefixCut := [⟨9,24789362,24789376⟩,
⟨64,172098418,172098524⟩]
theorem checked70746 : checkPrefixCuts (2^48) 9276751873 10 Manual.Count131072.C070746.packed 64 cuts70746 = true := by
 decide +kernel
def pointBounds70746 : List (Nat × Nat × Nat) := [(9276770304,115943773552108,115944163133871)]
theorem point_links_checked70746 : (cuts70746.take 1).map (fun c => (9276751873-1+2*2^10*c.k,115943748762746+c.lower,115944138344495+c.upper)) = pointBounds70746 := by
 decide +kernel
def cuts70747 : List PrefixCut := [⟨64,172095989,172096092⟩]
theorem checked70747 : checkPrefixCuts (2^48) 9276882945 10 Manual.Count131072.C070747.packed 64 cuts70747 = true := by
 decide +kernel
def cuts70748 : List PrefixCut := [⟨23,62745257,62745295⟩,
⟨64,172579010,172579118⟩]
theorem checked70748 : checkPrefixCuts (2^48) 9277014017 10 Manual.Count131072.C070748.packed 64 cuts70748 = true := by
 decide +kernel
def pointBounds70748 : List (Nat × Nat × Nat) := [(9277061120,115944155702410,115944545284406)]
theorem point_links_checked70748 : (cuts70748.take 1).map (fun c => (9277014017-1+2*2^10*c.k,115944092957153+c.lower,115944482539111+c.upper)) = pointBounds70748 := by
 decide +kernel
def cuts70749 : List PrefixCut := [⟨64,175246544,175246646⟩]
theorem checked70749 : checkPrefixCuts (2^48) 9277145089 10 Manual.Count131072.C070749.packed 64 cuts70749 = true := by
 decide +kernel
def cuts70750 : List PrefixCut := [⟨37,98908817,98908878⟩,
⟨64,172301072,172301173⟩]
theorem checked70750 : checkPrefixCuts (2^48) 9277276161 10 Manual.Count131072.C070750.packed 64 cuts70750 = true := by
 decide +kernel
def pointBounds70750 : List (Nat × Nat × Nat) := [(9277351936,115944539691524,115944929273753)]
theorem point_links_checked70750 : (cuts70750.take 1).map (fun c => (9277276161-1+2*2^10*c.k,115944440782707+c.lower,115944830364875+c.upper)) = pointBounds70750 := by
 decide +kernel
def cuts70751 : List PrefixCut := [⟨64,171722186,171722288⟩]
theorem checked70751 : checkPrefixCuts (2^48) 9277407233 10 Manual.Count131072.C070751.packed 64 cuts70751 = true := by
 decide +kernel
def cuts70752 : List PrefixCut := [⟨51,140956032,140956117⟩,
⟨64,176816741,176816847⟩]
theorem checked70752 : checkPrefixCuts (2^48) 9277538305 10 Manual.Count131072.C070752.packed 64 cuts70752 = true := by
 decide +kernel
def pointBounds70752 : List (Nat × Nat × Nat) := [(9277642752,115944925761997,115945315344453)]
theorem point_links_checked70752 : (cuts70752.take 1).map (fun c => (9277538305-1+2*2^10*c.k,115944784805965+c.lower,115945174388336+c.upper)) = pointBounds70752 := by
 decide +kernel
def cuts70753 : List PrefixCut := [⟨64,173659018,173659117⟩]
theorem checked70753 : checkPrefixCuts (2^48) 9277669377 10 Manual.Count131072.C070753.packed 64 cuts70753 = true := by
 decide +kernel
def cuts70754 : List PrefixCut := [⟨64,173959943,173960044⟩]
theorem checked70754 : checkPrefixCuts (2^48) 9277800449 10 Manual.Count131072.C070754.packed 64 cuts70754 = true := by
 decide +kernel
def cuts70755 : List PrefixCut := [⟨1,2700091,2700093⟩,
⟨64,175201343,175201449⟩]
theorem checked70755 : checkPrefixCuts (2^48) 9277931521 10 Manual.Count131072.C070755.packed 64 cuts70755 = true := by
 decide +kernel
def pointBounds70755 : List (Nat × Nat × Nat) := [(9277933568,115945311941758,115945701524437)]
theorem point_links_checked70755 : (cuts70755.take 1).map (fun c => (9277931521-1+2*2^10*c.k,115945309241667+c.lower,115945698824344+c.upper)) = pointBounds70755 := by
 decide +kernel
def cuts70756 : List PrefixCut := [⟨64,174228075,174228173⟩]
theorem checked70756 : checkPrefixCuts (2^48) 9278062593 10 Manual.Count131072.C070756.packed 64 cuts70756 = true := by
 decide +kernel
def cuts70757 : List PrefixCut := [⟨15,40196789,40196816⟩,
⟨64,172557056,172557165⟩]
theorem checked70757 : checkPrefixCuts (2^48) 9278193665 10 Manual.Count131072.C070757.packed 64 cuts70757 = true := by
 decide +kernel
def pointBounds70757 : List (Nat × Nat × Nat) := [(9278224384,115945698867874,115946088450782)]
theorem point_links_checked70757 : (cuts70757.take 1).map (fun c => (9278193665-1+2*2^10*c.k,115945658671085+c.lower,115946048253966+c.upper)) = pointBounds70757 := by
 decide +kernel
def cuts70758 : List PrefixCut := [⟨64,176801756,176801859⟩]
theorem checked70758 : checkPrefixCuts (2^48) 9278324737 10 Manual.Count131072.C070758.packed 64 cuts70758 = true := by
 decide +kernel
def cuts70759 : List PrefixCut := [⟨29,78024956,78024998⟩,
⟨64,173007224,173007327⟩]
theorem checked70759 : checkPrefixCuts (2^48) 9278455809 10 Manual.Count131072.C070759.packed 64 cuts70759 = true := by
 decide +kernel
def pointBounds70759 : List (Nat × Nat × Nat) := [(9278515200,115946086054853,115946475637988)]
theorem point_links_checked70759 : (cuts70759.take 1).map (fun c => (9278455809-1+2*2^10*c.k,115946008029897+c.lower,115946397612990+c.upper)) = pointBounds70759 := by
 decide +kernel
def cuts70760 : List PrefixCut := [⟨64,172580098,172580200⟩]
theorem checked70760 : checkPrefixCuts (2^48) 9278586881 10 Manual.Count131072.C070760.packed 64 cuts70760 = true := by
 decide +kernel
def cuts70761 : List PrefixCut := [⟨43,118095687,118095755⟩,
⟨64,173457386,173457490⟩]
theorem checked70761 : checkPrefixCuts (2^48) 9278717953 10 Manual.Count131072.C070761.packed 64 cuts70761 = true := by
 decide +kernel
def pointBounds70761 : List (Nat × Nat × Nat) := [(9278806016,115946471712906,115946861296272)]
theorem point_links_checked70761 : (cuts70761.take 1).map (fun c => (9278717953-1+2*2^10*c.k,115946353617219+c.lower,115946743200517+c.upper)) = pointBounds70761 := by
 decide +kernel
def cuts70762 : List PrefixCut := [⟨64,174637990,174638091⟩]
theorem checked70762 : checkPrefixCuts (2^48) 9278849025 10 Manual.Count131072.C070762.packed 64 cuts70762 = true := by
 decide +kernel
def cuts70763 : List PrefixCut := [⟨57,151915117,151915211⟩,
⟨64,170540362,170540468⟩]
theorem checked70763 : checkPrefixCuts (2^48) 9278980097 10 Manual.Count131072.C070763.packed 64 cuts70763 = true := by
 decide +kernel
def pointBounds70763 : List (Nat × Nat × Nat) := [(9279096832,115946853627712,115947243211309)]
theorem point_links_checked70763 : (cuts70763.take 1).map (fun c => (9278980097-1+2*2^10*c.k,115946701712595+c.lower,115947091296098+c.upper)) = pointBounds70763 := by
 decide +kernel
def cuts70764 : List PrefixCut := [⟨64,172540007,172540104⟩]
theorem checked70764 : checkPrefixCuts (2^48) 9279111169 10 Manual.Count131072.C070764.packed 64 cuts70764 = true := by
 decide +kernel
def cuts70765 : List PrefixCut := [⟨64,169564857,169564961⟩]
theorem checked70765 : checkPrefixCuts (2^48) 9279242241 10 Manual.Count131072.C070765.packed 64 cuts70765 = true := by
 decide +kernel
def cuts70766 : List PrefixCut := [⟨7,19140357,19140367⟩,
⟨64,172292460,172292562⟩]
theorem checked70766 : checkPrefixCuts (2^48) 9279373313 10 Manual.Count131072.C070766.packed 64 cuts70766 = true := by
 decide +kernel
def pointBounds70766 : List (Nat × Nat × Nat) := [(9279387648,115947233498178,115947623081998)]
theorem point_links_checked70766 : (cuts70766.take 1).map (fun c => (9279373313-1+2*2^10*c.k,115947214357821+c.lower,115947603941631+c.upper)) = pointBounds70766 := by
 decide +kernel
def cuts70767 : List PrefixCut := [⟨64,174625654,174625756⟩]
theorem checked70767 : checkPrefixCuts (2^48) 9279504385 10 Manual.Count131072.C070767.packed 64 cuts70767 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000023
