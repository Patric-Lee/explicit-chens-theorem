import PlattAssemblyKernel
import PlattCertificates.Count131072.C069664
import PlattCertificates.Count131072.C069665
import PlattCertificates.Count131072.C069666
import PlattCertificates.Count131072.C069667
import PlattCertificates.Count131072.C069668
import PlattCertificates.Count131072.C069669
import PlattCertificates.Count131072.C069670
import PlattCertificates.Count131072.C069671
import PlattCertificates.Count131072.C069672
import PlattCertificates.Count131072.C069673
import PlattCertificates.Count131072.C069674
import PlattCertificates.Count131072.C069675
import PlattCertificates.Count131072.C069676
import PlattCertificates.Count131072.C069677
import PlattCertificates.Count131072.C069678
import PlattCertificates.Count131072.C069679
import PlattCertificates.Count131072.C069680
import PlattCertificates.Count131072.C069681
import PlattCertificates.Count131072.C069682
import PlattCertificates.Count131072.C069683
import PlattCertificates.Count131072.C069684
import PlattCertificates.Count131072.C069685
import PlattCertificates.Count131072.C069686
import PlattCertificates.Count131072.C069687
import PlattCertificates.Count131072.C069688
import PlattCertificates.Count131072.C069689
import PlattCertificates.Count131072.C069690
import PlattCertificates.Count131072.C069691
import PlattCertificates.Count131072.C069692
import PlattCertificates.Count131072.C069693
import PlattCertificates.Count131072.C069694
import PlattCertificates.Count131072.C069695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000302
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69664 : List PrefixCut := [⟨42,115856431,115856500⟩,
⟨64,175448114,175448219⟩]
theorem checked69664 : checkPrefixCuts (2^48) 9134931969 10 Manual.Count131072.C069664.packed 64 cuts69664 = true := by
 decide +kernel
def pointBounds69664 : List (Nat × Nat × Nat) := [(9135017984,115754855100412,115755244570969)]
theorem point_links_checked69664 : (cuts69664.take 1).map (fun c => (9134931969-1+2*2^10*c.k,115754739243981+c.lower,115755128714469+c.upper)) = pointBounds69664 := by
 decide +kernel
def cuts69665 : List PrefixCut := [⟨64,174521236,174521334⟩]
theorem checked69665 : checkPrefixCuts (2^48) 9135063041 10 Manual.Count131072.C069665.packed 64 cuts69665 = true := by
 decide +kernel
def cuts69666 : List PrefixCut := [⟨54,149961786,149961868⟩,
⟨64,177199358,177199456⟩]
theorem checked69666 : checkPrefixCuts (2^48) 9135194113 10 Manual.Count131072.C069666.packed 64 cuts69666 = true := by
 decide +kernel
def pointBounds69666 : List (Nat × Nat × Nat) := [(9135304704,115755239175117,115755628645890)]
theorem point_links_checked69666 : (cuts69666.take 1).map (fun c => (9135194113-1+2*2^10*c.k,115755089213331+c.lower,115755478684022+c.upper)) = pointBounds69666 := by
 decide +kernel
def cuts69667 : List PrefixCut := [⟨64,177813044,177813146⟩]
theorem checked69667 : checkPrefixCuts (2^48) 9135325185 10 Manual.Count131072.C069667.packed 64 cuts69667 = true := by
 decide +kernel
def cuts69668 : List PrefixCut := [⟨64,176054268,176054370⟩]
theorem checked69668 : checkPrefixCuts (2^48) 9135456257 10 Manual.Count131072.C069668.packed 64 cuts69668 = true := by
 decide +kernel
def cuts69669 : List PrefixCut := [⟨2,5515135,5515138⟩,
⟨64,172200429,172200527⟩]
theorem checked69669 : checkPrefixCuts (2^48) 9135587329 10 Manual.Count131072.C069669.packed 64 cuts69669 = true := by
 decide +kernel
def pointBounds69669 : List (Nat × Nat × Nat) := [(9135591424,115755625795136,115756015266132)]
theorem point_links_checked69669 : (cuts69669.take 1).map (fun c => (9135587329-1+2*2^10*c.k,115755620280001+c.lower,115756009750994+c.upper)) = pointBounds69669 := by
 decide +kernel
def cuts69670 : List PrefixCut := [⟨64,176881087,176881190⟩]
theorem checked69670 : checkPrefixCuts (2^48) 9135718401 10 Manual.Count131072.C069670.packed 64 cuts69670 = true := by
 decide +kernel
def cuts69671 : List PrefixCut := [⟨14,39128552,39128576⟩,
⟨64,175553741,175553842⟩]
theorem checked69671 : checkPrefixCuts (2^48) 9135849473 10 Manual.Count131072.C069671.packed 64 cuts69671 = true := by
 decide +kernel
def pointBounds69671 : List (Nat × Nat × Nat) := [(9135878144,115756008490069,115756397961287)]
theorem point_links_checked69671 : (cuts69671.take 1).map (fun c => (9135849473-1+2*2^10*c.k,115755969361517+c.lower,115756358832711+c.upper)) = pointBounds69671 := by
 decide +kernel
def cuts69672 : List PrefixCut := [⟨64,176290642,176290745⟩]
theorem checked69672 : checkPrefixCuts (2^48) 9135980545 10 Manual.Count131072.C069672.packed 64 cuts69672 = true := by
 decide +kernel
def cuts69673 : List PrefixCut := [⟨26,73140465,73140505⟩,
⟨64,177366416,177366515⟩]
theorem checked69673 : checkPrefixCuts (2^48) 9136111617 10 Manual.Count131072.C069673.packed 64 cuts69673 = true := by
 decide +kernel
def pointBounds69673 : List (Nat × Nat × Nat) := [(9136164864,115756394346365,115756783817803)]
theorem point_links_checked69673 : (cuts69673.take 1).map (fun c => (9136111617-1+2*2^10*c.k,115756321205900+c.lower,115756710677298+c.upper)) = pointBounds69673 := by
 decide +kernel
def cuts69674 : List PrefixCut := [⟨64,179736115,179736218⟩]
theorem checked69674 : checkPrefixCuts (2^48) 9136242689 10 Manual.Count131072.C069674.packed 64 cuts69674 = true := by
 decide +kernel
def cuts69675 : List PrefixCut := [⟨38,104038720,104038784⟩,
⟨64,173294682,173294785⟩]
theorem checked69675 : checkPrefixCuts (2^48) 9136373761 10 Manual.Count131072.C069675.packed 64 cuts69675 = true := by
 decide +kernel
def pointBounds69675 : List (Nat × Nat × Nat) := [(9136451584,115756782347151,115757171818815)]
theorem point_links_checked69675 : (cuts69675.take 1).map (fun c => (9136373761-1+2*2^10*c.k,115756678308431+c.lower,115757067780031+c.upper)) = pointBounds69675 := by
 decide +kernel
def cuts69676 : List PrefixCut := [⟨64,177728470,177728572⟩]
theorem checked69676 : checkPrefixCuts (2^48) 9136504833 10 Manual.Count131072.C069676.packed 64 cuts69676 = true := by
 decide +kernel
def cuts69677 : List PrefixCut := [⟨50,135428037,135428119⟩,
⟨64,172735173,172735282⟩]
theorem checked69677 : checkPrefixCuts (2^48) 9136635905 10 Manual.Count131072.C069677.packed 64 cuts69677 = true := by
 decide +kernel
def pointBounds69677 : List (Nat × Nat × Nat) := [(9136738304,115757164759620,115757554231507)]
theorem point_links_checked69677 : (cuts69677.take 1).map (fun c => (9136635905-1+2*2^10*c.k,115757029331583+c.lower,115757418803388+c.upper)) = pointBounds69677 := by
 decide +kernel
def cuts69678 : List PrefixCut := [⟨64,177538525,177538635⟩]
theorem checked69678 : checkPrefixCuts (2^48) 9136766977 10 Manual.Count131072.C069678.packed 64 cuts69678 = true := by
 decide +kernel
def cuts69679 : List PrefixCut := [⟨62,171066726,171066823⟩,
⟨64,176180516,176180615⟩]
theorem checked69679 : checkPrefixCuts (2^48) 9136898049 10 Manual.Count131072.C069679.packed 64 cuts69679 = true := by
 decide +kernel
def pointBounds69679 : List (Nat × Nat × Nat) := [(9137025024,115757550672007,115757940144128)]
theorem point_links_checked69679 : (cuts69679.take 1).map (fun c => (9136898049-1+2*2^10*c.k,115757379605281+c.lower,115757769077305+c.upper)) = pointBounds69679 := by
 decide +kernel
def cuts69680 : List PrefixCut := [⟨64,175808311,175808417⟩]
theorem checked69680 : checkPrefixCuts (2^48) 9137029121 10 Manual.Count131072.C069680.packed 64 cuts69680 = true := by
 decide +kernel
def cuts69681 : List PrefixCut := [⟨64,173865069,173865177⟩]
theorem checked69681 : checkPrefixCuts (2^48) 9137160193 10 Manual.Count131072.C069681.packed 64 cuts69681 = true := by
 decide +kernel
def cuts69682 : List PrefixCut := [⟨10,27847752,27847769⟩,
⟨64,178175246,178175351⟩]
theorem checked69682 : checkPrefixCuts (2^48) 9137291265 10 Manual.Count131072.C069682.packed 64 cuts69682 = true := by
 decide +kernel
def pointBounds69682 : List (Nat × Nat × Nat) := [(9137311744,115757933306929,115758322779283)]
theorem point_links_checked69682 : (cuts69682.take 1).map (fun c => (9137291265-1+2*2^10*c.k,115757905459177+c.lower,115758294931514+c.upper)) = pointBounds69682 := by
 decide +kernel
def cuts69683 : List PrefixCut := [⟨64,175615931,175616035⟩]
theorem checked69683 : checkPrefixCuts (2^48) 9137422337 10 Manual.Count131072.C069683.packed 64 cuts69683 = true := by
 decide +kernel
def cuts69684 : List PrefixCut := [⟨22,60653293,60653329⟩,
⟨64,176783950,176784055⟩]
theorem checked69684 : checkPrefixCuts (2^48) 9137553409 10 Manual.Count131072.C069684.packed 64 cuts69684 = true := by
 decide +kernel
def pointBounds69684 : List (Nat × Nat × Nat) := [(9137598464,115758319903647,115758709376229)]
theorem point_links_checked69684 : (cuts69684.take 1).map (fun c => (9137553409-1+2*2^10*c.k,115758259250354+c.lower,115758648722900+c.upper)) = pointBounds69684 := by
 decide +kernel
def cuts69685 : List PrefixCut := [⟨64,175395253,175395363⟩]
theorem checked69685 : checkPrefixCuts (2^48) 9137684481 10 Manual.Count131072.C069685.packed 64 cuts69685 = true := by
 decide +kernel
def cuts69686 : List PrefixCut := [⟨34,94011318,94011372⟩,
⟨64,176563258,176563363⟩]
theorem checked69686 : checkPrefixCuts (2^48) 9137815553 10 Manual.Count131072.C069686.packed 64 cuts69686 = true := by
 decide +kernel
def pointBounds69686 : List (Nat × Nat × Nat) := [(9137885184,115758705440875,115759094913690)]
theorem point_links_checked69686 : (cuts69686.take 1).map (fun c => (9137815553-1+2*2^10*c.k,115758611429557+c.lower,115759000902318+c.upper)) = pointBounds69686 := by
 decide +kernel
def cuts69687 : List PrefixCut := [⟨64,177608013,177608115⟩]
theorem checked69687 : checkPrefixCuts (2^48) 9137946625 10 Manual.Count131072.C069687.packed 64 cuts69687 = true := by
 decide +kernel
def cuts69688 : List PrefixCut := [⟨46,124348720,124348796⟩,
⟨64,174001606,174001710⟩]
theorem checked69688 : checkPrefixCuts (2^48) 9138077697 10 Manual.Count131072.C069688.packed 64 cuts69688 = true := by
 decide +kernel
def pointBounds69688 : List (Nat × Nat × Nat) := [(9138171904,115759089949548,115759479422592)]
theorem point_links_checked69688 : (cuts69688.take 1).map (fun c => (9138077697-1+2*2^10*c.k,115758965600828+c.lower,115759355073796+c.upper)) = pointBounds69688 := by
 decide +kernel
def cuts69689 : List PrefixCut := [⟨64,176155235,176155342⟩]
theorem checked69689 : checkPrefixCuts (2^48) 9138208769 10 Manual.Count131072.C069689.packed 64 cuts69689 = true := by
 decide +kernel
def cuts69690 : List PrefixCut := [⟨58,158934881,158934972⟩,
⟨64,175413477,175413577⟩]
theorem checked69690 : checkPrefixCuts (2^48) 9138339841 10 Manual.Count131072.C069690.packed 64 cuts69690 = true := by
 decide +kernel
def pointBounds69690 : List (Nat × Nat × Nat) := [(9138458624,115759474692550,115759864165820)]
theorem point_links_checked69690 : (cuts69690.take 1).map (fun c => (9138339841-1+2*2^10*c.k,115759315757669+c.lower,115759705230848+c.upper)) = pointBounds69690 := by
 decide +kernel
def cuts69691 : List PrefixCut := [⟨64,175010552,175010653⟩]
theorem checked69691 : checkPrefixCuts (2^48) 9138470913 10 Manual.Count131072.C069691.packed 64 cuts69691 = true := by
 decide +kernel
def cuts69692 : List PrefixCut := [⟨64,179012099,179012206⟩]
theorem checked69692 : checkPrefixCuts (2^48) 9138601985 10 Manual.Count131072.C069692.packed 64 cuts69692 = true := by
 decide +kernel
def cuts69693 : List PrefixCut := [⟨6,16108498,16108509⟩,
⟨64,174882338,174882445⟩]
theorem checked69693 : checkPrefixCuts (2^48) 9138733057 10 Manual.Count131072.C069693.packed 64 cuts69693 = true := by
 decide +kernel
def pointBounds69693 : List (Nat × Nat × Nat) := [(9138745344,115759861302295,115760250775793)]
theorem point_links_checked69693 : (cuts69693.take 1).map (fun c => (9138733057-1+2*2^10*c.k,115759845193797+c.lower,115760234667284+c.upper)) = pointBounds69693 := by
 decide +kernel
def cuts69694 : List PrefixCut := [⟨64,175649809,175649907⟩]
theorem checked69694 : checkPrefixCuts (2^48) 9138864129 10 Manual.Count131072.C069694.packed 64 cuts69694 = true := by
 decide +kernel
def cuts69695 : List PrefixCut := [⟨18,48878434,48878462⟩,
⟨64,174723324,174723429⟩]
theorem checked69695 : checkPrefixCuts (2^48) 9138995201 10 Manual.Count131072.C069695.packed 64 cuts69695 = true := by
 decide +kernel
def pointBounds69695 : List (Nat × Nat × Nat) := [(9139032064,115760244604378,115760634078098)]
theorem point_links_checked69695 : (cuts69695.take 1).map (fun c => (9138995201-1+2*2^10*c.k,115760195725944+c.lower,115760585199636+c.upper)) = pointBounds69695 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000302
