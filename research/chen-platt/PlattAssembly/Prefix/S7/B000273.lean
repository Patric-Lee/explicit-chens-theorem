import PlattAssemblyKernel
import PlattCertificates.Count131072.C068736
import PlattCertificates.Count131072.C068737
import PlattCertificates.Count131072.C068738
import PlattCertificates.Count131072.C068739
import PlattCertificates.Count131072.C068740
import PlattCertificates.Count131072.C068741
import PlattCertificates.Count131072.C068742
import PlattCertificates.Count131072.C068743
import PlattCertificates.Count131072.C068744
import PlattCertificates.Count131072.C068745
import PlattCertificates.Count131072.C068746
import PlattCertificates.Count131072.C068747
import PlattCertificates.Count131072.C068748
import PlattCertificates.Count131072.C068749
import PlattCertificates.Count131072.C068750
import PlattCertificates.Count131072.C068751
import PlattCertificates.Count131072.C068752
import PlattCertificates.Count131072.C068753
import PlattCertificates.Count131072.C068754
import PlattCertificates.Count131072.C068755
import PlattCertificates.Count131072.C068756
import PlattCertificates.Count131072.C068757
import PlattCertificates.Count131072.C068758
import PlattCertificates.Count131072.C068759
import PlattCertificates.Count131072.C068760
import PlattCertificates.Count131072.C068761
import PlattCertificates.Count131072.C068762
import PlattCertificates.Count131072.C068763
import PlattCertificates.Count131072.C068764
import PlattCertificates.Count131072.C068765
import PlattCertificates.Count131072.C068766
import PlattCertificates.Count131072.C068767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000273
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68736 : List PrefixCut := [⟨64,179689487,179689591⟩]
theorem checked68736 : checkPrefixCuts (2^48) 9013297153 10 Manual.Count131072.C068736.packed 64 cuts68736 = true := by
 decide +kernel
def cuts68737 : List PrefixCut := [⟨37,104958190,104958250⟩,
⟨64,181591791,181591894⟩]
theorem checked68737 : checkPrefixCuts (2^48) 9013428225 10 Manual.Count131072.C068737.packed 64 cuts68737 = true := by
 decide +kernel
def pointBounds68737 : List (Nat × Nat × Nat) := [(9013504000,115590458170196,115590847544212)]
theorem point_links_checked68737 : (cuts68737.take 1).map (fun c => (9013428225-1+2*2^10*c.k,115590353212006+c.lower,115590742585962+c.upper)) = pointBounds68737 := by
 decide +kernel
def cuts68738 : List PrefixCut := [⟨64,180527423,180527520⟩]
theorem checked68738 : checkPrefixCuts (2^48) 9013559297 10 Manual.Count131072.C068738.packed 64 cuts68738 = true := by
 decide +kernel
def cuts68739 : List PrefixCut := [⟨47,131654380,131654459⟩,
⟨64,179057107,179057216⟩]
theorem checked68739 : checkPrefixCuts (2^48) 9013690369 10 Manual.Count131072.C068739.packed 64 cuts68739 = true := by
 decide +kernel
def pointBounds68739 : List (Nat × Nat × Nat) := [(9013786624,115590846985600,115591236359835)]
theorem point_links_checked68739 : (cuts68739.take 1).map (fun c => (9013690369-1+2*2^10*c.k,115590715331220+c.lower,115591104705376+c.upper)) = pointBounds68739 := by
 decide +kernel
def cuts68740 : List PrefixCut := [⟨64,178804681,178804784⟩]
theorem checked68740 : checkPrefixCuts (2^48) 9013821441 10 Manual.Count131072.C068740.packed 64 cuts68740 = true := by
 decide +kernel
def cuts68741 : List PrefixCut := [⟨57,158442638,158442734⟩,
⟨64,178302468,178302577⟩]
theorem checked68741 : checkPrefixCuts (2^48) 9013952513 10 Manual.Count131072.C068741.packed 64 cuts68741 = true := by
 decide +kernel
def pointBounds68741 : List (Nat × Nat × Nat) := [(9014069248,115591231635646,115591621010110)]
theorem point_links_checked68741 : (cuts68741.take 1).map (fun c => (9013952513-1+2*2^10*c.k,115591073193008+c.lower,115591462567376+c.upper)) = pointBounds68741 := by
 decide +kernel
def cuts68742 : List PrefixCut := [⟨64,176519998,176520100⟩]
theorem checked68742 : checkPrefixCuts (2^48) 9014083585 10 Manual.Count131072.C068742.packed 64 cuts68742 = true := by
 decide +kernel
def cuts68743 : List PrefixCut := [⟨64,177828908,177829010⟩]
theorem checked68743 : checkPrefixCuts (2^48) 9014214657 10 Manual.Count131072.C068743.packed 64 cuts68743 = true := by
 decide +kernel
def cuts68744 : List PrefixCut := [⟨3,8274679,8274685⟩,
⟨64,179637364,179637468⟩]
theorem checked68744 : checkPrefixCuts (2^48) 9014345729 10 Manual.Count131072.C068744.packed 64 cuts68744 = true := by
 decide +kernel
def pointBounds68744 : List (Nat × Nat × Nat) := [(9014351872,115591614119061,115592003493748)]
theorem point_links_checked68744 : (cuts68744.take 1).map (fun c => (9014345729-1+2*2^10*c.k,115591605844382+c.lower,115591995219063+c.upper)) = pointBounds68744 := by
 decide +kernel
def cuts68745 : List PrefixCut := [⟨64,179322488,179322594⟩]
theorem checked68745 : checkPrefixCuts (2^48) 9014476801 10 Manual.Count131072.C068745.packed 64 cuts68745 = true := by
 decide +kernel
def cuts68746 : List PrefixCut := [⟨13,35189747,35189762⟩,
⟨64,177727469,177727567⟩]
theorem checked68746 : checkPrefixCuts (2^48) 9014607873 10 Manual.Count131072.C068746.packed 64 cuts68746 = true := by
 decide +kernel
def pointBounds68746 : List (Nat × Nat × Nat) := [(9014634496,115591999993981,115592389368887)]
theorem point_links_checked68746 : (cuts68746.take 1).map (fun c => (9014607873-1+2*2^10*c.k,115591964804234+c.lower,115592354179125+c.upper)) = pointBounds68746 := by
 decide +kernel
def cuts68747 : List PrefixCut := [⟨64,178005908,178006012⟩]
theorem checked68747 : checkPrefixCuts (2^48) 9014738945 10 Manual.Count131072.C068747.packed 64 cuts68747 = true := by
 decide +kernel
def cuts68748 : List PrefixCut := [⟨23,64975727,64975767⟩,
⟨64,177534975,177535078⟩]
theorem checked68748 : checkPrefixCuts (2^48) 9014870017 10 Manual.Count131072.C068748.packed 64 cuts68748 = true := by
 decide +kernel
def pointBounds68748 : List (Nat × Nat × Nat) := [(9014917120,115592385513338,115592774888471)]
theorem point_links_checked68748 : (cuts68748.take 1).map (fun c => (9014870017-1+2*2^10*c.k,115592320537611+c.lower,115592709912704+c.upper)) = pointBounds68748 := by
 decide +kernel
def cuts68749 : List PrefixCut := [⟨64,178812514,178812611⟩]
theorem checked68749 : checkPrefixCuts (2^48) 9015001089 10 Manual.Count131072.C068749.packed 64 cuts68749 = true := by
 decide +kernel
def cuts68750 : List PrefixCut := [⟨33,91793783,91793839⟩,
⟨64,177748355,177748461⟩]
theorem checked68750 : checkPrefixCuts (2^48) 9015132161 10 Manual.Count131072.C068750.packed 64 cuts68750 = true := by
 decide +kernel
def pointBounds68750 : List (Nat × Nat × Nat) := [(9015199744,115592768678883,115593158054232)]
theorem point_links_checked68750 : (cuts68750.take 1).map (fun c => (9015132161-1+2*2^10*c.k,115592676885100+c.lower,115593066260393+c.upper)) = pointBounds68750 := by
 decide +kernel
def cuts68751 : List PrefixCut := [⟨64,179900081,179900179⟩]
theorem checked68751 : checkPrefixCuts (2^48) 9015263233 10 Manual.Count131072.C068751.packed 64 cuts68751 = true := by
 decide +kernel
def cuts68752 : List PrefixCut := [⟨43,121888465,121888541⟩,
⟨64,181083871,181083980⟩]
theorem checked68752 : checkPrefixCuts (2^48) 9015394305 10 Manual.Count131072.C068752.packed 64 cuts68752 = true := by
 decide +kernel
def pointBounds68752 : List (Nat × Nat × Nat) := [(9015482368,115593156422001,115593545797574)]
theorem point_links_checked68752 : (cuts68752.take 1).map (fun c => (9015394305-1+2*2^10*c.k,115593034533536+c.lower,115593423909033+c.upper)) = pointBounds68752 := by
 decide +kernel
def cuts68753 : List PrefixCut := [⟨64,177022515,177022618⟩]
theorem checked68753 : checkPrefixCuts (2^48) 9015525377 10 Manual.Count131072.C068753.packed 64 cuts68753 = true := by
 decide +kernel
def cuts68754 : List PrefixCut := [⟨53,148921726,148921814⟩,
⟨64,180235651,180235754⟩]
theorem checked68754 : checkPrefixCuts (2^48) 9015656449 10 Manual.Count131072.C068754.packed 64 cuts68754 = true := by
 decide +kernel
def pointBounds68754 : List (Nat × Nat × Nat) := [(9015764992,115593541561648,115593930937445)]
theorem point_links_checked68754 : (cuts68754.take 1).map (fun c => (9015656449-1+2*2^10*c.k,115593392639922+c.lower,115593782015631+c.upper)) = pointBounds68754 := by
 decide +kernel
def cuts68755 : List PrefixCut := [⟨64,176611516,176611623⟩]
theorem checked68755 : checkPrefixCuts (2^48) 9015787521 10 Manual.Count131072.C068755.packed 64 cuts68755 = true := by
 decide +kernel
def cuts68756 : List PrefixCut := [⟨63,175141647,175141747⟩,
⟨64,177545534,177545636⟩]
theorem checked68756 : checkPrefixCuts (2^48) 9015918593 10 Manual.Count131072.C068756.packed 64 cuts68756 = true := by
 decide +kernel
def pointBounds68756 : List (Nat × Nat × Nat) := [(9016047616,115593924628736,115594314004755)]
theorem point_links_checked68756 : (cuts68756.take 1).map (fun c => (9015918593-1+2*2^10*c.k,115593749487089+c.lower,115594138863008+c.upper)) = pointBounds68756 := by
 decide +kernel
def cuts68757 : List PrefixCut := [⟨64,178104899,178105003⟩]
theorem checked68757 : checkPrefixCuts (2^48) 9016049665 10 Manual.Count131072.C068757.packed 64 cuts68757 = true := by
 decide +kernel
def cuts68758 : List PrefixCut := [⟨64,178383272,178383383⟩]
theorem checked68758 : checkPrefixCuts (2^48) 9016180737 10 Manual.Count131072.C068758.packed 64 cuts68758 = true := by
 decide +kernel
def cuts68759 : List PrefixCut := [⟨9,25786376,25786393⟩,
⟨64,177256827,177256933⟩]
theorem checked68759 : checkPrefixCuts (2^48) 9016311809 10 Manual.Count131072.C068759.packed 64 cuts68759 = true := by
 decide +kernel
def pointBounds68759 : List (Nat × Nat × Nat) := [(9016330240,115594309307170,115594698683423)]
theorem point_links_checked68759 : (cuts68759.take 1).map (fun c => (9016311809-1+2*2^10*c.k,115594283520794+c.lower,115594672897030+c.upper)) = pointBounds68759 := by
 decide +kernel
def cuts68760 : List PrefixCut := [⟨64,178471743,178471842⟩]
theorem checked68760 : checkPrefixCuts (2^48) 9016442881 10 Manual.Count131072.C068760.packed 64 cuts68760 = true := by
 decide +kernel
def cuts68761 : List PrefixCut := [⟨19,53818852,53818886⟩,
⟨64,178781313,178781425⟩]
theorem checked68761 : checkPrefixCuts (2^48) 9016573953 10 Manual.Count131072.C068761.packed 64 cuts68761 = true := by
 decide +kernel
def pointBounds68761 : List (Nat × Nat × Nat) := [(9016612864,115594693068216,115595082444691)]
theorem point_links_checked68761 : (cuts68761.take 1).map (fun c => (9016573953-1+2*2^10*c.k,115594639249364+c.lower,115595028625805+c.upper)) = pointBounds68761 := by
 decide +kernel
def cuts68762 : List PrefixCut := [⟨64,180245919,180246026⟩]
theorem checked68762 : checkPrefixCuts (2^48) 9016705025 10 Manual.Count131072.C068762.packed 64 cuts68762 = true := by
 decide +kernel
def cuts68763 : List PrefixCut := [⟨29,80132730,80132780⟩,
⟨64,178401527,178401634⟩]
theorem checked68763 : checkPrefixCuts (2^48) 9016836097 10 Manual.Count131072.C068763.packed 64 cuts68763 = true := by
 decide +kernel
def pointBounds68763 : List (Nat × Nat × Nat) := [(9016895488,115595078409326,115595467786036)]
theorem point_links_checked68763 : (cuts68763.take 1).map (fun c => (9016836097-1+2*2^10*c.k,115594998276596+c.lower,115595387653256+c.upper)) = pointBounds68763 := by
 decide +kernel
def cuts68764 : List PrefixCut := [⟨64,177431236,177431341⟩]
theorem checked68764 : checkPrefixCuts (2^48) 9016967169 10 Manual.Count131072.C068764.packed 64 cuts68764 = true := by
 decide +kernel
def cuts68765 : List PrefixCut := [⟨39,110128452,110128515⟩,
⟨64,179488889,179488995⟩]
theorem checked68765 : checkPrefixCuts (2^48) 9017098241 10 Manual.Count131072.C068765.packed 64 cuts68765 = true := by
 decide +kernel
def pointBounds68765 : List (Nat × Nat × Nat) := [(9017178112,115595464237811,115595853614746)]
theorem point_links_checked68765 : (cuts68765.take 1).map (fun c => (9017098241-1+2*2^10*c.k,115595354109359+c.lower,115595743486231+c.upper)) = pointBounds68765 := by
 decide +kernel
def cuts68766 : List PrefixCut := [⟨64,179423845,179423946⟩]
theorem checked68766 : checkPrefixCuts (2^48) 9017229313 10 Manual.Count131072.C068766.packed 64 cuts68766 = true := by
 decide +kernel
def cuts68767 : List PrefixCut := [⟨49,135565018,135565093⟩,
⟨64,177922926,177923026⟩]
theorem checked68767 : checkPrefixCuts (2^48) 9017360385 10 Manual.Count131072.C068767.packed 64 cuts68767 = true := by
 decide +kernel
def pointBounds68767 : List (Nat × Nat × Nat) := [(9017460736,115595848587111,115596237964265)]
theorem point_links_checked68767 : (cuts68767.take 1).map (fun c => (9017360385-1+2*2^10*c.k,115595713022093+c.lower,115596102399172+c.upper)) = pointBounds68767 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000273
