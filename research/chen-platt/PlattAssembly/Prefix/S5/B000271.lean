import PlattAssemblyKernel
import PlattCertificates.Count131072.C048672
import PlattCertificates.Count131072.C048673
import PlattCertificates.Count131072.C048674
import PlattCertificates.Count131072.C048675
import PlattCertificates.Count131072.C048676
import PlattCertificates.Count131072.C048677
import PlattCertificates.Count131072.C048678
import PlattCertificates.Count131072.C048679
import PlattCertificates.Count131072.C048680
import PlattCertificates.Count131072.C048681
import PlattCertificates.Count131072.C048682
import PlattCertificates.Count131072.C048683
import PlattCertificates.Count131072.C048684
import PlattCertificates.Count131072.C048685
import PlattCertificates.Count131072.C048686
import PlattCertificates.Count131072.C048687
import PlattCertificates.Count131072.C048688
import PlattCertificates.Count131072.C048689
import PlattCertificates.Count131072.C048690
import PlattCertificates.Count131072.C048691
import PlattCertificates.Count131072.C048692
import PlattCertificates.Count131072.C048693
import PlattCertificates.Count131072.C048694
import PlattCertificates.Count131072.C048695
import PlattCertificates.Count131072.C048696
import PlattCertificates.Count131072.C048697
import PlattCertificates.Count131072.C048698
import PlattCertificates.Count131072.C048699
import PlattCertificates.Count131072.C048700
import PlattCertificates.Count131072.C048701
import PlattCertificates.Count131072.C048702
import PlattCertificates.Count131072.C048703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000271
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48672 : List PrefixCut := [⟨64,253848560,253848706⟩]
theorem checked48672 : checkPrefixCuts (2^48) 6383468545 10 Manual.Count131072.C048672.packed 64 cuts48672 = true := by
 decide +kernel
def cuts48673 : List PrefixCut := [⟨34,137791267,137791344⟩,
⟨64,257282626,257282775⟩]
theorem checked48673 : checkPrefixCuts (2^48) 6383599617 10 Manual.Count131072.C048673.packed 64 cuts48673 = true := by
 decide +kernel
def pointBounds48673 : List (Nat × Nat × Nat) := [(6383669248,111322063077387,111322450008477)]
theorem point_links_checked48673 : (cuts48673.take 1).map (fun c => (6383599617-1+2*2^10*c.k,111321925286120+c.lower,111322312217133+c.upper)) = pointBounds48673 := by
 decide +kernel
def cuts48674 : List PrefixCut := [⟨64,257762335,257762484⟩]
theorem checked48674 : checkPrefixCuts (2^48) 6383730689 10 Manual.Count131072.C048674.packed 64 cuts48674 = true := by
 decide +kernel
def cuts48675 : List PrefixCut := [⟨4,16490261,16490269⟩,
⟨64,258682977,258683123⟩]
theorem checked48675 : checkPrefixCuts (2^48) 6383861761 10 Manual.Count131072.C048675.packed 64 cuts48675 = true := by
 decide +kernel
def pointBounds48675 : List (Nat × Nat × Nat) := [(6383869952,111322456821342,111322843752661)]
theorem point_links_checked48675 : (cuts48675.take 1).map (fun c => (6383861761-1+2*2^10*c.k,111322440331081+c.lower,111322827262392+c.upper)) = pointBounds48675 := by
 decide +kernel
def cuts48676 : List PrefixCut := [⟨38,150657105,150657189⟩,
⟨64,254268617,254268756⟩]
theorem checked48676 : checkPrefixCuts (2^48) 6383992833 10 Manual.Count131072.C048676.packed 64 cuts48676 = true := by
 decide +kernel
def pointBounds48676 : List (Nat × Nat × Nat) := [(6384070656,111322849671163,111323236602704)]
theorem point_links_checked48676 : (cuts48676.take 1).map (fun c => (6383992833-1+2*2^10*c.k,111322699014058+c.lower,111323085945515+c.upper)) = pointBounds48676 := by
 decide +kernel
def cuts48677 : List PrefixCut := [⟨64,255982862,255983008⟩]
theorem checked48677 : checkPrefixCuts (2^48) 6384123905 10 Manual.Count131072.C048677.packed 64 cuts48677 = true := by
 decide +kernel
def cuts48678 : List PrefixCut := [⟨8,32934380,32934398⟩,
⟨64,255404487,255404626⟩]
theorem checked48678 : checkPrefixCuts (2^48) 6384254977 10 Manual.Count131072.C048678.packed 64 cuts48678 = true := by
 decide +kernel
def pointBounds48678 : List (Nat × Nat × Nat) := [(6384271360,111323242199917,111323629131677)]
theorem point_links_checked48678 : (cuts48678.take 1).map (fun c => (6384254977-1+2*2^10*c.k,111323209265537+c.lower,111323596197279+c.upper)) = pointBounds48678 := by
 decide +kernel
def cuts48679 : List PrefixCut := [⟨42,168900040,168900138⟩,
⟨64,254870208,254870358⟩]
theorem checked48679 : checkPrefixCuts (2^48) 6384386049 10 Manual.Count131072.C048679.packed 64 cuts48679 = true := by
 decide +kernel
def pointBounds48679 : List (Nat × Nat × Nat) := [(6384472064,111323633570064,111324020502043)]
theorem point_links_checked48679 : (cuts48679.take 1).map (fun c => (6384386049-1+2*2^10*c.k,111323464670024+c.lower,111323851601905+c.upper)) = pointBounds48679 := by
 decide +kernel
def cuts48680 : List PrefixCut := [⟨64,254424085,254424235⟩]
theorem checked48680 : checkPrefixCuts (2^48) 6384517121 10 Manual.Count131072.C048680.packed 64 cuts48680 = true := by
 decide +kernel
def cuts48681 : List PrefixCut := [⟨12,47965696,47965727⟩,
⟨64,256402729,256402875⟩]
theorem checked48681 : checkPrefixCuts (2^48) 6384648193 10 Manual.Count131072.C048681.packed 64 cuts48681 = true := by
 decide +kernel
def pointBounds48681 : List (Nat × Nat × Nat) := [(6384672768,111324021930013,111324408862225)]
theorem point_links_checked48681 : (cuts48681.take 1).map (fun c => (6384648193-1+2*2^10*c.k,111323973964317+c.lower,111324360896498+c.upper)) = pointBounds48681 := by
 decide +kernel
def cuts48682 : List PrefixCut := [⟨46,182291359,182291459⟩,
⟨64,255912511,255912653⟩]
theorem checked48682 : checkPrefixCuts (2^48) 6384779265 10 Manual.Count131072.C048682.packed 64 cuts48682 = true := by
 decide +kernel
def pointBounds48682 : List (Nat × Nat × Nat) := [(6384873472,111324412658405,111324799590832)]
theorem point_links_checked48682 : (cuts48682.take 1).map (fun c => (6384779265-1+2*2^10*c.k,111324230367046+c.lower,111324617299373+c.upper)) = pointBounds48682 := by
 decide +kernel
def cuts48683 : List PrefixCut := [⟨64,255642780,255642926⟩]
theorem checked48683 : checkPrefixCuts (2^48) 6384910337 10 Manual.Count131072.C048683.packed 64 cuts48683 = true := by
 decide +kernel
def cuts48684 : List PrefixCut := [⟨16,63612308,63612347⟩,
⟨64,254094616,254094765⟩]
theorem checked48684 : checkPrefixCuts (2^48) 6385041409 10 Manual.Count131072.C048684.packed 64 cuts48684 = true := by
 decide +kernel
def pointBounds48684 : List (Nat × Nat × Nat) := [(6385074176,111324805534645,111325192467299)]
theorem point_links_checked48684 : (cuts48684.take 1).map (fun c => (6385041409-1+2*2^10*c.k,111324741922337+c.lower,111325128854952+c.upper)) = pointBounds48684 := by
 decide +kernel
def cuts48685 : List PrefixCut := [⟨50,204673802,204673911⟩,
⟨64,260393168,260393306⟩]
theorem checked48685 : checkPrefixCuts (2^48) 6385172481 10 Manual.Count131072.C048685.packed 64 cuts48685 = true := by
 decide +kernel
def pointBounds48685 : List (Nat × Nat × Nat) := [(6385274880,111325200690755,111325587623628)]
theorem point_links_checked48685 : (cuts48685.take 1).map (fun c => (6385172481-1+2*2^10*c.k,111324996016953+c.lower,111325382949717+c.upper)) = pointBounds48685 := by
 decide +kernel
def cuts48686 : List PrefixCut := [⟨64,252585450,252585591⟩]
theorem checked48686 : checkPrefixCuts (2^48) 6385303553 10 Manual.Count131072.C048686.packed 64 cuts48686 = true := by
 decide +kernel
def cuts48687 : List PrefixCut := [⟨20,82034057,82034101⟩,
⟨64,257781734,257781876⟩]
theorem checked48687 : checkPrefixCuts (2^48) 6385434625 10 Manual.Count131072.C048687.packed 64 cuts48687 = true := by
 decide +kernel
def pointBounds48687 : List (Nat × Nat × Nat) := [(6385475584,111325591029628,111325977962715)]
theorem point_links_checked48687 : (cuts48687.take 1).map (fun c => (6385434625-1+2*2^10*c.k,111325508995571+c.lower,111325895928614+c.upper)) = pointBounds48687 := by
 decide +kernel
def cuts48688 : List PrefixCut := [⟨54,215813165,215813294⟩,
⟨64,255925087,255925238⟩]
theorem checked48688 : checkPrefixCuts (2^48) 6385565697 10 Manual.Count131072.C048688.packed 64 cuts48688 = true := by
 decide +kernel
def pointBounds48688 : List (Nat × Nat × Nat) := [(6385676288,111325982590470,111326369523784)]
theorem point_links_checked48688 : (cuts48688.take 1).map (fun c => (6385565697-1+2*2^10*c.k,111325766777305+c.lower,111326153710490+c.upper)) = pointBounds48688 := by
 decide +kernel
def cuts48689 : List PrefixCut := [⟨64,256536907,256537059⟩]
theorem checked48689 : checkPrefixCuts (2^48) 6385696769 10 Manual.Count131072.C048689.packed 64 cuts48689 = true := by
 decide +kernel
def cuts48690 : List PrefixCut := [⟨24,97235833,97235889⟩,
⟨64,257104707,257104860⟩]
theorem checked48690 : checkPrefixCuts (2^48) 6385827841 10 Manual.Count131072.C048690.packed 64 cuts48690 = true := by
 decide +kernel
def pointBounds48690 : List (Nat × Nat × Nat) := [(6385876992,111326376475132,111326763408676)]
theorem point_links_checked48690 : (cuts48690.take 1).map (fun c => (6385827841-1+2*2^10*c.k,111326279239299+c.lower,111326666172787+c.upper)) = pointBounds48690 := by
 decide +kernel
def cuts48691 : List PrefixCut := [⟨58,233033754,233033886⟩,
⟨64,257187563,257187707⟩]
theorem checked48691 : checkPrefixCuts (2^48) 6385958913 10 Manual.Count131072.C048691.packed 64 cuts48691 = true := by
 decide +kernel
def pointBounds48691 : List (Nat × Nat × Nat) := [(6386077696,111326769377760,111327156311533)]
theorem point_links_checked48691 : (cuts48691.take 1).map (fun c => (6385958913-1+2*2^10*c.k,111326536344006+c.lower,111326923277647+c.upper)) = pointBounds48691 := by
 decide +kernel
def cuts48692 : List PrefixCut := [⟨64,253479907,253480048⟩]
theorem checked48692 : checkPrefixCuts (2^48) 6386089985 10 Manual.Count131072.C048692.packed 64 cuts48692 = true := by
 decide +kernel
def cuts48693 : List PrefixCut := [⟨28,111421973,111422037⟩,
⟨64,255193625,255193773⟩]
theorem checked48693 : checkPrefixCuts (2^48) 6386221057 10 Manual.Count131072.C048693.packed 64 cuts48693 = true := by
 decide +kernel
def pointBounds48693 : List (Nat × Nat × Nat) := [(6386278400,111327158433449,111327545367439)]
theorem point_links_checked48693 : (cuts48693.take 1).map (fun c => (6386221057-1+2*2^10*c.k,111327047011476+c.lower,111327433945402+c.upper)) = pointBounds48693 := by
 decide +kernel
def cuts48694 : List PrefixCut := [⟨62,246638127,246638263⟩,
⟨64,254703586,254703728⟩]
theorem checked48694 : checkPrefixCuts (2^48) 6386352129 10 Manual.Count131072.C048694.packed 64 cuts48694 = true := by
 decide +kernel
def pointBounds48694 : List (Nat × Nat × Nat) := [(6386479104,111327548843228,111327935777438)]
theorem point_links_checked48694 : (cuts48694.take 1).map (fun c => (6386352129-1+2*2^10*c.k,111327302205101+c.lower,111327689139175+c.upper)) = pointBounds48694 := by
 decide +kernel
def cuts48695 : List PrefixCut := [⟨64,255447575,255447719⟩]
theorem checked48695 : checkPrefixCuts (2^48) 6386483201 10 Manual.Count131072.C048695.packed 64 cuts48695 = true := by
 decide +kernel
def cuts48696 : List PrefixCut := [⟨32,127633693,127633761⟩,
⟨64,258218889,258219031⟩]
theorem checked48696 : checkPrefixCuts (2^48) 6386614273 10 Manual.Count131072.C048696.packed 64 cuts48696 = true := by
 decide +kernel
def pointBounds48696 : List (Nat × Nat × Nat) := [(6386679808,111327939989955,111328326924383)]
theorem point_links_checked48696 : (cuts48696.take 1).map (fun c => (6386614273-1+2*2^10*c.k,111327812356262+c.lower,111328199290622+c.upper)) = pointBounds48696 := by
 decide +kernel
def cuts48697 : List PrefixCut := [⟨64,255040476,255040623⟩]
theorem checked48697 : checkPrefixCuts (2^48) 6386745345 10 Manual.Count131072.C048697.packed 64 cuts48697 = true := by
 decide +kernel
def cuts48698 : List PrefixCut := [⟨2,8020887,8020891⟩,
⟨64,250628196,250628344⟩]
theorem checked48698 : checkPrefixCuts (2^48) 6386876417 10 Manual.Count131072.C048698.packed 64 cuts48698 = true := by
 decide +kernel
def pointBounds48698 : List (Nat × Nat × Nat) := [(6386880512,111328333636514,111328720571167)]
theorem point_links_checked48698 : (cuts48698.take 1).map (fun c => (6386876417-1+2*2^10*c.k,111328325615627+c.lower,111328712550276+c.upper)) = pointBounds48698 := by
 decide +kernel
def cuts48699 : List PrefixCut := [⟨36,145341749,145341838⟩,
⟨64,257365692,257365844⟩]
theorem checked48699 : checkPrefixCuts (2^48) 6387007489 10 Manual.Count131072.C048699.packed 64 cuts48699 = true := by
 decide +kernel
def pointBounds48699 : List (Nat × Nat × Nat) := [(6387081216,111328721585572,111329108520458)]
theorem point_links_checked48699 : (cuts48699.take 1).map (fun c => (6387007489-1+2*2^10*c.k,111328576243823+c.lower,111328963178620+c.upper)) = pointBounds48699 := by
 decide +kernel
def cuts48700 : List PrefixCut := [⟨64,259255337,259255486⟩]
theorem checked48700 : checkPrefixCuts (2^48) 6387138561 10 Manual.Count131072.C048700.packed 64 cuts48700 = true := by
 decide +kernel
def cuts48701 : List PrefixCut := [⟨6,23752687,23752702⟩,
⟨64,255548323,255548472⟩]
theorem checked48701 : checkPrefixCuts (2^48) 6387269633 10 Manual.Count131072.C048701.packed 64 cuts48701 = true := by
 decide +kernel
def pointBounds48701 : List (Nat × Nat × Nat) := [(6387281920,111329116617539,111329503552652)]
theorem point_links_checked48701 : (cuts48701.take 1).map (fun c => (6387269633-1+2*2^10*c.k,111329092864852+c.lower,111329479799950+c.upper)) = pointBounds48701 := by
 decide +kernel
def cuts48702 : List PrefixCut := [⟨40,158508717,158508811⟩,
⟨64,254088887,254089039⟩]
theorem checked48702 : checkPrefixCuts (2^48) 6387400705 10 Manual.Count131072.C048702.packed 64 cuts48702 = true := by
 decide +kernel
def pointBounds48702 : List (Nat × Nat × Nat) := [(6387482624,111329506921892,111329893857233)]
theorem point_links_checked48702 : (cuts48702.take 1).map (fun c => (6387400705-1+2*2^10*c.k,111329348413175+c.lower,111329735348422+c.upper)) = pointBounds48702 := by
 decide +kernel
def cuts48703 : List PrefixCut := [⟨64,255581915,255582062⟩]
theorem checked48703 : checkPrefixCuts (2^48) 6387531777 10 Manual.Count131072.C048703.packed 64 cuts48703 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000271
