import PlattAssemblyKernel
import PlattCertificates.Count131072.C057872
import PlattCertificates.Count131072.C057873
import PlattCertificates.Count131072.C057874
import PlattCertificates.Count131072.C057875
import PlattCertificates.Count131072.C057876
import PlattCertificates.Count131072.C057877
import PlattCertificates.Count131072.C057878
import PlattCertificates.Count131072.C057879
import PlattCertificates.Count131072.C057880
import PlattCertificates.Count131072.C057881
import PlattCertificates.Count131072.C057882
import PlattCertificates.Count131072.C057883
import PlattCertificates.Count131072.C057884
import PlattCertificates.Count131072.C057885
import PlattCertificates.Count131072.C057886
import PlattCertificates.Count131072.C057887
import PlattCertificates.Count131072.C057888
import PlattCertificates.Count131072.C057889
import PlattCertificates.Count131072.C057890
import PlattCertificates.Count131072.C057891
import PlattCertificates.Count131072.C057892
import PlattCertificates.Count131072.C057893
import PlattCertificates.Count131072.C057894
import PlattCertificates.Count131072.C057895
import PlattCertificates.Count131072.C057896
import PlattCertificates.Count131072.C057897
import PlattCertificates.Count131072.C057898
import PlattCertificates.Count131072.C057899
import PlattCertificates.Count131072.C057900
import PlattCertificates.Count131072.C057901
import PlattCertificates.Count131072.C057902
import PlattCertificates.Count131072.C057903
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000246
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57872 : List PrefixCut := [⟨64,214850288,214850406⟩]
theorem checked57872 : checkPrefixCuts (2^48) 7589330945 10 Manual.Count131072.C057872.packed 64 cuts57872 = true := by
 decide +kernel
def cuts57873 : List PrefixCut := [⟨16,52812623,52812650⟩,
⟨64,211731249,211731368⟩]
theorem checked57873 : checkPrefixCuts (2^48) 7589462017 10 Manual.Count131072.C057873.packed 64 cuts57873 = true := by
 decide +kernel
def pointBounds57873 : List (Nat × Nat × Nat) := [(7589494784,113470881998258,113471270151063)]
theorem point_links_checked57873 : (cuts57873.take 1).map (fun c => (7589462017-1+2*2^10*c.k,113470829185635+c.lower,113471217338413+c.upper)) = pointBounds57873 := by
 decide +kernel
def cuts57874 : List PrefixCut := [⟨64,211950108,211950233⟩]
theorem checked57874 : checkPrefixCuts (2^48) 7589593089 10 Manual.Count131072.C057874.packed 64 cuts57874 = true := by
 decide +kernel
def cuts57875 : List PrefixCut := [⟨4,13759016,13759024⟩,
⟨64,216211347,216211471⟩]
theorem checked57875 : checkPrefixCuts (2^48) 7589724161 10 Manual.Count131072.C057875.packed 64 cuts57875 = true := by
 decide +kernel
def pointBounds57875 : List (Nat × Nat × Nat) := [(7589732352,113471266626008,113471654779038)]
theorem point_links_checked57875 : (cuts57875.take 1).map (fun c => (7589724161-1+2*2^10*c.k,113471252866992+c.lower,113471641020014+c.upper)) = pointBounds57875 := by
 decide +kernel
def cuts57876 : List PrefixCut := [⟨56,188097116,188097227⟩,
⟨64,214501688,214501814⟩]
theorem checked57876 : checkPrefixCuts (2^48) 7589855233 10 Manual.Count131072.C057876.packed 64 cuts57876 = true := by
 decide +kernel
def pointBounds57876 : List (Nat × Nat × Nat) := [(7589969920,113471657175455,113472045328712)]
theorem point_links_checked57876 : (cuts57876.take 1).map (fun c => (7589855233-1+2*2^10*c.k,113471469078339+c.lower,113471857231485+c.upper)) = pointBounds57876 := by
 decide +kernel
def cuts57877 : List PrefixCut := [⟨64,212569586,212569710⟩]
theorem checked57877 : checkPrefixCuts (2^48) 7589986305 10 Manual.Count131072.C057877.packed 64 cuts57877 = true := by
 decide +kernel
def cuts57878 : List PrefixCut := [⟨44,146667895,146667978⟩,
⟨64,213678416,213678538⟩]
theorem checked57878 : checkPrefixCuts (2^48) 7590117377 10 Manual.Count131072.C057878.packed 64 cuts57878 = true := by
 decide +kernel
def pointBounds57878 : List (Nat × Nat × Nat) := [(7590207488,113472042817508,113472430970987)]
theorem point_links_checked57878 : (cuts57878.take 1).map (fun c => (7590117377-1+2*2^10*c.k,113471896149613+c.lower,113472284303009+c.upper)) = pointBounds57878 := by
 decide +kernel
def cuts57879 : List PrefixCut := [⟨64,214008485,214008611⟩]
theorem checked57879 : checkPrefixCuts (2^48) 7590248449 10 Manual.Count131072.C057879.packed 64 cuts57879 = true := by
 decide +kernel
def cuts57880 : List PrefixCut := [⟨32,103795190,103795249⟩,
⟨64,210519008,210519129⟩]
theorem checked57880 : checkPrefixCuts (2^48) 7590379521 10 Manual.Count131072.C057880.packed 64 cuts57880 = true := by
 decide +kernel
def pointBounds57880 : List (Nat × Nat × Nat) := [(7590445056,113472427631704,113472815785407)]
theorem point_links_checked57880 : (cuts57880.take 1).map (fun c => (7590379521-1+2*2^10*c.k,113472323836514+c.lower,113472711990158+c.upper)) = pointBounds57880 := by
 decide +kernel
def cuts57881 : List PrefixCut := [⟨64,214297750,214297873⟩]
theorem checked57881 : checkPrefixCuts (2^48) 7590510593 10 Manual.Count131072.C057881.packed 64 cuts57881 = true := by
 decide +kernel
def cuts57882 : List PrefixCut := [⟨20,68415795,68415835⟩,
⟨64,215443601,215443725⟩]
theorem checked57882 : checkPrefixCuts (2^48) 7590641665 10 Manual.Count131072.C057882.packed 64 cuts57882 = true := by
 decide +kernel
def pointBounds57882 : List (Nat × Nat × Nat) := [(7590682624,113472817069067,113473205222995)]
theorem point_links_checked57882 : (cuts57882.take 1).map (fun c => (7590641665-1+2*2^10*c.k,113472748653272+c.lower,113473136807160+c.upper)) = pointBounds57882 := by
 decide +kernel
def cuts57883 : List PrefixCut := [⟨64,213548755,213548877⟩]
theorem checked57883 : checkPrefixCuts (2^48) 7590772737 10 Manual.Count131072.C057883.packed 64 cuts57883 = true := by
 decide +kernel
def cuts57884 : List PrefixCut := [⟨8,26549646,26549660⟩,
⟨64,213767541,213767660⟩]
theorem checked57884 : checkPrefixCuts (2^48) 7590903809 10 Manual.Count131072.C057884.packed 64 cuts57884 = true := by
 decide +kernel
def pointBounds57884 : List (Nat × Nat × Nat) := [(7590920192,113473204195274,113473592349422)]
theorem point_links_checked57884 : (cuts57884.take 1).map (fun c => (7590903809-1+2*2^10*c.k,113473177645628+c.lower,113473565799762+c.upper)) = pointBounds57884 := by
 decide +kernel
def cuts57885 : List PrefixCut := [⟨60,197782651,197782763⟩,
⟨64,210834562,210834681⟩]
theorem checked57885 : checkPrefixCuts (2^48) 7591034881 10 Manual.Count131072.C057885.packed 64 cuts57885 = true := by
 decide +kernel
def pointBounds57885 : List (Nat × Nat × Nat) := [(7591157760,113473589195820,113473977350185)]
theorem point_links_checked57885 : (cuts57885.take 1).map (fun c => (7591034881-1+2*2^10*c.k,113473391413169+c.lower,113473779567422+c.upper)) = pointBounds57885 := by
 decide +kernel
def cuts57886 : List PrefixCut := [⟨64,210793834,210793955⟩]
theorem checked57886 : checkPrefixCuts (2^48) 7591165953 10 Manual.Count131072.C057886.packed 64 cuts57886 = true := by
 decide +kernel
def cuts57887 : List PrefixCut := [⟨48,158880895,158880985⟩,
⟨64,212421628,212421748⟩]
theorem checked57887 : checkPrefixCuts (2^48) 7591297025 10 Manual.Count131072.C057887.packed 64 cuts57887 = true := by
 decide +kernel
def pointBounds57887 : List (Nat × Nat × Nat) := [(7591395328,113473971922460,113474360077043)]
theorem point_links_checked57887 : (cuts57887.take 1).map (fun c => (7591297025-1+2*2^10*c.k,113473813041565+c.lower,113474201196058+c.upper)) = pointBounds57887 := by
 decide +kernel
def cuts57888 : List PrefixCut := [⟨64,208005740,208005858⟩]
theorem checked57888 : checkPrefixCuts (2^48) 7591428097 10 Manual.Count131072.C057888.packed 64 cuts57888 = true := by
 decide +kernel
def cuts57889 : List PrefixCut := [⟨36,122206357,122206427⟩,
⟨64,217048938,217049064⟩]
theorem checked57889 : checkPrefixCuts (2^48) 7591559169 10 Manual.Count131072.C057889.packed 64 cuts57889 = true := by
 decide +kernel
def pointBounds57889 : List (Nat × Nat × Nat) := [(7591632896,113474355675290,113474743830091)]
theorem point_links_checked57889 : (cuts57889.take 1).map (fun c => (7591559169-1+2*2^10*c.k,113474233468933+c.lower,113474621623664+c.upper)) = pointBounds57889 := by
 decide +kernel
def cuts57890 : List PrefixCut := [⟨64,209778209,209778326⟩]
theorem checked57890 : checkPrefixCuts (2^48) 7591690241 10 Manual.Count131072.C057890.packed 64 cuts57890 = true := by
 decide +kernel
def cuts57891 : List PrefixCut := [⟨24,78193180,78193226⟩,
⟨64,214891027,214891151⟩]
theorem checked57891 : checkPrefixCuts (2^48) 7591821313 10 Manual.Count131072.C057891.packed 64 cuts57891 = true := by
 decide +kernel
def pointBounds57891 : List (Nat × Nat × Nat) := [(7591870464,113474738489260,113475126644280)]
theorem point_links_checked57891 : (cuts57891.take 1).map (fun c => (7591821313-1+2*2^10*c.k,113474660296080+c.lower,113475048451054+c.upper)) = pointBounds57891 := by
 decide +kernel
def cuts57892 : List PrefixCut := [⟨64,213441406,213441528⟩]
theorem checked57892 : checkPrefixCuts (2^48) 7591952385 10 Manual.Count131072.C057892.packed 64 cuts57892 = true := by
 decide +kernel
def cuts57893 : List PrefixCut := [⟨12,40263158,40263180⟩,
⟨64,213548954,213549073⟩]
theorem checked57893 : checkPrefixCuts (2^48) 7592083457 10 Manual.Count131072.C057893.packed 64 cuts57893 = true := by
 decide +kernel
def pointBounds57893 : List (Nat × Nat × Nat) := [(7592108032,113475128891671,113475517046913)]
theorem point_links_checked57893 : (cuts57893.take 1).map (fun c => (7592083457-1+2*2^10*c.k,113475088628513+c.lower,113475476783733+c.upper)) = pointBounds57893 := by
 decide +kernel
def cuts57894 : List PrefixCut := [⟨64,217289729,217289850⟩]
theorem checked57894 : checkPrefixCuts (2^48) 7592214529 10 Manual.Count131072.C057894.packed 64 cuts57894 = true := by
 decide +kernel
def pointBounds57894 : List (Nat × Nat × Nat) := [(7592345600,113475519467196,113475907622656)]
theorem point_links_checked57894 : (cuts57894.take 1).map (fun c => (7592214529-1+2*2^10*c.k,113475302177467+c.lower,113475690332806+c.upper)) = pointBounds57894 := by
 decide +kernel
def cuts57895 : List PrefixCut := [⟨64,214839141,214839260⟩]
theorem checked57895 : checkPrefixCuts (2^48) 7592345601 10 Manual.Count131072.C057895.packed 64 cuts57895 = true := by
 decide +kernel
def cuts57896 : List PrefixCut := [⟨52,174352480,174352578⟩,
⟨64,215428577,215428699⟩]
theorem checked57896 : checkPrefixCuts (2^48) 7592476673 10 Manual.Count131072.C057896.packed 64 cuts57896 = true := by
 decide +kernel
def pointBounds57896 : List (Nat × Nat × Nat) := [(7592583168,113475908658817,113476296814494)]
theorem point_links_checked57896 : (cuts57896.take 1).map (fun c => (7592476673-1+2*2^10*c.k,113475734306337+c.lower,113476122461916+c.upper)) = pointBounds57896 := by
 decide +kernel
def cuts57897 : List PrefixCut := [⟨64,214016140,214016257⟩]
theorem checked57897 : checkPrefixCuts (2^48) 7592607745 10 Manual.Count131072.C057897.packed 64 cuts57897 = true := by
 decide +kernel
def cuts57898 : List PrefixCut := [⟨40,132938003,132938080⟩,
⟨64,211751098,211751220⟩]
theorem checked57898 : checkPrefixCuts (2^48) 7592738817 10 Manual.Count131072.C057898.packed 64 cuts57898 = true := by
 decide +kernel
def pointBounds57898 : List (Nat × Nat × Nat) := [(7592820736,113476296689057,113476684844952)]
theorem point_links_checked57898 : (cuts57898.take 1).map (fun c => (7592738817-1+2*2^10*c.k,113476163751054+c.lower,113476551906872+c.upper)) = pointBounds57898 := by
 decide +kernel
def cuts57899 : List PrefixCut := [⟨64,213267324,213267445⟩]
theorem checked57899 : checkPrefixCuts (2^48) 7592869889 10 Manual.Count131072.C057899.packed 64 cuts57899 = true := by
 decide +kernel
def cuts57900 : List PrefixCut := [⟨28,92267655,92267710⟩,
⟨64,212299838,212299959⟩]
theorem checked57900 : checkPrefixCuts (2^48) 7593000961 10 Manual.Count131072.C057900.packed 64 cuts57900 = true := by
 decide +kernel
def pointBounds57900 : List (Nat × Nat × Nat) := [(7593058304,113476681037131,113477069193247)]
theorem point_links_checked57900 : (cuts57900.take 1).map (fun c => (7593000961-1+2*2^10*c.k,113476588769476+c.lower,113476976925537+c.upper)) = pointBounds57900 := by
 decide +kernel
def cuts57901 : List PrefixCut := [⟨64,212778063,212778190⟩]
theorem checked57901 : checkPrefixCuts (2^48) 7593132033 10 Manual.Count131072.C057901.packed 64 cuts57901 = true := by
 decide +kernel
def cuts57902 : List PrefixCut := [⟨16,54862047,54862079⟩,
⟨64,214776116,214776241⟩]
theorem checked57902 : checkPrefixCuts (2^48) 7593263105 10 Manual.Count131072.C057902.packed 64 cuts57902 = true := by
 decide +kernel
def pointBounds57902 : List (Nat × Nat × Nat) := [(7593295872,113477068709424,113477456865765)]
theorem point_links_checked57902 : (cuts57902.take 1).map (fun c => (7593263105-1+2*2^10*c.k,113477013847377+c.lower,113477402003686+c.upper)) = pointBounds57902 := by
 decide +kernel
def cuts57903 : List PrefixCut := [⟨64,213586220,213586343⟩]
theorem checked57903 : checkPrefixCuts (2^48) 7593394177 10 Manual.Count131072.C057903.packed 64 cuts57903 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000246
