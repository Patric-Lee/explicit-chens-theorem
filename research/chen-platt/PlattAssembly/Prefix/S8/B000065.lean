import PlattAssemblyKernel
import PlattCertificates.Count131072.C072080
import PlattCertificates.Count131072.C072081
import PlattCertificates.Count131072.C072082
import PlattCertificates.Count131072.C072083
import PlattCertificates.Count131072.C072084
import PlattCertificates.Count131072.C072085
import PlattCertificates.Count131072.C072086
import PlattCertificates.Count131072.C072087
import PlattCertificates.Count131072.C072088
import PlattCertificates.Count131072.C072089
import PlattCertificates.Count131072.C072090
import PlattCertificates.Count131072.C072091
import PlattCertificates.Count131072.C072092
import PlattCertificates.Count131072.C072093
import PlattCertificates.Count131072.C072094
import PlattCertificates.Count131072.C072095
import PlattCertificates.Count131072.C072096
import PlattCertificates.Count131072.C072097
import PlattCertificates.Count131072.C072098
import PlattCertificates.Count131072.C072099
import PlattCertificates.Count131072.C072100
import PlattCertificates.Count131072.C072101
import PlattCertificates.Count131072.C072102
import PlattCertificates.Count131072.C072103
import PlattCertificates.Count131072.C072104
import PlattCertificates.Count131072.C072105
import PlattCertificates.Count131072.C072106
import PlattCertificates.Count131072.C072107
import PlattCertificates.Count131072.C072108
import PlattCertificates.Count131072.C072109
import PlattCertificates.Count131072.C072110
import PlattCertificates.Count131072.C072111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72080 : List PrefixCut := [⟨64,171654506,171654598⟩]
theorem checked72080 : checkPrefixCuts (2^48) 9451601921 10 Manual.Count131072.C072080.packed 64 cuts72080 = true := by
 decide +kernel
def cuts72081 : List PrefixCut := [⟨14,36331840,36331862⟩,
⟨64,168495440,168495544⟩]
theorem checked72081 : checkPrefixCuts (2^48) 9451732993 10 Manual.Count131072.C072081.packed 64 cuts72081 = true := by
 decide +kernel
def pointBounds72081 : List (Nat × Nat × Nat) := [(9451761664,116172873542248,116173263259649)]
theorem point_links_checked72081 : (cuts72081.take 1).map (fun c => (9451732993-1+2*2^10*c.k,116172837210408+c.lower,116173226927787+c.upper)) = pointBounds72081 := by
 decide +kernel
def cuts72082 : List PrefixCut := [⟨64,171471069,171471165⟩]
theorem checked72082 : checkPrefixCuts (2^48) 9451864065 10 Manual.Count131072.C072082.packed 64 cuts72082 = true := by
 decide +kernel
def cuts72083 : List PrefixCut := [⟨31,83560760,83560812⟩,
⟨64,169711720,169711821⟩]
theorem checked72083 : checkPrefixCuts (2^48) 9451995137 10 Manual.Count131072.C072083.packed 64 cuts72083 = true := by
 decide +kernel
def pointBounds72083 : List (Nat × Nat × Nat) := [(9452058624,116173260737677,116173650455308)]
theorem point_links_checked72083 : (cuts72083.take 1).map (fun c => (9451995137-1+2*2^10*c.k,116173177176917+c.lower,116173566894496+c.upper)) = pointBounds72083 := by
 decide +kernel
def cuts72084 : List PrefixCut := [⟨64,170632502,170632608⟩]
theorem checked72084 : checkPrefixCuts (2^48) 9452126209 10 Manual.Count131072.C072084.packed 64 cuts72084 = true := by
 decide +kernel
def cuts72085 : List PrefixCut := [⟨48,127243254,127243328⟩,
⟨64,169945233,169945335⟩]
theorem checked72085 : checkPrefixCuts (2^48) 9452257281 10 Manual.Count131072.C072085.packed 64 cuts72085 = true := by
 decide +kernel
def pointBounds72085 : List (Nat × Nat × Nat) := [(9452355584,116173644764393,116174034482253)]
theorem point_links_checked72085 : (cuts72085.take 1).map (fun c => (9452257281-1+2*2^10*c.k,116173517521139+c.lower,116173907238925+c.upper)) = pointBounds72085 := by
 decide +kernel
def cuts72086 : List PrefixCut := [⟨64,168543322,168543420⟩]
theorem checked72086 : checkPrefixCuts (2^48) 9452388353 10 Manual.Count131072.C072086.packed 64 cuts72086 = true := by
 decide +kernel
def cuts72087 : List PrefixCut := [⟨64,168600534,168600631⟩]
theorem checked72087 : checkPrefixCuts (2^48) 9452519425 10 Manual.Count131072.C072087.packed 64 cuts72087 = true := by
 decide +kernel
def cuts72088 : List PrefixCut := [⟨1,2263078,2263080⟩,
⟨64,170057273,170057371⟩]
theorem checked72088 : checkPrefixCuts (2^48) 9452650497 10 Manual.Count131072.C072088.packed 64 cuts72088 = true := by
 decide +kernel
def pointBounds72088 : List (Nat × Nat × Nat) := [(9452652544,116174026873306,116174416591391)]
theorem point_links_checked72088 : (cuts72088.take 1).map (fun c => (9452650497-1+2*2^10*c.k,116174024610228+c.lower,116174414328311+c.upper)) = pointBounds72088 := by
 decide +kernel
def cuts72089 : List PrefixCut := [⟨64,168178984,168179082⟩]
theorem checked72089 : checkPrefixCuts (2^48) 9452781569 10 Manual.Count131072.C072089.packed 64 cuts72089 = true := by
 decide +kernel
def cuts72090 : List PrefixCut := [⟨18,48833405,48833437⟩,
⟨64,169069943,169070045⟩]
theorem checked72090 : checkPrefixCuts (2^48) 9452912641 10 Manual.Count131072.C072090.packed 64 cuts72090 = true := by
 decide +kernel
def pointBounds72090 : List (Nat × Nat × Nat) := [(9452949504,116174411679890,116174801398201)]
theorem point_links_checked72090 : (cuts72090.take 1).map (fun c => (9452912641-1+2*2^10*c.k,116174362846485+c.lower,116174752564764+c.upper)) = pointBounds72090 := by
 decide +kernel
def cuts72091 : List PrefixCut := [⟨64,170437288,170437383⟩]
theorem checked72091 : checkPrefixCuts (2^48) 9453043713 10 Manual.Count131072.C072091.packed 64 cuts72091 = true := by
 decide +kernel
def cuts72092 : List PrefixCut := [⟨35,91411050,91411103⟩,
⟨64,167784904,167785000⟩]
theorem checked72092 : checkPrefixCuts (2^48) 9453174785 10 Manual.Count131072.C072092.packed 64 cuts72092 = true := by
 decide +kernel
def pointBounds72092 : List (Nat × Nat × Nat) := [(9453246464,116174793764766,116175183483295)]
theorem point_links_checked72092 : (cuts72092.take 1).map (fun c => (9453174785-1+2*2^10*c.k,116174702353716+c.lower,116175092072192+c.upper)) = pointBounds72092 := by
 decide +kernel
def cuts72093 : List PrefixCut := [⟨64,167038193,167038295⟩]
theorem checked72093 : checkPrefixCuts (2^48) 9453305857 10 Manual.Count131072.C072093.packed 64 cuts72093 = true := by
 decide +kernel
def cuts72094 : List PrefixCut := [⟨52,139345623,139345707⟩,
⟨64,169924033,169924137⟩]
theorem checked72094 : checkPrefixCuts (2^48) 9453436929 10 Manual.Count131072.C072094.packed 64 cuts72094 = true := by
 decide +kernel
def pointBounds72094 : List (Nat × Nat × Nat) := [(9453543424,116175176522436,116175566241194)]
theorem point_links_checked72094 : (cuts72094.take 1).map (fun c => (9453436929-1+2*2^10*c.k,116175037176813+c.lower,116175426895487+c.upper)) = pointBounds72094 := by
 decide +kernel
def cuts72095 : List PrefixCut := [⟨64,169653705,169653805⟩]
theorem checked72095 : checkPrefixCuts (2^48) 9453568001 10 Manual.Count131072.C072095.packed 64 cuts72095 = true := by
 decide +kernel
def cuts72096 : List PrefixCut := [⟨64,170514797,170514899⟩]
theorem checked72096 : checkPrefixCuts (2^48) 9453699073 10 Manual.Count131072.C072096.packed 64 cuts72096 = true := by
 decide +kernel
def cuts72097 : List PrefixCut := [⟨5,13130166,13130175⟩,
⟨64,169142848,169142951⟩]
theorem checked72097 : checkPrefixCuts (2^48) 9453830145 10 Manual.Count131072.C072097.packed 64 cuts72097 = true := by
 decide +kernel
def pointBounds72097 : List (Nat × Nat × Nat) := [(9453840384,116175560399514,116175950118503)]
theorem point_links_checked72097 : (cuts72097.take 1).map (fun c => (9453830145-1+2*2^10*c.k,116175547269348+c.lower,116175936988328+c.upper)) = pointBounds72097 := by
 decide +kernel
def cuts72098 : List PrefixCut := [⟨64,171343717,171343813⟩]
theorem checked72098 : checkPrefixCuts (2^48) 9453961217 10 Manual.Count131072.C072098.packed 64 cuts72098 = true := by
 decide +kernel
def cuts72099 : List PrefixCut := [⟨22,58533204,58533239⟩,
⟨64,171073380,171073472⟩]
theorem checked72099 : checkPrefixCuts (2^48) 9454092289 10 Manual.Count131072.C072099.packed 64 cuts72099 = true := by
 decide +kernel
def pointBounds72099 : List (Nat × Nat × Nat) := [(9454137344,116175946289117,116176336008331)]
theorem point_links_checked72099 : (cuts72099.take 1).map (fun c => (9454092289-1+2*2^10*c.k,116175887755913+c.lower,116176277475092+c.upper)) = pointBounds72099 := by
 decide +kernel
def cuts72100 : List PrefixCut := [⟨64,170028990,170029094⟩]
theorem checked72100 : checkPrefixCuts (2^48) 9454223361 10 Manual.Count131072.C072100.packed 64 cuts72100 = true := by
 decide +kernel
def cuts72101 : List PrefixCut := [⟨39,106136682,106136742⟩,
⟨64,173331299,173331400⟩]
theorem checked72101 : checkPrefixCuts (2^48) 9454354433 10 Manual.Count131072.C072101.packed 64 cuts72101 = true := by
 decide +kernel
def pointBounds72101 : List (Nat × Nat × Nat) := [(9454434304,116176334994965,116176724714400)]
theorem point_links_checked72101 : (cuts72101.take 1).map (fun c => (9454354433-1+2*2^10*c.k,116176228858283+c.lower,116176618577658+c.upper)) = pointBounds72101 := by
 decide +kernel
def cuts72102 : List PrefixCut := [⟨64,166451710,166451804⟩]
theorem checked72102 : checkPrefixCuts (2^48) 9454485505 10 Manual.Count131072.C072102.packed 64 cuts72102 = true := by
 decide +kernel
def cuts72103 : List PrefixCut := [⟨56,148080854,148080942⟩,
⟨64,167878417,167878517⟩]
theorem checked72103 : checkPrefixCuts (2^48) 9454616577 10 Manual.Count131072.C072103.packed 64 cuts72103 = true := by
 decide +kernel
def pointBounds72103 : List (Nat × Nat × Nat) := [(9454731264,116176716722146,116177106441804)]
theorem point_links_checked72103 : (cuts72103.take 1).map (fun c => (9454616577-1+2*2^10*c.k,116176568641292+c.lower,116176958360862+c.upper)) = pointBounds72103 := by
 decide +kernel
def cuts72104 : List PrefixCut := [⟨64,168858498,168858596⟩]
theorem checked72104 : checkPrefixCuts (2^48) 9454747649 10 Manual.Count131072.C072104.packed 64 cuts72104 = true := by
 decide +kernel
def cuts72105 : List PrefixCut := [⟨64,168885923,168886023⟩]
theorem checked72105 : checkPrefixCuts (2^48) 9454878721 10 Manual.Count131072.C072105.packed 64 cuts72105 = true := by
 decide +kernel
def cuts72106 : List PrefixCut := [⟨9,23815913,23815928⟩,
⟨64,169657609,169657708⟩]
theorem checked72106 : checkPrefixCuts (2^48) 9455009793 10 Manual.Count131072.C072106.packed 64 cuts72106 = true := by
 decide +kernel
def pointBounds72106 : List (Nat × Nat × Nat) := [(9455028224,116177098080043,116177487799926)]
theorem point_links_checked72106 : (cuts72106.take 1).map (fun c => (9455009793-1+2*2^10*c.k,116177074264130+c.lower,116177463983998+c.upper)) = pointBounds72106 := by
 decide +kernel
def cuts72107 : List PrefixCut := [⟨64,170250630,170250735⟩]
theorem checked72107 : checkPrefixCuts (2^48) 9455140865 10 Manual.Count131072.C072107.packed 64 cuts72107 = true := by
 decide +kernel
def cuts72108 : List PrefixCut := [⟨26,69986946,69986990⟩,
⟨64,171290196,171290300⟩]
theorem checked72108 : checkPrefixCuts (2^48) 9455271937 10 Manual.Count131072.C072108.packed 64 cuts72108 = true := by
 decide +kernel
def pointBounds72108 : List (Nat × Nat × Nat) := [(9455325184,116177484159315,116177873879431)]
theorem point_links_checked72108 : (cuts72108.take 1).map (fun c => (9455271937-1+2*2^10*c.k,116177414172369+c.lower,116177803892441+c.upper)) = pointBounds72108 := by
 decide +kernel
def cuts72109 : List PrefixCut := [⟨64,167239301,167239400⟩]
theorem checked72109 : checkPrefixCuts (2^48) 9455403009 10 Manual.Count131072.C072109.packed 64 cuts72109 = true := by
 decide +kernel
def cuts72110 : List PrefixCut := [⟨43,114279858,114279925⟩,
⟨64,170451930,170452031⟩]
theorem checked72110 : checkPrefixCuts (2^48) 9455534081 10 Manual.Count131072.C072110.packed 64 cuts72110 = true := by
 decide +kernel
def pointBounds72110 : List (Nat × Nat × Nat) := [(9455622144,116177866981724,116178256702066)]
theorem point_links_checked72110 : (cuts72110.take 1).map (fun c => (9455534081-1+2*2^10*c.k,116177752701866+c.lower,116178142422141+c.upper)) = pointBounds72110 := by
 decide +kernel
def cuts72111 : List PrefixCut := [⟨64,171670057,171670153⟩]
theorem checked72111 : checkPrefixCuts (2^48) 9455665153 10 Manual.Count131072.C072111.packed 64 cuts72111 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000065
