import PlattAssemblyKernel
import PlattCertificates.Count131072.C070128
import PlattCertificates.Count131072.C070129
import PlattCertificates.Count131072.C070130
import PlattCertificates.Count131072.C070131
import PlattCertificates.Count131072.C070132
import PlattCertificates.Count131072.C070133
import PlattCertificates.Count131072.C070134
import PlattCertificates.Count131072.C070135
import PlattCertificates.Count131072.C070136
import PlattCertificates.Count131072.C070137
import PlattCertificates.Count131072.C070138
import PlattCertificates.Count131072.C070139
import PlattCertificates.Count131072.C070140
import PlattCertificates.Count131072.C070141
import PlattCertificates.Count131072.C070142
import PlattCertificates.Count131072.C070143
import PlattCertificates.Count131072.C070144
import PlattCertificates.Count131072.C070145
import PlattCertificates.Count131072.C070146
import PlattCertificates.Count131072.C070147
import PlattCertificates.Count131072.C070148
import PlattCertificates.Count131072.C070149
import PlattCertificates.Count131072.C070150
import PlattCertificates.Count131072.C070151
import PlattCertificates.Count131072.C070152
import PlattCertificates.Count131072.C070153
import PlattCertificates.Count131072.C070154
import PlattCertificates.Count131072.C070155
import PlattCertificates.Count131072.C070156
import PlattCertificates.Count131072.C070157
import PlattCertificates.Count131072.C070158
import PlattCertificates.Count131072.C070159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70128 : List PrefixCut := [⟨64,172083925,172084027⟩]
theorem checked70128 : checkPrefixCuts (2^48) 9195749377 10 Manual.Count131072.C070128.packed 64 cuts70128 = true := by
 decide +kernel
def cuts70129 : List PrefixCut := [⟨34,91489365,91489421⟩,
⟨64,175325963,175326065⟩]
theorem checked70129 : checkPrefixCuts (2^48) 9195880449 10 Manual.Count131072.C070129.packed 64 cuts70129 = true := by
 decide +kernel
def pointBounds70129 : List (Nat × Nat × Nat) := [(9195950080,115836376602662,115836766121143)]
theorem point_links_checked70129 : (cuts70129.take 1).map (fun c => (9195880449-1+2*2^10*c.k,115836285113297+c.lower,115836674631722+c.upper)) = pointBounds70129 := by
 decide +kernel
def cuts70130 : List PrefixCut := [⟨64,176302937,176303041⟩]
theorem checked70130 : checkPrefixCuts (2^48) 9196011521 10 Manual.Count131072.C070130.packed 64 cuts70130 = true := by
 decide +kernel
def cuts70131 : List PrefixCut := [⟨47,126073410,126073487⟩,
⟨64,173117219,173117323⟩]
theorem checked70131 : checkPrefixCuts (2^48) 9196142593 10 Manual.Count131072.C070131.packed 64 cuts70131 = true := by
 decide +kernel
def pointBounds70131 : List (Nat × Nat × Nat) := [(9196238848,115836762815607,115837152334315)]
theorem point_links_checked70131 : (cuts70131.take 1).map (fun c => (9196142593-1+2*2^10*c.k,115836636742197+c.lower,115837026260828+c.upper)) = pointBounds70131 := by
 decide +kernel
def cuts70132 : List PrefixCut := [⟨64,174920579,174920682⟩]
theorem checked70132 : checkPrefixCuts (2^48) 9196273665 10 Manual.Count131072.C070132.packed 64 cuts70132 = true := by
 decide +kernel
def cuts70133 : List PrefixCut := [⟨60,163746667,163746759⟩,
⟨64,175928109,175928206⟩]
theorem checked70133 : checkPrefixCuts (2^48) 9196404737 10 Manual.Count131072.C070133.packed 64 cuts70133 = true := by
 decide +kernel
def pointBounds70133 : List (Nat × Nat × Nat) := [(9196527616,115837148526662,115837538045592)]
theorem point_links_checked70133 : (cuts70133.take 1).map (fun c => (9196404737-1+2*2^10*c.k,115836984779995+c.lower,115837374298833+c.upper)) = pointBounds70133 := by
 decide +kernel
def cuts70134 : List PrefixCut := [⟨64,174762571,174762674⟩]
theorem checked70134 : checkPrefixCuts (2^48) 9196535809 10 Manual.Count131072.C070134.packed 64 cuts70134 = true := by
 decide +kernel
def cuts70135 : List PrefixCut := [⟨64,174882496,174882606⟩]
theorem checked70135 : checkPrefixCuts (2^48) 9196666881 10 Manual.Count131072.C070135.packed 64 cuts70135 = true := by
 decide +kernel
def cuts70136 : List PrefixCut := [⟨9,24698815,24698830⟩,
⟨64,171299165,171299262⟩]
theorem checked70136 : checkPrefixCuts (2^48) 9196797953 10 Manual.Count131072.C070136.packed 64 cuts70136 = true := by
 decide +kernel
def pointBounds70136 : List (Nat × Nat × Nat) := [(9196816384,115837535051986,115837924571149)]
theorem point_links_checked70136 : (cuts70136.take 1).map (fun c => (9196797953-1+2*2^10*c.k,115837510353171+c.lower,115837899872319+c.upper)) = pointBounds70136 := by
 decide +kernel
def cuts70137 : List PrefixCut := [⟨64,174877522,174877619⟩]
theorem checked70137 : checkPrefixCuts (2^48) 9196929025 10 Manual.Count131072.C070137.packed 64 cuts70137 = true := by
 decide +kernel
def cuts70138 : List PrefixCut := [⟨22,59342710,59342747⟩,
⟨64,173559020,173559127⟩]
theorem checked70138 : checkPrefixCuts (2^48) 9197060097 10 Manual.Count131072.C070138.packed 64 cuts70138 = true := by
 decide +kernel
def pointBounds70138 : List (Nat × Nat × Nat) := [(9197105152,115837915872568,115838305391947)]
theorem point_links_checked70138 : (cuts70138.take 1).map (fun c => (9197060097-1+2*2^10*c.k,115837856529858+c.lower,115838246049200+c.upper)) = pointBounds70138 := by
 decide +kernel
def cuts70139 : List PrefixCut := [⟨64,174719507,174719613⟩]
theorem checked70139 : checkPrefixCuts (2^48) 9197191169 10 Manual.Count131072.C070139.packed 64 cuts70139 = true := by
 decide +kernel
def cuts70140 : List PrefixCut := [⟨35,93831512,93831565⟩,
⟨64,171748445,171748551⟩]
theorem checked70140 : checkPrefixCuts (2^48) 9197322241 10 Manual.Count131072.C070140.packed 64 cuts70140 = true := by
 decide +kernel
def pointBounds70140 : List (Nat × Nat × Nat) := [(9197393920,115838298639897,115838688159505)]
theorem point_links_checked70140 : (cuts70140.take 1).map (fun c => (9197322241-1+2*2^10*c.k,115838204808385+c.lower,115838594327940+c.upper)) = pointBounds70140 := by
 decide +kernel
def cuts70141 : List PrefixCut := [⟨64,174653318,174653420⟩]
theorem checked70141 : checkPrefixCuts (2^48) 9197453313 10 Manual.Count131072.C070141.packed 64 cuts70141 = true := by
 decide +kernel
def cuts70142 : List PrefixCut := [⟨48,128930309,128930388⟩,
⟨64,172784054,172784156⟩]
theorem checked70142 : checkPrefixCuts (2^48) 9197584385 10 Manual.Count131072.C070142.packed 64 cuts70142 = true := by
 decide +kernel
def pointBounds70142 : List (Nat × Nat × Nat) := [(9197682688,115838680140457,115839069660299)]
theorem point_links_checked70142 : (cuts70142.take 1).map (fun c => (9197584385-1+2*2^10*c.k,115838551210148+c.lower,115838940729911+c.upper)) = pointBounds70142 := by
 decide +kernel
def cuts70143 : List PrefixCut := [⟨64,175750023,175750129⟩]
theorem checked70143 : checkPrefixCuts (2^48) 9197715457 10 Manual.Count131072.C070143.packed 64 cuts70143 = true := by
 decide +kernel
def cuts70144 : List PrefixCut := [⟨61,166138539,166138638⟩,
⟨64,174156219,174156324⟩]
theorem checked70144 : checkPrefixCuts (2^48) 9197846529 10 Manual.Count131072.C070144.packed 64 cuts70144 = true := by
 decide +kernel
def pointBounds70144 : List (Nat × Nat × Nat) := [(9197971456,115839065882764,115839455402834)]
theorem point_links_checked70144 : (cuts70144.take 1).map (fun c => (9197846529-1+2*2^10*c.k,115838899744225+c.lower,115839289264196+c.upper)) = pointBounds70144 := by
 decide +kernel
def cuts70145 : List PrefixCut := [⟨64,175714419,175714521⟩]
theorem checked70145 : checkPrefixCuts (2^48) 9197977601 10 Manual.Count131072.C070145.packed 64 cuts70145 = true := by
 decide +kernel
def cuts70146 : List PrefixCut := [⟨64,176079135,176079243⟩]
theorem checked70146 : checkPrefixCuts (2^48) 9198108673 10 Manual.Count131072.C070146.packed 64 cuts70146 = true := by
 decide +kernel
def cuts70147 : List PrefixCut := [⟨10,27816234,27816251⟩,
⟨64,175709409,175709513⟩]
theorem checked70147 : checkPrefixCuts (2^48) 9198239745 10 Manual.Count131072.C070147.packed 64 cuts70147 = true := by
 decide +kernel
def pointBounds70147 : List (Nat × Nat × Nat) := [(9198260224,115839453510232,115839843030535)]
theorem point_links_checked70147 : (cuts70147.take 1).map (fun c => (9198239745-1+2*2^10*c.k,115839425693998+c.lower,115839815214284+c.upper)) = pointBounds70147 := by
 decide +kernel
def cuts70148 : List PrefixCut := [⟨64,176471925,176472020⟩]
theorem checked70148 : checkPrefixCuts (2^48) 9198370817 10 Manual.Count131072.C070148.packed 64 cuts70148 = true := by
 decide +kernel
def cuts70149 : List PrefixCut := [⟨23,62577005,62577040⟩,
⟨64,175245408,175245511⟩]
theorem checked70149 : checkPrefixCuts (2^48) 9198501889 10 Manual.Count131072.C070149.packed 64 cuts70149 = true := by
 decide +kernel
def pointBounds70149 : List (Nat × Nat × Nat) := [(9198548992,115839840452337,115840229972857)]
theorem point_links_checked70149 : (cuts70149.take 1).map (fun c => (9198501889-1+2*2^10*c.k,115839777875332+c.lower,115840167395817+c.upper)) = pointBounds70149 := by
 decide +kernel
def cuts70150 : List PrefixCut := [⟨64,174569731,174569837⟩]
theorem checked70150 : checkPrefixCuts (2^48) 9198632961 10 Manual.Count131072.C070150.packed 64 cuts70150 = true := by
 decide +kernel
def cuts70151 : List PrefixCut := [⟨36,99569428,99569490⟩,
⟨64,175332221,175332329⟩]
theorem checked70151 : checkPrefixCuts (2^48) 9198764033 10 Manual.Count131072.C070151.packed 64 cuts70151 = true := by
 decide +kernel
def pointBounds70151 : List (Nat × Nat × Nat) := [(9198837760,115840227259899,115840616780655)]
theorem point_links_checked70151 : (cuts70151.take 1).map (fun c => (9198764033-1+2*2^10*c.k,115840127690471+c.lower,115840517211165+c.upper)) = pointBounds70151 := by
 decide +kernel
def cuts70152 : List PrefixCut := [⟨64,174778935,174779041⟩]
theorem checked70152 : checkPrefixCuts (2^48) 9198895105 10 Manual.Count131072.C070152.packed 64 cuts70152 = true := by
 decide +kernel
def cuts70153 : List PrefixCut := [⟨49,133193828,133193902⟩,
⟨64,174745845,174745942⟩]
theorem checked70153 : checkPrefixCuts (2^48) 9199026177 10 Manual.Count131072.C070153.packed 64 cuts70153 = true := by
 decide +kernel
def pointBounds70153 : List (Nat × Nat × Nat) := [(9199126528,115840610995455,115841000516437)]
theorem point_links_checked70153 : (cuts70153.take 1).map (fun c => (9199026177-1+2*2^10*c.k,115840477801627+c.lower,115840867322535+c.upper)) = pointBounds70153 := by
 decide +kernel
def cuts70154 : List PrefixCut := [⟨64,172387343,172387441⟩]
theorem checked70154 : checkPrefixCuts (2^48) 9199157249 10 Manual.Count131072.C070154.packed 64 cuts70154 = true := by
 decide +kernel
def cuts70155 : List PrefixCut := [⟨62,169202815,169202914⟩,
⟨64,175016252,175016354⟩]
theorem checked70155 : checkPrefixCuts (2^48) 9199288321 10 Manual.Count131072.C070155.packed 64 cuts70155 = true := by
 decide +kernel
def pointBounds70155 : List (Nat × Nat × Nat) := [(9199415296,115840994137630,115841383658832)]
theorem point_links_checked70155 : (cuts70155.take 1).map (fun c => (9199288321-1+2*2^10*c.k,115840824934815+c.lower,115841214455918+c.upper)) = pointBounds70155 := by
 decide +kernel
def cuts70156 : List PrefixCut := [⟨64,172168251,172168348⟩]
theorem checked70156 : checkPrefixCuts (2^48) 9199419393 10 Manual.Count131072.C070156.packed 64 cuts70156 = true := by
 decide +kernel
def cuts70157 : List PrefixCut := [⟨64,174399332,174399435⟩]
theorem checked70157 : checkPrefixCuts (2^48) 9199550465 10 Manual.Count131072.C070157.packed 64 cuts70157 = true := by
 decide +kernel
def cuts70158 : List PrefixCut := [⟨11,30565522,30565541⟩,
⟨64,175069962,175070061⟩]
theorem checked70158 : checkPrefixCuts (2^48) 9199681537 10 Manual.Count131072.C070158.packed 64 cuts70158 = true := by
 decide +kernel
def pointBounds70158 : List (Nat × Nat × Nat) := [(9199704064,115841377084172,115841766605596)]
theorem point_links_checked70158 : (cuts70158.take 1).map (fun c => (9199681537-1+2*2^10*c.k,115841346518650+c.lower,115841736040055+c.upper)) = pointBounds70158 := by
 decide +kernel
def cuts70159 : List PrefixCut := [⟨64,174608542,174608638⟩]
theorem checked70159 : checkPrefixCuts (2^48) 9199812609 10 Manual.Count131072.C070159.packed 64 cuts70159 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000004
