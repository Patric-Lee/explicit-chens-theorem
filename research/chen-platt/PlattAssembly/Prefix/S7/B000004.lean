import PlattAssemblyKernel
import PlattCertificates.Count131072.C060128
import PlattCertificates.Count131072.C060129
import PlattCertificates.Count131072.C060130
import PlattCertificates.Count131072.C060131
import PlattCertificates.Count131072.C060132
import PlattCertificates.Count131072.C060133
import PlattCertificates.Count131072.C060134
import PlattCertificates.Count131072.C060135
import PlattCertificates.Count131072.C060136
import PlattCertificates.Count131072.C060137
import PlattCertificates.Count131072.C060138
import PlattCertificates.Count131072.C060139
import PlattCertificates.Count131072.C060140
import PlattCertificates.Count131072.C060141
import PlattCertificates.Count131072.C060142
import PlattCertificates.Count131072.C060143
import PlattCertificates.Count131072.C060144
import PlattCertificates.Count131072.C060145
import PlattCertificates.Count131072.C060146
import PlattCertificates.Count131072.C060147
import PlattCertificates.Count131072.C060148
import PlattCertificates.Count131072.C060149
import PlattCertificates.Count131072.C060150
import PlattCertificates.Count131072.C060151
import PlattCertificates.Count131072.C060152
import PlattCertificates.Count131072.C060153
import PlattCertificates.Count131072.C060154
import PlattCertificates.Count131072.C060155
import PlattCertificates.Count131072.C060156
import PlattCertificates.Count131072.C060157
import PlattCertificates.Count131072.C060158
import PlattCertificates.Count131072.C060159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60128 : List PrefixCut := [⟨64,202580952,202581068⟩]
theorem checked60128 : checkPrefixCuts (2^48) 7885029377 10 Manual.Count131072.C060128.packed 64 cuts60128 = true := by
 decide +kernel
def cuts60129 : List PrefixCut := [⟨27,86849982,86850032⟩,
⟨64,204433808,204433926⟩]
theorem checked60129 : checkPrefixCuts (2^48) 7885160449 10 Manual.Count131072.C060129.packed 64 cuts60129 = true := by
 decide +kernel
def pointBounds60129 : List (Nat × Nat × Nat) := [(7885215744,113943386875491,113943775297895)]
theorem point_links_checked60129 : (cuts60129.take 1).map (fun c => (7885160449-1+2*2^10*c.k,113943300025509+c.lower,113943688447863+c.upper)) = pointBounds60129 := by
 decide +kernel
def cuts60130 : List PrefixCut := [⟨64,207785845,207785960⟩]
theorem checked60130 : checkPrefixCuts (2^48) 7885291521 10 Manual.Count131072.C060130.packed 64 cuts60130 = true := by
 decide +kernel
def cuts60131 : List PrefixCut := [⟨20,64573174,64573211⟩,
⟨64,205533561,205533680⟩]
theorem checked60131 : checkPrefixCuts (2^48) 7885422593 10 Manual.Count131072.C060131.packed 64 cuts60131 = true := by
 decide +kernel
def pointBounds60131 : List (Nat × Nat × Nat) := [(7885463552,113943776818336,113944165240960)]
theorem point_links_checked60131 : (cuts60131.take 1).map (fun c => (7885422593-1+2*2^10*c.k,113943712245162+c.lower,113944100667749+c.upper)) = pointBounds60131 := by
 decide +kernel
def cuts60132 : List PrefixCut := [⟨64,203888191,203888306⟩]
theorem checked60132 : checkPrefixCuts (2^48) 7885553665 10 Manual.Count131072.C060132.packed 64 cuts60132 = true := by
 decide +kernel
def cuts60133 : List PrefixCut := [⟨13,42262118,42262138⟩,
⟨64,207525600,207525715⟩]
theorem checked60133 : checkPrefixCuts (2^48) 7885684737 10 Manual.Count131072.C060133.packed 64 cuts60133 = true := by
 decide +kernel
def pointBounds60133 : List (Nat × Nat × Nat) := [(7885711360,113944163929032,113944552351873)]
theorem point_links_checked60133 : (cuts60133.take 1).map (fun c => (7885684737-1+2*2^10*c.k,113944121666914+c.lower,113944510089735+c.upper)) = pointBounds60133 := by
 decide +kernel
def cuts60134 : List PrefixCut := [⟨64,205166368,205166486⟩]
theorem checked60134 : checkPrefixCuts (2^48) 7885815809 10 Manual.Count131072.C060134.packed 64 cuts60134 = true := by
 decide +kernel
def cuts60135 : List PrefixCut := [⟨6,19631258,19631270⟩,
⟨64,205020207,205020324⟩]
theorem checked60135 : checkPrefixCuts (2^48) 7885946881 10 Manual.Count131072.C060135.packed 64 cuts60135 = true := by
 decide +kernel
def pointBounds60135 : List (Nat × Nat × Nat) := [(7885959168,113944553990140,113944942413206)]
theorem point_links_checked60135 : (cuts60135.take 1).map (fun c => (7885946881-1+2*2^10*c.k,113944534358882+c.lower,113944922781936+c.upper)) = pointBounds60135 := by
 decide +kernel
def cuts60136 : List PrefixCut := [⟨63,200019876,200019992⟩,
⟨64,203160776,203160894⟩]
theorem checked60136 : checkPrefixCuts (2^48) 7886077953 10 Manual.Count131072.C060136.packed 64 cuts60136 = true := by
 decide +kernel
def pointBounds60136 : List (Nat × Nat × Nat) := [(7886206976,113944939398965,113945327822252)]
theorem point_links_checked60136 : (cuts60136.take 1).map (fun c => (7886077953-1+2*2^10*c.k,113944739379089+c.lower,113945127802260+c.upper)) = pointBounds60136 := by
 decide +kernel
def cuts60137 : List PrefixCut := [⟨64,205049055,205049169⟩]
theorem checked60137 : checkPrefixCuts (2^48) 7886209025 10 Manual.Count131072.C060137.packed 64 cuts60137 = true := by
 decide +kernel
def cuts60138 : List PrefixCut := [⟨56,179241147,179241253⟩,
⟨64,204867207,204867328⟩]
theorem checked60138 : checkPrefixCuts (2^48) 7886340097 10 Manual.Count131072.C060138.packed 64 cuts60138 = true := by
 decide +kernel
def pointBounds60138 : List (Nat × Nat × Nat) := [(7886454784,113945326830067,113945715253576)]
theorem point_links_checked60138 : (cuts60138.take 1).map (fun c => (7886340097-1+2*2^10*c.k,113945147588920+c.lower,113945536012323+c.upper)) = pointBounds60138 := by
 decide +kernel
def cuts60139 : List PrefixCut := [⟨64,203793094,203793208⟩]
theorem checked60139 : checkPrefixCuts (2^48) 7886471169 10 Manual.Count131072.C060139.packed 64 cuts60139 = true := by
 decide +kernel
def cuts60140 : List PrefixCut := [⟨49,154180933,154181022⟩,
⟨64,204432084,204432202⟩]
theorem checked60140 : checkPrefixCuts (2^48) 7886602241 10 Manual.Count131072.C060140.packed 64 cuts60140 = true := by
 decide +kernel
def pointBounds60140 : List (Nat × Nat × Nat) := [(7886702592,113945710430154,113946098853881)]
theorem point_links_checked60140 : (cuts60140.take 1).map (fun c => (7886602241-1+2*2^10*c.k,113945556249221+c.lower,113945944672859+c.upper)) = pointBounds60140 := by
 decide +kernel
def cuts60141 : List PrefixCut := [⟨64,203929069,203929186⟩]
theorem checked60141 : checkPrefixCuts (2^48) 7886733313 10 Manual.Count131072.C060141.packed 64 cuts60141 = true := by
 decide +kernel
def cuts60142 : List PrefixCut := [⟨42,136617036,136617112⟩,
⟨64,207458875,207458993⟩]
theorem checked60142 : checkPrefixCuts (2^48) 7886864385 10 Manual.Count131072.C060142.packed 64 cuts60142 = true := by
 decide +kernel
def pointBounds60142 : List (Nat × Nat × Nat) := [(7886950400,113946101227410,113946489651359)]
theorem point_links_checked60142 : (cuts60142.take 1).map (fun c => (7886864385-1+2*2^10*c.k,113945964610374+c.lower,113946353034247+c.upper)) = pointBounds60142 := by
 decide +kernel
def cuts60143 : List PrefixCut := [⟨64,206491831,206491950⟩]
theorem checked60143 : checkPrefixCuts (2^48) 7886995457 10 Manual.Count131072.C060143.packed 64 cuts60143 = true := by
 decide +kernel
def cuts60144 : List PrefixCut := [⟨35,111095885,111095949⟩,
⟨64,205310701,205310819⟩]
theorem checked60144 : checkPrefixCuts (2^48) 7887126529 10 Manual.Count131072.C060144.packed 64 cuts60144 = true := by
 decide +kernel
def pointBounds60144 : List (Nat × Nat × Nat) := [(7887198208,113946489656965,113946878081139)]
theorem point_links_checked60144 : (cuts60144.take 1).map (fun c => (7887126529-1+2*2^10*c.k,113946378561080+c.lower,113946766985190+c.upper)) = pointBounds60144 := by
 decide +kernel
def cuts60145 : List PrefixCut := [⟨64,201774293,201774415⟩]
theorem checked60145 : checkPrefixCuts (2^48) 7887257601 10 Manual.Count131072.C060145.packed 64 cuts60145 = true := by
 decide +kernel
def cuts60146 : List PrefixCut := [⟨28,90215660,90215707⟩,
⟨64,204269000,204269112⟩]
theorem checked60146 : checkPrefixCuts (2^48) 7887388673 10 Manual.Count131072.C060146.packed 64 cuts60146 = true := by
 decide +kernel
def pointBounds60146 : List (Nat × Nat × Nat) := [(7887446016,113946875861734,113947264286131)]
theorem point_links_checked60146 : (cuts60146.take 1).map (fun c => (7887388673-1+2*2^10*c.k,113946785646074+c.lower,113947174070424+c.upper)) = pointBounds60146 := by
 decide +kernel
def cuts60147 : List PrefixCut := [⟨64,203694605,203694721⟩]
theorem checked60147 : checkPrefixCuts (2^48) 7887519745 10 Manual.Count131072.C060147.packed 64 cuts60147 = true := by
 decide +kernel
def cuts60148 : List PrefixCut := [⟨21,66517621,66517661⟩,
⟨64,206117831,206117950⟩]
theorem checked60148 : checkPrefixCuts (2^48) 7887650817 10 Manual.Count131072.C060148.packed 64 cuts60148 = true := by
 decide +kernel
def pointBounds60148 : List (Nat × Nat × Nat) := [(7887693824,113947260127300,113947648551918)]
theorem point_links_checked60148 : (cuts60148.take 1).map (fun c => (7887650817-1+2*2^10*c.k,113947193609679+c.lower,113947582034257+c.upper)) = pointBounds60148 := by
 decide +kernel
def cuts60149 : List PrefixCut := [⟨64,205472090,205472213⟩]
theorem checked60149 : checkPrefixCuts (2^48) 7887781889 10 Manual.Count131072.C060149.packed 64 cuts60149 = true := by
 decide +kernel
def cuts60150 : List PrefixCut := [⟨14,44997858,44997884⟩,
⟨64,205718461,205718581⟩]
theorem checked60150 : checkPrefixCuts (2^48) 7887912961 10 Manual.Count131072.C060150.packed 64 cuts60150 = true := by
 decide +kernel
def pointBounds60150 : List (Nat × Nat × Nat) := [(7887941632,113947650197458,113948038622304)]
theorem point_links_checked60150 : (cuts60150.take 1).map (fun c => (7887912961-1+2*2^10*c.k,113947605199600+c.lower,113947993624420+c.upper)) = pointBounds60150 := by
 decide +kernel
def cuts60151 : List PrefixCut := [⟨64,206393017,206393138⟩]
theorem checked60151 : checkPrefixCuts (2^48) 7888044033 10 Manual.Count131072.C060151.packed 64 cuts60151 = true := by
 decide +kernel
def cuts60152 : List PrefixCut := [⟨7,21516917,21516931⟩,
⟨64,207031885,207032003⟩]
theorem checked60152 : checkPrefixCuts (2^48) 7888175105 10 Manual.Count131072.C060152.packed 64 cuts60152 = true := by
 decide +kernel
def pointBounds60152 : List (Nat × Nat × Nat) := [(7888189440,113948038827995,113948427253070)]
theorem point_links_checked60152 : (cuts60152.take 1).map (fun c => (7888175105-1+2*2^10*c.k,113948017311078+c.lower,113948405736139+c.upper)) = pointBounds60152 := by
 decide +kernel
def cuts60153 : List PrefixCut := [⟨64,204102499,204102620⟩]
theorem checked60153 : checkPrefixCuts (2^48) 7888306177 10 Manual.Count131072.C060153.packed 64 cuts60153 = true := by
 decide +kernel
def pointBounds60153 : List (Nat × Nat × Nat) := [(7888437248,113948428445462,113948816870762)]
theorem point_links_checked60153 : (cuts60153.take 1).map (fun c => (7888306177-1+2*2^10*c.k,113948224342963+c.lower,113948612768142+c.upper)) = pointBounds60153 := by
 decide +kernel
def cuts60154 : List PrefixCut := [⟨64,204670026,204670138⟩]
theorem checked60154 : checkPrefixCuts (2^48) 7888437249 10 Manual.Count131072.C060154.packed 64 cuts60154 = true := by
 decide +kernel
def cuts60155 : List PrefixCut := [⟨57,181367044,181367148⟩,
⟨64,203917314,203917432⟩]
theorem checked60155 : checkPrefixCuts (2^48) 7888568321 10 Manual.Count131072.C060155.packed 64 cuts60155 = true := by
 decide +kernel
def pointBounds60155 : List (Nat × Nat × Nat) := [(7888685056,113948814482532,113949202908048)]
theorem point_links_checked60155 : (cuts60155.take 1).map (fun c => (7888568321-1+2*2^10*c.k,113948633115488+c.lower,113949021540900+c.upper)) = pointBounds60155 := by
 decide +kernel
def cuts60156 : List PrefixCut := [⟨64,204877312,204877429⟩]
theorem checked60156 : checkPrefixCuts (2^48) 7888699393 10 Manual.Count131072.C060156.packed 64 cuts60156 = true := by
 decide +kernel
def cuts60157 : List PrefixCut := [⟨50,161023612,161023702⟩,
⟨64,205658860,205658972⟩]
theorem checked60157 : checkPrefixCuts (2^48) 7888830465 10 Manual.Count131072.C060157.packed 64 cuts60157 = true := by
 decide +kernel
def pointBounds60157 : List (Nat × Nat × Nat) := [(7888932864,113949202933726,113949591359463)]
theorem point_links_checked60157 : (cuts60157.take 1).map (fun c => (7888830465-1+2*2^10*c.k,113949041910114+c.lower,113949430335761+c.upper)) = pointBounds60157 := by
 decide +kernel
def cuts60158 : List PrefixCut := [⟨64,203193566,203193683⟩]
theorem checked60158 : checkPrefixCuts (2^48) 7888961537 10 Manual.Count131072.C060158.packed 64 cuts60158 = true := by
 decide +kernel
def cuts60159 : List PrefixCut := [⟨43,139182976,139183058⟩,
⟨64,204581665,204581783⟩]
theorem checked60159 : checkPrefixCuts (2^48) 7889092609 10 Manual.Count131072.C060159.packed 64 cuts60159 = true := by
 decide +kernel
def pointBounds60159 : List (Nat × Nat × Nat) := [(7889180672,113949589945516,113949978371474)]
theorem point_links_checked60159 : (cuts60159.take 1).map (fun c => (7889092609-1+2*2^10*c.k,113949450762540+c.lower,113949839188416+c.upper)) = pointBounds60159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000004
