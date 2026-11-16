import PlattAssemblyKernel
import PlattCertificates.Count131072.C066144
import PlattCertificates.Count131072.C066145
import PlattCertificates.Count131072.C066146
import PlattCertificates.Count131072.C066147
import PlattCertificates.Count131072.C066148
import PlattCertificates.Count131072.C066149
import PlattCertificates.Count131072.C066150
import PlattCertificates.Count131072.C066151
import PlattCertificates.Count131072.C066152
import PlattCertificates.Count131072.C066153
import PlattCertificates.Count131072.C066154
import PlattCertificates.Count131072.C066155
import PlattCertificates.Count131072.C066156
import PlattCertificates.Count131072.C066157
import PlattCertificates.Count131072.C066158
import PlattCertificates.Count131072.C066159
import PlattCertificates.Count131072.C066160
import PlattCertificates.Count131072.C066161
import PlattCertificates.Count131072.C066162
import PlattCertificates.Count131072.C066163
import PlattCertificates.Count131072.C066164
import PlattCertificates.Count131072.C066165
import PlattCertificates.Count131072.C066166
import PlattCertificates.Count131072.C066167
import PlattCertificates.Count131072.C066168
import PlattCertificates.Count131072.C066169
import PlattCertificates.Count131072.C066170
import PlattCertificates.Count131072.C066171
import PlattCertificates.Count131072.C066172
import PlattCertificates.Count131072.C066173
import PlattCertificates.Count131072.C066174
import PlattCertificates.Count131072.C066175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66144 : List PrefixCut := [⟨64,187409264,187409373⟩]
theorem checked66144 : checkPrefixCuts (2^48) 8673558529 10 Manual.Count131072.C066144.packed 64 cuts66144 = true := by
 decide +kernel
def cuts66145 : List PrefixCut := [⟨31,89403769,89403814⟩,
⟨64,185199750,185199847⟩]
theorem checked66145 : checkPrefixCuts (2^48) 8673689601 10 Manual.Count131072.C066145.packed 64 cuts66145 = true := by
 decide +kernel
def pointBounds66145 : List (Nat × Nat × Nat) := [(8673753088,115118259259246,115118648357893)]
theorem point_links_checked66145 : (cuts66145.take 1).map (fun c => (8673689601-1+2*2^10*c.k,115118169855477+c.lower,115118558954079+c.upper)) = pointBounds66145 := by
 decide +kernel
def cuts66146 : List PrefixCut := [⟨64,188474482,188474590⟩]
theorem checked66146 : checkPrefixCuts (2^48) 8673820673 10 Manual.Count131072.C066146.packed 64 cuts66146 = true := by
 decide +kernel
def cuts66147 : List PrefixCut := [⟨36,105463983,105464042⟩,
⟨64,185648457,185648565⟩]
theorem checked66147 : checkPrefixCuts (2^48) 8673951745 10 Manual.Count131072.C066147.packed 64 cuts66147 = true := by
 decide +kernel
def pointBounds66147 : List (Nat × Nat × Nat) := [(8674025472,115118648993692,115119038092558)]
theorem point_links_checked66147 : (cuts66147.take 1).map (fun c => (8673951745-1+2*2^10*c.k,115118543529709+c.lower,115118932628516+c.upper)) = pointBounds66147 := by
 decide +kernel
def cuts66148 : List PrefixCut := [⟨64,183276799,183276905⟩]
theorem checked66148 : checkPrefixCuts (2^48) 8674082817 10 Manual.Count131072.C066148.packed 64 cuts66148 = true := by
 decide +kernel
def cuts66149 : List PrefixCut := [⟨41,118148470,118148543⟩,
⟨64,184766707,184766817⟩]
theorem checked66149 : checkPrefixCuts (2^48) 8674213889 10 Manual.Count131072.C066149.packed 64 cuts66149 = true := by
 decide +kernel
def pointBounds66149 : List (Nat × Nat × Nat) := [(8674297856,115119030603435,115119419702529)]
theorem point_links_checked66149 : (cuts66149.take 1).map (fun c => (8674213889-1+2*2^10*c.k,115118912454965+c.lower,115119301553986+c.upper)) = pointBounds66149 := by
 decide +kernel
def cuts66150 : List PrefixCut := [⟨64,187132685,187132787⟩]
theorem checked66150 : checkPrefixCuts (2^48) 8674344961 10 Manual.Count131072.C066150.packed 64 cuts66150 = true := by
 decide +kernel
def cuts66151 : List PrefixCut := [⟨46,136088834,136088909⟩,
⟨64,188590042,188590148⟩]
theorem checked66151 : checkPrefixCuts (2^48) 8674476033 10 Manual.Count131072.C066151.packed 64 cuts66151 = true := by
 decide +kernel
def pointBounds66151 : List (Nat × Nat × Nat) := [(8674570240,115119420443191,115119809542499)]
theorem point_links_checked66151 : (cuts66151.take 1).map (fun c => (8674476033-1+2*2^10*c.k,115119284354357+c.lower,115119673453590+c.upper)) = pointBounds66151 := by
 decide +kernel
def cuts66152 : List PrefixCut := [⟨64,189333485,189333593⟩]
theorem checked66152 : checkPrefixCuts (2^48) 8674607105 10 Manual.Count131072.C066152.packed 64 cuts66152 = true := by
 decide +kernel
def cuts66153 : List PrefixCut := [⟨51,145883769,145883852⟩,
⟨64,182484226,182484330⟩]
theorem checked66153 : checkPrefixCuts (2^48) 8674738177 10 Manual.Count131072.C066153.packed 64 cuts66153 = true := by
 decide +kernel
def pointBounds66153 : List (Nat × Nat × Nat) := [(8674842624,115119808161653,115120197261183)]
theorem point_links_checked66153 : (cuts66153.take 1).map (fun c => (8674738177-1+2*2^10*c.k,115119662277884+c.lower,115120051377331+c.upper)) = pointBounds66153 := by
 decide +kernel
def cuts66154 : List PrefixCut := [⟨64,184720309,184720414⟩]
theorem checked66154 : checkPrefixCuts (2^48) 8674869249 10 Manual.Count131072.C066154.packed 64 cuts66154 = true := by
 decide +kernel
def cuts66155 : List PrefixCut := [⟨56,162070047,162070139⟩,
⟨64,185398873,185398979⟩]
theorem checked66155 : checkPrefixCuts (2^48) 8675000321 10 Manual.Count131072.C066155.packed 64 cuts66155 = true := by
 decide +kernel
def pointBounds66155 : List (Nat × Nat × Nat) := [(8675115008,115120191552466,115120580652214)]
theorem point_links_checked66155 : (cuts66155.take 1).map (fun c => (8675000321-1+2*2^10*c.k,115120029482419+c.lower,115120418582075+c.upper)) = pointBounds66155 := by
 decide +kernel
def cuts66156 : List PrefixCut := [⟨64,183319553,183319655⟩]
theorem checked66156 : checkPrefixCuts (2^48) 8675131393 10 Manual.Count131072.C066156.packed 64 cuts66156 = true := by
 decide +kernel
def cuts66157 : List PrefixCut := [⟨61,175529931,175530034⟩,
⟨64,184160358,184160467⟩]
theorem checked66157 : checkPrefixCuts (2^48) 8675262465 10 Manual.Count131072.C066157.packed 64 cuts66157 = true := by
 decide +kernel
def pointBounds66157 : List (Nat × Nat × Nat) := [(8675387392,115120573730776,115120962830743)]
theorem point_links_checked66157 : (cuts66157.take 1).map (fun c => (8675262465-1+2*2^10*c.k,115120398200845+c.lower,115120787300709+c.upper)) = pointBounds66157 := by
 decide +kernel
def cuts66158 : List PrefixCut := [⟨64,185682485,185682593⟩]
theorem checked66158 : checkPrefixCuts (2^48) 8675393537 10 Manual.Count131072.C066158.packed 64 cuts66158 = true := by
 decide +kernel
def cuts66159 : List PrefixCut := [⟨64,186945015,186945121⟩]
theorem checked66159 : checkPrefixCuts (2^48) 8675524609 10 Manual.Count131072.C066159.packed 64 cuts66159 = true := by
 decide +kernel
def cuts66160 : List PrefixCut := [⟨2,5677737,5677741⟩,
⟨64,187428843,187428946⟩]
theorem checked66160 : checkPrefixCuts (2^48) 8675655681 10 Manual.Count131072.C066160.packed 64 cuts66160 = true := by
 decide +kernel
def pointBounds66160 : List (Nat × Nat × Nat) := [(8675659776,115120960666440,115121349766631)]
theorem point_links_checked66160 : (cuts66160.take 1).map (fun c => (8675655681-1+2*2^10*c.k,115120954988703+c.lower,115121344088890+c.upper)) = pointBounds66160 := by
 decide +kernel
def cuts66161 : List PrefixCut := [⟨64,187718023,187718134⟩]
theorem checked66161 : checkPrefixCuts (2^48) 8675786753 10 Manual.Count131072.C066161.packed 64 cuts66161 = true := by
 decide +kernel
def cuts66162 : List PrefixCut := [⟨7,21152975,21152989⟩,
⟨64,185671279,185671389⟩]
theorem checked66162 : checkPrefixCuts (2^48) 8675917825 10 Manual.Count131072.C066162.packed 64 cuts66162 = true := by
 decide +kernel
def pointBounds66162 : List (Nat × Nat × Nat) := [(8675932160,115121351288544,115121740388959)]
theorem point_links_checked66162 : (cuts66162.take 1).map (fun c => (8675917825-1+2*2^10*c.k,115121330135569+c.lower,115121719235970+c.upper)) = pointBounds66162 := by
 decide +kernel
def cuts66163 : List PrefixCut := [⟨64,185668467,185668571⟩]
theorem checked66163 : checkPrefixCuts (2^48) 8676048897 10 Manual.Count131072.C066163.packed 64 cuts66163 = true := by
 decide +kernel
def cuts66164 : List PrefixCut := [⟨12,35329575,35329592⟩,
⟨64,187904165,187904265⟩]
theorem checked66164 : checkPrefixCuts (2^48) 8676179969 10 Manual.Count131072.C066164.packed 64 cuts66164 = true := by
 decide +kernel
def pointBounds66164 : List (Nat × Nat × Nat) := [(8676204544,115121736804890,115122125905522)]
theorem point_links_checked66164 : (cuts66164.take 1).map (fun c => (8676179969-1+2*2^10*c.k,115121701475315+c.lower,115122090575930+c.upper)) = pointBounds66164 := by
 decide +kernel
def cuts66165 : List PrefixCut := [⟨64,186506321,186506432⟩]
theorem checked66165 : checkPrefixCuts (2^48) 8676311041 10 Manual.Count131072.C066165.packed 64 cuts66165 = true := by
 decide +kernel
def cuts66166 : List PrefixCut := [⟨17,49505296,49505324⟩,
⟨64,184751709,184751817⟩]
theorem checked66166 : checkPrefixCuts (2^48) 8676442113 10 Manual.Count131072.C066166.packed 64 cuts66166 = true := by
 decide +kernel
def pointBounds66166 : List (Nat × Nat × Nat) := [(8676476928,115122125391097,115122514491951)]
theorem point_links_checked66166 : (cuts66166.take 1).map (fun c => (8676442113-1+2*2^10*c.k,115122075885801+c.lower,115122464986627+c.upper)) = pointBounds66166 := by
 decide +kernel
def cuts66167 : List PrefixCut := [⟨64,186111416,186111520⟩]
theorem checked66167 : checkPrefixCuts (2^48) 8676573185 10 Manual.Count131072.C066167.packed 64 cuts66167 = true := by
 decide +kernel
def cuts66168 : List PrefixCut := [⟨22,63420625,63420658⟩,
⟨64,186984474,186984577⟩]
theorem checked66168 : checkPrefixCuts (2^48) 8676704257 10 Manual.Count131072.C066168.packed 64 cuts66168 = true := by
 decide +kernel
def pointBounds66168 : List (Nat × Nat × Nat) := [(8676749312,115122510169551,115122899270622)]
theorem point_links_checked66168 : (cuts66168.take 1).map (fun c => (8676704257-1+2*2^10*c.k,115122446748926+c.lower,115122835849964+c.upper)) = pointBounds66168 := by
 decide +kernel
def cuts66169 : List PrefixCut := [⟨64,186008472,186008577⟩]
theorem checked66169 : checkPrefixCuts (2^48) 8676835329 10 Manual.Count131072.C066169.packed 64 cuts66169 = true := by
 decide +kernel
def cuts66170 : List PrefixCut := [⟨27,76686310,76686356⟩,
⟨64,184026866,184026978⟩]
theorem checked66170 : checkPrefixCuts (2^48) 8676966401 10 Manual.Count131072.C066170.packed 64 cuts66170 = true := by
 decide +kernel
def pointBounds66170 : List (Nat × Nat × Nat) := [(8677021696,115122896428182,115123285529474)]
theorem point_links_checked66170 : (cuts66170.take 1).map (fun c => (8676966401-1+2*2^10*c.k,115122819741872+c.lower,115123208843118+c.upper)) = pointBounds66170 := by
 decide +kernel
def cuts66171 : List PrefixCut := [⟨64,184153837,184153944⟩]
theorem checked66171 : checkPrefixCuts (2^48) 8677097473 10 Manual.Count131072.C066171.packed 64 cuts66171 = true := by
 decide +kernel
def cuts66172 : List PrefixCut := [⟨32,93973520,93973573⟩,
⟨64,185059345,185059451⟩]
theorem checked66172 : checkPrefixCuts (2^48) 8677228545 10 Manual.Count131072.C066172.packed 64 cuts66172 = true := by
 decide +kernel
def pointBounds66172 : List (Nat × Nat × Nat) := [(8677294080,115123281896095,115123670997613)]
theorem point_links_checked66172 : (cuts66172.take 1).map (fun c => (8677228545-1+2*2^10*c.k,115123187922575+c.lower,115123577024040+c.upper)) = pointBounds66172 := by
 decide +kernel
def cuts66173 : List PrefixCut := [⟨64,186581109,186581220⟩]
theorem checked66173 : checkPrefixCuts (2^48) 8677359617 10 Manual.Count131072.C066173.packed 64 cuts66173 = true := by
 decide +kernel
def cuts66174 : List PrefixCut := [⟨37,105745332,105745391⟩,
⟨64,185832227,185832329⟩]
theorem checked66174 : checkPrefixCuts (2^48) 8677490689 10 Manual.Count131072.C066174.packed 64 cuts66174 = true := by
 decide +kernel
def pointBounds66174 : List (Nat × Nat × Nat) := [(8677566464,115123665308361,115124054410102)]
theorem point_links_checked66174 : (cuts66174.take 1).map (fun c => (8677490689-1+2*2^10*c.k,115123559563029+c.lower,115123948664711+c.upper)) = pointBounds66174 := by
 decide +kernel
def cuts66175 : List PrefixCut := [⟨64,188878484,188878590⟩]
theorem checked66175 : checkPrefixCuts (2^48) 8677621761 10 Manual.Count131072.C066175.packed 64 cuts66175 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000192
