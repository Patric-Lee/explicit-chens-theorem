import PlattAssemblyKernel
import PlattCertificates.Count131072.C074128
import PlattCertificates.Count131072.C074129
import PlattCertificates.Count131072.C074130
import PlattCertificates.Count131072.C074131
import PlattCertificates.Count131072.C074132
import PlattCertificates.Count131072.C074133
import PlattCertificates.Count131072.C074134
import PlattCertificates.Count131072.C074135
import PlattCertificates.Count131072.C074136
import PlattCertificates.Count131072.C074137
import PlattCertificates.Count131072.C074138
import PlattCertificates.Count131072.C074139
import PlattCertificates.Count131072.C074140
import PlattCertificates.Count131072.C074141
import PlattCertificates.Count131072.C074142
import PlattCertificates.Count131072.C074143
import PlattCertificates.Count131072.C074144
import PlattCertificates.Count131072.C074145
import PlattCertificates.Count131072.C074146
import PlattCertificates.Count131072.C074147
import PlattCertificates.Count131072.C074148
import PlattCertificates.Count131072.C074149
import PlattCertificates.Count131072.C074150
import PlattCertificates.Count131072.C074151
import PlattCertificates.Count131072.C074152
import PlattCertificates.Count131072.C074153
import PlattCertificates.Count131072.C074154
import PlattCertificates.Count131072.C074155
import PlattCertificates.Count131072.C074156
import PlattCertificates.Count131072.C074157
import PlattCertificates.Count131072.C074158
import PlattCertificates.Count131072.C074159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000129
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74128 : List PrefixCut := [⟨64,164336731,164336832⟩]
theorem checked74128 : checkPrefixCuts (2^48) 9720037377 10 Manual.Count131072.C074128.packed 64 cuts74128 = true := by
 decide +kernel
def cuts74129 : List PrefixCut := [⟨2,5299280,5299283⟩,
⟨64,163494757,163494850⟩]
theorem checked74129 : checkPrefixCuts (2^48) 9720168449 10 Manual.Count131072.C074129.packed 64 cuts74129 = true := by
 decide +kernel
def pointBounds74129 : List (Nat × Nat × Nat) := [(9720172544,116515857575586,116516247497375)]
theorem point_links_checked74129 : (cuts74129.take 1).map (fun c => (9720168449-1+2*2^10*c.k,116515852276306+c.lower,116516242198092+c.upper)) = pointBounds74129 := by
 decide +kernel
def cuts74130 : List PrefixCut := [⟨64,164911460,164911559⟩]
theorem checked74130 : checkPrefixCuts (2^48) 9720299521 10 Manual.Count131072.C074130.packed 64 cuts74130 = true := by
 decide +kernel
def cuts74131 : List PrefixCut := [⟨23,58550991,58551023⟩,
⟨64,165314617,165314716⟩]
theorem checked74131 : checkPrefixCuts (2^48) 9720430593 10 Manual.Count131072.C074131.packed 64 cuts74131 = true := by
 decide +kernel
def pointBounds74131 : List (Nat × Nat × Nat) := [(9720477696,116516239233514,116516629155524)]
theorem point_links_checked74131 : (cuts74131.take 1).map (fun c => (9720430593-1+2*2^10*c.k,116516180682523+c.lower,116516570604501+c.upper)) = pointBounds74131 := by
 decide +kernel
def cuts74132 : List PrefixCut := [⟨64,164298913,164299009⟩]
theorem checked74132 : checkPrefixCuts (2^48) 9720561665 10 Manual.Count131072.C074132.packed 64 cuts74132 = true := by
 decide +kernel
def cuts74133 : List PrefixCut := [⟨44,113971305,113971374⟩,
⟨64,165020610,165020707⟩]
theorem checked74133 : checkPrefixCuts (2^48) 9720692737 10 Manual.Count131072.C074133.packed 64 cuts74133 = true := by
 decide +kernel
def pointBounds74133 : List (Nat × Nat × Nat) := [(9720782848,116516624267358,116517014189600)]
theorem point_links_checked74133 : (cuts74133.take 1).map (fun c => (9720692737-1+2*2^10*c.k,116516510296053+c.lower,116516900218226+c.upper)) = pointBounds74133 := by
 decide +kernel
def cuts74134 : List PrefixCut := [⟨64,163020433,163020533⟩]
theorem checked74134 : checkPrefixCuts (2^48) 9720823809 10 Manual.Count131072.C074134.packed 64 cuts74134 = true := by
 decide +kernel
def cuts74135 : List PrefixCut := [⟨64,164350177,164350276⟩]
theorem checked74135 : checkPrefixCuts (2^48) 9720954881 10 Manual.Count131072.C074135.packed 64 cuts74135 = true := by
 decide +kernel
def cuts74136 : List PrefixCut := [⟨1,2577002,2577004⟩,
⟨64,166722266,166722361⟩]
theorem checked74136 : checkPrefixCuts (2^48) 9721085953 10 Manual.Count131072.C074136.packed 64 cuts74136 = true := by
 decide +kernel
def pointBounds74136 : List (Nat × Nat × Nat) := [(9721088000,116517005264275,116517395186746)]
theorem point_links_checked74136 : (cuts74136.take 1).map (fun c => (9721085953-1+2*2^10*c.k,116517002687273+c.lower,116517392609742+c.upper)) = pointBounds74136 := by
 decide +kernel
def cuts74137 : List PrefixCut := [⟨64,167675524,167675622⟩]
theorem checked74137 : checkPrefixCuts (2^48) 9721217025 10 Manual.Count131072.C074137.packed 64 cuts74137 = true := by
 decide +kernel
def cuts74138 : List PrefixCut := [⟨22,57763709,57763741⟩,
⟨64,166399278,166399377⟩]
theorem checked74138 : checkPrefixCuts (2^48) 9721348097 10 Manual.Count131072.C074138.packed 64 cuts74138 = true := by
 decide +kernel
def pointBounds74138 : List (Nat × Nat × Nat) := [(9721393152,116517394848772,116517784771466)]
theorem point_links_checked74138 : (cuts74138.take 1).map (fun c => (9721348097-1+2*2^10*c.k,116517337085063+c.lower,116517727007725+c.upper)) = pointBounds74138 := by
 decide +kernel
def cuts74139 : List PrefixCut := [⟨64,164659806,164659901⟩]
theorem checked74139 : checkPrefixCuts (2^48) 9721479169 10 Manual.Count131072.C074139.packed 64 cuts74139 = true := by
 decide +kernel
def cuts74140 : List PrefixCut := [⟨43,111383705,111383770⟩,
⟨64,165728859,165728959⟩]
theorem checked74140 : checkPrefixCuts (2^48) 9721610241 10 Manual.Count131072.C074140.packed 64 cuts74140 = true := by
 decide +kernel
def pointBounds74140 : List (Nat × Nat × Nat) := [(9721698304,116517779527852,116518169450773)]
theorem point_links_checked74140 : (cuts74140.take 1).map (fun c => (9721610241-1+2*2^10*c.k,116517668144147+c.lower,116518058067003+c.upper)) = pointBounds74140 := by
 decide +kernel
def cuts74141 : List PrefixCut := [⟨64,166103030,166103123⟩]
theorem checked74141 : checkPrefixCuts (2^48) 9721741313 10 Manual.Count131072.C074141.packed 64 cuts74141 = true := by
 decide +kernel
def cuts74142 : List PrefixCut := [⟨64,166013921,166014019⟩]
theorem checked74142 : checkPrefixCuts (2^48) 9721872385 10 Manual.Count131072.C074142.packed 64 cuts74142 = true := by
 decide +kernel
def pointBounds74142 : List (Nat × Nat × Nat) := [(9722003456,116518165989957,116518555913104)]
theorem point_links_checked74142 : (cuts74142.take 1).map (fun c => (9721872385-1+2*2^10*c.k,116517999976036+c.lower,116518389899085+c.upper)) = pointBounds74142 := by
 decide +kernel
def cuts74143 : List PrefixCut := [⟨64,164998356,164998457⟩]
theorem checked74143 : checkPrefixCuts (2^48) 9722003457 10 Manual.Count131072.C074143.packed 64 cuts74143 = true := by
 decide +kernel
def cuts74144 : List PrefixCut := [⟨64,163259030,163259131⟩]
theorem checked74144 : checkPrefixCuts (2^48) 9722134529 10 Manual.Count131072.C074144.packed 64 cuts74144 = true := by
 decide +kernel
def cuts74145 : List PrefixCut := [⟨21,54341983,54342018⟩,
⟨64,163604246,163604353⟩]
theorem checked74145 : checkPrefixCuts (2^48) 9722265601 10 Manual.Count131072.C074145.packed 64 cuts74145 = true := by
 decide +kernel
def pointBounds74145 : List (Nat × Nat × Nat) := [(9722308608,116518548589326,116518938512710)]
theorem point_links_checked74145 : (cuts74145.take 1).map (fun c => (9722265601-1+2*2^10*c.k,116518494247343+c.lower,116518884170692+c.upper)) = pointBounds74145 := by
 decide +kernel
def cuts74146 : List PrefixCut := [⟨64,165281196,165281296⟩]
theorem checked74146 : checkPrefixCuts (2^48) 9722396673 10 Manual.Count131072.C074146.packed 64 cuts74146 = true := by
 decide +kernel
def cuts74147 : List PrefixCut := [⟨42,106480547,106480609⟩,
⟨64,163020813,163020915⟩]
theorem checked74147 : checkPrefixCuts (2^48) 9722527745 10 Manual.Count131072.C074147.packed 64 cuts74147 = true := by
 decide +kernel
def pointBounds74147 : List (Nat × Nat × Nat) := [(9722613760,116518929613332,116519319536950)]
theorem point_links_checked74147 : (cuts74147.take 1).map (fun c => (9722527745-1+2*2^10*c.k,116518823132785+c.lower,116519213056341+c.upper)) = pointBounds74147 := by
 decide +kernel
def cuts74148 : List PrefixCut := [⟨64,164379274,164379373⟩]
theorem checked74148 : checkPrefixCuts (2^48) 9722658817 10 Manual.Count131072.C074148.packed 64 cuts74148 = true := by
 decide +kernel
def cuts74149 : List PrefixCut := [⟨63,160237250,160237344⟩,
⟨64,163103263,163103359⟩]
theorem checked74149 : checkPrefixCuts (2^48) 9722789889 10 Manual.Count131072.C074149.packed 64 cuts74149 = true := by
 decide +kernel
def pointBounds74149 : List (Nat × Nat × Nat) := [(9722918912,116519310770122,116519700693973)]
theorem point_links_checked74149 : (cuts74149.take 1).map (fun c => (9722789889-1+2*2^10*c.k,116519150532872+c.lower,116519540456629+c.upper)) = pointBounds74149 := by
 decide +kernel
def cuts74150 : List PrefixCut := [⟨64,164982795,164982890⟩]
theorem checked74150 : checkPrefixCuts (2^48) 9722920961 10 Manual.Count131072.C074150.packed 64 cuts74150 = true := by
 decide +kernel
def cuts74151 : List PrefixCut := [⟨64,164662126,164662229⟩]
theorem checked74151 : checkPrefixCuts (2^48) 9723052033 10 Manual.Count131072.C074151.packed 64 cuts74151 = true := by
 decide +kernel
def cuts74152 : List PrefixCut := [⟨20,51181446,51181476⟩,
⟨64,165238877,165238972⟩]
theorem checked74152 : checkPrefixCuts (2^48) 9723183105 10 Manual.Count131072.C074152.packed 64 cuts74152 = true := by
 decide +kernel
def pointBounds74152 : List (Nat × Nat × Nat) := [(9723224064,116519694462502,116520084386583)]
theorem point_links_checked74152 : (cuts74152.take 1).map (fun c => (9723183105-1+2*2^10*c.k,116519643281056+c.lower,116520033205107+c.upper)) = pointBounds74152 := by
 decide +kernel
def cuts74153 : List PrefixCut := [⟨64,164426086,164426185⟩]
theorem checked74153 : checkPrefixCuts (2^48) 9723314177 10 Manual.Count131072.C074153.packed 64 cuts74153 = true := by
 decide +kernel
def cuts74154 : List PrefixCut := [⟨41,104531001,104531068⟩,
⟨64,162629118,162629221⟩]
theorem checked74154 : checkPrefixCuts (2^48) 9723445249 10 Manual.Count131072.C074154.packed 64 cuts74154 = true := by
 decide +kernel
def pointBounds74154 : List (Nat × Nat × Nat) := [(9723529216,116520077477020,116520467401332)]
theorem point_links_checked74154 : (cuts74154.take 1).map (fun c => (9723445249-1+2*2^10*c.k,116519972946019+c.lower,116520362870264+c.upper)) = pointBounds74154 := by
 decide +kernel
def cuts74155 : List PrefixCut := [⟨64,165463781,165463883⟩]
theorem checked74155 : checkPrefixCuts (2^48) 9723576321 10 Manual.Count131072.C074155.packed 64 cuts74155 = true := by
 decide +kernel
def cuts74156 : List PrefixCut := [⟨62,162364230,162364315⟩,
⟨64,166561530,166561618⟩]
theorem checked74156 : checkPrefixCuts (2^48) 9723707393 10 Manual.Count131072.C074156.packed 64 cuts74156 = true := by
 decide +kernel
def pointBounds74156 : List (Nat × Nat × Nat) := [(9723834368,116520463403148,116520853327683)]
theorem point_links_checked74156 : (cuts74156.take 1).map (fun c => (9723707393-1+2*2^10*c.k,116520301038918+c.lower,116520690963368+c.upper)) = pointBounds74156 := by
 decide +kernel
def cuts74157 : List PrefixCut := [⟨64,163780409,163780500⟩]
theorem checked74157 : checkPrefixCuts (2^48) 9723838465 10 Manual.Count131072.C074157.packed 64 cuts74157 = true := by
 decide +kernel
def cuts74158 : List PrefixCut := [⟨64,165283405,165283507⟩]
theorem checked74158 : checkPrefixCuts (2^48) 9723969537 10 Manual.Count131072.C074158.packed 64 cuts74158 = true := by
 decide +kernel
def cuts74159 : List PrefixCut := [⟨19,49584589,49584621⟩,
⟨64,164789096,164789198⟩]
theorem checked74159 : checkPrefixCuts (2^48) 9724100609 10 Manual.Count131072.C074159.packed 64 cuts74159 = true := by
 decide +kernel
def pointBounds74159 : List (Nat × Nat × Nat) := [(9724139520,116520846248851,116521236173614)]
theorem point_links_checked74159 : (cuts74159.take 1).map (fun c => (9724100609-1+2*2^10*c.k,116520796664262+c.lower,116521186588993+c.upper)) = pointBounds74159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000129
