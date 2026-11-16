import PlattAssemblyKernel
import PlattCertificates.Count131072.C075184
import PlattCertificates.Count131072.C075185
import PlattCertificates.Count131072.C075186
import PlattCertificates.Count131072.C075187
import PlattCertificates.Count131072.C075188
import PlattCertificates.Count131072.C075189
import PlattCertificates.Count131072.C075190
import PlattCertificates.Count131072.C075191
import PlattCertificates.Count131072.C075192
import PlattCertificates.Count131072.C075193
import PlattCertificates.Count131072.C075194
import PlattCertificates.Count131072.C075195
import PlattCertificates.Count131072.C075196
import PlattCertificates.Count131072.C075197
import PlattCertificates.Count131072.C075198
import PlattCertificates.Count131072.C075199
import PlattCertificates.Count131072.C075200
import PlattCertificates.Count131072.C075201
import PlattCertificates.Count131072.C075202
import PlattCertificates.Count131072.C075203
import PlattCertificates.Count131072.C075204
import PlattCertificates.Count131072.C075205
import PlattCertificates.Count131072.C075206
import PlattCertificates.Count131072.C075207
import PlattCertificates.Count131072.C075208
import PlattCertificates.Count131072.C075209
import PlattCertificates.Count131072.C075210
import PlattCertificates.Count131072.C075211
import PlattCertificates.Count131072.C075212
import PlattCertificates.Count131072.C075213
import PlattCertificates.Count131072.C075214
import PlattCertificates.Count131072.C075215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75184 : List PrefixCut := [⟨64,162429197,162429300⟩]
theorem checked75184 : checkPrefixCuts (2^48) 9858449409 10 Manual.Count131072.C075184.packed 64 cuts75184 = true := by
 decide +kernel
def cuts75185 : List PrefixCut := [⟨12,30207194,30207214⟩,
⟨64,161427749,161427848⟩]
theorem checked75185 : checkPrefixCuts (2^48) 9858580481 10 Manual.Count131072.C075185.packed 64 cuts75185 = true := by
 decide +kernel
def pointBounds75185 : List (Nat × Nat × Nat) := [(9858605056,116688873493373,116689263518778)]
theorem point_links_checked75185 : (cuts75185.take 1).map (fun c => (9858580481-1+2*2^10*c.k,116688843286179+c.lower,116689233311564+c.upper)) = pointBounds75185 := by
 decide +kernel
def cuts75186 : List PrefixCut := [⟨64,164280681,164280774⟩]
theorem checked75186 : checkPrefixCuts (2^48) 9858711553 10 Manual.Count131072.C075186.packed 64 cuts75186 = true := by
 decide +kernel
def cuts75187 : List PrefixCut := [⟨35,88477679,88477735⟩,
⟨64,161166509,161166609⟩]
theorem checked75187 : checkPrefixCuts (2^48) 9858842625 10 Manual.Count131072.C075187.packed 64 cuts75187 = true := by
 decide +kernel
def pointBounds75187 : List (Nat × Nat × Nat) := [(9858914304,116689257472288,116689647497921)]
theorem point_links_checked75187 : (cuts75187.take 1).map (fun c => (9858842625-1+2*2^10*c.k,116689168994609+c.lower,116689559020186+c.upper)) = pointBounds75187 := by
 decide +kernel
def cuts75188 : List PrefixCut := [⟨64,161792461,161792558⟩]
theorem checked75188 : checkPrefixCuts (2^48) 9858973697 10 Manual.Count131072.C075188.packed 64 cuts75188 = true := by
 decide +kernel
def cuts75189 : List PrefixCut := [⟨58,146544935,146545030⟩,
⟨64,161133669,161133771⟩]
theorem checked75189 : checkPrefixCuts (2^48) 9859104769 10 Manual.Count131072.C075189.packed 64 cuts75189 = true := by
 decide +kernel
def pointBounds75189 : List (Nat × Nat × Nat) := [(9859223552,116689638498514,116690028524383)]
theorem point_links_checked75189 : (cuts75189.take 1).map (fun c => (9859104769-1+2*2^10*c.k,116689491953579+c.lower,116689881979353+c.upper)) = pointBounds75189 := by
 decide +kernel
def cuts75190 : List PrefixCut := [⟨64,163529652,163529751⟩]
theorem checked75190 : checkPrefixCuts (2^48) 9859235841 10 Manual.Count131072.C075190.packed 64 cuts75190 = true := by
 decide +kernel
def cuts75191 : List PrefixCut := [⟨64,164783631,164783730⟩]
theorem checked75191 : checkPrefixCuts (2^48) 9859366913 10 Manual.Count131072.C075191.packed 64 cuts75191 = true := by
 decide +kernel
def cuts75192 : List PrefixCut := [⟨17,44050415,44050443⟩,
⟨64,165694981,165695077⟩]
theorem checked75192 : checkPrefixCuts (2^48) 9859497985 10 Manual.Count131072.C075192.packed 64 cuts75192 = true := by
 decide +kernel
def pointBounds75192 : List (Nat × Nat × Nat) := [(9859532800,116690025450946,116690415477048)]
theorem point_links_checked75192 : (cuts75192.take 1).map (fun c => (9859497985-1+2*2^10*c.k,116689981400531+c.lower,116690371426605+c.upper)) = pointBounds75192 := by
 decide +kernel
def cuts75193 : List PrefixCut := [⟨64,161324938,161325025⟩]
theorem checked75193 : checkPrefixCuts (2^48) 9859629057 10 Manual.Count131072.C075193.packed 64 cuts75193 = true := by
 decide +kernel
def cuts75194 : List PrefixCut := [⟨40,101344429,101344489⟩,
⟨64,161037326,161037423⟩]
theorem checked75194 : checkPrefixCuts (2^48) 9859760129 10 Manual.Count131072.C075194.packed 64 cuts75194 = true := by
 decide +kernel
def pointBounds75194 : List (Nat × Nat × Nat) := [(9859842048,116690409764879,116690799791196)]
theorem point_links_checked75194 : (cuts75194.take 1).map (fun c => (9859760129-1+2*2^10*c.k,116690308420450+c.lower,116690698446707+c.upper)) = pointBounds75194 := by
 decide +kernel
def cuts75195 : List PrefixCut := [⟨64,163261859,163261955⟩]
theorem checked75195 : checkPrefixCuts (2^48) 9859891201 10 Manual.Count131072.C075195.packed 64 cuts75195 = true := by
 decide +kernel
def cuts75196 : List PrefixCut := [⟨63,158178372,158178472⟩,
⟨64,160690482,160690584⟩]
theorem checked75196 : checkPrefixCuts (2^48) 9860022273 10 Manual.Count131072.C075196.packed 64 cuts75196 = true := by
 decide +kernel
def pointBounds75196 : List (Nat × Nat × Nat) := [(9860151296,116690790898007,116691180924557)]
theorem point_links_checked75196 : (cuts75196.take 1).map (fun c => (9860022273-1+2*2^10*c.k,116690632719635+c.lower,116691022746085+c.upper)) = pointBounds75196 := by
 decide +kernel
def cuts75197 : List PrefixCut := [⟨64,163914092,163914181⟩]
theorem checked75197 : checkPrefixCuts (2^48) 9860153345 10 Manual.Count131072.C075197.packed 64 cuts75197 = true := by
 decide +kernel
def cuts75198 : List PrefixCut := [⟨64,164768293,164768395⟩]
theorem checked75198 : checkPrefixCuts (2^48) 9860284417 10 Manual.Count131072.C075198.packed 64 cuts75198 = true := by
 decide +kernel
def cuts75199 : List PrefixCut := [⟨22,56520846,56520880⟩,
⟨64,162368272,162368368⟩]
theorem checked75199 : checkPrefixCuts (2^48) 9860415489 10 Manual.Count131072.C075199.packed 64 cuts75199 = true := by
 decide +kernel
def pointBounds75199 : List (Nat × Nat × Nat) := [(9860460544,116691178613348,116691568640125)]
theorem point_links_checked75199 : (cuts75199.take 1).map (fun c => (9860415489-1+2*2^10*c.k,116691122092502+c.lower,116691512119245+c.upper)) = pointBounds75199 := by
 decide +kernel
def cuts75200 : List PrefixCut := [⟨64,159768476,159768583⟩]
theorem checked75200 : checkPrefixCuts (2^48) 9860546561 10 Manual.Count131072.C075200.packed 64 cuts75200 = true := by
 decide +kernel
def cuts75201 : List PrefixCut := [⟨45,114836758,114836826⟩,
⟨64,163134667,163134765⟩]
theorem checked75201 : checkPrefixCuts (2^48) 9860677633 10 Manual.Count131072.C075201.packed 64 cuts75201 = true := by
 decide +kernel
def pointBounds75201 : List (Nat × Nat × Nat) := [(9860769792,116691559066008,116691949093022)]
theorem point_links_checked75201 : (cuts75201.take 1).map (fun c => (9860677633-1+2*2^10*c.k,116691444229250+c.lower,116691834256196+c.upper)) = pointBounds75201 := by
 decide +kernel
def cuts75202 : List PrefixCut := [⟨64,160877460,160877554⟩]
theorem checked75202 : checkPrefixCuts (2^48) 9860808705 10 Manual.Count131072.C075202.packed 64 cuts75202 = true := by
 decide +kernel
def cuts75203 : List PrefixCut := [⟨64,163130329,163130425⟩]
theorem checked75203 : checkPrefixCuts (2^48) 9860939777 10 Manual.Count131072.C075203.packed 64 cuts75203 = true := by
 decide +kernel
def cuts75204 : List PrefixCut := [⟨4,10018957,10018964⟩,
⟨64,163071063,163071164⟩]
theorem checked75204 : checkPrefixCuts (2^48) 9861070849 10 Manual.Count131072.C075204.packed 64 cuts75204 = true := by
 decide +kernel
def pointBounds75204 : List (Nat × Nat × Nat) := [(9861079040,116691941390663,116692331417904)]
theorem point_links_checked75204 : (cuts75204.take 1).map (fun c => (9861070849-1+2*2^10*c.k,116691931371706+c.lower,116692321398940+c.upper)) = pointBounds75204 := by
 decide +kernel
def cuts75205 : List PrefixCut := [⟨64,162155514,162155609⟩]
theorem checked75205 : checkPrefixCuts (2^48) 9861201921 10 Manual.Count131072.C075205.packed 64 cuts75205 = true := by
 decide +kernel
def cuts75206 : List PrefixCut := [⟨27,69531262,69531305⟩,
⟨64,163437805,163437905⟩]
theorem checked75206 : checkPrefixCuts (2^48) 9861332993 10 Manual.Count131072.C075206.packed 64 cuts75206 = true := by
 decide +kernel
def pointBounds75206 : List (Nat × Nat × Nat) := [(9861388288,116692326129545,116692716157018)]
theorem point_links_checked75206 : (cuts75206.take 1).map (fun c => (9861332993-1+2*2^10*c.k,116692256598283+c.lower,116692646625713+c.upper)) = pointBounds75206 := by
 decide +kernel
def cuts75207 : List PrefixCut := [⟨64,164377523,164377624⟩]
theorem checked75207 : checkPrefixCuts (2^48) 9861464065 10 Manual.Count131072.C075207.packed 64 cuts75207 = true := by
 decide +kernel
def cuts75208 : List PrefixCut := [⟨50,127470284,127470359⟩,
⟨64,163176571,163176665⟩]
theorem checked75208 : checkPrefixCuts (2^48) 9861595137 10 Manual.Count131072.C075208.packed 64 cuts75208 = true := by
 decide +kernel
def pointBounds75208 : List (Nat × Nat × Nat) := [(9861697536,116692711883895,116693101911601)]
theorem point_links_checked75208 : (cuts75208.take 1).map (fun c => (9861595137-1+2*2^10*c.k,116692584413611+c.lower,116692974441242+c.upper)) = pointBounds75208 := by
 decide +kernel
def cuts75209 : List PrefixCut := [⟨64,162946067,162946170⟩]
theorem checked75209 : checkPrefixCuts (2^48) 9861726209 10 Manual.Count131072.C075209.packed 64 cuts75209 = true := by
 decide +kernel
def cuts75210 : List PrefixCut := [⟨64,160318076,160318177⟩]
theorem checked75210 : checkPrefixCuts (2^48) 9861857281 10 Manual.Count131072.C075210.packed 64 cuts75210 = true := by
 decide +kernel
def cuts75211 : List PrefixCut := [⟨9,23232673,23232687⟩,
⟨64,165110870,165110966⟩]
theorem checked75211 : checkPrefixCuts (2^48) 9861988353 10 Manual.Count131072.C075211.packed 64 cuts75211 = true := by
 decide +kernel
def pointBounds75211 : List (Nat × Nat × Nat) := [(9862006784,116693094086998,116693484114941)]
theorem point_links_checked75211 : (cuts75211.take 1).map (fun c => (9861988353-1+2*2^10*c.k,116693070854325+c.lower,116693460882254+c.upper)) = pointBounds75211 := by
 decide +kernel
def cuts75212 : List PrefixCut := [⟨64,163253514,163253614⟩]
theorem checked75212 : checkPrefixCuts (2^48) 9862119425 10 Manual.Count131072.C075212.packed 64 cuts75212 = true := by
 decide +kernel
def cuts75213 : List PrefixCut := [⟨32,80912426,80912472⟩,
⟨64,161767233,161767330⟩]
theorem checked75213 : checkPrefixCuts (2^48) 9862250497 10 Manual.Count131072.C075213.packed 64 cuts75213 = true := by
 decide +kernel
def pointBounds75213 : List (Nat × Nat × Nat) := [(9862316032,116693480131135,116693870159306)]
theorem point_links_checked75213 : (cuts75213.take 1).map (fun c => (9862250497-1+2*2^10*c.k,116693399218709+c.lower,116693789246834+c.upper)) = pointBounds75213 := by
 decide +kernel
def cuts75214 : List PrefixCut := [⟨64,159681665,159681764⟩]
theorem checked75214 : checkPrefixCuts (2^48) 9862381569 10 Manual.Count131072.C075214.packed 64 cuts75214 = true := by
 decide +kernel
def cuts75215 : List PrefixCut := [⟨55,139530662,139530745⟩,
⟨64,163075769,163075866⟩]
theorem checked75215 : checkPrefixCuts (2^48) 9862512641 10 Manual.Count131072.C075215.packed 64 cuts75215 = true := by
 decide +kernel
def pointBounds75215 : List (Nat × Nat × Nat) := [(9862625280,116693860198269,116694250226673)]
theorem point_links_checked75215 : (cuts75215.take 1).map (fun c => (9862512641-1+2*2^10*c.k,116693720667607+c.lower,116694110695928+c.upper)) = pointBounds75215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000162
