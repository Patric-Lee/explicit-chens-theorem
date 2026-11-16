import PlattAssemblyKernel
import PlattCertificates.Count131072.C075216
import PlattCertificates.Count131072.C075217
import PlattCertificates.Count131072.C075218
import PlattCertificates.Count131072.C075219
import PlattCertificates.Count131072.C075220
import PlattCertificates.Count131072.C075221
import PlattCertificates.Count131072.C075222
import PlattCertificates.Count131072.C075223
import PlattCertificates.Count131072.C075224
import PlattCertificates.Count131072.C075225
import PlattCertificates.Count131072.C075226
import PlattCertificates.Count131072.C075227
import PlattCertificates.Count131072.C075228
import PlattCertificates.Count131072.C075229
import PlattCertificates.Count131072.C075230
import PlattCertificates.Count131072.C075231
import PlattCertificates.Count131072.C075232
import PlattCertificates.Count131072.C075233
import PlattCertificates.Count131072.C075234
import PlattCertificates.Count131072.C075235
import PlattCertificates.Count131072.C075236
import PlattCertificates.Count131072.C075237
import PlattCertificates.Count131072.C075238
import PlattCertificates.Count131072.C075239
import PlattCertificates.Count131072.C075240
import PlattCertificates.Count131072.C075241
import PlattCertificates.Count131072.C075242
import PlattCertificates.Count131072.C075243
import PlattCertificates.Count131072.C075244
import PlattCertificates.Count131072.C075245
import PlattCertificates.Count131072.C075246
import PlattCertificates.Count131072.C075247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000163
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75216 : List PrefixCut := [⟨64,161247086,161247177⟩]
theorem checked75216 : checkPrefixCuts (2^48) 9862643713 10 Manual.Count131072.C075216.packed 64 cuts75216 = true := by
 decide +kernel
def cuts75217 : List PrefixCut := [⟨64,163784911,163785004⟩]
theorem checked75217 : checkPrefixCuts (2^48) 9862774785 10 Manual.Count131072.C075217.packed 64 cuts75217 = true := by
 decide +kernel
def cuts75218 : List PrefixCut := [⟨14,36443917,36443937⟩,
⟨64,164210820,164210917⟩]
theorem checked75218 : checkPrefixCuts (2^48) 9862905857 10 Manual.Count131072.C075218.packed 64 cuts75218 = true := by
 decide +kernel
def pointBounds75218 : List (Nat × Nat × Nat) := [(9862934528,116694245219290,116694635247912)]
theorem point_links_checked75218 : (cuts75218.take 1).map (fun c => (9862905857-1+2*2^10*c.k,116694208775373+c.lower,116694598803975+c.upper)) = pointBounds75218 := by
 decide +kernel
def cuts75219 : List PrefixCut := [⟨64,160384513,160384609⟩]
theorem checked75219 : checkPrefixCuts (2^48) 9863036929 10 Manual.Count131072.C075219.packed 64 cuts75219 = true := by
 decide +kernel
def cuts75220 : List PrefixCut := [⟨37,93689827,93689884⟩,
⟨64,160781915,160782008⟩]
theorem checked75220 : checkPrefixCuts (2^48) 9863168001 10 Manual.Count131072.C075220.packed 64 cuts75220 = true := by
 decide +kernel
def pointBounds75220 : List (Nat × Nat × Nat) := [(9863243776,116694627060533,116695017089385)]
theorem point_links_checked75220 : (cuts75220.take 1).map (fun c => (9863168001-1+2*2^10*c.k,116694533370706+c.lower,116694923399501+c.upper)) = pointBounds75220 := by
 decide +kernel
def cuts75221 : List PrefixCut := [⟨64,163947431,163947531⟩]
theorem checked75221 : checkPrefixCuts (2^48) 9863299073 10 Manual.Count131072.C075221.packed 64 cuts75221 = true := by
 decide +kernel
def cuts75222 : List PrefixCut := [⟨60,153472226,153472321⟩,
⟨64,163146219,163146320⟩]
theorem checked75222 : checkPrefixCuts (2^48) 9863430145 10 Manual.Count131072.C075222.packed 64 cuts75222 = true := by
 decide +kernel
def pointBounds75222 : List (Nat × Nat × Nat) := [(9863553024,116695011572278,116695401601361)]
theorem point_links_checked75222 : (cuts75222.take 1).map (fun c => (9863430145-1+2*2^10*c.k,116694858100052+c.lower,116695248129040+c.upper)) = pointBounds75222 := by
 decide +kernel
def cuts75223 : List PrefixCut := [⟨64,161117927,161118028⟩]
theorem checked75223 : checkPrefixCuts (2^48) 9863561217 10 Manual.Count131072.C075223.packed 64 cuts75223 = true := by
 decide +kernel
def cuts75224 : List PrefixCut := [⟨64,161144332,161144430⟩]
theorem checked75224 : checkPrefixCuts (2^48) 9863692289 10 Manual.Count131072.C075224.packed 64 cuts75224 = true := by
 decide +kernel
def cuts75225 : List PrefixCut := [⟨19,48882216,48882244⟩,
⟨64,163653355,163653454⟩]
theorem checked75225 : checkPrefixCuts (2^48) 9863823361 10 Manual.Count131072.C075225.packed 64 cuts75225 = true := by
 decide +kernel
def pointBounds75225 : List (Nat × Nat × Nat) := [(9863862272,116695392390746,116695782420062)]
theorem point_links_checked75225 : (cuts75225.take 1).map (fun c => (9863823361-1+2*2^10*c.k,116695343508530+c.lower,116695733537818+c.upper)) = pointBounds75225 := by
 decide +kernel
def cuts75226 : List PrefixCut := [⟨64,163879465,163879562⟩]
theorem checked75226 : checkPrefixCuts (2^48) 9863954433 10 Manual.Count131072.C075226.packed 64 cuts75226 = true := by
 decide +kernel
def cuts75227 : List PrefixCut := [⟨42,106778727,106778786⟩,
⟨64,162165185,162165275⟩]
theorem checked75227 : checkPrefixCuts (2^48) 9864085505 10 Manual.Count131072.C075227.packed 64 cuts75227 = true := by
 decide +kernel
def pointBounds75227 : List (Nat × Nat × Nat) := [(9864171520,116695777820077,116696167849620)]
theorem point_links_checked75227 : (cuts75227.take 1).map (fun c => (9864085505-1+2*2^10*c.k,116695671041350+c.lower,116696061070834+c.upper)) = pointBounds75227 := by
 decide +kernel
def cuts75228 : List PrefixCut := [⟨64,164816759,164816853⟩]
theorem checked75228 : checkPrefixCuts (2^48) 9864216577 10 Manual.Count131072.C075228.packed 64 cuts75228 = true := by
 decide +kernel
def cuts75229 : List PrefixCut := [⟨64,162132329,162132432⟩]
theorem checked75229 : checkPrefixCuts (2^48) 9864347649 10 Manual.Count131072.C075229.packed 64 cuts75229 = true := by
 decide +kernel
def cuts75230 : List PrefixCut := [⟨1,2568077,2568078⟩,
⟨64,162558200,162558293⟩]
theorem checked75230 : checkPrefixCuts (2^48) 9864478721 10 Manual.Count131072.C075230.packed 64 cuts75230 = true := by
 decide +kernel
def pointBounds75230 : List (Nat × Nat × Nat) := [(9864480768,116696162723700,116696552753472)]
theorem point_links_checked75230 : (cuts75230.take 1).map (fun c => (9864478721-1+2*2^10*c.k,116696160155623+c.lower,116696550185394+c.upper)) = pointBounds75230 := by
 decide +kernel
def cuts75231 : List PrefixCut := [⟨64,162812840,162812933⟩]
theorem checked75231 : checkPrefixCuts (2^48) 9864609793 10 Manual.Count131072.C075231.packed 64 cuts75231 = true := by
 decide +kernel
def cuts75232 : List PrefixCut := [⟨24,62687789,62687828⟩,
⟨64,163324272,163324376⟩]
theorem checked75232 : checkPrefixCuts (2^48) 9864740865 10 Manual.Count131072.C075232.packed 64 cuts75232 = true := by
 decide +kernel
def pointBounds75232 : List (Nat × Nat × Nat) := [(9864790016,116696548214452,116696938244448)]
theorem point_links_checked75232 : (cuts75232.take 1).map (fun c => (9864740865-1+2*2^10*c.k,116696485526663+c.lower,116696875556620+c.upper)) = pointBounds75232 := by
 decide +kernel
def cuts75233 : List PrefixCut := [⟨64,160725608,160725704⟩]
theorem checked75233 : checkPrefixCuts (2^48) 9864871937 10 Manual.Count131072.C075233.packed 64 cuts75233 = true := by
 decide +kernel
def cuts75234 : List PrefixCut := [⟨47,118552674,118552746⟩,
⟨64,161351187,161351289⟩]
theorem checked75234 : checkPrefixCuts (2^48) 9865003009 10 Manual.Count131072.C075234.packed 64 cuts75234 = true := by
 decide +kernel
def pointBounds75234 : List (Nat × Nat × Nat) := [(9865099264,116696928129217,116697318159446)]
theorem point_links_checked75234 : (cuts75234.take 1).map (fun c => (9865003009-1+2*2^10*c.k,116696809576543+c.lower,116697199606700+c.upper)) = pointBounds75234 := by
 decide +kernel
def cuts75235 : List PrefixCut := [⟨64,163232162,163232265⟩]
theorem checked75235 : checkPrefixCuts (2^48) 9865134081 10 Manual.Count131072.C075235.packed 64 cuts75235 = true := by
 decide +kernel
def cuts75236 : List PrefixCut := [⟨64,161860465,161860563⟩]
theorem checked75236 : checkPrefixCuts (2^48) 9865265153 10 Manual.Count131072.C075236.packed 64 cuts75236 = true := by
 decide +kernel
def cuts75237 : List PrefixCut := [⟨6,15064642,15064650⟩,
⟨64,161401823,161401918⟩]
theorem checked75237 : checkPrefixCuts (2^48) 9865396225 10 Manual.Count131072.C075237.packed 64 cuts75237 = true := by
 decide +kernel
def pointBounds75237 : List (Nat × Nat × Nat) := [(9865408512,116697311084999,116697701115467)]
theorem point_links_checked75237 : (cuts75237.take 1).map (fun c => (9865396225-1+2*2^10*c.k,116697296020357+c.lower,116697686050817+c.upper)) = pointBounds75237 := by
 decide +kernel
def cuts75238 : List PrefixCut := [⟨64,162997403,162997501⟩]
theorem checked75238 : checkPrefixCuts (2^48) 9865527297 10 Manual.Count131072.C075238.packed 64 cuts75238 = true := by
 decide +kernel
def cuts75239 : List PrefixCut := [⟨29,72981506,72981550⟩,
⟨64,161283404,161283502⟩]
theorem checked75239 : checkPrefixCuts (2^48) 9865658369 10 Manual.Count131072.C075239.packed 64 cuts75239 = true := by
 decide +kernel
def pointBounds75239 : List (Nat × Nat × Nat) := [(9865717760,116697693401089,116698083431786)]
theorem point_links_checked75239 : (cuts75239.take 1).map (fun c => (9865658369-1+2*2^10*c.k,116697620419583+c.lower,116698010450236+c.upper)) = pointBounds75239 := by
 decide +kernel
def cuts75240 : List PrefixCut := [⟨64,166445230,166445328⟩]
theorem checked75240 : checkPrefixCuts (2^48) 9865789441 10 Manual.Count131072.C075240.packed 64 cuts75240 = true := by
 decide +kernel
def cuts75241 : List PrefixCut := [⟨52,130666776,130666857⟩,
⟨64,160366166,160366267⟩]
theorem checked75241 : checkPrefixCuts (2^48) 9865920513 10 Manual.Count131072.C075241.packed 64 cuts75241 = true := by
 decide +kernel
def pointBounds75241 : List (Nat × Nat × Nat) := [(9866027008,116698078814993,116698468845923)]
theorem point_links_checked75241 : (cuts75241.take 1).map (fun c => (9865920513-1+2*2^10*c.k,116697948148217+c.lower,116698338179066+c.upper)) = pointBounds75241 := by
 decide +kernel
def cuts75242 : List PrefixCut := [⟨64,163302575,163302673⟩]
theorem checked75242 : checkPrefixCuts (2^48) 9866051585 10 Manual.Count131072.C075242.packed 64 cuts75242 = true := by
 decide +kernel
def cuts75243 : List PrefixCut := [⟨64,159905447,159905543⟩]
theorem checked75243 : checkPrefixCuts (2^48) 9866182657 10 Manual.Count131072.C075243.packed 64 cuts75243 = true := by
 decide +kernel
def cuts75244 : List PrefixCut := [⟨11,28528848,28528867⟩,
⟨64,164838783,164838885⟩]
theorem checked75244 : checkPrefixCuts (2^48) 9866313729 10 Manual.Count131072.C075244.packed 64 cuts75244 = true := by
 decide +kernel
def pointBounds75244 : List (Nat × Nat × Nat) := [(9866336256,116698460251253,116698850282416)]
theorem point_links_checked75244 : (cuts75244.take 1).map (fun c => (9866313729-1+2*2^10*c.k,116698431722405+c.lower,116698821753549+c.upper)) = pointBounds75244 := by
 decide +kernel
def cuts75245 : List PrefixCut := [⟨64,161413185,161413283⟩]
theorem checked75245 : checkPrefixCuts (2^48) 9866444801 10 Manual.Count131072.C075245.packed 64 cuts75245 = true := by
 decide +kernel
def cuts75246 : List PrefixCut := [⟨34,85954937,85954982⟩,
⟨64,163778866,163778959⟩]
theorem checked75246 : checkPrefixCuts (2^48) 9866575873 10 Manual.Count131072.C075246.packed 64 cuts75246 = true := by
 decide +kernel
def pointBounds75246 : List (Nat × Nat × Nat) := [(9866645504,116698843929310,116699233960699)]
theorem point_links_checked75246 : (cuts75246.take 1).map (fun c => (9866575873-1+2*2^10*c.k,116698757974373+c.lower,116699148005717+c.upper)) = pointBounds75246 := by
 decide +kernel
def cuts75247 : List PrefixCut := [⟨64,161237743,161237838⟩]
theorem checked75247 : checkPrefixCuts (2^48) 9866706945 10 Manual.Count131072.C075247.packed 64 cuts75247 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000163
