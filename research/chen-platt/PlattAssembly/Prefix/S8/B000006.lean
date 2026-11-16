import PlattAssemblyKernel
import PlattCertificates.Count131072.C070192
import PlattCertificates.Count131072.C070193
import PlattCertificates.Count131072.C070194
import PlattCertificates.Count131072.C070195
import PlattCertificates.Count131072.C070196
import PlattCertificates.Count131072.C070197
import PlattCertificates.Count131072.C070198
import PlattCertificates.Count131072.C070199
import PlattCertificates.Count131072.C070200
import PlattCertificates.Count131072.C070201
import PlattCertificates.Count131072.C070202
import PlattCertificates.Count131072.C070203
import PlattCertificates.Count131072.C070204
import PlattCertificates.Count131072.C070205
import PlattCertificates.Count131072.C070206
import PlattCertificates.Count131072.C070207
import PlattCertificates.Count131072.C070208
import PlattCertificates.Count131072.C070209
import PlattCertificates.Count131072.C070210
import PlattCertificates.Count131072.C070211
import PlattCertificates.Count131072.C070212
import PlattCertificates.Count131072.C070213
import PlattCertificates.Count131072.C070214
import PlattCertificates.Count131072.C070215
import PlattCertificates.Count131072.C070216
import PlattCertificates.Count131072.C070217
import PlattCertificates.Count131072.C070218
import PlattCertificates.Count131072.C070219
import PlattCertificates.Count131072.C070220
import PlattCertificates.Count131072.C070221
import PlattCertificates.Count131072.C070222
import PlattCertificates.Count131072.C070223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70192 : List PrefixCut := [⟨64,177431677,177431777⟩]
theorem checked70192 : checkPrefixCuts (2^48) 9204137985 10 Manual.Count131072.C070192.packed 64 cuts70192 = true := by
 decide +kernel
def cuts70193 : List PrefixCut := [⟨27,74311382,74311428⟩,
⟨64,175869552,175869653⟩]
theorem checked70193 : checkPrefixCuts (2^48) 9204269057 10 Manual.Count131072.C070193.packed 64 cuts70193 = true := by
 decide +kernel
def pointBounds70193 : List (Nat × Nat × Nat) := [(9204324352,115847545448357,115847934973407)]
theorem point_links_checked70193 : (cuts70193.take 1).map (fun c => (9204269057-1+2*2^10*c.k,115847471136975+c.lower,115847860661979+c.upper)) = pointBounds70193 := by
 decide +kernel
def cuts70194 : List PrefixCut := [⟨64,175255418,175255520⟩]
theorem checked70194 : checkPrefixCuts (2^48) 9204400129 10 Manual.Count131072.C070194.packed 64 cuts70194 = true := by
 decide +kernel
def cuts70195 : List PrefixCut := [⟨40,110393441,110393509⟩,
⟨64,177882799,177882903⟩]
theorem checked70195 : checkPrefixCuts (2^48) 9204531201 10 Manual.Count131072.C070195.packed 64 cuts70195 = true := by
 decide +kernel
def pointBounds70195 : List (Nat × Nat × Nat) := [(9204613120,115847932655386,115848322180661)]
theorem point_links_checked70195 : (cuts70195.take 1).map (fun c => (9204531201-1+2*2^10*c.k,115847822261945+c.lower,115848211787152+c.upper)) = pointBounds70195 := by
 decide +kernel
def cuts70196 : List PrefixCut := [⟨64,173782641,173782746⟩]
theorem checked70196 : checkPrefixCuts (2^48) 9204662273 10 Manual.Count131072.C070196.packed 64 cuts70196 = true := by
 decide +kernel
def cuts70197 : List PrefixCut := [⟨53,144638597,144638681⟩,
⟨64,174085948,174086052⟩]
theorem checked70197 : checkPrefixCuts (2^48) 9204793345 10 Manual.Count131072.C070197.packed 64 cuts70197 = true := by
 decide +kernel
def pointBounds70197 : List (Nat × Nat × Nat) := [(9204901888,115848318565982,115848708091482)]
theorem point_links_checked70197 : (cuts70197.take 1).map (fun c => (9204793345-1+2*2^10*c.k,115848173927385+c.lower,115848563452801+c.upper)) = pointBounds70197 := by
 decide +kernel
def cuts70198 : List PrefixCut := [⟨64,176621490,176621593⟩]
theorem checked70198 : checkPrefixCuts (2^48) 9204924417 10 Manual.Count131072.C070198.packed 64 cuts70198 = true := by
 decide +kernel
def cuts70199 : List PrefixCut := [⟨64,173714054,173714160⟩]
theorem checked70199 : checkPrefixCuts (2^48) 9205055489 10 Manual.Count131072.C070199.packed 64 cuts70199 = true := by
 decide +kernel
def cuts70200 : List PrefixCut := [⟨2,5809792,5809795⟩,
⟨64,176249528,176249628⟩]
theorem checked70200 : checkPrefixCuts (2^48) 9205186561 10 Manual.Count131072.C070200.packed 64 cuts70200 = true := by
 decide +kernel
def pointBounds70200 : List (Nat × Nat × Nat) := [(9205190656,115848704158669,115849093684401)]
theorem point_links_checked70200 : (cuts70200.take 1).map (fun c => (9205186561-1+2*2^10*c.k,115848698348877+c.lower,115849087874606+c.upper)) = pointBounds70200 := by
 decide +kernel
def cuts70201 : List PrefixCut := [⟨64,175023920,175024027⟩]
theorem checked70201 : checkPrefixCuts (2^48) 9205317633 10 Manual.Count131072.C070201.packed 64 cuts70201 = true := by
 decide +kernel
def cuts70202 : List PrefixCut := [⟨15,40759059,40759082⟩,
⟨64,176642000,176642102⟩]
theorem checked70202 : checkPrefixCuts (2^48) 9205448705 10 Manual.Count131072.C070202.packed 64 cuts70202 = true := by
 decide +kernel
def pointBounds70202 : List (Nat × Nat × Nat) := [(9205479424,115849090381384,115849479907343)]
theorem point_links_checked70202 : (cuts70202.take 1).map (fun c => (9205448705-1+2*2^10*c.k,115849049622325+c.lower,115849439148261+c.upper)) = pointBounds70202 := by
 decide +kernel
def cuts70203 : List PrefixCut := [⟨64,173490124,173490227⟩]
theorem checked70203 : checkPrefixCuts (2^48) 9205579777 10 Manual.Count131072.C070203.packed 64 cuts70203 = true := by
 decide +kernel
def cuts70204 : List PrefixCut := [⟨28,75797957,75798003⟩,
⟨64,173487651,173487754⟩]
theorem checked70204 : checkPrefixCuts (2^48) 9205710849 10 Manual.Count131072.C070204.packed 64 cuts70204 = true := by
 decide +kernel
def pointBounds70204 : List (Nat × Nat × Nat) := [(9205768192,115849475552406,115849865078593)]
theorem point_links_checked70204 : (cuts70204.take 1).map (fun c => (9205710849-1+2*2^10*c.k,115849399754449+c.lower,115849789280590+c.upper)) = pointBounds70204 := by
 decide +kernel
def cuts70205 : List PrefixCut := [⟨64,175227975,175228076⟩]
theorem checked70205 : checkPrefixCuts (2^48) 9205841921 10 Manual.Count131072.C070205.packed 64 cuts70205 = true := by
 decide +kernel
def cuts70206 : List PrefixCut := [⟨41,112210638,112210706⟩,
⟨64,174613984,174614092⟩]
theorem checked70206 : checkPrefixCuts (2^48) 9205972993 10 Manual.Count131072.C070206.packed 64 cuts70206 = true := by
 decide +kernel
def pointBounds70206 : List (Nat × Nat × Nat) := [(9206056960,115849860680713,115850250207126)]
theorem point_links_checked70206 : (cuts70206.take 1).map (fun c => (9205972993-1+2*2^10*c.k,115849748470075+c.lower,115850137996420+c.upper)) = pointBounds70206 := by
 decide +kernel
def cuts70207 : List PrefixCut := [⟨64,174672650,174672746⟩]
theorem checked70207 : checkPrefixCuts (2^48) 9206104065 10 Manual.Count131072.C070207.packed 64 cuts70207 = true := by
 decide +kernel
def cuts70208 : List PrefixCut := [⟨54,147520469,147520557⟩,
⟨64,174394992,174395097⟩]
theorem checked70208 : checkPrefixCuts (2^48) 9206235137 10 Manual.Count131072.C070208.packed 64 cuts70208 = true := by
 decide +kernel
def pointBounds70208 : List (Nat × Nat × Nat) := [(9206345728,115850245277178,115850634803815)]
theorem point_links_checked70208 : (cuts70208.take 1).map (fun c => (9206235137-1+2*2^10*c.k,115850097756709+c.lower,115850487283258+c.upper)) = pointBounds70208 := by
 decide +kernel
def cuts70209 : List PrefixCut := [⟨64,176868993,176869103⟩]
theorem checked70209 : checkPrefixCuts (2^48) 9206366209 10 Manual.Count131072.C070209.packed 64 cuts70209 = true := by
 decide +kernel
def cuts70210 : List PrefixCut := [⟨64,176438445,176438546⟩]
theorem checked70210 : checkPrefixCuts (2^48) 9206497281 10 Manual.Count131072.C070210.packed 64 cuts70210 = true := by
 decide +kernel
def cuts70211 : List PrefixCut := [⟨3,8529883,8529889⟩,
⟨64,174204114,174204219⟩]
theorem checked70211 : checkPrefixCuts (2^48) 9206628353 10 Manual.Count131072.C070211.packed 64 cuts70211 = true := by
 decide +kernel
def pointBounds70211 : List (Nat × Nat × Nat) := [(9206634496,115850633989022,115851023515893)]
theorem point_links_checked70211 : (cuts70211.take 1).map (fun c => (9206628353-1+2*2^10*c.k,115850625459139+c.lower,115851014986004+c.upper)) = pointBounds70211 := by
 decide +kernel
def cuts70212 : List PrefixCut := [⟨64,174201636,174201736⟩]
theorem checked70212 : checkPrefixCuts (2^48) 9206759425 10 Manual.Count131072.C070212.packed 64 cuts70212 = true := by
 decide +kernel
def cuts70213 : List PrefixCut := [⟨16,43198441,43198467⟩,
⟨64,176430899,176431004⟩]
theorem checked70213 : checkPrefixCuts (2^48) 9206890497 10 Manual.Count131072.C070213.packed 64 cuts70213 = true := by
 decide +kernel
def pointBounds70213 : List (Nat × Nat × Nat) := [(9206923264,115851017063330,115851406590426)]
theorem point_links_checked70213 : (cuts70213.take 1).map (fun c => (9206890497-1+2*2^10*c.k,115850973864889+c.lower,115851363391959+c.upper)) = pointBounds70213 := by
 decide +kernel
def cuts70214 : List PrefixCut := [⟨64,175022103,175022206⟩]
theorem checked70214 : checkPrefixCuts (2^48) 9207021569 10 Manual.Count131072.C070214.packed 64 cuts70214 = true := by
 decide +kernel
def cuts70215 : List PrefixCut := [⟨29,79943768,79943816⟩,
⟨64,174805626,174805734⟩]
theorem checked70215 : checkPrefixCuts (2^48) 9207152641 10 Manual.Count131072.C070215.packed 64 cuts70215 = true := by
 decide +kernel
def pointBounds70215 : List (Nat × Nat × Nat) := [(9207212032,115851405261659,115851794788985)]
theorem point_links_checked70215 : (cuts70215.take 1).map (fun c => (9207152641-1+2*2^10*c.k,115851325317891+c.lower,115851714845169+c.upper)) = pointBounds70215 := by
 decide +kernel
def cuts70216 : List PrefixCut := [⟨64,175353400,175353507⟩]
theorem checked70216 : checkPrefixCuts (2^48) 9207283713 10 Manual.Count131072.C070216.packed 64 cuts70216 = true := by
 decide +kernel
def cuts70217 : List PrefixCut := [⟨42,114913812,114913877⟩,
⟨64,175350899,175350999⟩]
theorem checked70217 : checkPrefixCuts (2^48) 9207414785 10 Manual.Count131072.C070217.packed 64 cuts70217 = true := by
 decide +kernel
def pointBounds70217 : List (Nat × Nat × Nat) := [(9207500800,115851790390729,115852179918287)]
theorem point_links_checked70217 : (cuts70217.take 1).map (fun c => (9207414785-1+2*2^10*c.k,115851675476917+c.lower,115852065004410+c.upper)) = pointBounds70217 := by
 decide +kernel
def cuts70218 : List PrefixCut := [⟨64,174217310,174217412⟩]
theorem checked70218 : checkPrefixCuts (2^48) 9207545857 10 Manual.Count131072.C070218.packed 64 cuts70218 = true := by
 decide +kernel
def cuts70219 : List PrefixCut := [⟨55,148903565,148903651⟩,
⟨64,173756311,173756411⟩]
theorem checked70219 : checkPrefixCuts (2^48) 9207676929 10 Manual.Count131072.C070219.packed 64 cuts70219 = true := by
 decide +kernel
def pointBounds70219 : List (Nat × Nat × Nat) := [(9207789568,115852173948691,115852563476472)]
theorem point_links_checked70219 : (cuts70219.take 1).map (fun c => (9207676929-1+2*2^10*c.k,115852025045126+c.lower,115852414572821+c.upper)) = pointBounds70219 := by
 decide +kernel
def cuts70220 : List PrefixCut := [⟨64,175098852,175098959⟩]
theorem checked70220 : checkPrefixCuts (2^48) 9207808001 10 Manual.Count131072.C070220.packed 64 cuts70220 = true := by
 decide +kernel
def cuts70221 : List PrefixCut := [⟨64,176227407,176227508⟩]
theorem checked70221 : checkPrefixCuts (2^48) 9207939073 10 Manual.Count131072.C070221.packed 64 cuts70221 = true := by
 decide +kernel
def cuts70222 : List PrefixCut := [⟨4,10943440,10943447⟩,
⟨64,176775109,176775217⟩]
theorem checked70222 : checkPrefixCuts (2^48) 9208070145 10 Manual.Count131072.C070222.packed 64 cuts70222 = true := by
 decide +kernel
def pointBounds70222 : List (Nat × Nat × Nat) := [(9208078336,115852561071136,115852950599146)]
theorem point_links_checked70222 : (cuts70222.take 1).map (fun c => (9208070145-1+2*2^10*c.k,115852550127696+c.lower,115852939655699+c.upper)) = pointBounds70222 := by
 decide +kernel
def cuts70223 : List PrefixCut := [⟨64,174143786,174143894⟩]
theorem checked70223 : checkPrefixCuts (2^48) 9208201217 10 Manual.Count131072.C070223.packed 64 cuts70223 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000006
