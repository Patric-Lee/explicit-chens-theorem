import PlattAssemblyKernel
import PlattCertificates.Count131072.C048192
import PlattCertificates.Count131072.C048193
import PlattCertificates.Count131072.C048194
import PlattCertificates.Count131072.C048195
import PlattCertificates.Count131072.C048196
import PlattCertificates.Count131072.C048197
import PlattCertificates.Count131072.C048198
import PlattCertificates.Count131072.C048199
import PlattCertificates.Count131072.C048200
import PlattCertificates.Count131072.C048201
import PlattCertificates.Count131072.C048202
import PlattCertificates.Count131072.C048203
import PlattCertificates.Count131072.C048204
import PlattCertificates.Count131072.C048205
import PlattCertificates.Count131072.C048206
import PlattCertificates.Count131072.C048207
import PlattCertificates.Count131072.C048208
import PlattCertificates.Count131072.C048209
import PlattCertificates.Count131072.C048210
import PlattCertificates.Count131072.C048211
import PlattCertificates.Count131072.C048212
import PlattCertificates.Count131072.C048213
import PlattCertificates.Count131072.C048214
import PlattCertificates.Count131072.C048215
import PlattCertificates.Count131072.C048216
import PlattCertificates.Count131072.C048217
import PlattCertificates.Count131072.C048218
import PlattCertificates.Count131072.C048219
import PlattCertificates.Count131072.C048220
import PlattCertificates.Count131072.C048221
import PlattCertificates.Count131072.C048222
import PlattCertificates.Count131072.C048223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000256
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48192 : List PrefixCut := [⟨34,140011803,140011882⟩,
⟨64,258379338,258379484⟩]
theorem checked48192 : checkPrefixCuts (2^48) 6320553985 10 Manual.Count131072.C048192.packed 64 cuts48192 = true := by
 decide +kernel
def pointBounds48192 : List (Nat × Nat × Nat) := [(6320623616,111198330535661,111198717396055)]
theorem point_links_checked48192 : (cuts48192.take 1).map (fun c => (6320553985-1+2*2^10*c.k,111198190523858+c.lower,111198577384173+c.upper)) = pointBounds48192 := by
 decide +kernel
def cuts48193 : List PrefixCut := [⟨64,255123109,255123260⟩]
theorem checked48193 : checkPrefixCuts (2^48) 6320685057 10 Manual.Count131072.C048193.packed 64 cuts48193 = true := by
 decide +kernel
def cuts48194 : List PrefixCut := [⟨3,12201602,12201608⟩,
⟨64,258635780,258635924⟩]
theorem checked48194 : checkPrefixCuts (2^48) 6320816129 10 Manual.Count131072.C048194.packed 64 cuts48194 = true := by
 decide +kernel
def pointBounds48194 : List (Nat × Nat × Nat) := [(6320822272,111198716227907,111199103088525)]
theorem point_links_checked48194 : (cuts48194.take 1).map (fun c => (6320816129-1+2*2^10*c.k,111198704026305+c.lower,111199090886917+c.upper)) = pointBounds48194 := by
 decide +kernel
def cuts48195 : List PrefixCut := [⟨36,146816185,146816273⟩,
⟨64,259253856,259254006⟩]
theorem checked48195 : checkPrefixCuts (2^48) 6320947201 10 Manual.Count131072.C048195.packed 64 cuts48195 = true := by
 decide +kernel
def pointBounds48195 : List (Nat × Nat × Nat) := [(6321020928,111199109478270,111199496339114)]
theorem point_links_checked48195 : (cuts48195.take 1).map (fun c => (6320947201-1+2*2^10*c.k,111198962662085+c.lower,111199349522841+c.upper)) = pointBounds48195 := by
 decide +kernel
def cuts48196 : List PrefixCut := [⟨64,260985090,260985243⟩]
theorem checked48196 : checkPrefixCuts (2^48) 6321078273 10 Manual.Count131072.C048196.packed 64 cuts48196 = true := by
 decide +kernel
def cuts48197 : List PrefixCut := [⟨5,19191830,19191842⟩,
⟨64,259821939,259822094⟩]
theorem checked48197 : checkPrefixCuts (2^48) 6321209345 10 Manual.Count131072.C048197.packed 64 cuts48197 = true := by
 decide +kernel
def pointBounds48197 : List (Nat × Nat × Nat) := [(6321219584,111199502092861,111199888953932)]
theorem point_links_checked48197 : (cuts48197.take 1).map (fun c => (6321209345-1+2*2^10*c.k,111199482901031+c.lower,111199869762090+c.upper)) = pointBounds48197 := by
 decide +kernel
def cuts48198 : List PrefixCut := [⟨38,152951783,152951874⟩,
⟨64,258614321,258614470⟩]
theorem checked48198 : checkPrefixCuts (2^48) 6321340417 10 Manual.Count131072.C048198.packed 64 cuts48198 = true := by
 decide +kernel
def pointBounds48198 : List (Nat × Nat × Nat) := [(6321418240,111199895674753,111200282536058)]
theorem point_links_checked48198 : (cuts48198.take 1).map (fun c => (6321340417-1+2*2^10*c.k,111199742722970+c.lower,111200129584184+c.upper)) = pointBounds48198 := by
 decide +kernel
def cuts48199 : List PrefixCut := [⟨64,260835273,260835424⟩]
theorem checked48199 : checkPrefixCuts (2^48) 6321471489 10 Manual.Count131072.C048199.packed 64 cuts48199 = true := by
 decide +kernel
def cuts48200 : List PrefixCut := [⟨7,28407477,28407493⟩,
⟨64,259449601,259449749⟩]
theorem checked48200 : checkPrefixCuts (2^48) 6321602561 10 Manual.Count131072.C048200.packed 64 cuts48200 = true := by
 decide +kernel
def pointBounds48200 : List (Nat × Nat × Nat) := [(6321616896,111200290580041,111200677441571)]
theorem point_links_checked48200 : (cuts48200.take 1).map (fun c => (6321602561-1+2*2^10*c.k,111200262172564+c.lower,111200649034078+c.upper)) = pointBounds48200 := by
 decide +kernel
def cuts48201 : List PrefixCut := [⟨40,161669068,161669158⟩,
⟨64,259221594,259221742⟩]
theorem checked48201 : checkPrefixCuts (2^48) 6321733633 10 Manual.Count131072.C048201.packed 64 cuts48201 = true := by
 decide +kernel
def pointBounds48201 : List (Nat × Nat × Nat) := [(6321815552,111200683291233,111201070152985)]
theorem point_links_checked48201 : (cuts48201.take 1).map (fun c => (6321733633-1+2*2^10*c.k,111200521622165+c.lower,111200908483827+c.upper)) = pointBounds48201 := by
 decide +kernel
def cuts48202 : List PrefixCut := [⟨64,259438819,259438971⟩]
theorem checked48202 : checkPrefixCuts (2^48) 6321864705 10 Manual.Count131072.C048202.packed 64 cuts48202 = true := by
 decide +kernel
def cuts48203 : List PrefixCut := [⟨9,35084156,35084176⟩,
⟨64,258275852,258275993⟩]
theorem checked48203 : checkPrefixCuts (2^48) 6321995777 10 Manual.Count131072.C048203.packed 64 cuts48203 = true := by
 decide +kernel
def pointBounds48203 : List (Nat × Nat × Nat) := [(6322014208,111201075366734,111201462228716)]
theorem point_links_checked48203 : (cuts48203.take 1).map (fun c => (6321995777-1+2*2^10*c.k,111201040282578+c.lower,111201427144540+c.upper)) = pointBounds48203 := by
 decide +kernel
def cuts48204 : List PrefixCut := [⟨42,170741409,170741512⟩,
⟨64,259294509,259294663⟩]
theorem checked48204 : checkPrefixCuts (2^48) 6322126849 10 Manual.Count131072.C048204.packed 64 cuts48204 = true := by
 decide +kernel
def pointBounds48204 : List (Nat × Nat × Nat) := [(6322212864,111201469299839,111201856162045)]
theorem point_links_checked48204 : (cuts48204.take 1).map (fun c => (6322126849-1+2*2^10*c.k,111201298558430+c.lower,111201685420533+c.upper)) = pointBounds48204 := by
 decide +kernel
def cuts48205 : List PrefixCut := [⟨64,255771977,255772126⟩]
theorem checked48205 : checkPrefixCuts (2^48) 6322257921 10 Manual.Count131072.C048205.packed 64 cuts48205 = true := by
 decide +kernel
def cuts48206 : List PrefixCut := [⟨11,43362732,43362757⟩,
⟨64,258749507,258749658⟩]
theorem checked48206 : checkPrefixCuts (2^48) 6322388993 10 Manual.Count131072.C048206.packed 64 cuts48206 = true := by
 decide +kernel
def pointBounds48206 : List (Nat × Nat × Nat) := [(6322411520,111201856987648,111202243850079)]
theorem point_links_checked48206 : (cuts48206.take 1).map (fun c => (6322388993-1+2*2^10*c.k,111201813624916+c.lower,111202200487322+c.upper)) = pointBounds48206 := by
 decide +kernel
def cuts48207 : List PrefixCut := [⟨44,178655124,178655222⟩,
⟨64,258744151,258744297⟩]
theorem checked48207 : checkPrefixCuts (2^48) 6322520065 10 Manual.Count131072.C048207.packed 64 cuts48207 = true := by
 decide +kernel
def pointBounds48207 : List (Nat × Nat × Nat) := [(6322610176,111202251029547,111202637892202)]
theorem point_links_checked48207 : (cuts48207.take 1).map (fun c => (6322520065-1+2*2^10*c.k,111202072374423+c.lower,111202459236980+c.upper)) = pointBounds48207 := by
 decide +kernel
def cuts48208 : List PrefixCut := [⟨64,257625831,257625979⟩]
theorem checked48208 : checkPrefixCuts (2^48) 6322651137 10 Manual.Count131072.C048208.packed 64 cuts48208 = true := by
 decide +kernel
def cuts48209 : List PrefixCut := [⟨13,52441587,52441615⟩,
⟨64,258599875,258600022⟩]
theorem checked48209 : checkPrefixCuts (2^48) 6322782209 10 Manual.Count131072.C048209.packed 64 cuts48209 = true := by
 decide +kernel
def pointBounds48209 : List (Nat × Nat × Nat) := [(6322808832,111202641185992,111203028048871)]
theorem point_links_checked48209 : (cuts48209.take 1).map (fun c => (6322782209-1+2*2^10*c.k,111202588744405+c.lower,111202975607256+c.upper)) = pointBounds48209 := by
 decide +kernel
def cuts48210 : List PrefixCut := [⟨46,185143350,185143458⟩,
⟨64,257793224,257793375⟩]
theorem checked48210 : checkPrefixCuts (2^48) 6322913281 10 Manual.Count131072.C048210.packed 64 cuts48210 = true := by
 decide +kernel
def pointBounds48210 : List (Nat × Nat × Nat) := [(6323007488,111203032487630,111203419350736)]
theorem point_links_checked48210 : (cuts48210.take 1).map (fun c => (6322913281-1+2*2^10*c.k,111202847344280+c.lower,111203234207278+c.upper)) = pointBounds48210 := by
 decide +kernel
def cuts48211 : List PrefixCut := [⟨64,259123316,259123459⟩]
theorem checked48211 : checkPrefixCuts (2^48) 6323044353 10 Manual.Count131072.C048211.packed 64 cuts48211 = true := by
 decide +kernel
def cuts48212 : List PrefixCut := [⟨15,61741879,61741917⟩,
⟨64,256981281,256981436⟩]
theorem checked48212 : checkPrefixCuts (2^48) 6323175425 10 Manual.Count131072.C048212.packed 64 cuts48212 = true := by
 decide +kernel
def pointBounds48212 : List (Nat × Nat × Nat) := [(6323206144,111203426002699,111203812866029)]
theorem point_links_checked48212 : (cuts48212.take 1).map (fun c => (6323175425-1+2*2^10*c.k,111203364260820+c.lower,111203751124112+c.upper)) = pointBounds48212 := by
 decide +kernel
def cuts48213 : List PrefixCut := [⟨48,193811916,193812021⟩,
⟨64,257376581,257376723⟩]
theorem checked48213 : checkPrefixCuts (2^48) 6323306497 10 Manual.Count131072.C048213.packed 64 cuts48213 = true := by
 decide +kernel
def pointBounds48213 : List (Nat × Nat × Nat) := [(6323404800,111203815054017,111204201917569)]
theorem point_links_checked48213 : (cuts48213.take 1).map (fun c => (6323306497-1+2*2^10*c.k,111203621242101+c.lower,111204008105548+c.upper)) = pointBounds48213 := by
 decide +kernel
def cuts48214 : List PrefixCut := [⟨64,259507837,259507990⟩]
theorem checked48214 : checkPrefixCuts (2^48) 6323437569 10 Manual.Count131072.C048214.packed 64 cuts48214 = true := by
 decide +kernel
def cuts48215 : List PrefixCut := [⟨17,67880662,67880702⟩,
⟨64,260481701,260481853⟩]
theorem checked48215 : checkPrefixCuts (2^48) 6323568641 10 Manual.Count131072.C048215.packed 64 cuts48215 = true := by
 decide +kernel
def pointBounds48215 : List (Nat × Nat × Nat) := [(6323603456,111204206007181,111204592870963)]
theorem point_links_checked48215 : (cuts48215.take 1).map (fun c => (6323568641-1+2*2^10*c.k,111204138126519+c.lower,111204524990261+c.upper)) = pointBounds48215 := by
 decide +kernel
def cuts48216 : List PrefixCut := [⟨50,203681188,203681310⟩,
⟨64,257672168,257672321⟩]
theorem checked48216 : checkPrefixCuts (2^48) 6323699713 10 Manual.Count131072.C048216.packed 64 cuts48216 = true := by
 decide +kernel
def pointBounds48216 : List (Nat × Nat × Nat) := [(6323802112,111204602289408,111204989153424)]
theorem point_links_checked48216 : (cuts48216.take 1).map (fun c => (6323699713-1+2*2^10*c.k,111204398608220+c.lower,111204785472114+c.upper)) = pointBounds48216 := by
 decide +kernel
def cuts48217 : List PrefixCut := [⟨64,253794433,253794581⟩]
theorem checked48217 : checkPrefixCuts (2^48) 6323830785 10 Manual.Count131072.C048217.packed 64 cuts48217 = true := by
 decide +kernel
def cuts48218 : List PrefixCut := [⟨19,76956281,76956328⟩,
⟨64,259263785,259263939⟩]
theorem checked48218 : checkPrefixCuts (2^48) 6323961857 10 Manual.Count131072.C048218.packed 64 cuts48218 = true := by
 decide +kernel
def pointBounds48218 : List (Nat × Nat × Nat) := [(6324000768,111204987031102,111205373895344)]
theorem point_links_checked48218 : (cuts48218.take 1).map (fun c => (6323961857-1+2*2^10*c.k,111204910074821+c.lower,111205296939016+c.upper)) = pointBounds48218 := by
 decide +kernel
def cuts48219 : List PrefixCut := [⟨52,208786882,208787003⟩,
⟨64,258991351,258991501⟩]
theorem checked48219 : checkPrefixCuts (2^48) 6324092929 10 Manual.Count131072.C048219.packed 64 cuts48219 = true := by
 decide +kernel
def pointBounds48219 : List (Nat × Nat × Nat) := [(6324199424,111205378125488,111205764989958)]
theorem point_links_checked48219 : (cuts48219.take 1).map (fun c => (6324092929-1+2*2^10*c.k,111205169338606+c.lower,111205556202955+c.upper)) = pointBounds48219 := by
 decide +kernel
def cuts48220 : List PrefixCut := [⟨64,257517260,257517413⟩]
theorem checked48220 : checkPrefixCuts (2^48) 6324224001 10 Manual.Count131072.C048220.packed 64 cuts48220 = true := by
 decide +kernel
def cuts48221 : List PrefixCut := [⟨21,83582916,83582966⟩,
⟨64,255286627,255286774⟩]
theorem checked48221 : checkPrefixCuts (2^48) 6324355073 10 Manual.Count131072.C048221.packed 64 cuts48221 = true := by
 decide +kernel
def pointBounds48221 : List (Nat × Nat × Nat) := [(6324398080,111205769430133,111206156294835)]
theorem point_links_checked48221 : (cuts48221.take 1).map (fun c => (6324355073-1+2*2^10*c.k,111205685847217+c.lower,111206072711869+c.upper)) = pointBounds48221 := by
 decide +kernel
def cuts48222 : List PrefixCut := [⟨54,218520488,218520614⟩,
⟨64,258396723,258396871⟩]
theorem checked48222 : checkPrefixCuts (2^48) 6324486145 10 Manual.Count131072.C048222.packed 64 cuts48222 = true := by
 decide +kernel
def pointBounds48222 : List (Nat × Nat × Nat) := [(6324596736,111206159654332,111206546519257)]
theorem point_links_checked48222 : (cuts48222.take 1).map (fun c => (6324486145-1+2*2^10*c.k,111205941133844+c.lower,111206327998643+c.upper)) = pointBounds48222 := by
 decide +kernel
def cuts48223 : List PrefixCut := [⟨64,258836402,258836546⟩]
theorem checked48223 : checkPrefixCuts (2^48) 6324617217 10 Manual.Count131072.C048223.packed 64 cuts48223 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000256
