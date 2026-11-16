import PlattAssemblyKernel
import PlattCertificates.Count131072.C017232
import PlattCertificates.Count131072.C017233
import PlattCertificates.Count131072.C017234
import PlattCertificates.Count131072.C017235
import PlattCertificates.Count131072.C017236
import PlattCertificates.Count131072.C017237
import PlattCertificates.Count131072.C017238
import PlattCertificates.Count131072.C017239
import PlattCertificates.Count131072.C017240
import PlattCertificates.Count131072.C017241
import PlattCertificates.Count131072.C017242
import PlattCertificates.Count131072.C017243
import PlattCertificates.Count131072.C017244
import PlattCertificates.Count131072.C017245
import PlattCertificates.Count131072.C017246
import PlattCertificates.Count131072.C017247
import PlattCertificates.Count131072.C017248
import PlattCertificates.Count131072.C017249
import PlattCertificates.Count131072.C017250
import PlattCertificates.Count131072.C017251
import PlattCertificates.Count131072.C017252
import PlattCertificates.Count131072.C017253
import PlattCertificates.Count131072.C017254
import PlattCertificates.Count131072.C017255
import PlattCertificates.Count131072.C017256
import PlattCertificates.Count131072.C017257
import PlattCertificates.Count131072.C017258
import PlattCertificates.Count131072.C017259
import PlattCertificates.Count131072.C017260
import PlattCertificates.Count131072.C017261
import PlattCertificates.Count131072.C017262
import PlattCertificates.Count131072.C017263
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000226
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17232 : List PrefixCut := [⟨30,177649471,177649580⟩,
⟨100,598748716,598749087⟩,
⟨128,763328326,763328799⟩]
theorem checked17232 : checkPrefixCuts (2^48) 2262564865 9 Manual.Count131072.C017232.packed 128 cuts17232 = true := by
 decide +kernel
def pointBounds17232 : List (Nat × Nat × Nat) := [(2262595584,98084161960854,98084541161435),(2262667264,98084583060099,98084962260942)]
theorem point_links_checked17232 : (cuts17232.take 2).map (fun c => (2262564865-1+2*2^9*c.k,98083984311383+c.lower,98084363511855+c.upper)) = pointBounds17232 := by
 decide +kernel
def cuts17233 : List PrefixCut := [⟨42,253893974,253894129⟩,
⟨112,665512727,665513133⟩,
⟨128,760050086,760050549⟩]
theorem checked17233 : checkPrefixCuts (2^48) 2262695937 9 Manual.Count131072.C017233.packed 128 cuts17233 = true := by
 decide +kernel
def pointBounds17233 : List (Nat × Nat × Nat) := [(2262738944,98085001533683,98085380734783),(2262810624,98085413152436,98085792353787)]
theorem point_links_checked17233 : (cuts17233.take 2).map (fun c => (2262695937-1+2*2^9*c.k,98084747639709+c.lower,98085126840654+c.upper)) = pointBounds17233 := by
 decide +kernel
def cuts17234 : List PrefixCut := [⟨54,318312193,318312398⟩,
⟨124,731397485,731397949⟩,
⟨128,754532856,754533335⟩]
theorem checked17234 : checkPrefixCuts (2^48) 2262827009 9 Manual.Count131072.C017234.packed 128 cuts17234 = true := by
 decide +kernel
def pointBounds17234 : List (Nat × Nat × Nat) := [(2262882304,98085826001988,98086205203601),(2262953984,98086239087280,98086618289152)]
theorem point_links_checked17234 : (cuts17234.take 2).map (fun c => (2262827009-1+2*2^9*c.k,98085507689795+c.lower,98085886891203+c.upper)) = pointBounds17234 := by
 decide +kernel
def cuts17235 : List PrefixCut := [⟨66,390185510,390185756⟩,
⟨128,753991574,753992051⟩]
theorem checked17235 : checkPrefixCuts (2^48) 2262958081 9 Manual.Count131072.C017235.packed 128 cuts17235 = true := by
 decide +kernel
def pointBounds17235 : List (Nat × Nat × Nat) := [(2263025664,98086652408161,98087031610294)]
theorem point_links_checked17235 : (cuts17235.take 1).map (fun c => (2262958081-1+2*2^9*c.k,98086262222651+c.lower,98086641424538+c.upper)) = pointBounds17235 := by
 decide +kernel
def cuts17236 : List PrefixCut := [⟨8,49501719,49501751⟩,
⟨78,462547737,462548024⟩,
⟨128,760912794,760913263⟩]
theorem checked17236 : checkPrefixCuts (2^48) 2263089153 9 Manual.Count131072.C017236.packed 128 cuts17236 = true := by
 decide +kernel
def pointBounds17236 : List (Nat × Nat × Nat) := [(2263097344,98087065715944,98087444918340),(2263169024,98087478761962,98087857964613)]
theorem point_links_checked17236 : (cuts17236.take 2).map (fun c => (2263089153-1+2*2^9*c.k,98087016214225+c.lower,98087395416589+c.upper)) = pointBounds17236 := by
 decide +kernel
def cuts17237 : List PrefixCut := [⟨20,118274572,118274644⟩,
⟨90,528806991,528807320⟩,
⟨128,753655419,753655887⟩]
theorem checked17237 : checkPrefixCuts (2^48) 2263220225 9 Manual.Count131072.C017237.packed 128 cuts17237 = true := by
 decide +kernel
def pointBounds17237 : List (Nat × Nat × Nat) := [(2263240704,98087895401591,98088274604496),(2263312384,98088305934010,98088685137172)]
theorem point_links_checked17237 : (cuts17237.take 2).map (fun c => (2263220225-1+2*2^9*c.k,98087777127019+c.lower,98088156329852+c.upper)) = pointBounds17237 := by
 decide +kernel
def cuts17238 : List PrefixCut := [⟨32,191640468,191640582⟩,
⟨102,604385395,604385767⟩,
⟨128,758088851,758089319⟩]
theorem checked17238 : checkPrefixCuts (2^48) 2263351297 9 Manual.Count131072.C017238.packed 128 cuts17238 = true := by
 decide +kernel
def pointBounds17238 : List (Nat × Nat × Nat) := [(2263384064,98088722422906,98089101626321),(2263455744,98089135167833,98089514371506)]
theorem point_links_checked17238 : (cuts17238.take 2).map (fun c => (2263351297-1+2*2^9*c.k,98088530782438+c.lower,98088909985739+c.upper)) = pointBounds17238 := by
 decide +kernel
def cuts17239 : List PrefixCut := [⟨44,267608842,267609009⟩,
⟨114,680452021,680452446⟩,
⟨128,763143436,763143914⟩]
theorem checked17239 : checkPrefixCuts (2^48) 2263482369 9 Manual.Count131072.C017239.packed 128 cuts17239 = true := by
 decide +kernel
def pointBounds17239 : List (Nat × Nat × Nat) := [(2263527424,98089556480131,98089935684067),(2263599104,98089969323310,98090348527504)]
theorem point_links_checked17239 : (cuts17239.take 2).map (fun c => (2263482369-1+2*2^9*c.k,98089288871289+c.lower,98089668075058+c.upper)) = pointBounds17239 := by
 decide +kernel
def cuts17240 : List PrefixCut := [⟨56,333993457,333993667⟩,
⟨126,744199244,744199714⟩,
⟨128,755762906,755763384⟩]
theorem checked17240 : checkPrefixCuts (2^48) 2263613441 9 Manual.Count131072.C017240.packed 128 cuts17240 = true := by
 decide +kernel
def pointBounds17240 : List (Nat × Nat × Nat) := [(2263670784,98090386008182,98090765212639),(2263742464,98090796213969,98091175418686)]
theorem point_links_checked17240 : (cuts17240.take 2).map (fun c => (2263613441-1+2*2^9*c.k,98090052014725+c.lower,98090431218972+c.upper)) = pointBounds17240 := by
 decide +kernel
def cuts17241 : List PrefixCut := [⟨68,400121195,400121446⟩,
⟨128,756962248,756962720⟩]
theorem checked17241 : checkPrefixCuts (2^48) 2263744513 9 Manual.Count131072.C017241.packed 128 cuts17241 = true := by
 decide +kernel
def pointBounds17241 : List (Nat × Nat × Nat) := [(2263814144,98091207898826,98091587103802)]
theorem point_links_checked17241 : (cuts17241.take 1).map (fun c => (2263744513-1+2*2^9*c.k,98090807777631+c.lower,98091186982356+c.upper)) = pointBounds17241 := by
 decide +kernel
def cuts17242 : List PrefixCut := [⟨10,59555464,59555499⟩,
⟨80,471214344,471214643⟩,
⟨128,753313176,753313645⟩]
theorem checked17242 : checkPrefixCuts (2^48) 2263875585 9 Manual.Count131072.C017242.packed 128 cuts17242 = true := by
 decide +kernel
def pointBounds17242 : List (Nat × Nat × Nat) := [(2263885824,98091624295343,98092003500575),(2263957504,98092035954223,98092415159719)]
theorem point_links_checked17242 : (cuts17242.take 2).map (fun c => (2263875585-1+2*2^9*c.k,98091564739879+c.lower,98091943945076+c.upper)) = pointBounds17242 := by
 decide +kernel
def cuts17243 : List PrefixCut := [⟨22,127060539,127060619⟩,
⟨92,544163493,544163835⟩,
⟨128,752026224,752026697⟩]
theorem checked17243 : checkPrefixCuts (2^48) 2264006657 9 Manual.Count131072.C017243.packed 128 cuts17243 = true := by
 decide +kernel
def pointBounds17243 : List (Nat × Nat × Nat) := [(2264029184,98092445113594,98092824319340),(2264100864,98092862216548,98093241422556)]
theorem point_links_checked17243 : (cuts17243.take 2).map (fun c => (2264006657-1+2*2^9*c.k,98092318053055+c.lower,98092697258721+c.upper)) = pointBounds17243 := by
 decide +kernel
def cuts17244 : List PrefixCut := [⟨34,201146254,201146380⟩,
⟨104,612628576,612628954⟩,
⟨128,755090464,755090929⟩]
theorem checked17244 : checkPrefixCuts (2^48) 2264137729 9 Manual.Count131072.C017244.packed 128 cuts17244 = true := by
 decide +kernel
def pointBounds17244 : List (Nat × Nat × Nat) := [(2264172544,98093271225533,98093650431798),(2264244224,98093682707855,98094061914372)]
theorem point_links_checked17244 : (cuts17244.take 2).map (fun c => (2264137729-1+2*2^9*c.k,98093070079279+c.lower,98093449285418+c.upper)) = pointBounds17244 := by
 decide +kernel
def cuts17245 : List PrefixCut := [⟨46,276839075,276839246⟩,
⟨116,691527432,691527856⟩,
⟨128,761635304,761635771⟩]
theorem checked17245 : checkPrefixCuts (2^48) 2264268801 9 Manual.Count131072.C017245.packed 128 cuts17245 = true := by
 decide +kernel
def pointBounds17245 : List (Nat × Nat × Nat) := [(2264315904,98094102008818,98094481215593),(2264387584,98094516697175,98094895904203)]
theorem point_links_checked17245 : (cuts17245.take 2).map (fun c => (2264268801-1+2*2^9*c.k,98093825169743+c.lower,98094204376347+c.upper)) = pointBounds17245 := by
 decide +kernel
def cuts17246 : List PrefixCut := [⟨58,345686045,345686254⟩,
⟨128,756619103,756619569⟩]
theorem checked17246 : checkPrefixCuts (2^48) 2264399873 9 Manual.Count131072.C017246.packed 128 cuts17246 = true := by
 decide +kernel
def pointBounds17246 : List (Nat × Nat × Nat) := [(2264459264,98094932491092,98095311698372),(2264530944,98095343424150,98095722631687)]
theorem point_links_checked17246 : (cuts17246.take 2).map (fun c => (2264399873-1+2*2^9*c.k,98094586805047+c.lower,98094966012118+c.upper)) = pointBounds17246 := by
 decide +kernel
def cuts17247 : List PrefixCut := [⟨70,409677155,409677405⟩,
⟨128,757818024,757818492⟩]
theorem checked17247 : checkPrefixCuts (2^48) 2264530945 9 Manual.Count131072.C017247.packed 128 cuts17247 = true := by
 decide +kernel
def pointBounds17247 : List (Nat × Nat × Nat) := [(2264602624,98095753101305,98096132309092)]
theorem point_links_checked17247 : (cuts17247.take 1).map (fun c => (2264530945-1+2*2^9*c.k,98095343424150+c.lower,98095722631687+c.upper)) = pointBounds17247 := by
 decide +kernel
def cuts17248 : List PrefixCut := [⟨12,71466573,71466616⟩,
⟨82,483479252,483479552⟩,
⟨128,752305795,752306264⟩]
theorem checked17248 : checkPrefixCuts (2^48) 2264662017 9 Manual.Count131072.C017248.packed 128 cuts17248 = true := by
 decide +kernel
def pointBounds17248 : List (Nat × Nat × Nat) := [(2264674304,98096172708747,98096551916795),(2264745984,98096584721426,98096963929731)]
theorem point_links_checked17248 : (cuts17248.take 2).map (fun c => (2264662017-1+2*2^9*c.k,98096101242174+c.lower,98096480450179+c.upper)) = pointBounds17248 := by
 decide +kernel
def cuts17249 : List PrefixCut := [⟨24,137828910,137828996⟩,
⟨94,550064116,550064463⟩,
⟨128,750149419,750149890⟩]
theorem checked17249 : checkPrefixCuts (2^48) 2264793089 9 Manual.Count131072.C017249.packed 128 cuts17249 = true := by
 decide +kernel
def pointBounds17249 : List (Nat × Nat × Nat) := [(2264817664,98096991376879,98097370585439),(2264889344,98097403612085,98097782820906)]
theorem point_links_checked17249 : (cuts17249.take 2).map (fun c => (2264793089-1+2*2^9*c.k,98096853547969+c.lower,98097232756443+c.upper)) = pointBounds17249 := by
 decide +kernel
def cuts17250 : List PrefixCut := [⟨36,213130960,213131091⟩,
⟨106,627204096,627204483⟩,
⟨128,760171978,760172446⟩]
theorem checked17250 : checkPrefixCuts (2^48) 2264924161 9 Manual.Count131072.C017250.packed 128 cuts17250 = true := by
 decide +kernel
def pointBounds17250 : List (Nat × Nat × Nat) := [(2264961024,98097816828348,98098196037424),(2265032704,98098230901484,98098610110816)]
theorem point_links_checked17250 : (cuts17250.take 2).map (fun c => (2264924161-1+2*2^9*c.k,98097603697388+c.lower,98097982906333+c.upper)) = pointBounds17250 := by
 decide +kernel
def cuts17251 : List PrefixCut := [⟨48,287554079,287554255⟩,
⟨118,708932545,708932979⟩,
⟨128,767211201,767211672⟩]
theorem checked17251 : checkPrefixCuts (2^48) 2265055233 9 Manual.Count131072.C017251.packed 128 cuts17251 = true := by
 decide +kernel
def pointBounds17251 : List (Nat × Nat × Nat) := [(2265104384,98098651423445,98099030633034),(2265176064,98099072801911,98099452011758)]
theorem point_links_checked17251 : (cuts17251.take 2).map (fun c => (2265055233-1+2*2^9*c.k,98098363869366+c.lower,98098743078779+c.upper)) = pointBounds17251 := by
 decide +kernel
def cuts17252 : List PrefixCut := [⟨60,351654565,351654782⟩,
⟨128,751137523,751137989⟩]
theorem checked17252 : checkPrefixCuts (2^48) 2265186305 9 Manual.Count131072.C017252.packed 128 cuts17252 = true := by
 decide +kernel
def pointBounds17252 : List (Nat × Nat × Nat) := [(2265247744,98099482735132,98099861945233)]
theorem point_links_checked17252 : (cuts17252.take 1).map (fun c => (2265186305-1+2*2^9*c.k,98099131080567+c.lower,98099510290451+c.upper)) = pointBounds17252 := by
 decide +kernel
def cuts17253 : List PrefixCut := [⟨2,10810098,10810105⟩,
⟨72,427054314,427054580⟩,
⟨128,759294643,759295116⟩]
theorem checked17253 : checkPrefixCuts (2^48) 2265317377 9 Manual.Count131072.C017253.packed 128 cuts17253 = true := by
 decide +kernel
def pointBounds17253 : List (Nat × Nat × Nat) := [(2265319424,98099893028188,98100272238545),(2265391104,98100309272404,98100688483020)]
theorem point_links_checked17253 : (cuts17253.take 2).map (fun c => (2265317377-1+2*2^9*c.k,98099882218090+c.lower,98100261428440+c.upper)) = pointBounds17253 := by
 decide +kernel
def cuts17254 : List PrefixCut := [⟨14,81505690,81505741⟩,
⟨84,490268823,490269127⟩,
⟨128,747820234,747820693⟩]
theorem checked17254 : checkPrefixCuts (2^48) 2265448449 9 Manual.Count131072.C017254.packed 128 cuts17254 = true := by
 decide +kernel
def pointBounds17254 : List (Nat × Nat × Nat) := [(2265462784,98100723018423,98101102229297),(2265534464,98101131781556,98101510992683)]
theorem point_links_checked17254 : (cuts17254.take 2).map (fun c => (2265448449-1+2*2^9*c.k,98100641512733+c.lower,98101020723556+c.upper)) = pointBounds17254 := by
 decide +kernel
def cuts17255 : List PrefixCut := [⟨26,150453352,150453448⟩,
⟨96,563538956,563539305⟩,
⟨128,753243358,753243827⟩]
theorem checked17255 : checkPrefixCuts (2^48) 2265579521 9 Manual.Count131072.C017255.packed 128 cuts17255 = true := by
 decide +kernel
def pointBounds17255 : List (Nat × Nat × Nat) := [(2265606144,98101539786319,98101918997697),(2265677824,98101952871923,98102332083554)]
theorem point_links_checked17255 : (cuts17255.take 2).map (fun c => (2265579521-1+2*2^9*c.k,98101389332967+c.lower,98101768544249+c.upper)) = pointBounds17255 := by
 decide +kernel
def cuts17256 : List PrefixCut := [⟨38,224486199,224486337⟩,
⟨108,644875161,644875559⟩,
⟨128,755684651,755685114⟩]
theorem checked17256 : checkPrefixCuts (2^48) 2265710593 9 Manual.Count131072.C017256.packed 128 cuts17256 = true := by
 decide +kernel
def pointBounds17256 : List (Nat × Nat × Nat) := [(2265749504,98102367062524,98102746274413),(2265821184,98102787451486,98103166663635)]
theorem point_links_checked17256 : (cuts17256.take 2).map (fun c => (2265710593-1+2*2^9*c.k,98102142576325+c.lower,98102521788076+c.upper)) = pointBounds17256 := by
 decide +kernel
def cuts17257 : List PrefixCut := [⟨50,295901402,295901585⟩,
⟨120,709058861,709059299⟩,
⟨128,752783722,752784186⟩]
theorem checked17257 : checkPrefixCuts (2^48) 2265841665 9 Manual.Count131072.C017257.packed 128 cuts17257 = true := by
 decide +kernel
def pointBounds17257 : List (Nat × Nat × Nat) := [(2265892864,98103194162378,98103573374775),(2265964544,98103607319837,98103986532489)]
theorem point_links_checked17257 : (cuts17257.take 2).map (fun c => (2265841665-1+2*2^9*c.k,98102898260976+c.lower,98103277473190+c.upper)) = pointBounds17257 := by
 decide +kernel
def cuts17258 : List PrefixCut := [⟨62,371034325,371034560⟩,
⟨128,762925653,762926129⟩]
theorem checked17258 : checkPrefixCuts (2^48) 2265972737 9 Manual.Count131072.C017258.packed 128 cuts17258 = true := by
 decide +kernel
def pointBounds17258 : List (Nat × Nat × Nat) := [(2266036224,98104022079023,98104401291936)]
theorem point_links_checked17258 : (cuts17258.take 1).map (fun c => (2265972737-1+2*2^9*c.k,98103651044698+c.lower,98104030257376+c.upper)) = pointBounds17258 := by
 decide +kernel
def cuts17259 : List PrefixCut := [⟨4,22482161,22482175⟩,
⟨74,424794379,424794645⟩,
⟨128,744250383,744250847⟩]
theorem checked17259 : checkPrefixCuts (2^48) 2266103809 9 Manual.Count131072.C017259.packed 128 cuts17259 = true := by
 decide +kernel
def pointBounds17259 : List (Nat × Nat × Nat) := [(2266107904,98104436452512,98104815665680),(2266179584,98104838764730,98105217978150)]
theorem point_links_checked17259 : (cuts17259.take 2).map (fun c => (2266103809-1+2*2^9*c.k,98104413970351+c.lower,98104793183505+c.upper)) = pointBounds17259 := by
 decide +kernel
def cuts17260 : List PrefixCut := [⟨16,88060135,88060190⟩,
⟨86,513572511,513572830⟩,
⟨128,765072996,765073471⟩]
theorem checked17260 : checkPrefixCuts (2^48) 2266234881 9 Manual.Count131072.C017260.packed 128 cuts17260 = true := by
 decide +kernel
def pointBounds17260 : List (Nat × Nat × Nat) := [(2266251264,98105246280869,98105625494542),(2266322944,98105671793245,98106051007182)]
theorem point_links_checked17260 : (cuts17260.take 2).map (fun c => (2266234881-1+2*2^9*c.k,98105158220734+c.lower,98105537434352+c.upper)) = pointBounds17260 := by
 decide +kernel
def cuts17261 : List PrefixCut := [⟨28,172632149,172632258⟩,
⟨98,578122386,578122750⟩,
⟨128,760309476,760309953⟩]
theorem checked17261 : checkPrefixCuts (2^48) 2266365953 9 Manual.Count131072.C017261.packed 128 cuts17261 = true := by
 decide +kernel
def pointBounds17261 : List (Nat × Nat × Nat) := [(2266394624,98106095925879,98106475140081),(2266466304,98106501416116,98106880630573)]
theorem point_links_checked17261 : (cuts17261.take 2).map (fun c => (2266365953-1+2*2^9*c.k,98105923293730+c.lower,98106302507823+c.upper)) = pointBounds17261 := by
 decide +kernel
def cuts17262 : List PrefixCut := [⟨40,236330271,236330423⟩,
⟨110,645396315,645396719⟩,
⟨128,747226138,747226608⟩]
theorem checked17262 : checkPrefixCuts (2^48) 2266497025 9 Manual.Count131072.C017262.packed 128 cuts17262 = true := by
 decide +kernel
def pointBounds17262 : List (Nat × Nat × Nat) := [(2266537984,98106919933477,98107299148199),(2266609664,98107328999521,98107708214495)]
theorem point_links_checked17262 : (cuts17262.take 2).map (fun c => (2266497025-1+2*2^9*c.k,98106683603206+c.lower,98107062817776+c.upper)) = pointBounds17262 := by
 decide +kernel
def cuts17263 : List PrefixCut := [⟨52,308713404,308713595⟩,
⟨122,728929468,728929918⟩,
⟨128,765933676,765934148⟩]
theorem checked17263 : checkPrefixCuts (2^48) 2266628097 9 Manual.Count131072.C017263.packed 128 cuts17263 = true := by
 decide +kernel
def pointBounds17263 : List (Nat × Nat × Nat) := [(2266681344,98107739542748,98108118757979),(2266753024,98108159758812,98108538974302)]
theorem point_links_checked17263 : (cuts17263.take 2).map (fun c => (2266628097-1+2*2^9*c.k,98107430829344+c.lower,98107810044384+c.upper)) = pointBounds17263 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000226
