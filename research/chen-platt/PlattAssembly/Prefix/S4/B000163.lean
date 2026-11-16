import PlattAssemblyKernel
import PlattCertificates.Count131072.C035216
import PlattCertificates.Count131072.C035217
import PlattCertificates.Count131072.C035218
import PlattCertificates.Count131072.C035219
import PlattCertificates.Count131072.C035220
import PlattCertificates.Count131072.C035221
import PlattCertificates.Count131072.C035222
import PlattCertificates.Count131072.C035223
import PlattCertificates.Count131072.C035224
import PlattCertificates.Count131072.C035225
import PlattCertificates.Count131072.C035226
import PlattCertificates.Count131072.C035227
import PlattCertificates.Count131072.C035228
import PlattCertificates.Count131072.C035229
import PlattCertificates.Count131072.C035230
import PlattCertificates.Count131072.C035231
import PlattCertificates.Count131072.C035232
import PlattCertificates.Count131072.C035233
import PlattCertificates.Count131072.C035234
import PlattCertificates.Count131072.C035235
import PlattCertificates.Count131072.C035236
import PlattCertificates.Count131072.C035237
import PlattCertificates.Count131072.C035238
import PlattCertificates.Count131072.C035239
import PlattCertificates.Count131072.C035240
import PlattCertificates.Count131072.C035241
import PlattCertificates.Count131072.C035242
import PlattCertificates.Count131072.C035243
import PlattCertificates.Count131072.C035244
import PlattCertificates.Count131072.C035245
import PlattCertificates.Count131072.C035246
import PlattCertificates.Count131072.C035247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000163
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts35216 : List PrefixCut := [⟨64,357644693,357644913⟩]
theorem checked35216 : checkPrefixCuts (2^48) 4619763713 10 Manual.Count131072.C035216.packed 64 cuts35216 = true := by
 decide +kernel
def cuts35217 : List PrefixCut := [⟨5,28513659,28513677⟩,
⟨64,359766983,359767206⟩]
theorem checked35217 : checkPrefixCuts (2^48) 4619894785 10 Manual.Count131072.C035217.packed 64 cuts35217 = true := by
 decide +kernel
def pointBounds35217 : List (Nat × Nat × Nat) := [(4619905024,107261347645073,107261732176269)]
theorem point_links_checked35217 : (cuts35217.take 1).map (fun c => (4619894785-1+2*2^10*c.k,107261319131414+c.lower,107261703662592+c.upper)) = pointBounds35217 := by
 decide +kernel
def cuts35218 : List PrefixCut := [⟨12,67565598,67565642⟩,
⟨64,356284131,356284355⟩]
theorem checked35218 : checkPrefixCuts (2^48) 4620025857 10 Manual.Count131072.C035218.packed 64 cuts35218 = true := by
 decide +kernel
def pointBounds35218 : List (Nat × Nat × Nat) := [(4620050432,107261746463995,107262130995440)]
theorem point_links_checked35218 : (cuts35218.take 1).map (fun c => (4620025857-1+2*2^10*c.k,107261678898397+c.lower,107262063429798+c.upper)) = pointBounds35218 := by
 decide +kernel
def cuts35219 : List PrefixCut := [⟨19,109052129,109052196⟩,
⟨64,364559465,364559690⟩]
theorem checked35219 : checkPrefixCuts (2^48) 4620156929 10 Manual.Count131072.C035219.packed 64 cuts35219 = true := by
 decide +kernel
def pointBounds35219 : List (Nat × Nat × Nat) := [(4620195840,107262144234657,107262528766349)]
theorem point_links_checked35219 : (cuts35219.take 1).map (fun c => (4620156929-1+2*2^10*c.k,107262035182528+c.lower,107262419714153+c.upper)) = pointBounds35219 := by
 decide +kernel
def cuts35220 : List PrefixCut := [⟨26,147307339,147307429⟩,
⟨64,362721475,362721702⟩]
theorem checked35220 : checkPrefixCuts (2^48) 4620288001 10 Manual.Count131072.C035220.packed 64 cuts35220 = true := by
 decide +kernel
def pointBounds35220 : List (Nat × Nat × Nat) := [(4620341248,107262547049332,107262931581272)]
theorem point_links_checked35220 : (cuts35220.take 1).map (fun c => (4620288001-1+2*2^10*c.k,107262399741993+c.lower,107262784273843+c.upper)) = pointBounds35220 := by
 decide +kernel
def cuts35221 : List PrefixCut := [⟨33,189398191,189398306⟩,
⟨64,362162963,362163185⟩]
theorem checked35221 : checkPrefixCuts (2^48) 4620419073 10 Manual.Count131072.C035221.packed 64 cuts35221 = true := by
 decide +kernel
def pointBounds35221 : List (Nat × Nat × Nat) := [(4620486656,107262951861659,107263336393851)]
theorem point_links_checked35221 : (cuts35221.take 1).map (fun c => (4620419073-1+2*2^10*c.k,107262762463468+c.lower,107263146995545+c.upper)) = pointBounds35221 := by
 decide +kernel
def cuts35222 : List PrefixCut := [⟨40,221861543,221861675⟩,
⟨64,355817257,355817467⟩]
theorem checked35222 : checkPrefixCuts (2^48) 4620550145 10 Manual.Count131072.C035222.packed 64 cuts35222 = true := by
 decide +kernel
def pointBounds35222 : List (Nat × Nat × Nat) := [(4620632064,107263346487974,107263731020405)]
theorem point_links_checked35222 : (cuts35222.take 1).map (fun c => (4620550145-1+2*2^10*c.k,107263124626431+c.lower,107263509158730+c.upper)) = pointBounds35222 := by
 decide +kernel
def cuts35223 : List PrefixCut := [⟨47,262972995,262973163⟩,
⟨64,356111751,356111979⟩]
theorem checked35223 : checkPrefixCuts (2^48) 4620681217 10 Manual.Count131072.C035223.packed 64 cuts35223 = true := by
 decide +kernel
def pointBounds35223 : List (Nat × Nat × Nat) := [(4620777472,107263743416683,107264127949360)]
theorem point_links_checked35223 : (cuts35223.take 1).map (fun c => (4620681217-1+2*2^10*c.k,107263480443688+c.lower,107263864976197+c.upper)) = pointBounds35223 := by
 decide +kernel
def cuts35224 : List PrefixCut := [⟨54,302802824,302803005⟩,
⟨64,358964604,358964822⟩]
theorem checked35224 : checkPrefixCuts (2^48) 4620812289 10 Manual.Count131072.C035224.packed 64 cuts35224 = true := by
 decide +kernel
def pointBounds35224 : List (Nat × Nat × Nat) := [(4620922880,107264139358263,107264523891181)]
theorem point_links_checked35224 : (cuts35224.take 1).map (fun c => (4620812289-1+2*2^10*c.k,107263836555439+c.lower,107264221088176+c.upper)) = pointBounds35224 := by
 decide +kernel
def cuts35225 : List PrefixCut := [⟨61,340863758,340863968⟩,
⟨64,358893466,358893687⟩]
theorem checked35225 : checkPrefixCuts (2^48) 4620943361 10 Manual.Count131072.C035225.packed 64 cuts35225 = true := by
 decide +kernel
def pointBounds35225 : List (Nat × Nat × Nat) := [(4621068288,107264536383801,107264920916966)]
theorem point_links_checked35225 : (cuts35225.take 1).map (fun c => (4620943361-1+2*2^10*c.k,107264195520043+c.lower,107264580052998+c.upper)) = pointBounds35225 := by
 decide +kernel
def cuts35226 : List PrefixCut := [⟨64,359553343,359553557⟩]
theorem checked35226 : checkPrefixCuts (2^48) 4621074433 10 Manual.Count131072.C035226.packed 64 cuts35226 = true := by
 decide +kernel
def cuts35227 : List PrefixCut := [⟨4,22049186,22049200⟩,
⟨64,355705874,355706095⟩]
theorem checked35227 : checkPrefixCuts (2^48) 4621205505 10 Manual.Count131072.C035227.packed 64 cuts35227 = true := by
 decide +kernel
def pointBounds35227 : List (Nat × Nat × Nat) := [(4621213696,107264936016038,107265320549442)]
theorem point_links_checked35227 : (cuts35227.take 1).map (fun c => (4621205505-1+2*2^10*c.k,107264913966852+c.lower,107265298500242+c.upper)) = pointBounds35227 := by
 decide +kernel
def cuts35228 : List PrefixCut := [⟨11,59202120,59202156⟩,
⟨64,358375665,358375883⟩]
theorem checked35228 : checkPrefixCuts (2^48) 4621336577 10 Manual.Count131072.C035228.packed 64 cuts35228 = true := by
 decide +kernel
def pointBounds35228 : List (Nat × Nat × Nat) := [(4621359104,107265328874846,107265713408493)]
theorem point_links_checked35228 : (cuts35228.take 1).map (fun c => (4621336577-1+2*2^10*c.k,107265269672726+c.lower,107265654206337+c.upper)) = pointBounds35228 := by
 decide +kernel
def cuts35229 : List PrefixCut := [⟨18,102260678,102260741⟩,
⟨64,361898025,361898247⟩]
theorem checked35229 : checkPrefixCuts (2^48) 4621467649 10 Manual.Count131072.C035229.packed 64 cuts35229 = true := by
 decide +kernel
def pointBounds35229 : List (Nat × Nat × Nat) := [(4621504512,107265730309069,107266114842961)]
theorem point_links_checked35229 : (cuts35229.take 1).map (fun c => (4621467649-1+2*2^10*c.k,107265628048391+c.lower,107266012582220+c.upper)) = pointBounds35229 := by
 decide +kernel
def cuts35230 : List PrefixCut := [⟨25,138678154,138678243⟩,
⟨64,356832795,356833024⟩]
theorem checked35230 : checkPrefixCuts (2^48) 4621598721 10 Manual.Count131072.C035230.packed 64 cuts35230 = true := by
 decide +kernel
def pointBounds35230 : List (Nat × Nat × Nat) := [(4621649920,107266128624570,107266513158710)]
theorem point_links_checked35230 : (cuts35230.take 1).map (fun c => (4621598721-1+2*2^10*c.k,107265989946416+c.lower,107266374480467+c.upper)) = pointBounds35230 := by
 decide +kernel
def cuts35231 : List PrefixCut := [⟨32,177712246,177712356⟩,
⟨64,357248985,357249206⟩]
theorem checked35231 : checkPrefixCuts (2^48) 4621729793 10 Manual.Count131072.C035231.packed 64 cuts35231 = true := by
 decide +kernel
def pointBounds35231 : List (Nat × Nat × Nat) := [(4621795328,107266524491457,107266909025847)]
theorem point_links_checked35231 : (cuts35231.take 1).map (fun c => (4621729793-1+2*2^10*c.k,107266346779211+c.lower,107266731313491+c.upper)) = pointBounds35231 := by
 decide +kernel
def cuts35232 : List PrefixCut := [⟨39,216195874,216196011⟩,
⟨64,356629844,356630069⟩]
theorem checked35232 : checkPrefixCuts (2^48) 4621860865 10 Manual.Count131072.C035232.packed 64 cuts35232 = true := by
 decide +kernel
def pointBounds35232 : List (Nat × Nat × Nat) := [(4621940736,107266920224070,107267304758708)]
theorem point_links_checked35232 : (cuts35232.take 1).map (fun c => (4621860865-1+2*2^10*c.k,107266704028196+c.lower,107267088562697+c.upper)) = pointBounds35232 := by
 decide +kernel
def cuts35233 : List PrefixCut := [⟨46,259609982,259610142⟩,
⟨64,358081337,358081561⟩]
theorem checked35233 : checkPrefixCuts (2^48) 4621991937 10 Manual.Count131072.C035233.packed 64 cuts35233 = true := by
 decide +kernel
def pointBounds35233 : List (Nat × Nat × Nat) := [(4622086144,107267320268022,107267704802908)]
theorem point_links_checked35233 : (cuts35233.take 1).map (fun c => (4621991937-1+2*2^10*c.k,107267060658040+c.lower,107267445192766+c.upper)) = pointBounds35233 := by
 decide +kernel
def cuts35234 : List PrefixCut := [⟨53,296079254,296079442⟩,
⟨64,357279468,357279695⟩]
theorem checked35234 : checkPrefixCuts (2^48) 4622123009 10 Manual.Count131072.C035234.packed 64 cuts35234 = true := by
 decide +kernel
def pointBounds35234 : List (Nat × Nat × Nat) := [(4622231552,107267714818631,107268099353769)]
theorem point_links_checked35234 : (cuts35234.take 1).map (fun c => (4622123009-1+2*2^10*c.k,107267418739377+c.lower,107267803274327+c.upper)) = pointBounds35234 := by
 decide +kernel
def cuts35235 : List PrefixCut := [⟨60,338757673,338757885⟩,
⟨64,359948757,359948982⟩]
theorem checked35235 : checkPrefixCuts (2^48) 4622254081 10 Manual.Count131072.C035235.packed 64 cuts35235 = true := by
 decide +kernel
def pointBounds35235 : List (Nat × Nat × Nat) := [(4622376960,107268114776518,107268499311907)]
theorem point_links_checked35235 : (cuts35235.take 1).map (fun c => (4622254081-1+2*2^10*c.k,107267776018845+c.lower,107268160554022+c.upper)) = pointBounds35235 := by
 decide +kernel
def cuts35236 : List PrefixCut := [⟨64,359816768,359816993⟩]
theorem checked35236 : checkPrefixCuts (2^48) 4622385153 10 Manual.Count131072.C035236.packed 64 cuts35236 = true := by
 decide +kernel
def cuts35237 : List PrefixCut := [⟨3,16136406,16136415⟩,
⟨64,361207026,361207241⟩]
theorem checked35237 : checkPrefixCuts (2^48) 4622516225 10 Manual.Count131072.C035237.packed 64 cuts35237 = true := by
 decide +kernel
def pointBounds35237 : List (Nat × Nat × Nat) := [(4622522368,107268511920776,107268896456412)]
theorem point_links_checked35237 : (cuts35237.take 1).map (fun c => (4622516225-1+2*2^10*c.k,107268495784370+c.lower,107268880319997+c.upper)) = pointBounds35237 := by
 decide +kernel
def cuts35238 : List PrefixCut := [⟨10,57419529,57419563⟩,
⟨64,360953228,360953449⟩]
theorem checked35238 : checkPrefixCuts (2^48) 4622647297 10 Manual.Count131072.C035238.packed 64 cuts35238 = true := by
 decide +kernel
def pointBounds35238 : List (Nat × Nat × Nat) := [(4622667776,107268914410925,107269298946801)]
theorem point_links_checked35238 : (cuts35238.take 1).map (fun c => (4622647297-1+2*2^10*c.k,107268856991396+c.lower,107269241527238+c.upper)) = pointBounds35238 := by
 decide +kernel
def cuts35239 : List PrefixCut := [⟨17,93463773,93463834⟩,
⟨64,352479567,352479791⟩]
theorem checked35239 : checkPrefixCuts (2^48) 4622778369 10 Manual.Count131072.C035239.packed 64 cuts35239 = true := by
 decide +kernel
def pointBounds35239 : List (Nat × Nat × Nat) := [(4622813184,107269311408397,107269695944521)]
theorem point_links_checked35239 : (cuts35239.take 1).map (fun c => (4622778369-1+2*2^10*c.k,107269217944624+c.lower,107269602480687+c.upper)) = pointBounds35239 := by
 decide +kernel
def cuts35240 : List PrefixCut := [⟨24,135838079,135838164⟩,
⟨64,361419842,361420066⟩]
theorem checked35240 : checkPrefixCuts (2^48) 4622909441 10 Manual.Count131072.C035240.packed 64 cuts35240 = true := by
 decide +kernel
def pointBounds35240 : List (Nat × Nat × Nat) := [(4622958592,107269706262270,107270090798642)]
theorem point_links_checked35240 : (cuts35240.take 1).map (fun c => (4622909441-1+2*2^10*c.k,107269570424191+c.lower,107269954960478+c.upper)) = pointBounds35240 := by
 decide +kernel
def cuts35241 : List PrefixCut := [⟨31,175530901,175531009⟩,
⟨64,356295360,356295584⟩]
theorem checked35241 : checkPrefixCuts (2^48) 4623040513 10 Manual.Count131072.C035241.packed 64 cuts35241 = true := by
 decide +kernel
def pointBounds35241 : List (Nat × Nat × Nat) := [(4623104000,107270107374934,107270491911553)]
theorem point_links_checked35241 : (cuts35241.take 1).map (fun c => (4623040513-1+2*2^10*c.k,107269931844033+c.lower,107270316380544+c.upper)) = pointBounds35241 := by
 decide +kernel
def cuts35242 : List PrefixCut := [⟨38,210776939,210777069⟩,
⟨64,357989930,357990148⟩]
theorem checked35242 : checkPrefixCuts (2^48) 4623171585 10 Manual.Count131072.C035242.packed 64 cuts35242 = true := by
 decide +kernel
def pointBounds35242 : List (Nat × Nat × Nat) := [(4623249408,107270498916332,107270883453197)]
theorem point_links_checked35242 : (cuts35242.take 1).map (fun c => (4623171585-1+2*2^10*c.k,107270288139393+c.lower,107270672676128+c.upper)) = pointBounds35242 := by
 decide +kernel
def cuts35243 : List PrefixCut := [⟨45,253630962,253631120⟩,
⟨64,359927977,359928198⟩]
theorem checked35243 : checkPrefixCuts (2^48) 4623302657 10 Manual.Count131072.C035243.packed 64 cuts35243 = true := by
 decide +kernel
def pointBounds35243 : List (Nat × Nat × Nat) := [(4623394816,107270899760285,107271284297396)]
theorem point_links_checked35243 : (cuts35243.take 1).map (fun c => (4623302657-1+2*2^10*c.k,107270646129323+c.lower,107271030666276+c.upper)) = pointBounds35243 := by
 decide +kernel
def cuts35244 : List PrefixCut := [⟨52,286985272,286985457⟩,
⟨64,354743029,354743256⟩]
theorem checked35244 : checkPrefixCuts (2^48) 4623433729 10 Manual.Count131072.C035244.packed 64 cuts35244 = true := by
 decide +kernel
def pointBounds35244 : List (Nat × Nat × Nat) := [(4623540224,107271293042572,107271677579931)]
theorem point_links_checked35244 : (cuts35244.take 1).map (fun c => (4623433729-1+2*2^10*c.k,107271006057300+c.lower,107271390594474+c.upper)) = pointBounds35244 := by
 decide +kernel
def cuts35245 : List PrefixCut := [⟨59,335313450,335313659⟩,
⟨64,363438471,363438697⟩]
theorem checked35245 : checkPrefixCuts (2^48) 4623564801 10 Manual.Count131072.C035245.packed 64 cuts35245 = true := by
 decide +kernel
def pointBounds35245 : List (Nat × Nat × Nat) := [(4623685632,107271696113779,107272080651389)]
theorem point_links_checked35245 : (cuts35245.take 1).map (fun c => (4623564801-1+2*2^10*c.k,107271360800329+c.lower,107271745337730+c.upper)) = pointBounds35245 := by
 decide +kernel
def cuts35246 : List PrefixCut := [⟨64,360688719,360688945⟩]
theorem checked35246 : checkPrefixCuts (2^48) 4623695873 10 Manual.Count131072.C035246.packed 64 cuts35246 = true := by
 decide +kernel
def cuts35247 : List PrefixCut := [⟨2,11505347,11505354⟩,
⟨64,357452174,357452396⟩]
theorem checked35247 : checkPrefixCuts (2^48) 4623826945 10 Manual.Count131072.C035247.packed 64 cuts35247 = true := by
 decide +kernel
def pointBounds35247 : List (Nat × Nat × Nat) := [(4623831040,107272096432866,107272480970726)]
theorem point_links_checked35247 : (cuts35247.take 1).map (fun c => (4623826945-1+2*2^10*c.k,107272084927519+c.lower,107272469465372+c.upper)) = pointBounds35247 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000163
