import PlattAssemblyKernel
import PlattCertificates.Count131072.C073296
import PlattCertificates.Count131072.C073297
import PlattCertificates.Count131072.C073298
import PlattCertificates.Count131072.C073299
import PlattCertificates.Count131072.C073300
import PlattCertificates.Count131072.C073301
import PlattCertificates.Count131072.C073302
import PlattCertificates.Count131072.C073303
import PlattCertificates.Count131072.C073304
import PlattCertificates.Count131072.C073305
import PlattCertificates.Count131072.C073306
import PlattCertificates.Count131072.C073307
import PlattCertificates.Count131072.C073308
import PlattCertificates.Count131072.C073309
import PlattCertificates.Count131072.C073310
import PlattCertificates.Count131072.C073311
import PlattCertificates.Count131072.C073312
import PlattCertificates.Count131072.C073313
import PlattCertificates.Count131072.C073314
import PlattCertificates.Count131072.C073315
import PlattCertificates.Count131072.C073316
import PlattCertificates.Count131072.C073317
import PlattCertificates.Count131072.C073318
import PlattCertificates.Count131072.C073319
import PlattCertificates.Count131072.C073320
import PlattCertificates.Count131072.C073321
import PlattCertificates.Count131072.C073322
import PlattCertificates.Count131072.C073323
import PlattCertificates.Count131072.C073324
import PlattCertificates.Count131072.C073325
import PlattCertificates.Count131072.C073326
import PlattCertificates.Count131072.C073327
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73296 : List PrefixCut := [⟨42,108389914,108389977⟩,
⟨64,165937801,165937897⟩]
theorem checked73296 : checkPrefixCuts (2^48) 9610985473 10 Manual.Count131072.C073296.packed 64 cuts73296 = true := by
 decide +kernel
def pointBounds73296 : List (Nat × Nat × Nat) := [(9611071488,116377616541224,116378006380561)]
theorem point_links_checked73296 : (cuts73296.take 1).map (fun c => (9610985473-1+2*2^10*c.k,116377508151310+c.lower,116377897990584+c.upper)) = pointBounds73296 := by
 decide +kernel
def cuts73297 : List PrefixCut := [⟨64,165584118,165584212⟩]
theorem checked73297 : checkPrefixCuts (2^48) 9611116545 10 Manual.Count131072.C073297.packed 64 cuts73297 = true := by
 decide +kernel
def cuts73298 : List PrefixCut := [⟨61,159607603,159607695⟩,
⟨64,167807571,167807669⟩]
theorem checked73298 : checkPrefixCuts (2^48) 9611247617 10 Manual.Count131072.C073298.packed 64 cuts73298 = true := by
 decide +kernel
def pointBounds73298 : List (Nat × Nat × Nat) := [(9611372544,116377999280832,116378389120388)]
theorem point_links_checked73298 : (cuts73298.take 1).map (fun c => (9611247617-1+2*2^10*c.k,116377839673229+c.lower,116378229512693+c.upper)) = pointBounds73298 := by
 decide +kernel
def cuts73299 : List PrefixCut := [⟨64,166897440,166897535⟩]
theorem checked73299 : checkPrefixCuts (2^48) 9611378689 10 Manual.Count131072.C073299.packed 64 cuts73299 = true := by
 decide +kernel
def cuts73300 : List PrefixCut := [⟨64,165138066,165138173⟩]
theorem checked73300 : checkPrefixCuts (2^48) 9611509761 10 Manual.Count131072.C073300.packed 64 cuts73300 = true := by
 decide +kernel
def cuts73301 : List PrefixCut := [⟨16,41291483,41291510⟩,
⟨64,166980733,166980833⟩]
theorem checked73301 : checkPrefixCuts (2^48) 9611640833 10 Manual.Count131072.C073301.packed 64 cuts73301 = true := by
 decide +kernel
def pointBounds73301 : List (Nat × Nat × Nat) := [(9611673600,116378380807789,116378770647580)]
theorem point_links_checked73301 : (cuts73301.take 1).map (fun c => (9611640833-1+2*2^10*c.k,116378339516306+c.lower,116378729356070+c.upper)) = pointBounds73301 := by
 decide +kernel
def cuts73302 : List PrefixCut := [⟨64,167154171,167154273⟩]
theorem checked73302 : checkPrefixCuts (2^48) 9611771905 10 Manual.Count131072.C073302.packed 64 cuts73302 = true := by
 decide +kernel
def cuts73303 : List PrefixCut := [⟨35,91190016,91190069⟩,
⟨64,166624786,166624877⟩]
theorem checked73303 : checkPrefixCuts (2^48) 9611902977 10 Manual.Count131072.C073303.packed 64 cuts73303 = true := by
 decide +kernel
def pointBounds73303 : List (Nat × Nat × Nat) := [(9611974656,116378764841226,116379154681245)]
theorem point_links_checked73303 : (cuts73303.take 1).map (fun c => (9611902977-1+2*2^10*c.k,116378673651210+c.lower,116379063491176+c.upper)) = pointBounds73303 := by
 decide +kernel
def cuts73304 : List PrefixCut := [⟨64,167032470,167032571⟩]
theorem checked73304 : checkPrefixCuts (2^48) 9612034049 10 Manual.Count131072.C073304.packed 64 cuts73304 = true := by
 decide +kernel
def cuts73305 : List PrefixCut := [⟨54,142813319,142813404⟩,
⟨64,168025833,168025932⟩]
theorem checked73305 : checkPrefixCuts (2^48) 9612165121 10 Manual.Count131072.C073305.packed 64 cuts73305 = true := by
 decide +kernel
def pointBounds73305 : List (Nat × Nat × Nat) := [(9612275712,116379150121785,116379539962028)]
theorem point_links_checked73305 : (cuts73305.take 1).map (fun c => (9612165121-1+2*2^10*c.k,116379007308466+c.lower,116379397148624+c.upper)) = pointBounds73305 := by
 decide +kernel
def cuts73306 : List PrefixCut := [⟨64,167262189,167262289⟩]
theorem checked73306 : checkPrefixCuts (2^48) 9612296193 10 Manual.Count131072.C073306.packed 64 cuts73306 = true := by
 decide +kernel
def cuts73307 : List PrefixCut := [⟨64,167084198,167084299⟩]
theorem checked73307 : checkPrefixCuts (2^48) 9612427265 10 Manual.Count131072.C073307.packed 64 cuts73307 = true := by
 decide +kernel
def cuts73308 : List PrefixCut := [⟨9,23513419,23513434⟩,
⟨64,167696851,167696945⟩]
theorem checked73308 : checkPrefixCuts (2^48) 9612558337 10 Manual.Count131072.C073308.packed 64 cuts73308 = true := by
 decide +kernel
def pointBounds73308 : List (Nat × Nat × Nat) := [(9612576768,116379533194105,116379923034578)]
theorem point_links_checked73308 : (cuts73308.take 1).map (fun c => (9612558337-1+2*2^10*c.k,116379509680686+c.lower,116379899521144+c.upper)) = pointBounds73308 := by
 decide +kernel
def cuts73309 : List PrefixCut := [⟨64,168250909,168251003⟩]
theorem checked73309 : checkPrefixCuts (2^48) 9612689409 10 Manual.Count131072.C073309.packed 64 cuts73309 = true := by
 decide +kernel
def cuts73310 : List PrefixCut := [⟨28,72939245,72939287⟩,
⟨64,167516588,167516688⟩]
theorem checked73310 : checkPrefixCuts (2^48) 9612820481 10 Manual.Count131072.C073310.packed 64 cuts73310 = true := by
 decide +kernel
def pointBounds73310 : List (Nat × Nat × Nat) := [(9612877824,116379918567691,116380308408379)]
theorem point_links_checked73310 : (cuts73310.take 1).map (fun c => (9612820481-1+2*2^10*c.k,116379845628446+c.lower,116380235469092+c.upper)) = pointBounds73310 := by
 decide +kernel
def cuts73311 : List PrefixCut := [⟨64,167572865,167572966⟩]
theorem checked73311 : checkPrefixCuts (2^48) 9612951553 10 Manual.Count131072.C073311.packed 64 cuts73311 = true := by
 decide +kernel
def cuts73312 : List PrefixCut := [⟨47,123533382,123533460⟩,
⟨64,168595382,168595487⟩]
theorem checked73312 : checkPrefixCuts (2^48) 9613082625 10 Manual.Count131072.C073312.packed 64 cuts73312 = true := by
 decide +kernel
def pointBounds73312 : List (Nat × Nat × Nat) := [(9613178880,116380304251281,116380694092206)]
theorem point_links_checked73312 : (cuts73312.take 1).map (fun c => (9613082625-1+2*2^10*c.k,116380180717899+c.lower,116380570558746+c.upper)) = pointBounds73312 := by
 decide +kernel
def cuts73313 : List PrefixCut := [⟨64,169120125,169120225⟩]
theorem checked73313 : checkPrefixCuts (2^48) 9613213697 10 Manual.Count131072.C073313.packed 64 cuts73313 = true := by
 decide +kernel
def cuts73314 : List PrefixCut := [⟨64,164755184,164755283⟩]
theorem checked73314 : checkPrefixCuts (2^48) 9613344769 10 Manual.Count131072.C073314.packed 64 cuts73314 = true := by
 decide +kernel
def cuts73315 : List PrefixCut := [⟨2,5240975,5240979⟩,
⟨64,165484920,165485019⟩]
theorem checked73315 : checkPrefixCuts (2^48) 9613475841 10 Manual.Count131072.C073315.packed 64 cuts73315 = true := by
 decide +kernel
def pointBounds73315 : List (Nat × Nat × Nat) := [(9613479936,116380688429565,116381078270720)]
theorem point_links_checked73315 : (cuts73315.take 1).map (fun c => (9613475841-1+2*2^10*c.k,116380683188590+c.lower,116381073029741+c.upper)) = pointBounds73315 := by
 decide +kernel
def cuts73316 : List PrefixCut := [⟨64,165687618,165687714⟩]
theorem checked73316 : checkPrefixCuts (2^48) 9613606913 10 Manual.Count131072.C073316.packed 64 cuts73316 = true := by
 decide +kernel
def cuts73317 : List PrefixCut := [⟨21,52613174,52613203⟩,
⟨64,162845358,162845455⟩]
theorem checked73317 : checkPrefixCuts (2^48) 9613737985 10 Manual.Count131072.C073317.packed 64 cuts73317 = true := by
 decide +kernel
def pointBounds73317 : List (Nat × Nat × Nat) := [(9613780992,116381066974302,116381456815677)]
theorem point_links_checked73317 : (cuts73317.take 1).map (fun c => (9613737985-1+2*2^10*c.k,116381014361128+c.lower,116381404202474+c.upper)) = pointBounds73317 := by
 decide +kernel
def cuts73318 : List PrefixCut := [⟨64,168288806,168288909⟩]
theorem checked73318 : checkPrefixCuts (2^48) 9613869057 10 Manual.Count131072.C073318.packed 64 cuts73318 = true := by
 decide +kernel
def cuts73319 : List PrefixCut := [⟨40,107243407,107243476⟩,
⟨64,167876656,167876760⟩]
theorem checked73319 : checkPrefixCuts (2^48) 9614000129 10 Manual.Count131072.C073319.packed 64 cuts73319 = true := by
 decide +kernel
def pointBounds73319 : List (Nat × Nat × Nat) := [(9614082048,116381452738699,116381842580314)]
theorem point_links_checked73319 : (cuts73319.take 1).map (fun c => (9614000129-1+2*2^10*c.k,116381345495292+c.lower,116381735336838+c.upper)) = pointBounds73319 := by
 decide +kernel
def cuts73320 : List PrefixCut := [⟨64,170421442,170421543⟩]
theorem checked73320 : checkPrefixCuts (2^48) 9614131201 10 Manual.Count131072.C073320.packed 64 cuts73320 = true := by
 decide +kernel
def cuts73321 : List PrefixCut := [⟨59,152853245,152853337⟩,
⟨64,165705595,165705695⟩]
theorem checked73321 : checkPrefixCuts (2^48) 9614262273 10 Manual.Count131072.C073321.packed 64 cuts73321 = true := by
 decide +kernel
def pointBounds73321 : List (Nat × Nat × Nat) := [(9614383104,116381836646635,116382226488478)]
theorem point_links_checked73321 : (cuts73321.take 1).map (fun c => (9614262273-1+2*2^10*c.k,116381683793390+c.lower,116382073635141+c.upper)) = pointBounds73321 := by
 decide +kernel
def cuts73322 : List PrefixCut := [⟨64,165878981,165879080⟩]
theorem checked73322 : checkPrefixCuts (2^48) 9614393345 10 Manual.Count131072.C073322.packed 64 cuts73322 = true := by
 decide +kernel
def cuts73323 : List PrefixCut := [⟨64,165115559,165115659⟩]
theorem checked73323 : checkPrefixCuts (2^48) 9614524417 10 Manual.Count131072.C073323.packed 64 cuts73323 = true := by
 decide +kernel
def cuts73324 : List PrefixCut := [⟨14,36916486,36916506⟩,
⟨64,168889836,168889929⟩]
theorem checked73324 : checkPrefixCuts (2^48) 9614655489 10 Manual.Count131072.C073324.packed 64 cuts73324 = true := by
 decide +kernel
def pointBounds73324 : List (Nat × Nat × Nat) := [(9614684160,116382217410011,116382607252081)]
theorem point_links_checked73324 : (cuts73324.take 1).map (fun c => (9614655489-1+2*2^10*c.k,116382180493525+c.lower,116382570335575+c.upper)) = pointBounds73324 := by
 decide +kernel
def cuts73325 : List PrefixCut := [⟨64,168038563,168038662⟩]
theorem checked73325 : checkPrefixCuts (2^48) 9614786561 10 Manual.Count131072.C073325.packed 64 cuts73325 = true := by
 decide +kernel
def cuts73326 : List PrefixCut := [⟨33,85160127,85160174⟩,
⟨64,166865279,166865374⟩]
theorem checked73326 : checkPrefixCuts (2^48) 9614917633 10 Manual.Count131072.C073326.packed 64 cuts73326 = true := by
 decide +kernel
def pointBounds73326 : List (Nat × Nat × Nat) := [(9614985216,116382602582051,116382992424340)]
theorem point_links_checked73326 : (cuts73326.take 1).map (fun c => (9614917633-1+2*2^10*c.k,116382517421924+c.lower,116382907264166+c.upper)) = pointBounds73326 := by
 decide +kernel
def cuts73327 : List PrefixCut := [⟨64,168560904,168561007⟩]
theorem checked73327 : checkPrefixCuts (2^48) 9615048705 10 Manual.Count131072.C073327.packed 64 cuts73327 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000103
