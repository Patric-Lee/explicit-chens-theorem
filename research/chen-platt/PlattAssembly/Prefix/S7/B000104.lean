import PlattAssemblyKernel
import PlattCertificates.Count131072.C063328
import PlattCertificates.Count131072.C063329
import PlattCertificates.Count131072.C063330
import PlattCertificates.Count131072.C063331
import PlattCertificates.Count131072.C063332
import PlattCertificates.Count131072.C063333
import PlattCertificates.Count131072.C063334
import PlattCertificates.Count131072.C063335
import PlattCertificates.Count131072.C063336
import PlattCertificates.Count131072.C063337
import PlattCertificates.Count131072.C063338
import PlattCertificates.Count131072.C063339
import PlattCertificates.Count131072.C063340
import PlattCertificates.Count131072.C063341
import PlattCertificates.Count131072.C063342
import PlattCertificates.Count131072.C063343
import PlattCertificates.Count131072.C063344
import PlattCertificates.Count131072.C063345
import PlattCertificates.Count131072.C063346
import PlattCertificates.Count131072.C063347
import PlattCertificates.Count131072.C063348
import PlattCertificates.Count131072.C063349
import PlattCertificates.Count131072.C063350
import PlattCertificates.Count131072.C063351
import PlattCertificates.Count131072.C063352
import PlattCertificates.Count131072.C063353
import PlattCertificates.Count131072.C063354
import PlattCertificates.Count131072.C063355
import PlattCertificates.Count131072.C063356
import PlattCertificates.Count131072.C063357
import PlattCertificates.Count131072.C063358
import PlattCertificates.Count131072.C063359
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63328 : List PrefixCut := [⟨64,193942380,193942489⟩]
theorem checked63328 : checkPrefixCuts (2^48) 8304459777 10 Manual.Count131072.C063328.packed 64 cuts63328 = true := by
 decide +kernel
def cuts63329 : List PrefixCut := [⟨55,166485666,166485763⟩,
⟨64,192651365,192651477⟩]
theorem checked63329 : checkPrefixCuts (2^48) 8304590849 10 Manual.Count131072.C063329.packed 64 cuts63329 = true := by
 decide +kernel
def pointBounds63329 : List (Nat × Nat × Nat) := [(8304703488,114582974347811,114583363136989)]
theorem point_links_checked63329 : (cuts63329.take 1).map (fun c => (8304590849-1+2*2^10*c.k,114582807862145+c.lower,114583196651226+c.upper)) = pointBounds63329 := by
 decide +kernel
def cuts63330 : List PrefixCut := [⟨64,197427248,197427359⟩]
theorem checked63330 : checkPrefixCuts (2^48) 8304721921 10 Manual.Count131072.C063330.packed 64 cuts63330 = true := by
 decide +kernel
def cuts63331 : List PrefixCut := [⟨54,164243516,164243608⟩,
⟨64,194882180,194882290⟩]
theorem checked63331 : checkPrefixCuts (2^48) 8304852993 10 Manual.Count131072.C063331.packed 64 cuts63331 = true := by
 decide +kernel
def pointBounds63331 : List (Nat × Nat × Nat) := [(8304963584,114583362184274,114583750973670)]
theorem point_links_checked63331 : (cuts63331.take 1).map (fun c => (8304852993-1+2*2^10*c.k,114583197940758+c.lower,114583586730062+c.upper)) = pointBounds63331 := by
 decide +kernel
def cuts63332 : List PrefixCut := [⟨64,195624733,195624845⟩]
theorem checked63332 : checkPrefixCuts (2^48) 8304984065 10 Manual.Count131072.C063332.packed 64 cuts63332 = true := by
 decide +kernel
def cuts63333 : List PrefixCut := [⟨53,163628292,163628387⟩,
⟨64,197587337,197587453⟩]
theorem checked63333 : checkPrefixCuts (2^48) 8305115137 10 Manual.Count131072.C063333.packed 64 cuts63333 = true := by
 decide +kernel
def pointBounds63333 : List (Nat × Nat × Nat) := [(8305223680,114583752075963,114584140865584)]
theorem point_links_checked63333 : (cuts63333.take 1).map (fun c => (8305115137-1+2*2^10*c.k,114583588447671+c.lower,114583977237197+c.upper)) = pointBounds63333 := by
 decide +kernel
def cuts63334 : List PrefixCut := [⟨64,194262935,194263043⟩]
theorem checked63334 : checkPrefixCuts (2^48) 8305246209 10 Manual.Count131072.C063334.packed 64 cuts63334 = true := by
 decide +kernel
def cuts63335 : List PrefixCut := [⟨52,156946736,156946828⟩,
⟨64,194124283,194124395⟩]
theorem checked63335 : checkPrefixCuts (2^48) 8305377281 10 Manual.Count131072.C063335.packed 64 cuts63335 = true := by
 decide +kernel
def pointBounds63335 : List (Nat × Nat × Nat) := [(8305483776,114584137244679,114584526034521)]
theorem point_links_checked63335 : (cuts63335.take 1).map (fun c => (8305377281-1+2*2^10*c.k,114583980297943+c.lower,114584369087693+c.upper)) = pointBounds63335 := by
 decide +kernel
def cuts63336 : List PrefixCut := [⟨64,193409556,193409668⟩]
theorem checked63336 : checkPrefixCuts (2^48) 8305508353 10 Manual.Count131072.C063336.packed 64 cuts63336 = true := by
 decide +kernel
def cuts63337 : List PrefixCut := [⟨51,157179034,157179124⟩,
⟨64,196388759,196388873⟩]
theorem checked63337 : checkPrefixCuts (2^48) 8305639425 10 Manual.Count131072.C063337.packed 64 cuts63337 = true := by
 decide +kernel
def pointBounds63337 : List (Nat × Nat × Nat) := [(8305743872,114584525010816,114584913800880)]
theorem point_links_checked63337 : (cuts63337.take 1).map (fun c => (8305639425-1+2*2^10*c.k,114584367831782+c.lower,114584756621756+c.upper)) = pointBounds63337 := by
 decide +kernel
def cuts63338 : List PrefixCut := [⟨64,194928439,194928553⟩]
theorem checked63338 : checkPrefixCuts (2^48) 8305770497 10 Manual.Count131072.C063338.packed 64 cuts63338 = true := by
 decide +kernel
def cuts63339 : List PrefixCut := [⟨50,151785841,151785930⟩,
⟨64,193400387,193400499⟩]
theorem checked63339 : checkPrefixCuts (2^48) 8305901569 10 Manual.Count131072.C063339.packed 64 cuts63339 = true := by
 decide +kernel
def pointBounds63339 : List (Nat × Nat × Nat) := [(8306003968,114584910934821,114585299725112)]
theorem point_links_checked63339 : (cuts63339.take 1).map (fun c => (8305901569-1+2*2^10*c.k,114584759148980+c.lower,114585147939182+c.upper)) = pointBounds63339 := by
 decide +kernel
def cuts63340 : List PrefixCut := [⟨64,193668425,193668537⟩]
theorem checked63340 : checkPrefixCuts (2^48) 8306032641 10 Manual.Count131072.C063340.packed 64 cuts63340 = true := by
 decide +kernel
def cuts63341 : List PrefixCut := [⟨49,148087359,148087444⟩,
⟨64,192953746,192953857⟩]
theorem checked63341 : checkPrefixCuts (2^48) 8306163713 10 Manual.Count131072.C063341.packed 64 cuts63341 = true := by
 decide +kernel
def pointBounds63341 : List (Nat × Nat × Nat) := [(8306264064,114585294305151,114585683095662)]
theorem point_links_checked63341 : (cuts63341.take 1).map (fun c => (8306163713-1+2*2^10*c.k,114585146217792+c.lower,114585535008218+c.upper)) = pointBounds63341 := by
 decide +kernel
def cuts63342 : List PrefixCut := [⟨64,193628448,193628553⟩]
theorem checked63342 : checkPrefixCuts (2^48) 8306294785 10 Manual.Count131072.C063342.packed 64 cuts63342 = true := by
 decide +kernel
def cuts63343 : List PrefixCut := [⟨48,145710669,145710754⟩,
⟨64,194336986,194337100⟩]
theorem checked63343 : checkPrefixCuts (2^48) 8306425857 10 Manual.Count131072.C063343.packed 64 cuts63343 = true := by
 decide +kernel
def pointBounds63343 : List (Nat × Nat × Nat) := [(8306524160,114585678510655,114586067301382)]
theorem point_links_checked63343 : (cuts63343.take 1).map (fun c => (8306425857-1+2*2^10*c.k,114585532799986+c.lower,114585921590628+c.upper)) = pointBounds63343 := by
 decide +kernel
def cuts63344 : List PrefixCut := [⟨64,191656972,191657085⟩]
theorem checked63344 : checkPrefixCuts (2^48) 8306556929 10 Manual.Count131072.C063344.packed 64 cuts63344 = true := by
 decide +kernel
def cuts63345 : List PrefixCut := [⟨47,142825861,142825942⟩,
⟨64,194635828,194635939⟩]
theorem checked63345 : checkPrefixCuts (2^48) 8306688001 10 Manual.Count131072.C063345.packed 64 cuts63345 = true := by
 decide +kernel
def pointBounds63345 : List (Nat × Nat × Nat) := [(8306784256,114586061619805,114586450410755)]
theorem point_links_checked63345 : (cuts63345.take 1).map (fun c => (8306688001-1+2*2^10*c.k,114585918793944+c.lower,114586307584813+c.upper)) = pointBounds63345 := by
 decide +kernel
def cuts63346 : List PrefixCut := [⟨64,195344330,195344437⟩]
theorem checked63346 : checkPrefixCuts (2^48) 8306819073 10 Manual.Count131072.C063346.packed 64 cuts63346 = true := by
 decide +kernel
def cuts63347 : List PrefixCut := [⟨46,139094121,139094198⟩,
⟨64,192528882,192528987⟩]
theorem checked63347 : checkPrefixCuts (2^48) 8306950145 10 Manual.Count131072.C063347.packed 64 cuts63347 = true := by
 decide +kernel
def pointBounds63347 : List (Nat × Nat × Nat) := [(8307044352,114586447868223,114586836659387)]
theorem point_links_checked63347 : (cuts63347.take 1).map (fun c => (8306950145-1+2*2^10*c.k,114586308774102+c.lower,114586697565189+c.upper)) = pointBounds63347 := by
 decide +kernel
def cuts63348 : List PrefixCut := [⟨64,193000203,193000312⟩]
theorem checked63348 : checkPrefixCuts (2^48) 8307081217 10 Manual.Count131072.C063348.packed 64 cuts63348 = true := by
 decide +kernel
def cuts63349 : List PrefixCut := [⟨45,137565012,137565090⟩,
⟨64,194657428,194657540⟩]
theorem checked63349 : checkPrefixCuts (2^48) 8307212289 10 Manual.Count131072.C063349.packed 64 cuts63349 = true := by
 decide +kernel
def pointBounds63349 : List (Nat × Nat × Nat) := [(8307304448,114586831868199,114587220659578)]
theorem point_links_checked63349 : (cuts63349.take 1).map (fun c => (8307212289-1+2*2^10*c.k,114586694303187+c.lower,114587083094488+c.upper)) = pointBounds63349 := by
 decide +kernel
def cuts63350 : List PrefixCut := [⟨64,192418115,192418227⟩]
theorem checked63350 : checkPrefixCuts (2^48) 8307343361 10 Manual.Count131072.C063350.packed 64 cuts63350 = true := by
 decide +kernel
def cuts63351 : List PrefixCut := [⟨44,133698140,133698220⟩,
⟨64,194956209,194956322⟩]
theorem checked63351 : checkPrefixCuts (2^48) 8307474433 10 Manual.Count131072.C063351.packed 64 cuts63351 = true := by
 decide +kernel
def pointBounds63351 : List (Nat × Nat × Nat) := [(8307564544,114587215076870,114587603868475)]
theorem point_links_checked63351 : (cuts63351.take 1).map (fun c => (8307474433-1+2*2^10*c.k,114587081378730+c.lower,114587470170255+c.upper)) = pointBounds63351 := by
 decide +kernel
def cuts63352 : List PrefixCut := [⟨64,193225184,193225300⟩]
theorem checked63352 : checkPrefixCuts (2^48) 8307605505 10 Manual.Count131072.C063352.packed 64 cuts63352 = true := by
 decide +kernel
def cuts63353 : List PrefixCut := [⟨43,133693942,133694018⟩,
⟨64,195661577,195661691⟩]
theorem checked63353 : checkPrefixCuts (2^48) 8307736577 10 Manual.Count131072.C063353.packed 64 cuts63353 = true := by
 decide +kernel
def pointBounds63353 : List (Nat × Nat × Nat) := [(8307824640,114587603254065,114587992045895)]
theorem point_links_checked63353 : (cuts63353.take 1).map (fun c => (8307736577-1+2*2^10*c.k,114587469560123+c.lower,114587858351877+c.upper)) = pointBounds63353 := by
 decide +kernel
def cuts63354 : List PrefixCut := [⟨64,193998340,193998448⟩]
theorem checked63354 : checkPrefixCuts (2^48) 8307867649 10 Manual.Count131072.C063354.packed 64 cuts63354 = true := by
 decide +kernel
def cuts63355 : List PrefixCut := [⟨42,128641661,128641739⟩,
⟨64,196366874,196366991⟩]
theorem checked63355 : checkPrefixCuts (2^48) 8307998721 10 Manual.Count131072.C063355.packed 64 cuts63355 = true := by
 decide +kernel
def pointBounds63355 : List (Nat × Nat × Nat) := [(8308084736,114587987861701,114588376653755)]
theorem point_links_checked63355 : (cuts63355.take 1).map (fun c => (8307998721-1+2*2^10*c.k,114587859220040+c.lower,114588248012016+c.upper)) = pointBounds63355 := by
 decide +kernel
def cuts63356 : List PrefixCut := [⟨64,196194350,196194463⟩]
theorem checked63356 : checkPrefixCuts (2^48) 8308129793 10 Manual.Count131072.C063356.packed 64 cuts63356 = true := by
 decide +kernel
def cuts63357 : List PrefixCut := [⟨41,125724030,125724105⟩,
⟨64,193582627,193582741⟩]
theorem checked63357 : checkPrefixCuts (2^48) 8308260865 10 Manual.Count131072.C063357.packed 64 cuts63357 = true := by
 decide +kernel
def pointBounds63357 : List (Nat × Nat × Nat) := [(8308344832,114588377505294,114588766297575)]
theorem point_links_checked63357 : (cuts63357.take 1).map (fun c => (8308260865-1+2*2^10*c.k,114588251781264+c.lower,114588640573470+c.upper)) = pointBounds63357 := by
 decide +kernel
def cuts63358 : List PrefixCut := [⟨64,194765310,194765414⟩]
theorem checked63358 : checkPrefixCuts (2^48) 8308391937 10 Manual.Count131072.C063358.packed 64 cuts63358 = true := by
 decide +kernel
def cuts63359 : List PrefixCut := [⟨40,121993541,121993610⟩,
⟨64,195812434,195812546⟩]
theorem checked63359 : checkPrefixCuts (2^48) 8308523009 10 Manual.Count131072.C063359.packed 64 cuts63359 = true := by
 decide +kernel
def pointBounds63359 : List (Nat × Nat × Nat) := [(8308604928,114588762122742,114589150915235)]
theorem point_links_checked63359 : (cuts63359.take 1).map (fun c => (8308523009-1+2*2^10*c.k,114588640129201+c.lower,114589028921625+c.upper)) = pointBounds63359 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000104
