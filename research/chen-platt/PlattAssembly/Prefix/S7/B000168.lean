import PlattAssemblyKernel
import PlattCertificates.Count131072.C065376
import PlattCertificates.Count131072.C065377
import PlattCertificates.Count131072.C065378
import PlattCertificates.Count131072.C065379
import PlattCertificates.Count131072.C065380
import PlattCertificates.Count131072.C065381
import PlattCertificates.Count131072.C065382
import PlattCertificates.Count131072.C065383
import PlattCertificates.Count131072.C065384
import PlattCertificates.Count131072.C065385
import PlattCertificates.Count131072.C065386
import PlattCertificates.Count131072.C065387
import PlattCertificates.Count131072.C065388
import PlattCertificates.Count131072.C065389
import PlattCertificates.Count131072.C065390
import PlattCertificates.Count131072.C065391
import PlattCertificates.Count131072.C065392
import PlattCertificates.Count131072.C065393
import PlattCertificates.Count131072.C065394
import PlattCertificates.Count131072.C065395
import PlattCertificates.Count131072.C065396
import PlattCertificates.Count131072.C065397
import PlattCertificates.Count131072.C065398
import PlattCertificates.Count131072.C065399
import PlattCertificates.Count131072.C065400
import PlattCertificates.Count131072.C065401
import PlattCertificates.Count131072.C065402
import PlattCertificates.Count131072.C065403
import PlattCertificates.Count131072.C065404
import PlattCertificates.Count131072.C065405
import PlattCertificates.Count131072.C065406
import PlattCertificates.Count131072.C065407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000168
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65376 : List PrefixCut := [⟨64,189642650,189642764⟩]
theorem checked65376 : checkPrefixCuts (2^48) 8572895233 10 Manual.Count131072.C065376.packed 64 cuts65376 = true := by
 decide +kernel
def cuts65377 : List PrefixCut := [⟨41,119378818,119378886⟩,
⟨64,187275816,187275927⟩]
theorem checked65377 : checkPrefixCuts (2^48) 8573026305 10 Manual.Count131072.C065377.packed 64 cuts65377 = true := by
 decide +kernel
def pointBounds65377 : List (Nat × Nat × Nat) := [(8573110272,114974707080391,114975096095772)]
theorem point_links_checked65377 : (cuts65377.take 1).map (fun c => (8573026305-1+2*2^10*c.k,114974587701573+c.lower,114974976716886+c.upper)) = pointBounds65377 := by
 decide +kernel
def cuts65378 : List PrefixCut := [⟨64,188717553,188717669⟩]
theorem checked65378 : checkPrefixCuts (2^48) 8573157377 10 Manual.Count131072.C065378.packed 64 cuts65378 = true := by
 decide +kernel
def cuts65379 : List PrefixCut := [⟨44,129060393,129060472⟩,
⟨64,186810454,186810566⟩]
theorem checked65379 : checkPrefixCuts (2^48) 8573288449 10 Manual.Count131072.C065379.packed 64 cuts65379 = true := by
 decide +kernel
def pointBounds65379 : List (Nat × Nat × Nat) := [(8573378560,114975092755335,114975481770954)]
theorem point_links_checked65379 : (cuts65379.take 1).map (fun c => (8573288449-1+2*2^10*c.k,114974963694942+c.lower,114975352710482+c.upper)) = pointBounds65379 := by
 decide +kernel
def cuts65380 : List PrefixCut := [⟨64,189138589,189138698⟩]
theorem checked65380 : checkPrefixCuts (2^48) 8573419521 10 Manual.Count131072.C065380.packed 64 cuts65380 = true := by
 decide +kernel
def cuts65381 : List PrefixCut := [⟨47,136705895,136705973⟩,
⟨64,187362856,187362962⟩]
theorem checked65381 : checkPrefixCuts (2^48) 8573550593 10 Manual.Count131072.C065381.packed 64 cuts65381 = true := by
 decide +kernel
def pointBounds65381 : List (Nat × Nat × Nat) := [(8573646848,114975476349880,114975865365719)]
theorem point_links_checked65381 : (cuts65381.take 1).map (fun c => (8573550593-1+2*2^10*c.k,114975339643985+c.lower,114975728659746+c.upper)) = pointBounds65381 := by
 decide +kernel
def cuts65382 : List PrefixCut := [⟨64,189428274,189428381⟩]
theorem checked65382 : checkPrefixCuts (2^48) 8573681665 10 Manual.Count131072.C065382.packed 64 cuts65382 = true := by
 decide +kernel
def cuts65383 : List PrefixCut := [⟨50,145368631,145368711⟩,
⟨64,187324296,187324402⟩]
theorem checked65383 : checkPrefixCuts (2^48) 8573812737 10 Manual.Count131072.C065383.packed 64 cuts65383 = true := by
 decide +kernel
def pointBounds65383 : List (Nat × Nat × Nat) := [(8573915136,114975861803746,114976250819800)]
theorem point_links_checked65383 : (cuts65383.take 1).map (fun c => (8573812737-1+2*2^10*c.k,114975716435115+c.lower,114976105451089+c.upper)) = pointBounds65383 := by
 decide +kernel
def cuts65384 : List PrefixCut := [⟨64,190440179,190440290⟩]
theorem checked65384 : checkPrefixCuts (2^48) 8573943809 10 Manual.Count131072.C065384.packed 64 cuts65384 = true := by
 decide +kernel
def cuts65385 : List PrefixCut := [⟨53,153177275,153177364⟩,
⟨64,185512995,185513104⟩]
theorem checked65385 : checkPrefixCuts (2^48) 8574074881 10 Manual.Count131072.C065385.packed 64 cuts65385 = true := by
 decide +kernel
def pointBounds65385 : List (Nat × Nat × Nat) := [(8574183424,114976247376865,114976636393145)]
theorem point_links_checked65385 : (cuts65385.take 1).map (fun c => (8574074881-1+2*2^10*c.k,114976094199590+c.lower,114976483215781+c.upper)) = pointBounds65385 := by
 decide +kernel
def cuts65386 : List PrefixCut := [⟨64,187118750,187118854⟩]
theorem checked65386 : checkPrefixCuts (2^48) 8574205953 10 Manual.Count131072.C065386.packed 64 cuts65386 = true := by
 decide +kernel
def cuts65387 : List PrefixCut := [⟨56,164924759,164924854⟩,
⟨64,187641130,187641240⟩]
theorem checked65387 : checkPrefixCuts (2^48) 8574337025 10 Manual.Count131072.C065387.packed 64 cuts65387 = true := by
 decide +kernel
def pointBounds65387 : List (Nat × Nat × Nat) := [(8574451712,114976631756094,114977020772593)]
theorem point_links_checked65387 : (cuts65387.take 1).map (fun c => (8574337025-1+2*2^10*c.k,114976466831335+c.lower,114976855847739+c.upper)) = pointBounds65387 := by
 decide +kernel
def cuts65388 : List PrefixCut := [⟨64,188590227,188590339⟩]
theorem checked65388 : checkPrefixCuts (2^48) 8574468097 10 Manual.Count131072.C065388.packed 64 cuts65388 = true := by
 decide +kernel
def cuts65389 : List PrefixCut := [⟨59,173290369,173290472⟩,
⟨64,188160599,188160711⟩]
theorem checked65389 : checkPrefixCuts (2^48) 8574599169 10 Manual.Count131072.C065389.packed 64 cuts65389 = true := by
 decide +kernel
def pointBounds65389 : List (Nat × Nat × Nat) := [(8574720000,114977016353061,114977405369790)]
theorem point_links_checked65389 : (cuts65389.take 1).map (fun c => (8574599169-1+2*2^10*c.k,114976843062692+c.lower,114977232079318+c.upper)) = pointBounds65389 := by
 decide +kernel
def cuts65390 : List PrefixCut := [⟨64,188157735,188157851⟩]
theorem checked65390 : checkPrefixCuts (2^48) 8574730241 10 Manual.Count131072.C065390.packed 64 cuts65390 = true := by
 decide +kernel
def cuts65391 : List PrefixCut := [⟨62,181950911,181951023⟩,
⟨64,187826604,187826719⟩]
theorem checked65391 : checkPrefixCuts (2^48) 8574861313 10 Manual.Count131072.C065391.packed 64 cuts65391 = true := by
 decide +kernel
def pointBounds65391 : List (Nat × Nat × Nat) := [(8574988288,114977401331937,114977790348903)]
theorem point_links_checked65391 : (cuts65391.take 1).map (fun c => (8574861313-1+2*2^10*c.k,114977219381026+c.lower,114977608397880+c.upper)) = pointBounds65391 := by
 decide +kernel
def cuts65392 : List PrefixCut := [⟨64,186773348,186773459⟩]
theorem checked65392 : checkPrefixCuts (2^48) 8574992385 10 Manual.Count131072.C065392.packed 64 cuts65392 = true := by
 decide +kernel
def cuts65393 : List PrefixCut := [⟨64,188116265,188116376⟩]
theorem checked65393 : checkPrefixCuts (2^48) 8575123457 10 Manual.Count131072.C065393.packed 64 cuts65393 = true := by
 decide +kernel
def cuts65394 : List PrefixCut := [⟨1,2855695,2855697⟩,
⟨64,185356183,185356298⟩]
theorem checked65394 : checkPrefixCuts (2^48) 8575254529 10 Manual.Count131072.C065394.packed 64 cuts65394 = true := by
 decide +kernel
def pointBounds65394 : List (Nat × Nat × Nat) := [(8575256576,114977784952938,114978173970131)]
theorem point_links_checked65394 : (cuts65394.take 1).map (fun c => (8575254529-1+2*2^10*c.k,114977782097243+c.lower,114978171114434+c.upper)) = pointBounds65394 := by
 decide +kernel
def cuts65395 : List PrefixCut := [⟨64,186239606,186239708⟩]
theorem checked65395 : checkPrefixCuts (2^48) 8575385601 10 Manual.Count131072.C065395.packed 64 cuts65395 = true := by
 decide +kernel
def cuts65396 : List PrefixCut := [⟨4,12013242,12013249⟩,
⟨64,188764116,188764220⟩]
theorem checked65396 : checkPrefixCuts (2^48) 8575516673 10 Manual.Count131072.C065396.packed 64 cuts65396 = true := by
 decide +kernel
def pointBounds65396 : List (Nat × Nat × Nat) := [(8575524864,114978165706274,114978554723689)]
theorem point_links_checked65396 : (cuts65396.take 1).map (fun c => (8575516673-1+2*2^10*c.k,114978153693032+c.lower,114978542710440+c.upper)) = pointBounds65396 := by
 decide +kernel
def cuts65397 : List PrefixCut := [⟨64,188104770,188104881⟩]
theorem checked65397 : checkPrefixCuts (2^48) 8575647745 10 Manual.Count131072.C065397.packed 64 cuts65397 = true := by
 decide +kernel
def cuts65398 : List PrefixCut := [⟨7,19758876,19758888⟩,
⟨64,187839327,187839431⟩]
theorem checked65398 : checkPrefixCuts (2^48) 8575778817 10 Manual.Count131072.C065398.packed 64 cuts65398 = true := by
 decide +kernel
def pointBounds65398 : List (Nat × Nat × Nat) := [(8575793152,114978550320794,114978939338429)]
theorem point_links_checked65398 : (cuts65398.take 1).map (fun c => (8575778817-1+2*2^10*c.k,114978530561918+c.lower,114978919579541+c.upper)) = pointBounds65398 := by
 decide +kernel
def cuts65399 : List PrefixCut := [⟨64,187770812,187770932⟩]
theorem checked65399 : checkPrefixCuts (2^48) 8575909889 10 Manual.Count131072.C065399.packed 64 cuts65399 = true := by
 decide +kernel
def cuts65400 : List PrefixCut := [⟨10,29703037,29703057⟩,
⟨64,190229509,190229619⟩]
theorem checked65400 : checkPrefixCuts (2^48) 8576040961 10 Manual.Count131072.C065400.packed 64 cuts65400 = true := by
 decide +kernel
def pointBounds65400 : List (Nat × Nat × Nat) := [(8576061440,114978935875094,114979324892961)]
theorem point_links_checked65400 : (cuts65400.take 1).map (fun c => (8576040961-1+2*2^10*c.k,114978906172057+c.lower,114979295189904+c.upper)) = pointBounds65400 := by
 decide +kernel
def cuts65401 : List PrefixCut := [⟨64,185139439,185139547⟩]
theorem checked65401 : checkPrefixCuts (2^48) 8576172033 10 Manual.Count131072.C065401.packed 64 cuts65401 = true := by
 decide +kernel
def cuts65402 : List PrefixCut := [⟨13,39384026,39384048⟩,
⟨64,186482244,186482353⟩]
theorem checked65402 : checkPrefixCuts (2^48) 8576303105 10 Manual.Count131072.C065402.packed 64 cuts65402 = true := by
 decide +kernel
def pointBounds65402 : List (Nat × Nat × Nat) := [(8576329728,114979320925031,114979709943118)]
theorem point_links_checked65402 : (cuts65402.take 1).map (fun c => (8576303105-1+2*2^10*c.k,114979281541005+c.lower,114979670559070+c.upper)) = pointBounds65402 := by
 decide +kernel
def cuts65403 : List PrefixCut := [⟨64,187660880,187660984⟩]
theorem checked65403 : checkPrefixCuts (2^48) 8576434177 10 Manual.Count131072.C065403.packed 64 cuts65403 = true := by
 decide +kernel
def cuts65404 : List PrefixCut := [⟨16,46963999,46964027⟩,
⟨64,187658004,187658116⟩]
theorem checked65404 : checkPrefixCuts (2^48) 8576565249 10 Manual.Count131072.C065404.packed 64 cuts65404 = true := by
 decide +kernel
def pointBounds65404 : List (Nat × Nat × Nat) := [(8576598016,114979702648128,114980091666434)]
theorem point_links_checked65404 : (cuts65404.take 1).map (fun c => (8576565249-1+2*2^10*c.k,114979655684129+c.lower,114980044702407+c.upper)) = pointBounds65404 := by
 decide +kernel
def cuts65405 : List PrefixCut := [⟨64,188967854,188967971⟩]
theorem checked65405 : checkPrefixCuts (2^48) 8576696321 10 Manual.Count131072.C065405.packed 64 cuts65405 = true := by
 decide +kernel
def cuts65406 : List PrefixCut := [⟨19,55987495,55987528⟩,
⟨64,189358796,189358906⟩]
theorem checked65406 : checkPrefixCuts (2^48) 8576827393 10 Manual.Count131072.C065406.packed 64 cuts65406 = true := by
 decide +kernel
def pointBounds65406 : List (Nat × Nat × Nat) := [(8576866304,114980088297482,114980477316022)]
theorem point_links_checked65406 : (cuts65406.take 1).map (fun c => (8576827393-1+2*2^10*c.k,114980032309987+c.lower,114980421328494+c.upper)) = pointBounds65406 := by
 decide +kernel
def cuts65407 : List PrefixCut := [⟨64,188076031,188076145⟩]
theorem checked65407 : checkPrefixCuts (2^48) 8576958465 10 Manual.Count131072.C065407.packed 64 cuts65407 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000168
