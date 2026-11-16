import PlattAssemblyKernel
import PlattCertificates.Count131072.C068320
import PlattCertificates.Count131072.C068321
import PlattCertificates.Count131072.C068322
import PlattCertificates.Count131072.C068323
import PlattCertificates.Count131072.C068324
import PlattCertificates.Count131072.C068325
import PlattCertificates.Count131072.C068326
import PlattCertificates.Count131072.C068327
import PlattCertificates.Count131072.C068328
import PlattCertificates.Count131072.C068329
import PlattCertificates.Count131072.C068330
import PlattCertificates.Count131072.C068331
import PlattCertificates.Count131072.C068332
import PlattCertificates.Count131072.C068333
import PlattCertificates.Count131072.C068334
import PlattCertificates.Count131072.C068335
import PlattCertificates.Count131072.C068336
import PlattCertificates.Count131072.C068337
import PlattCertificates.Count131072.C068338
import PlattCertificates.Count131072.C068339
import PlattCertificates.Count131072.C068340
import PlattCertificates.Count131072.C068341
import PlattCertificates.Count131072.C068342
import PlattCertificates.Count131072.C068343
import PlattCertificates.Count131072.C068344
import PlattCertificates.Count131072.C068345
import PlattCertificates.Count131072.C068346
import PlattCertificates.Count131072.C068347
import PlattCertificates.Count131072.C068348
import PlattCertificates.Count131072.C068349
import PlattCertificates.Count131072.C068350
import PlattCertificates.Count131072.C068351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000260
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68320 : List PrefixCut := [⟨24,68084606,68084645⟩,
⟨64,181128735,181128844⟩]
theorem checked68320 : checkPrefixCuts (2^48) 8958771201 10 Manual.Count131072.C068320.packed 64 cuts68320 = true := by
 decide +kernel
def pointBounds68320 : List (Nat × Nat × Nat) := [(8958820352,115515723479625,115516112809887)]
theorem point_links_checked68320 : (cuts68320.take 1).map (fun c => (8958771201-1+2*2^10*c.k,115515655395019+c.lower,115516044725242+c.upper)) = pointBounds68320 := by
 decide +kernel
def cuts68321 : List PrefixCut := [⟨64,180152115,180152219⟩]
theorem checked68321 : checkPrefixCuts (2^48) 8958902273 10 Manual.Count131072.C068321.packed 64 cuts68321 = true := by
 decide +kernel
def cuts68322 : List PrefixCut := [⟨33,91865883,91865936⟩,
⟨64,181657526,181657633⟩]
theorem checked68322 : checkPrefixCuts (2^48) 8959033345 10 Manual.Count131072.C068322.packed 64 cuts68322 = true := by
 decide +kernel
def pointBounds68322 : List (Nat × Nat × Nat) := [(8959100928,115516108541752,115516497872241)]
theorem point_links_checked68322 : (cuts68322.take 1).map (fun c => (8959033345-1+2*2^10*c.k,115516016675869+c.lower,115516406006305+c.upper)) = pointBounds68322 := by
 decide +kernel
def cuts68323 : List PrefixCut := [⟨64,178167550,178167661⟩]
theorem checked68323 : checkPrefixCuts (2^48) 8959164417 10 Manual.Count131072.C068323.packed 64 cuts68323 = true := by
 decide +kernel
def cuts68324 : List PrefixCut := [⟨42,117907733,117907803⟩,
⟨64,179264546,179264650⟩]
theorem checked68324 : checkPrefixCuts (2^48) 8959295489 10 Manual.Count131072.C068324.packed 64 cuts68324 = true := by
 decide +kernel
def pointBounds68324 : List (Nat × Nat × Nat) := [(8959381504,115516494408678,115516883739402)]
theorem point_links_checked68324 : (cuts68324.take 1).map (fun c => (8959295489-1+2*2^10*c.k,115516376500945+c.lower,115516765831599+c.upper)) = pointBounds68324 := by
 decide +kernel
def cuts68325 : List PrefixCut := [⟨64,181178310,181178418⟩]
theorem checked68325 : checkPrefixCuts (2^48) 8959426561 10 Manual.Count131072.C068325.packed 64 cuts68325 = true := by
 decide +kernel
def cuts68326 : List PrefixCut := [⟨51,140649326,140649405⟩,
⟨64,176997346,176997446⟩]
theorem checked68326 : checkPrefixCuts (2^48) 8959557633 10 Manual.Count131072.C068326.packed 64 cuts68326 = true := by
 decide +kernel
def pointBounds68326 : List (Nat × Nat × Nat) := [(8959662080,115516877593127,115517266924072)]
theorem point_links_checked68326 : (cuts68326.take 1).map (fun c => (8959557633-1+2*2^10*c.k,115516736943801+c.lower,115517126274667+c.upper)) = pointBounds68326 := by
 decide +kernel
def cuts68327 : List PrefixCut := [⟨64,178816853,178816957⟩]
theorem checked68327 : checkPrefixCuts (2^48) 8959688705 10 Manual.Count131072.C068327.packed 64 cuts68327 = true := by
 decide +kernel
def cuts68328 : List PrefixCut := [⟨60,170489333,170489426⟩,
⟨64,181233193,181233292⟩]
theorem checked68328 : checkPrefixCuts (2^48) 8959819777 10 Manual.Count131072.C068328.packed 64 cuts68328 = true := by
 decide +kernel
def pointBounds68328 : List (Nat × Nat × Nat) := [(8959942656,115517263247333,115517652578496)]
theorem point_links_checked68328 : (cuts68328.take 1).map (fun c => (8959819777-1+2*2^10*c.k,115517092758000+c.lower,115517482089070+c.upper)) = pointBounds68328 := by
 decide +kernel
def cuts68329 : List PrefixCut := [⟨64,179534151,179534253⟩]
theorem checked68329 : checkPrefixCuts (2^48) 8959950849 10 Manual.Count131072.C068329.packed 64 cuts68329 = true := by
 decide +kernel
def cuts68330 : List PrefixCut := [⟨64,180379727,180379834⟩]
theorem checked68330 : checkPrefixCuts (2^48) 8960081921 10 Manual.Count131072.C068330.packed 64 cuts68330 = true := by
 decide +kernel
def cuts68331 : List PrefixCut := [⟨5,13193813,13193822⟩,
⟨64,178272351,178272459⟩]
theorem checked68331 : checkPrefixCuts (2^48) 8960212993 10 Manual.Count131072.C068331.packed 64 cuts68331 = true := by
 decide +kernel
def pointBounds68331 : List (Nat × Nat × Nat) := [(8960223232,115517647098884,115518036430271)]
theorem point_links_checked68331 : (cuts68331.take 1).map (fun c => (8960212993-1+2*2^10*c.k,115517633905071+c.lower,115518023236449+c.upper)) = pointBounds68331 := by
 decide +kernel
def cuts68332 : List PrefixCut := [⟨64,178363996,178364096⟩]
theorem checked68332 : checkPrefixCuts (2^48) 8960344065 10 Manual.Count131072.C068332.packed 64 cuts68332 = true := by
 decide +kernel
def cuts68333 : List PrefixCut := [⟨14,40114263,40114285⟩,
⟨64,181314185,181314286⟩]
theorem checked68333 : checkPrefixCuts (2^48) 8960475137 10 Manual.Count131072.C068333.packed 64 cuts68333 = true := by
 decide +kernel
def pointBounds68333 : List (Nat × Nat × Nat) := [(8960503808,115518030655681,115518419987289)]
theorem point_links_checked68333 : (cuts68333.take 1).map (fun c => (8960475137-1+2*2^10*c.k,115517990541418+c.lower,115518379873004+c.upper)) = pointBounds68333 := by
 decide +kernel
def cuts68334 : List PrefixCut := [⟨64,180212103,180212207⟩]
theorem checked68334 : checkPrefixCuts (2^48) 8960606209 10 Manual.Count131072.C068334.packed 64 cuts68334 = true := by
 decide +kernel
def cuts68335 : List PrefixCut := [⟨23,64143188,64143224⟩,
⟨64,177979237,177979340⟩]
theorem checked68335 : checkPrefixCuts (2^48) 8960737281 10 Manual.Count131072.C068335.packed 64 cuts68335 = true := by
 decide +kernel
def pointBounds68335 : List (Nat × Nat × Nat) := [(8960784384,115518416210894,115518805542721)]
theorem point_links_checked68335 : (cuts68335.take 1).map (fun c => (8960737281-1+2*2^10*c.k,115518352067706+c.lower,115518741399497+c.upper)) = pointBounds68335 := by
 decide +kernel
def cuts68336 : List PrefixCut := [⟨64,178259318,178259421⟩]
theorem checked68336 : checkPrefixCuts (2^48) 8960868353 10 Manual.Count131072.C068336.packed 64 cuts68336 = true := by
 decide +kernel
def cuts68337 : List PrefixCut := [⟨32,88861686,88861741⟩,
⟨64,180141356,180141459⟩]
theorem checked68337 : checkPrefixCuts (2^48) 8960999425 10 Manual.Count131072.C068337.packed 64 cuts68337 = true := by
 decide +kernel
def pointBounds68337 : List (Nat × Nat × Nat) := [(8961064960,115518797167947,115519186499999)]
theorem point_links_checked68337 : (cuts68337.take 1).map (fun c => (8960999425-1+2*2^10*c.k,115518708306261+c.lower,115519097638258+c.upper)) = pointBounds68337 := by
 decide +kernel
def cuts68338 : List PrefixCut := [⟨64,180390024,180390136⟩]
theorem checked68338 : checkPrefixCuts (2^48) 8961130497 10 Manual.Count131072.C068338.packed 64 cuts68338 = true := by
 decide +kernel
def cuts68339 : List PrefixCut := [⟨41,116060102,116060168⟩,
⟨64,181298277,181298381⟩]
theorem checked68339 : checkPrefixCuts (2^48) 8961261569 10 Manual.Count131072.C068339.packed 64 cuts68339 = true := by
 decide +kernel
def pointBounds68339 : List (Nat × Nat × Nat) := [(8961345536,115519184897743,115519574230021)]
theorem point_links_checked68339 : (cuts68339.take 1).map (fun c => (8961261569-1+2*2^10*c.k,115519068837641+c.lower,115519458169853+c.upper)) = pointBounds68339 := by
 decide +kernel
def cuts68340 : List PrefixCut := [⟨64,182928900,182929012⟩]
theorem checked68340 : checkPrefixCuts (2^48) 8961392641 10 Manual.Count131072.C068340.packed 64 cuts68340 = true := by
 decide +kernel
def cuts68341 : List PrefixCut := [⟨50,139990305,139990389⟩,
⟨64,179282788,179282894⟩]
theorem checked68341 : checkPrefixCuts (2^48) 8961523713 10 Manual.Count131072.C068341.packed 64 cuts68341 = true := by
 decide +kernel
def pointBounds68341 : List (Nat × Nat × Nat) := [(8961626112,115519573055123,115519962387635)]
theorem point_links_checked68341 : (cuts68341.take 1).map (fun c => (8961523713-1+2*2^10*c.k,115519433064818+c.lower,115519822397246+c.upper)) = pointBounds68341 := by
 decide +kernel
def cuts68342 : List PrefixCut := [⟨64,176987332,176987446⟩]
theorem checked68342 : checkPrefixCuts (2^48) 8961654785 10 Manual.Count131072.C068342.packed 64 cuts68342 = true := by
 decide +kernel
def cuts68343 : List PrefixCut := [⟨59,162568502,162568598⟩,
⟨64,176545020,176545125⟩]
theorem checked68343 : checkPrefixCuts (2^48) 8961785857 10 Manual.Count131072.C068343.packed 64 cuts68343 = true := by
 decide +kernel
def pointBounds68343 : List (Nat × Nat × Nat) := [(8961906688,115519951903440,115520341236184)]
theorem point_links_checked68343 : (cuts68343.take 1).map (fun c => (8961785857-1+2*2^10*c.k,115519789334938+c.lower,115520178667586+c.upper)) = pointBounds68343 := by
 decide +kernel
def cuts68344 : List PrefixCut := [⟨64,180374185,180374290⟩]
theorem checked68344 : checkPrefixCuts (2^48) 8961916929 10 Manual.Count131072.C068344.packed 64 cuts68344 = true := by
 decide +kernel
def cuts68345 : List PrefixCut := [⟨64,179649185,179649292⟩]
theorem checked68345 : checkPrefixCuts (2^48) 8962048001 10 Manual.Count131072.C068345.packed 64 cuts68345 = true := by
 decide +kernel
def cuts68346 : List PrefixCut := [⟨4,11620575,11620580⟩,
⟨64,177950603,177950707⟩]
theorem checked68346 : checkPrefixCuts (2^48) 8962179073 10 Manual.Count131072.C068346.packed 64 cuts68346 = true := by
 decide +kernel
def pointBounds68346 : List (Nat × Nat × Nat) := [(8962187264,115520337523903,115520726856873)]
theorem point_links_checked68346 : (cuts68346.take 1).map (fun c => (8962179073-1+2*2^10*c.k,115520325903328+c.lower,115520715236293+c.upper)) = pointBounds68346 := by
 decide +kernel
def cuts68347 : List PrefixCut := [⟨64,180491900,180492007⟩]
theorem checked68347 : checkPrefixCuts (2^48) 8962310145 10 Manual.Count131072.C068347.packed 64 cuts68347 = true := by
 decide +kernel
def cuts68348 : List PrefixCut := [⟨13,35206132,35206152⟩,
⟨64,178887548,178887650⟩]
theorem checked68348 : checkPrefixCuts (2^48) 8962441217 10 Manual.Count131072.C068348.packed 64 cuts68348 = true := by
 decide +kernel
def pointBounds68348 : List (Nat × Nat × Nat) := [(8962467840,115520719551963,115521108885159)]
theorem point_links_checked68348 : (cuts68348.take 1).map (fun c => (8962441217-1+2*2^10*c.k,115520684345831+c.lower,115521073679007+c.upper)) = pointBounds68348 := by
 decide +kernel
def cuts68349 : List PrefixCut := [⟨64,179041961,179042063⟩]
theorem checked68349 : checkPrefixCuts (2^48) 8962572289 10 Manual.Count131072.C068349.packed 64 cuts68349 = true := by
 decide +kernel
def cuts68350 : List PrefixCut := [⟨22,60548943,60548982⟩,
⟨64,177500508,177500611⟩]
theorem checked68350 : checkPrefixCuts (2^48) 8962703361 10 Manual.Count131072.C068350.packed 64 cuts68350 = true := by
 decide +kernel
def pointBounds68350 : List (Nat × Nat × Nat) := [(8962748416,115521102824283,115521492157702)]
theorem point_links_checked68350 : (cuts68350.take 1).map (fun c => (8962703361-1+2*2^10*c.k,115521042275340+c.lower,115521431608720+c.upper)) = pointBounds68350 := by
 decide +kernel
def cuts68351 : List PrefixCut := [⟨64,177246686,177246789⟩]
theorem checked68351 : checkPrefixCuts (2^48) 8962834433 10 Manual.Count131072.C068351.packed 64 cuts68351 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000260
