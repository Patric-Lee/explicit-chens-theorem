import PlattAssemblyKernel
import PlattCertificates.Count131072.C069312
import PlattCertificates.Count131072.C069313
import PlattCertificates.Count131072.C069314
import PlattCertificates.Count131072.C069315
import PlattCertificates.Count131072.C069316
import PlattCertificates.Count131072.C069317
import PlattCertificates.Count131072.C069318
import PlattCertificates.Count131072.C069319
import PlattCertificates.Count131072.C069320
import PlattCertificates.Count131072.C069321
import PlattCertificates.Count131072.C069322
import PlattCertificates.Count131072.C069323
import PlattCertificates.Count131072.C069324
import PlattCertificates.Count131072.C069325
import PlattCertificates.Count131072.C069326
import PlattCertificates.Count131072.C069327
import PlattCertificates.Count131072.C069328
import PlattCertificates.Count131072.C069329
import PlattCertificates.Count131072.C069330
import PlattCertificates.Count131072.C069331
import PlattCertificates.Count131072.C069332
import PlattCertificates.Count131072.C069333
import PlattCertificates.Count131072.C069334
import PlattCertificates.Count131072.C069335
import PlattCertificates.Count131072.C069336
import PlattCertificates.Count131072.C069337
import PlattCertificates.Count131072.C069338
import PlattCertificates.Count131072.C069339
import PlattCertificates.Count131072.C069340
import PlattCertificates.Count131072.C069341
import PlattCertificates.Count131072.C069342
import PlattCertificates.Count131072.C069343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000291
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69312 : List PrefixCut := [⟨64,178909174,178909279⟩]
theorem checked69312 : checkPrefixCuts (2^48) 9088794625 10 Manual.Count131072.C069312.packed 64 cuts69312 = true := by
 decide +kernel
def cuts69313 : List PrefixCut := [⟨39,108391006,108391070⟩,
⟨64,177977529,177977631⟩]
theorem checked69313 : checkPrefixCuts (2^48) 9088925697 10 Manual.Count131072.C069313.packed 64 cuts69313 = true := by
 decide +kernel
def pointBounds69313 : List (Nat × Nat × Nat) := [(9089005568,115692876843749,115693266277853)]
theorem point_links_checked69313 : (cuts69313.take 1).map (fun c => (9088925697-1+2*2^10*c.k,115692768452743+c.lower,115693157886783+c.upper)) = pointBounds69313 := by
 decide +kernel
def cuts69314 : List PrefixCut := [⟨64,177324623,177324725⟩]
theorem checked69314 : checkPrefixCuts (2^48) 9089056769 10 Manual.Count131072.C069314.packed 64 cuts69314 = true := by
 decide +kernel
def cuts69315 : List PrefixCut := [⟨50,137249846,137249927⟩,
⟨64,175804639,175804742⟩]
theorem checked69315 : checkPrefixCuts (2^48) 9089187841 10 Manual.Count131072.C069315.packed 64 cuts69315 = true := by
 decide +kernel
def pointBounds69315 : List (Nat × Nat × Nat) := [(9089290240,115693261004741,115693650439066)]
theorem point_links_checked69315 : (cuts69315.take 1).map (fun c => (9089187841-1+2*2^10*c.k,115693123754895+c.lower,115693513189139+c.upper)) = pointBounds69315 := by
 decide +kernel
def cuts69316 : List PrefixCut := [⟨64,177907902,177908010⟩]
theorem checked69316 : checkPrefixCuts (2^48) 9089318913 10 Manual.Count131072.C069316.packed 64 cuts69316 = true := by
 decide +kernel
def cuts69317 : List PrefixCut := [⟨61,168088867,168088968⟩,
⟨64,176697630,176697737⟩]
theorem checked69317 : checkPrefixCuts (2^48) 9089449985 10 Manual.Count131072.C069317.packed 64 cuts69317 = true := by
 decide +kernel
def pointBounds69317 : List (Nat × Nat × Nat) := [(9089574912,115693645556303,115694034990859)]
theorem point_links_checked69317 : (cuts69317.take 1).map (fun c => (9089449985-1+2*2^10*c.k,115693477467436+c.lower,115693866901891+c.upper)) = pointBounds69317 := by
 decide +kernel
def cuts69318 : List PrefixCut := [⟨64,176447330,176447441⟩]
theorem checked69318 : checkPrefixCuts (2^48) 9089581057 10 Manual.Count131072.C069318.packed 64 cuts69318 = true := by
 decide +kernel
def cuts69319 : List PrefixCut := [⟨64,178178896,178178992⟩]
theorem checked69319 : checkPrefixCuts (2^48) 9089712129 10 Manual.Count131072.C069319.packed 64 cuts69319 = true := by
 decide +kernel
def cuts69320 : List PrefixCut := [⟨8,21397396,21397410⟩,
⟨64,175451354,175451459⟩]
theorem checked69320 : checkPrefixCuts (2^48) 9089843201 10 Manual.Count131072.C069320.packed 64 cuts69320 = true := by
 decide +kernel
def pointBounds69320 : List (Nat × Nat × Nat) := [(9089859584,115694030188688,115694419623471)]
theorem point_links_checked69320 : (cuts69320.take 1).map (fun c => (9089843201-1+2*2^10*c.k,115694008791292+c.lower,115694398226061+c.upper)) = pointBounds69320 := by
 decide +kernel
def cuts69321 : List PrefixCut := [⟨64,176935138,176935249⟩]
theorem checked69321 : checkPrefixCuts (2^48) 9089974273 10 Manual.Count131072.C069321.packed 64 cuts69321 = true := by
 decide +kernel
def cuts69322 : List PrefixCut := [⟨19,51990084,51990113⟩,
⟨64,177211280,177211381⟩]
theorem checked69322 : checkPrefixCuts (2^48) 9090105345 10 Manual.Count131072.C069322.packed 64 cuts69322 = true := by
 decide +kernel
def pointBounds69322 : List (Nat × Nat × Nat) := [(9090144256,115694413167868,115694802602882)]
theorem point_links_checked69322 : (cuts69322.take 1).map (fun c => (9090105345-1+2*2^10*c.k,115694361177784+c.lower,115694750612769+c.upper)) = pointBounds69322 := by
 decide +kernel
def cuts69323 : List PrefixCut := [⟨64,176930037,176930143⟩]
theorem checked69323 : checkPrefixCuts (2^48) 9090236417 10 Manual.Count131072.C069323.packed 64 cuts69323 = true := by
 decide +kernel
def cuts69324 : List PrefixCut := [⟨30,83355028,83355077⟩,
⟨64,175472198,175472304⟩]
theorem checked69324 : checkPrefixCuts (2^48) 9090367489 10 Manual.Count131072.C069324.packed 64 cuts69324 = true := by
 decide +kernel
def pointBounds69324 : List (Nat × Nat × Nat) := [(9090428928,115694798674129,115695188109370)]
theorem point_links_checked69324 : (cuts69324.take 1).map (fun c => (9090367489-1+2*2^10*c.k,115694715319101+c.lower,115695104754293+c.upper)) = pointBounds69324 := by
 decide +kernel
def cuts69325 : List PrefixCut := [⟨64,177513255,177513364⟩]
theorem checked69325 : checkPrefixCuts (2^48) 9090498561 10 Manual.Count131072.C069325.packed 64 cuts69325 = true := by
 decide +kernel
def cuts69326 : List PrefixCut := [⟨41,112643572,112643638⟩,
⟨64,177046248,177046352⟩]
theorem checked69326 : checkPrefixCuts (2^48) 9090629633 10 Manual.Count131072.C069326.packed 64 cuts69326 = true := by
 decide +kernel
def pointBounds69326 : List (Nat × Nat × Nat) := [(9090713600,115695180948126,115695570383599)]
theorem point_links_checked69326 : (cuts69326.take 1).map (fun c => (9090629633-1+2*2^10*c.k,115695068304554+c.lower,115695457739961+c.upper)) = pointBounds69326 := by
 decide +kernel
def cuts69327 : List PrefixCut := [⟨64,175495559,175495663⟩]
theorem checked69327 : checkPrefixCuts (2^48) 9090760705 10 Manual.Count131072.C069327.packed 64 cuts69327 = true := by
 decide +kernel
def cuts69328 : List PrefixCut := [⟨52,145212323,145212406⟩,
⟨64,179394252,179394356⟩]
theorem checked69328 : checkPrefixCuts (2^48) 9090891777 10 Manual.Count131072.C069328.packed 64 cuts69328 = true := by
 decide +kernel
def pointBounds69328 : List (Nat × Nat × Nat) := [(9090998272,115695566058684,115695955494382)]
theorem point_links_checked69328 : (cuts69328.take 1).map (fun c => (9090891777-1+2*2^10*c.k,115695420846361+c.lower,115695810281976+c.upper)) = pointBounds69328 := by
 decide +kernel
def cuts69329 : List PrefixCut := [⟨64,177905509,177905616⟩]
theorem checked69329 : checkPrefixCuts (2^48) 9091022849 10 Manual.Count131072.C069329.packed 64 cuts69329 = true := by
 decide +kernel
def cuts69330 : List PrefixCut := [⟨63,172763410,172763515⟩,
⟨64,175859506,175859613⟩]
theorem checked69330 : checkPrefixCuts (2^48) 9091153921 10 Manual.Count131072.C069330.packed 64 cuts69330 = true := by
 decide +kernel
def pointBounds69330 : List (Nat × Nat × Nat) := [(9091282944,115695950909532,115696340345463)]
theorem point_links_checked69330 : (cuts69330.take 1).map (fun c => (9091153921-1+2*2^10*c.k,115695778146122+c.lower,115696167581948+c.upper)) = pointBounds69330 := by
 decide +kernel
def cuts69331 : List PrefixCut := [⟨64,177528857,177528961⟩]
theorem checked69331 : checkPrefixCuts (2^48) 9091284993 10 Manual.Count131072.C069331.packed 64 cuts69331 = true := by
 decide +kernel
def cuts69332 : List PrefixCut := [⟨64,180993840,180993943⟩]
theorem checked69332 : checkPrefixCuts (2^48) 9091416065 10 Manual.Count131072.C069332.packed 64 cuts69332 = true := by
 decide +kernel
def cuts69333 : List PrefixCut := [⟨10,27523467,27523484⟩,
⟨64,177771411,177771516⟩]
theorem checked69333 : checkPrefixCuts (2^48) 9091547137 10 Manual.Count131072.C069333.packed 64 cuts69333 = true := by
 decide +kernel
def pointBounds69333 : List (Nat × Nat × Nat) := [(9091567616,115696340051792,115696729487949)]
theorem point_links_checked69333 : (cuts69333.take 1).map (fun c => (9091547137-1+2*2^10*c.k,115696312528325+c.lower,115696701964465+c.upper)) = pointBounds69333 := by
 decide +kernel
def cuts69334 : List PrefixCut := [⟨64,177552129,177552234⟩]
theorem checked69334 : checkPrefixCuts (2^48) 9091678209 10 Manual.Count131072.C069334.packed 64 cuts69334 = true := by
 decide +kernel
def cuts69335 : List PrefixCut := [⟨21,58729417,58729446⟩,
⟨64,175351499,175351599⟩]
theorem checked69335 : checkPrefixCuts (2^48) 9091809281 10 Manual.Count131072.C069335.packed 64 cuts69335 = true := by
 decide +kernel
def pointBounds69335 : List (Nat × Nat × Nat) := [(9091852288,115696726581282,115697116017661)]
theorem point_links_checked69335 : (cuts69335.take 1).map (fun c => (9091809281-1+2*2^10*c.k,115696667851865+c.lower,115697057288215+c.upper)) = pointBounds69335 := by
 decide +kernel
def cuts69336 : List PrefixCut := [⟨64,175256076,175256185⟩]
theorem checked69336 : checkPrefixCuts (2^48) 9091940353 10 Manual.Count131072.C069336.packed 64 cuts69336 = true := by
 decide +kernel
def cuts69337 : List PrefixCut := [⟨32,89840604,89840655⟩,
⟨64,177080087,177080190⟩]
theorem checked69337 : checkPrefixCuts (2^48) 9092071425 10 Manual.Count131072.C069337.packed 64 cuts69337 = true := by
 decide +kernel
def pointBounds69337 : List (Nat × Nat × Nat) := [(9092136960,115697108300044,115697497736654)]
theorem point_links_checked69337 : (cuts69337.take 1).map (fun c => (9092071425-1+2*2^10*c.k,115697018459440+c.lower,115697407895999+c.upper)) = pointBounds69337 := by
 decide +kernel
def cuts69338 : List PrefixCut := [⟨64,178842118,178842217⟩]
theorem checked69338 : checkPrefixCuts (2^48) 9092202497 10 Manual.Count131072.C069338.packed 64 cuts69338 = true := by
 decide +kernel
def cuts69339 : List PrefixCut := [⟨43,117049309,117049381⟩,
⟨64,174877010,174877117⟩]
theorem checked69339 : checkPrefixCuts (2^48) 9092333569 10 Manual.Count131072.C069339.packed 64 cuts69339 = true := by
 decide +kernel
def pointBounds69339 : List (Nat × Nat × Nat) := [(9092421632,115697491430954,115697880867787)]
theorem point_links_checked69339 : (cuts69339.take 1).map (fun c => (9092333569-1+2*2^10*c.k,115697374381645+c.lower,115697763818406+c.upper)) = pointBounds69339 := by
 decide +kernel
def cuts69340 : List PrefixCut := [⟨64,177165293,177165399⟩]
theorem checked69340 : checkPrefixCuts (2^48) 9092464641 10 Manual.Count131072.C069340.packed 64 cuts69340 = true := by
 decide +kernel
def cuts69341 : List PrefixCut := [⟨54,145866117,145866199⟩,
⟨64,171683492,171683588⟩]
theorem checked69341 : checkPrefixCuts (2^48) 9092595713 10 Manual.Count131072.C069341.packed 64 cuts69341 = true := by
 decide +kernel
def pointBounds69341 : List (Nat × Nat × Nat) := [(9092706304,115697872290065,115698261727121)]
theorem point_links_checked69341 : (cuts69341.take 1).map (fun c => (9092595713-1+2*2^10*c.k,115697726423948+c.lower,115698115860922+c.upper)) = pointBounds69341 := by
 decide +kernel
def cuts69342 : List PrefixCut := [⟨64,178460333,178460437⟩]
theorem checked69342 : checkPrefixCuts (2^48) 9092726785 10 Manual.Count131072.C069342.packed 64 cuts69342 = true := by
 decide +kernel
def cuts69343 : List PrefixCut := [⟨64,181119921,181120025⟩]
theorem checked69343 : checkPrefixCuts (2^48) 9092857857 10 Manual.Count131072.C069343.packed 64 cuts69343 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000291
