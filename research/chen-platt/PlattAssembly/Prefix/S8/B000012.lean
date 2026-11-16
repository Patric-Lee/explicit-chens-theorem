import PlattAssemblyKernel
import PlattCertificates.Count131072.C070384
import PlattCertificates.Count131072.C070385
import PlattCertificates.Count131072.C070386
import PlattCertificates.Count131072.C070387
import PlattCertificates.Count131072.C070388
import PlattCertificates.Count131072.C070389
import PlattCertificates.Count131072.C070390
import PlattCertificates.Count131072.C070391
import PlattCertificates.Count131072.C070392
import PlattCertificates.Count131072.C070393
import PlattCertificates.Count131072.C070394
import PlattCertificates.Count131072.C070395
import PlattCertificates.Count131072.C070396
import PlattCertificates.Count131072.C070397
import PlattCertificates.Count131072.C070398
import PlattCertificates.Count131072.C070399
import PlattCertificates.Count131072.C070400
import PlattCertificates.Count131072.C070401
import PlattCertificates.Count131072.C070402
import PlattCertificates.Count131072.C070403
import PlattCertificates.Count131072.C070404
import PlattCertificates.Count131072.C070405
import PlattCertificates.Count131072.C070406
import PlattCertificates.Count131072.C070407
import PlattCertificates.Count131072.C070408
import PlattCertificates.Count131072.C070409
import PlattCertificates.Count131072.C070410
import PlattCertificates.Count131072.C070411
import PlattCertificates.Count131072.C070412
import PlattCertificates.Count131072.C070413
import PlattCertificates.Count131072.C070414
import PlattCertificates.Count131072.C070415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70384 : List PrefixCut := [⟨64,174935033,174935137⟩]
theorem checked70384 : checkPrefixCuts (2^48) 9229303809 10 Manual.Count131072.C070384.packed 64 cuts70384 = true := by
 decide +kernel
def cuts70385 : List PrefixCut := [⟨6,16499149,16499159⟩,
⟨64,173346681,173346781⟩]
theorem checked70385 : checkPrefixCuts (2^48) 9229434881 10 Manual.Count131072.C070385.packed 64 cuts70385 = true := by
 decide +kernel
def pointBounds70385 : List (Nat × Nat × Nat) := [(9229447168,115881003751863,115881393296648)]
theorem point_links_checked70385 : (cuts70385.take 1).map (fun c => (9229434881-1+2*2^10*c.k,115880987252714+c.lower,115881376797489+c.upper)) = pointBounds70385 := by
 decide +kernel
def cuts70386 : List PrefixCut := [⟨64,175905960,175906060⟩]
theorem checked70386 : checkPrefixCuts (2^48) 9229565953 10 Manual.Count131072.C070386.packed 64 cuts70386 = true := by
 decide +kernel
def cuts70387 : List PrefixCut := [⟨19,52820097,52820129⟩,
⟨64,177214817,177214921⟩]
theorem checked70387 : checkPrefixCuts (2^48) 9229697025 10 Manual.Count131072.C070387.packed 64 cuts70387 = true := by
 decide +kernel
def pointBounds70387 : List (Nat × Nat × Nat) := [(9229735936,115881389325452,115881778870459)]
theorem point_links_checked70387 : (cuts70387.take 1).map (fun c => (9229697025-1+2*2^10*c.k,115881336505355+c.lower,115881726050330+c.upper)) = pointBounds70387 := by
 decide +kernel
def cuts70388 : List PrefixCut := [⟨64,176510882,176510986⟩]
theorem checked70388 : checkPrefixCuts (2^48) 9229828097 10 Manual.Count131072.C070388.packed 64 cuts70388 = true := by
 decide +kernel
def cuts70389 : List PrefixCut := [⟨32,85723366,85723413⟩,
⟨64,172604944,172605039⟩]
theorem checked70389 : checkPrefixCuts (2^48) 9229959169 10 Manual.Count131072.C070389.packed 64 cuts70389 = true := by
 decide +kernel
def pointBounds70389 : List (Nat × Nat × Nat) := [(9230024704,115881775954420,115882165499650)]
theorem point_links_checked70389 : (cuts70389.take 1).map (fun c => (9229959169-1+2*2^10*c.k,115881690231054+c.lower,115882079776237+c.upper)) = pointBounds70389 := by
 decide +kernel
def cuts70390 : List PrefixCut := [⟨64,175499527,175499631⟩]
theorem checked70390 : checkPrefixCuts (2^48) 9230090241 10 Manual.Count131072.C070390.packed 64 cuts70390 = true := by
 decide +kernel
def cuts70391 : List PrefixCut := [⟨45,124327180,124327255⟩,
⟨64,175801988,175802095⟩]
theorem checked70391 : checkPrefixCuts (2^48) 9230221313 10 Manual.Count131072.C070391.packed 64 cuts70391 = true := by
 decide +kernel
def pointBounds70391 : List (Nat × Nat × Nat) := [(9230313472,115882162662705,115882552208162)]
theorem point_links_checked70391 : (cuts70391.take 1).map (fun c => (9230221313-1+2*2^10*c.k,115882038335525+c.lower,115882427880907+c.upper)) = pointBounds70391 := by
 decide +kernel
def cuts70392 : List PrefixCut := [⟨64,175433569,175433667⟩]
theorem checked70392 : checkPrefixCuts (2^48) 9230352385 10 Manual.Count131072.C070392.packed 64 cuts70392 = true := by
 decide +kernel
def cuts70393 : List PrefixCut := [⟨58,159940307,159940403⟩,
⟨64,176681319,176681425⟩]
theorem checked70393 : checkPrefixCuts (2^48) 9230483457 10 Manual.Count131072.C070393.packed 64 cuts70393 = true := by
 decide +kernel
def pointBounds70393 : List (Nat × Nat × Nat) := [(9230602240,115882549511389,115882939057072)]
theorem point_links_checked70393 : (cuts70393.take 1).map (fun c => (9230483457-1+2*2^10*c.k,115882389571082+c.lower,115882779116669+c.upper)) = pointBounds70393 := by
 decide +kernel
def cuts70394 : List PrefixCut := [⟨64,173568473,173568579⟩]
theorem checked70394 : checkPrefixCuts (2^48) 9230614529 10 Manual.Count131072.C070394.packed 64 cuts70394 = true := by
 decide +kernel
def cuts70395 : List PrefixCut := [⟨64,175334601,175334707⟩]
theorem checked70395 : checkPrefixCuts (2^48) 9230745601 10 Manual.Count131072.C070395.packed 64 cuts70395 = true := by
 decide +kernel
def cuts70396 : List PrefixCut := [⟨7,19057959,19057970⟩,
⟨64,172557301,172557402⟩]
theorem checked70396 : checkPrefixCuts (2^48) 9230876673 10 Manual.Count131072.C070396.packed 64 cuts70396 = true := by
 decide +kernel
def pointBounds70396 : List (Nat × Nat × Nat) := [(9230891008,115882934213434,115883323759350)]
theorem point_links_checked70396 : (cuts70396.take 1).map (fun c => (9230876673-1+2*2^10*c.k,115882915155475+c.lower,115883304701380+c.upper)) = pointBounds70396 := by
 decide +kernel
def cuts70397 : List PrefixCut := [⟨64,175360123,175360227⟩]
theorem checked70397 : checkPrefixCuts (2^48) 9231007745 10 Manual.Count131072.C070397.packed 64 cuts70397 = true := by
 decide +kernel
def cuts70398 : List PrefixCut := [⟨20,55464630,55464662⟩,
⟨64,176760243,176760348⟩]
theorem checked70398 : checkPrefixCuts (2^48) 9231138817 10 Manual.Count131072.C070398.packed 64 cuts70398 = true := by
 decide +kernel
def pointBounds70398 : List (Nat × Nat × Nat) := [(9231179776,115883318537529,115883708083671)]
theorem point_links_checked70398 : (cuts70398.take 1).map (fun c => (9231138817-1+2*2^10*c.k,115883263072899+c.lower,115883652619009+c.upper)) = pointBounds70398 := by
 decide +kernel
def cuts70399 : List PrefixCut := [⟨64,172092585,172092690⟩]
theorem checked70399 : checkPrefixCuts (2^48) 9231269889 10 Manual.Count131072.C070399.packed 64 cuts70399 = true := by
 decide +kernel
def cuts70400 : List PrefixCut := [⟨33,90984899,90984951⟩,
⟨64,172608501,172608605⟩]
theorem checked70400 : checkPrefixCuts (2^48) 9231400961 10 Manual.Count131072.C070400.packed 64 cuts70400 = true := by
 decide +kernel
def pointBounds70400 : List (Nat × Nat × Nat) := [(9231468544,115883702910626,115884092456998)]
theorem point_links_checked70400 : (cuts70400.take 1).map (fun c => (9231400961-1+2*2^10*c.k,115883611925727+c.lower,115884001472047+c.upper)) = pointBounds70400 := by
 decide +kernel
def cuts70401 : List PrefixCut := [⟨64,173246318,173246423⟩]
theorem checked70401 : checkPrefixCuts (2^48) 9231532033 10 Manual.Count131072.C070401.packed 64 cuts70401 = true := by
 decide +kernel
def cuts70402 : List PrefixCut := [⟨46,126685980,126686054⟩,
⟨64,175134254,175134359⟩]
theorem checked70402 : checkPrefixCuts (2^48) 9231663105 10 Manual.Count131072.C070402.packed 64 cuts70402 = true := by
 decide +kernel
def pointBounds70402 : List (Nat × Nat × Nat) := [(9231757312,115884084466526,115884474013129)]
theorem point_links_checked70402 : (cuts70402.take 1).map (fun c => (9231663105-1+2*2^10*c.k,115883957780546+c.lower,115884347327075+c.upper)) = pointBounds70402 := by
 decide +kernel
def cuts70403 : List PrefixCut := [⟨64,174125596,174125701⟩]
theorem checked70403 : checkPrefixCuts (2^48) 9231794177 10 Manual.Count131072.C070403.packed 64 cuts70403 = true := by
 decide +kernel
def cuts70404 : List PrefixCut := [⟨59,161378790,161378886⟩,
⟨64,174732918,174733023⟩]
theorem checked70404 : checkPrefixCuts (2^48) 9231925249 10 Manual.Count131072.C070404.packed 64 cuts70404 = true := by
 decide +kernel
def pointBounds70404 : List (Nat × Nat × Nat) := [(9232046080,115884468419186,115884857966021)]
theorem point_links_checked70404 : (cuts70404.take 1).map (fun c => (9231925249-1+2*2^10*c.k,115884307040396+c.lower,115884696587135+c.upper)) = pointBounds70404 := by
 decide +kernel
def cuts70405 : List PrefixCut := [⟨64,171071778,171071881⟩]
theorem checked70405 : checkPrefixCuts (2^48) 9232056321 10 Manual.Count131072.C070405.packed 64 cuts70405 = true := by
 decide +kernel
def cuts70406 : List PrefixCut := [⟨64,172776702,172776807⟩]
theorem checked70406 : checkPrefixCuts (2^48) 9232187393 10 Manual.Count131072.C070406.packed 64 cuts70406 = true := by
 decide +kernel
def cuts70407 : List PrefixCut := [⟨8,20640354,20640367⟩,
⟨64,174115701,174115802⟩]
theorem checked70407 : checkPrefixCuts (2^48) 9232318465 10 Manual.Count131072.C070407.packed 64 cuts70407 = true := by
 decide +kernel
def pointBounds70407 : List (Nat × Nat × Nat) := [(9232334848,115884846262148,115885235809213)]
theorem point_links_checked70407 : (cuts70407.take 1).map (fun c => (9232318465-1+2*2^10*c.k,115884825621794+c.lower,115885215168846+c.upper)) = pointBounds70407 := by
 decide +kernel
def cuts70408 : List PrefixCut := [⟨64,173320569,173320670⟩]
theorem checked70408 : checkPrefixCuts (2^48) 9232449537 10 Manual.Count131072.C070408.packed 64 cuts70408 = true := by
 decide +kernel
def cuts70409 : List PrefixCut := [⟨21,57407136,57407170⟩,
⟨64,174720505,174720615⟩]
theorem checked70409 : checkPrefixCuts (2^48) 9232580609 10 Manual.Count131072.C070409.packed 64 cuts70409 = true := by
 decide +kernel
def pointBounds70409 : List (Nat × Nat × Nat) := [(9232623616,115885230465200,115885620012488)]
theorem point_links_checked70409 : (cuts70409.take 1).map (fun c => (9232580609-1+2*2^10*c.k,115885173058064+c.lower,115885562605318+c.upper)) = pointBounds70409 := by
 decide +kernel
def cuts70410 : List PrefixCut := [⟨64,175967978,175968077⟩]
theorem checked70410 : checkPrefixCuts (2^48) 9232711681 10 Manual.Count131072.C070410.packed 64 cuts70410 = true := by
 decide +kernel
def cuts70411 : List PrefixCut := [⟨34,90879213,90879264⟩,
⟨64,171849854,171849956⟩]
theorem checked70411 : checkPrefixCuts (2^48) 9232842753 10 Manual.Count131072.C070411.packed 64 cuts70411 = true := by
 decide +kernel
def pointBounds70411 : List (Nat × Nat × Nat) := [(9232912384,115885614625760,115886004173274)]
theorem point_links_checked70411 : (cuts70411.take 1).map (fun c => (9232842753-1+2*2^10*c.k,115885523746547+c.lower,115885913294010+c.upper)) = pointBounds70411 := by
 decide +kernel
def cuts70412 : List PrefixCut := [⟨64,174286268,174286368⟩]
theorem checked70412 : checkPrefixCuts (2^48) 9232973825 10 Manual.Count131072.C070412.packed 64 cuts70412 = true := by
 decide +kernel
def cuts70413 : List PrefixCut := [⟨47,127062487,127062558⟩,
⟨64,172911964,172912063⟩]
theorem checked70413 : checkPrefixCuts (2^48) 9233104897 10 Manual.Count131072.C070413.packed 64 cuts70413 = true := by
 decide +kernel
def pointBounds70413 : List (Nat × Nat × Nat) := [(9233201152,115885996945156,115886386492892)]
theorem point_links_checked70413 : (cuts70413.take 1).map (fun c => (9233104897-1+2*2^10*c.k,115885869882669+c.lower,115886259430334+c.upper)) = pointBounds70413 := by
 decide +kernel
def cuts70414 : List PrefixCut := [⟨64,175378784,175378880⟩]
theorem checked70414 : checkPrefixCuts (2^48) 9233235969 10 Manual.Count131072.C070414.packed 64 cuts70414 = true := by
 decide +kernel
def cuts70415 : List PrefixCut := [⟨60,164280068,164280165⟩,
⟨64,175101928,175102033⟩]
theorem checked70415 : checkPrefixCuts (2^48) 9233367041 10 Manual.Count131072.C070415.packed 64 cuts70415 = true := by
 decide +kernel
def pointBounds70415 : List (Nat × Nat × Nat) := [(9233489920,115886382453485,115886772001442)]
theorem point_links_checked70415 : (cuts70415.take 1).map (fun c => (9233367041-1+2*2^10*c.k,115886218173417+c.lower,115886607721277+c.upper)) = pointBounds70415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000012
