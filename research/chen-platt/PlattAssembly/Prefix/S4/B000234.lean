import PlattAssemblyKernel
import PlattCertificates.Count131072.C037488
import PlattCertificates.Count131072.C037489
import PlattCertificates.Count131072.C037490
import PlattCertificates.Count131072.C037491
import PlattCertificates.Count131072.C037492
import PlattCertificates.Count131072.C037493
import PlattCertificates.Count131072.C037494
import PlattCertificates.Count131072.C037495
import PlattCertificates.Count131072.C037496
import PlattCertificates.Count131072.C037497
import PlattCertificates.Count131072.C037498
import PlattCertificates.Count131072.C037499
import PlattCertificates.Count131072.C037500
import PlattCertificates.Count131072.C037501
import PlattCertificates.Count131072.C037502
import PlattCertificates.Count131072.C037503
import PlattCertificates.Count131072.C037504
import PlattCertificates.Count131072.C037505
import PlattCertificates.Count131072.C037506
import PlattCertificates.Count131072.C037507
import PlattCertificates.Count131072.C037508
import PlattCertificates.Count131072.C037509
import PlattCertificates.Count131072.C037510
import PlattCertificates.Count131072.C037511
import PlattCertificates.Count131072.C037512
import PlattCertificates.Count131072.C037513
import PlattCertificates.Count131072.C037514
import PlattCertificates.Count131072.C037515
import PlattCertificates.Count131072.C037516
import PlattCertificates.Count131072.C037517
import PlattCertificates.Count131072.C037518
import PlattCertificates.Count131072.C037519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000234
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts37488 : List PrefixCut := [⟨64,331694071,331694271⟩]
theorem checked37488 : checkPrefixCuts (2^48) 4917559297 10 Manual.Count131072.C037488.packed 64 cuts37488 = true := by
 decide +kernel
def cuts37489 : List PrefixCut := [⟨4,21750122,21750136⟩,
⟨64,341472689,341472895⟩]
theorem checked37489 : checkPrefixCuts (2^48) 4917690369 10 Manual.Count131072.C037489.packed 64 cuts37489 = true := by
 decide +kernel
def pointBounds37489 : List (Nat × Nat × Nat) := [(4917698560,108050346924339,108050731940179)]
theorem point_links_checked37489 : (cuts37489.take 1).map (fun c => (4917690369-1+2*2^10*c.k,108050325174217+c.lower,108050710190043+c.upper)) = pointBounds37489 := by
 decide +kernel
def cuts37490 : List PrefixCut := [⟨16,82132938,82132992⟩,
⟨64,333565131,333565337⟩]
theorem checked37490 : checkPrefixCuts (2^48) 4917821441 10 Manual.Count131072.C037490.packed 64 cuts37490 = true := by
 decide +kernel
def pointBounds37490 : List (Nat × Nat × Nat) := [(4917854208,108050748779844,108051133795930)]
theorem point_links_checked37490 : (cuts37490.take 1).map (fun c => (4917821441-1+2*2^10*c.k,108050666646906+c.lower,108051051662938+c.upper)) = pointBounds37490 := by
 decide +kernel
def cuts37491 : List PrefixCut := [⟨28,145889033,145889121⟩,
⟨64,333384556,333384759⟩]
theorem checked37491 : checkPrefixCuts (2^48) 4917952513 10 Manual.Count131072.C037491.packed 64 cuts37491 = true := by
 decide +kernel
def pointBounds37491 : List (Nat × Nat × Nat) := [(4918009856,108051146101070,108051531117396)]
theorem point_links_checked37491 : (cuts37491.take 1).map (fun c => (4917952513-1+2*2^10*c.k,108051000212037+c.lower,108051385228275+c.upper)) = pointBounds37491 := by
 decide +kernel
def cuts37492 : List PrefixCut := [⟨40,212159632,212159761⟩,
⟨64,340300733,340300940⟩]
theorem checked37492 : checkPrefixCuts (2^48) 4918083585 10 Manual.Count131072.C037492.packed 64 cuts37492 = true := by
 decide +kernel
def pointBounds37492 : List (Nat × Nat × Nat) := [(4918165504,108051545756225,108051930772795)]
theorem point_links_checked37492 : (cuts37492.take 1).map (fun c => (4918083585-1+2*2^10*c.k,108051333596593+c.lower,108051718613034+c.upper)) = pointBounds37492 := by
 decide +kernel
def cuts37493 : List PrefixCut := [⟨52,272359902,272360072⟩,
⟨64,333309563,333309770⟩]
theorem checked37493 : checkPrefixCuts (2^48) 4918214657 10 Manual.Count131072.C037493.packed 64 cuts37493 = true := by
 decide +kernel
def pointBounds37493 : List (Nat × Nat × Nat) := [(4918321152,108051946257228,108052331274046)]
theorem point_links_checked37493 : (cuts37493.take 1).map (fun c => (4918214657-1+2*2^10*c.k,108051673897326+c.lower,108052058913974+c.upper)) = pointBounds37493 := by
 decide +kernel
def cuts37494 : List PrefixCut := [⟨64,340625981,340626191⟩]
theorem checked37494 : checkPrefixCuts (2^48) 4918345729 10 Manual.Count131072.C037494.packed 64 cuts37494 = true := by
 decide +kernel
def pointBounds37494 : List (Nat × Nat × Nat) := [(4918476800,108052347832870,108052732849935)]
theorem point_links_checked37494 : (cuts37494.take 1).map (fun c => (4918345729-1+2*2^10*c.k,108052007206889+c.lower,108052392223744+c.upper)) = pointBounds37494 := by
 decide +kernel
def cuts37495 : List PrefixCut := [⟨64,336038717,336038919⟩]
theorem checked37495 : checkPrefixCuts (2^48) 4918476801 10 Manual.Count131072.C037495.packed 64 cuts37495 = true := by
 decide +kernel
def cuts37496 : List PrefixCut := [⟨12,65867578,65867618⟩,
⟨64,342496275,342496482⟩]
theorem checked37496 : checkPrefixCuts (2^48) 4918607873 10 Manual.Count131072.C037496.packed 64 cuts37496 = true := by
 decide +kernel
def pointBounds37496 : List (Nat × Nat × Nat) := [(4918632448,108052749739165,108053134756472)]
theorem point_links_checked37496 : (cuts37496.take 1).map (fun c => (4918607873-1+2*2^10*c.k,108052683871587+c.lower,108053068888854+c.upper)) = pointBounds37496 := by
 decide +kernel
def cuts37497 : List PrefixCut := [⟨24,128698394,128698473⟩,
⟨64,339053664,339053872⟩]
theorem checked37497 : checkPrefixCuts (2^48) 4918738945 10 Manual.Count131072.C037497.packed 64 cuts37497 = true := by
 decide +kernel
def pointBounds37497 : List (Nat × Nat × Nat) := [(4918788096,108053155066256,108053540083809)]
theorem point_links_checked37497 : (cuts37497.take 1).map (fun c => (4918738945-1+2*2^10*c.k,108053026367862+c.lower,108053411385336+c.upper)) = pointBounds37497 := by
 decide +kernel
def cuts37498 : List PrefixCut := [⟨36,185688812,185688930⟩,
⟨64,331777342,331777546⟩]
theorem checked37498 : checkPrefixCuts (2^48) 4918870017 10 Manual.Count131072.C037498.packed 64 cuts37498 = true := by
 decide +kernel
def pointBounds37498 : List (Nat × Nat × Nat) := [(4918943744,108053551110338,108053936128138)]
theorem point_links_checked37498 : (cuts37498.take 1).map (fun c => (4918870017-1+2*2^10*c.k,108053365421526+c.lower,108053750439208+c.upper)) = pointBounds37498 := by
 decide +kernel
def cuts37499 : List PrefixCut := [⟨48,251030255,251030408⟩,
⟨64,337433399,337433604⟩]
theorem checked37499 : checkPrefixCuts (2^48) 4919001089 10 Manual.Count131072.C037499.packed 64 cuts37499 = true := by
 decide +kernel
def pointBounds37499 : List (Nat × Nat × Nat) := [(4919099392,108053948229123,108054333247162)]
theorem point_links_checked37499 : (cuts37499.take 1).map (fun c => (4919001089-1+2*2^10*c.k,108053697198868+c.lower,108054082216754+c.upper)) = pointBounds37499 := by
 decide +kernel
def cuts37500 : List PrefixCut := [⟨60,318256083,318256277⟩,
⟨64,339827631,339827838⟩]
theorem checked37500 : checkPrefixCuts (2^48) 4919132161 10 Manual.Count131072.C037500.packed 64 cuts37500 = true := by
 decide +kernel
def pointBounds37500 : List (Nat × Nat × Nat) := [(4919255040,108054352888350,108054737906635)]
theorem point_links_checked37500 : (cuts37500.take 1).map (fun c => (4919132161-1+2*2^10*c.k,108054034632267+c.lower,108054419650358+c.upper)) = pointBounds37500 := by
 decide +kernel
def cuts37501 : List PrefixCut := [⟨64,332952363,332952566⟩]
theorem checked37501 : checkPrefixCuts (2^48) 4919263233 10 Manual.Count131072.C037501.packed 64 cuts37501 = true := by
 decide +kernel
def cuts37502 : List PrefixCut := [⟨8,42398015,42398040⟩,
⟨64,327565179,327565383⟩]
theorem checked37502 : checkPrefixCuts (2^48) 4919394305 10 Manual.Count131072.C037502.packed 64 cuts37502 = true := by
 decide +kernel
def pointBounds37502 : List (Nat × Nat × Nat) := [(4919410688,108054749810276,108055134828802)]
theorem point_links_checked37502 : (cuts37502.take 1).map (fun c => (4919394305-1+2*2^10*c.k,108054707412261+c.lower,108055092430762+c.upper)) = pointBounds37502 := by
 decide +kernel
def cuts37503 : List PrefixCut := [⟨20,105047890,105047956⟩,
⟨64,335051649,335051850⟩]
theorem checked37503 : checkPrefixCuts (2^48) 4919525377 10 Manual.Count131072.C037503.packed 64 cuts37503 = true := by
 decide +kernel
def pointBounds37503 : List (Nat × Nat × Nat) := [(4919566336,108055140025330,108055525044101)]
theorem point_links_checked37503 : (cuts37503.take 1).map (fun c => (4919525377-1+2*2^10*c.k,108055034977440+c.lower,108055419996145+c.upper)) = pointBounds37503 := by
 decide +kernel
def cuts37504 : List PrefixCut := [⟨32,167694100,167694200⟩,
⟨64,338704338,338704540⟩]
theorem checked37504 : checkPrefixCuts (2^48) 4919656449 10 Manual.Count131072.C037504.packed 64 cuts37504 = true := by
 decide +kernel
def pointBounds37504 : List (Nat × Nat × Nat) := [(4919721984,108055537723189,108055922742195)]
theorem point_links_checked37504 : (cuts37504.take 1).map (fun c => (4919656449-1+2*2^10*c.k,108055370029089+c.lower,108055755047995+c.upper)) = pointBounds37504 := by
 decide +kernel
def cuts37505 : List PrefixCut := [⟨44,226675104,226675242⟩,
⟨64,331257782,331257980⟩]
theorem checked37505 : checkPrefixCuts (2^48) 4919787521 10 Manual.Count131072.C037505.packed 64 cuts37505 = true := by
 decide +kernel
def pointBounds37505 : List (Nat × Nat × Nat) := [(4919877632,108055935408531,108056320427777)]
theorem point_links_checked37505 : (cuts37505.take 1).map (fun c => (4919787521-1+2*2^10*c.k,108055708733427+c.lower,108056093752535+c.upper)) = pointBounds37505 := by
 decide +kernel
def cuts37506 : List PrefixCut := [⟨56,286339167,286339339⟩,
⟨64,329360983,329361180⟩]
theorem checked37506 : checkPrefixCuts (2^48) 4919918593 10 Manual.Count131072.C037506.packed 64 cuts37506 = true := by
 decide +kernel
def pointBounds37506 : List (Nat × Nat × Nat) := [(4920033280,108056326330376,108056711349854)]
theorem point_links_checked37506 : (cuts37506.take 1).map (fun c => (4919918593-1+2*2^10*c.k,108056039991209+c.lower,108056425010515+c.upper)) = pointBounds37506 := by
 decide +kernel
def cuts37507 : List PrefixCut := [⟨64,339421040,339421246⟩]
theorem checked37507 : checkPrefixCuts (2^48) 4920049665 10 Manual.Count131072.C037507.packed 64 cuts37507 = true := by
 decide +kernel
def cuts37508 : List PrefixCut := [⟨4,21281448,21281461⟩,
⟨64,342043510,342043716⟩]
theorem checked37508 : checkPrefixCuts (2^48) 4920180737 10 Manual.Count131072.C037508.packed 64 cuts37508 = true := by
 decide +kernel
def pointBounds37508 : List (Nat × Nat × Nat) := [(4920188928,108056730054680,108057115074402)]
theorem point_links_checked37508 : (cuts37508.take 1).map (fun c => (4920180737-1+2*2^10*c.k,108056708773232+c.lower,108057093792941+c.upper)) = pointBounds37508 := by
 decide +kernel
def cuts37509 : List PrefixCut := [⟨16,84093597,84093646⟩,
⟨64,337572336,337572541⟩]
theorem checked37509 : checkPrefixCuts (2^48) 4920311809 10 Manual.Count131072.C037509.packed 64 cuts37509 = true := by
 decide +kernel
def pointBounds37509 : List (Nat × Nat × Nat) := [(4920344576,108057134910339,108057519930303)]
theorem point_links_checked37509 : (cuts37509.take 1).map (fun c => (4920311809-1+2*2^10*c.k,108057050816742+c.lower,108057435836657+c.upper)) = pointBounds37509 := by
 decide +kernel
def cuts37510 : List PrefixCut := [⟨28,145243132,145243221⟩,
⟨64,333845023,333845229⟩]
theorem checked37510 : checkPrefixCuts (2^48) 4920442881 10 Manual.Count131072.C037510.packed 64 cuts37510 = true := by
 decide +kernel
def pointBounds37510 : List (Nat × Nat × Nat) := [(4920500224,108057533632210,108057918652419)]
theorem point_links_checked37510 : (cuts37510.take 1).map (fun c => (4920442881-1+2*2^10*c.k,108057388389078+c.lower,108057773409198+c.upper)) = pointBounds37510 := by
 decide +kernel
def cuts37511 : List PrefixCut := [⟨40,213539537,213539666⟩,
⟨64,338641258,338641464⟩]
theorem checked37511 : checkPrefixCuts (2^48) 4920573953 10 Manual.Count131072.C037511.packed 64 cuts37511 = true := by
 decide +kernel
def pointBounds37511 : List (Nat × Nat × Nat) := [(4920655872,108057935773638,108058320794093)]
theorem point_links_checked37511 : (cuts37511.take 1).map (fun c => (4920573953-1+2*2^10*c.k,108057722234101+c.lower,108058107254427+c.upper)) = pointBounds37511 := by
 decide +kernel
def cuts37512 : List PrefixCut := [⟨52,274395753,274395920⟩,
⟨64,337774205,337774410⟩]
theorem checked37512 : checkPrefixCuts (2^48) 4920705025 10 Manual.Count131072.C037512.packed 64 cuts37512 = true := by
 decide +kernel
def pointBounds37512 : List (Nat × Nat × Nat) := [(4920811520,108058335271112,108058720291811)]
theorem point_links_checked37512 : (cuts37512.take 1).map (fun c => (4920705025-1+2*2^10*c.k,108058060875359+c.lower,108058445895891+c.upper)) = pointBounds37512 := by
 decide +kernel
def cuts37513 : List PrefixCut := [⟨64,331644814,331645013⟩]
theorem checked37513 : checkPrefixCuts (2^48) 4920836097 10 Manual.Count131072.C037513.packed 64 cuts37513 = true := by
 decide +kernel
def pointBounds37513 : List (Nat × Nat × Nat) := [(4920967168,108058730294378,108059115315314)]
theorem point_links_checked37513 : (cuts37513.take 1).map (fun c => (4920836097-1+2*2^10*c.k,108058398649564+c.lower,108058783670301+c.upper)) = pointBounds37513 := by
 decide +kernel
def cuts37514 : List PrefixCut := [⟨64,329462394,329462595⟩]
theorem checked37514 : checkPrefixCuts (2^48) 4920967169 10 Manual.Count131072.C037514.packed 64 cuts37514 = true := by
 decide +kernel
def cuts37515 : List PrefixCut := [⟨12,62688386,62688422⟩,
⟨64,336488831,336489030⟩]
theorem checked37515 : checkPrefixCuts (2^48) 4921098241 10 Manual.Count131072.C037515.packed 64 cuts37515 = true := by
 decide +kernel
def pointBounds37515 : List (Nat × Nat × Nat) := [(4921122816,108059122445158,108059507466331)]
theorem point_links_checked37515 : (cuts37515.take 1).map (fun c => (4921098241-1+2*2^10*c.k,108059059756772+c.lower,108059444777909+c.upper)) = pointBounds37515 := by
 decide +kernel
def cuts37516 : List PrefixCut := [⟨24,125830686,125830763⟩,
⟨64,341284266,341284476⟩]
theorem checked37516 : checkPrefixCuts (2^48) 4921229313 10 Manual.Count131072.C037516.packed 64 cuts37516 = true := by
 decide +kernel
def pointBounds37516 : List (Nat × Nat × Nat) := [(4921278464,108059522076289,108059907097702)]
theorem point_links_checked37516 : (cuts37516.take 1).map (fun c => (4921229313-1+2*2^10*c.k,108059396245603+c.lower,108059781266939+c.upper)) = pointBounds37516 := by
 decide +kernel
def cuts37517 : List PrefixCut := [⟨36,192972896,192973010⟩,
⟨64,339216263,339216464⟩]
theorem checked37517 : checkPrefixCuts (2^48) 4921360385 10 Manual.Count131072.C037517.packed 64 cuts37517 = true := by
 decide +kernel
def pointBounds37517 : List (Nat × Nat × Nat) := [(4921434112,108059930502765,108060315524425)]
theorem point_links_checked37517 : (cuts37517.take 1).map (fun c => (4921360385-1+2*2^10*c.k,108059737529869+c.lower,108060122551415+c.upper)) = pointBounds37517 := by
 decide +kernel
def cuts37518 : List PrefixCut := [⟨48,251532315,251532469⟩,
⟨64,335890033,335890237⟩]
theorem checked37518 : checkPrefixCuts (2^48) 4921491457 10 Manual.Count131072.C037518.packed 64 cuts37518 = true := by
 decide +kernel
def pointBounds37518 : List (Nat × Nat × Nat) := [(4921589760,108060328278447,108060713300348)]
theorem point_links_checked37518 : (cuts37518.take 1).map (fun c => (4921491457-1+2*2^10*c.k,108060076746132+c.lower,108060461767879+c.upper)) = pointBounds37518 := by
 decide +kernel
def cuts37519 : List PrefixCut := [⟨60,312833513,312833703⟩,
⟨64,332964397,332964599⟩]
theorem checked37519 : checkPrefixCuts (2^48) 4921622529 10 Manual.Count131072.C037519.packed 64 cuts37519 = true := by
 decide +kernel
def pointBounds37519 : List (Nat × Nat × Nat) := [(4921745408,108060725469678,108061110491819)]
theorem point_links_checked37519 : (cuts37519.take 1).map (fun c => (4921622529-1+2*2^10*c.k,108060412636165+c.lower,108060797658116+c.upper)) = pointBounds37519 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000234
