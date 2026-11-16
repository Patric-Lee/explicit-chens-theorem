import PlattAssemblyKernel
import PlattCertificates.Count131072.C074480
import PlattCertificates.Count131072.C074481
import PlattCertificates.Count131072.C074482
import PlattCertificates.Count131072.C074483
import PlattCertificates.Count131072.C074484
import PlattCertificates.Count131072.C074485
import PlattCertificates.Count131072.C074486
import PlattCertificates.Count131072.C074487
import PlattCertificates.Count131072.C074488
import PlattCertificates.Count131072.C074489
import PlattCertificates.Count131072.C074490
import PlattCertificates.Count131072.C074491
import PlattCertificates.Count131072.C074492
import PlattCertificates.Count131072.C074493
import PlattCertificates.Count131072.C074494
import PlattCertificates.Count131072.C074495
import PlattCertificates.Count131072.C074496
import PlattCertificates.Count131072.C074497
import PlattCertificates.Count131072.C074498
import PlattCertificates.Count131072.C074499
import PlattCertificates.Count131072.C074500
import PlattCertificates.Count131072.C074501
import PlattCertificates.Count131072.C074502
import PlattCertificates.Count131072.C074503
import PlattCertificates.Count131072.C074504
import PlattCertificates.Count131072.C074505
import PlattCertificates.Count131072.C074506
import PlattCertificates.Count131072.C074507
import PlattCertificates.Count131072.C074508
import PlattCertificates.Count131072.C074509
import PlattCertificates.Count131072.C074510
import PlattCertificates.Count131072.C074511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000140
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74480 : List PrefixCut := [⟨41,106408177,106408240⟩,
⟨64,164713240,164713338⟩]
theorem checked74480 : checkPrefixCuts (2^48) 9766174721 10 Manual.Count131072.C074480.packed 64 cuts74480 = true := by
 decide +kernel
def pointBounds74480 : List (Nat × Nat × Nat) := [(9766258688,116573730063971,116574120020382)]
theorem point_links_checked74480 : (cuts74480.take 1).map (fun c => (9766174721-1+2*2^10*c.k,116573623655794+c.lower,116574013612142+c.upper)) = pointBounds74480 := by
 decide +kernel
def cuts74481 : List PrefixCut := [⟨64,164278698,164278801⟩]
theorem checked74481 : checkPrefixCuts (2^48) 9766305793 10 Manual.Count131072.C074481.packed 64 cuts74481 = true := by
 decide +kernel
def cuts74482 : List PrefixCut := [⟨63,161567395,161567496⟩,
⟨64,164247678,164247781⟩]
theorem checked74482 : checkPrefixCuts (2^48) 9766436865 10 Manual.Count131072.C074482.packed 64 cuts74482 = true := by
 decide +kernel
def pointBounds74482 : List (Nat × Nat × Nat) := [(9766565888,116574114215127,116574504171777)]
theorem point_links_checked74482 : (cuts74482.take 1).map (fun c => (9766436865-1+2*2^10*c.k,116573952647732+c.lower,116574342604281+c.upper)) = pointBounds74482 := by
 decide +kernel
def cuts74483 : List PrefixCut := [⟨64,167703886,167703979⟩]
theorem checked74483 : checkPrefixCuts (2^48) 9766567937 10 Manual.Count131072.C074483.packed 64 cuts74483 = true := by
 decide +kernel
def cuts74484 : List PrefixCut := [⟨64,164617929,164618027⟩]
theorem checked74484 : checkPrefixCuts (2^48) 9766699009 10 Manual.Count131072.C074484.packed 64 cuts74484 = true := by
 decide +kernel
def cuts74485 : List PrefixCut := [⟨21,53546461,53546493⟩,
⟨64,162742467,162742566⟩]
theorem checked74485 : checkPrefixCuts (2^48) 9766830081 10 Manual.Count131072.C074485.packed 64 cuts74485 = true := by
 decide +kernel
def pointBounds74485 : List (Nat × Nat × Nat) := [(9766873088,116574502763686,116574892720561)]
theorem point_links_checked74485 : (cuts74485.take 1).map (fun c => (9766830081-1+2*2^10*c.k,116574449217225+c.lower,116574839174068+c.upper)) = pointBounds74485 := by
 decide +kernel
def cuts74486 : List PrefixCut := [⟨64,163086106,163086205⟩]
theorem checked74486 : checkPrefixCuts (2^48) 9766961153 10 Manual.Count131072.C074486.packed 64 cuts74486 = true := by
 decide +kernel
def cuts74487 : List PrefixCut := [⟨43,110115748,110115817⟩,
⟨64,166772674,166772777⟩]
theorem checked74487 : checkPrefixCuts (2^48) 9767092225 10 Manual.Count131072.C074487.packed 64 cuts74487 = true := by
 decide +kernel
def pointBounds74487 : List (Nat × Nat × Nat) := [(9767180288,116574885161546,116575275118656)]
theorem point_links_checked74487 : (cuts74487.take 1).map (fun c => (9767092225-1+2*2^10*c.k,116574775045798+c.lower,116575165002839+c.upper)) = pointBounds74487 := by
 decide +kernel
def cuts74488 : List PrefixCut := [⟨64,163859824,163859916⟩]
theorem checked74488 : checkPrefixCuts (2^48) 9767223297 10 Manual.Count131072.C074488.packed 64 cuts74488 = true := by
 decide +kernel
def cuts74489 : List PrefixCut := [⟨64,164808614,164808710⟩]
theorem checked74489 : checkPrefixCuts (2^48) 9767354369 10 Manual.Count131072.C074489.packed 64 cuts74489 = true := by
 decide +kernel
def cuts74490 : List PrefixCut := [⟨1,2680031,2680032⟩,
⟨64,165123393,165123494⟩]
theorem checked74490 : checkPrefixCuts (2^48) 9767485441 10 Manual.Count131072.C074490.packed 64 cuts74490 = true := by
 decide +kernel
def pointBounds74490 : List (Nat × Nat × Nat) := [(9767487488,116575273166941,116575663124274)]
theorem point_links_checked74490 : (cuts74490.take 1).map (fun c => (9767485441-1+2*2^10*c.k,116575270486910+c.lower,116575660444242+c.upper)) = pointBounds74490 := by
 decide +kernel
def cuts74491 : List PrefixCut := [⟨64,162124204,162124302⟩]
theorem checked74491 : checkPrefixCuts (2^48) 9767616513 10 Manual.Count131072.C074491.packed 64 cuts74491 = true := by
 decide +kernel
def cuts74492 : List PrefixCut := [⟨23,58786061,58786096⟩,
⟨64,166790313,166790411⟩]
theorem checked74492 : checkPrefixCuts (2^48) 9767747585 10 Manual.Count131072.C074492.packed 64 cuts74492 = true := by
 decide +kernel
def pointBounds74492 : List (Nat × Nat × Nat) := [(9767794688,116575656520568,116576046478134)]
theorem point_links_checked74492 : (cuts74492.take 1).map (fun c => (9767747585-1+2*2^10*c.k,116575597734507+c.lower,116575987692038+c.upper)) = pointBounds74492 := by
 decide +kernel
def cuts74493 : List PrefixCut := [⟨64,161975782,161975879⟩]
theorem checked74493 : checkPrefixCuts (2^48) 9767878657 10 Manual.Count131072.C074493.packed 64 cuts74493 = true := by
 decide +kernel
def cuts74494 : List PrefixCut := [⟨45,116329610,116329676⟩,
⟨64,165777289,165777383⟩]
theorem checked74494 : checkPrefixCuts (2^48) 9768009729 10 Manual.Count131072.C074494.packed 64 cuts74494 = true := by
 decide +kernel
def pointBounds74494 : List (Nat × Nat × Nat) := [(9768101888,116576042830212,116576432788004)]
theorem point_links_checked74494 : (cuts74494.take 1).map (fun c => (9768009729-1+2*2^10*c.k,116575926500602+c.lower,116576316458328+c.upper)) = pointBounds74494 := by
 decide +kernel
def cuts74495 : List PrefixCut := [⟨64,165602175,165602274⟩]
theorem checked74495 : checkPrefixCuts (2^48) 9768140801 10 Manual.Count131072.C074495.packed 64 cuts74495 = true := by
 decide +kernel
def cuts74496 : List PrefixCut := [⟨64,163006599,163006695⟩]
theorem checked74496 : checkPrefixCuts (2^48) 9768271873 10 Manual.Count131072.C074496.packed 64 cuts74496 = true := by
 decide +kernel
def cuts74497 : List PrefixCut := [⟨3,7578298,7578304⟩,
⟨64,165770608,165770710⟩]
theorem checked74497 : checkPrefixCuts (2^48) 9768402945 10 Manual.Count131072.C074497.packed 64 cuts74497 = true := by
 decide +kernel
def pointBounds74497 : List (Nat × Nat × Nat) := [(9768409088,116576428464963,116576818422984)]
theorem point_links_checked74497 : (cuts74497.take 1).map (fun c => (9768402945-1+2*2^10*c.k,116576420886665+c.lower,116576810844680+c.upper)) = pointBounds74497 := by
 decide +kernel
def cuts74498 : List PrefixCut := [⟨64,162598820,162598920⟩]
theorem checked74498 : checkPrefixCuts (2^48) 9768534017 10 Manual.Count131072.C074498.packed 64 cuts74498 = true := by
 decide +kernel
def cuts74499 : List PrefixCut := [⟨25,65004344,65004389⟩,
⟨64,165737355,165737465⟩]
theorem checked74499 : checkPrefixCuts (2^48) 9768665089 10 Manual.Count131072.C074499.packed 64 cuts74499 = true := by
 decide +kernel
def pointBounds74499 : List (Nat × Nat × Nat) := [(9768716288,116576814260437,116577204218699)]
theorem point_links_checked74499 : (cuts74499.take 1).map (fun c => (9768665089-1+2*2^10*c.k,116576749256093+c.lower,116577139214310+c.upper)) = pointBounds74499 := by
 decide +kernel
def cuts74500 : List PrefixCut := [⟨64,164467336,164467434⟩]
theorem checked74500 : checkPrefixCuts (2^48) 9768796161 10 Manual.Count131072.C074500.packed 64 cuts74500 = true := by
 decide +kernel
def cuts74501 : List PrefixCut := [⟨47,120266061,120266136⟩,
⟨64,163917683,163917782⟩]
theorem checked74501 : checkPrefixCuts (2^48) 9768927233 10 Manual.Count131072.C074501.packed 64 cuts74501 = true := by
 decide +kernel
def pointBounds74501 : List (Nat × Nat × Nat) := [(9769023488,116577199726845,116577589685345)]
theorem point_links_checked74501 : (cuts74501.take 1).map (fun c => (9768927233-1+2*2^10*c.k,116577079460784+c.lower,116577469419209+c.upper)) = pointBounds74501 := by
 decide +kernel
def cuts74502 : List PrefixCut := [⟨64,165356113,165356212⟩]
theorem checked74502 : checkPrefixCuts (2^48) 9769058305 10 Manual.Count131072.C074502.packed 64 cuts74502 = true := by
 decide +kernel
def cuts74503 : List PrefixCut := [⟨64,164662395,164662494⟩]
theorem checked74503 : checkPrefixCuts (2^48) 9769189377 10 Manual.Count131072.C074503.packed 64 cuts74503 = true := by
 decide +kernel
def cuts74504 : List PrefixCut := [⟨5,12821389,12821397⟩,
⟨64,163219599,163219692⟩]
theorem checked74504 : checkPrefixCuts (2^48) 9769320449 10 Manual.Count131072.C074504.packed 64 cuts74504 = true := by
 decide +kernel
def pointBounds74504 : List (Nat × Nat × Nat) := [(9769330688,116577586218364,116577976177094)]
theorem point_links_checked74504 : (cuts74504.take 1).map (fun c => (9769320449-1+2*2^10*c.k,116577573396975+c.lower,116577963355697+c.upper)) = pointBounds74504 := by
 decide +kernel
def cuts74505 : List PrefixCut := [⟨64,162785236,162785328⟩]
theorem checked74505 : checkPrefixCuts (2^48) 9769451521 10 Manual.Count131072.C074505.packed 64 cuts74505 = true := by
 decide +kernel
def cuts74506 : List PrefixCut := [⟨27,70558805,70558846⟩,
⟨64,165865852,165865945⟩]
theorem checked74506 : checkPrefixCuts (2^48) 9769582593 10 Manual.Count131072.C074506.packed 64 cuts74506 = true := by
 decide +kernel
def pointBounds74506 : List (Nat × Nat × Nat) := [(9769637888,116577969960615,116578359919563)]
theorem point_links_checked74506 : (cuts74506.take 1).map (fun c => (9769582593-1+2*2^10*c.k,116577899401810+c.lower,116578289360717+c.upper)) = pointBounds74506 := by
 decide +kernel
def cuts74507 : List PrefixCut := [⟨64,165604317,165604418⟩]
theorem checked74507 : checkPrefixCuts (2^48) 9769713665 10 Manual.Count131072.C074507.packed 64 cuts74507 = true := by
 decide +kernel
def cuts74508 : List PrefixCut := [⟨49,124317017,124317094⟩,
⟨64,162980358,162980458⟩]
theorem checked74508 : checkPrefixCuts (2^48) 9769844737 10 Manual.Count131072.C074508.packed 64 cuts74508 = true := by
 decide +kernel
def pointBounds74508 : List (Nat × Nat × Nat) := [(9769945088,116578355188996,116578745148174)]
theorem point_links_checked74508 : (cuts74508.take 1).map (fun c => (9769844737-1+2*2^10*c.k,116578230871979+c.lower,116578620831080+c.upper)) = pointBounds74508 := by
 decide +kernel
def cuts74509 : List PrefixCut := [⟨64,163208644,163208738⟩]
theorem checked74509 : checkPrefixCuts (2^48) 9769975809 10 Manual.Count131072.C074509.packed 64 cuts74509 = true := by
 decide +kernel
def cuts74510 : List PrefixCut := [⟨64,166519564,166519659⟩]
theorem checked74510 : checkPrefixCuts (2^48) 9770106881 10 Manual.Count131072.C074510.packed 64 cuts74510 = true := by
 decide +kernel
def cuts74511 : List PrefixCut := [⟨7,16478977,16478986⟩,
⟨64,161763807,161763902⟩]
theorem checked74511 : checkPrefixCuts (2^48) 9770237953 10 Manual.Count131072.C074511.packed 64 cuts74511 = true := by
 decide +kernel
def pointBounds74511 : List (Nat × Nat × Nat) := [(9770252288,116578740059522,116579130018921)]
theorem point_links_checked74511 : (cuts74511.take 1).map (fun c => (9770237953-1+2*2^10*c.k,116578723580545+c.lower,116579113539935+c.upper)) = pointBounds74511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000140
