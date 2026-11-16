import PlattAssemblyKernel
import PlattCertificates.Count131072.C074512
import PlattCertificates.Count131072.C074513
import PlattCertificates.Count131072.C074514
import PlattCertificates.Count131072.C074515
import PlattCertificates.Count131072.C074516
import PlattCertificates.Count131072.C074517
import PlattCertificates.Count131072.C074518
import PlattCertificates.Count131072.C074519
import PlattCertificates.Count131072.C074520
import PlattCertificates.Count131072.C074521
import PlattCertificates.Count131072.C074522
import PlattCertificates.Count131072.C074523
import PlattCertificates.Count131072.C074524
import PlattCertificates.Count131072.C074525
import PlattCertificates.Count131072.C074526
import PlattCertificates.Count131072.C074527
import PlattCertificates.Count131072.C074528
import PlattCertificates.Count131072.C074529
import PlattCertificates.Count131072.C074530
import PlattCertificates.Count131072.C074531
import PlattCertificates.Count131072.C074532
import PlattCertificates.Count131072.C074533
import PlattCertificates.Count131072.C074534
import PlattCertificates.Count131072.C074535
import PlattCertificates.Count131072.C074536
import PlattCertificates.Count131072.C074537
import PlattCertificates.Count131072.C074538
import PlattCertificates.Count131072.C074539
import PlattCertificates.Count131072.C074540
import PlattCertificates.Count131072.C074541
import PlattCertificates.Count131072.C074542
import PlattCertificates.Count131072.C074543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74512 : List PrefixCut := [⟨64,163547781,163547880⟩]
theorem checked74512 : checkPrefixCuts (2^48) 9770369025 10 Manual.Count131072.C074512.packed 64 cuts74512 = true := by
 decide +kernel
def cuts74513 : List PrefixCut := [⟨29,75391998,75392043⟩,
⟨64,163804872,163804974⟩]
theorem checked74513 : checkPrefixCuts (2^48) 9770500097 10 Manual.Count131072.C074513.packed 64 cuts74513 = true := by
 decide +kernel
def pointBounds74513 : List (Nat × Nat × Nat) := [(9770559488,116579124284131,116579514243760)]
theorem point_links_checked74513 : (cuts74513.take 1).map (fun c => (9770500097-1+2*2^10*c.k,116579048892133+c.lower,116579438851717+c.upper)) = pointBounds74513 := by
 decide +kernel
def cuts74514 : List PrefixCut := [⟨64,164148371,164148467⟩]
theorem checked74514 : checkPrefixCuts (2^48) 9770631169 10 Manual.Count131072.C074514.packed 64 cuts74514 = true := by
 decide +kernel
def cuts74515 : List PrefixCut := [⟨51,130383741,130383824⟩,
⟨64,163368357,163368465⟩]
theorem checked74515 : checkPrefixCuts (2^48) 9770762241 10 Manual.Count131072.C074515.packed 64 cuts74515 = true := by
 decide +kernel
def pointBounds74515 : List (Nat × Nat × Nat) := [(9770866688,116579507229117,116579897188982)]
theorem point_links_checked74515 : (cuts74515.take 1).map (fun c => (9770762241-1+2*2^10*c.k,116579376845376+c.lower,116579766805158+c.upper)) = pointBounds74515 := by
 decide +kernel
def cuts74516 : List PrefixCut := [⟨64,165094612,165094708⟩]
theorem checked74516 : checkPrefixCuts (2^48) 9770893313 10 Manual.Count131072.C074516.packed 64 cuts74516 = true := by
 decide +kernel
def cuts74517 : List PrefixCut := [⟨64,163306369,163306466⟩]
theorem checked74517 : checkPrefixCuts (2^48) 9771024385 10 Manual.Count131072.C074517.packed 64 cuts74517 = true := by
 decide +kernel
def cuts74518 : List PrefixCut := [⟨9,23362222,23362238⟩,
⟨64,162007879,162007984⟩]
theorem checked74518 : checkPrefixCuts (2^48) 9771155457 10 Manual.Count131072.C074518.packed 64 cuts74518 = true := by
 decide +kernel
def pointBounds74518 : List (Nat × Nat × Nat) := [(9771173888,116579891976936,116580281937035)]
theorem point_links_checked74518 : (cuts74518.take 1).map (fun c => (9771155457-1+2*2^10*c.k,116579868614714+c.lower,116580258574797+c.upper)) = pointBounds74518 := by
 decide +kernel
def cuts74519 : List PrefixCut := [⟨64,163359589,163359691⟩]
theorem checked74519 : checkPrefixCuts (2^48) 9771286529 10 Manual.Count131072.C074519.packed 64 cuts74519 = true := by
 decide +kernel
def cuts74520 : List PrefixCut := [⟨31,81088465,81088515⟩,
⟨64,168196768,168196869⟩]
theorem checked74520 : checkPrefixCuts (2^48) 9771417601 10 Manual.Count131072.C074520.packed 64 cuts74520 = true := by
 decide +kernel
def pointBounds74520 : List (Nat × Nat × Nat) := [(9771481088,116580275070647,116580665030987)]
theorem point_links_checked74520 : (cuts74520.take 1).map (fun c => (9771417601-1+2*2^10*c.k,116580193982182+c.lower,116580583942472+c.upper)) = pointBounds74520 := by
 decide +kernel
def cuts74521 : List PrefixCut := [⟨64,161540480,161540582⟩]
theorem checked74521 : checkPrefixCuts (2^48) 9771548673 10 Manual.Count131072.C074521.packed 64 cuts74521 = true := by
 decide +kernel
def cuts74522 : List PrefixCut := [⟨53,136190088,136190164⟩,
⟨64,165225341,165225435⟩]
theorem checked74522 : checkPrefixCuts (2^48) 9771679745 10 Manual.Count131072.C074522.packed 64 cuts74522 = true := by
 decide +kernel
def pointBounds74522 : List (Nat × Nat × Nat) := [(9771788288,116580659909518,116581049870087)]
theorem point_links_checked74522 : (cuts74522.take 1).map (fun c => (9771679745-1+2*2^10*c.k,116580523719430+c.lower,116580913679923+c.upper)) = pointBounds74522 := by
 decide +kernel
def cuts74523 : List PrefixCut := [⟨64,164272566,164272668⟩]
theorem checked74523 : checkPrefixCuts (2^48) 9771810817 10 Manual.Count131072.C074523.packed 64 cuts74523 = true := by
 decide +kernel
def cuts74524 : List PrefixCut := [⟨64,165307320,165307418⟩]
theorem checked74524 : checkPrefixCuts (2^48) 9771941889 10 Manual.Count131072.C074524.packed 64 cuts74524 = true := by
 decide +kernel
def cuts74525 : List PrefixCut := [⟨11,27334976,27334991⟩,
⟨64,162223096,162223188⟩]
theorem checked74525 : checkPrefixCuts (2^48) 9772072961 10 Manual.Count131072.C074525.packed 64 cuts74525 = true := by
 decide +kernel
def pointBounds74525 : List (Nat × Nat × Nat) := [(9772095488,116581045859633,116581435820435)]
theorem point_links_checked74525 : (cuts74525.take 1).map (fun c => (9772072961-1+2*2^10*c.k,116581018524657+c.lower,116581408485444+c.upper)) = pointBounds74525 := by
 decide +kernel
def cuts74526 : List PrefixCut := [⟨64,164842033,164842128⟩]
theorem checked74526 : checkPrefixCuts (2^48) 9772204033 10 Manual.Count131072.C074526.packed 64 cuts74526 = true := by
 decide +kernel
def cuts74527 : List PrefixCut := [⟨33,85286096,85286144⟩,
⟨64,163630102,163630201⟩]
theorem checked74527 : checkPrefixCuts (2^48) 9772335105 10 Manual.Count131072.C074527.packed 64 cuts74527 = true := by
 decide +kernel
def pointBounds74527 : List (Nat × Nat × Nat) := [(9772402688,116581430875882,116581820836904)]
theorem point_links_checked74527 : (cuts74527.take 1).map (fun c => (9772335105-1+2*2^10*c.k,116581345589786+c.lower,116581735550760+c.upper)) = pointBounds74527 := by
 decide +kernel
def cuts74528 : List PrefixCut := [⟨64,163685518,163685619⟩]
theorem checked74528 : checkPrefixCuts (2^48) 9772466177 10 Manual.Count131072.C074528.packed 64 cuts74528 = true := by
 decide +kernel
def cuts74529 : List PrefixCut := [⟨55,140641617,140641704⟩,
⟨64,164288147,164288247⟩]
theorem checked74529 : checkPrefixCuts (2^48) 9772597249 10 Manual.Count131072.C074529.packed 64 cuts74529 = true := by
 decide +kernel
def pointBounds74529 : List (Nat × Nat × Nat) := [(9772709888,116581813547023,116582203508284)]
theorem point_links_checked74529 : (cuts74529.take 1).map (fun c => (9772597249-1+2*2^10*c.k,116581672905406+c.lower,116582062866580+c.upper)) = pointBounds74529 := by
 decide +kernel
def cuts74530 : List PrefixCut := [⟨64,162413824,162413921⟩]
theorem checked74530 : checkPrefixCuts (2^48) 9772728321 10 Manual.Count131072.C074530.packed 64 cuts74530 = true := by
 decide +kernel
def cuts74531 : List PrefixCut := [⟨64,166011845,166011952⟩]
theorem checked74531 : checkPrefixCuts (2^48) 9772859393 10 Manual.Count131072.C074531.packed 64 cuts74531 = true := by
 decide +kernel
def cuts74532 : List PrefixCut := [⟨13,32747041,32747061⟩,
⟨64,161459040,161459139⟩]
theorem checked74532 : checkPrefixCuts (2^48) 9772990465 10 Manual.Count131072.C074532.packed 64 cuts74532 = true := by
 decide +kernel
def pointBounds74532 : List (Nat × Nat × Nat) := [(9773017088,116582198366263,116582588327761)]
theorem point_links_checked74532 : (cuts74532.take 1).map (fun c => (9772990465-1+2*2^10*c.k,116582165619222+c.lower,116582555580700+c.upper)) = pointBounds74532 := by
 decide +kernel
def cuts74533 : List PrefixCut := [⟨64,165373783,165373877⟩]
theorem checked74533 : checkPrefixCuts (2^48) 9773121537 10 Manual.Count131072.C074533.packed 64 cuts74533 = true := by
 decide +kernel
def cuts74534 : List PrefixCut := [⟨35,90692547,90692601⟩,
⟨64,166897972,166898069⟩]
theorem checked74534 : checkPrefixCuts (2^48) 9773252609 10 Manual.Count131072.C074534.packed 64 cuts74534 = true := by
 decide +kernel
def pointBounds74534 : List (Nat × Nat × Nat) := [(9773324288,116582583144592,116582973106317)]
theorem point_links_checked74534 : (cuts74534.take 1).map (fun c => (9773252609-1+2*2^10*c.k,116582492452045+c.lower,116582882413716+c.upper)) = pointBounds74534 := by
 decide +kernel
def cuts74535 : List PrefixCut := [⟨64,164678134,164678232⟩]
theorem checked74535 : checkPrefixCuts (2^48) 9773383681 10 Manual.Count131072.C074535.packed 64 cuts74535 = true := by
 decide +kernel
def cuts74536 : List PrefixCut := [⟨57,146129115,146129201⟩,
⟨64,164560728,164560826⟩]
theorem checked74536 : checkPrefixCuts (2^48) 9773514753 10 Manual.Count131072.C074536.packed 64 cuts74536 = true := by
 decide +kernel
def pointBounds74536 : List (Nat × Nat × Nat) := [(9773631488,116582970157266,116583360119218)]
theorem point_links_checked74536 : (cuts74536.take 1).map (fun c => (9773514753-1+2*2^10*c.k,116582824028151+c.lower,116583213990017+c.upper)) = pointBounds74536 := by
 decide +kernel
def cuts74537 : List PrefixCut := [⟨64,164184133,164184234⟩]
theorem checked74537 : checkPrefixCuts (2^48) 9773645825 10 Manual.Count131072.C074537.packed 64 cuts74537 = true := by
 decide +kernel
def cuts74538 : List PrefixCut := [⟨64,165074698,165074793⟩]
theorem checked74538 : checkPrefixCuts (2^48) 9773776897 10 Manual.Count131072.C074538.packed 64 cuts74538 = true := by
 decide +kernel
def cuts74539 : List PrefixCut := [⟨15,37150139,37150162⟩,
⟨64,163690157,163690248⟩]
theorem checked74539 : checkPrefixCuts (2^48) 9773907969 10 Manual.Count131072.C074539.packed 64 cuts74539 = true := by
 decide +kernel
def pointBounds74539 : List (Nat × Nat × Nat) := [(9773938688,116583354997849,116583744960032)]
theorem point_links_checked74539 : (cuts74539.take 1).map (fun c => (9773907969-1+2*2^10*c.k,116583317847710+c.lower,116583707809870+c.upper)) = pointBounds74539 := by
 decide +kernel
def cuts74540 : List PrefixCut := [⟨64,167287726,167287821⟩]
theorem checked74540 : checkPrefixCuts (2^48) 9774039041 10 Manual.Count131072.C074540.packed 64 cuts74540 = true := by
 decide +kernel
def cuts74541 : List PrefixCut := [⟨37,95464438,95464494⟩,
⟨64,166479139,166479235⟩]
theorem checked74541 : checkPrefixCuts (2^48) 9774170113 10 Manual.Count131072.C074541.packed 64 cuts74541 = true := by
 decide +kernel
def pointBounds74541 : List (Nat × Nat × Nat) := [(9774245888,116583744290031,116584134252433)]
theorem point_links_checked74541 : (cuts74541.take 1).map (fun c => (9774170113-1+2*2^10*c.k,116583648825593+c.lower,116584038787939+c.upper)) = pointBounds74541 := by
 decide +kernel
def cuts74542 : List PrefixCut := [⟨64,164979449,164979539⟩]
theorem checked74542 : checkPrefixCuts (2^48) 9774301185 10 Manual.Count131072.C074542.packed 64 cuts74542 = true := by
 decide +kernel
def cuts74543 : List PrefixCut := [⟨59,149974142,149974232⟩,
⟨64,162183937,162184035⟩]
theorem checked74543 : checkPrefixCuts (2^48) 9774432257 10 Manual.Count131072.C074543.packed 64 cuts74543 = true := by
 decide +kernel
def pointBounds74543 : List (Nat × Nat × Nat) := [(9774553088,116584130258323,116584520220945)]
theorem point_links_checked74543 : (cuts74543.take 1).map (fun c => (9774432257-1+2*2^10*c.k,116583980284181+c.lower,116584370246713+c.upper)) = pointBounds74543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000141
