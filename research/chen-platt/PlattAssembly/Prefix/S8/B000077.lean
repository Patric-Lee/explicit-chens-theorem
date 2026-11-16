import PlattAssemblyKernel
import PlattCertificates.Count131072.C072464
import PlattCertificates.Count131072.C072465
import PlattCertificates.Count131072.C072466
import PlattCertificates.Count131072.C072467
import PlattCertificates.Count131072.C072468
import PlattCertificates.Count131072.C072469
import PlattCertificates.Count131072.C072470
import PlattCertificates.Count131072.C072471
import PlattCertificates.Count131072.C072472
import PlattCertificates.Count131072.C072473
import PlattCertificates.Count131072.C072474
import PlattCertificates.Count131072.C072475
import PlattCertificates.Count131072.C072476
import PlattCertificates.Count131072.C072477
import PlattCertificates.Count131072.C072478
import PlattCertificates.Count131072.C072479
import PlattCertificates.Count131072.C072480
import PlattCertificates.Count131072.C072481
import PlattCertificates.Count131072.C072482
import PlattCertificates.Count131072.C072483
import PlattCertificates.Count131072.C072484
import PlattCertificates.Count131072.C072485
import PlattCertificates.Count131072.C072486
import PlattCertificates.Count131072.C072487
import PlattCertificates.Count131072.C072488
import PlattCertificates.Count131072.C072489
import PlattCertificates.Count131072.C072490
import PlattCertificates.Count131072.C072491
import PlattCertificates.Count131072.C072492
import PlattCertificates.Count131072.C072493
import PlattCertificates.Count131072.C072494
import PlattCertificates.Count131072.C072495
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72464 : List PrefixCut := [⟨7,17892222,17892234⟩,
⟨64,168227324,168227427⟩]
theorem checked72464 : checkPrefixCuts (2^48) 9501933569 10 Manual.Count131072.C072464.packed 64 cuts72464 = true := by
 decide +kernel
def pointBounds72464 : List (Nat × Nat × Nat) := [(9501947904,116237744773358,116238134529348)]
theorem point_links_checked72464 : (cuts72464.take 1).map (fun c => (9501933569-1+2*2^10*c.k,116237726881136+c.lower,116238116637114+c.upper)) = pointBounds72464 := by
 decide +kernel
def cuts72465 : List PrefixCut := [⟨64,168876698,168876798⟩]
theorem checked72465 : checkPrefixCuts (2^48) 9502064641 10 Manual.Count131072.C072465.packed 64 cuts72465 = true := by
 decide +kernel
def cuts72466 : List PrefixCut := [⟨24,61169459,61169494⟩,
⟨64,169081706,169081807⟩]
theorem checked72466 : checkPrefixCuts (2^48) 9502195713 10 Manual.Count131072.C072466.packed 64 cuts72466 = true := by
 decide +kernel
def pointBounds72466 : List (Nat × Nat × Nat) := [(9502244864,116238125154617,116238514910833)]
theorem point_links_checked72466 : (cuts72466.take 1).map (fun c => (9502195713-1+2*2^10*c.k,116238063985158+c.lower,116238453741339+c.upper)) = pointBounds72466 := by
 decide +kernel
def cuts72467 : List PrefixCut := [⟨64,167065129,167065231⟩]
theorem checked72467 : checkPrefixCuts (2^48) 9502326785 10 Manual.Count131072.C072467.packed 64 cuts72467 = true := by
 decide +kernel
def cuts72468 : List PrefixCut := [⟨41,108857697,108857758⟩,
⟨64,168988196,168988294⟩]
theorem checked72468 : checkPrefixCuts (2^48) 9502457857 10 Manual.Count131072.C072468.packed 64 cuts72468 = true := by
 decide +kernel
def pointBounds72468 : List (Nat × Nat × Nat) := [(9502541824,116238508989690,116238898746135)]
theorem point_links_checked72468 : (cuts72468.take 1).map (fun c => (9502457857-1+2*2^10*c.k,116238400131993+c.lower,116238789888377+c.upper)) = pointBounds72468 := by
 decide +kernel
def cuts72469 : List PrefixCut := [⟨64,166616217,166616311⟩]
theorem checked72469 : checkPrefixCuts (2^48) 9502588929 10 Manual.Count131072.C072469.packed 64 cuts72469 = true := by
 decide +kernel
def cuts72470 : List PrefixCut := [⟨58,153551478,153551565⟩,
⟨64,168716953,168717047⟩]
theorem checked72470 : checkPrefixCuts (2^48) 9502720001 10 Manual.Count131072.C072470.packed 64 cuts72470 = true := by
 decide +kernel
def pointBounds72470 : List (Nat × Nat × Nat) := [(9502838784,116238889287884,116239279044547)]
theorem point_links_checked72470 : (cuts72470.take 1).map (fun c => (9502720001-1+2*2^10*c.k,116238735736406+c.lower,116239125492982+c.upper)) = pointBounds72470 := by
 decide +kernel
def cuts72471 : List PrefixCut := [⟨64,168299949,168300047⟩]
theorem checked72471 : checkPrefixCuts (2^48) 9502851073 10 Manual.Count131072.C072471.packed 64 cuts72471 = true := by
 decide +kernel
def cuts72472 : List PrefixCut := [⟨64,168149527,168149632⟩]
theorem checked72472 : checkPrefixCuts (2^48) 9502982145 10 Manual.Count131072.C072472.packed 64 cuts72472 = true := by
 decide +kernel
def cuts72473 : List PrefixCut := [⟨12,31751772,31751793⟩,
⟨64,169420826,169420931⟩]
theorem checked72473 : checkPrefixCuts (2^48) 9503113217 10 Manual.Count131072.C072473.packed 64 cuts72473 = true := by
 decide +kernel
def pointBounds72473 : List (Nat × Nat × Nat) := [(9503137792,116239272654607,116239662411501)]
theorem point_links_checked72473 : (cuts72473.take 1).map (fun c => (9503113217-1+2*2^10*c.k,116239240902835+c.lower,116239630659708+c.upper)) = pointBounds72473 := by
 decide +kernel
def cuts72474 : List PrefixCut := [⟨64,170692084,170692192⟩]
theorem checked72474 : checkPrefixCuts (2^48) 9503244289 10 Manual.Count131072.C072474.packed 64 cuts72474 = true := by
 decide +kernel
def cuts72475 : List PrefixCut := [⟨30,78518157,78518204⟩,
⟨64,167787146,167787247⟩]
theorem checked72475 : checkPrefixCuts (2^48) 9503375361 10 Manual.Count131072.C072475.packed 64 cuts72475 = true := by
 decide +kernel
def pointBounds72475 : List (Nat × Nat × Nat) := [(9503436800,116239659533902,116240049291035)]
theorem point_links_checked72475 : (cuts72475.take 1).map (fun c => (9503375361-1+2*2^10*c.k,116239581015745+c.lower,116239970772831+c.upper)) = pointBounds72475 := by
 decide +kernel
def cuts72476 : List PrefixCut := [⟨64,170391207,170391309⟩]
theorem checked72476 : checkPrefixCuts (2^48) 9503506433 10 Manual.Count131072.C072476.packed 64 cuts72476 = true := by
 decide +kernel
def cuts72477 : List PrefixCut := [⟨48,126733034,126733109⟩,
⟨64,169470707,169470808⟩]
theorem checked72477 : checkPrefixCuts (2^48) 9503637505 10 Manual.Count131072.C072477.packed 64 cuts72477 = true := by
 decide +kernel
def pointBounds72477 : List (Nat × Nat × Nat) := [(9503735808,116240045927132,116240435684496)]
theorem point_links_checked72477 : (cuts72477.take 1).map (fun c => (9503637505-1+2*2^10*c.k,116239919194098+c.lower,116240308951387+c.upper)) = pointBounds72477 := by
 decide +kernel
def cuts72478 : List PrefixCut := [⟨64,169527613,169527711⟩]
theorem checked72478 : checkPrefixCuts (2^48) 9503768577 10 Manual.Count131072.C072478.packed 64 cuts72478 = true := by
 decide +kernel
def cuts72479 : List PrefixCut := [⟨64,168192543,168192638⟩]
theorem checked72479 : checkPrefixCuts (2^48) 9503899649 10 Manual.Count131072.C072479.packed 64 cuts72479 = true := by
 decide +kernel
def cuts72480 : List PrefixCut := [⟨2,5419794,5419798⟩,
⟨64,168190216,168190316⟩]
theorem checked72480 : checkPrefixCuts (2^48) 9504030721 10 Manual.Count131072.C072480.packed 64 cuts72480 = true := by
 decide +kernel
def pointBounds72480 : List (Nat × Nat × Nat) := [(9504034816,116240431804755,116240821562342)]
theorem point_links_checked72480 : (cuts72480.take 1).map (fun c => (9504030721-1+2*2^10*c.k,116240426384961+c.lower,116240816142544+c.upper)) = pointBounds72480 := by
 decide +kernel
def cuts72481 : List PrefixCut := [⟨64,169254050,169254150⟩]
theorem checked72481 : checkPrefixCuts (2^48) 9504161793 10 Manual.Count131072.C072481.packed 64 cuts72481 = true := by
 decide +kernel
def cuts72482 : List PrefixCut := [⟨20,54818273,54818302⟩,
⟨64,169192508,169192606⟩]
theorem checked72482 : checkPrefixCuts (2^48) 9504292865 10 Manual.Count131072.C072482.packed 64 cuts72482 = true := by
 decide +kernel
def pointBounds72482 : List (Nat × Nat × Nat) := [(9504333824,116240818647500,116241208405312)]
theorem point_links_checked72482 : (cuts72482.take 1).map (fun c => (9504292865-1+2*2^10*c.k,116240763829227+c.lower,116241153587010+c.upper)) = pointBounds72482 := by
 decide +kernel
def cuts72483 : List PrefixCut := [⟨64,170967054,170967161⟩]
theorem checked72483 : checkPrefixCuts (2^48) 9504423937 10 Manual.Count131072.C072483.packed 64 cuts72483 = true := by
 decide +kernel
def cuts72484 : List PrefixCut := [⟨38,98883199,98883255⟩,
⟨64,166344827,166344921⟩]
theorem checked72484 : checkPrefixCuts (2^48) 9504555009 10 Manual.Count131072.C072484.packed 64 cuts72484 = true := by
 decide +kernel
def pointBounds72484 : List (Nat × Nat × Nat) := [(9504632832,116241202871988,116241592630032)]
theorem point_links_checked72484 : (cuts72484.take 1).map (fun c => (9504555009-1+2*2^10*c.k,116241103988789+c.lower,116241493746777+c.upper)) = pointBounds72484 := by
 decide +kernel
def cuts72485 : List PrefixCut := [⟨64,168000947,168001042⟩]
theorem checked72485 : checkPrefixCuts (2^48) 9504686081 10 Manual.Count131072.C072485.packed 64 cuts72485 = true := by
 decide +kernel
def cuts72486 : List PrefixCut := [⟨56,148216775,148216868⟩,
⟨64,169331227,169331333⟩]
theorem checked72486 : checkPrefixCuts (2^48) 9504817153 10 Manual.Count131072.C072486.packed 64 cuts72486 = true := by
 decide +kernel
def pointBounds72486 : List (Nat × Nat × Nat) := [(9504931840,116241586551338,116241976309608)]
theorem point_links_checked72486 : (cuts72486.take 1).map (fun c => (9504817153-1+2*2^10*c.k,116241438334563+c.lower,116241828092740+c.upper)) = pointBounds72486 := by
 decide +kernel
def cuts72487 : List PrefixCut := [⟨64,168351654,168351757⟩]
theorem checked72487 : checkPrefixCuts (2^48) 9504948225 10 Manual.Count131072.C072487.packed 64 cuts72487 = true := by
 decide +kernel
def cuts72488 : List PrefixCut := [⟨64,167993985,167994080⟩]
theorem checked72488 : checkPrefixCuts (2^48) 9505079297 10 Manual.Count131072.C072488.packed 64 cuts72488 = true := by
 decide +kernel
def cuts72489 : List PrefixCut := [⟨10,27391714,27391730⟩,
⟨64,169413055,169413160⟩]
theorem checked72489 : checkPrefixCuts (2^48) 9505210369 10 Manual.Count131072.C072489.packed 64 cuts72489 = true := by
 decide +kernel
def pointBounds72489 : List (Nat × Nat × Nat) := [(9505230848,116241971403143,116242361161640)]
theorem point_links_checked72489 : (cuts72489.take 1).map (fun c => (9505210369-1+2*2^10*c.k,116241944011429+c.lower,116242333769910+c.upper)) = pointBounds72489 := by
 decide +kernel
def cuts72490 : List PrefixCut := [⟨64,168344684,168344780⟩]
theorem checked72490 : checkPrefixCuts (2^48) 9505341441 10 Manual.Count131072.C072490.packed 64 cuts72490 = true := by
 decide +kernel
def cuts72491 : List PrefixCut := [⟨28,73762966,73763012⟩,
⟨64,169289933,169290033⟩]
theorem checked72491 : checkPrefixCuts (2^48) 9505472513 10 Manual.Count131072.C072491.packed 64 cuts72491 = true := by
 decide +kernel
def pointBounds72491 : List (Nat × Nat × Nat) := [(9505529856,116242355532134,116242745290862)]
theorem point_links_checked72491 : (cuts72491.take 1).map (fun c => (9505472513-1+2*2^10*c.k,116242281769168+c.lower,116242671527850+c.upper)) = pointBounds72491 := by
 decide +kernel
def cuts72492 : List PrefixCut := [⟨64,170116716,170116827⟩]
theorem checked72492 : checkPrefixCuts (2^48) 9505603585 10 Manual.Count131072.C072492.packed 64 cuts72492 = true := by
 decide +kernel
def cuts72493 : List PrefixCut := [⟨46,119539261,119539335⟩,
⟨64,167212506,167212609⟩]
theorem checked72493 : checkPrefixCuts (2^48) 9505734657 10 Manual.Count131072.C072493.packed 64 cuts72493 = true := by
 decide +kernel
def pointBounds72493 : List (Nat × Nat × Nat) := [(9505828864,116242740715078,116243130474045)]
theorem point_links_checked72493 : (cuts72493.take 1).map (fun c => (9505734657-1+2*2^10*c.k,116242621175817+c.lower,116243010934710+c.upper)) = pointBounds72493 := by
 decide +kernel
def cuts72494 : List PrefixCut := [⟨64,166854885,166854983⟩]
theorem checked72494 : checkPrefixCuts (2^48) 9505865729 10 Manual.Count131072.C072494.packed 64 cuts72494 = true := by
 decide +kernel
def cuts72495 : List PrefixCut := [⟨64,169428657,169428756⟩]
theorem checked72495 : checkPrefixCuts (2^48) 9505996801 10 Manual.Count131072.C072495.packed 64 cuts72495 = true := by
 decide +kernel
def pointBounds72495 : List (Nat × Nat × Nat) := [(9506127872,116243124671865,116243514431058)]
theorem point_links_checked72495 : (cuts72495.take 1).map (fun c => (9505996801-1+2*2^10*c.k,116242955243208+c.lower,116243345002302+c.upper)) = pointBounds72495 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000077
