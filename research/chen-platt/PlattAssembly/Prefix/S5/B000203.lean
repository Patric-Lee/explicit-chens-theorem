import PlattAssemblyKernel
import PlattCertificates.Count131072.C046496
import PlattCertificates.Count131072.C046497
import PlattCertificates.Count131072.C046498
import PlattCertificates.Count131072.C046499
import PlattCertificates.Count131072.C046500
import PlattCertificates.Count131072.C046501
import PlattCertificates.Count131072.C046502
import PlattCertificates.Count131072.C046503
import PlattCertificates.Count131072.C046504
import PlattCertificates.Count131072.C046505
import PlattCertificates.Count131072.C046506
import PlattCertificates.Count131072.C046507
import PlattCertificates.Count131072.C046508
import PlattCertificates.Count131072.C046509
import PlattCertificates.Count131072.C046510
import PlattCertificates.Count131072.C046511
import PlattCertificates.Count131072.C046512
import PlattCertificates.Count131072.C046513
import PlattCertificates.Count131072.C046514
import PlattCertificates.Count131072.C046515
import PlattCertificates.Count131072.C046516
import PlattCertificates.Count131072.C046517
import PlattCertificates.Count131072.C046518
import PlattCertificates.Count131072.C046519
import PlattCertificates.Count131072.C046520
import PlattCertificates.Count131072.C046521
import PlattCertificates.Count131072.C046522
import PlattCertificates.Count131072.C046523
import PlattCertificates.Count131072.C046524
import PlattCertificates.Count131072.C046525
import PlattCertificates.Count131072.C046526
import PlattCertificates.Count131072.C046527
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000203
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46496 : List PrefixCut := [⟨64,271998067,271998226⟩]
theorem checked46496 : checkPrefixCuts (2^48) 6098255873 10 Manual.Count131072.C046496.packed 64 cuts46496 = true := by
 decide +kernel
def cuts46497 : List PrefixCut := [⟨6,26308683,26308697⟩,
⟨64,270653730,270653879⟩]
theorem checked46497 : checkPrefixCuts (2^48) 6098386945 10 Manual.Count131072.C046497.packed 64 cuts46497 = true := by
 decide +kernel
def pointBounds46497 : List (Nat × Nat × Nat) := [(6098399232,110751487859582,110751874464066)]
theorem point_links_checked46497 : (cuts46497.take 1).map (fun c => (6098386945-1+2*2^10*c.k,110751461550899+c.lower,110751848155369+c.upper)) = pointBounds46497 := by
 decide +kernel
def cuts46498 : List PrefixCut := [⟨36,151801696,151801787⟩,
⟨64,268340198,268340358⟩]
theorem checked46498 : checkPrefixCuts (2^48) 6098518017 10 Manual.Count131072.C046498.packed 64 cuts46498 = true := by
 decide +kernel
def pointBounds46498 : List (Nat × Nat × Nat) := [(6098591744,110751884006325,110752270611035)]
theorem point_links_checked46498 : (cuts46498.take 1).map (fun c => (6098518017-1+2*2^10*c.k,110751732204629+c.lower,110752118809248+c.upper)) = pointBounds46498 := by
 decide +kernel
def cuts46499 : List PrefixCut := [⟨64,270503618,270503773⟩]
theorem checked46499 : checkPrefixCuts (2^48) 6098649089 10 Manual.Count131072.C046499.packed 64 cuts46499 = true := by
 decide +kernel
def cuts46500 : List PrefixCut := [⟨2,8769001,8769006⟩,
⟨64,268559398,268559556⟩]
theorem checked46500 : checkPrefixCuts (2^48) 6098780161 10 Manual.Count131072.C046500.packed 64 cuts46500 = true := by
 decide +kernel
def pointBounds46500 : List (Nat × Nat × Nat) := [(6098784256,110752279817446,110752666422385)]
theorem point_links_checked46500 : (cuts46500.take 1).map (fun c => (6098780161-1+2*2^10*c.k,110752271048445+c.lower,110752657653379+c.upper)) = pointBounds46500 := by
 decide +kernel
def cuts46501 : List PrefixCut := [⟨32,134254471,134254547⟩,
⟨64,268738249,268738405⟩]
theorem checked46501 : checkPrefixCuts (2^48) 6098911233 10 Manual.Count131072.C046501.packed 64 cuts46501 = true := by
 decide +kernel
def pointBounds46501 : List (Nat × Nat × Nat) := [(6098976768,110752673862314,110753060467482)]
theorem point_links_checked46501 : (cuts46501.take 1).map (fun c => (6098911233-1+2*2^10*c.k,110752539607843+c.lower,110752926212935+c.upper)) = pointBounds46501 := by
 decide +kernel
def cuts46502 : List PrefixCut := [⟨62,262179244,262179391⟩,
⟨64,270024692,270024844⟩]
theorem checked46502 : checkPrefixCuts (2^48) 6099042305 10 Manual.Count131072.C046502.packed 64 cuts46502 = true := by
 decide +kernel
def pointBounds46502 : List (Nat × Nat × Nat) := [(6099169280,110753070525336,110753457130731)]
theorem point_links_checked46502 : (cuts46502.take 1).map (fun c => (6099042305-1+2*2^10*c.k,110752808346092+c.lower,110753194951340+c.upper)) = pointBounds46502 := by
 decide +kernel
def cuts46503 : List PrefixCut := [⟨64,264988604,264988762⟩]
theorem checked46503 : checkPrefixCuts (2^48) 6099173377 10 Manual.Count131072.C046503.packed 64 cuts46503 = true := by
 decide +kernel
def cuts46504 : List PrefixCut := [⟨28,116755624,116755693⟩,
⟨64,265859721,265859879⟩]
theorem checked46504 : checkPrefixCuts (2^48) 6099304449 10 Manual.Count131072.C046504.packed 64 cuts46504 = true := by
 decide +kernel
def pointBounds46504 : List (Nat × Nat × Nat) := [(6099361792,110753460115012,110753846720639)]
theorem point_links_checked46504 : (cuts46504.take 1).map (fun c => (6099304449-1+2*2^10*c.k,110753343359388+c.lower,110753729964946+c.upper)) = pointBounds46504 := by
 decide +kernel
def cuts46505 : List PrefixCut := [⟨58,244903443,244903581⟩,
⟨64,271345531,271345684⟩]
theorem checked46505 : checkPrefixCuts (2^48) 6099435521 10 Manual.Count131072.C046505.packed 64 cuts46505 = true := by
 decide +kernel
def pointBounds46505 : List (Nat × Nat × Nat) := [(6099554304,110753854122552,110754240728406)]
theorem point_links_checked46505 : (cuts46505.take 1).map (fun c => (6099435521-1+2*2^10*c.k,110753609219109+c.lower,110753995824825+c.upper)) = pointBounds46505 := by
 decide +kernel
def cuts46506 : List PrefixCut := [⟨64,269632292,269632447⟩]
theorem checked46506 : checkPrefixCuts (2^48) 6099566593 10 Manual.Count131072.C046506.packed 64 cuts46506 = true := by
 decide +kernel
def cuts46507 : List PrefixCut := [⟨24,102120057,102120111⟩,
⟨64,271564604,271564755⟩]
theorem checked46507 : checkPrefixCuts (2^48) 6099697665 10 Manual.Count131072.C046507.packed 64 cuts46507 = true := by
 decide +kernel
def pointBounds46507 : List (Nat × Nat × Nat) := [(6099746816,110754252316989,110754638923067)]
theorem point_links_checked46507 : (cuts46507.take 1).map (fun c => (6099697665-1+2*2^10*c.k,110754150196932+c.lower,110754536802956+c.upper)) = pointBounds46507 := by
 decide +kernel
def cuts46508 : List PrefixCut := [⟨54,228645016,228645143⟩,
⟨64,271420325,271420478⟩]
theorem checked46508 : checkPrefixCuts (2^48) 6099828737 10 Manual.Count131072.C046508.packed 64 cuts46508 = true := by
 decide +kernel
def pointBounds46508 : List (Nat × Nat × Nat) := [(6099939328,110754650406552,110755037012854)]
theorem point_links_checked46508 : (cuts46508.take 1).map (fun c => (6099828737-1+2*2^10*c.k,110754421761536+c.lower,110754808367711+c.upper)) = pointBounds46508 := by
 decide +kernel
def cuts46509 : List PrefixCut := [⟨64,267261634,267261789⟩]
theorem checked46509 : checkPrefixCuts (2^48) 6099959809 10 Manual.Count131072.C046509.packed 64 cuts46509 = true := by
 decide +kernel
def cuts46510 : List PrefixCut := [⟨20,82779788,82779838⟩,
⟨64,269009256,269009414⟩]
theorem checked46510 : checkPrefixCuts (2^48) 6100090881 10 Manual.Count131072.C046510.packed 64 cuts46510 = true := by
 decide +kernel
def pointBounds46510 : List (Nat × Nat × Nat) := [(6100131840,110755043223283,110755429829816)]
theorem point_links_checked46510 : (cuts46510.take 1).map (fun c => (6100090881-1+2*2^10*c.k,110754960443495+c.lower,110755347049978+c.upper)) = pointBounds46510 := by
 decide +kernel
def cuts46511 : List PrefixCut := [⟨50,204959913,204960032⟩,
⟨64,263927937,263928090⟩]
theorem checked46511 : checkPrefixCuts (2^48) 6100221953 10 Manual.Count131072.C046511.packed 64 cuts46511 = true := by
 decide +kernel
def pointBounds46511 : List (Nat × Nat × Nat) := [(6100324352,110755434412664,110755821019424)]
theorem point_links_checked46511 : (cuts46511.take 1).map (fun c => (6100221953-1+2*2^10*c.k,110755229452751+c.lower,110755616059392+c.upper)) = pointBounds46511 := by
 decide +kernel
def cuts46512 : List PrefixCut := [⟨64,272735069,272735222⟩]
theorem checked46512 : checkPrefixCuts (2^48) 6100353025 10 Manual.Count131072.C046512.packed 64 cuts46512 = true := by
 decide +kernel
def cuts46513 : List PrefixCut := [⟨16,67548434,67548472⟩,
⟨64,268299844,268299997⟩]
theorem checked46513 : checkPrefixCuts (2^48) 6100484097 10 Manual.Count131072.C046513.packed 64 cuts46513 = true := by
 decide +kernel
def pointBounds46513 : List (Nat × Nat × Nat) := [(6100516864,110755833664191,110756220271176)]
theorem point_links_checked46513 : (cuts46513.take 1).map (fun c => (6100484097-1+2*2^10*c.k,110755766115757+c.lower,110756152722704+c.upper)) = pointBounds46513 := by
 decide +kernel
def cuts46514 : List PrefixCut := [⟨46,196180533,196180640⟩,
⟨64,272492657,272492805⟩]
theorem checked46514 : checkPrefixCuts (2^48) 6100615169 10 Manual.Count131072.C046514.packed 64 cuts46514 = true := by
 decide +kernel
def pointBounds46514 : List (Nat × Nat × Nat) := [(6100709376,110756230596134,110756617203341)]
theorem point_links_checked46514 : (cuts46514.take 1).map (fun c => (6100615169-1+2*2^10*c.k,110756034415601+c.lower,110756421022701+c.upper)) = pointBounds46514 := by
 decide +kernel
def cuts46515 : List PrefixCut := [⟨64,262982528,262982683⟩]
theorem checked46515 : checkPrefixCuts (2^48) 6100746241 10 Manual.Count131072.C046515.packed 64 cuts46515 = true := by
 decide +kernel
def cuts46516 : List PrefixCut := [⟨12,50104451,50104479⟩,
⟨64,269666623,269666782⟩]
theorem checked46516 : checkPrefixCuts (2^48) 6100877313 10 Manual.Count131072.C046516.packed 64 cuts46516 = true := by
 decide +kernel
def pointBounds46516 : List (Nat × Nat × Nat) := [(6100901888,110756619995237,110757006602668)]
theorem point_links_checked46516 : (cuts46516.take 1).map (fun c => (6100877313-1+2*2^10*c.k,110756569890786+c.lower,110756956498189+c.upper)) = pointBounds46516 := by
 decide +kernel
def cuts46517 : List PrefixCut := [⟨42,176883411,176883515⟩,
⟨64,269061095,269061251⟩]
theorem checked46517 : checkPrefixCuts (2^48) 6101008385 10 Manual.Count131072.C046517.packed 64 cuts46517 = true := by
 decide +kernel
def pointBounds46517 : List (Nat × Nat × Nat) := [(6101094400,110757016440820,110757403048486)]
theorem point_links_checked46517 : (cuts46517.take 1).map (fun c => (6101008385-1+2*2^10*c.k,110756839557409+c.lower,110757226164971+c.upper)) = pointBounds46517 := by
 decide +kernel
def cuts46518 : List PrefixCut := [⟨64,266102695,266102849⟩]
theorem checked46518 : checkPrefixCuts (2^48) 6101139457 10 Manual.Count131072.C046518.packed 64 cuts46518 = true := by
 decide +kernel
def cuts46519 : List PrefixCut := [⟨8,33262437,33262456⟩,
⟨64,264620751,264620906⟩]
theorem checked46519 : checkPrefixCuts (2^48) 6101270529 10 Manual.Count131072.C046519.packed 64 cuts46519 = true := by
 decide +kernel
def pointBounds46519 : List (Nat × Nat × Nat) := [(6101286912,110757407983636,110757794591527)]
theorem point_links_checked46519 : (cuts46519.take 1).map (fun c => (6101270529-1+2*2^10*c.k,110757374721199+c.lower,110757761329071+c.upper)) = pointBounds46519 := by
 decide +kernel
def cuts46520 : List PrefixCut := [⟨38,160172163,160172253⟩,
⟨64,266091315,266091468⟩]
theorem checked46520 : checkPrefixCuts (2^48) 6101401601 10 Manual.Count131072.C046520.packed 64 cuts46520 = true := by
 decide +kernel
def pointBounds46520 : List (Nat × Nat × Nat) := [(6101479424,110757799514113,110758186122230)]
theorem point_links_checked46520 : (cuts46520.take 1).map (fun c => (6101401601-1+2*2^10*c.k,110757639341950+c.lower,110758025949977+c.upper)) = pointBounds46520 := by
 decide +kernel
def cuts46521 : List PrefixCut := [⟨64,268299866,268300021⟩]
theorem checked46521 : checkPrefixCuts (2^48) 6101532673 10 Manual.Count131072.C046521.packed 64 cuts46521 = true := by
 decide +kernel
def cuts46522 : List PrefixCut := [⟨4,16007392,16007402⟩,
⟨64,267740534,267740682⟩]
theorem checked46522 : checkPrefixCuts (2^48) 6101663745 10 Manual.Count131072.C046522.packed 64 cuts46522 = true := by
 decide +kernel
def pointBounds46522 : List (Nat × Nat × Nat) := [(6101671936,110758189740523,110758576348868)]
theorem point_links_checked46522 : (cuts46522.take 1).map (fun c => (6101663745-1+2*2^10*c.k,110758173733131+c.lower,110758560341466+c.upper)) = pointBounds46522 := by
 decide +kernel
def cuts46523 : List PrefixCut := [⟨34,142955601,142955683⟩,
⟨64,267965451,267965609⟩]
theorem checked46523 : checkPrefixCuts (2^48) 6101794817 10 Manual.Count131072.C046523.packed 64 cuts46523 = true := by
 decide +kernel
def pointBounds46523 : List (Nat × Nat × Nat) := [(6101864448,110758584429266,110758971037831)]
theorem point_links_checked46523 : (cuts46523.take 1).map (fun c => (6101794817-1+2*2^10*c.k,110758441473665+c.lower,110758828082148+c.upper)) = pointBounds46523 := by
 decide +kernel
def cuts46524 : List PrefixCut := [⟨64,270358368,270358519⟩]
theorem checked46524 : checkPrefixCuts (2^48) 6101925889 10 Manual.Count131072.C046524.packed 64 cuts46524 = true := by
 decide +kernel
def pointBounds46524 : List (Nat × Nat × Nat) := [(6102056960,110758979797484,110759366406276)]
theorem point_links_checked46524 : (cuts46524.take 1).map (fun c => (6101925889-1+2*2^10*c.k,110758709439116+c.lower,110759096047757+c.upper)) = pointBounds46524 := by
 decide +kernel
def cuts46525 : List PrefixCut := [⟨64,267492623,267492782⟩]
theorem checked46525 : checkPrefixCuts (2^48) 6102056961 10 Manual.Count131072.C046525.packed 64 cuts46525 = true := by
 decide +kernel
def cuts46526 : List PrefixCut := [⟨30,126202512,126202585⟩,
⟨64,268086562,268086715⟩]
theorem checked46526 : checkPrefixCuts (2^48) 6102188033 10 Manual.Count131072.C046526.packed 64 cuts46526 = true := by
 decide +kernel
def pointBounds46526 : List (Nat × Nat × Nat) := [(6102249472,110759373492619,110759760101643)]
theorem point_links_checked46526 : (cuts46526.take 1).map (fun c => (6102188033-1+2*2^10*c.k,110759247290107+c.lower,110759633899058+c.upper)) = pointBounds46526 := by
 decide +kernel
def cuts46527 : List PrefixCut := [⟨60,252259976,252260120⟩,
⟨64,269879699,269879854⟩]
theorem checked46527 : checkPrefixCuts (2^48) 6102319105 10 Manual.Count131072.C046527.packed 64 cuts46527 = true := by
 decide +kernel
def pointBounds46527 : List (Nat × Nat × Nat) := [(6102441984,110759767636645,110760154245893)]
theorem point_links_checked46527 : (cuts46527.take 1).map (fun c => (6102319105-1+2*2^10*c.k,110759515376669+c.lower,110759901985773+c.upper)) = pointBounds46527 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000203
