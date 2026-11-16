import PlattAssemblyKernel
import PlattCertificates.Count131072.C070480
import PlattCertificates.Count131072.C070481
import PlattCertificates.Count131072.C070482
import PlattCertificates.Count131072.C070483
import PlattCertificates.Count131072.C070484
import PlattCertificates.Count131072.C070485
import PlattCertificates.Count131072.C070486
import PlattCertificates.Count131072.C070487
import PlattCertificates.Count131072.C070488
import PlattCertificates.Count131072.C070489
import PlattCertificates.Count131072.C070490
import PlattCertificates.Count131072.C070491
import PlattCertificates.Count131072.C070492
import PlattCertificates.Count131072.C070493
import PlattCertificates.Count131072.C070494
import PlattCertificates.Count131072.C070495
import PlattCertificates.Count131072.C070496
import PlattCertificates.Count131072.C070497
import PlattCertificates.Count131072.C070498
import PlattCertificates.Count131072.C070499
import PlattCertificates.Count131072.C070500
import PlattCertificates.Count131072.C070501
import PlattCertificates.Count131072.C070502
import PlattCertificates.Count131072.C070503
import PlattCertificates.Count131072.C070504
import PlattCertificates.Count131072.C070505
import PlattCertificates.Count131072.C070506
import PlattCertificates.Count131072.C070507
import PlattCertificates.Count131072.C070508
import PlattCertificates.Count131072.C070509
import PlattCertificates.Count131072.C070510
import PlattCertificates.Count131072.C070511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70480 : List PrefixCut := [⟨64,172808573,172808684⟩]
theorem checked70480 : checkPrefixCuts (2^48) 9241886721 10 Manual.Count131072.C070480.packed 64 cuts70480 = true := by
 decide +kernel
def cuts70481 : List PrefixCut := [⟨64,173628418,173628521⟩]
theorem checked70481 : checkPrefixCuts (2^48) 9242017793 10 Manual.Count131072.C070481.packed 64 cuts70481 = true := by
 decide +kernel
def cuts70482 : List PrefixCut := [⟨7,18821526,18821537⟩,
⟨64,173199587,173199685⟩]
theorem checked70482 : checkPrefixCuts (2^48) 9242148865 10 Manual.Count131072.C070482.packed 64 cuts70482 = true := by
 decide +kernel
def pointBounds70482 : List (Nat × Nat × Nat) := [(9242163200,115897904649504,115898294204233)]
theorem point_links_checked70482 : (cuts70482.take 1).map (fun c => (9242148865-1+2*2^10*c.k,115897885827978+c.lower,115898275382696+c.upper)) = pointBounds70482 := by
 decide +kernel
def cuts70483 : List PrefixCut := [⟨64,174750346,174750446⟩]
theorem checked70483 : checkPrefixCuts (2^48) 9242279937 10 Manual.Count131072.C070483.packed 64 cuts70483 = true := by
 decide +kernel
def cuts70484 : List PrefixCut := [⟨21,56919711,56919743⟩,
⟨64,173529668,173529769⟩]
theorem checked70484 : checkPrefixCuts (2^48) 9242411009 10 Manual.Count131072.C070484.packed 64 cuts70484 = true := by
 decide +kernel
def pointBounds70484 : List (Nat × Nat × Nat) := [(9242454016,115898290697622,115898680252570)]
theorem point_links_checked70484 : (cuts70484.take 1).map (fun c => (9242411009-1+2*2^10*c.k,115898233777911+c.lower,115898623332827+c.upper)) = pointBounds70484 := by
 decide +kernel
def cuts70485 : List PrefixCut := [⟨64,173740385,173740483⟩]
theorem checked70485 : checkPrefixCuts (2^48) 9242542081 10 Manual.Count131072.C070485.packed 64 cuts70485 = true := by
 decide +kernel
def cuts70486 : List PrefixCut := [⟨35,95533331,95533381⟩,
⟨64,173250675,173250775⟩]
theorem checked70486 : checkPrefixCuts (2^48) 9242673153 10 Manual.Count131072.C070486.packed 64 cuts70486 = true := by
 decide +kernel
def pointBounds70486 : List (Nat × Nat × Nat) := [(9242744832,115898676581295,115899066136460)]
theorem point_links_checked70486 : (cuts70486.take 1).map (fun c => (9242673153-1+2*2^10*c.k,115898581047964+c.lower,115898970603079+c.upper)) = pointBounds70486 := by
 decide +kernel
def cuts70487 : List PrefixCut := [⟨64,176263068,176263170⟩]
theorem checked70487 : checkPrefixCuts (2^48) 9242804225 10 Manual.Count131072.C070487.packed 64 cuts70487 = true := by
 decide +kernel
def cuts70488 : List PrefixCut := [⟨49,134601430,134601509⟩,
⟨64,174159352,174159455⟩]
theorem checked70488 : checkPrefixCuts (2^48) 9242935297 10 Manual.Count131072.C070488.packed 64 cuts70488 = true := by
 decide +kernel
def pointBounds70488 : List (Nat × Nat × Nat) := [(9243035648,115899065163137,115899454718533)]
theorem point_links_checked70488 : (cuts70488.take 1).map (fun c => (9242935297-1+2*2^10*c.k,115898930561707+c.lower,115899320117024+c.upper)) = pointBounds70488 := by
 decide +kernel
def cuts70489 : List PrefixCut := [⟨64,171233444,171233550⟩]
theorem checked70489 : checkPrefixCuts (2^48) 9243066369 10 Manual.Count131072.C070489.packed 64 cuts70489 = true := by
 decide +kernel
def cuts70490 : List PrefixCut := [⟨63,172357755,172357862⟩,
⟨64,175281117,175281225⟩]
theorem checked70490 : checkPrefixCuts (2^48) 9243197441 10 Manual.Count131072.C070490.packed 64 cuts70490 = true := by
 decide +kernel
def pointBounds70490 : List (Nat × Nat × Nat) := [(9243326464,115899448312258,115899837867891)]
theorem point_links_checked70490 : (cuts70490.take 1).map (fun c => (9243197441-1+2*2^10*c.k,115899275954503+c.lower,115899665510029+c.upper)) = pointBounds70490 := by
 decide +kernel
def cuts70491 : List PrefixCut := [⟨64,174395546,174395644⟩]
theorem checked70491 : checkPrefixCuts (2^48) 9243328513 10 Manual.Count131072.C070491.packed 64 cuts70491 = true := by
 decide +kernel
def cuts70492 : List PrefixCut := [⟨64,175854718,175854817⟩]
theorem checked70492 : checkPrefixCuts (2^48) 9243459585 10 Manual.Count131072.C070492.packed 64 cuts70492 = true := by
 decide +kernel
def cuts70493 : List PrefixCut := [⟨13,36236420,36236442⟩,
⟨64,175730434,175730539⟩]
theorem checked70493 : checkPrefixCuts (2^48) 9243590657 10 Manual.Count131072.C070493.packed 64 cuts70493 = true := by
 decide +kernel
def pointBounds70493 : List (Nat × Nat × Nat) := [(9243617280,115899837722304,115900227278157)]
theorem point_links_checked70493 : (cuts70493.take 1).map (fun c => (9243590657-1+2*2^10*c.k,115899801485884+c.lower,115900191041715+c.upper)) = pointBounds70493 := by
 decide +kernel
def cuts70494 : List PrefixCut := [⟨64,173626874,173626976⟩]
theorem checked70494 : checkPrefixCuts (2^48) 9243721729 10 Manual.Count131072.C070494.packed 64 cuts70494 = true := by
 decide +kernel
def cuts70495 : List PrefixCut := [⟨27,73323271,73323315⟩,
⟨64,173593961,173594063⟩]
theorem checked70495 : checkPrefixCuts (2^48) 9243852801 10 Manual.Count131072.C070495.packed 64 cuts70495 = true := by
 decide +kernel
def pointBounds70495 : List (Nat × Nat × Nat) := [(9243908096,115900224166463,115900613722545)]
theorem point_links_checked70495 : (cuts70495.take 1).map (fun c => (9243852801-1+2*2^10*c.k,115900150843192+c.lower,115900540399230+c.upper)) = pointBounds70495 := by
 decide +kernel
def cuts70496 : List PrefixCut := [⟨64,173408802,173408903⟩]
theorem checked70496 : checkPrefixCuts (2^48) 9243983873 10 Manual.Count131072.C070496.packed 64 cuts70496 = true := by
 decide +kernel
def cuts70497 : List PrefixCut := [⟨41,110316557,110316621⟩,
⟨64,174350253,174350351⟩]
theorem checked70497 : checkPrefixCuts (2^48) 9244114945 10 Manual.Count131072.C070497.packed 64 cuts70497 = true := by
 decide +kernel
def pointBounds70497 : List (Nat × Nat × Nat) := [(9244198912,115900608162512,115900997718817)]
theorem point_links_checked70497 : (cuts70497.take 1).map (fun c => (9244114945-1+2*2^10*c.k,115900497845955+c.lower,115900887402196+c.upper)) = pointBounds70497 := by
 decide +kernel
def cuts70498 : List PrefixCut := [⟨64,174713172,174713274⟩]
theorem checked70498 : checkPrefixCuts (2^48) 9244246017 10 Manual.Count131072.C070498.packed 64 cuts70498 = true := by
 decide +kernel
def cuts70499 : List PrefixCut := [⟨55,151539911,151539993⟩,
⟨64,176385338,176385432⟩]
theorem checked70499 : checkPrefixCuts (2^48) 9244377089 10 Manual.Count131072.C070499.packed 64 cuts70499 = true := by
 decide +kernel
def pointBounds70499 : List (Nat × Nat × Nat) := [(9244489728,115900998449291,115901388005814)]
theorem point_links_checked70499 : (cuts70499.take 1).map (fun c => (9244377089-1+2*2^10*c.k,115900846909380+c.lower,115901236465821+c.upper)) = pointBounds70499 := by
 decide +kernel
def cuts70500 : List PrefixCut := [⟨64,174221041,174221148⟩]
theorem checked70500 : checkPrefixCuts (2^48) 9244508161 10 Manual.Count131072.C070500.packed 64 cuts70500 = true := by
 decide +kernel
def cuts70501 : List PrefixCut := [⟨64,174035907,174036013⟩]
theorem checked70501 : checkPrefixCuts (2^48) 9244639233 10 Manual.Count131072.C070501.packed 64 cuts70501 = true := by
 decide +kernel
def cuts70502 : List PrefixCut := [⟨5,13792453,13792460⟩,
⟨64,171415010,171415110⟩]
theorem checked70502 : checkPrefixCuts (2^48) 9244770305 10 Manual.Count131072.C070502.packed 64 cuts70502 = true := by
 decide +kernel
def pointBounds70502 : List (Nat × Nat × Nat) := [(9244780544,115901385344119,115901774900874)]
theorem point_links_checked70502 : (cuts70502.take 1).map (fun c => (9244770305-1+2*2^10*c.k,115901371551666+c.lower,115901761108414+c.upper)) = pointBounds70502 := by
 decide +kernel
def cuts70503 : List PrefixCut := [⟨64,174396325,174396427⟩]
theorem checked70503 : checkPrefixCuts (2^48) 9244901377 10 Manual.Count131072.C070503.packed 64 cuts70503 = true := by
 decide +kernel
def cuts70504 : List PrefixCut := [⟨19,50723044,50723076⟩,
⟨64,172323521,172323623⟩]
theorem checked70504 : checkPrefixCuts (2^48) 9245032449 10 Manual.Count131072.C070504.packed 64 cuts70504 = true := by
 decide +kernel
def pointBounds70504 : List (Nat × Nat × Nat) := [(9245071360,115901768086045,115902157643027)]
theorem point_links_checked70504 : (cuts70504.take 1).map (fun c => (9245032449-1+2*2^10*c.k,115901717363001+c.lower,115902106919951+c.upper)) = pointBounds70504 := by
 decide +kernel
def cuts70505 : List PrefixCut := [⟨64,172960447,172960545⟩]
theorem checked70505 : checkPrefixCuts (2^48) 9245163521 10 Manual.Count131072.C070505.packed 64 cuts70505 = true := by
 decide +kernel
def cuts70506 : List PrefixCut := [⟨33,87742760,87742811⟩,
⟨64,174297550,174297654⟩]
theorem checked70506 : checkPrefixCuts (2^48) 9245294593 10 Manual.Count131072.C070506.packed 64 cuts70506 = true := by
 decide +kernel
def pointBounds70506 : List (Nat × Nat × Nat) := [(9245362176,115902150389729,115902539946930)]
theorem point_links_checked70506 : (cuts70506.take 1).map (fun c => (9245294593-1+2*2^10*c.k,115902062646969+c.lower,115902452204119+c.upper)) = pointBounds70506 := by
 decide +kernel
def cuts70507 : List PrefixCut := [⟨64,172894643,172894751⟩]
theorem checked70507 : checkPrefixCuts (2^48) 9245425665 10 Manual.Count131072.C070507.packed 64 cuts70507 = true := by
 decide +kernel
def cuts70508 : List PrefixCut := [⟨47,128748460,128748535⟩,
⟨64,173409760,173409863⟩]
theorem checked70508 : checkPrefixCuts (2^48) 9245556737 10 Manual.Count131072.C070508.packed 64 cuts70508 = true := by
 decide +kernel
def pointBounds70508 : List (Nat × Nat × Nat) := [(9245652992,115902538587622,115902928145059)]
theorem point_links_checked70508 : (cuts70508.take 1).map (fun c => (9245556737-1+2*2^10*c.k,115902409839162+c.lower,115902799396524+c.upper)) = pointBounds70508 := by
 decide +kernel
def cuts70509 : List PrefixCut := [⟨64,172463527,172463632⟩]
theorem checked70509 : checkPrefixCuts (2^48) 9245687809 10 Manual.Count131072.C070509.packed 64 cuts70509 = true := by
 decide +kernel
def cuts70510 : List PrefixCut := [⟨61,162901968,162902066⟩,
⟨64,171365138,171365241⟩]
theorem checked70510 : checkPrefixCuts (2^48) 9245818881 10 Manual.Count131072.C070510.packed 64 cuts70510 = true := by
 decide +kernel
def pointBounds70510 : List (Nat × Nat × Nat) := [(9245943808,115902918614417,115903308172085)]
theorem point_links_checked70510 : (cuts70510.take 1).map (fun c => (9245818881-1+2*2^10*c.k,115902755712449+c.lower,115903145270019+c.upper)) = pointBounds70510 := by
 decide +kernel
def cuts70511 : List PrefixCut := [⟨64,174802741,174802849⟩]
theorem checked70511 : checkPrefixCuts (2^48) 9245949953 10 Manual.Count131072.C070511.packed 64 cuts70511 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000015
