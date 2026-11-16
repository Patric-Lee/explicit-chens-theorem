import PlattAssemblyKernel
import PlattCertificates.Count131072.C054480
import PlattCertificates.Count131072.C054481
import PlattCertificates.Count131072.C054482
import PlattCertificates.Count131072.C054483
import PlattCertificates.Count131072.C054484
import PlattCertificates.Count131072.C054485
import PlattCertificates.Count131072.C054486
import PlattCertificates.Count131072.C054487
import PlattCertificates.Count131072.C054488
import PlattCertificates.Count131072.C054489
import PlattCertificates.Count131072.C054490
import PlattCertificates.Count131072.C054491
import PlattCertificates.Count131072.C054492
import PlattCertificates.Count131072.C054493
import PlattCertificates.Count131072.C054494
import PlattCertificates.Count131072.C054495
import PlattCertificates.Count131072.C054496
import PlattCertificates.Count131072.C054497
import PlattCertificates.Count131072.C054498
import PlattCertificates.Count131072.C054499
import PlattCertificates.Count131072.C054500
import PlattCertificates.Count131072.C054501
import PlattCertificates.Count131072.C054502
import PlattCertificates.Count131072.C054503
import PlattCertificates.Count131072.C054504
import PlattCertificates.Count131072.C054505
import PlattCertificates.Count131072.C054506
import PlattCertificates.Count131072.C054507
import PlattCertificates.Count131072.C054508
import PlattCertificates.Count131072.C054509
import PlattCertificates.Count131072.C054510
import PlattCertificates.Count131072.C054511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000140
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54480 : List PrefixCut := [⟨64,224831644,224831773⟩]
theorem checked54480 : checkPrefixCuts (2^48) 7144734721 10 Manual.Count131072.C054480.packed 64 cuts54480 = true := by
 decide +kernel
def cuts54481 : List PrefixCut := [⟨19,65553778,65553816⟩,
⟨64,224788127,224788257⟩]
theorem checked54481 : checkPrefixCuts (2^48) 7144865793 10 Manual.Count131072.C054481.packed 64 cuts54481 = true := by
 decide +kernel
def pointBounds54481 : List (Nat × Nat × Nat) := [(7144904704,112723079503366,112723467231296)]
theorem point_links_checked54481 : (cuts54481.take 1).map (fun c => (7144865793-1+2*2^10*c.k,112723013949588+c.lower,112723401677480+c.upper)) = pointBounds54481 := by
 decide +kernel
def cuts54482 : List PrefixCut := [⟨64,225611283,225611412⟩]
theorem checked54482 : checkPrefixCuts (2^48) 7144996865 10 Manual.Count131072.C054482.packed 64 cuts54482 = true := by
 decide +kernel
def cuts54483 : List PrefixCut := [⟨1,3545456,3545458⟩,
⟨64,229152567,229152694⟩]
theorem checked54483 : checkPrefixCuts (2^48) 7145127937 10 Manual.Count131072.C054483.packed 64 cuts54483 = true := by
 decide +kernel
def pointBounds54483 : List (Nat × Nat × Nat) := [(7145129984,112723467894454,112723855622607)]
theorem point_links_checked54483 : (cuts54483.take 1).map (fun c => (7145127937-1+2*2^10*c.k,112723464348998+c.lower,112723852077149+c.upper)) = pointBounds54483 := by
 decide +kernel
def cuts54484 : List PrefixCut := [⟨47,170098850,170098947⟩,
⟨64,229778659,229778792⟩]
theorem checked54484 : checkPrefixCuts (2^48) 7145259009 10 Manual.Count131072.C054484.packed 64 cuts54484 = true := by
 decide +kernel
def pointBounds54484 : List (Nat × Nat × Nat) := [(7145355264,112723863600415,112724251328790)]
theorem point_links_checked54484 : (cuts54484.take 1).map (fun c => (7145259009-1+2*2^10*c.k,112723693501565+c.lower,112724081229843+c.upper)) = pointBounds54484 := by
 decide +kernel
def cuts54485 : List PrefixCut := [⟨64,229735040,229735167⟩]
theorem checked54485 : checkPrefixCuts (2^48) 7145390081 10 Manual.Count131072.C054485.packed 64 cuts54485 = true := by
 decide +kernel
def cuts54486 : List PrefixCut := [⟨29,102339462,102339519⟩,
⟨64,225161439,225161567⟩]
theorem checked54486 : checkPrefixCuts (2^48) 7145521153 10 Manual.Count131072.C054486.packed 64 cuts54486 = true := by
 decide +kernel
def pointBounds54486 : List (Nat × Nat × Nat) := [(7145580544,112724255354726,112724643083321)]
theorem point_links_checked54486 : (cuts54486.take 1).map (fun c => (7145521153-1+2*2^10*c.k,112724153015264+c.lower,112724540743802+c.upper)) = pointBounds54486 := by
 decide +kernel
def cuts54487 : List PrefixCut := [⟨64,226732932,226733061⟩]
theorem checked54487 : checkPrefixCuts (2^48) 7145652225 10 Manual.Count131072.C054487.packed 64 cuts54487 = true := by
 decide +kernel
def cuts54488 : List PrefixCut := [⟨11,38208579,38208600⟩,
⟨64,228383143,228383272⟩]
theorem checked54488 : checkPrefixCuts (2^48) 7145783297 10 Manual.Count131072.C054488.packed 64 cuts54488 = true := by
 decide +kernel
def pointBounds54488 : List (Nat × Nat × Nat) := [(7145805824,112724643118214,112725030847030)]
theorem point_links_checked54488 : (cuts54488.take 1).map (fun c => (7145783297-1+2*2^10*c.k,112724604909635+c.lower,112724992638430+c.upper)) = pointBounds54488 := by
 decide +kernel
def cuts54489 : List PrefixCut := [⟨57,201043015,201043130⟩,
⟨64,225897437,225897566⟩]
theorem checked54489 : checkPrefixCuts (2^48) 7145914369 10 Manual.Count131072.C054489.packed 64 cuts54489 = true := by
 decide +kernel
def pointBounds54489 : List (Nat × Nat × Nat) := [(7146031104,112725034335793,112725422064832)]
theorem point_links_checked54489 : (cuts54489.take 1).map (fun c => (7145914369-1+2*2^10*c.k,112724833292778+c.lower,112725221021702+c.upper)) = pointBounds54489 := by
 decide +kernel
def cuts54490 : List PrefixCut := [⟨64,228689879,228690004⟩]
theorem checked54490 : checkPrefixCuts (2^48) 7146045441 10 Manual.Count131072.C054490.packed 64 cuts54490 = true := by
 decide +kernel
def cuts54491 : List PrefixCut := [⟨39,136991329,136991405⟩,
⟨64,228252396,228252524⟩]
theorem checked54491 : checkPrefixCuts (2^48) 7146176513 10 Manual.Count131072.C054491.packed 64 cuts54491 = true := by
 decide +kernel
def pointBounds54491 : List (Nat × Nat × Nat) := [(7146256384,112725424871423,112725812600677)]
theorem point_links_checked54491 : (cuts54491.take 1).map (fun c => (7146176513-1+2*2^10*c.k,112725287880094+c.lower,112725675609272+c.upper)) = pointBounds54491 := by
 decide +kernel
def cuts54492 : List PrefixCut := [⟨64,226278872,226278995⟩]
theorem checked54492 : checkPrefixCuts (2^48) 7146307585 10 Manual.Count131072.C054492.packed 64 cuts54492 = true := by
 decide +kernel
def cuts54493 : List PrefixCut := [⟨21,74322546,74322589⟩,
⟨64,230449666,230449796⟩]
theorem checked54493 : checkPrefixCuts (2^48) 7146438657 10 Manual.Count131072.C054493.packed 64 cuts54493 = true := by
 decide +kernel
def pointBounds54493 : List (Nat × Nat × Nat) := [(7146481664,112725816733908,112726204463380)]
theorem point_links_checked54493 : (cuts54493.take 1).map (fun c => (7146438657-1+2*2^10*c.k,112725742411362+c.lower,112726130140791+c.upper)) = pointBounds54493 := by
 decide +kernel
def cuts54494 : List PrefixCut := [⟨64,223592361,223592492⟩]
theorem checked54494 : checkPrefixCuts (2^48) 7146569729 10 Manual.Count131072.C054494.packed 64 cuts54494 = true := by
 decide +kernel
def cuts54495 : List PrefixCut := [⟨3,10909721,10909727⟩,
⟨64,229574735,229574865⟩]
theorem checked54495 : checkPrefixCuts (2^48) 7146700801 10 Manual.Count131072.C054495.packed 64 cuts54495 = true := by
 decide +kernel
def pointBounds54495 : List (Nat × Nat × Nat) := [(7146706944,112726207363110,112726595092806)]
theorem point_links_checked54495 : (cuts54495.take 1).map (fun c => (7146700801-1+2*2^10*c.k,112726196453389+c.lower,112726584183079+c.upper)) = pointBounds54495 := by
 decide +kernel
def cuts54496 : List PrefixCut := [⟨49,173842254,173842352⟩,
⟨64,226577337,226577466⟩]
theorem checked54496 : checkPrefixCuts (2^48) 7146831873 10 Manual.Count131072.C054496.packed 64 cuts54496 = true := by
 decide +kernel
def pointBounds54496 : List (Nat × Nat × Nat) := [(7146932224,112726599870378,112726987600296)]
theorem point_links_checked54496 : (cuts54496.take 1).map (fun c => (7146831873-1+2*2^10*c.k,112726426028124+c.lower,112726813757944+c.upper)) = pointBounds54496 := by
 decide +kernel
def cuts54497 : List PrefixCut := [⟨64,226573195,226573321⟩]
theorem checked54497 : checkPrefixCuts (2^48) 7146962945 10 Manual.Count131072.C054497.packed 64 cuts54497 = true := by
 decide +kernel
def cuts54498 : List PrefixCut := [⟨31,108027431,108027492⟩,
⟨64,223063970,223064098⟩]
theorem checked54498 : checkPrefixCuts (2^48) 7147094017 10 Manual.Count131072.C054498.packed 64 cuts54498 = true := by
 decide +kernel
def pointBounds54498 : List (Nat × Nat × Nat) := [(7147157504,112726987206087,112727374936223)]
theorem point_links_checked54498 : (cuts54498.take 1).map (fun c => (7147094017-1+2*2^10*c.k,112726879178656+c.lower,112727266908731+c.upper)) = pointBounds54498 := by
 decide +kernel
def cuts54499 : List PrefixCut := [⟨64,231172580,231172708⟩]
theorem checked54499 : checkPrefixCuts (2^48) 7147225089 10 Manual.Count131072.C054499.packed 64 cuts54499 = true := by
 decide +kernel
def cuts54500 : List PrefixCut := [⟨13,47415456,47415482⟩,
⟨64,226836425,226836552⟩]
theorem checked54500 : checkPrefixCuts (2^48) 7147356161 10 Manual.Count131072.C054500.packed 64 cuts54500 = true := by
 decide +kernel
def pointBounds54500 : List (Nat × Nat × Nat) := [(7147382784,112727380830662,112727768561019)]
theorem point_links_checked54500 : (cuts54500.take 1).map (fun c => (7147356161-1+2*2^10*c.k,112727333415206+c.lower,112727721145537+c.upper)) = pointBounds54500 := by
 decide +kernel
def cuts54501 : List PrefixCut := [⟨59,208874835,208874954⟩,
⟨64,226871616,226871746⟩]
theorem checked54501 : checkPrefixCuts (2^48) 7147487233 10 Manual.Count131072.C054501.packed 64 cuts54501 = true := by
 decide +kernel
def pointBounds54501 : List (Nat × Nat × Nat) := [(7147608064,112727769126466,112728156857043)]
theorem point_links_checked54501 : (cuts54501.take 1).map (fun c => (7147487233-1+2*2^10*c.k,112727560251631+c.lower,112727947982089+c.upper)) = pointBounds54501 := by
 decide +kernel
def cuts54502 : List PrefixCut := [⟨64,228915202,228915336⟩]
theorem checked54502 : checkPrefixCuts (2^48) 7147618305 10 Manual.Count131072.C054502.packed 64 cuts54502 = true := by
 decide +kernel
def cuts54503 : List PrefixCut := [⟨41,145939616,145939700⟩,
⟨64,225918206,225918337⟩]
theorem checked54503 : checkPrefixCuts (2^48) 7147749377 10 Manual.Count131072.C054503.packed 64 cuts54503 = true := by
 decide +kernel
def pointBounds54503 : List (Nat × Nat × Nat) := [(7147833344,112728161978065,112728549708871)]
theorem point_links_checked54503 : (cuts54503.take 1).map (fun c => (7147749377-1+2*2^10*c.k,112728016038449+c.lower,112728403769171+c.upper)) = pointBounds54503 := by
 decide +kernel
def cuts54504 : List PrefixCut := [⟨64,227410441,227410571⟩]
theorem checked54504 : checkPrefixCuts (2^48) 7147880449 10 Manual.Count131072.C054504.packed 64 cuts54504 = true := by
 decide +kernel
def cuts54505 : List PrefixCut := [⟨23,83481233,83481281⟩,
⟨64,227485053,227485182⟩]
theorem checked54505 : checkPrefixCuts (2^48) 7148011521 10 Manual.Count131072.C054505.packed 64 cuts54505 = true := by
 decide +kernel
def pointBounds54505 : List (Nat × Nat × Nat) := [(7148058624,112728552848329,112728940579360)]
theorem point_links_checked54505 : (cuts54505.take 1).map (fun c => (7148011521-1+2*2^10*c.k,112728469367096+c.lower,112728857098079+c.upper)) = pointBounds54505 := by
 decide +kernel
def cuts54506 : List PrefixCut := [⟨64,227992750,227992881⟩]
theorem checked54506 : checkPrefixCuts (2^48) 7148142593 10 Manual.Count131072.C054506.packed 64 cuts54506 = true := by
 decide +kernel
def cuts54507 : List PrefixCut := [⟨5,17561961,17561971⟩,
⟨64,226295394,226295520⟩]
theorem checked54507 : checkPrefixCuts (2^48) 7148273665 10 Manual.Count131072.C054507.packed 64 cuts54507 = true := by
 decide +kernel
def pointBounds54507 : List (Nat × Nat × Nat) := [(7148283904,112728942406860,112729330138113)]
theorem point_links_checked54507 : (cuts54507.take 1).map (fun c => (7148273665-1+2*2^10*c.k,112728924844899+c.lower,112729312576142+c.upper)) = pointBounds54507 := by
 decide +kernel
def cuts54508 : List PrefixCut := [⟨51,181875983,181876087⟩,
⟨64,226881897,226882028⟩]
theorem checked54508 : checkPrefixCuts (2^48) 7148404737 10 Manual.Count131072.C054508.packed 64 cuts54508 = true := by
 decide +kernel
def pointBounds54508 : List (Nat × Nat × Nat) := [(7148509184,112729333016276,112729720747749)]
theorem point_links_checked54508 : (cuts54508.take 1).map (fun c => (7148404737-1+2*2^10*c.k,112729151140293+c.lower,112729538871662+c.upper)) = pointBounds54508 := by
 decide +kernel
def cuts54509 : List PrefixCut := [⟨64,226720230,226720359⟩]
theorem checked54509 : checkPrefixCuts (2^48) 7148535809 10 Manual.Count131072.C054509.packed 64 cuts54509 = true := by
 decide +kernel
def cuts54510 : List PrefixCut := [⟨33,117886578,117886645⟩,
⟨64,225456108,225456237⟩]
theorem checked54510 : checkPrefixCuts (2^48) 7148666881 10 Manual.Count131072.C054510.packed 64 cuts54510 = true := by
 decide +kernel
def pointBounds54510 : List (Nat × Nat × Nat) := [(7148734464,112729722628998,112730110360694)]
theorem point_links_checked54510 : (cuts54510.take 1).map (fun c => (7148666881-1+2*2^10*c.k,112729604742420+c.lower,112729992474049+c.upper)) = pointBounds54510 := by
 decide +kernel
def cuts54511 : List PrefixCut := [⟨64,226987503,226987633⟩]
theorem checked54511 : checkPrefixCuts (2^48) 7148797953 10 Manual.Count131072.C054511.packed 64 cuts54511 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000140
