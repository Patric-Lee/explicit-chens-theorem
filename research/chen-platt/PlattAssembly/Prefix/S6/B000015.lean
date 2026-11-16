import PlattAssemblyKernel
import PlattCertificates.Count131072.C050480
import PlattCertificates.Count131072.C050481
import PlattCertificates.Count131072.C050482
import PlattCertificates.Count131072.C050483
import PlattCertificates.Count131072.C050484
import PlattCertificates.Count131072.C050485
import PlattCertificates.Count131072.C050486
import PlattCertificates.Count131072.C050487
import PlattCertificates.Count131072.C050488
import PlattCertificates.Count131072.C050489
import PlattCertificates.Count131072.C050490
import PlattCertificates.Count131072.C050491
import PlattCertificates.Count131072.C050492
import PlattCertificates.Count131072.C050493
import PlattCertificates.Count131072.C050494
import PlattCertificates.Count131072.C050495
import PlattCertificates.Count131072.C050496
import PlattCertificates.Count131072.C050497
import PlattCertificates.Count131072.C050498
import PlattCertificates.Count131072.C050499
import PlattCertificates.Count131072.C050500
import PlattCertificates.Count131072.C050501
import PlattCertificates.Count131072.C050502
import PlattCertificates.Count131072.C050503
import PlattCertificates.Count131072.C050504
import PlattCertificates.Count131072.C050505
import PlattCertificates.Count131072.C050506
import PlattCertificates.Count131072.C050507
import PlattCertificates.Count131072.C050508
import PlattCertificates.Count131072.C050509
import PlattCertificates.Count131072.C050510
import PlattCertificates.Count131072.C050511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50480 : List PrefixCut := [⟨2,8120553,8120557⟩,
⟨64,246972986,246973126⟩]
theorem checked50480 : checkPrefixCuts (2^48) 6620446721 10 Manual.Count131072.C050480.packed 64 cuts50480 = true := by
 decide +kernel
def pointBounds50480 : List (Nat × Nat × Nat) := [(6620450816,111775762226298,111776149416034)]
theorem point_links_checked50480 : (cuts50480.take 1).map (fun c => (6620446721-1+2*2^10*c.k,111775754105745+c.lower,111776141295477+c.upper)) = pointBounds50480 := by
 decide +kernel
def cuts50481 : List PrefixCut := [⟨40,152458392,152458481⟩,
⟨64,247223148,247223292⟩]
theorem checked50481 : checkPrefixCuts (2^48) 6620577793 10 Manual.Count131072.C050481.packed 64 cuts50481 = true := by
 decide +kernel
def pointBounds50481 : List (Nat × Nat × Nat) := [(6620659712,111776153537123,111776540727084)]
theorem point_links_checked50481 : (cuts50481.take 1).map (fun c => (6620577793-1+2*2^10*c.k,111776001078731+c.lower,111776388268603+c.upper)) = pointBounds50481 := by
 decide +kernel
def cuts50482 : List PrefixCut := [⟨64,246835651,246835787⟩]
theorem checked50482 : checkPrefixCuts (2^48) 6620708865 10 Manual.Count131072.C050482.packed 64 cuts50482 = true := by
 decide +kernel
def cuts50483 : List PrefixCut := [⟨14,51483704,51483733⟩,
⟨64,245725434,245725574⟩]
theorem checked50483 : checkPrefixCuts (2^48) 6620839937 10 Manual.Count131072.C050483.packed 64 cuts50483 = true := by
 decide +kernel
def pointBounds50483 : List (Nat × Nat × Nat) := [(6620868608,111776546621234,111776933811415)]
theorem point_links_checked50483 : (cuts50483.take 1).map (fun c => (6620839937-1+2*2^10*c.k,111776495137530+c.lower,111776882327682+c.upper)) = pointBounds50483 := by
 decide +kernel
def cuts50484 : List PrefixCut := [⟨52,199000023,199000142⟩,
⟨64,244572747,244572892⟩]
theorem checked50484 : checkPrefixCuts (2^48) 6620971009 10 Manual.Count131072.C050484.packed 64 cuts50484 = true := by
 decide +kernel
def pointBounds50484 : List (Nat × Nat × Nat) := [(6621077504,111776939862987,111777327053398)]
theorem point_links_checked50484 : (cuts50484.take 1).map (fun c => (6620971009-1+2*2^10*c.k,111776740862964+c.lower,111777128053256+c.upper)) = pointBounds50484 := by
 decide +kernel
def cuts50485 : List PrefixCut := [⟨64,248521471,248521608⟩]
theorem checked50485 : checkPrefixCuts (2^48) 6621102081 10 Manual.Count131072.C050485.packed 64 cuts50485 = true := by
 decide +kernel
def cuts50486 : List PrefixCut := [⟨26,99220156,99220213⟩,
⟨64,247496280,247496420⟩]
theorem checked50486 : checkPrefixCuts (2^48) 6621233153 10 Manual.Count131072.C050486.packed 64 cuts50486 = true := by
 decide +kernel
def pointBounds50486 : List (Nat × Nat × Nat) := [(6621286400,111777333177338,111777720367969)]
theorem point_links_checked50486 : (cuts50486.take 1).map (fun c => (6621233153-1+2*2^10*c.k,111777233957182+c.lower,111777621147756+c.upper)) = pointBounds50486 := by
 decide +kernel
def cuts50487 : List PrefixCut := [⟨64,245620949,245621095⟩]
theorem checked50487 : checkPrefixCuts (2^48) 6621364225 10 Manual.Count131072.C050487.packed 64 cuts50487 = true := by
 decide +kernel
def pointBounds50487 : List (Nat × Nat × Nat) := [(6621495296,111777727074411,111778114265271)]
theorem point_links_checked50487 : (cuts50487.take 1).map (fun c => (6621364225-1+2*2^10*c.k,111777481453462+c.lower,111777868644176+c.upper)) = pointBounds50487 := by
 decide +kernel
def cuts50488 : List PrefixCut := [⟨64,248464217,248464355⟩]
theorem checked50488 : checkPrefixCuts (2^48) 6621495297 10 Manual.Count131072.C050488.packed 64 cuts50488 = true := by
 decide +kernel
def cuts50489 : List PrefixCut := [⟨38,147248314,147248397⟩,
⟨64,245993826,245993963⟩]
theorem checked50489 : checkPrefixCuts (2^48) 6621626369 10 Manual.Count131072.C050489.packed 64 cuts50489 = true := by
 decide +kernel
def pointBounds50489 : List (Nat × Nat × Nat) := [(6621704192,111778122786942,111778509978023)]
theorem point_links_checked50489 : (cuts50489.take 1).map (fun c => (6621626369-1+2*2^10*c.k,111777975538628+c.lower,111778362729626+c.upper)) = pointBounds50489 := by
 decide +kernel
def cuts50490 : List PrefixCut := [⟨64,245903922,245904065⟩]
theorem checked50490 : checkPrefixCuts (2^48) 6621757441 10 Manual.Count131072.C050490.packed 64 cuts50490 = true := by
 decide +kernel
def cuts50491 : List PrefixCut := [⟨12,46757329,46757353⟩,
⟨64,244453872,244454007⟩]
theorem checked50491 : checkPrefixCuts (2^48) 6621888513 10 Manual.Count131072.C050491.packed 64 cuts50491 = true := by
 decide +kernel
def pointBounds50491 : List (Nat × Nat × Nat) := [(6621913088,111778514193705,111778901385007)]
theorem point_links_checked50491 : (cuts50491.take 1).map (fun c => (6621888513-1+2*2^10*c.k,111778467436376+c.lower,111778854627654+c.upper)) = pointBounds50491 := by
 decide +kernel
def cuts50492 : List PrefixCut := [⟨50,193357840,193357952⟩,
⟨64,247679423,247679564⟩]
theorem checked50492 : checkPrefixCuts (2^48) 6622019585 10 Manual.Count131072.C050492.packed 64 cuts50492 = true := by
 decide +kernel
def pointBounds50492 : List (Nat × Nat × Nat) := [(6622121984,111778905248088,111779292439613)]
theorem point_links_checked50492 : (cuts50492.take 1).map (fun c => (6622019585-1+2*2^10*c.k,111778711890248+c.lower,111779099081661+c.upper)) = pointBounds50492 := by
 decide +kernel
def cuts50493 : List PrefixCut := [⟨64,248227099,248227245⟩]
theorem checked50493 : checkPrefixCuts (2^48) 6622150657 10 Manual.Count131072.C050493.packed 64 cuts50493 = true := by
 decide +kernel
def cuts50494 : List PrefixCut := [⟨24,91766264,91766316⟩,
⟨64,244524332,244524471⟩]
theorem checked50494 : checkPrefixCuts (2^48) 6622281729 10 Manual.Count131072.C050494.packed 64 cuts50494 = true := by
 decide +kernel
def pointBounds50494 : List (Nat × Nat × Nat) := [(6622330880,111779299563034,111779686754786)]
theorem point_links_checked50494 : (cuts50494.take 1).map (fun c => (6622281729-1+2*2^10*c.k,111779207796770+c.lower,111779594988470+c.upper)) = pointBounds50494 := by
 decide +kernel
def cuts50495 : List PrefixCut := [⟨62,242096901,242097036⟩,
⟨64,249449842,249449981⟩]
theorem checked50495 : checkPrefixCuts (2^48) 6622412801 10 Manual.Count131072.C050495.packed 64 cuts50495 = true := by
 decide +kernel
def pointBounds50495 : List (Nat × Nat × Nat) := [(6622539776,111779694418003,111780081609977)]
theorem point_links_checked50495 : (cuts50495.take 1).map (fun c => (6622412801-1+2*2^10*c.k,111779452321102+c.lower,111779839512941+c.upper)) = pointBounds50495 := by
 decide +kernel
def cuts50496 : List PrefixCut := [⟨64,246979794,246979936⟩]
theorem checked50496 : checkPrefixCuts (2^48) 6622543873 10 Manual.Count131072.C050496.packed 64 cuts50496 = true := by
 decide +kernel
def cuts50497 : List PrefixCut := [⟨36,137322194,137322275⟩,
⟨64,241959743,241959885⟩]
theorem checked50497 : checkPrefixCuts (2^48) 6622674945 10 Manual.Count131072.C050497.packed 64 cuts50497 = true := by
 decide +kernel
def pointBounds50497 : List (Nat × Nat × Nat) := [(6622748672,111780086072932,111780473265133)]
theorem point_links_checked50497 : (cuts50497.take 1).map (fun c => (6622674945-1+2*2^10*c.k,111779948750738+c.lower,111780335942858+c.upper)) = pointBounds50497 := by
 decide +kernel
def cuts50498 : List PrefixCut := [⟨64,244929990,244930124⟩]
theorem checked50498 : checkPrefixCuts (2^48) 6622806017 10 Manual.Count131072.C050498.packed 64 cuts50498 = true := by
 decide +kernel
def cuts50499 : List PrefixCut := [⟨10,38844950,38844972⟩,
⟨64,247475120,247475262⟩]
theorem checked50499 : checkPrefixCuts (2^48) 6622937089 10 Manual.Count131072.C050499.packed 64 cuts50499 = true := by
 decide +kernel
def pointBounds50499 : List (Nat × Nat × Nat) := [(6622957568,111780474485421,111780861677839)]
theorem point_links_checked50499 : (cuts50499.take 1).map (fun c => (6622937089-1+2*2^10*c.k,111780435640471+c.lower,111780822832867+c.upper)) = pointBounds50499 := by
 decide +kernel
def cuts50500 : List PrefixCut := [⟨48,185635000,185635108⟩,
⟨64,247130232,247130377⟩]
theorem checked50500 : checkPrefixCuts (2^48) 6623068161 10 Manual.Count131072.C050500.packed 64 cuts50500 = true := by
 decide +kernel
def pointBounds50500 : List (Nat × Nat × Nat) := [(6623166464,111780868750591,111781255943237)]
theorem point_links_checked50500 : (cuts50500.take 1).map (fun c => (6623068161-1+2*2^10*c.k,111780683115591+c.lower,111781070308129+c.upper)) = pointBounds50500 := by
 decide +kernel
def cuts50501 : List PrefixCut := [⟨64,247125323,247125461⟩]
theorem checked50501 : checkPrefixCuts (2^48) 6623199233 10 Manual.Count131072.C050501.packed 64 cuts50501 = true := by
 decide +kernel
def cuts50502 : List PrefixCut := [⟨22,84612210,84612258⟩,
⟨64,245675549,245675687⟩]
theorem checked50502 : checkPrefixCuts (2^48) 6623330305 10 Manual.Count131072.C050502.packed 64 cuts50502 = true := by
 decide +kernel
def pointBounds50502 : List (Nat × Nat × Nat) := [(6623375360,111781261983356,111781649176225)]
theorem point_links_checked50502 : (cuts50502.take 1).map (fun c => (6623330305-1+2*2^10*c.k,111781177371146+c.lower,111781564563967+c.upper)) = pointBounds50502 := by
 decide +kernel
def cuts50503 : List PrefixCut := [⟨60,235344227,235344358⟩,
⟨64,250430247,250430386⟩]
theorem checked50503 : checkPrefixCuts (2^48) 6623461377 10 Manual.Count131072.C050503.packed 64 cuts50503 = true := by
 decide +kernel
def pointBounds50503 : List (Nat × Nat × Nat) := [(6623584256,111781658390922,111782045584012)]
theorem point_links_checked50503 : (cuts50503.take 1).map (fun c => (6623461377-1+2*2^10*c.k,111781423046695+c.lower,111781810239654+c.upper)) = pointBounds50503 := by
 decide +kernel
def cuts50504 : List PrefixCut := [⟨64,249872861,249873000⟩]
theorem checked50504 : checkPrefixCuts (2^48) 6623592449 10 Manual.Count131072.C050504.packed 64 cuts50504 = true := by
 decide +kernel
def cuts50505 : List PrefixCut := [⟨34,132923559,132923634⟩,
⟨64,247998189,247998327⟩]
theorem checked50505 : checkPrefixCuts (2^48) 6623723521 10 Manual.Count131072.C050505.packed 64 cuts50505 = true := by
 decide +kernel
def pointBounds50505 : List (Nat × Nat × Nat) := [(6623793152,111782056273362,111782443466674)]
theorem point_links_checked50505 : (cuts50505.take 1).map (fun c => (6623723521-1+2*2^10*c.k,111781923349803+c.lower,111782310543040+c.upper)) = pointBounds50505 := by
 decide +kernel
def cuts50506 : List PrefixCut := [⟨64,244168818,244168960⟩]
theorem checked50506 : checkPrefixCuts (2^48) 6623854593 10 Manual.Count131072.C050506.packed 64 cuts50506 = true := by
 decide +kernel
def cuts50507 : List PrefixCut := [⟨8,30340167,30340186⟩,
⟨64,244886357,244886496⟩]
theorem checked50507 : checkPrefixCuts (2^48) 6623985665 10 Manual.Count131072.C050507.packed 64 cuts50507 = true := by
 decide +kernel
def pointBounds50507 : List (Nat × Nat × Nat) := [(6624002048,111782445856977,111782833050513)]
theorem point_links_checked50507 : (cuts50507.take 1).map (fun c => (6623985665-1+2*2^10*c.k,111782415516810+c.lower,111782802710327+c.upper)) = pointBounds50507 := by
 decide +kernel
def cuts50508 : List PrefixCut := [⟨46,175067619,175067720⟩,
⟨64,244414108,244414246⟩]
theorem checked50508 : checkPrefixCuts (2^48) 6624116737 10 Manual.Count131072.C050508.packed 64 cuts50508 = true := by
 decide +kernel
def pointBounds50508 : List (Nat × Nat × Nat) := [(6624210944,111782835470786,111783222664543)]
theorem point_links_checked50508 : (cuts50508.take 1).map (fun c => (6624116737-1+2*2^10*c.k,111782660403167+c.lower,111783047596823+c.upper)) = pointBounds50508 := by
 decide +kernel
def cuts50509 : List PrefixCut := [⟨64,243389495,243389634⟩]
theorem checked50509 : checkPrefixCuts (2^48) 6624247809 10 Manual.Count131072.C050509.packed 64 cuts50509 = true := by
 decide +kernel
def cuts50510 : List PrefixCut := [⟨20,76823054,76823100⟩,
⟨64,246061549,246061689⟩]
theorem checked50510 : checkPrefixCuts (2^48) 6624378881 10 Manual.Count131072.C050510.packed 64 cuts50510 = true := by
 decide +kernel
def pointBounds50510 : List (Nat × Nat × Nat) := [(6624419840,111783225029824,111783612223803)]
theorem point_links_checked50510 : (cuts50510.take 1).map (fun c => (6624378881-1+2*2^10*c.k,111783148206770+c.lower,111783535400703+c.upper)) = pointBounds50510 := by
 decide +kernel
def cuts50511 : List PrefixCut := [⟨58,224472230,224472359⟩,
⟨64,247756266,247756409⟩]
theorem checked50511 : checkPrefixCuts (2^48) 6624509953 10 Manual.Count131072.C050511.packed 64 cuts50511 = true := by
 decide +kernel
def pointBounds50511 : List (Nat × Nat × Nat) := [(6624628736,111783618740549,111784005934751)]
theorem point_links_checked50511 : (cuts50511.take 1).map (fun c => (6624509953-1+2*2^10*c.k,111783394268319+c.lower,111783781462392+c.upper)) = pointBounds50511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000015
