import PlattAssemblyKernel
import PlattCertificates.Count131072.C071504
import PlattCertificates.Count131072.C071505
import PlattCertificates.Count131072.C071506
import PlattCertificates.Count131072.C071507
import PlattCertificates.Count131072.C071508
import PlattCertificates.Count131072.C071509
import PlattCertificates.Count131072.C071510
import PlattCertificates.Count131072.C071511
import PlattCertificates.Count131072.C071512
import PlattCertificates.Count131072.C071513
import PlattCertificates.Count131072.C071514
import PlattCertificates.Count131072.C071515
import PlattCertificates.Count131072.C071516
import PlattCertificates.Count131072.C071517
import PlattCertificates.Count131072.C071518
import PlattCertificates.Count131072.C071519
import PlattCertificates.Count131072.C071520
import PlattCertificates.Count131072.C071521
import PlattCertificates.Count131072.C071522
import PlattCertificates.Count131072.C071523
import PlattCertificates.Count131072.C071524
import PlattCertificates.Count131072.C071525
import PlattCertificates.Count131072.C071526
import PlattCertificates.Count131072.C071527
import PlattCertificates.Count131072.C071528
import PlattCertificates.Count131072.C071529
import PlattCertificates.Count131072.C071530
import PlattCertificates.Count131072.C071531
import PlattCertificates.Count131072.C071532
import PlattCertificates.Count131072.C071533
import PlattCertificates.Count131072.C071534
import PlattCertificates.Count131072.C071535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71504 : List PrefixCut := [⟨30,77902814,77902860⟩,
⟨64,169134034,169134133⟩]
theorem checked71504 : checkPrefixCuts (2^48) 9376104449 10 Manual.Count131072.C071504.packed 64 cuts71504 = true := by
 decide +kernel
def pointBounds71504 : List (Nat × Nat × Nat) := [(9376165888,116074420626532,116074810285657)]
theorem point_links_checked71504 : (cuts71504.take 1).map (fun c => (9376104449-1+2*2^10*c.k,116074342723718+c.lower,116074732382797+c.upper)) = pointBounds71504 := by
 decide +kernel
def cuts71505 : List PrefixCut := [⟨64,170962879,170962973⟩]
theorem checked71505 : checkPrefixCuts (2^48) 9376235521 10 Manual.Count131072.C071505.packed 64 cuts71505 = true := by
 decide +kernel
def cuts71506 : List PrefixCut := [⟨46,122839637,122839713⟩,
⟨64,171530866,171530969⟩]
theorem checked71506 : checkPrefixCuts (2^48) 9376366593 10 Manual.Count131072.C071506.packed 64 cuts71506 = true := by
 decide +kernel
def pointBounds71506 : List (Nat × Nat × Nat) := [(9376460800,116074805660268,116075195319616)]
theorem point_links_checked71506 : (cuts71506.take 1).map (fun c => (9376366593-1+2*2^10*c.k,116074682820631+c.lower,116075072479903+c.upper)) = pointBounds71506 := by
 decide +kernel
def cuts71507 : List PrefixCut := [⟨64,170507828,170507930⟩]
theorem checked71507 : checkPrefixCuts (2^48) 9376497665 10 Manual.Count131072.C071507.packed 64 cuts71507 = true := by
 decide +kernel
def cuts71508 : List PrefixCut := [⟨62,169244697,169244797⟩,
⟨64,174617984,174618087⟩]
theorem checked71508 : checkPrefixCuts (2^48) 9376628737 10 Manual.Count131072.C071508.packed 64 cuts71508 = true := by
 decide +kernel
def pointBounds71508 : List (Nat × Nat × Nat) := [(9376755712,116075194104022,116075583763599)]
theorem point_links_checked71508 : (cuts71508.take 1).map (fun c => (9376628737-1+2*2^10*c.k,116075024859325+c.lower,116075414518802+c.upper)) = pointBounds71508 := by
 decide +kernel
def cuts71509 : List PrefixCut := [⟨64,172454241,172454343⟩]
theorem checked71509 : checkPrefixCuts (2^48) 9376759809 10 Manual.Count131072.C071509.packed 64 cuts71509 = true := by
 decide +kernel
def cuts71510 : List PrefixCut := [⟨64,173562479,173562586⟩]
theorem checked71510 : checkPrefixCuts (2^48) 9376890881 10 Manual.Count131072.C071510.packed 64 cuts71510 = true := by
 decide +kernel
def cuts71511 : List PrefixCut := [⟨14,36711364,36711386⟩,
⟨64,171218700,171218795⟩]
theorem checked71511 : checkPrefixCuts (2^48) 9377021953 10 Manual.Count131072.C071511.packed 64 cuts71511 = true := by
 decide +kernel
def pointBounds71511 : List (Nat × Nat × Nat) := [(9377050624,116075582205393,116075971865204)]
theorem point_links_checked71511 : (cuts71511.take 1).map (fun c => (9377021953-1+2*2^10*c.k,116075545494029+c.lower,116075935153818+c.upper)) = pointBounds71511 := by
 decide +kernel
def cuts71512 : List PrefixCut := [⟨64,168154599,168154704⟩]
theorem checked71512 : checkPrefixCuts (2^48) 9377153025 10 Manual.Count131072.C071512.packed 64 cuts71512 = true := by
 decide +kernel
def cuts71513 : List PrefixCut := [⟨30,79994174,79994224⟩,
⟨64,173915391,173915491⟩]
theorem checked71513 : checkPrefixCuts (2^48) 9377284097 10 Manual.Count131072.C071513.packed 64 cuts71513 = true := by
 decide +kernel
def pointBounds71513 : List (Nat × Nat × Nat) := [(9377345536,116075964861502,116076354521541)]
theorem point_links_checked71513 : (cuts71513.take 1).map (fun c => (9377284097-1+2*2^10*c.k,116075884867328+c.lower,116076274527317+c.upper)) = pointBounds71513 := by
 decide +kernel
def cuts71514 : List PrefixCut := [⟨64,173132553,173132648⟩]
theorem checked71514 : checkPrefixCuts (2^48) 9377415169 10 Manual.Count131072.C071514.packed 64 cuts71514 = true := by
 decide +kernel
def cuts71515 : List PrefixCut := [⟨46,123694640,123694710⟩,
⟨64,172559835,172559932⟩]
theorem checked71515 : checkPrefixCuts (2^48) 9377546241 10 Manual.Count131072.C071515.packed 64 cuts71515 = true := by
 decide +kernel
def pointBounds71515 : List (Nat × Nat × Nat) := [(9377640448,116076355609912,116076745270166)]
theorem point_links_checked71515 : (cuts71515.take 1).map (fun c => (9377546241-1+2*2^10*c.k,116076231915272+c.lower,116076621575456+c.upper)) = pointBounds71515 := by
 decide +kernel
def cuts71516 : List PrefixCut := [⟨64,168805512,168805615⟩]
theorem checked71516 : checkPrefixCuts (2^48) 9377677313 10 Manual.Count131072.C071516.packed 64 cuts71516 = true := by
 decide +kernel
def cuts71517 : List PrefixCut := [⟨62,165831728,165831824⟩,
⟨64,171714587,171714686⟩]
theorem checked71517 : checkPrefixCuts (2^48) 9377808385 10 Manual.Count131072.C071517.packed 64 cuts71517 = true := by
 decide +kernel
def pointBounds71517 : List (Nat × Nat × Nat) := [(9377935360,116076739112347,116077128772827)]
theorem point_links_checked71517 : (cuts71517.take 1).map (fun c => (9377808385-1+2*2^10*c.k,116076573280619+c.lower,116076962941003+c.upper)) = pointBounds71517 := by
 decide +kernel
def cuts71518 : List PrefixCut := [⟨64,171652178,171652273⟩]
theorem checked71518 : checkPrefixCuts (2^48) 9377939457 10 Manual.Count131072.C071518.packed 64 cuts71518 = true := by
 decide +kernel
def cuts71519 : List PrefixCut := [⟨64,169188620,169188721⟩]
theorem checked71519 : checkPrefixCuts (2^48) 9378070529 10 Manual.Count131072.C071519.packed 64 cuts71519 = true := by
 decide +kernel
def cuts71520 : List PrefixCut := [⟨14,37337034,37337055⟩,
⟨64,170746965,170747060⟩]
theorem checked71520 : checkPrefixCuts (2^48) 9378201601 10 Manual.Count131072.C071520.packed 64 cuts71520 = true := by
 decide +kernel
def pointBounds71520 : List (Nat × Nat × Nat) := [(9378230272,116077123173038,116077512833738)]
theorem point_links_checked71520 : (cuts71520.take 1).map (fun c => (9378201601-1+2*2^10*c.k,116077085836004+c.lower,116077475496683+c.upper)) = pointBounds71520 := by
 decide +kernel
def cuts71521 : List PrefixCut := [⟨64,171164758,171164856⟩]
theorem checked71521 : checkPrefixCuts (2^48) 9378332673 10 Manual.Count131072.C071521.packed 64 cuts71521 = true := by
 decide +kernel
def cuts71522 : List PrefixCut := [⟨30,81214636,81214689⟩,
⟨64,171102345,171102452⟩]
theorem checked71522 : checkPrefixCuts (2^48) 9378463745 10 Manual.Count131072.C071522.packed 64 cuts71522 = true := by
 decide +kernel
def pointBounds71522 : List (Nat × Nat × Nat) := [(9378525184,116077508962363,116077898623288)]
theorem point_links_checked71522 : (cuts71522.take 1).map (fun c => (9378463745-1+2*2^10*c.k,116077427747727+c.lower,116077817408599+c.upper)) = pointBounds71522 := by
 decide +kernel
def cuts71523 : List PrefixCut := [⟨64,170829848,170829944⟩]
theorem checked71523 : checkPrefixCuts (2^48) 9378594817 10 Manual.Count131072.C071523.packed 64 cuts71523 = true := by
 decide +kernel
def cuts71524 : List PrefixCut := [⟨46,123048833,123048903⟩,
⟨64,171817848,171817944⟩]
theorem checked71524 : checkPrefixCuts (2^48) 9378725889 10 Manual.Count131072.C071524.packed 64 cuts71524 = true := by
 decide +kernel
def pointBounds71524 : List (Nat × Nat × Nat) := [(9378820096,116077892728753,116078282389898)]
theorem point_links_checked71524 : (cuts71524.take 1).map (fun c => (9378725889-1+2*2^10*c.k,116077769679920+c.lower,116078159340995+c.upper)) = pointBounds71524 := by
 decide +kernel
def cuts71525 : List PrefixCut := [⟨64,173826212,173826314⟩]
theorem checked71525 : checkPrefixCuts (2^48) 9378856961 10 Manual.Count131072.C071525.packed 64 cuts71525 = true := by
 decide +kernel
def cuts71526 : List PrefixCut := [⟨62,165240664,165240763⟩,
⟨64,171212815,171212918⟩]
theorem checked71526 : checkPrefixCuts (2^48) 9378988033 10 Manual.Count131072.C071526.packed 64 cuts71526 = true := by
 decide +kernel
def pointBounds71526 : List (Nat × Nat × Nat) := [(9379115008,116078280564644,116078670226016)]
theorem point_links_checked71526 : (cuts71526.take 1).map (fun c => (9378988033-1+2*2^10*c.k,116078115323980+c.lower,116078504985253+c.upper)) = pointBounds71526 := by
 decide +kernel
def cuts71527 : List PrefixCut := [⟨64,172740979,172741071⟩]
theorem checked71527 : checkPrefixCuts (2^48) 9379119105 10 Manual.Count131072.C071527.packed 64 cuts71527 = true := by
 decide +kernel
def cuts71528 : List PrefixCut := [⟨64,171658192,171658290⟩]
theorem checked71528 : checkPrefixCuts (2^48) 9379250177 10 Manual.Count131072.C071528.packed 64 cuts71528 = true := by
 decide +kernel
def cuts71529 : List PrefixCut := [⟨14,37122270,37122291⟩,
⟨64,171385707,171385808⟩]
theorem checked71529 : checkPrefixCuts (2^48) 9379381249 10 Manual.Count131072.C071529.packed 64 cuts71529 = true := by
 decide +kernel
def pointBounds71529 : List (Nat × Nat × Nat) := [(9379409920,116078668058236,116079057719823)]
theorem point_links_checked71529 : (cuts71529.take 1).map (fun c => (9379381249-1+2*2^10*c.k,116078630935966+c.lower,116079020597532+c.upper)) = pointBounds71529 := by
 decide +kernel
def cuts71530 : List PrefixCut := [⟨64,171683390,171683502⟩]
theorem checked71530 : checkPrefixCuts (2^48) 9379512321 10 Manual.Count131072.C071530.packed 64 cuts71530 = true := by
 decide +kernel
def cuts71531 : List PrefixCut := [⟨30,80574238,80574289⟩,
⟨64,173991684,173991791⟩]
theorem checked71531 : checkPrefixCuts (2^48) 9379643393 10 Manual.Count131072.C071531.packed 64 cuts71531 = true := by
 decide +kernel
def pointBounds71531 : List (Nat × Nat × Nat) := [(9379704832,116079054579301,116079444241131)]
theorem point_links_checked71531 : (cuts71531.take 1).map (fun c => (9379643393-1+2*2^10*c.k,116078974005063+c.lower,116079363666842+c.upper)) = pointBounds71531 := by
 decide +kernel
def cuts71532 : List PrefixCut := [⟨64,172038714,172038812⟩]
theorem checked71532 : checkPrefixCuts (2^48) 9379774465 10 Manual.Count131072.C071532.packed 64 cuts71532 = true := by
 decide +kernel
def cuts71533 : List PrefixCut := [⟨46,121442926,121442997⟩,
⟨64,170625915,170626018⟩]
theorem checked71533 : checkPrefixCuts (2^48) 9379905537 10 Manual.Count131072.C071533.packed 64 cuts71533 = true := by
 decide +kernel
def pointBounds71533 : List (Nat × Nat × Nat) := [(9379999744,116079441478387,116079831140442)]
theorem point_links_checked71533 : (cuts71533.take 1).map (fun c => (9379905537-1+2*2^10*c.k,116079320035461+c.lower,116079709697445+c.upper)) = pointBounds71533 := by
 decide +kernel
def cuts71534 : List PrefixCut := [⟨64,171253704,171253804⟩]
theorem checked71534 : checkPrefixCuts (2^48) 9380036609 10 Manual.Count131072.C071534.packed 64 cuts71534 = true := by
 decide +kernel
def cuts71535 : List PrefixCut := [⟨62,166870296,166870399⟩,
⟨64,172091520,172091626⟩]
theorem checked71535 : checkPrefixCuts (2^48) 9380167681 10 Manual.Count131072.C071535.packed 64 cuts71535 = true := by
 decide +kernel
def pointBounds71535 : List (Nat × Nat × Nat) := [(9380294656,116079828785376,116080218447666)]
theorem point_links_checked71535 : (cuts71535.take 1).map (fun c => (9380167681-1+2*2^10*c.k,116079661915080+c.lower,116080051577267+c.upper)) = pointBounds71535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000047
