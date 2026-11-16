import PlattAssemblyKernel
import PlattCertificates.Count131072.C073488
import PlattCertificates.Count131072.C073489
import PlattCertificates.Count131072.C073490
import PlattCertificates.Count131072.C073491
import PlattCertificates.Count131072.C073492
import PlattCertificates.Count131072.C073493
import PlattCertificates.Count131072.C073494
import PlattCertificates.Count131072.C073495
import PlattCertificates.Count131072.C073496
import PlattCertificates.Count131072.C073497
import PlattCertificates.Count131072.C073498
import PlattCertificates.Count131072.C073499
import PlattCertificates.Count131072.C073500
import PlattCertificates.Count131072.C073501
import PlattCertificates.Count131072.C073502
import PlattCertificates.Count131072.C073503
import PlattCertificates.Count131072.C073504
import PlattCertificates.Count131072.C073505
import PlattCertificates.Count131072.C073506
import PlattCertificates.Count131072.C073507
import PlattCertificates.Count131072.C073508
import PlattCertificates.Count131072.C073509
import PlattCertificates.Count131072.C073510
import PlattCertificates.Count131072.C073511
import PlattCertificates.Count131072.C073512
import PlattCertificates.Count131072.C073513
import PlattCertificates.Count131072.C073514
import PlattCertificates.Count131072.C073515
import PlattCertificates.Count131072.C073516
import PlattCertificates.Count131072.C073517
import PlattCertificates.Count131072.C073518
import PlattCertificates.Count131072.C073519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000109
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73488 : List PrefixCut := [⟨64,167958100,167958197⟩]
theorem checked73488 : checkPrefixCuts (2^48) 9636151297 10 Manual.Count131072.C073488.packed 64 cuts73488 = true := by
 decide +kernel
def cuts73489 : List PrefixCut := [⟨46,120607099,120607172⟩,
⟨64,167400819,167400920⟩]
theorem checked73489 : checkPrefixCuts (2^48) 9636282369 10 Manual.Count131072.C073489.packed 64 cuts73489 = true := by
 decide +kernel
def pointBounds73489 : List (Nat × Nat × Nat) := [(9636376576,116409822498130,116410212356674)]
theorem point_links_checked73489 : (cuts73489.take 1).map (fun c => (9636282369-1+2*2^10*c.k,116409701891031+c.lower,116410091749502+c.upper)) = pointBounds73489 := by
 decide +kernel
def cuts73490 : List PrefixCut := [⟨64,166434640,166434737⟩]
theorem checked73490 : checkPrefixCuts (2^48) 9636413441 10 Manual.Count131072.C073490.packed 64 cuts73490 = true := by
 decide +kernel
def cuts73491 : List PrefixCut := [⟨64,166724464,166724563⟩]
theorem checked73491 : checkPrefixCuts (2^48) 9636544513 10 Manual.Count131072.C073491.packed 64 cuts73491 = true := by
 decide +kernel
def cuts73492 : List PrefixCut := [⟨2,5491237,5491240⟩,
⟨64,164619186,164619287⟩]
theorem checked73492 : checkPrefixCuts (2^48) 9636675585 10 Manual.Count131072.C073492.packed 64 cuts73492 = true := by
 decide +kernel
def pointBounds73492 : List (Nat × Nat × Nat) := [(9636679680,116410207942191,116410597800962)]
theorem point_links_checked73492 : (cuts73492.take 1).map (fun c => (9636675585-1+2*2^10*c.k,116410202450954+c.lower,116410592309722+c.upper)) = pointBounds73492 := by
 decide +kernel
def cuts73493 : List PrefixCut := [⟨64,167187268,167187365⟩]
theorem checked73493 : checkPrefixCuts (2^48) 9636806657 10 Manual.Count131072.C073493.packed 64 cuts73493 = true := by
 decide +kernel
def cuts73494 : List PrefixCut := [⟨22,59584016,59584052⟩,
⟨64,167623123,167623225⟩]
theorem checked73494 : checkPrefixCuts (2^48) 9636937729 10 Manual.Count131072.C073494.packed 64 cuts73494 = true := by
 decide +kernel
def pointBounds73494 : List (Nat × Nat × Nat) := [(9636982784,116410593841424,116410983700426)]
theorem point_links_checked73494 : (cuts73494.take 1).map (fun c => (9636937729-1+2*2^10*c.k,116410534257408+c.lower,116410924116374+c.upper)) = pointBounds73494 := by
 decide +kernel
def cuts73495 : List PrefixCut := [⟨64,167533206,167533305⟩]
theorem checked73495 : checkPrefixCuts (2^48) 9637068801 10 Manual.Count131072.C073495.packed 64 cuts73495 = true := by
 decide +kernel
def cuts73496 : List PrefixCut := [⟨42,108328739,108328806⟩,
⟨64,166275018,166275122⟩]
theorem checked73496 : checkPrefixCuts (2^48) 9637199873 10 Manual.Count131072.C073496.packed 64 cuts73496 = true := by
 decide +kernel
def pointBounds73496 : List (Nat × Nat × Nat) := [(9637285888,116410977742476,116411367601710)]
theorem point_links_checked73496 : (cuts73496.take 1).map (fun c => (9637199873-1+2*2^10*c.k,116410869413737+c.lower,116411259272904+c.upper)) = pointBounds73496 := by
 decide +kernel
def cuts73497 : List PrefixCut := [⟨64,167441018,167441108⟩]
theorem checked73497 : checkPrefixCuts (2^48) 9637330945 10 Manual.Count131072.C073497.packed 64 cuts73497 = true := by
 decide +kernel
def cuts73498 : List PrefixCut := [⟨62,161655962,161656060⟩,
⟨64,167059060,167059162⟩]
theorem checked73498 : checkPrefixCuts (2^48) 9637462017 10 Manual.Count131072.C073498.packed 64 cuts73498 = true := by
 decide +kernel
def pointBounds73498 : List (Nat × Nat × Nat) := [(9637588992,116411364785735,116411754645194)]
theorem point_links_checked73498 : (cuts73498.take 1).map (fun c => (9637462017-1+2*2^10*c.k,116411203129773+c.lower,116411592989134+c.upper)) = pointBounds73498 := by
 decide +kernel
def cuts73499 : List PrefixCut := [⟨64,165100018,165100121⟩]
theorem checked73499 : checkPrefixCuts (2^48) 9637593089 10 Manual.Count131072.C073499.packed 64 cuts73499 = true := by
 decide +kernel
def cuts73500 : List PrefixCut := [⟨64,166820877,166820984⟩]
theorem checked73500 : checkPrefixCuts (2^48) 9637724161 10 Manual.Count131072.C073500.packed 64 cuts73500 = true := by
 decide +kernel
def cuts73501 : List PrefixCut := [⟨18,45063445,45063472⟩,
⟨64,165095507,165095605⟩]
theorem checked73501 : checkPrefixCuts (2^48) 9637855233 10 Manual.Count131072.C073501.packed 64 cuts73501 = true := by
 decide +kernel
def pointBounds73501 : List (Nat × Nat × Nat) := [(9637892096,116411747173173,116412137032873)]
theorem point_links_checked73501 : (cuts73501.take 1).map (fun c => (9637855233-1+2*2^10*c.k,116411702109728+c.lower,116412091969401+c.upper)) = pointBounds73501 := by
 decide +kernel
def cuts73502 : List PrefixCut := [⟨64,163983501,163983607⟩]
theorem checked73502 : checkPrefixCuts (2^48) 9637986305 10 Manual.Count131072.C073502.packed 64 cuts73502 = true := by
 decide +kernel
def cuts73503 : List PrefixCut := [⟨38,101134234,101134294⟩,
⟨64,169325641,169325739⟩]
theorem checked73503 : checkPrefixCuts (2^48) 9638117377 10 Manual.Count131072.C073503.packed 64 cuts73503 = true := by
 decide +kernel
def pointBounds73503 : List (Nat × Nat × Nat) := [(9638195200,116412132322970,116412522182907)]
theorem point_links_checked73503 : (cuts73503.take 1).map (fun c => (9638117377-1+2*2^10*c.k,116412031188736+c.lower,116412421048613+c.upper)) = pointBounds73503 := by
 decide +kernel
def cuts73504 : List PrefixCut := [⟨64,167658723,167658824⟩]
theorem checked73504 : checkPrefixCuts (2^48) 9638248449 10 Manual.Count131072.C073504.packed 64 cuts73504 = true := by
 decide +kernel
def cuts73505 : List PrefixCut := [⟨58,149784085,149784174⟩,
⟨64,165203359,165203458⟩]
theorem checked73505 : checkPrefixCuts (2^48) 9638379521 10 Manual.Count131072.C073505.packed 64 cuts73505 = true := by
 decide +kernel
def pointBounds73505 : List (Nat × Nat × Nat) := [(9638498304,116412517957185,116412907817350)]
theorem point_links_checked73505 : (cuts73505.take 1).map (fun c => (9638379521-1+2*2^10*c.k,116412368173100+c.lower,116412758033176+c.upper)) = pointBounds73505 := by
 decide +kernel
def cuts73506 : List PrefixCut := [⟨64,166047994,166048095⟩]
theorem checked73506 : checkPrefixCuts (2^48) 9638510593 10 Manual.Count131072.C073506.packed 64 cuts73506 = true := by
 decide +kernel
def cuts73507 : List PrefixCut := [⟨64,165432480,165432580⟩]
theorem checked73507 : checkPrefixCuts (2^48) 9638641665 10 Manual.Count131072.C073507.packed 64 cuts73507 = true := by
 decide +kernel
def cuts73508 : List PrefixCut := [⟨14,35276395,35276418⟩,
⟨64,166452300,166452404⟩]
theorem checked73508 : checkPrefixCuts (2^48) 9638772737 10 Manual.Count131072.C073508.packed 64 cuts73508 = true := by
 decide +kernel
def pointBounds73508 : List (Nat × Nat × Nat) := [(9638801408,116412900133328,116413289993727)]
theorem point_links_checked73508 : (cuts73508.take 1).map (fun c => (9638772737-1+2*2^10*c.k,116412864856933+c.lower,116413254717309+c.upper)) = pointBounds73508 := by
 decide +kernel
def cuts73509 : List PrefixCut := [⟨64,165661598,165661694⟩]
theorem checked73509 : checkPrefixCuts (2^48) 9638903809 10 Manual.Count131072.C073509.packed 64 cuts73509 = true := by
 decide +kernel
def cuts73510 : List PrefixCut := [⟨34,90261707,90261758⟩,
⟨64,167937054,167937154⟩]
theorem checked73510 : checkPrefixCuts (2^48) 9639034881 10 Manual.Count131072.C073510.packed 64 cuts73510 = true := by
 decide +kernel
def pointBounds73510 : List (Nat × Nat × Nat) := [(9639104512,116413287232538,116413677093165)]
theorem point_links_checked73510 : (cuts73510.take 1).map (fun c => (9639034881-1+2*2^10*c.k,116413196970831+c.lower,116413586831407+c.upper)) = pointBounds73510 := by
 decide +kernel
def cuts73511 : List PrefixCut := [⟨64,167963966,167964065⟩]
theorem checked73511 : checkPrefixCuts (2^48) 9639165953 10 Manual.Count131072.C073511.packed 64 cuts73511 = true := by
 decide +kernel
def cuts73512 : List PrefixCut := [⟨54,140980504,140980592⟩,
⟨64,167815675,167815778⟩]
theorem checked73512 : checkPrefixCuts (2^48) 9639297025 10 Manual.Count131072.C073512.packed 64 cuts73512 = true := by
 decide +kernel
def pointBounds73512 : List (Nat × Nat × Nat) := [(9639407616,116413673852355,116414063713218)]
theorem point_links_checked73512 : (cuts73512.take 1).map (fun c => (9639297025-1+2*2^10*c.k,116413532871851+c.lower,116413922732626+c.upper)) = pointBounds73512 := by
 decide +kernel
def cuts73513 : List PrefixCut := [⟨64,166353395,166353492⟩]
theorem checked73513 : checkPrefixCuts (2^48) 9639428097 10 Manual.Count131072.C073513.packed 64 cuts73513 = true := by
 decide +kernel
def cuts73514 : List PrefixCut := [⟨64,165387535,165387643⟩]
theorem checked73514 : checkPrefixCuts (2^48) 9639559169 10 Manual.Count131072.C073514.packed 64 cuts73514 = true := by
 decide +kernel
def cuts73515 : List PrefixCut := [⟨10,25608004,25608017⟩,
⟨64,164596902,164596997⟩]
theorem checked73515 : checkPrefixCuts (2^48) 9639690241 10 Manual.Count131072.C073515.packed 64 cuts73515 = true := by
 decide +kernel
def pointBounds73515 : List (Nat × Nat × Nat) := [(9639710720,116414058036460,116414447897556)]
theorem point_links_checked73515 : (cuts73515.take 1).map (fun c => (9639690241-1+2*2^10*c.k,116414032428456+c.lower,116414422289539+c.upper)) = pointBounds73515 := by
 decide +kernel
def cuts73516 : List PrefixCut := [⟨64,165324645,165324741⟩]
theorem checked73516 : checkPrefixCuts (2^48) 9639821313 10 Manual.Count131072.C073516.packed 64 cuts73516 = true := by
 decide +kernel
def cuts73517 : List PrefixCut := [⟨30,78135700,78135745⟩,
⟨64,165701981,165702082⟩]
theorem checked73517 : checkPrefixCuts (2^48) 9639952385 10 Manual.Count131072.C073517.packed 64 cuts73517 = true := by
 decide +kernel
def pointBounds73517 : List (Nat × Nat × Nat) := [(9640013824,116414440485703,116414830347022)]
theorem point_links_checked73517 : (cuts73517.take 1).map (fun c => (9639952385-1+2*2^10*c.k,116414362350003+c.lower,116414752211277+c.upper)) = pointBounds73517 := by
 decide +kernel
def cuts73518 : List PrefixCut := [⟨64,165933303,165933410⟩]
theorem checked73518 : checkPrefixCuts (2^48) 9640083457 10 Manual.Count131072.C073518.packed 64 cuts73518 = true := by
 decide +kernel
def cuts73519 : List PrefixCut := [⟨50,130193149,130193231⟩,
⟨64,165843465,165843563⟩]
theorem checked73519 : checkPrefixCuts (2^48) 9640214529 10 Manual.Count131072.C073519.packed 64 cuts73519 = true := by
 decide +kernel
def pointBounds73519 : List (Nat × Nat × Nat) := [(9640316928,116414824178436,116415214040000)]
theorem point_links_checked73519 : (cuts73519.take 1).map (fun c => (9640214529-1+2*2^10*c.k,116414693985287+c.lower,116415083846769+c.upper)) = pointBounds73519 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000109
