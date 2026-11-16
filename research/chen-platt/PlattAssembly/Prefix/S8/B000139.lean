import PlattAssemblyKernel
import PlattCertificates.Count131072.C074448
import PlattCertificates.Count131072.C074449
import PlattCertificates.Count131072.C074450
import PlattCertificates.Count131072.C074451
import PlattCertificates.Count131072.C074452
import PlattCertificates.Count131072.C074453
import PlattCertificates.Count131072.C074454
import PlattCertificates.Count131072.C074455
import PlattCertificates.Count131072.C074456
import PlattCertificates.Count131072.C074457
import PlattCertificates.Count131072.C074458
import PlattCertificates.Count131072.C074459
import PlattCertificates.Count131072.C074460
import PlattCertificates.Count131072.C074461
import PlattCertificates.Count131072.C074462
import PlattCertificates.Count131072.C074463
import PlattCertificates.Count131072.C074464
import PlattCertificates.Count131072.C074465
import PlattCertificates.Count131072.C074466
import PlattCertificates.Count131072.C074467
import PlattCertificates.Count131072.C074468
import PlattCertificates.Count131072.C074469
import PlattCertificates.Count131072.C074470
import PlattCertificates.Count131072.C074471
import PlattCertificates.Count131072.C074472
import PlattCertificates.Count131072.C074473
import PlattCertificates.Count131072.C074474
import PlattCertificates.Count131072.C074475
import PlattCertificates.Count131072.C074476
import PlattCertificates.Count131072.C074477
import PlattCertificates.Count131072.C074478
import PlattCertificates.Count131072.C074479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000139
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74448 : List PrefixCut := [⟨64,166860013,166860113⟩]
theorem checked74448 : checkPrefixCuts (2^48) 9761980417 10 Manual.Count131072.C074448.packed 64 cuts74448 = true := by
 decide +kernel
def cuts74449 : List PrefixCut := [⟨64,161177632,161177727⟩]
theorem checked74449 : checkPrefixCuts (2^48) 9762111489 10 Manual.Count131072.C074449.packed 64 cuts74449 = true := by
 decide +kernel
def cuts74450 : List PrefixCut := [⟨20,51466824,51466853⟩,
⟨64,165183234,165183333⟩]
theorem checked74450 : checkPrefixCuts (2^48) 9762242561 10 Manual.Count131072.C074450.packed 64 cuts74450 = true := by
 decide +kernel
def pointBounds74450 : List (Nat × Nat × Nat) := [(9762283520,116568747484901,116569137438320)]
theorem point_links_checked74450 : (cuts74450.take 1).map (fun c => (9762242561-1+2*2^10*c.k,116568696018077+c.lower,116569085971467+c.upper)) = pointBounds74450 := by
 decide +kernel
def cuts74451 : List PrefixCut := [⟨64,165065704,165065794⟩]
theorem checked74451 : checkPrefixCuts (2^48) 9762373633 10 Manual.Count131072.C074451.packed 64 cuts74451 = true := by
 decide +kernel
def cuts74452 : List PrefixCut := [⟨41,107082486,107082546⟩,
⟨64,166937558,166937655⟩]
theorem checked74452 : checkPrefixCuts (2^48) 9762504705 10 Manual.Count131072.C074452.packed 64 cuts74452 = true := by
 decide +kernel
def pointBounds74452 : List (Nat × Nat × Nat) := [(9762588672,116569133349501,116569523303140)]
theorem point_links_checked74452 : (cuts74452.take 1).map (fun c => (9762504705-1+2*2^10*c.k,116569026267015+c.lower,116569416220594+c.upper)) = pointBounds74452 := by
 decide +kernel
def cuts74453 : List PrefixCut := [⟨64,163100708,163100807⟩]
theorem checked74453 : checkPrefixCuts (2^48) 9762635777 10 Manual.Count131072.C074453.packed 64 cuts74453 = true := by
 decide +kernel
def cuts74454 : List PrefixCut := [⟨62,159436980,159437076⟩,
⟨64,165232029,165232127⟩]
theorem checked74454 : checkPrefixCuts (2^48) 9762766849 10 Manual.Count131072.C074454.packed 64 cuts74454 = true := by
 decide +kernel
def pointBounds74454 : List (Nat × Nat × Nat) := [(9762893824,116569515742261,116569905696132)]
theorem point_links_checked74454 : (cuts74454.take 1).map (fun c => (9762766849-1+2*2^10*c.k,116569356305281+c.lower,116569746259056+c.upper)) = pointBounds74454 := by
 decide +kernel
def cuts74455 : List PrefixCut := [⟨64,163788268,163788362⟩]
theorem checked74455 : checkPrefixCuts (2^48) 9762897921 10 Manual.Count131072.C074455.packed 64 cuts74455 = true := by
 decide +kernel
def cuts74456 : List PrefixCut := [⟨64,166092510,166092597⟩]
theorem checked74456 : checkPrefixCuts (2^48) 9763028993 10 Manual.Count131072.C074456.packed 64 cuts74456 = true := by
 decide +kernel
def cuts74457 : List PrefixCut := [⟨19,48953761,48953789⟩,
⟨64,162082897,162082989⟩]
theorem checked74457 : checkPrefixCuts (2^48) 9763160065 10 Manual.Count131072.C074457.packed 64 cuts74457 = true := by
 decide +kernel
def pointBounds74457 : List (Nat × Nat × Nat) := [(9763198976,116569900371849,116570290325931)]
theorem point_links_checked74457 : (cuts74457.take 1).map (fun c => (9763160065-1+2*2^10*c.k,116569851418088+c.lower,116570241372142+c.upper)) = pointBounds74457 := by
 decide +kernel
def cuts74458 : List PrefixCut := [⟨64,166289856,166289961⟩]
theorem checked74458 : checkPrefixCuts (2^48) 9763291137 10 Manual.Count131072.C074458.packed 64 cuts74458 = true := by
 decide +kernel
def cuts74459 : List PrefixCut := [⟨40,99173171,99173234⟩,
⟨64,162741597,162741695⟩]
theorem checked74459 : checkPrefixCuts (2^48) 9763422209 10 Manual.Count131072.C074459.packed 64 cuts74459 = true := by
 decide +kernel
def pointBounds74459 : List (Nat × Nat × Nat) := [(9763504128,116570278964012,116570668918326)]
theorem point_links_checked74459 : (cuts74459.take 1).map (fun c => (9763422209-1+2*2^10*c.k,116570179790841+c.lower,116570569745092+c.upper)) = pointBounds74459 := by
 decide +kernel
def cuts74460 : List PrefixCut := [⟨64,164007913,164008007⟩]
theorem checked74460 : checkPrefixCuts (2^48) 9763553281 10 Manual.Count131072.C074460.packed 64 cuts74460 = true := by
 decide +kernel
def cuts74461 : List PrefixCut := [⟨61,155270692,155270797⟩,
⟨64,162737242,162737353⟩]
theorem checked74461 : checkPrefixCuts (2^48) 9763684353 10 Manual.Count131072.C074461.packed 64 cuts74461 = true := by
 decide +kernel
def pointBounds74461 : List (Nat × Nat × Nat) := [(9763809280,116570661811043,116571051765591)]
theorem point_links_checked74461 : (cuts74461.take 1).map (fun c => (9763684353-1+2*2^10*c.k,116570506540351+c.lower,116570896494794+c.upper)) = pointBounds74461 := by
 decide +kernel
def cuts74462 : List PrefixCut := [⟨64,164205293,164205391⟩]
theorem checked74462 : checkPrefixCuts (2^48) 9763815425 10 Manual.Count131072.C074462.packed 64 cuts74462 = true := by
 decide +kernel
def cuts74463 : List PrefixCut := [⟨64,165096756,165096850⟩]
theorem checked74463 : checkPrefixCuts (2^48) 9763946497 10 Manual.Count131072.C074463.packed 64 cuts74463 = true := by
 decide +kernel
def cuts74464 : List PrefixCut := [⟨18,45922273,45922302⟩,
⟨64,163451371,163451474⟩]
theorem checked74464 : checkPrefixCuts (2^48) 9764077569 10 Manual.Count131072.C074464.packed 64 cuts74464 = true := by
 decide +kernel
def pointBounds74464 : List (Nat × Nat × Nat) := [(9764114432,116571044501915,116571434456690)]
theorem point_links_checked74464 : (cuts74464.take 1).map (fun c => (9764077569-1+2*2^10*c.k,116570998579642+c.lower,116571388534388+c.upper)) = pointBounds74464 := by
 decide +kernel
def cuts74465 : List PrefixCut := [⟨64,164256337,164256438⟩]
theorem checked74465 : checkPrefixCuts (2^48) 9764208641 10 Manual.Count131072.C074465.packed 64 cuts74465 = true := by
 decide +kernel
def cuts74466 : List PrefixCut := [⟨39,98846773,98846829⟩,
⟨64,161775045,161775141⟩]
theorem checked74466 : checkPrefixCuts (2^48) 9764339713 10 Manual.Count131072.C074466.packed 64 cuts74466 = true := by
 decide +kernel
def pointBounds74466 : List (Nat × Nat × Nat) := [(9764419584,116571425134123,116571815089129)]
theorem point_links_checked74466 : (cuts74466.take 1).map (fun c => (9764339713-1+2*2^10*c.k,116571326287350+c.lower,116571716242300+c.upper)) = pointBounds74466 := by
 decide +kernel
def cuts74467 : List PrefixCut := [⟨64,163127709,163127807⟩]
theorem checked74467 : checkPrefixCuts (2^48) 9764470785 10 Manual.Count131072.C074467.packed 64 cuts74467 = true := by
 decide +kernel
def cuts74468 : List PrefixCut := [⟨60,154939040,154939135⟩,
⟨64,165431585,165431687⟩]
theorem checked74468 : checkPrefixCuts (2^48) 9764601857 10 Manual.Count131072.C074468.packed 64 cuts74468 = true := by
 decide +kernel
def pointBounds74468 : List (Nat × Nat × Nat) := [(9764724736,116571806129144,116572196084383)]
theorem point_links_checked74468 : (cuts74468.take 1).map (fun c => (9764601857-1+2*2^10*c.k,116571651190104+c.lower,116572041145248+c.upper)) = pointBounds74468 := by
 decide +kernel
def cuts74469 : List PrefixCut := [⟨64,164795198,164795299⟩]
theorem checked74469 : checkPrefixCuts (2^48) 9764732929 10 Manual.Count131072.C074469.packed 64 cuts74469 = true := by
 decide +kernel
def cuts74470 : List PrefixCut := [⟨64,165023593,165023693⟩]
theorem checked74470 : checkPrefixCuts (2^48) 9764864001 10 Manual.Count131072.C074470.packed 64 cuts74470 = true := by
 decide +kernel
def cuts74471 : List PrefixCut := [⟨17,45139694,45139723⟩,
⟨64,165742002,165742106⟩]
theorem checked74471 : checkPrefixCuts (2^48) 9764995073 10 Manual.Count131072.C074471.packed 64 cuts74471 = true := by
 decide +kernel
def pointBounds74471 : List (Nat × Nat × Nat) := [(9765029888,116572191580174,116572581535650)]
theorem point_links_checked74471 : (cuts74471.take 1).map (fun c => (9764995073-1+2*2^10*c.k,116572146440480+c.lower,116572536395927+c.upper)) = pointBounds74471 := by
 decide +kernel
def cuts74472 : List PrefixCut := [⟨64,164154430,164154528⟩]
theorem checked74472 : checkPrefixCuts (2^48) 9765126145 10 Manual.Count131072.C074472.packed 64 cuts74472 = true := by
 decide +kernel
def cuts74473 : List PrefixCut := [⟨39,99731025,99731082⟩,
⟨64,163201040,163201135⟩]
theorem checked74473 : checkPrefixCuts (2^48) 9765257217 10 Manual.Count131072.C074473.packed 64 cuts74473 = true := by
 decide +kernel
def pointBounds74473 : List (Nat × Nat × Nat) := [(9765337088,116572576067937,116572966023643)]
theorem point_links_checked74473 : (cuts74473.take 1).map (fun c => (9765257217-1+2*2^10*c.k,116572476336912+c.lower,116572866292561+c.upper)) = pointBounds74473 := by
 decide +kernel
def cuts74474 : List PrefixCut := [⟨64,166167671,166167772⟩]
theorem checked74474 : checkPrefixCuts (2^48) 9765388289 10 Manual.Count131072.C074474.packed 64 cuts74474 = true := by
 decide +kernel
def cuts74475 : List PrefixCut := [⟨61,156567373,156567474⟩,
⟨64,164407219,164407325⟩]
theorem checked74475 : checkPrefixCuts (2^48) 9765519361 10 Manual.Count131072.C074475.packed 64 cuts74475 = true := by
 decide +kernel
def pointBounds74475 : List (Nat × Nat × Nat) := [(9765644288,116572962272996,116573352228942)]
theorem point_links_checked74475 : (cuts74475.take 1).map (fun c => (9765519361-1+2*2^10*c.k,116572805705623+c.lower,116573195661468+c.upper)) = pointBounds74475 := by
 decide +kernel
def cuts74476 : List PrefixCut := [⟨64,161695687,161695788⟩]
theorem checked74476 : checkPrefixCuts (2^48) 9765650433 10 Manual.Count131072.C074476.packed 64 cuts74476 = true := by
 decide +kernel
def cuts74477 : List PrefixCut := [⟨64,165959218,165959320⟩]
theorem checked74477 : checkPrefixCuts (2^48) 9765781505 10 Manual.Count131072.C074477.packed 64 cuts74477 = true := by
 decide +kernel
def cuts74478 : List PrefixCut := [⟨19,49775806,49775834⟩,
⟨64,163391853,163391953⟩]
theorem checked74478 : checkPrefixCuts (2^48) 9765912577 10 Manual.Count131072.C074478.packed 64 cuts74478 = true := by
 decide +kernel
def pointBounds74478 : List (Nat × Nat × Nat) := [(9765951488,116573347543553,116573737499735)]
theorem point_links_checked74478 : (cuts74478.take 1).map (fun c => (9765912577-1+2*2^10*c.k,116573297767747+c.lower,116573687723901+c.upper)) = pointBounds74478 := by
 decide +kernel
def cuts74479 : List PrefixCut := [⟨64,162496194,162496288⟩]
theorem checked74479 : checkPrefixCuts (2^48) 9766043649 10 Manual.Count131072.C074479.packed 64 cuts74479 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000139
