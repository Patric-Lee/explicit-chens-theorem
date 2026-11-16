import PlattAssemblyKernel
import PlattCertificates.Count131072.C045472
import PlattCertificates.Count131072.C045473
import PlattCertificates.Count131072.C045474
import PlattCertificates.Count131072.C045475
import PlattCertificates.Count131072.C045476
import PlattCertificates.Count131072.C045477
import PlattCertificates.Count131072.C045478
import PlattCertificates.Count131072.C045479
import PlattCertificates.Count131072.C045480
import PlattCertificates.Count131072.C045481
import PlattCertificates.Count131072.C045482
import PlattCertificates.Count131072.C045483
import PlattCertificates.Count131072.C045484
import PlattCertificates.Count131072.C045485
import PlattCertificates.Count131072.C045486
import PlattCertificates.Count131072.C045487
import PlattCertificates.Count131072.C045488
import PlattCertificates.Count131072.C045489
import PlattCertificates.Count131072.C045490
import PlattCertificates.Count131072.C045491
import PlattCertificates.Count131072.C045492
import PlattCertificates.Count131072.C045493
import PlattCertificates.Count131072.C045494
import PlattCertificates.Count131072.C045495
import PlattCertificates.Count131072.C045496
import PlattCertificates.Count131072.C045497
import PlattCertificates.Count131072.C045498
import PlattCertificates.Count131072.C045499
import PlattCertificates.Count131072.C045500
import PlattCertificates.Count131072.C045501
import PlattCertificates.Count131072.C045502
import PlattCertificates.Count131072.C045503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000171
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45472 : List PrefixCut := [⟨64,271936608,271936763⟩]
theorem checked45472 : checkPrefixCuts (2^48) 5964038145 10 Manual.Count131072.C045472.packed 64 cuts45472 = true := by
 decide +kernel
def cuts45473 : List PrefixCut := [⟨26,112038815,112038879⟩,
⟨64,274101605,274101764⟩]
theorem checked45473 : checkPrefixCuts (2^48) 5964169217 10 Manual.Count131072.C045473.packed 64 cuts45473 = true := by
 decide +kernel
def pointBounds45473 : List (Nat × Nat × Nat) := [(5964222464,110473401248881,110473787693581)]
theorem point_links_checked45473 : (cuts45473.take 1).map (fun c => (5964169217-1+2*2^10*c.k,110473289210066+c.lower,110473675654702+c.upper)) = pointBounds45473 := by
 decide +kernel
def cuts45474 : List PrefixCut := [⟨54,232094403,232094540⟩,
⟨64,272349455,272349615⟩]
theorem checked45474 : checkPrefixCuts (2^48) 5964300289 10 Manual.Count131072.C045474.packed 64 cuts45474 = true := by
 decide +kernel
def pointBounds45474 : List (Nat × Nat × Nat) := [(5964410880,110473795406074,110474181851006)]
theorem point_links_checked45474 : (cuts45474.take 1).map (fun c => (5964300289-1+2*2^10*c.k,110473563311671+c.lower,110473949756466+c.upper)) = pointBounds45474 := by
 decide +kernel
def cuts45475 : List PrefixCut := [⟨64,275080576,275080733⟩]
theorem checked45475 : checkPrefixCuts (2^48) 5964431361 10 Manual.Count131072.C045475.packed 64 cuts45475 = true := by
 decide +kernel
def cuts45476 : List PrefixCut := [⟨18,76166374,76166415⟩,
⟨64,274744175,274744335⟩]
theorem checked45476 : checkPrefixCuts (2^48) 5964562433 10 Manual.Count131072.C045476.packed 64 cuts45476 = true := by
 decide +kernel
def pointBounds45476 : List (Nat × Nat × Nat) := [(5964599296,110474186908076,110474573353229)]
theorem point_links_checked45476 : (cuts45476.take 1).map (fun c => (5964562433-1+2*2^10*c.k,110474110741702+c.lower,110474497186814+c.upper)) = pointBounds45476 := by
 decide +kernel
def cuts45477 : List PrefixCut := [⟨46,195979234,195979354⟩,
⟨64,271482074,271482240⟩]
theorem checked45477 : checkPrefixCuts (2^48) 5964693505 10 Manual.Count131072.C045477.packed 64 cuts45477 = true := by
 decide +kernel
def pointBounds45477 : List (Nat × Nat × Nat) := [(5964787712,110474581465111,110474967910503)]
theorem point_links_checked45477 : (cuts45477.take 1).map (fun c => (5964693505-1+2*2^10*c.k,110474385485877+c.lower,110474771931149+c.upper)) = pointBounds45477 := by
 decide +kernel
def cuts45478 : List PrefixCut := [⟨64,273174891,273175050⟩]
theorem checked45478 : checkPrefixCuts (2^48) 5964824577 10 Manual.Count131072.C045478.packed 64 cuts45478 = true := by
 decide +kernel
def cuts45479 : List PrefixCut := [⟨10,43412973,43413000⟩,
⟨64,276094496,276094650⟩]
theorem checked45479 : checkPrefixCuts (2^48) 5964955649 10 Manual.Count131072.C045479.packed 64 cuts45479 = true := by
 decide +kernel
def pointBounds45479 : List (Nat × Nat × Nat) := [(5964976128,110474973555815,110475360001439)]
theorem point_links_checked45479 : (cuts45479.take 1).map (fun c => (5964955649-1+2*2^10*c.k,110474930142842+c.lower,110475316588439+c.upper)) = pointBounds45479 := by
 decide +kernel
def cuts45480 : List PrefixCut := [⟨38,161992130,161992222⟩,
⟨64,275616583,275616739⟩]
theorem checked45480 : checkPrefixCuts (2^48) 5965086721 10 Manual.Count131072.C045480.packed 64 cuts45480 = true := by
 decide +kernel
def pointBounds45480 : List (Nat × Nat × Nat) := [(5965164544,110475368229468,110475754675311)]
theorem point_links_checked45480 : (cuts45480.take 1).map (fun c => (5965086721-1+2*2^10*c.k,110475206237338+c.lower,110475592683089+c.upper)) = pointBounds45480 := by
 decide +kernel
def cuts45481 : List PrefixCut := [⟨64,276176737,276176898⟩]
theorem checked45481 : checkPrefixCuts (2^48) 5965217793 10 Manual.Count131072.C045481.packed 64 cuts45481 = true := by
 decide +kernel
def cuts45482 : List PrefixCut := [⟨2,9248254,9248259⟩,
⟨64,278199612,278199771⟩]
theorem checked45482 : checkPrefixCuts (2^48) 5965348865 10 Manual.Count131072.C045482.packed 64 cuts45482 = true := by
 decide +kernel
def pointBounds45482 : List (Nat × Nat × Nat) := [(5965352960,110475767278912,110476153724985)]
theorem point_links_checked45482 : (cuts45482.take 1).map (fun c => (5965348865-1+2*2^10*c.k,110475758030658+c.lower,110476144476726+c.upper)) = pointBounds45482 := by
 decide +kernel
def cuts45483 : List PrefixCut := [⟨30,130085470,130085545⟩,
⟨64,277202654,277202815⟩]
theorem checked45483 : checkPrefixCuts (2^48) 5965479937 10 Manual.Count131072.C045483.packed 64 cuts45483 = true := by
 decide +kernel
def pointBounds45483 : List (Nat × Nat × Nat) := [(5965541376,110476166315740,110476552762042)]
theorem point_links_checked45483 : (cuts45483.take 1).map (fun c => (5965479937-1+2*2^10*c.k,110476036230270+c.lower,110476422676497+c.upper)) = pointBounds45483 := by
 decide +kernel
def cuts45484 : List PrefixCut := [⟨58,249123281,249123423⟩,
⟨64,274884611,274884767⟩]
theorem checked45484 : checkPrefixCuts (2^48) 5965611009 10 Manual.Count131072.C045484.packed 64 cuts45484 = true := by
 decide +kernel
def pointBounds45484 : List (Nat × Nat × Nat) := [(5965729792,110476562556205,110476949002735)]
theorem point_links_checked45484 : (cuts45484.take 1).map (fun c => (5965611009-1+2*2^10*c.k,110476313432924+c.lower,110476699879312+c.upper)) = pointBounds45484 := by
 decide +kernel
def cuts45485 : List PrefixCut := [⟨64,274642680,274642835⟩]
theorem checked45485 : checkPrefixCuts (2^48) 5965742081 10 Manual.Count131072.C045485.packed 64 cuts45485 = true := by
 decide +kernel
def cuts45486 : List PrefixCut := [⟨22,93889509,93889562⟩,
⟨64,273457126,273457290⟩]
theorem checked45486 : checkPrefixCuts (2^48) 5965873153 10 Manual.Count131072.C045486.packed 64 cuts45486 = true := by
 decide +kernel
def pointBounds45486 : List (Nat × Nat × Nat) := [(5965918208,110476956849724,110477343296476)]
theorem point_links_checked45486 : (cuts45486.take 1).map (fun c => (5965873153-1+2*2^10*c.k,110476862960215+c.lower,110477249406914+c.upper)) = pointBounds45486 := by
 decide +kernel
def cuts45487 : List PrefixCut := [⟨50,215279595,215279718⟩,
⟨64,273734225,273734380⟩]
theorem checked45487 : checkPrefixCuts (2^48) 5966004225 10 Manual.Count131072.C045487.packed 64 cuts45487 = true := by
 decide +kernel
def pointBounds45487 : List (Nat × Nat × Nat) := [(5966106624,110477351696936,110477738143922)]
theorem point_links_checked45487 : (cuts45487.take 1).map (fun c => (5966004225-1+2*2^10*c.k,110477136417341+c.lower,110477522864204+c.upper)) = pointBounds45487 := by
 decide +kernel
def cuts45488 : List PrefixCut := [⟨64,275049176,275049336⟩]
theorem checked45488 : checkPrefixCuts (2^48) 5966135297 10 Manual.Count131072.C045488.packed 64 cuts45488 = true := by
 decide +kernel
def cuts45489 : List PrefixCut := [⟨14,59443792,59443826⟩,
⟨64,272589897,272590053⟩]
theorem checked45489 : checkPrefixCuts (2^48) 5966266369 10 Manual.Count131072.C045489.packed 64 cuts45489 = true := by
 decide +kernel
def pointBounds45489 : List (Nat × Nat × Nat) := [(5966295040,110477744644534,110478131091746)]
theorem point_links_checked45489 : (cuts45489.take 1).map (fun c => (5966266369-1+2*2^10*c.k,110477685200742+c.lower,110478071647920+c.upper)) = pointBounds45489 := by
 decide +kernel
def cuts45490 : List PrefixCut := [⟨42,179458838,179458938⟩,
⟨64,274754028,274754181⟩]
theorem checked45490 : checkPrefixCuts (2^48) 5966397441 10 Manual.Count131072.C045490.packed 64 cuts45490 = true := by
 decide +kernel
def pointBounds45490 : List (Nat × Nat × Nat) := [(5966483456,110478137249477,110478523696911)]
theorem point_links_checked45490 : (cuts45490.take 1).map (fun c => (5966397441-1+2*2^10*c.k,110477957790639+c.lower,110478344237973+c.upper)) = pointBounds45490 := by
 decide +kernel
def cuts45491 : List PrefixCut := [⟨64,278380469,278380628⟩]
theorem checked45491 : checkPrefixCuts (2^48) 5966528513 10 Manual.Count131072.C045491.packed 64 cuts45491 = true := by
 decide +kernel
def cuts45492 : List PrefixCut := [⟨6,26040363,26040379⟩,
⟨64,277808286,277808442⟩]
theorem checked45492 : checkPrefixCuts (2^48) 5966659585 10 Manual.Count131072.C045492.packed 64 cuts45492 = true := by
 decide +kernel
def pointBounds45492 : List (Nat × Nat × Nat) := [(5966671872,110478536965499,110478923413161)]
theorem point_links_checked45492 : (cuts45492.take 1).map (fun c => (5966659585-1+2*2^10*c.k,110478510925136+c.lower,110478897372782+c.upper)) = pointBounds45492 := by
 decide +kernel
def cuts45493 : List PrefixCut := [⟨34,144539019,144539099⟩,
⟨64,277283249,277283408⟩]
theorem checked45493 : checkPrefixCuts (2^48) 5966790657 10 Manual.Count131072.C045493.packed 64 cuts45493 = true := by
 decide +kernel
def pointBounds45493 : List (Nat × Nat × Nat) := [(5966860288,110478933272441,110479319720323)]
theorem point_links_checked45493 : (cuts45493.take 1).map (fun c => (5966790657-1+2*2^10*c.k,110478788733422+c.lower,110479175181224+c.upper)) = pointBounds45493 := by
 decide +kernel
def cuts45494 : List PrefixCut := [⟨62,263597421,263597578⟩,
⟨64,272041125,272041286⟩]
theorem checked45494 : checkPrefixCuts (2^48) 5966921729 10 Manual.Count131072.C045494.packed 64 cuts45494 = true := by
 decide +kernel
def pointBounds45494 : List (Nat × Nat × Nat) := [(5967048704,110479329614092,110479716062210)]
theorem point_links_checked45494 : (cuts45494.take 1).map (fun c => (5966921729-1+2*2^10*c.k,110479066016671+c.lower,110479452464632+c.upper)) = pointBounds45494 := by
 decide +kernel
def cuts45495 : List PrefixCut := [⟨64,278167339,278167494⟩]
theorem checked45495 : checkPrefixCuts (2^48) 5967052801 10 Manual.Count131072.C045495.packed 64 cuts45495 = true := by
 decide +kernel
def cuts45496 : List PrefixCut := [⟨26,111463336,111463400⟩,
⟨64,275755566,275755727⟩]
theorem checked45496 : checkPrefixCuts (2^48) 5967183873 10 Manual.Count131072.C045496.packed 64 cuts45496 = true := by
 decide +kernel
def pointBounds45496 : List (Nat × Nat × Nat) := [(5967237120,110479727688471,110480114136812)]
theorem point_links_checked45496 : (cuts45496.take 1).map (fun c => (5967183873-1+2*2^10*c.k,110479616225135+c.lower,110480002673412+c.upper)) = pointBounds45496 := by
 decide +kernel
def cuts45497 : List PrefixCut := [⟨54,230845075,230845209⟩,
⟨64,274334415,274334575⟩]
theorem checked45497 : checkPrefixCuts (2^48) 5967314945 10 Manual.Count131072.C045497.packed 64 cuts45497 = true := by
 decide +kernel
def pointBounds45497 : List (Nat × Nat × Nat) := [(5967425536,110480122825776,110480509274348)]
theorem point_links_checked45497 : (cuts45497.take 1).map (fun c => (5967314945-1+2*2^10*c.k,110479891980701+c.lower,110480278429139+c.upper)) = pointBounds45497 := by
 decide +kernel
def cuts45498 : List PrefixCut := [⟨64,270177639,270177796⟩]
theorem checked45498 : checkPrefixCuts (2^48) 5967446017 10 Manual.Count131072.C045498.packed 64 cuts45498 = true := by
 decide +kernel
def cuts45499 : List PrefixCut := [⟨18,76599564,76599612⟩,
⟨64,274133710,274133872⟩]
theorem checked45499 : checkPrefixCuts (2^48) 5967577089 10 Manual.Count131072.C045499.packed 64 cuts45499 = true := by
 decide +kernel
def pointBounds45499 : List (Nat × Nat × Nat) := [(5967613952,110480513092319,110480899541122)]
theorem point_links_checked45499 : (cuts45499.take 1).map (fun c => (5967577089-1+2*2^10*c.k,110480436492755+c.lower,110480822941510+c.upper)) = pointBounds45499 := by
 decide +kernel
def cuts45500 : List PrefixCut := [⟨46,199040324,199040441⟩,
⟨64,277193461,277193625⟩]
theorem checked45500 : checkPrefixCuts (2^48) 5967708161 10 Manual.Count131072.C045500.packed 64 cuts45500 = true := by
 decide +kernel
def pointBounds45500 : List (Nat × Nat × Nat) := [(5967802368,110480909666789,110481296115823)]
theorem point_links_checked45500 : (cuts45500.take 1).map (fun c => (5967708161-1+2*2^10*c.k,110480710626465+c.lower,110481097075382+c.upper)) = pointBounds45500 := by
 decide +kernel
def cuts45501 : List PrefixCut := [⟨64,271904897,271905059⟩]
theorem checked45501 : checkPrefixCuts (2^48) 5967839233 10 Manual.Count131072.C045501.packed 64 cuts45501 = true := by
 decide +kernel
def cuts45502 : List PrefixCut := [⟨10,43768355,43768382⟩,
⟨64,273644025,273644187⟩]
theorem checked45502 : checkPrefixCuts (2^48) 5967970305 10 Manual.Count131072.C045502.packed 64 cuts45502 = true := by
 decide +kernel
def pointBounds45502 : List (Nat × Nat × Nat) := [(5967990784,110481303493178,110481689942448)]
theorem point_links_checked45502 : (cuts45502.take 1).map (fun c => (5967970305-1+2*2^10*c.k,110481259724823+c.lower,110481646174066+c.upper)) = pointBounds45502 := by
 decide +kernel
def cuts45503 : List PrefixCut := [⟨38,164409931,164410024⟩,
⟨64,277458202,277458358⟩]
theorem checked45503 : checkPrefixCuts (2^48) 5968101377 10 Manual.Count131072.C045503.packed 64 cuts45503 = true := by
 decide +kernel
def pointBounds45503 : List (Nat × Nat × Nat) := [(5968179200,110481697778779,110482084228277)]
theorem point_links_checked45503 : (cuts45503.take 1).map (fun c => (5968101377-1+2*2^10*c.k,110481533368848+c.lower,110481919818253+c.upper)) = pointBounds45503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000171
