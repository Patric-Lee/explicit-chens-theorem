import PlattAssemblyKernel
import PlattCertificates.Count131072.C066400
import PlattCertificates.Count131072.C066401
import PlattCertificates.Count131072.C066402
import PlattCertificates.Count131072.C066403
import PlattCertificates.Count131072.C066404
import PlattCertificates.Count131072.C066405
import PlattCertificates.Count131072.C066406
import PlattCertificates.Count131072.C066407
import PlattCertificates.Count131072.C066408
import PlattCertificates.Count131072.C066409
import PlattCertificates.Count131072.C066410
import PlattCertificates.Count131072.C066411
import PlattCertificates.Count131072.C066412
import PlattCertificates.Count131072.C066413
import PlattCertificates.Count131072.C066414
import PlattCertificates.Count131072.C066415
import PlattCertificates.Count131072.C066416
import PlattCertificates.Count131072.C066417
import PlattCertificates.Count131072.C066418
import PlattCertificates.Count131072.C066419
import PlattCertificates.Count131072.C066420
import PlattCertificates.Count131072.C066421
import PlattCertificates.Count131072.C066422
import PlattCertificates.Count131072.C066423
import PlattCertificates.Count131072.C066424
import PlattCertificates.Count131072.C066425
import PlattCertificates.Count131072.C066426
import PlattCertificates.Count131072.C066427
import PlattCertificates.Count131072.C066428
import PlattCertificates.Count131072.C066429
import PlattCertificates.Count131072.C066430
import PlattCertificates.Count131072.C066431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66400 : List PrefixCut := [⟨64,185200013,185200124⟩]
theorem checked66400 : checkPrefixCuts (2^48) 8707112961 10 Manual.Count131072.C066400.packed 64 cuts66400 = true := by
 decide +kernel
def cuts66401 : List PrefixCut := [⟨6,17294677,17294686⟩,
⟨64,185682133,185682233⟩]
theorem checked66401 : checkPrefixCuts (2^48) 8707244033 10 Manual.Count131072.C066401.packed 64 cuts66401 = true := by
 decide +kernel
def pointBounds66401 : List (Nat × Nat × Nat) := [(8707256320,115165675816380,115166064942444)]
theorem point_links_checked66401 : (cuts66401.take 1).map (fun c => (8707244033-1+2*2^10*c.k,115165658521703+c.lower,115166047647758+c.upper)) = pointBounds66401 := by
 decide +kernel
def cuts66402 : List PrefixCut := [⟨64,184450970,184451077⟩]
theorem checked66402 : checkPrefixCuts (2^48) 8707375105 10 Manual.Count131072.C066402.packed 64 cuts66402 = true := by
 decide +kernel
def cuts66403 : List PrefixCut := [⟨11,32293178,32293196⟩,
⟨64,186581658,186581760⟩]
theorem checked66403 : checkPrefixCuts (2^48) 8707506177 10 Manual.Count131072.C066403.packed 64 cuts66403 = true := by
 decide +kernel
def pointBounds66403 : List (Nat × Nat × Nat) := [(8707528704,115166060947984,115166450074264)]
theorem point_links_checked66403 : (cuts66403.take 1).map (fun c => (8707506177-1+2*2^10*c.k,115166028654806+c.lower,115166417781068+c.upper)) = pointBounds66403 := by
 decide +kernel
def cuts66404 : List PrefixCut := [⟨64,186029309,186029415⟩]
theorem checked66404 : checkPrefixCuts (2^48) 8707637249 10 Manual.Count131072.C066404.packed 64 cuts66404 = true := by
 decide +kernel
def cuts66405 : List PrefixCut := [⟨16,44090634,44090660⟩,
⟨64,184184022,184184131⟩]
theorem checked66405 : checkPrefixCuts (2^48) 8707768321 10 Manual.Count131072.C066405.packed 64 cuts66405 = true := by
 decide +kernel
def pointBounds66405 : List (Nat × Nat × Nat) := [(8707801088,115166445356407,115166834482903)]
theorem point_links_checked66405 : (cuts66405.take 1).map (fun c => (8707768321-1+2*2^10*c.k,115166401265773+c.lower,115166790392243+c.upper)) = pointBounds66405 := by
 decide +kernel
def cuts66406 : List PrefixCut := [⟨64,184245904,184246004⟩]
theorem checked66406 : checkPrefixCuts (2^48) 8707899393 10 Manual.Count131072.C066406.packed 64 cuts66406 = true := by
 decide +kernel
def cuts66407 : List PrefixCut := [⟨21,62319746,62319785⟩,
⟨64,185956274,185956389⟩]
theorem checked66407 : checkPrefixCuts (2^48) 8708030465 10 Manual.Count131072.C066407.packed 64 cuts66407 = true := by
 decide +kernel
def pointBounds66407 : List (Nat × Nat × Nat) := [(8708073472,115166832015445,115167221142163)]
theorem point_links_checked66407 : (cuts66407.take 1).map (fun c => (8708030465-1+2*2^10*c.k,115166769695699+c.lower,115167158822378+c.upper)) = pointBounds66407 := by
 decide +kernel
def cuts66408 : List PrefixCut := [⟨64,187763546,187763658⟩]
theorem checked66408 : checkPrefixCuts (2^48) 8708161537 10 Manual.Count131072.C066408.packed 64 cuts66408 = true := by
 decide +kernel
def cuts66409 : List PrefixCut := [⟨26,75731685,75731729⟩,
⟨64,186629440,186629549⟩]
theorem checked66409 : checkPrefixCuts (2^48) 8708292609 10 Manual.Count131072.C066409.packed 64 cuts66409 = true := by
 decide +kernel
def pointBounds66409 : List (Nat × Nat × Nat) := [(8708345856,115167219147204,115167608274154)]
theorem point_links_checked66409 : (cuts66409.take 1).map (fun c => (8708292609-1+2*2^10*c.k,115167143415519+c.lower,115167532542425+c.upper)) = pointBounds66409 := by
 decide +kernel
def cuts66410 : List PrefixCut := [⟨64,185333762,185333868⟩]
theorem checked66410 : checkPrefixCuts (2^48) 8708423681 10 Manual.Count131072.C066410.packed 64 cuts66410 = true := by
 decide +kernel
def cuts66411 : List PrefixCut := [⟨31,89950845,89950896⟩,
⟨64,185040084,185040192⟩]
theorem checked66411 : checkPrefixCuts (2^48) 8708554753 10 Manual.Count131072.C066411.packed 64 cuts66411 = true := by
 decide +kernel
def pointBounds66411 : List (Nat × Nat × Nat) := [(8708618240,115167605329566,115167994456738)]
theorem point_links_checked66411 : (cuts66411.take 1).map (fun c => (8708554753-1+2*2^10*c.k,115167515378721+c.lower,115167904505842+c.upper)) = pointBounds66411 := by
 decide +kernel
def cuts66412 : List PrefixCut := [⟨64,184940334,184940437⟩]
theorem checked66412 : checkPrefixCuts (2^48) 8708685825 10 Manual.Count131072.C066412.packed 64 cuts66412 = true := by
 decide +kernel
def cuts66413 : List PrefixCut := [⟨36,106076028,106076090⟩,
⟨64,190205769,190205881⟩]
theorem checked66413 : checkPrefixCuts (2^48) 8708816897 10 Manual.Count131072.C066413.packed 64 cuts66413 = true := by
 decide +kernel
def pointBounds66413 : List (Nat × Nat × Nat) := [(8708890624,115167991435167,115168380562561)]
theorem point_links_checked66413 : (cuts66413.take 1).map (fun c => (8708816897-1+2*2^10*c.k,115167885359139+c.lower,115168274486471+c.upper)) = pointBounds66413 := by
 decide +kernel
def cuts66414 : List PrefixCut := [⟨64,188845490,188845597⟩]
theorem checked66414 : checkPrefixCuts (2^48) 8708947969 10 Manual.Count131072.C066414.packed 64 cuts66414 = true := by
 decide +kernel
def cuts66415 : List PrefixCut := [⟨41,119937863,119937933⟩,
⟨64,186160126,186160232⟩]
theorem checked66415 : checkPrefixCuts (2^48) 8709079041 10 Manual.Count131072.C066415.packed 64 cuts66415 = true := by
 decide +kernel
def pointBounds66415 : List (Nat × Nat × Nat) := [(8709163008,115168384348261,115168773475882)]
theorem point_links_checked66415 : (cuts66415.take 1).map (fun c => (8709079041-1+2*2^10*c.k,115168264410398+c.lower,115168653537949+c.upper)) = pointBounds66415 := by
 decide +kernel
def cuts66416 : List PrefixCut := [⟨64,184121217,184121323⟩]
theorem checked66416 : checkPrefixCuts (2^48) 8709210113 10 Manual.Count131072.C066416.packed 64 cuts66416 = true := by
 decide +kernel
def cuts66417 : List PrefixCut := [⟨46,133992749,133992830⟩,
⟨64,185992921,185993035⟩]
theorem checked66417 : checkPrefixCuts (2^48) 8709341185 10 Manual.Count131072.C066417.packed 64 cuts66417 = true := by
 decide +kernel
def pointBounds66417 : List (Nat × Nat × Nat) := [(8709435392,115168768684490,115169157812334)]
theorem point_links_checked66417 : (cuts66417.take 1).map (fun c => (8709341185-1+2*2^10*c.k,115168634691741+c.lower,115169023819504+c.upper)) = pointBounds66417 := by
 decide +kernel
def cuts66418 : List PrefixCut := [⟨64,184632767,184632876⟩]
theorem checked66418 : checkPrefixCuts (2^48) 8709472257 10 Manual.Count131072.C066418.packed 64 cuts66418 = true := by
 decide +kernel
def cuts66419 : List PrefixCut := [⟨51,145461382,145461464⟩,
⟨64,183531193,183531294⟩]
theorem checked66419 : checkPrefixCuts (2^48) 8709603329 10 Manual.Count131072.C066419.packed 64 cuts66419 = true := by
 decide +kernel
def pointBounds66419 : List (Nat × Nat × Nat) := [(8709707776,115169150778811,115169539906879)]
theorem point_links_checked66419 : (cuts66419.take 1).map (fun c => (8709603329-1+2*2^10*c.k,115169005317429+c.lower,115169394445415+c.upper)) = pointBounds66419 := by
 decide +kernel
def cuts66420 : List PrefixCut := [⟨64,183883922,183884026⟩]
theorem checked66420 : checkPrefixCuts (2^48) 8709734401 10 Manual.Count131072.C066420.packed 64 cuts66420 = true := by
 decide +kernel
def cuts66421 : List PrefixCut := [⟨56,161098136,161098228⟩,
⟨64,184656743,184656848⟩]
theorem checked66421 : checkPrefixCuts (2^48) 8709865473 10 Manual.Count131072.C066421.packed 64 cuts66421 = true := by
 decide +kernel
def pointBounds66421 : List (Nat × Nat × Nat) := [(8709980160,115169533830680,115169922958963)]
theorem point_links_checked66421 : (cuts66421.take 1).map (fun c => (8709865473-1+2*2^10*c.k,115169372732544+c.lower,115169761860735+c.upper)) = pointBounds66421 := by
 decide +kernel
def cuts66422 : List PrefixCut := [⟨64,186334404,186334507⟩]
theorem checked66422 : checkPrefixCuts (2^48) 8709996545 10 Manual.Count131072.C066422.packed 64 cuts66422 = true := by
 decide +kernel
def cuts66423 : List PrefixCut := [⟨61,178931396,178931500⟩,
⟨64,187656539,187656647⟩]
theorem checked66423 : checkPrefixCuts (2^48) 8710127617 10 Manual.Count131072.C066423.packed 64 cuts66423 = true := by
 decide +kernel
def pointBounds66423 : List (Nat × Nat × Nat) := [(8710252544,115169922655087,115170311783590)]
theorem point_links_checked66423 : (cuts66423.take 1).map (fun c => (8710127617-1+2*2^10*c.k,115169743723691+c.lower,115170132852090+c.upper)) = pointBounds66423 := by
 decide +kernel
def cuts66424 : List PrefixCut := [⟨64,184228307,184228418⟩]
theorem checked66424 : checkPrefixCuts (2^48) 8710258689 10 Manual.Count131072.C066424.packed 64 cuts66424 = true := by
 decide +kernel
def cuts66425 : List PrefixCut := [⟨64,181640368,181640474⟩]
theorem checked66425 : checkPrefixCuts (2^48) 8710389761 10 Manual.Count131072.C066425.packed 64 cuts66425 = true := by
 decide +kernel
def cuts66426 : List PrefixCut := [⟨2,5558068,5558072⟩,
⟨64,183124086,183124194⟩]
theorem checked66426 : checkPrefixCuts (2^48) 8710520833 10 Manual.Count131072.C066426.packed 64 cuts66426 = true := by
 decide +kernel
def pointBounds66426 : List (Nat × Nat × Nat) := [(8710524928,115170302806973,115170691935701)]
theorem point_links_checked66426 : (cuts66426.take 1).map (fun c => (8710520833-1+2*2^10*c.k,115170297248905+c.lower,115170686377629+c.upper)) = pointBounds66426 := by
 decide +kernel
def cuts66427 : List PrefixCut := [⟨64,186061892,186062000⟩]
theorem checked66427 : checkPrefixCuts (2^48) 8710651905 10 Manual.Count131072.C066427.packed 64 cuts66427 = true := by
 decide +kernel
def cuts66428 : List PrefixCut := [⟨7,21682264,21682276⟩,
⟨64,184960438,184960548⟩]
theorem checked66428 : checkPrefixCuts (2^48) 8710782977 10 Manual.Count131072.C066428.packed 64 cuts66428 = true := by
 decide +kernel
def pointBounds66428 : List (Nat × Nat × Nat) := [(8710797312,115170688117147,115171077246099)]
theorem point_links_checked66428 : (cuts66428.take 1).map (fun c => (8710782977-1+2*2^10*c.k,115170666434883+c.lower,115171055563823+c.upper)) = pointBounds66428 := by
 decide +kernel
def cuts66429 : List PrefixCut := [⟨64,186573288,186573391⟩]
theorem checked66429 : checkPrefixCuts (2^48) 8710914049 10 Manual.Count131072.C066429.packed 64 cuts66429 = true := by
 decide +kernel
def cuts66430 : List PrefixCut := [⟨12,33701801,33701820⟩,
⟨64,184243994,184244102⟩]
theorem checked66430 : checkPrefixCuts (2^48) 8711045121 10 Manual.Count131072.C066430.packed 64 cuts66430 = true := by
 decide +kernel
def pointBounds66430 : List (Nat × Nat × Nat) := [(8711069696,115171071670410,115171460799582)]
theorem point_links_checked66430 : (cuts66430.take 1).map (fun c => (8711045121-1+2*2^10*c.k,115171037968609+c.lower,115171427097762+c.upper)) = pointBounds66430 := by
 decide +kernel
def cuts66431 : List PrefixCut := [⟨64,185307514,185307619⟩]
theorem checked66431 : checkPrefixCuts (2^48) 8711176193 10 Manual.Count131072.C066431.packed 64 cuts66431 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000200
