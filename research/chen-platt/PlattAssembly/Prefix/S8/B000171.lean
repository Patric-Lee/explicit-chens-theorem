import PlattAssemblyKernel
import PlattCertificates.Count131072.C075472
import PlattCertificates.Count131072.C075473
import PlattCertificates.Count131072.C075474
import PlattCertificates.Count131072.C075475
import PlattCertificates.Count131072.C075476
import PlattCertificates.Count131072.C075477
import PlattCertificates.Count131072.C075478
import PlattCertificates.Count131072.C075479
import PlattCertificates.Count131072.C075480
import PlattCertificates.Count131072.C075481
import PlattCertificates.Count131072.C075482
import PlattCertificates.Count131072.C075483
import PlattCertificates.Count131072.C075484
import PlattCertificates.Count131072.C075485
import PlattCertificates.Count131072.C075486
import PlattCertificates.Count131072.C075487
import PlattCertificates.Count131072.C075488
import PlattCertificates.Count131072.C075489
import PlattCertificates.Count131072.C075490
import PlattCertificates.Count131072.C075491
import PlattCertificates.Count131072.C075492
import PlattCertificates.Count131072.C075493
import PlattCertificates.Count131072.C075494
import PlattCertificates.Count131072.C075495
import PlattCertificates.Count131072.C075496
import PlattCertificates.Count131072.C075497
import PlattCertificates.Count131072.C075498
import PlattCertificates.Count131072.C075499
import PlattCertificates.Count131072.C075500
import PlattCertificates.Count131072.C075501
import PlattCertificates.Count131072.C075502
import PlattCertificates.Count131072.C075503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000171
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75472 : List PrefixCut := [⟨64,161894941,161895036⟩]
theorem checked75472 : checkPrefixCuts (2^48) 9896198145 10 Manual.Count131072.C075472.packed 64 cuts75472 = true := by
 decide +kernel
def cuts75473 : List PrefixCut := [⟨3,7764759,7764765⟩,
⟨64,160243162,160243261⟩]
theorem checked75473 : checkPrefixCuts (2^48) 9896329217 10 Manual.Count131072.C075473.packed 64 cuts75473 = true := by
 decide +kernel
def pointBounds75473 : List (Nat × Nat × Nat) := [(9896335360,116735593915079,116735983968622)]
theorem point_links_checked75473 : (cuts75473.take 1).map (fun c => (9896329217-1+2*2^10*c.k,116735586150320+c.lower,116735976203857+c.upper)) = pointBounds75473 := by
 decide +kernel
def cuts75474 : List PrefixCut := [⟨64,162260400,162260499⟩]
theorem checked75474 : checkPrefixCuts (2^48) 9896460289 10 Manual.Count131072.C075474.packed 64 cuts75474 = true := by
 decide +kernel
def cuts75475 : List PrefixCut := [⟨27,67264195,67264236⟩,
⟨64,160238912,160239012⟩]
theorem checked75475 : checkPrefixCuts (2^48) 9896591361 10 Manual.Count131072.C075475.packed 64 cuts75475 = true := by
 decide +kernel
def pointBounds75475 : List (Nat × Nat × Nat) := [(9896646656,116735975918077,116736365971853)]
theorem point_links_checked75475 : (cuts75475.take 1).map (fun c => (9896591361-1+2*2^10*c.k,116735908653882+c.lower,116736298707617+c.upper)) = pointBounds75475 := by
 decide +kernel
def cuts75476 : List PrefixCut := [⟨64,163649708,163649810⟩]
theorem checked75476 : checkPrefixCuts (2^48) 9896722433 10 Manual.Count131072.C075476.packed 64 cuts75476 = true := by
 decide +kernel
def cuts75477 : List PrefixCut := [⟨51,130741876,130741952⟩,
⟨64,163420020,163420116⟩]
theorem checked75477 : checkPrefixCuts (2^48) 9896853505 10 Manual.Count131072.C075477.packed 64 cuts75477 = true := by
 decide +kernel
def pointBounds75477 : List (Nat × Nat × Nat) := [(9896957952,116736363284378,116736753338391)]
theorem point_links_checked75477 : (cuts75477.take 1).map (fun c => (9896853505-1+2*2^10*c.k,116736232542502+c.lower,116736622596439+c.upper)) = pointBounds75477 := by
 decide +kernel
def cuts75478 : List PrefixCut := [⟨64,163304089,163304197⟩]
theorem checked75478 : checkPrefixCuts (2^48) 9896984577 10 Manual.Count131072.C075478.packed 64 cuts75478 = true := by
 decide +kernel
def cuts75479 : List PrefixCut := [⟨64,161595548,161595642⟩]
theorem checked75479 : checkPrefixCuts (2^48) 9897115649 10 Manual.Count131072.C075479.packed 64 cuts75479 = true := by
 decide +kernel
def cuts75480 : List PrefixCut := [⟨11,27415855,27415871⟩,
⟨64,162219063,162219157⟩]
theorem checked75480 : checkPrefixCuts (2^48) 9897246721 10 Manual.Count131072.C075480.packed 64 cuts75480 = true := by
 decide +kernel
def pointBounds75480 : List (Nat × Nat × Nat) := [(9897269248,116736748278014,116737138332265)]
theorem point_links_checked75480 : (cuts75480.take 1).map (fun c => (9897246721-1+2*2^10*c.k,116736720862159+c.lower,116737110916394+c.upper)) = pointBounds75480 := by
 decide +kernel
def cuts75481 : List PrefixCut := [⟨64,163638880,163638978⟩]
theorem checked75481 : checkPrefixCuts (2^48) 9897377793 10 Manual.Count131072.C075481.packed 64 cuts75481 = true := by
 decide +kernel
def cuts75482 : List PrefixCut := [⟨35,89326459,89326510⟩,
⟨64,164034847,164034948⟩]
theorem checked75482 : checkPrefixCuts (2^48) 9897508865 10 Manual.Count131072.C075482.packed 64 cuts75482 = true := by
 decide +kernel
def pointBounds75482 : List (Nat × Nat × Nat) := [(9897580544,116737136046561,116737526101039)]
theorem point_links_checked75482 : (cuts75482.take 1).map (fun c => (9897508865-1+2*2^10*c.k,116737046720102+c.lower,116737436774529+c.upper)) = pointBounds75482 := by
 decide +kernel
def cuts75483 : List PrefixCut := [⟨64,161786044,161786148⟩]
theorem checked75483 : checkPrefixCuts (2^48) 9897639937 10 Manual.Count131072.C075483.packed 64 cuts75483 = true := by
 decide +kernel
def cuts75484 : List PrefixCut := [⟨59,151091284,151091383⟩,
⟨64,163518623,163518730⟩]
theorem checked75484 : checkPrefixCuts (2^48) 9897771009 10 Manual.Count131072.C075484.packed 64 cuts75484 = true := by
 decide +kernel
def pointBounds75484 : List (Nat × Nat × Nat) := [(9897891840,116737523632277,116737913687008)]
theorem point_links_checked75484 : (cuts75484.take 1).map (fun c => (9897771009-1+2*2^10*c.k,116737372540993+c.lower,116737762595625+c.upper)) = pointBounds75484 := by
 decide +kernel
def cuts75485 : List PrefixCut := [⟨64,163288961,163289065⟩]
theorem checked75485 : checkPrefixCuts (2^48) 9897902081 10 Manual.Count131072.C075485.packed 64 cuts75485 = true := by
 decide +kernel
def cuts75486 : List PrefixCut := [⟨64,163628047,163628142⟩]
theorem checked75486 : checkPrefixCuts (2^48) 9898033153 10 Manual.Count131072.C075486.packed 64 cuts75486 = true := by
 decide +kernel
def cuts75487 : List PrefixCut := [⟨19,47660453,47660482⟩,
⟨64,159843771,159843869⟩]
theorem checked75487 : checkPrefixCuts (2^48) 9898164225 10 Manual.Count131072.C075487.packed 64 cuts75487 = true := by
 decide +kernel
def pointBounds75487 : List (Nat × Nat × Nat) := [(9898203136,116737910637077,116738300692044)]
theorem point_links_checked75487 : (cuts75487.take 1).map (fun c => (9898164225-1+2*2^10*c.k,116737862976624+c.lower,116738253031562+c.upper)) = pointBounds75487 := by
 decide +kernel
def cuts75488 : List PrefixCut := [⟨64,160239765,160239861⟩]
theorem checked75488 : checkPrefixCuts (2^48) 9898295297 10 Manual.Count131072.C075488.packed 64 cuts75488 = true := by
 decide +kernel
def cuts75489 : List PrefixCut := [⟨43,108484105,108484169⟩,
⟨64,161517270,161517367⟩]
theorem checked75489 : checkPrefixCuts (2^48) 9898426369 10 Manual.Count131072.C075489.packed 64 cuts75489 = true := by
 decide +kernel
def pointBounds75489 : List (Nat × Nat × Nat) := [(9898514432,116738291544265,116738681599461)]
theorem point_links_checked75489 : (cuts75489.take 1).map (fun c => (9898426369-1+2*2^10*c.k,116738183060160+c.lower,116738573115292+c.upper)) = pointBounds75489 := by
 decide +kernel
def cuts75490 : List PrefixCut := [⟨64,165723621,165723723⟩]
theorem checked75490 : checkPrefixCuts (2^48) 9898557441 10 Manual.Count131072.C075490.packed 64 cuts75490 = true := by
 decide +kernel
def cuts75491 : List PrefixCut := [⟨64,163787825,163787925⟩]
theorem checked75491 : checkPrefixCuts (2^48) 9898688513 10 Manual.Count131072.C075491.packed 64 cuts75491 = true := by
 decide +kernel
def cuts75492 : List PrefixCut := [⟨3,6938185,6938191⟩,
⟨64,162164856,162164951⟩]
theorem checked75492 : checkPrefixCuts (2^48) 9898819585 10 Manual.Count131072.C075492.packed 64 cuts75492 = true := by
 decide +kernel
def pointBounds75492 : List (Nat × Nat × Nat) := [(9898825728,116738681027061,116739071082498)]
theorem point_links_checked75492 : (cuts75492.take 1).map (fun c => (9898819585-1+2*2^10*c.k,116738674088876+c.lower,116739064144307+c.upper)) = pointBounds75492 := by
 decide +kernel
def cuts75493 : List PrefixCut := [⟨64,162589235,162589332⟩]
theorem checked75493 : checkPrefixCuts (2^48) 9898950657 10 Manual.Count131072.C075493.packed 64 cuts75493 = true := by
 decide +kernel
def cuts75494 : List PrefixCut := [⟨27,67958131,67958175⟩,
⟨64,162842974,162843079⟩]
theorem checked75494 : checkPrefixCuts (2^48) 9899081729 10 Manual.Count131072.C075494.packed 64 cuts75494 = true := by
 decide +kernel
def pointBounds75494 : List (Nat × Nat × Nat) := [(9899137024,116739066801098,116739456856765)]
theorem point_links_checked75494 : (cuts75494.take 1).map (fun c => (9899081729-1+2*2^10*c.k,116738998842967+c.lower,116739388898590+c.upper)) = pointBounds75494 := by
 decide +kernel
def cuts75495 : List PrefixCut := [⟨64,161276976,161277066⟩]
theorem checked75495 : checkPrefixCuts (2^48) 9899212801 10 Manual.Count131072.C075495.packed 64 cuts75495 = true := by
 decide +kernel
def cuts75496 : List PrefixCut := [⟨51,130680556,130680630⟩,
⟨64,163151444,163151541⟩]
theorem checked75496 : checkPrefixCuts (2^48) 9899343873 10 Manual.Count131072.C075496.packed 64 cuts75496 = true := by
 decide +kernel
def pointBounds75496 : List (Nat × Nat × Nat) := [(9899448320,116739453643473,116739843699365)]
theorem point_links_checked75496 : (cuts75496.take 1).map (fun c => (9899343873-1+2*2^10*c.k,116739322962917+c.lower,116739713018735+c.upper)) = pointBounds75496 := by
 decide +kernel
def cuts75497 : List PrefixCut := [⟨64,158912745,158912840⟩]
theorem checked75497 : checkPrefixCuts (2^48) 9899474945 10 Manual.Count131072.C075497.packed 64 cuts75497 = true := by
 decide +kernel
def cuts75498 : List PrefixCut := [⟨64,161782344,161782439⟩]
theorem checked75498 : checkPrefixCuts (2^48) 9899606017 10 Manual.Count131072.C075498.packed 64 cuts75498 = true := by
 decide +kernel
def cuts75499 : List PrefixCut := [⟨11,27465824,27465841⟩,
⟨64,161211557,161211654⟩]
theorem checked75499 : checkPrefixCuts (2^48) 9899737089 10 Manual.Count131072.C075499.packed 64 cuts75499 = true := by
 decide +kernel
def pointBounds75499 : List (Nat × Nat × Nat) := [(9899759616,116739834275274,116740224331396)]
theorem point_links_checked75499 : (cuts75499.take 1).map (fun c => (9899737089-1+2*2^10*c.k,116739806809450+c.lower,116740196865555+c.upper)) = pointBounds75499 := by
 decide +kernel
def cuts75500 : List PrefixCut := [⟨64,161948666,161948761⟩]
theorem checked75500 : checkPrefixCuts (2^48) 9899868161 10 Manual.Count131072.C075500.packed 64 cuts75500 = true := by
 decide +kernel
def cuts75501 : List PrefixCut := [⟨35,89531442,89531497⟩,
⟨64,163538683,163538784⟩]
theorem checked75501 : checkPrefixCuts (2^48) 9899999233 10 Manual.Count131072.C075501.packed 64 cuts75501 = true := by
 decide +kernel
def pointBounds75501 : List (Nat × Nat × Nat) := [(9900070912,116740219501115,116740609557467)]
theorem point_links_checked75501 : (cuts75501.take 1).map (fun c => (9899999233-1+2*2^10*c.k,116740129969673+c.lower,116740520025970+c.upper)) = pointBounds75501 := by
 decide +kernel
def cuts75502 : List PrefixCut := [⟨64,160295357,160295452⟩]
theorem checked75502 : checkPrefixCuts (2^48) 9900130305 10 Manual.Count131072.C075502.packed 64 cuts75502 = true := by
 decide +kernel
def cuts75503 : List PrefixCut := [⟨59,147641586,147641673⟩,
⟨64,160634414,160634509⟩]
theorem checked75503 : checkPrefixCuts (2^48) 9900261377 10 Manual.Count131072.C075503.packed 64 cuts75503 = true := by
 decide +kernel
def pointBounds75503 : List (Nat × Nat × Nat) := [(9900382208,116740601445299,116740991501879)]
theorem point_links_checked75503 : (cuts75503.take 1).map (fun c => (9900261377-1+2*2^10*c.k,116740453803713+c.lower,116740843860206+c.upper)) = pointBounds75503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000171
