import PlattAssemblyKernel
import PlattCertificates.Count131072.C057488
import PlattCertificates.Count131072.C057489
import PlattCertificates.Count131072.C057490
import PlattCertificates.Count131072.C057491
import PlattCertificates.Count131072.C057492
import PlattCertificates.Count131072.C057493
import PlattCertificates.Count131072.C057494
import PlattCertificates.Count131072.C057495
import PlattCertificates.Count131072.C057496
import PlattCertificates.Count131072.C057497
import PlattCertificates.Count131072.C057498
import PlattCertificates.Count131072.C057499
import PlattCertificates.Count131072.C057500
import PlattCertificates.Count131072.C057501
import PlattCertificates.Count131072.C057502
import PlattCertificates.Count131072.C057503
import PlattCertificates.Count131072.C057504
import PlattCertificates.Count131072.C057505
import PlattCertificates.Count131072.C057506
import PlattCertificates.Count131072.C057507
import PlattCertificates.Count131072.C057508
import PlattCertificates.Count131072.C057509
import PlattCertificates.Count131072.C057510
import PlattCertificates.Count131072.C057511
import PlattCertificates.Count131072.C057512
import PlattCertificates.Count131072.C057513
import PlattCertificates.Count131072.C057514
import PlattCertificates.Count131072.C057515
import PlattCertificates.Count131072.C057516
import PlattCertificates.Count131072.C057517
import PlattCertificates.Count131072.C057518
import PlattCertificates.Count131072.C057519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000234
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57488 : List PrefixCut := [⟨64,213820525,213820649⟩]
theorem checked57488 : checkPrefixCuts (2^48) 7538999297 10 Manual.Count131072.C057488.packed 64 cuts57488 = true := by
 decide +kernel
def pointBounds57488 : List (Nat × Nat × Nat) := [(7539130368,113388527700470,113388915806346)]
theorem point_links_checked57488 : (cuts57488.take 1).map (fun c => (7538999297-1+2*2^10*c.k,113388313879945+c.lower,113388701985697+c.upper)) = pointBounds57488 := by
 decide +kernel
def cuts57489 : List PrefixCut := [⟨64,214339484,214339606⟩]
theorem checked57489 : checkPrefixCuts (2^48) 7539130369 10 Manual.Count131072.C057489.packed 64 cuts57489 = true := by
 decide +kernel
def cuts57490 : List PrefixCut := [⟨52,173156408,173156505⟩,
⟨64,214597099,214597220⟩]
theorem checked57490 : checkPrefixCuts (2^48) 7539261441 10 Manual.Count131072.C057490.packed 64 cuts57490 = true := by
 decide +kernel
def pointBounds57490 : List (Nat × Nat × Nat) := [(7539367936,113388915196362,113389303302457)]
theorem point_links_checked57490 : (cuts57490.take 1).map (fun c => (7539261441-1+2*2^10*c.k,113388742039954+c.lower,113389130145952+c.upper)) = pointBounds57490 := by
 decide +kernel
def cuts57491 : List PrefixCut := [⟨64,214182686,214182810⟩]
theorem checked57491 : checkPrefixCuts (2^48) 7539392513 10 Manual.Count131072.C057491.packed 64 cuts57491 = true := by
 decide +kernel
def cuts57492 : List PrefixCut := [⟨40,131337656,131337731⟩,
⟨64,212685656,212685774⟩]
theorem checked57492 : checkPrefixCuts (2^48) 7539523585 10 Manual.Count131072.C057492.packed 64 cuts57492 = true := by
 decide +kernel
def pointBounds57492 : List (Nat × Nat × Nat) := [(7539605504,113389302157395,113389690263713)]
theorem point_links_checked57492 : (cuts57492.take 1).map (fun c => (7539523585-1+2*2^10*c.k,113389170819739+c.lower,113389558925982+c.upper)) = pointBounds57492 := by
 decide +kernel
def cuts57493 : List PrefixCut := [⟨64,217049857,217049981⟩]
theorem checked57493 : checkPrefixCuts (2^48) 7539654657 10 Manual.Count131072.C057493.packed 64 cuts57493 = true := by
 decide +kernel
def cuts57494 : List PrefixCut := [⟨28,93105530,93105585⟩,
⟨64,215888775,215888899⟩]
theorem checked57494 : checkPrefixCuts (2^48) 7539785729 10 Manual.Count131072.C057494.packed 64 cuts57494 = true := by
 decide +kernel
def pointBounds57494 : List (Nat × Nat × Nat) := [(7539843072,113389693660782,113390081767322)]
theorem point_links_checked57494 : (cuts57494.take 1).map (fun c => (7539785729-1+2*2^10*c.k,113389600555252+c.lower,113389988661737+c.upper)) = pointBounds57494 := by
 decide +kernel
def cuts57495 : List PrefixCut := [⟨64,211554619,211554739⟩]
theorem checked57495 : checkPrefixCuts (2^48) 7539916801 10 Manual.Count131072.C057495.packed 64 cuts57495 = true := by
 decide +kernel
def cuts57496 : List PrefixCut := [⟨16,54689288,54689320⟩,
⟨64,212857531,212857650⟩]
theorem checked57496 : checkPrefixCuts (2^48) 7540047873 10 Manual.Count131072.C057496.packed 64 cuts57496 = true := by
 decide +kernel
def pointBounds57496 : List (Nat × Nat × Nat) := [(7540080640,113390082687934,113390470794695)]
theorem point_links_checked57496 : (cuts57496.take 1).map (fun c => (7540047873-1+2*2^10*c.k,113390027998646+c.lower,113390416105375+c.upper)) = pointBounds57496 := by
 decide +kernel
def cuts57497 : List PrefixCut := [⟨64,218191966,218192089⟩]
theorem checked57497 : checkPrefixCuts (2^48) 7540178945 10 Manual.Count131072.C057497.packed 64 cuts57497 = true := by
 decide +kernel
def cuts57498 : List PrefixCut := [⟨4,12729303,12729310⟩,
⟨64,214455252,214455377⟩]
theorem checked57498 : checkPrefixCuts (2^48) 7540310017 10 Manual.Count131072.C057498.packed 64 cuts57498 = true := by
 decide +kernel
def pointBounds57498 : List (Nat × Nat × Nat) := [(7540318208,113390471777446,113390859884424)]
theorem point_links_checked57498 : (cuts57498.take 1).map (fun c => (7540310017-1+2*2^10*c.k,113390459048143+c.lower,113390847155114+c.upper)) = pointBounds57498 := by
 decide +kernel
def cuts57499 : List PrefixCut := [⟨56,186306146,186306251⟩,
⟨64,214040922,214041043⟩]
theorem checked57499 : checkPrefixCuts (2^48) 7540441089 10 Manual.Count131072.C057499.packed 64 cuts57499 = true := by
 decide +kernel
def pointBounds57499 : List (Nat × Nat × Nat) := [(7540555776,113390859809541,113391247916742)]
theorem point_links_checked57499 : (cuts57499.take 1).map (fun c => (7540441089-1+2*2^10*c.k,113390673503395+c.lower,113391061610491+c.upper)) = pointBounds57499 := by
 decide +kernel
def cuts57500 : List PrefixCut := [⟨64,213365302,213365430⟩]
theorem checked57500 : checkPrefixCuts (2^48) 7540572161 10 Manual.Count131072.C057500.packed 64 cuts57500 = true := by
 decide +kernel
def cuts57501 : List PrefixCut := [⟨44,145837317,145837402⟩,
⟨64,211196646,211196770⟩]
theorem checked57501 : checkPrefixCuts (2^48) 7540703233 10 Manual.Count131072.C057501.packed 64 cuts57501 = true := by
 decide +kernel
def pointBounds57501 : List (Nat × Nat × Nat) := [(7540793344,113391246746936,113391634854366)]
theorem point_links_checked57501 : (cuts57501.take 1).map (fun c => (7540703233-1+2*2^10*c.k,113391100909619+c.lower,113391489016964+c.upper)) = pointBounds57501 := by
 decide +kernel
def cuts57502 : List PrefixCut := [⟨64,215298873,215298994⟩]
theorem checked57502 : checkPrefixCuts (2^48) 7540834305 10 Manual.Count131072.C057502.packed 64 cuts57502 = true := by
 decide +kernel
def cuts57503 : List PrefixCut := [⟨32,107125465,107125527⟩,
⟨64,211935811,211935932⟩]
theorem checked57503 : checkPrefixCuts (2^48) 7540965377 10 Manual.Count131072.C057503.packed 64 cuts57503 = true := by
 decide +kernel
def pointBounds57503 : List (Nat × Nat × Nat) := [(7541030912,113391634530603,113392022638255)]
theorem point_links_checked57503 : (cuts57503.take 1).map (fun c => (7540965377-1+2*2^10*c.k,113391527405138+c.lower,113391915512728+c.upper)) = pointBounds57503 := by
 decide +kernel
def cuts57504 : List PrefixCut := [⟨64,216187184,216187305⟩]
theorem checked57504 : checkPrefixCuts (2^48) 7541096449 10 Manual.Count131072.C057504.packed 64 cuts57504 = true := by
 decide +kernel
def cuts57505 : List PrefixCut := [⟨20,67968299,67968340⟩,
⟨64,216929927,216930053⟩]
theorem checked57505 : checkPrefixCuts (2^48) 7541227521 10 Manual.Count131072.C057505.packed 64 cuts57505 = true := by
 decide +kernel
def pointBounds57505 : List (Nat × Nat × Nat) := [(7541268480,113392023496432,113392411604305)]
theorem point_links_checked57505 : (cuts57505.take 1).map (fun c => (7541227521-1+2*2^10*c.k,113391955528133+c.lower,113392343635965+c.upper)) = pointBounds57505 := by
 decide +kernel
def cuts57506 : List PrefixCut := [⟨64,216067711,216067833⟩]
theorem checked57506 : checkPrefixCuts (2^48) 7541358593 10 Manual.Count131072.C057506.packed 64 cuts57506 = true := by
 decide +kernel
def cuts57507 : List PrefixCut := [⟨8,26648961,26648976⟩,
⟨64,211809096,211809215⟩]
theorem checked57507 : checkPrefixCuts (2^48) 7541489665 10 Manual.Count131072.C057507.packed 64 cuts57507 = true := by
 decide +kernel
def pointBounds57507 : List (Nat × Nat × Nat) := [(7541506048,113392415174732,113392803282827)]
theorem point_links_checked57507 : (cuts57507.take 1).map (fun c => (7541489665-1+2*2^10*c.k,113392388525771+c.lower,113392776633851+c.upper)) = pointBounds57507 := by
 decide +kernel
def cuts57508 : List PrefixCut := [⟨60,201728446,201728562⟩,
⟨64,215798929,215799053⟩]
theorem checked57508 : checkPrefixCuts (2^48) 7541620737 10 Manual.Count131072.C057508.packed 64 cuts57508 = true := by
 decide +kernel
def pointBounds57508 : List (Nat × Nat × Nat) := [(7541743616,113392802063313,113393190171628)]
theorem point_links_checked57508 : (cuts57508.take 1).map (fun c => (7541620737-1+2*2^10*c.k,113392600334867+c.lower,113392988443066+c.upper)) = pointBounds57508 := by
 decide +kernel
def cuts57509 : List PrefixCut := [⟨64,213406574,213406701⟩]
theorem checked57509 : checkPrefixCuts (2^48) 7541751809 10 Manual.Count131072.C057509.packed 64 cuts57509 = true := by
 decide +kernel
def cuts57510 : List PrefixCut := [⟨48,161787948,161788035⟩,
⟨64,214111991,214112109⟩]
theorem checked57510 : checkPrefixCuts (2^48) 7541882881 10 Manual.Count131072.C057510.packed 64 cuts57510 = true := by
 decide +kernel
def pointBounds57510 : List (Nat × Nat × Nat) := [(7541981184,113393191328318,113393579436855)]
theorem point_links_checked57510 : (cuts57510.take 1).map (fun c => (7541882881-1+2*2^10*c.k,113393029540370+c.lower,113393417648820+c.upper)) = pointBounds57510 := by
 decide +kernel
def cuts57511 : List PrefixCut := [⟨64,216347475,216347598⟩]
theorem checked57511 : checkPrefixCuts (2^48) 7542013953 10 Manual.Count131072.C057511.packed 64 cuts57511 = true := by
 decide +kernel
def cuts57512 : List PrefixCut := [⟨36,121775450,121775517⟩,
⟨64,214738983,214739104⟩]
theorem checked57512 : checkPrefixCuts (2^48) 7542145025 10 Manual.Count131072.C057512.packed 64 cuts57512 = true := by
 decide +kernel
def pointBounds57512 : List (Nat × Nat × Nat) := [(7542218752,113393581775286,113393969884044)]
theorem point_links_checked57512 : (cuts57512.take 1).map (fun c => (7542145025-1+2*2^10*c.k,113393459999836+c.lower,113393848108527+c.upper)) = pointBounds57512 := by
 decide +kernel
def cuts57513 : List PrefixCut := [⟨64,212981244,212981367⟩]
theorem checked57513 : checkPrefixCuts (2^48) 7542276097 10 Manual.Count131072.C057513.packed 64 cuts57513 = true := by
 decide +kernel
def cuts57514 : List PrefixCut := [⟨24,81280460,81280505⟩,
⟨64,214918104,214918227⟩]
theorem checked57514 : checkPrefixCuts (2^48) 7542407169 10 Manual.Count131072.C057514.packed 64 cuts57514 = true := by
 decide +kernel
def pointBounds57514 : List (Nat × Nat × Nat) := [(7542456320,113393969000523,113394357109503)]
theorem point_links_checked57514 : (cuts57514.take 1).map (fun c => (7542407169-1+2*2^10*c.k,113393887720063+c.lower,113394275828998+c.upper)) = pointBounds57514 := by
 decide +kernel
def cuts57515 : List PrefixCut := [⟨64,216668315,216668435⟩]
theorem checked57515 : checkPrefixCuts (2^48) 7542538241 10 Manual.Count131072.C057515.packed 64 cuts57515 = true := by
 decide +kernel
def cuts57516 : List PrefixCut := [⟨12,41086695,41086718⟩,
⟨64,214164291,214164413⟩]
theorem checked57516 : checkPrefixCuts (2^48) 7542669313 10 Manual.Count131072.C057516.packed 64 cuts57516 = true := by
 decide +kernel
def pointBounds57516 : List (Nat × Nat × Nat) := [(7542693888,113394360393177,113394748502378)]
theorem point_links_checked57516 : (cuts57516.take 1).map (fun c => (7542669313-1+2*2^10*c.k,113394319306482+c.lower,113394707415660+c.upper)) = pointBounds57516 := by
 decide +kernel
def cuts57517 : List PrefixCut := [⟨64,213153009,213153135⟩]
theorem checked57517 : checkPrefixCuts (2^48) 7542800385 10 Manual.Count131072.C057517.packed 64 cuts57517 = true := by
 decide +kernel
def pointBounds57517 : List (Nat × Nat × Nat) := [(7542931456,113394746623782,113395134733208)]
theorem point_links_checked57517 : (cuts57517.take 1).map (fun c => (7542800385-1+2*2^10*c.k,113394533470773+c.lower,113394921580073+c.upper)) = pointBounds57517 := by
 decide +kernel
def cuts57518 : List PrefixCut := [⟨64,217851115,217851237⟩]
theorem checked57518 : checkPrefixCuts (2^48) 7542931457 10 Manual.Count131072.C057518.packed 64 cuts57518 = true := by
 decide +kernel
def cuts57519 : List PrefixCut := [⟨52,172770617,172770717⟩,
⟨64,214003849,214003973⟩]
theorem checked57519 : checkPrefixCuts (2^48) 7543062529 10 Manual.Count131072.C057519.packed 64 cuts57519 = true := by
 decide +kernel
def pointBounds57519 : List (Nat × Nat × Nat) := [(7543169024,113395137245514,113395525355162)]
theorem point_links_checked57519 : (cuts57519.take 1).map (fun c => (7543062529-1+2*2^10*c.k,113394964474897+c.lower,113395352584445+c.upper)) = pointBounds57519 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000234
