import PlattAssemblyKernel
import PlattCertificates.Count131072.C060480
import PlattCertificates.Count131072.C060481
import PlattCertificates.Count131072.C060482
import PlattCertificates.Count131072.C060483
import PlattCertificates.Count131072.C060484
import PlattCertificates.Count131072.C060485
import PlattCertificates.Count131072.C060486
import PlattCertificates.Count131072.C060487
import PlattCertificates.Count131072.C060488
import PlattCertificates.Count131072.C060489
import PlattCertificates.Count131072.C060490
import PlattCertificates.Count131072.C060491
import PlattCertificates.Count131072.C060492
import PlattCertificates.Count131072.C060493
import PlattCertificates.Count131072.C060494
import PlattCertificates.Count131072.C060495
import PlattCertificates.Count131072.C060496
import PlattCertificates.Count131072.C060497
import PlattCertificates.Count131072.C060498
import PlattCertificates.Count131072.C060499
import PlattCertificates.Count131072.C060500
import PlattCertificates.Count131072.C060501
import PlattCertificates.Count131072.C060502
import PlattCertificates.Count131072.C060503
import PlattCertificates.Count131072.C060504
import PlattCertificates.Count131072.C060505
import PlattCertificates.Count131072.C060506
import PlattCertificates.Count131072.C060507
import PlattCertificates.Count131072.C060508
import PlattCertificates.Count131072.C060509
import PlattCertificates.Count131072.C060510
import PlattCertificates.Count131072.C060511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60480 : List PrefixCut := [⟨64,203638333,203638452⟩]
theorem checked60480 : checkPrefixCuts (2^48) 7931166721 10 Manual.Count131072.C060480.packed 64 cuts60480 = true := by
 decide +kernel
def cuts60481 : List PrefixCut := [⟨10,32082135,32082154⟩,
⟨64,203528505,203528621⟩]
theorem checked60481 : checkPrefixCuts (2^48) 7931297793 10 Manual.Count131072.C060481.packed 64 cuts60481 = true := by
 decide +kernel
def pointBounds60481 : List (Nat × Nat × Nat) := [(7931318272,114015385274922,114015773738479)]
theorem point_links_checked60481 : (cuts60481.take 1).map (fun c => (7931297793-1+2*2^10*c.k,114015353192787+c.lower,114015741656325+c.upper)) = pointBounds60481 := by
 decide +kernel
def cuts60482 : List PrefixCut := [⟨64,205086613,205086730⟩]
theorem checked60482 : checkPrefixCuts (2^48) 7931428865 10 Manual.Count131072.C060482.packed 64 cuts60482 = true := by
 decide +kernel
def cuts60483 : List PrefixCut := [⟨4,12988587,12988595⟩,
⟨64,204763856,204763979⟩]
theorem checked60483 : checkPrefixCuts (2^48) 7931559937 10 Manual.Count131072.C060483.packed 64 cuts60483 = true := by
 decide +kernel
def pointBounds60483 : List (Nat × Nat × Nat) := [(7931568128,114015774796492,114016163260271)]
theorem point_links_checked60483 : (cuts60483.take 1).map (fun c => (7931559937-1+2*2^10*c.k,114015761807905+c.lower,114016150271676+c.upper)) = pointBounds60483 := by
 decide +kernel
def cuts60484 : List PrefixCut := [⟨62,199189043,199189161⟩,
⟨64,205718614,205718736⟩]
theorem checked60484 : checkPrefixCuts (2^48) 7931691009 10 Manual.Count131072.C060484.packed 64 cuts60484 = true := by
 decide +kernel
def pointBounds60484 : List (Nat × Nat × Nat) := [(7931817984,114016165760804,114016554224816)]
theorem point_links_checked60484 : (cuts60484.take 1).map (fun c => (7931691009-1+2*2^10*c.k,114015966571761+c.lower,114016355035655+c.upper)) = pointBounds60484 := by
 decide +kernel
def cuts60485 : List PrefixCut := [⟨64,204366721,204366837⟩]
theorem checked60485 : checkPrefixCuts (2^48) 7931822081 10 Manual.Count131072.C060485.packed 64 cuts60485 = true := by
 decide +kernel
def cuts60486 : List PrefixCut := [⟨56,177607151,177607254⟩,
⟨64,203369735,203369852⟩]
theorem checked60486 : checkPrefixCuts (2^48) 7931953153 10 Manual.Count131072.C060486.packed 64 cuts60486 = true := by
 decide +kernel
def pointBounds60486 : List (Nat × Nat × Nat) := [(7932067840,114016554264247,114016942728482)]
theorem point_links_checked60486 : (cuts60486.take 1).map (fun c => (7931953153-1+2*2^10*c.k,114016376657096+c.lower,114016765121228+c.upper)) = pointBounds60486 := by
 decide +kernel
def cuts60487 : List PrefixCut := [⟨64,207731088,207731202⟩]
theorem checked60487 : checkPrefixCuts (2^48) 7932084225 10 Manual.Count131072.C060487.packed 64 cuts60487 = true := by
 decide +kernel
def cuts60488 : List PrefixCut := [⟨50,159042880,159042973⟩,
⟨64,204108204,204108323⟩]
theorem checked60488 : checkPrefixCuts (2^48) 7932215297 10 Manual.Count131072.C060488.packed 64 cuts60488 = true := by
 decide +kernel
def pointBounds60488 : List (Nat × Nat × Nat) := [(7932317696,114016946800799,114017335265255)]
theorem point_links_checked60488 : (cuts60488.take 1).map (fun c => (7932215297-1+2*2^10*c.k,114016787757919+c.lower,114017176222282+c.upper)) = pointBounds60488 := by
 decide +kernel
def cuts60489 : List PrefixCut := [⟨64,205204850,205204969⟩]
theorem checked60489 : checkPrefixCuts (2^48) 7932346369 10 Manual.Count131072.C060489.packed 64 cuts60489 = true := by
 decide +kernel
def cuts60490 : List PrefixCut := [⟨44,139770128,139770207⟩,
⟨64,203711148,203711263⟩]
theorem checked60490 : checkPrefixCuts (2^48) 7932477441 10 Manual.Count131072.C060490.packed 64 cuts60490 = true := by
 decide +kernel
def pointBounds60490 : List (Nat × Nat × Nat) := [(7932567552,114017336841101,114017725305781)]
theorem point_links_checked60490 : (cuts60490.take 1).map (fun c => (7932477441-1+2*2^10*c.k,114017197070973+c.lower,114017585535574+c.upper)) = pointBounds60490 := by
 decide +kernel
def cuts60491 : List PrefixCut := [⟨64,204985157,204985277⟩]
theorem checked60491 : checkPrefixCuts (2^48) 7932608513 10 Manual.Count131072.C060491.packed 64 cuts60491 = true := by
 decide +kernel
def cuts60492 : List PrefixCut := [⟨38,121243739,121243813⟩,
⟨64,202036748,202036868⟩]
theorem checked60492 : checkPrefixCuts (2^48) 7932739585 10 Manual.Count131072.C060492.packed 64 cuts60492 = true := by
 decide +kernel
def pointBounds60492 : List (Nat × Nat × Nat) := [(7932817408,114017727011017,114018115475927)]
theorem point_links_checked60492 : (cuts60492.take 1).map (fun c => (7932739585-1+2*2^10*c.k,114017605767278+c.lower,114017994232114+c.upper)) = pointBounds60492 := by
 decide +kernel
def cuts60493 : List PrefixCut := [⟨64,203665556,203665672⟩]
theorem checked60493 : checkPrefixCuts (2^48) 7932870657 10 Manual.Count131072.C060493.packed 64 cuts60493 = true := by
 decide +kernel
def cuts60494 : List PrefixCut := [⟨32,102824999,102825054⟩,
⟨64,206394251,206394364⟩]
theorem checked60494 : checkPrefixCuts (2^48) 7933001729 10 Manual.Count131072.C060494.packed 64 cuts60494 = true := by
 decide +kernel
def pointBounds60494 : List (Nat × Nat × Nat) := [(7933067264,114018114294581,114018502759708)]
theorem point_links_checked60494 : (cuts60494.take 1).map (fun c => (7933001729-1+2*2^10*c.k,114018011469582+c.lower,114018399934654+c.upper)) = pointBounds60494 := by
 decide +kernel
def cuts60495 : List PrefixCut := [⟨64,200217211,200217330⟩]
theorem checked60495 : checkPrefixCuts (2^48) 7933132801 10 Manual.Count131072.C060495.packed 64 cuts60495 = true := by
 decide +kernel
def cuts60496 : List PrefixCut := [⟨26,83910718,83910766⟩,
⟨64,206742218,206742336⟩]
theorem checked60496 : checkPrefixCuts (2^48) 7933263873 10 Manual.Count131072.C060496.packed 64 cuts60496 = true := by
 decide +kernel
def pointBounds60496 : List (Nat × Nat × Nat) := [(7933317120,114018501991762,114018890457114)]
theorem point_links_checked60496 : (cuts60496.take 1).map (fun c => (7933263873-1+2*2^10*c.k,114018418081044+c.lower,114018806546348+c.upper)) = pointBounds60496 := by
 decide +kernel
def cuts60497 : List PrefixCut := [⟨64,205319639,205319757⟩]
theorem checked60497 : checkPrefixCuts (2^48) 7933394945 10 Manual.Count131072.C060497.packed 64 cuts60497 = true := by
 decide +kernel
def cuts60498 : List PrefixCut := [⟨20,63968773,63968809⟩,
⟨64,204429273,204429388⟩]
theorem checked60498 : checkPrefixCuts (2^48) 7933526017 10 Manual.Count131072.C060498.packed 64 cuts60498 = true := by
 decide +kernel
def pointBounds60498 : List (Nat × Nat × Nat) := [(7933566976,114018894111674,114019282577250)]
theorem point_links_checked60498 : (cuts60498.take 1).map (fun c => (7933526017-1+2*2^10*c.k,114018830142901+c.lower,114019218608441+c.upper)) = pointBounds60498 := by
 decide +kernel
def cuts60499 : List PrefixCut := [⟨64,202581021,202581138⟩]
theorem checked60499 : checkPrefixCuts (2^48) 7933657089 10 Manual.Count131072.C060499.packed 64 cuts60499 = true := by
 decide +kernel
def cuts60500 : List PrefixCut := [⟨14,45766530,45766556⟩,
⟨64,205699716,205699838⟩]
theorem checked60500 : checkPrefixCuts (2^48) 7933788161 10 Manual.Count131072.C060500.packed 64 cuts60500 = true := by
 decide +kernel
def pointBounds60500 : List (Nat × Nat × Nat) := [(7933816832,114019282919725,114019671385523)]
theorem point_links_checked60500 : (cuts60500.take 1).map (fun c => (7933788161-1+2*2^10*c.k,114019237153195+c.lower,114019625618967+c.upper)) = pointBounds60500 := by
 decide +kernel
def cuts60501 : List PrefixCut := [⟨64,203461259,203461379⟩]
theorem checked60501 : checkPrefixCuts (2^48) 7933919233 10 Manual.Count131072.C060501.packed 64 cuts60501 = true := by
 decide +kernel
def cuts60502 : List PrefixCut := [⟨8,25614239,25614254⟩,
⟨64,202961237,202961357⟩]
theorem checked60502 : checkPrefixCuts (2^48) 7934050305 10 Manual.Count131072.C060502.packed 64 cuts60502 = true := by
 decide +kernel
def pointBounds60502 : List (Nat × Nat × Nat) := [(7934066688,114019671928409,114020060394438)]
theorem point_links_checked60502 : (cuts60502.take 1).map (fun c => (7934050305-1+2*2^10*c.k,114019646314170+c.lower,114020034780184+c.upper)) = pointBounds60502 := by
 decide +kernel
def cuts60503 : List PrefixCut := [⟨64,202532179,202532294⟩]
theorem checked60503 : checkPrefixCuts (2^48) 7934181377 10 Manual.Count131072.C060503.packed 64 cuts60503 = true := by
 decide +kernel
def cuts60504 : List PrefixCut := [⟨2,6350140,6350144⟩,
⟨64,206431090,206431212⟩]
theorem checked60504 : checkPrefixCuts (2^48) 7934312449 10 Manual.Count131072.C060504.packed 64 cuts60504 = true := by
 decide +kernel
def pointBounds60504 : List (Nat × Nat × Nat) := [(7934316544,114020058157726,114020446623979)]
theorem point_links_checked60504 : (cuts60504.take 1).map (fun c => (7934312449-1+2*2^10*c.k,114020051807586+c.lower,114020440273835+c.upper)) = pointBounds60504 := by
 decide +kernel
def cuts60505 : List PrefixCut := [⟨60,191563862,191563978⟩,
⟨64,205611764,205611887⟩]
theorem checked60505 : checkPrefixCuts (2^48) 7934443521 10 Manual.Count131072.C060505.packed 64 cuts60505 = true := by
 decide +kernel
def pointBounds60505 : List (Nat × Nat × Nat) := [(7934566400,114020449802538,114020838269025)]
theorem point_links_checked60505 : (cuts60505.take 1).map (fun c => (7934443521-1+2*2^10*c.k,114020258238676+c.lower,114020646705047+c.upper)) = pointBounds60505 := by
 decide +kernel
def cuts60506 : List PrefixCut := [⟨64,204082988,204083107⟩]
theorem checked60506 : checkPrefixCuts (2^48) 7934574593 10 Manual.Count131072.C060506.packed 64 cuts60506 = true := by
 decide +kernel
def cuts60507 : List PrefixCut := [⟨54,169351188,169351289⟩,
⟨64,201348151,201348272⟩]
theorem checked60507 : checkPrefixCuts (2^48) 7934705665 10 Manual.Count131072.C060507.packed 64 cuts60507 = true := by
 decide +kernel
def pointBounds60507 : List (Nat × Nat × Nat) := [(7934816256,114020837284616,114021225751330)]
theorem point_links_checked60507 : (cuts60507.take 1).map (fun c => (7934705665-1+2*2^10*c.k,114020667933428+c.lower,114021056400041+c.upper)) = pointBounds60507 := by
 decide +kernel
def cuts60508 : List PrefixCut := [⟨64,205459692,205459808⟩]
theorem checked60508 : checkPrefixCuts (2^48) 7934836737 10 Manual.Count131072.C060508.packed 64 cuts60508 = true := by
 decide +kernel
def cuts60509 : List PrefixCut := [⟨48,155334086,155334169⟩,
⟨64,205208009,205208122⟩]
theorem checked60509 : checkPrefixCuts (2^48) 7934967809 10 Manual.Count131072.C060509.packed 64 cuts60509 = true := by
 decide +kernel
def pointBounds60509 : List (Nat × Nat × Nat) := [(7935066112,114021230075357,114021618542290)]
theorem point_links_checked60509 : (cuts60509.take 1).map (fun c => (7934967809-1+2*2^10*c.k,114021074741271+c.lower,114021463208121+c.upper)) = pointBounds60509 := by
 decide +kernel
def cuts60510 : List PrefixCut := [⟨64,203856685,203856801⟩]
theorem checked60510 : checkPrefixCuts (2^48) 7935098881 10 Manual.Count131072.C060510.packed 64 cuts60510 = true := by
 decide +kernel
def cuts60511 : List PrefixCut := [⟨42,134046258,134046334⟩,
⟨64,203250306,203250421⟩]
theorem checked60511 : checkPrefixCuts (2^48) 7935229953 10 Manual.Count131072.C060511.packed 64 cuts60511 = true := by
 decide +kernel
def pointBounds60511 : List (Nat × Nat × Nat) := [(7935315968,114021617852223,114022006319378)]
theorem point_links_checked60511 : (cuts60511.take 1).map (fun c => (7935229953-1+2*2^10*c.k,114021483805965+c.lower,114021872273044+c.upper)) = pointBounds60511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000015
