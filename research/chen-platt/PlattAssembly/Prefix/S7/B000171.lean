import PlattAssemblyKernel
import PlattCertificates.Count131072.C065472
import PlattCertificates.Count131072.C065473
import PlattCertificates.Count131072.C065474
import PlattCertificates.Count131072.C065475
import PlattCertificates.Count131072.C065476
import PlattCertificates.Count131072.C065477
import PlattCertificates.Count131072.C065478
import PlattCertificates.Count131072.C065479
import PlattCertificates.Count131072.C065480
import PlattCertificates.Count131072.C065481
import PlattCertificates.Count131072.C065482
import PlattCertificates.Count131072.C065483
import PlattCertificates.Count131072.C065484
import PlattCertificates.Count131072.C065485
import PlattCertificates.Count131072.C065486
import PlattCertificates.Count131072.C065487
import PlattCertificates.Count131072.C065488
import PlattCertificates.Count131072.C065489
import PlattCertificates.Count131072.C065490
import PlattCertificates.Count131072.C065491
import PlattCertificates.Count131072.C065492
import PlattCertificates.Count131072.C065493
import PlattCertificates.Count131072.C065494
import PlattCertificates.Count131072.C065495
import PlattCertificates.Count131072.C065496
import PlattCertificates.Count131072.C065497
import PlattCertificates.Count131072.C065498
import PlattCertificates.Count131072.C065499
import PlattCertificates.Count131072.C065500
import PlattCertificates.Count131072.C065501
import PlattCertificates.Count131072.C065502
import PlattCertificates.Count131072.C065503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000171
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65472 : List PrefixCut := [⟨64,188020535,188020647⟩]
theorem checked65472 : checkPrefixCuts (2^48) 8585478145 10 Manual.Count131072.C065472.packed 64 cuts65472 = true := by
 decide +kernel
def cuts65473 : List PrefixCut := [⟨55,161200325,161200420⟩,
⟨64,188640561,188640671⟩]
theorem checked65473 : checkPrefixCuts (2^48) 8585609217 10 Manual.Count131072.C065473.packed 64 cuts65473 = true := by
 decide +kernel
def pointBounds65473 : List (Nat × Nat × Nat) := [(8585721856,114992772371614,114993161397523)]
theorem point_links_checked65473 : (cuts65473.take 1).map (fun c => (8585609217-1+2*2^10*c.k,114992611171289+c.lower,114993000197103+c.upper)) = pointBounds65473 := by
 decide +kernel
def cuts65474 : List PrefixCut := [⟨64,188572132,188572237⟩]
theorem checked65474 : checkPrefixCuts (2^48) 8585740289 10 Manual.Count131072.C065474.packed 64 cuts65474 = true := by
 decide +kernel
def cuts65475 : List PrefixCut := [⟨59,173620176,173620279⟩,
⟨64,188143053,188143164⟩]
theorem checked65475 : checkPrefixCuts (2^48) 8585871361 10 Manual.Count131072.C065475.packed 64 cuts65475 = true := by
 decide +kernel
def pointBounds65475 : List (Nat × Nat × Nat) := [(8585992192,114993162004158,114993551030290)]
theorem point_links_checked65475 : (cuts65475.take 1).map (fun c => (8585871361-1+2*2^10*c.k,114992988383982+c.lower,114993377410011+c.upper)) = pointBounds65475 := by
 decide +kernel
def cuts65476 : List PrefixCut := [⟨64,188631932,188632043⟩]
theorem checked65476 : checkPrefixCuts (2^48) 8586002433 10 Manual.Count131072.C065476.packed 64 cuts65476 = true := by
 decide +kernel
def cuts65477 : List PrefixCut := [⟨63,184924681,184924787⟩,
⟨64,187875061,187875169⟩]
theorem checked65477 : checkPrefixCuts (2^48) 8586133505 10 Manual.Count131072.C065477.packed 64 cuts65477 = true := by
 decide +kernel
def pointBounds65477 : List (Nat × Nat × Nat) := [(8586262528,114993550083648,114993939110005)]
theorem point_links_checked65477 : (cuts65477.take 1).map (fun c => (8586133505-1+2*2^10*c.k,114993365158967+c.lower,114993754185218+c.upper)) = pointBounds65477 := by
 decide +kernel
def cuts65478 : List PrefixCut := [⟨64,191314262,191314376⟩]
theorem checked65478 : checkPrefixCuts (2^48) 8586264577 10 Manual.Count131072.C065478.packed 64 cuts65478 = true := by
 decide +kernel
def cuts65479 : List PrefixCut := [⟨64,185836873,185836982⟩]
theorem checked65479 : checkPrefixCuts (2^48) 8586395649 10 Manual.Count131072.C065479.packed 64 cuts65479 = true := by
 decide +kernel
def cuts65480 : List PrefixCut := [⟨3,9244238,9244242⟩,
⟨64,189243235,189243346⟩]
theorem checked65480 : checkPrefixCuts (2^48) 8586526721 10 Manual.Count131072.C065480.packed 64 cuts65480 = true := by
 decide +kernel
def pointBounds65480 : List (Nat × Nat × Nat) := [(8586532864,114993939429401,114994328455987)]
theorem point_links_checked65480 : (cuts65480.take 1).map (fun c => (8586526721-1+2*2^10*c.k,114993930185163+c.lower,114994319211745+c.upper)) = pointBounds65480 := by
 decide +kernel
def cuts65481 : List PrefixCut := [⟨64,187207981,187208086⟩]
theorem checked65481 : checkPrefixCuts (2^48) 8586657793 10 Manual.Count131072.C065481.packed 64 cuts65481 = true := by
 decide +kernel
def cuts65482 : List PrefixCut := [⟨7,20323580,20323591⟩,
⟨64,187991827,187991934⟩]
theorem checked65482 : checkPrefixCuts (2^48) 8586788865 10 Manual.Count131072.C065482.packed 64 cuts65482 = true := by
 decide +kernel
def pointBounds65482 : List (Nat × Nat × Nat) := [(8586803200,114994326959959,114994715986768)]
theorem point_links_checked65482 : (cuts65482.take 1).map (fun c => (8586788865-1+2*2^10*c.k,114994306636379+c.lower,114994695663177+c.upper)) = pointBounds65482 := by
 decide +kernel
def cuts65483 : List PrefixCut := [⟨64,187792297,187792406⟩]
theorem checked65483 : checkPrefixCuts (2^48) 8586919937 10 Manual.Count131072.C065483.packed 64 cuts65483 = true := by
 decide +kernel
def cuts65484 : List PrefixCut := [⟨11,32352826,32352843⟩,
⟨64,189526694,189526797⟩]
theorem checked65484 : checkPrefixCuts (2^48) 8587051009 10 Manual.Count131072.C065484.packed 64 cuts65484 = true := by
 decide +kernel
def pointBounds65484 : List (Nat × Nat × Nat) := [(8587073536,114994714773329,114995103800360)]
theorem point_links_checked65484 : (cuts65484.take 1).map (fun c => (8587051009-1+2*2^10*c.k,114994682420503+c.lower,114995071447517+c.upper)) = pointBounds65484 := by
 decide +kernel
def cuts65485 : List PrefixCut := [⟨64,187425993,187426099⟩]
theorem checked65485 : checkPrefixCuts (2^48) 8587182081 10 Manual.Count131072.C065485.packed 64 cuts65485 = true := by
 decide +kernel
def cuts65486 : List PrefixCut := [⟨15,44905770,44905796⟩,
⟨64,188701469,188701576⟩]
theorem checked65486 : checkPrefixCuts (2^48) 8587313153 10 Manual.Count131072.C065486.packed 64 cuts65486 = true := by
 decide +kernel
def pointBounds65486 : List (Nat × Nat × Nat) := [(8587343872,114995104278960,114995493306209)]
theorem point_links_checked65486 : (cuts65486.take 1).map (fun c => (8587313153-1+2*2^10*c.k,114995059373190+c.lower,114995448400413+c.upper)) = pointBounds65486 := by
 decide +kernel
def cuts65487 : List PrefixCut := [⟨64,187289177,187289285⟩]
theorem checked65487 : checkPrefixCuts (2^48) 8587444225 10 Manual.Count131072.C065487.packed 64 cuts65487 = true := by
 decide +kernel
def cuts65488 : List PrefixCut := [⟨19,56605738,56605772⟩,
⟨64,187450197,187450305⟩]
theorem checked65488 : checkPrefixCuts (2^48) 8587575297 10 Manual.Count131072.C065488.packed 64 cuts65488 = true := by
 decide +kernel
def pointBounds65488 : List (Nat × Nat × Nat) := [(8587614208,114995491969574,114995880997046)]
theorem point_links_checked65488 : (cuts65488.take 1).map (fun c => (8587575297-1+2*2^10*c.k,114995435363836+c.lower,114995824391274+c.upper)) = pointBounds65488 := by
 decide +kernel
def cuts65489 : List PrefixCut := [⟨64,187185120,187185225⟩]
theorem checked65489 : checkPrefixCuts (2^48) 8587706369 10 Manual.Count131072.C065489.packed 64 cuts65489 = true := by
 decide +kernel
def cuts65490 : List PrefixCut := [⟨23,67944445,67944485⟩,
⟨64,188788278,188788384⟩]
theorem checked65490 : checkPrefixCuts (2^48) 8587837441 10 Manual.Count131072.C065490.packed 64 cuts65490 = true := by
 decide +kernel
def pointBounds65490 : List (Nat × Nat × Nat) := [(8587884544,114995877943598,114996266971289)]
theorem point_links_checked65490 : (cuts65490.take 1).map (fun c => (8587837441-1+2*2^10*c.k,114995809999153+c.lower,114996199026804+c.upper)) = pointBounds65490 := by
 decide +kernel
def cuts65491 : List PrefixCut := [⟨64,189866990,189867101⟩]
theorem checked65491 : checkPrefixCuts (2^48) 8587968513 10 Manual.Count131072.C065491.packed 64 cuts65491 = true := by
 decide +kernel
def cuts65492 : List PrefixCut := [⟨27,78987481,78987523⟩,
⟨64,187471525,187471631⟩]
theorem checked65492 : checkPrefixCuts (2^48) 8588099585 10 Manual.Count131072.C065492.packed 64 cuts65492 = true := by
 decide +kernel
def pointBounds65492 : List (Nat × Nat × Nat) := [(8588154880,114996267641902,114996656669812)]
theorem point_links_checked65492 : (cuts65492.take 1).map (fun c => (8588099585-1+2*2^10*c.k,114996188654421+c.lower,114996577682289+c.upper)) = pointBounds65492 := by
 decide +kernel
def cuts65493 : List PrefixCut := [⟨64,191368797,191368905⟩]
theorem checked65493 : checkPrefixCuts (2^48) 8588230657 10 Manual.Count131072.C065493.packed 64 cuts65493 = true := by
 decide +kernel
def cuts65494 : List PrefixCut := [⟨31,91144137,91144187⟩,
⟨64,187006979,187007086⟩]
theorem checked65494 : checkPrefixCuts (2^48) 8588361729 10 Manual.Count131072.C065494.packed 64 cuts65494 = true := by
 decide +kernel
def pointBounds65494 : List (Nat × Nat × Nat) := [(8588425216,114996658638880,114997047667012)]
theorem point_links_checked65494 : (cuts65494.take 1).map (fun c => (8588361729-1+2*2^10*c.k,114996567494743+c.lower,114996956522825+c.upper)) = pointBounds65494 := by
 decide +kernel
def cuts65495 : List PrefixCut := [⟨64,186414195,186414300⟩]
theorem checked65495 : checkPrefixCuts (2^48) 8588492801 10 Manual.Count131072.C065495.packed 64 cuts65495 = true := by
 decide +kernel
def cuts65496 : List PrefixCut := [⟨35,104578177,104578238⟩,
⟨64,187820594,187820703⟩]
theorem checked65496 : checkPrefixCuts (2^48) 8588623873 10 Manual.Count131072.C065496.packed 64 cuts65496 = true := by
 decide +kernel
def pointBounds65496 : List (Nat × Nat × Nat) := [(8588695552,114997045494094,114997434522449)]
theorem point_links_checked65496 : (cuts65496.take 1).map (fun c => (8588623873-1+2*2^10*c.k,114996940915917+c.lower,114997329944211+c.upper)) = pointBounds65496 := by
 decide +kernel
def cuts65497 : List PrefixCut := [⟨64,187686626,187686736⟩]
theorem checked65497 : checkPrefixCuts (2^48) 8588754945 10 Manual.Count131072.C065497.packed 64 cuts65497 = true := by
 decide +kernel
def cuts65498 : List PrefixCut := [⟨39,115455189,115455258⟩,
⟨64,188175345,188175457⟩]
theorem checked65498 : checkPrefixCuts (2^48) 8588886017 10 Manual.Count131072.C065498.packed 64 cuts65498 = true := by
 decide +kernel
def pointBounds65498 : List (Nat × Nat × Nat) := [(8588965888,114997431878326,114997820906908)]
theorem point_links_checked65498 : (cuts65498.take 1).map (fun c => (8588886017-1+2*2^10*c.k,114997316423137+c.lower,114997705451650+c.upper)) = pointBounds65498 := by
 decide +kernel
def cuts65499 : List PrefixCut := [⟨64,188664040,188664149⟩]
theorem checked65499 : checkPrefixCuts (2^48) 8589017089 10 Manual.Count131072.C065499.packed 64 cuts65499 = true := by
 decide +kernel
def cuts65500 : List PrefixCut := [⟨43,124037565,124037638⟩,
⟨64,188824986,188825100⟩]
theorem checked65500 : checkPrefixCuts (2^48) 8589148161 10 Manual.Count131072.C065500.packed 64 cuts65500 = true := by
 decide +kernel
def pointBounds65500 : List (Nat × Nat × Nat) := [(8589236224,114997817300087,114998206328894)]
theorem point_links_checked65500 : (cuts65500.take 1).map (fun c => (8589148161-1+2*2^10*c.k,114997693262522+c.lower,114998082291256+c.upper)) = pointBounds65500 := by
 decide +kernel
def cuts65501 : List PrefixCut := [⟨64,189084301,189084404⟩]
theorem checked65501 : checkPrefixCuts (2^48) 8589279233 10 Manual.Count131072.C065501.packed 64 cuts65501 = true := by
 decide +kernel
def cuts65502 : List PrefixCut := [⟨47,138747371,138747452⟩,
⟨64,188098323,188098433⟩]
theorem checked65502 : checkPrefixCuts (2^48) 8589410305 10 Manual.Count131072.C065502.packed 64 cuts65502 = true := by
 decide +kernel
def pointBounds65502 : List (Nat × Nat × Nat) := [(8589506560,114998209919180,114998598948212)]
theorem point_links_checked65502 : (cuts65502.take 1).map (fun c => (8589410305-1+2*2^10*c.k,114998071171809+c.lower,114998460200760+c.upper)) = pointBounds65502 := by
 decide +kernel
def cuts65503 : List PrefixCut := [⟨64,189570062,189570165⟩]
theorem checked65503 : checkPrefixCuts (2^48) 8589541377 10 Manual.Count131072.C065503.packed 64 cuts65503 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000171
