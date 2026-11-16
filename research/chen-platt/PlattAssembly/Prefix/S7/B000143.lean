import PlattAssemblyKernel
import PlattCertificates.Count131072.C064576
import PlattCertificates.Count131072.C064577
import PlattCertificates.Count131072.C064578
import PlattCertificates.Count131072.C064579
import PlattCertificates.Count131072.C064580
import PlattCertificates.Count131072.C064581
import PlattCertificates.Count131072.C064582
import PlattCertificates.Count131072.C064583
import PlattCertificates.Count131072.C064584
import PlattCertificates.Count131072.C064585
import PlattCertificates.Count131072.C064586
import PlattCertificates.Count131072.C064587
import PlattCertificates.Count131072.C064588
import PlattCertificates.Count131072.C064589
import PlattCertificates.Count131072.C064590
import PlattCertificates.Count131072.C064591
import PlattCertificates.Count131072.C064592
import PlattCertificates.Count131072.C064593
import PlattCertificates.Count131072.C064594
import PlattCertificates.Count131072.C064595
import PlattCertificates.Count131072.C064596
import PlattCertificates.Count131072.C064597
import PlattCertificates.Count131072.C064598
import PlattCertificates.Count131072.C064599
import PlattCertificates.Count131072.C064600
import PlattCertificates.Count131072.C064601
import PlattCertificates.Count131072.C064602
import PlattCertificates.Count131072.C064603
import PlattCertificates.Count131072.C064604
import PlattCertificates.Count131072.C064605
import PlattCertificates.Count131072.C064606
import PlattCertificates.Count131072.C064607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000143
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64576 : List PrefixCut := [⟨16,47133781,47133809⟩,
⟨64,189198817,189198925⟩]
theorem checked64576 : checkPrefixCuts (2^48) 8468037633 10 Manual.Count131072.C064576.packed 64 cuts64576 = true := by
 decide +kernel
def pointBounds64576 : List (Nat × Nat × Nat) := [(8468070400,114822924879266,114823313806745)]
theorem point_links_checked64576 : (cuts64576.take 1).map (fun c => (8468037633-1+2*2^10*c.k,114822877745485+c.lower,114823266672936+c.upper)) = pointBounds64576 := by
 decide +kernel
def cuts64577 : List PrefixCut := [⟨64,190824592,190824700⟩]
theorem checked64577 : checkPrefixCuts (2^48) 8468168705 10 Manual.Count131072.C064577.packed 64 cuts64577 = true := by
 decide +kernel
def cuts64578 : List PrefixCut := [⟨18,53314688,53314718⟩,
⟨64,188362003,188362111⟩]
theorem checked64578 : checkPrefixCuts (2^48) 8468299777 10 Manual.Count131072.C064578.packed 64 cuts64578 = true := by
 decide +kernel
def pointBounds64578 : List (Nat × Nat × Nat) := [(8468336640,114823311083582,114823700011279)]
theorem point_links_checked64578 : (cuts64578.take 1).map (fun c => (8468299777-1+2*2^10*c.k,114823257768894+c.lower,114823646696561+c.upper)) = pointBounds64578 := by
 decide +kernel
def cuts64579 : List PrefixCut := [⟨64,190984887,190984998⟩]
theorem checked64579 : checkPrefixCuts (2^48) 8468430849 10 Manual.Count131072.C064579.packed 64 cuts64579 = true := by
 decide +kernel
def cuts64580 : List PrefixCut := [⟨20,60126719,60126756⟩,
⟨64,192045519,192045629⟩]
theorem checked64580 : checkPrefixCuts (2^48) 8468561921 10 Manual.Count131072.C064580.packed 64 cuts64580 = true := by
 decide +kernel
def pointBounds64580 : List (Nat × Nat × Nat) := [(8468602880,114823697242503,114824086170426)]
theorem point_links_checked64580 : (cuts64580.take 1).map (fun c => (8468561921-1+2*2^10*c.k,114823637115784+c.lower,114824026043670+c.upper)) = pointBounds64580 := by
 decide +kernel
def cuts64581 : List PrefixCut := [⟨64,191211630,191211743⟩]
theorem checked64581 : checkPrefixCuts (2^48) 8468692993 10 Manual.Count131072.C064581.packed 64 cuts64581 = true := by
 decide +kernel
def cuts64582 : List PrefixCut := [⟨22,65475926,65475965⟩,
⟨64,190676887,190677001⟩]
theorem checked64582 : checkPrefixCuts (2^48) 8468824065 10 Manual.Count131072.C064582.packed 64 cuts64582 = true := by
 decide +kernel
def pointBounds64582 : List (Nat × Nat × Nat) := [(8468869120,114824085848859,114824474777007)]
theorem point_links_checked64582 : (cuts64582.take 1).map (fun c => (8468824065-1+2*2^10*c.k,114824020372933+c.lower,114824409301042+c.upper)) = pointBounds64582 := by
 decide +kernel
def cuts64583 : List PrefixCut := [⟨64,191006291,191006402⟩]
theorem checked64583 : checkPrefixCuts (2^48) 8468955137 10 Manual.Count131072.C064583.packed 64 cuts64583 = true := by
 decide +kernel
def cuts64584 : List PrefixCut := [⟨24,71356558,71356600⟩,
⟨64,189009218,189009330⟩]
theorem checked64584 : checkPrefixCuts (2^48) 8469086209 10 Manual.Count131072.C064584.packed 64 cuts64584 = true := by
 decide +kernel
def pointBounds64584 : List (Nat × Nat × Nat) := [(8469135360,114824473412669,114824862341045)]
theorem point_links_checked64584 : (cuts64584.take 1).map (fun c => (8469086209-1+2*2^10*c.k,114824402056111+c.lower,114824790984445+c.upper)) = pointBounds64584 := by
 decide +kernel
def cuts64585 : List PrefixCut := [⟨64,190169520,190169635⟩]
theorem checked64585 : checkPrefixCuts (2^48) 8469217281 10 Manual.Count131072.C064585.packed 64 cuts64585 = true := by
 decide +kernel
def cuts64586 : List PrefixCut := [⟨26,76738310,76738356⟩,
⟨64,187441359,187441468⟩]
theorem checked64586 : checkPrefixCuts (2^48) 8469348353 10 Manual.Count131072.C064586.packed 64 cuts64586 = true := by
 decide +kernel
def pointBounds64586 : List (Nat × Nat × Nat) := [(8469401600,114824857973159,114825246901766)]
theorem point_links_checked64586 : (cuts64586.take 1).map (fun c => (8469348353-1+2*2^10*c.k,114824781234849+c.lower,114825170163410+c.upper)) = pointBounds64586 := by
 decide +kernel
def cuts64587 : List PrefixCut := [⟨64,190595656,190595765⟩]
theorem checked64587 : checkPrefixCuts (2^48) 8469479425 10 Manual.Count131072.C064587.packed 64 cuts64587 = true := by
 decide +kernel
def cuts64588 : List PrefixCut := [⟨28,83382597,83382645⟩,
⟨64,189030753,189030866⟩]
theorem checked64588 : checkPrefixCuts (2^48) 8469610497 10 Manual.Count131072.C064588.packed 64 cuts64588 = true := by
 decide +kernel
def pointBounds64588 : List (Nat × Nat × Nat) := [(8469667840,114825242654461,114825631583288)]
theorem point_links_checked64588 : (cuts64588.take 1).map (fun c => (8469610497-1+2*2^10*c.k,114825159271864+c.lower,114825548200643+c.upper)) = pointBounds64588 := by
 decide +kernel
def cuts64589 : List PrefixCut := [⟨64,190423601,190423711⟩]
theorem checked64589 : checkPrefixCuts (2^48) 8469741569 10 Manual.Count131072.C064589.packed 64 cuts64589 = true := by
 decide +kernel
def cuts64590 : List PrefixCut := [⟨30,89328591,89328638⟩,
⟨64,191351154,191351258⟩]
theorem checked64590 : checkPrefixCuts (2^48) 8469872641 10 Manual.Count131072.C064590.packed 64 cuts64590 = true := by
 decide +kernel
def pointBounds64590 : List (Nat × Nat × Nat) := [(8469934080,114825628054809,114826016983858)]
theorem point_links_checked64590 : (cuts64590.take 1).map (fun c => (8469872641-1+2*2^10*c.k,114825538726218+c.lower,114825927655220+c.upper)) = pointBounds64590 := by
 decide +kernel
def cuts64591 : List PrefixCut := [⟨64,190816508,190816613⟩]
theorem checked64591 : checkPrefixCuts (2^48) 8470003713 10 Manual.Count131072.C064591.packed 64 cuts64591 = true := by
 decide +kernel
def cuts64592 : List PrefixCut := [⟨32,95606526,95606581⟩,
⟨64,189916299,189916410⟩]
theorem checked64592 : checkPrefixCuts (2^48) 8470134785 10 Manual.Count131072.C064592.packed 64 cuts64592 = true := by
 decide +kernel
def pointBounds64592 : List (Nat × Nat × Nat) := [(8470200320,114826016500406,114826405429672)]
theorem point_links_checked64592 : (cuts64592.take 1).map (fun c => (8470134785-1+2*2^10*c.k,114825920893880+c.lower,114826309823091+c.upper)) = pointBounds64592 := by
 decide +kernel
def cuts64593 : List PrefixCut := [⟨64,190445047,190445160⟩]
theorem checked64593 : checkPrefixCuts (2^48) 8470265857 10 Manual.Count131072.C064593.packed 64 cuts64593 = true := by
 decide +kernel
def cuts64594 : List PrefixCut := [⟨34,102382519,102382579⟩,
⟨64,190508563,190508675⟩]
theorem checked64594 : checkPrefixCuts (2^48) 8470396929 10 Manual.Count131072.C064594.packed 64 cuts64594 = true := by
 decide +kernel
def pointBounds64594 : List (Nat × Nat × Nat) := [(8470466560,114826403637745,114826792567240)]
theorem point_links_checked64594 : (cuts64594.take 1).map (fun c => (8470396929-1+2*2^10*c.k,114826301255226+c.lower,114826690184661+c.upper)) = pointBounds64594 := by
 decide +kernel
def cuts64595 : List PrefixCut := [⟨64,193130745,193130851⟩]
theorem checked64595 : checkPrefixCuts (2^48) 8470528001 10 Manual.Count131072.C064595.packed 64 cuts64595 = true := by
 decide +kernel
def cuts64596 : List PrefixCut := [⟨36,106964959,106965022⟩,
⟨64,190635570,190635681⟩]
theorem checked64596 : checkPrefixCuts (2^48) 8470659073 10 Manual.Count131072.C064596.packed 64 cuts64596 = true := by
 decide +kernel
def pointBounds64596 : List (Nat × Nat × Nat) := [(8470732800,114826791859493,114827180789209)]
theorem point_links_checked64596 : (cuts64596.take 1).map (fun c => (8470659073-1+2*2^10*c.k,114826684894534+c.lower,114827073824187+c.upper)) = pointBounds64596 := by
 decide +kernel
def cuts64597 : List PrefixCut := [⟨64,188871508,188871625⟩]
theorem checked64597 : checkPrefixCuts (2^48) 8470790145 10 Manual.Count131072.C064597.packed 64 cuts64597 = true := by
 decide +kernel
def cuts64598 : List PrefixCut := [⟨38,115501285,115501350⟩,
⟨64,191526853,191526964⟩]
theorem checked64598 : checkPrefixCuts (2^48) 8470921217 10 Manual.Count131072.C064598.packed 64 cuts64598 = true := by
 decide +kernel
def pointBounds64598 : List (Nat × Nat × Nat) := [(8470999040,114827179902897,114827568832843)]
theorem point_links_checked64598 : (cuts64598.take 1).map (fun c => (8470921217-1+2*2^10*c.k,114827064401612+c.lower,114827453331493+c.upper)) = pointBounds64598 := by
 decide +kernel
def cuts64599 : List PrefixCut := [⟨64,190659948,190660058⟩]
theorem checked64599 : checkPrefixCuts (2^48) 8471052289 10 Manual.Count131072.C064599.packed 64 cuts64599 = true := by
 decide +kernel
def cuts64600 : List PrefixCut := [⟨40,116461265,116461337⟩,
⟨64,187899151,187899262⟩]
theorem checked64600 : checkPrefixCuts (2^48) 8471183361 10 Manual.Count131072.C064600.packed 64 cuts64600 = true := by
 decide +kernel
def pointBounds64600 : List (Nat × Nat × Nat) := [(8471265280,114827563049678,114827951979852)]
theorem point_links_checked64600 : (cuts64600.take 1).map (fun c => (8471183361-1+2*2^10*c.k,114827446588413+c.lower,114827835518515+c.upper)) = pointBounds64600 := by
 decide +kernel
def cuts64601 : List PrefixCut := [⟨64,192049565,192049676⟩]
theorem checked64601 : checkPrefixCuts (2^48) 8471314433 10 Manual.Count131072.C064601.packed 64 cuts64601 = true := by
 decide +kernel
def cuts64602 : List PrefixCut := [⟨42,123734156,123734227⟩,
⟨64,189288831,189288937⟩]
theorem checked64602 : checkPrefixCuts (2^48) 8471445505 10 Manual.Count131072.C064602.packed 64 cuts64602 = true := by
 decide +kernel
def pointBounds64602 : List (Nat × Nat × Nat) := [(8471531520,114827950271285,114828339201680)]
theorem point_links_checked64602 : (cuts64602.take 1).map (fun c => (8471445505-1+2*2^10*c.k,114827826537129+c.lower,114828215467453+c.upper)) = pointBounds64602 := by
 decide +kernel
def cuts64603 : List PrefixCut := [⟨64,189119783,189119884⟩]
theorem checked64603 : checkPrefixCuts (2^48) 8471576577 10 Manual.Count131072.C064603.packed 64 cuts64603 = true := by
 decide +kernel
def cuts64604 : List PrefixCut := [⟨44,129179208,129179287⟩,
⟨64,189449086,189449200⟩]
theorem checked64604 : checkPrefixCuts (2^48) 8471707649 10 Manual.Count131072.C064604.packed 64 cuts64604 = true := by
 decide +kernel
def pointBounds64604 : List (Nat × Nat × Nat) := [(8471797760,114828334124951,114828723055561)]
theorem point_links_checked64604 : (cuts64604.take 1).map (fun c => (8471707649-1+2*2^10*c.k,114828204945743+c.lower,114828593876274+c.upper)) = pointBounds64604 := by
 decide +kernel
def cuts64605 : List PrefixCut := [⟨64,188648783,188648890⟩]
theorem checked64605 : checkPrefixCuts (2^48) 8471838721 10 Manual.Count131072.C064605.packed 64 cuts64605 = true := by
 decide +kernel
def cuts64606 : List PrefixCut := [⟨46,138212131,138212211⟩,
⟨64,189974832,189974944⟩]
theorem checked64606 : checkPrefixCuts (2^48) 8471969793 10 Manual.Count131072.C064606.packed 64 cuts64606 = true := by
 decide +kernel
def pointBounds64606 : List (Nat × Nat × Nat) := [(8472064000,114828721255743,114829110186575)]
theorem point_links_checked64606 : (cuts64606.take 1).map (fun c => (8471969793-1+2*2^10*c.k,114828583043612+c.lower,114828971974364+c.upper)) = pointBounds64606 := by
 decide +kernel
def cuts64607 : List PrefixCut := [⟨64,191234372,191234490⟩]
theorem checked64607 : checkPrefixCuts (2^48) 8472100865 10 Manual.Count131072.C064607.packed 64 cuts64607 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000143
