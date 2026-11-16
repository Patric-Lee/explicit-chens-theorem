import PlattAssemblyKernel
import PlattCertificates.Count131072.C067552
import PlattCertificates.Count131072.C067553
import PlattCertificates.Count131072.C067554
import PlattCertificates.Count131072.C067555
import PlattCertificates.Count131072.C067556
import PlattCertificates.Count131072.C067557
import PlattCertificates.Count131072.C067558
import PlattCertificates.Count131072.C067559
import PlattCertificates.Count131072.C067560
import PlattCertificates.Count131072.C067561
import PlattCertificates.Count131072.C067562
import PlattCertificates.Count131072.C067563
import PlattCertificates.Count131072.C067564
import PlattCertificates.Count131072.C067565
import PlattCertificates.Count131072.C067566
import PlattCertificates.Count131072.C067567
import PlattCertificates.Count131072.C067568
import PlattCertificates.Count131072.C067569
import PlattCertificates.Count131072.C067570
import PlattCertificates.Count131072.C067571
import PlattCertificates.Count131072.C067572
import PlattCertificates.Count131072.C067573
import PlattCertificates.Count131072.C067574
import PlattCertificates.Count131072.C067575
import PlattCertificates.Count131072.C067576
import PlattCertificates.Count131072.C067577
import PlattCertificates.Count131072.C067578
import PlattCertificates.Count131072.C067579
import PlattCertificates.Count131072.C067580
import PlattCertificates.Count131072.C067581
import PlattCertificates.Count131072.C067582
import PlattCertificates.Count131072.C067583
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000236
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67552 : List PrefixCut := [⟨53,149218986,149219074⟩,
⟨64,181344048,181344157⟩]
theorem checked67552 : checkPrefixCuts (2^48) 8858107905 10 Manual.Count131072.C067552.packed 64 cuts67552 = true := by
 decide +kernel
def pointBounds67552 : List (Nat × Nat × Nat) := [(8858216448,115376991847700,115377381096842)]
theorem point_links_checked67552 : (cuts67552.take 1).map (fun c => (8858107905-1+2*2^10*c.k,115376842628714+c.lower,115377231877768+c.upper)) = pointBounds67552 := by
 decide +kernel
def cuts67553 : List PrefixCut := [⟨64,180261018,180261124⟩]
theorem checked67553 : checkPrefixCuts (2^48) 8858238977 10 Manual.Count131072.C067553.packed 64 cuts67553 = true := by
 decide +kernel
def cuts67554 : List PrefixCut := [⟨61,172473596,172473694⟩,
⟨64,181402248,181402352⟩]
theorem checked67554 : checkPrefixCuts (2^48) 8858370049 10 Manual.Count131072.C067554.packed 64 cuts67554 = true := by
 decide +kernel
def pointBounds67554 : List (Nat × Nat × Nat) := [(8858494976,115377376707376,115377765956743)]
theorem point_links_checked67554 : (cuts67554.take 1).map (fun c => (8858370049-1+2*2^10*c.k,115377204233780+c.lower,115377593483049+c.upper)) = pointBounds67554 := by
 decide +kernel
def cuts67555 : List PrefixCut := [⟨64,181208925,181209036⟩]
theorem checked67555 : checkPrefixCuts (2^48) 8858501121 10 Manual.Count131072.C067555.packed 64 cuts67555 = true := by
 decide +kernel
def cuts67556 : List PrefixCut := [⟨64,181015603,181015713⟩]
theorem checked67556 : checkPrefixCuts (2^48) 8858632193 10 Manual.Count131072.C067556.packed 64 cuts67556 = true := by
 decide +kernel
def cuts67557 : List PrefixCut := [⟨5,13916833,13916842⟩,
⟨64,183268831,183268937⟩]
theorem checked67557 : checkPrefixCuts (2^48) 8858763265 10 Manual.Count131072.C067557.packed 64 cuts67557 = true := by
 decide +kernel
def pointBounds67557 : List (Nat × Nat × Nat) := [(8858773504,115377761777389,115378151026992)]
theorem point_links_checked67557 : (cuts67557.take 1).map (fun c => (8858763265-1+2*2^10*c.k,115377747860556+c.lower,115378137110150+c.upper)) = pointBounds67557 := by
 decide +kernel
def cuts67558 : List PrefixCut := [⟨64,182185845,182185950⟩]
theorem checked67558 : checkPrefixCuts (2^48) 8858894337 10 Manual.Count131072.C067558.packed 64 cuts67558 = true := by
 decide +kernel
def cuts67559 : List PrefixCut := [⟨13,36697377,36697400⟩,
⟨64,183104537,183104645⟩]
theorem checked67559 : checkPrefixCuts (2^48) 8859025409 10 Manual.Count131072.C067559.packed 64 cuts67559 = true := by
 decide +kernel
def pointBounds67559 : List (Nat × Nat × Nat) := [(8859052032,115378150012609,115378539262437)]
theorem point_links_checked67559 : (cuts67559.take 1).map (fun c => (8859025409-1+2*2^10*c.k,115378113315232+c.lower,115378502565037+c.upper)) = pointBounds67559 := by
 decide +kernel
def cuts67560 : List PrefixCut := [⟨64,183228938,183229046⟩]
theorem checked67560 : checkPrefixCuts (2^48) 8859156481 10 Manual.Count131072.C067560.packed 64 cuts67560 = true := by
 decide +kernel
def cuts67561 : List PrefixCut := [⟨21,59698934,59698969⟩,
⟨64,185259582,185259687⟩]
theorem checked67561 : checkPrefixCuts (2^48) 8859287553 10 Manual.Count131072.C067561.packed 64 cuts67561 = true := by
 decide +kernel
def pointBounds67561 : List (Nat × Nat × Nat) := [(8859330560,115378539347641,115378928597697)]
theorem point_links_checked67561 : (cuts67561.take 1).map (fun c => (8859287553-1+2*2^10*c.k,115378479648707+c.lower,115378868898728+c.upper)) = pointBounds67561 := by
 decide +kernel
def cuts67562 : List PrefixCut := [⟨64,180808909,180809018⟩]
theorem checked67562 : checkPrefixCuts (2^48) 8859418625 10 Manual.Count131072.C067562.packed 64 cuts67562 = true := by
 decide +kernel
def cuts67563 : List PrefixCut := [⟨29,83906376,83906423⟩,
⟨64,184396301,184396408⟩]
theorem checked67563 : checkPrefixCuts (2^48) 8859549697 10 Manual.Count131072.C067563.packed 64 cuts67563 = true := by
 decide +kernel
def pointBounds67563 : List (Nat × Nat × Nat) := [(8859609088,115378929623574,115379318873856)]
theorem point_links_checked67563 : (cuts67563.take 1).map (fun c => (8859549697-1+2*2^10*c.k,115378845717198+c.lower,115379234967433+c.upper)) = pointBounds67563 := by
 decide +kernel
def cuts67564 : List PrefixCut := [⟨64,180326994,180327101⟩]
theorem checked67564 : checkPrefixCuts (2^48) 8859680769 10 Manual.Count131072.C067564.packed 64 cuts67564 = true := by
 decide +kernel
def cuts67565 : List PrefixCut := [⟨37,104077585,104077644⟩,
⟨64,180991497,180991600⟩]
theorem checked67565 : checkPrefixCuts (2^48) 8859811841 10 Manual.Count131072.C067565.packed 64 cuts67565 = true := by
 decide +kernel
def pointBounds67565 : List (Nat × Nat × Nat) := [(8859887616,115379314518078,115379703768586)]
theorem point_links_checked67565 : (cuts67565.take 1).map (fun c => (8859811841-1+2*2^10*c.k,115379210440493+c.lower,115379599690942+c.upper)) = pointBounds67565 := by
 decide +kernel
def cuts67566 : List PrefixCut := [⟨64,181528886,181528988⟩]
theorem checked67566 : checkPrefixCuts (2^48) 8859942913 10 Manual.Count131072.C067566.packed 64 cuts67566 = true := by
 decide +kernel
def cuts67567 : List PrefixCut := [⟨45,127202058,127202133⟩,
⟨64,180827302,180827410⟩]
theorem checked67567 : checkPrefixCuts (2^48) 8860073985 10 Manual.Count131072.C067567.packed 64 cuts67567 = true := by
 decide +kernel
def pointBounds67567 : List (Nat × Nat × Nat) := [(8860166144,115379700162934,115380089413663)]
theorem point_links_checked67567 : (cuts67567.take 1).map (fun c => (8860073985-1+2*2^10*c.k,115379572960876+c.lower,115379962211530+c.upper)) = pointBounds67567 := by
 decide +kernel
def cuts67568 : List PrefixCut := [⟨64,179204458,179204559⟩]
theorem checked67568 : checkPrefixCuts (2^48) 8860205057 10 Manual.Count131072.C067568.packed 64 cuts67568 = true := by
 decide +kernel
def cuts67569 : List PrefixCut := [⟨53,150039204,150039293⟩,
⟨64,180758415,180758523⟩]
theorem checked67569 : checkPrefixCuts (2^48) 8860336129 10 Manual.Count131072.C067569.packed 64 cuts67569 = true := by
 decide +kernel
def pointBounds67569 : List (Nat × Nat × Nat) := [(8860444672,115380083031840,115380472282792)]
theorem point_links_checked67569 : (cuts67569.take 1).map (fun c => (8860336129-1+2*2^10*c.k,115379932992636+c.lower,115380322243499+c.upper)) = pointBounds67569 := by
 decide +kernel
def cuts67570 : List PrefixCut := [⟨64,181327543,181327646⟩]
theorem checked67570 : checkPrefixCuts (2^48) 8860467201 10 Manual.Count131072.C067570.packed 64 cuts67570 = true := by
 decide +kernel
def cuts67571 : List PrefixCut := [⟨61,172716136,172716239⟩,
⟨64,181102510,181102619⟩]
theorem checked67571 : checkPrefixCuts (2^48) 8860598273 10 Manual.Count131072.C067571.packed 64 cuts67571 = true := by
 decide +kernel
def pointBounds67571 : List (Nat × Nat × Nat) := [(8860723200,115380467794730,115380857045907)]
theorem point_links_checked67571 : (cuts67571.take 1).map (fun c => (8860598273-1+2*2^10*c.k,115380295078594+c.lower,115380684329668+c.upper)) = pointBounds67571 := by
 decide +kernel
def cuts67572 : List PrefixCut := [⟨64,182338702,182338808⟩]
theorem checked67572 : checkPrefixCuts (2^48) 8860729345 10 Manual.Count131072.C067572.packed 64 cuts67572 = true := by
 decide +kernel
def cuts67573 : List PrefixCut := [⟨64,178555867,178555973⟩]
theorem checked67573 : checkPrefixCuts (2^48) 8860860417 10 Manual.Count131072.C067573.packed 64 cuts67573 = true := by
 decide +kernel
def cuts67574 : List PrefixCut := [⟨5,15088660,15088670⟩,
⟨64,183540395,183540503⟩]
theorem checked67574 : checkPrefixCuts (2^48) 8860991489 10 Manual.Count131072.C067574.packed 64 cuts67574 = true := by
 decide +kernel
def pointBounds67574 : List (Nat × Nat × Nat) := [(8861001728,115380852164333,115381241415738)]
theorem point_links_checked67574 : (cuts67574.take 1).map (fun c => (8860991489-1+2*2^10*c.k,115380837075673+c.lower,115381226327068+c.upper)) = pointBounds67574 := by
 decide +kernel
def cuts67575 : List PrefixCut := [⟨64,182457685,182457790⟩]
theorem checked67575 : checkPrefixCuts (2^48) 8861122561 10 Manual.Count131072.C067575.packed 64 cuts67575 = true := by
 decide +kernel
def cuts67576 : List PrefixCut := [⟨13,36116388,36116409⟩,
⟨64,182264384,182264488⟩]
theorem checked67576 : checkPrefixCuts (2^48) 8861253633 10 Manual.Count131072.C067576.packed 64 cuts67576 = true := by
 decide +kernel
def pointBounds67576 : List (Nat × Nat × Nat) := [(8861280256,115381239190141,115381628441770)]
theorem point_links_checked67576 : (cuts67576.take 1).map (fun c => (8861253633-1+2*2^10*c.k,115381203073753+c.lower,115381592325361+c.upper)) = pointBounds67576 := by
 decide +kernel
def cuts67577 : List PrefixCut := [⟨64,181975825,181975929⟩]
theorem checked67577 : checkPrefixCuts (2^48) 8861384705 10 Manual.Count131072.C067577.packed 64 cuts67577 = true := by
 decide +kernel
def cuts67578 : List PrefixCut := [⟨21,60096849,60096885⟩,
⟨64,181496674,181496783⟩]
theorem checked67578 : checkPrefixCuts (2^48) 8861515777 10 Manual.Count131072.C067578.packed 64 cuts67578 = true := by
 decide +kernel
def pointBounds67578 : List (Nat × Nat × Nat) := [(8861558784,115381627410811,115382016662663)]
theorem point_links_checked67578 : (cuts67578.take 1).map (fun c => (8861515777-1+2*2^10*c.k,115381567313962+c.lower,115381956565778+c.upper)) = pointBounds67578 := by
 decide +kernel
def cuts67579 : List PrefixCut := [⟨64,179747035,179747141⟩]
theorem checked67579 : checkPrefixCuts (2^48) 8861646849 10 Manual.Count131072.C067579.packed 64 cuts67579 = true := by
 decide +kernel
def cuts67580 : List PrefixCut := [⟨29,83408834,83408886⟩,
⟨64,182634754,182634866⟩]
theorem checked67580 : checkPrefixCuts (2^48) 8861777921 10 Manual.Count131072.C067580.packed 64 cuts67580 = true := by
 decide +kernel
def pointBounds67580 : List (Nat × Nat × Nat) := [(8861837312,115382011966505,115382401218588)]
theorem point_links_checked67580 : (cuts67580.take 1).map (fun c => (8861777921-1+2*2^10*c.k,115381928557671+c.lower,115382317809702+c.upper)) = pointBounds67580 := by
 decide +kernel
def cuts67581 : List PrefixCut := [⟨64,178757089,178757191⟩]
theorem checked67581 : checkPrefixCuts (2^48) 8861908993 10 Manual.Count131072.C067581.packed 64 cuts67581 = true := by
 decide +kernel
def cuts67582 : List PrefixCut := [⟨37,106242968,106243028⟩,
⟨64,181835316,181835421⟩]
theorem checked67582 : checkPrefixCuts (2^48) 8862040065 10 Manual.Count131072.C067582.packed 64 cuts67582 = true := by
 decide +kernel
def pointBounds67582 : List (Nat × Nat × Nat) := [(8862115840,115382396192482,115382785444787)]
theorem point_links_checked67582 : (cuts67582.take 1).map (fun c => (8862040065-1+2*2^10*c.k,115382289949514+c.lower,115382679201759+c.upper)) = pointBounds67582 := by
 decide +kernel
def cuts67583 : List PrefixCut := [⟨64,181451495,181451603⟩]
theorem checked67583 : checkPrefixCuts (2^48) 8862171137 10 Manual.Count131072.C067583.packed 64 cuts67583 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000236
