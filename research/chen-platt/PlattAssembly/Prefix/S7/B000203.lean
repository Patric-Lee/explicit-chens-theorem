import PlattAssemblyKernel
import PlattCertificates.Count131072.C066496
import PlattCertificates.Count131072.C066497
import PlattCertificates.Count131072.C066498
import PlattCertificates.Count131072.C066499
import PlattCertificates.Count131072.C066500
import PlattCertificates.Count131072.C066501
import PlattCertificates.Count131072.C066502
import PlattCertificates.Count131072.C066503
import PlattCertificates.Count131072.C066504
import PlattCertificates.Count131072.C066505
import PlattCertificates.Count131072.C066506
import PlattCertificates.Count131072.C066507
import PlattCertificates.Count131072.C066508
import PlattCertificates.Count131072.C066509
import PlattCertificates.Count131072.C066510
import PlattCertificates.Count131072.C066511
import PlattCertificates.Count131072.C066512
import PlattCertificates.Count131072.C066513
import PlattCertificates.Count131072.C066514
import PlattCertificates.Count131072.C066515
import PlattCertificates.Count131072.C066516
import PlattCertificates.Count131072.C066517
import PlattCertificates.Count131072.C066518
import PlattCertificates.Count131072.C066519
import PlattCertificates.Count131072.C066520
import PlattCertificates.Count131072.C066521
import PlattCertificates.Count131072.C066522
import PlattCertificates.Count131072.C066523
import PlattCertificates.Count131072.C066524
import PlattCertificates.Count131072.C066525
import PlattCertificates.Count131072.C066526
import PlattCertificates.Count131072.C066527
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000203
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66496 : List PrefixCut := [⟨56,162433681,162433775⟩,
⟨64,184642253,184642360⟩]
theorem checked66496 : checkPrefixCuts (2^48) 8719695873 10 Manual.Count131072.C066496.packed 64 cuts66496 = true := by
 decide +kernel
def pointBounds66496 : List (Nat × Nat × Nat) := [(8719810560,115183406911343,115183796047752)]
theorem point_links_checked66496 : (cuts66496.take 1).map (fun c => (8719695873-1+2*2^10*c.k,115183244477662+c.lower,115183633613977+c.upper)) = pointBounds66496 := by
 decide +kernel
def cuts66497 : List PrefixCut := [⟨64,186350291,186350401⟩]
theorem checked66497 : checkPrefixCuts (2^48) 8719826945 10 Manual.Count131072.C066497.packed 64 cuts66497 = true := by
 decide +kernel
def cuts66498 : List PrefixCut := [⟨62,177373940,177374042⟩,
⟨64,183668327,183668433⟩]
theorem checked66498 : checkPrefixCuts (2^48) 8719958017 10 Manual.Count131072.C066498.packed 64 cuts66498 = true := by
 decide +kernel
def pointBounds66498 : List (Nat × Nat × Nat) := [(8720084992,115183792844146,115184181980780)]
theorem point_links_checked66498 : (cuts66498.take 1).map (fun c => (8719958017-1+2*2^10*c.k,115183615470206+c.lower,115184004606738+c.upper)) = pointBounds66498 := by
 decide +kernel
def cuts66499 : List PrefixCut := [⟨64,183536450,183536552⟩]
theorem checked66499 : checkPrefixCuts (2^48) 8720089089 10 Manual.Count131072.C066499.packed 64 cuts66499 = true := by
 decide +kernel
def cuts66500 : List PrefixCut := [⟨64,182759020,182759131⟩]
theorem checked66500 : checkPrefixCuts (2^48) 8720220161 10 Manual.Count131072.C066500.packed 64 cuts66500 = true := by
 decide +kernel
def cuts66501 : List PrefixCut := [⟨4,11329549,11329555⟩,
⟨64,186984644,186984755⟩]
theorem checked66501 : checkPrefixCuts (2^48) 8720351233 10 Manual.Count131072.C066501.packed 64 cuts66501 = true := by
 decide +kernel
def pointBounds66501 : List (Nat × Nat × Nat) := [(8720359424,115184176763552,115184565900409)]
theorem point_links_checked66501 : (cuts66501.take 1).map (fun c => (8720351233-1+2*2^10*c.k,115184165434003+c.lower,115184554570854+c.upper)) = pointBounds66501 := by
 decide +kernel
def cuts66502 : List PrefixCut := [⟨64,185755311,185755415⟩]
theorem checked66502 : checkPrefixCuts (2^48) 8720482305 10 Manual.Count131072.C066502.packed 64 cuts66502 = true := by
 decide +kernel
def cuts66503 : List PrefixCut := [⟨10,29113783,29113802⟩,
⟨64,185558863,185558971⟩]
theorem checked66503 : checkPrefixCuts (2^48) 8720613377 10 Manual.Count131072.C066503.packed 64 cuts66503 = true := by
 decide +kernel
def pointBounds66503 : List (Nat × Nat × Nat) := [(8720633856,115184567287741,115184956424826)]
theorem point_links_checked66503 : (cuts66503.take 1).map (fun c => (8720613377-1+2*2^10*c.k,115184538173958+c.lower,115184927311024+c.upper)) = pointBounds66503 := by
 decide +kernel
def cuts66504 : List PrefixCut := [⟨64,182877134,182877246⟩]
theorem checked66504 : checkPrefixCuts (2^48) 8720744449 10 Manual.Count131072.C066504.packed 64 cuts66504 = true := by
 decide +kernel
def cuts66505 : List PrefixCut := [⟨16,46800099,46800127⟩,
⟨64,184810938,184811043⟩]
theorem checked66505 : checkPrefixCuts (2^48) 8720875521 10 Manual.Count131072.C066505.packed 64 cuts66505 = true := by
 decide +kernel
def pointBounds66505 : List (Nat × Nat × Nat) := [(8720908288,115184953410054,115185342547368)]
theorem point_links_checked66505 : (cuts66505.take 1).map (fun c => (8720875521-1+2*2^10*c.k,115184906609955+c.lower,115185295747241+c.upper)) = pointBounds66505 := by
 decide +kernel
def cuts66506 : List PrefixCut := [⟨64,186647847,186647950⟩]
theorem checked66506 : checkPrefixCuts (2^48) 8721006593 10 Manual.Count131072.C066506.packed 64 cuts66506 = true := by
 decide +kernel
def cuts66507 : List PrefixCut := [⟨22,65066271,65066308⟩,
⟨64,184773111,184773215⟩]
theorem checked66507 : checkPrefixCuts (2^48) 8721137665 10 Manual.Count131072.C066507.packed 64 cuts66507 = true := by
 decide +kernel
def pointBounds66507 : List (Nat × Nat × Nat) := [(8721182720,115185343135011,115185732272542)]
theorem point_links_checked66507 : (cuts66507.take 1).map (fun c => (8721137665-1+2*2^10*c.k,115185278068740+c.lower,115185667206234+c.upper)) = pointBounds66507 := by
 decide +kernel
def cuts66508 : List PrefixCut := [⟨64,186964972,186965079⟩]
theorem checked66508 : checkPrefixCuts (2^48) 8721268737 10 Manual.Count131072.C066508.packed 64 cuts66508 = true := by
 decide +kernel
def cuts66509 : List PrefixCut := [⟨28,80943050,80943098⟩,
⟨64,185122556,185122662⟩]
theorem checked66509 : checkPrefixCuts (2^48) 8721399809 10 Manual.Count131072.C066509.packed 64 cuts66509 = true := by
 decide +kernel
def pointBounds66509 : List (Nat × Nat × Nat) := [(8721457152,115185730749873,115186119887626)]
theorem point_links_checked66509 : (cuts66509.take 1).map (fun c => (8721399809-1+2*2^10*c.k,115185649806823+c.lower,115186038944528+c.upper)) = pointBounds66509 := by
 decide +kernel
def cuts66510 : List PrefixCut := [⟨64,186927080,186927190⟩]
theorem checked66510 : checkPrefixCuts (2^48) 8721530881 10 Manual.Count131072.C066510.packed 64 cuts66510 = true := by
 decide +kernel
def cuts66511 : List PrefixCut := [⟨34,96883403,96883456⟩,
⟨64,182438354,182438454⟩]
theorem checked66511 : checkPrefixCuts (2^48) 8721661953 10 Manual.Count131072.C066511.packed 64 cuts66511 = true := by
 decide +kernel
def pointBounds66511 : List (Nat × Nat × Nat) := [(8721731584,115186118739862,115186507877836)]
theorem point_links_checked66511 : (cuts66511.take 1).map (fun c => (8721661953-1+2*2^10*c.k,115186021856459+c.lower,115186410994380+c.upper)) = pointBounds66511 := by
 decide +kernel
def cuts66512 : List PrefixCut := [⟨64,185598298,185598403⟩]
theorem checked66512 : checkPrefixCuts (2^48) 8721793025 10 Manual.Count131072.C066512.packed 64 cuts66512 = true := by
 decide +kernel
def cuts66513 : List PrefixCut := [⟨40,115824064,115824133⟩,
⟨64,185660060,185660168⟩]
theorem checked66513 : checkPrefixCuts (2^48) 8721924097 10 Manual.Count131072.C066513.packed 64 cuts66513 = true := by
 decide +kernel
def pointBounds66513 : List (Nat × Nat × Nat) := [(8722006016,115186505717175,115186894855370)]
theorem point_links_checked66513 : (cuts66513.take 1).map (fun c => (8721924097-1+2*2^10*c.k,115186389893111+c.lower,115186779031237+c.upper)) = pointBounds66513 := by
 decide +kernel
def cuts66514 : List PrefixCut := [⟨64,184689110,184689214⟩]
theorem checked66514 : checkPrefixCuts (2^48) 8722055169 10 Manual.Count131072.C066514.packed 64 cuts66514 = true := by
 decide +kernel
def cuts66515 : List PrefixCut := [⟨46,132052801,132052876⟩,
⟨64,184266833,184266936⟩]
theorem checked66515 : checkPrefixCuts (2^48) 8722186241 10 Manual.Count131072.C066515.packed 64 cuts66515 = true := by
 decide +kernel
def pointBounds66515 : List (Nat × Nat × Nat) := [(8722280448,115186892295082,115187281433495)]
theorem point_links_checked66515 : (cuts66515.take 1).map (fun c => (8722186241-1+2*2^10*c.k,115186760242281+c.lower,115187149380619+c.upper)) = pointBounds66515 := by
 decide +kernel
def cuts66516 : List PrefixCut := [⟨64,183747738,183747840⟩]
theorem checked66516 : checkPrefixCuts (2^48) 8722317313 10 Manual.Count131072.C066516.packed 64 cuts66516 = true := by
 decide +kernel
def cuts66517 : List PrefixCut := [⟨52,149990839,149990931⟩,
⟨64,184229024,184229136⟩]
theorem checked66517 : checkPrefixCuts (2^48) 8722448385 10 Manual.Count131072.C066517.packed 64 cuts66517 = true := by
 decide +kernel
def pointBounds66517 : List (Nat × Nat × Nat) := [(8722554880,115187278247691,115187667386326)]
theorem point_links_checked66517 : (cuts66517.take 1).map (fun c => (8722448385-1+2*2^10*c.k,115187128256852+c.lower,115187517395395+c.upper)) = pointBounds66517 := by
 decide +kernel
def cuts66518 : List PrefixCut := [⟨64,187614548,187614657⟩]
theorem checked66518 : checkPrefixCuts (2^48) 8722579457 10 Manual.Count131072.C066518.packed 64 cuts66518 = true := by
 decide +kernel
def cuts66519 : List PrefixCut := [⟨58,169186272,169186365⟩,
⟨64,186966346,186966450⟩]
theorem checked66519 : checkPrefixCuts (2^48) 8722710529 10 Manual.Count131072.C066519.packed 64 cuts66519 = true := by
 decide +kernel
def pointBounds66519 : List (Nat × Nat × Nat) := [(8722829312,115187669286696,115188058425553)]
theorem point_links_checked66519 : (cuts66519.take 1).map (fun c => (8722710529-1+2*2^10*c.k,115187500100424+c.lower,115187889239188+c.upper)) = pointBounds66519 := by
 decide +kernel
def cuts66520 : List PrefixCut := [⟨64,181381087,181381193⟩]
theorem checked66520 : checkPrefixCuts (2^48) 8722841601 10 Manual.Count131072.C066520.packed 64 cuts66520 = true := by
 decide +kernel
def cuts66521 : List PrefixCut := [⟨64,185185984,185186092⟩]
theorem checked66521 : checkPrefixCuts (2^48) 8722972673 10 Manual.Count131072.C066521.packed 64 cuts66521 = true := by
 decide +kernel
def pointBounds66521 : List (Nat × Nat × Nat) := [(8723103744,115188053633841,115188442772923)]
theorem point_links_checked66521 : (cuts66521.take 1).map (fun c => (8722972673-1+2*2^10*c.k,115187868447857+c.lower,115188257586831+c.upper)) = pointBounds66521 := by
 decide +kernel
def cuts66522 : List PrefixCut := [⟨64,185570401,185570505⟩]
theorem checked66522 : checkPrefixCuts (2^48) 8723103745 10 Manual.Count131072.C066522.packed 64 cuts66522 = true := by
 decide +kernel
def cuts66523 : List PrefixCut := [⟨64,183212124,183212235⟩]
theorem checked66523 : checkPrefixCuts (2^48) 8723234817 10 Manual.Count131072.C066523.packed 64 cuts66523 = true := by
 decide +kernel
def cuts66524 : List PrefixCut := [⟨6,17359513,17359524⟩,
⟨64,183015790,183015894⟩]
theorem checked66524 : checkPrefixCuts (2^48) 8723365889 10 Manual.Count131072.C066524.packed 64 cuts66524 = true := by
 decide +kernel
def pointBounds66524 : List (Nat × Nat × Nat) := [(8723378176,115188439775879,115188828915187)]
theorem point_links_checked66524 : (cuts66524.take 1).map (fun c => (8723365889-1+2*2^10*c.k,115188422416366+c.lower,115188811555663+c.upper)) = pointBounds66524 := by
 decide +kernel
def cuts66525 : List PrefixCut := [⟨64,185852440,185852550⟩]
theorem checked66525 : checkPrefixCuts (2^48) 8723496961 10 Manual.Count131072.C066525.packed 64 cuts66525 = true := by
 decide +kernel
def cuts66526 : List PrefixCut := [⟨12,35008351,35008373⟩,
⟨64,184720368,184720477⟩]
theorem checked66526 : checkPrefixCuts (2^48) 8723628033 10 Manual.Count131072.C066526.packed 64 cuts66526 = true := by
 decide +kernel
def pointBounds66526 : List (Nat × Nat × Nat) := [(8723652608,115188826292947,115189215432480)]
theorem point_links_checked66526 : (cuts66526.take 1).map (fun c => (8723628033-1+2*2^10*c.k,115188791284596+c.lower,115189180424107+c.upper)) = pointBounds66526 := by
 decide +kernel
def cuts66527 : List PrefixCut := [⟨64,183523771,183523876⟩]
theorem checked66527 : checkPrefixCuts (2^48) 8723759105 10 Manual.Count131072.C066527.packed 64 cuts66527 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000203
