import PlattAssemblyKernel
import PlattCertificates.Count131072.C063488
import PlattCertificates.Count131072.C063489
import PlattCertificates.Count131072.C063490
import PlattCertificates.Count131072.C063491
import PlattCertificates.Count131072.C063492
import PlattCertificates.Count131072.C063493
import PlattCertificates.Count131072.C063494
import PlattCertificates.Count131072.C063495
import PlattCertificates.Count131072.C063496
import PlattCertificates.Count131072.C063497
import PlattCertificates.Count131072.C063498
import PlattCertificates.Count131072.C063499
import PlattCertificates.Count131072.C063500
import PlattCertificates.Count131072.C063501
import PlattCertificates.Count131072.C063502
import PlattCertificates.Count131072.C063503
import PlattCertificates.Count131072.C063504
import PlattCertificates.Count131072.C063505
import PlattCertificates.Count131072.C063506
import PlattCertificates.Count131072.C063507
import PlattCertificates.Count131072.C063508
import PlattCertificates.Count131072.C063509
import PlattCertificates.Count131072.C063510
import PlattCertificates.Count131072.C063511
import PlattCertificates.Count131072.C063512
import PlattCertificates.Count131072.C063513
import PlattCertificates.Count131072.C063514
import PlattCertificates.Count131072.C063515
import PlattCertificates.Count131072.C063516
import PlattCertificates.Count131072.C063517
import PlattCertificates.Count131072.C063518
import PlattCertificates.Count131072.C063519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000109
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63488 : List PrefixCut := [⟨48,147710844,147710927⟩,
⟨64,195279518,195279627⟩]
theorem checked63488 : checkPrefixCuts (2^48) 8325431297 10 Manual.Count131072.C063488.packed 64 cuts63488 = true := by
 decide +kernel
def pointBounds63488 : List (Nat × Nat × Nat) := [(8325529600,114613818200560,114614207007477)]
theorem point_links_checked63488 : (cuts63488.take 1).map (fun c => (8325431297-1+2*2^10*c.k,114613670489716+c.lower,114614059296550+c.upper)) = pointBounds63488 := by
 decide +kernel
def cuts63489 : List PrefixCut := [⟨64,195580711,195580822⟩]
theorem checked63489 : checkPrefixCuts (2^48) 8325562369 10 Manual.Count131072.C063489.packed 64 cuts63489 = true := by
 decide +kernel
def cuts63490 : List PrefixCut := [⟨48,143446424,143446509⟩,
⟨64,190540297,190540409⟩]
theorem checked63490 : checkPrefixCuts (2^48) 8325693441 10 Manual.Count131072.C063490.packed 64 cuts63490 = true := by
 decide +kernel
def pointBounds63490 : List (Nat × Nat × Nat) := [(8325791744,114614204796369,114614593603508)]
theorem point_links_checked63490 : (cuts63490.take 1).map (fun c => (8325693441-1+2*2^10*c.k,114614061349945+c.lower,114614450156999+c.upper)) = pointBounds63490 := by
 decide +kernel
def cuts63491 : List PrefixCut := [⟨64,196149271,196149381⟩]
theorem checked63491 : checkPrefixCuts (2^48) 8325824513 10 Manual.Count131072.C063491.packed 64 cuts63491 = true := by
 decide +kernel
def cuts63492 : List PrefixCut := [⟨48,146247855,146247942⟩,
⟨64,193374049,193374166⟩]
theorem checked63492 : checkPrefixCuts (2^48) 8325955585 10 Manual.Count131072.C063492.packed 64 cuts63492 = true := by
 decide +kernel
def pointBounds63492 : List (Nat × Nat × Nat) := [(8326053888,114614594287368,114614983094731)]
theorem point_links_checked63492 : (cuts63492.take 1).map (fun c => (8325955585-1+2*2^10*c.k,114614448039513+c.lower,114614836846789+c.upper)) = pointBounds63492 := by
 decide +kernel
def cuts63493 : List PrefixCut := [⟨64,195906459,195906572⟩]
theorem checked63493 : checkPrefixCuts (2^48) 8326086657 10 Manual.Count131072.C063493.packed 64 cuts63493 = true := by
 decide +kernel
def cuts63494 : List PrefixCut := [⟨48,142592244,142592327⟩,
⟨64,191677666,191677777⟩]
theorem checked63494 : checkPrefixCuts (2^48) 8326217729 10 Manual.Count131072.C063494.packed 64 cuts63494 = true := by
 decide +kernel
def pointBounds63494 : List (Nat × Nat × Nat) := [(8326316032,114614979912265,114615368719854)]
theorem point_links_checked63494 : (cuts63494.take 1).map (fun c => (8326217729-1+2*2^10*c.k,114614837320021+c.lower,114615226127527+c.upper)) = pointBounds63494 := by
 decide +kernel
def cuts63495 : List PrefixCut := [⟨64,192418378,192418493⟩]
theorem checked63495 : checkPrefixCuts (2^48) 8326348801 10 Manual.Count131072.C063495.packed 64 cuts63495 = true := by
 decide +kernel
def cuts63496 : List PrefixCut := [⟨48,146238648,146238731⟩,
⟨64,192922419,192922529⟩]
theorem checked63496 : checkPrefixCuts (2^48) 8326479873 10 Manual.Count131072.C063496.packed 64 cuts63496 = true := by
 decide +kernel
def pointBounds63496 : List (Nat × Nat × Nat) := [(8326578176,114615367654713,114615756462528)]
theorem point_links_checked63496 : (cuts63496.take 1).map (fun c => (8326479873-1+2*2^10*c.k,114615221416065+c.lower,114615610223797+c.upper)) = pointBounds63496 := by
 decide +kernel
def cuts63497 : List PrefixCut := [⟨64,194237731,194237848⟩]
theorem checked63497 : checkPrefixCuts (2^48) 8326610945 10 Manual.Count131072.C063497.packed 64 cuts63497 = true := by
 decide +kernel
def cuts63498 : List PrefixCut := [⟨48,143326946,143327030⟩,
⟨64,192443084,192443198⟩]
theorem checked63498 : checkPrefixCuts (2^48) 8326742017 10 Manual.Count131072.C063498.packed 64 cuts63498 = true := by
 decide +kernel
def pointBounds63498 : List (Nat × Nat × Nat) := [(8326840320,114615751903161,114616140711204)]
theorem point_links_checked63498 : (cuts63498.take 1).map (fun c => (8326742017-1+2*2^10*c.k,114615608576215+c.lower,114615997384174+c.upper)) = pointBounds63498 := by
 decide +kernel
def cuts63499 : List PrefixCut := [⟨64,193454135,193454247⟩]
theorem checked63499 : checkPrefixCuts (2^48) 8326873089 10 Manual.Count131072.C063499.packed 64 cuts63499 = true := by
 decide +kernel
def cuts63500 : List PrefixCut := [⟨48,149406877,149406964⟩,
⟨64,199265115,199265230⟩]
theorem checked63500 : checkPrefixCuts (2^48) 8327004161 10 Manual.Count131072.C063500.packed 64 cuts63500 = true := by
 decide +kernel
def pointBounds63500 : List (Nat × Nat × Nat) := [(8327102464,114616143880311,114616532688583)]
theorem point_links_checked63500 : (cuts63500.take 1).map (fun c => (8327004161-1+2*2^10*c.k,114615994473434+c.lower,114616383281619+c.upper)) = pointBounds63500 := by
 decide +kernel
def cuts63501 : List PrefixCut := [⟨64,190642513,190642619⟩]
theorem checked63501 : checkPrefixCuts (2^48) 8327135233 10 Manual.Count131072.C063501.packed 64 cuts63501 = true := by
 decide +kernel
def cuts63502 : List PrefixCut := [⟨48,145853022,145853106⟩,
⟨64,193816828,193816935⟩]
theorem checked63502 : checkPrefixCuts (2^48) 8327266305 10 Manual.Count131072.C063502.packed 64 cuts63502 = true := by
 decide +kernel
def pointBounds63502 : List (Nat × Nat × Nat) := [(8327364608,114616530234084,114616919042574)]
theorem point_links_checked63502 : (cuts63502.take 1).map (fun c => (8327266305-1+2*2^10*c.k,114616384381062+c.lower,114616773189468+c.upper)) = pointBounds63502 := by
 decide +kernel
def cuts63503 : List PrefixCut := [⟨64,197126264,197126375⟩]
theorem checked63503 : checkPrefixCuts (2^48) 8327397377 10 Manual.Count131072.C063503.packed 64 cuts63503 = true := by
 decide +kernel
def cuts63504 : List PrefixCut := [⟨48,145138623,145138706⟩,
⟨64,193134717,193134828⟩]
theorem checked63504 : checkPrefixCuts (2^48) 8327528449 10 Manual.Count131072.C063504.packed 64 cuts63504 = true := by
 decide +kernel
def pointBounds63504 : List (Nat × Nat × Nat) := [(8327626752,114616920462777,114617309271484)]
theorem point_links_checked63504 : (cuts63504.take 1).map (fun c => (8327528449-1+2*2^10*c.k,114616775324154+c.lower,114617164132778+c.upper)) = pointBounds63504 := by
 decide +kernel
def cuts63505 : List PrefixCut := [⟨64,192996486,192996598⟩]
theorem checked63505 : checkPrefixCuts (2^48) 8327659521 10 Manual.Count131072.C063505.packed 64 cuts63505 = true := by
 decide +kernel
def cuts63506 : List PrefixCut := [⟨48,145505855,145505944⟩,
⟨64,192047080,192047198⟩]
theorem checked63506 : checkPrefixCuts (2^48) 8327790593 10 Manual.Count131072.C063506.packed 64 cuts63506 = true := by
 decide +kernel
def pointBounds63506 : List (Nat × Nat × Nat) := [(8327888896,114617306961212,114617695770148)]
theorem point_links_checked63506 : (cuts63506.take 1).map (fun c => (8327790593-1+2*2^10*c.k,114617161455357+c.lower,114617550264204+c.upper)) = pointBounds63506 := by
 decide +kernel
def cuts63507 : List PrefixCut := [⟨64,194139569,194139680⟩]
theorem checked63507 : checkPrefixCuts (2^48) 8327921665 10 Manual.Count131072.C063507.packed 64 cuts63507 = true := by
 decide +kernel
def cuts63508 : List PrefixCut := [⟨48,147461580,147461662⟩,
⟨64,195488453,195488560⟩]
theorem checked63508 : checkPrefixCuts (2^48) 8328052737 10 Manual.Count131072.C063508.packed 64 cuts63508 = true := by
 decide +kernel
def pointBounds63508 : List (Nat × Nat × Nat) := [(8328151040,114617695103586,114618083912744)]
theorem point_links_checked63508 : (cuts63508.take 1).map (fun c => (8328052737-1+2*2^10*c.k,114617547642006+c.lower,114617936451082+c.upper)) = pointBounds63508 := by
 decide +kernel
def cuts63509 : List PrefixCut := [⟨64,193896857,193896967⟩]
theorem checked63509 : checkPrefixCuts (2^48) 8328183809 10 Manual.Count131072.C063509.packed 64 cuts63509 = true := by
 decide +kernel
def cuts63510 : List PrefixCut := [⟨48,148369455,148369538⟩,
⟨64,196935568,196935676⟩]
theorem checked63510 : checkPrefixCuts (2^48) 8328314881 10 Manual.Count131072.C063510.packed 64 cuts63510 = true := by
 decide +kernel
def pointBounds63510 : List (Nat × Nat × Nat) := [(8328413184,114618085396771,114618474206147)]
theorem point_links_checked63510 : (cuts63510.take 1).map (fun c => (8328314881-1+2*2^10*c.k,114617937027316+c.lower,114618325836609+c.upper)) = pointBounds63510 := by
 decide +kernel
def cuts63511 : List PrefixCut := [⟨64,193992168,193992283⟩]
theorem checked63511 : checkPrefixCuts (2^48) 8328445953 10 Manual.Count131072.C063511.packed 64 cuts63511 = true := by
 decide +kernel
def cuts63512 : List PrefixCut := [⟨48,145627299,145627384⟩,
⟨64,193853924,193854037⟩]
theorem checked63512 : checkPrefixCuts (2^48) 8328577025 10 Manual.Count131072.C063512.packed 64 cuts63512 = true := by
 decide +kernel
def pointBounds63512 : List (Nat × Nat × Nat) := [(8328675328,114618473582351,114618862391952)]
theorem point_links_checked63512 : (cuts63512.take 1).map (fun c => (8328577025-1+2*2^10*c.k,114618327955052+c.lower,114618716764568+c.upper)) = pointBounds63512 := by
 decide +kernel
def cuts63513 : List PrefixCut := [⟨64,192363877,192363992⟩]
theorem checked63513 : checkPrefixCuts (2^48) 8328708097 10 Manual.Count131072.C063513.packed 64 cuts63513 = true := by
 decide +kernel
def cuts63514 : List PrefixCut := [⟨48,143493634,143493719⟩,
⟨64,191718741,191718853⟩]
theorem checked63514 : checkPrefixCuts (2^48) 8328839169 10 Manual.Count131072.C063514.packed 64 cuts63514 = true := by
 decide +kernel
def pointBounds63514 : List (Nat × Nat × Nat) := [(8328937472,114618857666487,114619246476316)]
theorem point_links_checked63514 : (cuts63514.take 1).map (fun c => (8328839169-1+2*2^10*c.k,114618714172853+c.lower,114619102982597+c.upper)) = pointBounds63514 := by
 decide +kernel
def cuts63515 : List PrefixCut := [⟨64,190363938,190364048⟩]
theorem checked63515 : checkPrefixCuts (2^48) 8328970241 10 Manual.Count131072.C063515.packed 64 cuts63515 = true := by
 decide +kernel
def cuts63516 : List PrefixCut := [⟨48,146767120,146767206⟩,
⟨64,193943099,193943214⟩]
theorem checked63516 : checkPrefixCuts (2^48) 8329101313 10 Manual.Count131072.C063516.packed 64 cuts63516 = true := by
 decide +kernel
def pointBounds63516 : List (Nat × Nat × Nat) := [(8329199616,114619243022652,114619631832704)]
theorem point_links_checked63516 : (cuts63516.take 1).map (fun c => (8329101313-1+2*2^10*c.k,114619096255532+c.lower,114619485065498+c.upper)) = pointBounds63516 := by
 decide +kernel
def cuts63517 : List PrefixCut := [⟨64,196744898,196745012⟩]
theorem checked63517 : checkPrefixCuts (2^48) 8329232385 10 Manual.Count131072.C063517.packed 64 cuts63517 = true := by
 decide +kernel
def cuts63518 : List PrefixCut := [⟨48,145444591,145444671⟩,
⟨64,193261151,193261254⟩]
theorem checked63518 : checkPrefixCuts (2^48) 8329363457 10 Manual.Count131072.C063518.packed 64 cuts63518 = true := by
 decide +kernel
def pointBounds63518 : List (Nat × Nat × Nat) := [(8329461760,114619632388120,114620021198395)]
theorem point_links_checked63518 : (cuts63518.take 1).map (fun c => (8329363457-1+2*2^10*c.k,114619486943529+c.lower,114619875753724+c.upper)) = pointBounds63518 := by
 decide +kernel
def cuts63519 : List PrefixCut := [⟨64,193832554,193832672⟩]
theorem checked63519 : checkPrefixCuts (2^48) 8329494529 10 Manual.Count131072.C063519.packed 64 cuts63519 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000109
