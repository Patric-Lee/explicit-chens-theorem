import PlattAssemblyKernel
import PlattCertificates.Count131072.C064544
import PlattCertificates.Count131072.C064545
import PlattCertificates.Count131072.C064546
import PlattCertificates.Count131072.C064547
import PlattCertificates.Count131072.C064548
import PlattCertificates.Count131072.C064549
import PlattCertificates.Count131072.C064550
import PlattCertificates.Count131072.C064551
import PlattCertificates.Count131072.C064552
import PlattCertificates.Count131072.C064553
import PlattCertificates.Count131072.C064554
import PlattCertificates.Count131072.C064555
import PlattCertificates.Count131072.C064556
import PlattCertificates.Count131072.C064557
import PlattCertificates.Count131072.C064558
import PlattCertificates.Count131072.C064559
import PlattCertificates.Count131072.C064560
import PlattCertificates.Count131072.C064561
import PlattCertificates.Count131072.C064562
import PlattCertificates.Count131072.C064563
import PlattCertificates.Count131072.C064564
import PlattCertificates.Count131072.C064565
import PlattCertificates.Count131072.C064566
import PlattCertificates.Count131072.C064567
import PlattCertificates.Count131072.C064568
import PlattCertificates.Count131072.C064569
import PlattCertificates.Count131072.C064570
import PlattCertificates.Count131072.C064571
import PlattCertificates.Count131072.C064572
import PlattCertificates.Count131072.C064573
import PlattCertificates.Count131072.C064574
import PlattCertificates.Count131072.C064575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000142
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64544 : List PrefixCut := [⟨64,193150254,193150367⟩]
theorem checked64544 : checkPrefixCuts (2^48) 8463843329 10 Manual.Count131072.C064544.packed 64 cuts64544 = true := by
 decide +kernel
def cuts64545 : List PrefixCut := [⟨50,147820427,147820515⟩,
⟨64,189156618,189156733⟩]
theorem checked64545 : checkPrefixCuts (2^48) 8463974401 10 Manual.Count131072.C064545.packed 64 cuts64545 = true := by
 decide +kernel
def pointBounds64545 : List (Nat × Nat × Nat) := [(8464076800,114817111867763,114817500791901)]
theorem point_links_checked64545 : (cuts64545.take 1).map (fun c => (8463974401-1+2*2^10*c.k,114816964047336+c.lower,114817352971386+c.upper)) = pointBounds64545 := by
 decide +kernel
def cuts64546 : List PrefixCut := [⟨64,190317612,190317721⟩]
theorem checked64546 : checkPrefixCuts (2^48) 8464105473 10 Manual.Count131072.C064546.packed 64 cuts64546 = true := by
 decide +kernel
def cuts64547 : List PrefixCut := [⟨52,157758886,157758975⟩,
⟨64,192309943,192310052⟩]
theorem checked64547 : checkPrefixCuts (2^48) 8464236545 10 Manual.Count131072.C064547.packed 64 cuts64547 = true := by
 decide +kernel
def pointBounds64547 : List (Nat × Nat × Nat) := [(8464343040,114817501280452,114817890204815)]
theorem point_links_checked64547 : (cuts64547.take 1).map (fun c => (8464236545-1+2*2^10*c.k,114817343521566+c.lower,114817732445840+c.upper)) = pointBounds64547 := by
 decide +kernel
def cuts64548 : List PrefixCut := [⟨64,193903138,193903250⟩]
theorem checked64548 : checkPrefixCuts (2^48) 8464367617 10 Manual.Count131072.C064548.packed 64 cuts64548 = true := by
 decide +kernel
def cuts64549 : List PrefixCut := [⟨54,162043656,162043751⟩,
⟨64,192636516,192636626⟩]
theorem checked64549 : checkPrefixCuts (2^48) 8464498689 10 Manual.Count131072.C064549.packed 64 cuts64549 = true := by
 decide +kernel
def pointBounds64549 : List (Nat × Nat × Nat) := [(8464609280,114817891778303,114818280702893)]
theorem point_links_checked64549 : (cuts64549.take 1).map (fun c => (8464498689-1+2*2^10*c.k,114817729734647+c.lower,114818118659142+c.upper)) = pointBounds64549 := by
 decide +kernel
def cuts64550 : List PrefixCut := [⟨64,192167963,192168075⟩]
theorem checked64550 : checkPrefixCuts (2^48) 8464629761 10 Manual.Count131072.C064550.packed 64 cuts64550 = true := by
 decide +kernel
def cuts64551 : List PrefixCut := [⟨56,169054823,169054919⟩,
⟨64,192663790,192663901⟩]
theorem checked64551 : checkPrefixCuts (2^48) 8464760833 10 Manual.Count131072.C064551.packed 64 cuts64551 = true := by
 decide +kernel
def pointBounds64551 : List (Nat × Nat × Nat) := [(8464875520,114818283593949,114818672518762)]
theorem point_links_checked64551 : (cuts64551.take 1).map (fun c => (8464760833-1+2*2^10*c.k,114818114539126+c.lower,114818503463843+c.upper)) = pointBounds64551 := by
 decide +kernel
def cuts64552 : List PrefixCut := [⟨64,193824624,193824731⟩]
theorem checked64552 : checkPrefixCuts (2^48) 8464891905 10 Manual.Count131072.C064552.packed 64 cuts64552 = true := by
 decide +kernel
def cuts64553 : List PrefixCut := [⟨58,172906712,172906800⟩,
⟨64,191460788,191460887⟩]
theorem checked64553 : checkPrefixCuts (2^48) 8465022977 10 Manual.Count131072.C064553.packed 64 cuts64553 = true := by
 decide +kernel
def pointBounds64553 : List (Nat × Nat × Nat) := [(8465141760,114818673934252,114819062859275)]
theorem point_links_checked64553 : (cuts64553.take 1).map (fun c => (8465022977-1+2*2^10*c.k,114818501027540+c.lower,114818889952475+c.upper)) = pointBounds64553 := by
 decide +kernel
def cuts64554 : List PrefixCut := [⟨64,189363016,189363128⟩]
theorem checked64554 : checkPrefixCuts (2^48) 8465154049 10 Manual.Count131072.C064554.packed 64 cuts64554 = true := by
 decide +kernel
def cuts64555 : List PrefixCut := [⟨60,183109134,183109242⟩,
⟨64,195045881,195045997⟩]
theorem checked64555 : checkPrefixCuts (2^48) 8465285121 10 Manual.Count131072.C064555.packed 64 cuts64555 = true := by
 decide +kernel
def pointBounds64555 : List (Nat × Nat × Nat) := [(8465408000,114819064960478,114819453885732)]
theorem point_links_checked64555 : (cuts64555.take 1).map (fun c => (8465285121-1+2*2^10*c.k,114818881851344+c.lower,114819270776490+c.upper)) = pointBounds64555 := by
 decide +kernel
def cuts64556 : List PrefixCut := [⟨64,190820154,190820263⟩]
theorem checked64556 : checkPrefixCuts (2^48) 8465416193 10 Manual.Count131072.C064556.packed 64 cuts64556 = true := by
 decide +kernel
def cuts64557 : List PrefixCut := [⟨62,183735153,183735261⟩,
⟨64,189919459,189919570⟩]
theorem checked64557 : checkPrefixCuts (2^48) 8465547265 10 Manual.Count131072.C064557.packed 64 cuts64557 = true := by
 decide +kernel
def pointBounds64557 : List (Nat × Nat × Nat) := [(8465674240,114819451452532,114819840378011)]
theorem point_links_checked64557 : (cuts64557.take 1).map (fun c => (8465547265-1+2*2^10*c.k,114819267717379+c.lower,114819656642750+c.upper)) = pointBounds64557 := by
 decide +kernel
def cuts64558 : List PrefixCut := [⟨64,190647995,190648106⟩]
theorem checked64558 : checkPrefixCuts (2^48) 8465678337 10 Manual.Count131072.C064558.packed 64 cuts64558 = true := by
 decide +kernel
def cuts64559 : List PrefixCut := [⟨64,190046560,190046670⟩]
theorem checked64559 : checkPrefixCuts (2^48) 8465809409 10 Manual.Count131072.C064559.packed 64 cuts64559 = true := by
 decide +kernel
def pointBounds64559 : List (Nat × Nat × Nat) := [(8465940480,114819838331393,114820227257096)]
theorem point_links_checked64559 : (cuts64559.take 1).map (fun c => (8465809409-1+2*2^10*c.k,114819648284833+c.lower,114820037210426+c.upper)) = pointBounds64559 := by
 decide +kernel
def cuts64560 : List PrefixCut := [⟨64,188580717,188580829⟩]
theorem checked64560 : checkPrefixCuts (2^48) 8465940481 10 Manual.Count131072.C064560.packed 64 cuts64560 = true := by
 decide +kernel
def cuts64561 : List PrefixCut := [⟨64,191536811,191536922⟩]
theorem checked64561 : checkPrefixCuts (2^48) 8466071553 10 Manual.Count131072.C064561.packed 64 cuts64561 = true := by
 decide +kernel
def cuts64562 : List PrefixCut := [⟨2,6217166,6217170⟩,
⟨64,187943217,187943321⟩]
theorem checked64562 : checkPrefixCuts (2^48) 8466202625 10 Manual.Count131072.C064562.packed 64 cuts64562 = true := by
 decide +kernel
def pointBounds64562 : List (Nat × Nat × Nat) := [(8466206720,114820224666087,114820613592017)]
theorem point_links_checked64562 : (cuts64562.take 1).map (fun c => (8466202625-1+2*2^10*c.k,114820218448921+c.lower,114820607374847+c.upper)) = pointBounds64562 := by
 decide +kernel
def cuts64563 : List PrefixCut := [⟨64,192229047,192229153⟩]
theorem checked64563 : checkPrefixCuts (2^48) 8466333697 10 Manual.Count131072.C064563.packed 64 cuts64563 = true := by
 decide +kernel
def cuts64564 : List PrefixCut := [⟨4,11902012,11902019⟩,
⟨64,186840263,186840369⟩]
theorem checked64564 : checkPrefixCuts (2^48) 8466464769 10 Manual.Count131072.C064564.packed 64 cuts64564 = true := by
 decide +kernel
def pointBounds64564 : List (Nat × Nat × Nat) := [(8466472960,114820610523197,114820999449340)]
theorem point_links_checked64564 : (cuts64564.take 1).map (fun c => (8466464769-1+2*2^10*c.k,114820598621185+c.lower,114820987547321+c.upper)) = pointBounds64564 := by
 decide +kernel
def cuts64565 : List PrefixCut := [⟨64,192056864,192056975⟩]
theorem checked64565 : checkPrefixCuts (2^48) 8466595841 10 Manual.Count131072.C064565.packed 64 cuts64565 = true := by
 decide +kernel
def cuts64566 : List PrefixCut := [⟨6,18218154,18218164⟩,
⟨64,190657621,190657732⟩]
theorem checked64566 : checkPrefixCuts (2^48) 8466726913 10 Manual.Count131072.C064566.packed 64 cuts64566 = true := by
 decide +kernel
def pointBounds64566 : List (Nat × Nat × Nat) := [(8466739200,114820995736466,114821384662829)]
theorem point_links_checked64566 : (cuts64566.take 1).map (fun c => (8466726913-1+2*2^10*c.k,114820977518312+c.lower,114821366444665+c.upper)) = pointBounds64566 := by
 decide +kernel
def cuts64567 : List PrefixCut := [⟨64,193247701,193247811⟩]
theorem checked64567 : checkPrefixCuts (2^48) 8466857985 10 Manual.Count131072.C064567.packed 64 cuts64567 = true := by
 decide +kernel
def cuts64568 : List PrefixCut := [⟨8,22938200,22938213⟩,
⟨64,188790065,188790175⟩]
theorem checked64568 : checkPrefixCuts (2^48) 8466989057 10 Manual.Count131072.C064568.packed 64 cuts64568 = true := by
 decide +kernel
def pointBounds64568 : List (Nat × Nat × Nat) := [(8467005440,114821384361834,114821773288421)]
theorem point_links_checked64568 : (cuts64568.take 1).map (fun c => (8466989057-1+2*2^10*c.k,114821361423634+c.lower,114821750350208+c.upper)) = pointBounds64568 := by
 decide +kernel
def cuts64569 : List PrefixCut := [⟨64,189119592,189119704⟩]
theorem checked64569 : checkPrefixCuts (2^48) 8467120129 10 Manual.Count131072.C064569.packed 64 cuts64569 = true := by
 decide +kernel
def cuts64570 : List PrefixCut := [⟨10,27458496,27458513⟩,
⟨64,186291030,186291143⟩]
theorem checked64570 : checkPrefixCuts (2^48) 8467251201 10 Manual.Count131072.C064570.packed 64 cuts64570 = true := by
 decide +kernel
def pointBounds64570 : List (Nat × Nat × Nat) := [(8467271680,114821766791787,114822155718600)]
theorem point_links_checked64570 : (cuts64570.take 1).map (fun c => (8467251201-1+2*2^10*c.k,114821739333291+c.lower,114822128260087+c.upper)) = pointBounds64570 := by
 decide +kernel
def cuts64571 : List PrefixCut := [⟨64,190410175,190410279⟩]
theorem checked64571 : checkPrefixCuts (2^48) 8467382273 10 Manual.Count131072.C064571.packed 64 cuts64571 = true := by
 decide +kernel
def cuts64572 : List PrefixCut := [⟨12,35901032,35901051⟩,
⟨64,190872611,190872720⟩]
theorem checked64572 : checkPrefixCuts (2^48) 8467513345 10 Manual.Count131072.C064572.packed 64 cuts64572 = true := by
 decide +kernel
def pointBounds64572 : List (Nat × Nat × Nat) := [(8467537920,114822151935528,114822540862560)]
theorem point_links_checked64572 : (cuts64572.take 1).map (fun c => (8467513345-1+2*2^10*c.k,114822116034496+c.lower,114822504961509+c.upper)) = pointBounds64572 := by
 decide +kernel
def cuts64573 : List PrefixCut := [⟨64,190503994,190504108⟩]
theorem checked64573 : checkPrefixCuts (2^48) 8467644417 10 Manual.Count131072.C064573.packed 64 cuts64573 = true := by
 decide +kernel
def cuts64574 : List PrefixCut := [⟨14,42714245,42714268⟩,
⟨64,191996877,191996983⟩]
theorem checked64574 : checkPrefixCuts (2^48) 8467775489 10 Manual.Count131072.C064574.packed 64 cuts64574 = true := by
 decide +kernel
def pointBounds64574 : List (Nat × Nat × Nat) := [(8467804160,114822540125346,114822929052605)]
theorem point_links_checked64574 : (cuts64574.take 1).map (fun c => (8467775489-1+2*2^10*c.k,114822497411101+c.lower,114822886338337+c.upper)) = pointBounds64574 := by
 decide +kernel
def cuts64575 : List PrefixCut := [⟨64,188337507,188337616⟩]
theorem checked64575 : checkPrefixCuts (2^48) 8467906561 10 Manual.Count131072.C064575.packed 64 cuts64575 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000142
