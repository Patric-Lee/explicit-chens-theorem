import PlattAssemblyKernel
import PlattCertificates.Count131072.C058480
import PlattCertificates.Count131072.C058481
import PlattCertificates.Count131072.C058482
import PlattCertificates.Count131072.C058483
import PlattCertificates.Count131072.C058484
import PlattCertificates.Count131072.C058485
import PlattCertificates.Count131072.C058486
import PlattCertificates.Count131072.C058487
import PlattCertificates.Count131072.C058488
import PlattCertificates.Count131072.C058489
import PlattCertificates.Count131072.C058490
import PlattCertificates.Count131072.C058491
import PlattCertificates.Count131072.C058492
import PlattCertificates.Count131072.C058493
import PlattCertificates.Count131072.C058494
import PlattCertificates.Count131072.C058495
import PlattCertificates.Count131072.C058496
import PlattCertificates.Count131072.C058497
import PlattCertificates.Count131072.C058498
import PlattCertificates.Count131072.C058499
import PlattCertificates.Count131072.C058500
import PlattCertificates.Count131072.C058501
import PlattCertificates.Count131072.C058502
import PlattCertificates.Count131072.C058503
import PlattCertificates.Count131072.C058504
import PlattCertificates.Count131072.C058505
import PlattCertificates.Count131072.C058506
import PlattCertificates.Count131072.C058507
import PlattCertificates.Count131072.C058508
import PlattCertificates.Count131072.C058509
import PlattCertificates.Count131072.C058510
import PlattCertificates.Count131072.C058511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000265
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58480 : List PrefixCut := [⟨64,209461300,209461415⟩]
theorem checked58480 : checkPrefixCuts (2^48) 7669022721 10 Manual.Count131072.C058480.packed 64 cuts58480 = true := by
 decide +kernel
def cuts58481 : List PrefixCut := [⟨16,54172347,54172377⟩,
⟨64,211476340,211476459⟩]
theorem checked58481 : checkPrefixCuts (2^48) 7669153793 10 Manual.Count131072.C058481.packed 64 cuts58481 = true := by
 decide +kernel
def pointBounds58481 : List (Nat × Nat × Nat) := [(7669186560,113600063538322,113600451764780)]
theorem point_links_checked58481 : (cuts58481.take 1).map (fun c => (7669153793-1+2*2^10*c.k,113600009365975+c.lower,113600397592403+c.upper)) = pointBounds58481 := by
 decide +kernel
def cuts58482 : List PrefixCut := [⟨64,212683857,212683978⟩]
theorem checked58482 : checkPrefixCuts (2^48) 7669284865 10 Manual.Count131072.C058482.packed 64 cuts58482 = true := by
 decide +kernel
def cuts58483 : List PrefixCut := [⟨6,20185509,20185521⟩,
⟨64,211982920,211983040⟩]
theorem checked58483 : checkPrefixCuts (2^48) 7669415937 10 Manual.Count131072.C058483.packed 64 cuts58483 = true := by
 decide +kernel
def pointBounds58483 : List (Nat × Nat × Nat) := [(7669428224,113600453711681,113600841938361)]
theorem point_links_checked58483 : (cuts58483.take 1).map (fun c => (7669415937-1+2*2^10*c.k,113600433526172+c.lower,113600821752840+c.upper)) = pointBounds58483 := by
 decide +kernel
def cuts58484 : List PrefixCut := [⟨60,198180188,198180303⟩,
⟨64,211355389,211355511⟩]
theorem checked58484 : checkPrefixCuts (2^48) 7669547009 10 Manual.Count131072.C058484.packed 64 cuts58484 = true := by
 decide +kernel
def pointBounds58484 : List (Nat × Nat × Nat) := [(7669669888,113600843689280,113601231916183)]
theorem point_links_checked58484 : (cuts58484.take 1).map (fun c => (7669547009-1+2*2^10*c.k,113600645509092+c.lower,113601033735880+c.upper)) = pointBounds58484 := by
 decide +kernel
def cuts58485 : List PrefixCut := [⟨64,207388234,207388353⟩]
theorem checked58485 : checkPrefixCuts (2^48) 7669678081 10 Manual.Count131072.C058485.packed 64 cuts58485 = true := by
 decide +kernel
def cuts58486 : List PrefixCut := [⟨50,165585113,165585207⟩,
⟨64,211421559,211421680⟩]
theorem checked58486 : checkPrefixCuts (2^48) 7669809153 10 Manual.Count131072.C058486.packed 64 cuts58486 = true := by
 decide +kernel
def pointBounds58486 : List (Nat × Nat × Nat) := [(7669911552,113601229837828,113601618064951)]
theorem point_links_checked58486 : (cuts58486.take 1).map (fun c => (7669809153-1+2*2^10*c.k,113601064252715+c.lower,113601452479744+c.upper)) = pointBounds58486 := by
 decide +kernel
def cuts58487 : List PrefixCut := [⟨64,211307852,211307974⟩]
theorem checked58487 : checkPrefixCuts (2^48) 7669940225 10 Manual.Count131072.C058487.packed 64 cuts58487 = true := by
 decide +kernel
def cuts58488 : List PrefixCut := [⟨40,129726101,129726176⟩,
⟨64,209212478,209212600⟩]
theorem checked58488 : checkPrefixCuts (2^48) 7670071297 10 Manual.Count131072.C058488.packed 64 cuts58488 = true := by
 decide +kernel
def pointBounds58488 : List (Nat × Nat × Nat) := [(7670153216,113601616708227,113602004935574)]
theorem point_links_checked58488 : (cuts58488.take 1).map (fun c => (7670071297-1+2*2^10*c.k,113601486982126+c.lower,113601875209398+c.upper)) = pointBounds58488 := by
 decide +kernel
def cuts58489 : List PrefixCut := [⟨64,214273064,214273185⟩]
theorem checked58489 : checkPrefixCuts (2^48) 7670202369 10 Manual.Count131072.C058489.packed 64 cuts58489 = true := by
 decide +kernel
def cuts58490 : List PrefixCut := [⟨30,98383103,98383159⟩,
⟨64,212948342,212948463⟩]
theorem checked58490 : checkPrefixCuts (2^48) 7670333441 10 Manual.Count131072.C058490.packed 64 cuts58490 = true := by
 decide +kernel
def pointBounds58490 : List (Nat × Nat × Nat) := [(7670394880,113602008850771,113602397078342)]
theorem point_links_checked58490 : (cuts58490.take 1).map (fun c => (7670333441-1+2*2^10*c.k,113601910467668+c.lower,113602298695183+c.upper)) = pointBounds58490 := by
 decide +kernel
def cuts58491 : List PrefixCut := [⟨64,213678623,213678744⟩]
theorem checked58491 : checkPrefixCuts (2^48) 7670464513 10 Manual.Count131072.C058491.packed 64 cuts58491 = true := by
 decide +kernel
def cuts58492 : List PrefixCut := [⟨20,64069846,64069881⟩,
⟨64,209565126,209565243⟩]
theorem checked58492 : checkPrefixCuts (2^48) 7670595585 10 Manual.Count131072.C058492.packed 64 cuts58492 = true := by
 decide +kernel
def pointBounds58492 : List (Nat × Nat × Nat) := [(7670636544,113602401164479,113602789392271)]
theorem point_links_checked58492 : (cuts58492.take 1).map (fun c => (7670595585-1+2*2^10*c.k,113602337094633+c.lower,113602725322390+c.upper)) = pointBounds58492 := by
 decide +kernel
def cuts58493 : List PrefixCut := [⟨64,212203533,212203654⟩]
theorem checked58493 : checkPrefixCuts (2^48) 7670726657 10 Manual.Count131072.C058493.packed 64 cuts58493 = true := by
 decide +kernel
def cuts58494 : List PrefixCut := [⟨10,32877831,32877850⟩,
⟨64,212126532,212126656⟩]
theorem checked58494 : checkPrefixCuts (2^48) 7670857729 10 Manual.Count131072.C058494.packed 64 cuts58494 = true := by
 decide +kernel
def pointBounds58494 : List (Nat × Nat × Nat) := [(7670878208,113602791741123,113603179969137)]
theorem point_links_checked58494 : (cuts58494.take 1).map (fun c => (7670857729-1+2*2^10*c.k,113602758863292+c.lower,113603147091287+c.upper)) = pointBounds58494 := by
 decide +kernel
def cuts58495 : List PrefixCut := [⟨64,212196308,212196430⟩]
theorem checked58495 : checkPrefixCuts (2^48) 7670988801 10 Manual.Count131072.C058495.packed 64 cuts58495 = true := by
 decide +kernel
def pointBounds58495 : List (Nat × Nat × Nat) := [(7671119872,113603183186132,113603571414373)]
theorem point_links_checked58495 : (cuts58495.take 1).map (fun c => (7670988801-1+2*2^10*c.k,113602970989824+c.lower,113603359217943+c.upper)) = pointBounds58495 := by
 decide +kernel
def cuts58496 : List PrefixCut := [⟨64,207422637,207422758⟩]
theorem checked58496 : checkPrefixCuts (2^48) 7671119873 10 Manual.Count131072.C058496.packed 64 cuts58496 = true := by
 decide +kernel
def cuts58497 : List PrefixCut := [⟨54,181147979,181148081⟩,
⟨64,215087708,215087829⟩]
theorem checked58497 : checkPrefixCuts (2^48) 7671250945 10 Manual.Count131072.C058497.packed 64 cuts58497 = true := by
 decide +kernel
def pointBounds58497 : List (Nat × Nat × Nat) := [(7671361536,113603571756748,113603959985212)]
theorem point_links_checked58497 : (cuts58497.take 1).map (fun c => (7671250945-1+2*2^10*c.k,113603390608769+c.lower,113603778837131+c.upper)) = pointBounds58497 := by
 decide +kernel
def cuts58498 : List PrefixCut := [⟨64,211084683,211084803⟩]
theorem checked58498 : checkPrefixCuts (2^48) 7671382017 10 Manual.Count131072.C058498.packed 64 cuts58498 = true := by
 decide +kernel
def cuts58499 : List PrefixCut := [⟨44,148340532,148340617⟩,
⟨64,213722813,213722937⟩]
theorem checked58499 : checkPrefixCuts (2^48) 7671513089 10 Manual.Count131072.C058499.packed 64 cuts58499 = true := by
 decide +kernel
def pointBounds58499 : List (Nat × Nat × Nat) := [(7671603200,113603965121692,113604353350380)]
theorem point_links_checked58499 : (cuts58499.take 1).map (fun c => (7671513089-1+2*2^10*c.k,113603816781160+c.lower,113604205009763+c.upper)) = pointBounds58499 := by
 decide +kernel
def cuts58500 : List PrefixCut := [⟨64,210563815,210563936⟩]
theorem checked58500 : checkPrefixCuts (2^48) 7671644161 10 Manual.Count131072.C058500.packed 64 cuts58500 = true := by
 decide +kernel
def cuts58501 : List PrefixCut := [⟨34,113223807,113223872⟩,
⟨64,212541444,212541568⟩]
theorem checked58501 : checkPrefixCuts (2^48) 7671775233 10 Manual.Count131072.C058501.packed 64 cuts58501 = true := by
 decide +kernel
def pointBounds58501 : List (Nat × Nat × Nat) := [(7671844864,113604354291595,113604742520508)]
theorem point_links_checked58501 : (cuts58501.take 1).map (fun c => (7671775233-1+2*2^10*c.k,113604241067788+c.lower,113604629296636+c.upper)) = pointBounds58501 := by
 decide +kernel
def cuts58502 : List PrefixCut := [⟨64,215619653,215619773⟩]
theorem checked58502 : checkPrefixCuts (2^48) 7671906305 10 Manual.Count131072.C058502.packed 64 cuts58502 = true := by
 decide +kernel
def cuts58503 : List PrefixCut := [⟨24,78439584,78439628⟩,
⟨64,210222835,210222955⟩]
theorem checked58503 : checkPrefixCuts (2^48) 7672037377 10 Manual.Count131072.C058503.packed 64 cuts58503 = true := by
 decide +kernel
def pointBounds58503 : List (Nat × Nat × Nat) := [(7672086528,113604747668469,113605135897605)]
theorem point_links_checked58503 : (cuts58503.take 1).map (fun c => (7672037377-1+2*2^10*c.k,113604669228885+c.lower,113605057457977+c.upper)) = pointBounds58503 := by
 decide +kernel
def cuts58504 : List PrefixCut := [⟨64,211796794,211796917⟩]
theorem checked58504 : checkPrefixCuts (2^48) 7672168449 10 Manual.Count131072.C058504.packed 64 cuts58504 = true := by
 decide +kernel
def cuts58505 : List PrefixCut := [⟨14,46555923,46555949⟩,
⟨64,208821551,208821668⟩]
theorem checked58505 : checkPrefixCuts (2^48) 7672299521 10 Manual.Count131072.C058505.packed 64 cuts58505 = true := by
 decide +kernel
def pointBounds58505 : List (Nat × Nat × Nat) := [(7672328192,113605137804437,113605526033798)]
theorem point_links_checked58505 : (cuts58505.take 1).map (fun c => (7672299521-1+2*2^10*c.k,113605091248514+c.lower,113605479477849+c.upper)) = pointBounds58505 := by
 decide +kernel
def cuts58506 : List PrefixCut := [⟨64,212376528,212376651⟩]
theorem checked58506 : checkPrefixCuts (2^48) 7672430593 10 Manual.Count131072.C058506.packed 64 cuts58506 = true := by
 decide +kernel
def cuts58507 : List PrefixCut := [⟨4,13353664,13353672⟩,
⟨64,211455792,211455911⟩]
theorem checked58507 : checkPrefixCuts (2^48) 7672561665 10 Manual.Count131072.C058507.packed 64 cuts58507 = true := by
 decide +kernel
def pointBounds58507 : List (Nat × Nat × Nat) := [(7672569856,113605525800257,113605914029840)]
theorem point_links_checked58507 : (cuts58507.take 1).map (fun c => (7672561665-1+2*2^10*c.k,113605512446593+c.lower,113605900676168+c.upper)) = pointBounds58507 := by
 decide +kernel
def cuts58508 : List PrefixCut := [⟨58,189918236,189918349⟩,
⟨64,209727965,209728090⟩]
theorem checked58508 : checkPrefixCuts (2^48) 7672692737 10 Manual.Count131072.C058508.packed 64 cuts58508 = true := by
 decide +kernel
def pointBounds58508 : List (Nat × Nat × Nat) := [(7672811520,113605913820621,113606302050428)]
theorem point_links_checked58508 : (cuts58508.take 1).map (fun c => (7672692737-1+2*2^10*c.k,113605723902385+c.lower,113606112132079+c.upper)) = pointBounds58508 := by
 decide +kernel
def cuts58509 : List PrefixCut := [⟨64,212108854,212108974⟩]
theorem checked58509 : checkPrefixCuts (2^48) 7672823809 10 Manual.Count131072.C058509.packed 64 cuts58509 = true := by
 decide +kernel
def cuts58510 : List PrefixCut := [⟨48,158217203,158217290⟩,
⟨64,210821315,210821432⟩]
theorem checked58510 : checkPrefixCuts (2^48) 7672954881 10 Manual.Count131072.C058510.packed 64 cuts58510 = true := by
 decide +kernel
def pointBounds58510 : List (Nat × Nat × Nat) := [(7673053184,113606303956407,113606692186433)]
theorem point_links_checked58510 : (cuts58510.take 1).map (fun c => (7672954881-1+2*2^10*c.k,113606145739204+c.lower,113606533969143+c.upper)) = pointBounds58510 := by
 decide +kernel
def cuts58511 : List PrefixCut := [⟨64,208946875,208946993⟩]
theorem checked58511 : checkPrefixCuts (2^48) 7673085953 10 Manual.Count131072.C058511.packed 64 cuts58511 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000265
