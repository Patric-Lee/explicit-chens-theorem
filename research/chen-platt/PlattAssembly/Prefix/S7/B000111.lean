import PlattAssemblyKernel
import PlattCertificates.Count131072.C063552
import PlattCertificates.Count131072.C063553
import PlattCertificates.Count131072.C063554
import PlattCertificates.Count131072.C063555
import PlattCertificates.Count131072.C063556
import PlattCertificates.Count131072.C063557
import PlattCertificates.Count131072.C063558
import PlattCertificates.Count131072.C063559
import PlattCertificates.Count131072.C063560
import PlattCertificates.Count131072.C063561
import PlattCertificates.Count131072.C063562
import PlattCertificates.Count131072.C063563
import PlattCertificates.Count131072.C063564
import PlattCertificates.Count131072.C063565
import PlattCertificates.Count131072.C063566
import PlattCertificates.Count131072.C063567
import PlattCertificates.Count131072.C063568
import PlattCertificates.Count131072.C063569
import PlattCertificates.Count131072.C063570
import PlattCertificates.Count131072.C063571
import PlattCertificates.Count131072.C063572
import PlattCertificates.Count131072.C063573
import PlattCertificates.Count131072.C063574
import PlattCertificates.Count131072.C063575
import PlattCertificates.Count131072.C063576
import PlattCertificates.Count131072.C063577
import PlattCertificates.Count131072.C063578
import PlattCertificates.Count131072.C063579
import PlattCertificates.Count131072.C063580
import PlattCertificates.Count131072.C063581
import PlattCertificates.Count131072.C063582
import PlattCertificates.Count131072.C063583
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000111
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63552 : List PrefixCut := [⟨48,144623758,144623843⟩,
⟨64,193968377,193968489⟩]
theorem checked63552 : checkPrefixCuts (2^48) 8333819905 10 Manual.Count131072.C063552.packed 64 cuts63552 = true := by
 decide +kernel
def pointBounds63552 : List (Nat × Nat × Nat) := [(8333918208,114626215098907,114626603912983)]
theorem point_links_checked63552 : (cuts63552.take 1).map (fun c => (8333819905-1+2*2^10*c.k,114626070475149+c.lower,114626459289140+c.upper)) = pointBounds63552 := by
 decide +kernel
def cuts63553 : List PrefixCut := [⟨64,194539479,194539590⟩]
theorem checked63553 : checkPrefixCuts (2^48) 8333950977 10 Manual.Count131072.C063553.packed 64 cuts63553 = true := by
 decide +kernel
def cuts63554 : List PrefixCut := [⟨48,145463554,145463637⟩,
⟨64,195245676,195245785⟩]
theorem checked63554 : checkPrefixCuts (2^48) 8334082049 10 Manual.Count131072.C063554.packed 64 cuts63554 = true := by
 decide +kernel
def pointBounds63554 : List (Nat × Nat × Nat) := [(8334180352,114626604446559,114626993260856)]
theorem point_links_checked63554 : (cuts63554.take 1).map (fun c => (8334082049-1+2*2^10*c.k,114626458983005+c.lower,114626847797219+c.upper)) = pointBounds63554 := by
 decide +kernel
def cuts63555 : List PrefixCut := [⟨64,195276393,195276504⟩]
theorem checked63555 : checkPrefixCuts (2^48) 8334213121 10 Manual.Count131072.C063555.packed 64 cuts63555 = true := by
 decide +kernel
def cuts63556 : List PrefixCut := [⟨48,144445804,144445889⟩,
⟨64,193179417,193179528⟩]
theorem checked63556 : checkPrefixCuts (2^48) 8334344193 10 Manual.Count131072.C063556.packed 64 cuts63556 = true := by
 decide +kernel
def pointBounds63556 : List (Nat × Nat × Nat) := [(8334442496,114626993950878,114627382765397)]
theorem point_links_checked63556 : (cuts63556.take 1).map (fun c => (8334344193-1+2*2^10*c.k,114626849505074+c.lower,114627238319508+c.upper)) = pointBounds63556 := by
 decide +kernel
def cuts63557 : List PrefixCut := [⟨64,194594813,194594920⟩]
theorem checked63557 : checkPrefixCuts (2^48) 8334475265 10 Manual.Count131072.C063557.packed 64 cuts63557 = true := by
 decide +kernel
def cuts63558 : List PrefixCut := [⟨48,146129843,146129928⟩,
⟨64,197158374,197158489⟩]
theorem checked63558 : checkPrefixCuts (2^48) 8334606337 10 Manual.Count131072.C063558.packed 64 cuts63558 = true := by
 decide +kernel
def pointBounds63558 : List (Nat × Nat × Nat) := [(8334704640,114627383409147,114627772223884)]
theorem point_links_checked63558 : (cuts63558.take 1).map (fun c => (8334606337-1+2*2^10*c.k,114627237279304+c.lower,114627626093956+c.upper)) = pointBounds63558 := by
 decide +kernel
def cuts63559 : List PrefixCut := [⟨64,193744390,193744509⟩]
theorem checked63559 : checkPrefixCuts (2^48) 8334737409 10 Manual.Count131072.C063559.packed 64 cuts63559 = true := by
 decide +kernel
def cuts63560 : List PrefixCut := [⟨48,144335404,144335487⟩,
⟨64,194923316,194923427⟩]
theorem checked63560 : checkPrefixCuts (2^48) 8334868481 10 Manual.Count131072.C063560.packed 64 cuts63560 = true := by
 decide +kernel
def pointBounds63560 : List (Nat × Nat × Nat) := [(8334966784,114627772517472,114628161332441)]
theorem point_links_checked63560 : (cuts63560.take 1).map (fun c => (8334868481-1+2*2^10*c.k,114627628182068+c.lower,114628016996954+c.upper)) = pointBounds63560 := by
 decide +kernel
def cuts63561 : List PrefixCut := [⟨64,192522571,192522683⟩]
theorem checked63561 : checkPrefixCuts (2^48) 8334999553 10 Manual.Count131072.C063561.packed 64 cuts63561 = true := by
 decide +kernel
def cuts63562 : List PrefixCut := [⟨48,143621701,143621782⟩,
⟨64,190696022,190696129⟩]
theorem checked63562 : checkPrefixCuts (2^48) 8335130625 10 Manual.Count131072.C063562.packed 64 cuts63562 = true := by
 decide +kernel
def pointBounds63562 : List (Nat × Nat × Nat) := [(8335228928,114628159249656,114628548064846)]
theorem point_links_checked63562 : (cuts63562.take 1).map (fun c => (8335130625-1+2*2^10*c.k,114628015627955+c.lower,114628404443064+c.upper)) = pointBounds63562 := by
 decide +kernel
def cuts63563 : List PrefixCut := [⟨64,194981672,194981783⟩]
theorem checked63563 : checkPrefixCuts (2^48) 8335261697 10 Manual.Count131072.C063563.packed 64 cuts63563 = true := by
 decide +kernel
def cuts63564 : List PrefixCut := [⟨48,143380813,143380896⟩,
⟨64,193560326,193560437⟩]
theorem checked63564 : checkPrefixCuts (2^48) 8335392769 10 Manual.Count131072.C063564.packed 64 cuts63564 = true := by
 decide +kernel
def pointBounds63564 : List (Nat × Nat × Nat) := [(8335491072,114628544686462,114628933501872)]
theorem point_links_checked63564 : (cuts63564.take 1).map (fun c => (8335392769-1+2*2^10*c.k,114628401305649+c.lower,114628790120976+c.upper)) = pointBounds63564 := by
 decide +kernel
def cuts63565 : List PrefixCut := [⟨64,195684668,195684778⟩]
theorem checked63565 : checkPrefixCuts (2^48) 8335523841 10 Manual.Count131072.C063565.packed 64 cuts63565 = true := by
 decide +kernel
def cuts63566 : List PrefixCut := [⟨48,145841315,145841402⟩,
⟨64,195006236,195006351⟩]
theorem checked63566 : checkPrefixCuts (2^48) 8335654913 10 Manual.Count131072.C063566.packed 64 cuts63566 = true := by
 decide +kernel
def pointBounds63566 : List (Nat × Nat × Nat) := [(8335753216,114628936391958,114629325207593)]
theorem point_links_checked63566 : (cuts63566.take 1).map (fun c => (8335654913-1+2*2^10*c.k,114628790550643+c.lower,114629179366191+c.upper)) = pointBounds63566 := by
 decide +kernel
def cuts63567 : List PrefixCut := [⟨64,191761572,191761685⟩]
theorem checked63567 : checkPrefixCuts (2^48) 8335785985 10 Manual.Count131072.C063567.packed 64 cuts63567 = true := by
 decide +kernel
def cuts63568 : List PrefixCut := [⟨48,144553615,144553700⟩,
⟨64,193818286,193818400⟩]
theorem checked63568 : checkPrefixCuts (2^48) 8335917057 10 Manual.Count131072.C063568.packed 64 cuts63568 = true := by
 decide +kernel
def pointBounds63568 : List (Nat × Nat × Nat) := [(8336015360,114629321872066,114629710687927)]
theorem point_links_checked63568 : (cuts63568.take 1).map (fun c => (8335917057-1+2*2^10*c.k,114629177318451+c.lower,114629566134227+c.upper)) = pointBounds63568 := by
 decide +kernel
def cuts63569 : List PrefixCut := [⟨64,194794448,194794557⟩]
theorem checked63569 : checkPrefixCuts (2^48) 8336048129 10 Manual.Count131072.C063569.packed 64 cuts63569 = true := by
 decide +kernel
def cuts63570 : List PrefixCut := [⟨48,145730843,145730929⟩,
⟨64,194622551,194622666⟩]
theorem checked63570 : checkPrefixCuts (2^48) 8336179201 10 Manual.Count131072.C063570.packed 64 cuts63570 = true := by
 decide +kernel
def pointBounds63570 : List (Nat × Nat × Nat) := [(8336277504,114629711662028,114630100478113)]
theorem point_links_checked63570 : (cuts63570.take 1).map (fun c => (8336179201-1+2*2^10*c.k,114629565931185+c.lower,114629954747184+c.upper)) = pointBounds63570 := by
 decide +kernel
def cuts63571 : List PrefixCut := [⟨64,192559857,192559973⟩]
theorem checked63571 : checkPrefixCuts (2^48) 8336310273 10 Manual.Count131072.C063571.packed 64 cuts63571 = true := by
 decide +kernel
def cuts63572 : List PrefixCut := [⟨48,147549541,147549624⟩,
⟨64,195933254,195933366⟩]
theorem checked63572 : checkPrefixCuts (2^48) 8336441345 10 Manual.Count131072.C063572.packed 64 cuts63572 = true := by
 decide +kernel
def pointBounds63572 : List (Nat × Nat × Nat) := [(8336539648,114630100663134,114630489479447)]
theorem point_links_checked63572 : (cuts63572.take 1).map (fun c => (8336441345-1+2*2^10*c.k,114629953113593+c.lower,114630341929823+c.upper)) = pointBounds63572 := by
 decide +kernel
def cuts63573 : List PrefixCut := [⟨64,193499186,193499305⟩]
theorem checked63573 : checkPrefixCuts (2^48) 8336572417 10 Manual.Count131072.C063573.packed 64 cuts63573 = true := by
 decide +kernel
def cuts63574 : List PrefixCut := [⟨48,146059322,146059409⟩,
⟨64,195083008,195083125⟩]
theorem checked63574 : checkPrefixCuts (2^48) 8336703489 10 Manual.Count131072.C063574.packed 64 cuts63574 = true := by
 decide +kernel
def pointBounds63574 : List (Nat × Nat × Nat) := [(8336801792,114630488605355,114630877421903)]
theorem point_links_checked63574 : (cuts63574.take 1).map (fun c => (8336703489-1+2*2^10*c.k,114630342546033+c.lower,114630731362494+c.upper)) = pointBounds63574 := by
 decide +kernel
def cuts63575 : List PrefixCut := [⟨64,193999527,193999635⟩]
theorem checked63575 : checkPrefixCuts (2^48) 8336834561 10 Manual.Count131072.C063575.packed 64 cuts63575 = true := by
 decide +kernel
def cuts63576 : List PrefixCut := [⟨48,147168867,147168952⟩,
⟨64,194435399,194435513⟩]
theorem checked63576 : checkPrefixCuts (2^48) 8336965633 10 Manual.Count131072.C063576.packed 64 cuts63576 = true := by
 decide +kernel
def pointBounds63576 : List (Nat × Nat × Nat) := [(8337063936,114630878797435,114631267614206)]
theorem point_links_checked63576 : (cuts63576.take 1).map (fun c => (8336965633-1+2*2^10*c.k,114630731628568+c.lower,114631120445254+c.upper)) = pointBounds63576 := by
 decide +kernel
def cuts63577 : List PrefixCut := [⟨64,192237849,192237961⟩]
theorem checked63577 : checkPrefixCuts (2^48) 8337096705 10 Manual.Count131072.C063577.packed 64 cuts63577 = true := by
 decide +kernel
def cuts63578 : List PrefixCut := [⟨48,142944119,142944208⟩,
⟨64,190445491,190445608⟩]
theorem checked63578 : checkPrefixCuts (2^48) 8337227777 10 Manual.Count131072.C063578.packed 64 cuts63578 = true := by
 decide +kernel
def pointBounds63578 : List (Nat × Nat × Nat) := [(8337326080,114631261245935,114631650062936)]
theorem point_links_checked63578 : (cuts63578.take 1).map (fun c => (8337227777-1+2*2^10*c.k,114631118301816+c.lower,114631507118728+c.upper)) = pointBounds63578 := by
 decide +kernel
def cuts63579 : List PrefixCut := [⟨64,195472795,195472908⟩]
theorem checked63579 : checkPrefixCuts (2^48) 8337358849 10 Manual.Count131072.C063579.packed 64 cuts63579 = true := by
 decide +kernel
def cuts63580 : List PrefixCut := [⟨48,146923296,146923384⟩,
⟨64,194558211,194558324⟩]
theorem checked63580 : checkPrefixCuts (2^48) 8337489921 10 Manual.Count131072.C063580.packed 64 cuts63580 = true := by
 decide +kernel
def pointBounds63580 : List (Nat × Nat × Nat) := [(8337588224,114631651143398,114632039960628)]
theorem point_links_checked63580 : (cuts63580.take 1).map (fun c => (8337489921-1+2*2^10*c.k,114631504220102+c.lower,114631893037244+c.upper)) = pointBounds63580 := by
 decide +kernel
def cuts63581 : List PrefixCut := [⟨64,195162825,195162940⟩]
theorem checked63581 : checkPrefixCuts (2^48) 8337620993 10 Manual.Count131072.C063581.packed 64 cuts63581 = true := by
 decide +kernel
def cuts63582 : List PrefixCut := [⟨48,144285488,144285573⟩,
⟨64,193505559,193505673⟩]
theorem checked63582 : checkPrefixCuts (2^48) 8337752065 10 Manual.Count131072.C063582.packed 64 cuts63582 = true := by
 decide +kernel
def pointBounds63582 : List (Nat × Nat × Nat) := [(8337850368,114632038226626,114632427044081)]
theorem point_links_checked63582 : (cuts63582.take 1).map (fun c => (8337752065-1+2*2^10*c.k,114631893941138+c.lower,114632282758508+c.upper)) = pointBounds63582 := by
 decide +kernel
def cuts63583 : List PrefixCut := [⟨64,193299972,193300077⟩]
theorem checked63583 : checkPrefixCuts (2^48) 8337883137 10 Manual.Count131072.C063583.packed 64 cuts63583 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000111
