import PlattAssemblyKernel
import PlattCertificates.Count131072.C056432
import PlattCertificates.Count131072.C056433
import PlattCertificates.Count131072.C056434
import PlattCertificates.Count131072.C056435
import PlattCertificates.Count131072.C056436
import PlattCertificates.Count131072.C056437
import PlattCertificates.Count131072.C056438
import PlattCertificates.Count131072.C056439
import PlattCertificates.Count131072.C056440
import PlattCertificates.Count131072.C056441
import PlattCertificates.Count131072.C056442
import PlattCertificates.Count131072.C056443
import PlattCertificates.Count131072.C056444
import PlattCertificates.Count131072.C056445
import PlattCertificates.Count131072.C056446
import PlattCertificates.Count131072.C056447
import PlattCertificates.Count131072.C056448
import PlattCertificates.Count131072.C056449
import PlattCertificates.Count131072.C056450
import PlattCertificates.Count131072.C056451
import PlattCertificates.Count131072.C056452
import PlattCertificates.Count131072.C056453
import PlattCertificates.Count131072.C056454
import PlattCertificates.Count131072.C056455
import PlattCertificates.Count131072.C056456
import PlattCertificates.Count131072.C056457
import PlattCertificates.Count131072.C056458
import PlattCertificates.Count131072.C056459
import PlattCertificates.Count131072.C056460
import PlattCertificates.Count131072.C056461
import PlattCertificates.Count131072.C056462
import PlattCertificates.Count131072.C056463
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000201
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56432 : List PrefixCut := [⟨64,219150705,219150830⟩]
theorem checked56432 : checkPrefixCuts (2^48) 7400587265 10 Manual.Count131072.C056432.packed 64 cuts56432 = true := by
 decide +kernel
def cuts56433 : List PrefixCut := [⟨47,162972311,162972401⟩,
⟨64,221352766,221352890⟩]
theorem checked56433 : checkPrefixCuts (2^48) 7400718337 10 Manual.Count131072.C056433.packed 64 cuts56433 = true := by
 decide +kernel
def pointBounds56433 : List (Nat × Nat × Nat) := [(7400814592,113159252253590,113159640229222)]
theorem point_links_checked56433 : (cuts56433.take 1).map (fun c => (7400718337-1+2*2^10*c.k,113159089281279+c.lower,113159477256821+c.upper)) = pointBounds56433 := by
 decide +kernel
def cuts56434 : List PrefixCut := [⟨64,219447234,219447360⟩]
theorem checked56434 : checkPrefixCuts (2^48) 7400849409 10 Manual.Count131072.C056434.packed 64 cuts56434 = true := by
 decide +kernel
def cuts56435 : List PrefixCut := [⟨32,109493956,109494017⟩,
⟨64,217275517,217275643⟩]
theorem checked56435 : checkPrefixCuts (2^48) 7400980481 10 Manual.Count131072.C056435.packed 64 cuts56435 = true := by
 decide +kernel
def pointBounds56435 : List (Nat × Nat × Nat) := [(7401046016,113159639575235,113160027551088)]
theorem point_links_checked56435 : (cuts56435.take 1).map (fun c => (7400980481-1+2*2^10*c.k,113159530081279+c.lower,113159918057071+c.upper)) = pointBounds56435 := by
 decide +kernel
def cuts56436 : List PrefixCut := [⟨64,222900262,222900385⟩]
theorem checked56436 : checkPrefixCuts (2^48) 7401111553 10 Manual.Count131072.C056436.packed 64 cuts56436 = true := by
 decide +kernel
def cuts56437 : List PrefixCut := [⟨17,57502376,57502408⟩,
⟨64,219131309,219131430⟩]
theorem checked56437 : checkPrefixCuts (2^48) 7401242625 10 Manual.Count131072.C056437.packed 64 cuts56437 = true := by
 decide +kernel
def pointBounds56437 : List (Nat × Nat × Nat) := [(7401277440,113160027759434,113160415735507)]
theorem point_links_checked56437 : (cuts56437.take 1).map (fun c => (7401242625-1+2*2^10*c.k,113159970257058+c.lower,113160358233099+c.upper)) = pointBounds56437 := by
 decide +kernel
def cuts56438 : List PrefixCut := [⟨64,216541405,216541527⟩]
theorem checked56438 : checkPrefixCuts (2^48) 7401373697 10 Manual.Count131072.C056438.packed 64 cuts56438 = true := by
 decide +kernel
def cuts56439 : List PrefixCut := [⟨2,7529822,7529826⟩,
⟨64,222127855,222127982⟩]
theorem checked56439 : checkPrefixCuts (2^48) 7401504769 10 Manual.Count131072.C056439.packed 64 cuts56439 = true := by
 decide +kernel
def pointBounds56439 : List (Nat × Nat × Nat) := [(7401508864,113160413459594,113160801435882)]
theorem point_links_checked56439 : (cuts56439.take 1).map (fun c => (7401504769-1+2*2^10*c.k,113160405929772+c.lower,113160793906056+c.upper)) = pointBounds56439 := by
 decide +kernel
def cuts56440 : List PrefixCut := [⟨51,177631011,177631109⟩,
⟨64,222960548,222960672⟩]
theorem checked56440 : checkPrefixCuts (2^48) 7401635841 10 Manual.Count131072.C056440.packed 64 cuts56440 = true := by
 decide +kernel
def pointBounds56440 : List (Nat × Nat × Nat) := [(7401740288,113160805688638,113161193665147)]
theorem point_links_checked56440 : (cuts56440.take 1).map (fun c => (7401635841-1+2*2^10*c.k,113160628057627+c.lower,113161016034038+c.upper)) = pointBounds56440 := by
 decide +kernel
def cuts56441 : List PrefixCut := [⟨64,215769337,215769460⟩]
theorem checked56441 : checkPrefixCuts (2^48) 7401766913 10 Manual.Count131072.C056441.packed 64 cuts56441 = true := by
 decide +kernel
def cuts56442 : List PrefixCut := [⟨36,122485631,122485700⟩,
⟨64,217818987,217819112⟩]
theorem checked56442 : checkPrefixCuts (2^48) 7401897985 10 Manual.Count131072.C056442.packed 64 cuts56442 = true := by
 decide +kernel
def pointBounds56442 : List (Nat × Nat × Nat) := [(7401971712,113161189273143,113161577249870)]
theorem point_links_checked56442 : (cuts56442.take 1).map (fun c => (7401897985-1+2*2^10*c.k,113161066787512+c.lower,113161454764170+c.upper)) = pointBounds56442 := by
 decide +kernel
def cuts56443 : List PrefixCut := [⟨64,219982642,219982765⟩]
theorem checked56443 : checkPrefixCuts (2^48) 7402029057 10 Manual.Count131072.C056443.packed 64 cuts56443 = true := by
 decide +kernel
def cuts56444 : List PrefixCut := [⟨21,71983098,71983140⟩,
⟨64,218495720,218495843⟩]
theorem checked56444 : checkPrefixCuts (2^48) 7402160129 10 Manual.Count131072.C056444.packed 64 cuts56444 = true := by
 decide +kernel
def pointBounds56444 : List (Nat × Nat × Nat) := [(7402203136,113161576572239,113161964549187)]
theorem point_links_checked56444 : (cuts56444.take 1).map (fun c => (7402160129-1+2*2^10*c.k,113161504589141+c.lower,113161892566047+c.upper)) = pointBounds56444 := by
 decide +kernel
def cuts56445 : List PrefixCut := [⟨64,221876110,221876231⟩]
theorem checked56445 : checkPrefixCuts (2^48) 7402291201 10 Manual.Count131072.C056445.packed 64 cuts56445 = true := by
 decide +kernel
def cuts56446 : List PrefixCut := [⟨6,20685421,20685433⟩,
⟨64,222252409,222252534⟩]
theorem checked56446 : checkPrefixCuts (2^48) 7402422273 10 Manual.Count131072.C056446.packed 64 cuts56446 = true := by
 decide +kernel
def pointBounds56446 : List (Nat × Nat × Nat) := [(7402434560,113161965646392,113162353623554)]
theorem point_links_checked56446 : (cuts56446.take 1).map (fun c => (7402422273-1+2*2^10*c.k,113161944960971+c.lower,113162332938121+c.upper)) = pointBounds56446 := by
 decide +kernel
def cuts56447 : List PrefixCut := [⟨55,190194730,190194837⟩,
⟨64,222172411,222172536⟩]
theorem checked56447 : checkPrefixCuts (2^48) 7402553345 10 Manual.Count131072.C056447.packed 64 cuts56447 = true := by
 decide +kernel
def pointBounds56447 : List (Nat × Nat × Nat) := [(7402665984,113162357408110,113162745385492)]
theorem point_links_checked56447 : (cuts56447.take 1).map (fun c => (7402553345-1+2*2^10*c.k,113162167213380+c.lower,113162555190655+c.upper)) = pointBounds56447 := by
 decide +kernel
def cuts56448 : List PrefixCut := [⟨64,217871899,217872025⟩]
theorem checked56448 : checkPrefixCuts (2^48) 7402684417 10 Manual.Count131072.C056448.packed 64 cuts56448 = true := by
 decide +kernel
def cuts56449 : List PrefixCut := [⟨40,135892309,135892386⟩,
⟨64,217753961,217754086⟩]
theorem checked56449 : checkPrefixCuts (2^48) 7402815489 10 Manual.Count131072.C056449.packed 64 cuts56449 = true := by
 decide +kernel
def pointBounds56449 : List (Nat × Nat × Nat) := [(7402897408,113162743149999,113163131127602)]
theorem point_links_checked56449 : (cuts56449.take 1).map (fun c => (7402815489-1+2*2^10*c.k,113162607257690+c.lower,113162995235216+c.upper)) = pointBounds56449 := by
 decide +kernel
def cuts56450 : List PrefixCut := [⟨64,220373602,220373725⟩]
theorem checked56450 : checkPrefixCuts (2^48) 7402946561 10 Manual.Count131072.C056450.packed 64 cuts56450 = true := by
 decide +kernel
def cuts56451 : List PrefixCut := [⟨25,85395626,85395675⟩,
⟨64,218582717,218582843⟩]
theorem checked56451 : checkPrefixCuts (2^48) 7403077633 10 Manual.Count131072.C056451.packed 64 cuts56451 = true := by
 decide +kernel
def pointBounds56451 : List (Nat × Nat × Nat) := [(7403128832,113163130780879,113163518758702)]
theorem point_links_checked56451 : (cuts56451.take 1).map (fun c => (7403077633-1+2*2^10*c.k,113163045385253+c.lower,113163433363027+c.upper)) = pointBounds56451 := by
 decide +kernel
def cuts56452 : List PrefixCut := [⟨64,218768944,218769070⟩]
theorem checked56452 : checkPrefixCuts (2^48) 7403208705 10 Manual.Count131072.C056452.packed 64 cuts56452 = true := by
 decide +kernel
def cuts56453 : List PrefixCut := [⟨10,33951805,33951823⟩,
⟨64,215913597,215913719⟩]
theorem checked56453 : checkPrefixCuts (2^48) 7403339777 10 Manual.Count131072.C056453.packed 64 cuts56453 = true := by
 decide +kernel
def pointBounds56453 : List (Nat × Nat × Nat) := [(7403360256,113163516688719,113163904666763)]
theorem point_links_checked56453 : (cuts56453.take 1).map (fun c => (7403339777-1+2*2^10*c.k,113163482736914+c.lower,113163870714940+c.upper)) = pointBounds56453 := by
 decide +kernel
def cuts56454 : List PrefixCut := [⟨59,200588273,200588386⟩,
⟨64,217278468,217278591⟩]
theorem checked56454 : checkPrefixCuts (2^48) 7403470849 10 Manual.Count131072.C056454.packed 64 cuts56454 = true := by
 decide +kernel
def pointBounds56454 : List (Nat × Nat × Nat) := [(7403591680,113163899238784,113164287217045)]
theorem point_links_checked56454 : (cuts56454.take 1).map (fun c => (7403470849-1+2*2^10*c.k,113163698650511+c.lower,113164086628659+c.upper)) = pointBounds56454 := by
 decide +kernel
def cuts56455 : List PrefixCut := [⟨64,218187075,218187200⟩]
theorem checked56455 : checkPrefixCuts (2^48) 7403601921 10 Manual.Count131072.C056455.packed 64 cuts56455 = true := by
 decide +kernel
def cuts56456 : List PrefixCut := [⟨44,148269185,148269269⟩,
⟨64,216016195,216016317⟩]
theorem checked56456 : checkPrefixCuts (2^48) 7403732993 10 Manual.Count131072.C056456.packed 64 cuts56456 = true := by
 decide +kernel
def pointBounds56456 : List (Nat × Nat × Nat) := [(7403823104,113164282385239,113164670363719)]
theorem point_links_checked56456 : (cuts56456.take 1).map (fun c => (7403732993-1+2*2^10*c.k,113164134116054+c.lower,113164522094450+c.upper)) = pointBounds56456 := by
 decide +kernel
def cuts56457 : List PrefixCut := [⟨64,222171126,222171253⟩]
theorem checked56457 : checkPrefixCuts (2^48) 7403864065 10 Manual.Count131072.C056457.packed 64 cuts56457 = true := by
 decide +kernel
def cuts56458 : List PrefixCut := [⟨29,100173398,100173454⟩,
⟨64,221292803,221292928⟩]
theorem checked56458 : checkPrefixCuts (2^48) 7403995137 10 Manual.Count131072.C056458.packed 64 cuts56458 = true := by
 decide +kernel
def pointBounds56458 : List (Nat × Nat × Nat) := [(7404054528,113164672476773,113165060455474)]
theorem point_links_checked56458 : (cuts56458.take 1).map (fun c => (7403995137-1+2*2^10*c.k,113164572303375+c.lower,113164960282020+c.upper)) = pointBounds56458 := by
 decide +kernel
def cuts56459 : List PrefixCut := [⟨64,216955092,216955214⟩]
theorem checked56459 : checkPrefixCuts (2^48) 7404126209 10 Manual.Count131072.C056459.packed 64 cuts56459 = true := by
 decide +kernel
def cuts56460 : List PrefixCut := [⟨14,47519007,47519033⟩,
⟨64,219156143,219156265⟩]
theorem checked56460 : checkPrefixCuts (2^48) 7404257281 10 Manual.Count131072.C056460.packed 64 cuts56460 = true := by
 decide +kernel
def pointBounds56460 : List (Nat × Nat × Nat) := [(7404285952,113165058070277,113165446049195)]
theorem point_links_checked56460 : (cuts56460.take 1).map (fun c => (7404257281-1+2*2^10*c.k,113165010551270+c.lower,113165398530162+c.upper)) = pointBounds56460 := by
 decide +kernel
def cuts56461 : List PrefixCut := [⟨63,214248435,214248557⟩,
⟨64,217783731,217783855⟩]
theorem checked56461 : checkPrefixCuts (2^48) 7404388353 10 Manual.Count131072.C056461.packed 64 cuts56461 = true := by
 decide +kernel
def pointBounds56461 : List (Nat × Nat × Nat) := [(7404517376,113165443955848,113165831934984)]
theorem point_links_checked56461 : (cuts56461.take 1).map (fun c => (7404388353-1+2*2^10*c.k,113165229707413+c.lower,113165617686427+c.upper)) = pointBounds56461 := by
 decide +kernel
def cuts56462 : List PrefixCut := [⟨64,220250782,220250909⟩]
theorem checked56462 : checkPrefixCuts (2^48) 7404519425 10 Manual.Count131072.C056462.packed 64 cuts56462 = true := by
 decide +kernel
def cuts56463 : List PrefixCut := [⟨48,164748378,164748472⟩,
⟨64,220588993,220589119⟩]
theorem checked56463 : checkPrefixCuts (2^48) 7404650497 10 Manual.Count131072.C056463.packed 64 cuts56463 = true := by
 decide +kernel
def pointBounds56463 : List (Nat × Nat × Nat) := [(7404748800,113165832490304,113166220469663)]
theorem point_links_checked56463 : (cuts56463.take 1).map (fun c => (7404650497-1+2*2^10*c.k,113165667741926+c.lower,113166055721191+c.upper)) = pointBounds56463 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000201
