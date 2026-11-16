import PlattAssemblyKernel
import PlattCertificates.Count131072.C039504
import PlattCertificates.Count131072.C039505
import PlattCertificates.Count131072.C039506
import PlattCertificates.Count131072.C039507
import PlattCertificates.Count131072.C039508
import PlattCertificates.Count131072.C039509
import PlattCertificates.Count131072.C039510
import PlattCertificates.Count131072.C039511
import PlattCertificates.Count131072.C039512
import PlattCertificates.Count131072.C039513
import PlattCertificates.Count131072.C039514
import PlattCertificates.Count131072.C039515
import PlattCertificates.Count131072.C039516
import PlattCertificates.Count131072.C039517
import PlattCertificates.Count131072.C039518
import PlattCertificates.Count131072.C039519
import PlattCertificates.Count131072.C039520
import PlattCertificates.Count131072.C039521
import PlattCertificates.Count131072.C039522
import PlattCertificates.Count131072.C039523
import PlattCertificates.Count131072.C039524
import PlattCertificates.Count131072.C039525
import PlattCertificates.Count131072.C039526
import PlattCertificates.Count131072.C039527
import PlattCertificates.Count131072.C039528
import PlattCertificates.Count131072.C039529
import PlattCertificates.Count131072.C039530
import PlattCertificates.Count131072.C039531
import PlattCertificates.Count131072.C039532
import PlattCertificates.Count131072.C039533
import PlattCertificates.Count131072.C039534
import PlattCertificates.Count131072.C039535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000297
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39504 : List PrefixCut := [⟨64,315377363,315377556⟩]
theorem checked39504 : checkPrefixCuts (2^48) 5181800449 10 Manual.Count131072.C039504.packed 64 cuts39504 = true := by
 decide +kernel
def cuts39505 : List PrefixCut := [⟨4,19934884,19934895⟩,
⟨64,317161867,317162054⟩]
theorem checked39505 : checkPrefixCuts (2^48) 5181931521 10 Manual.Count131072.C039505.packed 64 cuts39505 = true := by
 decide +kernel
def pointBounds39505 : List (Nat × Nat × Nat) := [(5181939712,108709693977987,108710079390494)]
theorem point_links_checked39505 : (cuts39505.take 1).map (fun c => (5181931521-1+2*2^10*c.k,108709674043103+c.lower,108710059455599+c.upper)) = pointBounds39505 := by
 decide +kernel
def cuts39506 : List PrefixCut := [⟨20,98856830,98856887⟩,
⟨64,317696990,317697175⟩]
theorem checked39506 : checkPrefixCuts (2^48) 5182062593 10 Manual.Count131072.C039506.packed 64 cuts39506 = true := by
 decide +kernel
def pointBounds39506 : List (Nat × Nat × Nat) := [(5182103552,108710090061800,108710475474540)]
theorem point_links_checked39506 : (cuts39506.take 1).map (fun c => (5182062593-1+2*2^10*c.k,108709991204970+c.lower,108710376617653+c.upper)) = pointBounds39506 := by
 decide +kernel
def cuts39507 : List PrefixCut := [⟨36,178371755,178371864⟩,
⟨64,318014871,318015062⟩]
theorem checked39507 : checkPrefixCuts (2^48) 5182193665 10 Manual.Count131072.C039507.packed 64 cuts39507 = true := by
 decide +kernel
def pointBounds39507 : List (Nat × Nat × Nat) := [(5182267392,108710487273715,108710872686692)]
theorem point_links_checked39507 : (cuts39507.take 1).map (fun c => (5182193665-1+2*2^10*c.k,108710308901960+c.lower,108710694314828+c.upper)) = pointBounds39507 := by
 decide +kernel
def cuts39508 : List PrefixCut := [⟨52,258642537,258642693⟩,
⟨64,317409380,317409571⟩]
theorem checked39508 : checkPrefixCuts (2^48) 5182324737 10 Manual.Count131072.C039508.packed 64 cuts39508 = true := by
 decide +kernel
def pointBounds39508 : List (Nat × Nat × Nat) := [(5182431232,108710885559368,108711270972583)]
theorem point_links_checked39508 : (cuts39508.take 1).map (fun c => (5182324737-1+2*2^10*c.k,108710626916831+c.lower,108711012329890+c.upper)) = pointBounds39508 := by
 decide +kernel
def cuts39509 : List PrefixCut := [⟨64,316641016,316641204⟩]
theorem checked39509 : checkPrefixCuts (2^48) 5182455809 10 Manual.Count131072.C039509.packed 64 cuts39509 = true := by
 decide +kernel
def cuts39510 : List PrefixCut := [⟨4,20095298,20095309⟩,
⟨64,316252801,316252990⟩]
theorem checked39510 : checkPrefixCuts (2^48) 5182586881 10 Manual.Count131072.C039510.packed 64 cuts39510 = true := by
 decide +kernel
def pointBounds39510 : List (Nat × Nat × Nat) := [(5182595072,108711281062525,108711666475974)]
theorem point_links_checked39510 : (cuts39510.take 1).map (fun c => (5182586881-1+2*2^10*c.k,108711260967227+c.lower,108711646380665+c.upper)) = pointBounds39510 := by
 decide +kernel
def cuts39511 : List PrefixCut := [⟨20,98464165,98464223⟩,
⟨64,321567102,321567296⟩]
theorem checked39511 : checkPrefixCuts (2^48) 5182717953 10 Manual.Count131072.C039511.packed 64 cuts39511 = true := by
 decide +kernel
def pointBounds39511 : List (Nat × Nat × Nat) := [(5182758912,108711675684193,108712061097878)]
theorem point_links_checked39511 : (cuts39511.take 1).map (fun c => (5182717953-1+2*2^10*c.k,108711577220028+c.lower,108711962633655+c.upper)) = pointBounds39511 := by
 decide +kernel
def cuts39512 : List PrefixCut := [⟨36,179544009,179544117⟩,
⟨64,317648842,317649033⟩]
theorem checked39512 : checkPrefixCuts (2^48) 5182849025 10 Manual.Count131072.C039512.packed 64 cuts39512 = true := by
 decide +kernel
def pointBounds39512 : List (Nat × Nat × Nat) := [(5182922752,108712078331139,108712463745068)]
theorem point_links_checked39512 : (cuts39512.take 1).map (fun c => (5182849025-1+2*2^10*c.k,108711898787130+c.lower,108712284200951+c.upper)) = pointBounds39512 := by
 decide +kernel
def cuts39513 : List PrefixCut := [⟨52,257197827,257197982⟩,
⟨64,316663223,316663415⟩]
theorem checked39513 : checkPrefixCuts (2^48) 5182980097 10 Manual.Count131072.C039513.packed 64 cuts39513 = true := by
 decide +kernel
def pointBounds39513 : List (Nat × Nat × Nat) := [(5183086592,108712473633799,108712859047966)]
theorem point_links_checked39513 : (cuts39513.take 1).map (fun c => (5182980097-1+2*2^10*c.k,108712216435972+c.lower,108712601849984+c.upper)) = pointBounds39513 := by
 decide +kernel
def cuts39514 : List PrefixCut := [⟨64,321922902,321923095⟩]
theorem checked39514 : checkPrefixCuts (2^48) 5183111169 10 Manual.Count131072.C039514.packed 64 cuts39514 = true := by
 decide +kernel
def cuts39515 : List PrefixCut := [⟨4,21070243,21070255⟩,
⟨64,319525345,319525537⟩]
theorem checked39515 : checkPrefixCuts (2^48) 5183242241 10 Manual.Count131072.C039515.packed 64 cuts39515 = true := by
 decide +kernel
def pointBounds39515 : List (Nat × Nat × Nat) := [(5183250432,108712876092340,108713261506749)]
theorem point_links_checked39515 : (cuts39515.take 1).map (fun c => (5183242241-1+2*2^10*c.k,108712855022097+c.lower,108713240436494+c.upper)) = pointBounds39515 := by
 decide +kernel
def cuts39516 : List PrefixCut := [⟨20,98723218,98723275⟩,
⟨64,322395285,322395474⟩]
theorem checked39516 : checkPrefixCuts (2^48) 5183373313 10 Manual.Count131072.C039516.packed 64 cuts39516 = true := by
 decide +kernel
def pointBounds39516 : List (Nat × Nat × Nat) := [(5183414272,108713273270660,108713658685306)]
theorem point_links_checked39516 : (cuts39516.take 1).map (fun c => (5183373313-1+2*2^10*c.k,108713174547442+c.lower,108713559962031+c.upper)) = pointBounds39516 := by
 decide +kernel
def cuts39517 : List PrefixCut := [⟨36,180878835,180878940⟩,
⟨64,320812435,320812622⟩]
theorem checked39517 : checkPrefixCuts (2^48) 5183504385 10 Manual.Count131072.C039517.packed 64 cuts39517 = true := by
 decide +kernel
def pointBounds39517 : List (Nat × Nat × Nat) := [(5183578112,108713677821562,108714063236445)]
theorem point_links_checked39517 : (cuts39517.take 1).map (fun c => (5183504385-1+2*2^10*c.k,108713496942727+c.lower,108713882357505+c.upper)) = pointBounds39517 := by
 decide +kernel
def cuts39518 : List PrefixCut := [⟨52,256948145,256948305⟩,
⟨64,317817801,317817996⟩]
theorem checked39518 : checkPrefixCuts (2^48) 5183635457 10 Manual.Count131072.C039518.packed 64 cuts39518 = true := by
 decide +kernel
def pointBounds39518 : List (Nat × Nat × Nat) := [(5183741952,108714074703307,108714460118432)]
theorem point_links_checked39518 : (cuts39518.take 1).map (fun c => (5183635457-1+2*2^10*c.k,108713817755162+c.lower,108714203170127+c.upper)) = pointBounds39518 := by
 decide +kernel
def cuts39519 : List PrefixCut := [⟨64,320198925,320199116⟩]
theorem checked39519 : checkPrefixCuts (2^48) 5183766529 10 Manual.Count131072.C039519.packed 64 cuts39519 = true := by
 decide +kernel
def cuts39520 : List PrefixCut := [⟨4,20850387,20850401⟩,
⟨64,316715822,316716017⟩]
theorem checked39520 : checkPrefixCuts (2^48) 5183897601 10 Manual.Count131072.C039520.packed 64 cuts39520 = true := by
 decide +kernel
def pointBounds39520 : List (Nat × Nat × Nat) := [(5183905792,108714476622275,108714862037640)]
theorem point_links_checked39520 : (cuts39520.take 1).map (fun c => (5183897601-1+2*2^10*c.k,108714455771888+c.lower,108714841187239+c.upper)) = pointBounds39520 := by
 decide +kernel
def cuts39521 : List PrefixCut := [⟨20,98439268,98439327⟩,
⟨64,319694062,319694253⟩]
theorem checked39521 : checkPrefixCuts (2^48) 5184028673 10 Manual.Count131072.C039521.packed 64 cuts39521 = true := by
 decide +kernel
def pointBounds39521 : List (Nat × Nat × Nat) := [(5184069632,108714870926978,108715256342583)]
theorem point_links_checked39521 : (cuts39521.take 1).map (fun c => (5184028673-1+2*2^10*c.k,108714772487710+c.lower,108715157903256+c.upper)) = pointBounds39521 := by
 decide +kernel
def cuts39522 : List PrefixCut := [⟨36,179335716,179335824⟩,
⟨64,317731402,317731589⟩]
theorem checked39522 : checkPrefixCuts (2^48) 5184159745 10 Manual.Count131072.C039522.packed 64 cuts39522 = true := by
 decide +kernel
def pointBounds39522 : List (Nat × Nat × Nat) := [(5184233472,108715271517488,108715656933333)]
theorem point_links_checked39522 : (cuts39522.take 1).map (fun c => (5184159745-1+2*2^10*c.k,108715092181772+c.lower,108715477597509+c.upper)) = pointBounds39522 := by
 decide +kernel
def cuts39523 : List PrefixCut := [⟨52,255395451,255395607⟩,
⟨64,315334443,315334634⟩]
theorem checked39523 : checkPrefixCuts (2^48) 5184290817 10 Manual.Count131072.C039523.packed 64 cuts39523 = true := by
 decide +kernel
def pointBounds39523 : List (Nat × Nat × Nat) := [(5184397312,108715665308625,108716050724705)]
theorem point_links_checked39523 : (cuts39523.take 1).map (fun c => (5184290817-1+2*2^10*c.k,108715409913174+c.lower,108715795329098+c.upper)) = pointBounds39523 := by
 decide +kernel
def cuts39524 : List PrefixCut := [⟨64,321027131,321027323⟩]
theorem checked39524 : checkPrefixCuts (2^48) 5184421889 10 Manual.Count131072.C039524.packed 64 cuts39524 = true := by
 decide +kernel
def cuts39525 : List PrefixCut := [⟨4,18947565,18947577⟩,
⟨64,317272964,317273150⟩]
theorem checked39525 : checkPrefixCuts (2^48) 5184552961 10 Manual.Count131072.C039525.packed 64 cuts39525 = true := by
 decide +kernel
def pointBounds39525 : List (Nat × Nat × Nat) := [(5184561152,108716065222313,108716450638632)]
theorem point_links_checked39525 : (cuts39525.take 1).map (fun c => (5184552961-1+2*2^10*c.k,108716046274748+c.lower,108716431691055+c.upper)) = pointBounds39525 := by
 decide +kernel
def cuts39526 : List PrefixCut := [⟨20,98101086,98101144⟩,
⟨64,315310529,315310716⟩]
theorem checked39526 : checkPrefixCuts (2^48) 5184684033 10 Manual.Count131072.C039526.packed 64 cuts39526 = true := by
 decide +kernel
def pointBounds39526 : List (Nat × Nat × Nat) := [(5184724992,108716461648798,108716847065349)]
theorem point_links_checked39526 : (cuts39526.take 1).map (fun c => (5184684033-1+2*2^10*c.k,108716363547712+c.lower,108716748964205+c.upper)) = pointBounds39526 := by
 decide +kernel
def cuts39527 : List PrefixCut := [⟨36,178607297,178607404⟩,
⟨64,318342663,318342851⟩]
theorem checked39527 : checkPrefixCuts (2^48) 5184815105 10 Manual.Count131072.C039527.packed 64 cuts39527 = true := by
 decide +kernel
def pointBounds39527 : List (Nat × Nat × Nat) := [(5184888832,108716857465538,108717242882325)]
theorem point_links_checked39527 : (cuts39527.take 1).map (fun c => (5184815105-1+2*2^10*c.k,108716678858241+c.lower,108717064274921+c.upper)) = pointBounds39527 := by
 decide +kernel
def cuts39528 : List PrefixCut := [⟨52,254440304,254440459⟩,
⟨64,312851718,312851909⟩]
theorem checked39528 : checkPrefixCuts (2^48) 5184946177 10 Manual.Count131072.C039528.packed 64 cuts39528 = true := by
 decide +kernel
def pointBounds39528 : List (Nat × Nat × Nat) := [(5185052672,108717251641208,108717637058231)]
theorem point_links_checked39528 : (cuts39528.take 1).map (fun c => (5184946177-1+2*2^10*c.k,108716997200904+c.lower,108717382617772+c.upper)) = pointBounds39528 := by
 decide +kernel
def cuts39529 : List PrefixCut := [⟨64,320660868,320661058⟩]
theorem checked39529 : checkPrefixCuts (2^48) 5185077249 10 Manual.Count131072.C039529.packed 64 cuts39529 = true := by
 decide +kernel
def cuts39530 : List PrefixCut := [⟨4,19759433,19759445⟩,
⟨64,315767243,315767432⟩]
theorem checked39530 : checkPrefixCuts (2^48) 5185208321 10 Manual.Count131072.C039530.packed 64 cuts39530 = true := by
 decide +kernel
def pointBounds39530 : List (Nat × Nat × Nat) := [(5185216512,108717650472923,108718035890184)]
theorem point_links_checked39530 : (cuts39530.take 1).map (fun c => (5185208321-1+2*2^10*c.k,108717630713490+c.lower,108718016130739+c.upper)) = pointBounds39530 := by
 decide +kernel
def cuts39531 : List PrefixCut := [⟨20,102268444,102268504⟩,
⟨64,320807475,320807666⟩]
theorem checked39531 : checkPrefixCuts (2^48) 5185339393 10 Manual.Count131072.C039531.packed 64 cuts39531 = true := by
 decide +kernel
def pointBounds39531 : List (Nat × Nat × Nat) := [(5185380352,108718048749177,108718434166675)]
theorem point_links_checked39531 : (cuts39531.take 1).map (fun c => (5185339393-1+2*2^10*c.k,108717946480733+c.lower,108718331898171+c.upper)) = pointBounds39531 := by
 decide +kernel
def cuts39532 : List PrefixCut := [⟨36,170931074,170931177⟩,
⟨64,312168629,312168815⟩]
theorem checked39532 : checkPrefixCuts (2^48) 5185470465 10 Manual.Count131072.C039532.packed 64 cuts39532 = true := by
 decide +kernel
def pointBounds39532 : List (Nat × Nat × Nat) := [(5185544192,108718438219282,108718823637014)]
theorem point_links_checked39532 : (cuts39532.take 1).map (fun c => (5185470465-1+2*2^10*c.k,108718267288208+c.lower,108718652705837+c.upper)) = pointBounds39532 := by
 decide +kernel
def cuts39533 : List PrefixCut := [⟨52,258913360,258913517⟩,
⟨64,320302731,320302924⟩]
theorem checked39533 : checkPrefixCuts (2^48) 5185601537 10 Manual.Count131072.C039533.packed 64 cuts39533 = true := by
 decide +kernel
def pointBounds39533 : List (Nat × Nat × Nat) := [(5185708032,108718838370197,108719223788169)]
theorem point_links_checked39533 : (cuts39533.take 1).map (fun c => (5185601537-1+2*2^10*c.k,108718579456837+c.lower,108718964874652+c.upper)) = pointBounds39533 := by
 decide +kernel
def cuts39534 : List PrefixCut := [⟨64,313672668,313672851⟩]
theorem checked39534 : checkPrefixCuts (2^48) 5185732609 10 Manual.Count131072.C039534.packed 64 cuts39534 = true := by
 decide +kernel
def cuts39535 : List PrefixCut := [⟨4,20299709,20299721⟩,
⟨64,315021729,315021922⟩]
theorem checked39535 : checkPrefixCuts (2^48) 5185863681 10 Manual.Count131072.C039535.packed 64 cuts39535 = true := by
 decide +kernel
def pointBounds39535 : List (Nat × Nat × Nat) := [(5185871872,108719233731945,108719619150148)]
theorem point_links_checked39535 : (cuts39535.take 1).map (fun c => (5185863681-1+2*2^10*c.k,108719213432236+c.lower,108719598850427+c.upper)) = pointBounds39535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000297
