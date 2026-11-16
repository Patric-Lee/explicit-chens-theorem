import PlattAssemblyKernel
import PlattCertificates.Count131072.C072528
import PlattCertificates.Count131072.C072529
import PlattCertificates.Count131072.C072530
import PlattCertificates.Count131072.C072531
import PlattCertificates.Count131072.C072532
import PlattCertificates.Count131072.C072533
import PlattCertificates.Count131072.C072534
import PlattCertificates.Count131072.C072535
import PlattCertificates.Count131072.C072536
import PlattCertificates.Count131072.C072537
import PlattCertificates.Count131072.C072538
import PlattCertificates.Count131072.C072539
import PlattCertificates.Count131072.C072540
import PlattCertificates.Count131072.C072541
import PlattCertificates.Count131072.C072542
import PlattCertificates.Count131072.C072543
import PlattCertificates.Count131072.C072544
import PlattCertificates.Count131072.C072545
import PlattCertificates.Count131072.C072546
import PlattCertificates.Count131072.C072547
import PlattCertificates.Count131072.C072548
import PlattCertificates.Count131072.C072549
import PlattCertificates.Count131072.C072550
import PlattCertificates.Count131072.C072551
import PlattCertificates.Count131072.C072552
import PlattCertificates.Count131072.C072553
import PlattCertificates.Count131072.C072554
import PlattCertificates.Count131072.C072555
import PlattCertificates.Count131072.C072556
import PlattCertificates.Count131072.C072557
import PlattCertificates.Count131072.C072558
import PlattCertificates.Count131072.C072559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72528 : List PrefixCut := [⟨64,169381191,169381288⟩]
theorem checked72528 : checkPrefixCuts (2^48) 9510322177 10 Manual.Count131072.C072528.packed 64 cuts72528 = true := by
 decide +kernel
def cuts72529 : List PrefixCut := [⟨64,169408469,169408561⟩]
theorem checked72529 : checkPrefixCuts (2^48) 9510453249 10 Manual.Count131072.C072529.packed 64 cuts72529 = true := by
 decide +kernel
def cuts72530 : List PrefixCut := [⟨14,35988635,35988658⟩,
⟨64,167600778,167600883⟩]
theorem checked72530 : checkPrefixCuts (2^48) 9510584321 10 Manual.Count131072.C072530.packed 64 cuts72530 = true := by
 decide +kernel
def pointBounds72530 : List (Nat × Nat × Nat) := [(9510612992,116248907707659,116249297470296)]
theorem point_links_checked72530 : (cuts72530.take 1).map (fun c => (9510584321-1+2*2^10*c.k,116248871719024+c.lower,116249261481638+c.upper)) = pointBounds72530 := by
 decide +kernel
def cuts72531 : List PrefixCut := [⟨64,171061129,171061228⟩]
theorem checked72531 : checkPrefixCuts (2^48) 9510715393 10 Manual.Count131072.C072531.packed 64 cuts72531 = true := by
 decide +kernel
def cuts72532 : List PrefixCut := [⟨32,82658959,82659010⟩,
⟨64,167596151,167596251⟩]
theorem checked72532 : checkPrefixCuts (2^48) 9510846465 10 Manual.Count131072.C072532.packed 64 cuts72532 = true := by
 decide +kernel
def pointBounds72532 : List (Nat × Nat × Nat) := [(9510912000,116249293039890,116249682802759)]
theorem point_links_checked72532 : (cuts72532.take 1).map (fun c => (9510846465-1+2*2^10*c.k,116249210380931+c.lower,116249600143749+c.upper)) = pointBounds72532 := by
 decide +kernel
def cuts72533 : List PrefixCut := [⟨64,168511283,168511373⟩]
theorem checked72533 : checkPrefixCuts (2^48) 9510977537 10 Manual.Count131072.C072533.packed 64 cuts72533 = true := by
 decide +kernel
def cuts72534 : List PrefixCut := [⟨50,134209564,134209642⟩,
⟨64,170462174,170462274⟩]
theorem checked72534 : checkPrefixCuts (2^48) 9511108609 10 Manual.Count131072.C072534.packed 64 cuts72534 = true := by
 decide +kernel
def pointBounds72534 : List (Nat × Nat × Nat) := [(9511211008,116249680697929,116250070461015)]
theorem point_links_checked72534 : (cuts72534.take 1).map (fun c => (9511108609-1+2*2^10*c.k,116249546488365+c.lower,116249936251373+c.upper)) = pointBounds72534 := by
 decide +kernel
def cuts72535 : List PrefixCut := [⟨64,166671814,166671909⟩]
theorem checked72535 : checkPrefixCuts (2^48) 9511239681 10 Manual.Count131072.C072535.packed 64 cuts72535 = true := by
 decide +kernel
def cuts72536 : List PrefixCut := [⟨64,168090006,168090104⟩]
theorem checked72536 : checkPrefixCuts (2^48) 9511370753 10 Manual.Count131072.C072536.packed 64 cuts72536 = true := by
 decide +kernel
def cuts72537 : List PrefixCut := [⟨4,10564735,10564740⟩,
⟨64,171106173,171106276⟩]
theorem checked72537 : checkPrefixCuts (2^48) 9511501825 10 Manual.Count131072.C072537.packed 64 cuts72537 = true := by
 decide +kernel
def pointBounds72537 : List (Nat × Nat × Nat) := [(9511510016,116250062277094,116250452040400)]
theorem point_links_checked72537 : (cuts72537.take 1).map (fun c => (9511501825-1+2*2^10*c.k,116250051712359+c.lower,116250441475660+c.upper)) = pointBounds72537 := by
 decide +kernel
def cuts72538 : List PrefixCut := [⟨64,171074226,171074323⟩]
theorem checked72538 : checkPrefixCuts (2^48) 9511632897 10 Manual.Count131072.C072538.packed 64 cuts72538 = true := by
 decide +kernel
def cuts72539 : List PrefixCut := [⟨22,59273218,59273250⟩,
⟨64,170450430,170450526⟩]
theorem checked72539 : checkPrefixCuts (2^48) 9511763969 10 Manual.Count131072.C072539.packed 64 cuts72539 = true := by
 decide +kernel
def pointBounds72539 : List (Nat × Nat × Nat) := [(9511809024,116250453165976,116250842929509)]
theorem point_links_checked72539 : (cuts72539.take 1).map (fun c => (9511763969-1+2*2^10*c.k,116250393892758+c.lower,116250783656259+c.upper)) = pointBounds72539 := by
 decide +kernel
def cuts72540 : List PrefixCut := [⟨64,168731762,168731859⟩]
theorem checked72540 : checkPrefixCuts (2^48) 9511895041 10 Manual.Count131072.C072540.packed 64 cuts72540 = true := by
 decide +kernel
def cuts72541 : List PrefixCut := [⟨40,105759476,105759537⟩,
⟨64,169853897,169853993⟩]
theorem checked72541 : checkPrefixCuts (2^48) 9512026113 10 Manual.Count131072.C072541.packed 64 cuts72541 = true := by
 decide +kernel
def pointBounds72541 : List (Nat × Nat × Nat) := [(9512108032,116250838834426,116251228598181)]
theorem point_links_checked72541 : (cuts72541.take 1).map (fun c => (9512026113-1+2*2^10*c.k,116250733074950+c.lower,116251122838644+c.upper)) = pointBounds72541 := by
 decide +kernel
def cuts72542 : List PrefixCut := [⟨64,166448603,166448702⟩]
theorem checked72542 : checkPrefixCuts (2^48) 9512157185 10 Manual.Count131072.C072542.packed 64 cuts72542 = true := by
 decide +kernel
def cuts72543 : List PrefixCut := [⟨58,150970599,150970690⟩,
⟨64,166002457,166002557⟩]
theorem checked72543 : checkPrefixCuts (2^48) 9512288257 10 Manual.Count131072.C072543.packed 64 cuts72543 = true := by
 decide +kernel
def pointBounds72543 : List (Nat × Nat × Nat) := [(9512407040,116251220348049,116251610112029)]
theorem point_links_checked72543 : (cuts72543.take 1).map (fun c => (9512288257-1+2*2^10*c.k,116251069377450+c.lower,116251459141339+c.upper)) = pointBounds72543 := by
 decide +kernel
def cuts72544 : List PrefixCut := [⟨64,168456144,168456248⟩]
theorem checked72544 : checkPrefixCuts (2^48) 9512419329 10 Manual.Count131072.C072544.packed 64 cuts72544 = true := by
 decide +kernel
def cuts72545 : List PrefixCut := [⟨64,168483413,168483513⟩]
theorem checked72545 : checkPrefixCuts (2^48) 9512550401 10 Manual.Count131072.C072545.packed 64 cuts72545 = true := by
 decide +kernel
def cuts72546 : List PrefixCut := [⟨12,30595438,30595457⟩,
⟨64,169043280,169043378⟩]
theorem checked72546 : checkPrefixCuts (2^48) 9512681473 10 Manual.Count131072.C072546.packed 64 cuts72546 = true := by
 decide +kernel
def pointBounds72546 : List (Nat × Nat × Nat) := [(9512706048,116251602914902,116251992679114)]
theorem point_links_checked72546 : (cuts72546.take 1).map (fun c => (9512681473-1+2*2^10*c.k,116251572319464+c.lower,116251962083657+c.upper)) = pointBounds72546 := by
 decide +kernel
def cuts72547 : List PrefixCut := [⟨64,167531939,167532036⟩]
theorem checked72547 : checkPrefixCuts (2^48) 9512812545 10 Manual.Count131072.C072547.packed 64 cuts72547 = true := by
 decide +kernel
def cuts72548 : List PrefixCut := [⟨30,78291239,78291285⟩,
⟨64,167263328,167263432⟩]
theorem checked72548 : checkPrefixCuts (2^48) 9512943617 10 Manual.Count131072.C072548.packed 64 cuts72548 = true := by
 decide +kernel
def pointBounds72548 : List (Nat × Nat × Nat) := [(9513005056,116251987185922,116252376950356)]
theorem point_links_checked72548 : (cuts72548.take 1).map (fun c => (9512943617-1+2*2^10*c.k,116251908894683+c.lower,116252298659071+c.upper)) = pointBounds72548 := by
 decide +kernel
def cuts72549 : List PrefixCut := [⟨64,170574875,170574982⟩]
theorem checked72549 : checkPrefixCuts (2^48) 9513074689 10 Manual.Count131072.C072549.packed 64 cuts72549 = true := by
 decide +kernel
def cuts72550 : List PrefixCut := [⟨48,125717939,125718010⟩,
⟨64,169122730,169122824⟩]
theorem checked72550 : checkPrefixCuts (2^48) 9513205761 10 Manual.Count131072.C072550.packed 64 cuts72550 = true := by
 decide +kernel
def pointBounds72550 : List (Nat × Nat × Nat) := [(9513304064,116252372450825,116252762215495)]
theorem point_links_checked72550 : (cuts72550.take 1).map (fun c => (9513205761-1+2*2^10*c.k,116252246732886+c.lower,116252636497485+c.upper)) = pointBounds72550 := by
 decide +kernel
def cuts72551 : List PrefixCut := [⟨64,169505053,169505152⟩]
theorem checked72551 : checkPrefixCuts (2^48) 9513336833 10 Manual.Count131072.C072551.packed 64 cuts72551 = true := by
 decide +kernel
def cuts72552 : List PrefixCut := [⟨64,168822211,168822306⟩]
theorem checked72552 : checkPrefixCuts (2^48) 9513467905 10 Manual.Count131072.C072552.packed 64 cuts72552 = true := by
 decide +kernel
def cuts72553 : List PrefixCut := [⟨2,5443930,5443933⟩,
⟨64,169056572,169056673⟩]
theorem checked72553 : checkPrefixCuts (2^48) 9513598977 10 Manual.Count131072.C072553.packed 64 cuts72553 = true := by
 decide +kernel
def pointBounds72553 : List (Nat × Nat × Nat) := [(9513603072,116252759626810,116253149391700)]
theorem point_links_checked72553 : (cuts72553.take 1).map (fun c => (9513598977-1+2*2^10*c.k,116252754182880+c.lower,116253143947767+c.upper)) = pointBounds72553 := by
 decide +kernel
def cuts72554 : List PrefixCut := [⟨64,168373775,168373867⟩]
theorem checked72554 : checkPrefixCuts (2^48) 9513730049 10 Manual.Count131072.C072554.packed 64 cuts72554 = true := by
 decide +kernel
def cuts72555 : List PrefixCut := [⟨20,50769072,50769101⟩,
⟨64,166270873,166270969⟩]
theorem checked72555 : checkPrefixCuts (2^48) 9513861121 10 Manual.Count131072.C072555.packed 64 cuts72555 = true := by
 decide +kernel
def pointBounds72555 : List (Nat × Nat × Nat) := [(9513902080,116253142382299,116253532147408)]
theorem point_links_checked72555 : (cuts72555.take 1).map (fun c => (9513861121-1+2*2^10*c.k,116253091613227+c.lower,116253481378307+c.upper)) = pointBounds72555 := by
 decide +kernel
def cuts72556 : List PrefixCut := [⟨64,169818809,169818909⟩]
theorem checked72556 : checkPrefixCuts (2^48) 9513992193 10 Manual.Count131072.C072556.packed 64 cuts72556 = true := by
 decide +kernel
def cuts72557 : List PrefixCut := [⟨38,99345864,99345925⟩,
⟨64,167715938,167716042⟩]
theorem checked72557 : checkPrefixCuts (2^48) 9514123265 10 Manual.Count131072.C072557.packed 64 cuts72557 = true := by
 decide +kernel
def pointBounds72557 : List (Nat × Nat × Nat) := [(9514201088,116253527048773,116253916814110)]
theorem point_links_checked72557 : (cuts72557.take 1).map (fun c => (9514123265-1+2*2^10*c.k,116253427702909+c.lower,116253817468185+c.upper)) = pointBounds72557 := by
 decide +kernel
def cuts72558 : List PrefixCut := [⟨64,169252018,169252114⟩]
theorem checked72558 : checkPrefixCuts (2^48) 9514254337 10 Manual.Count131072.C072558.packed 64 cuts72558 = true := by
 decide +kernel
def cuts72559 : List PrefixCut := [⟨56,148718559,148718649⟩,
⟨64,170462618,170462723⟩]
theorem checked72559 : checkPrefixCuts (2^48) 9514385409 10 Manual.Count131072.C072559.packed 64 cuts72559 = true := by
 decide +kernel
def pointBounds72559 : List (Nat × Nat × Nat) := [(9514500096,116253913389424,116254303154990)]
theorem point_links_checked72559 : (cuts72559.take 1).map (fun c => (9514385409-1+2*2^10*c.k,116253764670865+c.lower,116254154436341+c.upper)) = pointBounds72559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000079
