import PlattAssemblyKernel
import PlattCertificates.Count131072.C066560
import PlattCertificates.Count131072.C066561
import PlattCertificates.Count131072.C066562
import PlattCertificates.Count131072.C066563
import PlattCertificates.Count131072.C066564
import PlattCertificates.Count131072.C066565
import PlattCertificates.Count131072.C066566
import PlattCertificates.Count131072.C066567
import PlattCertificates.Count131072.C066568
import PlattCertificates.Count131072.C066569
import PlattCertificates.Count131072.C066570
import PlattCertificates.Count131072.C066571
import PlattCertificates.Count131072.C066572
import PlattCertificates.Count131072.C066573
import PlattCertificates.Count131072.C066574
import PlattCertificates.Count131072.C066575
import PlattCertificates.Count131072.C066576
import PlattCertificates.Count131072.C066577
import PlattCertificates.Count131072.C066578
import PlattCertificates.Count131072.C066579
import PlattCertificates.Count131072.C066580
import PlattCertificates.Count131072.C066581
import PlattCertificates.Count131072.C066582
import PlattCertificates.Count131072.C066583
import PlattCertificates.Count131072.C066584
import PlattCertificates.Count131072.C066585
import PlattCertificates.Count131072.C066586
import PlattCertificates.Count131072.C066587
import PlattCertificates.Count131072.C066588
import PlattCertificates.Count131072.C066589
import PlattCertificates.Count131072.C066590
import PlattCertificates.Count131072.C066591
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000205
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66560 : List PrefixCut := [⟨64,182400868,182400973⟩]
theorem checked66560 : checkPrefixCuts (2^48) 8728084481 10 Manual.Count131072.C066560.packed 64 cuts66560 = true := by
 decide +kernel
def cuts66561 : List PrefixCut := [⟨50,142087599,142087682⟩,
⟨64,182752852,182752959⟩]
theorem checked66561 : checkPrefixCuts (2^48) 8728215553 10 Manual.Count131072.C066561.packed 64 cuts66561 = true := by
 decide +kernel
def pointBounds66561 : List (Nat × Nat × Nat) := [(8728317952,115195390837776,115195779981161)]
theorem point_links_checked66561 : (cuts66561.take 1).map (fun c => (8728215553-1+2*2^10*c.k,115195248750177+c.lower,115195637893479+c.upper)) = pointBounds66561 := by
 decide +kernel
def cuts66562 : List PrefixCut := [⟨64,188844999,188845109⟩]
theorem checked66562 : checkPrefixCuts (2^48) 8728346625 10 Manual.Count131072.C066562.packed 64 cuts66562 = true := by
 decide +kernel
def cuts66563 : List PrefixCut := [⟨56,162431513,162431608⟩,
⟨64,185552916,185553027⟩]
theorem checked66563 : checkPrefixCuts (2^48) 8728477697 10 Manual.Count131072.C066563.packed 64 cuts66563 = true := by
 decide +kernel
def pointBounds66563 : List (Nat × Nat × Nat) := [(8728592384,115195782779541,115196171923155)]
theorem point_links_checked66563 : (cuts66563.take 1).map (fun c => (8728477697-1+2*2^10*c.k,115195620348028+c.lower,115196009491547+c.upper)) = pointBounds66563 := by
 decide +kernel
def cuts66564 : List PrefixCut := [⟨64,185163166,185163271⟩]
theorem checked66564 : checkPrefixCuts (2^48) 8728608769 10 Manual.Count131072.C066564.packed 64 cuts66564 = true := by
 decide +kernel
def cuts66565 : List PrefixCut := [⟨62,178969055,178969160⟩,
⟨64,184547688,184547796⟩]
theorem checked66565 : checkPrefixCuts (2^48) 8728739841 10 Manual.Count131072.C066565.packed 64 cuts66565 = true := by
 decide +kernel
def pointBounds66565 : List (Nat × Nat × Nat) := [(8728866816,115196170033165,115196559177005)]
theorem point_links_checked66565 : (cuts66565.take 1).map (fun c => (8728739841-1+2*2^10*c.k,115195991064110+c.lower,115196380207845+c.upper)) = pointBounds66565 := by
 decide +kernel
def cuts66566 : List PrefixCut := [⟨64,183867758,183867871⟩]
theorem checked66566 : checkPrefixCuts (2^48) 8728870913 10 Manual.Count131072.C066566.packed 64 cuts66566 = true := by
 decide +kernel
def cuts66567 : List PrefixCut := [⟨64,185219321,185219426⟩]
theorem checked66567 : checkPrefixCuts (2^48) 8729001985 10 Manual.Count131072.C066567.packed 64 cuts66567 = true := by
 decide +kernel
def cuts66568 : List PrefixCut := [⟨4,11672851,11672857⟩,
⟨64,182153233,182153344⟩]
theorem checked66568 : checkPrefixCuts (2^48) 8729133057 10 Manual.Count131072.C066568.packed 64 cuts66568 = true := by
 decide +kernel
def pointBounds66568 : List (Nat × Nat × Nat) := [(8729141248,115196556371728,115196945515795)]
theorem point_links_checked66568 : (cuts66568.take 1).map (fun c => (8729133057-1+2*2^10*c.k,115196544698877+c.lower,115196933842938+c.upper)) = pointBounds66568 := by
 decide +kernel
def cuts66569 : List PrefixCut := [⟨64,184762313,184762417⟩]
theorem checked66569 : checkPrefixCuts (2^48) 8729264129 10 Manual.Count131072.C066569.packed 64 cuts66569 = true := by
 decide +kernel
def cuts66570 : List PrefixCut := [⟨10,28536341,28536357⟩,
⟨64,184340356,184340465⟩]
theorem checked66570 : checkPrefixCuts (2^48) 8729395201 10 Manual.Count131072.C066570.packed 64 cuts66570 = true := by
 decide +kernel
def pointBounds66570 : List (Nat × Nat × Nat) := [(8729415680,115196940150764,115197329295056)]
theorem point_links_checked66570 : (cuts66570.take 1).map (fun c => (8729395201-1+2*2^10*c.k,115196911614423+c.lower,115197300758699+c.upper)) = pointBounds66570 := by
 decide +kernel
def cuts66571 : List PrefixCut := [⟨64,187078300,187078402⟩]
theorem checked66571 : checkPrefixCuts (2^48) 8729526273 10 Manual.Count131072.C066571.packed 64 cuts66571 = true := by
 decide +kernel
def cuts66572 : List PrefixCut := [⟨16,45979176,45979204⟩,
⟨64,184560530,184560634⟩]
theorem checked66572 : checkPrefixCuts (2^48) 8729657345 10 Manual.Count131072.C066572.packed 64 cuts66572 = true := by
 decide +kernel
def pointBounds66572 : List (Nat × Nat × Nat) := [(8729690112,115197329012255,115197718156770)]
theorem point_links_checked66572 : (cuts66572.take 1).map (fun c => (8729657345-1+2*2^10*c.k,115197283033079+c.lower,115197672177566+c.upper)) = pointBounds66572 := by
 decide +kernel
def cuts66573 : List PrefixCut := [⟨64,182236292,182236401⟩]
theorem checked66573 : checkPrefixCuts (2^48) 8729788417 10 Manual.Count131072.C066573.packed 64 cuts66573 = true := by
 decide +kernel
def cuts66574 : List PrefixCut := [⟨22,64775123,64775161⟩,
⟨64,185296573,185296680⟩]
theorem checked66574 : checkPrefixCuts (2^48) 8729919489 10 Manual.Count131072.C066574.packed 64 cuts66574 = true := by
 decide +kernel
def pointBounds66574 : List (Nat × Nat × Nat) := [(8729964544,115197714605024,115198103749762)]
theorem point_links_checked66574 : (cuts66574.take 1).map (fun c => (8729919489-1+2*2^10*c.k,115197649829901+c.lower,115198038974601+c.upper)) = pointBounds66574 := by
 decide +kernel
def cuts66575 : List PrefixCut := [⟨64,181328031,181328141⟩]
theorem checked66575 : checkPrefixCuts (2^48) 8730050561 10 Manual.Count131072.C066575.packed 64 cuts66575 = true := by
 decide +kernel
def cuts66576 : List PrefixCut := [⟨28,80990596,80990645⟩,
⟨64,185742375,185742486⟩]
theorem checked66576 : checkPrefixCuts (2^48) 8730181633 10 Manual.Count131072.C066576.packed 64 cuts66576 = true := by
 decide +kernel
def pointBounds66576 : List (Nat × Nat × Nat) := [(8730238976,115198097445101,115198486590067)]
theorem point_links_checked66576 : (cuts66576.take 1).map (fun c => (8730181633-1+2*2^10*c.k,115198016454505+c.lower,115198405599422+c.upper)) = pointBounds66576 := by
 decide +kernel
def cuts66577 : List PrefixCut := [⟨64,183482720,183482826⟩]
theorem checked66577 : checkPrefixCuts (2^48) 8730312705 10 Manual.Count131072.C066577.packed 64 cuts66577 = true := by
 decide +kernel
def cuts66578 : List PrefixCut := [⟨34,99913274,99913331⟩,
⟨64,185801296,185801401⟩]
theorem checked66578 : checkPrefixCuts (2^48) 8730443777 10 Manual.Count131072.C066578.packed 64 cuts66578 = true := by
 decide +kernel
def pointBounds66578 : List (Nat × Nat × Nat) := [(8730513408,115198485592874,115198874738065)]
theorem point_links_checked66578 : (cuts66578.take 1).map (fun c => (8730443777-1+2*2^10*c.k,115198385679600+c.lower,115198774824734+c.upper)) = pointBounds66578 := by
 decide +kernel
def cuts66579 : List PrefixCut := [⟨64,184605630,184605734⟩]
theorem checked66579 : checkPrefixCuts (2^48) 8730574849 10 Manual.Count131072.C066579.packed 64 cuts66579 = true := by
 decide +kernel
def cuts66580 : List PrefixCut := [⟨40,116771472,116771540⟩,
⟨64,184699577,184699687⟩]
theorem checked66580 : checkPrefixCuts (2^48) 8730705921 10 Manual.Count131072.C066580.packed 64 cuts66580 = true := by
 decide +kernel
def pointBounds66580 : List (Nat × Nat × Nat) := [(8730787840,115198872857998,115199262003409)]
theorem point_links_checked66580 : (cuts66580.take 1).map (fun c => (8730705921-1+2*2^10*c.k,115198756086526+c.lower,115199145231869+c.upper)) = pointBounds66580 := by
 decide +kernel
def cuts66581 : List PrefixCut := [⟨64,184567845,184567950⟩]
theorem checked66581 : checkPrefixCuts (2^48) 8730836993 10 Manual.Count131072.C066581.packed 64 cuts66581 = true := by
 decide +kernel
def cuts66582 : List PrefixCut := [⟨46,132306833,132306903⟩,
⟨64,184274918,184275016⟩]
theorem checked66582 : checkPrefixCuts (2^48) 8730968065 10 Manual.Count131072.C066582.packed 64 cuts66582 = true := by
 decide +kernel
def pointBounds66582 : List (Nat × Nat × Nat) := [(8731062272,115199257660781,115199646806409)]
theorem point_links_checked66582 : (cuts66582.take 1).map (fun c => (8730968065-1+2*2^10*c.k,115199125353948+c.lower,115199514499506+c.upper)) = pointBounds66582 := by
 decide +kernel
def cuts66583 : List PrefixCut := [⟨64,185303763,185303865⟩]
theorem checked66583 : checkPrefixCuts (2^48) 8731099137 10 Manual.Count131072.C066583.packed 64 cuts66583 = true := by
 decide +kernel
def cuts66584 : List PrefixCut := [⟨52,153644009,153644093⟩,
⟨64,187589860,187589961⟩]
theorem checked66584 : checkPrefixCuts (2^48) 8731230209 10 Manual.Count131072.C066584.packed 64 cuts66584 = true := by
 decide +kernel
def pointBounds66584 : List (Nat × Nat × Nat) := [(8731336704,115199648576638,115200037722480)]
theorem point_links_checked66584 : (cuts66584.take 1).map (fun c => (8731230209-1+2*2^10*c.k,115199494932629+c.lower,115199884078387+c.upper)) = pointBounds66584 := by
 decide +kernel
def cuts66585 : List PrefixCut := [⟨64,187458077,187458189⟩]
theorem checked66585 : checkPrefixCuts (2^48) 8731361281 10 Manual.Count131072.C066585.packed 64 cuts66585 = true := by
 decide +kernel
def cuts66586 : List PrefixCut := [⟨58,165953630,165953722⟩,
⟨64,182877679,182877781⟩]
theorem checked66586 : checkPrefixCuts (2^48) 8731492353 10 Manual.Count131072.C066586.packed 64 cuts66586 = true := by
 decide +kernel
def pointBounds66586 : List (Nat × Nat × Nat) := [(8731611136,115200035934196,115200425080259)]
theorem point_links_checked66586 : (cuts66586.take 1).map (fun c => (8731492353-1+2*2^10*c.k,115199869980566+c.lower,115200259126537+c.upper)) = pointBounds66586 := by
 decide +kernel
def cuts66587 : List PrefixCut := [⟨64,185776185,185776291⟩]
theorem checked66587 : checkPrefixCuts (2^48) 8731623425 10 Manual.Count131072.C066587.packed 64 cuts66587 = true := by
 decide +kernel
def cuts66588 : List PrefixCut := [⟨64,184290544,184290651⟩]
theorem checked66588 : checkPrefixCuts (2^48) 8731754497 10 Manual.Count131072.C066588.packed 64 cuts66588 = true := by
 decide +kernel
def pointBounds66588 : List (Nat × Nat × Nat) := [(8731885568,115200422924974,115200812071260)]
theorem point_links_checked66588 : (cuts66588.take 1).map (fun c => (8731754497-1+2*2^10*c.k,115200238634430+c.lower,115200627780609+c.upper)) = pointBounds66588 := by
 decide +kernel
def cuts66589 : List PrefixCut := [⟨64,184029902,184030011⟩]
theorem checked66589 : checkPrefixCuts (2^48) 8731885569 10 Manual.Count131072.C066589.packed 64 cuts66589 = true := by
 decide +kernel
def cuts66590 : List PrefixCut := [⟨64,184768542,184768651⟩]
theorem checked66590 : checkPrefixCuts (2^48) 8732016641 10 Manual.Count131072.C066590.packed 64 cuts66590 = true := by
 decide +kernel
def cuts66591 : List PrefixCut := [⟨6,16310558,16310566⟩,
⟨64,183025124,183025237⟩]
theorem checked66591 : checkPrefixCuts (2^48) 8732147713 10 Manual.Count131072.C066591.packed 64 cuts66591 = true := by
 decide +kernel
def pointBounds66591 : List (Nat × Nat × Nat) := [(8732160000,115200808033976,115201197180488)]
theorem point_links_checked66591 : (cuts66591.take 1).map (fun c => (8732147713-1+2*2^10*c.k,115200791723418+c.lower,115201180869922+c.upper)) = pointBounds66591 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000205
