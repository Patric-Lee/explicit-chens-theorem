import PlattAssemblyKernel
import PlattCertificates.Count131072.C061632
import PlattCertificates.Count131072.C061633
import PlattCertificates.Count131072.C061634
import PlattCertificates.Count131072.C061635
import PlattCertificates.Count131072.C061636
import PlattCertificates.Count131072.C061637
import PlattCertificates.Count131072.C061638
import PlattCertificates.Count131072.C061639
import PlattCertificates.Count131072.C061640
import PlattCertificates.Count131072.C061641
import PlattCertificates.Count131072.C061642
import PlattCertificates.Count131072.C061643
import PlattCertificates.Count131072.C061644
import PlattCertificates.Count131072.C061645
import PlattCertificates.Count131072.C061646
import PlattCertificates.Count131072.C061647
import PlattCertificates.Count131072.C061648
import PlattCertificates.Count131072.C061649
import PlattCertificates.Count131072.C061650
import PlattCertificates.Count131072.C061651
import PlattCertificates.Count131072.C061652
import PlattCertificates.Count131072.C061653
import PlattCertificates.Count131072.C061654
import PlattCertificates.Count131072.C061655
import PlattCertificates.Count131072.C061656
import PlattCertificates.Count131072.C061657
import PlattCertificates.Count131072.C061658
import PlattCertificates.Count131072.C061659
import PlattCertificates.Count131072.C061660
import PlattCertificates.Count131072.C061661
import PlattCertificates.Count131072.C061662
import PlattCertificates.Count131072.C061663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61632 : List PrefixCut := [⟨64,200251813,200251935⟩]
theorem checked61632 : checkPrefixCuts (2^48) 8082161665 10 Manual.Count131072.C061632.packed 64 cuts61632 = true := by
 decide +kernel
def cuts61633 : List PrefixCut := [⟨32,101134642,101134700⟩,
⟨64,200144097,200144216⟩]
theorem checked61633 : checkPrefixCuts (2^48) 8082292737 10 Manual.Count131072.C061633.packed 64 cuts61633 = true := by
 decide +kernel
def pointBounds61633 : List (Nat × Nat × Nat) := [(8082358272,114248301501579,114248690098474)]
theorem point_links_checked61633 : (cuts61633.take 1).map (fun c => (8082292737-1+2*2^10*c.k,114248200366937+c.lower,114248588963774+c.upper)) = pointBounds61633 := by
 decide +kernel
def cuts61634 : List PrefixCut := [⟨64,201081132,201081251⟩]
theorem checked61634 : checkPrefixCuts (2^48) 8082423809 10 Manual.Count131072.C061634.packed 64 cuts61634 = true := by
 decide +kernel
def cuts61635 : List PrefixCut := [⟨28,86818393,86818444⟩,
⟨64,201530573,201530689⟩]
theorem checked61635 : checkPrefixCuts (2^48) 8082554881 10 Manual.Count131072.C061635.packed 64 cuts61635 = true := by
 decide +kernel
def pointBounds61635 : List (Nat × Nat × Nat) := [(8082612224,114248688410559,114249077007685)]
theorem point_links_checked61635 : (cuts61635.take 1).map (fun c => (8082554881-1+2*2^10*c.k,114248601592166+c.lower,114248990189241+c.upper)) = pointBounds61635 := by
 decide +kernel
def cuts61636 : List PrefixCut := [⟨64,198776206,198776317⟩]
theorem checked61636 : checkPrefixCuts (2^48) 8082685953 10 Manual.Count131072.C061636.packed 64 cuts61636 = true := by
 decide +kernel
def cuts61637 : List PrefixCut := [⟨24,75254131,75254176⟩,
⟨64,199608741,199608856⟩]
theorem checked61637 : checkPrefixCuts (2^48) 8082817025 10 Manual.Count131072.C061637.packed 64 cuts61637 = true := by
 decide +kernel
def pointBounds61637 : List (Nat × Nat × Nat) := [(8082866176,114249077153076,114249465750423)]
theorem point_links_checked61637 : (cuts61637.take 1).map (fun c => (8082817025-1+2*2^10*c.k,114249001898945+c.lower,114249390496247+c.upper)) = pointBounds61637 := by
 decide +kernel
def cuts61638 : List PrefixCut := [⟨64,201242202,201242316⟩]
theorem checked61638 : checkPrefixCuts (2^48) 8082948097 10 Manual.Count131072.C061638.packed 64 cuts61638 = true := by
 decide +kernel
def cuts61639 : List PrefixCut := [⟨20,60661048,60661079⟩,
⟨64,199706742,199706851⟩]
theorem checked61639 : checkPrefixCuts (2^48) 8083079169 10 Manual.Count131072.C061639.packed 64 cuts61639 = true := by
 decide +kernel
def pointBounds61639 : List (Nat × Nat × Nat) := [(8083120128,114249463410936,114249852008498)]
theorem point_links_checked61639 : (cuts61639.take 1).map (fun c => (8083079169-1+2*2^10*c.k,114249402749888+c.lower,114249791347419+c.upper)) = pointBounds61639 := by
 decide +kernel
def cuts61640 : List PrefixCut := [⟨64,198728518,198728632⟩]
theorem checked61640 : checkPrefixCuts (2^48) 8083210241 10 Manual.Count131072.C061640.packed 64 cuts61640 = true := by
 decide +kernel
def cuts61641 : List PrefixCut := [⟨16,49794792,49794817⟩,
⟨64,201197584,201197694⟩]
theorem checked61641 : checkPrefixCuts (2^48) 8083341313 10 Manual.Count131072.C061641.packed 64 cuts61641 = true := by
 decide +kernel
def pointBounds61641 : List (Nat × Nat × Nat) := [(8083374080,114249850979940,114250239577719)]
theorem point_links_checked61641 : (cuts61641.take 1).map (fun c => (8083341313-1+2*2^10*c.k,114249801185148+c.lower,114250189782902+c.upper)) = pointBounds61641 := by
 decide +kernel
def cuts61642 : List PrefixCut := [⟨64,198861339,198861457⟩]
theorem checked61642 : checkPrefixCuts (2^48) 8083472385 10 Manual.Count131072.C061642.packed 64 cuts61642 = true := by
 decide +kernel
def cuts61643 : List PrefixCut := [⟨12,37118567,37118589⟩,
⟨64,199728608,199728726⟩]
theorem checked61643 : checkPrefixCuts (2^48) 8083603457 10 Manual.Count131072.C061643.packed 64 cuts61643 = true := by
 decide +kernel
def pointBounds61643 : List (Nat × Nat × Nat) := [(8083628032,114250238362638,114250626960642)]
theorem point_links_checked61643 : (cuts61643.take 1).map (fun c => (8083603457-1+2*2^10*c.k,114250201244071+c.lower,114250589842053+c.upper)) = pointBounds61643 := by
 decide +kernel
def cuts61644 : List PrefixCut := [⟨64,201048519,201048632⟩]
theorem checked61644 : checkPrefixCuts (2^48) 8083734529 10 Manual.Count131072.C061644.packed 64 cuts61644 = true := by
 decide +kernel
def cuts61645 : List PrefixCut := [⟨8,25940384,25940399⟩,
⟨64,202229115,202229227⟩]
theorem checked61645 : checkPrefixCuts (2^48) 8083865601 10 Manual.Count131072.C061645.packed 64 cuts61645 = true := by
 decide +kernel
def pointBounds61645 : List (Nat × Nat × Nat) := [(8083881984,114250627961582,114251016559810)]
theorem point_links_checked61645 : (cuts61645.take 1).map (fun c => (8083865601-1+2*2^10*c.k,114250602021198+c.lower,114250990619411+c.upper)) = pointBounds61645 := by
 decide +kernel
def cuts61646 : List PrefixCut := [⟨64,201042006,201042119⟩]
theorem checked61646 : checkPrefixCuts (2^48) 8083996673 10 Manual.Count131072.C061646.packed 64 cuts61646 = true := by
 decide +kernel
def cuts61647 : List PrefixCut := [⟨4,12847914,12847922⟩,
⟨64,203406357,203406476⟩]
theorem checked61647 : checkPrefixCuts (2^48) 8084127745 10 Manual.Count131072.C061647.packed 64 cuts61647 = true := by
 decide +kernel
def pointBounds61647 : List (Nat × Nat × Nat) := [(8084135936,114251018140233,114251406738679)]
theorem point_links_checked61647 : (cuts61647.take 1).map (fun c => (8084127745-1+2*2^10*c.k,114251005292319+c.lower,114251393890757+c.upper)) = pointBounds61647 := by
 decide +kernel
def cuts61648 : List PrefixCut := [⟨64,201766652,201766768⟩]
theorem checked61648 : checkPrefixCuts (2^48) 8084258817 10 Manual.Count131072.C061648.packed 64 cuts61648 = true := by
 decide +kernel
def pointBounds61648 : List (Nat × Nat × Nat) := [(8084389888,114251410465328,114251799064001)]
theorem point_links_checked61648 : (cuts61648.take 1).map (fun c => (8084258817-1+2*2^10*c.k,114251208698676+c.lower,114251597297233+c.upper)) = pointBounds61648 := by
 decide +kernel
def cuts61649 : List PrefixCut := [⟨64,196297148,196297261⟩]
theorem checked61649 : checkPrefixCuts (2^48) 8084389889 10 Manual.Count131072.C061649.packed 64 cuts61649 = true := by
 decide +kernel
def cuts61650 : List PrefixCut := [⟨60,188077419,188077525⟩,
⟨64,199740770,199740884⟩]
theorem checked61650 : checkPrefixCuts (2^48) 8084520961 10 Manual.Count131072.C061650.packed 64 cuts61650 = true := by
 decide +kernel
def pointBounds61650 : List (Nat × Nat × Nat) := [(8084643840,114251794839895,114252183438787)]
theorem point_links_checked61650 : (cuts61650.take 1).map (fun c => (8084520961-1+2*2^10*c.k,114251606762476+c.lower,114251995361262+c.upper)) = pointBounds61650 := by
 decide +kernel
def cuts61651 : List PrefixCut := [⟨64,199006397,199006507⟩]
theorem checked61651 : checkPrefixCuts (2^48) 8084652033 10 Manual.Count131072.C061651.packed 64 cuts61651 = true := by
 decide +kernel
def cuts61652 : List PrefixCut := [⟨56,175468346,175468438⟩,
⟨64,199943195,199943303⟩]
theorem checked61652 : checkPrefixCuts (2^48) 8084783105 10 Manual.Count131072.C061652.packed 64 cuts61652 = true := by
 decide +kernel
def pointBounds61652 : List (Nat × Nat × Nat) := [(8084897792,114252180977989,114252569577091)]
theorem point_links_checked61652 : (cuts61652.take 1).map (fun c => (8084783105-1+2*2^10*c.k,114252005509643+c.lower,114252394108653+c.upper)) = pointBounds61652 := by
 decide +kernel
def cuts61653 : List PrefixCut := [⟨64,201645863,201645973⟩]
theorem checked61653 : checkPrefixCuts (2^48) 8084914177 10 Manual.Count131072.C061653.packed 64 cuts61653 = true := by
 decide +kernel
def cuts61654 : List PrefixCut := [⟨52,161711196,161711290⟩,
⟨64,198718215,198718333⟩]
theorem checked61654 : checkPrefixCuts (2^48) 8085045249 10 Manual.Count131072.C061654.packed 64 cuts61654 = true := by
 decide +kernel
def pointBounds61654 : List (Nat × Nat × Nat) := [(8085151744,114252568809897,114252957409219)]
theorem point_links_checked61654 : (cuts61654.take 1).map (fun c => (8085045249-1+2*2^10*c.k,114252407098701+c.lower,114252795697929+c.upper)) = pointBounds61654 := by
 decide +kernel
def cuts61655 : List PrefixCut := [⟨64,203449621,203449731⟩]
theorem checked61655 : checkPrefixCuts (2^48) 8085176321 10 Manual.Count131072.C061655.packed 64 cuts61655 = true := by
 decide +kernel
def cuts61656 : List PrefixCut := [⟨48,150182947,150183037⟩,
⟨64,199756147,199756266⟩]
theorem checked61656 : checkPrefixCuts (2^48) 8085307393 10 Manual.Count131072.C061656.packed 64 cuts61656 = true := by
 decide +kernel
def pointBounds61656 : List (Nat × Nat × Nat) := [(8085405696,114252959449484,114253348049030)]
theorem point_links_checked61656 : (cuts61656.take 1).map (fun c => (8085307393-1+2*2^10*c.k,114252809266537+c.lower,114253197865993+c.upper)) = pointBounds61656 := by
 decide +kernel
def cuts61657 : List PrefixCut := [⟨64,196445740,196445856⟩]
theorem checked61657 : checkPrefixCuts (2^48) 8085438465 10 Manual.Count131072.C061657.packed 64 cuts61657 = true := by
 decide +kernel
def cuts61658 : List PrefixCut := [⟨44,137158536,137158614⟩,
⟨64,197800221,197800335⟩]
theorem checked61658 : checkPrefixCuts (2^48) 8085569537 10 Manual.Count131072.C061658.packed 64 cuts61658 = true := by
 decide +kernel
def pointBounds61658 : List (Nat × Nat × Nat) := [(8085659648,114253342626960,114253731226729)]
theorem point_links_checked61658 : (cuts61658.take 1).map (fun c => (8085569537-1+2*2^10*c.k,114253205468424+c.lower,114253594068115+c.upper)) = pointBounds61658 := by
 decide +kernel
def cuts61659 : List PrefixCut := [⟨64,201835110,201835222⟩]
theorem checked61659 : checkPrefixCuts (2^48) 8085700609 10 Manual.Count131072.C061659.packed 64 cuts61659 = true := by
 decide +kernel
def cuts61660 : List PrefixCut := [⟨40,122289994,122290068⟩,
⟨64,197724168,197724287⟩]
theorem checked61660 : checkPrefixCuts (2^48) 8085831681 10 Manual.Count131072.C061660.packed 64 cuts61660 = true := by
 decide +kernel
def pointBounds61660 : List (Nat × Nat × Nat) := [(8085913600,114253727393749,114254115993740)]
theorem point_links_checked61660 : (cuts61660.take 1).map (fun c => (8085831681-1+2*2^10*c.k,114253605103755+c.lower,114253993703672+c.upper)) = pointBounds61660 := by
 decide +kernel
def cuts61661 : List PrefixCut := [⟨64,199357041,199357155⟩]
theorem checked61661 : checkPrefixCuts (2^48) 8085962753 10 Manual.Count131072.C061661.packed 64 cuts61661 = true := by
 decide +kernel
def cuts61662 : List PrefixCut := [⟨36,112017256,112017320⟩,
⟨64,199597475,199597592⟩]
theorem checked61662 : checkPrefixCuts (2^48) 8086093825 10 Manual.Count131072.C061662.packed 64 cuts61662 = true := by
 decide +kernel
def pointBounds61662 : List (Nat × Nat × Nat) := [(8086167552,114254114202220,114254502802434)]
theorem point_links_checked61662 : (cuts61662.take 1).map (fun c => (8086093825-1+2*2^10*c.k,114254002184964+c.lower,114254390785114+c.upper)) = pointBounds61662 := by
 decide +kernel
def cuts61663 : List PrefixCut := [⟨64,201891651,201891765⟩]
theorem checked61663 : checkPrefixCuts (2^48) 8086224897 10 Manual.Count131072.C061663.packed 64 cuts61663 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000051
