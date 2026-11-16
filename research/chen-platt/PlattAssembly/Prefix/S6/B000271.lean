import PlattAssemblyKernel
import PlattCertificates.Count131072.C058672
import PlattCertificates.Count131072.C058673
import PlattCertificates.Count131072.C058674
import PlattCertificates.Count131072.C058675
import PlattCertificates.Count131072.C058676
import PlattCertificates.Count131072.C058677
import PlattCertificates.Count131072.C058678
import PlattCertificates.Count131072.C058679
import PlattCertificates.Count131072.C058680
import PlattCertificates.Count131072.C058681
import PlattCertificates.Count131072.C058682
import PlattCertificates.Count131072.C058683
import PlattCertificates.Count131072.C058684
import PlattCertificates.Count131072.C058685
import PlattCertificates.Count131072.C058686
import PlattCertificates.Count131072.C058687
import PlattCertificates.Count131072.C058688
import PlattCertificates.Count131072.C058689
import PlattCertificates.Count131072.C058690
import PlattCertificates.Count131072.C058691
import PlattCertificates.Count131072.C058692
import PlattCertificates.Count131072.C058693
import PlattCertificates.Count131072.C058694
import PlattCertificates.Count131072.C058695
import PlattCertificates.Count131072.C058696
import PlattCertificates.Count131072.C058697
import PlattCertificates.Count131072.C058698
import PlattCertificates.Count131072.C058699
import PlattCertificates.Count131072.C058700
import PlattCertificates.Count131072.C058701
import PlattCertificates.Count131072.C058702
import PlattCertificates.Count131072.C058703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000271
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58672 : List PrefixCut := [⟨64,207715314,207715439⟩]
theorem checked58672 : checkPrefixCuts (2^48) 7694188545 10 Manual.Count131072.C058672.packed 64 cuts58672 = true := by
 decide +kernel
def pointBounds58672 : List (Nat × Nat × Nat) := [(7694319616,113640514146547,113640902396141)]
theorem point_links_checked58672 : (cuts58672.take 1).map (fun c => (7694188545-1+2*2^10*c.k,113640306431233+c.lower,113640694680702+c.upper)) = pointBounds58672 := by
 decide +kernel
def cuts58673 : List PrefixCut := [⟨64,207455701,207455819⟩]
theorem checked58673 : checkPrefixCuts (2^48) 7694319617 10 Manual.Count131072.C058673.packed 64 cuts58673 = true := by
 decide +kernel
def cuts58674 : List PrefixCut := [⟨54,177785029,177785131⟩,
⟨64,211476102,211476223⟩]
theorem checked58674 : checkPrefixCuts (2^48) 7694450689 10 Manual.Count131072.C058674.packed 64 cuts58674 = true := by
 decide +kernel
def pointBounds58674 : List (Nat × Nat × Nat) := [(7694561280,113640899387277,113641287637091)]
theorem point_links_checked58674 : (cuts58674.take 1).map (fun c => (7694450689-1+2*2^10*c.k,113640721602248+c.lower,113641109851960+c.upper)) = pointBounds58674 := by
 decide +kernel
def cuts58675 : List PrefixCut := [⟨64,211691998,211692122⟩]
theorem checked58675 : checkPrefixCuts (2^48) 7694581761 10 Manual.Count131072.C058675.packed 64 cuts58675 = true := by
 decide +kernel
def cuts58676 : List PrefixCut := [⟨44,142442854,142442936⟩,
⟨64,207701165,207701285⟩]
theorem checked58676 : checkPrefixCuts (2^48) 7694712833 10 Manual.Count131072.C058676.packed 64 cuts58676 = true := by
 decide +kernel
def pointBounds58676 : List (Nat × Nat × Nat) := [(7694802944,113641287213202,113641675463241)]
theorem point_links_checked58676 : (cuts58676.take 1).map (fun c => (7694712833-1+2*2^10*c.k,113641144770348+c.lower,113641533020305+c.upper)) = pointBounds58676 := by
 decide +kernel
def cuts58677 : List PrefixCut := [⟨64,212013987,212014104⟩]
theorem checked58677 : checkPrefixCuts (2^48) 7694843905 10 Manual.Count131072.C058677.packed 64 cuts58677 = true := by
 decide +kernel
def cuts58678 : List PrefixCut := [⟨34,112114289,112114352⟩,
⟨64,211351966,211352085⟩]
theorem checked58678 : checkPrefixCuts (2^48) 7694974977 10 Manual.Count131072.C058678.packed 64 cuts58678 = true := by
 decide +kernel
def pointBounds58678 : List (Nat × Nat × Nat) := [(7695044608,113641676599789,113642064850046)]
theorem point_links_checked58678 : (cuts58678.take 1).map (fun c => (7694974977-1+2*2^10*c.k,113641564485500+c.lower,113641952735694+c.upper)) = pointBounds58678 := by
 decide +kernel
def cuts58679 : List PrefixCut := [⟨64,210507076,210507192⟩]
theorem checked58679 : checkPrefixCuts (2^48) 7695106049 10 Manual.Count131072.C058679.packed 64 cuts58679 = true := by
 decide +kernel
def cuts58680 : List PrefixCut := [⟨24,77947057,77947103⟩,
⟨64,211015551,211015674⟩]
theorem checked58680 : checkPrefixCuts (2^48) 7695237121 10 Manual.Count131072.C058680.packed 64 cuts58680 = true := by
 decide +kernel
def pointBounds58680 : List (Nat × Nat × Nat) := [(7695286272,113642064291599,113642452542074)]
theorem point_links_checked58680 : (cuts58680.take 1).map (fun c => (7695237121-1+2*2^10*c.k,113641986344542+c.lower,113642374594971+c.upper)) = pointBounds58680 := by
 decide +kernel
def cuts58681 : List PrefixCut := [⟨64,211341180,211341301⟩]
theorem checked58681 : checkPrefixCuts (2^48) 7695368193 10 Manual.Count131072.C058681.packed 64 cuts58681 = true := by
 decide +kernel
def cuts58682 : List PrefixCut := [⟨14,45757192,45757218⟩,
⟨64,208923536,208923656⟩]
theorem checked58682 : checkPrefixCuts (2^48) 7695499265 10 Manual.Count131072.C058682.packed 64 cuts58682 = true := by
 decide +kernel
def pointBounds58682 : List (Nat × Nat × Nat) := [(7695527936,113642454458465,113642842709164)]
theorem point_links_checked58682 : (cuts58682.take 1).map (fun c => (7695499265-1+2*2^10*c.k,113642408701273+c.lower,113642796951946+c.upper)) = pointBounds58682 := by
 decide +kernel
def cuts58683 : List PrefixCut := [⟨64,207383815,207383929⟩]
theorem checked58683 : checkPrefixCuts (2^48) 7695630337 10 Manual.Count131072.C058683.packed 64 cuts58683 = true := by
 decide +kernel
def cuts58684 : List PrefixCut := [⟨4,12655051,12655059⟩,
⟨64,210123383,210123502⟩]
theorem checked58684 : checkPrefixCuts (2^48) 7695761409 10 Manual.Count131072.C058684.packed 64 cuts58684 = true := by
 decide +kernel
def pointBounds58684 : List (Nat × Nat × Nat) := [(7695769600,113642837663675,113643225914590)]
theorem point_links_checked58684 : (cuts58684.take 1).map (fun c => (7695761409-1+2*2^10*c.k,113642825008624+c.lower,113643213259531+c.upper)) = pointBounds58684 := by
 decide +kernel
def cuts58685 : List PrefixCut := [⟨58,190955011,190955120⟩,
⟨64,210449005,210449126⟩]
theorem checked58685 : checkPrefixCuts (2^48) 7695892481 10 Manual.Count131072.C058685.packed 64 cuts58685 = true := by
 decide +kernel
def pointBounds58685 : List (Nat × Nat × Nat) := [(7696011264,113643226087018,113643614338153)]
theorem point_links_checked58685 : (cuts58685.take 1).map (fun c => (7695892481-1+2*2^10*c.k,113643035132007+c.lower,113643423383033+c.upper)) = pointBounds58685 := by
 decide +kernel
def cuts58686 : List PrefixCut := [⟨64,212237524,212237645⟩]
theorem checked58686 : checkPrefixCuts (2^48) 7696023553 10 Manual.Count131072.C058686.packed 64 cuts58686 = true := by
 decide +kernel
def cuts58687 : List PrefixCut := [⟨48,157228238,157228324⟩,
⟨64,210990401,210990519⟩]
theorem checked58687 : checkPrefixCuts (2^48) 7696154625 10 Manual.Count131072.C058687.packed 64 cuts58687 = true := by
 decide +kernel
def pointBounds58687 : List (Nat × Nat × Nat) := [(7696252928,113643615046774,113644003298128)]
theorem point_links_checked58687 : (cuts58687.take 1).map (fun c => (7696154625-1+2*2^10*c.k,113643457818536+c.lower,113643846069804+c.upper)) = pointBounds58687 := by
 decide +kernel
def cuts58688 : List PrefixCut := [⟨64,207987875,207987992⟩]
theorem checked58688 : checkPrefixCuts (2^48) 7696285697 10 Manual.Count131072.C058688.packed 64 cuts58688 = true := by
 decide +kernel
def cuts58689 : List PrefixCut := [⟨38,125332296,125332371⟩,
⟨64,211641517,211641642⟩]
theorem checked58689 : checkPrefixCuts (2^48) 7696416769 10 Manual.Count131072.C058689.packed 64 cuts58689 = true := by
 decide +kernel
def pointBounds58689 : List (Nat × Nat × Nat) := [(7696494592,113644002129108,113644390380686)]
theorem point_links_checked58689 : (cuts58689.take 1).map (fun c => (7696416769-1+2*2^10*c.k,113643876796812+c.lower,113644265048315+c.upper)) = pointBounds58689 := by
 decide +kernel
def cuts58690 : List PrefixCut := [⟨64,210540760,210540879⟩]
theorem checked58690 : checkPrefixCuts (2^48) 7696547841 10 Manual.Count131072.C058690.packed 64 cuts58690 = true := by
 decide +kernel
def cuts58691 : List PrefixCut := [⟨28,91280765,91280816⟩,
⟨64,210866319,210866436⟩]
theorem checked58691 : checkPrefixCuts (2^48) 7696678913 10 Manual.Count131072.C058691.packed 64 cuts58691 = true := by
 decide +kernel
def pointBounds58691 : List (Nat × Nat × Nat) := [(7696736256,113644390259854,113644778511652)]
theorem point_links_checked58691 : (cuts58691.take 1).map (fun c => (7696678913-1+2*2^10*c.k,113644298979089+c.lower,113644687230836+c.upper)) = pointBounds58691 := by
 decide +kernel
def cuts58692 : List PrefixCut := [⟨64,211374729,211374849⟩]
theorem checked58692 : checkPrefixCuts (2^48) 7696809985 10 Manual.Count131072.C058692.packed 64 cuts58692 = true := by
 decide +kernel
def cuts58693 : List PrefixCut := [⟨18,60010753,60010788⟩,
⟨64,211480837,211480957⟩]
theorem checked58693 : checkPrefixCuts (2^48) 7696941057 10 Manual.Count131072.C058693.packed 64 cuts58693 = true := by
 decide +kernel
def pointBounds58693 : List (Nat × Nat × Nat) := [(7696977920,113644781230890,113645169482909)]
theorem point_links_checked58693 : (cuts58693.take 1).map (fun c => (7696941057-1+2*2^10*c.k,113644721220137+c.lower,113645109472121+c.upper)) = pointBounds58693 := by
 decide +kernel
def cuts58694 : List PrefixCut := [⟨64,209612211,209612331⟩]
theorem checked58694 : checkPrefixCuts (2^48) 7697072129 10 Manual.Count131072.C058694.packed 64 cuts58694 = true := by
 decide +kernel
def cuts58695 : List PrefixCut := [⟨8,24537414,24537429⟩,
⟨64,211071356,211071474⟩]
theorem checked58695 : checkPrefixCuts (2^48) 7697203201 10 Manual.Count131072.C058695.packed 64 cuts58695 = true := by
 decide +kernel
def pointBounds58695 : List (Nat × Nat × Nat) := [(7697219584,113645166850599,113645555102838)]
theorem point_links_checked58695 : (cuts58695.take 1).map (fun c => (7697203201-1+2*2^10*c.k,113645142313185+c.lower,113645530565409+c.upper)) = pointBounds58695 := by
 decide +kernel
def cuts58696 : List PrefixCut := [⟨62,204266279,204266394⟩,
⟨64,210848380,210848498⟩]
theorem checked58696 : checkPrefixCuts (2^48) 7697334273 10 Manual.Count131072.C058696.packed 64 cuts58696 = true := by
 decide +kernel
def pointBounds58696 : List (Nat × Nat × Nat) := [(7697461248,113645557650820,113645945903277)]
theorem point_links_checked58696 : (cuts58696.take 1).map (fun c => (7697334273-1+2*2^10*c.k,113645353384541+c.lower,113645741636883+c.upper)) = pointBounds58696 := by
 decide +kernel
def cuts58697 : List PrefixCut := [⟨64,209784329,209784451⟩]
theorem checked58697 : checkPrefixCuts (2^48) 7697465345 10 Manual.Count131072.C058697.packed 64 cuts58697 = true := by
 decide +kernel
def cuts58698 : List PrefixCut := [⟨52,170728241,170728339⟩,
⟨64,208683781,208683903⟩]
theorem checked58698 : checkPrefixCuts (2^48) 7697596417 10 Manual.Count131072.C058698.packed 64 cuts58698 = true := by
 decide +kernel
def pointBounds58698 : List (Nat × Nat × Nat) := [(7697702912,113645944745491,113646332998171)]
theorem point_links_checked58698 : (cuts58698.take 1).map (fun c => (7697596417-1+2*2^10*c.k,113645774017250+c.lower,113646162269832+c.upper)) = pointBounds58698 := by
 decide +kernel
def cuts58699 : List PrefixCut := [⟨64,212446508,212446625⟩]
theorem checked58699 : checkPrefixCuts (2^48) 7697727489 10 Manual.Count131072.C058699.packed 64 cuts58699 = true := by
 decide +kernel
def cuts58700 : List PrefixCut := [⟨42,140519852,140519932⟩,
⟨64,210907155,210907275⟩]
theorem checked58700 : checkPrefixCuts (2^48) 7697858561 10 Manual.Count131072.C058700.packed 64 cuts58700 = true := by
 decide +kernel
def pointBounds58700 : List (Nat × Nat × Nat) := [(7697944576,113646335667391,113646723920292)]
theorem point_links_checked58700 : (cuts58700.take 1).map (fun c => (7697858561-1+2*2^10*c.k,113646195147539+c.lower,113646583400360+c.upper)) = pointBounds58700 := by
 decide +kernel
def cuts58701 : List PrefixCut := [⟨64,210464776,210464898⟩]
theorem checked58701 : checkPrefixCuts (2^48) 7697989633 10 Manual.Count131072.C058701.packed 64 cuts58701 = true := by
 decide +kernel
def cuts58702 : List PrefixCut := [⟨32,105011662,105011720⟩,
⟨64,210022430,210022548⟩]
theorem checked58702 : checkPrefixCuts (2^48) 7698120705 10 Manual.Count131072.C058702.packed 64 cuts58702 = true := by
 decide +kernel
def pointBounds58702 : List (Nat × Nat × Nat) := [(7698186240,113646721531132,113647109784253)]
theorem point_links_checked58702 : (cuts58702.take 1).map (fun c => (7698120705-1+2*2^10*c.k,113646616519470+c.lower,113647004772533+c.upper)) = pointBounds58702 := by
 decide +kernel
def cuts58703 : List PrefixCut := [⟨64,211554522,211554641⟩]
theorem checked58703 : checkPrefixCuts (2^48) 7698251777 10 Manual.Count131072.C058703.packed 64 cuts58703 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000271
