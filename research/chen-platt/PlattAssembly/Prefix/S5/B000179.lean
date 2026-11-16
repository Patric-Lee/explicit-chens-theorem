import PlattAssemblyKernel
import PlattCertificates.Count131072.C045728
import PlattCertificates.Count131072.C045729
import PlattCertificates.Count131072.C045730
import PlattCertificates.Count131072.C045731
import PlattCertificates.Count131072.C045732
import PlattCertificates.Count131072.C045733
import PlattCertificates.Count131072.C045734
import PlattCertificates.Count131072.C045735
import PlattCertificates.Count131072.C045736
import PlattCertificates.Count131072.C045737
import PlattCertificates.Count131072.C045738
import PlattCertificates.Count131072.C045739
import PlattCertificates.Count131072.C045740
import PlattCertificates.Count131072.C045741
import PlattCertificates.Count131072.C045742
import PlattCertificates.Count131072.C045743
import PlattCertificates.Count131072.C045744
import PlattCertificates.Count131072.C045745
import PlattCertificates.Count131072.C045746
import PlattCertificates.Count131072.C045747
import PlattCertificates.Count131072.C045748
import PlattCertificates.Count131072.C045749
import PlattCertificates.Count131072.C045750
import PlattCertificates.Count131072.C045751
import PlattCertificates.Count131072.C045752
import PlattCertificates.Count131072.C045753
import PlattCertificates.Count131072.C045754
import PlattCertificates.Count131072.C045755
import PlattCertificates.Count131072.C045756
import PlattCertificates.Count131072.C045757
import PlattCertificates.Count131072.C045758
import PlattCertificates.Count131072.C045759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45728 : List PrefixCut := [⟨64,274263626,274263778⟩]
theorem checked45728 : checkPrefixCuts (2^48) 5997592577 10 Manual.Count131072.C045728.packed 64 cuts45728 = true := by
 decide +kernel
def cuts45729 : List PrefixCut := [⟨18,78326407,78326452⟩,
⟨64,275994031,275994189⟩]
theorem checked45729 : checkPrefixCuts (2^48) 5997723649 10 Manual.Count131072.C045729.packed 64 cuts45729 = true := by
 decide +kernel
def pointBounds45729 : List (Nat × Nat × Nat) := [(5997760512,110543553522119,110543940007179)]
theorem point_links_checked45729 : (cuts45729.take 1).map (fun c => (5997723649-1+2*2^10*c.k,110543475195712+c.lower,110543861680727+c.upper)) = pointBounds45729 := by
 decide +kernel
def cuts45730 : List PrefixCut := [⟨46,196772849,196772959⟩,
⟨64,272609110,272609264⟩]
theorem checked45730 : checkPrefixCuts (2^48) 5997854721 10 Manual.Count131072.C045730.packed 64 cuts45730 = true := by
 decide +kernel
def pointBounds45730 : List (Nat × Nat × Nat) := [(5997948928,110543947962592,110544334447875)]
theorem point_links_checked45730 : (cuts45730.take 1).map (fun c => (5997854721-1+2*2^10*c.k,110543751189743+c.lower,110544137674916+c.upper)) = pointBounds45730 := by
 decide +kernel
def cuts45731 : List PrefixCut := [⟨64,268145005,268145162⟩]
theorem checked45731 : checkPrefixCuts (2^48) 5997985793 10 Manual.Count131072.C045731.packed 64 cuts45731 = true := by
 decide +kernel
def cuts45732 : List PrefixCut := [⟨10,44533847,44533873⟩,
⟨64,273535732,273535890⟩]
theorem checked45732 : checkPrefixCuts (2^48) 5998116865 10 Manual.Count131072.C045732.packed 64 cuts45732 = true := by
 decide +kernel
def pointBounds45732 : List (Nat × Nat × Nat) := [(5998137344,110544336477705,110544722963215)]
theorem point_links_checked45732 : (cuts45732.take 1).map (fun c => (5998116865-1+2*2^10*c.k,110544291943858+c.lower,110544678429342+c.upper)) = pointBounds45732 := by
 decide +kernel
def cuts45733 : List PrefixCut := [⟨38,159266429,159266520⟩,
⟨64,270995726,270995884⟩]
theorem checked45733 : checkPrefixCuts (2^48) 5998247937 10 Manual.Count131072.C045733.packed 64 cuts45733 = true := by
 decide +kernel
def pointBounds45733 : List (Nat × Nat × Nat) := [(5998325760,110544724746019,110545111231752)]
theorem point_links_checked45733 : (cuts45733.take 1).map (fun c => (5998247937-1+2*2^10*c.k,110544565479590+c.lower,110544951965232+c.upper)) = pointBounds45733 := by
 decide +kernel
def cuts45734 : List PrefixCut := [⟨64,274086848,274087011⟩]
theorem checked45734 : checkPrefixCuts (2^48) 5998379009 10 Manual.Count131072.C045734.packed 64 cuts45734 = true := by
 decide +kernel
def cuts45735 : List PrefixCut := [⟨2,8634038,8634042⟩,
⟨64,273611646,273611804⟩]
theorem checked45735 : checkPrefixCuts (2^48) 5998510081 10 Manual.Count131072.C045735.packed 64 cuts45735 = true := by
 decide +kernel
def pointBounds45735 : List (Nat × Nat × Nat) := [(5998514176,110545119196202,110545505682169)]
theorem point_links_checked45735 : (cuts45735.take 1).map (fun c => (5998510081-1+2*2^10*c.k,110545110562164+c.lower,110545497048127+c.upper)) = pointBounds45735 := by
 decide +kernel
def cuts45736 : List PrefixCut := [⟨30,130398651,130398726⟩,
⟨64,278110230,278110392⟩]
theorem checked45736 : checkPrefixCuts (2^48) 5998641153 10 Manual.Count131072.C045736.packed 64 cuts45736 = true := by
 decide +kernel
def pointBounds45736 : List (Nat × Nat × Nat) := [(5998702592,110545514572461,110545901058657)]
theorem point_links_checked45736 : (cuts45736.take 1).map (fun c => (5998641153-1+2*2^10*c.k,110545384173810+c.lower,110545770659931+c.upper)) = pointBounds45736 := by
 decide +kernel
def cuts45737 : List PrefixCut := [⟨58,248309201,248309351⟩,
⟨64,274256574,274256738⟩]
theorem checked45737 : checkPrefixCuts (2^48) 5998772225 10 Manual.Count131072.C045737.packed 64 cuts45737 = true := by
 decide +kernel
def pointBounds45737 : List (Nat × Nat × Nat) := [(5998891008,110545910593241,110546297079674)]
theorem point_links_checked45737 : (cuts45737.take 1).map (fun c => (5998772225-1+2*2^10*c.k,110545662284040+c.lower,110546048770323+c.upper)) = pointBounds45737 := by
 decide +kernel
def cuts45738 : List PrefixCut := [⟨64,270168517,270168672⟩]
theorem checked45738 : checkPrefixCuts (2^48) 5998903297 10 Manual.Count131072.C045738.packed 64 cuts45738 = true := by
 decide +kernel
def cuts45739 : List PrefixCut := [⟨22,93839714,93839769⟩,
⟨64,271617090,271617250⟩]
theorem checked45739 : checkPrefixCuts (2^48) 5999034369 10 Manual.Count131072.C045739.packed 64 cuts45739 = true := by
 decide +kernel
def pointBounds45739 : List (Nat × Nat × Nat) := [(5999079424,110546300548845,110546687035502)]
theorem point_links_checked45739 : (cuts45739.take 1).map (fun c => (5999034369-1+2*2^10*c.k,110546206709131+c.lower,110546593195733+c.upper)) = pointBounds45739 := by
 decide +kernel
def cuts45740 : List PrefixCut := [⟨50,212822812,212822932⟩,
⟨64,272971808,272971965⟩]
theorem checked45740 : checkPrefixCuts (2^48) 5999165441 10 Manual.Count131072.C045740.packed 64 cuts45740 = true := by
 decide +kernel
def pointBounds45740 : List (Nat × Nat × Nat) := [(5999267840,110546691149033,110547077635915)]
theorem point_links_checked45740 : (cuts45740.take 1).map (fun c => (5999165441-1+2*2^10*c.k,110546478326221+c.lower,110546864812983+c.upper)) = pointBounds45740 := by
 decide +kernel
def cuts45741 : List PrefixCut := [⟨64,273810341,273810496⟩]
theorem checked45741 : checkPrefixCuts (2^48) 5999296513 10 Manual.Count131072.C045741.packed 64 cuts45741 = true := by
 decide +kernel
def cuts45742 : List PrefixCut := [⟨14,59725143,59725181⟩,
⟨64,272819129,272819300⟩]
theorem checked45742 : checkPrefixCuts (2^48) 5999427585 10 Manual.Count131072.C045742.packed 64 cuts45742 = true := by
 decide +kernel
def pointBounds45742 : List (Nat × Nat × Nat) := [(5999456256,110547084833513,110547471320625)]
theorem point_links_checked45742 : (cuts45742.take 1).map (fun c => (5999427585-1+2*2^10*c.k,110547025108370+c.lower,110547411595444+c.upper)) = pointBounds45742 := by
 decide +kernel
def cuts45743 : List PrefixCut := [⟨42,183299246,183299352⟩,
⟨64,276519523,276519681⟩]
theorem checked45743 : checkPrefixCuts (2^48) 5999558657 10 Manual.Count131072.C045743.packed 64 cuts45743 = true := by
 decide +kernel
def pointBounds45743 : List (Nat × Nat × Nat) := [(5999644672,110547481226745,110547867714096)]
theorem point_links_checked45743 : (cuts45743.take 1).map (fun c => (5999558657-1+2*2^10*c.k,110547297927499+c.lower,110547684414744+c.upper)) = pointBounds45743 := by
 decide +kernel
def cuts45744 : List PrefixCut := [⟨64,276278876,276279032⟩]
theorem checked45744 : checkPrefixCuts (2^48) 5999689729 10 Manual.Count131072.C045744.packed 64 cuts45744 = true := by
 decide +kernel
def cuts45745 : List PrefixCut := [⟨6,25427299,25427315⟩,
⟨64,271628431,271628582⟩]
theorem checked45745 : checkPrefixCuts (2^48) 5999820801 10 Manual.Count131072.C045745.packed 64 cuts45745 = true := by
 decide +kernel
def pointBounds45745 : List (Nat × Nat × Nat) := [(5999833088,110547876153197,110548262640772)]
theorem point_links_checked45745 : (cuts45745.take 1).map (fun c => (5999820801-1+2*2^10*c.k,110547850725898+c.lower,110548237213457+c.upper)) = pointBounds45745 := by
 decide +kernel
def cuts45746 : List PrefixCut := [⟨34,143599427,143599509⟩,
⟨64,270543499,270543651⟩]
theorem checked45746 : checkPrefixCuts (2^48) 5999951873 10 Manual.Count131072.C045746.packed 64 cuts45746 = true := by
 decide +kernel
def pointBounds45746 : List (Nat × Nat × Nat) := [(6000021504,110548265953756,110548652441548)]
theorem point_links_checked45746 : (cuts45746.take 1).map (fun c => (5999951873-1+2*2^10*c.k,110548122354329+c.lower,110548508842039+c.upper)) = pointBounds45746 := by
 decide +kernel
def cuts45747 : List PrefixCut := [⟨62,261765272,261765430⟩,
⟨64,270631418,270631581⟩]
theorem checked45747 : checkPrefixCuts (2^48) 6000082945 10 Manual.Count131072.C045747.packed 64 cuts45747 = true := by
 decide +kernel
def pointBounds45747 : List (Nat × Nat × Nat) := [(6000209920,110548654663100,110549041151120)]
theorem point_links_checked45747 : (cuts45747.take 1).map (fun c => (6000082945-1+2*2^10*c.k,110548392897828+c.lower,110548779385690+c.upper)) = pointBounds45747 := by
 decide +kernel
def cuts45748 : List PrefixCut := [⟨64,275269630,275269788⟩]
theorem checked45748 : checkPrefixCuts (2^48) 6000214017 10 Manual.Count131072.C045748.packed 64 cuts45748 = true := by
 decide +kernel
def cuts45749 : List PrefixCut := [⟨26,111879335,111879399⟩,
⟨64,272730517,272730675⟩]
theorem checked45749 : checkPrefixCuts (2^48) 6000345089 10 Manual.Count131072.C045749.packed 64 cuts45749 = true := by
 decide +kernel
def pointBounds45749 : List (Nat × Nat × Nat) := [(6000398336,110549050678211,110549437166458)]
theorem point_links_checked45749 : (cuts45749.take 1).map (fun c => (6000345089-1+2*2^10*c.k,110548938798876+c.lower,110549325287059+c.upper)) = pointBounds45749 := by
 decide +kernel
def cuts45750 : List PrefixCut := [⟨54,228678095,228678221⟩,
⟨64,272302363,272302514⟩]
theorem checked45750 : checkPrefixCuts (2^48) 6000476161 10 Manual.Count131072.C045750.packed 64 cuts45750 = true := by
 decide +kernel
def pointBounds45750 : List (Nat × Nat × Nat) := [(6000586752,110549440207488,110549826695955)]
theorem point_links_checked45750 : (cuts45750.take 1).map (fun c => (6000476161-1+2*2^10*c.k,110549211529393+c.lower,110549598017734+c.upper)) = pointBounds45750 := by
 decide +kernel
def cuts45751 : List PrefixCut := [⟨64,276752634,276752797⟩]
theorem checked45751 : checkPrefixCuts (2^48) 6000607233 10 Manual.Count131072.C045751.packed 64 cuts45751 = true := by
 decide +kernel
def cuts45752 : List PrefixCut := [⟨18,76973674,76973718⟩,
⟨64,269523003,269523162⟩]
theorem checked45752 : checkPrefixCuts (2^48) 6000738305 10 Manual.Count131072.C045752.packed 64 cuts45752 = true := by
 decide +kernel
def pointBounds45752 : List (Nat × Nat × Nat) := [(6000775168,110549837558064,110550224046763)]
theorem point_links_checked45752 : (cuts45752.take 1).map (fun c => (6000738305-1+2*2^10*c.k,110549760584390+c.lower,110550147073045+c.upper)) = pointBounds45752 := by
 decide +kernel
def cuts45753 : List PrefixCut := [⟨46,194891600,194891712⟩,
⟨64,271534050,271534209⟩]
theorem checked45753 : checkPrefixCuts (2^48) 6000869377 10 Manual.Count131072.C045753.packed 64 cuts45753 = true := by
 decide +kernel
def pointBounds45753 : List (Nat × Nat × Nat) := [(6000963584,110550224998993,110550611487919)]
theorem point_links_checked45753 : (cuts45753.take 1).map (fun c => (6000869377-1+2*2^10*c.k,110550030107393+c.lower,110550416596207+c.upper)) = pointBounds45753 := by
 decide +kernel
def cuts45754 : List PrefixCut := [⟨64,273967158,273967308⟩]
theorem checked45754 : checkPrefixCuts (2^48) 6001000449 10 Manual.Count131072.C045754.packed 64 cuts45754 = true := by
 decide +kernel
def cuts45755 : List PrefixCut := [⟨10,42682238,42682265⟩,
⟨64,271100046,271100205⟩]
theorem checked45755 : checkPrefixCuts (2^48) 6001131521 10 Manual.Count131072.C045755.packed 64 cuts45755 = true := by
 decide +kernel
def pointBounds45755 : List (Nat × Nat × Nat) := [(6001152000,110550618290839,110551004779989)]
theorem point_links_checked45755 : (cuts45755.take 1).map (fun c => (6001131521-1+2*2^10*c.k,110550575608601+c.lower,110550962097724+c.upper)) = pointBounds45755 := by
 decide +kernel
def cuts45756 : List PrefixCut := [⟨38,162610292,162610390⟩,
⟨64,271610067,271610225⟩]
theorem checked45756 : checkPrefixCuts (2^48) 6001262593 10 Manual.Count131072.C045756.packed 64 cuts45756 = true := by
 decide +kernel
def pointBounds45756 : List (Nat × Nat × Nat) := [(6001340416,110551009318939,110551395808319)]
theorem point_links_checked45756 : (cuts45756.take 1).map (fun c => (6001262593-1+2*2^10*c.k,110550846708647+c.lower,110551233197929+c.upper)) = pointBounds45756 := by
 decide +kernel
def cuts45757 : List PrefixCut := [⟨64,267429938,267430095⟩]
theorem checked45757 : checkPrefixCuts (2^48) 6001393665 10 Manual.Count131072.C045757.packed 64 cuts45757 = true := by
 decide +kernel
def cuts45758 : List PrefixCut := [⟨2,9520812,9520816⟩,
⟨64,274177701,274177856⟩]
theorem checked45758 : checkPrefixCuts (2^48) 6001524737 10 Manual.Count131072.C045758.packed 64 cuts45758 = true := by
 decide +kernel
def pointBounds45758 : List (Nat × Nat × Nat) := [(6001528832,110551395269464,110551781759065)]
theorem point_links_checked45758 : (cuts45758.take 1).map (fun c => (6001524737-1+2*2^10*c.k,110551385748652+c.lower,110551772238249+c.upper)) = pointBounds45758 := by
 decide +kernel
def cuts45759 : List PrefixCut := [⟨30,128973077,128973155⟩,
⟨64,272999250,272999412⟩]
theorem checked45759 : checkPrefixCuts (2^48) 6001655809 10 Manual.Count131072.C045759.packed 64 cuts45759 = true := by
 decide +kernel
def pointBounds45759 : List (Nat × Nat × Nat) := [(6001717248,110551788899430,110552175389260)]
theorem point_links_checked45759 : (cuts45759.take 1).map (fun c => (6001655809-1+2*2^10*c.k,110551659926353+c.lower,110552046416105+c.upper)) = pointBounds45759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000179
