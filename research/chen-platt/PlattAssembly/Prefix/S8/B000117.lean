import PlattAssemblyKernel
import PlattCertificates.Count131072.C073744
import PlattCertificates.Count131072.C073745
import PlattCertificates.Count131072.C073746
import PlattCertificates.Count131072.C073747
import PlattCertificates.Count131072.C073748
import PlattCertificates.Count131072.C073749
import PlattCertificates.Count131072.C073750
import PlattCertificates.Count131072.C073751
import PlattCertificates.Count131072.C073752
import PlattCertificates.Count131072.C073753
import PlattCertificates.Count131072.C073754
import PlattCertificates.Count131072.C073755
import PlattCertificates.Count131072.C073756
import PlattCertificates.Count131072.C073757
import PlattCertificates.Count131072.C073758
import PlattCertificates.Count131072.C073759
import PlattCertificates.Count131072.C073760
import PlattCertificates.Count131072.C073761
import PlattCertificates.Count131072.C073762
import PlattCertificates.Count131072.C073763
import PlattCertificates.Count131072.C073764
import PlattCertificates.Count131072.C073765
import PlattCertificates.Count131072.C073766
import PlattCertificates.Count131072.C073767
import PlattCertificates.Count131072.C073768
import PlattCertificates.Count131072.C073769
import PlattCertificates.Count131072.C073770
import PlattCertificates.Count131072.C073771
import PlattCertificates.Count131072.C073772
import PlattCertificates.Count131072.C073773
import PlattCertificates.Count131072.C073774
import PlattCertificates.Count131072.C073775
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000117
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73744 : List PrefixCut := [⟨6,15136640,15136649⟩,
⟨64,165279460,165279556⟩]
theorem checked73744 : checkPrefixCuts (2^48) 9669705729 10 Manual.Count131072.C073744.packed 64 cuts73744 = true := by
 decide +kernel
def pointBounds73744 : List (Nat × Nat × Nat) := [(9669718016,116452124536909,116452514420726)]
theorem point_links_checked73744 : (cuts73744.take 1).map (fun c => (9669705729-1+2*2^10*c.k,116452109400269+c.lower,116452499284077+c.upper)) = pointBounds73744 := by
 decide +kernel
def cuts73745 : List PrefixCut := [⟨64,166819946,166820051⟩]
theorem checked73745 : checkPrefixCuts (2^48) 9669836801 10 Manual.Count131072.C073745.packed 64 cuts73745 = true := by
 decide +kernel
def cuts73746 : List PrefixCut := [⟨26,66948564,66948605⟩,
⟨64,163412058,163412157⟩]
theorem checked73746 : checkPrefixCuts (2^48) 9669967873 10 Manual.Count131072.C073746.packed 64 cuts73746 = true := by
 decide +kernel
def pointBounds73746 : List (Nat × Nat × Nat) := [(9670021120,116452508448239,116452898332289)]
theorem point_links_checked73746 : (cuts73746.take 1).map (fun c => (9669967873-1+2*2^10*c.k,116452441499675+c.lower,116452831383684+c.upper)) = pointBounds73746 := by
 decide +kernel
def cuts73747 : List PrefixCut := [⟨64,166029531,166029630⟩]
theorem checked73747 : checkPrefixCuts (2^48) 9670098945 10 Manual.Count131072.C073747.packed 64 cuts73747 = true := by
 decide +kernel
def cuts73748 : List PrefixCut := [⟨46,118437283,118437355⟩,
⟨64,164979412,164979512⟩]
theorem checked73748 : checkPrefixCuts (2^48) 9670230017 10 Manual.Count131072.C073748.packed 64 cuts73748 = true := by
 decide +kernel
def pointBounds73748 : List (Nat × Nat × Nat) := [(9670324224,116452889378547,116453279262826)]
theorem point_links_checked73748 : (cuts73748.take 1).map (fun c => (9670230017-1+2*2^10*c.k,116452770941264+c.lower,116453160825471+c.upper)) = pointBounds73748 := by
 decide +kernel
def cuts73749 : List PrefixCut := [⟨64,168237119,168237212⟩]
theorem checked73749 : checkPrefixCuts (2^48) 9670361089 10 Manual.Count131072.C073749.packed 64 cuts73749 = true := by
 decide +kernel
def cuts73750 : List PrefixCut := [⟨64,167070597,167070701⟩]
theorem checked73750 : checkPrefixCuts (2^48) 9670492161 10 Manual.Count131072.C073750.packed 64 cuts73750 = true := by
 decide +kernel
def cuts73751 : List PrefixCut := [⟨2,5471960,5471964⟩,
⟨64,164012202,164012301⟩]
theorem checked73751 : checkPrefixCuts (2^48) 9670623233 10 Manual.Count131072.C073751.packed 64 cuts73751 = true := by
 decide +kernel
def pointBounds73751 : List (Nat × Nat × Nat) := [(9670627328,116453276700352,116453666584860)]
theorem point_links_checked73751 : (cuts73751.take 1).map (fun c => (9670623233-1+2*2^10*c.k,116453271228392+c.lower,116453661112896+c.upper)) = pointBounds73751 := by
 decide +kernel
def cuts73752 : List PrefixCut := [⟨64,166047381,166047482⟩]
theorem checked73752 : checkPrefixCuts (2^48) 9670754305 10 Manual.Count131072.C073752.packed 64 cuts73752 = true := by
 decide +kernel
def cuts73753 : List PrefixCut := [⟨22,56813591,56813621⟩,
⟨64,166539914,166540006⟩]
theorem checked73753 : checkPrefixCuts (2^48) 9670885377 10 Manual.Count131072.C073753.packed 64 cuts73753 = true := by
 decide +kernel
def pointBounds73753 : List (Nat × Nat × Nat) := [(9670930432,116453658101566,116454047986300)]
theorem point_links_checked73753 : (cuts73753.take 1).map (fun c => (9670885377-1+2*2^10*c.k,116453601287975+c.lower,116453991172679+c.upper)) = pointBounds73753 := by
 decide +kernel
def cuts73754 : List PrefixCut := [⟨64,166828704,166828803⟩]
theorem checked73754 : checkPrefixCuts (2^48) 9671016449 10 Manual.Count131072.C073754.packed 64 cuts73754 = true := by
 decide +kernel
def cuts73755 : List PrefixCut := [⟨42,109141774,109141839⟩,
⟨64,164614520,164614620⟩]
theorem checked73755 : checkPrefixCuts (2^48) 9671147521 10 Manual.Count131072.C073755.packed 64 cuts73755 = true := by
 decide +kernel
def pointBounds73755 : List (Nat × Nat × Nat) := [(9671233536,116454043798367,116454433683327)]
theorem point_links_checked73755 : (cuts73755.take 1).map (fun c => (9671147521-1+2*2^10*c.k,116453934656593+c.lower,116454324541488+c.upper)) = pointBounds73755 := by
 decide +kernel
def cuts73756 : List PrefixCut := [⟨64,164612280,164612377⟩]
theorem checked73756 : checkPrefixCuts (2^48) 9671278593 10 Manual.Count131072.C073756.packed 64 cuts73756 = true := by
 decide +kernel
def cuts73757 : List PrefixCut := [⟨62,160360952,160361049⟩,
⟨64,165424948,165425048⟩]
theorem checked73757 : checkPrefixCuts (2^48) 9671409665 10 Manual.Count131072.C073757.packed 64 cuts73757 = true := by
 decide +kernel
def pointBounds73757 : List (Nat × Nat × Nat) := [(9671536640,116454424244345,116454814129534)]
theorem point_links_checked73757 : (cuts73757.take 1).map (fun c => (9671409665-1+2*2^10*c.k,116454263883393+c.lower,116454653768485+c.upper)) = pointBounds73757 := by
 decide +kernel
def cuts73758 : List PrefixCut := [⟨64,166819669,166819764⟩]
theorem checked73758 : checkPrefixCuts (2^48) 9671540737 10 Manual.Count131072.C073758.packed 64 cuts73758 = true := by
 decide +kernel
def cuts73759 : List PrefixCut := [⟨64,164343665,164343763⟩]
theorem checked73759 : checkPrefixCuts (2^48) 9671671809 10 Manual.Count131072.C073759.packed 64 cuts73759 = true := by
 decide +kernel
def cuts73760 : List PrefixCut := [⟨18,46302196,46302221⟩,
⟨64,165971167,165971260⟩]
theorem checked73760 : checkPrefixCuts (2^48) 9671802881 10 Manual.Count131072.C073760.packed 64 cuts73760 = true := by
 decide +kernel
def pointBounds73760 : List (Nat × Nat × Nat) := [(9671839744,116454806773871,116455196659281)]
theorem point_links_checked73760 : (cuts73760.take 1).map (fun c => (9671802881-1+2*2^10*c.k,116454760471675+c.lower,116455150357060+c.upper)) = pointBounds73760 := by
 decide +kernel
def cuts73761 : List PrefixCut := [⟨64,167249409,167249507⟩]
theorem checked73761 : checkPrefixCuts (2^48) 9671933953 10 Manual.Count131072.C073761.packed 64 cuts73761 = true := by
 decide +kernel
def cuts73762 : List PrefixCut := [⟨38,98567537,98567593⟩,
⟨64,166519605,166519698⟩]
theorem checked73762 : checkPrefixCuts (2^48) 9672065025 10 Manual.Count131072.C073762.packed 64 cuts73762 = true := by
 decide +kernel
def pointBounds73762 : List (Nat × Nat × Nat) := [(9672142848,116455192259788,116455582145420)]
theorem point_links_checked73762 : (cuts73762.take 1).map (fun c => (9672065025-1+2*2^10*c.k,116455093692251+c.lower,116455483577827+c.upper)) = pointBounds73762 := by
 decide +kernel
def cuts73763 : List PrefixCut := [⟨64,166691963,166692058⟩]
theorem checked73763 : checkPrefixCuts (2^48) 9672196097 10 Manual.Count131072.C073763.packed 64 cuts73763 = true := by
 decide +kernel
def cuts73764 : List PrefixCut := [⟨58,151033527,151033615⟩,
⟨64,167999220,167999320⟩]
theorem checked73764 : checkPrefixCuts (2^48) 9672327169 10 Manual.Count131072.C073764.packed 64 cuts73764 = true := by
 decide +kernel
def pointBounds73764 : List (Nat × Nat × Nat) := [(9672445952,116455577937346,116455967823198)]
theorem point_links_checked73764 : (cuts73764.take 1).map (fun c => (9672327169-1+2*2^10*c.k,116455426903819+c.lower,116455816789583+c.upper)) = pointBounds73764 := by
 decide +kernel
def cuts73765 : List PrefixCut := [⟨64,163631886,163631979⟩]
theorem checked73765 : checkPrefixCuts (2^48) 9672458241 10 Manual.Count131072.C073765.packed 64 cuts73765 = true := by
 decide +kernel
def cuts73766 : List PrefixCut := [⟨64,166190474,166190570⟩]
theorem checked73766 : checkPrefixCuts (2^48) 9672589313 10 Manual.Count131072.C073766.packed 64 cuts73766 = true := by
 decide +kernel
def cuts73767 : List PrefixCut := [⟨14,36869478,36869502⟩,
⟨64,167701409,167701507⟩]
theorem checked73767 : checkPrefixCuts (2^48) 9672720385 10 Manual.Count131072.C073767.packed 64 cuts73767 = true := by
 decide +kernel
def pointBounds73767 : List (Nat × Nat × Nat) := [(9672749056,116455961594877,116456351480954)]
theorem point_links_checked73767 : (cuts73767.take 1).map (fun c => (9672720385-1+2*2^10*c.k,116455924725399+c.lower,116456314611452+c.upper)) = pointBounds73767 := by
 decide +kernel
def cuts73768 : List PrefixCut := [⟨64,165167492,165167593⟩]
theorem checked73768 : checkPrefixCuts (2^48) 9672851457 10 Manual.Count131072.C073768.packed 64 cuts73768 = true := by
 decide +kernel
def cuts73769 : List PrefixCut := [⟨34,87238731,87238782⟩,
⟨64,163070146,163070241⟩]
theorem checked73769 : checkPrefixCuts (2^48) 9672982529 10 Manual.Count131072.C073769.packed 64 cuts73769 = true := by
 decide +kernel
def pointBounds73769 : List (Nat × Nat × Nat) := [(9673052160,116456344833031,116456734719334)]
theorem point_links_checked73769 : (cuts73769.take 1).map (fun c => (9672982529-1+2*2^10*c.k,116456257594300+c.lower,116456647480552+c.upper)) = pointBounds73769 := by
 decide +kernel
def cuts73770 : List PrefixCut := [⟨64,165046625,165046727⟩]
theorem checked73770 : checkPrefixCuts (2^48) 9673113601 10 Manual.Count131072.C073770.packed 64 cuts73770 = true := by
 decide +kernel
def cuts73771 : List PrefixCut := [⟨54,140922208,140922295⟩,
⟨64,167226736,167226839⟩]
theorem checked73771 : checkPrefixCuts (2^48) 9673244673 10 Manual.Count131072.C073771.packed 64 cuts73771 = true := by
 decide +kernel
def pointBounds73771 : List (Nat × Nat × Nat) := [(9673355264,116456726633279,116457116519815)]
theorem point_links_checked73771 : (cuts73771.take 1).map (fun c => (9673244673-1+2*2^10*c.k,116456585711071+c.lower,116456975597520+c.upper)) = pointBounds73771 := by
 decide +kernel
def cuts73772 : List PrefixCut := [⟨64,163354481,163354584⟩]
theorem checked73772 : checkPrefixCuts (2^48) 9673375745 10 Manual.Count131072.C073772.packed 64 cuts73772 = true := by
 decide +kernel
def cuts73773 : List PrefixCut := [⟨64,167280403,167280509⟩]
theorem checked73773 : checkPrefixCuts (2^48) 9673506817 10 Manual.Count131072.C073773.packed 64 cuts73773 = true := by
 decide +kernel
def cuts73774 : List PrefixCut := [⟨10,24005089,24005105⟩,
⟨64,161109590,161109690⟩]
theorem checked73774 : checkPrefixCuts (2^48) 9673637889 10 Manual.Count131072.C073774.packed 64 cuts73774 = true := by
 decide +kernel
def pointBounds73774 : List (Nat × Nat × Nat) := [(9673658368,116457107577780,116457497464557)]
theorem point_links_checked73774 : (cuts73774.take 1).map (fun c => (9673637889-1+2*2^10*c.k,116457083572691+c.lower,116457473459452+c.upper)) = pointBounds73774 := by
 decide +kernel
def cuts73775 : List PrefixCut := [⟨64,164104353,164104447⟩]
theorem checked73775 : checkPrefixCuts (2^48) 9673768961 10 Manual.Count131072.C073775.packed 64 cuts73775 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000117
