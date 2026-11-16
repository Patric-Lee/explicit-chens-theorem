import PlattAssemblyKernel
import PlattCertificates.Count131072.C066720
import PlattCertificates.Count131072.C066721
import PlattCertificates.Count131072.C066722
import PlattCertificates.Count131072.C066723
import PlattCertificates.Count131072.C066724
import PlattCertificates.Count131072.C066725
import PlattCertificates.Count131072.C066726
import PlattCertificates.Count131072.C066727
import PlattCertificates.Count131072.C066728
import PlattCertificates.Count131072.C066729
import PlattCertificates.Count131072.C066730
import PlattCertificates.Count131072.C066731
import PlattCertificates.Count131072.C066732
import PlattCertificates.Count131072.C066733
import PlattCertificates.Count131072.C066734
import PlattCertificates.Count131072.C066735
import PlattCertificates.Count131072.C066736
import PlattCertificates.Count131072.C066737
import PlattCertificates.Count131072.C066738
import PlattCertificates.Count131072.C066739
import PlattCertificates.Count131072.C066740
import PlattCertificates.Count131072.C066741
import PlattCertificates.Count131072.C066742
import PlattCertificates.Count131072.C066743
import PlattCertificates.Count131072.C066744
import PlattCertificates.Count131072.C066745
import PlattCertificates.Count131072.C066746
import PlattCertificates.Count131072.C066747
import PlattCertificates.Count131072.C066748
import PlattCertificates.Count131072.C066749
import PlattCertificates.Count131072.C066750
import PlattCertificates.Count131072.C066751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000210
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66720 : List PrefixCut := [⟨58,167711661,167711760⟩,
⟨64,184151334,184151444⟩]
theorem checked66720 : checkPrefixCuts (2^48) 8749056001 10 Manual.Count131072.C066720.packed 64 cuts66720 = true := by
 decide +kernel
def pointBounds66720 : List (Nat × Nat × Nat) := [(8749174784,115224730081269,115225119241715)]
theorem point_links_checked66720 : (cuts66720.take 1).map (fun c => (8749056001-1+2*2^10*c.k,115224562369608+c.lower,115224951529955+c.upper)) = pointBounds66720 := by
 decide +kernel
def cuts66721 : List PrefixCut := [⟨64,185081534,185081646⟩]
theorem checked66721 : checkPrefixCuts (2^48) 8749187073 10 Manual.Count131072.C066721.packed 64 cuts66721 = true := by
 decide +kernel
def cuts66722 : List PrefixCut := [⟨64,181314772,181314880⟩]
theorem checked66722 : checkPrefixCuts (2^48) 8749318145 10 Manual.Count131072.C066722.packed 64 cuts66722 = true := by
 decide +kernel
def pointBounds66722 : List (Nat × Nat × Nat) := [(8749449216,115225112917248,115225502077925)]
theorem point_links_checked66722 : (cuts66722.take 1).map (fun c => (8749318145-1+2*2^10*c.k,115224931602476+c.lower,115225320763045+c.upper)) = pointBounds66722 := by
 decide +kernel
def cuts66723 : List PrefixCut := [⟨64,185204676,185204777⟩]
theorem checked66723 : checkPrefixCuts (2^48) 8749449217 10 Manual.Count131072.C066723.packed 64 cuts66723 = true := by
 decide +kernel
def cuts66724 : List PrefixCut := [⟨64,184783675,184783784⟩]
theorem checked66724 : checkPrefixCuts (2^48) 8749580289 10 Manual.Count131072.C066724.packed 64 cuts66724 = true := by
 decide +kernel
def cuts66725 : List PrefixCut := [⟨6,17146395,17146405⟩,
⟨64,184620075,184620180⟩]
theorem checked66725 : checkPrefixCuts (2^48) 8749711361 10 Manual.Count131072.C066725.packed 64 cuts66725 = true := by
 decide +kernel
def pointBounds66725 : List (Nat × Nat × Nat) := [(8749723648,115225500051994,115225889212891)]
theorem point_links_checked66725 : (cuts66725.take 1).map (fun c => (8749711361-1+2*2^10*c.k,115225482905599+c.lower,115225872066486+c.upper)) = pointBounds66725 := by
 decide +kernel
def cuts66726 : List PrefixCut := [⟨64,186643944,186644053⟩]
theorem checked66726 : checkPrefixCuts (2^48) 8749842433 10 Manual.Count131072.C066726.packed 64 cuts66726 = true := by
 decide +kernel
def cuts66727 : List PrefixCut := [⟨12,33873548,33873567⟩,
⟨64,182201903,182202006⟩]
theorem checked66727 : checkPrefixCuts (2^48) 8749973505 10 Manual.Count131072.C066727.packed 64 cuts66727 = true := by
 decide +kernel
def pointBounds66727 : List (Nat × Nat × Nat) := [(8749998080,115225888043166,115226277204286)]
theorem point_links_checked66727 : (cuts66727.take 1).map (fun c => (8749973505-1+2*2^10*c.k,115225854169618+c.lower,115226243330719+c.upper)) = pointBounds66727 := by
 decide +kernel
def cuts66728 : List PrefixCut := [⟨64,183035545,183035652⟩]
theorem checked66728 : checkPrefixCuts (2^48) 8750104577 10 Manual.Count131072.C066728.packed 64 cuts66728 = true := by
 decide +kernel
def cuts66729 : List PrefixCut := [⟨18,51822045,51822076⟩,
⟨64,184158665,184158777⟩]
theorem checked66729 : checkPrefixCuts (2^48) 8750235649 10 Manual.Count131072.C066729.packed 64 cuts66729 = true := by
 decide +kernel
def pointBounds66729 : List (Nat × Nat × Nat) := [(8750272512,115226271229111,115226660390453)]
theorem point_links_checked66729 : (cuts66729.take 1).map (fun c => (8750235649-1+2*2^10*c.k,115226219407066+c.lower,115226608568377+c.upper)) = pointBounds66729 := by
 decide +kernel
def cuts66730 : List PrefixCut := [⟨64,181357370,181357483⟩]
theorem checked66730 : checkPrefixCuts (2^48) 8750366721 10 Manual.Count131072.C066730.packed 64 cuts66730 = true := by
 decide +kernel
def cuts66731 : List PrefixCut := [⟨24,71506436,71506483⟩,
⟨64,183734993,183735108⟩]
theorem checked66731 : checkPrefixCuts (2^48) 8750497793 10 Manual.Count131072.C066731.packed 64 cuts66731 = true := by
 decide +kernel
def pointBounds66731 : List (Nat × Nat × Nat) := [(8750546944,115226656429537,115227045591120)]
theorem point_links_checked66731 : (cuts66731.take 1).map (fun c => (8750497793-1+2*2^10*c.k,115226584923101+c.lower,115226974084637+c.upper)) = pointBounds66731 := by
 decide +kernel
def cuts66732 : List PrefixCut := [⟨64,184343380,184343487⟩]
theorem checked66732 : checkPrefixCuts (2^48) 8750628865 10 Manual.Count131072.C066732.packed 64 cuts66732 = true := by
 decide +kernel
def cuts66733 : List PrefixCut := [⟨30,85657139,85657184⟩,
⟨64,185369921,185370024⟩]
theorem checked66733 : checkPrefixCuts (2^48) 8750759937 10 Manual.Count131072.C066733.packed 64 cuts66733 = true := by
 decide +kernel
def pointBounds66733 : List (Nat × Nat × Nat) := [(8750821376,115227038658613,115227427820416)]
theorem point_links_checked66733 : (cuts66733.take 1).map (fun c => (8750759937-1+2*2^10*c.k,115226953001474+c.lower,115227342163232+c.upper)) = pointBounds66733 := by
 decide +kernel
def cuts66734 : List PrefixCut := [⟨64,182279307,182279407⟩]
theorem checked66734 : checkPrefixCuts (2^48) 8750891009 10 Manual.Count131072.C066734.packed 64 cuts66734 = true := by
 decide +kernel
def cuts66735 : List PrefixCut := [⟨36,102347969,102348031⟩,
⟨64,183337994,183338103⟩]
theorem checked66735 : checkPrefixCuts (2^48) 8751022081 10 Manual.Count131072.C066735.packed 64 cuts66735 = true := by
 decide +kernel
def pointBounds66735 : List (Nat × Nat × Nat) := [(8751095808,115227422998671,115227812160694)]
theorem point_links_checked66735 : (cuts66735.take 1).map (fun c => (8751022081-1+2*2^10*c.k,115227320650702+c.lower,115227709812663+c.upper)) = pointBounds66735 := by
 decide +kernel
def cuts66736 : List PrefixCut := [⟨64,187034128,187034233⟩]
theorem checked66736 : checkPrefixCuts (2^48) 8751153153 10 Manual.Count131072.C066736.packed 64 cuts66736 = true := by
 decide +kernel
def cuts66737 : List PrefixCut := [⟨42,118909130,118909201⟩,
⟨64,182978701,182978811⟩]
theorem checked66737 : checkPrefixCuts (2^48) 8751284225 10 Manual.Count131072.C066737.packed 64 cuts66737 = true := by
 decide +kernel
def pointBounds66737 : List (Nat × Nat × Nat) := [(8751370240,115227809931954,115228199094200)]
theorem point_links_checked66737 : (cuts66737.take 1).map (fun c => (8751284225-1+2*2^10*c.k,115227691022824+c.lower,115228080184999+c.upper)) = pointBounds66737 := by
 decide +kernel
def cuts66738 : List PrefixCut := [⟨64,183233274,183233377⟩]
theorem checked66738 : checkPrefixCuts (2^48) 8751415297 10 Manual.Count131072.C066738.packed 64 cuts66738 = true := by
 decide +kernel
def cuts66739 : List PrefixCut := [⟨48,140004199,140004279⟩,
⟨64,184291897,184292003⟩]
theorem checked66739 : checkPrefixCuts (2^48) 8751546369 10 Manual.Count131072.C066739.packed 64 cuts66739 = true := by
 decide +kernel
def pointBounds66739 : List (Nat × Nat × Nat) := [(8751644672,115228197238998,115228586401466)]
theorem point_links_checked66739 : (cuts66739.take 1).map (fun c => (8751546369-1+2*2^10*c.k,115228057234799+c.lower,115228446397187+c.upper)) = pointBounds66739 := by
 decide +kernel
def cuts66740 : List PrefixCut := [⟨64,186090203,186090313⟩]
theorem checked66740 : checkPrefixCuts (2^48) 8751677441 10 Manual.Count131072.C066740.packed 64 cuts66740 = true := by
 decide +kernel
def cuts66741 : List PrefixCut := [⟨54,158299930,158300025⟩,
⟨64,185894470,185894581⟩]
theorem checked66741 : checkPrefixCuts (2^48) 8751808513 10 Manual.Count131072.C066741.packed 64 cuts66741 = true := by
 decide +kernel
def pointBounds66741 : List (Nat × Nat × Nat) := [(8751919104,115228585916829,115228975079528)]
theorem point_links_checked66741 : (cuts66741.take 1).map (fun c => (8751808513-1+2*2^10*c.k,115228427616899+c.lower,115228816779503+c.upper)) = pointBounds66741 := by
 decide +kernel
def cuts66742 : List PrefixCut := [⟨64,181356933,181357037⟩]
theorem checked66742 : checkPrefixCuts (2^48) 8751939585 10 Manual.Count131072.C066742.packed 64 cuts66742 = true := by
 decide +kernel
def cuts66743 : List PrefixCut := [⟨60,172349315,172349413⟩,
⟨64,184441656,184441761⟩]
theorem checked66743 : checkPrefixCuts (2^48) 8752070657 10 Manual.Count131072.C066743.packed 64 cuts66743 = true := by
 decide +kernel
def pointBounds66743 : List (Nat × Nat × Nat) := [(8752193536,115228967217617,115229356380534)]
theorem point_links_checked66743 : (cuts66743.take 1).map (fun c => (8752070657-1+2*2^10*c.k,115228794868302+c.lower,115229184031121+c.upper)) = pointBounds66743 := by
 decide +kernel
def cuts66744 : List PrefixCut := [⟨64,185468033,185468143⟩]
theorem checked66744 : checkPrefixCuts (2^48) 8752201729 10 Manual.Count131072.C066744.packed 64 cuts66744 = true := by
 decide +kernel
def cuts66745 : List PrefixCut := [⟨64,182152787,182152890⟩]
theorem checked66745 : checkPrefixCuts (2^48) 8752332801 10 Manual.Count131072.C066745.packed 64 cuts66745 = true := by
 decide +kernel
def cuts66746 : List PrefixCut := [⟨2,5434955,5434958⟩,
⟨64,184980077,184980182⟩]
theorem checked66746 : checkPrefixCuts (2^48) 8752463873 10 Manual.Count131072.C066746.packed 64 cuts66746 = true := by
 decide +kernel
def pointBounds66746 : List (Nat × Nat × Nat) := [(8752467968,115229352365733,115229741528873)]
theorem point_links_checked66746 : (cuts66746.take 1).map (fun c => (8752463873-1+2*2^10*c.k,115229346930778+c.lower,115229736093915+c.upper)) = pointBounds66746 := by
 decide +kernel
def cuts66747 : List PrefixCut := [⟨64,182211660,182211765⟩]
theorem checked66747 : checkPrefixCuts (2^48) 8752594945 10 Manual.Count131072.C066747.packed 64 cuts66747 = true := by
 decide +kernel
def cuts66748 : List PrefixCut := [⟨8,23572190,23572201⟩,
⟨64,183945478,183945585⟩]
theorem checked66748 : checkPrefixCuts (2^48) 8752726017 10 Manual.Count131072.C066748.packed 64 cuts66748 = true := by
 decide +kernel
def pointBounds66748 : List (Nat × Nat × Nat) := [(8752742400,115229737694705,115230126858063)]
theorem point_links_checked66748 : (cuts66748.take 1).map (fun c => (8752726017-1+2*2^10*c.k,115229714122515+c.lower,115230103285862+c.upper)) = pointBounds66748 := by
 decide +kernel
def cuts66749 : List PrefixCut := [⟨64,182945831,182945943⟩]
theorem checked66749 : checkPrefixCuts (2^48) 8752857089 10 Manual.Count131072.C066749.packed 64 cuts66749 = true := by
 decide +kernel
def cuts66750 : List PrefixCut := [⟨14,40775743,40775766⟩,
⟨64,184390170,184390278⟩]
theorem checked66750 : checkPrefixCuts (2^48) 8752988161 10 Manual.Count131072.C066750.packed 64 cuts66750 = true := by
 decide +kernel
def pointBounds66750 : List (Nat × Nat × Nat) := [(8753016832,115230121789567,115230510953156)]
theorem point_links_checked66750 : (cuts66750.take 1).map (fun c => (8752988161-1+2*2^10*c.k,115230081013824+c.lower,115230470177390+c.upper)) = pointBounds66750 := by
 decide +kernel
def cuts66751 : List PrefixCut := [⟨64,185673671,185673778⟩]
theorem checked66751 : checkPrefixCuts (2^48) 8753119233 10 Manual.Count131072.C066751.packed 64 cuts66751 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000210
