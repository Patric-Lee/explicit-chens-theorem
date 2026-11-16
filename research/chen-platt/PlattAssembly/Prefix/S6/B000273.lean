import PlattAssemblyKernel
import PlattCertificates.Count131072.C058736
import PlattCertificates.Count131072.C058737
import PlattCertificates.Count131072.C058738
import PlattCertificates.Count131072.C058739
import PlattCertificates.Count131072.C058740
import PlattCertificates.Count131072.C058741
import PlattCertificates.Count131072.C058742
import PlattCertificates.Count131072.C058743
import PlattCertificates.Count131072.C058744
import PlattCertificates.Count131072.C058745
import PlattCertificates.Count131072.C058746
import PlattCertificates.Count131072.C058747
import PlattCertificates.Count131072.C058748
import PlattCertificates.Count131072.C058749
import PlattCertificates.Count131072.C058750
import PlattCertificates.Count131072.C058751
import PlattCertificates.Count131072.C058752
import PlattCertificates.Count131072.C058753
import PlattCertificates.Count131072.C058754
import PlattCertificates.Count131072.C058755
import PlattCertificates.Count131072.C058756
import PlattCertificates.Count131072.C058757
import PlattCertificates.Count131072.C058758
import PlattCertificates.Count131072.C058759
import PlattCertificates.Count131072.C058760
import PlattCertificates.Count131072.C058761
import PlattCertificates.Count131072.C058762
import PlattCertificates.Count131072.C058763
import PlattCertificates.Count131072.C058764
import PlattCertificates.Count131072.C058765
import PlattCertificates.Count131072.C058766
import PlattCertificates.Count131072.C058767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000273
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58736 : List PrefixCut := [⟨64,207269847,207269969⟩]
theorem checked58736 : checkPrefixCuts (2^48) 7702577153 10 Manual.Count131072.C058736.packed 64 cuts58736 = true := by
 decide +kernel
def cuts58737 : List PrefixCut := [⟨34,112732564,112732630⟩,
⟨64,211578274,211578394⟩]
theorem checked58737 : checkPrefixCuts (2^48) 7702708225 10 Manual.Count131072.C058737.packed 64 cuts58737 = true := by
 decide +kernel
def pointBounds58737 : List (Nat × Nat × Nat) := [(7702777856,113654091765556,113654480022866)]
theorem point_links_checked58737 : (cuts58737.take 1).map (fun c => (7702708225-1+2*2^10*c.k,113653979032992+c.lower,113654367290236+c.upper)) = pointBounds58737 := by
 decide +kernel
def cuts58738 : List PrefixCut := [⟨64,207043562,207043684⟩]
theorem checked58738 : checkPrefixCuts (2^48) 7702839297 10 Manual.Count131072.C058738.packed 64 cuts58738 = true := by
 decide +kernel
def cuts58739 : List PrefixCut := [⟨24,78745789,78745833⟩,
⟨64,209561345,209561464⟩]
theorem checked58739 : checkPrefixCuts (2^48) 7702970369 10 Manual.Count131072.C058739.packed 64 cuts58739 = true := by
 decide +kernel
def pointBounds58739 : List (Nat × Nat × Nat) := [(7703019520,113654476400617,113654864658147)]
theorem point_links_checked58739 : (cuts58739.take 1).map (fun c => (7702970369-1+2*2^10*c.k,113654397654828+c.lower,113654785912314+c.upper)) = pointBounds58739 := by
 decide +kernel
def cuts58740 : List PrefixCut := [⟨64,210361680,210361795⟩]
theorem checked58740 : checkPrefixCuts (2^48) 7703101441 10 Manual.Count131072.C058740.packed 64 cuts58740 = true := by
 decide +kernel
def cuts58741 : List PrefixCut := [⟨14,46990146,46990172⟩,
⟨64,208859963,208860083⟩]
theorem checked58741 : checkPrefixCuts (2^48) 7703232513 10 Manual.Count131072.C058741.packed 64 cuts58741 = true := by
 decide +kernel
def pointBounds58741 : List (Nat × Nat × Nat) := [(7703261184,113654864567999,113655252825745)]
theorem point_links_checked58741 : (cuts58741.take 1).map (fun c => (7703232513-1+2*2^10*c.k,113654817577853+c.lower,113655205835573+c.upper)) = pointBounds58741 := by
 decide +kernel
def cuts58742 : List PrefixCut := [⟨64,210902580,210902699⟩]
theorem checked58742 : checkPrefixCuts (2^48) 7703363585 10 Manual.Count131072.C058742.packed 64 cuts58742 = true := by
 decide +kernel
def cuts58743 : List PrefixCut := [⟨4,12934657,12934664⟩,
⟨64,210679755,210679875⟩]
theorem checked58743 : checkPrefixCuts (2^48) 7703494657 10 Manual.Count131072.C058743.packed 64 cuts58743 = true := by
 decide +kernel
def pointBounds58743 : List (Nat × Nat × Nat) := [(7703502848,113655250275053,113655638533019)]
theorem point_links_checked58743 : (cuts58743.take 1).map (fun c => (7703494657-1+2*2^10*c.k,113655237340396+c.lower,113655625598355+c.upper)) = pointBounds58743 := by
 decide +kernel
def cuts58744 : List PrefixCut := [⟨58,189849854,189849964⟩,
⟨64,209580043,209580163⟩]
theorem checked58744 : checkPrefixCuts (2^48) 7703625729 10 Manual.Count131072.C058744.packed 64 cuts58744 = true := by
 decide +kernel
def pointBounds58744 : List (Nat × Nat × Nat) := [(7703744512,113655637870005,113656026128194)]
theorem point_links_checked58744 : (cuts58744.take 1).map (fun c => (7703625729-1+2*2^10*c.k,113655448020151+c.lower,113655836278230+c.upper)) = pointBounds58744 := by
 decide +kernel
def cuts58745 : List PrefixCut := [⟨64,210636059,210636181⟩]
theorem checked58745 : checkPrefixCuts (2^48) 7703756801 10 Manual.Count131072.C058745.packed 64 cuts58745 = true := by
 decide +kernel
def cuts58746 : List PrefixCut := [⟨48,159445295,159445387⟩,
⟨64,212313163,212313282⟩]
theorem checked58746 : checkPrefixCuts (2^48) 7703887873 10 Manual.Count131072.C058746.packed 64 cuts58746 = true := by
 decide +kernel
def pointBounds58746 : List (Nat × Nat × Nat) := [(7703986176,113656027681548,113656415939961)]
theorem point_links_checked58746 : (cuts58746.take 1).map (fun c => (7703887873-1+2*2^10*c.k,113655868236253+c.lower,113656256494574+c.upper)) = pointBounds58746 := by
 decide +kernel
def cuts58747 : List PrefixCut := [⟨64,209898159,209898279⟩]
theorem checked58747 : checkPrefixCuts (2^48) 7704018945 10 Manual.Count131072.C058747.packed 64 cuts58747 = true := by
 decide +kernel
def cuts58748 : List PrefixCut := [⟨38,124293108,124293178⟩,
⟨64,210259952,210260071⟩]
theorem checked58748 : checkPrefixCuts (2^48) 7704150017 10 Manual.Count131072.C058748.packed 64 cuts58748 = true := by
 decide +kernel
def pointBounds58748 : List (Nat × Nat × Nat) := [(7704227840,113656414740683,113656802999313)]
theorem point_links_checked58748 : (cuts58748.take 1).map (fun c => (7704150017-1+2*2^10*c.k,113656290447575+c.lower,113656678706135+c.upper)) = pointBounds58748 := by
 decide +kernel
def cuts58749 : List PrefixCut := [⟨64,207443208,207443328⟩]
theorem checked58749 : checkPrefixCuts (2^48) 7704281089 10 Manual.Count131072.C058749.packed 64 cuts58749 = true := by
 decide +kernel
def cuts58750 : List PrefixCut := [⟨28,92540901,92540954⟩,
⟨64,209302932,209303052⟩]
theorem checked58750 : checkPrefixCuts (2^48) 7704412161 10 Manual.Count131072.C058750.packed 64 cuts58750 = true := by
 decide +kernel
def pointBounds58750 : List (Nat × Nat × Nat) := [(7704469504,113656800691636,113657188950488)]
theorem point_links_checked58750 : (cuts58750.take 1).map (fun c => (7704412161-1+2*2^10*c.k,113656708150735+c.lower,113657096409534+c.upper)) = pointBounds58750 := by
 decide +kernel
def cuts58751 : List PrefixCut := [⟨64,207070838,207070956⟩]
theorem checked58751 : checkPrefixCuts (2^48) 7704543233 10 Manual.Count131072.C058751.packed 64 cuts58751 = true := by
 decide +kernel
def cuts58752 : List PrefixCut := [⟨18,60754238,60754273⟩,
⟨64,208820897,208821014⟩]
theorem checked58752 : checkPrefixCuts (2^48) 7704674305 10 Manual.Count131072.C058752.packed 64 cuts58752 = true := by
 decide +kernel
def pointBounds58752 : List (Nat × Nat × Nat) := [(7704711168,113657185278743,113657573537815)]
theorem point_links_checked58752 : (cuts58752.take 1).map (fun c => (7704674305-1+2*2^10*c.k,113657124524505+c.lower,113657512783542+c.upper)) = pointBounds58752 := by
 decide +kernel
def cuts58753 : List PrefixCut := [⟨64,209328782,209328902⟩]
theorem checked58753 : checkPrefixCuts (2^48) 7704805377 10 Manual.Count131072.C058753.packed 64 cuts58753 = true := by
 decide +kernel
def cuts58754 : List PrefixCut := [⟨8,25499142,25499157⟩,
⟨64,208704162,208704284⟩]
theorem checked58754 : checkPrefixCuts (2^48) 7704936449 10 Manual.Count131072.C058754.packed 64 cuts58754 = true := by
 decide +kernel
def pointBounds58754 : List (Nat × Nat × Nat) := [(7704952832,113657568173326,113657956432615)]
theorem point_links_checked58754 : (cuts58754.take 1).map (fun c => (7704936449-1+2*2^10*c.k,113657542674184+c.lower,113657930933458+c.upper)) = pointBounds58754 := by
 decide +kernel
def cuts58755 : List PrefixCut := [⟨62,206399244,206399361⟩,
⟨64,213084330,213084451⟩]
theorem checked58755 : checkPrefixCuts (2^48) 7705067521 10 Manual.Count131072.C058755.packed 64 cuts58755 = true := by
 decide +kernel
def pointBounds58755 : List (Nat × Nat × Nat) := [(7705194496,113657957777590,113658346037103)]
theorem point_links_checked58755 : (cuts58755.take 1).map (fun c => (7705067521-1+2*2^10*c.k,113657751378346+c.lower,113658139637742+c.upper)) = pointBounds58755 := by
 decide +kernel
def cuts58756 : List PrefixCut := [⟨64,208550944,208551063⟩]
theorem checked58756 : checkPrefixCuts (2^48) 7705198593 10 Manual.Count131072.C058756.packed 64 cuts58756 = true := by
 decide +kernel
def cuts58757 : List PrefixCut := [⟨52,173954179,173954276⟩,
⟨64,214793974,214794095⟩]
theorem checked58757 : checkPrefixCuts (2^48) 7705329665 10 Manual.Count131072.C058757.packed 64 cuts58757 = true := by
 decide +kernel
def pointBounds58757 : List (Nat × Nat × Nat) := [(7705436160,113658346967799,113658735227532)]
theorem point_links_checked58757 : (cuts58757.take 1).map (fun c => (7705329665-1+2*2^10*c.k,113658173013620+c.lower,113658561273256+c.upper)) = pointBounds58757 := by
 decide +kernel
def cuts58758 : List PrefixCut := [⟨64,210041547,210041667⟩]
theorem checked58758 : checkPrefixCuts (2^48) 7705460737 10 Manual.Count131072.C058758.packed 64 cuts58758 = true := by
 decide +kernel
def cuts58759 : List PrefixCut := [⟨42,136178058,136178138⟩,
⟨64,208905584,208905705⟩]
theorem checked58759 : checkPrefixCuts (2^48) 7705591809 10 Manual.Count131072.C058759.packed 64 cuts58759 = true := by
 decide +kernel
def pointBounds58759 : List (Nat × Nat × Nat) := [(7705677824,113658734027199,113659122287156)]
theorem point_links_checked58759 : (cuts58759.take 1).map (fun c => (7705591809-1+2*2^10*c.k,113658597849141+c.lower,113658986109018+c.upper)) = pointBounds58759 := by
 decide +kernel
def cuts58760 : List PrefixCut := [⟨64,209888290,209888410⟩]
theorem checked58760 : checkPrefixCuts (2^48) 7705722881 10 Manual.Count131072.C058760.packed 64 cuts58760 = true := by
 decide +kernel
def cuts58761 : List PrefixCut := [⟨32,104431426,104431488⟩,
⟨64,208241004,208241128⟩]
theorem checked58761 : checkPrefixCuts (2^48) 7705853953 10 Manual.Count131072.C058761.packed 64 cuts58761 = true := by
 decide +kernel
def pointBounds58761 : List (Nat × Nat × Nat) := [(7705919488,113659121074441,113659509334621)]
theorem point_links_checked58761 : (cuts58761.take 1).map (fun c => (7705853953-1+2*2^10*c.k,113659016643015+c.lower,113659404903133+c.upper)) = pointBounds58761 := by
 decide +kernel
def cuts58762 : List PrefixCut := [⟨64,211086533,211086650⟩]
theorem checked58762 : checkPrefixCuts (2^48) 7705985025 10 Manual.Count131072.C058762.packed 64 cuts58762 = true := by
 decide +kernel
def cuts58763 : List PrefixCut := [⟨22,72686868,72686908⟩,
⟨64,211375144,211375265⟩]
theorem checked58763 : checkPrefixCuts (2^48) 7706116097 10 Manual.Count131072.C058763.packed 64 cuts58763 = true := by
 decide +kernel
def pointBounds58763 : List (Nat × Nat × Nat) := [(7706161152,113659508657420,113659896917819)]
theorem point_links_checked58763 : (cuts58763.take 1).map (fun c => (7706116097-1+2*2^10*c.k,113659435970552+c.lower,113659824230911+c.upper)) = pointBounds58763 := by
 decide +kernel
def cuts58764 : List PrefixCut := [⟨64,208449535,208449655⟩]
theorem checked58764 : checkPrefixCuts (2^48) 7706247169 10 Manual.Count131072.C058764.packed 64 cuts58764 = true := by
 decide +kernel
def cuts58765 : List PrefixCut := [⟨12,40250404,40250428⟩,
⟨64,210893146,210893264⟩]
theorem checked58765 : checkPrefixCuts (2^48) 7706378241 10 Manual.Count131072.C058765.packed 64 cuts58765 = true := by
 decide +kernel
def pointBounds58765 : List (Nat × Nat × Nat) := [(7706402816,113659896045635,113660284306259)]
theorem point_links_checked58765 : (cuts58765.take 1).map (fun c => (7706378241-1+2*2^10*c.k,113659855795231+c.lower,113660244055831+c.upper)) = pointBounds58765 := by
 decide +kernel
def cuts58766 : List PrefixCut := [⟨64,209939914,209940037⟩]
theorem checked58766 : checkPrefixCuts (2^48) 7706509313 10 Manual.Count131072.C058766.packed 64 cuts58766 = true := by
 decide +kernel
def cuts58767 : List PrefixCut := [⟨2,6282072,6282075⟩,
⟨64,210228524,210228644⟩]
theorem checked58767 : checkPrefixCuts (2^48) 7706640385 10 Manual.Count131072.C058767.packed 64 cuts58767 = true := by
 decide +kernel
def pointBounds58767 : List (Nat × Nat × Nat) := [(7706644480,113660282910363,113660671171207)]
theorem point_links_checked58767 : (cuts58767.take 1).map (fun c => (7706640385-1+2*2^10*c.k,113660276628291+c.lower,113660664889132+c.upper)) = pointBounds58767 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000273
