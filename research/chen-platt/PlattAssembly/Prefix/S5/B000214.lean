import PlattAssemblyKernel
import PlattCertificates.Count131072.C046848
import PlattCertificates.Count131072.C046849
import PlattCertificates.Count131072.C046850
import PlattCertificates.Count131072.C046851
import PlattCertificates.Count131072.C046852
import PlattCertificates.Count131072.C046853
import PlattCertificates.Count131072.C046854
import PlattCertificates.Count131072.C046855
import PlattCertificates.Count131072.C046856
import PlattCertificates.Count131072.C046857
import PlattCertificates.Count131072.C046858
import PlattCertificates.Count131072.C046859
import PlattCertificates.Count131072.C046860
import PlattCertificates.Count131072.C046861
import PlattCertificates.Count131072.C046862
import PlattCertificates.Count131072.C046863
import PlattCertificates.Count131072.C046864
import PlattCertificates.Count131072.C046865
import PlattCertificates.Count131072.C046866
import PlattCertificates.Count131072.C046867
import PlattCertificates.Count131072.C046868
import PlattCertificates.Count131072.C046869
import PlattCertificates.Count131072.C046870
import PlattCertificates.Count131072.C046871
import PlattCertificates.Count131072.C046872
import PlattCertificates.Count131072.C046873
import PlattCertificates.Count131072.C046874
import PlattCertificates.Count131072.C046875
import PlattCertificates.Count131072.C046876
import PlattCertificates.Count131072.C046877
import PlattCertificates.Count131072.C046878
import PlattCertificates.Count131072.C046879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000214
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46848 : List PrefixCut := [⟨8,32570894,32570914⟩,
⟨64,266703221,266703375⟩]
theorem checked46848 : checkPrefixCuts (2^48) 6144393217 10 Manual.Count131072.C046848.packed 64 cuts46848 = true := by
 decide +kernel
def pointBounds46848 : List (Nat × Nat × Nat) := [(6144409600,110845420791957,110845807450285)]
theorem point_links_checked46848 : (cuts46848.take 1).map (fun c => (6144393217-1+2*2^10*c.k,110845388221063+c.lower,110845774879371+c.upper)) = pointBounds46848 := by
 decide +kernel
def cuts46849 : List PrefixCut := [⟨38,159735196,159735287⟩,
⟨64,266285267,266285415⟩]
theorem checked46849 : checkPrefixCuts (2^48) 6144524289 10 Manual.Count131072.C046849.packed 64 cuts46849 = true := by
 decide +kernel
def pointBounds46849 : List (Nat × Nat × Nat) := [(6144602112,110845814659480,110846201318033)]
theorem point_links_checked46849 : (cuts46849.take 1).map (fun c => (6144524289-1+2*2^10*c.k,110845654924284+c.lower,110846041582746+c.upper)) = pointBounds46849 := by
 decide +kernel
def cuts46850 : List PrefixCut := [⟨64,268890580,268890732⟩]
theorem checked46850 : checkPrefixCuts (2^48) 6144655361 10 Manual.Count131072.C046850.packed 64 cuts46850 = true := by
 decide +kernel
def cuts46851 : List PrefixCut := [⟨4,15803442,15803451⟩,
⟨64,267098357,267098514⟩]
theorem checked46851 : checkPrefixCuts (2^48) 6144786433 10 Manual.Count131072.C046851.packed 64 cuts46851 = true := by
 decide +kernel
def pointBounds46851 : List (Nat × Nat × Nat) := [(6144794624,110846205903573,110846592562344)]
theorem point_links_checked46851 : (cuts46851.take 1).map (fun c => (6144786433-1+2*2^10*c.k,110846190100131+c.lower,110846576758893+c.upper)) = pointBounds46851 := by
 decide +kernel
def cuts46852 : List PrefixCut := [⟨34,143097538,143097615⟩,
⟨64,269749416,269749565⟩]
theorem checked46852 : checkPrefixCuts (2^48) 6144917505 10 Manual.Count131072.C046852.packed 64 cuts46852 = true := by
 decide +kernel
def pointBounds46852 : List (Nat × Nat × Nat) := [(6144987136,110846600296026,110846986955022)]
theorem point_links_checked46852 : (cuts46852.take 1).map (fun c => (6144917505-1+2*2^10*c.k,110846457198488+c.lower,110846843857407+c.upper)) = pointBounds46852 := by
 decide +kernel
def cuts46853 : List PrefixCut := [⟨64,264934205,264934353⟩]
theorem checked46853 : checkPrefixCuts (2^48) 6145048577 10 Manual.Count131072.C046853.packed 64 cuts46853 = true := by
 decide +kernel
def pointBounds46853 : List (Nat × Nat × Nat) := [(6145179648,110846991882109,110847378541325)]
theorem point_links_checked46853 : (cuts46853.take 1).map (fun c => (6145048577-1+2*2^10*c.k,110846726947904+c.lower,110847113606972+c.upper)) = pointBounds46853 := by
 decide +kernel
def cuts46854 : List PrefixCut := [⟨64,262317725,262317879⟩]
theorem checked46854 : checkPrefixCuts (2^48) 6145179649 10 Manual.Count131072.C046854.packed 64 cuts46854 = true := by
 decide +kernel
def cuts46855 : List PrefixCut := [⟨30,124996314,124996385⟩,
⟨64,265747340,265747493⟩]
theorem checked46855 : checkPrefixCuts (2^48) 6145310721 10 Manual.Count131072.C046855.packed 64 cuts46855 = true := by
 decide +kernel
def pointBounds46855 : List (Nat × Nat × Nat) := [(6145372160,110847379196148,110847765855589)]
theorem point_links_checked46855 : (cuts46855.take 1).map (fun c => (6145310721-1+2*2^10*c.k,110847254199834+c.lower,110847640859204+c.upper)) = pointBounds46855 := by
 decide +kernel
def cuts46856 : List PrefixCut := [⟨60,243253163,243253305⟩,
⟨64,259924828,259924979⟩]
theorem checked46856 : checkPrefixCuts (2^48) 6145441793 10 Manual.Count131072.C046856.packed 64 cuts46856 = true := by
 decide +kernel
def pointBounds46856 : List (Nat × Nat × Nat) := [(6145564672,110847763200337,110848149860002)]
theorem point_links_checked46856 : (cuts46856.take 1).map (fun c => (6145441793-1+2*2^10*c.k,110847519947174+c.lower,110847906606697+c.upper)) = pointBounds46856 := by
 decide +kernel
def cuts46857 : List PrefixCut := [⟨64,263308554,263308703⟩]
theorem checked46857 : checkPrefixCuts (2^48) 6145572865 10 Manual.Count131072.C046857.packed 64 cuts46857 = true := by
 decide +kernel
def cuts46858 : List PrefixCut := [⟨26,107767559,107767622⟩,
⟨64,267150105,267150261⟩]
theorem checked46858 : checkPrefixCuts (2^48) 6145703937 10 Manual.Count131072.C046858.packed 64 cuts46858 = true := by
 decide +kernel
def pointBounds46858 : List (Nat × Nat × Nat) := [(6145757184,110848150948115,110848537608001)]
theorem point_links_checked46858 : (cuts46858.take 1).map (fun c => (6145703937-1+2*2^10*c.k,110848043180556+c.lower,110848429840379+c.upper)) = pointBounds46858 := by
 decide +kernel
def cuts46859 : List PrefixCut := [⟨56,230688891,230689028⟩,
⟨64,264488092,264488249⟩]
theorem checked46859 : checkPrefixCuts (2^48) 6145835009 10 Manual.Count131072.C046859.packed 64 cuts46859 = true := by
 decide +kernel
def pointBounds46859 : List (Nat × Nat × Nat) := [(6145949696,110848541019552,110848927679668)]
theorem point_links_checked46859 : (cuts46859.take 1).map (fun c => (6145835009-1+2*2^10*c.k,110848310330661+c.lower,110848696990640+c.upper)) = pointBounds46859 := by
 decide +kernel
def cuts46860 : List PrefixCut := [⟨64,269794994,269795150⟩]
theorem checked46860 : checkPrefixCuts (2^48) 6145966081 10 Manual.Count131072.C046860.packed 64 cuts46860 = true := by
 decide +kernel
def cuts46861 : List PrefixCut := [⟨22,90403618,90403666⟩,
⟨64,265072165,265072313⟩]
theorem checked46861 : checkPrefixCuts (2^48) 6146097153 10 Manual.Count131072.C046861.packed 64 cuts46861 = true := by
 decide +kernel
def pointBounds46861 : List (Nat × Nat × Nat) := [(6146142208,110848935017365,110849321677705)]
theorem point_links_checked46861 : (cuts46861.take 1).map (fun c => (6146097153-1+2*2^10*c.k,110848844613747+c.lower,110849231274039+c.upper)) = pointBounds46861 := by
 decide +kernel
def cuts46862 : List PrefixCut := [⟨52,215149449,215149574⟩,
⟨64,264059017,264059172⟩]
theorem checked46862 : checkPrefixCuts (2^48) 6146228225 10 Manual.Count131072.C046862.packed 64 cuts46862 = true := by
 decide +kernel
def pointBounds46862 : List (Nat × Nat × Nat) := [(6146334720,110849324835361,110849711495926)]
theorem point_links_checked46862 : (cuts46862.take 1).map (fun c => (6146228225-1+2*2^10*c.k,110849109685912+c.lower,110849496346352+c.upper)) = pointBounds46862 := by
 decide +kernel
def cuts46863 : List PrefixCut := [⟨64,264236526,264236680⟩]
theorem checked46863 : checkPrefixCuts (2^48) 6146359297 10 Manual.Count131072.C046863.packed 64 cuts46863 = true := by
 decide +kernel
def cuts46864 : List PrefixCut := [⟨18,73041866,73041907⟩,
⟨64,264917823,264917973⟩]
theorem checked46864 : checkPrefixCuts (2^48) 6146490369 10 Manual.Count131072.C046864.packed 64 cuts46864 = true := by
 decide +kernel
def pointBounds46864 : List (Nat × Nat × Nat) := [(6146527232,110849711023321,110850097684111)]
theorem point_links_checked46864 : (cuts46864.take 1).map (fun c => (6146490369-1+2*2^10*c.k,110849637981455+c.lower,110850024642204+c.upper)) = pointBounds46864 := by
 decide +kernel
def cuts46865 : List PrefixCut := [⟨48,197184931,197185048⟩,
⟨64,263584169,263584324⟩]
theorem checked46865 : checkPrefixCuts (2^48) 6146621441 10 Manual.Count131072.C046865.packed 64 cuts46865 = true := by
 decide +kernel
def pointBounds46865 : List (Nat × Nat × Nat) := [(6146719744,110850100084209,110850486745225)]
theorem point_links_checked46865 : (cuts46865.take 1).map (fun c => (6146621441-1+2*2^10*c.k,110849902899278+c.lower,110850289560177+c.upper)) = pointBounds46865 := by
 decide +kernel
def cuts46866 : List PrefixCut := [⟨64,265776577,265776726⟩]
theorem checked46866 : checkPrefixCuts (2^48) 6146752513 10 Manual.Count131072.C046866.packed 64 cuts46866 = true := by
 decide +kernel
def cuts46867 : List PrefixCut := [⟨14,56552345,56552378⟩,
⟨64,262428169,262428319⟩]
theorem checked46867 : checkPrefixCuts (2^48) 6146883585 10 Manual.Count131072.C046867.packed 64 cuts46867 = true := by
 decide +kernel
def pointBounds46867 : List (Nat × Nat × Nat) := [(6146912256,110850488812369,110850875473605)]
theorem point_links_checked46867 : (cuts46867.take 1).map (fun c => (6146883585-1+2*2^10*c.k,110850432260024+c.lower,110850818921227+c.upper)) = pointBounds46867 := by
 decide +kernel
def cuts46868 : List PrefixCut := [⟨44,183069110,183069210⟩,
⟨64,267505285,267505432⟩]
theorem checked46868 : checkPrefixCuts (2^48) 6147014657 10 Manual.Count131072.C046868.packed 64 cuts46868 = true := by
 decide +kernel
def pointBounds46868 : List (Nat × Nat × Nat) := [(6147104768,110850877757303,110851264418756)]
theorem point_links_checked46868 : (cuts46868.take 1).map (fun c => (6147014657-1+2*2^10*c.k,110850694688193+c.lower,110851081349546+c.upper)) = pointBounds46868 := by
 decide +kernel
def cuts46869 : List PrefixCut := [⟨64,267041661,267041809⟩]
theorem checked46869 : checkPrefixCuts (2^48) 6147145729 10 Manual.Count131072.C046869.packed 64 cuts46869 = true := by
 decide +kernel
def cuts46870 : List PrefixCut := [⟨10,42079606,42079630⟩,
⟨64,266166010,266166162⟩]
theorem checked46870 : checkPrefixCuts (2^48) 6147276801 10 Manual.Count131072.C046870.packed 64 cuts46870 = true := by
 decide +kernel
def pointBounds46870 : List (Nat × Nat × Nat) := [(6147297280,110851271314745,110851657976417)]
theorem point_links_checked46870 : (cuts46870.take 1).map (fun c => (6147276801-1+2*2^10*c.k,110851229235139+c.lower,110851615896787+c.upper)) = pointBounds46870 := by
 decide +kernel
def cuts46871 : List PrefixCut := [⟨40,166390932,166391027⟩,
⟨64,264695151,264695304⟩]
theorem checked46871 : checkPrefixCuts (2^48) 6147407873 10 Manual.Count131072.C046871.packed 64 cuts46871 = true := by
 decide +kernel
def pointBounds46871 : List (Nat × Nat × Nat) := [(6147489792,110851661792081,110852048453976)]
theorem point_links_checked46871 : (cuts46871.take 1).map (fun c => (6147407873-1+2*2^10*c.k,110851495401149+c.lower,110851882062949+c.upper)) = pointBounds46871 := by
 decide +kernel
def cuts46872 : List PrefixCut := [⟨64,265971503,265971658⟩]
theorem checked46872 : checkPrefixCuts (2^48) 6147538945 10 Manual.Count131072.C046872.packed 64 cuts46872 = true := by
 decide +kernel
def cuts46873 : List PrefixCut := [⟨6,25044710,25044724⟩,
⟨64,269994940,269995090⟩]
theorem checked46873 : checkPrefixCuts (2^48) 6147670017 10 Manual.Count131072.C046873.packed 64 cuts46873 = true := by
 decide +kernel
def pointBounds46873 : List (Nat × Nat × Nat) := [(6147682304,110852051112513,110852437774635)]
theorem point_links_checked46873 : (cuts46873.take 1).map (fun c => (6147670017-1+2*2^10*c.k,110852026067803+c.lower,110852412729911+c.upper)) = pointBounds46873 := by
 decide +kernel
def cuts46874 : List PrefixCut := [⟨36,150767933,150768018⟩,
⟨64,267928893,267929049⟩]
theorem checked46874 : checkPrefixCuts (2^48) 6147801089 10 Manual.Count131072.C046874.packed 64 cuts46874 = true := by
 decide +kernel
def pointBounds46874 : List (Nat × Nat × Nat) := [(6147874816,110852446830676,110852833493019)]
theorem point_links_checked46874 : (cuts46874.take 1).map (fun c => (6147801089-1+2*2^10*c.k,110852296062743+c.lower,110852682725001+c.upper)) = pointBounds46874 := by
 decide +kernel
def cuts46875 : List PrefixCut := [⟨64,266183422,266183575⟩]
theorem checked46875 : checkPrefixCuts (2^48) 6147932161 10 Manual.Count131072.C046875.packed 64 cuts46875 = true := by
 decide +kernel
def cuts46876 : List PrefixCut := [⟨2,7874621,7874625⟩,
⟨64,266589774,266589931⟩]
theorem checked46876 : checkPrefixCuts (2^48) 6148063233 10 Manual.Count131072.C046876.packed 64 cuts46876 = true := by
 decide +kernel
def pointBounds46876 : List (Nat × Nat × Nat) := [(6148067328,110852838049679,110853224712250)]
theorem point_links_checked46876 : (cuts46876.take 1).map (fun c => (6148063233-1+2*2^10*c.k,110852830175058+c.lower,110853216837625+c.upper)) = pointBounds46876 := by
 decide +kernel
def cuts46877 : List PrefixCut := [⟨32,132537368,132537441⟩,
⟨64,265393792,265393940⟩]
theorem checked46877 : checkPrefixCuts (2^48) 6148194305 10 Manual.Count131072.C046877.packed 64 cuts46877 = true := by
 decide +kernel
def pointBounds46877 : List (Nat × Nat × Nat) := [(6148259840,110853229302200,110853615964997)]
theorem point_links_checked46877 : (cuts46877.take 1).map (fun c => (6148194305-1+2*2^10*c.k,110853096764832+c.lower,110853483427556+c.upper)) = pointBounds46877 := by
 decide +kernel
def cuts46878 : List PrefixCut := [⟨62,261359569,261359716⟩,
⟨64,269691489,269691641⟩]
theorem checked46878 : checkPrefixCuts (2^48) 6148325377 10 Manual.Count131072.C046878.packed 64 cuts46878 = true := by
 decide +kernel
def pointBounds46878 : List (Nat × Nat × Nat) := [(6148452352,110853623518193,110854010181212)]
theorem point_links_checked46878 : (cuts46878.take 1).map (fun c => (6148325377-1+2*2^10*c.k,110853362158624+c.lower,110853748821496+c.upper)) = pointBounds46878 := by
 decide +kernel
def cuts46879 : List PrefixCut := [⟨64,267534112,267534264⟩]
theorem checked46879 : checkPrefixCuts (2^48) 6148456449 10 Manual.Count131072.C046879.packed 64 cuts46879 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000214
