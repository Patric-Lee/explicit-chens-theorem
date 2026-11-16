import PlattAssemblyKernel
import PlattCertificates.Count131072.C063040
import PlattCertificates.Count131072.C063041
import PlattCertificates.Count131072.C063042
import PlattCertificates.Count131072.C063043
import PlattCertificates.Count131072.C063044
import PlattCertificates.Count131072.C063045
import PlattCertificates.Count131072.C063046
import PlattCertificates.Count131072.C063047
import PlattCertificates.Count131072.C063048
import PlattCertificates.Count131072.C063049
import PlattCertificates.Count131072.C063050
import PlattCertificates.Count131072.C063051
import PlattCertificates.Count131072.C063052
import PlattCertificates.Count131072.C063053
import PlattCertificates.Count131072.C063054
import PlattCertificates.Count131072.C063055
import PlattCertificates.Count131072.C063056
import PlattCertificates.Count131072.C063057
import PlattCertificates.Count131072.C063058
import PlattCertificates.Count131072.C063059
import PlattCertificates.Count131072.C063060
import PlattCertificates.Count131072.C063061
import PlattCertificates.Count131072.C063062
import PlattCertificates.Count131072.C063063
import PlattCertificates.Count131072.C063064
import PlattCertificates.Count131072.C063065
import PlattCertificates.Count131072.C063066
import PlattCertificates.Count131072.C063067
import PlattCertificates.Count131072.C063068
import PlattCertificates.Count131072.C063069
import PlattCertificates.Count131072.C063070
import PlattCertificates.Count131072.C063071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63040 : List PrefixCut := [⟨9,28465098,28465115⟩,
⟨64,197075216,197075330⟩]
theorem checked63040 : checkPrefixCuts (2^48) 8266711041 10 Manual.Count131072.C063040.packed 64 cuts63040 = true := by
 decide +kernel
def pointBounds63040 : List (Nat × Nat × Nat) := [(8266729472,114526461635087,114526850391755)]
theorem point_links_checked63040 : (cuts63040.take 1).map (fun c => (8266711041-1+2*2^10*c.k,114526433169989+c.lower,114526821926640+c.upper)) = pointBounds63040 := by
 decide +kernel
def cuts63041 : List PrefixCut := [⟨64,197106113,197106228⟩]
theorem checked63041 : checkPrefixCuts (2^48) 8266842113 10 Manual.Count131072.C063041.packed 64 cuts63041 = true := by
 decide +kernel
def cuts63042 : List PrefixCut := [⟨8,24037948,24037964⟩,
⟨64,194583464,194583581⟩]
theorem checked63042 : checkPrefixCuts (2^48) 8266973185 10 Manual.Count131072.C063042.packed 64 cuts63042 = true := by
 decide +kernel
def pointBounds63042 : List (Nat × Nat × Nat) := [(8266989568,114526851389266,114527240146162)]
theorem point_links_checked63042 : (cuts63042.take 1).map (fun c => (8266973185-1+2*2^10*c.k,114526827351318+c.lower,114527216108198+c.upper)) = pointBounds63042 := by
 decide +kernel
def cuts63043 : List PrefixCut := [⟨64,195635835,195635948⟩]
theorem checked63043 : checkPrefixCuts (2^48) 8267104257 10 Manual.Count131072.C063043.packed 64 cuts63043 = true := by
 decide +kernel
def cuts63044 : List PrefixCut := [⟨7,21926275,21926287⟩,
⟨64,196790333,196790449⟩]
theorem checked63044 : checkPrefixCuts (2^48) 8267235329 10 Manual.Count131072.C063044.packed 64 cuts63044 = true := by
 decide +kernel
def pointBounds63044 : List (Nat × Nat × Nat) := [(8267249664,114527239496892,114527628254014)]
theorem point_links_checked63044 : (cuts63044.take 1).map (fun c => (8267235329-1+2*2^10*c.k,114527217570617+c.lower,114527606327727+c.upper)) = pointBounds63044 := by
 decide +kernel
def cuts63045 : List PrefixCut := [⟨64,197059590,197059701⟩]
theorem checked63045 : checkPrefixCuts (2^48) 8267366401 10 Manual.Count131072.C063045.packed 64 cuts63045 = true := by
 decide +kernel
def cuts63046 : List PrefixCut := [⟨6,18418851,18418862⟩,
⟨64,198077820,198077932⟩]
theorem checked63046 : checkPrefixCuts (2^48) 8267497473 10 Manual.Count131072.C063046.packed 64 cuts63046 = true := by
 decide +kernel
def pointBounds63046 : List (Nat × Nat × Nat) := [(8267509760,114527629839391,114528018596739)]
theorem point_links_checked63046 : (cuts63046.take 1).map (fun c => (8267497473-1+2*2^10*c.k,114527611420540+c.lower,114528000177877+c.upper)) = pointBounds63046 := by
 decide +kernel
def cuts63047 : List PrefixCut := [⟨64,194057364,194057478⟩]
theorem checked63047 : checkPrefixCuts (2^48) 8267628545 10 Manual.Count131072.C063047.packed 64 cuts63047 = true := by
 decide +kernel
def cuts63048 : List PrefixCut := [⟨5,15660635,15660645⟩,
⟨64,195518201,195518315⟩]
theorem checked63048 : checkPrefixCuts (2^48) 8267759617 10 Manual.Count131072.C063048.packed 64 cuts63048 = true := by
 decide +kernel
def pointBounds63048 : List (Nat × Nat × Nat) := [(8267769856,114528019216359,114528407973932)]
theorem point_links_checked63048 : (cuts63048.take 1).map (fun c => (8267759617-1+2*2^10*c.k,114528003555724+c.lower,114528392313287+c.upper)) = pointBounds63048 := by
 decide +kernel
def cuts63049 : List PrefixCut := [⟨64,195617240,195617349⟩]
theorem checked63049 : checkPrefixCuts (2^48) 8267890689 10 Manual.Count131072.C063049.packed 64 cuts63049 = true := by
 decide +kernel
def cuts63050 : List PrefixCut := [⟨4,13038771,13038776⟩,
⟨64,195103502,195103610⟩]
theorem checked63050 : checkPrefixCuts (2^48) 8268021761 10 Manual.Count131072.C063050.packed 64 cuts63050 = true := by
 decide +kernel
def pointBounds63050 : List (Nat × Nat × Nat) := [(8268029952,114528407729936,114528796487727)]
theorem point_links_checked63050 : (cuts63050.take 1).map (fun c => (8268021761-1+2*2^10*c.k,114528394691165+c.lower,114528783448951+c.upper)) = pointBounds63050 := by
 decide +kernel
def cuts63051 : List PrefixCut := [⟨64,194113138,194113251⟩]
theorem checked63051 : checkPrefixCuts (2^48) 8268152833 10 Manual.Count131072.C063051.packed 64 cuts63051 = true := by
 decide +kernel
def cuts63052 : List PrefixCut := [⟨3,9634087,9634093⟩,
⟨64,196050488,196050604⟩]
theorem checked63052 : checkPrefixCuts (2^48) 8268283905 10 Manual.Count131072.C063052.packed 64 cuts63052 = true := by
 decide +kernel
def pointBounds63052 : List (Nat × Nat × Nat) := [(8268290048,114528793541892,114529182299905)]
theorem point_links_checked63052 : (cuts63052.take 1).map (fun c => (8268283905-1+2*2^10*c.k,114528783907805+c.lower,114529172665812+c.upper)) = pointBounds63052 := by
 decide +kernel
def cuts63053 : List PrefixCut := [⟨64,194345265,194345381⟩]
theorem checked63053 : checkPrefixCuts (2^48) 8268414977 10 Manual.Count131072.C063053.packed 64 cuts63053 = true := by
 decide +kernel
def cuts63054 : List PrefixCut := [⟨2,5446662,5446664⟩,
⟨64,192299711,192299815⟩]
theorem checked63054 : checkPrefixCuts (2^48) 8268546049 10 Manual.Count131072.C063054.packed 64 cuts63054 = true := by
 decide +kernel
def pointBounds63054 : List (Nat × Nat × Nat) := [(8268550144,114529179750220,114529568508461)]
theorem point_links_checked63054 : (cuts63054.take 1).map (fun c => (8268546049-1+2*2^10*c.k,114529174303558+c.lower,114529563061797+c.upper)) = pointBounds63054 := by
 decide +kernel
def cuts63055 : List PrefixCut := [⟨64,196041166,196041282⟩]
theorem checked63055 : checkPrefixCuts (2^48) 8268677121 10 Manual.Count131072.C063055.packed 64 cuts63055 = true := by
 decide +kernel
def cuts63056 : List PrefixCut := [⟨1,3438097,3438098⟩,
⟨64,195595535,195595645⟩]
theorem checked63056 : checkPrefixCuts (2^48) 8268808193 10 Manual.Count131072.C063056.packed 64 cuts63056 = true := by
 decide +kernel
def pointBounds63056 : List (Nat × Nat × Nat) := [(8268810240,114529566082532,114529954840992)]
theorem point_links_checked63056 : (cuts63056.take 1).map (fun c => (8268808193-1+2*2^10*c.k,114529562644435+c.lower,114529951402894+c.upper)) = pointBounds63056 := by
 decide +kernel
def cuts63057 : List PrefixCut := [⟨64,195320118,195320230⟩]
theorem checked63057 : checkPrefixCuts (2^48) 8268939265 10 Manual.Count131072.C063057.packed 64 cuts63057 = true := by
 decide +kernel
def pointBounds63057 : List (Nat × Nat × Nat) := [(8269070336,114529953560088,114530342318769)]
theorem point_links_checked63057 : (cuts63057.take 1).map (fun c => (8268939265-1+2*2^10*c.k,114529758239970+c.lower,114530146998539+c.upper)) = pointBounds63057 := by
 decide +kernel
def cuts63058 : List PrefixCut := [⟨64,195997793,195997907⟩]
theorem checked63058 : checkPrefixCuts (2^48) 8269070337 10 Manual.Count131072.C063058.packed 64 cuts63058 = true := by
 decide +kernel
def cuts63059 : List PrefixCut := [⟨63,193543933,193544041⟩,
⟨64,196879697,196879807⟩]
theorem checked63059 : checkPrefixCuts (2^48) 8269201409 10 Manual.Count131072.C063059.packed 64 cuts63059 = true := by
 decide +kernel
def pointBounds63059 : List (Nat × Nat × Nat) := [(8269330432,114530343101814,114530731860717)]
theorem point_links_checked63059 : (cuts63059.take 1).map (fun c => (8269201409-1+2*2^10*c.k,114530149557881+c.lower,114530538316676+c.upper)) = pointBounds63059 := by
 decide +kernel
def cuts63060 : List PrefixCut := [⟨64,193779110,193779220⟩]
theorem checked63060 : checkPrefixCuts (2^48) 8269332481 10 Manual.Count131072.C063060.packed 64 cuts63060 = true := by
 decide +kernel
def cuts63061 : List PrefixCut := [⟨62,189827736,189827846⟩,
⟨64,196294830,196294944⟩]
theorem checked63061 : checkPrefixCuts (2^48) 8269463553 10 Manual.Count131072.C063061.packed 64 cuts63061 = true := by
 decide +kernel
def pointBounds63061 : List (Nat × Nat × Nat) := [(8269590528,114530730044424,114531118803549)]
theorem point_links_checked63061 : (cuts63061.take 1).map (fun c => (8269463553-1+2*2^10*c.k,114530540216688+c.lower,114530928975703+c.upper)) = pointBounds63061 := by
 decide +kernel
def cuts63062 : List PrefixCut := [⟨64,196019425,196019534⟩]
theorem checked63062 : checkPrefixCuts (2^48) 8269594625 10 Manual.Count131072.C063062.packed 64 cuts63062 = true := by
 decide +kernel
def cuts63063 : List PrefixCut := [⟨61,186724405,186724517⟩,
⟨64,196390703,196390820⟩]
theorem checked63063 : checkPrefixCuts (2^48) 8269725697 10 Manual.Count131072.C063063.packed 64 cuts63063 = true := by
 decide +kernel
def pointBounds63063 : List (Nat × Nat × Nat) := [(8269850624,114531119255348,114531508014698)]
theorem point_links_checked63063 : (cuts63063.take 1).map (fun c => (8269725697-1+2*2^10*c.k,114530932530943+c.lower,114531321290181+c.upper)) = pointBounds63063 := by
 decide +kernel
def cuts63064 : List PrefixCut := [⟨64,194413501,194413619⟩]
theorem checked63064 : checkPrefixCuts (2^48) 8269856769 10 Manual.Count131072.C063064.packed 64 cuts63064 = true := by
 decide +kernel
def cuts63065 : List PrefixCut := [⟨60,181545113,181545218⟩,
⟨64,193355323,193355435⟩]
theorem checked63065 : checkPrefixCuts (2^48) 8269987841 10 Manual.Count131072.C063065.packed 64 cuts63065 = true := by
 decide +kernel
def pointBounds63065 : List (Nat × Nat × Nat) := [(8270110720,114531504880260,114531893639838)]
theorem point_links_checked63065 : (cuts63065.take 1).map (fun c => (8269987841-1+2*2^10*c.k,114531323335147+c.lower,114531712094620+c.upper)) = pointBounds63065 := by
 decide +kernel
def cuts63066 : List PrefixCut := [⟨64,196687684,196687793⟩]
theorem checked63066 : checkPrefixCuts (2^48) 8270118913 10 Manual.Count131072.C063066.packed 64 cuts63066 = true := by
 decide +kernel
def cuts63067 : List PrefixCut := [⟨59,181335184,181335288⟩,
⟨64,196888773,196888887⟩]
theorem checked63067 : checkPrefixCuts (2^48) 8270249985 10 Manual.Count131072.C063067.packed 64 cuts63067 = true := by
 decide +kernel
def pointBounds63067 : List (Nat × Nat × Nat) := [(8270370816,114531894713338,114532283473136)]
theorem point_links_checked63067 : (cuts63067.take 1).map (fun c => (8270249985-1+2*2^10*c.k,114531713378154+c.lower,114532102137848+c.upper)) = pointBounds63067 := by
 decide +kernel
def cuts63068 : List PrefixCut := [⟨64,193516306,193516415⟩]
theorem checked63068 : checkPrefixCuts (2^48) 8270381057 10 Manual.Count131072.C063068.packed 64 cuts63068 = true := by
 decide +kernel
def cuts63069 : List PrefixCut := [⟨58,176326553,176326648⟩,
⟨64,194227930,194228037⟩]
theorem checked63069 : checkPrefixCuts (2^48) 8270512129 10 Manual.Count131072.C063069.packed 64 cuts63069 = true := by
 decide +kernel
def pointBounds63069 : List (Nat × Nat × Nat) := [(8270630912,114532280109786,114532668869798)]
theorem point_links_checked63069 : (cuts63069.take 1).map (fun c => (8270512129-1+2*2^10*c.k,114532103783233+c.lower,114532492543150+c.upper)) = pointBounds63069 := by
 decide +kernel
def cuts63070 : List PrefixCut := [⟨64,194667282,194667396⟩]
theorem checked63070 : checkPrefixCuts (2^48) 8270643201 10 Manual.Count131072.C063070.packed 64 cuts63070 = true := by
 decide +kernel
def cuts63071 : List PrefixCut := [⟨57,173019870,173019968⟩,
⟨64,194800325,194800436⟩]
theorem checked63071 : checkPrefixCuts (2^48) 8270774273 10 Manual.Count131072.C063071.packed 64 cuts63071 = true := by
 decide +kernel
def pointBounds63071 : List (Nat × Nat × Nat) := [(8270891008,114532665698315,114533054458551)]
theorem point_links_checked63071 : (cuts63071.take 1).map (fun c => (8270774273-1+2*2^10*c.k,114532492678445+c.lower,114532881438583+c.upper)) = pointBounds63071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000095
