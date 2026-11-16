import PlattAssemblyKernel
import PlattCertificates.Count131072.C066912
import PlattCertificates.Count131072.C066913
import PlattCertificates.Count131072.C066914
import PlattCertificates.Count131072.C066915
import PlattCertificates.Count131072.C066916
import PlattCertificates.Count131072.C066917
import PlattCertificates.Count131072.C066918
import PlattCertificates.Count131072.C066919
import PlattCertificates.Count131072.C066920
import PlattCertificates.Count131072.C066921
import PlattCertificates.Count131072.C066922
import PlattCertificates.Count131072.C066923
import PlattCertificates.Count131072.C066924
import PlattCertificates.Count131072.C066925
import PlattCertificates.Count131072.C066926
import PlattCertificates.Count131072.C066927
import PlattCertificates.Count131072.C066928
import PlattCertificates.Count131072.C066929
import PlattCertificates.Count131072.C066930
import PlattCertificates.Count131072.C066931
import PlattCertificates.Count131072.C066932
import PlattCertificates.Count131072.C066933
import PlattCertificates.Count131072.C066934
import PlattCertificates.Count131072.C066935
import PlattCertificates.Count131072.C066936
import PlattCertificates.Count131072.C066937
import PlattCertificates.Count131072.C066938
import PlattCertificates.Count131072.C066939
import PlattCertificates.Count131072.C066940
import PlattCertificates.Count131072.C066941
import PlattCertificates.Count131072.C066942
import PlattCertificates.Count131072.C066943
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000216
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66912 : List PrefixCut := [⟨64,181570050,181570154⟩]
theorem checked66912 : checkPrefixCuts (2^48) 8774221825 10 Manual.Count131072.C066912.packed 64 cuts66912 = true := by
 decide +kernel
def cuts66913 : List PrefixCut := [⟨34,96782789,96782854⟩,
⟨64,182048526,182048641⟩]
theorem checked66913 : checkPrefixCuts (2^48) 8774352897 10 Manual.Count131072.C066913.packed 64 cuts66913 = true := by
 decide +kernel
def pointBounds66913 : List (Nat × Nat × Nat) := [(8774422528,115260144486615,115260533667716)]
theorem point_links_checked66913 : (cuts66913.take 1).map (fun c => (8774352897-1+2*2^10*c.k,115260047703826+c.lower,115260436884862+c.upper)) = pointBounds66913 := by
 decide +kernel
def cuts66914 : List PrefixCut := [⟨64,182494922,182495021⟩]
theorem checked66914 : checkPrefixCuts (2^48) 8774483969 10 Manual.Count131072.C066914.packed 64 cuts66914 = true := by
 decide +kernel
def cuts66915 : List PrefixCut := [⟨40,112626447,112626515⟩,
⟨64,181465682,181465792⟩]
theorem checked66915 : checkPrefixCuts (2^48) 8774615041 10 Manual.Count131072.C066915.packed 64 cuts66915 = true := by
 decide +kernel
def pointBounds66915 : List (Nat × Nat × Nat) := [(8774696960,115260524873721,115260914055039)]
theorem point_links_checked66915 : (cuts66915.take 1).map (fun c => (8774615041-1+2*2^10*c.k,115260412247274+c.lower,115260801428524+c.upper)) = pointBounds66915 := by
 decide +kernel
def cuts66916 : List PrefixCut := [⟨64,183066870,183066974⟩]
theorem checked66916 : checkPrefixCuts (2^48) 8774746113 10 Manual.Count131072.C066916.packed 64 cuts66916 = true := by
 decide +kernel
def cuts66917 : List PrefixCut := [⟨46,131484389,131484460⟩,
⟨64,182679197,182679299⟩]
theorem checked66917 : checkPrefixCuts (2^48) 8774877185 10 Manual.Count131072.C066917.packed 64 cuts66917 = true := by
 decide +kernel
def pointBounds66917 : List (Nat × Nat × Nat) := [(8774971392,115260908264215,115261297445750)]
theorem point_links_checked66917 : (cuts66917.take 1).map (fun c => (8774877185-1+2*2^10*c.k,115260776779826+c.lower,115261165961290+c.upper)) = pointBounds66917 := by
 decide +kernel
def cuts66918 : List PrefixCut := [⟨64,183414242,183414347⟩]
theorem checked66918 : checkPrefixCuts (2^48) 8775008257 10 Manual.Count131072.C066918.packed 64 cuts66918 = true := by
 decide +kernel
def cuts66919 : List PrefixCut := [⟨52,148544923,148545012⟩,
⟨64,182802056,182802166⟩]
theorem checked66919 : checkPrefixCuts (2^48) 8775139329 10 Manual.Count131072.C066919.packed 64 cuts66919 = true := by
 decide +kernel
def pointBounds66919 : List (Nat × Nat × Nat) := [(8775245824,115261291418188,115261680599948)]
theorem point_links_checked66919 : (cuts66919.take 1).map (fun c => (8775139329-1+2*2^10*c.k,115261142873265+c.lower,115261532054936+c.upper)) = pointBounds66919 := by
 decide +kernel
def cuts66920 : List PrefixCut := [⟨64,180874785,180874887⟩]
theorem checked66920 : checkPrefixCuts (2^48) 8775270401 10 Manual.Count131072.C066920.packed 64 cuts66920 = true := by
 decide +kernel
def cuts66921 : List PrefixCut := [⟨58,167753435,167753530⟩,
⟨64,184945628,184945733⟩]
theorem checked66921 : checkPrefixCuts (2^48) 8775401473 10 Manual.Count131072.C066921.packed 64 cuts66921 = true := by
 decide +kernel
def pointBounds66921 : List (Nat × Nat × Nat) := [(8775520256,115261674303541,115262063485519)]
theorem point_links_checked66921 : (cuts66921.take 1).map (fun c => (8775401473-1+2*2^10*c.k,115261506550106+c.lower,115261895731989+c.upper)) = pointBounds66921 := by
 decide +kernel
def cuts66922 : List PrefixCut := [⟨64,181703312,181703415⟩]
theorem checked66922 : checkPrefixCuts (2^48) 8775532545 10 Manual.Count131072.C066922.packed 64 cuts66922 = true := by
 decide +kernel
def cuts66923 : List PrefixCut := [⟨64,182791134,182791240⟩]
theorem checked66923 : checkPrefixCuts (2^48) 8775663617 10 Manual.Count131072.C066923.packed 64 cuts66923 = true := by
 decide +kernel
def pointBounds66923 : List (Nat × Nat × Nat) := [(8775794688,115262055990180,115262445172377)]
theorem point_links_checked66923 : (cuts66923.take 1).map (fun c => (8775663617-1+2*2^10*c.k,115261873199046+c.lower,115262262381137+c.upper)) = pointBounds66923 := by
 decide +kernel
def cuts66924 : List PrefixCut := [⟨64,186220285,186220393⟩]
theorem checked66924 : checkPrefixCuts (2^48) 8775794689 10 Manual.Count131072.C066924.packed 64 cuts66924 = true := by
 decide +kernel
def cuts66925 : List PrefixCut := [⟨64,183106402,183106506⟩]
theorem checked66925 : checkPrefixCuts (2^48) 8775925761 10 Manual.Count131072.C066925.packed 64 cuts66925 = true := by
 decide +kernel
def cuts66926 : List PrefixCut := [⟨6,17511872,17511882⟩,
⟨64,182879156,182879263⟩]
theorem checked66926 : checkPrefixCuts (2^48) 8776056833 10 Manual.Count131072.C066926.packed 64 cuts66926 = true := by
 decide +kernel
def pointBounds66926 : List (Nat × Nat × Nat) := [(8776069120,115262442828739,115262832011158)]
theorem point_links_checked66926 : (cuts66926.take 1).map (fun c => (8776056833-1+2*2^10*c.k,115262425316867+c.lower,115262814499276+c.upper)) = pointBounds66926 := by
 decide +kernel
def cuts66927 : List PrefixCut := [⟨64,183549931,183550039⟩]
theorem checked66927 : checkPrefixCuts (2^48) 8776187905 10 Manual.Count131072.C066927.packed 64 cuts66927 = true := by
 decide +kernel
def cuts66928 : List PrefixCut := [⟨12,34477450,34477468⟩,
⟨64,183835850,183835955⟩]
theorem checked66928 : checkPrefixCuts (2^48) 8776318977 10 Manual.Count131072.C066928.packed 64 cuts66928 = true := by
 decide +kernel
def pointBounds66928 : List (Nat × Nat × Nat) := [(8776343552,115262826223404,115263215406046)]
theorem point_links_checked66928 : (cuts66928.take 1).map (fun c => (8776318977-1+2*2^10*c.k,115262791745954+c.lower,115263180928578+c.upper)) = pointBounds66928 := by
 decide +kernel
def cuts66929 : List PrefixCut := [⟨64,180593886,180593992⟩]
theorem checked66929 : checkPrefixCuts (2^48) 8776450049 10 Manual.Count131072.C066929.packed 64 cuts66929 = true := by
 decide +kernel
def cuts66930 : List PrefixCut := [⟨18,52885186,52885217⟩,
⟨64,186043257,186043365⟩]
theorem checked66930 : checkPrefixCuts (2^48) 8776581121 10 Manual.Count131072.C066930.packed 64 cuts66930 = true := by
 decide +kernel
def pointBounds66930 : List (Nat × Nat × Nat) := [(8776617984,115263209060876,115263598243742)]
theorem point_links_checked66930 : (cuts66930.take 1).map (fun c => (8776581121-1+2*2^10*c.k,115263156175690+c.lower,115263545358525+c.upper)) = pointBounds66930 := by
 decide +kernel
def cuts66931 : List PrefixCut := [⟨64,183057927,183058036⟩]
theorem checked66931 : checkPrefixCuts (2^48) 8776712193 10 Manual.Count131072.C066931.packed 64 cuts66931 = true := by
 decide +kernel
def cuts66932 : List PrefixCut := [⟨24,69175173,69175210⟩,
⟨64,184273846,184273950⟩]
theorem checked66932 : checkPrefixCuts (2^48) 8776843265 10 Manual.Count131072.C066932.packed 64 cuts66932 = true := by
 decide +kernel
def pointBounds66932 : List (Nat × Nat × Nat) := [(8776892416,115263594452047,115263983635136)]
theorem point_links_checked66932 : (cuts66932.take 1).map (fun c => (8776843265-1+2*2^10*c.k,115263525276874+c.lower,115263914459926+c.upper)) = pointBounds66932 := by
 decide +kernel
def cuts66933 : List PrefixCut := [⟨64,183437278,183437391⟩]
theorem checked66933 : checkPrefixCuts (2^48) 8776974337 10 Manual.Count131072.C066933.packed 64 cuts66933 = true := by
 decide +kernel
def cuts66934 : List PrefixCut := [⟨30,87869348,87869397⟩,
⟨64,184749386,184749494⟩]
theorem checked66934 : checkPrefixCuts (2^48) 8777105409 10 Manual.Count131072.C066934.packed 64 cuts66934 = true := by
 decide +kernel
def pointBounds66934 : List (Nat × Nat × Nat) := [(8777166848,115263980857346,115264370040664)]
theorem point_links_checked66934 : (cuts66934.take 1).map (fun c => (8777105409-1+2*2^10*c.k,115263892987998+c.lower,115264282171267+c.upper)) = pointBounds66934 := by
 decide +kernel
def cuts66935 : List PrefixCut := [⟨64,181668035,181668144⟩]
theorem checked66935 : checkPrefixCuts (2^48) 8777236481 10 Manual.Count131072.C066935.packed 64 cuts66935 = true := by
 decide +kernel
def cuts66936 : List PrefixCut := [⟨36,99571526,99571585⟩,
⟨64,182338740,182338843⟩]
theorem checked66936 : checkPrefixCuts (2^48) 8777367553 10 Manual.Count131072.C066936.packed 64 cuts66936 = true := by
 decide +kernel
def pointBounds66936 : List (Nat × Nat × Nat) := [(8777441280,115264358976945,115264748160490)]
theorem point_links_checked66936 : (cuts66936.take 1).map (fun c => (8777367553-1+2*2^10*c.k,115264259405419+c.lower,115264648588905+c.upper)) = pointBounds66936 := by
 decide +kernel
def cuts66937 : List PrefixCut := [⟨64,185446588,185446691⟩]
theorem checked66937 : checkPrefixCuts (2^48) 8777498625 10 Manual.Count131072.C066937.packed 64 cuts66937 = true := by
 decide +kernel
def cuts66938 : List PrefixCut := [⟨42,120861066,120861134⟩,
⟨64,184674205,184674311⟩]
theorem checked66938 : checkPrefixCuts (2^48) 8777629697 10 Manual.Count131072.C066938.packed 64 cuts66938 = true := by
 decide +kernel
def pointBounds66938 : List (Nat × Nat × Nat) := [(8777715712,115264748051813,115265137235573)]
theorem point_links_checked66938 : (cuts66938.take 1).map (fun c => (8777629697-1+2*2^10*c.k,115264627190747+c.lower,115265016374439+c.upper)) = pointBounds66938 := by
 decide +kernel
def cuts66939 : List PrefixCut := [⟨64,182619196,182619302⟩]
theorem checked66939 : checkPrefixCuts (2^48) 8777760769 10 Manual.Count131072.C066939.packed 64 cuts66939 = true := by
 decide +kernel
def cuts66940 : List PrefixCut := [⟨48,137211112,137211198⟩,
⟨64,182840921,182841033⟩]
theorem checked66940 : checkPrefixCuts (2^48) 8777891841 10 Manual.Count131072.C066940.packed 64 cuts66940 = true := by
 decide +kernel
def pointBounds66940 : List (Nat × Nat × Nat) := [(8777990144,115265131695260,115265520879250)]
theorem point_links_checked66940 : (cuts66940.take 1).map (fun c => (8777891841-1+2*2^10*c.k,115264994484148+c.lower,115265383668052+c.upper)) = pointBounds66940 := by
 decide +kernel
def cuts66941 : List PrefixCut := [⟨64,184056697,184056809⟩]
theorem checked66941 : checkPrefixCuts (2^48) 8778022913 10 Manual.Count131072.C066941.packed 64 cuts66941 = true := by
 decide +kernel
def cuts66942 : List PrefixCut := [⟨54,154842775,154842858⟩,
⟨64,183156121,183156219⟩]
theorem checked66942 : checkPrefixCuts (2^48) 8778153985 10 Manual.Count131072.C066942.packed 64 cuts66942 = true := by
 decide +kernel
def pointBounds66942 : List (Nat × Nat × Nat) := [(8778264576,115265516224541,115265905408752)]
theorem point_links_checked66942 : (cuts66942.take 1).map (fun c => (8778153985-1+2*2^10*c.k,115265361381766+c.lower,115265750565894+c.upper)) = pointBounds66942 := by
 decide +kernel
def cuts66943 : List PrefixCut := [⟨64,184884859,184884965⟩]
theorem checked66943 : checkPrefixCuts (2^48) 8778285057 10 Manual.Count131072.C066943.packed 64 cuts66943 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000216
