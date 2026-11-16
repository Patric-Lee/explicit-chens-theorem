import PlattAssemblyKernel
import PlattCertificates.Count131072.C068032
import PlattCertificates.Count131072.C068033
import PlattCertificates.Count131072.C068034
import PlattCertificates.Count131072.C068035
import PlattCertificates.Count131072.C068036
import PlattCertificates.Count131072.C068037
import PlattCertificates.Count131072.C068038
import PlattCertificates.Count131072.C068039
import PlattCertificates.Count131072.C068040
import PlattCertificates.Count131072.C068041
import PlattCertificates.Count131072.C068042
import PlattCertificates.Count131072.C068043
import PlattCertificates.Count131072.C068044
import PlattCertificates.Count131072.C068045
import PlattCertificates.Count131072.C068046
import PlattCertificates.Count131072.C068047
import PlattCertificates.Count131072.C068048
import PlattCertificates.Count131072.C068049
import PlattCertificates.Count131072.C068050
import PlattCertificates.Count131072.C068051
import PlattCertificates.Count131072.C068052
import PlattCertificates.Count131072.C068053
import PlattCertificates.Count131072.C068054
import PlattCertificates.Count131072.C068055
import PlattCertificates.Count131072.C068056
import PlattCertificates.Count131072.C068057
import PlattCertificates.Count131072.C068058
import PlattCertificates.Count131072.C068059
import PlattCertificates.Count131072.C068060
import PlattCertificates.Count131072.C068061
import PlattCertificates.Count131072.C068062
import PlattCertificates.Count131072.C068063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000251
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68032 : List PrefixCut := [⟨64,181358777,181358884⟩]
theorem checked68032 : checkPrefixCuts (2^48) 8921022465 10 Manual.Count131072.C068032.packed 64 cuts68032 = true := by
 decide +kernel
def cuts68033 : List PrefixCut := [⟨34,94496080,94496132⟩,
⟨64,179589256,179589353⟩]
theorem checked68033 : checkPrefixCuts (2^48) 8921153537 10 Manual.Count131072.C068033.packed 64 cuts68033 = true := by
 decide +kernel
def pointBounds68033 : List (Nat × Nat × Nat) := [(8921223168,115464045332857,115464434632990)]
theorem point_links_checked68033 : (cuts68033.take 1).map (fun c => (8921153537-1+2*2^10*c.k,115463950836777+c.lower,115464340136858+c.upper)) = pointBounds68033 := by
 decide +kernel
def cuts68034 : List PrefixCut := [⟨64,179996770,179996873⟩]
theorem checked68034 : checkPrefixCuts (2^48) 8921284609 10 Manual.Count131072.C068034.packed 64 cuts68034 = true := by
 decide +kernel
def cuts68035 : List PrefixCut := [⟨43,119954309,119954378⟩,
⟨64,181129925,181130032⟩]
theorem checked68035 : checkPrefixCuts (2^48) 8921415681 10 Manual.Count131072.C068035.packed 64 cuts68035 = true := by
 decide +kernel
def pointBounds68035 : List (Nat × Nat × Nat) := [(8921503744,115464430377112,115464819677462)]
theorem point_links_checked68035 : (cuts68035.take 1).map (fun c => (8921415681-1+2*2^10*c.k,115464310422803+c.lower,115464699723084+c.upper)) = pointBounds68035 := by
 decide +kernel
def cuts68036 : List PrefixCut := [⟨64,179171192,179171294⟩]
theorem checked68036 : checkPrefixCuts (2^48) 8921546753 10 Manual.Count131072.C068036.packed 64 cuts68036 = true := by
 decide +kernel
def cuts68037 : List PrefixCut := [⟨52,145063959,145064044⟩,
⟨64,178789974,178790080⟩]
theorem checked68037 : checkPrefixCuts (2^48) 8921677825 10 Manual.Count131072.C068037.packed 64 cuts68037 = true := by
 decide +kernel
def pointBounds68037 : List (Nat × Nat × Nat) := [(8921784320,115464815787879,115465205088454)]
theorem point_links_checked68037 : (cuts68037.take 1).map (fun c => (8921677825-1+2*2^10*c.k,115464670723920+c.lower,115465060024410+c.upper)) = pointBounds68037 := by
 decide +kernel
def cuts68038 : List PrefixCut := [⟨64,177020604,177020709⟩]
theorem checked68038 : checkPrefixCuts (2^48) 8921808897 10 Manual.Count131072.C068038.packed 64 cuts68038 = true := by
 decide +kernel
def cuts68039 : List PrefixCut := [⟨61,172538180,172538282⟩,
⟨64,180740703,180740810⟩]
theorem checked68039 : checkPrefixCuts (2^48) 8921939969 10 Manual.Count131072.C068039.packed 64 cuts68039 = true := by
 decide +kernel
def pointBounds68039 : List (Nat × Nat × Nat) := [(8922064896,115465199072678,115465588373481)]
theorem point_links_checked68039 : (cuts68039.take 1).map (fun c => (8921939969-1+2*2^10*c.k,115465026534498+c.lower,115465415835199+c.upper)) = pointBounds68039 := by
 decide +kernel
def cuts68040 : List PrefixCut := [⟨64,180958894,180959004⟩]
theorem checked68040 : checkPrefixCuts (2^48) 8922071041 10 Manual.Count131072.C068040.packed 64 cuts68040 = true := by
 decide +kernel
def cuts68041 : List PrefixCut := [⟨64,178968743,178968847⟩]
theorem checked68041 : checkPrefixCuts (2^48) 8922202113 10 Manual.Count131072.C068041.packed 64 cuts68041 = true := by
 decide +kernel
def cuts68042 : List PrefixCut := [⟨6,17445606,17445616⟩,
⟨64,183571986,183572089⟩]
theorem checked68042 : checkPrefixCuts (2^48) 8922333185 10 Manual.Count131072.C068042.packed 64 cuts68042 = true := by
 decide +kernel
def pointBounds68042 : List (Nat × Nat × Nat) := [(8922345472,115465584648444,115465973949476)]
theorem point_links_checked68042 : (cuts68042.take 1).map (fun c => (8922333185-1+2*2^10*c.k,115465567202838+c.lower,115465956503860+c.upper)) = pointBounds68042 := by
 decide +kernel
def cuts68043 : List PrefixCut := [⟨64,180351544,180351647⟩]
theorem checked68043 : checkPrefixCuts (2^48) 8922464257 10 Manual.Count131072.C068043.packed 64 cuts68043 = true := by
 decide +kernel
def cuts68044 : List PrefixCut := [⟨15,41830326,41830350⟩,
⟨64,179623329,179623431⟩]
theorem checked68044 : checkPrefixCuts (2^48) 8922595329 10 Manual.Count131072.C068044.packed 64 cuts68044 = true := by
 decide +kernel
def pointBounds68044 : List (Nat × Nat × Nat) := [(8922626048,115465972956694,115466362257946)]
theorem point_links_checked68044 : (cuts68044.take 1).map (fun c => (8922595329-1+2*2^10*c.k,115465931126368+c.lower,115466320427596+c.upper)) = pointBounds68044 := by
 decide +kernel
def cuts68045 : List PrefixCut := [⟨64,179084436,179084540⟩]
theorem checked68045 : checkPrefixCuts (2^48) 8922726401 10 Manual.Count131072.C068045.packed 64 cuts68045 = true := by
 decide +kernel
def cuts68046 : List PrefixCut := [⟨24,66087382,66087420⟩,
⟨64,178356244,178356344⟩]
theorem checked68046 : checkPrefixCuts (2^48) 8922857473 10 Manual.Count131072.C068046.packed 64 cuts68046 = true := by
 decide +kernel
def pointBounds68046 : List (Nat × Nat × Nat) := [(8922906624,115466355921515,115466745222987)]
theorem point_links_checked68046 : (cuts68046.take 1).map (fun c => (8922857473-1+2*2^10*c.k,115466289834133+c.lower,115466679135567+c.upper)) = pointBounds68046 := by
 decide +kernel
def cuts68047 : List PrefixCut := [⟨64,179268423,179268526⟩]
theorem checked68047 : checkPrefixCuts (2^48) 8922988545 10 Manual.Count131072.C068047.packed 64 cuts68047 = true := by
 decide +kernel
def cuts68048 : List PrefixCut := [⟨33,92519522,92519579⟩,
⟨64,181126892,181126999⟩]
theorem checked68048 : checkPrefixCuts (2^48) 8923119617 10 Manual.Count131072.C068048.packed 64 cuts68048 = true := by
 decide +kernel
def pointBounds68048 : List (Nat × Nat × Nat) := [(8923187200,115466739978322,115467129280016)]
theorem point_links_checked68048 : (cuts68048.take 1).map (fun c => (8923119617-1+2*2^10*c.k,115466647458800+c.lower,115467036760437+c.upper)) = pointBounds68048 := by
 decide +kernel
def cuts68049 : List PrefixCut := [⟨64,179736306,179736414⟩]
theorem checked68049 : checkPrefixCuts (2^48) 8923250689 10 Manual.Count131072.C068049.packed 64 cuts68049 = true := by
 decide +kernel
def cuts68050 : List PrefixCut := [⟨42,121568149,121568215⟩,
⟨64,185032942,185033049⟩]
theorem checked68050 : checkPrefixCuts (2^48) 8923381761 10 Manual.Count131072.C068050.packed 64 cuts68050 = true := by
 decide +kernel
def pointBounds68050 : List (Nat × Nat × Nat) := [(8923467776,115467129890147,115467519192065)]
theorem point_links_checked68050 : (cuts68050.take 1).map (fun c => (8923381761-1+2*2^10*c.k,115467008321998+c.lower,115467397623850+c.upper)) = pointBounds68050 := by
 decide +kernel
def cuts68051 : List PrefixCut := [⟨64,180235717,180235824⟩]
theorem checked68051 : checkPrefixCuts (2^48) 8923512833 10 Manual.Count131072.C068051.packed 64 cuts68051 = true := by
 decide +kernel
def cuts68052 : List PrefixCut := [⟨51,147586947,147587032⟩,
⟨64,184333586,184333692⟩]
theorem checked68052 : checkPrefixCuts (2^48) 8923643905 10 Manual.Count131072.C068052.packed 64 cuts68052 = true := by
 decide +kernel
def pointBounds68052 : List (Nat × Nat × Nat) := [(8923748352,115467521177604,115467910479755)]
theorem point_links_checked68052 : (cuts68052.take 1).map (fun c => (8923643905-1+2*2^10*c.k,115467373590657+c.lower,115467762892723+c.upper)) = pointBounds68052 := by
 decide +kernel
def cuts68053 : List PrefixCut := [⟨64,182406790,182406899⟩]
theorem checked68053 : checkPrefixCuts (2^48) 8923774977 10 Manual.Count131072.C068053.packed 64 cuts68053 = true := by
 decide +kernel
def cuts68054 : List PrefixCut := [⟨60,168841396,168841487⟩,
⟨64,180448565,180448663⟩]
theorem checked68054 : checkPrefixCuts (2^48) 8923906049 10 Manual.Count131072.C068054.packed 64 cuts68054 = true := by
 decide +kernel
def pointBounds68054 : List (Nat × Nat × Nat) := [(8924028928,115467909172429,115468298474801)]
theorem point_links_checked68054 : (cuts68054.take 1).map (fun c => (8923906049-1+2*2^10*c.k,115467740331033+c.lower,115468129633314+c.upper)) = pointBounds68054 := by
 decide +kernel
def cuts68055 : List PrefixCut := [⟨64,177670317,177670417⟩]
theorem checked68055 : checkPrefixCuts (2^48) 8924037121 10 Manual.Count131072.C068055.packed 64 cuts68055 = true := by
 decide +kernel
def cuts68056 : List PrefixCut := [⟨64,181894126,181894229⟩]
theorem checked68056 : checkPrefixCuts (2^48) 8924168193 10 Manual.Count131072.C068056.packed 64 cuts68056 = true := by
 decide +kernel
def cuts68057 : List PrefixCut := [⟨5,13877715,13877723⟩,
⟨64,181197576,181197683⟩]
theorem checked68057 : checkPrefixCuts (2^48) 8924299265 10 Manual.Count131072.C068057.packed 64 cuts68057 = true := by
 decide +kernel
def pointBounds68057 : List (Nat × Nat × Nat) := [(8924309504,115468294221756,115468683524346)]
theorem point_links_checked68057 : (cuts68057.take 1).map (fun c => (8924299265-1+2*2^10*c.k,115468280344041+c.lower,115468669646623+c.upper)) = pointBounds68057 := by
 decide +kernel
def cuts68058 : List PrefixCut := [⟨64,181573391,181573495⟩]
theorem checked68058 : checkPrefixCuts (2^48) 8924430337 10 Manual.Count131072.C068058.packed 64 cuts68058 = true := by
 decide +kernel
def cuts68059 : List PrefixCut := [⟨14,39865678,39865702⟩,
⟨64,181665341,181665445⟩]
theorem checked68059 : checkPrefixCuts (2^48) 8924561409 10 Manual.Count131072.C068059.packed 64 cuts68059 = true := by
 decide +kernel
def pointBounds68059 : List (Nat × Nat × Nat) := [(8924590080,115468682980686,115469072283503)]
theorem point_links_checked68059 : (cuts68059.take 1).map (fun c => (8924561409-1+2*2^10*c.k,115468643115008+c.lower,115469032417801+c.upper)) = pointBounds68059 := by
 decide +kernel
def cuts68060 : List PrefixCut := [⟨64,180243437,180243543⟩]
theorem checked68060 : checkPrefixCuts (2^48) 8924692481 10 Manual.Count131072.C068060.packed 64 cuts68060 = true := by
 decide +kernel
def cuts68061 : List PrefixCut := [⟨23,63423612,63423649⟩,
⟨64,179136950,179137051⟩]
theorem checked68061 : checkPrefixCuts (2^48) 8924823553 10 Manual.Count131072.C068061.packed 64 cuts68061 = true := by
 decide +kernel
def pointBounds68061 : List (Nat × Nat × Nat) := [(8924870656,115469068447398,115469457750438)]
theorem point_links_checked68061 : (cuts68061.take 1).map (fun c => (8924823553-1+2*2^10*c.k,115469005023786+c.lower,115469394326789+c.upper)) = pointBounds68061 := by
 decide +kernel
def cuts68062 : List PrefixCut := [⟨64,181846553,181846658⟩]
theorem checked68062 : checkPrefixCuts (2^48) 8924954625 10 Manual.Count131072.C068062.packed 64 cuts68062 = true := by
 decide +kernel
def cuts68063 : List PrefixCut := [⟨32,88588512,88588568⟩,
⟨64,179857031,179857140⟩]
theorem checked68063 : checkPrefixCuts (2^48) 8925085697 10 Manual.Count131072.C068063.packed 64 cuts68063 = true := by
 decide +kernel
def pointBounds68063 : List (Nat × Nat × Nat) := [(8925151232,115469454595801,115469843899066)]
theorem point_links_checked68063 : (cuts68063.take 1).map (fun c => (8925085697-1+2*2^10*c.k,115469366007289+c.lower,115469755310498+c.upper)) = pointBounds68063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000251
