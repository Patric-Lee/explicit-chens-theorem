import PlattAssemblyKernel
import PlattCertificates.Count131072.C071056
import PlattCertificates.Count131072.C071057
import PlattCertificates.Count131072.C071058
import PlattCertificates.Count131072.C071059
import PlattCertificates.Count131072.C071060
import PlattCertificates.Count131072.C071061
import PlattCertificates.Count131072.C071062
import PlattCertificates.Count131072.C071063
import PlattCertificates.Count131072.C071064
import PlattCertificates.Count131072.C071065
import PlattCertificates.Count131072.C071066
import PlattCertificates.Count131072.C071067
import PlattCertificates.Count131072.C071068
import PlattCertificates.Count131072.C071069
import PlattCertificates.Count131072.C071070
import PlattCertificates.Count131072.C071071
import PlattCertificates.Count131072.C071072
import PlattCertificates.Count131072.C071073
import PlattCertificates.Count131072.C071074
import PlattCertificates.Count131072.C071075
import PlattCertificates.Count131072.C071076
import PlattCertificates.Count131072.C071077
import PlattCertificates.Count131072.C071078
import PlattCertificates.Count131072.C071079
import PlattCertificates.Count131072.C071080
import PlattCertificates.Count131072.C071081
import PlattCertificates.Count131072.C071082
import PlattCertificates.Count131072.C071083
import PlattCertificates.Count131072.C071084
import PlattCertificates.Count131072.C071085
import PlattCertificates.Count131072.C071086
import PlattCertificates.Count131072.C071087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71056 : List PrefixCut := [⟨64,171921905,171922013⟩]
theorem checked71056 : checkPrefixCuts (2^48) 9317384193 10 Manual.Count131072.C071056.packed 64 cuts71056 = true := by
 decide +kernel
def cuts71057 : List PrefixCut := [⟨23,60388081,60388122⟩,
⟨64,172372594,172372706⟩]
theorem checked71057 : checkPrefixCuts (2^48) 9317515265 10 Manual.Count131072.C071057.packed 64 cuts71057 = true := by
 decide +kernel
def pointBounds71057 : List (Nat × Nat × Nat) := [(9317562368,115997588948539,115997978562141)]
theorem point_links_checked71057 : (cuts71057.take 1).map (fun c => (9317515265-1+2*2^10*c.k,115997528560458+c.lower,115997918174019+c.upper)) = pointBounds71057 := by
 decide +kernel
def cuts71058 : List PrefixCut := [⟨64,173941029,173941129⟩]
theorem checked71058 : checkPrefixCuts (2^48) 9317646337 10 Manual.Count131072.C071058.packed 64 cuts71058 = true := by
 decide +kernel
def cuts71059 : List PrefixCut := [⟨38,103916367,103916429⟩,
⟨64,173394847,173394951⟩]
theorem checked71059 : checkPrefixCuts (2^48) 9317777409 10 Manual.Count131072.C071059.packed 64 cuts71059 = true := by
 decide +kernel
def pointBounds71059 : List (Nat × Nat × Nat) := [(9317855232,115997978790448,115998368404283)]
theorem point_links_checked71059 : (cuts71059.take 1).map (fun c => (9317777409-1+2*2^10*c.k,115997874874081+c.lower,115998264487854+c.upper)) = pointBounds71059 := by
 decide +kernel
def cuts71060 : List PrefixCut := [⟨64,171851810,171851918⟩]
theorem checked71060 : checkPrefixCuts (2^48) 9317908481 10 Manual.Count131072.C071060.packed 64 cuts71060 = true := by
 decide +kernel
def cuts71061 : List PrefixCut := [⟨53,142820337,142820417⟩,
⟨64,171396287,171396381⟩]
theorem checked71061 : checkPrefixCuts (2^48) 9318039553 10 Manual.Count131072.C071061.packed 64 cuts71061 = true := by
 decide +kernel
def pointBounds71061 : List (Nat × Nat × Nat) := [(9318148096,115998362941075,115998752555140)]
theorem point_links_checked71061 : (cuts71061.take 1).map (fun c => (9318039553-1+2*2^10*c.k,115998220120738+c.lower,115998609734723+c.upper)) = pointBounds71061 := by
 decide +kernel
def cuts71062 : List PrefixCut := [⟨64,174354129,174354223⟩]
theorem checked71062 : checkPrefixCuts (2^48) 9318170625 10 Manual.Count131072.C071062.packed 64 cuts71062 = true := by
 decide +kernel
def cuts71063 : List PrefixCut := [⟨64,171935181,171935282⟩]
theorem checked71063 : checkPrefixCuts (2^48) 9318301697 10 Manual.Count131072.C071063.packed 64 cuts71063 = true := by
 decide +kernel
def cuts71064 : List PrefixCut := [⟨4,10723213,10723220⟩,
⟨64,171962960,171963065⟩]
theorem checked71064 : checkPrefixCuts (2^48) 9318432769 10 Manual.Count131072.C071064.packed 64 cuts71064 = true := by
 decide +kernel
def pointBounds71064 : List (Nat × Nat × Nat) := [(9318440960,115998748529548,115999138143829)]
theorem point_links_checked71064 : (cuts71064.take 1).map (fun c => (9318432769-1+2*2^10*c.k,115998737806335+c.lower,115999127420609+c.upper)) = pointBounds71064 := by
 decide +kernel
def cuts71065 : List PrefixCut := [⟨64,173621855,173621951⟩]
theorem checked71065 : checkPrefixCuts (2^48) 9318563841 10 Manual.Count131072.C071065.packed 64 cuts71065 = true := by
 decide +kernel
def cuts71066 : List PrefixCut := [⟨19,50714758,50714792⟩,
⟨64,173136123,173136228⟩]
theorem checked71066 : checkPrefixCuts (2^48) 9318694913 10 Manual.Count131072.C071066.packed 64 cuts71066 = true := by
 decide +kernel
def pointBounds71066 : List (Nat × Nat × Nat) := [(9318733824,115999134105908,115999523720417)]
theorem point_links_checked71066 : (cuts71066.take 1).map (fun c => (9318694913-1+2*2^10*c.k,115999083391150+c.lower,115999473005625+c.upper)) = pointBounds71066 := by
 decide +kernel
def cuts71067 : List PrefixCut := [⟨64,172741019,172741123⟩]
theorem checked71067 : checkPrefixCuts (2^48) 9318825985 10 Manual.Count131072.C071067.packed 64 cuts71067 = true := by
 decide +kernel
def cuts71068 : List PrefixCut := [⟨34,92274551,92274604⟩,
⟨64,173131255,173131356⟩]
theorem checked71068 : checkPrefixCuts (2^48) 9318957057 10 Manual.Count131072.C071068.packed 64 cuts71068 = true := by
 decide +kernel
def pointBounds71068 : List (Nat × Nat × Nat) := [(9319026688,115999521542843,115999911157580)]
theorem point_links_checked71068 : (cuts71068.take 1).map (fun c => (9318957057-1+2*2^10*c.k,115999429268292+c.lower,115999818882976+c.upper)) = pointBounds71068 := by
 decide +kernel
def cuts71069 : List PrefixCut := [⟨64,171830060,171830162⟩]
theorem checked71069 : checkPrefixCuts (2^48) 9319088129 10 Manual.Count131072.C071069.packed 64 cuts71069 = true := by
 decide +kernel
def cuts71070 : List PrefixCut := [⟨49,130147030,130147110⟩,
⟨64,170226840,170226944⟩]
theorem checked71070 : checkPrefixCuts (2^48) 9319219201 10 Manual.Count131072.C071070.packed 64 cuts71070 = true := by
 decide +kernel
def pointBounds71070 : List (Nat × Nat × Nat) := [(9319319552,115999904376637,116000293991604)]
theorem point_links_checked71070 : (cuts71070.take 1).map (fun c => (9319219201-1+2*2^10*c.k,115999774229607+c.lower,116000163844494+c.upper)) = pointBounds71070 := by
 decide +kernel
def cuts71071 : List PrefixCut := [⟨64,170375470,170375570⟩]
theorem checked71071 : checkPrefixCuts (2^48) 9319350273 10 Manual.Count131072.C071071.packed 64 cuts71071 = true := by
 decide +kernel
def cuts71072 : List PrefixCut := [⟨64,172245646,172245749⟩]
theorem checked71072 : checkPrefixCuts (2^48) 9319481345 10 Manual.Count131072.C071072.packed 64 cuts71072 = true := by
 decide +kernel
def pointBounds71072 : List (Nat × Nat × Nat) := [(9319612416,116000287077563,116000676692757)]
theorem point_links_checked71072 : (cuts71072.take 1).map (fun c => (9319481345-1+2*2^10*c.k,116000114831917+c.lower,116000504447008+c.upper)) = pointBounds71072 := by
 decide +kernel
def cuts71073 : List PrefixCut := [⟨64,173149291,173149391⟩]
theorem checked71073 : checkPrefixCuts (2^48) 9319612417 10 Manual.Count131072.C071073.packed 64 cuts71073 = true := by
 decide +kernel
def cuts71074 : List PrefixCut := [⟨64,171938782,171938881⟩]
theorem checked71074 : checkPrefixCuts (2^48) 9319743489 10 Manual.Count131072.C071074.packed 64 cuts71074 = true := by
 decide +kernel
def cuts71075 : List PrefixCut := [⟨15,40409641,40409665⟩,
⟨64,170788707,170788811⟩]
theorem checked71075 : checkPrefixCuts (2^48) 9319874561 10 Manual.Count131072.C071075.packed 64 cuts71075 = true := by
 decide +kernel
def pointBounds71075 : List (Nat × Nat × Nat) := [(9319905280,116000672575277,116001062190694)]
theorem point_links_checked71075 : (cuts71075.take 1).map (fun c => (9319874561-1+2*2^10*c.k,116000632165636+c.lower,116001021781029+c.upper)) = pointBounds71075 := by
 decide +kernel
def cuts71076 : List PrefixCut := [⟨64,169548065,169548162⟩]
theorem checked71076 : checkPrefixCuts (2^48) 9320005633 10 Manual.Count131072.C071076.packed 64 cuts71076 = true := by
 decide +kernel
def cuts71077 : List PrefixCut := [⟨30,80605471,80605523⟩,
⟨64,173501949,173502056⟩]
theorem checked71077 : checkPrefixCuts (2^48) 9320136705 10 Manual.Count131072.C071077.packed 64 cuts71077 = true := by
 decide +kernel
def pointBounds71077 : List (Nat × Nat × Nat) := [(9320198144,116001053107879,116001442723525)]
theorem point_links_checked71077 : (cuts71077.take 1).map (fun c => (9320136705-1+2*2^10*c.k,116000972502408+c.lower,116001362118002+c.upper)) = pointBounds71077 := by
 decide +kernel
def cuts71078 : List PrefixCut := [⟨64,171415698,171415797⟩]
theorem checked71078 : checkPrefixCuts (2^48) 9320267777 10 Manual.Count131072.C071078.packed 64 cuts71078 = true := by
 decide +kernel
def cuts71079 : List PrefixCut := [⟨45,120255314,120255389⟩,
⟨64,171896485,171896589⟩]
theorem checked71079 : checkPrefixCuts (2^48) 9320398849 10 Manual.Count131072.C071079.packed 64 cuts71079 = true := by
 decide +kernel
def pointBounds71079 : List (Nat × Nat × Nat) := [(9320491008,116001437675369,116001827291244)]
theorem point_links_checked71079 : (cuts71079.take 1).map (fun c => (9320398849-1+2*2^10*c.k,116001317420055+c.lower,116001707035855+c.upper)) = pointBounds71079 := by
 decide +kernel
def cuts71080 : List PrefixCut := [⟨64,172618847,172618947⟩]
theorem checked71080 : checkPrefixCuts (2^48) 9320529921 10 Manual.Count131072.C071080.packed 64 cuts71080 = true := by
 decide +kernel
def cuts71081 : List PrefixCut := [⟨60,162650883,162650986⟩,
⟨64,173280795,173280905⟩]
theorem checked71081 : checkPrefixCuts (2^48) 9320660993 10 Manual.Count131072.C071081.packed 64 cuts71081 = true := by
 decide +kernel
def pointBounds71081 : List (Nat × Nat × Nat) := [(9320783872,116001824586270,116002214202377)]
theorem point_links_checked71081 : (cuts71081.take 1).map (fun c => (9320660993-1+2*2^10*c.k,116001661935387+c.lower,116002051551391+c.upper)) = pointBounds71081 := by
 decide +kernel
def cuts71082 : List PrefixCut := [⟨64,171919442,171919539⟩]
theorem checked71082 : checkPrefixCuts (2^48) 9320792065 10 Manual.Count131072.C071082.packed 64 cuts71082 = true := by
 decide +kernel
def cuts71083 : List PrefixCut := [⟨64,173185339,173185439⟩]
theorem checked71083 : checkPrefixCuts (2^48) 9320923137 10 Manual.Count131072.C071083.packed 64 cuts71083 = true := by
 decide +kernel
def cuts71084 : List PrefixCut := [⟨11,29623959,29623977⟩,
⟨64,173635853,173635960⟩]
theorem checked71084 : checkPrefixCuts (2^48) 9321054209 10 Manual.Count131072.C071084.packed 64 cuts71084 = true := by
 decide +kernel
def pointBounds71084 : List (Nat × Nat × Nat) := [(9321076736,116002209944922,116002599561251)]
theorem point_links_checked71084 : (cuts71084.take 1).map (fun c => (9321054209-1+2*2^10*c.k,116002180320963+c.lower,116002569937274+c.upper)) = pointBounds71084 := by
 decide +kernel
def cuts71085 : List PrefixCut := [⟨64,173754202,173754303⟩]
theorem checked71085 : checkPrefixCuts (2^48) 9321185281 10 Manual.Count131072.C071085.packed 64 cuts71085 = true := by
 decide +kernel
def cuts71086 : List PrefixCut := [⟨26,71385281,71385323⟩,
⟨64,172362731,172362833⟩]
theorem checked71086 : checkPrefixCuts (2^48) 9321316353 10 Manual.Count131072.C071086.packed 64 cuts71086 = true := by
 decide +kernel
def pointBounds71086 : List (Nat × Nat × Nat) := [(9321369600,116002599096299,116002988712860)]
theorem point_links_checked71086 : (cuts71086.take 1).map (fun c => (9321316353-1+2*2^10*c.k,116002527711018+c.lower,116002917327537+c.upper)) = pointBounds71086 := by
 decide +kernel
def cuts71087 : List PrefixCut := [⟨64,172752839,172752942⟩]
theorem checked71087 : checkPrefixCuts (2^48) 9321447425 10 Manual.Count131072.C071087.packed 64 cuts71087 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000033
