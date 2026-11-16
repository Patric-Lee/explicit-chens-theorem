import PlattAssemblyKernel
import PlattCertificates.Count131072.C059056
import PlattCertificates.Count131072.C059057
import PlattCertificates.Count131072.C059058
import PlattCertificates.Count131072.C059059
import PlattCertificates.Count131072.C059060
import PlattCertificates.Count131072.C059061
import PlattCertificates.Count131072.C059062
import PlattCertificates.Count131072.C059063
import PlattCertificates.Count131072.C059064
import PlattCertificates.Count131072.C059065
import PlattCertificates.Count131072.C059066
import PlattCertificates.Count131072.C059067
import PlattCertificates.Count131072.C059068
import PlattCertificates.Count131072.C059069
import PlattCertificates.Count131072.C059070
import PlattCertificates.Count131072.C059071
import PlattCertificates.Count131072.C059072
import PlattCertificates.Count131072.C059073
import PlattCertificates.Count131072.C059074
import PlattCertificates.Count131072.C059075
import PlattCertificates.Count131072.C059076
import PlattCertificates.Count131072.C059077
import PlattCertificates.Count131072.C059078
import PlattCertificates.Count131072.C059079
import PlattCertificates.Count131072.C059080
import PlattCertificates.Count131072.C059081
import PlattCertificates.Count131072.C059082
import PlattCertificates.Count131072.C059083
import PlattCertificates.Count131072.C059084
import PlattCertificates.Count131072.C059085
import PlattCertificates.Count131072.C059086
import PlattCertificates.Count131072.C059087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000283
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59056 : List PrefixCut := [⟨64,209491029,209491148⟩]
theorem checked59056 : checkPrefixCuts (2^48) 7744520193 10 Manual.Count131072.C059056.packed 64 cuts59056 = true := by
 decide +kernel
def cuts59057 : List PrefixCut := [⟨14,44449147,44449174⟩,
⟨64,209414790,209414905⟩]
theorem checked59057 : checkPrefixCuts (2^48) 7744651265 10 Manual.Count131072.C059057.packed 64 cuts59057 = true := by
 decide +kernel
def pointBounds59057 : List (Nat × Nat × Nat) := [(7744679936,113721158755114,113721547050690)]
theorem point_links_checked59057 : (cuts59057.take 1).map (fun c => (7744651265-1+2*2^10*c.k,113721114305967+c.lower,113721502601516+c.upper)) = pointBounds59057 := by
 decide +kernel
def cuts59058 : List PrefixCut := [⟨64,205667869,205667994⟩]
theorem checked59058 : checkPrefixCuts (2^48) 7744782337 10 Manual.Count131072.C059058.packed 64 cuts59058 = true := by
 decide +kernel
def cuts59059 : List PrefixCut := [⟨5,16318084,16318093⟩,
⟨64,208971594,208971714⟩]
theorem checked59059 : checkPrefixCuts (2^48) 7744913409 10 Manual.Count131072.C059059.packed 64 cuts59059 = true := by
 decide +kernel
def pointBounds59059 : List (Nat × Nat × Nat) := [(7744923648,113721545706710,113721934002508)]
theorem point_links_checked59059 : (cuts59059.take 1).map (fun c => (7744913409-1+2*2^10*c.k,113721529388626+c.lower,113721917684415+c.upper)) = pointBounds59059 := by
 decide +kernel
def cuts59060 : List PrefixCut := [⟨60,194394907,194395018⟩,
⟨64,207550705,207550824⟩]
theorem checked59060 : checkPrefixCuts (2^48) 7745044481 10 Manual.Count131072.C059060.packed 64 cuts59060 = true := by
 decide +kernel
def pointBounds59060 : List (Nat × Nat × Nat) := [(7745167360,113721932755127,113722321051147)]
theorem point_links_checked59060 : (cuts59060.take 1).map (fun c => (7745044481-1+2*2^10*c.k,113721738360220+c.lower,113722126656129+c.upper)) = pointBounds59060 := by
 decide +kernel
def cuts59061 : List PrefixCut := [⟨64,209727711,209727830⟩]
theorem checked59061 : checkPrefixCuts (2^48) 7745175553 10 Manual.Count131072.C059061.packed 64 cuts59061 = true := by
 decide +kernel
def cuts59062 : List PrefixCut := [⟨51,166478600,166478696⟩,
⟨64,208670266,208670386⟩]
theorem checked59062 : checkPrefixCuts (2^48) 7745306625 10 Manual.Count131072.C059062.packed 64 cuts59062 = true := by
 decide +kernel
def pointBounds59062 : List (Nat × Nat × Nat) := [(7745411072,113722322117236,113722710413479)]
theorem point_links_checked59062 : (cuts59062.take 1).map (fun c => (7745306625-1+2*2^10*c.k,113722155638636+c.lower,113722543934783+c.upper)) = pointBounds59062 := by
 decide +kernel
def cuts59063 : List PrefixCut := [⟨64,208703080,208703199⟩]
theorem checked59063 : checkPrefixCuts (2^48) 7745437697 10 Manual.Count131072.C059063.packed 64 cuts59063 = true := by
 decide +kernel
def cuts59064 : List PrefixCut := [⟨42,138237059,138237138⟩,
⟨64,210480201,210480321⟩]
theorem checked59064 : checkPrefixCuts (2^48) 7745568769 10 Manual.Count131072.C059064.packed 64 cuts59064 = true := by
 decide +kernel
def pointBounds59064 : List (Nat × Nat × Nat) := [(7745654784,113722711249041,113723099545506)]
theorem point_links_checked59064 : (cuts59064.take 1).map (fun c => (7745568769-1+2*2^10*c.k,113722573011982+c.lower,113722961308368+c.upper)) = pointBounds59064 := by
 decide +kernel
def cuts59065 : List PrefixCut := [⟨64,211058063,211058187⟩]
theorem checked59065 : checkPrefixCuts (2^48) 7745699841 10 Manual.Count131072.C059065.packed 64 cuts59065 = true := by
 decide +kernel
def cuts59066 : List PrefixCut := [⟨33,106181777,106181840⟩,
⟨64,207238932,207239052⟩]
theorem checked59066 : checkPrefixCuts (2^48) 7745830913 10 Manual.Count131072.C059066.packed 64 cuts59066 = true := by
 decide +kernel
def pointBounds59066 : List (Nat × Nat × Nat) := [(7745898496,113723100732023,113723489028716)]
theorem point_links_checked59066 : (cuts59066.take 1).map (fun c => (7745830913-1+2*2^10*c.k,113722994550246+c.lower,113723382846876+c.upper)) = pointBounds59066 := by
 decide +kernel
def cuts59067 : List PrefixCut := [⟨64,214212333,214212454⟩]
theorem checked59067 : checkPrefixCuts (2^48) 7745961985 10 Manual.Count131072.C059067.packed 64 cuts59067 = true := by
 decide +kernel
def cuts59068 : List PrefixCut := [⟨24,78525435,78525478⟩,
⟨64,208976117,208976233⟩]
theorem checked59068 : checkPrefixCuts (2^48) 7746093057 10 Manual.Count131072.C059068.packed 64 cuts59068 = true := by
 decide +kernel
def pointBounds59068 : List (Nat × Nat × Nat) := [(7746142208,113723494526946,113723882823860)]
theorem point_links_checked59068 : (cuts59068.take 1).map (fun c => (7746093057-1+2*2^10*c.k,113723416001511+c.lower,113723804298382+c.upper)) = pointBounds59068 := by
 decide +kernel
def cuts59069 : List PrefixCut := [⟨64,206756042,206756162⟩]
theorem checked59069 : checkPrefixCuts (2^48) 7746224129 10 Manual.Count131072.C059069.packed 64 cuts59069 = true := by
 decide +kernel
def cuts59070 : List PrefixCut := [⟨15,48509036,48509065⟩,
⟨64,209768418,209768538⟩]
theorem checked59070 : checkPrefixCuts (2^48) 7746355201 10 Manual.Count131072.C059070.packed 64 cuts59070 = true := by
 decide +kernel
def pointBounds59070 : List (Nat × Nat × Nat) := [(7746385920,113723880242706,113724268539842)]
theorem point_links_checked59070 : (cuts59070.take 1).map (fun c => (7746355201-1+2*2^10*c.k,113723831733670+c.lower,113724220030777+c.upper)) = pointBounds59070 := by
 decide +kernel
def cuts59071 : List PrefixCut := [⟨64,207730110,207730227⟩]
theorem checked59071 : checkPrefixCuts (2^48) 7746486273 10 Manual.Count131072.C059071.packed 64 cuts59071 = true := by
 decide +kernel
def cuts59072 : List PrefixCut := [⟨6,20020680,20020692⟩,
⟨64,208380601,208380721⟩]
theorem checked59072 : checkPrefixCuts (2^48) 7746617345 10 Manual.Count131072.C059072.packed 64 cuts59072 = true := by
 decide +kernel
def pointBounds59072 : List (Nat × Nat × Nat) := [(7746629632,113724269252878,113724657550234)]
theorem point_links_checked59072 : (cuts59072.take 1).map (fun c => (7746617345-1+2*2^10*c.k,113724249232198+c.lower,113724637529542+c.upper)) = pointBounds59072 := by
 decide +kernel
def cuts59073 : List PrefixCut := [⟨61,200492617,200492731⟩,
⟨64,210230126,210230245⟩]
theorem checked59073 : checkPrefixCuts (2^48) 7746748417 10 Manual.Count131072.C059073.packed 64 cuts59073 = true := by
 decide +kernel
def pointBounds59073 : List (Nat × Nat × Nat) := [(7746873344,113724658105416,113725046402994)]
theorem point_links_checked59073 : (cuts59073.take 1).map (fun c => (7746748417-1+2*2^10*c.k,113724457612799+c.lower,113724845910263+c.upper)) = pointBounds59073 := by
 decide +kernel
def cuts59074 : List PrefixCut := [⟨64,209027568,209027686⟩]
theorem checked59074 : checkPrefixCuts (2^48) 7746879489 10 Manual.Count131072.C059074.packed 64 cuts59074 = true := by
 decide +kernel
def cuts59075 : List PrefixCut := [⟨52,167132281,167132381⟩,
⟨64,205863045,205863169⟩]
theorem checked59075 : checkPrefixCuts (2^48) 7747010561 10 Manual.Count131072.C059075.packed 64 cuts59075 = true := by
 decide +kernel
def pointBounds59075 : List (Nat × Nat × Nat) := [(7747117056,113725044002774,113725432300575)]
theorem point_links_checked59075 : (cuts59075.take 1).map (fun c => (7747010561-1+2*2^10*c.k,113724876870493+c.lower,113725265168194+c.upper)) = pointBounds59075 := by
 decide +kernel
def cuts59076 : List PrefixCut := [⟨64,210110459,210110581⟩]
theorem checked59076 : checkPrefixCuts (2^48) 7747141633 10 Manual.Count131072.C059076.packed 64 cuts59076 = true := by
 decide +kernel
def cuts59077 : List PrefixCut := [⟨43,139223913,139223994⟩,
⟨64,206691720,206691842⟩]
theorem checked59077 : checkPrefixCuts (2^48) 7747272705 10 Manual.Count131072.C059077.packed 64 cuts59077 = true := by
 decide +kernel
def pointBounds59077 : List (Nat × Nat × Nat) := [(7747360768,113725432067910,113725820365938)]
theorem point_links_checked59077 : (cuts59077.take 1).map (fun c => (7747272705-1+2*2^10*c.k,113725292843997+c.lower,113725681141944+c.upper)) = pointBounds59077 := by
 decide +kernel
def cuts59078 : List PrefixCut := [⟨64,209522047,209522167⟩]
theorem checked59078 : checkPrefixCuts (2^48) 7747403777 10 Manual.Count131072.C059078.packed 64 cuts59078 = true := by
 decide +kernel
def cuts59079 : List PrefixCut := [⟨34,111208381,111208447⟩,
⟨64,208610255,208610375⟩]
theorem checked59079 : checkPrefixCuts (2^48) 7747534849 10 Manual.Count131072.C059079.packed 64 cuts59079 = true := by
 decide +kernel
def pointBounds59079 : List (Nat × Nat × Nat) := [(7747604480,113725820266145,113726208564400)]
theorem point_links_checked59079 : (cuts59079.take 1).map (fun c => (7747534849-1+2*2^10*c.k,113725709057764+c.lower,113726097355953+c.upper)) = pointBounds59079 := by
 decide +kernel
def cuts59080 : List PrefixCut := [⟨64,209442299,209442419⟩]
theorem checked59080 : checkPrefixCuts (2^48) 7747665921 10 Manual.Count131072.C059080.packed 64 cuts59080 = true := by
 decide +kernel
def cuts59081 : List PrefixCut := [⟨25,82213774,82213822⟩,
⟨64,209329800,209329915⟩]
theorem checked59081 : checkPrefixCuts (2^48) 7747796993 10 Manual.Count131072.C059081.packed 64 cuts59081 = true := by
 decide +kernel
def pointBounds59081 : List (Nat × Nat × Nat) := [(7747848192,113726209324092,113726597622569)]
theorem point_links_checked59081 : (cuts59081.take 1).map (fun c => (7747796993-1+2*2^10*c.k,113726127110318+c.lower,113726515408747+c.upper)) = pointBounds59081 := by
 decide +kernel
def cuts59082 : List PrefixCut := [⟨64,208018382,208018499⟩]
theorem checked59082 : checkPrefixCuts (2^48) 7747928065 10 Manual.Count131072.C059082.packed 64 cuts59082 = true := by
 decide +kernel
def cuts59083 : List PrefixCut := [⟨16,53330036,53330067⟩,
⟨64,208995763,208995881⟩]
theorem checked59083 : checkPrefixCuts (2^48) 7748059137 10 Manual.Count131072.C059083.packed 64 cuts59083 = true := by
 decide +kernel
def pointBounds59083 : List (Nat × Nat × Nat) := [(7748091904,113726597788536,113726986087228)]
theorem point_links_checked59083 : (cuts59083.take 1).map (fun c => (7748059137-1+2*2^10*c.k,113726544458500+c.lower,113726932757161+c.upper)) = pointBounds59083 := by
 decide +kernel
def cuts59084 : List PrefixCut := [⟨64,208011360,208011482⟩]
theorem checked59084 : checkPrefixCuts (2^48) 7748190209 10 Manual.Count131072.C059084.packed 64 cuts59084 = true := by
 decide +kernel
def cuts59085 : List PrefixCut := [⟨7,22522849,22522863⟩,
⟨64,207935184,207935305⟩]
theorem checked59085 : checkPrefixCuts (2^48) 7748321281 10 Manual.Count131072.C059085.packed 64 cuts59085 = true := by
 decide +kernel
def pointBounds59085 : List (Nat × Nat × Nat) := [(7748335616,113726983988472,113727372287387)]
theorem point_links_checked59085 : (cuts59085.take 1).map (fun c => (7748321281-1+2*2^10*c.k,113726961465623+c.lower,113727349764524+c.upper)) = pointBounds59085 := by
 decide +kernel
def cuts59086 : List PrefixCut := [⟨62,200702793,200702910⟩,
⟨64,206660256,206660376⟩]
theorem checked59086 : checkPrefixCuts (2^48) 7748452353 10 Manual.Count131072.C059086.packed 64 cuts59086 = true := by
 decide +kernel
def pointBounds59086 : List (Nat × Nat × Nat) := [(7748579328,113727370103600,113727758402739)]
theorem point_links_checked59086 : (cuts59086.take 1).map (fun c => (7748452353-1+2*2^10*c.k,113727169400807+c.lower,113727557699829+c.upper)) = pointBounds59086 := by
 decide +kernel
def cuts59087 : List PrefixCut := [⟨64,209490186,209490307⟩]
theorem checked59087 : checkPrefixCuts (2^48) 7748583425 10 Manual.Count131072.C059087.packed 64 cuts59087 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000283
