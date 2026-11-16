import PlattAssemblyKernel
import PlattCertificates.Count131072.C066080
import PlattCertificates.Count131072.C066081
import PlattCertificates.Count131072.C066082
import PlattCertificates.Count131072.C066083
import PlattCertificates.Count131072.C066084
import PlattCertificates.Count131072.C066085
import PlattCertificates.Count131072.C066086
import PlattCertificates.Count131072.C066087
import PlattCertificates.Count131072.C066088
import PlattCertificates.Count131072.C066089
import PlattCertificates.Count131072.C066090
import PlattCertificates.Count131072.C066091
import PlattCertificates.Count131072.C066092
import PlattCertificates.Count131072.C066093
import PlattCertificates.Count131072.C066094
import PlattCertificates.Count131072.C066095
import PlattCertificates.Count131072.C066096
import PlattCertificates.Count131072.C066097
import PlattCertificates.Count131072.C066098
import PlattCertificates.Count131072.C066099
import PlattCertificates.Count131072.C066100
import PlattCertificates.Count131072.C066101
import PlattCertificates.Count131072.C066102
import PlattCertificates.Count131072.C066103
import PlattCertificates.Count131072.C066104
import PlattCertificates.Count131072.C066105
import PlattCertificates.Count131072.C066106
import PlattCertificates.Count131072.C066107
import PlattCertificates.Count131072.C066108
import PlattCertificates.Count131072.C066109
import PlattCertificates.Count131072.C066110
import PlattCertificates.Count131072.C066111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66080 : List PrefixCut := [⟨64,184472305,184472412⟩]
theorem checked66080 : checkPrefixCuts (2^48) 8665169921 10 Manual.Count131072.C066080.packed 64 cuts66080 = true := by
 decide +kernel
def cuts66081 : List PrefixCut := [⟨4,11758838,11758844⟩,
⟨64,185703863,185703967⟩]
theorem checked66081 : checkPrefixCuts (2^48) 8665300993 10 Manual.Count131072.C066081.packed 64 cuts66081 = true := by
 decide +kernel
def pointBounds66081 : List (Nat × Nat × Nat) := [(8665309184,115106287066995,115106676158690)]
theorem point_links_checked66081 : (cuts66081.take 1).map (fun c => (8665300993-1+2*2^10*c.k,115106275308157+c.lower,115106664399846+c.upper)) = pointBounds66081 := by
 decide +kernel
def cuts66082 : List PrefixCut := [⟨64,185018910,185019024⟩]
theorem checked66082 : checkPrefixCuts (2^48) 8665432065 10 Manual.Count131072.C066082.packed 64 cuts66082 = true := by
 decide +kernel
def cuts66083 : List PrefixCut := [⟨9,26115506,26115521⟩,
⟨64,185340924,185341039⟩]
theorem checked66083 : checkPrefixCuts (2^48) 8665563137 10 Manual.Count131072.C066083.packed 64 cuts66083 = true := by
 decide +kernel
def pointBounds66083 : List (Nat × Nat × Nat) := [(8665581568,115106672146436,115107061238358)]
theorem point_links_checked66083 : (cuts66083.take 1).map (fun c => (8665563137-1+2*2^10*c.k,115106646030930+c.lower,115107035122837+c.upper)) = pointBounds66083 := by
 decide +kernel
def cuts66084 : List PrefixCut := [⟨64,186052729,186052836⟩]
theorem checked66084 : checkPrefixCuts (2^48) 8665694209 10 Manual.Count131072.C066084.packed 64 cuts66084 = true := by
 decide +kernel
def cuts66085 : List PrefixCut := [⟨14,39561823,39561847⟩,
⟨64,182606952,182607059⟩]
theorem checked66085 : checkPrefixCuts (2^48) 8665825281 10 Manual.Count131072.C066085.packed 64 cuts66085 = true := by
 decide +kernel
def pointBounds66085 : List (Nat × Nat × Nat) := [(8665853952,115107056986406,115107446078559)]
theorem point_links_checked66085 : (cuts66085.take 1).map (fun c => (8665825281-1+2*2^10*c.k,115107017424583+c.lower,115107406516712+c.upper)) = pointBounds66085 := by
 decide +kernel
def cuts66086 : List PrefixCut := [⟨64,187898478,187898585⟩]
theorem checked66086 : checkPrefixCuts (2^48) 8665956353 10 Manual.Count131072.C066086.packed 64 cuts66086 = true := by
 decide +kernel
def cuts66087 : List PrefixCut := [⟨19,54728753,54728784⟩,
⟨64,184550206,184550312⟩]
theorem checked66087 : checkPrefixCuts (2^48) 8666087425 10 Manual.Count131072.C066087.packed 64 cuts66087 = true := by
 decide +kernel
def pointBounds66087 : List (Nat × Nat × Nat) := [(8666126336,115107442658766,115107831751140)]
theorem point_links_checked66087 : (cuts66087.take 1).map (fun c => (8666087425-1+2*2^10*c.k,115107387930013+c.lower,115107777022356+c.upper)) = pointBounds66087 := by
 decide +kernel
def cuts66088 : List PrefixCut := [⟨64,186820969,186821077⟩]
theorem checked66088 : checkPrefixCuts (2^48) 8666218497 10 Manual.Count131072.C066088.packed 64 cuts66088 = true := by
 decide +kernel
def cuts66089 : List PrefixCut := [⟨24,69472515,69472555⟩,
⟨64,185356603,185356714⟩]
theorem checked66089 : checkPrefixCuts (2^48) 8666349569 10 Manual.Count131072.C066089.packed 64 cuts66089 = true := by
 decide +kernel
def pointBounds66089 : List (Nat × Nat × Nat) := [(8666398720,115107828773703,115108217866300)]
theorem point_links_checked66089 : (cuts66089.take 1).map (fun c => (8666349569-1+2*2^10*c.k,115107759301188+c.lower,115108148393745+c.upper)) = pointBounds66089 := by
 decide +kernel
def cuts66090 : List PrefixCut := [⟨64,185191401,185191514⟩]
theorem checked66090 : checkPrefixCuts (2^48) 8666480641 10 Manual.Count131072.C066090.packed 64 cuts66090 = true := by
 decide +kernel
def cuts66091 : List PrefixCut := [⟨29,84215365,84215412⟩,
⟨64,188144078,188144182⟩]
theorem checked66091 : checkPrefixCuts (2^48) 8666611713 10 Manual.Count131072.C066091.packed 64 cuts66091 = true := by
 decide +kernel
def pointBounds66091 : List (Nat × Nat × Nat) := [(8666671104,115108214064557,115108603157385)]
theorem point_links_checked66091 : (cuts66091.take 1).map (fun c => (8666611713-1+2*2^10*c.k,115108129849192+c.lower,115108518941973+c.upper)) = pointBounds66091 := by
 decide +kernel
def cuts66092 : List PrefixCut := [⟨64,184373866,184373974⟩]
theorem checked66092 : checkPrefixCuts (2^48) 8666742785 10 Manual.Count131072.C066092.packed 64 cuts66092 = true := by
 decide +kernel
def cuts66093 : List PrefixCut := [⟨34,97008699,97008753⟩,
⟨64,183494200,183494308⟩]
theorem checked66093 : checkPrefixCuts (2^48) 8666873857 10 Manual.Count131072.C066093.packed 64 cuts66093 = true := by
 decide +kernel
def pointBounds66093 : List (Nat × Nat × Nat) := [(8666943488,115108599375835,115108988468882)]
theorem point_links_checked66093 : (cuts66093.take 1).map (fun c => (8666873857-1+2*2^10*c.k,115108502367136+c.lower,115108891460129+c.upper)) = pointBounds66093 := by
 decide +kernel
def cuts66094 : List PrefixCut := [⟨64,186446780,186446891⟩]
theorem checked66094 : checkPrefixCuts (2^48) 8667004929 10 Manual.Count131072.C066094.packed 64 cuts66094 = true := by
 decide +kernel
def cuts66095 : List PrefixCut := [⟨39,111067795,111067864⟩,
⟨64,183586076,183586184⟩]
theorem checked66095 : checkPrefixCuts (2^48) 8667136001 10 Manual.Count131072.C066095.packed 64 cuts66095 = true := by
 decide +kernel
def pointBounds66095 : List (Nat × Nat × Nat) := [(8667215872,115108983375911,115109372469192)]
theorem point_links_checked66095 : (cuts66095.take 1).map (fun c => (8667136001-1+2*2^10*c.k,115108872308116+c.lower,115109261401328+c.upper)) = pointBounds66095 := by
 decide +kernel
def cuts66096 : List PrefixCut := [⟨64,184947268,184947382⟩]
theorem checked66096 : checkPrefixCuts (2^48) 8667267073 10 Manual.Count131072.C066096.packed 64 cuts66096 = true := by
 decide +kernel
def cuts66097 : List PrefixCut := [⟨44,129185397,129185475⟩,
⟨64,185951200,185951315⟩]
theorem checked66097 : checkPrefixCuts (2^48) 8667398145 10 Manual.Count131072.C066097.packed 64 cuts66097 = true := by
 decide +kernel
def pointBounds66097 : List (Nat × Nat × Nat) := [(8667488256,115109370026857,115109759120369)]
theorem point_links_checked66097 : (cuts66097.take 1).map (fun c => (8667398145-1+2*2^10*c.k,115109240841460+c.lower,115109629934894+c.upper)) = pointBounds66097 := by
 decide +kernel
def cuts66098 : List PrefixCut := [⟨64,186273130,186273244⟩]
theorem checked66098 : checkPrefixCuts (2^48) 8667529217 10 Manual.Count131072.C066098.packed 64 cuts66098 = true := by
 decide +kernel
def cuts66099 : List PrefixCut := [⟨49,143015322,143015407⟩,
⟨64,188478524,188478633⟩]
theorem checked66099 : checkPrefixCuts (2^48) 8667660289 10 Manual.Count131072.C066099.packed 64 cuts66099 = true := by
 decide +kernel
def pointBounds66099 : List (Nat × Nat × Nat) := [(8667760640,115109756081112,115110145174860)]
theorem point_links_checked66099 : (cuts66099.take 1).map (fun c => (8667660289-1+2*2^10*c.k,115109613065790+c.lower,115110002159453+c.upper)) = pointBounds66099 := by
 decide +kernel
def cuts66100 : List PrefixCut := [⟨64,184416523,184416623⟩]
theorem checked66100 : checkPrefixCuts (2^48) 8667791361 10 Manual.Count131072.C066100.packed 64 cuts66100 = true := by
 decide +kernel
def cuts66101 : List PrefixCut := [⟨54,156617083,156617170⟩,
⟨64,185907472,185907576⟩]
theorem checked66101 : checkPrefixCuts (2^48) 8667922433 10 Manual.Count131072.C066101.packed 64 cuts66101 = true := by
 decide +kernel
def pointBounds66101 : List (Nat × Nat × Nat) := [(8668033024,115110142577920,115110531671879)]
theorem point_links_checked66101 : (cuts66101.take 1).map (fun c => (8667922433-1+2*2^10*c.k,115109985960837+c.lower,115110375054709+c.upper)) = pointBounds66101 := by
 decide +kernel
def cuts66102 : List PrefixCut := [⟨64,191197670,191197773⟩]
theorem checked66102 : checkPrefixCuts (2^48) 8668053505 10 Manual.Count131072.C066102.packed 64 cuts66102 = true := by
 decide +kernel
def cuts66103 : List PrefixCut := [⟨59,170510258,170510358⟩,
⟨64,184895227,184895336⟩]
theorem checked66103 : checkPrefixCuts (2^48) 8668184577 10 Manual.Count131072.C066103.packed 64 cuts66103 = true := by
 decide +kernel
def pointBounds66103 : List (Nat × Nat × Nat) := [(8668305408,115110533576237,115110922670416)]
theorem point_links_checked66103 : (cuts66103.take 1).map (fun c => (8668184577-1+2*2^10*c.k,115110363065979+c.lower,115110752160058+c.upper)) = pointBounds66103 := by
 decide +kernel
def cuts66104 : List PrefixCut := [⟨64,187068009,187068118⟩]
theorem checked66104 : checkPrefixCuts (2^48) 8668315649 10 Manual.Count131072.C066104.packed 64 cuts66104 = true := by
 decide +kernel
def cuts66105 : List PrefixCut := [⟨64,186415766,186415871⟩]
theorem checked66105 : checkPrefixCuts (2^48) 8668446721 10 Manual.Count131072.C066105.packed 64 cuts66105 = true := by
 decide +kernel
def pointBounds66105 : List (Nat × Nat × Nat) := [(8668577792,115110921444981,115111310539383)]
theorem point_links_checked66105 : (cuts66105.take 1).map (fun c => (8668446721-1+2*2^10*c.k,115110735029215+c.lower,115111124123512+c.upper)) = pointBounds66105 := by
 decide +kernel
def cuts66106 : List PrefixCut := [⟨64,184334834,184334939⟩]
theorem checked66106 : checkPrefixCuts (2^48) 8668577793 10 Manual.Count131072.C066106.packed 64 cuts66106 = true := by
 decide +kernel
def cuts66107 : List PrefixCut := [⟨64,186020482,186020586⟩]
theorem checked66107 : checkPrefixCuts (2^48) 8668708865 10 Manual.Count131072.C066107.packed 64 cuts66107 = true := by
 decide +kernel
def cuts66108 : List PrefixCut := [⟨5,14254204,14254212⟩,
⟨64,187381396,187381504⟩]
theorem checked66108 : checkPrefixCuts (2^48) 8668839937 10 Manual.Count131072.C066108.packed 64 cuts66108 = true := by
 decide +kernel
def pointBounds66108 : List (Nat × Nat × Nat) := [(8668850176,115111306054501,115111695149120)]
theorem point_links_checked66108 : (cuts66108.take 1).map (fun c => (8668839937-1+2*2^10*c.k,115111291800297+c.lower,115111680894908+c.upper)) = pointBounds66108 := by
 decide +kernel
def cuts66109 : List PrefixCut := [⟨64,187800659,187800762⟩]
theorem checked66109 : checkPrefixCuts (2^48) 8668971009 10 Manual.Count131072.C066109.packed 64 cuts66109 = true := by
 decide +kernel
def cuts66110 : List PrefixCut := [⟨10,27858152,27858170⟩,
⟨64,186174389,186174497⟩]
theorem checked66110 : checkPrefixCuts (2^48) 8669102081 10 Manual.Count131072.C066110.packed 64 cuts66110 = true := by
 decide +kernel
def pointBounds66110 : List (Nat × Nat × Nat) := [(8669122560,115111694840504,115112083935344)]
theorem point_links_checked66110 : (cuts66110.take 1).map (fun c => (8669102081-1+2*2^10*c.k,115111666982352+c.lower,115112056077174+c.upper)) = pointBounds66110 := by
 decide +kernel
def cuts66111 : List PrefixCut := [⟨64,184158553,184158664⟩]
theorem checked66111 : checkPrefixCuts (2^48) 8669233153 10 Manual.Count131072.C066111.packed 64 cuts66111 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000190
