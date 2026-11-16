import PlattAssemblyKernel
import PlattCertificates.Count131072.C066304
import PlattCertificates.Count131072.C066305
import PlattCertificates.Count131072.C066306
import PlattCertificates.Count131072.C066307
import PlattCertificates.Count131072.C066308
import PlattCertificates.Count131072.C066309
import PlattCertificates.Count131072.C066310
import PlattCertificates.Count131072.C066311
import PlattCertificates.Count131072.C066312
import PlattCertificates.Count131072.C066313
import PlattCertificates.Count131072.C066314
import PlattCertificates.Count131072.C066315
import PlattCertificates.Count131072.C066316
import PlattCertificates.Count131072.C066317
import PlattCertificates.Count131072.C066318
import PlattCertificates.Count131072.C066319
import PlattCertificates.Count131072.C066320
import PlattCertificates.Count131072.C066321
import PlattCertificates.Count131072.C066322
import PlattCertificates.Count131072.C066323
import PlattCertificates.Count131072.C066324
import PlattCertificates.Count131072.C066325
import PlattCertificates.Count131072.C066326
import PlattCertificates.Count131072.C066327
import PlattCertificates.Count131072.C066328
import PlattCertificates.Count131072.C066329
import PlattCertificates.Count131072.C066330
import PlattCertificates.Count131072.C066331
import PlattCertificates.Count131072.C066332
import PlattCertificates.Count131072.C066333
import PlattCertificates.Count131072.C066334
import PlattCertificates.Count131072.C066335
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000197
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66304 : List PrefixCut := [⟨64,182586806,182586911⟩]
theorem checked66304 : checkPrefixCuts (2^48) 8694530049 10 Manual.Count131072.C066304.packed 64 cuts66304 = true := by
 decide +kernel
def cuts66305 : List PrefixCut := [⟨32,92846281,92846336⟩,
⟨64,184396946,184397054⟩]
theorem checked66305 : checkPrefixCuts (2^48) 8694661121 10 Manual.Count131072.C066305.packed 64 cuts66305 = true := by
 decide +kernel
def pointBounds66305 : List (Nat × Nat × Nat) := [(8694726656,115147962927653,115148352043470)]
theorem point_links_checked66305 : (cuts66305.take 1).map (fun c => (8694661121-1+2*2^10*c.k,115147870081372+c.lower,115148259197134+c.upper)) = pointBounds66305 := by
 decide +kernel
def cuts66306 : List PrefixCut := [⟨64,184588419,184588519⟩]
theorem checked66306 : checkPrefixCuts (2^48) 8694792193 10 Manual.Count131072.C066306.packed 64 cuts66306 = true := by
 decide +kernel
def cuts66307 : List PrefixCut := [⟨37,108025978,108026043⟩,
⟨64,186527936,186528048⟩]
theorem checked66307 : checkPrefixCuts (2^48) 8694923265 10 Manual.Count131072.C066307.packed 64 cuts66307 = true := by
 decide +kernel
def pointBounds66307 : List (Nat × Nat × Nat) := [(8694999040,115148347092715,115148736208750)]
theorem point_links_checked66307 : (cuts66307.take 1).map (fun c => (8694923265-1+2*2^10*c.k,115148239066737+c.lower,115148628182707+c.upper)) = pointBounds66307 := by
 decide +kernel
def cuts66308 : List PrefixCut := [⟨64,183773547,183773652⟩]
theorem checked66308 : checkPrefixCuts (2^48) 8695054337 10 Manual.Count131072.C066308.packed 64 cuts66308 = true := by
 decide +kernel
def cuts66309 : List PrefixCut := [⟨42,124629076,124629149⟩,
⟨64,188173243,188173355⟩]
theorem checked66309 : checkPrefixCuts (2^48) 8695185409 10 Manual.Count131072.C066309.packed 64 cuts66309 = true := by
 decide +kernel
def pointBounds66309 : List (Nat × Nat × Nat) := [(8695271424,115148733997296,115149123113556)]
theorem point_links_checked66309 : (cuts66309.take 1).map (fun c => (8695185409-1+2*2^10*c.k,115148609368220+c.lower,115148998484407+c.upper)) = pointBounds66309 := by
 decide +kernel
def cuts66310 : List PrefixCut := [⟨64,182699770,182699882⟩]
theorem checked66310 : checkPrefixCuts (2^48) 8695316481 10 Manual.Count131072.C066310.packed 64 cuts66310 = true := by
 decide +kernel
def cuts66311 : List PrefixCut := [⟨47,135339784,135339866⟩,
⟨64,184153672,184153781⟩]
theorem checked66311 : checkPrefixCuts (2^48) 8695447553 10 Manual.Count131072.C066311.packed 64 cuts66311 = true := by
 decide +kernel
def pointBounds66311 : List (Nat × Nat × Nat) := [(8695543808,115149115581017,115149504697510)]
theorem point_links_checked66311 : (cuts66311.take 1).map (fun c => (8695447553-1+2*2^10*c.k,115148980241233+c.lower,115149369357644+c.upper)) = pointBounds66311 := by
 decide +kernel
def cuts66312 : List PrefixCut := [⟨64,184442222,184442331⟩]
theorem checked66312 : checkPrefixCuts (2^48) 8695578625 10 Manual.Count131072.C066312.packed 64 cuts66312 = true := by
 decide +kernel
def cuts66313 : List PrefixCut := [⟨52,152199978,152200065⟩,
⟨64,187028975,187029085⟩]
theorem checked66313 : checkPrefixCuts (2^48) 8695709697 10 Manual.Count131072.C066313.packed 64 cuts66313 = true := by
 decide +kernel
def pointBounds66313 : List (Nat × Nat × Nat) := [(8695816192,115149501037105,115149890153821)]
theorem point_links_checked66313 : (cuts66313.take 1).map (fun c => (8695709697-1+2*2^10*c.k,115149348837127+c.lower,115149737953756+c.upper)) = pointBounds66313 := by
 decide +kernel
def cuts66314 : List PrefixCut := [⟨64,184825086,184825194⟩]
theorem checked66314 : checkPrefixCuts (2^48) 8695840769 10 Manual.Count131072.C066314.packed 64 cuts66314 = true := by
 decide +kernel
def cuts66315 : List PrefixCut := [⟨57,163524160,163524257⟩,
⟨64,183851241,183851349⟩]
theorem checked66315 : checkPrefixCuts (2^48) 8695971841 10 Manual.Count131072.C066315.packed 64 cuts66315 = true := by
 decide +kernel
def pointBounds66315 : List (Nat × Nat × Nat) := [(8696088576,115149884215348,115150273332292)]
theorem point_links_checked66315 : (cuts66315.take 1).map (fun c => (8695971841-1+2*2^10*c.k,115149720691188+c.lower,115150109808035+c.upper)) = pointBounds66315 := by
 decide +kernel
def cuts66316 : List PrefixCut := [⟨64,182553777,182553881⟩]
theorem checked66316 : checkPrefixCuts (2^48) 8696102913 10 Manual.Count131072.C066316.packed 64 cuts66316 = true := by
 decide +kernel
def cuts66317 : List PrefixCut := [⟨62,182939483,182939586⟩,
⟨64,188668436,188668543⟩]
theorem checked66317 : checkPrefixCuts (2^48) 8696233985 10 Manual.Count131072.C066317.packed 64 cuts66317 = true := by
 decide +kernel
def pointBounds66317 : List (Nat × Nat × Nat) := [(8696360960,115150270035689,115150659152851)]
theorem point_links_checked66317 : (cuts66317.take 1).map (fun c => (8696233985-1+2*2^10*c.k,115150087096206+c.lower,115150476213265+c.upper)) = pointBounds66317 := by
 decide +kernel
def cuts66318 : List PrefixCut := [⟨64,188633219,188633327⟩]
theorem checked66318 : checkPrefixCuts (2^48) 8696365057 10 Manual.Count131072.C066318.packed 64 cuts66318 = true := by
 decide +kernel
def cuts66319 : List PrefixCut := [⟨64,185296653,185296764⟩]
theorem checked66319 : checkPrefixCuts (2^48) 8696496129 10 Manual.Count131072.C066319.packed 64 cuts66319 = true := by
 decide +kernel
def cuts66320 : List PrefixCut := [⟨3,8123859,8123863⟩,
⟨64,186103008,186103109⟩]
theorem checked66320 : checkPrefixCuts (2^48) 8696627201 10 Manual.Count131072.C066320.packed 64 cuts66320 = true := by
 decide +kernel
def pointBounds66320 : List (Nat × Nat × Nat) := [(8696633344,115150657818373,115151046935762)]
theorem point_links_checked66320 : (cuts66320.take 1).map (fun c => (8696627201-1+2*2^10*c.k,115150649694514+c.lower,115151038811899+c.upper)) = pointBounds66320 := by
 decide +kernel
def cuts66321 : List PrefixCut := [⟨64,185679449,185679554⟩]
theorem checked66321 : checkPrefixCuts (2^48) 8696758273 10 Manual.Count131072.C066321.packed 64 cuts66321 = true := by
 decide +kernel
def cuts66322 : List PrefixCut := [⟨8,22752580,22752592⟩,
⟨64,188265819,188265925⟩]
theorem checked66322 : checkPrefixCuts (2^48) 8696889345 10 Manual.Count131072.C066322.packed 64 cuts66322 = true := by
 decide +kernel
def pointBounds66322 : List (Nat × Nat × Nat) := [(8696905728,115151044229551,115151433347154)]
theorem point_links_checked66322 : (cuts66322.take 1).map (fun c => (8696889345-1+2*2^10*c.k,115151021476971+c.lower,115151410594562+c.upper)) = pointBounds66322 := by
 decide +kernel
def cuts66323 : List PrefixCut := [⟨64,185868044,185868156⟩]
theorem checked66323 : checkPrefixCuts (2^48) 8697020417 10 Manual.Count131072.C066323.packed 64 cuts66323 = true := by
 decide +kernel
def cuts66324 : List PrefixCut := [⟨13,37315671,37315694⟩,
⟨64,186383055,186383171⟩]
theorem checked66324 : checkPrefixCuts (2^48) 8697151489 10 Manual.Count131072.C066324.packed 64 cuts66324 = true := by
 decide +kernel
def pointBounds66324 : List (Nat × Nat × Nat) := [(8697178112,115151432926505,115151822044337)]
theorem point_links_checked66324 : (cuts66324.take 1).map (fun c => (8697151489-1+2*2^10*c.k,115151395610834+c.lower,115151784728643+c.upper)) = pointBounds66324 := by
 decide +kernel
def cuts66325 : List PrefixCut := [⟨64,186380263,186380369⟩]
theorem checked66325 : checkPrefixCuts (2^48) 8697282561 10 Manual.Count131072.C066325.packed 64 cuts66325 = true := by
 decide +kernel
def cuts66326 : List PrefixCut := [⟨18,51845508,51845539⟩,
⟨64,185665459,185665576⟩]
theorem checked66326 : checkPrefixCuts (2^48) 8697413633 10 Manual.Count131072.C066326.packed 64 cuts66326 = true := by
 decide +kernel
def pointBounds66326 : List (Nat × Nat × Nat) := [(8697450496,115151820219660,115152209337722)]
theorem point_links_checked66326 : (cuts66326.take 1).map (fun c => (8697413633-1+2*2^10*c.k,115151768374152+c.lower,115152157492183+c.upper)) = pointBounds66326 := by
 decide +kernel
def cuts66327 : List PrefixCut := [⟨64,186180475,186180586⟩]
theorem checked66327 : checkPrefixCuts (2^48) 8697544705 10 Manual.Count131072.C066327.packed 64 cuts66327 = true := by
 decide +kernel
def cuts66328 : List PrefixCut := [⟨23,65274142,65274180⟩,
⟨64,183232719,183232827⟩]
theorem checked66328 : checkPrefixCuts (2^48) 8697675777 10 Manual.Count131072.C066328.packed 64 cuts66328 = true := by
 decide +kernel
def pointBounds66328 : List (Nat × Nat × Nat) := [(8697722880,115152205494228,115152594612525)]
theorem point_links_checked66328 : (cuts66328.take 1).map (fun c => (8697675777-1+2*2^10*c.k,115152140220086+c.lower,115152529338345+c.upper)) = pointBounds66328 := by
 decide +kernel
def cuts66329 : List PrefixCut := [⟨64,184427336,184427445⟩]
theorem checked66329 : checkPrefixCuts (2^48) 8697806849 10 Manual.Count131072.C066329.packed 64 cuts66329 = true := by
 decide +kernel
def cuts66330 : List PrefixCut := [⟨28,83167769,83167819⟩,
⟨64,186495663,186495772⟩]
theorem checked66330 : checkPrefixCuts (2^48) 8697937921 10 Manual.Count131072.C066330.packed 64 cuts66330 = true := by
 decide +kernel
def pointBounds66330 : List (Nat × Nat × Nat) := [(8697995264,115152591047910,115152980166436)]
theorem point_links_checked66330 : (cuts66330.take 1).map (fun c => (8697937921-1+2*2^10*c.k,115152507880141+c.lower,115152896998617+c.upper)) = pointBounds66330 := by
 decide +kernel
def cuts66331 : List PrefixCut := [⟨64,187042965,187043078⟩]
theorem checked66331 : checkPrefixCuts (2^48) 8698068993 10 Manual.Count131072.C066331.packed 64 cuts66331 = true := by
 decide +kernel
def cuts66332 : List PrefixCut := [⟨33,95559095,95559151⟩,
⟨64,184030687,184030793⟩]
theorem checked66332 : checkPrefixCuts (2^48) 8698200065 10 Manual.Count131072.C066332.packed 64 cuts66332 = true := by
 decide +kernel
def pointBounds66332 : List (Nat × Nat × Nat) := [(8698267648,115152976977864,115153366096618)]
theorem point_links_checked66332 : (cuts66332.take 1).map (fun c => (8698200065-1+2*2^10*c.k,115152881418769+c.lower,115153270537467+c.upper)) = pointBounds66332 := by
 decide +kernel
def cuts66333 : List PrefixCut := [⟨64,184804534,184804637⟩]
theorem checked66333 : checkPrefixCuts (2^48) 8698331137 10 Manual.Count131072.C066333.packed 64 cuts66333 = true := by
 decide +kernel
def cuts66334 : List PrefixCut := [⟨38,109923558,109923622⟩,
⟨64,185060618,185060726⟩]
theorem checked66334 : checkPrefixCuts (2^48) 8698462209 10 Manual.Count131072.C066334.packed 64 cuts66334 = true := by
 decide +kernel
def pointBounds66334 : List (Nat × Nat × Nat) := [(8698540032,115153360177548,115153749296519)]
theorem point_links_checked66334 : (cuts66334.take 1).map (fun c => (8698462209-1+2*2^10*c.k,115153250253990+c.lower,115153639372897+c.upper)) = pointBounds66334 := by
 decide +kernel
def cuts66335 : List PrefixCut := [⟨64,183051601,183051706⟩]
theorem checked66335 : checkPrefixCuts (2^48) 8698593281 10 Manual.Count131072.C066335.packed 64 cuts66335 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000197
