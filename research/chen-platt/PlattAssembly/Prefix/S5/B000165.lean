import PlattAssemblyKernel
import PlattCertificates.Count131072.C045280
import PlattCertificates.Count131072.C045281
import PlattCertificates.Count131072.C045282
import PlattCertificates.Count131072.C045283
import PlattCertificates.Count131072.C045284
import PlattCertificates.Count131072.C045285
import PlattCertificates.Count131072.C045286
import PlattCertificates.Count131072.C045287
import PlattCertificates.Count131072.C045288
import PlattCertificates.Count131072.C045289
import PlattCertificates.Count131072.C045290
import PlattCertificates.Count131072.C045291
import PlattCertificates.Count131072.C045292
import PlattCertificates.Count131072.C045293
import PlattCertificates.Count131072.C045294
import PlattCertificates.Count131072.C045295
import PlattCertificates.Count131072.C045296
import PlattCertificates.Count131072.C045297
import PlattCertificates.Count131072.C045298
import PlattCertificates.Count131072.C045299
import PlattCertificates.Count131072.C045300
import PlattCertificates.Count131072.C045301
import PlattCertificates.Count131072.C045302
import PlattCertificates.Count131072.C045303
import PlattCertificates.Count131072.C045304
import PlattCertificates.Count131072.C045305
import PlattCertificates.Count131072.C045306
import PlattCertificates.Count131072.C045307
import PlattCertificates.Count131072.C045308
import PlattCertificates.Count131072.C045309
import PlattCertificates.Count131072.C045310
import PlattCertificates.Count131072.C045311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45280 : List PrefixCut := [⟨64,271667119,271667270⟩]
theorem checked45280 : checkPrefixCuts (2^48) 5938872321 10 Manual.Count131072.C045280.packed 64 cuts45280 = true := by
 decide +kernel
def cuts45281 : List PrefixCut := [⟨27,116589424,116589493⟩,
⟨64,277537936,277538100⟩]
theorem checked45281 : checkPrefixCuts (2^48) 5939003393 10 Manual.Count131072.C045281.packed 64 cuts45281 = true := by
 decide +kernel
def pointBounds45281 : List (Nat × Nat × Nat) := [(5939058688,110420528827530,110420915241816)]
theorem point_links_checked45281 : (cuts45281.take 1).map (fun c => (5939003393-1+2*2^10*c.k,110420412238106+c.lower,110420798652323+c.upper)) = pointBounds45281 := by
 decide +kernel
def cuts45282 : List PrefixCut := [⟨54,234262661,234262799⟩,
⟨64,277579213,277579372⟩]
theorem checked45282 : checkPrefixCuts (2^48) 5939134465 10 Manual.Count131072.C045282.packed 64 cuts45282 = true := by
 decide +kernel
def pointBounds45282 : List (Nat × Nat × Nat) := [(5939245056,110420924038703,110421310453222)]
theorem point_links_checked45282 : (cuts45282.take 1).map (fun c => (5939134465-1+2*2^10*c.k,110420689776042+c.lower,110421076190423+c.upper)) = pointBounds45282 := by
 decide +kernel
def cuts45283 : List PrefixCut := [⟨64,275961763,275961922⟩]
theorem checked45283 : checkPrefixCuts (2^48) 5939265537 10 Manual.Count131072.C045283.packed 64 cuts45283 = true := by
 decide +kernel
def cuts45284 : List PrefixCut := [⟨17,73740428,73740473⟩,
⟨64,277709126,277709293⟩]
theorem checked45284 : checkPrefixCuts (2^48) 5939396609 10 Manual.Count131072.C045284.packed 64 cuts45284 = true := by
 decide +kernel
def pointBounds45284 : List (Nat × Nat × Nat) := [(5939431424,110421317057446,110421703472190)]
theorem point_links_checked45284 : (cuts45284.take 1).map (fun c => (5939396609-1+2*2^10*c.k,110421243317018+c.lower,110421629731717+c.upper)) = pointBounds45284 := by
 decide +kernel
def cuts45285 : List PrefixCut := [⟨44,186573459,186573566⟩,
⟨64,273532699,273532858⟩]
theorem checked45285 : checkPrefixCuts (2^48) 5939527681 10 Manual.Count131072.C045285.packed 64 cuts45285 = true := by
 decide +kernel
def pointBounds45285 : List (Nat × Nat × Nat) := [(5939617792,110421707599603,110422094014576)]
theorem point_links_checked45285 : (cuts45285.take 1).map (fun c => (5939527681-1+2*2^10*c.k,110421521026144+c.lower,110421907441010+c.upper)) = pointBounds45285 := by
 decide +kernel
def cuts45286 : List PrefixCut := [⟨64,276606928,276607089⟩]
theorem checked45286 : checkPrefixCuts (2^48) 5939658753 10 Manual.Count131072.C045286.packed 64 cuts45286 = true := by
 decide +kernel
def cuts45287 : List PrefixCut := [⟨7,30280910,30280928⟩,
⟨64,279112368,279112530⟩]
theorem checked45287 : checkPrefixCuts (2^48) 5939789825 10 Manual.Count131072.C045287.packed 64 cuts45287 = true := by
 decide +kernel
def pointBounds45287 : List (Nat × Nat × Nat) := [(5939804160,110422101446681,110422487861885)]
theorem point_links_checked45287 : (cuts45287.take 1).map (fun c => (5939789825-1+2*2^10*c.k,110422071165771+c.lower,110422457580957+c.upper)) = pointBounds45287 := by
 decide +kernel
def cuts45288 : List PrefixCut := [⟨34,147656964,147657046⟩,
⟨64,275931347,275931500⟩]
theorem checked45288 : checkPrefixCuts (2^48) 5939920897 10 Manual.Count131072.C045288.packed 64 cuts45288 = true := by
 decide +kernel
def pointBounds45288 : List (Nat × Nat × Nat) := [(5939990528,110422497935103,110422884350533)]
theorem point_links_checked45288 : (cuts45288.take 1).map (fun c => (5939920897-1+2*2^10*c.k,110422350278139+c.lower,110422736693487+c.upper)) = pointBounds45288 := by
 decide +kernel
def cuts45289 : List PrefixCut := [⟨61,261804503,261804654⟩,
⟨64,274977509,274977666⟩]
theorem checked45289 : checkPrefixCuts (2^48) 5940051969 10 Manual.Count131072.C045289.packed 64 cuts45289 = true := by
 decide +kernel
def pointBounds45289 : List (Nat × Nat × Nat) := [(5940176896,110422888013989,110423274429641)]
theorem point_links_checked45289 : (cuts45289.take 1).map (fun c => (5940051969-1+2*2^10*c.k,110422626209486+c.lower,110423012624987+c.upper)) = pointBounds45289 := by
 decide +kernel
def cuts45290 : List PrefixCut := [⟨64,271180682,271180842⟩]
theorem checked45290 : checkPrefixCuts (2^48) 5940183041 10 Manual.Count131072.C045290.packed 64 cuts45290 = true := by
 decide +kernel
def cuts45291 : List PrefixCut := [⟨24,102727737,102727800⟩,
⟨64,272406703,272406864⟩]
theorem checked45291 : checkPrefixCuts (2^48) 5940314113 10 Manual.Count131072.C045291.packed 64 cuts45291 = true := by
 decide +kernel
def pointBounds45291 : List (Nat × Nat × Nat) := [(5940363264,110423275095414,110423661511295)]
theorem point_links_checked45291 : (cuts45291.take 1).map (fun c => (5940314113-1+2*2^10*c.k,110423172367677+c.lower,110423558783495+c.upper)) = pointBounds45291 := by
 decide +kernel
def cuts45292 : List PrefixCut := [⟨51,221891675,221891803⟩,
⟨64,277565354,277565512⟩]
theorem checked45292 : checkPrefixCuts (2^48) 5940445185 10 Manual.Count131072.C045292.packed 64 cuts45292 = true := by
 decide +kernel
def pointBounds45292 : List (Nat × Nat × Nat) := [(5940549632,110423666666055,110424053082162)]
theorem point_links_checked45292 : (cuts45292.take 1).map (fun c => (5940445185-1+2*2^10*c.k,110423444774380+c.lower,110423831190359+c.upper)) = pointBounds45292 := by
 decide +kernel
def cuts45293 : List PrefixCut := [⟨64,277890887,277891052⟩]
theorem checked45293 : checkPrefixCuts (2^48) 5940576257 10 Manual.Count131072.C045293.packed 64 cuts45293 = true := by
 decide +kernel
def cuts45294 : List PrefixCut := [⟨14,59320503,59320535⟩,
⟨64,274141747,274141903⟩]
theorem checked45294 : checkPrefixCuts (2^48) 5940707329 10 Manual.Count131072.C045294.packed 64 cuts45294 = true := by
 decide +kernel
def pointBounds45294 : List (Nat × Nat × Nat) := [(5940736000,110424059551124,110424445967458)]
theorem point_links_checked45294 : (cuts45294.take 1).map (fun c => (5940707329-1+2*2^10*c.k,110424000230621+c.lower,110424386646923+c.upper)) = pointBounds45294 := by
 decide +kernel
def cuts45295 : List PrefixCut := [⟨41,175398252,175398351⟩,
⟨64,273282861,273283016⟩]
theorem checked45295 : checkPrefixCuts (2^48) 5940838401 10 Manual.Count131072.C045295.packed 64 cuts45295 = true := by
 decide +kernel
def pointBounds45295 : List (Nat × Nat × Nat) := [(5940922368,110424449770620,110424836187177)]
theorem point_links_checked45295 : (cuts45295.take 1).map (fun c => (5940838401-1+2*2^10*c.k,110424274372368+c.lower,110424660788826+c.upper)) = pointBounds45295 := by
 decide +kernel
def cuts45296 : List PrefixCut := [⟨64,274319132,274319292⟩]
theorem checked45296 : checkPrefixCuts (2^48) 5940969473 10 Manual.Count131072.C045296.packed 64 cuts45296 = true := by
 decide +kernel
def cuts45297 : List PrefixCut := [⟨4,18192974,18192984⟩,
⟨64,277676867,277677023⟩]
theorem checked45297 : checkPrefixCuts (2^48) 5941100545 10 Manual.Count131072.C045297.packed 64 cuts45297 = true := by
 decide +kernel
def pointBounds45297 : List (Nat × Nat × Nat) := [(5941108736,110424840167335,110425226584118)]
theorem point_links_checked45297 : (cuts45297.take 1).map (fun c => (5941100545-1+2*2^10*c.k,110424821974361+c.lower,110425208391134+c.upper)) = pointBounds45297 := by
 decide +kernel
def cuts45298 : List PrefixCut := [⟨31,134738099,134738177⟩,
⟨64,280465911,280466070⟩]
theorem checked45298 : checkPrefixCuts (2^48) 5941231617 10 Manual.Count131072.C045298.packed 64 cuts45298 = true := by
 decide +kernel
def pointBounds45298 : List (Nat × Nat × Nat) := [(5941295104,110425234389327,110425620806334)]
theorem point_links_checked45298 : (cuts45298.take 1).map (fun c => (5941231617-1+2*2^10*c.k,110425099651228+c.lower,110425486068157+c.upper)) = pointBounds45298 := by
 decide +kernel
def cuts45299 : List PrefixCut := [⟨58,251987646,251987789⟩,
⟨64,277569868,277570024⟩]
theorem checked45299 : checkPrefixCuts (2^48) 5941362689 10 Manual.Count131072.C045299.packed 64 cuts45299 = true := by
 decide +kernel
def pointBounds45299 : List (Nat × Nat × Nat) := [(5941481472,110425632104785,110426018522016)]
theorem point_links_checked45299 : (cuts45299.take 1).map (fun c => (5941362689-1+2*2^10*c.k,110425380117139+c.lower,110425766534227+c.upper)) = pointBounds45299 := by
 decide +kernel
def cuts45300 : List PrefixCut := [⟨64,275431902,275432066⟩]
theorem checked45300 : checkPrefixCuts (2^48) 5941493761 10 Manual.Count131072.C045300.packed 64 cuts45300 = true := by
 decide +kernel
def cuts45301 : List PrefixCut := [⟨21,92330401,92330455⟩,
⟨64,279405156,279405320⟩]
theorem checked45301 : checkPrefixCuts (2^48) 5941624833 10 Manual.Count131072.C045301.packed 64 cuts45301 = true := by
 decide +kernel
def pointBounds45301 : List (Nat × Nat × Nat) := [(5941667840,110426025449310,110426411866772)]
theorem point_links_checked45301 : (cuts45301.take 1).map (fun c => (5941624833-1+2*2^10*c.k,110425933118909+c.lower,110426319536317+c.upper)) = pointBounds45301 := by
 decide +kernel
def cuts45302 : List PrefixCut := [⟨48,209857764,209857879⟩,
⟨64,280393820,280393974⟩]
theorem checked45302 : checkPrefixCuts (2^48) 5941755905 10 Manual.Count131072.C045302.packed 64 cuts45302 = true := by
 decide +kernel
def pointBounds45302 : List (Nat × Nat × Nat) := [(5941854208,110426422381829,110426808799516)]
theorem point_links_checked45302 : (cuts45302.take 1).map (fun c => (5941755905-1+2*2^10*c.k,110426212524065+c.lower,110426598941637+c.upper)) = pointBounds45302 := by
 decide +kernel
def cuts45303 : List PrefixCut := [⟨64,276692725,276692881⟩]
theorem checked45303 : checkPrefixCuts (2^48) 5941886977 10 Manual.Count131072.C045303.packed 64 cuts45303 = true := by
 decide +kernel
def cuts45304 : List PrefixCut := [⟨11,47322792,47322819⟩,
⟨64,275028656,275028816⟩]
theorem checked45304 : checkPrefixCuts (2^48) 5942018049 10 Manual.Count131072.C045304.packed 64 cuts45304 = true := by
 decide +kernel
def pointBounds45304 : List (Nat × Nat × Nat) := [(5942040576,110426816933402,110427203351311)]
theorem point_links_checked45304 : (cuts45304.take 1).map (fun c => (5942018049-1+2*2^10*c.k,110426769610610+c.lower,110427156028492+c.upper)) = pointBounds45304 := by
 decide +kernel
def cuts45305 : List PrefixCut := [⟨38,164227980,164228070⟩,
⟨64,277769981,277770135⟩]
theorem checked45305 : checkPrefixCuts (2^48) 5942149121 10 Manual.Count131072.C045305.packed 64 cuts45305 = true := by
 decide +kernel
def pointBounds45305 : List (Nat × Nat × Nat) := [(5942226944,110427208867246,110427595285378)]
theorem point_links_checked45305 : (cuts45305.take 1).map (fun c => (5942149121-1+2*2^10*c.k,110427044639266+c.lower,110427431057308+c.upper)) = pointBounds45305 := by
 decide +kernel
def cuts45306 : List PrefixCut := [⟨64,274448092,274448251⟩]
theorem checked45306 : checkPrefixCuts (2^48) 5942280193 10 Manual.Count131072.C045306.packed 64 cuts45306 = true := by
 decide +kernel
def cuts45307 : List PrefixCut := [⟨1,4073571,4073574⟩,
⟨64,274157863,274158018⟩]
theorem checked45307 : checkPrefixCuts (2^48) 5942411265 10 Manual.Count131072.C045307.packed 64 cuts45307 = true := by
 decide +kernel
def pointBounds45307 : List (Nat × Nat × Nat) := [(5942413312,110427600930910,110427987349268)]
theorem point_links_checked45307 : (cuts45307.take 1).map (fun c => (5942411265-1+2*2^10*c.k,110427596857339+c.lower,110427983275694+c.upper)) = pointBounds45307 := by
 decide +kernel
def cuts45308 : List PrefixCut := [⟨28,120924995,120925066⟩,
⟨64,278319971,278320133⟩]
theorem checked45308 : checkPrefixCuts (2^48) 5942542337 10 Manual.Count131072.C045308.packed 64 cuts45308 = true := by
 decide +kernel
def pointBounds45308 : List (Nat × Nat × Nat) := [(5942599680,110427991940197,110428378358778)]
theorem point_links_checked45308 : (cuts45308.take 1).map (fun c => (5942542337-1+2*2^10*c.k,110427871015202+c.lower,110428257433712+c.upper)) = pointBounds45308 := by
 decide +kernel
def cuts45309 : List PrefixCut := [⟨55,235780902,235781036⟩,
⟨64,275140433,275140588⟩]
theorem checked45309 : checkPrefixCuts (2^48) 5942673409 10 Manual.Count131072.C045309.packed 64 cuts45309 = true := by
 decide +kernel
def pointBounds45309 : List (Nat × Nat × Nat) := [(5942786048,110428385116075,110428771534881)]
theorem point_links_checked45309 : (cuts45309.take 1).map (fun c => (5942673409-1+2*2^10*c.k,110428149335173+c.lower,110428535753845+c.upper)) = pointBounds45309 := by
 decide +kernel
def cuts45310 : List PrefixCut := [⟨64,274471244,274471405⟩]
theorem checked45310 : checkPrefixCuts (2^48) 5942804481 10 Manual.Count131072.C045310.packed 64 cuts45310 = true := by
 decide +kernel
def cuts45311 : List PrefixCut := [⟨18,77864431,77864479⟩,
⟨64,275933449,275933609⟩]
theorem checked45311 : checkPrefixCuts (2^48) 5942935553 10 Manual.Count131072.C045311.packed 64 cuts45311 = true := by
 decide +kernel
def pointBounds45311 : List (Nat × Nat × Nat) := [(5942972416,110428776811281,110429163230317)]
theorem point_links_checked45311 : (cuts45311.take 1).map (fun c => (5942935553-1+2*2^10*c.k,110428698946850+c.lower,110429085365838+c.upper)) = pointBounds45311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000165
