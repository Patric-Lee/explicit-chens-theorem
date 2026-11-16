import PlattAssemblyKernel
import PlattCertificates.Count131072.C051280
import PlattCertificates.Count131072.C051281
import PlattCertificates.Count131072.C051282
import PlattCertificates.Count131072.C051283
import PlattCertificates.Count131072.C051284
import PlattCertificates.Count131072.C051285
import PlattCertificates.Count131072.C051286
import PlattCertificates.Count131072.C051287
import PlattCertificates.Count131072.C051288
import PlattCertificates.Count131072.C051289
import PlattCertificates.Count131072.C051290
import PlattCertificates.Count131072.C051291
import PlattCertificates.Count131072.C051292
import PlattCertificates.Count131072.C051293
import PlattCertificates.Count131072.C051294
import PlattCertificates.Count131072.C051295
import PlattCertificates.Count131072.C051296
import PlattCertificates.Count131072.C051297
import PlattCertificates.Count131072.C051298
import PlattCertificates.Count131072.C051299
import PlattCertificates.Count131072.C051300
import PlattCertificates.Count131072.C051301
import PlattCertificates.Count131072.C051302
import PlattCertificates.Count131072.C051303
import PlattCertificates.Count131072.C051304
import PlattCertificates.Count131072.C051305
import PlattCertificates.Count131072.C051306
import PlattCertificates.Count131072.C051307
import PlattCertificates.Count131072.C051308
import PlattCertificates.Count131072.C051309
import PlattCertificates.Count131072.C051310
import PlattCertificates.Count131072.C051311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51280 : List PrefixCut := [⟨64,242117880,242118019⟩]
theorem checked51280 : checkPrefixCuts (2^48) 6725304321 10 Manual.Count131072.C051280.packed 64 cuts51280 = true := by
 decide +kernel
def cuts51281 : List PrefixCut := [⟨33,125054032,125054103⟩,
⟨64,242364282,242364417⟩]
theorem checked51281 : checkPrefixCuts (2^48) 6725435393 10 Manual.Count131072.C051281.packed 64 cuts51281 = true := by
 decide +kernel
def pointBounds51281 : List (Nat × Nat × Nat) := [(6725502976,111971634065994,111972021367037)]
theorem point_links_checked51281 : (cuts51281.take 1).map (fun c => (6725435393-1+2*2^10*c.k,111971509011962+c.lower,111971896312934+c.upper)) = pointBounds51281 := by
 decide +kernel
def cuts51282 : List PrefixCut := [⟨64,242610657,242610793⟩]
theorem checked51282 : checkPrefixCuts (2^48) 6725566465 10 Manual.Count131072.C051282.packed 64 cuts51282 = true := by
 decide +kernel
def cuts51283 : List PrefixCut := [⟨8,31304257,31304275⟩,
⟨64,249553056,249553201⟩]
theorem checked51283 : checkPrefixCuts (2^48) 6725697537 10 Manual.Count131072.C051283.packed 64 cuts51283 = true := by
 decide +kernel
def pointBounds51283 : List (Nat × Nat × Nat) := [(6725713920,111972025291158,111972412592419)]
theorem point_links_checked51283 : (cuts51283.take 1).map (fun c => (6725697537-1+2*2^10*c.k,111971993986901+c.lower,111972381288144+c.upper)) = pointBounds51283 := by
 decide +kernel
def cuts51284 : List PrefixCut := [⟨47,178739429,178739529⟩,
⟨64,242684911,242685048⟩]
theorem checked51284 : checkPrefixCuts (2^48) 6725828609 10 Manual.Count131072.C051284.packed 64 cuts51284 = true := by
 decide +kernel
def pointBounds51284 : List (Nat × Nat × Nat) := [(6725924864,111972422279386,111972809580874)]
theorem point_links_checked51284 : (cuts51284.take 1).map (fun c => (6725828609-1+2*2^10*c.k,111972243539957+c.lower,111972630841345+c.upper)) = pointBounds51284 := by
 decide +kernel
def cuts51285 : List PrefixCut := [⟨64,238369755,238369889⟩]
theorem checked51285 : checkPrefixCuts (2^48) 6725959681 10 Manual.Count131072.C051285.packed 64 cuts51285 = true := by
 decide +kernel
def cuts51286 : List PrefixCut := [⟨22,85035293,85035340⟩,
⟨64,245688485,245688624⟩]
theorem checked51286 : checkPrefixCuts (2^48) 6726090753 10 Manual.Count131072.C051286.packed 64 cuts51286 = true := by
 decide +kernel
def pointBounds51286 : List (Nat × Nat × Nat) := [(6726135808,111972809629916,111973196931622)]
theorem point_links_checked51286 : (cuts51286.take 1).map (fun c => (6726090753-1+2*2^10*c.k,111972724594623+c.lower,111973111896282+c.upper)) = pointBounds51286 := by
 decide +kernel
def cuts51287 : List PrefixCut := [⟨61,232669381,232669511⟩,
⟨64,243340266,243340402⟩]
theorem checked51287 : checkPrefixCuts (2^48) 6726221825 10 Manual.Count131072.C051287.packed 64 cuts51287 = true := by
 decide +kernel
def pointBounds51287 : List (Nat × Nat × Nat) := [(6726346752,111973202952489,111973590254417)]
theorem point_links_checked51287 : (cuts51287.take 1).map (fun c => (6726221825-1+2*2^10*c.k,111972970283108+c.lower,111973357584906+c.upper)) = pointBounds51287 := by
 decide +kernel
def cuts51288 : List PrefixCut := [⟨64,243126287,243126424⟩]
theorem checked51288 : checkPrefixCuts (2^48) 6726352897 10 Manual.Count131072.C051288.packed 64 cuts51288 = true := by
 decide +kernel
def cuts51289 : List PrefixCut := [⟨36,134366031,134366105⟩,
⟨64,238560405,238560538⟩]
theorem checked51289 : checkPrefixCuts (2^48) 6726483969 10 Manual.Count131072.C051289.packed 64 cuts51289 = true := by
 decide +kernel
def pointBounds51289 : List (Nat × Nat × Nat) := [(6726557696,111973591115692,111973978417837)]
theorem point_links_checked51289 : (cuts51289.take 1).map (fun c => (6726483969-1+2*2^10*c.k,111973456749661+c.lower,111973844051732+c.upper)) = pointBounds51289 := by
 decide +kernel
def cuts51290 : List PrefixCut := [⟨64,245292753,245292894⟩]
theorem checked51290 : checkPrefixCuts (2^48) 6726615041 10 Manual.Count131072.C051290.packed 64 cuts51290 = true := by
 decide +kernel
def cuts51291 : List PrefixCut := [⟨11,41760378,41760404⟩,
⟨64,240685143,240685284⟩]
theorem checked51291 : checkPrefixCuts (2^48) 6726746113 10 Manual.Count131072.C051291.packed 64 cuts51291 = true := by
 decide +kernel
def pointBounds51291 : List (Nat × Nat × Nat) := [(6726768640,111973982363197,111974369665568)]
theorem point_links_checked51291 : (cuts51291.take 1).map (fun c => (6726746113-1+2*2^10*c.k,111973940602819+c.lower,111974327905164+c.upper)) = pointBounds51291 := by
 decide +kernel
def cuts51292 : List PrefixCut := [⟨50,191222546,191222654⟩,
⟨64,243525793,243525931⟩]
theorem checked51292 : checkPrefixCuts (2^48) 6726877185 10 Manual.Count131072.C051292.packed 64 cuts51292 = true := by
 decide +kernel
def pointBounds51292 : List (Nat × Nat × Nat) := [(6726979584,111974372510508,111974759813102)]
theorem point_links_checked51292 : (cuts51292.take 1).map (fun c => (6726877185-1+2*2^10*c.k,111974181287962+c.lower,111974568590448+c.upper)) = pointBounds51292 := by
 decide +kernel
def cuts51293 : List PrefixCut := [⟨64,240550232,240550374⟩]
theorem checked51293 : checkPrefixCuts (2^48) 6727008257 10 Manual.Count131072.C051293.packed 64 cuts51293 = true := by
 decide +kernel
def cuts51294 : List PrefixCut := [⟨25,93766874,93766927⟩,
⟨64,241842622,241842759⟩]
theorem checked51294 : checkPrefixCuts (2^48) 6727139329 10 Manual.Count131072.C051294.packed 64 cuts51294 = true := by
 decide +kernel
def pointBounds51294 : List (Nat × Nat × Nat) := [(6727190528,111974759130861,111975146433680)]
theorem point_links_checked51294 : (cuts51294.take 1).map (fun c => (6727139329-1+2*2^10*c.k,111974665363987+c.lower,111975052666753+c.upper)) = pointBounds51294 := by
 decide +kernel
def cuts51295 : List PrefixCut := [⟨64,240833728,240833865⟩]
theorem checked51295 : checkPrefixCuts (2^48) 6727270401 10 Manual.Count131072.C051295.packed 64 cuts51295 = true := by
 decide +kernel
def pointBounds51295 : List (Nat × Nat × Nat) := [(6727401472,111975148040337,111975535343377)]
theorem point_links_checked51295 : (cuts51295.take 1).map (fun c => (6727270401-1+2*2^10*c.k,111974907206609+c.lower,111975294509512+c.upper)) = pointBounds51295 := by
 decide +kernel
def cuts51296 : List PrefixCut := [⟨64,246184510,246184651⟩]
theorem checked51296 : checkPrefixCuts (2^48) 6727401473 10 Manual.Count131072.C051296.packed 64 cuts51296 = true := by
 decide +kernel
def cuts51297 : List PrefixCut := [⟨39,146687522,146687607⟩,
⟨64,241451926,241452064⟩]
theorem checked51297 : checkPrefixCuts (2^48) 6727532545 10 Manual.Count131072.C051297.packed 64 cuts51297 = true := by
 decide +kernel
def pointBounds51297 : List (Nat × Nat × Nat) := [(6727612416,111975540912369,111975928215635)]
theorem point_links_checked51297 : (cuts51297.take 1).map (fun c => (6727532545-1+2*2^10*c.k,111975394224847+c.lower,111975781528028+c.upper)) = pointBounds51297 := by
 decide +kernel
def cuts51298 : List PrefixCut := [⟨64,241572758,241572896⟩]
theorem checked51298 : checkPrefixCuts (2^48) 6727663617 10 Manual.Count131072.C051298.packed 64 cuts51298 = true := by
 decide +kernel
def cuts51299 : List PrefixCut := [⟨14,54765323,54765353⟩,
⟨64,243492557,243492701⟩]
theorem checked51299 : checkPrefixCuts (2^48) 6727794689 10 Manual.Count131072.C051299.packed 64 cuts51299 = true := by
 decide +kernel
def pointBounds51299 : List (Nat × Nat × Nat) := [(6727823360,111975932014854,111976319318341)]
theorem point_links_checked51299 : (cuts51299.take 1).map (fun c => (6727794689-1+2*2^10*c.k,111975877249531+c.lower,111976264552988+c.upper)) = pointBounds51299 := by
 decide +kernel
def cuts51300 : List PrefixCut := [⟨53,198472193,198472302⟩,
⟨64,238383790,238383923⟩]
theorem checked51300 : checkPrefixCuts (2^48) 6727925761 10 Manual.Count131072.C051300.packed 64 cuts51300 = true := by
 decide +kernel
def pointBounds51300 : List (Nat × Nat × Nat) := [(6728034304,111976319214281,111976706517991)]
theorem point_links_checked51300 : (cuts51300.take 1).map (fun c => (6727925761-1+2*2^10*c.k,111976120742088+c.lower,111976508045689+c.upper)) = pointBounds51300 := by
 decide +kernel
def cuts51301 : List PrefixCut := [⟨64,241098457,241098596⟩]
theorem checked51301 : checkPrefixCuts (2^48) 6728056833 10 Manual.Count131072.C051301.packed 64 cuts51301 = true := by
 decide +kernel
def cuts51302 : List PrefixCut := [⟨28,107348597,107348654⟩,
⟨64,245277234,245277371⟩]
theorem checked51302 : checkPrefixCuts (2^48) 6728187905 10 Manual.Count131072.C051302.packed 64 cuts51302 = true := by
 decide +kernel
def pointBounds51302 : List (Nat × Nat × Nat) := [(6728245248,111976707572932,111977094876862)]
theorem point_links_checked51302 : (cuts51302.take 1).map (fun c => (6728187905-1+2*2^10*c.k,111976600224335+c.lower,111976987528208+c.upper)) = pointBounds51302 := by
 decide +kernel
def cuts51303 : List PrefixCut := [⟨64,245523449,245523591⟩]
theorem checked51303 : checkPrefixCuts (2^48) 6728318977 10 Manual.Count131072.C051303.packed 64 cuts51303 = true := by
 decide +kernel
def cuts51304 : List PrefixCut := [⟨3,10751215,10751221⟩,
⟨64,242715836,242715972⟩]
theorem checked51304 : checkPrefixCuts (2^48) 6728450049 10 Manual.Count131072.C051304.packed 64 cuts51304 = true := by
 decide +kernel
def pointBounds51304 : List (Nat × Nat × Nat) := [(6728456192,111977101776233,111977489080391)]
theorem point_links_checked51304 : (cuts51304.take 1).map (fun c => (6728450049-1+2*2^10*c.k,111977091025018+c.lower,111977478329170+c.upper)) = pointBounds51304 := by
 decide +kernel
def cuts51305 : List PrefixCut := [⟨42,159674498,159674589⟩,
⟨64,242794787,242794926⟩]
theorem checked51305 : checkPrefixCuts (2^48) 6728581121 10 Manual.Count131072.C051305.packed 64 cuts51305 = true := by
 decide +kernel
def pointBounds51305 : List (Nat × Nat × Nat) := [(6728667136,111977493415352,111977880719731)]
theorem point_links_checked51305 : (cuts51305.take 1).map (fun c => (6728581121-1+2*2^10*c.k,111977333740854+c.lower,111977721045142+c.upper)) = pointBounds51305 := by
 decide +kernel
def cuts51306 : List PrefixCut := [⟨64,240112821,240112959⟩]
theorem checked51306 : checkPrefixCuts (2^48) 6728712193 10 Manual.Count131072.C051306.packed 64 cuts51306 = true := by
 decide +kernel
def cuts51307 : List PrefixCut := [⟨17,64043242,64043279⟩,
⟨64,241781382,241781518⟩]
theorem checked51307 : checkPrefixCuts (2^48) 6728843265 10 Manual.Count131072.C051307.packed 64 cuts51307 = true := by
 decide +kernel
def pointBounds51307 : List (Nat × Nat × Nat) := [(6728878080,111977880691704,111978267996306)]
theorem point_links_checked51307 : (cuts51307.take 1).map (fun c => (6728843265-1+2*2^10*c.k,111977816648462+c.lower,111978203953027+c.upper)) = pointBounds51307 := by
 decide +kernel
def cuts51308 : List PrefixCut := [⟨56,214378365,214378488⟩,
⟨64,243031584,243031724⟩]
theorem checked51308 : checkPrefixCuts (2^48) 6728974337 10 Manual.Count131072.C051308.packed 64 cuts51308 = true := by
 decide +kernel
def pointBounds51308 : List (Nat × Nat × Nat) := [(6729089024,111978272808209,111978660113033)]
theorem point_links_checked51308 : (cuts51308.take 1).map (fun c => (6728974337-1+2*2^10*c.k,111978058429844+c.lower,111978445734545+c.upper)) = pointBounds51308 := by
 decide +kernel
def cuts51309 : List PrefixCut := [⟨64,248088160,248088297⟩]
theorem checked51309 : checkPrefixCuts (2^48) 6729105409 10 Manual.Count131072.C051309.packed 64 cuts51309 = true := by
 decide +kernel
def cuts51310 : List PrefixCut := [⟨31,117328818,117328884⟩,
⟨64,243775010,243775149⟩]
theorem checked51310 : checkPrefixCuts (2^48) 6729236481 10 Manual.Count131072.C051310.packed 64 cuts51310 = true := by
 decide +kernel
def pointBounds51310 : List (Nat × Nat × Nat) := [(6729299968,111978666878406,111979054183450)]
theorem point_links_checked51310 : (cuts51310.take 1).map (fun c => (6729236481-1+2*2^10*c.k,111978549549588+c.lower,111978936854566+c.upper)) = pointBounds51310 := by
 decide +kernel
def cuts51311 : List PrefixCut := [⟨64,245443354,245443495⟩]
theorem checked51311 : checkPrefixCuts (2^48) 6729367553 10 Manual.Count131072.C051311.packed 64 cuts51311 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000040
