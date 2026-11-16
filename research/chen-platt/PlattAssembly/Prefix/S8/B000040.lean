import PlattAssemblyKernel
import PlattCertificates.Count131072.C071280
import PlattCertificates.Count131072.C071281
import PlattCertificates.Count131072.C071282
import PlattCertificates.Count131072.C071283
import PlattCertificates.Count131072.C071284
import PlattCertificates.Count131072.C071285
import PlattCertificates.Count131072.C071286
import PlattCertificates.Count131072.C071287
import PlattCertificates.Count131072.C071288
import PlattCertificates.Count131072.C071289
import PlattCertificates.Count131072.C071290
import PlattCertificates.Count131072.C071291
import PlattCertificates.Count131072.C071292
import PlattCertificates.Count131072.C071293
import PlattCertificates.Count131072.C071294
import PlattCertificates.Count131072.C071295
import PlattCertificates.Count131072.C071296
import PlattCertificates.Count131072.C071297
import PlattCertificates.Count131072.C071298
import PlattCertificates.Count131072.C071299
import PlattCertificates.Count131072.C071300
import PlattCertificates.Count131072.C071301
import PlattCertificates.Count131072.C071302
import PlattCertificates.Count131072.C071303
import PlattCertificates.Count131072.C071304
import PlattCertificates.Count131072.C071305
import PlattCertificates.Count131072.C071306
import PlattCertificates.Count131072.C071307
import PlattCertificates.Count131072.C071308
import PlattCertificates.Count131072.C071309
import PlattCertificates.Count131072.C071310
import PlattCertificates.Count131072.C071311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71280 : List PrefixCut := [⟨51,137985023,137985105⟩,
⟨64,173640443,173640545⟩]
theorem checked71280 : checkPrefixCuts (2^48) 9346744321 10 Manual.Count131072.C071280.packed 64 cuts71280 = true := by
 decide +kernel
def pointBounds71280 : List (Nat × Nat × Nat) := [(9346848768,116036059538858,116036449175257)]
theorem point_links_checked71280 : (cuts71280.take 1).map (fun c => (9346744321-1+2*2^10*c.k,116035921553835+c.lower,116036311190152+c.upper)) = pointBounds71280 := by
 decide +kernel
def cuts71281 : List PrefixCut := [⟨64,172885156,172885252⟩]
theorem checked71281 : checkPrefixCuts (2^48) 9346875393 10 Manual.Count131072.C071281.packed 64 cuts71281 = true := by
 decide +kernel
def cuts71282 : List PrefixCut := [⟨64,173756030,173756132⟩]
theorem checked71282 : checkPrefixCuts (2^48) 9347006465 10 Manual.Count131072.C071282.packed 64 cuts71282 = true := by
 decide +kernel
def cuts71283 : List PrefixCut := [⟨2,5570994,5570997⟩,
⟨64,170049657,170049755⟩]
theorem checked71283 : checkPrefixCuts (2^48) 9347137537 10 Manual.Count131072.C071283.packed 64 cuts71283 = true := by
 decide +kernel
def pointBounds71283 : List (Nat × Nat × Nat) := [(9347141632,116036447406458,116036837043078)]
theorem point_links_checked71283 : (cuts71283.take 1).map (fun c => (9347137537-1+2*2^10*c.k,116036441835464+c.lower,116036831472081+c.upper)) = pointBounds71283 := by
 decide +kernel
def cuts71284 : List PrefixCut := [⟨64,170739871,170739967⟩]
theorem checked71284 : checkPrefixCuts (2^48) 9347268609 10 Manual.Count131072.C071284.packed 64 cuts71284 = true := by
 decide +kernel
def cuts71285 : List PrefixCut := [⟨17,45470007,45470028⟩,
⟨64,171128944,171129039⟩]
theorem checked71285 : checkPrefixCuts (2^48) 9347399681 10 Manual.Count131072.C071285.packed 64 cuts71285 = true := by
 decide +kernel
def pointBounds71285 : List (Nat × Nat × Nat) := [(9347434496,116036828094999,116037217731831)]
theorem point_links_checked71285 : (cuts71285.take 1).map (fun c => (9347399681-1+2*2^10*c.k,116036782624992+c.lower,116037172261803+c.upper)) = pointBounds71285 := by
 decide +kernel
def cuts71286 : List PrefixCut := [⟨64,171698671,171698772⟩]
theorem checked71286 : checkPrefixCuts (2^48) 9347530753 10 Manual.Count131072.C071286.packed 64 cuts71286 = true := by
 decide +kernel
def cuts71287 : List PrefixCut := [⟨32,87715354,87715407⟩,
⟨64,172810397,172810495⟩]
theorem checked71287 : checkPrefixCuts (2^48) 9347661825 10 Manual.Count131072.C071287.packed 64 cuts71287 = true := by
 decide +kernel
def pointBounds71287 : List (Nat × Nat × Nat) := [(9347727360,116037213167961,116037602805021)]
theorem point_links_checked71287 : (cuts71287.take 1).map (fun c => (9347661825-1+2*2^10*c.k,116037125452607+c.lower,116037515089614+c.upper)) = pointBounds71287 := by
 decide +kernel
def cuts71288 : List PrefixCut := [⟨64,171121746,171121846⟩]
theorem checked71288 : checkPrefixCuts (2^48) 9347792897 10 Manual.Count131072.C071288.packed 64 cuts71288 = true := by
 decide +kernel
def cuts71289 : List PrefixCut := [⟨47,126073914,126073982⟩,
⟨64,171059130,171059224⟩]
theorem checked71289 : checkPrefixCuts (2^48) 9347923969 10 Manual.Count131072.C071289.packed 64 cuts71289 = true := by
 decide +kernel
def pointBounds71289 : List (Nat × Nat × Nat) := [(9348020224,116037595458664,116037985095937)]
theorem point_links_checked71289 : (cuts71289.take 1).map (fun c => (9347923969-1+2*2^10*c.k,116037469384750+c.lower,116037859021955+c.upper)) = pointBounds71289 := by
 decide +kernel
def cuts71290 : List PrefixCut := [⟨64,171116941,171117042⟩]
theorem checked71290 : checkPrefixCuts (2^48) 9348055041 10 Manual.Count131072.C071290.packed 64 cuts71290 = true := by
 decide +kernel
def cuts71291 : List PrefixCut := [⟨62,165002268,165002368⟩,
⟨64,170693000,170693103⟩]
theorem checked71291 : checkPrefixCuts (2^48) 9348186113 10 Manual.Count131072.C071291.packed 64 cuts71291 = true := by
 decide +kernel
def pointBounds71291 : List (Nat × Nat × Nat) := [(9348313088,116037976563089,116038366200589)]
theorem point_links_checked71291 : (cuts71291.take 1).map (fun c => (9348186113-1+2*2^10*c.k,116037811560821+c.lower,116038201198221+c.upper)) = pointBounds71291 := by
 decide +kernel
def cuts71292 : List PrefixCut := [⟨64,173370343,173370451⟩]
theorem checked71292 : checkPrefixCuts (2^48) 9348317185 10 Manual.Count131072.C071292.packed 64 cuts71292 = true := by
 decide +kernel
def cuts71293 : List PrefixCut := [⟨64,169604288,169604390⟩]
theorem checked71293 : checkPrefixCuts (2^48) 9348448257 10 Manual.Count131072.C071293.packed 64 cuts71293 = true := by
 decide +kernel
def cuts71294 : List PrefixCut := [⟨13,35046641,35046663⟩,
⟨64,172582663,172582771⟩]
theorem checked71294 : checkPrefixCuts (2^48) 9348579329 10 Manual.Count131072.C071294.packed 64 cuts71294 = true := by
 decide +kernel
def pointBounds71294 : List (Nat × Nat × Nat) := [(9348605952,116038360275093,116038749912828)]
theorem point_links_checked71294 : (cuts71294.take 1).map (fun c => (9348579329-1+2*2^10*c.k,116038325228452+c.lower,116038714866165+c.upper)) = pointBounds71294 := by
 decide +kernel
def cuts71295 : List PrefixCut := [⟨64,172881333,172881434⟩]
theorem checked71295 : checkPrefixCuts (2^48) 9348710401 10 Manual.Count131072.C071295.packed 64 cuts71295 = true := by
 decide +kernel
def cuts71296 : List PrefixCut := [⟨28,75209546,75209591⟩,
⟨64,170831575,170831678⟩]
theorem checked71296 : checkPrefixCuts (2^48) 9348841473 10 Manual.Count131072.C071296.packed 64 cuts71296 = true := by
 decide +kernel
def pointBounds71296 : List (Nat × Nat × Nat) := [(9348898816,116038745901994,116039135539961)]
theorem point_links_checked71296 : (cuts71296.take 1).map (fun c => (9348841473-1+2*2^10*c.k,116038670692448+c.lower,116039060330370+c.upper)) = pointBounds71296 := by
 decide +kernel
def cuts71297 : List PrefixCut := [⟨64,172274339,172274438⟩]
theorem checked71297 : checkPrefixCuts (2^48) 9348972545 10 Manual.Count131072.C071297.packed 64 cuts71297 = true := by
 decide +kernel
def cuts71298 : List PrefixCut := [⟨43,115791559,115791635⟩,
⟨64,172633197,172633304⟩]
theorem checked71298 : checkPrefixCuts (2^48) 9349103617 10 Manual.Count131072.C071298.packed 64 cuts71298 = true := by
 decide +kernel
def pointBounds71298 : List (Nat × Nat × Nat) := [(9349191680,116039129589921,116039519228121)]
theorem point_links_checked71298 : (cuts71298.take 1).map (fun c => (9349103617-1+2*2^10*c.k,116039013798362+c.lower,116039403436486+c.upper)) = pointBounds71298 := by
 decide +kernel
def cuts71299 : List PrefixCut := [⟨64,173714622,173714724⟩]
theorem checked71299 : checkPrefixCuts (2^48) 9349234689 10 Manual.Count131072.C071299.packed 64 cuts71299 = true := by
 decide +kernel
def cuts71300 : List PrefixCut := [⟨58,154775540,154775636⟩,
⟨64,170400507,170400610⟩]
theorem checked71300 : checkPrefixCuts (2^48) 9349365761 10 Manual.Count131072.C071300.packed 64 cuts71300 = true := by
 decide +kernel
def pointBounds71300 : List (Nat × Nat × Nat) := [(9349484544,116039514921721,116039904560150)]
theorem point_links_checked71300 : (cuts71300.take 1).map (fun c => (9349365761-1+2*2^10*c.k,116039360146181+c.lower,116039749784514+c.upper)) = pointBounds71300 := by
 decide +kernel
def cuts71301 : List PrefixCut := [⟨64,171331408,171331508⟩]
theorem checked71301 : checkPrefixCuts (2^48) 9349496833 10 Manual.Count131072.C071301.packed 64 cuts71301 = true := by
 decide +kernel
def cuts71302 : List PrefixCut := [⟨64,170847314,170847424⟩]
theorem checked71302 : checkPrefixCuts (2^48) 9349627905 10 Manual.Count131072.C071302.packed 64 cuts71302 = true := by
 decide +kernel
def cuts71303 : List PrefixCut := [⟨9,24385061,24385075⟩,
⟨64,172350167,172350268⟩]
theorem checked71303 : checkPrefixCuts (2^48) 9349758977 10 Manual.Count131072.C071303.packed 64 cuts71303 = true := by
 decide +kernel
def pointBounds71303 : List (Nat × Nat × Nat) := [(9349777408,116039897110471,116040286749131)]
theorem point_links_checked71303 : (cuts71303.take 1).map (fun c => (9349758977-1+2*2^10*c.k,116039872725410+c.lower,116040262364056+c.upper)) = pointBounds71303 := by
 decide +kernel
def cuts71304 : List PrefixCut := [⟨64,171896166,171896266⟩]
theorem checked71304 : checkPrefixCuts (2^48) 9349890049 10 Manual.Count131072.C071304.packed 64 cuts71304 = true := by
 decide +kernel
def cuts71305 : List PrefixCut := [⟨24,62526253,62526295⟩,
⟨64,172044270,172044379⟩]
theorem checked71305 : checkPrefixCuts (2^48) 9350021121 10 Manual.Count131072.C071305.packed 64 cuts71305 = true := by
 decide +kernel
def pointBounds71305 : List (Nat × Nat × Nat) := [(9350070272,116040279497996,116040669136885)]
theorem point_links_checked71305 : (cuts71305.take 1).map (fun c => (9350021121-1+2*2^10*c.k,116040216971743+c.lower,116040606610590+c.upper)) = pointBounds71305 := by
 decide +kernel
def cuts71306 : List PrefixCut := [⟨64,174450165,174450266⟩]
theorem checked71306 : checkPrefixCuts (2^48) 9350152193 10 Manual.Count131072.C071306.packed 64 cuts71306 = true := by
 decide +kernel
def cuts71307 : List PrefixCut := [⟨39,103555100,103555164⟩,
⟨64,170474103,170474209⟩]
theorem checked71307 : checkPrefixCuts (2^48) 9350283265 10 Manual.Count131072.C071307.packed 64 cuts71307 = true := by
 decide +kernel
def pointBounds71307 : List (Nat × Nat × Nat) := [(9350363136,116040667021278,116041056660399)]
theorem point_links_checked71307 : (cuts71307.take 1).map (fun c => (9350283265-1+2*2^10*c.k,116040563466178+c.lower,116040953105235+c.upper)) = pointBounds71307 := by
 decide +kernel
def cuts71308 : List PrefixCut := [⟨64,172187575,172187676⟩]
theorem checked71308 : checkPrefixCuts (2^48) 9350414337 10 Manual.Count131072.C071308.packed 64 cuts71308 = true := by
 decide +kernel
def cuts71309 : List PrefixCut := [⟨54,143257004,143257085⟩,
⟨64,169596360,169596456⟩]
theorem checked71309 : checkPrefixCuts (2^48) 9350545409 10 Manual.Count131072.C071309.packed 64 cuts71309 = true := by
 decide +kernel
def pointBounds71309 : List (Nat × Nat × Nat) := [(9350656000,116041049384860,116041439024205)]
theorem point_links_checked71309 : (cuts71309.take 1).map (fun c => (9350545409-1+2*2^10*c.k,116040906127856+c.lower,116041295767120+c.upper)) = pointBounds71309 := by
 decide +kernel
def cuts71310 : List PrefixCut := [⟨64,169834809,169834902⟩]
theorem checked71310 : checkPrefixCuts (2^48) 9350676481 10 Manual.Count131072.C071310.packed 64 cuts71310 = true := by
 decide +kernel
def cuts71311 : List PrefixCut := [⟨64,172511428,172511537⟩]
theorem checked71311 : checkPrefixCuts (2^48) 9350807553 10 Manual.Count131072.C071311.packed 64 cuts71311 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000040
