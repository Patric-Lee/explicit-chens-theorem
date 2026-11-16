import PlattAssemblyKernel
import PlattCertificates.Count131072.C063296
import PlattCertificates.Count131072.C063297
import PlattCertificates.Count131072.C063298
import PlattCertificates.Count131072.C063299
import PlattCertificates.Count131072.C063300
import PlattCertificates.Count131072.C063301
import PlattCertificates.Count131072.C063302
import PlattCertificates.Count131072.C063303
import PlattCertificates.Count131072.C063304
import PlattCertificates.Count131072.C063305
import PlattCertificates.Count131072.C063306
import PlattCertificates.Count131072.C063307
import PlattCertificates.Count131072.C063308
import PlattCertificates.Count131072.C063309
import PlattCertificates.Count131072.C063310
import PlattCertificates.Count131072.C063311
import PlattCertificates.Count131072.C063312
import PlattCertificates.Count131072.C063313
import PlattCertificates.Count131072.C063314
import PlattCertificates.Count131072.C063315
import PlattCertificates.Count131072.C063316
import PlattCertificates.Count131072.C063317
import PlattCertificates.Count131072.C063318
import PlattCertificates.Count131072.C063319
import PlattCertificates.Count131072.C063320
import PlattCertificates.Count131072.C063321
import PlattCertificates.Count131072.C063322
import PlattCertificates.Count131072.C063323
import PlattCertificates.Count131072.C063324
import PlattCertificates.Count131072.C063325
import PlattCertificates.Count131072.C063326
import PlattCertificates.Count131072.C063327
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63296 : List PrefixCut := [⟨8,25026702,25026715⟩,
⟨64,196821115,196821222⟩]
theorem checked63296 : checkPrefixCuts (2^48) 8300265473 10 Manual.Count131072.C063296.packed 64 cuts63296 = true := by
 decide +kernel
def pointBounds63296 : List (Nat × Nat × Nat) := [(8300281856,114576400219902,114576789005296)]
theorem point_links_checked63296 : (cuts63296.take 1).map (fun c => (8300265473-1+2*2^10*c.k,114576375193200+c.lower,114576763978581+c.upper)) = pointBounds63296 := by
 decide +kernel
def cuts63297 : List PrefixCut := [⟨64,196444963,196445076⟩]
theorem checked63297 : checkPrefixCuts (2^48) 8300396545 10 Manual.Count131072.C063297.packed 64 cuts63297 = true := by
 decide +kernel
def cuts63298 : List PrefixCut := [⟨7,20888838,20888852⟩,
⟨64,194237709,194237821⟩]
theorem checked63298 : checkPrefixCuts (2^48) 8300527617 10 Manual.Count131072.C063298.packed 64 cuts63298 = true := by
 decide +kernel
def pointBounds63298 : List (Nat × Nat × Nat) := [(8300541952,114576789348116,114577178133731)]
theorem point_links_checked63298 : (cuts63298.take 1).map (fun c => (8300527617-1+2*2^10*c.k,114576768459278+c.lower,114577157244879+c.upper)) = pointBounds63298 := by
 decide +kernel
def cuts63299 : List PrefixCut := [⟨64,195997946,195998056⟩]
theorem checked63299 : checkPrefixCuts (2^48) 8300658689 10 Manual.Count131072.C063299.packed 64 cuts63299 = true := by
 decide +kernel
def cuts63300 : List PrefixCut := [⟨6,18989256,18989267⟩,
⟨64,194672400,194672519⟩]
theorem checked63300 : checkPrefixCuts (2^48) 8300789761 10 Manual.Count131072.C063300.packed 64 cuts63300 = true := by
 decide +kernel
def pointBounds63300 : List (Nat × Nat × Nat) := [(8300802048,114577177684189,114577566470023)]
theorem point_links_checked63300 : (cuts63300.take 1).map (fun c => (8300789761-1+2*2^10*c.k,114577158694933+c.lower,114577547480756+c.upper)) = pointBounds63300 := by
 decide +kernel
def cuts63301 : List PrefixCut := [⟨64,192193985,192194096⟩]
theorem checked63301 : checkPrefixCuts (2^48) 8300920833 10 Manual.Count131072.C063301.packed 64 cuts63301 = true := by
 decide +kernel
def cuts63302 : List PrefixCut := [⟨5,15530010,15530020⟩,
⟨64,196056471,196056589⟩]
theorem checked63302 : checkPrefixCuts (2^48) 8301051905 10 Manual.Count131072.C063302.packed 64 cuts63302 = true := by
 decide +kernel
def pointBounds63302 : List (Nat × Nat × Nat) := [(8301062144,114577561091328,114577949877391)]
theorem point_links_checked63302 : (cuts63302.take 1).map (fun c => (8301051905-1+2*2^10*c.k,114577545561318+c.lower,114577934347371+c.upper)) = pointBounds63302 := by
 decide +kernel
def cuts63303 : List PrefixCut := [⟨64,193849386,193849495⟩]
theorem checked63303 : checkPrefixCuts (2^48) 8301182977 10 Manual.Count131072.C063303.packed 64 cuts63303 = true := by
 decide +kernel
def cuts63304 : List PrefixCut := [⟨4,12986478,12986486⟩,
⟨64,194117602,194117718⟩]
theorem checked63304 : checkPrefixCuts (2^48) 8301314049 10 Manual.Count131072.C063304.packed 64 cuts63304 = true := by
 decide +kernel
def pointBounds63304 : List (Nat × Nat × Nat) := [(8301322240,114577948453653,114578337239941)]
theorem point_links_checked63304 : (cuts63304.take 1).map (fun c => (8301314049-1+2*2^10*c.k,114577935467175+c.lower,114578324253455+c.upper)) = pointBounds63304 := by
 decide +kernel
def cuts63305 : List PrefixCut := [⟨64,194284050,194284162⟩]
theorem checked63305 : checkPrefixCuts (2^48) 8301445121 10 Manual.Count131072.C063305.packed 64 cuts63305 = true := by
 decide +kernel
def cuts63306 : List PrefixCut := [⟨3,9697169,9697175⟩,
⟨64,195264267,195264375⟩]
theorem checked63306 : checkPrefixCuts (2^48) 8301576193 10 Manual.Count131072.C063306.packed 64 cuts63306 = true := by
 decide +kernel
def pointBounds63306 : List (Nat × Nat × Nat) := [(8301582336,114578333565996,114578722352510)]
theorem point_links_checked63306 : (cuts63306.take 1).map (fun c => (8301576193-1+2*2^10*c.k,114578323868827+c.lower,114578712655335+c.upper)) = pointBounds63306 := by
 decide +kernel
def cuts63307 : List PrefixCut := [⟨64,198821251,198821366⟩]
theorem checked63307 : checkPrefixCuts (2^48) 8301707265 10 Manual.Count131072.C063307.packed 64 cuts63307 = true := by
 decide +kernel
def cuts63308 : List PrefixCut := [⟨2,6408067,6408071⟩,
⟨64,194512178,194512292⟩]
theorem checked63308 : checkPrefixCuts (2^48) 8301838337 10 Manual.Count131072.C063308.packed 64 cuts63308 = true := by
 decide +kernel
def pointBounds63308 : List (Nat × Nat × Nat) := [(8301842432,114578724362412,114579113149147)]
theorem point_links_checked63308 : (cuts63308.take 1).map (fun c => (8301838337-1+2*2^10*c.k,114578717954345+c.lower,114579106741076+c.upper)) = pointBounds63308 := by
 decide +kernel
def cuts63309 : List PrefixCut := [⟨64,195017677,195017790⟩]
theorem checked63309 : checkPrefixCuts (2^48) 8301969409 10 Manual.Count131072.C063309.packed 64 cuts63309 = true := by
 decide +kernel
def cuts63310 : List PrefixCut := [⟨1,3458214,3458215⟩,
⟨64,193251608,193251722⟩]
theorem checked63310 : checkPrefixCuts (2^48) 8302100481 10 Manual.Count131072.C063310.packed 64 cuts63310 = true := by
 decide +kernel
def pointBounds63310 : List (Nat × Nat × Nat) := [(8302102528,114579110942414,114579499729373)]
theorem point_links_checked63310 : (cuts63310.take 1).map (fun c => (8302100481-1+2*2^10*c.k,114579107484200+c.lower,114579496271158+c.upper)) = pointBounds63310 := by
 decide +kernel
def cuts63311 : List PrefixCut := [⟨64,193146833,193146943⟩]
theorem checked63311 : checkPrefixCuts (2^48) 8302231553 10 Manual.Count131072.C063311.packed 64 cuts63311 = true := by
 decide +kernel
def pointBounds63311 : List (Nat × Nat × Nat) := [(8302362624,114579493882641,114579882669823)]
theorem point_links_checked63311 : (cuts63311.take 1).map (fun c => (8302231553-1+2*2^10*c.k,114579300735808+c.lower,114579689522880+c.upper)) = pointBounds63311 := by
 decide +kernel
def cuts63312 : List PrefixCut := [⟨64,195449182,195449296⟩]
theorem checked63312 : checkPrefixCuts (2^48) 8302362625 10 Manual.Count131072.C063312.packed 64 cuts63312 = true := by
 decide +kernel
def cuts63313 : List PrefixCut := [⟨63,195208800,195208916⟩,
⟨64,198327777,198327895⟩]
theorem checked63313 : checkPrefixCuts (2^48) 8302493697 10 Manual.Count131072.C063313.packed 64 cuts63313 = true := by
 decide +kernel
def pointBounds63313 : List (Nat × Nat × Nat) := [(8302622720,114579884540623,114580273328035)]
theorem point_links_checked63313 : (cuts63313.take 1).map (fun c => (8302493697-1+2*2^10*c.k,114579689331823+c.lower,114580078119119+c.upper)) = pointBounds63313 := by
 decide +kernel
def cuts63314 : List PrefixCut := [⟨64,193578425,193578530⟩]
theorem checked63314 : checkPrefixCuts (2^48) 8302624769 10 Manual.Count131072.C063314.packed 64 cuts63314 = true := by
 decide +kernel
def cuts63315 : List PrefixCut := [⟨62,188591947,188592051⟩,
⟨64,193982183,193982290⟩]
theorem checked63315 : checkPrefixCuts (2^48) 8302755841 10 Manual.Count131072.C063315.packed 64 cuts63315 = true := by
 decide +kernel
def pointBounds63315 : List (Nat × Nat × Nat) := [(8302882816,114580269829972,114580658617595)]
theorem point_links_checked63315 : (cuts63315.take 1).map (fun c => (8302755841-1+2*2^10*c.k,114580081238025+c.lower,114580470025544+c.upper)) = pointBounds63315 := by
 decide +kernel
def cuts63316 : List PrefixCut := [⟨64,194521537,194521646⟩]
theorem checked63316 : checkPrefixCuts (2^48) 8302886913 10 Manual.Count131072.C063316.packed 64 cuts63316 = true := by
 decide +kernel
def cuts63317 : List PrefixCut := [⟨61,186043512,186043618⟩,
⟨64,194755758,194755869⟩]
theorem checked63317 : checkPrefixCuts (2^48) 8303017985 10 Manual.Count131072.C063317.packed 64 cuts63317 = true := by
 decide +kernel
def pointBounds63317 : List (Nat × Nat × Nat) := [(8303142912,114580655785257,114581044573098)]
theorem point_links_checked63317 : (cuts63317.take 1).map (fun c => (8303017985-1+2*2^10*c.k,114580469741745+c.lower,114580858529480+c.upper)) = pointBounds63317 := by
 decide +kernel
def cuts63318 : List PrefixCut := [⟨64,193769587,193769701⟩]
theorem checked63318 : checkPrefixCuts (2^48) 8303149057 10 Manual.Count131072.C063318.packed 64 cuts63318 = true := by
 decide +kernel
def cuts63319 : List PrefixCut := [⟨60,182207071,182207180⟩,
⟨64,194207219,194207334⟩]
theorem checked63319 : checkPrefixCuts (2^48) 8303280129 10 Manual.Count131072.C063319.packed 64 cuts63319 = true := by
 decide +kernel
def pointBounds63319 : List (Nat × Nat × Nat) := [(8303403008,114581040474161,114581429262230)]
theorem point_links_checked63319 : (cuts63319.take 1).map (fun c => (8303280129-1+2*2^10*c.k,114580858267090+c.lower,114581247055050+c.upper)) = pointBounds63319 := by
 decide +kernel
def cuts63320 : List PrefixCut := [⟨64,197051634,197051746⟩]
theorem checked63320 : checkPrefixCuts (2^48) 8303411201 10 Manual.Count131072.C063320.packed 64 cuts63320 = true := by
 decide +kernel
def cuts63321 : List PrefixCut := [⟨59,179794584,179794689⟩,
⟨64,194641758,194641872⟩]
theorem checked63321 : checkPrefixCuts (2^48) 8303542273 10 Manual.Count131072.C063321.packed 64 cuts63321 = true := by
 decide +kernel
def pointBounds63321 : List (Nat × Nat × Nat) := [(8303663104,114581429320527,114581818108819)]
theorem point_links_checked63321 : (cuts63321.take 1).map (fun c => (8303542273-1+2*2^10*c.k,114581249525943+c.lower,114581638314130+c.upper)) = pointBounds63321 := by
 decide +kernel
def cuts63322 : List PrefixCut := [⟨64,195248845,195248953⟩]
theorem checked63322 : checkPrefixCuts (2^48) 8303673345 10 Manual.Count131072.C063322.packed 64 cuts63322 = true := by
 decide +kernel
def cuts63323 : List PrefixCut := [⟨58,177280563,177280663⟩,
⟨64,196635516,196635627⟩]
theorem checked63323 : checkPrefixCuts (2^48) 8303804417 10 Manual.Count131072.C063323.packed 64 cuts63323 = true := by
 decide +kernel
def pointBounds63323 : List (Nat × Nat × Nat) := [(8303923200,114581816697109,114582205485618)]
theorem point_links_checked63323 : (cuts63323.take 1).map (fun c => (8303804417-1+2*2^10*c.k,114581639416546+c.lower,114582028204955+c.upper)) = pointBounds63323 := by
 decide +kernel
def cuts63324 : List PrefixCut := [⟨64,194700339,194700456⟩]
theorem checked63324 : checkPrefixCuts (2^48) 8303935489 10 Manual.Count131072.C063324.packed 64 cuts63324 = true := by
 decide +kernel
def cuts63325 : List PrefixCut := [⟨57,172529594,172529691⟩,
⟨64,193205864,193205974⟩]
theorem checked63325 : checkPrefixCuts (2^48) 8304066561 10 Manual.Count131072.C063325.packed 64 cuts63325 = true := by
 decide +kernel
def pointBounds63325 : List (Nat × Nat × Nat) := [(8304183296,114582203281995,114582592070729)]
theorem point_links_checked63325 : (cuts63325.take 1).map (fun c => (8304066561-1+2*2^10*c.k,114582030752401+c.lower,114582419541038+c.upper)) = pointBounds63325 := by
 decide +kernel
def cuts63326 : List PrefixCut := [⟨64,194524703,194524815⟩]
theorem checked63326 : checkPrefixCuts (2^48) 8304197633 10 Manual.Count131072.C063326.packed 64 cuts63326 = true := by
 decide +kernel
def cuts63327 : List PrefixCut := [⟨56,171202258,171202358⟩,
⟨64,195436797,195436910⟩]
theorem checked63327 : checkPrefixCuts (2^48) 8304328705 10 Manual.Count131072.C063327.packed 64 cuts63327 = true := by
 decide +kernel
def pointBounds63327 : List (Nat × Nat × Nat) := [(8304443392,114582589685226,114582978474185)]
theorem point_links_checked63327 : (cuts63327.take 1).map (fun c => (8304328705-1+2*2^10*c.k,114582418482968+c.lower,114582807271827+c.upper)) = pointBounds63327 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000103
