import PlattAssemblyKernel
import PlattCertificates.Count131072.C046304
import PlattCertificates.Count131072.C046305
import PlattCertificates.Count131072.C046306
import PlattCertificates.Count131072.C046307
import PlattCertificates.Count131072.C046308
import PlattCertificates.Count131072.C046309
import PlattCertificates.Count131072.C046310
import PlattCertificates.Count131072.C046311
import PlattCertificates.Count131072.C046312
import PlattCertificates.Count131072.C046313
import PlattCertificates.Count131072.C046314
import PlattCertificates.Count131072.C046315
import PlattCertificates.Count131072.C046316
import PlattCertificates.Count131072.C046317
import PlattCertificates.Count131072.C046318
import PlattCertificates.Count131072.C046319
import PlattCertificates.Count131072.C046320
import PlattCertificates.Count131072.C046321
import PlattCertificates.Count131072.C046322
import PlattCertificates.Count131072.C046323
import PlattCertificates.Count131072.C046324
import PlattCertificates.Count131072.C046325
import PlattCertificates.Count131072.C046326
import PlattCertificates.Count131072.C046327
import PlattCertificates.Count131072.C046328
import PlattCertificates.Count131072.C046329
import PlattCertificates.Count131072.C046330
import PlattCertificates.Count131072.C046331
import PlattCertificates.Count131072.C046332
import PlattCertificates.Count131072.C046333
import PlattCertificates.Count131072.C046334
import PlattCertificates.Count131072.C046335
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000197
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46304 : List PrefixCut := [⟨64,268258671,268258824⟩]
theorem checked46304 : checkPrefixCuts (2^48) 6073090049 10 Manual.Count131072.C046304.packed 64 cuts46304 = true := by
 decide +kernel
def pointBounds46304 : List (Nat × Nat × Nat) := [(6073221120,110699788772765,110700175347634)]
theorem point_links_checked46304 : (cuts46304.take 1).map (fun c => (6073090049-1+2*2^10*c.k,110699520514094+c.lower,110699907088810+c.upper)) = pointBounds46304 := by
 decide +kernel
def cuts46305 : List PrefixCut := [⟨64,268021170,268021328⟩]
theorem checked46305 : checkPrefixCuts (2^48) 6073221121 10 Manual.Count131072.C046305.packed 64 cuts46305 = true := by
 decide +kernel
def cuts46306 : List PrefixCut := [⟨29,121101215,121101286⟩,
⟨64,268710555,268710712⟩]
theorem checked46306 : checkPrefixCuts (2^48) 6073352193 10 Manual.Count131072.C046306.packed 64 cuts46306 = true := by
 decide +kernel
def pointBounds46306 : List (Nat × Nat × Nat) := [(6073411584,110700177895150,110700564470248)]
theorem point_links_checked46306 : (cuts46306.take 1).map (fun c => (6073352193-1+2*2^10*c.k,110700056793935+c.lower,110700443368962+c.upper)) = pointBounds46306 := by
 decide +kernel
def cuts46307 : List PrefixCut := [⟨58,247942722,247942863⟩,
⟨64,272412319,272412473⟩]
theorem checked46307 : checkPrefixCuts (2^48) 6073483265 10 Manual.Count131072.C046307.packed 64 cuts46307 = true := by
 decide +kernel
def pointBounds46307 : List (Nat × Nat × Nat) := [(6073602048,110700573447212,110700960022537)]
theorem point_links_checked46307 : (cuts46307.take 1).map (fun c => (6073483265-1+2*2^10*c.k,110700325504490+c.lower,110700712079674+c.upper)) = pointBounds46307 := by
 decide +kernel
def cuts46308 : List PrefixCut := [⟨64,271525898,271526052⟩]
theorem checked46308 : checkPrefixCuts (2^48) 6073614337 10 Manual.Count131072.C046308.packed 64 cuts46308 = true := by
 decide +kernel
def cuts46309 : List PrefixCut := [⟨23,97180661,97180713⟩,
⟨64,271520047,271520199⟩]
theorem checked46309 : checkPrefixCuts (2^48) 6073745409 10 Manual.Count131072.C046309.packed 64 cuts46309 = true := by
 decide +kernel
def pointBounds46309 : List (Nat × Nat × Nat) := [(6073792512,110700966623368,110701353198912)]
theorem point_links_checked46309 : (cuts46309.take 1).map (fun c => (6073745409-1+2*2^10*c.k,110700869442707+c.lower,110701256018199+c.upper)) = pointBounds46309 := by
 decide +kernel
def cuts46310 : List PrefixCut := [⟨52,218175689,218175811⟩,
⟨64,267343474,267343622⟩]
theorem checked46310 : checkPrefixCuts (2^48) 6073876481 10 Manual.Count131072.C046310.packed 64 cuts46310 = true := by
 decide +kernel
def pointBounds46310 : List (Nat × Nat × Nat) := [(6073982976,110701359138443,110701745714209)]
theorem point_links_checked46310 : (cuts46310.take 1).map (fun c => (6073876481-1+2*2^10*c.k,110701140962754+c.lower,110701527538398+c.upper)) = pointBounds46310 := by
 decide +kernel
def cuts46311 : List PrefixCut := [⟨64,273500937,273501098⟩]
theorem checked46311 : checkPrefixCuts (2^48) 6074007553 10 Manual.Count131072.C046311.packed 64 cuts46311 = true := by
 decide +kernel
def cuts46312 : List PrefixCut := [⟨17,71965639,71965681⟩,
⟨64,269556227,269556379⟩]
theorem checked46312 : checkPrefixCuts (2^48) 6074138625 10 Manual.Count131072.C046312.packed 64 cuts46312 = true := by
 decide +kernel
def pointBounds46312 : List (Nat × Nat × Nat) := [(6074173440,110701753772804,110702140348799)]
theorem point_links_checked46312 : (cuts46312.take 1).map (fun c => (6074138625-1+2*2^10*c.k,110701681807165+c.lower,110702068383118+c.upper)) = pointBounds46312 := by
 decide +kernel
def cuts46313 : List PrefixCut := [⟨46,195733943,195734057⟩,
⟨64,270755209,270755368⟩]
theorem checked46313 : checkPrefixCuts (2^48) 6074269697 10 Manual.Count131072.C046313.packed 64 cuts46313 = true := by
 decide +kernel
def pointBounds46313 : List (Nat × Nat × Nat) := [(6074363904,110702147097335,110702533673554)]
theorem point_links_checked46313 : (cuts46313.take 1).map (fun c => (6074269697-1+2*2^10*c.k,110701951363392+c.lower,110702337939497+c.upper)) = pointBounds46313 := by
 decide +kernel
def cuts46314 : List PrefixCut := [⟨64,267737381,267737536⟩]
theorem checked46314 : checkPrefixCuts (2^48) 6074400769 10 Manual.Count131072.C046314.packed 64 cuts46314 = true := by
 decide +kernel
def cuts46315 : List PrefixCut := [⟨11,47356208,47356237⟩,
⟨64,274682099,274682258⟩]
theorem checked46315 : checkPrefixCuts (2^48) 6074531841 10 Manual.Count131072.C046315.packed 64 cuts46315 = true := by
 decide +kernel
def pointBounds46315 : List (Nat × Nat × Nat) := [(6074554368,110702537212190,110702923788638)]
theorem point_links_checked46315 : (cuts46315.take 1).map (fun c => (6074531841-1+2*2^10*c.k,110702489855982+c.lower,110702876432401+c.upper)) = pointBounds46315 := by
 decide +kernel
def cuts46316 : List PrefixCut := [⟨40,170005222,170005311⟩,
⟨64,270459663,270459810⟩]
theorem checked46316 : checkPrefixCuts (2^48) 6074662913 10 Manual.Count131072.C046316.packed 64 cuts46316 = true := by
 decide +kernel
def pointBounds46316 : List (Nat × Nat × Nat) := [(6074744832,110702934543303,110703321119970)]
theorem point_links_checked46316 : (cuts46316.take 1).map (fun c => (6074662913-1+2*2^10*c.k,110702764538081+c.lower,110703151114659+c.upper)) = pointBounds46316 := by
 decide +kernel
def cuts46317 : List PrefixCut := [⟨64,270453815,270453961⟩]
theorem checked46317 : checkPrefixCuts (2^48) 6074793985 10 Manual.Count131072.C046317.packed 64 cuts46317 = true := by
 decide +kernel
def cuts46318 : List PrefixCut := [⟨5,21220902,21220916⟩,
⟨64,267667966,267668123⟩]
theorem checked46318 : checkPrefixCuts (2^48) 6074925057 10 Manual.Count131072.C046318.packed 64 cuts46318 = true := by
 decide +kernel
def pointBounds46318 : List (Nat × Nat × Nat) := [(6074935296,110703326672461,110703713249346)]
theorem point_links_checked46318 : (cuts46318.take 1).map (fun c => (6074925057-1+2*2^10*c.k,110703305451559+c.lower,110703692028430+c.upper)) = pointBounds46318 := by
 decide +kernel
def cuts46319 : List PrefixCut := [⟨34,141360838,141360916⟩,
⟨64,270442134,270442282⟩]
theorem checked46319 : checkPrefixCuts (2^48) 6075056129 10 Manual.Count131072.C046319.packed 64 cuts46319 = true := by
 decide +kernel
def pointBounds46319 : List (Nat × Nat × Nat) := [(6075125760,110703714480363,110704101057469)]
theorem point_links_checked46319 : (cuts46319.take 1).map (fun c => (6075056129-1+2*2^10*c.k,110703573119525+c.lower,110703959696553+c.upper)) = pointBounds46319 := by
 decide +kernel
def cuts46320 : List PrefixCut := [⟨63,267332158,267332319⟩,
⟨64,271316615,271316778⟩]
theorem checked46320 : checkPrefixCuts (2^48) 6075187201 10 Manual.Count131072.C046320.packed 64 cuts46320 = true := by
 decide +kernel
def pointBounds46320 : List (Nat × Nat × Nat) := [(6075316224,110704110893817,110704497471154)]
theorem point_links_checked46320 : (cuts46320.take 1).map (fun c => (6075187201-1+2*2^10*c.k,110703843561659+c.lower,110704230138835+c.upper)) = pointBounds46320 := by
 decide +kernel
def cuts46321 : List PrefixCut := [⟨64,267928634,267928787⟩]
theorem checked46321 : checkPrefixCuts (2^48) 6075318273 10 Manual.Count131072.C046321.packed 64 cuts46321 = true := by
 decide +kernel
def cuts46322 : List PrefixCut := [⟨28,119298893,119298962⟩,
⟨64,269451725,269451880⟩]
theorem checked46322 : checkPrefixCuts (2^48) 6075449345 10 Manual.Count131072.C046322.packed 64 cuts46322 = true := by
 decide +kernel
def pointBounds46322 : List (Nat × Nat × Nat) := [(6075506688,110704502105801,110704888683362)]
theorem point_links_checked46322 : (cuts46322.take 1).map (fun c => (6075449345-1+2*2^10*c.k,110704382806908+c.lower,110704769384400+c.upper)) = pointBounds46322 := by
 decide +kernel
def cuts46323 : List PrefixCut := [⟨57,240027660,240027795⟩,
⟨64,268658329,268658482⟩]
theorem checked46323 : checkPrefixCuts (2^48) 6075580417 10 Manual.Count131072.C046323.packed 64 cuts46323 = true := by
 decide +kernel
def pointBounds46323 : List (Nat × Nat × Nat) := [(6075697152,110704892286293,110705278864075)]
theorem point_links_checked46323 : (cuts46323.take 1).map (fun c => (6075580417-1+2*2^10*c.k,110704652258633+c.lower,110705038836280+c.upper)) = pointBounds46323 := by
 decide +kernel
def cuts46324 : List PrefixCut := [⟨64,271478489,271478644⟩]
theorem checked46324 : checkPrefixCuts (2^48) 6075711489 10 Manual.Count131072.C046324.packed 64 cuts46324 = true := by
 decide +kernel
def cuts46325 : List PrefixCut := [⟨22,92329155,92329204⟩,
⟨64,267905535,267905681⟩]
theorem checked46325 : checkPrefixCuts (2^48) 6075842561 10 Manual.Count131072.C046325.packed 64 cuts46325 = true := by
 decide +kernel
def pointBounds46325 : List (Nat × Nat × Nat) := [(6075887616,110705284724606,110705671302610)]
theorem point_links_checked46325 : (cuts46325.take 1).map (fun c => (6075842561-1+2*2^10*c.k,110705192395451+c.lower,110705578973406+c.upper)) = pointBounds46325 := by
 decide +kernel
def cuts46326 : List PrefixCut := [⟨51,217359231,217359353⟩,
⟨64,271837424,271837577⟩]
theorem checked46326 : checkPrefixCuts (2^48) 6075973633 10 Manual.Count131072.C046326.packed 64 cuts46326 = true := by
 decide +kernel
def pointBounds46326 : List (Nat × Nat × Nat) := [(6076078080,110705677660217,110706064238440)]
theorem point_links_checked46326 : (cuts46326.take 1).map (fun c => (6075973633-1+2*2^10*c.k,110705460300986+c.lower,110705846879087+c.upper)) = pointBounds46326 := by
 decide +kernel
def cuts46327 : List PrefixCut := [⟨64,266226291,266226449⟩]
theorem checked46327 : checkPrefixCuts (2^48) 6076104705 10 Manual.Count131072.C046327.packed 64 cuts46327 = true := by
 decide +kernel
def cuts46328 : List PrefixCut := [⟨16,67076817,67076856⟩,
⟨64,269694779,269694930⟩]
theorem checked46328 : checkPrefixCuts (2^48) 6076235777 10 Manual.Count131072.C046328.packed 64 cuts46328 = true := by
 decide +kernel
def pointBounds46328 : List (Nat × Nat × Nat) := [(6076268544,110706065441518,110706452019969)]
theorem point_links_checked46328 : (cuts46328.take 1).map (fun c => (6076235777-1+2*2^10*c.k,110705998364701+c.lower,110706384943113+c.upper)) = pointBounds46328 := by
 decide +kernel
def cuts46329 : List PrefixCut := [⟨45,190339327,190339435⟩,
⟨64,270383817,270383971⟩]
theorem checked46329 : checkPrefixCuts (2^48) 6076366849 10 Manual.Count131072.C046329.packed 64 cuts46329 = true := by
 decide +kernel
def pointBounds46329 : List (Nat × Nat × Nat) := [(6076459008,110706458398807,110706844977478)]
theorem point_links_checked46329 : (cuts46329.take 1).map (fun c => (6076366849-1+2*2^10*c.k,110706268059480+c.lower,110706654638043+c.upper)) = pointBounds46329 := by
 decide +kernel
def cuts46330 : List PrefixCut := [⟨64,267691336,267691493⟩]
theorem checked46330 : checkPrefixCuts (2^48) 6076497921 10 Manual.Count131072.C046330.packed 64 cuts46330 = true := by
 decide +kernel
def cuts46331 : List PrefixCut := [⟨10,42244583,42244608⟩,
⟨64,269075158,269075319⟩]
theorem checked46331 : checkPrefixCuts (2^48) 6076628993 10 Manual.Count131072.C046331.packed 64 cuts46331 = true := by
 decide +kernel
def pointBounds46331 : List (Nat × Nat × Nat) := [(6076649472,110706848379216,110707234958115)]
theorem point_links_checked46331 : (cuts46331.take 1).map (fun c => (6076628993-1+2*2^10*c.k,110706806134633+c.lower,110707192713507+c.upper)) = pointBounds46331 := by
 decide +kernel
def cuts46332 : List PrefixCut := [⟨39,163786085,163786182⟩,
⟨64,267170297,267170456⟩]
theorem checked46332 : checkPrefixCuts (2^48) 6076760065 10 Manual.Count131072.C046332.packed 64 cuts46332 = true := by
 decide +kernel
def pointBounds46332 : List (Nat × Nat × Nat) := [(6076839936,110707238995876,110707625575008)]
theorem point_links_checked46332 : (cuts46332.take 1).map (fun c => (6076760065-1+2*2^10*c.k,110707075209791+c.lower,110707461788826+c.upper)) = pointBounds46332 := by
 decide +kernel
def cuts46333 : List PrefixCut := [⟨64,269017249,269017401⟩]
theorem checked46333 : checkPrefixCuts (2^48) 6076891137 10 Manual.Count131072.C046333.packed 64 cuts46333 = true := by
 decide +kernel
def cuts46334 : List PrefixCut := [⟨4,15933347,15933355⟩,
⟨64,263453346,263453497⟩]
theorem checked46334 : checkPrefixCuts (2^48) 6077022209 10 Manual.Count131072.C046334.packed 64 cuts46334 = true := by
 decide +kernel
def pointBounds46334 : List (Nat × Nat × Nat) := [(6077030400,110707627330684,110708013910038)]
theorem point_links_checked46334 : (cuts46334.take 1).map (fun c => (6077022209-1+2*2^10*c.k,110707611397337+c.lower,110707997976683+c.upper)) = pointBounds46334 := by
 decide +kernel
def cuts46335 : List PrefixCut := [⟨33,140432055,140432136⟩,
⟨64,268542511,268542670⟩]
theorem checked46335 : checkPrefixCuts (2^48) 6077153281 10 Manual.Count131072.C046335.packed 64 cuts46335 = true := by
 decide +kernel
def pointBounds46335 : List (Nat × Nat × Nat) := [(6077220864,110708015282738,110708401862316)]
theorem point_links_checked46335 : (cuts46335.take 1).map (fun c => (6077153281-1+2*2^10*c.k,110707874850683+c.lower,110708261430180+c.upper)) = pointBounds46335 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000197
