import PlattAssemblyKernel
import PlattCertificates.Count131072.C061312
import PlattCertificates.Count131072.C061313
import PlattCertificates.Count131072.C061314
import PlattCertificates.Count131072.C061315
import PlattCertificates.Count131072.C061316
import PlattCertificates.Count131072.C061317
import PlattCertificates.Count131072.C061318
import PlattCertificates.Count131072.C061319
import PlattCertificates.Count131072.C061320
import PlattCertificates.Count131072.C061321
import PlattCertificates.Count131072.C061322
import PlattCertificates.Count131072.C061323
import PlattCertificates.Count131072.C061324
import PlattCertificates.Count131072.C061325
import PlattCertificates.Count131072.C061326
import PlattCertificates.Count131072.C061327
import PlattCertificates.Count131072.C061328
import PlattCertificates.Count131072.C061329
import PlattCertificates.Count131072.C061330
import PlattCertificates.Count131072.C061331
import PlattCertificates.Count131072.C061332
import PlattCertificates.Count131072.C061333
import PlattCertificates.Count131072.C061334
import PlattCertificates.Count131072.C061335
import PlattCertificates.Count131072.C061336
import PlattCertificates.Count131072.C061337
import PlattCertificates.Count131072.C061338
import PlattCertificates.Count131072.C061339
import PlattCertificates.Count131072.C061340
import PlattCertificates.Count131072.C061341
import PlattCertificates.Count131072.C061342
import PlattCertificates.Count131072.C061343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61312 : List PrefixCut := [⟨64,201331471,201331583⟩]
theorem checked61312 : checkPrefixCuts (2^48) 8040218625 10 Manual.Count131072.C061312.packed 64 cuts61312 = true := by
 decide +kernel
def cuts61313 : List PrefixCut := [⟨10,31261919,31261938⟩,
⟨64,200803062,200803180⟩]
theorem checked61313 : checkPrefixCuts (2^48) 8040349697 10 Manual.Count131072.C061313.packed 64 cuts61313 = true := by
 decide +kernel
def pointBounds61313 : List (Nat × Nat × Nat) := [(8040370176,114184005353281,114184393913291)]
theorem point_links_checked61313 : (cuts61313.take 1).map (fun c => (8040349697-1+2*2^10*c.k,114183974091362+c.lower,114184362651353+c.upper)) = pointBounds61313 := by
 decide +kernel
def cuts61314 : List PrefixCut := [⟨64,201674969,201675081⟩]
theorem checked61314 : checkPrefixCuts (2^48) 8040480769 10 Manual.Count131072.C061314.packed 64 cuts61314 = true := by
 decide +kernel
def cuts61315 : List PrefixCut := [⟨5,16068043,16068053⟩,
⟨64,201531654,201531771⟩]
theorem checked61315 : checkPrefixCuts (2^48) 8040611841 10 Manual.Count131072.C061315.packed 64 cuts61315 = true := by
 decide +kernel
def pointBounds61315 : List (Nat × Nat × Nat) := [(8040622080,114184392637436,114184781197667)]
theorem point_links_checked61315 : (cuts61315.take 1).map (fun c => (8040611841-1+2*2^10*c.k,114184376569393+c.lower,114184765129614+c.upper)) = pointBounds61315 := by
 decide +kernel
def cuts61316 : List PrefixCut := [⟨64,199393031,199393138⟩]
theorem checked61316 : checkPrefixCuts (2^48) 8040742913 10 Manual.Count131072.C061316.packed 64 cuts61316 = true := by
 decide +kernel
def pointBounds61316 : List (Nat × Nat × Nat) := [(8040873984,114184777494078,114185166054523)]
theorem point_links_checked61316 : (cuts61316.take 1).map (fun c => (8040742913-1+2*2^10*c.k,114184578101047+c.lower,114184966661385+c.upper)) = pointBounds61316 := by
 decide +kernel
def cuts61317 : List PrefixCut := [⟨64,203205324,203205437⟩]
theorem checked61317 : checkPrefixCuts (2^48) 8040873985 10 Manual.Count131072.C061317.packed 64 cuts61317 = true := by
 decide +kernel
def cuts61318 : List PrefixCut := [⟨59,187520067,187520168⟩,
⟨64,203832113,203832224⟩]
theorem checked61318 : checkPrefixCuts (2^48) 8041005057 10 Manual.Count131072.C061318.packed 64 cuts61318 = true := by
 decide +kernel
def pointBounds61318 : List (Nat × Nat × Nat) := [(8041125888,114185168219469,114185556780128)]
theorem point_links_checked61318 : (cuts61318.take 1).map (fun c => (8041005057-1+2*2^10*c.k,114184980699402+c.lower,114185369259960+c.upper)) = pointBounds61318 := by
 decide +kernel
def cuts61319 : List PrefixCut := [⟨64,200748422,200748541⟩]
theorem checked61319 : checkPrefixCuts (2^48) 8041136129 10 Manual.Count131072.C061319.packed 64 cuts61319 = true := by
 decide +kernel
def cuts61320 : List PrefixCut := [⟨54,165741836,165741932⟩,
⟨64,197174773,197174888⟩]
theorem checked61320 : checkPrefixCuts (2^48) 8041267201 10 Manual.Count131072.C061320.packed 64 cuts61320 = true := by
 decide +kernel
def pointBounds61320 : List (Nat × Nat × Nat) := [(8041377792,114185551021773,114185939582657)]
theorem point_links_checked61320 : (cuts61320.take 1).map (fun c => (8041267201-1+2*2^10*c.k,114185385279937+c.lower,114185773840725+c.upper)) = pointBounds61320 := by
 decide +kernel
def cuts61321 : List PrefixCut := [⟨64,202036987,202037107⟩]
theorem checked61321 : checkPrefixCuts (2^48) 8041398273 10 Manual.Count131072.C061321.packed 64 cuts61321 = true := by
 decide +kernel
def cuts61322 : List PrefixCut := [⟨49,153695701,153695794⟩,
⟨64,200738596,200738713⟩]
theorem checked61322 : checkPrefixCuts (2^48) 8041529345 10 Manual.Count131072.C061322.packed 64 cuts61322 = true := by
 decide +kernel
def pointBounds61322 : List (Nat × Nat × Nat) := [(8041629696,114185938187398,114186326748514)]
theorem point_links_checked61322 : (cuts61322.take 1).map (fun c => (8041529345-1+2*2^10*c.k,114185784491697+c.lower,114186173052720+c.upper)) = pointBounds61322 := by
 decide +kernel
def cuts61323 : List PrefixCut := [⟨64,201785396,201785509⟩]
theorem checked61323 : checkPrefixCuts (2^48) 8041660417 10 Manual.Count131072.C061323.packed 64 cuts61323 = true := by
 decide +kernel
def cuts61324 : List PrefixCut := [⟨44,139200251,139200332⟩,
⟨64,200732071,200732190⟩]
theorem checked61324 : checkPrefixCuts (2^48) 8041791489 10 Manual.Count131072.C061324.packed 64 cuts61324 = true := by
 decide +kernel
def pointBounds61324 : List (Nat × Nat × Nat) := [(8041881600,114186326215940,114186714777274)]
theorem point_links_checked61324 : (cuts61324.take 1).map (fun c => (8041791489-1+2*2^10*c.k,114186187015689+c.lower,114186575576942+c.upper)) = pointBounds61324 := by
 decide +kernel
def cuts61325 : List PrefixCut := [⟨64,201498802,201498913⟩]
theorem checked61325 : checkPrefixCuts (2^48) 8041922561 10 Manual.Count131072.C061325.packed 64 cuts61325 = true := by
 decide +kernel
def cuts61326 : List PrefixCut := [⟨39,119980695,119980768⟩,
⟨64,197960507,197960627⟩]
theorem checked61326 : checkPrefixCuts (2^48) 8042053633 10 Manual.Count131072.C061326.packed 64 cuts61326 = true := by
 decide +kernel
def pointBounds61326 : List (Nat × Nat × Nat) := [(8042133504,114186709227257,114187097788813)]
theorem point_links_checked61326 : (cuts61326.take 1).map (fun c => (8042053633-1+2*2^10*c.k,114186589246562+c.lower,114186977808045+c.upper)) = pointBounds61326 := by
 decide +kernel
def cuts61327 : List PrefixCut := [⟨64,201107246,201107360⟩]
theorem checked61327 : checkPrefixCuts (2^48) 8042184705 10 Manual.Count131072.C061327.packed 64 cuts61327 = true := by
 decide +kernel
def cuts61328 : List PrefixCut := [⟨34,105382242,105382298⟩,
⟨64,202223914,202224028⟩]
theorem checked61328 : checkPrefixCuts (2^48) 8042315777 10 Manual.Count131072.C061328.packed 64 cuts61328 = true := by
 decide +kernel
def pointBounds61328 : List (Nat × Nat × Nat) := [(8042385408,114187093696557,114187482258330)]
theorem point_links_checked61328 : (cuts61328.take 1).map (fun c => (8042315777-1+2*2^10*c.k,114186988314315+c.lower,114187376876032+c.upper)) = pointBounds61328 := by
 decide +kernel
def cuts61329 : List PrefixCut := [⟨64,204250542,204250652⟩]
theorem checked61329 : checkPrefixCuts (2^48) 8042446849 10 Manual.Count131072.C061329.packed 64 cuts61329 = true := by
 decide +kernel
def cuts61330 : List PrefixCut := [⟨29,91344684,91344735⟩,
⟨64,200432450,200432568⟩]
theorem checked61330 : checkPrefixCuts (2^48) 8042577921 10 Manual.Count131072.C061330.packed 64 cuts61330 = true := by
 decide +kernel
def pointBounds61330 : List (Nat × Nat × Nat) := [(8042637312,114187486133455,114187874695447)]
theorem point_links_checked61330 : (cuts61330.take 1).map (fun c => (8042577921-1+2*2^10*c.k,114187394788771+c.lower,114187783350712+c.upper)) = pointBounds61330 := by
 decide +kernel
def cuts61331 : List PrefixCut := [⟨64,202808991,202809109⟩]
theorem checked61331 : checkPrefixCuts (2^48) 8042708993 10 Manual.Count131072.C061331.packed 64 cuts61331 = true := by
 decide +kernel
def cuts61332 : List PrefixCut := [⟨24,76153137,76153183⟩,
⟨64,201300841,201300955⟩]
theorem checked61332 : checkPrefixCuts (2^48) 8042840065 10 Manual.Count131072.C061332.packed 64 cuts61332 = true := by
 decide +kernel
def pointBounds61332 : List (Nat × Nat × Nat) := [(8042889216,114187874183349,114188262745572)]
theorem point_links_checked61332 : (cuts61332.take 1).map (fun c => (8042840065-1+2*2^10*c.k,114187798030212+c.lower,114188186592389+c.upper)) = pointBounds61332 := by
 decide +kernel
def cuts61333 : List PrefixCut := [⟨64,201402549,201402663⟩]
theorem checked61333 : checkPrefixCuts (2^48) 8042971137 10 Manual.Count131072.C061333.packed 64 cuts61333 = true := by
 decide +kernel
def cuts61334 : List PrefixCut := [⟨19,60157658,60157688⟩,
⟨64,202589106,202589219⟩]
theorem checked61334 : checkPrefixCuts (2^48) 8043102209 10 Manual.Count131072.C061334.packed 64 cuts61334 = true := by
 decide +kernel
def pointBounds61334 : List (Nat × Nat × Nat) := [(8043141120,114188260891260,114188649453695)]
theorem point_links_checked61334 : (cuts61334.take 1).map (fun c => (8043102209-1+2*2^10*c.k,114188200733602+c.lower,114188589296007+c.upper)) = pointBounds61334 := by
 decide +kernel
def cuts61335 : List PrefixCut := [⟨64,203635654,203635771⟩]
theorem checked61335 : checkPrefixCuts (2^48) 8043233281 10 Manual.Count131072.C061335.packed 64 cuts61335 = true := by
 decide +kernel
def cuts61336 : List PrefixCut := [⟨14,43078364,43078389⟩,
⟨64,199817950,199818062⟩]
theorem checked61336 : checkPrefixCuts (2^48) 8043364353 10 Manual.Count131072.C061336.packed 64 cuts61336 = true := by
 decide +kernel
def pointBounds61336 : List (Nat × Nat × Nat) := [(8043393024,114188650036726,114189038599386)]
theorem point_links_checked61336 : (cuts61336.take 1).map (fun c => (8043364353-1+2*2^10*c.k,114188606958362+c.lower,114188995520997+c.upper)) = pointBounds61336 := by
 decide +kernel
def cuts61337 : List PrefixCut := [⟨64,203069119,203069230⟩]
theorem checked61337 : checkPrefixCuts (2^48) 8043495425 10 Manual.Count131072.C061337.packed 64 cuts61337 = true := by
 decide +kernel
def cuts61338 : List PrefixCut := [⟨9,29464520,29464537⟩,
⟨64,203170794,203170909⟩]
theorem checked61338 : checkPrefixCuts (2^48) 8043626497 10 Manual.Count131072.C061338.packed 64 cuts61338 = true := by
 decide +kernel
def pointBounds61338 : List (Nat × Nat × Nat) := [(8043644928,114189039309951,114189427872826)]
theorem point_links_checked61338 : (cuts61338.take 1).map (fun c => (8043626497-1+2*2^10*c.k,114189009845431+c.lower,114189398408289+c.upper)) = pointBounds61338 := by
 decide +kernel
def cuts61339 : List PrefixCut := [⟨64,202152703,202152819⟩]
theorem checked61339 : checkPrefixCuts (2^48) 8043757569 10 Manual.Count131072.C061339.packed 64 cuts61339 = true := by
 decide +kernel
def cuts61340 : List PrefixCut := [⟨4,13227117,13227125⟩,
⟨64,202219385,202219503⟩]
theorem checked61340 : checkPrefixCuts (2^48) 8043888641 10 Manual.Count131072.C061340.packed 64 cuts61340 = true := by
 decide +kernel
def pointBounds61340 : List (Nat × Nat × Nat) := [(8043896832,114189428396045,114189816959142)]
theorem point_links_checked61340 : (cuts61340.take 1).map (fun c => (8043888641-1+2*2^10*c.k,114189415168928+c.lower,114189803732017+c.upper)) = pointBounds61340 := by
 decide +kernel
def cuts61341 : List PrefixCut := [⟨63,198367042,198367154⟩,
⟨64,201236325,201236439⟩]
theorem checked61341 : checkPrefixCuts (2^48) 8044019713 10 Manual.Count131072.C061341.packed 64 cuts61341 = true := by
 decide +kernel
def pointBounds61341 : List (Nat × Nat × Nat) := [(8044148736,114189815755355,114190204318674)]
theorem point_links_checked61341 : (cuts61341.take 1).map (fun c => (8044019713-1+2*2^10*c.k,114189617388313+c.lower,114190005951520+c.upper)) = pointBounds61341 := by
 decide +kernel
def cuts61342 : List PrefixCut := [⟨64,199238571,199238686⟩]
theorem checked61342 : checkPrefixCuts (2^48) 8044150785 10 Manual.Count131072.C061342.packed 64 cuts61342 = true := by
 decide +kernel
def cuts61343 : List PrefixCut := [⟨58,183664731,183664843⟩,
⟨64,202419444,202419568⟩]
theorem checked61343 : checkPrefixCuts (2^48) 8044281857 10 Manual.Count131072.C061343.packed 64 cuts61343 = true := by
 decide +kernel
def pointBounds61343 : List (Nat × Nat × Nat) := [(8044400640,114190201527940,114190590091488)]
theorem point_links_checked61343 : (cuts61343.take 1).map (fun c => (8044281857-1+2*2^10*c.k,114190017863209+c.lower,114190406426645+c.upper)) = pointBounds61343 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000041
