import PlattAssemblyKernel
import PlattCertificates.Count131072.C069408
import PlattCertificates.Count131072.C069409
import PlattCertificates.Count131072.C069410
import PlattCertificates.Count131072.C069411
import PlattCertificates.Count131072.C069412
import PlattCertificates.Count131072.C069413
import PlattCertificates.Count131072.C069414
import PlattCertificates.Count131072.C069415
import PlattCertificates.Count131072.C069416
import PlattCertificates.Count131072.C069417
import PlattCertificates.Count131072.C069418
import PlattCertificates.Count131072.C069419
import PlattCertificates.Count131072.C069420
import PlattCertificates.Count131072.C069421
import PlattCertificates.Count131072.C069422
import PlattCertificates.Count131072.C069423
import PlattCertificates.Count131072.C069424
import PlattCertificates.Count131072.C069425
import PlattCertificates.Count131072.C069426
import PlattCertificates.Count131072.C069427
import PlattCertificates.Count131072.C069428
import PlattCertificates.Count131072.C069429
import PlattCertificates.Count131072.C069430
import PlattCertificates.Count131072.C069431
import PlattCertificates.Count131072.C069432
import PlattCertificates.Count131072.C069433
import PlattCertificates.Count131072.C069434
import PlattCertificates.Count131072.C069435
import PlattCertificates.Count131072.C069436
import PlattCertificates.Count131072.C069437
import PlattCertificates.Count131072.C069438
import PlattCertificates.Count131072.C069439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000294
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69408 : List PrefixCut := [⟨64,177981446,177981551⟩]
theorem checked69408 : checkPrefixCuts (2^48) 9101377537 10 Manual.Count131072.C069408.packed 64 cuts69408 = true := by
 decide +kernel
def cuts69409 : List PrefixCut := [⟨11,29998358,29998373⟩,
⟨64,174051281,174051385⟩]
theorem checked69409 : checkPrefixCuts (2^48) 9101508609 10 Manual.Count131072.C069409.packed 64 cuts69409 = true := by
 decide +kernel
def pointBounds69409 : List (Nat × Nat × Nat) := [(9101531136,115709788114413,115710177558458)]
theorem point_links_checked69409 : (cuts69409.take 1).map (fun c => (9101508609-1+2*2^10*c.k,115709758116055+c.lower,115710147560085+c.upper)) = pointBounds69409 := by
 decide +kernel
def cuts69410 : List PrefixCut := [⟨64,176491889,176491997⟩]
theorem checked69410 : checkPrefixCuts (2^48) 9101639681 10 Manual.Count131072.C069410.packed 64 cuts69410 = true := by
 decide +kernel
def cuts69411 : List PrefixCut := [⟨22,60551566,60551605⟩,
⟨64,178499480,178499589⟩]
theorem checked69411 : checkPrefixCuts (2^48) 9101770753 10 Manual.Count131072.C069411.packed 64 cuts69411 = true := by
 decide +kernel
def pointBounds69411 : List (Nat × Nat × Nat) := [(9101815808,115710169210791,115710558655072)]
theorem point_links_checked69411 : (cuts69411.take 1).map (fun c => (9101770753-1+2*2^10*c.k,115710108659225+c.lower,115710498103467+c.upper)) = pointBounds69411 := by
 decide +kernel
def cuts69412 : List PrefixCut := [⟨64,177754717,177754821⟩]
theorem checked69412 : checkPrefixCuts (2^48) 9101901825 10 Manual.Count131072.C069412.packed 64 cuts69412 = true := by
 decide +kernel
def cuts69413 : List PrefixCut := [⟨33,88165129,88165185⟩,
⟨64,173299072,173299178⟩]
theorem checked69413 : checkPrefixCuts (2^48) 9102032897 10 Manual.Count131072.C069413.packed 64 cuts69413 = true := by
 decide +kernel
def pointBounds69413 : List (Nat × Nat × Nat) := [(9102100480,115710553078551,115710942523062)]
theorem point_links_checked69413 : (cuts69413.take 1).map (fun c => (9102032897-1+2*2^10*c.k,115710464913422+c.lower,115710854357877+c.upper)) = pointBounds69413 := by
 decide +kernel
def cuts69414 : List PrefixCut := [⟨64,175554014,175554126⟩]
theorem checked69414 : checkPrefixCuts (2^48) 9102163969 10 Manual.Count131072.C069414.packed 64 cuts69414 = true := by
 decide +kernel
def cuts69415 : List PrefixCut := [⟨44,120322774,120322842⟩,
⟨64,176139028,176139128⟩]
theorem checked69415 : checkPrefixCuts (2^48) 9102295041 10 Manual.Count131072.C069415.packed 64 cuts69415 = true := by
 decide +kernel
def pointBounds69415 : List (Nat × Nat × Nat) := [(9102385152,115710934089282,115711323534023)]
theorem point_links_checked69415 : (cuts69415.take 1).map (fun c => (9102295041-1+2*2^10*c.k,115710813766508+c.lower,115711203211181+c.upper)) = pointBounds69415 := by
 decide +kernel
def cuts69416 : List PrefixCut := [⟨64,177156956,177157062⟩]
theorem checked69416 : checkPrefixCuts (2^48) 9102426113 10 Manual.Count131072.C069416.packed 64 cuts69416 = true := by
 decide +kernel
def cuts69417 : List PrefixCut := [⟨55,151396202,151396290⟩,
⟨64,176752408,176752513⟩]
theorem checked69417 : checkPrefixCuts (2^48) 9102557185 10 Manual.Count131072.C069417.packed 64 cuts69417 = true := by
 decide +kernel
def pointBounds69417 : List (Nat × Nat × Nat) := [(9102669824,115711318458694,115711707903661)]
theorem point_links_checked69417 : (cuts69417.take 1).map (fun c => (9102557185-1+2*2^10*c.k,115711167062492+c.lower,115711556507371+c.upper)) = pointBounds69417 := by
 decide +kernel
def cuts69418 : List PrefixCut := [⟨64,178110413,178110522⟩]
theorem checked69418 : checkPrefixCuts (2^48) 9102688257 10 Manual.Count131072.C069418.packed 64 cuts69418 = true := by
 decide +kernel
def cuts69419 : List PrefixCut := [⟨64,176994691,176994792⟩]
theorem checked69419 : checkPrefixCuts (2^48) 9102819329 10 Manual.Count131072.C069419.packed 64 cuts69419 = true := by
 decide +kernel
def cuts69420 : List PrefixCut := [⟨2,5627672,5627676⟩,
⟨64,175971745,175971855⟩]
theorem checked69420 : checkPrefixCuts (2^48) 9102950401 10 Manual.Count131072.C069420.packed 64 cuts69420 = true := by
 decide +kernel
def pointBounds69420 : List (Nat × Nat × Nat) := [(9102954496,115711704547676,115712093992874)]
theorem point_links_checked69420 : (cuts69420.take 1).map (fun c => (9102950401-1+2*2^10*c.k,115711698920004+c.lower,115712088365198+c.upper)) = pointBounds69420 := by
 decide +kernel
def cuts69421 : List PrefixCut := [⟨64,175660009,175660111⟩]
theorem checked69421 : checkPrefixCuts (2^48) 9103081473 10 Manual.Count131072.C069421.packed 64 cuts69421 = true := by
 decide +kernel
def cuts69422 : List PrefixCut := [⟨13,34321581,34321604⟩,
⟨64,175719302,175719407⟩]
theorem checked69422 : checkPrefixCuts (2^48) 9103212545 10 Manual.Count131072.C069422.packed 64 cuts69422 = true := by
 decide +kernel
def pointBounds69422 : List (Nat × Nat × Nat) := [(9103239168,115712084873339,115712474318768)]
theorem point_links_checked69422 : (cuts69422.take 1).map (fun c => (9103212545-1+2*2^10*c.k,115712050551758+c.lower,115712439997164+c.upper)) = pointBounds69422 := by
 decide +kernel
def cuts69423 : List PrefixCut := [⟨64,175222065,175222160⟩]
theorem checked69423 : checkPrefixCuts (2^48) 9103343617 10 Manual.Count131072.C069423.packed 64 cuts69423 = true := by
 decide +kernel
def cuts69424 : List PrefixCut := [⟨24,66322152,66322191⟩,
⟨64,178837094,178837199⟩]
theorem checked69424 : checkPrefixCuts (2^48) 9103474689 10 Manual.Count131072.C069424.packed 64 cuts69424 = true := by
 decide +kernel
def pointBounds69424 : List (Nat × Nat × Nat) := [(9103523840,115712467815277,115712857260922)]
theorem point_links_checked69424 : (cuts69424.take 1).map (fun c => (9103474689-1+2*2^10*c.k,115712401493125+c.lower,115712790938731+c.upper)) = pointBounds69424 := by
 decide +kernel
def cuts69425 : List PrefixCut := [⟨64,175588064,175588170⟩]
theorem checked69425 : checkPrefixCuts (2^48) 9103605761 10 Manual.Count131072.C069425.packed 64 cuts69425 = true := by
 decide +kernel
def cuts69426 : List PrefixCut := [⟨35,95259865,95259918⟩,
⟨64,176172969,176173069⟩]
theorem checked69426 : checkPrefixCuts (2^48) 9103736833 10 Manual.Count131072.C069426.packed 64 cuts69426 = true := by
 decide +kernel
def pointBounds69426 : List (Nat × Nat × Nat) := [(9103808512,115712851178148,115713240624018)]
theorem point_links_checked69426 : (cuts69426.take 1).map (fun c => (9103736833-1+2*2^10*c.k,115712755918283+c.lower,115713145364100+c.upper)) = pointBounds69426 := by
 decide +kernel
def cuts69427 : List PrefixCut := [⟨64,173882516,173882620⟩]
theorem checked69427 : checkPrefixCuts (2^48) 9103867905 10 Manual.Count131072.C069427.packed 64 cuts69427 = true := by
 decide +kernel
def cuts69428 : List PrefixCut := [⟨46,127133006,127133084⟩,
⟨64,176631663,176631773⟩]
theorem checked69428 : checkPrefixCuts (2^48) 9103998977 10 Manual.Count131072.C069428.packed 64 cuts69428 = true := by
 decide +kernel
def pointBounds69428 : List (Nat × Nat × Nat) := [(9104093184,115713233106774,115713622552873)]
theorem point_links_checked69428 : (cuts69428.take 1).map (fun c => (9103998977-1+2*2^10*c.k,115713105973768+c.lower,115713495419789+c.upper)) = pointBounds69428 := by
 decide +kernel
def cuts69429 : List PrefixCut := [⟨64,177247461,177247566⟩]
theorem checked69429 : checkPrefixCuts (2^48) 9104130049 10 Manual.Count131072.C069429.packed 64 cuts69429 = true := by
 decide +kernel
def cuts69430 : List PrefixCut := [⟨57,158540486,158540580⟩,
⟨64,177584994,177585100⟩]
theorem checked69430 : checkPrefixCuts (2^48) 9104261121 10 Manual.Count131072.C069430.packed 64 cuts69430 = true := by
 decide +kernel
def pointBounds69430 : List (Nat × Nat × Nat) := [(9104377856,115713618393378,115714007839708)]
theorem point_links_checked69430 : (cuts69430.take 1).map (fun c => (9104261121-1+2*2^10*c.k,115713459852892+c.lower,115713849299128+c.upper)) = pointBounds69430 := by
 decide +kernel
def cuts69431 : List PrefixCut := [⟨64,177149611,177149718⟩]
theorem checked69431 : checkPrefixCuts (2^48) 9104392193 10 Manual.Count131072.C069431.packed 64 cuts69431 = true := by
 decide +kernel
def cuts69432 : List PrefixCut := [⟨64,174797459,174797564⟩]
theorem checked69432 : checkPrefixCuts (2^48) 9104523265 10 Manual.Count131072.C069432.packed 64 cuts69432 = true := by
 decide +kernel
def cuts69433 : List PrefixCut := [⟨4,11686052,11686058⟩,
⟨64,173805671,173805777⟩]
theorem checked69433 : checkPrefixCuts (2^48) 9104654337 10 Manual.Count131072.C069433.packed 64 cuts69433 = true := by
 decide +kernel
def pointBounds69433 : List (Nat × Nat × Nat) := [(9104662528,115714001071008,115714390517568)]
theorem point_links_checked69433 : (cuts69433.take 1).map (fun c => (9104654337-1+2*2^10*c.k,115713989384956+c.lower,115714378831510+c.upper)) = pointBounds69433 := by
 decide +kernel
def cuts69434 : List PrefixCut := [⟨64,176090845,176090958⟩]
theorem checked69434 : checkPrefixCuts (2^48) 9104785409 10 Manual.Count131072.C069434.packed 64 cuts69434 = true := by
 decide +kernel
def cuts69435 : List PrefixCut := [⟨15,40869037,40869061⟩,
⟨64,175717348,175717454⟩]
theorem checked69435 : checkPrefixCuts (2^48) 9104916481 10 Manual.Count131072.C069435.packed 64 cuts69435 = true := by
 decide +kernel
def pointBounds69435 : List (Nat × Nat × Nat) := [(9104947200,115714380150509,115714769597306)]
theorem point_links_checked69435 : (cuts69435.take 1).map (fun c => (9104916481-1+2*2^10*c.k,115714339281472+c.lower,115714728728245+c.upper)) = pointBounds69435 := by
 decide +kernel
def cuts69436 : List PrefixCut := [⟨64,175962128,175962229⟩]
theorem checked69436 : checkPrefixCuts (2^48) 9105047553 10 Manual.Count131072.C069436.packed 64 cuts69436 = true := by
 decide +kernel
def cuts69437 : List PrefixCut := [⟨26,72430620,72430662⟩,
⟨64,178370855,178370956⟩]
theorem checked69437 : checkPrefixCuts (2^48) 9105178625 10 Manual.Count131072.C069437.packed 64 cuts69437 = true := by
 decide +kernel
def pointBounds69437 : List (Nat × Nat × Nat) := [(9105231872,115714763391568,115715152838590)]
theorem point_links_checked69437 : (cuts69437.take 1).map (fun c => (9105178625-1+2*2^10*c.k,115714690960948+c.lower,115715080407928+c.upper)) = pointBounds69437 := by
 decide +kernel
def cuts69438 : List PrefixCut := [⟨64,178646498,178646598⟩]
theorem checked69438 : checkPrefixCuts (2^48) 9105309697 10 Manual.Count131072.C069438.packed 64 cuts69438 = true := by
 decide +kernel
def cuts69439 : List PrefixCut := [⟨37,104732215,104732272⟩,
⟨64,179540401,179540502⟩]
theorem checked69439 : checkPrefixCuts (2^48) 9105440769 10 Manual.Count131072.C069439.packed 64 cuts69439 = true := by
 decide +kernel
def pointBounds69439 : List (Nat × Nat × Nat) := [(9105516544,115715152710516,115715542157754)]
theorem point_links_checked69439 : (cuts69439.take 1).map (fun c => (9105440769-1+2*2^10*c.k,115715047978301+c.lower,115715437425482+c.upper)) = pointBounds69439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000294
