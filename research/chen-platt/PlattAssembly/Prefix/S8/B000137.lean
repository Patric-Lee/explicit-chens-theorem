import PlattAssemblyKernel
import PlattCertificates.Count131072.C074384
import PlattCertificates.Count131072.C074385
import PlattCertificates.Count131072.C074386
import PlattCertificates.Count131072.C074387
import PlattCertificates.Count131072.C074388
import PlattCertificates.Count131072.C074389
import PlattCertificates.Count131072.C074390
import PlattCertificates.Count131072.C074391
import PlattCertificates.Count131072.C074392
import PlattCertificates.Count131072.C074393
import PlattCertificates.Count131072.C074394
import PlattCertificates.Count131072.C074395
import PlattCertificates.Count131072.C074396
import PlattCertificates.Count131072.C074397
import PlattCertificates.Count131072.C074398
import PlattCertificates.Count131072.C074399
import PlattCertificates.Count131072.C074400
import PlattCertificates.Count131072.C074401
import PlattCertificates.Count131072.C074402
import PlattCertificates.Count131072.C074403
import PlattCertificates.Count131072.C074404
import PlattCertificates.Count131072.C074405
import PlattCertificates.Count131072.C074406
import PlattCertificates.Count131072.C074407
import PlattCertificates.Count131072.C074408
import PlattCertificates.Count131072.C074409
import PlattCertificates.Count131072.C074410
import PlattCertificates.Count131072.C074411
import PlattCertificates.Count131072.C074412
import PlattCertificates.Count131072.C074413
import PlattCertificates.Count131072.C074414
import PlattCertificates.Count131072.C074415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000137
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74384 : List PrefixCut := [⟨64,162992210,162992309⟩]
theorem checked74384 : checkPrefixCuts (2^48) 9753591809 10 Manual.Count131072.C074384.packed 64 cuts74384 = true := by
 decide +kernel
def cuts74385 : List PrefixCut := [⟨8,20777886,20777902⟩,
⟨64,161431692,161431802⟩]
theorem checked74385 : checkPrefixCuts (2^48) 9753722881 10 Manual.Count131072.C074385.packed 64 cuts74385 = true := by
 decide +kernel
def pointBounds74385 : List (Nat × Nat × Nat) := [(9753739264,116558044267733,116558434214716)]
theorem point_links_checked74385 : (cuts74385.take 1).map (fun c => (9753722881-1+2*2^10*c.k,116558023489847+c.lower,116558413436814+c.upper)) = pointBounds74385 := by
 decide +kernel
def cuts74386 : List PrefixCut := [⟨64,166133311,166133407⟩]
theorem checked74386 : checkPrefixCuts (2^48) 9753853953 10 Manual.Count131072.C074386.packed 64 cuts74386 = true := by
 decide +kernel
def cuts74387 : List PrefixCut := [⟨29,74047926,74047969⟩,
⟨64,166015646,166015741⟩]
theorem checked74387 : checkPrefixCuts (2^48) 9753985025 10 Manual.Count131072.C074387.packed 64 cuts74387 = true := by
 decide +kernel
def pointBounds74387 : List (Nat × Nat × Nat) := [(9754044416,116558425102776,116558815049992)]
theorem point_links_checked74387 : (cuts74387.take 1).map (fun c => (9753985025-1+2*2^10*c.k,116558351054850+c.lower,116558741002023+c.upper)) = pointBounds74387 := by
 decide +kernel
def cuts74388 : List PrefixCut := [⟨64,164512870,164512969⟩]
theorem checked74388 : checkPrefixCuts (2^48) 9754116097 10 Manual.Count131072.C074388.packed 64 cuts74388 = true := by
 decide +kernel
def cuts74389 : List PrefixCut := [⟨50,127747721,127747792⟩,
⟨64,163731532,163731626⟩]
theorem checked74389 : checkPrefixCuts (2^48) 9754247169 10 Manual.Count131072.C074389.packed 64 cuts74389 = true := by
 decide +kernel
def pointBounds74389 : List (Nat × Nat × Nat) := [(9754349568,116558809331087,116559199278525)]
theorem point_links_checked74389 : (cuts74389.take 1).map (fun c => (9754247169-1+2*2^10*c.k,116558681583366+c.lower,116559071530733+c.upper)) = pointBounds74389 := by
 decide +kernel
def cuts74390 : List PrefixCut := [⟨64,167047774,167047870⟩]
theorem checked74390 : checkPrefixCuts (2^48) 9754378241 10 Manual.Count131072.C074390.packed 64 cuts74390 = true := by
 decide +kernel
def cuts74391 : List PrefixCut := [⟨64,164996780,164996880⟩]
theorem checked74391 : checkPrefixCuts (2^48) 9754509313 10 Manual.Count131072.C074391.packed 64 cuts74391 = true := by
 decide +kernel
def cuts74392 : List PrefixCut := [⟨7,18525209,18525218⟩,
⟨64,166033358,166033454⟩]
theorem checked74392 : checkPrefixCuts (2^48) 9754640385 10 Manual.Count131072.C074392.packed 64 cuts74392 = true := by
 decide +kernel
def pointBounds74392 : List (Nat × Nat × Nat) := [(9754654720,116559195884661,116559585832327)]
theorem point_links_checked74392 : (cuts74392.take 1).map (fun c => (9754640385-1+2*2^10*c.k,116559177359452+c.lower,116559567307109+c.upper)) = pointBounds74392 := by
 decide +kernel
def cuts74393 : List PrefixCut := [⟨64,165252044,165252136⟩]
theorem checked74393 : checkPrefixCuts (2^48) 9754771457 10 Manual.Count131072.C074393.packed 64 cuts74393 = true := by
 decide +kernel
def cuts74394 : List PrefixCut := [⟨28,72021144,72021185⟩,
⟨64,163287711,163287805⟩]
theorem checked74394 : checkPrefixCuts (2^48) 9754902529 10 Manual.Count131072.C074394.packed 64 cuts74394 = true := by
 decide +kernel
def pointBounds74394 : List (Nat × Nat × Nat) := [(9754959872,116559580665998,116559970613884)]
theorem point_links_checked74394 : (cuts74394.take 1).map (fun c => (9754902529-1+2*2^10*c.k,116559508644854+c.lower,116559898592699+c.upper)) = pointBounds74394 := by
 decide +kernel
def cuts74395 : List PrefixCut := [⟨64,163776049,163776150⟩]
theorem checked74395 : checkPrefixCuts (2^48) 9755033601 10 Manual.Count131072.C074395.packed 64 cuts74395 = true := by
 decide +kernel
def cuts74396 : List PrefixCut := [⟨49,123494216,123494294⟩,
⟨64,162360006,162360108⟩]
theorem checked74396 : checkPrefixCuts (2^48) 9755164673 10 Manual.Count131072.C074396.packed 64 cuts74396 = true := by
 decide +kernel
def pointBounds74396 : List (Nat × Nat × Nat) := [(9755265024,116559959202830,116560349150948)]
theorem point_links_checked74396 : (cuts74396.take 1).map (fun c => (9755164673-1+2*2^10*c.k,116559835708614+c.lower,116560225656654+c.upper)) = pointBounds74396 := by
 decide +kernel
def cuts74397 : List PrefixCut := [⟨64,165445142,165445243⟩]
theorem checked74397 : checkPrefixCuts (2^48) 9755295745 10 Manual.Count131072.C074397.packed 64 cuts74397 = true := by
 decide +kernel
def cuts74398 : List PrefixCut := [⟨64,164086822,164086921⟩]
theorem checked74398 : checkPrefixCuts (2^48) 9755426817 10 Manual.Count131072.C074398.packed 64 cuts74398 = true := by
 decide +kernel
def cuts74399 : List PrefixCut := [⟨6,15176549,15176558⟩,
⟨64,163969205,163969309⟩]
theorem checked74399 : checkPrefixCuts (2^48) 9755557889 10 Manual.Count131072.C074399.packed 64 cuts74399 = true := by
 decide +kernel
def pointBounds74399 : List (Nat × Nat × Nat) := [(9755570176,116560342777133,116560732725484)]
theorem point_links_checked74399 : (cuts74399.take 1).map (fun c => (9755557889-1+2*2^10*c.k,116560327600584+c.lower,116560717548926+c.upper)) = pointBounds74399 := by
 decide +kernel
def cuts74400 : List PrefixCut := [⟨64,162466678,162466779⟩]
theorem checked74400 : checkPrefixCuts (2^48) 9755688961 10 Manual.Count131072.C074400.packed 64 cuts74400 = true := by
 decide +kernel
def cuts74401 : List PrefixCut := [⟨27,68956078,68956119⟩,
⟨64,163935943,163936050⟩]
theorem checked74401 : checkPrefixCuts (2^48) 9755820033 10 Manual.Count131072.C074401.packed 64 cuts74401 = true := by
 decide +kernel
def pointBounds74401 : List (Nat × Nat × Nat) := [(9755875328,116560722992545,116561112941133)]
theorem point_links_checked74401 : (cuts74401.take 1).map (fun c => (9755820033-1+2*2^10*c.k,116560654036467+c.lower,116561043985014+c.upper)) = pointBounds74401 := by
 decide +kernel
def cuts74402 : List PrefixCut := [⟨64,163645227,163645325⟩]
theorem checked74402 : checkPrefixCuts (2^48) 9755951105 10 Manual.Count131072.C074402.packed 64 cuts74402 = true := by
 decide +kernel
def cuts74403 : List PrefixCut := [⟨48,124405840,124405917⟩,
⟨64,164941329,164941430⟩]
theorem checked74403 : checkPrefixCuts (2^48) 9756082177 10 Manual.Count131072.C074403.packed 64 cuts74403 = true := by
 decide +kernel
def pointBounds74403 : List (Nat × Nat × Nat) := [(9756180480,116561106023477,116561495972306)]
theorem point_links_checked74403 : (cuts74403.take 1).map (fun c => (9756082177-1+2*2^10*c.k,116560981617637+c.lower,116561371566389+c.upper)) = pointBounds74403 := by
 decide +kernel
def cuts74404 : List PrefixCut := [⟨64,163323467,163323567⟩]
theorem checked74404 : checkPrefixCuts (2^48) 9756213249 10 Manual.Count131072.C074404.packed 64 cuts74404 = true := by
 decide +kernel
def cuts74405 : List PrefixCut := [⟨64,163898298,163898401⟩]
theorem checked74405 : checkPrefixCuts (2^48) 9756344321 10 Manual.Count131072.C074405.packed 64 cuts74405 = true := by
 decide +kernel
def cuts74406 : List PrefixCut := [⟨5,13242171,13242178⟩,
⟨64,162886345,162886442⟩]
theorem checked74406 : checkPrefixCuts (2^48) 9756475393 10 Manual.Count131072.C074406.packed 64 cuts74406 = true := by
 decide +kernel
def pointBounds74406 : List (Nat × Nat × Nat) := [(9756485632,116561487022902,116561876971965)]
theorem point_links_checked74406 : (cuts74406.take 1).map (fun c => (9756475393-1+2*2^10*c.k,116561473780731+c.lower,116561863729787+c.upper)) = pointBounds74406 := by
 decide +kernel
def cuts74407 : List PrefixCut := [⟨64,163432289,163432387⟩]
theorem checked74407 : checkPrefixCuts (2^48) 9756606465 10 Manual.Count131072.C074407.packed 64 cuts74407 = true := by
 decide +kernel
def cuts74408 : List PrefixCut := [⟨26,67709085,67709126⟩,
⟨64,165853427,165853523⟩]
theorem checked74408 : checkPrefixCuts (2^48) 9756737537 10 Manual.Count131072.C074408.packed 64 cuts74408 = true := by
 decide +kernel
def pointBounds74408 : List (Nat × Nat × Nat) := [(9756790784,116561867808450,116562257757742)]
theorem point_links_checked74408 : (cuts74408.take 1).map (fun c => (9756737537-1+2*2^10*c.k,116561800099365+c.lower,116562190048616+c.upper)) = pointBounds74408 := by
 decide +kernel
def cuts74409 : List PrefixCut := [⟨64,166139680,166139777⟩]
theorem checked74409 : checkPrefixCuts (2^48) 9756868609 10 Manual.Count131072.C074409.packed 64 cuts74409 = true := by
 decide +kernel
def cuts74410 : List PrefixCut := [⟨47,118364849,118364919⟩,
⟨64,161348626,161348722⟩]
theorem checked74410 : checkPrefixCuts (2^48) 9756999681 10 Manual.Count131072.C074410.packed 64 cuts74410 = true := by
 decide +kernel
def pointBounds74410 : List (Nat × Nat × Nat) := [(9757095936,116562250457321,116562640406835)]
theorem point_links_checked74410 : (cuts74410.take 1).map (fun c => (9756999681-1+2*2^10*c.k,116562132092472+c.lower,116562522041916+c.upper)) = pointBounds74410 := by
 decide +kernel
def cuts74411 : List PrefixCut := [⟨64,163942763,163942858⟩]
theorem checked74411 : checkPrefixCuts (2^48) 9757130753 10 Manual.Count131072.C074411.packed 64 cuts74411 = true := by
 decide +kernel
def cuts74412 : List PrefixCut := [⟨64,163738642,163738736⟩]
theorem checked74412 : checkPrefixCuts (2^48) 9757261825 10 Manual.Count131072.C074412.packed 64 cuts74412 = true := by
 decide +kernel
def cuts74413 : List PrefixCut := [⟨4,10096567,10096573⟩,
⟨64,164688387,164688489⟩]
theorem checked74413 : checkPrefixCuts (2^48) 9757392897 10 Manual.Count131072.C074413.packed 64 cuts74413 = true := by
 decide +kernel
def pointBounds74413 : List (Nat × Nat × Nat) := [(9757401088,116562631219070,116563021168805)]
theorem point_links_checked74413 : (cuts74413.take 1).map (fun c => (9757392897-1+2*2^10*c.k,116562621122503+c.lower,116563011072232+c.upper)) = pointBounds74413 := by
 decide +kernel
def cuts74414 : List PrefixCut := [⟨64,165782357,165782459⟩]
theorem checked74414 : checkPrefixCuts (2^48) 9757523969 10 Manual.Count131072.C074414.packed 64 cuts74414 = true := by
 decide +kernel
def cuts74415 : List PrefixCut := [⟨25,64443074,64443110⟩,
⟨64,164424358,164424451⟩]
theorem checked74415 : checkPrefixCuts (2^48) 9757655041 10 Manual.Count131072.C074415.packed 64 cuts74415 = true := by
 decide +kernel
def pointBounds74415 : List (Nat × Nat × Nat) := [(9757706240,116563016036321,116563405986290)]
theorem point_links_checked74415 : (cuts74415.take 1).map (fun c => (9757655041-1+2*2^10*c.k,116562951593247+c.lower,116563341543180+c.upper)) = pointBounds74415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000137
