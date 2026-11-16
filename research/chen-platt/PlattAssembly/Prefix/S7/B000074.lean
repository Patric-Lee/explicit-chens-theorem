import PlattAssemblyKernel
import PlattCertificates.Count131072.C062368
import PlattCertificates.Count131072.C062369
import PlattCertificates.Count131072.C062370
import PlattCertificates.Count131072.C062371
import PlattCertificates.Count131072.C062372
import PlattCertificates.Count131072.C062373
import PlattCertificates.Count131072.C062374
import PlattCertificates.Count131072.C062375
import PlattCertificates.Count131072.C062376
import PlattCertificates.Count131072.C062377
import PlattCertificates.Count131072.C062378
import PlattCertificates.Count131072.C062379
import PlattCertificates.Count131072.C062380
import PlattCertificates.Count131072.C062381
import PlattCertificates.Count131072.C062382
import PlattCertificates.Count131072.C062383
import PlattCertificates.Count131072.C062384
import PlattCertificates.Count131072.C062385
import PlattCertificates.Count131072.C062386
import PlattCertificates.Count131072.C062387
import PlattCertificates.Count131072.C062388
import PlattCertificates.Count131072.C062389
import PlattCertificates.Count131072.C062390
import PlattCertificates.Count131072.C062391
import PlattCertificates.Count131072.C062392
import PlattCertificates.Count131072.C062393
import PlattCertificates.Count131072.C062394
import PlattCertificates.Count131072.C062395
import PlattCertificates.Count131072.C062396
import PlattCertificates.Count131072.C062397
import PlattCertificates.Count131072.C062398
import PlattCertificates.Count131072.C062399
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000074
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62368 : List PrefixCut := [⟨64,195652785,195652896⟩]
theorem checked62368 : checkPrefixCuts (2^48) 8178630657 10 Manual.Count131072.C062368.packed 64 cuts62368 = true := by
 decide +kernel
def cuts62369 : List PrefixCut := [⟨4,12458347,12458355⟩,
⟨64,199710634,199710747⟩]
theorem checked62369 : checkPrefixCuts (2^48) 8178761729 10 Manual.Count131072.C062369.packed 64 cuts62369 = true := by
 decide +kernel
def pointBounds62369 : List (Nat × Nat × Nat) := [(8178769920,114394525653196,114394914333997)]
theorem point_links_checked62369 : (cuts62369.take 1).map (fun c => (8178761729-1+2*2^10*c.k,114394513194849+c.lower,114394901875642+c.upper)) = pointBounds62369 := by
 decide +kernel
def cuts62370 : List PrefixCut := [⟨64,194992646,194992760⟩]
theorem checked62370 : checkPrefixCuts (2^48) 8178892801 10 Manual.Count131072.C062370.packed 64 cuts62370 = true := by
 decide +kernel
def cuts62371 : List PrefixCut := [⟨1,3269352,3269354⟩,
⟨64,196813461,196813569⟩]
theorem checked62371 : checkPrefixCuts (2^48) 8179023873 10 Manual.Count131072.C062371.packed 64 cuts62371 = true := by
 decide +kernel
def pointBounds62371 : List (Nat × Nat × Nat) := [(8179025920,114394911167481,114395299848503)]
theorem point_links_checked62371 : (cuts62371.take 1).map (fun c => (8179023873-1+2*2^10*c.k,114394907898129+c.lower,114395296579149+c.upper)) = pointBounds62371 := by
 decide +kernel
def cuts62372 : List PrefixCut := [⟨62,190753589,190753695⟩,
⟨64,197808284,197808394⟩]
theorem checked62372 : checkPrefixCuts (2^48) 8179154945 10 Manual.Count131072.C062372.packed 64 cuts62372 = true := by
 decide +kernel
def pointBounds62372 : List (Nat × Nat × Nat) := [(8179281920,114395295465179,114395684146413)]
theorem point_links_checked62372 : (cuts62372.take 1).map (fun c => (8179154945-1+2*2^10*c.k,114395104711590+c.lower,114395493392718+c.upper)) = pointBounds62372 := by
 decide +kernel
def cuts62373 : List PrefixCut := [⟨64,197220105,197220216⟩]
theorem checked62373 : checkPrefixCuts (2^48) 8179286017 10 Manual.Count131072.C062373.packed 64 cuts62373 = true := by
 decide +kernel
def cuts62374 : List PrefixCut := [⟨59,182419766,182419875⟩,
⟨64,198008428,198008544⟩]
theorem checked62374 : checkPrefixCuts (2^48) 8179417089 10 Manual.Count131072.C062374.packed 64 cuts62374 = true := by
 decide +kernel
def pointBounds62374 : List (Nat × Nat × Nat) := [(8179537920,114395682159745,114396070841203)]
theorem point_links_checked62374 : (cuts62374.take 1).map (fun c => (8179417089-1+2*2^10*c.k,114395499739979+c.lower,114395888421328+c.upper)) = pointBounds62374 := by
 decide +kernel
def cuts62375 : List PrefixCut := [⟨64,200895856,200895968⟩]
theorem checked62375 : checkPrefixCuts (2^48) 8179548161 10 Manual.Count131072.C062375.packed 64 cuts62375 = true := by
 decide +kernel
def cuts62376 : List PrefixCut := [⟨56,170507684,170507783⟩,
⟨64,194423305,194423419⟩]
theorem checked62376 : checkPrefixCuts (2^48) 8179679233 10 Manual.Count131072.C062376.packed 64 cuts62376 = true := by
 decide +kernel
def pointBounds62376 : List (Nat × Nat × Nat) := [(8179793920,114396069151947,114396457833623)]
theorem point_links_checked62376 : (cuts62376.take 1).map (fun c => (8179679233-1+2*2^10*c.k,114395898644263+c.lower,114396287325840+c.upper)) = pointBounds62376 := by
 decide +kernel
def cuts62377 : List PrefixCut := [⟨64,199650627,199650736⟩]
theorem checked62377 : checkPrefixCuts (2^48) 8179810305 10 Manual.Count131072.C062377.packed 64 cuts62377 = true := by
 decide +kernel
def cuts62378 : List PrefixCut := [⟨53,165340770,165340867⟩,
⟨64,198546300,198546418⟩]
theorem checked62378 : checkPrefixCuts (2^48) 8179941377 10 Manual.Count131072.C062378.packed 64 cuts62378 = true := by
 decide +kernel
def pointBounds62378 : List (Nat × Nat × Nat) := [(8180049920,114396458058965,114396846740862)]
theorem point_links_checked62378 : (cuts62378.take 1).map (fun c => (8179941377-1+2*2^10*c.k,114396292718195+c.lower,114396681399995+c.upper)) = pointBounds62378 := by
 decide +kernel
def cuts62379 : List PrefixCut := [⟨64,201158250,201158356⟩]
theorem checked62379 : checkPrefixCuts (2^48) 8180072449 10 Manual.Count131072.C062379.packed 64 cuts62379 = true := by
 decide +kernel
def cuts62380 : List PrefixCut := [⟨50,156113914,156114005⟩,
⟨64,200019524,200019641⟩]
theorem checked62380 : checkPrefixCuts (2^48) 8180203521 10 Manual.Count131072.C062380.packed 64 cuts62380 = true := by
 decide +kernel
def pointBounds62380 : List (Nat × Nat × Nat) := [(8180305920,114396848536659,114397237218774)]
theorem point_links_checked62380 : (cuts62380.take 1).map (fun c => (8180203521-1+2*2^10*c.k,114396692422745+c.lower,114397081104769+c.upper)) = pointBounds62380 := by
 decide +kernel
def cuts62381 : List PrefixCut := [⟨64,197229241,197229355⟩]
theorem checked62381 : checkPrefixCuts (2^48) 8180334593 10 Manual.Count131072.C062381.packed 64 cuts62381 = true := by
 decide +kernel
def cuts62382 : List PrefixCut := [⟨47,141692035,141692122⟩,
⟨64,193682066,193682184⟩]
theorem checked62382 : checkPrefixCuts (2^48) 8180465665 10 Manual.Count131072.C062382.packed 64 cuts62382 = true := by
 decide +kernel
def pointBounds62382 : List (Nat × Nat × Nat) := [(8180561920,114397231363545,114397620045887)]
theorem point_links_checked62382 : (cuts62382.take 1).map (fun c => (8180465665-1+2*2^10*c.k,114397089671510+c.lower,114397478353765+c.upper)) = pointBounds62382 := by
 decide +kernel
def cuts62383 : List PrefixCut := [⟨64,197326145,197326261⟩]
theorem checked62383 : checkPrefixCuts (2^48) 8180596737 10 Manual.Count131072.C062383.packed 64 cuts62383 = true := by
 decide +kernel
def cuts62384 : List PrefixCut := [⟨44,136148041,136148118⟩,
⟨64,198905694,198905808⟩]
theorem checked62384 : checkPrefixCuts (2^48) 8180727809 10 Manual.Count131072.C062384.packed 64 cuts62384 = true := by
 decide +kernel
def pointBounds62384 : List (Nat × Nat × Nat) := [(8180817920,114397616827762,114398005510328)]
theorem point_links_checked62384 : (cuts62384.take 1).map (fun c => (8180727809-1+2*2^10*c.k,114397480679721+c.lower,114397869362210+c.upper)) = pointBounds62384 := by
 decide +kernel
def cuts62385 : List PrefixCut := [⟨64,197251007,197251119⟩]
theorem checked62385 : checkPrefixCuts (2^48) 8180858881 10 Manual.Count131072.C062385.packed 64 cuts62385 = true := by
 decide +kernel
def cuts62386 : List PrefixCut := [⟨41,126269257,126269332⟩,
⟨64,198383223,198383340⟩]
theorem checked62386 : checkPrefixCuts (2^48) 8180989953 10 Manual.Count131072.C062386.packed 64 cuts62386 = true := by
 decide +kernel
def pointBounds62386 : List (Nat × Nat × Nat) := [(8181073920,114398003105679,114398391788469)]
theorem point_links_checked62386 : (cuts62386.take 1).map (fun c => (8180989953-1+2*2^10*c.k,114397876836422+c.lower,114398265519137+c.upper)) = pointBounds62386 := by
 decide +kernel
def cuts62387 : List PrefixCut := [⟨64,196212518,196212630⟩]
theorem checked62387 : checkPrefixCuts (2^48) 8181121025 10 Manual.Count131072.C062387.packed 64 cuts62387 = true := by
 decide +kernel
def cuts62388 : List PrefixCut := [⟨38,118317784,118317847⟩,
⟨64,197792009,197792120⟩]
theorem checked62388 : checkPrefixCuts (2^48) 8181252097 10 Manual.Count131072.C062388.packed 64 cuts62388 = true := by
 decide +kernel
def pointBounds62388 : List (Nat × Nat × Nat) := [(8181329920,114398389749947,114398778432954)]
theorem point_links_checked62388 : (cuts62388.take 1).map (fun c => (8181252097-1+2*2^10*c.k,114398271432163+c.lower,114398660115107+c.upper)) = pointBounds62388 := by
 decide +kernel
def cuts62389 : List PrefixCut := [⟨64,199096187,199096304⟩]
theorem checked62389 : checkPrefixCuts (2^48) 8181383169 10 Manual.Count131072.C062389.packed 64 cuts62389 = true := by
 decide +kernel
def cuts62390 : List PrefixCut := [⟨35,107752119,107752178⟩,
⟨64,196650346,196650456⟩]
theorem checked62390 : checkPrefixCuts (2^48) 8181514241 10 Manual.Count131072.C062390.packed 64 cuts62390 = true := by
 decide +kernel
def pointBounds62390 : List (Nat × Nat × Nat) := [(8181585920,114398776072478,114399164755709)]
theorem point_links_checked62390 : (cuts62390.take 1).map (fun c => (8181514241-1+2*2^10*c.k,114398668320359+c.lower,114399057003531+c.upper)) = pointBounds62390 := by
 decide +kernel
def cuts62391 : List PrefixCut := [⟨64,196027947,196028058⟩]
theorem checked62391 : checkPrefixCuts (2^48) 8181645313 10 Manual.Count131072.C062391.packed 64 cuts62391 = true := by
 decide +kernel
def cuts62392 : List PrefixCut := [⟨32,98391222,98391281⟩,
⟨64,196953662,196953780⟩]
theorem checked62392 : checkPrefixCuts (2^48) 8181776385 10 Manual.Count131072.C062392.packed 64 cuts62392 = true := by
 decide +kernel
def pointBounds62392 : List (Nat × Nat × Nat) := [(8181841920,114399159389874,114399548073326)]
theorem point_links_checked62392 : (cuts62392.take 1).map (fun c => (8181776385-1+2*2^10*c.k,114399060998652+c.lower,114399449682045+c.upper)) = pointBounds62392 := by
 decide +kernel
def cuts62393 : List PrefixCut := [⟨64,198877033,198877145⟩]
theorem checked62393 : checkPrefixCuts (2^48) 8181907457 10 Manual.Count131072.C062393.packed 64 cuts62393 = true := by
 decide +kernel
def cuts62394 : List PrefixCut := [⟨29,89994157,89994207⟩,
⟨64,199045838,199045951⟩]
theorem checked62394 : checkPrefixCuts (2^48) 8182038529 10 Manual.Count131072.C062394.packed 64 cuts62394 = true := by
 decide +kernel
def pointBounds62394 : List (Nat × Nat × Nat) := [(8182097920,114399546823504,114399935507177)]
theorem point_links_checked62394 : (cuts62394.take 1).map (fun c => (8182038529-1+2*2^10*c.k,114399456829347+c.lower,114399845512970+c.upper)) = pointBounds62394 := by
 decide +kernel
def cuts62395 : List PrefixCut := [⟨64,199489862,199489978⟩]
theorem checked62395 : checkPrefixCuts (2^48) 8182169601 10 Manual.Count131072.C062395.packed 64 cuts62395 = true := by
 decide +kernel
def cuts62396 : List PrefixCut := [⟨26,81425622,81425670⟩,
⟨64,196459456,196459575⟩]
theorem checked62396 : checkPrefixCuts (2^48) 8182300673 10 Manual.Count131072.C062396.packed 64 cuts62396 = true := by
 decide +kernel
def pointBounds62396 : List (Nat × Nat × Nat) := [(8182353920,114399936790669,114400325474569)]
theorem point_links_checked62396 : (cuts62396.take 1).map (fun c => (8182300673-1+2*2^10*c.k,114399855365047+c.lower,114400244048899+c.upper)) = pointBounds62396 := by
 decide +kernel
def cuts62397 : List PrefixCut := [⟨64,198589071,198589186⟩]
theorem checked62397 : checkPrefixCuts (2^48) 8182431745 10 Manual.Count131072.C062397.packed 64 cuts62397 = true := by
 decide +kernel
def cuts62398 : List PrefixCut := [⟨23,72100843,72100887⟩,
⟨64,199067481,199067601⟩]
theorem checked62398 : checkPrefixCuts (2^48) 8182562817 10 Manual.Count131072.C062398.packed 64 cuts62398 = true := by
 decide +kernel
def pointBounds62398 : List (Nat × Nat × Nat) := [(8182609920,114400322514417,114400711198547)]
theorem point_links_checked62398 : (cuts62398.take 1).map (fun c => (8182562817-1+2*2^10*c.k,114400250413574+c.lower,114400639097660+c.upper)) = pointBounds62398 := by
 decide +kernel
def cuts62399 : List PrefixCut := [⟨64,196690798,196690912⟩]
theorem checked62399 : checkPrefixCuts (2^48) 8182693889 10 Manual.Count131072.C062399.packed 64 cuts62399 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000074
