import PlattAssemblyKernel
import PlattCertificates.Count131072.C062400
import PlattCertificates.Count131072.C062401
import PlattCertificates.Count131072.C062402
import PlattCertificates.Count131072.C062403
import PlattCertificates.Count131072.C062404
import PlattCertificates.Count131072.C062405
import PlattCertificates.Count131072.C062406
import PlattCertificates.Count131072.C062407
import PlattCertificates.Count131072.C062408
import PlattCertificates.Count131072.C062409
import PlattCertificates.Count131072.C062410
import PlattCertificates.Count131072.C062411
import PlattCertificates.Count131072.C062412
import PlattCertificates.Count131072.C062413
import PlattCertificates.Count131072.C062414
import PlattCertificates.Count131072.C062415
import PlattCertificates.Count131072.C062416
import PlattCertificates.Count131072.C062417
import PlattCertificates.Count131072.C062418
import PlattCertificates.Count131072.C062419
import PlattCertificates.Count131072.C062420
import PlattCertificates.Count131072.C062421
import PlattCertificates.Count131072.C062422
import PlattCertificates.Count131072.C062423
import PlattCertificates.Count131072.C062424
import PlattCertificates.Count131072.C062425
import PlattCertificates.Count131072.C062426
import PlattCertificates.Count131072.C062427
import PlattCertificates.Count131072.C062428
import PlattCertificates.Count131072.C062429
import PlattCertificates.Count131072.C062430
import PlattCertificates.Count131072.C062431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62400 : List PrefixCut := [⟨20,60506377,60506415⟩,
⟨64,194967747,194967866⟩]
theorem checked62400 : checkPrefixCuts (2^48) 8182824961 10 Manual.Count131072.C062400.packed 64 cuts62400 = true := by
 decide +kernel
def pointBounds62400 : List (Nat × Nat × Nat) := [(8182865920,114400706678230,114401095362588)]
theorem point_links_checked62400 : (cuts62400.take 1).map (fun c => (8182824961-1+2*2^10*c.k,114400646171853+c.lower,114401034856173+c.upper)) = pointBounds62400 := by
 decide +kernel
def cuts62401 : List PrefixCut := [⟨64,197716431,197716542⟩]
theorem checked62401 : checkPrefixCuts (2^48) 8182956033 10 Manual.Count131072.C062401.packed 64 cuts62401 = true := by
 decide +kernel
def cuts62402 : List PrefixCut := [⟨17,51698809,51698840⟩,
⟨64,195236665,195236782⟩]
theorem checked62402 : checkPrefixCuts (2^48) 8183087105 10 Manual.Count131072.C062402.packed 64 cuts62402 = true := by
 decide +kernel
def pointBounds62402 : List (Nat × Nat × Nat) := [(8183121920,114401090554840,114401479239421)]
theorem point_links_checked62402 : (cuts62402.take 1).map (fun c => (8183087105-1+2*2^10*c.k,114401038856031+c.lower,114401427540581+c.upper)) = pointBounds62402 := by
 decide +kernel
def cuts62403 : List PrefixCut := [⟨64,200083419,200083535⟩]
theorem checked62403 : checkPrefixCuts (2^48) 8183218177 10 Manual.Count131072.C062403.packed 64 cuts62403 = true := by
 decide +kernel
def cuts62404 : List PrefixCut := [⟨14,43132572,43132597⟩,
⟨64,196984595,196984710⟩]
theorem checked62404 : checkPrefixCuts (2^48) 8183349249 10 Manual.Count131072.C062404.packed 64 cuts62404 = true := by
 decide +kernel
def pointBounds62404 : List (Nat × Nat × Nat) := [(8183377920,114401477308687,114401865993495)]
theorem point_links_checked62404 : (cuts62404.take 1).map (fun c => (8183349249-1+2*2^10*c.k,114401434176115+c.lower,114401822860898+c.upper)) = pointBounds62404 := by
 decide +kernel
def cuts62405 : List PrefixCut := [⟨64,197462980,197463092⟩]
theorem checked62405 : checkPrefixCuts (2^48) 8183480321 10 Manual.Count131072.C062405.packed 64 cuts62405 = true := by
 decide +kernel
def cuts62406 : List PrefixCut := [⟨11,34635666,34635686⟩,
⟨64,198629247,198629362⟩]
theorem checked62406 : checkPrefixCuts (2^48) 8183611393 10 Manual.Count131072.C062406.packed 64 cuts62406 = true := by
 decide +kernel
def pointBounds62406 : List (Nat × Nat × Nat) := [(8183633920,114401863259356,114402251944386)]
theorem point_links_checked62406 : (cuts62406.take 1).map (fun c => (8183611393-1+2*2^10*c.k,114401828623690+c.lower,114402217308700+c.upper)) = pointBounds62406 := by
 decide +kernel
def cuts62407 : List PrefixCut := [⟨64,194911497,194911608⟩]
theorem checked62407 : checkPrefixCuts (2^48) 8183742465 10 Manual.Count131072.C062407.packed 64 cuts62407 = true := by
 decide +kernel
def cuts62408 : List PrefixCut := [⟨8,24247638,24247652⟩,
⟨64,199895431,199895541⟩]
theorem checked62408 : checkPrefixCuts (2^48) 8183873537 10 Manual.Count131072.C062408.packed 64 cuts62408 = true := by
 decide +kernel
def pointBounds62408 : List (Nat × Nat × Nat) := [(8183889920,114402246412072,114402635097322)]
theorem point_links_checked62408 : (cuts62408.take 1).map (fun c => (8183873537-1+2*2^10*c.k,114402222164434+c.lower,114402610849670+c.upper)) = pointBounds62408 := by
 decide +kernel
def cuts62409 : List PrefixCut := [⟨64,198482111,198482226⟩]
theorem checked62409 : checkPrefixCuts (2^48) 8184004609 10 Manual.Count131072.C062409.packed 64 cuts62409 = true := by
 decide +kernel
def cuts62410 : List PrefixCut := [⟨5,14857656,14857664⟩,
⟨64,196862495,196862605⟩]
theorem checked62410 : checkPrefixCuts (2^48) 8184135681 10 Manual.Count131072.C062410.packed 64 cuts62410 = true := by
 decide +kernel
def pointBounds62410 : List (Nat × Nat × Nat) := [(8184145920,114402635399632,114403024085101)]
theorem point_links_checked62410 : (cuts62410.take 1).map (fun c => (8184135681-1+2*2^10*c.k,114402620541976+c.lower,114403009227437+c.upper)) = pointBounds62410 := by
 decide +kernel
def cuts62411 : List PrefixCut := [⟨64,194623876,194623987⟩]
theorem checked62411 : checkPrefixCuts (2^48) 8184266753 10 Manual.Count131072.C062411.packed 64 cuts62411 = true := by
 decide +kernel
def cuts62412 : List PrefixCut := [⟨2,6431236,6431240⟩,
⟨64,198713331,198713443⟩]
theorem checked62412 : checkPrefixCuts (2^48) 8184397825 10 Manual.Count131072.C062412.packed 64 cuts62412 = true := by
 decide +kernel
def pointBounds62412 : List (Nat × Nat × Nat) := [(8184401920,114403018459583,114403407145269)]
theorem point_links_checked62412 : (cuts62412.take 1).map (fun c => (8184397825-1+2*2^10*c.k,114403012028347+c.lower,114403400714029+c.upper)) = pointBounds62412 := by
 decide +kernel
def cuts62413 : List PrefixCut := [⟨63,195821330,195821441⟩,
⟨64,198710136,198710249⟩]
theorem checked62413 : checkPrefixCuts (2^48) 8184528897 10 Manual.Count131072.C062413.packed 64 cuts62413 = true := by
 decide +kernel
def pointBounds62413 : List (Nat × Nat × Nat) := [(8184657920,114403406563008,114403795248913)]
theorem point_links_checked62413 : (cuts62413.take 1).map (fun c => (8184528897-1+2*2^10*c.k,114403210741678+c.lower,114403599427472+c.upper)) = pointBounds62413 := by
 decide +kernel
def cuts62414 : List PrefixCut := [⟨64,198844505,198844619⟩]
theorem checked62414 : checkPrefixCuts (2^48) 8184659969 10 Manual.Count131072.C062414.packed 64 cuts62414 = true := by
 decide +kernel
def cuts62415 : List PrefixCut := [⟨60,185566996,185567104⟩,
⟨64,197362580,197362695⟩]
theorem checked62415 : checkPrefixCuts (2^48) 8184791041 10 Manual.Count131072.C062415.packed 64 cuts62415 = true := by
 decide +kernel
def pointBounds62415 : List (Nat × Nat × Nat) := [(8184913920,114403793863315,114404182549444)]
theorem point_links_checked62415 : (cuts62415.take 1).map (fun c => (8184791041-1+2*2^10*c.k,114403608296319+c.lower,114403996982340+c.upper)) = pointBounds62415 := by
 decide +kernel
def cuts62416 : List PrefixCut := [⟨64,195639956,195640070⟩]
theorem checked62416 : checkPrefixCuts (2^48) 8184922113 10 Manual.Count131072.C062416.packed 64 cuts62416 = true := by
 decide +kernel
def cuts62417 : List PrefixCut := [⟨57,173800206,173800302⟩,
⟨64,195774375,195774482⟩]
theorem checked62417 : checkPrefixCuts (2^48) 8185053185 10 Manual.Count131072.C062417.packed 64 cuts62417 = true := by
 decide +kernel
def pointBounds62417 : List (Nat × Nat × Nat) := [(8185169920,114404175099061,114404563785407)]
theorem point_links_checked62417 : (cuts62417.take 1).map (fun c => (8185053185-1+2*2^10*c.k,114404001298855+c.lower,114404389985105+c.upper)) = pointBounds62417 := by
 decide +kernel
def cuts62418 : List PrefixCut := [⟨64,200860684,200860795⟩]
theorem checked62418 : checkPrefixCuts (2^48) 8185184257 10 Manual.Count131072.C062418.packed 64 cuts62418 = true := by
 decide +kernel
def cuts62419 : List PrefixCut := [⟨54,166607729,166607820⟩,
⟨64,196490276,196490385⟩]
theorem checked62419 : checkPrefixCuts (2^48) 8185315329 10 Manual.Count131072.C062419.packed 64 cuts62419 = true := by
 decide +kernel
def pointBounds62419 : List (Nat × Nat × Nat) := [(8185425920,114404564541643,114404953228202)]
theorem point_links_checked62419 : (cuts62419.take 1).map (fun c => (8185315329-1+2*2^10*c.k,114404397933914+c.lower,114404786620382+c.upper)) = pointBounds62419 := by
 decide +kernel
def cuts62420 : List PrefixCut := [⟨64,202401661,202401777⟩]
theorem checked62420 : checkPrefixCuts (2^48) 8185446401 10 Manual.Count131072.C062420.packed 64 cuts62420 = true := by
 decide +kernel
def cuts62421 : List PrefixCut := [⟨51,154154553,154154633⟩,
⟨64,194076923,194077026⟩]
theorem checked62421 : checkPrefixCuts (2^48) 8185577473 10 Manual.Count131072.C062421.packed 64 cuts62421 = true := by
 decide +kernel
def pointBounds62421 : List (Nat × Nat × Nat) := [(8185681920,114404950980404,114405339667177)]
theorem point_links_checked62421 : (cuts62421.take 1).map (fun c => (8185577473-1+2*2^10*c.k,114404796825851+c.lower,114405185512544+c.upper)) = pointBounds62421 := by
 decide +kernel
def cuts62422 : List PrefixCut := [⟨64,198509582,198509696⟩]
theorem checked62422 : checkPrefixCuts (2^48) 8185708545 10 Manual.Count131072.C062422.packed 64 cuts62422 = true := by
 decide +kernel
def cuts62423 : List PrefixCut := [⟨48,147031883,147031970⟩,
⟨64,196099424,196099539⟩]
theorem checked62423 : checkPrefixCuts (2^48) 8185839617 10 Manual.Count131072.C062423.packed 64 cuts62423 = true := by
 decide +kernel
def pointBounds62423 : List (Nat × Nat × Nat) := [(8185937920,114405336444239,114405725131236)]
theorem point_links_checked62423 : (cuts62423.take 1).map (fun c => (8185839617-1+2*2^10*c.k,114405189412356+c.lower,114405578099266+c.upper)) = pointBounds62423 := by
 decide +kernel
def cuts62424 : List PrefixCut := [⟨64,198193758,198193869⟩]
theorem checked62424 : checkPrefixCuts (2^48) 8185970689 10 Manual.Count131072.C062424.packed 64 cuts62424 = true := by
 decide +kernel
def cuts62425 : List PrefixCut := [⟨45,137537171,137537245⟩,
⟨64,195508620,195508728⟩]
theorem checked62425 : checkPrefixCuts (2^48) 8186101761 10 Manual.Count131072.C062425.packed 64 cuts62425 = true := by
 decide +kernel
def pointBounds62425 : List (Nat × Nat × Nat) := [(8186193920,114405721242709,114406109929919)]
theorem point_links_checked62425 : (cuts62425.take 1).map (fun c => (8186101761-1+2*2^10*c.k,114405583705538+c.lower,114405972392674+c.upper)) = pointBounds62425 := by
 decide +kernel
def cuts62426 : List PrefixCut := [⟨64,197224671,197224782⟩]
theorem checked62426 : checkPrefixCuts (2^48) 8186232833 10 Manual.Count131072.C062426.packed 64 cuts62426 = true := by
 decide +kernel
def cuts62427 : List PrefixCut := [⟨42,128524412,128524482⟩,
⟨64,196121247,196121356⟩]
theorem checked62427 : checkPrefixCuts (2^48) 8186363905 10 Manual.Count131072.C062427.packed 64 cuts62427 = true := by
 decide +kernel
def pointBounds62427 : List (Nat × Nat × Nat) := [(8186449920,114406104963241,114406493650666)]
theorem point_links_checked62427 : (cuts62427.take 1).map (fun c => (8186363905-1+2*2^10*c.k,114405976438829+c.lower,114406365126184+c.upper)) = pointBounds62427 := by
 decide +kernel
def cuts62428 : List PrefixCut := [⟨64,198937497,198937610⟩]
theorem checked62428 : checkPrefixCuts (2^48) 8186494977 10 Manual.Count131072.C062428.packed 64 cuts62428 = true := by
 decide +kernel
def cuts62429 : List PrefixCut := [⟨39,120543700,120543765⟩,
⟨64,198762386,198762496⟩]
theorem checked62429 : checkPrefixCuts (2^48) 8186626049 10 Manual.Count131072.C062429.packed 64 cuts62429 = true := by
 decide +kernel
def pointBounds62429 : List (Nat × Nat × Nat) := [(8186705920,114406492041273,114406880728915)]
theorem point_links_checked62429 : (cuts62429.take 1).map (fun c => (8186626049-1+2*2^10*c.k,114406371497573+c.lower,114406760185150+c.upper)) = pointBounds62429 := by
 decide +kernel
def cuts62430 : List PrefixCut := [⟨64,196008686,196008798⟩]
theorem checked62430 : checkPrefixCuts (2^48) 8186757121 10 Manual.Count131072.C062430.packed 64 cuts62430 = true := by
 decide +kernel
def cuts62431 : List PrefixCut := [⟨36,111222615,111222681⟩,
⟨64,197002590,197002704⟩]
theorem checked62431 : checkPrefixCuts (2^48) 8186888193 10 Manual.Count131072.C062431.packed 64 cuts62431 = true := by
 decide +kernel
def pointBounds62431 : List (Nat × Nat × Nat) := [(8186961920,114406877491260,114407266179125)]
theorem point_links_checked62431 : (cuts62431.take 1).map (fun c => (8186888193-1+2*2^10*c.k,114406766268645+c.lower,114407154956444+c.upper)) = pointBounds62431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000075
