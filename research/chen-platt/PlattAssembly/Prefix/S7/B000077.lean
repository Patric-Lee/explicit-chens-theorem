import PlattAssemblyKernel
import PlattCertificates.Count131072.C062464
import PlattCertificates.Count131072.C062465
import PlattCertificates.Count131072.C062466
import PlattCertificates.Count131072.C062467
import PlattCertificates.Count131072.C062468
import PlattCertificates.Count131072.C062469
import PlattCertificates.Count131072.C062470
import PlattCertificates.Count131072.C062471
import PlattCertificates.Count131072.C062472
import PlattCertificates.Count131072.C062473
import PlattCertificates.Count131072.C062474
import PlattCertificates.Count131072.C062475
import PlattCertificates.Count131072.C062476
import PlattCertificates.Count131072.C062477
import PlattCertificates.Count131072.C062478
import PlattCertificates.Count131072.C062479
import PlattCertificates.Count131072.C062480
import PlattCertificates.Count131072.C062481
import PlattCertificates.Count131072.C062482
import PlattCertificates.Count131072.C062483
import PlattCertificates.Count131072.C062484
import PlattCertificates.Count131072.C062485
import PlattCertificates.Count131072.C062486
import PlattCertificates.Count131072.C062487
import PlattCertificates.Count131072.C062488
import PlattCertificates.Count131072.C062489
import PlattCertificates.Count131072.C062490
import PlattCertificates.Count131072.C062491
import PlattCertificates.Count131072.C062492
import PlattCertificates.Count131072.C062493
import PlattCertificates.Count131072.C062494
import PlattCertificates.Count131072.C062495
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62464 : List PrefixCut := [⟨49,153636155,153636244⟩,
⟨64,199166522,199166637⟩]
theorem checked62464 : checkPrefixCuts (2^48) 8191213569 10 Manual.Count131072.C062464.packed 64 cuts62464 = true := by
 decide +kernel
def pointBounds62464 : List (Nat × Nat × Nat) := [(8191313920,114413430186692,114413818878341)]
theorem point_links_checked62464 : (cuts62464.take 1).map (fun c => (8191213569-1+2*2^10*c.k,114413276550537+c.lower,114413665242097+c.upper)) = pointBounds62464 := by
 decide +kernel
def cuts62465 : List PrefixCut := [⟨64,195280387,195280497⟩]
theorem checked62465 : checkPrefixCuts (2^48) 8191344641 10 Manual.Count131072.C062465.packed 64 cuts62465 = true := by
 decide +kernel
def cuts62466 : List PrefixCut := [⟨46,144456717,144456800⟩,
⟨64,199881745,199881858⟩]
theorem checked62466 : checkPrefixCuts (2^48) 8191475713 10 Manual.Count131072.C062466.packed 64 cuts62466 = true := by
 decide +kernel
def pointBounds62466 : List (Nat × Nat × Nat) := [(8191569920,114413815454163,114414204146031)]
theorem point_links_checked62466 : (cuts62466.take 1).map (fun c => (8191475713-1+2*2^10*c.k,114413670997446+c.lower,114414059689231+c.upper)) = pointBounds62466 := by
 decide +kernel
def cuts62467 : List PrefixCut := [⟨64,196098818,196098928⟩]
theorem checked62467 : checkPrefixCuts (2^48) 8191606785 10 Manual.Count131072.C062467.packed 64 cuts62467 = true := by
 decide +kernel
def cuts62468 : List PrefixCut := [⟨43,135827618,135827700⟩,
⟨64,200940516,200940633⟩]
theorem checked62468 : checkPrefixCuts (2^48) 8191737857 10 Manual.Count131072.C062468.packed 64 cuts62468 = true := by
 decide +kernel
def pointBounds62468 : List (Nat × Nat × Nat) := [(8191825920,114414202805627,114414591497717)]
theorem point_links_checked62468 : (cuts62468.take 1).map (fun c => (8191737857-1+2*2^10*c.k,114414066978009+c.lower,114414455670017+c.upper)) = pointBounds62468 := by
 decide +kernel
def cuts62469 : List PrefixCut := [⟨64,197054627,197054733⟩]
theorem checked62469 : checkPrefixCuts (2^48) 8191868929 10 Manual.Count131072.C062469.packed 64 cuts62469 = true := by
 decide +kernel
def cuts62470 : List PrefixCut := [⟨40,121392306,121392376⟩,
⟨64,194233980,194234095⟩]
theorem checked62470 : checkPrefixCuts (2^48) 8192000001 10 Manual.Count131072.C062470.packed 64 cuts62470 = true := by
 decide +kernel
def pointBounds62470 : List (Nat × Nat × Nat) := [(8192081920,114414586365458,114414975057759)]
theorem point_links_checked62470 : (cuts62470.take 1).map (fun c => (8192000001-1+2*2^10*c.k,114414464973152+c.lower,114414853665383+c.upper)) = pointBounds62470 := by
 decide +kernel
def cuts62471 : List PrefixCut := [⟨64,194952411,194952531⟩]
theorem checked62471 : checkPrefixCuts (2^48) 8192131073 10 Manual.Count131072.C062471.packed 64 cuts62471 = true := by
 decide +kernel
def cuts62472 : List PrefixCut := [⟨38,116406482,116406550⟩,
⟨64,198075902,198076016⟩]
theorem checked62472 : checkPrefixCuts (2^48) 8192262145 10 Manual.Count131072.C062472.packed 64 cuts62472 = true := by
 decide +kernel
def pointBounds62472 : List (Nat × Nat × Nat) := [(8192339968,114414970566025,114415359258559)]
theorem point_links_checked62472 : (cuts62472.take 1).map (fun c => (8192262145-1+2*2^10*c.k,114414854159543+c.lower,114415242852009+c.upper)) = pointBounds62472 := by
 decide +kernel
def cuts62473 : List PrefixCut := [⟨64,195495900,195496013⟩]
theorem checked62473 : checkPrefixCuts (2^48) 8192393217 10 Manual.Count131072.C062473.packed 64 cuts62473 = true := by
 decide +kernel
def cuts62474 : List PrefixCut := [⟨36,112211191,112211255⟩,
⟨64,198791085,198791199⟩]
theorem checked62474 : checkPrefixCuts (2^48) 8192524289 10 Manual.Count131072.C062474.packed 64 cuts62474 = true := by
 decide +kernel
def pointBounds62474 : List (Nat × Nat × Nat) := [(8192598016,114415359942536,114415748635293)]
theorem point_links_checked62474 : (cuts62474.take 1).map (fun c => (8192524289-1+2*2^10*c.k,114415247731345+c.lower,114415636424038+c.upper)) = pointBounds62474 := by
 decide +kernel
def cuts62475 : List PrefixCut := [⟨64,199990389,199990506⟩]
theorem checked62475 : checkPrefixCuts (2^48) 8192655361 10 Manual.Count131072.C062475.packed 64 cuts62475 = true := by
 decide +kernel
def cuts62476 : List PrefixCut := [⟨34,103103211,103103273⟩,
⟨64,197307388,197307502⟩]
theorem checked62476 : checkPrefixCuts (2^48) 8192786433 10 Manual.Count131072.C062476.packed 64 cuts62476 = true := by
 decide +kernel
def pointBounds62476 : List (Nat × Nat × Nat) := [(8192856064,114415749616030,114416138309016)]
theorem point_links_checked62476 : (cuts62476.take 1).map (fun c => (8192786433-1+2*2^10*c.k,114415646512819+c.lower,114416035205743+c.upper)) = pointBounds62476 := by
 decide +kernel
def cuts62477 : List PrefixCut := [⟨64,197956986,197957101⟩]
theorem checked62477 : checkPrefixCuts (2^48) 8192917505 10 Manual.Count131072.C062477.packed 64 cuts62477 = true := by
 decide +kernel
def cuts62478 : List PrefixCut := [⟨32,99733126,99733182⟩,
⟨64,198503515,198503629⟩]
theorem checked62478 : checkPrefixCuts (2^48) 8193048577 10 Manual.Count131072.C062478.packed 64 cuts62478 = true := by
 decide +kernel
def pointBounds62478 : List (Nat × Nat × Nat) := [(8193114112,114416141510319,114416530203528)]
theorem point_links_checked62478 : (cuts62478.take 1).map (fun c => (8193048577-1+2*2^10*c.k,114416041777193+c.lower,114416430470346+c.upper)) = pointBounds62478 := by
 decide +kernel
def cuts62479 : List PrefixCut := [⟨64,197057453,197057563⟩]
theorem checked62479 : checkPrefixCuts (2^48) 8193179649 10 Manual.Count131072.C062479.packed 64 cuts62479 = true := by
 decide +kernel
def cuts62480 : List PrefixCut := [⟨30,91862871,91862923⟩,
⟨64,195817557,195817666⟩]
theorem checked62480 : checkPrefixCuts (2^48) 8193310721 10 Manual.Count131072.C062480.packed 64 cuts62480 = true := by
 decide +kernel
def pointBounds62480 : List (Nat × Nat × Nat) := [(8193372160,114416529201032,114416917894461)]
theorem point_links_checked62480 : (cuts62480.take 1).map (fun c => (8193310721-1+2*2^10*c.k,114416437338161+c.lower,114416826031538+c.upper)) = pointBounds62480 := by
 decide +kernel
def cuts62481 : List PrefixCut := [⟨64,198734479,198734594⟩]
theorem checked62481 : checkPrefixCuts (2^48) 8193441793 10 Manual.Count131072.C062481.packed 64 cuts62481 = true := by
 decide +kernel
def cuts62482 : List PrefixCut := [⟨28,87119245,87119293⟩,
⟨64,198319063,198319174⟩]
theorem checked62482 : checkPrefixCuts (2^48) 8193572865 10 Manual.Count131072.C062482.packed 64 cuts62482 = true := by
 decide +kernel
def pointBounds62482 : List (Nat × Nat × Nat) := [(8193630208,114416919009442,114417307703091)]
theorem point_links_checked62482 : (cuts62482.take 1).map (fun c => (8193572865-1+2*2^10*c.k,114416831890197+c.lower,114417220583798+c.upper)) = pointBounds62482 := by
 decide +kernel
def cuts62483 : List PrefixCut := [⟨64,199071641,199071752⟩]
theorem checked62483 : checkPrefixCuts (2^48) 8193703937 10 Manual.Count131072.C062483.packed 64 cuts62483 = true := by
 decide +kernel
def cuts62484 : List PrefixCut := [⟨26,80005632,80005677⟩,
⟨64,197728723,197728837⟩]
theorem checked62484 : checkPrefixCuts (2^48) 8193835009 10 Manual.Count131072.C062484.packed 64 cuts62484 = true := by
 decide +kernel
def pointBounds62484 : List (Nat × Nat × Nat) := [(8193888256,114417309286533,114417697980401)]
theorem point_links_checked62484 : (cuts62484.take 1).map (fun c => (8193835009-1+2*2^10*c.k,114417229280901+c.lower,114417617974724+c.upper)) = pointBounds62484 := by
 decide +kernel
def cuts62485 : List PrefixCut := [⟨64,196763729,196763844⟩]
theorem checked62485 : checkPrefixCuts (2^48) 8193966081 10 Manual.Count131072.C062485.packed 64 cuts62485 = true := by
 decide +kernel
def cuts62486 : List PrefixCut := [⟨24,74644363,74644403⟩,
⟨64,196520144,196520254⟩]
theorem checked62486 : checkPrefixCuts (2^48) 8194097153 10 Manual.Count131072.C062486.packed 64 cuts62486 = true := by
 decide +kernel
def pointBounds62486 : List (Nat × Nat × Nat) := [(8194146304,114417698417716,114418087111808)]
theorem point_links_checked62486 : (cuts62486.take 1).map (fun c => (8194097153-1+2*2^10*c.k,114417623773353+c.lower,114418012467405+c.upper)) = pointBounds62486 := by
 decide +kernel
def cuts62487 : List PrefixCut := [⟨64,196791795,196791909⟩]
theorem checked62487 : checkPrefixCuts (2^48) 8194228225 10 Manual.Count131072.C062487.packed 64 cuts62487 = true := by
 decide +kernel
def cuts62488 : List PrefixCut := [⟨22,68081189,68081226⟩,
⟨64,198093918,198094033⟩]
theorem checked62488 : checkPrefixCuts (2^48) 8194359297 10 Manual.Count131072.C062488.packed 64 cuts62488 = true := by
 decide +kernel
def pointBounds62488 : List (Nat × Nat × Nat) := [(8194404352,114418085166481,114418473860794)]
theorem point_links_checked62488 : (cuts62488.take 1).map (fun c => (8194359297-1+2*2^10*c.k,114418017085292+c.lower,114418405779568+c.upper)) = pointBounds62488 := by
 decide +kernel
def cuts62489 : List PrefixCut := [⟨64,196545050,196545162⟩]
theorem checked62489 : checkPrefixCuts (2^48) 8194490369 10 Manual.Count131072.C062489.packed 64 cuts62489 = true := by
 decide +kernel
def cuts62490 : List PrefixCut := [⟨20,62274109,62274145⟩,
⟨64,199633262,199633375⟩]
theorem checked62490 : checkPrefixCuts (2^48) 8194621441 10 Manual.Count131072.C062490.packed 64 cuts62490 = true := by
 decide +kernel
def pointBounds62490 : List (Nat × Nat × Nat) := [(8194662400,114418473998369,114418862692908)]
theorem point_links_checked62490 : (cuts62490.take 1).map (fun c => (8194621441-1+2*2^10*c.k,114418411724260+c.lower,114418800418763+c.upper)) = pointBounds62490 := by
 decide +kernel
def cuts62491 : List PrefixCut := [⟨64,197260066,197260184⟩]
theorem checked62491 : checkPrefixCuts (2^48) 8194752513 10 Manual.Count131072.C062491.packed 64 cuts62491 = true := by
 decide +kernel
def cuts62492 : List PrefixCut := [⟨18,54543927,54543962⟩,
⟨64,197462986,197463104⟩]
theorem checked62492 : checkPrefixCuts (2^48) 8194883585 10 Manual.Count131072.C062492.packed 64 cuts62492 = true := by
 decide +kernel
def pointBounds62492 : List (Nat × Nat × Nat) := [(8194920448,114418863161515,114419251856284)]
theorem point_links_checked62492 : (cuts62492.take 1).map (fun c => (8194883585-1+2*2^10*c.k,114418808617588+c.lower,114419197312322+c.upper)) = pointBounds62492 := by
 decide +kernel
def cuts62493 : List PrefixCut := [⟨64,198249816,198249926⟩]
theorem checked62493 : checkPrefixCuts (2^48) 8195014657 10 Manual.Count131072.C062493.packed 64 cuts62493 = true := by
 decide +kernel
def cuts62494 : List PrefixCut := [⟨16,49836727,49836759⟩,
⟨64,198246619,198246739⟩]
theorem checked62494 : checkPrefixCuts (2^48) 8195145729 10 Manual.Count131072.C062494.packed 64 cuts62494 = true := by
 decide +kernel
def pointBounds62494 : List (Nat × Nat × Nat) := [(8195178496,114419254167117,114419642862111)]
theorem point_links_checked62494 : (cuts62494.take 1).map (fun c => (8195145729-1+2*2^10*c.k,114419204330390+c.lower,114419593025352+c.upper)) = pointBounds62494 := by
 decide +kernel
def cuts62495 : List PrefixCut := [⟨64,197247435,197247549⟩]
theorem checked62495 : checkPrefixCuts (2^48) 8195276801 10 Manual.Count131072.C062495.packed 64 cuts62495 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000077
