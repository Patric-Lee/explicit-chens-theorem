import PlattAssemblyKernel
import PlattCertificates.Count131072.C049472
import PlattCertificates.Count131072.C049473
import PlattCertificates.Count131072.C049474
import PlattCertificates.Count131072.C049475
import PlattCertificates.Count131072.C049476
import PlattCertificates.Count131072.C049477
import PlattCertificates.Count131072.C049478
import PlattCertificates.Count131072.C049479
import PlattCertificates.Count131072.C049480
import PlattCertificates.Count131072.C049481
import PlattCertificates.Count131072.C049482
import PlattCertificates.Count131072.C049483
import PlattCertificates.Count131072.C049484
import PlattCertificates.Count131072.C049485
import PlattCertificates.Count131072.C049486
import PlattCertificates.Count131072.C049487
import PlattCertificates.Count131072.C049488
import PlattCertificates.Count131072.C049489
import PlattCertificates.Count131072.C049490
import PlattCertificates.Count131072.C049491
import PlattCertificates.Count131072.C049492
import PlattCertificates.Count131072.C049493
import PlattCertificates.Count131072.C049494
import PlattCertificates.Count131072.C049495
import PlattCertificates.Count131072.C049496
import PlattCertificates.Count131072.C049497
import PlattCertificates.Count131072.C049498
import PlattCertificates.Count131072.C049499
import PlattCertificates.Count131072.C049500
import PlattCertificates.Count131072.C049501
import PlattCertificates.Count131072.C049502
import PlattCertificates.Count131072.C049503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000296
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49472 : List PrefixCut := [⟨64,251177739,251177885⟩]
theorem checked49472 : checkPrefixCuts (2^48) 6488326145 10 Manual.Count131072.C049472.packed 64 cuts49472 = true := by
 decide +kernel
def cuts49473 : List PrefixCut := [⟨22,86891575,86891625⟩,
⟨64,249480851,249480993⟩]
theorem checked49473 : checkPrefixCuts (2^48) 6488457217 10 Manual.Count131072.C049473.packed 64 cuts49473 = true := by
 decide +kernel
def pointBounds49473 : List (Nat × Nat × Nat) := [(6488502272,111524989029097,111525376076010)]
theorem point_links_checked49473 : (cuts49473.take 1).map (fun c => (6488457217-1+2*2^10*c.k,111524902137522+c.lower,111525289184385+c.upper)) = pointBounds49473 := by
 decide +kernel
def cuts49474 : List PrefixCut := [⟨58,232991782,232991913⟩,
⟨64,255809219,255809362⟩]
theorem checked49474 : checkPrefixCuts (2^48) 6488588289 10 Manual.Count131072.C049474.packed 64 cuts49474 = true := by
 decide +kernel
def pointBounds49474 : List (Nat × Nat × Nat) := [(6488707072,111525384610155,111525771657291)]
theorem point_links_checked49474 : (cuts49474.take 1).map (fun c => (6488588289-1+2*2^10*c.k,111525151618373+c.lower,111525538665378+c.upper)) = pointBounds49474 := by
 decide +kernel
def cuts49475 : List PrefixCut := [⟨64,250425101,250425240⟩]
theorem checked49475 : checkPrefixCuts (2^48) 6488719361 10 Manual.Count131072.C049475.packed 64 cuts49475 = true := by
 decide +kernel
def cuts49476 : List PrefixCut := [⟨30,122282671,122282739⟩,
⟨64,254367442,254367584⟩]
theorem checked49476 : checkPrefixCuts (2^48) 6488850433 10 Manual.Count131072.C049476.packed 64 cuts49476 = true := by
 decide +kernel
def pointBounds49476 : List (Nat × Nat × Nat) := [(6488911872,111525780135364,111526167182719)]
theorem point_links_checked49476 : (cuts49476.take 1).map (fun c => (6488850433-1+2*2^10*c.k,111525657852693+c.lower,111526044899980+c.upper)) = pointBounds49476 := by
 decide +kernel
def cuts49477 : List PrefixCut := [⟨64,249981213,249981357⟩]
theorem checked49477 : checkPrefixCuts (2^48) 6488981505 10 Manual.Count131072.C049477.packed 64 cuts49477 = true := by
 decide +kernel
def cuts49478 : List PrefixCut := [⟨2,8198153,8198158⟩,
⟨64,252231710,252231853⟩]
theorem checked49478 : checkPrefixCuts (2^48) 6489112577 10 Manual.Count131072.C049478.packed 64 cuts49478 = true := by
 decide +kernel
def pointBounds49478 : List (Nat × Nat × Nat) := [(6489116672,111526170399501,111526557447079)]
theorem point_links_checked49478 : (cuts49478.take 1).map (fun c => (6489112577-1+2*2^10*c.k,111526162201348+c.lower,111526549248921+c.upper)) = pointBounds49478 := by
 decide +kernel
def cuts49479 : List PrefixCut := [⟨38,148603947,148604034⟩,
⟨64,251662741,251662885⟩]
theorem checked49479 : checkPrefixCuts (2^48) 6489243649 10 Manual.Count131072.C049479.packed 64 cuts49479 = true := by
 decide +kernel
def pointBounds49479 : List (Nat × Nat × Nat) := [(6489321472,111526563037005,111526950084808)]
theorem point_links_checked49479 : (cuts49479.take 1).map (fun c => (6489243649-1+2*2^10*c.k,111526414433058+c.lower,111526801480774+c.upper)) = pointBounds49479 := by
 decide +kernel
def cuts49480 : List PrefixCut := [⟨64,251831145,251831288⟩]
theorem checked49480 : checkPrefixCuts (2^48) 6489374721 10 Manual.Count131072.C049480.packed 64 cuts49480 = true := by
 decide +kernel
def cuts49481 : List PrefixCut := [⟨10,38732794,38732816⟩,
⟨64,248356196,248356342⟩]
theorem checked49481 : checkPrefixCuts (2^48) 6489505793 10 Manual.Count131072.C049481.packed 64 cuts49481 = true := by
 decide +kernel
def pointBounds49481 : List (Nat × Nat × Nat) := [(6489526272,111526956659738,111527343707763)]
theorem point_links_checked49481 : (cuts49481.take 1).map (fun c => (6489505793-1+2*2^10*c.k,111526917926944+c.lower,111527304974947+c.upper)) = pointBounds49481 := by
 decide +kernel
def cuts49482 : List PrefixCut := [⟨46,179606194,179606299⟩,
⟨64,248481292,248481438⟩]
theorem checked49482 : checkPrefixCuts (2^48) 6489636865 10 Manual.Count131072.C049482.packed 64 cuts49482 = true := by
 decide +kernel
def pointBounds49482 : List (Nat × Nat × Nat) := [(6489731072,111527345889334,111527732937588)]
theorem point_links_checked49482 : (cuts49482.take 1).map (fun c => (6489636865-1+2*2^10*c.k,111527166283140+c.lower,111527553331289+c.upper)) = pointBounds49482 := by
 decide +kernel
def cuts49483 : List PrefixCut := [⟨64,251946025,251946167⟩]
theorem checked49483 : checkPrefixCuts (2^48) 6489767937 10 Manual.Count131072.C049483.packed 64 cuts49483 = true := by
 decide +kernel
def cuts49484 : List PrefixCut := [⟨18,69610625,69610666⟩,
⟨64,251160234,251160380⟩]
theorem checked49484 : checkPrefixCuts (2^48) 6489899009 10 Manual.Count131072.C049484.packed 64 cuts49484 = true := by
 decide +kernel
def pointBounds49484 : List (Nat × Nat × Nat) := [(6489935872,111527736321082,111528123369560)]
theorem point_links_checked49484 : (cuts49484.take 1).map (fun c => (6489899009-1+2*2^10*c.k,111527666710457+c.lower,111528053758894+c.upper)) = pointBounds49484 := by
 decide +kernel
def cuts49485 : List PrefixCut := [⟨54,212773125,212773249⟩,
⟨64,251675610,251675754⟩]
theorem checked49485 : checkPrefixCuts (2^48) 6490030081 10 Manual.Count131072.C049485.packed 64 cuts49485 = true := by
 decide +kernel
def pointBounds49485 : List (Nat × Nat × Nat) := [(6490140672,111528130643816,111528517692523)]
theorem point_links_checked49485 : (cuts49485.take 1).map (fun c => (6490030081-1+2*2^10*c.k,111527917870691+c.lower,111528304919274+c.upper)) = pointBounds49485 := by
 decide +kernel
def cuts49486 : List PrefixCut := [⟨64,249892406,249892546⟩]
theorem checked49486 : checkPrefixCuts (2^48) 6490161153 10 Manual.Count131072.C049486.packed 64 cuts49486 = true := by
 decide +kernel
def cuts49487 : List PrefixCut := [⟨26,103997475,103997532⟩,
⟨64,254874689,254874833⟩]
theorem checked49487 : checkPrefixCuts (2^48) 6490292225 10 Manual.Count131072.C049487.packed 64 cuts49487 = true := by
 decide +kernel
def pointBounds49487 : List (Nat × Nat × Nat) := [(6490345472,111528523436182,111528910485106)]
theorem point_links_checked49487 : (cuts49487.take 1).map (fun c => (6490292225-1+2*2^10*c.k,111528419438707+c.lower,111528806487574+c.upper)) = pointBounds49487 := by
 decide +kernel
def cuts49488 : List PrefixCut := [⟨62,241295673,241295811⟩,
⟨64,248841507,248841649⟩]
theorem checked49488 : checkPrefixCuts (2^48) 6490423297 10 Manual.Count131072.C049488.packed 64 cuts49488 = true := by
 decide +kernel
def pointBounds49488 : List (Nat × Nat × Nat) := [(6490550272,111528915609069,111529302658218)]
theorem point_links_checked49488 : (cuts49488.take 1).map (fun c => (6490423297-1+2*2^10*c.k,111528674313396+c.lower,111529061362407+c.upper)) = pointBounds49488 := by
 decide +kernel
def cuts49489 : List PrefixCut := [⟨64,249270093,249270236⟩]
theorem checked49489 : checkPrefixCuts (2^48) 6490554369 10 Manual.Count131072.C049489.packed 64 cuts49489 = true := by
 decide +kernel
def cuts49490 : List PrefixCut := [⟨34,132872634,132872707⟩,
⟨64,251043081,251043225⟩]
theorem checked49490 : checkPrefixCuts (2^48) 6490685441 10 Manual.Count131072.C049490.packed 64 cuts49490 = true := by
 decide +kernel
def pointBounds49490 : List (Nat × Nat × Nat) := [(6490755072,111529305297630,111529692346999)]
theorem point_links_checked49490 : (cuts49490.take 1).map (fun c => (6490685441-1+2*2^10*c.k,111529172424996+c.lower,111529559474292+c.upper)) = pointBounds49490 := by
 decide +kernel
def cuts49491 : List PrefixCut := [⟨64,256371862,256372008⟩]
theorem checked49491 : checkPrefixCuts (2^48) 6490816513 10 Manual.Count131072.C049491.packed 64 cuts49491 = true := by
 decide +kernel
def cuts49492 : List PrefixCut := [⟨6,22722831,22722844⟩,
⟨64,253938311,253938458⟩]
theorem checked49492 : checkPrefixCuts (2^48) 6490947585 10 Manual.Count131072.C049492.packed 64 cuts49492 = true := by
 decide +kernel
def pointBounds49492 : List (Nat × Nat × Nat) := [(6490959872,111529702562770,111530089612369)]
theorem point_links_checked49492 : (cuts49492.take 1).map (fun c => (6490947585-1+2*2^10*c.k,111529679839939+c.lower,111530066889525+c.upper)) = pointBounds49492 := by
 decide +kernel
def cuts49493 : List PrefixCut := [⟨42,166384068,166384168⟩,
⟨64,250637644,250637794⟩]
theorem checked49493 : checkPrefixCuts (2^48) 6491078657 10 Manual.Count131072.C049493.packed 64 cuts49493 = true := by
 decide +kernel
def pointBounds49493 : List (Nat × Nat × Nat) := [(6491164672,111530100162318,111530487212151)]
theorem point_links_checked49493 : (cuts49493.take 1).map (fun c => (6491078657-1+2*2^10*c.k,111529933778250+c.lower,111530320827983+c.upper)) = pointBounds49493 := by
 decide +kernel
def cuts49494 : List PrefixCut := [⟨64,251803326,251803472⟩]
theorem checked49494 : checkPrefixCuts (2^48) 6491209729 10 Manual.Count131072.C049494.packed 64 cuts49494 = true := by
 decide +kernel
def cuts49495 : List PrefixCut := [⟨14,55806254,55806285⟩,
⟨64,252188508,252188648⟩]
theorem checked49495 : checkPrefixCuts (2^48) 6491340801 10 Manual.Count131072.C049495.packed 64 cuts49495 = true := by
 decide +kernel
def pointBounds49495 : List (Nat × Nat × Nat) := [(6491369472,111530492025474,111530879075534)]
theorem point_links_checked49495 : (cuts49495.take 1).map (fun c => (6491340801-1+2*2^10*c.k,111530436219220+c.lower,111530823269249+c.upper)) = pointBounds49495 := by
 decide +kernel
def cuts49496 : List PrefixCut := [⟨50,197463174,197463286⟩,
⟨64,252963897,252964037⟩]
theorem checked49496 : checkPrefixCuts (2^48) 6491471873 10 Manual.Count131072.C049496.packed 64 cuts49496 = true := by
 decide +kernel
def pointBounds49496 : List (Nat × Nat × Nat) := [(6491574272,111530885870902,111531272921183)]
theorem point_links_checked49496 : (cuts49496.take 1).map (fun c => (6491471873-1+2*2^10*c.k,111530688407728+c.lower,111531075457897+c.upper)) = pointBounds49496 := by
 decide +kernel
def cuts49497 : List PrefixCut := [⟨64,251441183,251441324⟩]
theorem checked49497 : checkPrefixCuts (2^48) 6491602945 10 Manual.Count131072.C049497.packed 64 cuts49497 = true := by
 decide +kernel
def cuts49498 : List PrefixCut := [⟨22,85980532,85980579⟩,
⟨64,248401026,248401167⟩]
theorem checked49498 : checkPrefixCuts (2^48) 6491734017 10 Manual.Count131072.C049498.packed 64 cuts49498 = true := by
 decide +kernel
def pointBounds49498 : List (Nat × Nat × Nat) := [(6491779072,111531278793340,111531665843837)]
theorem point_links_checked49498 : (cuts49498.take 1).map (fun c => (6491734017-1+2*2^10*c.k,111531192812808+c.lower,111531579863258+c.upper)) = pointBounds49498 := by
 decide +kernel
def cuts49499 : List PrefixCut := [⟨58,229882536,229882666⟩,
⟨64,254856317,254856462⟩]
theorem checked49499 : checkPrefixCuts (2^48) 6491865089 10 Manual.Count131072.C049499.packed 64 cuts49499 = true := by
 decide +kernel
def pointBounds49499 : List (Nat × Nat × Nat) := [(6491983872,111531671096370,111532058147091)]
theorem point_links_checked49499 : (cuts49499.take 1).map (fun c => (6491865089-1+2*2^10*c.k,111531441213834+c.lower,111531828264425+c.upper)) = pointBounds49499 := by
 decide +kernel
def cuts49500 : List PrefixCut := [⟨64,250428770,250428914⟩]
theorem checked49500 : checkPrefixCuts (2^48) 6491996161 10 Manual.Count131072.C049500.packed 64 cuts49500 = true := by
 decide +kernel
def cuts49501 : List PrefixCut := [⟨30,116064378,116064445⟩,
⟨64,248385991,248386134⟩]
theorem checked49501 : checkPrefixCuts (2^48) 6492127233 10 Manual.Count131072.C049501.packed 64 cuts49501 = true := by
 decide +kernel
def pointBounds49501 : List (Nat × Nat × Nat) := [(6492188672,111532062563299,111532449614246)]
theorem point_links_checked49501 : (cuts49501.take 1).map (fun c => (6492127233-1+2*2^10*c.k,111531946498921+c.lower,111532333549801+c.upper)) = pointBounds49501 := by
 decide +kernel
def cuts49502 : List PrefixCut := [⟨64,252889885,252890026⟩]
theorem checked49502 : checkPrefixCuts (2^48) 6492258305 10 Manual.Count131072.C049502.packed 64 cuts49502 = true := by
 decide +kernel
def cuts49503 : List PrefixCut := [⟨2,7760469,7760474⟩,
⟨64,248896216,248896361⟩]
theorem checked49503 : checkPrefixCuts (2^48) 6492389377 10 Manual.Count131072.C049503.packed 64 cuts49503 = true := by
 decide +kernel
def pointBounds49503 : List (Nat × Nat × Nat) := [(6492393472,111532455535266,111532842586435)]
theorem point_links_checked49503 : (cuts49503.take 1).map (fun c => (6492389377-1+2*2^10*c.k,111532447774797+c.lower,111532834825961+c.upper)) = pointBounds49503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000296
