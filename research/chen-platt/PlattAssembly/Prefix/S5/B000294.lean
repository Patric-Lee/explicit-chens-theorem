import PlattAssemblyKernel
import PlattCertificates.Count131072.C049408
import PlattCertificates.Count131072.C049409
import PlattCertificates.Count131072.C049410
import PlattCertificates.Count131072.C049411
import PlattCertificates.Count131072.C049412
import PlattCertificates.Count131072.C049413
import PlattCertificates.Count131072.C049414
import PlattCertificates.Count131072.C049415
import PlattCertificates.Count131072.C049416
import PlattCertificates.Count131072.C049417
import PlattCertificates.Count131072.C049418
import PlattCertificates.Count131072.C049419
import PlattCertificates.Count131072.C049420
import PlattCertificates.Count131072.C049421
import PlattCertificates.Count131072.C049422
import PlattCertificates.Count131072.C049423
import PlattCertificates.Count131072.C049424
import PlattCertificates.Count131072.C049425
import PlattCertificates.Count131072.C049426
import PlattCertificates.Count131072.C049427
import PlattCertificates.Count131072.C049428
import PlattCertificates.Count131072.C049429
import PlattCertificates.Count131072.C049430
import PlattCertificates.Count131072.C049431
import PlattCertificates.Count131072.C049432
import PlattCertificates.Count131072.C049433
import PlattCertificates.Count131072.C049434
import PlattCertificates.Count131072.C049435
import PlattCertificates.Count131072.C049436
import PlattCertificates.Count131072.C049437
import PlattCertificates.Count131072.C049438
import PlattCertificates.Count131072.C049439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000294
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49408 : List PrefixCut := [⟨23,89394879,89394930⟩,
⟨64,250503852,250503991⟩]
theorem checked49408 : checkPrefixCuts (2^48) 6479937537 10 Manual.Count131072.C049408.packed 64 cuts49408 = true := by
 decide +kernel
def pointBounds49408 : List (Nat × Nat × Nat) := [(6479984640,111508623452972,111509010490565)]
theorem point_links_checked49408 : (cuts49408.take 1).map (fun c => (6479937537-1+2*2^10*c.k,111508534058093+c.lower,111508921095635+c.upper)) = pointBounds49408 := by
 decide +kernel
def cuts49409 : List PrefixCut := [⟨58,231082834,231082965⟩,
⟨64,253278724,253278870⟩]
theorem checked49409 : checkPrefixCuts (2^48) 6480068609 10 Manual.Count131072.C049409.packed 64 cuts49409 = true := by
 decide +kernel
def pointBounds49409 : List (Nat × Nat × Nat) := [(6480187392,111509015644779,111509402682591)]
theorem point_links_checked49409 : (cuts49409.take 1).map (fun c => (6480068609-1+2*2^10*c.k,111508784561945+c.lower,111509171599626+c.upper)) = pointBounds49409 := by
 decide +kernel
def cuts49410 : List PrefixCut := [⟨64,253447374,253447523⟩]
theorem checked49410 : checkPrefixCuts (2^48) 6480199681 10 Manual.Count131072.C049410.packed 64 cuts49410 = true := by
 decide +kernel
def cuts49411 : List PrefixCut := [⟨29,115059496,115059562⟩,
⟨64,251661401,251661544⟩]
theorem checked49411 : checkPrefixCuts (2^48) 6480330753 10 Manual.Count131072.C049411.packed 64 cuts49411 = true := by
 decide +kernel
def pointBounds49411 : List (Nat × Nat × Nat) := [(6480390144,111509406347539,111509793385581)]
theorem point_links_checked49411 : (cuts49411.take 1).map (fun c => (6480330753-1+2*2^10*c.k,111509291288043+c.lower,111509678326019+c.upper)) = pointBounds49411 := by
 decide +kernel
def cuts49412 : List PrefixCut := [⟨64,252742142,252742284⟩]
theorem checked49412 : checkPrefixCuts (2^48) 6480461825 10 Manual.Count131072.C049412.packed 64 cuts49412 = true := by
 decide +kernel
def pointBounds49412 : List (Nat × Nat × Nat) := [(6480592896,111509795691586,111510182729847)]
theorem point_links_checked49412 : (cuts49412.take 1).map (fun c => (6480461825-1+2*2^10*c.k,111509542949444+c.lower,111509929987563+c.upper)) = pointBounds49412 := by
 decide +kernel
def cuts49413 : List PrefixCut := [⟨64,250174466,250174609⟩]
theorem checked49413 : checkPrefixCuts (2^48) 6480592897 10 Manual.Count131072.C049413.packed 64 cuts49413 = true := by
 decide +kernel
def cuts49414 : List PrefixCut := [⟨35,139070516,139070592⟩,
⟨64,252905664,252905802⟩]
theorem checked49414 : checkPrefixCuts (2^48) 6480723969 10 Manual.Count131072.C049414.packed 64 cuts49414 = true := by
 decide +kernel
def pointBounds49414 : List (Nat × Nat × Nat) := [(6480795648,111510184936568,111510571975048)]
theorem point_links_checked49414 : (cuts49414.take 1).map (fun c => (6480723969-1+2*2^10*c.k,111510045866052+c.lower,111510432904456+c.upper)) = pointBounds49414 := by
 decide +kernel
def cuts49415 : List PrefixCut := [⟨64,255940749,255940887⟩]
theorem checked49415 : checkPrefixCuts (2^48) 6480855041 10 Manual.Count131072.C049415.packed 64 cuts49415 = true := by
 decide +kernel
def cuts49416 : List PrefixCut := [⟨6,24799005,24799020⟩,
⟨64,255457833,255457978⟩]
theorem checked49416 : checkPrefixCuts (2^48) 6480986113 10 Manual.Count131072.C049416.packed 64 cuts49416 = true := by
 decide +kernel
def pointBounds49416 : List (Nat × Nat × Nat) := [(6480998400,111510579511470,111510966550165)]
theorem point_links_checked49416 : (cuts49416.take 1).map (fun c => (6480986113-1+2*2^10*c.k,111510554712465+c.lower,111510941751145+c.upper)) = pointBounds49416 := by
 decide +kernel
def cuts49417 : List PrefixCut := [⟨41,163599736,163599828⟩,
⟨64,252282317,252282457⟩]
theorem checked49417 : checkPrefixCuts (2^48) 6481117185 10 Manual.Count131072.C049417.packed 64 cuts49417 = true := by
 decide +kernel
def pointBounds49417 : List (Nat × Nat × Nat) := [(6481201152,111510973770034,111511360808951)]
theorem point_links_checked49417 : (cuts49417.take 1).map (fun c => (6481117185-1+2*2^10*c.k,111510810170298+c.lower,111511197209123+c.upper)) = pointBounds49417 := by
 decide +kernel
def cuts49418 : List PrefixCut := [⟨64,254752628,254752772⟩]
theorem checked49418 : checkPrefixCuts (2^48) 6481248257 10 Manual.Count131072.C049418.packed 64 cuts49418 = true := by
 decide +kernel
def cuts49419 : List PrefixCut := [⟨12,45816707,45816734⟩,
⟨64,251577238,251577383⟩]
theorem checked49419 : checkPrefixCuts (2^48) 6481379329 10 Manual.Count131072.C049419.packed 64 cuts49419 = true := by
 decide +kernel
def pointBounds49419 : List (Nat × Nat × Nat) := [(6481403904,111511363021950,111511750061086)]
theorem point_links_checked49419 : (cuts49419.take 1).map (fun c => (6481379329-1+2*2^10*c.k,111511317205243+c.lower,111511704244352+c.upper)) = pointBounds49419 := by
 decide +kernel
def cuts49420 : List PrefixCut := [⟨47,188820787,188820892⟩,
⟨64,255393768,255393912⟩]
theorem checked49420 : checkPrefixCuts (2^48) 6481510401 10 Manual.Count131072.C049420.packed 64 cuts49420 = true := by
 decide +kernel
def pointBounds49420 : List (Nat × Nat × Nat) := [(6481606656,111511757603268,111512144642627)]
theorem point_links_checked49420 : (cuts49420.take 1).map (fun c => (6481510401-1+2*2^10*c.k,111511568782481+c.lower,111511955821735+c.upper)) = pointBounds49420 := by
 decide +kernel
def cuts49421 : List PrefixCut := [⟨64,252522439,252522581⟩]
theorem checked49421 : checkPrefixCuts (2^48) 6481641473 10 Manual.Count131072.C049421.packed 64 cuts49421 = true := by
 decide +kernel
def cuts49422 : List PrefixCut := [⟨18,73085090,73085129⟩,
⟨64,254688631,254688776⟩]
theorem checked49422 : checkPrefixCuts (2^48) 6481772545 10 Manual.Count131072.C049422.packed 64 cuts49422 = true := by
 decide +kernel
def pointBounds49422 : List (Nat × Nat × Nat) := [(6481809408,111512149783778,111512536823357)]
theorem point_links_checked49422 : (cuts49422.take 1).map (fun c => (6481772545-1+2*2^10*c.k,111512076698688+c.lower,111512463738228+c.upper)) = pointBounds49422 := by
 decide +kernel
def cuts49423 : List PrefixCut := [⟨53,207785583,207785703⟩,
⟨64,250558145,250558291⟩]
theorem checked49423 : checkPrefixCuts (2^48) 6481903617 10 Manual.Count131072.C049423.packed 64 cuts49423 = true := by
 decide +kernel
def pointBounds49423 : List (Nat × Nat × Nat) := [(6482012160,111512539172902,111512926212707)]
theorem point_links_checked49423 : (cuts49423.take 1).map (fun c => (6481903617-1+2*2^10*c.k,111512331387319+c.lower,111512718427004+c.upper)) = pointBounds49423 := by
 decide +kernel
def cuts49424 : List PrefixCut := [⟨64,252507127,252507264⟩]
theorem checked49424 : checkPrefixCuts (2^48) 6482034689 10 Manual.Count131072.C049424.packed 64 cuts49424 = true := by
 decide +kernel
def cuts49425 : List PrefixCut := [⟨24,93793261,93793314⟩,
⟨64,248463736,248463879⟩]
theorem checked49425 : checkPrefixCuts (2^48) 6482165761 10 Manual.Count131072.C049425.packed 64 cuts49425 = true := by
 decide +kernel
def pointBounds49425 : List (Nat × Nat × Nat) := [(6482214912,111512928245852,111513315285873)]
theorem point_links_checked49425 : (cuts49425.take 1).map (fun c => (6482165761-1+2*2^10*c.k,111512834452591+c.lower,111513221492559+c.upper)) = pointBounds49425 := by
 decide +kernel
def cuts49426 : List PrefixCut := [⟨59,232262607,232262738⟩,
⟨64,251454799,251454942⟩]
theorem checked49426 : checkPrefixCuts (2^48) 6482296833 10 Manual.Count131072.C049426.packed 64 cuts49426 = true := by
 decide +kernel
def pointBounds49426 : List (Nat × Nat × Nat) := [(6482417664,111513315178934,111513702219176)]
theorem point_links_checked49426 : (cuts49426.take 1).map (fun c => (6482296833-1+2*2^10*c.k,111513082916327+c.lower,111513469956438+c.upper)) = pointBounds49426 := by
 decide +kernel
def cuts49427 : List PrefixCut := [⟨64,251927353,251927498⟩]
theorem checked49427 : checkPrefixCuts (2^48) 6482427905 10 Manual.Count131072.C049427.packed 64 cuts49427 = true := by
 decide +kernel
def cuts49428 : List PrefixCut := [⟨30,117755389,117755458⟩,
⟨64,251401208,251401353⟩]
theorem checked49428 : checkPrefixCuts (2^48) 6482558977 10 Manual.Count131072.C049428.packed 64 cuts49428 = true := by
 decide +kernel
def pointBounds49428 : List (Nat × Nat × Nat) := [(6482620416,111513704053868,111514091094336)]
theorem point_links_checked49428 : (cuts49428.take 1).map (fun c => (6482558977-1+2*2^10*c.k,111513586298479+c.lower,111513973338878+c.upper)) = pointBounds49428 := by
 decide +kernel
def cuts49429 : List PrefixCut := [⟨64,254305201,254305343⟩]
theorem checked49429 : checkPrefixCuts (2^48) 6482690049 10 Manual.Count131072.C049429.packed 64 cuts49429 = true := by
 decide +kernel
def cuts49430 : List PrefixCut := [⟨1,3473486,3473488⟩,
⟨64,252085730,252085874⟩]
theorem checked49430 : checkPrefixCuts (2^48) 6482821121 10 Manual.Count131072.C049430.packed 64 cuts49430 = true := by
 decide +kernel
def pointBounds49430 : List (Nat × Nat × Nat) := [(6482823168,111514095478374,111514482519062)]
theorem point_links_checked49430 : (cuts49430.take 1).map (fun c => (6482821121-1+2*2^10*c.k,111514092004888+c.lower,111514479045574+c.upper)) = pointBounds49430 := by
 decide +kernel
def cuts49431 : List PrefixCut := [⟨36,143711780,143711861⟩,
⟨64,254034421,254034564⟩]
theorem checked49431 : checkPrefixCuts (2^48) 6482952193 10 Manual.Count131072.C049431.packed 64 cuts49431 = true := by
 decide +kernel
def pointBounds49431 : List (Nat × Nat × Nat) := [(6483025920,111514487802398,111514874843309)]
theorem point_links_checked49431 : (cuts49431.take 1).map (fun c => (6482952193-1+2*2^10*c.k,111514344090618+c.lower,111514731131448+c.upper)) = pointBounds49431 := by
 decide +kernel
def cuts49432 : List PrefixCut := [⟨64,251207238,251207377⟩]
theorem checked49432 : checkPrefixCuts (2^48) 6483083265 10 Manual.Count131072.C049432.packed 64 cuts49432 = true := by
 decide +kernel
def cuts49433 : List PrefixCut := [⟨7,26613947,26613962⟩,
⟨64,249031346,249031488⟩]
theorem checked49433 : checkPrefixCuts (2^48) 6483214337 10 Manual.Count131072.C049433.packed 64 cuts49433 = true := by
 decide +kernel
def pointBounds49433 : List (Nat × Nat × Nat) := [(6483228672,111514875946224,111515262987351)]
theorem point_links_checked49433 : (cuts49433.take 1).map (fun c => (6483214337-1+2*2^10*c.k,111514849332277+c.lower,111515236373389+c.upper)) = pointBounds49433 := by
 decide +kernel
def cuts49434 : List PrefixCut := [⟨42,167971785,167971877⟩,
⟨64,253975594,253975733⟩]
theorem checked49434 : checkPrefixCuts (2^48) 6483345409 10 Manual.Count131072.C049434.packed 64 cuts49434 = true := by
 decide +kernel
def pointBounds49434 : List (Nat × Nat × Nat) := [(6483431424,111515266335408,111515653376754)]
theorem point_links_checked49434 : (cuts49434.take 1).map (fun c => (6483345409-1+2*2^10*c.k,111515098363623+c.lower,111515485404877+c.upper)) = pointBounds49434 := by
 decide +kernel
def cuts49435 : List PrefixCut := [⟨64,249629081,249629222⟩]
theorem checked49435 : checkPrefixCuts (2^48) 6483476481 10 Manual.Count131072.C049435.packed 64 cuts49435 = true := by
 decide +kernel
def cuts49436 : List PrefixCut := [⟨13,50750062,50750091⟩,
⟨64,252141978,252142124⟩]
theorem checked49436 : checkPrefixCuts (2^48) 6483607553 10 Manual.Count131072.C049436.packed 64 cuts49436 = true := by
 decide +kernel
def pointBounds49436 : List (Nat × Nat × Nat) := [(6483634176,111515652718360,111516039759923)]
theorem point_links_checked49436 : (cuts49436.take 1).map (fun c => (6483607553-1+2*2^10*c.k,111515601968298+c.lower,111515989009832+c.upper)) = pointBounds49436 := by
 decide +kernel
def cuts49437 : List PrefixCut := [⟨48,187800789,187800896⟩,
⟨64,249228298,249228439⟩]
theorem checked49437 : checkPrefixCuts (2^48) 6483738625 10 Manual.Count131072.C049437.packed 64 cuts49437 = true := by
 decide +kernel
def pointBounds49437 : List (Nat × Nat × Nat) := [(6483836928,111516041911065,111516428952852)]
theorem point_links_checked49437 : (cuts49437.take 1).map (fun c => (6483738625-1+2*2^10*c.k,111515854110276+c.lower,111516241151956+c.upper)) = pointBounds49437 := by
 decide +kernel
def cuts49438 : List PrefixCut := [⟨64,250959680,250959834⟩]
theorem checked49438 : checkPrefixCuts (2^48) 6483869697 10 Manual.Count131072.C049438.packed 64 cuts49438 = true := by
 decide +kernel
def cuts49439 : List PrefixCut := [⟨19,74883204,74883247⟩,
⟨64,253472420,253472563⟩]
theorem checked49439 : checkPrefixCuts (2^48) 6484000769 10 Manual.Count131072.C049439.packed 64 cuts49439 = true := by
 decide +kernel
def pointBounds49439 : List (Nat × Nat × Nat) := [(6484039680,111516429181458,111516816223476)]
theorem point_links_checked49439 : (cuts49439.take 1).map (fun c => (6484000769-1+2*2^10*c.k,111516354298254+c.lower,111516741340229+c.upper)) = pointBounds49439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000294
