import PlattAssemblyKernel
import PlattCertificates.Count131072.C050512
import PlattCertificates.Count131072.C050513
import PlattCertificates.Count131072.C050514
import PlattCertificates.Count131072.C050515
import PlattCertificates.Count131072.C050516
import PlattCertificates.Count131072.C050517
import PlattCertificates.Count131072.C050518
import PlattCertificates.Count131072.C050519
import PlattCertificates.Count131072.C050520
import PlattCertificates.Count131072.C050521
import PlattCertificates.Count131072.C050522
import PlattCertificates.Count131072.C050523
import PlattCertificates.Count131072.C050524
import PlattCertificates.Count131072.C050525
import PlattCertificates.Count131072.C050526
import PlattCertificates.Count131072.C050527
import PlattCertificates.Count131072.C050528
import PlattCertificates.Count131072.C050529
import PlattCertificates.Count131072.C050530
import PlattCertificates.Count131072.C050531
import PlattCertificates.Count131072.C050532
import PlattCertificates.Count131072.C050533
import PlattCertificates.Count131072.C050534
import PlattCertificates.Count131072.C050535
import PlattCertificates.Count131072.C050536
import PlattCertificates.Count131072.C050537
import PlattCertificates.Count131072.C050538
import PlattCertificates.Count131072.C050539
import PlattCertificates.Count131072.C050540
import PlattCertificates.Count131072.C050541
import PlattCertificates.Count131072.C050542
import PlattCertificates.Count131072.C050543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50512 : List PrefixCut := [⟨64,246774160,246774295⟩]
theorem checked50512 : checkPrefixCuts (2^48) 6624641025 10 Manual.Count131072.C050512.packed 64 cuts50512 = true := by
 decide +kernel
def cuts50513 : List PrefixCut := [⟨32,123045338,123045407⟩,
⟨64,247109154,247109291⟩]
theorem checked50513 : checkPrefixCuts (2^48) 6624772097 10 Manual.Count131072.C050513.packed 64 cuts50513 = true := by
 decide +kernel
def pointBounds50513 : List (Nat × Nat × Nat) := [(6624837632,111784011844083,111784399038503)]
theorem point_links_checked50513 : (cuts50513.take 1).map (fun c => (6624772097-1+2*2^10*c.k,111783888798745+c.lower,111784275993096+c.upper)) = pointBounds50513 := by
 decide +kernel
def cuts50514 : List PrefixCut := [⟨64,245489760,245489900⟩]
theorem checked50514 : checkPrefixCuts (2^48) 6624903169 10 Manual.Count131072.C050514.packed 64 cuts50514 = true := by
 decide +kernel
def cuts50515 : List PrefixCut := [⟨6,22560341,22560354⟩,
⟨64,240599018,240599155⟩]
theorem checked50515 : checkPrefixCuts (2^48) 6625034241 10 Manual.Count131072.C050515.packed 64 cuts50515 = true := by
 decide +kernel
def pointBounds50515 : List (Nat × Nat × Nat) := [(6625046528,111784403958000,111784791152641)]
theorem point_links_checked50515 : (cuts50515.take 1).map (fun c => (6625034241-1+2*2^10*c.k,111784381397659+c.lower,111784768592287+c.upper)) = pointBounds50515 := by
 decide +kernel
def cuts50516 : List PrefixCut := [⟨44,171513674,171513771⟩,
⟨64,250110931,250111073⟩]
theorem checked50516 : checkPrefixCuts (2^48) 6625165313 10 Manual.Count131072.C050516.packed 64 cuts50516 = true := by
 decide +kernel
def pointBounds50516 : List (Nat × Nat × Nat) := [(6625255424,111784793510351,111785180705213)]
theorem point_links_checked50516 : (cuts50516.take 1).map (fun c => (6625165313-1+2*2^10*c.k,111784621996677+c.lower,111785009191442+c.upper)) = pointBounds50516 := by
 decide +kernel
def cuts50517 : List PrefixCut := [⟨64,246707242,246707381⟩]
theorem checked50517 : checkPrefixCuts (2^48) 6625296385 10 Manual.Count131072.C050517.packed 64 cuts50517 = true := by
 decide +kernel
def cuts50518 : List PrefixCut := [⟨18,67804335,67804373⟩,
⟨64,243643544,243643681⟩]
theorem checked50518 : checkPrefixCuts (2^48) 6625427457 10 Manual.Count131072.C050518.packed 64 cuts50518 = true := by
 decide +kernel
def pointBounds50518 : List (Nat × Nat × Nat) := [(6625464320,111785186619185,111785573814269)]
theorem point_links_checked50518 : (cuts50518.take 1).map (fun c => (6625427457-1+2*2^10*c.k,111785118814850+c.lower,111785506009896+c.upper)) = pointBounds50518 := by
 decide +kernel
def cuts50519 : List PrefixCut := [⟨56,213943530,213943651⟩,
⟨64,243171426,243171564⟩]
theorem checked50519 : checkPrefixCuts (2^48) 6625558529 10 Manual.Count131072.C050519.packed 64 cuts50519 = true := by
 decide +kernel
def pointBounds50519 : List (Nat × Nat × Nat) := [(6625673216,111785576401924,111785963597228)]
theorem point_links_checked50519 : (cuts50519.take 1).map (fun c => (6625558529-1+2*2^10*c.k,111785362458394+c.lower,111785749653577+c.upper)) = pointBounds50519 := by
 decide +kernel
def cuts50520 : List PrefixCut := [⟨64,247287332,247287469⟩]
theorem checked50520 : checkPrefixCuts (2^48) 6625689601 10 Manual.Count131072.C050520.packed 64 cuts50520 = true := by
 decide +kernel
def cuts50521 : List PrefixCut := [⟨30,115166851,115166915⟩,
⟨64,249109121,249109261⟩]
theorem checked50521 : checkPrefixCuts (2^48) 6625820673 10 Manual.Count131072.C050521.packed 64 cuts50521 = true := by
 decide +kernel
def pointBounds50521 : List (Nat × Nat × Nat) := [(6625882112,111785968084003,111786355279525)]
theorem point_links_checked50521 : (cuts50521.take 1).map (fun c => (6625820673-1+2*2^10*c.k,111785852917152+c.lower,111786240112610+c.upper)) = pointBounds50521 := by
 decide +kernel
def cuts50522 : List PrefixCut := [⟨64,244388924,244389063⟩]
theorem checked50522 : checkPrefixCuts (2^48) 6625951745 10 Manual.Count131072.C050522.packed 64 cuts50522 = true := by
 decide +kernel
def cuts50523 : List PrefixCut := [⟨4,15165292,15165300⟩,
⟨64,248334658,248334805⟩]
theorem checked50523 : checkPrefixCuts (2^48) 6626082817 10 Manual.Count131072.C050523.packed 64 cuts50523 = true := by
 decide +kernel
def pointBounds50523 : List (Nat × Nat × Nat) := [(6626091008,111786361580489,111786748776234)]
theorem point_links_checked50523 : (cuts50523.take 1).map (fun c => (6626082817-1+2*2^10*c.k,111786346415197+c.lower,111786733610934+c.upper)) = pointBounds50523 := by
 decide +kernel
def cuts50524 : List PrefixCut := [⟨42,160272191,160272284⟩,
⟨64,245058873,245059011⟩]
theorem checked50524 : checkPrefixCuts (2^48) 6626213889 10 Manual.Count131072.C050524.packed 64 cuts50524 = true := by
 decide +kernel
def pointBounds50524 : List (Nat × Nat × Nat) := [(6626299904,111786755022046,111787142218023)]
theorem point_links_checked50524 : (cuts50524.take 1).map (fun c => (6626213889-1+2*2^10*c.k,111786594749855+c.lower,111786981945739+c.upper)) = pointBounds50524 := by
 decide +kernel
def cuts50525 : List PrefixCut := [⟨64,245563790,245563930⟩]
theorem checked50525 : checkPrefixCuts (2^48) 6626344961 10 Manual.Count131072.C050525.packed 64 cuts50525 = true := by
 decide +kernel
def cuts50526 : List PrefixCut := [⟨16,62101677,62101712⟩,
⟨64,245473959,245474093⟩]
theorem checked50526 : checkPrefixCuts (2^48) 6626476033 10 Manual.Count131072.C050526.packed 64 cuts50526 = true := by
 decide +kernel
def pointBounds50526 : List (Nat × Nat × Nat) := [(6626508800,111787147474195,111787534670392)]
theorem point_links_checked50526 : (cuts50526.take 1).map (fun c => (6626476033-1+2*2^10*c.k,111787085372518+c.lower,111787472568680+c.upper)) = pointBounds50526 := by
 decide +kernel
def cuts50527 : List PrefixCut := [⟨54,209619656,209619775⟩,
⟨64,249546810,249546953⟩]
theorem checked50527 : checkPrefixCuts (2^48) 6626607105 10 Manual.Count131072.C050527.packed 64 cuts50527 = true := by
 decide +kernel
def pointBounds50527 : List (Nat × Nat × Nat) := [(6626717696,111787540466133,111787927662548)]
theorem point_links_checked50527 : (cuts50527.take 1).map (fun c => (6626607105-1+2*2^10*c.k,111787330846477+c.lower,111787718042773+c.upper)) = pointBounds50527 := by
 decide +kernel
def cuts50528 : List PrefixCut := [⟨64,246865912,246866053⟩]
theorem checked50528 : checkPrefixCuts (2^48) 6626738177 10 Manual.Count131072.C050528.packed 64 cuts50528 = true := by
 decide +kernel
def cuts50529 : List PrefixCut := [⟨28,107800556,107800617⟩,
⟨64,245841674,245841815⟩]
theorem checked50529 : checkPrefixCuts (2^48) 6626869249 10 Manual.Count131072.C050529.packed 64 cuts50529 = true := by
 decide +kernel
def pointBounds50529 : List (Nat × Nat × Nat) := [(6626926592,111787935059755,111788322256396)]
theorem point_links_checked50529 : (cuts50529.take 1).map (fun c => (6626869249-1+2*2^10*c.k,111787827259199+c.lower,111788214455779+c.upper)) = pointBounds50529 := by
 decide +kernel
def cuts50530 : List PrefixCut := [⟨64,246558844,246558982⟩]
theorem checked50530 : checkPrefixCuts (2^48) 6627000321 10 Manual.Count131072.C050530.packed 64 cuts50530 = true := by
 decide +kernel
def cuts50531 : List PrefixCut := [⟨2,7772578,7772582⟩,
⟨64,242136808,242136941⟩]
theorem checked50531 : checkPrefixCuts (2^48) 6627131393 10 Manual.Count131072.C050531.packed 64 cuts50531 = true := by
 decide +kernel
def pointBounds50531 : List (Nat × Nat × Nat) := [(6627135488,111788327432295,111788714629158)]
theorem point_links_checked50531 : (cuts50531.take 1).map (fun c => (6627131393-1+2*2^10*c.k,111788319659717+c.lower,111788706856576+c.upper)) = pointBounds50531 := by
 decide +kernel
def cuts50532 : List PrefixCut := [⟨40,152856772,152856858⟩,
⟨64,245784612,245784749⟩]
theorem checked50532 : checkPrefixCuts (2^48) 6627262465 10 Manual.Count131072.C050532.packed 64 cuts50532 = true := by
 decide +kernel
def pointBounds50532 : List (Nat × Nat × Nat) := [(6627344384,111788714653297,111789101850375)]
theorem point_links_checked50532 : (cuts50532.take 1).map (fun c => (6627262465-1+2*2^10*c.k,111788561796525+c.lower,111788948993517+c.upper)) = pointBounds50532 := by
 decide +kernel
def cuts50533 : List PrefixCut := [⟨64,247903313,247903451⟩]
theorem checked50533 : checkPrefixCuts (2^48) 6627393537 10 Manual.Count131072.C050533.packed 64 cuts50533 = true := by
 decide +kernel
def cuts50534 : List PrefixCut := [⟨14,53682711,53682743⟩,
⟨64,247813452,247813593⟩]
theorem checked50534 : checkPrefixCuts (2^48) 6627524609 10 Manual.Count131072.C050534.packed 64 cuts50534 = true := by
 decide +kernel
def pointBounds50534 : List (Nat × Nat × Nat) := [(6627553280,111789109167161,111789496364460)]
theorem point_links_checked50534 : (cuts50534.take 1).map (fun c => (6627524609-1+2*2^10*c.k,111789055484450+c.lower,111789442681717+c.upper)) = pointBounds50534 := by
 decide +kernel
def cuts50535 : List PrefixCut := [⟨52,201984518,201984632⟩,
⟨64,246959181,246959321⟩]
theorem checked50535 : checkPrefixCuts (2^48) 6627655681 10 Manual.Count131072.C050535.packed 64 cuts50535 = true := by
 decide +kernel
def pointBounds50535 : List (Nat × Nat × Nat) := [(6627762176,111789505282420,111789892479942)]
theorem point_links_checked50535 : (cuts50535.take 1).map (fun c => (6627655681-1+2*2^10*c.k,111789303297902+c.lower,111789690495310+c.upper)) = pointBounds50535 := by
 decide +kernel
def cuts50536 : List PrefixCut := [⟨64,248016005,248016147⟩]
theorem checked50536 : checkPrefixCuts (2^48) 6627786753 10 Manual.Count131072.C050536.packed 64 cuts50536 = true := by
 decide +kernel
def cuts50537 : List PrefixCut := [⟨26,101838029,101838083⟩,
⟨64,247119279,247119415⟩]
theorem checked50537 : checkPrefixCuts (2^48) 6627917825 10 Manual.Count131072.C050537.packed 64 cuts50537 = true := by
 decide +kernel
def pointBounds50537 : List (Nat × Nat × Nat) := [(6627971072,111789900111117,111790287308861)]
theorem point_links_checked50537 : (cuts50537.take 1).map (fun c => (6627917825-1+2*2^10*c.k,111789798273088+c.lower,111790185470778+c.upper)) = pointBounds50537 := by
 decide +kernel
def cuts50538 : List PrefixCut := [⟨64,246859559,246859707⟩]
theorem checked50538 : checkPrefixCuts (2^48) 6628048897 10 Manual.Count131072.C050538.packed 64 cuts50538 = true := by
 decide +kernel
def pointBounds50538 : List (Nat × Nat × Nat) := [(6628179968,111790292251926,111790679449900)]
theorem point_links_checked50538 : (cuts50538.take 1).map (fun c => (6628048897-1+2*2^10*c.k,111790045392367+c.lower,111790432590193+c.upper)) = pointBounds50538 := by
 decide +kernel
def cuts50539 : List PrefixCut := [⟨64,246217713,246217848⟩]
theorem checked50539 : checkPrefixCuts (2^48) 6628179969 10 Manual.Count131072.C050539.packed 64 cuts50539 = true := by
 decide +kernel
def cuts50540 : List PrefixCut := [⟨38,146505301,146505385⟩,
⟨64,246127920,246128061⟩]
theorem checked50540 : checkPrefixCuts (2^48) 6628311041 10 Manual.Count131072.C050540.packed 64 cuts50540 = true := by
 decide +kernel
def pointBounds50540 : List (Nat × Nat × Nat) := [(6628388864,111790684974940,111791072173133)]
theorem point_links_checked50540 : (cuts50540.take 1).map (fun c => (6628311041-1+2*2^10*c.k,111790538469639+c.lower,111790925667748+c.upper)) = pointBounds50540 := by
 decide +kernel
def cuts50541 : List PrefixCut := [⟨64,243914918,243915056⟩]
theorem checked50541 : checkPrefixCuts (2^48) 6628442113 10 Manual.Count131072.C050541.packed 64 cuts50541 = true := by
 decide +kernel
def cuts50542 : List PrefixCut := [⟨12,47177280,47177304⟩,
⟨64,248283816,248283952⟩]
theorem checked50542 : checkPrefixCuts (2^48) 6628573185 10 Manual.Count131072.C050542.packed 64 cuts50542 = true := by
 decide +kernel
def pointBounds50542 : List (Nat × Nat × Nat) := [(6628597760,111791075689757,111791462888169)]
theorem point_links_checked50542 : (cuts50542.take 1).map (fun c => (6628573185-1+2*2^10*c.k,111791028512477+c.lower,111791415710865+c.upper)) = pointBounds50542 := by
 decide +kernel
def cuts50543 : List PrefixCut := [⟨50,194012106,194012216⟩,
⟨64,248533684,248533826⟩]
theorem checked50543 : checkPrefixCuts (2^48) 6628704257 10 Manual.Count131072.C050543.packed 64 cuts50543 = true := by
 decide +kernel
def pointBounds50543 : List (Nat × Nat × Nat) := [(6628806656,111791470808399,111791858007033)]
theorem point_links_checked50543 : (cuts50543.take 1).map (fun c => (6628704257-1+2*2^10*c.k,111791276796293+c.lower,111791663994817+c.upper)) = pointBounds50543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000016
