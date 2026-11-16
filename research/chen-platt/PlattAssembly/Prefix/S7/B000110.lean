import PlattAssemblyKernel
import PlattCertificates.Count131072.C063520
import PlattCertificates.Count131072.C063521
import PlattCertificates.Count131072.C063522
import PlattCertificates.Count131072.C063523
import PlattCertificates.Count131072.C063524
import PlattCertificates.Count131072.C063525
import PlattCertificates.Count131072.C063526
import PlattCertificates.Count131072.C063527
import PlattCertificates.Count131072.C063528
import PlattCertificates.Count131072.C063529
import PlattCertificates.Count131072.C063530
import PlattCertificates.Count131072.C063531
import PlattCertificates.Count131072.C063532
import PlattCertificates.Count131072.C063533
import PlattCertificates.Count131072.C063534
import PlattCertificates.Count131072.C063535
import PlattCertificates.Count131072.C063536
import PlattCertificates.Count131072.C063537
import PlattCertificates.Count131072.C063538
import PlattCertificates.Count131072.C063539
import PlattCertificates.Count131072.C063540
import PlattCertificates.Count131072.C063541
import PlattCertificates.Count131072.C063542
import PlattCertificates.Count131072.C063543
import PlattCertificates.Count131072.C063544
import PlattCertificates.Count131072.C063545
import PlattCertificates.Count131072.C063546
import PlattCertificates.Count131072.C063547
import PlattCertificates.Count131072.C063548
import PlattCertificates.Count131072.C063549
import PlattCertificates.Count131072.C063550
import PlattCertificates.Count131072.C063551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63520 : List PrefixCut := [⟨48,147737855,147737941⟩,
⟨64,196499069,196499185⟩]
theorem checked63520 : checkPrefixCuts (2^48) 8329625601 10 Manual.Count131072.C063520.packed 64 cuts63520 = true := by
 decide +kernel
def pointBounds63520 : List (Nat × Nat × Nat) := [(8329723904,114620021775089,114620410585591)]
theorem point_links_checked63520 : (cuts63520.take 1).map (fun c => (8329625601-1+2*2^10*c.k,114619874037234+c.lower,114620262847650+c.upper)) = pointBounds63520 := by
 decide +kernel
def cuts63521 : List PrefixCut := [⟨64,191427295,191427405⟩]
theorem checked63521 : checkPrefixCuts (2^48) 8329756673 10 Manual.Count131072.C063521.packed 64 cuts63521 = true := by
 decide +kernel
def cuts63522 : List PrefixCut := [⟨48,143340412,143340494⟩,
⟨64,191221541,191221651⟩]
theorem checked63522 : checkPrefixCuts (2^48) 8329887745 10 Manual.Count131072.C063522.packed 64 cuts63522 = true := by
 decide +kernel
def pointBounds63522 : List (Nat × Nat × Nat) := [(8329986048,114620405304010,114620794114734)]
theorem point_links_checked63522 : (cuts63522.take 1).map (fun c => (8329887745-1+2*2^10*c.k,114620261963598+c.lower,114620650774240+c.upper)) = pointBounds63522 := by
 decide +kernel
def cuts63523 : List PrefixCut := [⟨64,196388416,196388525⟩]
theorem checked63523 : checkPrefixCuts (2^48) 8330018817 10 Manual.Count131072.C063523.packed 64 cuts63523 = true := by
 decide +kernel
def cuts63524 : List PrefixCut := [⟨48,145971493,145971577⟩,
⟨64,192465752,192465862⟩]
theorem checked63524 : checkPrefixCuts (2^48) 8330149889 10 Manual.Count131072.C063524.packed 64 cuts63524 = true := by
 decide +kernel
def pointBounds63524 : List (Nat × Nat × Nat) := [(8330248192,114620795545048,114621184355993)]
theorem point_links_checked63524 : (cuts63524.take 1).map (fun c => (8330149889-1+2*2^10*c.k,114620649573555+c.lower,114621038384416+c.upper)) = pointBounds63524 := by
 decide +kernel
def cuts63525 : List PrefixCut := [⟨64,192901967,192902078⟩]
theorem checked63525 : checkPrefixCuts (2^48) 8330280961 10 Manual.Count131072.C063525.packed 64 cuts63525 = true := by
 decide +kernel
def cuts63526 : List PrefixCut := [⟨48,146811613,146811695⟩,
⟨64,196142628,196142740⟩]
theorem checked63526 : checkPrefixCuts (2^48) 8330412033 10 Manual.Count131072.C063526.packed 64 cuts63526 = true := by
 decide +kernel
def pointBounds63526 : List (Nat × Nat × Nat) := [(8330510336,114621181752887,114621570564051)]
theorem point_links_checked63526 : (cuts63526.take 1).map (fun c => (8330412033-1+2*2^10*c.k,114621034941274+c.lower,114621423752356+c.upper)) = pointBounds63526 := by
 decide +kernel
def cuts63527 : List PrefixCut := [⟨64,195396220,195396332⟩]
theorem checked63527 : checkPrefixCuts (2^48) 8330543105 10 Manual.Count131072.C063527.packed 64 cuts63527 = true := by
 decide +kernel
def cuts63528 : List PrefixCut := [⟨48,143630967,143631057⟩,
⟨64,192690133,192690251⟩]
theorem checked63528 : checkPrefixCuts (2^48) 8330674177 10 Manual.Count131072.C063528.packed 64 cuts63528 = true := by
 decide +kernel
def pointBounds63528 : List (Nat × Nat × Nat) := [(8330772480,114621570111089,114621958922485)]
theorem point_links_checked63528 : (cuts63528.take 1).map (fun c => (8330674177-1+2*2^10*c.k,114621426480122+c.lower,114621815291428+c.upper)) = pointBounds63528 := by
 decide +kernel
def cuts63529 : List PrefixCut := [⟨64,196133377,196133489⟩]
theorem checked63529 : checkPrefixCuts (2^48) 8330805249 10 Manual.Count131072.C063529.packed 64 cuts63529 = true := by
 decide +kernel
def cuts63530 : List PrefixCut := [⟨48,142883133,142883217⟩,
⟨64,191062311,191062422⟩]
theorem checked63530 : checkPrefixCuts (2^48) 8330936321 10 Manual.Count131072.C063530.packed 64 cuts63530 = true := by
 decide +kernel
def pointBounds63530 : List (Nat × Nat × Nat) := [(8331034624,114621958186765,114622346998385)]
theorem point_links_checked63530 : (cuts63530.take 1).map (fun c => (8330936321-1+2*2^10*c.k,114621815303632+c.lower,114622204115168+c.upper)) = pointBounds63530 := by
 decide +kernel
def cuts63531 : List PrefixCut := [⟨64,193424336,193424445⟩]
theorem checked63531 : checkPrefixCuts (2^48) 8331067393 10 Manual.Count131072.C063531.packed 64 cuts63531 = true := by
 decide +kernel
def cuts63532 : List PrefixCut := [⟨48,145480118,145480203⟩,
⟨64,192880722,192880836⟩]
theorem checked63532 : checkPrefixCuts (2^48) 8331198465 10 Manual.Count131072.C063532.packed 64 cuts63532 = true := by
 decide +kernel
def pointBounds63532 : List (Nat × Nat × Nat) := [(8331296768,114622345270397,114622734082238)]
theorem point_links_checked63532 : (cuts63532.take 1).map (fun c => (8331198465-1+2*2^10*c.k,114622199790279+c.lower,114622588602035+c.upper)) = pointBounds63532 := by
 decide +kernel
def cuts63533 : List PrefixCut := [⟨64,193316889,193316999⟩]
theorem checked63533 : checkPrefixCuts (2^48) 8331329537 10 Manual.Count131072.C063533.packed 64 cuts63533 = true := by
 decide +kernel
def cuts63534 : List PrefixCut := [⟨48,145239052,145239137⟩,
⟨64,193280060,193280175⟩]
theorem checked63534 : checkPrefixCuts (2^48) 8331460609 10 Manual.Count131072.C063534.packed 64 cuts63534 = true := by
 decide +kernel
def pointBounds63534 : List (Nat × Nat × Nat) := [(8331558912,114622731226942,114623120039007)]
theorem point_links_checked63534 : (cuts63534.take 1).map (fun c => (8331460609-1+2*2^10*c.k,114622585987890+c.lower,114622974799870+c.upper)) = pointBounds63534 := by
 decide +kernel
def cuts63535 : List PrefixCut := [⟨64,191249976,191250088⟩]
theorem checked63535 : checkPrefixCuts (2^48) 8331591681 10 Manual.Count131072.C063535.packed 64 cuts63535 = true := by
 decide +kernel
def cuts63536 : List PrefixCut := [⟨48,145842584,145842669⟩,
⟨64,193510472,193510583⟩]
theorem checked63536 : checkPrefixCuts (2^48) 8331722753 10 Manual.Count131072.C063536.packed 64 cuts63536 = true := by
 decide +kernel
def pointBounds63536 : List (Nat × Nat × Nat) := [(8331821056,114623116360510,114623505172802)]
theorem point_links_checked63536 : (cuts63536.take 1).map (fun c => (8331722753-1+2*2^10*c.k,114622970517926+c.lower,114623359330133+c.upper)) = pointBounds63536 := by
 decide +kernel
def cuts63537 : List PrefixCut := [⟨64,194554685,194554795⟩]
theorem checked63537 : checkPrefixCuts (2^48) 8331853825 10 Manual.Count131072.C063537.packed 64 cuts63537 = true := by
 decide +kernel
def cuts63538 : List PrefixCut := [⟨48,145837997,145838083⟩,
⟨64,193267908,193268021⟩]
theorem checked63538 : checkPrefixCuts (2^48) 8331984897 10 Manual.Count131072.C063538.packed 64 cuts63538 = true := by
 decide +kernel
def pointBounds63538 : List (Nat × Nat × Nat) := [(8332083200,114623504421080,114623893233594)]
theorem point_links_checked63538 : (cuts63538.take 1).map (fun c => (8331984897-1+2*2^10*c.k,114623358583083+c.lower,114623747395511+c.upper)) = pointBounds63538 := by
 decide +kernel
def cuts63539 : List PrefixCut := [⟨64,196440328,196440434⟩]
theorem checked63539 : checkPrefixCuts (2^48) 8332115969 10 Manual.Count131072.C063539.packed 64 cuts63539 = true := by
 decide +kernel
def cuts63540 : List PrefixCut := [⟨48,146475245,146475331⟩,
⟨64,194309035,194309151⟩]
theorem checked63540 : checkPrefixCuts (2^48) 8332247041 10 Manual.Count131072.C063540.packed 64 cuts63540 = true := by
 decide +kernel
def pointBounds63540 : List (Nat × Nat × Nat) := [(8332345344,114623894766564,114624283579297)]
theorem point_links_checked63540 : (cuts63540.take 1).map (fun c => (8332247041-1+2*2^10*c.k,114623748291319+c.lower,114624137103966+c.upper)) = pointBounds63540 := by
 decide +kernel
def cuts63541 : List PrefixCut := [⟨64,190826568,190826679⟩]
theorem checked63541 : checkPrefixCuts (2^48) 8332378113 10 Manual.Count131072.C063541.packed 64 cuts63541 = true := by
 decide +kernel
def cuts63542 : List PrefixCut := [⟨48,143970904,143970991⟩,
⟨64,193559741,193559857⟩]
theorem checked63542 : checkPrefixCuts (2^48) 8332509185 10 Manual.Count131072.C063542.packed 64 cuts63542 = true := by
 decide +kernel
def pointBounds63542 : List (Nat × Nat × Nat) := [(8332607488,114624277397826,114624666210787)]
theorem point_links_checked63542 : (cuts63542.take 1).map (fun c => (8332509185-1+2*2^10*c.k,114624133426922+c.lower,114624522239796+c.upper)) = pointBounds63542 := by
 decide +kernel
def cuts63543 : List PrefixCut := [⟨64,192678447,192678553⟩]
theorem checked63543 : checkPrefixCuts (2^48) 8332640257 10 Manual.Count131072.C063543.packed 64 cuts63543 = true := by
 decide +kernel
def cuts63544 : List PrefixCut := [⟨48,145418881,145418967⟩,
⟨64,194229247,194229362⟩]
theorem checked63544 : checkPrefixCuts (2^48) 8332771329 10 Manual.Count131072.C063544.packed 64 cuts63544 = true := by
 decide +kernel
def pointBounds63544 : List (Nat × Nat × Nat) := [(8332869632,114624665083991,114625053897173)]
theorem point_links_checked63544 : (cuts63544.take 1).map (fun c => (8332771329-1+2*2^10*c.k,114624519665110+c.lower,114624908478206+c.upper)) = pointBounds63544 := by
 decide +kernel
def cuts63545 : List PrefixCut := [⟨64,192976385,192976494⟩]
theorem checked63545 : checkPrefixCuts (2^48) 8332902401 10 Manual.Count131072.C063545.packed 64 cuts63545 = true := by
 decide +kernel
def cuts63546 : List PrefixCut := [⟨48,145988524,145988603⟩,
⟨64,194696022,194696126⟩]
theorem checked63546 : checkPrefixCuts (2^48) 8333033473 10 Manual.Count131072.C063546.packed 64 cuts63546 = true := by
 decide +kernel
def pointBounds63546 : List (Nat × Nat × Nat) := [(8333131776,114625052859266,114625441672665)]
theorem point_links_checked63546 : (cuts63546.take 1).map (fun c => (8333033473-1+2*2^10*c.k,114624906870742+c.lower,114625295684062+c.upper)) = pointBounds63546 := by
 decide +kernel
def cuts63547 : List PrefixCut := [⟨64,195841406,195841519⟩]
theorem checked63547 : checkPrefixCuts (2^48) 8333164545 10 Manual.Count131072.C063547.packed 64 cuts63547 = true := by
 decide +kernel
def cuts63548 : List PrefixCut := [⟨48,146794591,146794675⟩,
⟨64,195635661,195635774⟩]
theorem checked63548 : checkPrefixCuts (2^48) 8333295617 10 Manual.Count131072.C063548.packed 64 cuts63548 = true := by
 decide +kernel
def pointBounds63548 : List (Nat × Nat × Nat) := [(8333393920,114625444202761,114625833016382)]
theorem point_links_checked63548 : (cuts63548.take 1).map (fun c => (8333295617-1+2*2^10*c.k,114625297408170+c.lower,114625686221707+c.upper)) = pointBounds63548 := by
 decide +kernel
def cuts63549 : List PrefixCut := [⟨64,192322501,192322620⟩]
theorem checked63549 : checkPrefixCuts (2^48) 8333426689 10 Manual.Count131072.C063549.packed 64 cuts63549 = true := by
 decide +kernel
def cuts63550 : List PrefixCut := [⟨48,145878016,145878105⟩,
⟨64,193636734,193636849⟩]
theorem checked63550 : checkPrefixCuts (2^48) 8333557761 10 Manual.Count131072.C063550.packed 64 cuts63550 = true := by
 decide +kernel
def pointBounds63550 : List (Nat × Nat × Nat) := [(8333656064,114625831244348,114626220058206)]
theorem point_links_checked63550 : (cuts63550.take 1).map (fun c => (8333557761-1+2*2^10*c.k,114625685366332+c.lower,114626074180101+c.upper)) = pointBounds63550 := by
 decide +kernel
def cuts63551 : List PrefixCut := [⟨64,191472083,191472190⟩]
theorem checked63551 : checkPrefixCuts (2^48) 8333688833 10 Manual.Count131072.C063551.packed 64 cuts63551 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000110
