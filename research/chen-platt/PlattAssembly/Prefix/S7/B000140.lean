import PlattAssemblyKernel
import PlattCertificates.Count131072.C064480
import PlattCertificates.Count131072.C064481
import PlattCertificates.Count131072.C064482
import PlattCertificates.Count131072.C064483
import PlattCertificates.Count131072.C064484
import PlattCertificates.Count131072.C064485
import PlattCertificates.Count131072.C064486
import PlattCertificates.Count131072.C064487
import PlattCertificates.Count131072.C064488
import PlattCertificates.Count131072.C064489
import PlattCertificates.Count131072.C064490
import PlattCertificates.Count131072.C064491
import PlattCertificates.Count131072.C064492
import PlattCertificates.Count131072.C064493
import PlattCertificates.Count131072.C064494
import PlattCertificates.Count131072.C064495
import PlattCertificates.Count131072.C064496
import PlattCertificates.Count131072.C064497
import PlattCertificates.Count131072.C064498
import PlattCertificates.Count131072.C064499
import PlattCertificates.Count131072.C064500
import PlattCertificates.Count131072.C064501
import PlattCertificates.Count131072.C064502
import PlattCertificates.Count131072.C064503
import PlattCertificates.Count131072.C064504
import PlattCertificates.Count131072.C064505
import PlattCertificates.Count131072.C064506
import PlattCertificates.Count131072.C064507
import PlattCertificates.Count131072.C064508
import PlattCertificates.Count131072.C064509
import PlattCertificates.Count131072.C064510
import PlattCertificates.Count131072.C064511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000140
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64480 : List PrefixCut := [⟨50,147669777,147669856⟩,
⟨64,188781309,188781416⟩]
theorem checked64480 : checkPrefixCuts (2^48) 8455454721 10 Manual.Count131072.C064480.packed 64 cuts64480 = true := by
 decide +kernel
def pointBounds64480 : List (Nat × Nat × Nat) := [(8455557120,114804706776091,114805095693054)]
theorem point_links_checked64480 : (cuts64480.take 1).map (fun c => (8455454721-1+2*2^10*c.k,114804559106314+c.lower,114804948023198+c.upper)) = pointBounds64480 := by
 decide +kernel
def cuts64481 : List PrefixCut := [⟨64,192872857,192872972⟩]
theorem checked64481 : checkPrefixCuts (2^48) 8455585793 10 Manual.Count131072.C064481.packed 64 cuts64481 = true := by
 decide +kernel
def cuts64482 : List PrefixCut := [⟨52,156386594,156386680⟩,
⟨64,191837942,191838049⟩]
theorem checked64482 : checkPrefixCuts (2^48) 8455716865 10 Manual.Count131072.C064482.packed 64 cuts64482 = true := by
 decide +kernel
def pointBounds64482 : List (Nat × Nat × Nat) := [(8455823360,114805097147074,114805486064266)]
theorem point_links_checked64482 : (cuts64482.take 1).map (fun c => (8455716865-1+2*2^10*c.k,114804940760480+c.lower,114805329677586+c.upper)) = pointBounds64482 := by
 decide +kernel
def cuts64483 : List PrefixCut := [⟨64,194031933,194032047⟩]
theorem checked64483 : checkPrefixCuts (2^48) 8455847937 10 Manual.Count131072.C064483.packed 64 cuts64483 = true := by
 decide +kernel
def cuts64484 : List PrefixCut := [⟨54,161341453,161341547⟩,
⟨64,191931848,191931960⟩]
theorem checked64484 : checkPrefixCuts (2^48) 8455979009 10 Manual.Count131072.C064484.packed 64 cuts64484 = true := by
 decide +kernel
def pointBounds64484 : List (Nat × Nat × Nat) := [(8456089600,114805487971808,114805876889229)]
theorem point_links_checked64484 : (cuts64484.take 1).map (fun c => (8455979009-1+2*2^10*c.k,114805326630355+c.lower,114805715547682+c.upper)) = pointBounds64484 := by
 decide +kernel
def cuts64485 : List PrefixCut := [⟨64,188933104,188933215⟩]
theorem checked64485 : checkPrefixCuts (2^48) 8456110081 10 Manual.Count131072.C064485.packed 64 cuts64485 = true := by
 decide +kernel
def cuts64486 : List PrefixCut := [⟨56,167327861,167327958⟩,
⟨64,191093757,191093869⟩]
theorem checked64486 : checkPrefixCuts (2^48) 8456241153 10 Manual.Count131072.C064486.packed 64 cuts64486 = true := by
 decide +kernel
def pointBounds64486 : List (Nat × Nat × Nat) := [(8456355840,114805874823168,114806263740815)]
theorem point_links_checked64486 : (cuts64486.take 1).map (fun c => (8456241153-1+2*2^10*c.k,114805707495307+c.lower,114806096412857+c.upper)) = pointBounds64486 := by
 decide +kernel
def cuts64487 : List PrefixCut := [⟨64,191723227,191723327⟩]
theorem checked64487 : checkPrefixCuts (2^48) 8456372225 10 Manual.Count131072.C064487.packed 64 cuts64487 = true := by
 decide +kernel
def cuts64488 : List PrefixCut := [⟨58,170118538,170118639⟩,
⟨64,187260071,187260182⟩]
theorem checked64488 : checkPrefixCuts (2^48) 8456503297 10 Manual.Count131072.C064488.packed 64 cuts64488 = true := by
 decide +kernel
def pointBounds64488 : List (Nat × Nat × Nat) := [(8456622080,114806260430829,114806649348692)]
theorem point_links_checked64488 : (cuts64488.take 1).map (fun c => (8456503297-1+2*2^10*c.k,114806090312291+c.lower,114806479230053+c.upper)) = pointBounds64488 := by
 decide +kernel
def cuts64489 : List PrefixCut := [⟨64,186857772,186857878⟩]
theorem checked64489 : checkPrefixCuts (2^48) 8456634369 10 Manual.Count131072.C064489.packed 64 cuts64489 = true := by
 decide +kernel
def cuts64490 : List PrefixCut := [⟨60,179399411,179399506⟩,
⟨64,191015348,191015450⟩]
theorem checked64490 : checkPrefixCuts (2^48) 8456765441 10 Manual.Count131072.C064490.packed 64 cuts64490 = true := by
 decide +kernel
def pointBounds64490 : List (Nat × Nat × Nat) := [(8456888320,114806643829545,114807032747619)]
theorem point_links_checked64490 : (cuts64490.take 1).map (fun c => (8456765441-1+2*2^10*c.k,114806464430134+c.lower,114806853348113+c.upper)) = pointBounds64490 := by
 decide +kernel
def cuts64491 : List PrefixCut := [⟨64,190413278,190413387⟩]
theorem checked64491 : checkPrefixCuts (2^48) 8456896513 10 Manual.Count131072.C064491.packed 64 cuts64491 = true := by
 decide +kernel
def cuts64492 : List PrefixCut := [⟨62,185051869,185051972⟩,
⟨64,191209123,191209228⟩]
theorem checked64492 : checkPrefixCuts (2^48) 8457027585 10 Manual.Count131072.C064492.packed 64 cuts64492 = true := by
 decide +kernel
def pointBounds64492 : List (Nat × Nat × Nat) := [(8457154560,114807030910629,114807419828922)]
theorem point_links_checked64492 : (cuts64492.take 1).map (fun c => (8457027585-1+2*2^10*c.k,114806845858760+c.lower,114807234776950+c.upper)) = pointBounds64492 := by
 decide +kernel
def cuts64493 : List PrefixCut := [⟨64,190340818,190340931⟩]
theorem checked64493 : checkPrefixCuts (2^48) 8457158657 10 Manual.Count131072.C064493.packed 64 cuts64493 = true := by
 decide +kernel
def cuts64494 : List PrefixCut := [⟨64,191635848,191635957⟩]
theorem checked64494 : checkPrefixCuts (2^48) 8457289729 10 Manual.Count131072.C064494.packed 64 cuts64494 = true := by
 decide +kernel
def pointBounds64494 : List (Nat × Nat × Nat) := [(8457420800,114807419044549,114807807963066)]
theorem point_links_checked64494 : (cuts64494.take 1).map (fun c => (8457289729-1+2*2^10*c.k,114807227408701+c.lower,114807616327109+c.upper)) = pointBounds64494 := by
 decide +kernel
def cuts64495 : List PrefixCut := [⟨64,189469599,189469709⟩]
theorem checked64495 : checkPrefixCuts (2^48) 8457420801 10 Manual.Count131072.C064495.packed 64 cuts64495 = true := by
 decide +kernel
def cuts64496 : List PrefixCut := [⟨64,192195675,192195783⟩]
theorem checked64496 : checkPrefixCuts (2^48) 8457551873 10 Manual.Count131072.C064496.packed 64 cuts64496 = true := by
 decide +kernel
def cuts64497 : List PrefixCut := [⟨2,6456392,6456395⟩,
⟨64,193124540,193124647⟩]
theorem checked64497 : checkPrefixCuts (2^48) 8457682945 10 Manual.Count131072.C064497.packed 64 cuts64497 = true := by
 decide +kernel
def pointBounds64497 : List (Nat × Nat × Nat) := [(8457687040,114807807166215,114808196084953)]
theorem point_links_checked64497 : (cuts64497.take 1).map (fun c => (8457682945-1+2*2^10*c.k,114807800709823+c.lower,114808189628558+c.upper)) = pointBounds64497 := by
 decide +kernel
def cuts64498 : List PrefixCut := [⟨64,191890195,191890309⟩]
theorem checked64498 : checkPrefixCuts (2^48) 8457814017 10 Manual.Count131072.C064498.packed 64 cuts64498 = true := by
 decide +kernel
def cuts64499 : List PrefixCut := [⟨4,11947280,11947287⟩,
⟨64,192586092,192586203⟩]
theorem checked64499 : checkPrefixCuts (2^48) 8457945089 10 Manual.Count131072.C064499.packed 64 cuts64499 = true := by
 decide +kernel
def pointBounds64499 : List (Nat × Nat × Nat) := [(8457953280,114808197671838,114808586590801)]
theorem point_links_checked64499 : (cuts64499.take 1).map (fun c => (8457945089-1+2*2^10*c.k,114808185724558+c.lower,114808574643514+c.upper)) = pointBounds64499 := by
 decide +kernel
def cuts64500 : List PrefixCut := [⟨64,188855895,188856002⟩]
theorem checked64500 : checkPrefixCuts (2^48) 8458076161 10 Manual.Count131072.C064500.packed 64 cuts64500 = true := by
 decide +kernel
def cuts64501 : List PrefixCut := [⟨6,17970277,17970288⟩,
⟨64,189052653,189052761⟩]
theorem checked64501 : checkPrefixCuts (2^48) 8458207233 10 Manual.Count131072.C064501.packed 64 cuts64501 = true := by
 decide +kernel
def pointBounds64501 : List (Nat × Nat × Nat) := [(8458219520,114808585136822,114808974056007)]
theorem point_links_checked64501 : (cuts64501.take 1).map (fun c => (8458207233-1+2*2^10*c.k,114808567166545+c.lower,114808956085719+c.upper)) = pointBounds64501 := by
 decide +kernel
def cuts64502 : List PrefixCut := [⟨64,190780145,190780258⟩]
theorem checked64502 : checkPrefixCuts (2^48) 8458338305 10 Manual.Count131072.C064502.packed 64 cuts64502 = true := by
 decide +kernel
def cuts64503 : List PrefixCut := [⟨8,23393908,23393922⟩,
⟨64,191575845,191575962⟩]
theorem checked64503 : checkPrefixCuts (2^48) 8458469377 10 Manual.Count131072.C064503.packed 64 cuts64503 = true := by
 decide +kernel
def pointBounds64503 : List (Nat × Nat × Nat) := [(8458485760,114808970393251,114809359312660)]
theorem point_links_checked64503 : (cuts64503.take 1).map (fun c => (8458469377-1+2*2^10*c.k,114808946999343+c.lower,114809335918738+c.upper)) = pointBounds64503 := by
 decide +kernel
def cuts64504 : List PrefixCut := [⟨64,189709386,189709495⟩]
theorem checked64504 : checkPrefixCuts (2^48) 8458600449 10 Manual.Count131072.C064504.packed 64 cuts64504 = true := by
 decide +kernel
def cuts64505 : List PrefixCut := [⟨10,28584267,28584285⟩,
⟨64,189174015,189174127⟩]
theorem checked64505 : checkPrefixCuts (2^48) 8458731521 10 Manual.Count131072.C064505.packed 64 cuts64505 = true := by
 decide +kernel
def pointBounds64505 : List (Nat × Nat × Nat) := [(8458752000,114809356868841,114809745788480)]
theorem point_links_checked64505 : (cuts64505.take 1).map (fun c => (8458731521-1+2*2^10*c.k,114809328284574+c.lower,114809717204195+c.upper)) = pointBounds64505 := by
 decide +kernel
def cuts64506 : List PrefixCut := [⟨64,187108025,187108132⟩]
theorem checked64506 : checkPrefixCuts (2^48) 8458862593 10 Manual.Count131072.C064506.packed 64 cuts64506 = true := by
 decide +kernel
def cuts64507 : List PrefixCut := [⟨12,37234921,37234939⟩,
⟨64,193194457,193194563⟩]
theorem checked64507 : checkPrefixCuts (2^48) 8458993665 10 Manual.Count131072.C064507.packed 64 cuts64507 = true := by
 decide +kernel
def pointBounds64507 : List (Nat × Nat × Nat) := [(8459018240,114809741801535,114810130721393)]
theorem point_links_checked64507 : (cuts64507.take 1).map (fun c => (8458993665-1+2*2^10*c.k,114809704566614+c.lower,114810093486454+c.upper)) = pointBounds64507 := by
 decide +kernel
def cuts64508 : List PrefixCut := [⟨64,189298347,189298453⟩]
theorem checked64508 : checkPrefixCuts (2^48) 8459124737 10 Manual.Count131072.C064508.packed 64 cuts64508 = true := by
 decide +kernel
def cuts64509 : List PrefixCut := [⟨14,42524347,42524369⟩,
⟨64,191657853,191657962⟩]
theorem checked64509 : checkPrefixCuts (2^48) 8459255809 10 Manual.Count131072.C064509.packed 64 cuts64509 = true := by
 decide +kernel
def pointBounds64509 : List (Nat × Nat × Nat) := [(8459284480,114810129583765,114810518503839)]
theorem point_links_checked64509 : (cuts64509.take 1).map (fun c => (8459255809-1+2*2^10*c.k,114810087059418+c.lower,114810475979470+c.upper)) = pointBounds64509 := by
 decide +kernel
def cuts64510 : List PrefixCut := [⟨64,191355424,191355533⟩]
theorem checked64510 : checkPrefixCuts (2^48) 8459386881 10 Manual.Count131072.C064510.packed 64 cuts64510 = true := by
 decide +kernel
def cuts64511 : List PrefixCut := [⟨16,47913258,47913282⟩,
⟨64,190254460,190254570⟩]
theorem checked64511 : checkPrefixCuts (2^48) 8459517953 10 Manual.Count131072.C064511.packed 64 cuts64511 = true := by
 decide +kernel
def pointBounds64511 : List (Nat × Nat × Nat) := [(8459550720,114810517985953,114810906906247)]
theorem point_links_checked64511 : (cuts64511.take 1).map (fun c => (8459517953-1+2*2^10*c.k,114810470072695+c.lower,114810858992965+c.upper)) = pointBounds64511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000140
