import PlattAssemblyKernel
import PlattCertificates.Count131072.C059376
import PlattCertificates.Count131072.C059377
import PlattCertificates.Count131072.C059378
import PlattCertificates.Count131072.C059379
import PlattCertificates.Count131072.C059380
import PlattCertificates.Count131072.C059381
import PlattCertificates.Count131072.C059382
import PlattCertificates.Count131072.C059383
import PlattCertificates.Count131072.C059384
import PlattCertificates.Count131072.C059385
import PlattCertificates.Count131072.C059386
import PlattCertificates.Count131072.C059387
import PlattCertificates.Count131072.C059388
import PlattCertificates.Count131072.C059389
import PlattCertificates.Count131072.C059390
import PlattCertificates.Count131072.C059391
import PlattCertificates.Count131072.C059392
import PlattCertificates.Count131072.C059393
import PlattCertificates.Count131072.C059394
import PlattCertificates.Count131072.C059395
import PlattCertificates.Count131072.C059396
import PlattCertificates.Count131072.C059397
import PlattCertificates.Count131072.C059398
import PlattCertificates.Count131072.C059399
import PlattCertificates.Count131072.C059400
import PlattCertificates.Count131072.C059401
import PlattCertificates.Count131072.C059402
import PlattCertificates.Count131072.C059403
import PlattCertificates.Count131072.C059404
import PlattCertificates.Count131072.C059405
import PlattCertificates.Count131072.C059406
import PlattCertificates.Count131072.C059407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000293
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59376 : List PrefixCut := [⟨64,208290296,208290407⟩]
theorem checked59376 : checkPrefixCuts (2^48) 7786463233 10 Manual.Count131072.C059376.packed 64 cuts59376 = true := by
 decide +kernel
def cuts59377 : List PrefixCut := [⟨2,7265878,7265881⟩,
⟨64,209118219,209118340⟩]
theorem checked59377 : checkPrefixCuts (2^48) 7786594305 10 Manual.Count131072.C059377.packed 64 cuts59377 = true := by
 decide +kernel
def pointBounds59377 : List (Nat × Nat × Nat) := [(7786598400,113787895704305,113788284037974)]
theorem point_links_checked59377 : (cuts59377.take 1).map (fun c => (7786594305-1+2*2^10*c.k,113787888438427+c.lower,113788276772093+c.upper)) = pointBounds59377 := by
 decide +kernel
def cuts59378 : List PrefixCut := [⟨57,187137030,187137139⟩,
⟨64,209078544,209078665⟩]
theorem checked59378 : checkPrefixCuts (2^48) 7786725377 10 Manual.Count131072.C059378.packed 64 cuts59378 = true := by
 decide +kernel
def pointBounds59378 : List (Nat × Nat × Nat) := [(7786842112,113788284693676,113788673027572)]
theorem point_links_checked59378 : (cuts59378.take 1).map (fun c => (7786725377-1+2*2^10*c.k,113788097556646+c.lower,113788485890433+c.upper)) = pointBounds59378 := by
 decide +kernel
def cuts59379 : List PrefixCut := [⟨64,207665266,207665387⟩]
theorem checked59379 : checkPrefixCuts (2^48) 7786856449 10 Manual.Count131072.C059379.packed 64 cuts59379 = true := by
 decide +kernel
def cuts59380 : List PrefixCut := [⟨48,154779732,154779821⟩,
⟨64,205890592,205890711⟩]
theorem checked59380 : checkPrefixCuts (2^48) 7786987521 10 Manual.Count131072.C059380.packed 64 cuts59380 = true := by
 decide +kernel
def pointBounds59380 : List (Nat × Nat × Nat) := [(7787085824,113788669080188,113789057414306)]
theorem point_links_checked59380 : (cuts59380.take 1).map (fun c => (7786987521-1+2*2^10*c.k,113788514300456+c.lower,113788902634485+c.upper)) = pointBounds59380 := by
 decide +kernel
def cuts59381 : List PrefixCut := [⟨64,204079835,204079954⟩]
theorem checked59381 : checkPrefixCuts (2^48) 7787118593 10 Manual.Count131072.C059381.packed 64 cuts59381 = true := by
 decide +kernel
def cuts59382 : List PrefixCut := [⟨39,125460771,125460846⟩,
⟨64,205522219,205522337⟩]
theorem checked59382 : checkPrefixCuts (2^48) 7787249665 10 Manual.Count131072.C059382.packed 64 cuts59382 = true := by
 decide +kernel
def pointBounds59382 : List (Nat × Nat × Nat) := [(7787329536,113789049731654,113789438065996)]
theorem point_links_checked59382 : (cuts59382.take 1).map (fun c => (7787249665-1+2*2^10*c.k,113788924270883+c.lower,113789312605150+c.upper)) = pointBounds59382 := by
 decide +kernel
def cuts59383 : List PrefixCut := [⟨64,206711534,206711651⟩]
theorem checked59383 : checkPrefixCuts (2^48) 7787380737 10 Manual.Count131072.C059383.packed 64 cuts59383 = true := by
 decide +kernel
def cuts59384 : List PrefixCut := [⟨30,97372617,97372671⟩,
⟨64,209057418,209057537⟩]
theorem checked59384 : checkPrefixCuts (2^48) 7787511809 10 Manual.Count131072.C059384.packed 64 cuts59384 = true := by
 decide +kernel
def pointBounds59384 : List (Nat × Nat × Nat) := [(7787573248,113789433877253,113789822211809)]
theorem point_links_checked59384 : (cuts59384.take 1).map (fun c => (7787511809-1+2*2^10*c.k,113789336504636+c.lower,113789724839138+c.upper)) = pointBounds59384 := by
 decide +kernel
def cuts59385 : List PrefixCut := [⟨64,209053898,209054019⟩]
theorem checked59385 : checkPrefixCuts (2^48) 7787642881 10 Manual.Count131072.C059385.packed 64 cuts59385 = true := by
 decide +kernel
def cuts59386 : List PrefixCut := [⟨21,70334432,70334471⟩,
⟨64,210279247,210279362⟩]
theorem checked59386 : checkPrefixCuts (2^48) 7787773953 10 Manual.Count131072.C059386.packed 64 cuts59386 = true := by
 decide +kernel
def pointBounds59386 : List (Nat × Nat × Nat) := [(7787816960,113789824950384,113790213285165)]
theorem point_links_checked59386 : (cuts59386.take 1).map (fun c => (7787773953-1+2*2^10*c.k,113789754615952+c.lower,113790142950694+c.upper)) = pointBounds59386 := by
 decide +kernel
def cuts59387 : List PrefixCut := [⟨64,208866143,208866261⟩]
theorem checked59387 : checkPrefixCuts (2^48) 7787905025 10 Manual.Count131072.C059387.packed 64 cuts59387 = true := by
 decide +kernel
def cuts59388 : List PrefixCut := [⟨12,39394675,39394697⟩,
⟨64,208248239,208248352⟩]
theorem checked59388 : checkPrefixCuts (2^48) 7788036097 10 Manual.Count131072.C059388.packed 64 cuts59388 = true := by
 decide +kernel
def pointBounds59388 : List (Nat × Nat × Nat) := [(7788060672,113790213156017,113790601491014)]
theorem point_links_checked59388 : (cuts59388.take 1).map (fun c => (7788036097-1+2*2^10*c.k,113790173761342+c.lower,113790562096317+c.upper)) = pointBounds59388 := by
 decide +kernel
def cuts59389 : List PrefixCut := [⟨64,209184376,209184498⟩]
theorem checked59389 : checkPrefixCuts (2^48) 7788167169 10 Manual.Count131072.C059389.packed 64 cuts59389 = true := by
 decide +kernel
def cuts59390 : List PrefixCut := [⟨3,9215886,9215892⟩,
⟨64,204193491,204193605⟩]
theorem checked59390 : checkPrefixCuts (2^48) 7788298241 10 Manual.Count131072.C059390.packed 64 cuts59390 = true := by
 decide +kernel
def pointBounds59390 : List (Nat × Nat × Nat) := [(7788304384,113790600409843,113790988745059)]
theorem point_links_checked59390 : (cuts59390.take 1).map (fun c => (7788298241-1+2*2^10*c.k,113790591193957+c.lower,113790979529167+c.upper)) = pointBounds59390 := by
 decide +kernel
def cuts59391 : List PrefixCut := [⟨58,188035701,188035813⟩,
⟨64,207261944,207262068⟩]
theorem checked59391 : checkPrefixCuts (2^48) 7788429313 10 Manual.Count131072.C059391.packed 64 cuts59391 = true := by
 decide +kernel
def pointBounds59391 : List (Nat × Nat × Nat) := [(7788548096,113790983423149,113791371758585)]
theorem point_links_checked59391 : (cuts59391.take 1).map (fun c => (7788429313-1+2*2^10*c.k,113790795387448+c.lower,113791183722772+c.upper)) = pointBounds59391 := by
 decide +kernel
def cuts59392 : List PrefixCut := [⟨64,205740611,205740726⟩]
theorem checked59392 : checkPrefixCuts (2^48) 7788560385 10 Manual.Count131072.C059392.packed 64 cuts59392 = true := by
 decide +kernel
def cuts59393 : List PrefixCut := [⟨49,156588928,156589021⟩,
⟨64,206749003,206749126⟩]
theorem checked59393 : checkPrefixCuts (2^48) 7788691457 10 Manual.Count131072.C059393.packed 64 cuts59393 = true := by
 decide +kernel
def pointBounds59393 : List (Nat × Nat × Nat) := [(7788791808,113791364978931,113791753314587)]
theorem point_links_checked59393 : (cuts59393.take 1).map (fun c => (7788691457-1+2*2^10*c.k,113791208390003+c.lower,113791596725566+c.upper)) = pointBounds59393 := by
 decide +kernel
def cuts59394 : List PrefixCut := [⟨64,204830224,204830341⟩]
theorem checked59394 : checkPrefixCuts (2^48) 7788822529 10 Manual.Count131072.C059394.packed 64 cuts59394 = true := by
 decide +kernel
def cuts59395 : List PrefixCut := [⟨40,131034632,131034708⟩,
⟨64,208404395,208404516⟩]
theorem checked59395 : checkPrefixCuts (2^48) 7788953601 10 Manual.Count131072.C059395.packed 64 cuts59395 = true := by
 decide +kernel
def pointBounds59395 : List (Nat × Nat × Nat) := [(7789035520,113791751003862,113792139339741)]
theorem point_links_checked59395 : (cuts59395.take 1).map (fun c => (7788953601-1+2*2^10*c.k,113791619969230+c.lower,113792008305033+c.upper)) = pointBounds59395 := by
 decide +kernel
def cuts59396 : List PrefixCut := [⟨64,207352914,207353033⟩]
theorem checked59396 : checkPrefixCuts (2^48) 7789084673 10 Manual.Count131072.C059396.packed 64 cuts59396 = true := by
 decide +kernel
def cuts59397 : List PrefixCut := [⟨31,99591756,99591812⟩,
⟨64,207277142,207277261⟩]
theorem checked59397 : checkPrefixCuts (2^48) 7789215745 10 Manual.Count131072.C059397.packed 64 cuts59397 = true := by
 decide +kernel
def pointBounds59397 : List (Nat × Nat × Nat) := [(7789279232,113792135318295,113792523654394)]
theorem point_links_checked59397 : (cuts59397.take 1).map (fun c => (7789215745-1+2*2^10*c.k,113792035726539+c.lower,113792424062582+c.upper)) = pointBounds59397 := by
 decide +kernel
def cuts59398 : List PrefixCut := [⟨64,212657860,212657980⟩]
theorem checked59398 : checkPrefixCuts (2^48) 7789346817 10 Manual.Count131072.C059398.packed 64 cuts59398 = true := by
 decide +kernel
def cuts59399 : List PrefixCut := [⟨22,70319034,70319075⟩,
⟨64,205933179,205933297⟩]
theorem checked59399 : checkPrefixCuts (2^48) 7789477889 10 Manual.Count131072.C059399.packed 64 cuts59399 = true := by
 decide +kernel
def pointBounds59399 : List (Nat × Nat × Nat) := [(7789522944,113792525980575,113792914316898)]
theorem point_links_checked59399 : (cuts59399.take 1).map (fun c => (7789477889-1+2*2^10*c.k,113792455661541+c.lower,113792843997823+c.upper)) = pointBounds59399 := by
 decide +kernel
def cuts59400 : List PrefixCut := [⟨64,209217944,209218068⟩]
theorem checked59400 : checkPrefixCuts (2^48) 7789608961 10 Manual.Count131072.C059400.packed 64 cuts59400 = true := by
 decide +kernel
def cuts59401 : List PrefixCut := [⟨13,43577596,43577621⟩,
⟨64,211201788,211201909⟩]
theorem checked59401 : checkPrefixCuts (2^48) 7789740033 10 Manual.Count131072.C059401.packed 64 cuts59401 = true := by
 decide +kernel
def pointBounds59401 : List (Nat × Nat × Nat) := [(7789766656,113792914390260,113793302726809)]
theorem point_links_checked59401 : (cuts59401.take 1).map (fun c => (7789740033-1+2*2^10*c.k,113792870812664+c.lower,113793259149188+c.upper)) = pointBounds59401 := by
 decide +kernel
def cuts59402 : List PrefixCut := [⟨64,203935467,203935584⟩]
theorem checked59402 : checkPrefixCuts (2^48) 7789871105 10 Manual.Count131072.C059402.packed 64 cuts59402 = true := by
 decide +kernel
def cuts59403 : List PrefixCut := [⟨4,13766605,13766613⟩,
⟨64,206172244,206172358⟩]
theorem checked59403 : checkPrefixCuts (2^48) 7790002177 10 Manual.Count131072.C059403.packed 64 cuts59403 = true := by
 decide +kernel
def pointBounds59403 : List (Nat × Nat × Nat) := [(7790010368,113793299716524,113793688053294)]
theorem point_links_checked59403 : (cuts59403.take 1).map (fun c => (7790002177-1+2*2^10*c.k,113793285949919+c.lower,113793674286681+c.upper)) = pointBounds59403 := by
 decide +kernel
def cuts59404 : List PrefixCut := [⟨59,191463208,191463317⟩,
⟨64,207469528,207469645⟩]
theorem checked59404 : checkPrefixCuts (2^48) 7790133249 10 Manual.Count131072.C059404.packed 64 cuts59404 = true := by
 decide +kernel
def pointBounds59404 : List (Nat × Nat × Nat) := [(7790254080,113793683585371,113794071922356)]
theorem point_links_checked59404 : (cuts59404.take 1).map (fun c => (7790133249-1+2*2^10*c.k,113793492122163+c.lower,113793880459039+c.upper)) = pointBounds59404 := by
 decide +kernel
def cuts59405 : List PrefixCut := [⟨64,206779539,206779656⟩]
theorem checked59405 : checkPrefixCuts (2^48) 7790264321 10 Manual.Count131072.C059405.packed 64 cuts59405 = true := by
 decide +kernel
def cuts59406 : List PrefixCut := [⟨50,161829755,161829851⟩,
⟨64,207679326,207679447⟩]
theorem checked59406 : checkPrefixCuts (2^48) 7790395393 10 Manual.Count131072.C059406.packed 64 cuts59406 = true := by
 decide +kernel
def pointBounds59406 : List (Nat × Nat × Nat) := [(7790497792,113794068200985,113794456538191)]
theorem point_links_checked59406 : (cuts59406.take 1).map (fun c => (7790395393-1+2*2^10*c.k,113793906371230+c.lower,113794294708340+c.upper)) = pointBounds59406 := by
 decide +kernel
def cuts59407 : List PrefixCut := [⟨64,207964864,207964984⟩]
theorem checked59407 : checkPrefixCuts (2^48) 7790526465 10 Manual.Count131072.C059407.packed 64 cuts59407 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000293
