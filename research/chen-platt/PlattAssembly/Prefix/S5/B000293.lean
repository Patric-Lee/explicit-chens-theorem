import PlattAssemblyKernel
import PlattCertificates.Count131072.C049376
import PlattCertificates.Count131072.C049377
import PlattCertificates.Count131072.C049378
import PlattCertificates.Count131072.C049379
import PlattCertificates.Count131072.C049380
import PlattCertificates.Count131072.C049381
import PlattCertificates.Count131072.C049382
import PlattCertificates.Count131072.C049383
import PlattCertificates.Count131072.C049384
import PlattCertificates.Count131072.C049385
import PlattCertificates.Count131072.C049386
import PlattCertificates.Count131072.C049387
import PlattCertificates.Count131072.C049388
import PlattCertificates.Count131072.C049389
import PlattCertificates.Count131072.C049390
import PlattCertificates.Count131072.C049391
import PlattCertificates.Count131072.C049392
import PlattCertificates.Count131072.C049393
import PlattCertificates.Count131072.C049394
import PlattCertificates.Count131072.C049395
import PlattCertificates.Count131072.C049396
import PlattCertificates.Count131072.C049397
import PlattCertificates.Count131072.C049398
import PlattCertificates.Count131072.C049399
import PlattCertificates.Count131072.C049400
import PlattCertificates.Count131072.C049401
import PlattCertificates.Count131072.C049402
import PlattCertificates.Count131072.C049403
import PlattCertificates.Count131072.C049404
import PlattCertificates.Count131072.C049405
import PlattCertificates.Count131072.C049406
import PlattCertificates.Count131072.C049407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000293
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49376 : List PrefixCut := [⟨64,250144511,250144656⟩]
theorem checked49376 : checkPrefixCuts (2^48) 6475743233 10 Manual.Count131072.C049376.packed 64 cuts49376 = true := by
 decide +kernel
def cuts49377 : List PrefixCut := [⟨27,108140846,108140910⟩,
⟨64,254181657,254181805⟩]
theorem checked49377 : checkPrefixCuts (2^48) 6475874305 10 Manual.Count131072.C049377.packed 64 cuts49377 = true := by
 decide +kernel
def pointBounds49377 : List (Nat × Nat × Nat) := [(6475929600,111500822353966,111501209387113)]
theorem point_links_checked49377 : (cuts49377.take 1).map (fun c => (6475874305-1+2*2^10*c.k,111500714213120+c.lower,111501101246203+c.upper)) = pointBounds49377 := by
 decide +kernel
def cuts49378 : List PrefixCut := [⟨62,242397882,242398019⟩,
⟨64,250047442,250047583⟩]
theorem checked49378 : checkPrefixCuts (2^48) 6476005377 10 Manual.Count131072.C049378.packed 64 cuts49378 = true := by
 decide +kernel
def pointBounds49378 : List (Nat × Nat × Nat) := [(6476132352,111501210792659,111501597826027)]
theorem point_links_checked49378 : (cuts49378.take 1).map (fun c => (6476005377-1+2*2^10*c.k,111500968394777+c.lower,111501355428008+c.upper)) = pointBounds49378 := by
 decide +kernel
def cuts49379 : List PrefixCut := [⟨64,254649484,254649631⟩]
theorem checked49379 : checkPrefixCuts (2^48) 6476136449 10 Manual.Count131072.C049379.packed 64 cuts49379 = true := by
 decide +kernel
def cuts49380 : List PrefixCut := [⟨33,131038817,131038893⟩,
⟨64,255252789,255252936⟩]
theorem checked49380 : checkPrefixCuts (2^48) 6476267521 10 Manual.Count131072.C049380.packed 64 cuts49380 = true := by
 decide +kernel
def pointBounds49380 : List (Nat × Nat × Nat) := [(6476335104,111501604130520,111501991164115)]
theorem point_links_checked49380 : (cuts49380.take 1).map (fun c => (6476267521-1+2*2^10*c.k,111501473091703+c.lower,111501860125222+c.upper)) = pointBounds49380 := by
 decide +kernel
def cuts49381 : List PrefixCut := [⟨64,256377626,256377772⟩]
theorem checked49381 : checkPrefixCuts (2^48) 6476398593 10 Manual.Count131072.C049381.packed 64 cuts49381 = true := by
 decide +kernel
def cuts49382 : List PrefixCut := [⟨4,15776246,15776254⟩,
⟨64,250852978,250853122⟩]
theorem checked49382 : checkPrefixCuts (2^48) 6476529665 10 Manual.Count131072.C049382.packed 64 cuts49382 = true := by
 decide +kernel
def pointBounds49382 : List (Nat × Nat × Nat) := [(6476537856,111502000498364,111502387532184)]
theorem point_links_checked49382 : (cuts49382.take 1).map (fun c => (6476529665-1+2*2^10*c.k,111501984722118+c.lower,111502371755930+c.upper)) = pointBounds49382 := by
 decide +kernel
def cuts49383 : List PrefixCut := [⟨39,156932654,156932743⟩,
⟨64,254715785,254715930⟩]
theorem checked49383 : checkPrefixCuts (2^48) 6476660737 10 Manual.Count131072.C049383.packed 64 cuts49383 = true := by
 decide +kernel
def pointBounds49383 : List (Nat × Nat × Nat) := [(6476740608,111502392507750,111502779541795)]
theorem point_links_checked49383 : (cuts49383.take 1).map (fun c => (6476660737-1+2*2^10*c.k,111502235575096+c.lower,111502622609052+c.upper)) = pointBounds49383 := by
 decide +kernel
def cuts49384 : List PrefixCut := [⟨64,252668065,252668208⟩]
theorem checked49384 : checkPrefixCuts (2^48) 6476791809 10 Manual.Count131072.C049384.packed 64 cuts49384 = true := by
 decide +kernel
def cuts49385 : List PrefixCut := [⟨10,39286078,39286102⟩,
⟨64,250359707,250359846⟩]
theorem checked49385 : checkPrefixCuts (2^48) 6476922881 10 Manual.Count131072.C049385.packed 64 cuts49385 = true := by
 decide +kernel
def pointBounds49385 : List (Nat × Nat × Nat) := [(6476943360,111502782245024,111503169279292)]
theorem point_links_checked49385 : (cuts49385.take 1).map (fun c => (6476922881-1+2*2^10*c.k,111502742958946+c.lower,111503129993190+c.upper)) = pointBounds49385 := by
 decide +kernel
def cuts49386 : List PrefixCut := [⟨45,178781811,178781917⟩,
⟨64,253831173,253831319⟩]
theorem checked49386 : checkPrefixCuts (2^48) 6477053953 10 Manual.Count131072.C049386.packed 64 cuts49386 = true := by
 decide +kernel
def pointBounds49386 : List (Nat × Nat × Nat) := [(6477146112,111503172100464,111503559134953)]
theorem point_links_checked49386 : (cuts49386.take 1).map (fun c => (6477053953-1+2*2^10*c.k,111502993318653+c.lower,111503380353036+c.upper)) = pointBounds49386 := by
 decide +kernel
def cuts49387 : List PrefixCut := [⟨64,256520297,256520444⟩]
theorem checked49387 : checkPrefixCuts (2^48) 6477185025 10 Manual.Count131072.C049387.packed 64 cuts49387 = true := by
 decide +kernel
def cuts49388 : List PrefixCut := [⟨16,64009766,64009802⟩,
⟨64,253038717,253038862⟩]
theorem checked49388 : checkPrefixCuts (2^48) 6477316097 10 Manual.Count131072.C049388.packed 64 cuts49388 = true := by
 decide +kernel
def pointBounds49388 : List (Nat × Nat × Nat) := [(6477348864,111503567679889,111503954714601)]
theorem point_links_checked49388 : (cuts49388.take 1).map (fun c => (6477316097-1+2*2^10*c.k,111503503670123+c.lower,111503890704799+c.upper)) = pointBounds49388 := by
 decide +kernel
def cuts49389 : List PrefixCut := [⟨51,198672863,198672978⟩,
⟨64,249818004,249818150⟩]
theorem checked49389 : checkPrefixCuts (2^48) 6477447169 10 Manual.Count131072.C049389.packed 64 cuts49389 = true := by
 decide +kernel
def pointBounds49389 : List (Nat × Nat × Nat) := [(6477551616,111503955381703,111504342416639)]
theorem point_links_checked49389 : (cuts49389.take 1).map (fun c => (6477447169-1+2*2^10*c.k,111503756708840+c.lower,111504143743661+c.upper)) = pointBounds49389 := by
 decide +kernel
def cuts49390 : List PrefixCut := [⟨64,252593935,252594083⟩]
theorem checked49390 : checkPrefixCuts (2^48) 6477578241 10 Manual.Count131072.C049390.packed 64 cuts49390 = true := by
 decide +kernel
def cuts49391 : List PrefixCut := [⟨22,86514312,86514365⟩,
⟨64,251415608,251415756⟩]
theorem checked49391 : checkPrefixCuts (2^48) 6477709313 10 Manual.Count131072.C049391.packed 64 cuts49391 = true := by
 decide +kernel
def pointBounds49391 : List (Nat × Nat × Nat) := [(6477754368,111504345635091,111504732670259)]
theorem point_links_checked49391 : (cuts49391.take 1).map (fun c => (6477709313-1+2*2^10*c.k,111504259120779+c.lower,111504646155894+c.upper)) = pointBounds49391 := by
 decide +kernel
def cuts49392 : List PrefixCut := [⟨57,224123225,224123349⟩,
⟨64,250454612,250454751⟩]
theorem checked49392 : checkPrefixCuts (2^48) 6477840385 10 Manual.Count131072.C049392.packed 64 cuts49392 = true := by
 decide +kernel
def pointBounds49392 : List (Nat × Nat × Nat) := [(6477957120,111504734659612,111505121694999)]
theorem point_links_checked49392 : (cuts49392.take 1).map (fun c => (6477840385-1+2*2^10*c.k,111504510536387+c.lower,111504897571650+c.upper)) = pointBounds49392 := by
 decide +kernel
def cuts49393 : List PrefixCut := [⟨64,248668032,248668174⟩]
theorem checked49393 : checkPrefixCuts (2^48) 6477971457 10 Manual.Count131072.C049393.packed 64 cuts49393 = true := by
 decide +kernel
def cuts49394 : List PrefixCut := [⟨28,110189235,110189297⟩,
⟨64,250574814,250574955⟩]
theorem checked49394 : checkPrefixCuts (2^48) 6478102529 10 Manual.Count131072.C049394.packed 64 cuts49394 = true := by
 decide +kernel
def pointBounds49394 : List (Nat × Nat × Nat) := [(6478159872,111505119848266,111505506883872)]
theorem point_links_checked49394 : (cuts49394.take 1).map (fun c => (6478102529-1+2*2^10*c.k,111505009659031+c.lower,111505396694575+c.upper)) = pointBounds49394 := by
 decide +kernel
def cuts49395 : List PrefixCut := [⟨63,250917382,250917523⟩,
⟨64,254740846,254740989⟩]
theorem checked49395 : checkPrefixCuts (2^48) 6478233601 10 Manual.Count131072.C049395.packed 64 cuts49395 = true := by
 decide +kernel
def pointBounds49395 : List (Nat × Nat × Nat) := [(6478362624,111505511151227,111505898187053)]
theorem point_links_checked49395 : (cuts49395.take 1).map (fun c => (6478233601-1+2*2^10*c.k,111505260233845+c.lower,111505647269530+c.upper)) = pointBounds49395 := by
 decide +kernel
def cuts49396 : List PrefixCut := [⟨64,249000541,249000678⟩]
theorem checked49396 : checkPrefixCuts (2^48) 6478364673 10 Manual.Count131072.C049396.packed 64 cuts49396 = true := by
 decide +kernel
def cuts49397 : List PrefixCut := [⟨34,135990153,135990231⟩,
⟨64,254165713,254165858⟩]
theorem checked49397 : checkPrefixCuts (2^48) 6478495745 10 Manual.Count131072.C049397.packed 64 cuts49397 = true := by
 decide +kernel
def pointBounds49397 : List (Nat × Nat × Nat) := [(6478565376,111505899965385,111506287001428)]
theorem point_links_checked49397 : (cuts49397.take 1).map (fun c => (6478495745-1+2*2^10*c.k,111505763975232+c.lower,111506151011197+c.upper)) = pointBounds49397 := by
 decide +kernel
def cuts49398 : List PrefixCut := [⟨64,252900630,252900775⟩]
theorem checked49398 : checkPrefixCuts (2^48) 6478626817 10 Manual.Count131072.C049398.packed 64 cuts49398 = true := by
 decide +kernel
def cuts49399 : List PrefixCut := [⟨5,20332624,20332634⟩,
⟨64,249246099,249246241⟩]
theorem checked49399 : checkPrefixCuts (2^48) 6478757889 10 Manual.Count131072.C049399.packed 64 cuts49399 = true := by
 decide +kernel
def pointBounds49399 : List (Nat × Nat × Nat) := [(6478768128,111506291374199,111506678410464)]
theorem point_links_checked49399 : (cuts49399.take 1).map (fun c => (6478757889-1+2*2^10*c.k,111506271041575+c.lower,111506658077830+c.upper)) = pointBounds49399 := by
 decide +kernel
def cuts49400 : List PrefixCut := [⟨40,159441894,159441986⟩,
⟨64,253802737,253802882⟩]
theorem checked49400 : checkPrefixCuts (2^48) 6478888961 10 Manual.Count131072.C049400.packed 64 cuts49400 = true := by
 decide +kernel
def pointBounds49400 : List (Nat × Nat × Nat) := [(6478970880,111506679729568,111507066766057)]
theorem point_links_checked49400 : (cuts49400.take 1).map (fun c => (6478888961-1+2*2^10*c.k,111506520287674+c.lower,111506907324071+c.upper)) = pointBounds49400 := by
 decide +kernel
def cuts49401 : List PrefixCut := [⟨64,249844224,249844366⟩]
theorem checked49401 : checkPrefixCuts (2^48) 6479020033 10 Manual.Count131072.C049401.packed 64 cuts49401 = true := by
 decide +kernel
def cuts49402 : List PrefixCut := [⟨11,44746393,44746417⟩,
⟨64,248535928,248536067⟩]
theorem checked49402 : checkPrefixCuts (2^48) 6479151105 10 Manual.Count131072.C049402.packed 64 cuts49402 = true := by
 decide +kernel
def pointBounds49402 : List (Nat × Nat × Nat) := [(6479173632,111507068681028,111507455717736)]
theorem point_links_checked49402 : (cuts49402.take 1).map (fun c => (6479151105-1+2*2^10*c.k,111507023934635+c.lower,111507410971319+c.upper)) = pointBounds49402 := by
 decide +kernel
def cuts49403 : List PrefixCut := [⟨46,184237439,184237541⟩,
⟨64,255047149,255047290⟩]
theorem checked49403 : checkPrefixCuts (2^48) 6479282177 10 Manual.Count131072.C049403.packed 64 cuts49403 = true := by
 decide +kernel
def pointBounds49403 : List (Nat × Nat × Nat) := [(6479376384,111507456708002,111507843744927)]
theorem point_links_checked49403 : (cuts49403.take 1).map (fun c => (6479282177-1+2*2^10*c.k,111507272470563+c.lower,111507659507386+c.upper)) = pointBounds49403 := by
 decide +kernel
def cuts49404 : List PrefixCut := [⟨64,251479812,251479959⟩]
theorem checked49404 : checkPrefixCuts (2^48) 6479413249 10 Manual.Count131072.C049404.packed 64 cuts49404 = true := by
 decide +kernel
def cuts49405 : List PrefixCut := [⟨17,66029441,66029480⟩,
⟨64,252126314,252126463⟩]
theorem checked49405 : checkPrefixCuts (2^48) 6479544321 10 Manual.Count131072.C049405.packed 64 cuts49405 = true := by
 decide +kernel
def pointBounds49405 : List (Nat × Nat × Nat) := [(6479579136,111507845026965,111508232064115)]
theorem point_links_checked49405 : (cuts49405.take 1).map (fun c => (6479544321-1+2*2^10*c.k,111507778997524+c.lower,111508166034635+c.upper)) = pointBounds49405 := by
 decide +kernel
def cuts49406 : List PrefixCut := [⟨52,205858852,205858964⟩,
⟨64,252903140,252903278⟩]
theorem checked49406 : checkPrefixCuts (2^48) 6479675393 10 Manual.Count131072.C049406.packed 64 cuts49406 = true := by
 decide +kernel
def pointBounds49406 : List (Nat × Nat × Nat) := [(6479781888,111508236982690,111508624020062)]
theorem point_links_checked49406 : (cuts49406.take 1).map (fun c => (6479675393-1+2*2^10*c.k,111508031123838+c.lower,111508418161098+c.upper)) = pointBounds49406 := by
 decide +kernel
def cuts49407 : List PrefixCut := [⟨64,250031115,250031259⟩]
theorem checked49407 : checkPrefixCuts (2^48) 6479806465 10 Manual.Count131072.C049407.packed 64 cuts49407 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000293
