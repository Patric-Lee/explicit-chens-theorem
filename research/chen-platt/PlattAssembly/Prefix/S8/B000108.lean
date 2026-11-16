import PlattAssemblyKernel
import PlattCertificates.Count131072.C073456
import PlattCertificates.Count131072.C073457
import PlattCertificates.Count131072.C073458
import PlattCertificates.Count131072.C073459
import PlattCertificates.Count131072.C073460
import PlattCertificates.Count131072.C073461
import PlattCertificates.Count131072.C073462
import PlattCertificates.Count131072.C073463
import PlattCertificates.Count131072.C073464
import PlattCertificates.Count131072.C073465
import PlattCertificates.Count131072.C073466
import PlattCertificates.Count131072.C073467
import PlattCertificates.Count131072.C073468
import PlattCertificates.Count131072.C073469
import PlattCertificates.Count131072.C073470
import PlattCertificates.Count131072.C073471
import PlattCertificates.Count131072.C073472
import PlattCertificates.Count131072.C073473
import PlattCertificates.Count131072.C073474
import PlattCertificates.Count131072.C073475
import PlattCertificates.Count131072.C073476
import PlattCertificates.Count131072.C073477
import PlattCertificates.Count131072.C073478
import PlattCertificates.Count131072.C073479
import PlattCertificates.Count131072.C073480
import PlattCertificates.Count131072.C073481
import PlattCertificates.Count131072.C073482
import PlattCertificates.Count131072.C073483
import PlattCertificates.Count131072.C073484
import PlattCertificates.Count131072.C073485
import PlattCertificates.Count131072.C073486
import PlattCertificates.Count131072.C073487
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73456 : List PrefixCut := [⟨64,166423976,166424078⟩]
theorem checked73456 : checkPrefixCuts (2^48) 9631956993 10 Manual.Count131072.C073456.packed 64 cuts73456 = true := by
 decide +kernel
def cuts73457 : List PrefixCut := [⟨28,72676452,72676494⟩,
⟨64,166918491,166918593⟩]
theorem checked73457 : checkPrefixCuts (2^48) 9632088065 10 Manual.Count131072.C073457.packed 64 cuts73457 = true := by
 decide +kernel
def pointBounds73457 : List (Nat × Nat × Nat) := [(9632145408,116404452592540,116404842447898)]
theorem point_links_checked73457 : (cuts73457.take 1).map (fun c => (9632088065-1+2*2^10*c.k,116404379916088+c.lower,116404769771404+c.upper)) = pointBounds73457 := by
 decide +kernel
def cuts73458 : List PrefixCut := [⟨64,165835009,165835106⟩]
theorem checked73458 : checkPrefixCuts (2^48) 9632219137 10 Manual.Count131072.C073458.packed 64 cuts73458 = true := by
 decide +kernel
def cuts73459 : List PrefixCut := [⟨47,122526514,122526588⟩,
⟨64,166563289,166563389⟩]
theorem checked73459 : checkPrefixCuts (2^48) 9632350209 10 Manual.Count131072.C073459.packed 64 cuts73459 = true := by
 decide +kernel
def pointBounds73459 : List (Nat × Nat × Nat) := [(9632446464,116404835196102,116405225051691)]
theorem point_links_checked73459 : (cuts73459.take 1).map (fun c => (9632350209-1+2*2^10*c.k,116404712669588+c.lower,116405102525103+c.upper)) = pointBounds73459 := by
 decide +kernel
def cuts73460 : List PrefixCut := [⟨64,163638900,163638995⟩]
theorem checked73460 : checkPrefixCuts (2^48) 9632481281 10 Manual.Count131072.C073460.packed 64 cuts73460 = true := by
 decide +kernel
def cuts73461 : List PrefixCut := [⟨64,165302264,165302364⟩]
theorem checked73461 : checkPrefixCuts (2^48) 9632612353 10 Manual.Count131072.C073461.packed 64 cuts73461 = true := by
 decide +kernel
def cuts73462 : List PrefixCut := [⟨2,5405817,5405820⟩,
⟨64,166468843,166468941⟩]
theorem checked73462 : checkPrefixCuts (2^48) 9632743425 10 Manual.Count131072.C073462.packed 64 cuts73462 = true := by
 decide +kernel
def pointBounds73462 : List (Nat × Nat × Nat) := [(9632747520,116405213579858,116405603435671)]
theorem point_links_checked73462 : (cuts73462.take 1).map (fun c => (9632743425-1+2*2^10*c.k,116405208174041+c.lower,116405598029851+c.upper)) = pointBounds73462 := by
 decide +kernel
def cuts73463 : List PrefixCut := [⟨64,167606148,167606252⟩]
theorem checked73463 : checkPrefixCuts (2^48) 9632874497 10 Manual.Count131072.C073463.packed 64 cuts73463 = true := by
 decide +kernel
def cuts73464 : List PrefixCut := [⟨21,54757862,54757890⟩,
⟨64,165879911,165880011⟩]
theorem checked73464 : checkPrefixCuts (2^48) 9633005569 10 Manual.Count131072.C073464.packed 64 cuts73464 = true := by
 decide +kernel
def pointBounds73464 : List (Nat × Nat × Nat) := [(9633048576,116405597006894,116405986862934)]
theorem point_links_checked73464 : (cuts73464.take 1).map (fun c => (9633005569-1+2*2^10*c.k,116405542249032+c.lower,116405932105044+c.upper)) = pointBounds73464 := by
 decide +kernel
def cuts73465 : List PrefixCut := [⟨64,167280181,167280280⟩]
theorem checked73465 : checkPrefixCuts (2^48) 9633136641 10 Manual.Count131072.C073465.packed 64 cuts73465 = true := by
 decide +kernel
def cuts73466 : List PrefixCut := [⟨40,103113579,103113638⟩,
⟨64,165641644,165641739⟩]
theorem checked73466 : checkPrefixCuts (2^48) 9633267713 10 Manual.Count131072.C073466.packed 64 cuts73466 = true := by
 decide +kernel
def pointBounds73466 : List (Nat × Nat × Nat) := [(9633349632,116405978522703,116406368378973)]
theorem point_links_checked73466 : (cuts73466.take 1).map (fun c => (9633267713-1+2*2^10*c.k,116405875409124+c.lower,116406265265335+c.upper)) = pointBounds73466 := by
 decide +kernel
def cuts73467 : List PrefixCut := [⟨64,165230341,165230441⟩]
theorem checked73467 : checkPrefixCuts (2^48) 9633398785 10 Manual.Count131072.C073467.packed 64 cuts73467 = true := by
 decide +kernel
def cuts73468 : List PrefixCut := [⟨59,152518313,152518404⟩,
⟨64,165841661,165841760⟩]
theorem checked73468 : checkPrefixCuts (2^48) 9633529857 10 Manual.Count131072.C073468.packed 64 cuts73468 = true := by
 decide +kernel
def pointBounds73468 : List (Nat × Nat × Nat) := [(9633650688,116406358799422,116406748655919)]
theorem point_links_checked73468 : (cuts73468.take 1).map (fun c => (9633529857-1+2*2^10*c.k,116406206281109+c.lower,116406596137515+c.upper)) = pointBounds73468 := by
 decide +kernel
def cuts73469 : List PrefixCut := [⟨64,165196618,165196710⟩]
theorem checked73469 : checkPrefixCuts (2^48) 9633660929 10 Manual.Count131072.C073469.packed 64 cuts73469 = true := by
 decide +kernel
def cuts73470 : List PrefixCut := [⟨64,166450720,166450816⟩]
theorem checked73470 : checkPrefixCuts (2^48) 9633792001 10 Manual.Count131072.C073470.packed 64 cuts73470 = true := by
 decide +kernel
def cuts73471 : List PrefixCut := [⟨14,35586322,35586345⟩,
⟨64,165864102,165864204⟩]
theorem checked73471 : checkPrefixCuts (2^48) 9633923073 10 Manual.Count131072.C073471.packed 64 cuts73471 = true := by
 decide +kernel
def pointBounds73471 : List (Nat × Nat × Nat) := [(9633951744,116406739356430,116407129213146)]
theorem point_links_checked73471 : (cuts73471.take 1).map (fun c => (9633923073-1+2*2^10*c.k,116406703770108+c.lower,116407093626801+c.upper)) = pointBounds73471 := by
 decide +kernel
def cuts73472 : List PrefixCut := [⟨64,166738357,166738457⟩]
theorem checked73472 : checkPrefixCuts (2^48) 9634054145 10 Manual.Count131072.C073472.packed 64 cuts73472 = true := by
 decide +kernel
def cuts73473 : List PrefixCut := [⟨34,88787898,88787951⟩,
⟨64,166560782,166560882⟩]
theorem checked73473 : checkPrefixCuts (2^48) 9634185217 10 Manual.Count131072.C073473.packed 64 cuts73473 = true := by
 decide +kernel
def pointBounds73473 : List (Nat × Nat × Nat) := [(9634254848,116407125160465,116407515017413)]
theorem point_links_checked73473 : (cuts73473.take 1).map (fun c => (9634185217-1+2*2^10*c.k,116407036372567+c.lower,116407426229462+c.upper)) = pointBounds73473 := by
 decide +kernel
def cuts73474 : List PrefixCut := [⟨64,167639495,167639593⟩]
theorem checked73474 : checkPrefixCuts (2^48) 9634316289 10 Manual.Count131072.C073474.packed 64 cuts73474 = true := by
 decide +kernel
def cuts73475 : List PrefixCut := [⟨54,137896213,137896293⟩,
⟨64,163605502,163605597⟩]
theorem checked73475 : checkPrefixCuts (2^48) 9634447361 10 Manual.Count131072.C073475.packed 64 cuts73475 = true := by
 decide +kernel
def pointBounds73475 : List (Nat × Nat × Nat) := [(9634557952,116407508469057,116407898326230)]
theorem point_links_checked73475 : (cuts73475.take 1).map (fun c => (9634447361-1+2*2^10*c.k,116407370572844+c.lower,116407760429937+c.upper)) = pointBounds73475 := by
 decide +kernel
def cuts73476 : List PrefixCut := [⟨64,166670849,166670949⟩]
theorem checked73476 : checkPrefixCuts (2^48) 9634578433 10 Manual.Count131072.C073476.packed 64 cuts73476 = true := by
 decide +kernel
def cuts73477 : List PrefixCut := [⟨64,165383147,165383245⟩]
theorem checked73477 : checkPrefixCuts (2^48) 9634709505 10 Manual.Count131072.C073477.packed 64 cuts73477 = true := by
 decide +kernel
def cuts73478 : List PrefixCut := [⟨10,26614176,26614194⟩,
⟨64,168097795,168097896⟩]
theorem checked73478 : checkPrefixCuts (2^48) 9634840577 10 Manual.Count131072.C073478.packed 64 cuts73478 = true := by
 decide +kernel
def pointBounds73478 : List (Nat × Nat × Nat) := [(9634861056,116407892846518,116408282703922)]
theorem point_links_checked73478 : (cuts73478.take 1).map (fun c => (9634840577-1+2*2^10*c.k,116407866232342+c.lower,116408256089728+c.upper)) = pointBounds73478 := by
 decide +kernel
def cuts73479 : List PrefixCut := [⟨64,167160684,167160778⟩]
theorem checked73479 : checkPrefixCuts (2^48) 9634971649 10 Manual.Count131072.C073479.packed 64 cuts73479 = true := by
 decide +kernel
def cuts73480 : List PrefixCut := [⟨30,79314352,79314399⟩,
⟨64,167830316,167830413⟩]
theorem checked73480 : checkPrefixCuts (2^48) 9635102721 10 Manual.Count131072.C073480.packed 64 cuts73480 = true := by
 decide +kernel
def pointBounds73480 : List (Nat × Nat × Nat) := [(9635164160,116408280805173,116408670662801)]
theorem point_links_checked73480 : (cuts73480.take 1).map (fun c => (9635102721-1+2*2^10*c.k,116408201490821+c.lower,116408591348402+c.upper)) = pointBounds73480 := by
 decide +kernel
def cuts73481 : List PrefixCut := [⟨64,166951640,166951740⟩]
theorem checked73481 : checkPrefixCuts (2^48) 9635233793 10 Manual.Count131072.C073481.packed 64 cuts73481 = true := by
 decide +kernel
def cuts73482 : List PrefixCut := [⟨50,130492376,130492453⟩,
⟨64,166365122,166365221⟩]
theorem checked73482 : checkPrefixCuts (2^48) 9635364865 10 Manual.Count131072.C073482.packed 64 cuts73482 = true := by
 decide +kernel
def pointBounds73482 : List (Nat × Nat × Nat) := [(9635467264,116408666765153,116409056623008)]
theorem point_links_checked73482 : (cuts73482.take 1).map (fun c => (9635364865-1+2*2^10*c.k,116408536272777+c.lower,116408926130555+c.upper)) = pointBounds73482 := by
 decide +kernel
def cuts73483 : List PrefixCut := [⟨64,164230370,164230478⟩]
theorem checked73483 : checkPrefixCuts (2^48) 9635495937 10 Manual.Count131072.C073483.packed 64 cuts73483 = true := by
 decide +kernel
def cuts73484 : List PrefixCut := [⟨64,167529064,167529166⟩]
theorem checked73484 : checkPrefixCuts (2^48) 9635627009 10 Manual.Count131072.C073484.packed 64 cuts73484 = true := by
 decide +kernel
def cuts73485 : List PrefixCut := [⟨6,15774196,15774207⟩,
⟨64,167380726,167380821⟩]
theorem checked73485 : checkPrefixCuts (2^48) 9635758081 10 Manual.Count131072.C073485.packed 64 cuts73485 = true := by
 decide +kernel
def pointBounds73485 : List (Nat × Nat × Nat) := [(9635770368,116409050171529,116409440029627)]
theorem point_links_checked73485 : (cuts73485.take 1).map (fun c => (9635758081-1+2*2^10*c.k,116409034397333+c.lower,116409424255420+c.upper)) = pointBounds73485 := by
 decide +kernel
def cuts73486 : List PrefixCut := [⟨64,165450531,165450626⟩]
theorem checked73486 : checkPrefixCuts (2^48) 9635889153 10 Manual.Count131072.C073486.packed 64 cuts73486 = true := by
 decide +kernel
def cuts73487 : List PrefixCut := [⟨26,68352852,68352892⟩,
⟨64,166704341,166704438⟩]
theorem checked73487 : checkPrefixCuts (2^48) 9636020225 10 Manual.Count131072.C073487.packed 64 cuts73487 = true := by
 decide +kernel
def pointBounds73487 : List (Nat × Nat × Nat) := [(9636073472,116409435581442,116409825439759)]
theorem point_links_checked73487 : (cuts73487.take 1).map (fun c => (9636020225-1+2*2^10*c.k,116409367228590+c.lower,116409757086867+c.upper)) = pointBounds73487 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000108
