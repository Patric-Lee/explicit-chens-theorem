import PlattAssemblyKernel
import PlattCertificates.Count131072.C029376
import PlattCertificates.Count131072.C029377
import PlattCertificates.Count131072.C029378
import PlattCertificates.Count131072.C029379
import PlattCertificates.Count131072.C029380
import PlattCertificates.Count131072.C029381
import PlattCertificates.Count131072.C029382
import PlattCertificates.Count131072.C029383
import PlattCertificates.Count131072.C029384
import PlattCertificates.Count131072.C029385
import PlattCertificates.Count131072.C029386
import PlattCertificates.Count131072.C029387
import PlattCertificates.Count131072.C029388
import PlattCertificates.Count131072.C029389
import PlattCertificates.Count131072.C029390
import PlattCertificates.Count131072.C029391
import PlattCertificates.Count131072.C029392
import PlattCertificates.Count131072.C029393
import PlattCertificates.Count131072.C029394
import PlattCertificates.Count131072.C029395
import PlattCertificates.Count131072.C029396
import PlattCertificates.Count131072.C029397
import PlattCertificates.Count131072.C029398
import PlattCertificates.Count131072.C029399
import PlattCertificates.Count131072.C029400
import PlattCertificates.Count131072.C029401
import PlattCertificates.Count131072.C029402
import PlattCertificates.Count131072.C029403
import PlattCertificates.Count131072.C029404
import PlattCertificates.Count131072.C029405
import PlattCertificates.Count131072.C029406
import PlattCertificates.Count131072.C029407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000293
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29376 : List PrefixCut := [⟨38,125608807,125608878⟩,
⟨128,428890465,428890700⟩]
theorem checked29376 : checkPrefixCuts (2^48) 3854303233 9 Manual.Count131072.C029376.packed 128 cuts29376 = true := by
 decide +kernel
def pointBounds29376 : List (Nat × Nat × Nat) := [(3854342144,104960484088120,104960867259335)]
theorem point_links_checked29376 : (cuts29376.take 1).map (fun c => (3854303233-1+2*2^9*c.k,104960358479313+c.lower,104960741650457+c.upper)) = pointBounds29376 := by
 decide +kernel
def cuts29377 : List PrefixCut := [⟨28,95444955,95445008⟩,
⟨128,436032330,436032575⟩]
theorem checked29377 : checkPrefixCuts (2^48) 3854434305 9 Manual.Count131072.C029377.packed 128 cuts29377 = true := by
 decide +kernel
def pointBounds29377 : List (Nat × Nat × Nat) := [(3854462976,104960882814733,104961265986165)]
theorem point_links_checked29377 : (cuts29377.take 1).map (fun c => (3854434305-1+2*2^9*c.k,104960787369778+c.lower,104961170541157+c.upper)) = pointBounds29377 := by
 decide +kernel
def cuts29378 : List PrefixCut := [⟨18,59952372,59952406⟩,
⟨128,432950544,432950788⟩]
theorem checked29378 : checkPrefixCuts (2^48) 3854565377 9 Manual.Count131072.C029378.packed 128 cuts29378 = true := by
 decide +kernel
def pointBounds29378 : List (Nat × Nat × Nat) := [(3854583808,104961283354480,104961666526138)]
theorem point_links_checked29378 : (cuts29378.take 1).map (fun c => (3854565377-1+2*2^9*c.k,104961223402108+c.lower,104961606573732+c.upper)) = pointBounds29378 := by
 decide +kernel
def cuts29379 : List PrefixCut := [⟨8,29135462,29135478⟩,
⟨126,425560999,425561236⟩,
⟨128,432351749,432351990⟩]
theorem checked29379 : checkPrefixCuts (2^48) 3854696449 9 Manual.Count131072.C029379.packed 128 cuts29379 = true := by
 decide +kernel
def pointBounds29379 : List (Nat × Nat × Nat) := [(3854704640,104961685488114,104962068659998),(3854825472,104962081913651,104962465085756)]
theorem point_links_checked29379 : (cuts29379.take 2).map (fun c => (3854696449-1+2*2^9*c.k,104961656352652+c.lower,104962039524520+c.upper)) = pointBounds29379 := by
 decide +kernel
def cuts29380 : List PrefixCut := [⟨116,388746140,388746359⟩,
⟨128,432117905,432118148⟩]
theorem checked29380 : checkPrefixCuts (2^48) 3854827521 9 Manual.Count131072.C029380.packed 128 cuts29380 = true := by
 decide +kernel
def pointBounds29380 : List (Nat × Nat × Nat) := [(3854946304,104962477450541,104962860622869)]
theorem point_links_checked29380 : (cuts29380.take 1).map (fun c => (3854827521-1+2*2^9*c.k,104962088704401+c.lower,104962471876510+c.upper)) = pointBounds29380 := by
 decide +kernel
def cuts29381 : List PrefixCut := [⟨106,352809923,352810115⟩,
⟨128,427868371,427868603⟩]
theorem checked29381 : checkPrefixCuts (2^48) 3854958593 9 Manual.Count131072.C029381.packed 128 cuts29381 = true := by
 decide +kernel
def pointBounds29381 : List (Nat × Nat × Nat) := [(3855067136,104962873632229,104963256804773)]
theorem point_links_checked29381 : (cuts29381.take 1).map (fun c => (3854958593-1+2*2^9*c.k,104962520822306+c.lower,104962903994658+c.upper)) = pointBounds29381 := by
 decide +kernel
def cuts29382 : List PrefixCut := [⟨96,326294663,326294847⟩,
⟨128,434936031,434936277⟩]
theorem checked29382 : checkPrefixCuts (2^48) 3855089665 9 Manual.Count131072.C029382.packed 128 cuts29382 = true := by
 decide +kernel
def pointBounds29382 : List (Nat × Nat × Nat) := [(3855187968,104963274985340,104963658158108)]
theorem point_links_checked29382 : (cuts29382.take 1).map (fun c => (3855089665-1+2*2^9*c.k,104962948690677+c.lower,104963331863261+c.upper)) = pointBounds29382 := by
 decide +kernel
def cuts29383 : List PrefixCut := [⟨86,287734487,287734649⟩,
⟨128,432292863,432293106⟩]
theorem checked29383 : checkPrefixCuts (2^48) 3855220737 9 Manual.Count131072.C029383.packed 128 cuts29383 = true := by
 decide +kernel
def pointBounds29383 : List (Nat × Nat × Nat) := [(3855308800,104963671361195,104964054534187)]
theorem point_links_checked29383 : (cuts29383.take 1).map (fun c => (3855220737-1+2*2^9*c.k,104963383626708+c.lower,104963766799538+c.upper)) = pointBounds29383 := by
 decide +kernel
def cuts29384 : List PrefixCut := [⟨76,257718765,257718909⟩,
⟨128,436293638,436293878⟩]
theorem checked29384 : checkPrefixCuts (2^48) 3855351809 9 Manual.Count131072.C029384.packed 128 cuts29384 = true := by
 decide +kernel
def pointBounds29384 : List (Nat × Nat × Nat) := [(3855429632,104964073638336,104964456811553)]
theorem point_links_checked29384 : (cuts29384.take 1).map (fun c => (3855351809-1+2*2^9*c.k,104963815919571+c.lower,104964199092644+c.upper)) = pointBounds29384 := by
 decide +kernel
def cuts29385 : List PrefixCut := [⟨66,218652228,218652354⟩,
⟨128,426934101,426934344⟩]
theorem checked29385 : checkPrefixCuts (2^48) 3855482881 9 Manual.Count131072.C029385.packed 128 cuts29385 = true := by
 decide +kernel
def pointBounds29385 : List (Nat × Nat × Nat) := [(3855550464,104964470865437,104964854038876)]
theorem point_links_checked29385 : (cuts29385.take 1).map (fun c => (3855482881-1+2*2^9*c.k,104964252213209+c.lower,104964635386522+c.upper)) = pointBounds29385 := by
 decide +kernel
def cuts29386 : List PrefixCut := [⟨56,192071882,192071986⟩,
⟨128,436993994,436994234⟩]
theorem checked29386 : checkPrefixCuts (2^48) 3855613953 9 Manual.Count131072.C029386.packed 128 cuts29386 = true := by
 decide +kernel
def pointBounds29386 : List (Nat × Nat × Nat) := [(3855671296,104964871219192,104965254392852)]
theorem point_links_checked29386 : (cuts29386.take 1).map (fun c => (3855613953-1+2*2^9*c.k,104964679147310+c.lower,104965062320866+c.upper)) = pointBounds29386 := by
 decide +kernel
def cuts29387 : List PrefixCut := [⟨46,156733116,156733198⟩,
⟨128,432599149,432599392⟩]
theorem checked29387 : checkPrefixCuts (2^48) 3855745025 9 Manual.Count131072.C029387.packed 128 cuts29387 = true := by
 decide +kernel
def pointBounds29387 : List (Nat × Nat × Nat) := [(3855792128,104965272874420,104965656048298)]
theorem point_links_checked29387 : (cuts29387.take 1).map (fun c => (3855745025-1+2*2^9*c.k,104965116141304+c.lower,104965499315100+c.upper)) = pointBounds29387 := by
 decide +kernel
def cuts29388 : List PrefixCut := [⟨36,121250673,121250742⟩,
⟨128,431343477,431343715⟩]
theorem checked29388 : checkPrefixCuts (2^48) 3855876097 9 Manual.Count131072.C029388.packed 128 cuts29388 = true := by
 decide +kernel
def pointBounds29388 : List (Nat × Nat × Nat) := [(3855912960,104965669991126,104966053165234)]
theorem point_links_checked29388 : (cuts29388.take 1).map (fun c => (3855876097-1+2*2^9*c.k,104965548740453+c.lower,104965931914492+c.upper)) = pointBounds29388 := by
 decide +kernel
def cuts29389 : List PrefixCut := [⟨26,87522465,87522515⟩,
⟨128,440234247,440234498⟩]
theorem checked29389 : checkPrefixCuts (2^48) 3856007169 9 Manual.Count131072.C029389.packed 128 cuts29389 = true := by
 decide +kernel
def pointBounds29389 : List (Nat × Nat × Nat) := [(3856033792,104966067606395,104966450780722)]
theorem point_links_checked29389 : (cuts29389.take 1).map (fun c => (3856007169-1+2*2^9*c.k,104965980083930+c.lower,104966363258207+c.upper)) = pointBounds29389 := by
 decide +kernel
def cuts29390 : List PrefixCut := [⟨16,54015436,54015466⟩,
⟨128,435255638,435255884⟩]
theorem checked29390 : checkPrefixCuts (2^48) 3856138241 9 Manual.Count131072.C029390.packed 128 cuts29390 = true := by
 decide +kernel
def pointBounds29390 : List (Nat × Nat × Nat) := [(3856154624,104966474333613,104966857508171)]
theorem point_links_checked29390 : (cuts29390.take 1).map (fun c => (3856138241-1+2*2^9*c.k,104966420318177+c.lower,104966803492705+c.upper)) = pointBounds29390 := by
 decide +kernel
def cuts29391 : List PrefixCut := [⟨6,21386493,21386504⟩,
⟨124,416482624,416482853⟩,
⟨128,430204569,430204804⟩]
theorem checked29391 : checkPrefixCuts (2^48) 3856269313 9 Manual.Count131072.C029391.packed 128 cuts29391 = true := by
 decide +kernel
def pointBounds29391 : List (Nat × Nat × Nat) := [(3856275456,104966876960308,104967260135093),(3856396288,104967272056439,104967655231442)]
theorem point_links_checked29391 : (cuts29391.take 2).map (fun c => (3856269313-1+2*2^9*c.k,104966855573815+c.lower,104967238748589+c.upper)) = pointBounds29391 := by
 decide +kernel
def cuts29392 : List PrefixCut := [⟨114,385595180,385595391⟩,
⟨128,432379641,432379879⟩]
theorem checked29392 : checkPrefixCuts (2^48) 3856400385 9 Manual.Count131072.C029392.packed 128 cuts29392 = true := by
 decide +kernel
def pointBounds29392 : List (Nat × Nat × Nat) := [(3856517120,104967671373564,104968054548784)]
theorem point_links_checked29392 : (cuts29392.take 1).map (fun c => (3856400385-1+2*2^9*c.k,104967285778384+c.lower,104967668953393+c.upper)) = pointBounds29392 := by
 decide +kernel
def cuts29393 : List PrefixCut := [⟨104,350403540,350403733⟩,
⟨128,431343118,431343358⟩]
theorem checked29393 : checkPrefixCuts (2^48) 3856531457 9 Manual.Count131072.C029393.packed 128 cuts29393 = true := by
 decide +kernel
def pointBounds29393 : List (Nat × Nat × Nat) := [(3856637952,104968068561565,104968451737005)]
theorem point_links_checked29393 : (cuts29393.take 1).map (fun c => (3856531457-1+2*2^9*c.k,104967718158025+c.lower,104968101333272+c.upper)) = pointBounds29393 := by
 decide +kernel
def cuts29394 : List PrefixCut := [⟨94,317257746,317257919⟩,
⟨128,430817592,430817829⟩]
theorem checked29394 : checkPrefixCuts (2^48) 3856662529 9 Manual.Count131072.C029394.packed 128 cuts29394 = true := by
 decide +kernel
def pointBounds29394 : List (Nat × Nat × Nat) := [(3856758784,104968466758889,104968849934549)]
theorem point_links_checked29394 : (cuts29394.take 1).map (fun c => (3856662529-1+2*2^9*c.k,104968149501143+c.lower,104968532676630+c.upper)) = pointBounds29394 := by
 decide +kernel
def cuts29395 : List PrefixCut := [⟨84,283311330,283311493⟩,
⟨128,433649151,433649399⟩]
theorem checked29395 : checkPrefixCuts (2^48) 3856793601 9 Manual.Count131072.C029395.packed 128 cuts29395 = true := by
 decide +kernel
def pointBounds29395 : List (Nat × Nat × Nat) := [(3856879616,104968863630065,104969246805952)]
theorem point_links_checked29395 : (cuts29395.take 1).map (fun c => (3856793601-1+2*2^9*c.k,104968580318735+c.lower,104968963494459+c.upper)) = pointBounds29395 := by
 decide +kernel
def cuts29396 : List PrefixCut := [⟨74,250753727,250753867⟩,
⟨128,431955982,431956226⟩]
theorem checked29396 : checkPrefixCuts (2^48) 3856924673 9 Manual.Count131072.C029396.packed 128 cuts29396 = true := by
 decide +kernel
def pointBounds29396 : List (Nat × Nat × Nat) := [(3857000448,104969264721613,104969647897725)]
theorem point_links_checked29396 : (cuts29396.take 1).map (fun c => (3856924673-1+2*2^9*c.k,104969013967886+c.lower,104969397143858+c.upper)) = pointBounds29396 := by
 decide +kernel
def cuts29397 : List PrefixCut := [⟨64,214914292,214914413⟩,
⟨128,431576354,431576596⟩]
theorem checked29397 : checkPrefixCuts (2^48) 3857055745 9 Manual.Count131072.C029397.packed 128 cuts29397 = true := by
 decide +kernel
def pointBounds29397 : List (Nat × Nat × Nat) := [(3857121280,104969660838160,104970044014497)]
theorem point_links_checked29397 : (cuts29397.take 1).map (fun c => (3857055745-1+2*2^9*c.k,104969445923868+c.lower,104969829100084+c.upper)) = pointBounds29397 := by
 decide +kernel
def cuts29398 : List PrefixCut := [⟨54,184623264,184623365⟩,
⟨128,429518551,429518791⟩]
theorem checked29398 : checkPrefixCuts (2^48) 3857186817 9 Manual.Count131072.C029398.packed 128 cuts29398 = true := by
 decide +kernel
def pointBounds29398 : List (Nat × Nat × Nat) := [(3857242112,104970062123486,104970445300045)]
theorem point_links_checked29398 : (cuts29398.take 1).map (fun c => (3857186817-1+2*2^9*c.k,104969877500222+c.lower,104970260676680+c.upper)) = pointBounds29398 := by
 decide +kernel
def cuts29399 : List PrefixCut := [⟨44,147620819,147620900⟩,
⟨128,432714578,432714812⟩]
theorem checked29399 : checkPrefixCuts (2^48) 3857317889 9 Manual.Count131072.C029399.packed 128 cuts29399 = true := by
 decide +kernel
def pointBounds29399 : List (Nat × Nat × Nat) := [(3857362944,104970454639592,104970837816371)]
theorem point_links_checked29399 : (cuts29399.take 1).map (fun c => (3857317889-1+2*2^9*c.k,104970307018773+c.lower,104970690195471+c.upper)) = pointBounds29399 := by
 decide +kernel
def cuts29400 : List PrefixCut := [⟨34,117917668,117917736⟩,
⟨128,435618638,435618886⟩]
theorem checked29400 : checkPrefixCuts (2^48) 3857448961 9 Manual.Count131072.C029400.packed 128 cuts29400 = true := by
 decide +kernel
def pointBounds29400 : List (Nat × Nat × Nat) := [(3857483776,104970857651019,104971240828019)]
theorem point_links_checked29400 : (cuts29400.take 1).map (fun c => (3857448961-1+2*2^9*c.k,104970739733351+c.lower,104971122910283+c.upper)) = pointBounds29400 := by
 decide +kernel
def cuts29401 : List PrefixCut := [⟨24,81649481,81649527⟩,
⟨128,431225914,431226159⟩]
theorem checked29401 : checkPrefixCuts (2^48) 3857580033 9 Manual.Count131072.C029401.packed 128 cuts29401 = true := by
 decide +kernel
def pointBounds29401 : List (Nat × Nat × Nat) := [(3857604608,104971257001470,104971640178696)]
theorem point_links_checked29401 : (cuts29401.take 1).map (fun c => (3857580033-1+2*2^9*c.k,104971175351989+c.lower,104971558529169+c.upper)) = pointBounds29401 := by
 decide +kernel
def cuts29402 : List PrefixCut := [⟨14,44070304,44070332⟩,
⟨128,433473054,433473298⟩]
theorem checked29402 : checkPrefixCuts (2^48) 3857711105 9 Manual.Count131072.C029402.packed 128 cuts29402 = true := by
 decide +kernel
def pointBounds29402 : List (Nat × Nat × Nat) := [(3857725440,104971650648207,104972033825660)]
theorem point_links_checked29402 : (cuts29402.take 1).map (fun c => (3857711105-1+2*2^9*c.k,104971606577903+c.lower,104971989755328+c.upper)) = pointBounds29402 := by
 decide +kernel
def cuts29403 : List PrefixCut := [⟨4,12695336,12695344⟩,
⟨122,412518959,412519193⟩,
⟨128,432655733,432655978⟩]
theorem checked29403 : checkPrefixCuts (2^48) 3857842177 9 Manual.Count131072.C029403.packed 128 cuts29403 = true := by
 decide +kernel
def pointBounds29403 : List (Nat × Nat × Nat) := [(3857846272,104972052746293,104972435923970),(3857967104,104972452569916,104972835747819)]
theorem point_links_checked29403 : (cuts29403.take 2).map (fun c => (3857842177-1+2*2^9*c.k,104972040050957+c.lower,104972423228626+c.upper)) = pointBounds29403 := by
 decide +kernel
def cuts29404 : List PrefixCut := [⟨112,373691820,373692031⟩,
⟨128,428263613,428263853⟩]
theorem checked29404 : checkPrefixCuts (2^48) 3857973249 9 Manual.Count131072.C029404.packed 128 cuts29404 = true := by
 decide +kernel
def pointBounds29404 : List (Nat × Nat × Nat) := [(3858087936,104972846398510,104973229576635)]
theorem point_links_checked29404 : (cuts29404.take 1).map (fun c => (3857973249-1+2*2^9*c.k,104972472706690+c.lower,104972855884604+c.upper)) = pointBounds29404 := by
 decide +kernel
def cuts29405 : List PrefixCut := [⟨102,351865859,351866050⟩,
⟨128,441162242,441162480⟩]
theorem checked29405 : checkPrefixCuts (2^48) 3858104321 9 Manual.Count131072.C029405.packed 128 cuts29405 = true := by
 decide +kernel
def pointBounds29405 : List (Nat × Nat × Nat) := [(3858208768,104973252836162,104973636014507)]
theorem point_links_checked29405 : (cuts29405.take 1).map (fun c => (3858104321-1+2*2^9*c.k,104972900970303+c.lower,104973284148457+c.upper)) = pointBounds29405 := by
 decide +kernel
def cuts29406 : List PrefixCut := [⟨92,308082276,308082449⟩,
⟨128,430423080,430423321⟩]
theorem checked29406 : checkPrefixCuts (2^48) 3858235393 9 Manual.Count131072.C029406.packed 128 cuts29406 = true := by
 decide +kernel
def pointBounds29406 : List (Nat × Nat × Nat) := [(3858329600,104973650214821,104974033393386)]
theorem point_links_checked29406 : (cuts29406.take 1).map (fun c => (3858235393-1+2*2^9*c.k,104973342132545+c.lower,104973725310937+c.upper)) = pointBounds29406 := by
 decide +kernel
def cuts29407 : List PrefixCut := [⟨82,282758266,282758423⟩,
⟨128,435588096,435588336⟩]
theorem checked29407 : checkPrefixCuts (2^48) 3858366465 9 Manual.Count131072.C029407.packed 128 cuts29407 = true := by
 decide +kernel
def pointBounds29407 : List (Nat × Nat × Nat) := [(3858450432,104974055313891,104974438492681)]
theorem point_links_checked29407 : (cuts29407.take 1).map (fun c => (3858366465-1+2*2^9*c.k,104973772555625+c.lower,104974155734258+c.upper)) = pointBounds29407 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000293
