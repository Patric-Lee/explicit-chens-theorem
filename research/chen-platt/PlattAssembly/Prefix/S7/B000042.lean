import PlattAssemblyKernel
import PlattCertificates.Count131072.C061344
import PlattCertificates.Count131072.C061345
import PlattCertificates.Count131072.C061346
import PlattCertificates.Count131072.C061347
import PlattCertificates.Count131072.C061348
import PlattCertificates.Count131072.C061349
import PlattCertificates.Count131072.C061350
import PlattCertificates.Count131072.C061351
import PlattCertificates.Count131072.C061352
import PlattCertificates.Count131072.C061353
import PlattCertificates.Count131072.C061354
import PlattCertificates.Count131072.C061355
import PlattCertificates.Count131072.C061356
import PlattCertificates.Count131072.C061357
import PlattCertificates.Count131072.C061358
import PlattCertificates.Count131072.C061359
import PlattCertificates.Count131072.C061360
import PlattCertificates.Count131072.C061361
import PlattCertificates.Count131072.C061362
import PlattCertificates.Count131072.C061363
import PlattCertificates.Count131072.C061364
import PlattCertificates.Count131072.C061365
import PlattCertificates.Count131072.C061366
import PlattCertificates.Count131072.C061367
import PlattCertificates.Count131072.C061368
import PlattCertificates.Count131072.C061369
import PlattCertificates.Count131072.C061370
import PlattCertificates.Count131072.C061371
import PlattCertificates.Count131072.C061372
import PlattCertificates.Count131072.C061373
import PlattCertificates.Count131072.C061374
import PlattCertificates.Count131072.C061375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61344 : List PrefixCut := [⟨64,195173254,195173366⟩]
theorem checked61344 : checkPrefixCuts (2^48) 8044412929 10 Manual.Count131072.C061344.packed 64 cuts61344 = true := by
 decide +kernel
def cuts61345 : List PrefixCut := [⟨53,168403518,168403619⟩,
⟨64,202762734,202762856⟩]
theorem checked61345 : checkPrefixCuts (2^48) 8044544001 10 Manual.Count131072.C061345.packed 64 cuts61345 = true := by
 decide +kernel
def pointBounds61345 : List (Nat × Nat × Nat) := [(8044652544,114190583859425,114190972423198)]
theorem point_links_checked61345 : (cuts61345.take 1).map (fun c => (8044544001-1+2*2^10*c.k,114190415455907+c.lower,114190804019579+c.upper)) = pointBounds61345 := by
 decide +kernel
def cuts61346 : List PrefixCut := [⟨64,200415184,200415306⟩]
theorem checked61346 : checkPrefixCuts (2^48) 8044675073 10 Manual.Count131072.C061346.packed 64 cuts61346 = true := by
 decide +kernel
def cuts61347 : List PrefixCut := [⟨48,149224616,149224706⟩,
⟨64,200341939,200342057⟩]
theorem checked61347 : checkPrefixCuts (2^48) 8044806145 10 Manual.Count131072.C061347.packed 64 cuts61347 = true := by
 decide +kernel
def pointBounds61347 : List (Nat × Nat × Nat) := [(8044904448,114190967858441,114191356422447)]
theorem point_links_checked61347 : (cuts61347.take 1).map (fun c => (8044806145-1+2*2^10*c.k,114190818633825+c.lower,114191207197741+c.upper)) = pointBounds61347 := by
 decide +kernel
def cuts61348 : List PrefixCut := [⟨64,201493272,201493388⟩]
theorem checked61348 : checkPrefixCuts (2^48) 8044937217 10 Manual.Count131072.C061348.packed 64 cuts61348 = true := by
 decide +kernel
def cuts61349 : List PrefixCut := [⟨43,137149311,137149391⟩,
⟨64,203589215,203589332⟩]
theorem checked61349 : checkPrefixCuts (2^48) 8045068289 10 Manual.Count131072.C061349.packed 64 cuts61349 = true := by
 decide +kernel
def pointBounds61349 : List (Nat × Nat × Nat) := [(8045156352,114191357618347,114191746182577)]
theorem point_links_checked61349 : (cuts61349.take 1).map (fun c => (8045068289-1+2*2^10*c.k,114191220469036+c.lower,114191609033186+c.upper)) = pointBounds61349 := by
 decide +kernel
def cuts61350 : List PrefixCut := [⟨64,199352540,199352652⟩]
theorem checked61350 : checkPrefixCuts (2^48) 8045199361 10 Manual.Count131072.C061350.packed 64 cuts61350 = true := by
 decide +kernel
def cuts61351 : List PrefixCut := [⟨38,119302094,119302164⟩,
⟨64,200188955,200189072⟩]
theorem checked61351 : checkPrefixCuts (2^48) 8045330433 10 Manual.Count131072.C061351.packed 64 cuts61351 = true := by
 decide +kernel
def pointBounds61351 : List (Nat × Nat × Nat) := [(8045408256,114191742712885,114192131277334)]
theorem point_links_checked61351 : (cuts61351.take 1).map (fun c => (8045330433-1+2*2^10*c.k,114191623410791+c.lower,114192011975170+c.upper)) = pointBounds61351 := by
 decide +kernel
def cuts61352 : List PrefixCut := [⟨64,199171118,199171235⟩]
theorem checked61352 : checkPrefixCuts (2^48) 8045461505 10 Manual.Count131072.C061352.packed 64 cuts61352 = true := by
 decide +kernel
def cuts61353 : List PrefixCut := [⟨33,104639643,104639704⟩,
⟨64,199832606,199832717⟩]
theorem checked61353 : checkPrefixCuts (2^48) 8045592577 10 Manual.Count131072.C061353.packed 64 cuts61353 = true := by
 decide +kernel
def pointBounds61353 : List (Nat × Nat × Nat) := [(8045660160,114192127410507,114192515975181)]
theorem point_links_checked61353 : (cuts61353.take 1).map (fun c => (8045592577-1+2*2^10*c.k,114192022770864+c.lower,114192411335477+c.upper)) = pointBounds61353 := by
 decide +kernel
def cuts61354 : List PrefixCut := [⟨64,201123741,201123859⟩]
theorem checked61354 : checkPrefixCuts (2^48) 8045723649 10 Manual.Count131072.C061354.packed 64 cuts61354 = true := by
 decide +kernel
def cuts61355 : List PrefixCut := [⟨28,86024951,86025002⟩,
⟨64,198286773,198286889⟩]
theorem checked61355 : checkPrefixCuts (2^48) 8045854721 10 Manual.Count131072.C061355.packed 64 cuts61355 = true := by
 decide +kernel
def pointBounds61355 : List (Nat × Nat × Nat) := [(8045912064,114192509752162,114192898317055)]
theorem point_links_checked61355 : (cuts61355.take 1).map (fun c => (8045854721-1+2*2^10*c.k,114192423727211+c.lower,114192812292053+c.upper)) = pointBounds61355 := by
 decide +kernel
def cuts61356 : List PrefixCut := [⟨64,202656443,202656561⟩]
theorem checked61356 : checkPrefixCuts (2^48) 8045985793 10 Manual.Count131072.C061356.packed 64 cuts61356 = true := by
 decide +kernel
def cuts61357 : List PrefixCut := [⟨23,71504430,71504472⟩,
⟨64,200134398,200134516⟩]
theorem checked61357 : checkPrefixCuts (2^48) 8046116865 10 Manual.Count131072.C061357.packed 64 cuts61357 = true := by
 decide +kernel
def pointBounds61357 : List (Nat × Nat × Nat) := [(8046163968,114192896174857,114193284739975)]
theorem point_links_checked61357 : (cuts61357.take 1).map (fun c => (8046116865-1+2*2^10*c.k,114192824670427+c.lower,114193213235503+c.upper)) = pointBounds61357 := by
 decide +kernel
def cuts61358 : List PrefixCut := [⟨64,200970696,200970808⟩]
theorem checked61358 : checkPrefixCuts (2^48) 8046247937 10 Manual.Count131072.C061358.packed 64 cuts61358 = true := by
 decide +kernel
def cuts61359 : List PrefixCut := [⟨18,56844904,56844936⟩,
⟨64,201072372,201072489⟩]
theorem checked61359 : checkPrefixCuts (2^48) 8046379009 10 Manual.Count131072.C061359.packed 64 cuts61359 = true := by
 decide +kernel
def pointBounds61359 : List (Nat × Nat × Nat) := [(8046415872,114193282620425,114193671185763)]
theorem point_links_checked61359 : (cuts61359.take 1).map (fun c => (8046379009-1+2*2^10*c.k,114193225775521+c.lower,114193614340827+c.upper)) = pointBounds61359 := by
 decide +kernel
def cuts61360 : List PrefixCut := [⟨64,201034119,201034234⟩]
theorem checked61360 : checkPrefixCuts (2^48) 8046510081 10 Manual.Count131072.C061360.packed 64 cuts61360 = true := by
 decide +kernel
def cuts61361 : List PrefixCut := [⟨13,40122476,40122500⟩,
⟨64,204668767,204668884⟩]
theorem checked61361 : checkPrefixCuts (2^48) 8046641153 10 Manual.Count131072.C061361.packed 64 cuts61361 = true := by
 decide +kernel
def pointBounds61361 : List (Nat × Nat × Nat) := [(8046667776,114193668004488,114194056570050)]
theorem point_links_checked61361 : (cuts61361.take 1).map (fun c => (8046641153-1+2*2^10*c.k,114193627882012+c.lower,114194016447550+c.upper)) = pointBounds61361 := by
 decide +kernel
def cuts61362 : List PrefixCut := [⟨64,197879403,197879519⟩]
theorem checked61362 : checkPrefixCuts (2^48) 8046772225 10 Manual.Count131072.C061362.packed 64 cuts61362 = true := by
 decide +kernel
def cuts61363 : List PrefixCut := [⟨8,24870245,24870259⟩,
⟨64,197701287,197701405⟩]
theorem checked61363 : checkPrefixCuts (2^48) 8046903297 10 Manual.Count131072.C061363.packed 64 cuts61363 = true := by
 decide +kernel
def pointBounds61363 : List (Nat × Nat × Nat) := [(8046919680,114194055300427,114194443866212)]
theorem point_links_checked61363 : (cuts61363.take 1).map (fun c => (8046903297-1+2*2^10*c.k,114194030430182+c.lower,114194418995953+c.upper)) = pointBounds61363 := by
 decide +kernel
def cuts61364 : List PrefixCut := [⟨64,200566322,200566426⟩]
theorem checked61364 : checkPrefixCuts (2^48) 8047034369 10 Manual.Count131072.C061364.packed 64 cuts61364 = true := by
 decide +kernel
def cuts61365 : List PrefixCut := [⟨3,9234225,9234231⟩,
⟨64,202241980,202242101⟩]
theorem checked61365 : checkPrefixCuts (2^48) 8047165441 10 Manual.Count131072.C061365.packed 64 cuts61365 = true := by
 decide +kernel
def pointBounds61365 : List (Nat × Nat × Nat) := [(8047171584,114194437932016,114194826498015)]
theorem point_links_checked61365 : (cuts61365.take 1).map (fun c => (8047165441-1+2*2^10*c.k,114194428697791+c.lower,114194817263784+c.upper)) = pointBounds61365 := by
 decide +kernel
def cuts61366 : List PrefixCut := [⟨62,194123987,194124105⟩,
⟨64,200629711,200629833⟩]
theorem checked61366 : checkPrefixCuts (2^48) 8047296513 10 Manual.Count131072.C061366.packed 64 cuts61366 = true := by
 decide +kernel
def pointBounds61366 : List (Nat × Nat × Nat) := [(8047423488,114194825063758,114195213629990)]
theorem point_links_checked61366 : (cuts61366.take 1).map (fun c => (8047296513-1+2*2^10*c.k,114194630939771+c.lower,114195019505885+c.upper)) = pointBounds61366 := by
 decide +kernel
def cuts61367 : List PrefixCut := [⟨64,198877625,198877734⟩]
theorem checked61367 : checkPrefixCuts (2^48) 8047427585 10 Manual.Count131072.C061367.packed 64 cuts61367 = true := by
 decide +kernel
def cuts61368 : List PrefixCut := [⟨57,178028756,178028859⟩,
⟨64,199923666,199923781⟩]
theorem checked61368 : checkPrefixCuts (2^48) 8047558657 10 Manual.Count131072.C061368.packed 64 cuts61368 = true := by
 decide +kernel
def pointBounds61368 : List (Nat × Nat × Nat) := [(8047675392,114195208475863,114195597042311)]
theorem point_links_checked61368 : (cuts61368.take 1).map (fun c => (8047558657-1+2*2^10*c.k,114195030447107+c.lower,114195419013452+c.upper)) = pointBounds61368 := by
 decide +kernel
def cuts61369 : List PrefixCut := [⟨64,199535683,199535795⟩]
theorem checked61369 : checkPrefixCuts (2^48) 8047689729 10 Manual.Count131072.C061369.packed 64 cuts61369 = true := by
 decide +kernel
def cuts61370 : List PrefixCut := [⟨52,166446319,166446416⟩,
⟨64,204358978,204359098⟩]
theorem checked61370 : checkPrefixCuts (2^48) 8047820801 10 Manual.Count131072.C061370.packed 64 cuts61370 = true := by
 decide +kernel
def pointBounds61370 : List (Nat × Nat × Nat) := [(8047927296,114195596352775,114195984919444)]
theorem point_links_checked61370 : (cuts61370.take 1).map (fun c => (8047820801-1+2*2^10*c.k,114195429906456+c.lower,114195818473028+c.upper)) = pointBounds61370 := by
 decide +kernel
def cuts61371 : List PrefixCut := [⟨64,201942417,201942529⟩]
theorem checked61371 : checkPrefixCuts (2^48) 8047951873 10 Manual.Count131072.C061371.packed 64 cuts61371 = true := by
 decide +kernel
def cuts61372 : List PrefixCut := [⟨47,147170364,147170447⟩,
⟨64,199211170,199211286⟩]
theorem checked61372 : checkPrefixCuts (2^48) 8048082945 10 Manual.Count131072.C061372.packed 64 cuts61372 = true := by
 decide +kernel
def pointBounds61372 : List (Nat × Nat × Nat) := [(8048179200,114195983378215,114196371945102)]
theorem point_links_checked61372 : (cuts61372.take 1).map (fun c => (8048082945-1+2*2^10*c.k,114195836207851+c.lower,114196224774655+c.upper)) = pointBounds61372 := by
 decide +kernel
def cuts61373 : List PrefixCut := [⟨64,203299793,203299911⟩]
theorem checked61373 : checkPrefixCuts (2^48) 8048214017 10 Manual.Count131072.C061373.packed 64 cuts61373 = true := by
 decide +kernel
def cuts61374 : List PrefixCut := [⟨42,132512042,132512119⟩,
⟨64,200253862,200253974⟩]
theorem checked61374 : checkPrefixCuts (2^48) 8048345089 10 Manual.Count131072.C061374.packed 64 cuts61374 = true := by
 decide +kernel
def pointBounds61374 : List (Nat × Nat × Nat) := [(8048431104,114196371230856,114196759797971)]
theorem point_links_checked61374 : (cuts61374.take 1).map (fun c => (8048345089-1+2*2^10*c.k,114196238718814+c.lower,114196627285852+c.upper)) = pointBounds61374 := by
 decide +kernel
def cuts61375 : List PrefixCut := [⟨64,201684461,201684577⟩]
theorem checked61375 : checkPrefixCuts (2^48) 8048476161 10 Manual.Count131072.C061375.packed 64 cuts61375 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000042
