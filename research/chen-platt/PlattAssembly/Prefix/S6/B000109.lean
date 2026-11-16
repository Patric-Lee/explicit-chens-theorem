import PlattAssemblyKernel
import PlattCertificates.Count131072.C053488
import PlattCertificates.Count131072.C053489
import PlattCertificates.Count131072.C053490
import PlattCertificates.Count131072.C053491
import PlattCertificates.Count131072.C053492
import PlattCertificates.Count131072.C053493
import PlattCertificates.Count131072.C053494
import PlattCertificates.Count131072.C053495
import PlattCertificates.Count131072.C053496
import PlattCertificates.Count131072.C053497
import PlattCertificates.Count131072.C053498
import PlattCertificates.Count131072.C053499
import PlattCertificates.Count131072.C053500
import PlattCertificates.Count131072.C053501
import PlattCertificates.Count131072.C053502
import PlattCertificates.Count131072.C053503
import PlattCertificates.Count131072.C053504
import PlattCertificates.Count131072.C053505
import PlattCertificates.Count131072.C053506
import PlattCertificates.Count131072.C053507
import PlattCertificates.Count131072.C053508
import PlattCertificates.Count131072.C053509
import PlattCertificates.Count131072.C053510
import PlattCertificates.Count131072.C053511
import PlattCertificates.Count131072.C053512
import PlattCertificates.Count131072.C053513
import PlattCertificates.Count131072.C053514
import PlattCertificates.Count131072.C053515
import PlattCertificates.Count131072.C053516
import PlattCertificates.Count131072.C053517
import PlattCertificates.Count131072.C053518
import PlattCertificates.Count131072.C053519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000109
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53488 : List PrefixCut := [⟨64,230925097,230925227⟩]
theorem checked53488 : checkPrefixCuts (2^48) 7014711297 10 Manual.Count131072.C053488.packed 64 cuts53488 = true := by
 decide +kernel
def cuts53489 : List PrefixCut := [⟨21,76519324,76519366⟩,
⟨64,232044300,232044431⟩]
theorem checked53489 : checkPrefixCuts (2^48) 7014842369 10 Manual.Count131072.C053489.packed 64 cuts53489 = true := by
 decide +kernel
def pointBounds53489 : List (Nat × Nat × Nat) := [(7014885376,112495135531558,112495523130023)]
theorem point_links_checked53489 : (cuts53489.take 1).map (fun c => (7014842369-1+2*2^10*c.k,112495059012234+c.lower,112495446610657+c.upper)) = pointBounds53489 := by
 decide +kernel
def cuts53490 : List PrefixCut := [⟨64,229431866,229431993⟩]
theorem checked53490 : checkPrefixCuts (2^48) 7014973441 10 Manual.Count131072.C053490.packed 64 cuts53490 = true := by
 decide +kernel
def cuts53491 : List PrefixCut := [⟨1,4132784,4132786⟩,
⟨64,233199218,233199351⟩]
theorem checked53491 : checkPrefixCuts (2^48) 7015104513 10 Manual.Count131072.C053491.packed 64 cuts53491 = true := by
 decide +kernel
def pointBounds53491 : List (Nat × Nat × Nat) := [(7015106560,112495524621184,112495912219867)]
theorem point_links_checked53491 : (cuts53491.take 1).map (fun c => (7015104513-1+2*2^10*c.k,112495520488400+c.lower,112495908087081+c.upper)) = pointBounds53491 := by
 decide +kernel
def cuts53492 : List PrefixCut := [⟨45,161174519,161174614⟩,
⟨64,229423287,229423421⟩]
theorem checked53492 : checkPrefixCuts (2^48) 7015235585 10 Manual.Count131072.C053492.packed 64 cuts53492 = true := by
 decide +kernel
def pointBounds53492 : List (Nat × Nat × Nat) := [(7015327744,112495914862137,112496302461046)]
theorem point_links_checked53492 : (cuts53492.take 1).map (fun c => (7015235585-1+2*2^10*c.k,112495753687618+c.lower,112496141286432+c.upper)) = pointBounds53492 := by
 decide +kernel
def cuts53493 : List PrefixCut := [⟨64,234193549,234193681⟩]
theorem checked53493 : checkPrefixCuts (2^48) 7015366657 10 Manual.Count131072.C053493.packed 64 cuts53493 = true := by
 decide +kernel
def cuts53494 : List PrefixCut := [⟨25,89872671,89872721⟩,
⟨64,232584312,232584442⟩]
theorem checked53494 : checkPrefixCuts (2^48) 7015497729 10 Manual.Count131072.C053494.packed 64 cuts53494 = true := by
 decide +kernel
def pointBounds53494 : List (Nat × Nat × Nat) := [(7015548928,112496307177125,112496694776255)]
theorem point_links_checked53494 : (cuts53494.take 1).map (fun c => (7015497729-1+2*2^10*c.k,112496217304454+c.lower,112496604903534+c.upper)) = pointBounds53494 := by
 decide +kernel
def cuts53495 : List PrefixCut := [⟨64,232620088,232620222⟩]
theorem checked53495 : checkPrefixCuts (2^48) 7015628801 10 Manual.Count131072.C053495.packed 64 cuts53495 = true := by
 decide +kernel
def cuts53496 : List PrefixCut := [⟨5,18736200,18736210⟩,
⟨64,234140295,234140431⟩]
theorem checked53496 : checkPrefixCuts (2^48) 7015759873 10 Manual.Count131072.C053496.packed 64 cuts53496 = true := by
 decide +kernel
def pointBounds53496 : List (Nat × Nat × Nat) := [(7015770112,112496701245054,112497088844408)]
theorem point_links_checked53496 : (cuts53496.take 1).map (fun c => (7015759873-1+2*2^10*c.k,112496682508854+c.lower,112497070108198+c.upper)) = pointBounds53496 := by
 decide +kernel
def cuts53497 : List PrefixCut := [⟨49,177528061,177528165⟩,
⟨64,228840213,228840347⟩]
theorem checked53497 : checkPrefixCuts (2^48) 7015890945 10 Manual.Count131072.C053497.packed 64 cuts53497 = true := by
 decide +kernel
def pointBounds53497 : List (Nat × Nat × Nat) := [(7015991296,112497094177210,112497481776794)]
theorem point_links_checked53497 : (cuts53497.take 1).map (fun c => (7015890945-1+2*2^10*c.k,112496916649149+c.lower,112497304248629+c.upper)) = pointBounds53497 := by
 decide +kernel
def cuts53498 : List PrefixCut := [⟨64,231202906,231203034⟩]
theorem checked53498 : checkPrefixCuts (2^48) 7016022017 10 Manual.Count131072.C053498.packed 64 cuts53498 = true := by
 decide +kernel
def cuts53499 : List PrefixCut := [⟨29,108840014,108840075⟩,
⟨64,235932510,235932641⟩]
theorem checked53499 : checkPrefixCuts (2^48) 7016153089 10 Manual.Count131072.C053499.packed 64 cuts53499 = true := by
 decide +kernel
def pointBounds53499 : List (Nat × Nat × Nat) := [(7016212480,112497485532282,112497873132085)]
theorem point_links_checked53499 : (cuts53499.take 1).map (fun c => (7016153089-1+2*2^10*c.k,112497376692268+c.lower,112497764292010+c.upper)) = pointBounds53499 := by
 decide +kernel
def cuts53500 : List PrefixCut := [⟨64,231194269,231194401⟩]
theorem checked53500 : checkPrefixCuts (2^48) 7016284161 10 Manual.Count131072.C053500.packed 64 cuts53500 = true := by
 decide +kernel
def cuts53501 : List PrefixCut := [⟨9,31491510,31491528⟩,
⟨64,229103904,229104035⟩]
theorem checked53501 : checkPrefixCuts (2^48) 7016415233 10 Manual.Count131072.C053501.packed 64 cuts53501 = true := by
 decide +kernel
def pointBounds53501 : List (Nat × Nat × Nat) := [(7016433664,112497875310557,112498262910580)]
theorem point_links_checked53501 : (cuts53501.take 1).map (fun c => (7016415233-1+2*2^10*c.k,112497843819047+c.lower,112498231419052+c.upper)) = pointBounds53501 := by
 decide +kernel
def cuts53502 : List PrefixCut := [⟨53,192594834,192594944⟩,
⟨64,232750142,232750274⟩]
theorem checked53502 : checkPrefixCuts (2^48) 7016546305 10 Manual.Count131072.C053502.packed 64 cuts53502 = true := by
 decide +kernel
def pointBounds53502 : List (Nat × Nat × Nat) := [(7016654848,112498265517785,112498653118031)]
theorem point_links_checked53502 : (cuts53502.take 1).map (fun c => (7016546305-1+2*2^10*c.k,112498072922951+c.lower,112498460523087+c.upper)) = pointBounds53502 := by
 decide +kernel
def cuts53503 : List PrefixCut := [⟨64,233588201,233588336⟩]
theorem checked53503 : checkPrefixCuts (2^48) 7016677377 10 Manual.Count131072.C053503.packed 64 cuts53503 = true := by
 decide +kernel
def cuts53504 : List PrefixCut := [⟨33,122187796,122187866⟩,
⟨64,233463501,233463635⟩]
theorem checked53504 : checkPrefixCuts (2^48) 7016808449 10 Manual.Count131072.C053504.packed 64 cuts53504 = true := by
 decide +kernel
def pointBounds53504 : List (Nat × Nat × Nat) := [(7016876032,112498661449090,112499049049563)]
theorem point_links_checked53504 : (cuts53504.take 1).map (fun c => (7016808449-1+2*2^10*c.k,112498539261294+c.lower,112498926861697+c.upper)) = pointBounds53504 := by
 decide +kernel
def cuts53505 : List PrefixCut := [⟨64,231493594,231493726⟩]
theorem checked53505 : checkPrefixCuts (2^48) 7016939521 10 Manual.Count131072.C053505.packed 64 cuts53505 = true := by
 decide +kernel
def cuts53506 : List PrefixCut := [⟨13,46410511,46410537⟩,
⟨64,229804520,229804652⟩]
theorem checked53506 : checkPrefixCuts (2^48) 7017070593 10 Manual.Count131072.C053506.packed 64 cuts53506 = true := by
 decide +kernel
def pointBounds53506 : List (Nat × Nat × Nat) := [(7017097216,112499050628900,112499438229595)]
theorem point_links_checked53506 : (cuts53506.take 1).map (fun c => (7017070593-1+2*2^10*c.k,112499004218389+c.lower,112499391819058+c.upper)) = pointBounds53506 := by
 decide +kernel
def cuts53507 : List PrefixCut := [⟨57,205572950,205573066⟩,
⟨64,230562366,230562496⟩]
theorem checked53507 : checkPrefixCuts (2^48) 7017201665 10 Manual.Count131072.C053507.packed 64 cuts53507 = true := by
 decide +kernel
def pointBounds53507 : List (Nat × Nat × Nat) := [(7017318400,112499439595859,112499827196776)]
theorem point_links_checked53507 : (cuts53507.take 1).map (fun c => (7017201665-1+2*2^10*c.k,112499234022909+c.lower,112499621623710+c.upper)) = pointBounds53507 := by
 decide +kernel
def cuts53508 : List PrefixCut := [⟨64,229154171,229154303⟩]
theorem checked53508 : checkPrefixCuts (2^48) 7017332737 10 Manual.Count131072.C053508.packed 64 cuts53508 = true := by
 decide +kernel
def cuts53509 : List PrefixCut := [⟨37,134811102,134811181⟩,
⟨64,235407081,235407217⟩]
theorem checked53509 : checkPrefixCuts (2^48) 7017463809 10 Manual.Count131072.C053509.packed 64 cuts53509 = true := by
 decide +kernel
def pointBounds53509 : List (Nat × Nat × Nat) := [(7017539584,112499828550548,112500216151690)]
theorem point_links_checked53509 : (cuts53509.take 1).map (fun c => (7017463809-1+2*2^10*c.k,112499693739446+c.lower,112500081340509+c.upper)) = pointBounds53509 := by
 decide +kernel
def cuts53510 : List PrefixCut := [⟨64,229265937,229266071⟩]
theorem checked53510 : checkPrefixCuts (2^48) 7017594881 10 Manual.Count131072.C053510.packed 64 cuts53510 = true := by
 decide +kernel
def cuts53511 : List PrefixCut := [⟨17,62169000,62169035⟩,
⟨64,235598832,235598967⟩]
theorem checked53511 : checkPrefixCuts (2^48) 7017725953 10 Manual.Count131072.C053511.packed 64 cuts53511 = true := by
 decide +kernel
def pointBounds53511 : List (Nat × Nat × Nat) := [(7017760768,112500220581464,112500608182832)]
theorem point_links_checked53511 : (cuts53511.take 1).map (fun c => (7017725953-1+2*2^10*c.k,112500158412464+c.lower,112500546013797+c.upper)) = pointBounds53511 := by
 decide +kernel
def cuts53512 : List PrefixCut := [⟨61,225286792,225286918⟩,
⟨64,236276288,236276420⟩]
theorem checked53512 : checkPrefixCuts (2^48) 7017857025 10 Manual.Count131072.C053512.packed 64 cuts53512 = true := by
 decide +kernel
def pointBounds53512 : List (Nat × Nat × Nat) := [(7017981952,112500619298088,112501006899682)]
theorem point_links_checked53512 : (cuts53512.take 1).map (fun c => (7017857025-1+2*2^10*c.k,112500394011296+c.lower,112500781612764+c.upper)) = pointBounds53512 := by
 decide +kernel
def cuts53513 : List PrefixCut := [⟨64,230536516,230536648⟩]
theorem checked53513 : checkPrefixCuts (2^48) 7017988097 10 Manual.Count131072.C053513.packed 64 cuts53513 = true := by
 decide +kernel
def cuts53514 : List PrefixCut := [⟨41,148715437,148715519⟩,
⟨64,231735412,231735542⟩]
theorem checked53514 : checkPrefixCuts (2^48) 7018119169 10 Manual.Count131072.C053514.packed 64 cuts53514 = true := by
 decide +kernel
def pointBounds53514 : List (Nat × Nat × Nat) := [(7018203136,112501009539537,112501397141351)]
theorem point_links_checked53514 : (cuts53514.take 1).map (fun c => (7018119169-1+2*2^10*c.k,112500860824100+c.lower,112501248425832+c.upper)) = pointBounds53514 := by
 decide +kernel
def cuts53515 : List PrefixCut := [⟨64,228763269,228763400⟩]
theorem checked53515 : checkPrefixCuts (2^48) 7018250241 10 Manual.Count131072.C053515.packed 64 cuts53515 = true := by
 decide +kernel
def cuts53516 : List PrefixCut := [⟨21,76280213,76280255⟩,
⟨64,232729389,232729518⟩]
theorem checked53516 : checkPrefixCuts (2^48) 7018381313 10 Manual.Count131072.C053516.packed 64 cuts53516 = true := by
 decide +kernel
def pointBounds53516 : List (Nat × Nat × Nat) := [(7018424320,112501397602994,112501785205029)]
theorem point_links_checked53516 : (cuts53516.take 1).map (fun c => (7018381313-1+2*2^10*c.k,112501321322781+c.lower,112501708924774+c.upper)) = pointBounds53516 := by
 decide +kernel
def cuts53517 : List PrefixCut := [⟨64,235051084,235051217⟩]
theorem checked53517 : checkPrefixCuts (2^48) 7018512385 10 Manual.Count131072.C053517.packed 64 cuts53517 = true := by
 decide +kernel
def cuts53518 : List PrefixCut := [⟨1,3569246,3569248⟩,
⟨64,234685771,234685905⟩]
theorem checked53518 : checkPrefixCuts (2^48) 7018643457 10 Manual.Count131072.C053518.packed 64 cuts53518 = true := by
 decide +kernel
def pointBounds53518 : List (Nat × Nat × Nat) := [(7018645504,112501792672500,112502180274757)]
theorem point_links_checked53518 : (cuts53518.take 1).map (fun c => (7018643457-1+2*2^10*c.k,112501789103254+c.lower,112502176705509+c.upper)) = pointBounds53518 := by
 decide +kernel
def cuts53519 : List PrefixCut := [⟨45,161815110,161815204⟩,
⟨64,230871619,230871752⟩]
theorem checked53519 : checkPrefixCuts (2^48) 7018774529 10 Manual.Count131072.C053519.packed 64 cuts53519 = true := by
 decide +kernel
def pointBounds53519 : List (Nat × Nat × Nat) := [(7018866688,112502185604135,112502573206618)]
theorem point_links_checked53519 : (cuts53519.take 1).map (fun c => (7018774529-1+2*2^10*c.k,112502023789025+c.lower,112502411391414+c.upper)) = pointBounds53519 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000109
