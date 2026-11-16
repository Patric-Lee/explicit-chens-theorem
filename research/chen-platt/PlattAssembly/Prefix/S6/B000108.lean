import PlattAssemblyKernel
import PlattCertificates.Count131072.C053456
import PlattCertificates.Count131072.C053457
import PlattCertificates.Count131072.C053458
import PlattCertificates.Count131072.C053459
import PlattCertificates.Count131072.C053460
import PlattCertificates.Count131072.C053461
import PlattCertificates.Count131072.C053462
import PlattCertificates.Count131072.C053463
import PlattCertificates.Count131072.C053464
import PlattCertificates.Count131072.C053465
import PlattCertificates.Count131072.C053466
import PlattCertificates.Count131072.C053467
import PlattCertificates.Count131072.C053468
import PlattCertificates.Count131072.C053469
import PlattCertificates.Count131072.C053470
import PlattCertificates.Count131072.C053471
import PlattCertificates.Count131072.C053472
import PlattCertificates.Count131072.C053473
import PlattCertificates.Count131072.C053474
import PlattCertificates.Count131072.C053475
import PlattCertificates.Count131072.C053476
import PlattCertificates.Count131072.C053477
import PlattCertificates.Count131072.C053478
import PlattCertificates.Count131072.C053479
import PlattCertificates.Count131072.C053480
import PlattCertificates.Count131072.C053481
import PlattCertificates.Count131072.C053482
import PlattCertificates.Count131072.C053483
import PlattCertificates.Count131072.C053484
import PlattCertificates.Count131072.C053485
import PlattCertificates.Count131072.C053486
import PlattCertificates.Count131072.C053487
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53456 : List PrefixCut := [⟨64,231946553,231946683⟩]
theorem checked53456 : checkPrefixCuts (2^48) 7010516993 10 Manual.Count131072.C053456.packed 64 cuts53456 = true := by
 decide +kernel
def cuts53457 : List PrefixCut := [⟨25,89974988,89975040⟩,
⟨64,232986105,232986236⟩]
theorem checked53457 : checkPrefixCuts (2^48) 7010648065 10 Manual.Count131072.C053457.packed 64 cuts53457 = true := by
 decide +kernel
def pointBounds53457 : List (Nat × Nat × Nat) := [(7010699264,112487717909123,112488105503391)]
theorem point_links_checked53457 : (cuts53457.take 1).map (fun c => (7010648065-1+2*2^10*c.k,112487627934135+c.lower,112488015528351+c.upper)) = pointBounds53457 := by
 decide +kernel
def cuts53458 : List PrefixCut := [⟨64,231857592,231857724⟩]
theorem checked53458 : checkPrefixCuts (2^48) 7010779137 10 Manual.Count131072.C053458.packed 64 cuts53458 = true := by
 decide +kernel
def cuts53459 : List PrefixCut := [⟨4,14252575,14252583⟩,
⟨64,232335028,232335158⟩]
theorem checked53459 : checkPrefixCuts (2^48) 7010910209 10 Manual.Count131072.C053459.packed 64 cuts53459 = true := by
 decide +kernel
def pointBounds53459 : List (Nat × Nat × Nat) := [(7010918400,112488107030407,112488494624894)]
theorem point_links_checked53459 : (cuts53459.take 1).map (fun c => (7010910209-1+2*2^10*c.k,112488092777832+c.lower,112488480372311+c.upper)) = pointBounds53459 := by
 decide +kernel
def cuts53460 : List PrefixCut := [⟨47,170625161,170625262⟩,
⟨64,232852581,232852717⟩]
theorem checked53460 : checkPrefixCuts (2^48) 7011041281 10 Manual.Count131072.C053460.packed 64 cuts53460 = true := by
 decide +kernel
def pointBounds53460 : List (Nat × Nat × Nat) := [(7011137536,112488495738021,112488883332731)]
theorem point_links_checked53460 : (cuts53460.take 1).map (fun c => (7011041281-1+2*2^10*c.k,112488325112860+c.lower,112488712707469+c.upper)) = pointBounds53460 := by
 decide +kernel
def cuts53461 : List PrefixCut := [⟨64,230640199,230640330⟩]
theorem checked53461 : checkPrefixCuts (2^48) 7011172353 10 Manual.Count131072.C053461.packed 64 cuts53461 = true := by
 decide +kernel
def cuts53462 : List PrefixCut := [⟨26,94222003,94222056⟩,
⟨64,232723451,232723583⟩]
theorem checked53462 : checkPrefixCuts (2^48) 7011303425 10 Manual.Count131072.C053462.packed 64 cuts53462 = true := by
 decide +kernel
def pointBounds53462 : List (Nat × Nat × Nat) := [(7011356672,112488882827643,112489270422572)]
theorem point_links_checked53462 : (cuts53462.take 1).map (fun c => (7011303425-1+2*2^10*c.k,112488788605640+c.lower,112489176200516+c.upper)) = pointBounds53462 := by
 decide +kernel
def cuts53463 : List PrefixCut := [⟨64,232157075,232157208⟩]
theorem checked53463 : checkPrefixCuts (2^48) 7011434497 10 Manual.Count131072.C053463.packed 64 cuts53463 = true := by
 decide +kernel
def cuts53464 : List PrefixCut := [⟨5,19429862,19429874⟩,
⟨64,230747708,230747840⟩]
theorem checked53464 : checkPrefixCuts (2^48) 7011565569 10 Manual.Count131072.C053464.packed 64 cuts53464 = true := by
 decide +kernel
def pointBounds53464 : List (Nat × Nat × Nat) := [(7011575808,112489272916028,112489660511181)]
theorem point_links_checked53464 : (cuts53464.take 1).map (fun c => (7011565569-1+2*2^10*c.k,112489253486166+c.lower,112489641081307+c.upper)) = pointBounds53464 := by
 decide +kernel
def cuts53465 : List PrefixCut := [⟨48,175185545,175185644⟩,
⟨64,232509698,232509828⟩]
theorem checked53465 : checkPrefixCuts (2^48) 7011696641 10 Manual.Count131072.C053465.packed 64 cuts53465 = true := by
 decide +kernel
def pointBounds53465 : List (Nat × Nat × Nat) := [(7011794944,112489659419419,112490047014791)]
theorem point_links_checked53465 : (cuts53465.take 1).map (fun c => (7011696641-1+2*2^10*c.k,112489484233874+c.lower,112489871829147+c.upper)) = pointBounds53465 := by
 decide +kernel
def cuts53466 : List PrefixCut := [⟨64,232063772,232063903⟩]
theorem checked53466 : checkPrefixCuts (2^48) 7011827713 10 Manual.Count131072.C053466.packed 64 cuts53466 = true := by
 decide +kernel
def cuts53467 : List PrefixCut := [⟨27,97866106,97866161⟩,
⟨64,231818578,231818709⟩]
theorem checked53467 : checkPrefixCuts (2^48) 7011958785 10 Manual.Count131072.C053467.packed 64 cuts53467 = true := by
 decide +kernel
def pointBounds53467 : List (Nat × Nat × Nat) := [(7012014080,112490046673450,112490434269039)]
theorem point_links_checked53467 : (cuts53467.take 1).map (fun c => (7011958785-1+2*2^10*c.k,112489948807344+c.lower,112490336402878+c.upper)) = pointBounds53467 := by
 decide +kernel
def cuts53468 : List PrefixCut := [⟨64,229004357,229004484⟩]
theorem checked53468 : checkPrefixCuts (2^48) 7012089857 10 Manual.Count131072.C053468.packed 64 cuts53468 = true := by
 decide +kernel
def cuts53469 : List PrefixCut := [⟨6,22117461,22117475⟩,
⟨64,235663380,235663516⟩]
theorem checked53469 : checkPrefixCuts (2^48) 7012220929 10 Manual.Count131072.C053469.packed 64 cuts53469 = true := by
 decide +kernel
def pointBounds53469 : List (Nat × Nat × Nat) := [(7012233216,112490431747740,112490819343546)]
theorem point_links_checked53469 : (cuts53469.take 1).map (fun c => (7012220929-1+2*2^10*c.k,112490409630279+c.lower,112490797226071+c.upper)) = pointBounds53469 := by
 decide +kernel
def cuts53470 : List PrefixCut := [⟨49,179102815,179102917⟩,
⟨64,234494919,234495054⟩]
theorem checked53470 : checkPrefixCuts (2^48) 7012352001 10 Manual.Count131072.C053470.packed 64 cuts53470 = true := by
 decide +kernel
def pointBounds53470 : List (Nat × Nat × Nat) := [(7012452352,112490824396474,112491211992504)]
theorem point_links_checked53470 : (cuts53470.take 1).map (fun c => (7012352001-1+2*2^10*c.k,112490645293659+c.lower,112491032889587+c.upper)) = pointBounds53470 := by
 decide +kernel
def cuts53471 : List PrefixCut := [⟨64,233446958,233447085⟩]
theorem checked53471 : checkPrefixCuts (2^48) 7012483073 10 Manual.Count131072.C053471.packed 64 cuts53471 = true := by
 decide +kernel
def cuts53472 : List PrefixCut := [⟨29,104078354,104078413⟩,
⟨64,231154715,231154845⟩]
theorem checked53472 : checkPrefixCuts (2^48) 7012614145 10 Manual.Count131072.C053472.packed 64 cuts53472 = true := by
 decide +kernel
def pointBounds53472 : List (Nat × Nat × Nat) := [(7012673536,112491217313890,112491604910139)]
theorem point_links_checked53472 : (cuts53472.take 1).map (fun c => (7012614145-1+2*2^10*c.k,112491113235536+c.lower,112491500831726+c.upper)) = pointBounds53472 := by
 decide +kernel
def cuts53473 : List PrefixCut := [⟨64,232876307,232876437⟩]
theorem checked53473 : checkPrefixCuts (2^48) 7012745217 10 Manual.Count131072.C053473.packed 64 cuts53473 = true := by
 decide +kernel
def cuts53474 : List PrefixCut := [⟨9,32952326,32952344⟩,
⟨64,228175984,228176113⟩]
theorem checked53474 : checkPrefixCuts (2^48) 7012876289 10 Manual.Count131072.C053474.packed 64 cuts53474 = true := by
 decide +kernel
def pointBounds53474 : List (Nat × Nat × Nat) := [(7012894720,112491610218884,112491997815352)]
theorem point_links_checked53474 : (cuts53474.take 1).map (fun c => (7012876289-1+2*2^10*c.k,112491577266558+c.lower,112491964863008+c.upper)) = pointBounds53474 := by
 decide +kernel
def cuts53475 : List PrefixCut := [⟨53,190926055,190926168⟩,
⟨64,231743792,231743928⟩]
theorem checked53475 : checkPrefixCuts (2^48) 7013007361 10 Manual.Count131072.C053475.packed 64 cuts53475 = true := by
 decide +kernel
def pointBounds53475 : List (Nat × Nat × Nat) := [(7013115904,112491996368597,112492383965289)]
theorem point_links_checked53475 : (cuts53475.take 1).map (fun c => (7013007361-1+2*2^10*c.k,112491805442542+c.lower,112492193039121+c.upper)) = pointBounds53475 := by
 decide +kernel
def cuts53476 : List PrefixCut := [⟨64,228448388,228448519⟩]
theorem checked53476 : checkPrefixCuts (2^48) 7013138433 10 Manual.Count131072.C053476.packed 64 cuts53476 = true := by
 decide +kernel
def cuts53477 : List PrefixCut := [⟨33,118998573,118998638⟩,
⟨64,230972567,230972695⟩]
theorem checked53477 : checkPrefixCuts (2^48) 7013269505 10 Manual.Count131072.C053477.packed 64 cuts53477 = true := by
 decide +kernel
def pointBounds53477 : List (Nat × Nat × Nat) := [(7013337088,112492384633295,112492772230206)]
theorem point_links_checked53477 : (cuts53477.take 1).map (fun c => (7013269505-1+2*2^10*c.k,112492265634722+c.lower,112492653231568+c.upper)) = pointBounds53477 := by
 decide +kernel
def cuts53478 : List PrefixCut := [⟨64,233135475,233135604⟩]
theorem checked53478 : checkPrefixCuts (2^48) 7013400577 10 Manual.Count131072.C053478.packed 64 cuts53478 = true := by
 decide +kernel
def cuts53479 : List PrefixCut := [⟨13,47999119,47999145⟩,
⟨64,235218014,235218144⟩]
theorem checked53479 : checkPrefixCuts (2^48) 7013531649 10 Manual.Count131072.C053479.packed 64 cuts53479 = true := by
 decide +kernel
def pointBounds53479 : List (Nat × Nat × Nat) := [(7013558272,112492777741883,112493165339012)]
theorem point_links_checked53479 : (cuts53479.take 1).map (fun c => (7013531649-1+2*2^10*c.k,112492729742764+c.lower,112493117339867+c.upper)) = pointBounds53479 := by
 decide +kernel
def cuts53480 : List PrefixCut := [⟨57,208084598,208084715⟩,
⟨64,233608332,233608464⟩]
theorem checked53480 : checkPrefixCuts (2^48) 7013662721 10 Manual.Count131072.C053480.packed 64 cuts53480 = true := by
 decide +kernel
def pointBounds53480 : List (Nat × Nat × Nat) := [(7013779456,112493173045376,112493560642726)]
theorem point_links_checked53480 : (cuts53480.take 1).map (fun c => (7013662721-1+2*2^10*c.k,112492964960778+c.lower,112493352558011+c.upper)) = pointBounds53480 := by
 decide +kernel
def cuts53481 : List PrefixCut := [⟨64,232560538,232560672⟩]
theorem checked53481 : checkPrefixCuts (2^48) 7013793793 10 Manual.Count131072.C053481.packed 64 cuts53481 = true := by
 decide +kernel
def cuts53482 : List PrefixCut := [⟨37,133514672,133514749⟩,
⟨64,230188516,230188646⟩]
theorem checked53482 : checkPrefixCuts (2^48) 7013924865 10 Manual.Count131072.C053482.packed 64 cuts53482 = true := by
 decide +kernel
def pointBounds53482 : List (Nat × Nat × Nat) := [(7014000640,112493564644320,112493952241896)]
theorem point_links_checked53482 : (cuts53482.take 1).map (fun c => (7013924865-1+2*2^10*c.k,112493431129648+c.lower,112493818727147+c.upper)) = pointBounds53482 := by
 decide +kernel
def cuts53483 : List PrefixCut := [⟨64,233555117,233555250⟩]
theorem checked53483 : checkPrefixCuts (2^48) 7014055937 10 Manual.Count131072.C053483.packed 64 cuts53483 = true := by
 decide +kernel
def cuts53484 : List PrefixCut := [⟨17,62802302,62802337⟩,
⟨64,236560429,236560560⟩]
theorem checked53484 : checkPrefixCuts (2^48) 7014187009 10 Manual.Count131072.C053484.packed 64 cuts53484 = true := by
 decide +kernel
def pointBounds53484 : List (Nat × Nat × Nat) := [(7014221824,112493957675583,112494345273380)]
theorem point_links_checked53484 : (cuts53484.take 1).map (fun c => (7014187009-1+2*2^10*c.k,112493894873281+c.lower,112494282471043+c.upper)) = pointBounds53484 := by
 decide +kernel
def cuts53485 : List PrefixCut := [⟨61,221227118,221227247⟩,
⟨64,232462925,232463062⟩]
theorem checked53485 : checkPrefixCuts (2^48) 7014318081 10 Manual.Count131072.C053485.packed 64 cuts53485 = true := by
 decide +kernel
def pointBounds53485 : List (Nat × Nat × Nat) := [(7014443008,112494352660828,112494740258850)]
theorem point_links_checked53485 : (cuts53485.take 1).map (fun c => (7014318081-1+2*2^10*c.k,112494131433710+c.lower,112494519031603+c.upper)) = pointBounds53485 := by
 decide +kernel
def cuts53486 : List PrefixCut := [⟨64,231214625,231214757⟩]
theorem checked53486 : checkPrefixCuts (2^48) 7014449153 10 Manual.Count131072.C053486.packed 64 cuts53486 = true := by
 decide +kernel
def cuts53487 : List PrefixCut := [⟨41,148509588,148509672⟩,
⟨64,232975877,232976008⟩]
theorem checked53487 : checkPrefixCuts (2^48) 7014580225 10 Manual.Count131072.C053487.packed 64 cuts53487 = true := by
 decide +kernel
def pointBounds53487 : List (Nat × Nat × Nat) := [(7014664192,112494743620848,112495131219094)]
theorem point_links_checked53487 : (cuts53487.take 1).map (fun c => (7014580225-1+2*2^10*c.k,112494595111260+c.lower,112494982709422+c.upper)) = pointBounds53487 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000108
