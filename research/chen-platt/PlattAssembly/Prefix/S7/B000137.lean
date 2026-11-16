import PlattAssemblyKernel
import PlattCertificates.Count131072.C064384
import PlattCertificates.Count131072.C064385
import PlattCertificates.Count131072.C064386
import PlattCertificates.Count131072.C064387
import PlattCertificates.Count131072.C064388
import PlattCertificates.Count131072.C064389
import PlattCertificates.Count131072.C064390
import PlattCertificates.Count131072.C064391
import PlattCertificates.Count131072.C064392
import PlattCertificates.Count131072.C064393
import PlattCertificates.Count131072.C064394
import PlattCertificates.Count131072.C064395
import PlattCertificates.Count131072.C064396
import PlattCertificates.Count131072.C064397
import PlattCertificates.Count131072.C064398
import PlattCertificates.Count131072.C064399
import PlattCertificates.Count131072.C064400
import PlattCertificates.Count131072.C064401
import PlattCertificates.Count131072.C064402
import PlattCertificates.Count131072.C064403
import PlattCertificates.Count131072.C064404
import PlattCertificates.Count131072.C064405
import PlattCertificates.Count131072.C064406
import PlattCertificates.Count131072.C064407
import PlattCertificates.Count131072.C064408
import PlattCertificates.Count131072.C064409
import PlattCertificates.Count131072.C064410
import PlattCertificates.Count131072.C064411
import PlattCertificates.Count131072.C064412
import PlattCertificates.Count131072.C064413
import PlattCertificates.Count131072.C064414
import PlattCertificates.Count131072.C064415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000137
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64384 : List PrefixCut := [⟨64,191663063,191663170⟩]
theorem checked64384 : checkPrefixCuts (2^48) 8442871809 10 Manual.Count131072.C064384.packed 64 cuts64384 = true := by
 decide +kernel
def cuts64385 : List PrefixCut := [⟨62,182825557,182825665⟩,
⟨64,189026376,189026487⟩]
theorem checked64385 : checkPrefixCuts (2^48) 8443002881 10 Manual.Count131072.C064385.packed 64 cuts64385 = true := by
 decide +kernel
def pointBounds64385 : List (Nat × Nat × Nat) := [(8443129856,114786618627382,114787007533915)]
theorem point_links_checked64385 : (cuts64385.take 1).map (fun c => (8443002881-1+2*2^10*c.k,114786435801825+c.lower,114786824708250+c.upper)) = pointBounds64385 := by
 decide +kernel
def cuts64386 : List PrefixCut := [⟨64,190290261,190290372⟩]
theorem checked64386 : checkPrefixCuts (2^48) 8443133953 10 Manual.Count131072.C064386.packed 64 cuts64386 = true := by
 decide +kernel
def cuts64387 : List PrefixCut := [⟨63,186886971,186887080⟩,
⟨64,190187304,190187415⟩]
theorem checked64387 : checkPrefixCuts (2^48) 8443265025 10 Manual.Count131072.C064387.packed 64 cuts64387 = true := by
 decide +kernel
def pointBounds64387 : List (Nat × Nat × Nat) := [(8443394048,114787002005433,114787390912189)]
theorem point_links_checked64387 : (cuts64387.take 1).map (fun c => (8443265025-1+2*2^10*c.k,114786815118462+c.lower,114787204025109+c.upper)) = pointBounds64387 := by
 decide +kernel
def cuts64388 : List PrefixCut := [⟨64,186784023,186784135⟩]
theorem checked64388 : checkPrefixCuts (2^48) 8443396097 10 Manual.Count131072.C064388.packed 64 cuts64388 = true := by
 decide +kernel
def cuts64389 : List PrefixCut := [⟨64,187081165,187081266⟩]
theorem checked64389 : checkPrefixCuts (2^48) 8443527169 10 Manual.Count131072.C064389.packed 64 cuts64389 = true := by
 decide +kernel
def pointBounds64389 : List (Nat × Nat × Nat) := [(8443658240,114787379170954,114787768077925)]
theorem point_links_checked64389 : (cuts64389.take 1).map (fun c => (8443527169-1+2*2^10*c.k,114787192089789+c.lower,114787580996659+c.upper)) = pointBounds64389 := by
 decide +kernel
def cuts64390 : List PrefixCut := [⟨64,190145113,190145223⟩]
theorem checked64390 : checkPrefixCuts (2^48) 8443658241 10 Manual.Count131072.C064390.packed 64 cuts64390 = true := by
 decide +kernel
def cuts64391 : List PrefixCut := [⟨64,193042280,193042399⟩]
theorem checked64391 : checkPrefixCuts (2^48) 8443789313 10 Manual.Count131072.C064391.packed 64 cuts64391 = true := by
 decide +kernel
def cuts64392 : List PrefixCut := [⟨1,2866777,2866779⟩,
⟨64,192172602,192172713⟩]
theorem checked64392 : checkPrefixCuts (2^48) 8443920385 10 Manual.Count131072.C064392.packed 64 cuts64392 = true := by
 decide +kernel
def pointBounds64392 : List (Nat × Nat × Nat) := [(8443922432,114787765225124,114788154132326)]
theorem point_links_checked64392 : (cuts64392.take 1).map (fun c => (8443920385-1+2*2^10*c.k,114787762358347+c.lower,114788151265547+c.upper)) = pointBounds64392 := by
 decide +kernel
def cuts64393 : List PrefixCut := [⟨64,190169595,190169713⟩]
theorem checked64393 : checkPrefixCuts (2^48) 8444051457 10 Manual.Count131072.C064393.packed 64 cuts64393 = true := by
 decide +kernel
def cuts64394 : List PrefixCut := [⟨2,6233379,6233383⟩,
⟨64,192766645,192766752⟩]
theorem checked64394 : checkPrefixCuts (2^48) 8444182529 10 Manual.Count131072.C064394.packed 64 cuts64394 = true := by
 decide +kernel
def pointBounds64394 : List (Nat × Nat × Nat) := [(8444186624,114788150933923,114788539841356)]
theorem point_links_checked64394 : (cuts64394.take 1).map (fun c => (8444182529-1+2*2^10*c.k,114788144700544+c.lower,114788533607973+c.upper)) = pointBounds64394 := by
 decide +kernel
def cuts64395 : List PrefixCut := [⟨64,191363668,191363782⟩]
theorem checked64395 : checkPrefixCuts (2^48) 8444313601 10 Manual.Count131072.C064395.packed 64 cuts64395 = true := by
 decide +kernel
def cuts64396 : List PrefixCut := [⟨3,9699770,9699775⟩,
⟨64,191694031,191694140⟩]
theorem checked64396 : checkPrefixCuts (2^48) 8444444673 10 Manual.Count131072.C064396.packed 64 cuts64396 = true := by
 decide +kernel
def pointBounds64396 : List (Nat × Nat × Nat) := [(8444450816,114788538530627,114788927438282)]
theorem point_links_checked64396 : (cuts64396.take 1).map (fun c => (8444444673-1+2*2^10*c.k,114788528830857+c.lower,114788917738507+c.upper)) = pointBounds64396 := by
 decide +kernel
def cuts64397 : List PrefixCut := [⟨64,189424496,189424602⟩]
theorem checked64397 : checkPrefixCuts (2^48) 8444575745 10 Manual.Count131072.C064397.packed 64 cuts64397 = true := by
 decide +kernel
def cuts64398 : List PrefixCut := [⟨4,11566031,11566038⟩,
⟨64,187654985,187655095⟩]
theorem checked64398 : checkPrefixCuts (2^48) 8444706817 10 Manual.Count131072.C064398.packed 64 cuts64398 = true := by
 decide +kernel
def pointBounds64398 : List (Nat × Nat × Nat) := [(8444715008,114788921515415,114789310423287)]
theorem point_links_checked64398 : (cuts64398.take 1).map (fun c => (8444706817-1+2*2^10*c.k,114788909949384+c.lower,114789298857249+c.upper)) = pointBounds64398 := by
 decide +kernel
def cuts64399 : List PrefixCut := [⟨64,190618508,190618618⟩]
theorem checked64399 : checkPrefixCuts (2^48) 8444837889 10 Manual.Count131072.C064399.packed 64 cuts64399 = true := by
 decide +kernel
def cuts64400 : List PrefixCut := [⟨5,14932047,14932056⟩,
⟨64,191282154,191282266⟩]
theorem checked64400 : checkPrefixCuts (2^48) 8444968961 10 Manual.Count131072.C064400.packed 64 cuts64400 = true := by
 decide +kernel
def pointBounds64400 : List (Nat × Nat × Nat) := [(8444979200,114789303154924,114789692063018)]
theorem point_links_checked64400 : (cuts64400.take 1).map (fun c => (8444968961-1+2*2^10*c.k,114789288222877+c.lower,114789677130962+c.upper)) = pointBounds64400 := by
 decide +kernel
def cuts64401 : List PrefixCut := [⟨64,191379175,191379280⟩]
theorem checked64401 : checkPrefixCuts (2^48) 8445100033 10 Manual.Count131072.C064401.packed 64 cuts64401 = true := by
 decide +kernel
def cuts64402 : List PrefixCut := [⟨6,17664595,17664604⟩,
⟨64,193109332,193109440⟩]
theorem checked64402 : checkPrefixCuts (2^48) 8445231105 10 Manual.Count131072.C064402.packed 64 cuts64402 = true := by
 decide +kernel
def pointBounds64402 : List (Nat × Nat × Nat) := [(8445243392,114789688548801,114790077457112)]
theorem point_links_checked64402 : (cuts64402.take 1).map (fun c => (8445231105-1+2*2^10*c.k,114789670884206+c.lower,114790059792508+c.upper)) = pointBounds64402 := by
 decide +kernel
def cuts64403 : List PrefixCut := [⟨64,191406569,191406683⟩]
theorem checked64403 : checkPrefixCuts (2^48) 8445362177 10 Manual.Count131072.C064403.packed 64 cuts64403 = true := by
 decide +kernel
def cuts64404 : List PrefixCut := [⟨7,21330169,21330177⟩,
⟨64,191903524,191903627⟩]
theorem checked64404 : checkPrefixCuts (2^48) 8445493249 10 Manual.Count131072.C064404.packed 64 cuts64404 = true := by
 decide +kernel
def pointBounds64404 : List (Nat × Nat × Nat) := [(8445507584,114790076730276,114790465638808)]
theorem point_links_checked64404 : (cuts64404.take 1).map (fun c => (8445493249-1+2*2^10*c.k,114790055400107+c.lower,114790444308631+c.upper)) = pointBounds64404 := by
 decide +kernel
def cuts64405 : List PrefixCut := [⟨64,188767751,188767864⟩]
theorem checked64405 : checkPrefixCuts (2^48) 8445624321 10 Manual.Count131072.C064405.packed 64 cuts64405 = true := by
 decide +kernel
def cuts64406 : List PrefixCut := [⟨8,24495601,24495614⟩,
⟨64,190631130,190631241⟩]
theorem checked64406 : checkPrefixCuts (2^48) 8445755393 10 Manual.Count131072.C064406.packed 64 cuts64406 = true := by
 decide +kernel
def pointBounds64406 : List (Nat × Nat × Nat) := [(8445771776,114790460566983,114790849475736)]
theorem point_links_checked64406 : (cuts64406.take 1).map (fun c => (8445755393-1+2*2^10*c.k,114790436071382+c.lower,114790824980122+c.upper)) = pointBounds64406 := by
 decide +kernel
def cuts64407 : List PrefixCut := [⟨64,189861664,189861774⟩]
theorem checked64407 : checkPrefixCuts (2^48) 8445886465 10 Manual.Count131072.C064407.packed 64 cuts64407 = true := by
 decide +kernel
def cuts64408 : List PrefixCut := [⟨9,27394225,27394241⟩,
⟨64,192658102,192658210⟩]
theorem checked64408 : checkPrefixCuts (2^48) 8446017537 10 Manual.Count131072.C064408.packed 64 cuts64408 = true := by
 decide +kernel
def pointBounds64408 : List (Nat × Nat × Nat) := [(8446035968,114790843958401,114791232867378)]
theorem point_links_checked64408 : (cuts64408.take 1).map (fun c => (8446017537-1+2*2^10*c.k,114790816564176+c.lower,114791205473137+c.upper)) = pointBounds64408 := by
 decide +kernel
def cuts64409 : List PrefixCut := [⟨64,190322321,190322436⟩]
theorem checked64409 : checkPrefixCuts (2^48) 8446148609 10 Manual.Count131072.C064409.packed 64 cuts64409 = true := by
 decide +kernel
def cuts64410 : List PrefixCut := [⟨10,28559755,28559772⟩,
⟨64,191852319,191852428⟩]
theorem checked64410 : checkPrefixCuts (2^48) 8446279681 10 Manual.Count131072.C064410.packed 64 cuts64410 = true := by
 decide +kernel
def pointBounds64410 : List (Nat × Nat × Nat) := [(8446300160,114791228104354,114791617013555)]
theorem point_links_checked64410 : (cuts64410.take 1).map (fun c => (8446279681-1+2*2^10*c.k,114791199544599+c.lower,114791588453783+c.upper)) = pointBounds64410 := by
 decide +kernel
def cuts64411 : List PrefixCut := [⟨64,189250035,189250146⟩]
theorem checked64411 : checkPrefixCuts (2^48) 8446410753 10 Manual.Count131072.C064411.packed 64 cuts64411 = true := by
 decide +kernel
def cuts64412 : List PrefixCut := [⟨11,32824369,32824388⟩,
⟨64,189113793,189113907⟩]
theorem checked64412 : checkPrefixCuts (2^48) 8446541825 10 Manual.Count131072.C064412.packed 64 cuts64412 = true := by
 decide +kernel
def pointBounds64412 : List (Nat × Nat × Nat) := [(8446564352,114791613471322,114792002380745)]
theorem point_links_checked64412 : (cuts64412.take 1).map (fun c => (8446541825-1+2*2^10*c.k,114791580646953+c.lower,114791969556357+c.upper)) = pointBounds64412 := by
 decide +kernel
def cuts64413 : List PrefixCut := [⟨64,194442616,194442728⟩]
theorem checked64413 : checkPrefixCuts (2^48) 8446672897 10 Manual.Count131072.C064413.packed 64 cuts64413 = true := by
 decide +kernel
def cuts64414 : List PrefixCut := [⟨12,36555542,36555565⟩,
⟨64,191773779,191773893⟩]
theorem checked64414 : checkPrefixCuts (2^48) 8446803969 10 Manual.Count131072.C064414.packed 64 cuts64414 = true := by
 decide +kernel
def pointBounds64414 : List (Nat × Nat × Nat) := [(8446828544,114792000758904,114792389668557)]
theorem point_links_checked64414 : (cuts64414.take 1).map (fun c => (8446803969-1+2*2^10*c.k,114791964203362+c.lower,114792353112992+c.upper)) = pointBounds64414 := by
 decide +kernel
def cuts64415 : List PrefixCut := [⟨64,191504213,191504320⟩]
theorem checked64415 : checkPrefixCuts (2^48) 8446935041 10 Manual.Count131072.C064415.packed 64 cuts64415 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000137
