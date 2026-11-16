import PlattAssemblyKernel
import PlattCertificates.Count131072.C075376
import PlattCertificates.Count131072.C075377
import PlattCertificates.Count131072.C075378
import PlattCertificates.Count131072.C075379
import PlattCertificates.Count131072.C075380
import PlattCertificates.Count131072.C075381
import PlattCertificates.Count131072.C075382
import PlattCertificates.Count131072.C075383
import PlattCertificates.Count131072.C075384
import PlattCertificates.Count131072.C075385
import PlattCertificates.Count131072.C075386
import PlattCertificates.Count131072.C075387
import PlattCertificates.Count131072.C075388
import PlattCertificates.Count131072.C075389
import PlattCertificates.Count131072.C075390
import PlattCertificates.Count131072.C075391
import PlattCertificates.Count131072.C075392
import PlattCertificates.Count131072.C075393
import PlattCertificates.Count131072.C075394
import PlattCertificates.Count131072.C075395
import PlattCertificates.Count131072.C075396
import PlattCertificates.Count131072.C075397
import PlattCertificates.Count131072.C075398
import PlattCertificates.Count131072.C075399
import PlattCertificates.Count131072.C075400
import PlattCertificates.Count131072.C075401
import PlattCertificates.Count131072.C075402
import PlattCertificates.Count131072.C075403
import PlattCertificates.Count131072.C075404
import PlattCertificates.Count131072.C075405
import PlattCertificates.Count131072.C075406
import PlattCertificates.Count131072.C075407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000168
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75376 : List PrefixCut := [⟨19,47132555,47132583⟩,
⟨64,161559957,161560052⟩]
theorem checked75376 : checkPrefixCuts (2^48) 9883615233 10 Manual.Count131072.C075376.packed 64 cuts75376 = true := by
 decide +kernel
def pointBounds75376 : List (Nat × Nat × Nat) := [(9883654144,116719915693633,116720305737708)]
theorem point_links_checked75376 : (cuts75376.take 1).map (fun c => (9883615233-1+2*2^10*c.k,116719868561078+c.lower,116720258605125+c.upper)) = pointBounds75376 := by
 decide +kernel
def cuts75377 : List PrefixCut := [⟨64,161415432,161415531⟩]
theorem checked75377 : checkPrefixCuts (2^48) 9883746305 10 Manual.Count131072.C075377.packed 64 cuts75377 = true := by
 decide +kernel
def cuts75378 : List PrefixCut := [⟨42,108501421,108501486⟩,
⟨64,164289575,164289673⟩]
theorem checked75378 : checkPrefixCuts (2^48) 9883877377 10 Manual.Count131072.C075378.packed 64 cuts75378 = true := by
 decide +kernel
def pointBounds75378 : List (Nat × Nat × Nat) := [(9883963392,116720300037888,116720690082194)]
theorem point_links_checked75378 : (cuts75378.take 1).map (fun c => (9883877377-1+2*2^10*c.k,116720191536467+c.lower,116720581580708+c.upper)) = pointBounds75378 := by
 decide +kernel
def cuts75379 : List PrefixCut := [⟨64,165341062,165341162⟩]
theorem checked75379 : checkPrefixCuts (2^48) 9884008449 10 Manual.Count131072.C075379.packed 64 cuts75379 = true := by
 decide +kernel
def cuts75380 : List PrefixCut := [⟨64,164142817,164142920⟩]
theorem checked75380 : checkPrefixCuts (2^48) 9884139521 10 Manual.Count131072.C075380.packed 64 cuts75380 = true := by
 decide +kernel
def cuts75381 : List PrefixCut := [⟨1,2477503,2477505⟩,
⟨64,160581039,160581136⟩]
theorem checked75381 : checkPrefixCuts (2^48) 9884270593 10 Manual.Count131072.C075381.packed 64 cuts75381 = true := by
 decide +kernel
def pointBounds75381 : List (Nat × Nat × Nat) := [(9884272640,116720687787424,116721077831968)]
theorem point_links_checked75381 : (cuts75381.take 1).map (fun c => (9884270593-1+2*2^10*c.k,116720685309921+c.lower,116721075354463+c.upper)) = pointBounds75381 := by
 decide +kernel
def cuts75382 : List PrefixCut := [⟨64,160778233,160778331⟩]
theorem checked75382 : checkPrefixCuts (2^48) 9884401665 10 Manual.Count131072.C075382.packed 64 cuts75382 = true := by
 decide +kernel
def cuts75383 : List PrefixCut := [⟨24,61166936,61166968⟩,
⟨64,163367436,163367530⟩]
theorem checked75383 : checkPrefixCuts (2^48) 9884532737 10 Manual.Count131072.C075383.packed 64 cuts75383 = true := by
 decide +kernel
def pointBounds75383 : List (Nat × Nat × Nat) := [(9884581888,116721067836129,116721457880898)]
theorem point_links_checked75383 : (cuts75383.take 1).map (fun c => (9884532737-1+2*2^10*c.k,116721006669193+c.lower,116721396713930+c.upper)) = pointBounds75383 := by
 decide +kernel
def cuts75384 : List PrefixCut := [⟨64,161941475,161941574⟩]
theorem checked75384 : checkPrefixCuts (2^48) 9884663809 10 Manual.Count131072.C075384.packed 64 cuts75384 = true := by
 decide +kernel
def cuts75385 : List PrefixCut := [⟨47,119767544,119767617⟩,
⟨64,162451891,162451988⟩]
theorem checked75385 : checkPrefixCuts (2^48) 9884794881 10 Manual.Count131072.C075385.packed 64 cuts75385 = true := by
 decide +kernel
def pointBounds75385 : List (Nat × Nat × Nat) := [(9884891136,116721451745648,116721841790651)]
theorem point_links_checked75385 : (cuts75385.take 1).map (fun c => (9884794881-1+2*2^10*c.k,116721331978104+c.lower,116721722023034+c.upper)) = pointBounds75385 := by
 decide +kernel
def cuts75386 : List PrefixCut := [⟨64,163417883,163417981⟩]
theorem checked75386 : checkPrefixCuts (2^48) 9884925953 10 Manual.Count131072.C075386.packed 64 cuts75386 = true := by
 decide +kernel
def cuts75387 : List PrefixCut := [⟨64,163956731,163956830⟩]
theorem checked75387 : checkPrefixCuts (2^48) 9885057025 10 Manual.Count131072.C075387.packed 64 cuts75387 = true := by
 decide +kernel
def cuts75388 : List PrefixCut := [⟨6,15262274,15262284⟩,
⟨64,162303050,162303150⟩]
theorem checked75388 : checkPrefixCuts (2^48) 9885188097 10 Manual.Count131072.C075388.packed 64 cuts75388 = true := by
 decide +kernel
def pointBounds75388 : List (Nat × Nat × Nat) := [(9885200384,116721837066883,116722227112117)]
theorem point_links_checked75388 : (cuts75388.take 1).map (fun c => (9885188097-1+2*2^10*c.k,116721821804609+c.lower,116722211849833+c.upper)) = pointBounds75388 := by
 decide +kernel
def cuts75389 : List PrefixCut := [⟨64,164265599,164265704⟩]
theorem checked75389 : checkPrefixCuts (2^48) 9885319169 10 Manual.Count131072.C075389.packed 64 cuts75389 = true := by
 decide +kernel
def cuts75390 : List PrefixCut := [⟨29,72949279,72949322⟩,
⟨64,160476452,160476548⟩]
theorem checked75390 : checkPrefixCuts (2^48) 9885450241 10 Manual.Count131072.C075390.packed 64 cuts75390 = true := by
 decide +kernel
def pointBounds75390 : List (Nat × Nat × Nat) := [(9885509632,116722221322537,116722611368009)]
theorem point_links_checked75390 : (cuts75390.take 1).map (fun c => (9885450241-1+2*2^10*c.k,116722148373258+c.lower,116722538418687+c.upper)) = pointBounds75390 := by
 decide +kernel
def cuts75391 : List PrefixCut := [⟨64,160787514,160787615⟩]
theorem checked75391 : checkPrefixCuts (2^48) 9885581313 10 Manual.Count131072.C075391.packed 64 cuts75391 = true := by
 decide +kernel
def cuts75392 : List PrefixCut := [⟨52,134761510,134761587⟩,
⟨64,164942420,164942516⟩]
theorem checked75392 : checkPrefixCuts (2^48) 9885712385 10 Manual.Count131072.C075392.packed 64 cuts75392 = true := by
 decide +kernel
def pointBounds75392 : List (Nat × Nat × Nat) := [(9885818880,116722604398734,116722994444437)]
theorem point_links_checked75392 : (cuts75392.take 1).map (fun c => (9885712385-1+2*2^10*c.k,116722469637224+c.lower,116722859682850+c.upper)) = pointBounds75392 := by
 decide +kernel
def cuts75393 : List PrefixCut := [⟨64,163174941,163175042⟩]
theorem checked75393 : checkPrefixCuts (2^48) 9885843457 10 Manual.Count131072.C075393.packed 64 cuts75393 = true := by
 decide +kernel
def cuts75394 : List PrefixCut := [⟨64,161122789,161122887⟩]
theorem checked75394 : checkPrefixCuts (2^48) 9885974529 10 Manual.Count131072.C075394.packed 64 cuts75394 = true := by
 decide +kernel
def cuts75395 : List PrefixCut := [⟨11,28101604,28101619⟩,
⟨64,163939345,163939446⟩]
theorem checked75395 : checkPrefixCuts (2^48) 9886105601 10 Manual.Count131072.C075395.packed 64 cuts75395 = true := by
 decide +kernel
def pointBounds75395 : List (Nat × Nat × Nat) := [(9886128128,116722986978978,116723377024914)]
theorem point_links_checked75395 : (cuts75395.take 1).map (fun c => (9886105601-1+2*2^10*c.k,116722958877374+c.lower,116723348923295+c.upper)) = pointBounds75395 := by
 decide +kernel
def cuts75396 : List PrefixCut := [⟨64,160435213,160435315⟩]
theorem checked75396 : checkPrefixCuts (2^48) 9886236673 10 Manual.Count131072.C075396.packed 64 cuts75396 = true := by
 decide +kernel
def cuts75397 : List PrefixCut := [⟨34,86238391,86238443⟩,
⟨64,163450991,163451090⟩]
theorem checked75397 : checkPrefixCuts (2^48) 9886367745 10 Manual.Count131072.C075397.packed 64 cuts75397 = true := by
 decide +kernel
def pointBounds75397 : List (Nat × Nat × Nat) := [(9886437376,116723369490323,116723759536499)]
theorem point_links_checked75397 : (cuts75397.take 1).map (fun c => (9886367745-1+2*2^10*c.k,116723283251932+c.lower,116723673298056+c.upper)) = pointBounds75397 := by
 decide +kernel
def cuts75398 : List PrefixCut := [⟨64,161398951,161399046⟩]
theorem checked75398 : checkPrefixCuts (2^48) 9886498817 10 Manual.Count131072.C075398.packed 64 cuts75398 = true := by
 decide +kernel
def cuts75399 : List PrefixCut := [⟨57,146393186,146393277⟩,
⟨64,163560536,163560637⟩]
theorem checked75399 : checkPrefixCuts (2^48) 9886629889 10 Manual.Count131072.C075399.packed 64 cuts75399 = true := by
 decide +kernel
def pointBounds75399 : List (Nat × Nat × Nat) := [(9886746624,116723754495060,116724144541469)]
theorem point_links_checked75399 : (cuts75399.take 1).map (fun c => (9886629889-1+2*2^10*c.k,116723608101874+c.lower,116723998148192+c.upper)) = pointBounds75399 := by
 decide +kernel
def cuts75400 : List PrefixCut := [⟨64,161366203,161366302⟩]
theorem checked75400 : checkPrefixCuts (2^48) 9886760961 10 Manual.Count131072.C075400.packed 64 cuts75400 = true := by
 decide +kernel
def cuts75401 : List PrefixCut := [⟨64,160880084,160880177⟩]
theorem checked75401 : checkPrefixCuts (2^48) 9886892033 10 Manual.Count131072.C075401.packed 64 cuts75401 = true := by
 decide +kernel
def cuts75402 : List PrefixCut := [⟨16,40710779,40710803⟩,
⟨64,162073653,162073750⟩]
theorem checked75402 : checkPrefixCuts (2^48) 9887023105 10 Manual.Count131072.C075402.packed 64 cuts75402 = true := by
 decide +kernel
def pointBounds75402 : List (Nat × Nat × Nat) := [(9887055872,116724134619476,116724524666111)]
theorem point_links_checked75402 : (cuts75402.take 1).map (fun c => (9887023105-1+2*2^10*c.k,116724093908697+c.lower,116724483955308+c.upper)) = pointBounds75402 := by
 decide +kernel
def cuts75403 : List PrefixCut := [⟨64,160619611,160619710⟩]
theorem checked75403 : checkPrefixCuts (2^48) 9887154177 10 Manual.Count131072.C075403.packed 64 cuts75403 = true := by
 decide +kernel
def cuts75404 : List PrefixCut := [⟨39,97646114,97646173⟩,
⟨64,160361266,160361360⟩]
theorem checked75404 : checkPrefixCuts (2^48) 9887285249 10 Manual.Count131072.C075404.packed 64 cuts75404 = true := by
 decide +kernel
def pointBounds75404 : List (Nat × Nat × Nat) := [(9887365120,116724514248075,116724904294941)]
theorem point_links_checked75404 : (cuts75404.take 1).map (fun c => (9887285249-1+2*2^10*c.k,116724416601961+c.lower,116724806648768+c.upper)) = pointBounds75404 := by
 decide +kernel
def cuts75405 : List PrefixCut := [⟨64,160416089,160416179⟩]
theorem checked75405 : checkPrefixCuts (2^48) 9887416321 10 Manual.Count131072.C075405.packed 64 cuts75405 = true := by
 decide +kernel
def cuts75406 : List PrefixCut := [⟨62,157254093,157254186⟩,
⟨64,162691337,162691432⟩]
theorem checked75406 : checkPrefixCuts (2^48) 9887547393 10 Manual.Count131072.C075406.packed 64 cuts75406 = true := by
 decide +kernel
def pointBounds75406 : List (Nat × Nat × Nat) := [(9887674368,116724894633409,116725284680493)]
theorem point_links_checked75406 : (cuts75406.take 1).map (fun c => (9887547393-1+2*2^10*c.k,116724737379316+c.lower,116725127426307+c.upper)) = pointBounds75406 := by
 decide +kernel
def cuts75407 : List PrefixCut := [⟨64,162603776,162603868⟩]
theorem checked75407 : checkPrefixCuts (2^48) 9887678465 10 Manual.Count131072.C075407.packed 64 cuts75407 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000168
