import PlattAssemblyKernel
import PlattCertificates.Count131072.C072496
import PlattCertificates.Count131072.C072497
import PlattCertificates.Count131072.C072498
import PlattCertificates.Count131072.C072499
import PlattCertificates.Count131072.C072500
import PlattCertificates.Count131072.C072501
import PlattCertificates.Count131072.C072502
import PlattCertificates.Count131072.C072503
import PlattCertificates.Count131072.C072504
import PlattCertificates.Count131072.C072505
import PlattCertificates.Count131072.C072506
import PlattCertificates.Count131072.C072507
import PlattCertificates.Count131072.C072508
import PlattCertificates.Count131072.C072509
import PlattCertificates.Count131072.C072510
import PlattCertificates.Count131072.C072511
import PlattCertificates.Count131072.C072512
import PlattCertificates.Count131072.C072513
import PlattCertificates.Count131072.C072514
import PlattCertificates.Count131072.C072515
import PlattCertificates.Count131072.C072516
import PlattCertificates.Count131072.C072517
import PlattCertificates.Count131072.C072518
import PlattCertificates.Count131072.C072519
import PlattCertificates.Count131072.C072520
import PlattCertificates.Count131072.C072521
import PlattCertificates.Count131072.C072522
import PlattCertificates.Count131072.C072523
import PlattCertificates.Count131072.C072524
import PlattCertificates.Count131072.C072525
import PlattCertificates.Count131072.C072526
import PlattCertificates.Count131072.C072527
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000078
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72496 : List PrefixCut := [⟨64,168804517,168804618⟩]
theorem checked72496 : checkPrefixCuts (2^48) 9506127873 10 Manual.Count131072.C072496.packed 64 cuts72496 = true := by
 decide +kernel
def cuts72497 : List PrefixCut := [⟨64,168002737,168002836⟩]
theorem checked72497 : checkPrefixCuts (2^48) 9506258945 10 Manual.Count131072.C072497.packed 64 cuts72497 = true := by
 decide +kernel
def cuts72498 : List PrefixCut := [⟨18,47818475,47818500⟩,
⟨64,168859075,168859176⟩]
theorem checked72498 : checkPrefixCuts (2^48) 9506390017 10 Manual.Count131072.C072498.packed 64 cuts72498 = true := by
 decide +kernel
def pointBounds72498 : List (Nat × Nat × Nat) := [(9506426880,116243509297594,116243899057012)]
theorem point_links_checked72498 : (cuts72498.take 1).map (fun c => (9506390017-1+2*2^10*c.k,116243461479119+c.lower,116243851238512+c.upper)) = pointBounds72498 := by
 decide +kernel
def cuts72499 : List PrefixCut := [⟨64,170870131,170870234⟩]
theorem checked72499 : checkPrefixCuts (2^48) 9506521089 10 Manual.Count131072.C072499.packed 64 cuts72499 = true := by
 decide +kernel
def cuts72500 : List PrefixCut := [⟨36,95841388,95841441⟩,
⟨64,170038748,170038845⟩]
theorem checked72500 : checkPrefixCuts (2^48) 9506652161 10 Manual.Count131072.C072500.packed 64 cuts72500 = true := by
 decide +kernel
def pointBounds72500 : List (Nat × Nat × Nat) := [(9506725888,116243897049713,116244286809363)]
theorem point_links_checked72500 : (cuts72500.take 1).map (fun c => (9506652161-1+2*2^10*c.k,116243801208325+c.lower,116244190967922+c.upper)) = pointBounds72500 := by
 decide +kernel
def cuts72501 : List PrefixCut := [⟨64,167430925,167431022⟩]
theorem checked72501 : checkPrefixCuts (2^48) 9506783233 10 Manual.Count131072.C072501.packed 64 cuts72501 = true := by
 decide +kernel
def cuts72502 : List PrefixCut := [⟨54,145667497,145667581⟩,
⟨64,172047344,172047444⟩]
theorem checked72502 : checkPrefixCuts (2^48) 9506914305 10 Manual.Count131072.C072502.packed 64 cuts72502 = true := by
 decide +kernel
def pointBounds72502 : List (Nat × Nat × Nat) := [(9507024896,116244284345495,116244674105370)]
theorem point_links_checked72502 : (cuts72502.take 1).map (fun c => (9506914305-1+2*2^10*c.k,116244138677998+c.lower,116244528437789+c.upper)) = pointBounds72502 := by
 decide +kernel
def cuts72503 : List PrefixCut := [⟨64,165649906,165650005⟩]
theorem checked72503 : checkPrefixCuts (2^48) 9507045377 10 Manual.Count131072.C072503.packed 64 cuts72503 = true := by
 decide +kernel
def cuts72504 : List PrefixCut := [⟨64,171065592,171065695⟩]
theorem checked72504 : checkPrefixCuts (2^48) 9507176449 10 Manual.Count131072.C072504.packed 64 cuts72504 = true := by
 decide +kernel
def cuts72505 : List PrefixCut := [⟨8,21434843,21434857⟩,
⟨64,167332887,167332987⟩]
theorem checked72505 : checkPrefixCuts (2^48) 9507307521 10 Manual.Count131072.C072505.packed 64 cuts72505 = true := by
 decide +kernel
def pointBounds72505 : List (Nat × Nat × Nat) := [(9507323904,116244668875683,116245058635790)]
theorem point_links_checked72505 : (cuts72505.take 1).map (fun c => (9507307521-1+2*2^10*c.k,116244647440840+c.lower,116245037200933+c.upper)) = pointBounds72505 := by
 decide +kernel
def cuts72506 : List PrefixCut := [⟨64,167804264,167804361⟩]
theorem checked72506 : checkPrefixCuts (2^48) 9507438593 10 Manual.Count131072.C072506.packed 64 cuts72506 = true := by
 decide +kernel
def cuts72507 : List PrefixCut := [⟨26,68713817,68713859⟩,
⟨64,169637467,169637568⟩]
theorem checked72507 : checkPrefixCuts (2^48) 9507569665 10 Manual.Count131072.C072507.packed 64 cuts72507 = true := by
 decide +kernel
def pointBounds72507 : List (Nat × Nat × Nat) := [(9507622912,116245051291808,116245441052140)]
theorem point_links_checked72507 : (cuts72507.take 1).map (fun c => (9507569665-1+2*2^10*c.k,116244982577991+c.lower,116245372338281+c.upper)) = pointBounds72507 := by
 decide +kernel
def cuts72508 : List PrefixCut := [⟨64,167059510,167059614⟩]
theorem checked72508 : checkPrefixCuts (2^48) 9507700737 10 Manual.Count131072.C072508.packed 64 cuts72508 = true := by
 decide +kernel
def cuts72509 : List PrefixCut := [⟨44,117440611,117440681⟩,
⟨64,168863079,168863182⟩]
theorem checked72509 : checkPrefixCuts (2^48) 9507831809 10 Manual.Count131072.C072509.packed 64 cuts72509 = true := by
 decide +kernel
def pointBounds72509 : List (Nat × Nat × Nat) := [(9507921920,116245436715579,116245826476144)]
theorem point_links_checked72509 : (cuts72509.take 1).map (fun c => (9507831809-1+2*2^10*c.k,116245319274968+c.lower,116245709035463+c.upper)) = pointBounds72509 := by
 decide +kernel
def cuts72510 : List PrefixCut := [⟨64,170785000,170785097⟩]
theorem checked72510 : checkPrefixCuts (2^48) 9507962881 10 Manual.Count131072.C072510.packed 64 cuts72510 = true := by
 decide +kernel
def cuts72511 : List PrefixCut := [⟨62,164062699,164062797⟩,
⟨64,169302485,169302587⟩]
theorem checked72511 : checkPrefixCuts (2^48) 9508093953 10 Manual.Count131072.C072511.packed 64 cuts72511 = true := by
 decide +kernel
def pointBounds72511 : List (Nat × Nat × Nat) := [(9508220928,116245822985746,116246212746539)]
theorem point_links_checked72511 : (cuts72511.take 1).map (fun c => (9508093953-1+2*2^10*c.k,116245658923047+c.lower,116246048683742+c.upper)) = pointBounds72511 := by
 decide +kernel
def cuts72512 : List PrefixCut := [⟨64,172171634,172171735⟩]
theorem checked72512 : checkPrefixCuts (2^48) 9508225025 10 Manual.Count131072.C072512.packed 64 cuts72512 = true := by
 decide +kernel
def cuts72513 : List PrefixCut := [⟨64,169208997,169209100⟩]
theorem checked72513 : checkPrefixCuts (2^48) 9508356097 10 Manual.Count131072.C072513.packed 64 cuts72513 = true := by
 decide +kernel
def cuts72514 : List PrefixCut := [⟨16,42272281,42272308⟩,
⟨64,168969840,168969945⟩]
theorem checked72514 : checkPrefixCuts (2^48) 9508487169 10 Manual.Count131072.C072514.packed 64 cuts72514 = true := by
 decide +kernel
def pointBounds72514 : List (Nat × Nat × Nat) := [(9508519936,116246211878444,116246601639472)]
theorem point_links_checked72514 : (cuts72514.take 1).map (fun c => (9508487169-1+2*2^10*c.k,116246169606163+c.lower,116246559367164+c.upper)) = pointBounds72514 := by
 decide +kernel
def cuts72515 : List PrefixCut := [⟨64,168937924,168938022⟩]
theorem checked72515 : checkPrefixCuts (2^48) 9508618241 10 Manual.Count131072.C072515.packed 64 cuts72515 = true := by
 decide +kernel
def cuts72516 : List PrefixCut := [⟨34,89692745,89692800⟩,
⟨64,169231604,169231703⟩]
theorem checked72516 : checkPrefixCuts (2^48) 9508749313 10 Manual.Count131072.C072516.packed 64 cuts72516 = true := by
 decide +kernel
def pointBounds72516 : List (Nat × Nat × Nat) := [(9508818944,116246597206672,116246986967931)]
theorem point_links_checked72516 : (cuts72516.take 1).map (fun c => (9508749313-1+2*2^10*c.k,116246507513927+c.lower,116246897275131+c.upper)) = pointBounds72516 := by
 decide +kernel
def cuts72517 : List PrefixCut := [⟨64,167690015,167690115⟩]
theorem checked72517 : checkPrefixCuts (2^48) 9508880385 10 Manual.Count131072.C072517.packed 64 cuts72517 = true := by
 decide +kernel
def cuts72518 : List PrefixCut := [⟨52,135127153,135127238⟩,
⟨64,166030063,166030163⟩]
theorem checked72518 : checkPrefixCuts (2^48) 9509011457 10 Manual.Count131072.C072518.packed 64 cuts72518 = true := by
 decide +kernel
def pointBounds72518 : List (Nat × Nat × Nat) := [(9509117952,116246979562699,116247369324187)]
theorem point_links_checked72518 : (cuts72518.take 1).map (fun c => (9509011457-1+2*2^10*c.k,116246844435546+c.lower,116247234196949+c.upper)) = pointBounds72518 := by
 decide +kernel
def cuts72519 : List PrefixCut := [⟨64,169609396,169609501⟩]
theorem checked72519 : checkPrefixCuts (2^48) 9509142529 10 Manual.Count131072.C072519.packed 64 cuts72519 = true := by
 decide +kernel
def cuts72520 : List PrefixCut := [⟨64,167683080,167683182⟩]
theorem checked72520 : checkPrefixCuts (2^48) 9509273601 10 Manual.Count131072.C072520.packed 64 cuts72520 = true := by
 decide +kernel
def cuts72521 : List PrefixCut := [⟨6,15273400,15273410⟩,
⟨64,168095158,168095257⟩]
theorem checked72521 : checkPrefixCuts (2^48) 9509404673 10 Manual.Count131072.C072521.packed 64 cuts72521 = true := by
 decide +kernel
def pointBounds72521 : List (Nat × Nat × Nat) := [(9509416960,116247363031485,116247752793205)]
theorem point_links_checked72521 : (cuts72521.take 1).map (fun c => (9509404673-1+2*2^10*c.k,116247347758085+c.lower,116247737519795+c.upper)) = pointBounds72521 := by
 decide +kernel
def cuts72522 : List PrefixCut := [⟨64,171615132,171615238⟩]
theorem checked72522 : checkPrefixCuts (2^48) 9509535745 10 Manual.Count131072.C072522.packed 64 cuts72522 = true := by
 decide +kernel
def cuts72523 : List PrefixCut := [⟨24,63282109,63282149⟩,
⟨64,168623301,168623407⟩]
theorem checked72523 : checkPrefixCuts (2^48) 9509666817 10 Manual.Count131072.C072523.packed 64 cuts72523 = true := by
 decide +kernel
def pointBounds72523 : List (Nat × Nat × Nat) := [(9509715968,116247750750484,116248140512439)]
theorem point_links_checked72523 : (cuts72523.take 1).map (fun c => (9509666817-1+2*2^10*c.k,116247687468375+c.lower,116248077230290+c.upper)) = pointBounds72523 := by
 decide +kernel
def cuts72524 : List PrefixCut := [⟨64,166874693,166874794⟩]
theorem checked72524 : checkPrefixCuts (2^48) 9509797889 10 Manual.Count131072.C072524.packed 64 cuts72524 = true := by
 decide +kernel
def cuts72525 : List PrefixCut := [⟨42,110252058,110252126⟩,
⟨64,169920953,169921053⟩]
theorem checked72525 : checkPrefixCuts (2^48) 9509928961 10 Manual.Count131072.C072525.packed 64 cuts72525 = true := by
 decide +kernel
def pointBounds72525 : List (Nat × Nat × Nat) := [(9510014976,116248133218427,116248522980617)]
theorem point_links_checked72525 : (cuts72525.take 1).map (fun c => (9509928961-1+2*2^10*c.k,116248022966369+c.lower,116248412728491+c.upper)) = pointBounds72525 := by
 decide +kernel
def cuts72526 : List PrefixCut := [⟨64,168024387,168024488⟩]
theorem checked72526 : checkPrefixCuts (2^48) 9510060033 10 Manual.Count131072.C072526.packed 64 cuts72526 = true := by
 decide +kernel
def cuts72527 : List PrefixCut := [⟨60,161066843,161066937⟩,
⟨64,172017655,172017757⟩]
theorem checked72527 : checkPrefixCuts (2^48) 9510191105 10 Manual.Count131072.C072527.packed 64 cuts72527 = true := by
 decide +kernel
def pointBounds72527 : List (Nat × Nat × Nat) := [(9510313984,116248521978552,116248911740969)]
theorem point_links_checked72527 : (cuts72527.take 1).map (fun c => (9510191105-1+2*2^10*c.k,116248360911709+c.lower,116248750674032+c.upper)) = pointBounds72527 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000078
