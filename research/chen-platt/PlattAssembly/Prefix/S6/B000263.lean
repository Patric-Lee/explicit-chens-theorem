import PlattAssemblyKernel
import PlattCertificates.Count131072.C058416
import PlattCertificates.Count131072.C058417
import PlattCertificates.Count131072.C058418
import PlattCertificates.Count131072.C058419
import PlattCertificates.Count131072.C058420
import PlattCertificates.Count131072.C058421
import PlattCertificates.Count131072.C058422
import PlattCertificates.Count131072.C058423
import PlattCertificates.Count131072.C058424
import PlattCertificates.Count131072.C058425
import PlattCertificates.Count131072.C058426
import PlattCertificates.Count131072.C058427
import PlattCertificates.Count131072.C058428
import PlattCertificates.Count131072.C058429
import PlattCertificates.Count131072.C058430
import PlattCertificates.Count131072.C058431
import PlattCertificates.Count131072.C058432
import PlattCertificates.Count131072.C058433
import PlattCertificates.Count131072.C058434
import PlattCertificates.Count131072.C058435
import PlattCertificates.Count131072.C058436
import PlattCertificates.Count131072.C058437
import PlattCertificates.Count131072.C058438
import PlattCertificates.Count131072.C058439
import PlattCertificates.Count131072.C058440
import PlattCertificates.Count131072.C058441
import PlattCertificates.Count131072.C058442
import PlattCertificates.Count131072.C058443
import PlattCertificates.Count131072.C058444
import PlattCertificates.Count131072.C058445
import PlattCertificates.Count131072.C058446
import PlattCertificates.Count131072.C058447
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000263
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58416 : List PrefixCut := [⟨64,206898213,206898330⟩]
theorem checked58416 : checkPrefixCuts (2^48) 7660634113 10 Manual.Count131072.C058416.packed 64 cuts58416 = true := by
 decide +kernel
def cuts58417 : List PrefixCut := [⟨12,40930967,40930990⟩,
⟨64,211524200,211524320⟩]
theorem checked58417 : checkPrefixCuts (2^48) 7660765185 10 Manual.Count131072.C058417.packed 64 cuts58417 = true := by
 decide +kernel
def pointBounds58417 : List (Nat × Nat × Nat) := [(7660789760,113586506637848,113586894856574)]
theorem point_links_checked58417 : (cuts58417.take 1).map (fun c => (7660765185-1+2*2^10*c.k,113586465706881+c.lower,113586853925584+c.upper)) = pointBounds58417 := by
 decide +kernel
def cuts58418 : List PrefixCut := [⟨64,210197851,210197972⟩]
theorem checked58418 : checkPrefixCuts (2^48) 7660896257 10 Manual.Count131072.C058418.packed 64 cuts58418 = true := by
 decide +kernel
def cuts58419 : List PrefixCut := [⟨1,3269961,3269963⟩,
⟨64,211810878,211810998⟩]
theorem checked58419 : checkPrefixCuts (2^48) 7661027329 10 Manual.Count131072.C058419.packed 64 cuts58419 = true := by
 decide +kernel
def pointBounds58419 : List (Nat × Nat × Nat) := [(7661029376,113586890698893,113587278917839)]
theorem point_links_checked58419 : (cuts58419.take 1).map (fun c => (7661027329-1+2*2^10*c.k,113586887428932+c.lower,113587275647876+c.upper)) = pointBounds58419 := by
 decide +kernel
def cuts58420 : List PrefixCut := [⟨54,177308443,177308543⟩,
⟨64,209492624,209492744⟩]
theorem checked58420 : checkPrefixCuts (2^48) 7661158401 10 Manual.Count131072.C058420.packed 64 cuts58420 = true := by
 decide +kernel
def pointBounds58420 : List (Nat × Nat × Nat) := [(7661268992,113587276548253,113587664767417)]
theorem point_links_checked58420 : (cuts58420.take 1).map (fun c => (7661158401-1+2*2^10*c.k,113587099239810+c.lower,113587487458874+c.upper)) = pointBounds58420 := by
 decide +kernel
def cuts58421 : List PrefixCut := [⟨64,211032092,211032212⟩]
theorem checked58421 : checkPrefixCuts (2^48) 7661289473 10 Manual.Count131072.C058421.packed 64 cuts58421 = true := by
 decide +kernel
def cuts58422 : List PrefixCut := [⟨43,142694447,142694529⟩,
⟨64,213159337,213159458⟩]
theorem checked58422 : checkPrefixCuts (2^48) 7661420545 10 Manual.Count131072.C058422.packed 64 cuts58422 = true := by
 decide +kernel
def pointBounds58422 : List (Nat × Nat × Nat) := [(7661508608,113587662458973,113588050678359)]
theorem point_links_checked58422 : (cuts58422.take 1).map (fun c => (7661420545-1+2*2^10*c.k,113587519764526+c.lower,113587907983830+c.upper)) = pointBounds58422 := by
 decide +kernel
def cuts58423 : List PrefixCut := [⟨64,209371642,209371763⟩]
theorem checked58423 : checkPrefixCuts (2^48) 7661551617 10 Manual.Count131072.C058423.packed 64 cuts58423 = true := by
 decide +kernel
def cuts58424 : List PrefixCut := [⟨32,106209109,106209169⟩,
⟨64,212674474,212674594⟩]
theorem checked58424 : checkPrefixCuts (2^48) 7661682689 10 Manual.Count131072.C058424.packed 64 cuts58424 = true := by
 decide +kernel
def pointBounds58424 : List (Nat × Nat × Nat) := [(7661748224,113588048504614,113588436724220)]
theorem point_links_checked58424 : (cuts58424.take 1).map (fun c => (7661682689-1+2*2^10*c.k,113587942295505+c.lower,113588330515051+c.upper)) = pointBounds58424 := by
 decide +kernel
def cuts58425 : List PrefixCut := [⟨64,211238062,211238180⟩]
theorem checked58425 : checkPrefixCuts (2^48) 7661813761 10 Manual.Count131072.C058425.packed 64 cuts58425 = true := by
 decide +kernel
def cuts58426 : List PrefixCut := [⟨21,69101618,69101659⟩,
⟨64,213144745,213144868⟩]
theorem checked58426 : checkPrefixCuts (2^48) 7661944833 10 Manual.Count131072.C058426.packed 64 cuts58426 = true := by
 decide +kernel
def pointBounds58426 : List (Nat × Nat × Nat) := [(7661987840,113588435309659,113588823529484)]
theorem point_links_checked58426 : (cuts58426.take 1).map (fun c => (7661944833-1+2*2^10*c.k,113588366208041+c.lower,113588754427825+c.upper)) = pointBounds58426 := by
 decide +kernel
def cuts58427 : List PrefixCut := [⟨64,211157378,211157500⟩]
theorem checked58427 : checkPrefixCuts (2^48) 7662075905 10 Manual.Count131072.C058427.packed 64 cuts58427 = true := by
 decide +kernel
def cuts58428 : List PrefixCut := [⟨10,33061893,33061912⟩,
⟨64,212366014,212366136⟩]
theorem checked58428 : checkPrefixCuts (2^48) 7662206977 10 Manual.Count131072.C058428.packed 64 cuts58428 = true := by
 decide +kernel
def pointBounds58428 : List (Nat × Nat × Nat) := [(7662227456,113588823572057,113589211792105)]
theorem point_links_checked58428 : (cuts58428.take 1).map (fun c => (7662206977-1+2*2^10*c.k,113588790510164+c.lower,113589178730193+c.upper)) = pointBounds58428 := by
 decide +kernel
def cuts58429 : List PrefixCut := [⟨63,210672627,210672747⟩,
⟨64,213795037,213795159⟩]
theorem checked58429 : checkPrefixCuts (2^48) 7662338049 10 Manual.Count131072.C058429.packed 64 cuts58429 = true := by
 decide +kernel
def pointBounds58429 : List (Nat × Nat × Nat) := [(7662467072,113589213548805,113589601769076)]
theorem point_links_checked58429 : (cuts58429.take 1).map (fun c => (7662338049-1+2*2^10*c.k,113589002876178+c.lower,113589391096329+c.upper)) = pointBounds58429 := by
 decide +kernel
def cuts58430 : List PrefixCut := [⟨64,214305650,214305772⟩]
theorem checked58430 : checkPrefixCuts (2^48) 7662469121 10 Manual.Count131072.C058430.packed 64 cuts58430 = true := by
 decide +kernel
def cuts58431 : List PrefixCut := [⟨52,171728384,171728481⟩,
⟨64,210224603,210224723⟩]
theorem checked58431 : checkPrefixCuts (2^48) 7662600193 10 Manual.Count131072.C058431.packed 64 cuts58431 = true := by
 decide +kernel
def pointBounds58431 : List (Nat × Nat × Nat) := [(7662706688,113589602705249,113589990925741)]
theorem point_links_checked58431 : (cuts58431.take 1).map (fun c => (7662600193-1+2*2^10*c.k,113589430976865+c.lower,113589819197260+c.upper)) = pointBounds58431 := by
 decide +kernel
def cuts58432 : List PrefixCut := [⟨64,210074069,210074185⟩]
theorem checked58432 : checkPrefixCuts (2^48) 7662731265 10 Manual.Count131072.C058432.packed 64 cuts58432 = true := by
 decide +kernel
def cuts58433 : List PrefixCut := [⟨41,135174290,135174365⟩,
⟨64,210841857,210841978⟩]
theorem checked58433 : checkPrefixCuts (2^48) 7662862337 10 Manual.Count131072.C058433.packed 64 cuts58433 = true := by
 decide +kernel
def pointBounds58433 : List (Nat × Nat × Nat) := [(7662946304,113589986449827,113590374670533)]
theorem point_links_checked58433 : (cuts58433.take 1).map (fun c => (7662862337-1+2*2^10*c.k,113589851275537+c.lower,113590239496168+c.upper)) = pointBounds58433 := by
 decide +kernel
def cuts58434 : List PrefixCut := [⟨64,211866721,211866841⟩]
theorem checked58434 : checkPrefixCuts (2^48) 7662993409 10 Manual.Count131072.C058434.packed 64 cuts58434 = true := by
 decide +kernel
def cuts58435 : List PrefixCut := [⟨30,99136803,99136861⟩,
⟨64,212634437,212634560⟩]
theorem checked58435 : checkPrefixCuts (2^48) 7663124481 10 Manual.Count131072.C058435.packed 64 cuts58435 = true := by
 decide +kernel
def pointBounds58435 : List (Nat × Nat × Nat) := [(7663185920,113590373120918,113590761341848)]
theorem point_links_checked58435 : (cuts58435.take 1).map (fun c => (7663124481-1+2*2^10*c.k,113590273984115+c.lower,113590662204987+c.upper)) = pointBounds58435 := by
 decide +kernel
def cuts58436 : List PrefixCut := [⟨64,213145032,213145154⟩]
theorem checked58436 : checkPrefixCuts (2^48) 7663255553 10 Manual.Count131072.C058436.packed 64 cuts58436 = true := by
 decide +kernel
def cuts58437 : List PrefixCut := [⟨19,61485585,61485619⟩,
⟨64,211304897,211305019⟩]
theorem checked58437 : checkPrefixCuts (2^48) 7663386625 10 Manual.Count131072.C058437.packed 64 cuts58437 = true := by
 decide +kernel
def pointBounds58437 : List (Nat × Nat × Nat) := [(7663425536,113590761249169,113591149470320)]
theorem point_links_checked58437 : (cuts58437.take 1).map (fun c => (7663386625-1+2*2^10*c.k,113590699763584+c.lower,113591087984701+c.upper)) = pointBounds58437 := by
 decide +kernel
def cuts58438 : List PrefixCut := [⟨64,211154383,211154501⟩]
theorem checked58438 : checkPrefixCuts (2^48) 7663517697 10 Manual.Count131072.C058438.packed 64 cuts58438 = true := by
 decide +kernel
def cuts58439 : List PrefixCut := [⟨8,26334360,26334376⟩,
⟨64,212987184,212987310⟩]
theorem checked58439 : checkPrefixCuts (2^48) 7663648769 10 Manual.Count131072.C058439.packed 64 cuts58439 = true := by
 decide +kernel
def pointBounds58439 : List (Nat × Nat × Nat) := [(7663665152,113591148557224,113591536778597)]
theorem point_links_checked58439 : (cuts58439.take 1).map (fun c => (7663648769-1+2*2^10*c.k,113591122222864+c.lower,113591510444221+c.upper)) = pointBounds58439 := by
 decide +kernel
def cuts58440 : List PrefixCut := [⟨61,199541310,199541426⟩,
⟨64,209971872,209971994⟩]
theorem checked58440 : checkPrefixCuts (2^48) 7663779841 10 Manual.Count131072.C058440.packed 64 cuts58440 = true := by
 decide +kernel
def pointBounds58440 : List (Nat × Nat × Nat) := [(7663904768,113591534751358,113591922972957)]
theorem point_links_checked58440 : (cuts58440.take 1).map (fun c => (7663779841-1+2*2^10*c.k,113591335210048+c.lower,113591723431531+c.upper)) = pointBounds58440 := by
 decide +kernel
def cuts58441 : List PrefixCut := [⟨64,215881332,215881453⟩]
theorem checked58441 : checkPrefixCuts (2^48) 7663910913 10 Manual.Count131072.C058441.packed 64 cuts58441 = true := by
 decide +kernel
def cuts58442 : List PrefixCut := [⟨50,163983575,163983670⟩,
⟨64,209230169,209230291⟩]
theorem checked58442 : checkPrefixCuts (2^48) 7664041985 10 Manual.Count131072.C058442.packed 64 cuts58442 = true := by
 decide +kernel
def pointBounds58442 : List (Nat × Nat × Nat) := [(7664144384,113591925046827,113592313268648)]
theorem point_links_checked58442 : (cuts58442.take 1).map (fun c => (7664041985-1+2*2^10*c.k,113591761063252+c.lower,113592149284978+c.upper)) = pointBounds58442 := by
 decide +kernel
def cuts58443 : List PrefixCut := [⟨64,209997821,209997941⟩]
theorem checked58443 : checkPrefixCuts (2^48) 7664173057 10 Manual.Count131072.C058443.packed 64 cuts58443 = true := by
 decide +kernel
def cuts58444 : List PrefixCut := [⟨39,128648520,128648596⟩,
⟨64,211132712,211132832⟩]
theorem checked58444 : checkPrefixCuts (2^48) 7664304129 10 Manual.Count131072.C058444.packed 64 cuts58444 = true := by
 decide +kernel
def pointBounds58444 : List (Nat × Nat × Nat) := [(7664384000,113592308939762,113592697161806)]
theorem point_links_checked58444 : (cuts58444.take 1).map (fun c => (7664304129-1+2*2^10*c.k,113592180291242+c.lower,113592568513210+c.upper)) = pointBounds58444 := by
 decide +kernel
def cuts58445 : List PrefixCut := [⟨64,211055648,211055772⟩]
theorem checked58445 : checkPrefixCuts (2^48) 7664435201 10 Manual.Count131072.C058445.packed 64 cuts58445 = true := by
 decide +kernel
def cuts58446 : List PrefixCut := [⟨28,91589755,91589809⟩,
⟨64,212410813,212410935⟩]
theorem checked58446 : checkPrefixCuts (2^48) 7664566273 10 Manual.Count131072.C058446.packed 64 cuts58446 = true := by
 decide +kernel
def pointBounds58446 : List (Nat × Nat × Nat) := [(7664623616,113592694069357,113593082291623)]
theorem point_links_checked58446 : (cuts58446.take 1).map (fun c => (7664566273-1+2*2^10*c.k,113592602479602+c.lower,113592990701814+c.upper)) = pointBounds58446 := by
 decide +kernel
def cuts58447 : List PrefixCut := [⟨64,212664242,212664363⟩]
theorem checked58447 : checkPrefixCuts (2^48) 7664697345 10 Manual.Count131072.C058447.packed 64 cuts58447 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000263
