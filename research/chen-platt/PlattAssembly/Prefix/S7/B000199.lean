import PlattAssemblyKernel
import PlattCertificates.Count131072.C066368
import PlattCertificates.Count131072.C066369
import PlattCertificates.Count131072.C066370
import PlattCertificates.Count131072.C066371
import PlattCertificates.Count131072.C066372
import PlattCertificates.Count131072.C066373
import PlattCertificates.Count131072.C066374
import PlattCertificates.Count131072.C066375
import PlattCertificates.Count131072.C066376
import PlattCertificates.Count131072.C066377
import PlattCertificates.Count131072.C066378
import PlattCertificates.Count131072.C066379
import PlattCertificates.Count131072.C066380
import PlattCertificates.Count131072.C066381
import PlattCertificates.Count131072.C066382
import PlattCertificates.Count131072.C066383
import PlattCertificates.Count131072.C066384
import PlattCertificates.Count131072.C066385
import PlattCertificates.Count131072.C066386
import PlattCertificates.Count131072.C066387
import PlattCertificates.Count131072.C066388
import PlattCertificates.Count131072.C066389
import PlattCertificates.Count131072.C066390
import PlattCertificates.Count131072.C066391
import PlattCertificates.Count131072.C066392
import PlattCertificates.Count131072.C066393
import PlattCertificates.Count131072.C066394
import PlattCertificates.Count131072.C066395
import PlattCertificates.Count131072.C066396
import PlattCertificates.Count131072.C066397
import PlattCertificates.Count131072.C066398
import PlattCertificates.Count131072.C066399
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000199
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66368 : List PrefixCut := [⟨64,184189643,184189750⟩]
theorem checked66368 : checkPrefixCuts (2^48) 8702918657 10 Manual.Count131072.C066368.packed 64 cuts66368 = true := by
 decide +kernel
def cuts66369 : List PrefixCut := [⟨59,172640923,172641022⟩,
⟨64,187938514,187938622⟩]
theorem checked66369 : checkPrefixCuts (2^48) 8703049729 10 Manual.Count131072.C066369.packed 64 cuts66369 = true := by
 decide +kernel
def pointBounds66369 : List (Nat × Nat × Nat) := [(8703170560,115159908744262,115160297866978)]
theorem point_links_checked66369 : (cuts66369.take 1).map (fun c => (8703049729-1+2*2^10*c.k,115159736103339+c.lower,115160125225956+c.upper)) = pointBounds66369 := by
 decide +kernel
def cuts66370 : List PrefixCut := [⟨64,184669199,184669310⟩]
theorem checked66370 : checkPrefixCuts (2^48) 8703180801 10 Manual.Count131072.C066370.packed 64 cuts66370 = true := by
 decide +kernel
def cuts66371 : List PrefixCut := [⟨64,186930303,186930414⟩]
theorem checked66371 : checkPrefixCuts (2^48) 8703311873 10 Manual.Count131072.C066371.packed 64 cuts66371 = true := by
 decide +kernel
def pointBounds66371 : List (Nat × Nat × Nat) := [(8703442944,115160295641355,115160684764302)]
theorem point_links_checked66371 : (cuts66371.take 1).map (fun c => (8703311873-1+2*2^10*c.k,115160108711052+c.lower,115160497833888+c.upper)) = pointBounds66371 := by
 decide +kernel
def cuts66372 : List PrefixCut := [⟨64,185439821,185439925⟩]
theorem checked66372 : checkPrefixCuts (2^48) 8703442945 10 Manual.Count131072.C066372.packed 64 cuts66372 = true := by
 decide +kernel
def cuts66373 : List PrefixCut := [⟨64,187733165,187733274⟩]
theorem checked66373 : checkPrefixCuts (2^48) 8703574017 10 Manual.Count131072.C066373.packed 64 cuts66373 = true := by
 decide +kernel
def cuts66374 : List PrefixCut := [⟨5,14423481,14423491⟩,
⟨64,183817265,183817368⟩]
theorem checked66374 : checkPrefixCuts (2^48) 8703705089 10 Manual.Count131072.C066374.packed 64 cuts66374 = true := by
 decide +kernel
def pointBounds66374 : List (Nat × Nat × Nat) := [(8703715328,115160683237822,115161072360992)]
theorem point_links_checked66374 : (cuts66374.take 1).map (fun c => (8703705089-1+2*2^10*c.k,115160668814341+c.lower,115161057937501+c.upper)) = pointBounds66374 := by
 decide +kernel
def cuts66375 : List PrefixCut := [⟨64,185463793,185463898⟩]
theorem checked66375 : checkPrefixCuts (2^48) 8703836161 10 Manual.Count131072.C066375.packed 64 cuts66375 = true := by
 decide +kernel
def cuts66376 : List PrefixCut := [⟨10,27746564,27746579⟩,
⟨64,182259485,182259589⟩]
theorem checked66376 : checkPrefixCuts (2^48) 8703967233 10 Manual.Count131072.C066376.packed 64 cuts66376 = true := by
 decide +kernel
def pointBounds66376 : List (Nat × Nat × Nat) := [(8703987712,115161065841963,115161454965346)]
theorem point_links_checked66376 : (cuts66376.take 1).map (fun c => (8703967233-1+2*2^10*c.k,115161038095399+c.lower,115161427218767+c.upper)) = pointBounds66376 := by
 decide +kernel
def cuts66377 : List PrefixCut := [⟨64,184585068,184585177⟩]
theorem checked66377 : checkPrefixCuts (2^48) 8704098305 10 Manual.Count131072.C066377.packed 64 cuts66377 = true := by
 decide +kernel
def cuts66378 : List PrefixCut := [⟨15,43170777,43170798⟩,
⟨64,187395636,187395743⟩]
theorem checked66378 : checkPrefixCuts (2^48) 8704229377 10 Manual.Count131072.C066378.packed 64 cuts66378 = true := by
 decide +kernel
def pointBounds66378 : List (Nat × Nat × Nat) := [(8704260096,115161448110729,115161837234331)]
theorem point_links_checked66378 : (cuts66378.take 1).map (fun c => (8704229377-1+2*2^10*c.k,115161404939952+c.lower,115161794063533+c.upper)) = pointBounds66378 := by
 decide +kernel
def cuts66379 : List PrefixCut := [⟨64,181863214,181863319⟩]
theorem checked66379 : checkPrefixCuts (2^48) 8704360449 10 Manual.Count131072.C066379.packed 64 cuts66379 = true := by
 decide +kernel
def cuts66380 : List PrefixCut := [⟨20,58108987,58109024⟩,
⟨64,184350377,184350486⟩]
theorem checked66380 : checkPrefixCuts (2^48) 8704491521 10 Manual.Count131072.C066380.packed 64 cuts66380 = true := by
 decide +kernel
def pointBounds66380 : List (Nat × Nat × Nat) := [(8704532480,115161832307789,115162221431619)]
theorem point_links_checked66380 : (cuts66380.take 1).map (fun c => (8704491521-1+2*2^10*c.k,115161774198802+c.lower,115162163322595+c.upper)) = pointBounds66380 := by
 decide +kernel
def cuts66381 : List PrefixCut := [⟨64,187969238,187969344⟩]
theorem checked66381 : checkPrefixCuts (2^48) 8704622593 10 Manual.Count131072.C066381.packed 64 cuts66381 = true := by
 decide +kernel
def cuts66382 : List PrefixCut := [⟨25,72011545,72011585⟩,
⟨64,184377160,184377265⟩]
theorem checked66382 : checkPrefixCuts (2^48) 8704753665 10 Manual.Count131072.C066382.packed 64 cuts66382 = true := by
 decide +kernel
def pointBounds66382 : List (Nat × Nat × Nat) := [(8704804864,115162218529962,115162607654010)]
theorem point_links_checked66382 : (cuts66382.take 1).map (fun c => (8704753665-1+2*2^10*c.k,115162146518417+c.lower,115162535642425+c.upper)) = pointBounds66382 := by
 decide +kernel
def cuts66383 : List PrefixCut := [⟨64,187187528,187187639⟩]
theorem checked66383 : checkPrefixCuts (2^48) 8704884737 10 Manual.Count131072.C066383.packed 64 cuts66383 = true := by
 decide +kernel
def cuts66384 : List PrefixCut := [⟨30,87141961,87142012⟩,
⟨64,187605059,187605167⟩]
theorem checked66384 : checkPrefixCuts (2^48) 8705015809 10 Manual.Count131072.C066384.packed 64 cuts66384 = true := by
 decide +kernel
def pointBounds66384 : List (Nat × Nat × Nat) := [(8705077248,115162605225066,115162994349341)]
theorem point_links_checked66384 : (cuts66384.take 1).map (fun c => (8705015809-1+2*2^10*c.k,115162518083105+c.lower,115162907207329+c.upper)) = pointBounds66384 := by
 decide +kernel
def cuts66385 : List PrefixCut := [⟨64,182073116,182073222⟩]
theorem checked66385 : checkPrefixCuts (2^48) 8705146881 10 Manual.Count131072.C066385.packed 64 cuts66385 = true := by
 decide +kernel
def cuts66386 : List PrefixCut := [⟨35,102271450,102271511⟩,
⟨64,185109731,185109838⟩]
theorem checked66386 : checkPrefixCuts (2^48) 8705277953 10 Manual.Count131072.C066386.packed 64 cuts66386 = true := by
 decide +kernel
def pointBounds66386 : List (Nat × Nat × Nat) := [(8705349632,115162990032730,115163379157229)]
theorem point_links_checked66386 : (cuts66386.take 1).map (fun c => (8705277953-1+2*2^10*c.k,115162887761280+c.lower,115163276885718+c.upper)) = pointBounds66386 := by
 decide +kernel
def cuts66387 : List PrefixCut := [⟨64,186173942,186174046⟩]
theorem checked66387 : checkPrefixCuts (2^48) 8705409025 10 Manual.Count131072.C066387.packed 64 cuts66387 = true := by
 decide +kernel
def cuts66388 : List PrefixCut := [⟨40,115912715,115912780⟩,
⟨64,183907858,183907964⟩]
theorem checked66388 : checkPrefixCuts (2^48) 8705540097 10 Manual.Count131072.C066388.packed 64 cuts66388 = true := by
 decide +kernel
def pointBounds66388 : List (Nat × Nat × Nat) := [(8705622016,115163374957668,115163764082382)]
theorem point_links_checked66388 : (cuts66388.take 1).map (fun c => (8705540097-1+2*2^10*c.k,115163259044953+c.lower,115163648169602+c.upper)) = pointBounds66388 := by
 decide +kernel
def cuts66389 : List PrefixCut := [⟨64,185489349,185489457⟩]
theorem checked66389 : checkPrefixCuts (2^48) 8705671169 10 Manual.Count131072.C066389.packed 64 cuts66389 = true := by
 decide +kernel
def cuts66390 : List PrefixCut := [⟨45,132301331,132301411⟩,
⟨64,186812170,186812283⟩]
theorem checked66390 : checkPrefixCuts (2^48) 8705802241 10 Manual.Count131072.C066390.packed 64 cuts66390 = true := by
 decide +kernel
def pointBounds66390 : List (Nat × Nat × Nat) := [(8705894400,115163760743491,115164149868434)]
theorem point_links_checked66390 : (cuts66390.take 1).map (fun c => (8705802241-1+2*2^10*c.k,115163628442160+c.lower,115164017567023+c.upper)) = pointBounds66390 := by
 decide +kernel
def cuts66391 : List PrefixCut := [⟨64,183155931,183156036⟩]
theorem checked66391 : checkPrefixCuts (2^48) 8705933313 10 Manual.Count131072.C066391.packed 64 cuts66391 = true := by
 decide +kernel
def cuts66392 : List PrefixCut := [⟨50,142772409,142772494⟩,
⟨64,184349390,184349499⟩]
theorem checked66392 : checkPrefixCuts (2^48) 8706064385 10 Manual.Count131072.C066392.packed 64 cuts66392 = true := by
 decide +kernel
def pointBounds66392 : List (Nat × Nat × Nat) := [(8706166784,115164141182670,115164530307836)]
theorem point_links_checked66392 : (cuts66392.take 1).map (fun c => (8706064385-1+2*2^10*c.k,115163998410261+c.lower,115164387535342+c.upper)) = pointBounds66392 := by
 decide +kernel
def cuts66393 : List PrefixCut := [⟨64,184217305,184217416⟩]
theorem checked66393 : checkPrefixCuts (2^48) 8706195457 10 Manual.Count131072.C066393.packed 64 cuts66393 = true := by
 decide +kernel
def cuts66394 : List PrefixCut := [⟨55,159094534,159094627⟩,
⟨64,184925784,184925892⟩]
theorem checked66394 : checkPrefixCuts (2^48) 8706326529 10 Manual.Count131072.C066394.packed 64 cuts66394 = true := by
 decide +kernel
def pointBounds66394 : List (Nat × Nat × Nat) := [(8706439168,115164526071490,115164915196884)]
theorem point_links_checked66394 : (cuts66394.take 1).map (fun c => (8706326529-1+2*2^10*c.k,115164366976956+c.lower,115164756102257+c.upper)) = pointBounds66394 := by
 decide +kernel
def cuts66395 : List PrefixCut := [⟨64,183338870,183338975⟩]
theorem checked66395 : checkPrefixCuts (2^48) 8706457601 10 Manual.Count131072.C066395.packed 64 cuts66395 = true := by
 decide +kernel
def cuts66396 : List PrefixCut := [⟨60,173475933,173476024⟩,
⟨64,184984872,184984970⟩]
theorem checked66396 : checkPrefixCuts (2^48) 8706588673 10 Manual.Count131072.C066396.packed 64 cuts66396 = true := by
 decide +kernel
def pointBounds66396 : List (Nat × Nat × Nat) := [(8706711552,115164908717543,115165297843148)]
theorem point_links_checked66396 : (cuts66396.take 1).map (fun c => (8706588673-1+2*2^10*c.k,115164735241610+c.lower,115165124367124+c.upper)) = pointBounds66396 := by
 decide +kernel
def cuts66397 : List PrefixCut := [⟨64,183042406,183042518⟩]
theorem checked66397 : checkPrefixCuts (2^48) 8706719745 10 Manual.Count131072.C066397.packed 64 cuts66397 = true := by
 decide +kernel
def cuts66398 : List PrefixCut := [⟨64,184074130,184074239⟩]
theorem checked66398 : checkPrefixCuts (2^48) 8706850817 10 Manual.Count131072.C066398.packed 64 cuts66398 = true := by
 decide +kernel
def cuts66399 : List PrefixCut := [⟨1,3071111,3071113⟩,
⟨64,185978672,185978783⟩]
theorem checked66399 : checkPrefixCuts (2^48) 8706981889 10 Manual.Count131072.C066399.packed 64 cuts66399 = true := by
 decide +kernel
def pointBounds66399 : List (Nat × Nat × Nat) := [(8706983936,115165290414129,115165679539964)]
theorem point_links_checked66399 : (cuts66399.take 1).map (fun c => (8706981889-1+2*2^10*c.k,115165287343018+c.lower,115165676468851+c.upper)) = pointBounds66399 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000199
