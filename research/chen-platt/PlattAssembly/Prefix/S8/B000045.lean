import PlattAssemblyKernel
import PlattCertificates.Count131072.C071440
import PlattCertificates.Count131072.C071441
import PlattCertificates.Count131072.C071442
import PlattCertificates.Count131072.C071443
import PlattCertificates.Count131072.C071444
import PlattCertificates.Count131072.C071445
import PlattCertificates.Count131072.C071446
import PlattCertificates.Count131072.C071447
import PlattCertificates.Count131072.C071448
import PlattCertificates.Count131072.C071449
import PlattCertificates.Count131072.C071450
import PlattCertificates.Count131072.C071451
import PlattCertificates.Count131072.C071452
import PlattCertificates.Count131072.C071453
import PlattCertificates.Count131072.C071454
import PlattCertificates.Count131072.C071455
import PlattCertificates.Count131072.C071456
import PlattCertificates.Count131072.C071457
import PlattCertificates.Count131072.C071458
import PlattCertificates.Count131072.C071459
import PlattCertificates.Count131072.C071460
import PlattCertificates.Count131072.C071461
import PlattCertificates.Count131072.C071462
import PlattCertificates.Count131072.C071463
import PlattCertificates.Count131072.C071464
import PlattCertificates.Count131072.C071465
import PlattCertificates.Count131072.C071466
import PlattCertificates.Count131072.C071467
import PlattCertificates.Count131072.C071468
import PlattCertificates.Count131072.C071469
import PlattCertificates.Count131072.C071470
import PlattCertificates.Count131072.C071471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71440 : List PrefixCut := [⟨64,172350302,172350409⟩]
theorem checked71440 : checkPrefixCuts (2^48) 9367715841 10 Manual.Count131072.C071440.packed 64 cuts71440 = true := by
 decide +kernel
def cuts71441 : List PrefixCut := [⟨43,116791808,116791879⟩,
⟨64,174691536,174691639⟩]
theorem checked71441 : checkPrefixCuts (2^48) 9367846913 10 Manual.Count131072.C071441.packed 64 cuts71441 = true := by
 decide +kernel
def pointBounds71441 : List (Nat × Nat × Nat) := [(9367934976,116063665650182,116064055302954)]
theorem point_links_checked71441 : (cuts71441.take 1).map (fun c => (9367846913-1+2*2^10*c.k,116063548858374+c.lower,116063938511075+c.upper)) = pointBounds71441 := by
 decide +kernel
def cuts71442 : List PrefixCut := [⟨64,171954885,171954989⟩]
theorem checked71442 : checkPrefixCuts (2^48) 9367977985 10 Manual.Count131072.C071442.packed 64 cuts71442 = true := by
 decide +kernel
def cuts71443 : List PrefixCut := [⟨58,156268632,156268717⟩,
⟨64,171531833,171531928⟩]
theorem checked71443 : checkPrefixCuts (2^48) 9368109057 10 Manual.Count131072.C071443.packed 64 cuts71443 = true := by
 decide +kernel
def pointBounds71443 : List (Nat × Nat × Nat) := [(9368227840,116064051773427,116064441426420)]
theorem point_links_checked71443 : (cuts71443.take 1).map (fun c => (9368109057-1+2*2^10*c.k,116063895504795+c.lower,116064285157703+c.upper)) = pointBounds71443 := by
 decide +kernel
def cuts71444 : List PrefixCut := [⟨64,172941571,172941671⟩]
theorem checked71444 : checkPrefixCuts (2^48) 9368240129 10 Manual.Count131072.C071444.packed 64 cuts71444 = true := by
 decide +kernel
def cuts71445 : List PrefixCut := [⟨64,171346761,171346859⟩]
theorem checked71445 : checkPrefixCuts (2^48) 9368371201 10 Manual.Count131072.C071445.packed 64 cuts71445 = true := by
 decide +kernel
def cuts71446 : List PrefixCut := [⟨9,24396365,24396378⟩,
⟨64,171915214,171915311⟩]
theorem checked71446 : checkPrefixCuts (2^48) 9368502273 10 Manual.Count131072.C071446.packed 64 cuts71446 = true := by
 decide +kernel
def pointBounds71446 : List (Nat × Nat × Nat) := [(9368520704,116064435721325,116064825374539)]
theorem point_links_checked71446 : (cuts71446.take 1).map (fun c => (9368502273-1+2*2^10*c.k,116064411324960+c.lower,116064800978161+c.upper)) = pointBounds71446 := by
 decide +kernel
def cuts71447 : List PrefixCut := [⟨64,169989985,169990089⟩]
theorem checked71447 : checkPrefixCuts (2^48) 9368633345 10 Manual.Count131072.C071447.packed 64 cuts71447 = true := by
 decide +kernel
def cuts71448 : List PrefixCut := [⟨24,63963448,63963489⟩,
⟨64,169597033,169597134⟩]
theorem checked71448 : checkPrefixCuts (2^48) 9368764417 10 Manual.Count131072.C071448.packed 64 cuts71448 = true := by
 decide +kernel
def pointBounds71448 : List (Nat × Nat × Nat) := [(9368813568,116064817193607,116065206847050)]
theorem point_links_checked71448 : (cuts71448.take 1).map (fun c => (9368764417-1+2*2^10*c.k,116064753230159+c.lower,116065142883561+c.upper)) = pointBounds71448 := by
 decide +kernel
def cuts71449 : List PrefixCut := [⟨64,172388682,172388784⟩]
theorem checked71449 : checkPrefixCuts (2^48) 9368895489 10 Manual.Count131072.C071449.packed 64 cuts71449 = true := by
 decide +kernel
def cuts71450 : List PrefixCut := [⟨39,101605434,101605496⟩,
⟨64,167759663,167759764⟩]
theorem checked71450 : checkPrefixCuts (2^48) 9369026561 10 Manual.Count131072.C071450.packed 64 cuts71450 = true := by
 decide +kernel
def pointBounds71450 : List (Nat × Nat × Nat) := [(9369106432,116065196821308,116065586474975)]
theorem point_links_checked71450 : (cuts71450.take 1).map (fun c => (9369026561-1+2*2^10*c.k,116065095215874+c.lower,116065484869479+c.upper)) = pointBounds71450 := by
 decide +kernel
def cuts71451 : List PrefixCut := [⟨64,172143522,172143616⟩]
theorem checked71451 : checkPrefixCuts (2^48) 9369157633 10 Manual.Count131072.C071451.packed 64 cuts71451 = true := by
 decide +kernel
def cuts71452 : List PrefixCut := [⟨54,144442477,144442565⟩,
⟨64,172381447,172381551⟩]
theorem checked71452 : checkPrefixCuts (2^48) 9369288705 10 Manual.Count131072.C071452.packed 64 cuts71452 = true := by
 decide +kernel
def pointBounds71452 : List (Nat × Nat × Nat) := [(9369399296,116065579561536,116065969215424)]
theorem point_links_checked71452 : (cuts71452.take 1).map (fun c => (9369288705-1+2*2^10*c.k,116065435119059+c.lower,116065824772859+c.upper)) = pointBounds71452 := by
 decide +kernel
def cuts71453 : List PrefixCut := [⟨64,171027164,171027269⟩]
theorem checked71453 : checkPrefixCuts (2^48) 9369419777 10 Manual.Count131072.C071453.packed 64 cuts71453 = true := by
 decide +kernel
def cuts71454 : List PrefixCut := [⟨64,171355230,171355328⟩]
theorem checked71454 : checkPrefixCuts (2^48) 9369550849 10 Manual.Count131072.C071454.packed 64 cuts71454 = true := by
 decide +kernel
def cuts71455 : List PrefixCut := [⟨5,13248087,13248094⟩,
⟨64,173245405,173245501⟩]
theorem checked71455 : checkPrefixCuts (2^48) 9369681921 10 Manual.Count131072.C071455.packed 64 cuts71455 = true := by
 decide +kernel
def pointBounds71455 : List (Nat × Nat × Nat) := [(9369692160,116065963130987,116066352785101)]
theorem point_links_checked71455 : (cuts71455.take 1).map (fun c => (9369681921-1+2*2^10*c.k,116065949882900+c.lower,116066339537007+c.upper)) = pointBounds71455 := by
 decide +kernel
def cuts71456 : List PrefixCut := [⟨64,171921199,171921293⟩]
theorem checked71456 : checkPrefixCuts (2^48) 9369812993 10 Manual.Count131072.C071456.packed 64 cuts71456 = true := by
 decide +kernel
def cuts71457 : List PrefixCut := [⟨20,52990783,52990810⟩,
⟨64,170326686,170326777⟩]
theorem checked71457 : checkPrefixCuts (2^48) 9369944065 10 Manual.Count131072.C071457.packed 64 cuts71457 = true := by
 decide +kernel
def pointBounds71457 : List (Nat × Nat × Nat) := [(9369985024,116066348040287,116066737694611)]
theorem point_links_checked71457 : (cuts71457.take 1).map (fun c => (9369944065-1+2*2^10*c.k,116066295049504+c.lower,116066684703801+c.upper)) = pointBounds71457 := by
 decide +kernel
def cuts71458 : List PrefixCut := [⟨64,168251561,168251657⟩]
theorem checked71458 : checkPrefixCuts (2^48) 9370075137 10 Manual.Count131072.C071458.packed 64 cuts71458 = true := by
 decide +kernel
def cuts71459 : List PrefixCut := [⟨35,95644926,95644984⟩,
⟨64,174827793,174827900⟩]
theorem checked71459 : checkPrefixCuts (2^48) 9370206209 10 Manual.Count131072.C071459.packed 64 cuts71459 = true := by
 decide +kernel
def pointBounds71459 : List (Nat × Nat × Nat) := [(9370277888,116066729272677,116067118927219)]
theorem point_links_checked71459 : (cuts71459.take 1).map (fun c => (9370206209-1+2*2^10*c.k,116066633627751+c.lower,116067023282235+c.upper)) = pointBounds71459 := by
 decide +kernel
def cuts71460 : List PrefixCut := [⟨64,172151904,172152006⟩]
theorem checked71460 : checkPrefixCuts (2^48) 9370337281 10 Manual.Count131072.C071460.packed 64 cuts71460 = true := by
 decide +kernel
def cuts71461 : List PrefixCut := [⟨50,135262666,135262749⟩,
⟨64,173260904,173261011⟩]
theorem checked71461 : checkPrefixCuts (2^48) 9370468353 10 Manual.Count131072.C071461.packed 64 cuts71461 = true := by
 decide +kernel
def pointBounds71461 : List (Nat × Nat × Nat) := [(9370570752,116067115870114,116067505524890)]
theorem point_links_checked71461 : (cuts71461.take 1).map (fun c => (9370468353-1+2*2^10*c.k,116066980607448+c.lower,116067370262141+c.upper)) = pointBounds71461 := by
 decide +kernel
def cuts71462 : List PrefixCut := [⟨64,170344804,170344906⟩]
theorem checked71462 : checkPrefixCuts (2^48) 9370599425 10 Manual.Count131072.C071462.packed 64 cuts71462 = true := by
 decide +kernel
def cuts71463 : List PrefixCut := [⟨64,170943180,170943274⟩]
theorem checked71463 : checkPrefixCuts (2^48) 9370730497 10 Manual.Count131072.C071463.packed 64 cuts71463 = true := by
 decide +kernel
def cuts71464 : List PrefixCut := [⟨1,2433017,2433018⟩,
⟨64,169138561,169138662⟩]
theorem checked71464 : checkPrefixCuts (2^48) 9370861569 10 Manual.Count131072.C071464.packed 64 cuts71464 = true := by
 decide +kernel
def pointBounds71464 : List (Nat × Nat × Nat) := [(9370863616,116067497589353,116067887244350)]
theorem point_links_checked71464 : (cuts71464.take 1).map (fun c => (9370861569-1+2*2^10*c.k,116067495156336+c.lower,116067884811332+c.upper)) = pointBounds71464 := by
 decide +kernel
def cuts71465 : List PrefixCut := [⟨64,170608001,170608102⟩]
theorem checked71465 : checkPrefixCuts (2^48) 9370992641 10 Manual.Count131072.C071465.packed 64 cuts71465 = true := by
 decide +kernel
def cuts71466 : List PrefixCut := [⟨16,42982026,42982051⟩,
⟨64,169674484,169674585⟩]
theorem checked71466 : checkPrefixCuts (2^48) 9371123713 10 Manual.Count131072.C071466.packed 64 cuts71466 = true := by
 decide +kernel
def pointBounds71466 : List (Nat × Nat × Nat) := [(9371156480,116067877884924,116068267540147)]
theorem point_links_checked71466 : (cuts71466.take 1).map (fun c => (9371123713-1+2*2^10*c.k,116067834902898+c.lower,116068224558096+c.upper)) = pointBounds71466 := by
 decide +kernel
def cuts71467 : List PrefixCut := [⟨64,171354123,171354227⟩]
theorem checked71467 : checkPrefixCuts (2^48) 9371254785 10 Manual.Count131072.C071467.packed 64 cuts71467 = true := by
 decide +kernel
def cuts71468 : List PrefixCut := [⟨31,83228277,83228327⟩,
⟨64,171772215,171772316⟩]
theorem checked71468 : checkPrefixCuts (2^48) 9371385857 10 Manual.Count131072.C071468.packed 64 cuts71468 = true := by
 decide +kernel
def pointBounds71468 : List (Nat × Nat × Nat) := [(9371449344,116068259159782,116068648815235)]
theorem point_links_checked71468 : (cuts71468.take 1).map (fun c => (9371385857-1+2*2^10*c.k,116068175931505+c.lower,116068565586908+c.upper)) = pointBounds71468 := by
 decide +kernel
def cuts71469 : List PrefixCut := [⟨64,171199146,171199250⟩]
theorem checked71469 : checkPrefixCuts (2^48) 9371516929 10 Manual.Count131072.C071469.packed 64 cuts71469 = true := by
 decide +kernel
def cuts71470 : List PrefixCut := [⟨46,122811387,122811458⟩,
⟨64,170836339,170836438⟩]
theorem checked71470 : checkPrefixCuts (2^48) 9371648001 10 Manual.Count131072.C071470.packed 64 cuts71470 = true := by
 decide +kernel
def pointBounds71470 : List (Nat × Nat × Nat) := [(9371742208,116068641714253,116069031369932)]
theorem point_links_checked71470 : (cuts71470.take 1).map (fun c => (9371648001-1+2*2^10*c.k,116068518902866+c.lower,116068908558474+c.upper)) = pointBounds71470 := by
 decide +kernel
def cuts71471 : List PrefixCut := [⟨64,173356814,173356914⟩]
theorem checked71471 : checkPrefixCuts (2^48) 9371779073 10 Manual.Count131072.C071471.packed 64 cuts71471 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000045
