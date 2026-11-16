import PlattAssemblyKernel
import PlattCertificates.Count131072.C067424
import PlattCertificates.Count131072.C067425
import PlattCertificates.Count131072.C067426
import PlattCertificates.Count131072.C067427
import PlattCertificates.Count131072.C067428
import PlattCertificates.Count131072.C067429
import PlattCertificates.Count131072.C067430
import PlattCertificates.Count131072.C067431
import PlattCertificates.Count131072.C067432
import PlattCertificates.Count131072.C067433
import PlattCertificates.Count131072.C067434
import PlattCertificates.Count131072.C067435
import PlattCertificates.Count131072.C067436
import PlattCertificates.Count131072.C067437
import PlattCertificates.Count131072.C067438
import PlattCertificates.Count131072.C067439
import PlattCertificates.Count131072.C067440
import PlattCertificates.Count131072.C067441
import PlattCertificates.Count131072.C067442
import PlattCertificates.Count131072.C067443
import PlattCertificates.Count131072.C067444
import PlattCertificates.Count131072.C067445
import PlattCertificates.Count131072.C067446
import PlattCertificates.Count131072.C067447
import PlattCertificates.Count131072.C067448
import PlattCertificates.Count131072.C067449
import PlattCertificates.Count131072.C067450
import PlattCertificates.Count131072.C067451
import PlattCertificates.Count131072.C067452
import PlattCertificates.Count131072.C067453
import PlattCertificates.Count131072.C067454
import PlattCertificates.Count131072.C067455
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000232
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67424 : List PrefixCut := [⟨64,180860448,180860547⟩]
theorem checked67424 : checkPrefixCuts (2^48) 8841330689 10 Manual.Count131072.C067424.packed 64 cuts67424 = true := by
 decide +kernel
def cuts67425 : List PrefixCut := [⟨43,124700163,124700233⟩,
⟨64,183786650,183786755⟩]
theorem checked67425 : checkPrefixCuts (2^48) 8841461761 10 Manual.Count131072.C067425.packed 64 cuts67425 = true := by
 decide +kernel
def pointBounds67425 : List (Nat × Nat × Nat) := [(8841549824,115353839022753,115354228258384)]
theorem point_links_checked67425 : (cuts67425.take 1).map (fun c => (8841461761-1+2*2^10*c.k,115353714322590+c.lower,115354103558151+c.upper)) = pointBounds67425 := by
 decide +kernel
def cuts67426 : List PrefixCut := [⟨64,185534839,185534943⟩]
theorem checked67426 : checkPrefixCuts (2^48) 8841592833 10 Manual.Count131072.C067426.packed 64 cuts67426 = true := by
 decide +kernel
def cuts67427 : List PrefixCut := [⟨50,140486340,140486427⟩,
⟨64,180661383,180661494⟩]
theorem checked67427 : checkPrefixCuts (2^48) 8841723905 10 Manual.Count131072.C067427.packed 64 cuts67427 = true := by
 decide +kernel
def pointBounds67427 : List (Nat × Nat × Nat) := [(8841826304,115354224130419,115354613366276)]
theorem point_links_checked67427 : (cuts67427.take 1).map (fun c => (8841723905-1+2*2^10*c.k,115354083644079+c.lower,115354472879849+c.upper)) = pointBounds67427 := by
 decide +kernel
def cuts67428 : List PrefixCut := [⟨64,183046276,183046385⟩]
theorem checked67428 : checkPrefixCuts (2^48) 8841854977 10 Manual.Count131072.C067428.packed 64 cuts67428 = true := by
 decide +kernel
def cuts67429 : List PrefixCut := [⟨57,162160806,162160900⟩,
⟨64,181897546,181897653⟩]
theorem checked67429 : checkPrefixCuts (2^48) 8841986049 10 Manual.Count131072.C067429.packed 64 cuts67429 = true := by
 decide +kernel
def pointBounds67429 : List (Nat × Nat × Nat) := [(8842102784,115354609512544,115354998748628)]
theorem point_links_checked67429 : (cuts67429.take 1).map (fun c => (8841986049-1+2*2^10*c.k,115354447351738+c.lower,115354836587728+c.upper)) = pointBounds67429 := by
 decide +kernel
def cuts67430 : List PrefixCut := [⟨64,180876188,180876296⟩]
theorem checked67430 : checkPrefixCuts (2^48) 8842117121 10 Manual.Count131072.C067430.packed 64 cuts67430 = true := by
 decide +kernel
def cuts67431 : List PrefixCut := [⟨64,181860314,181860426⟩]
theorem checked67431 : checkPrefixCuts (2^48) 8842248193 10 Manual.Count131072.C067431.packed 64 cuts67431 = true := by
 decide +kernel
def pointBounds67431 : List (Nat × Nat × Nat) := [(8842379264,115354991985786,115355381222103)]
theorem point_links_checked67431 : (cuts67431.take 1).map (fun c => (8842248193-1+2*2^10*c.k,115354810125472+c.lower,115355199361677+c.upper)) = pointBounds67431 := by
 decide +kernel
def cuts67432 : List PrefixCut := [⟨64,184054052,184054158⟩]
theorem checked67432 : checkPrefixCuts (2^48) 8842379265 10 Manual.Count131072.C067432.packed 64 cuts67432 = true := by
 decide +kernel
def cuts67433 : List PrefixCut := [⟨64,183446516,183446618⟩]
theorem checked67433 : checkPrefixCuts (2^48) 8842510337 10 Manual.Count131072.C067433.packed 64 cuts67433 = true := by
 decide +kernel
def cuts67434 : List PrefixCut := [⟨7,19576380,19576394⟩,
⟨64,182839009,182839117⟩]
theorem checked67434 : checkPrefixCuts (2^48) 8842641409 10 Manual.Count131072.C067434.packed 64 cuts67434 = true := by
 decide +kernel
def pointBounds67434 : List (Nat × Nat × Nat) := [(8842655744,115355379062734,115355768299273)]
theorem point_links_checked67434 : (cuts67434.take 1).map (fun c => (8842641409-1+2*2^10*c.k,115355359486354+c.lower,115355748722879+c.upper)) = pointBounds67434 := by
 decide +kernel
def cuts67435 : List PrefixCut := [⟨64,182645321,182645421⟩]
theorem checked67435 : checkPrefixCuts (2^48) 8842772481 10 Manual.Count131072.C067435.packed 64 cuts67435 = true := by
 decide +kernel
def cuts67436 : List PrefixCut := [⟨14,41061403,41061428⟩,
⟨64,184138641,184138755⟩]
theorem checked67436 : checkPrefixCuts (2^48) 8842903553 10 Manual.Count131072.C067436.packed 64 cuts67436 = true := by
 decide +kernel
def pointBounds67436 : List (Nat × Nat × Nat) := [(8842932224,115355766032087,115356155268845)]
theorem point_links_checked67436 : (cuts67436.take 1).map (fun c => (8842903553-1+2*2^10*c.k,115355724970684+c.lower,115356114207417+c.upper)) = pointBounds67436 := by
 decide +kernel
def cuts67437 : List PrefixCut := [⟨64,182735385,182735495⟩]
theorem checked67437 : checkPrefixCuts (2^48) 8843034625 10 Manual.Count131072.C067437.packed 64 cuts67437 = true := by
 decide +kernel
def cuts67438 : List PrefixCut := [⟨21,58343609,58343646⟩,
⟨64,179931688,179931796⟩]
theorem checked67438 : checkPrefixCuts (2^48) 8843165697 10 Manual.Count131072.C067438.packed 64 cuts67438 = true := by
 decide +kernel
def pointBounds67438 : List (Nat × Nat × Nat) := [(8843208704,115356150188319,115356539425313)]
theorem point_links_checked67438 : (cuts67438.take 1).map (fun c => (8843165697-1+2*2^10*c.k,115356091844710+c.lower,115356481081667+c.upper)) = pointBounds67438 := by
 decide +kernel
def cuts67439 : List PrefixCut := [⟨64,182061559,182061664⟩]
theorem checked67439 : checkPrefixCuts (2^48) 8843296769 10 Manual.Count131072.C067439.packed 64 cuts67439 = true := by
 decide +kernel
def cuts67440 : List PrefixCut := [⟨28,79953457,79953500⟩,
⟨64,182950060,182950168⟩]
theorem checked67440 : checkPrefixCuts (2^48) 8843427841 10 Manual.Count131072.C067440.packed 64 cuts67440 = true := by
 decide +kernel
def pointBounds67440 : List (Nat × Nat × Nat) := [(8843485184,115356533791414,115356923028627)]
theorem point_links_checked67440 : (cuts67440.take 1).map (fun c => (8843427841-1+2*2^10*c.k,115356453837957+c.lower,115356843075127+c.upper)) = pointBounds67440 := by
 decide +kernel
def cuts67441 : List PrefixCut := [⟨64,183233806,183233916⟩]
theorem checked67441 : checkPrefixCuts (2^48) 8843558913 10 Manual.Count131072.C067441.packed 64 cuts67441 = true := by
 decide +kernel
def cuts67442 : List PrefixCut := [⟨35,102262204,102262262⟩,
⟨64,185586339,185586450⟩]
theorem checked67442 : checkPrefixCuts (2^48) 8843689985 10 Manual.Count131072.C067442.packed 64 cuts67442 = true := by
 decide +kernel
def pointBounds67442 : List (Nat × Nat × Nat) := [(8843761664,115356922284027,115357311521473)]
theorem point_links_checked67442 : (cuts67442.take 1).map (fun c => (8843689985-1+2*2^10*c.k,115356820021823+c.lower,115357209259211+c.upper)) = pointBounds67442 := by
 decide +kernel
def cuts67443 : List PrefixCut := [⟨64,183514823,183514929⟩]
theorem checked67443 : checkPrefixCuts (2^48) 8843821057 10 Manual.Count131072.C067443.packed 64 cuts67443 = true := by
 decide +kernel
def cuts67444 : List PrefixCut := [⟨42,120400281,120400355⟩,
⟨64,182748260,182748372⟩]
theorem checked67444 : checkPrefixCuts (2^48) 8843952129 10 Manual.Count131072.C067444.packed 64 cuts67444 = true := by
 decide +kernel
def pointBounds67444 : List (Nat × Nat × Nat) := [(8844038144,115357309523266,115357698760945)]
theorem point_links_checked67444 : (cuts67444.take 1).map (fun c => (8843952129-1+2*2^10*c.k,115357189122985+c.lower,115357578360590+c.upper)) = pointBounds67444 := by
 decide +kernel
def cuts67445 : List PrefixCut := [⟨64,183254786,183254892⟩]
theorem checked67445 : checkPrefixCuts (2^48) 8844083201 10 Manual.Count131072.C067445.packed 64 cuts67445 = true := by
 decide +kernel
def cuts67446 : List PrefixCut := [⟨49,140414977,140415063⟩,
⟨64,183506654,183506766⟩]
theorem checked67446 : checkPrefixCuts (2^48) 8844214273 10 Manual.Count131072.C067446.packed 64 cuts67446 = true := by
 decide +kernel
def pointBounds67446 : List (Nat × Nat × Nat) := [(8844314624,115357695541008,115358084778917)]
theorem point_links_checked67446 : (cuts67446.take 1).map (fun c => (8844214273-1+2*2^10*c.k,115357555126031+c.lower,115357944363854+c.upper)) = pointBounds67446 := by
 decide +kernel
def cuts67447 : List PrefixCut := [⟨64,181371654,181371757⟩]
theorem checked67447 : checkPrefixCuts (2^48) 8844345345 10 Manual.Count131072.C067447.packed 64 cuts67447 = true := by
 decide +kernel
def cuts67448 : List PrefixCut := [⟨56,160142037,160142128⟩,
⟨64,182355534,182355638⟩]
theorem checked67448 : checkPrefixCuts (2^48) 8844476417 10 Manual.Count131072.C067448.packed 64 cuts67448 = true := by
 decide +kernel
def pointBounds67448 : List (Nat × Nat × Nat) := [(8844591104,115358080146376,115358469384505)]
theorem point_links_checked67448 : (cuts67448.take 1).map (fun c => (8844476417-1+2*2^10*c.k,115357920004339+c.lower,115358309242377+c.upper)) = pointBounds67448 := by
 decide +kernel
def cuts67449 : List PrefixCut := [⟨64,181016209,181016316⟩]
theorem checked67449 : checkPrefixCuts (2^48) 8844607489 10 Manual.Count131072.C067449.packed 64 cuts67449 = true := by
 decide +kernel
def cuts67450 : List PrefixCut := [⟨63,176908292,176908397⟩,
⟨64,179867880,179867987⟩]
theorem checked67450 : checkPrefixCuts (2^48) 8844738561 10 Manual.Count131072.C067450.packed 64 cuts67450 = true := by
 decide +kernel
def pointBounds67450 : List (Nat × Nat × Nat) := [(8844867584,115358460284374,115358849522728)]
theorem point_links_checked67450 : (cuts67450.take 1).map (fun c => (8844738561-1+2*2^10*c.k,115358283376082+c.lower,115358672614331+c.upper)) = pointBounds67450 := by
 decide +kernel
def cuts67451 : List PrefixCut := [⟨64,181488197,181488303⟩]
theorem checked67451 : checkPrefixCuts (2^48) 8844869633 10 Manual.Count131072.C067451.packed 64 cuts67451 = true := by
 decide +kernel
def cuts67452 : List PrefixCut := [⟨64,181294574,181294680⟩]
theorem checked67452 : checkPrefixCuts (2^48) 8845000705 10 Manual.Count131072.C067452.packed 64 cuts67452 = true := by
 decide +kernel
def cuts67453 : List PrefixCut := [⟨6,17597874,17597883⟩,
⟨64,183296700,183296808⟩]
theorem checked67453 : checkPrefixCuts (2^48) 8845131777 10 Manual.Count131072.C067453.packed 64 cuts67453 = true := by
 decide +kernel
def pointBounds67453 : List (Nat × Nat × Nat) := [(8845144064,115358843624607,115359232863184)]
theorem point_links_checked67453 : (cuts67453.take 1).map (fun c => (8845131777-1+2*2^10*c.k,115358826026733+c.lower,115359215265301+c.upper)) = pointBounds67453 := by
 decide +kernel
def cuts67454 : List PrefixCut := [⟨64,178552520,178552625⟩]
theorem checked67454 : checkPrefixCuts (2^48) 8845262849 10 Manual.Count131072.C067454.packed 64 cuts67454 = true := by
 decide +kernel
def cuts67455 : List PrefixCut := [⟨13,37772221,37772245⟩,
⟨64,183514011,183514121⟩]
theorem checked67455 : checkPrefixCuts (2^48) 8845393921 10 Manual.Count131072.C067455.packed 64 cuts67455 = true := by
 decide +kernel
def pointBounds67455 : List (Nat × Nat × Nat) := [(8845420544,115359225648174,115359614886979)]
theorem point_links_checked67455 : (cuts67455.take 1).map (fun c => (8845393921-1+2*2^10*c.k,115359187875953+c.lower,115359577114734+c.upper)) = pointBounds67455 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000232
