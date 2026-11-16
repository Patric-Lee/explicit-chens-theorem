import PlattAssemblyKernel
import PlattCertificates.Count131072.C020480
import PlattCertificates.Count131072.C020481
import PlattCertificates.Count131072.C020482
import PlattCertificates.Count131072.C020483
import PlattCertificates.Count131072.C020484
import PlattCertificates.Count131072.C020485
import PlattCertificates.Count131072.C020486
import PlattCertificates.Count131072.C020487
import PlattCertificates.Count131072.C020488
import PlattCertificates.Count131072.C020489
import PlattCertificates.Count131072.C020490
import PlattCertificates.Count131072.C020491
import PlattCertificates.Count131072.C020492
import PlattCertificates.Count131072.C020493
import PlattCertificates.Count131072.C020494
import PlattCertificates.Count131072.C020495
import PlattCertificates.Count131072.C020496
import PlattCertificates.Count131072.C020497
import PlattCertificates.Count131072.C020498
import PlattCertificates.Count131072.C020499
import PlattCertificates.Count131072.C020500
import PlattCertificates.Count131072.C020501
import PlattCertificates.Count131072.C020502
import PlattCertificates.Count131072.C020503
import PlattCertificates.Count131072.C020504
import PlattCertificates.Count131072.C020505
import PlattCertificates.Count131072.C020506
import PlattCertificates.Count131072.C020507
import PlattCertificates.Count131072.C020508
import PlattCertificates.Count131072.C020509
import PlattCertificates.Count131072.C020510
import PlattCertificates.Count131072.C020511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20480 : List PrefixCut := [⟨67,334944420,334944616⟩,
⟨128,641925699,641926071⟩]
theorem checked20480 : checkPrefixCuts (2^48) 2688286721 9 Manual.Count131072.C020480.packed 128 cuts20480 = true := by
 decide +kernel
def pointBounds20480 : List (Nat × Nat × Nat) := [(2688355328,100328333766820,100328714316661)]
theorem point_links_checked20480 : (cuts20480.take 1).map (fun c => (2688286721-1+2*2^9*c.k,100327998822400+c.lower,100328379372045+c.upper)) = pointBounds20480 := by
 decide +kernel
def cuts20481 : List PrefixCut := [⟨22,106059727,106059790⟩,
⟨105,510607145,510607446⟩,
⟨128,623781835,623782203⟩]
theorem checked20481 : checkPrefixCuts (2^48) 2688417793 9 Manual.Count131072.C020481.packed 128 cuts20481 = true := by
 decide +kernel
def pointBounds20481 : List (Nat × Nat × Nat) := [(2688440320,100328746807826,100329127357906),(2688525312,100329151355244,100329531905562)]
theorem point_links_checked20481 : (cuts20481.take 2).map (fun c => (2688417793-1+2*2^9*c.k,100328640748099+c.lower,100329021298116+c.upper)) = pointBounds20481 := by
 decide +kernel
def cuts20482 : List PrefixCut := [⟨60,302876241,302876414⟩,
⟨128,640188169,640188540⟩]
theorem checked20482 : checkPrefixCuts (2^48) 2688548865 9 Manual.Count131072.C020482.packed 128 cuts20482 = true := by
 decide +kernel
def pointBounds20482 : List (Nat × Nat × Nat) := [(2688610304,100329567406175,100329947956733)]
theorem point_links_checked20482 : (cuts20482.take 1).map (fun c => (2688548865-1+2*2^9*c.k,100329264529934+c.lower,100329645080319+c.upper)) = pointBounds20482 := by
 decide +kernel
def cuts20483 : List PrefixCut := [⟨15,72339807,72339851⟩,
⟨98,482920726,482921014⟩,
⟨128,632514705,632515082⟩]
theorem checked20483 : checkPrefixCuts (2^48) 2688679937 9 Manual.Count131072.C020483.packed 128 cuts20483 = true := by
 decide +kernel
def pointBounds20483 : List (Nat × Nat × Nat) := [(2688695296,100329977057910,100330357608710),(2688780288,100330387638829,100330768189873)]
theorem point_links_checked20483 : (cuts20483.take 2).map (fun c => (2688679937-1+2*2^9*c.k,100329904718103+c.lower,100330285268859+c.upper)) = pointBounds20483 := by
 decide +kernel
def cuts20484 : List PrefixCut := [⟨53,262858336,262858486⟩,
⟨128,634682274,634682642⟩]
theorem checked20484 : checkPrefixCuts (2^48) 2688811009 9 Manual.Count131072.C020484.packed 128 cuts20484 = true := by
 decide +kernel
def pointBounds20484 : List (Nat × Nat × Nat) := [(2688865280,100330800091144,100331180642427)]
theorem point_links_checked20484 : (cuts20484.take 1).map (fun c => (2688811009-1+2*2^9*c.k,100330537232808+c.lower,100330917783941+c.upper)) = pointBounds20484 := by
 decide +kernel
def cuts20485 : List PrefixCut := [⟨8,38835729,38835751⟩,
⟨91,446865460,446865718⟩,
⟨128,635488558,635488925⟩]
theorem checked20485 : checkPrefixCuts (2^48) 2688942081 9 Manual.Count131072.C020485.packed 128 cuts20485 = true := by
 decide +kernel
def pointBounds20485 : List (Nat × Nat × Nat) := [(2688950272,100331210750811,100331591302334),(2689035264,100331618780542,100331999332301)]
theorem point_links_checked20485 : (cuts20485.take 2).map (fun c => (2688942081-1+2*2^9*c.k,100331171915082+c.lower,100331552466583+c.upper)) = pointBounds20485 := by
 decide +kernel
def cuts20486 : List PrefixCut := [⟨46,226930319,226930448⟩,
⟨128,629805503,629805873⟩]
theorem checked20486 : checkPrefixCuts (2^48) 2689073153 9 Manual.Count131072.C020486.packed 128 cuts20486 = true := by
 decide +kernel
def pointBounds20486 : List (Nat × Nat × Nat) := [(2689120256,100332034333959,100332414885956)]
theorem point_links_checked20486 : (cuts20486.take 1).map (fun c => (2689073153-1+2*2^9*c.k,100331807403640+c.lower,100332187955508+c.upper)) = pointBounds20486 := by
 decide +kernel
def cuts20487 : List PrefixCut := [⟨1,4186738,4186741⟩,
⟨84,409665836,409666074⟩,
⟨128,629879370,629879737⟩]
theorem checked20487 : checkPrefixCuts (2^48) 2689204225 9 Manual.Count131072.C020487.packed 128 cuts20487 = true := by
 decide +kernel
def pointBounds20487 : List (Nat × Nat × Nat) := [(2689205248,100332441395881,100332821948122),(2689290240,100332846874979,100333227427455)]
theorem point_links_checked20487 : (cuts20487.take 2).map (fun c => (2689204225-1+2*2^9*c.k,100332437209143+c.lower,100332817761381+c.upper)) = pointBounds20487 := by
 decide +kernel
def cuts20488 : List PrefixCut := [⟨39,190590584,190590694⟩,
⟨122,593113631,593113978⟩,
⟨128,625662391,625662756⟩]
theorem checked20488 : checkPrefixCuts (2^48) 2689335297 9 Manual.Count131072.C020488.packed 128 cuts20488 = true := by
 decide +kernel
def pointBounds20488 : List (Nat × Nat × Nat) := [(2689375232,100333257679097,100333638231812),(2689460224,100333660202144,100334040755096)]
theorem point_links_checked20488 : (cuts20488.take 2).map (fun c => (2689335297-1+2*2^9*c.k,100333067088513+c.lower,100333447641118+c.upper)) = pointBounds20488 := by
 decide +kernel
def cuts20489 : List PrefixCut := [⟨77,379066712,379066931⟩,
⟨128,633271713,633272079⟩]
theorem checked20489 : checkPrefixCuts (2^48) 2689466369 9 Manual.Count131072.C020489.packed 128 cuts20489 = true := by
 decide +kernel
def pointBounds20489 : List (Nat × Nat × Nat) := [(2689545216,100334071817616,100334452370805)]
theorem point_links_checked20489 : (cuts20489.take 1).map (fun c => (2689466369-1+2*2^9*c.k,100333692750904+c.lower,100334073303874+c.upper)) = pointBounds20489 := by
 decide +kernel
def cuts20490 : List PrefixCut := [⟨32,157397394,157397490⟩,
⟨115,566161279,566161610⟩,
⟨128,631147899,631148267⟩]
theorem checked20490 : checkPrefixCuts (2^48) 2689597441 9 Manual.Count131072.C020490.packed 128 cuts20490 = true := by
 decide +kernel
def pointBounds20490 : List (Nat × Nat × Nat) := [(2689630208,100334483420011,100334863973443),(2689715200,100334892183896,100335272737563)]
theorem point_links_checked20490 : (cuts20490.take 2).map (fun c => (2689597441-1+2*2^9*c.k,100334326022617+c.lower,100334706575953+c.upper)) = pointBounds20490 := by
 decide +kernel
def cuts20491 : List PrefixCut := [⟨70,344915438,344915644⟩,
⟨128,632582175,632582546⟩]
theorem checked20491 : checkPrefixCuts (2^48) 2689728513 9 Manual.Count131072.C020491.packed 128 cuts20491 = true := by
 decide +kernel
def pointBounds20491 : List (Nat × Nat × Nat) := [(2689800192,100335302085954,100335682639864)]
theorem point_links_checked20491 : (cuts20491.take 1).map (fun c => (2689728513-1+2*2^9*c.k,100334957170516+c.lower,100335337724220+c.upper)) = pointBounds20491 := by
 decide +kernel
def cuts20492 : List PrefixCut := [⟨25,123268832,123268906⟩,
⟨108,527703670,527703979⟩,
⟨128,623552321,623552686⟩]
theorem checked20492 : checkPrefixCuts (2^48) 2689859585 9 Manual.Count131072.C020492.packed 128 cuts20492 = true := by
 decide +kernel
def pointBounds20492 : List (Nat × Nat × Nat) := [(2689885184,100335713021523,100336093575672),(2689970176,100336117456361,100336498010745)]
theorem point_links_checked20492 : (cuts20492.take 2).map (fun c => (2689859585-1+2*2^9*c.k,100335589752691+c.lower,100335970306766+c.upper)) = pointBounds20492 := by
 decide +kernel
def cuts20493 : List PrefixCut := [⟨63,310247592,310247779⟩,
⟨128,628439806,628440177⟩]
theorem checked20493 : checkPrefixCuts (2^48) 2689990657 9 Manual.Count131072.C020493.packed 128 cuts20493 = true := by
 decide +kernel
def pointBounds20493 : List (Nat × Nat × Nat) := [(2690055168,100336523552604,100336904107231)]
theorem point_links_checked20493 : (cuts20493.take 1).map (fun c => (2689990657-1+2*2^9*c.k,100336213305012+c.lower,100336593859452+c.upper)) = pointBounds20493 := by
 decide +kernel
def cuts20494 : List PrefixCut := [⟨18,86007850,86007901⟩,
⟨101,491032115,491032406⟩,
⟨128,626316392,626316760⟩]
theorem checked20494 : checkPrefixCuts (2^48) 2690121729 9 Manual.Count131072.C020494.packed 128 cuts20494 = true := by
 decide +kernel
def pointBounds20494 : List (Nat × Nat × Nat) := [(2690140160,100336927752668,100337308307530),(2690225152,100337332776933,100337713332035)]
theorem point_links_checked20494 : (cuts20494.take 2).map (fun c => (2690121729-1+2*2^9*c.k,100336841744818+c.lower,100337222299629+c.upper)) = pointBounds20494 := by
 decide +kernel
def cuts20495 : List PrefixCut := [⟨56,277051152,277051315⟩,
⟨128,638527121,638527496⟩]
theorem checked20495 : checkPrefixCuts (2^48) 2690252801 9 Manual.Count131072.C020495.packed 128 cuts20495 = true := by
 decide +kernel
def pointBounds20495 : List (Nat × Nat × Nat) := [(2690310144,100337745112362,100338125667704)]
theorem point_links_checked20495 : (cuts20495.take 1).map (fun c => (2690252801-1+2*2^9*c.k,100337468061210+c.lower,100337848616389+c.upper)) = pointBounds20495 := by
 decide +kernel
def cuts20496 : List PrefixCut := [⟨11,54508249,54508279⟩,
⟨94,469433069,469433341⟩,
⟨128,635148242,635148608⟩]
theorem checked20496 : checkPrefixCuts (2^48) 2690383873 9 Manual.Count131072.C020496.packed 128 cuts20496 = true := by
 decide +kernel
def pointBounds20496 : List (Nat × Nat × Nat) := [(2690395136,100338161096580,100338541652164),(2690480128,100338576021400,100338956577226)]
theorem point_links_checked20496 : (cuts20496.take 2).map (fun c => (2690383873-1+2*2^9*c.k,100338106588331+c.lower,100338487143885+c.upper)) = pointBounds20496 := by
 decide +kernel
def cuts20497 : List PrefixCut := [⟨49,247627272,247627418⟩,
⟨128,628526752,628527118⟩]
theorem checked20497 : checkPrefixCuts (2^48) 2690514945 9 Manual.Count131072.C020497.packed 128 cuts20497 = true := by
 decide +kernel
def pointBounds20497 : List (Nat × Nat × Nat) := [(2690565120,100338989363845,100339369919911)]
theorem point_links_checked20497 : (cuts20497.take 1).map (fun c => (2690514945-1+2*2^9*c.k,100338741736573+c.lower,100339122292493+c.upper)) = pointBounds20497 := by
 decide +kernel
def cuts20498 : List PrefixCut := [⟨4,22282422,22282435⟩,
⟨87,433192722,433192977⟩,
⟨128,630797450,630797820⟩]
theorem checked20498 : checkPrefixCuts (2^48) 2690646017 9 Manual.Count131072.C020498.packed 128 cuts20498 = true := by
 decide +kernel
def pointBounds20498 : List (Nat × Nat × Nat) := [(2690650112,100339392545747,100339773102046),(2690735104,100339803456047,100340184012588)]
theorem point_links_checked20498 : (cuts20498.take 2).map (fun c => (2690646017-1+2*2^9*c.k,100339370263325+c.lower,100339750819611+c.upper)) = pointBounds20498 := by
 decide +kernel
def cuts20499 : List PrefixCut := [⟨42,202831887,202832006⟩,
⟨125,619887915,619888269⟩,
⟨128,633590811,633591172⟩]
theorem checked20499 : checkPrefixCuts (2^48) 2690777089 9 Manual.Count131072.C020499.packed 128 cuts20499 = true := by
 decide +kernel
def pointBounds20499 : List (Nat × Nat × Nat) := [(2690820096,100340203892662,100340584449437),(2690905088,100340620948690,100341001505700)]
theorem point_links_checked20499 : (cuts20499.take 2).map (fun c => (2690777089-1+2*2^9*c.k,100340001060775+c.lower,100340381617431+c.upper)) = pointBounds20499 := by
 decide +kernel
def cuts20500 : List PrefixCut := [⟨80,397796126,397796361⟩,
⟨128,630213010,630213379⟩]
theorem checked20500 : checkPrefixCuts (2^48) 2690908161 9 Manual.Count131072.C020500.packed 128 cuts20500 = true := by
 decide +kernel
def pointBounds20500 : List (Nat × Nat × Nat) := [(2690990080,100341032447712,100341413004964)]
theorem point_links_checked20500 : (cuts20500.take 1).map (fun c => (2690908161-1+2*2^9*c.k,100340634651586+c.lower,100341015208603+c.upper)) = pointBounds20500 := by
 decide +kernel
def cuts20501 : List PrefixCut := [⟨35,169236991,169237090⟩,
⟨118,583847806,583848145⟩,
⟨128,632587771,632588137⟩]
theorem checked20501 : checkPrefixCuts (2^48) 2691039233 9 Manual.Count131072.C020501.packed 128 cuts20501 = true := by
 decide +kernel
def pointBounds20501 : List (Nat × Nat × Nat) := [(2691075072,100341434101587,100341814659072),(2691160064,100341848712402,100342229270127)]
theorem point_links_checked20501 : (cuts20501.take 2).map (fun c => (2691039233-1+2*2^9*c.k,100341264864596+c.lower,100341645421982+c.upper)) = pointBounds20501 := by
 decide +kernel
def cuts20502 : List PrefixCut := [⟨73,366589820,366590034⟩,
⟨128,636636039,636636414⟩]
theorem checked20502 : checkPrefixCuts (2^48) 2691170305 9 Manual.Count131072.C020502.packed 128 cuts20502 = true := by
 decide +kernel
def pointBounds20502 : List (Nat × Nat × Nat) := [(2691245056,100342264042187,100342644600153)]
theorem point_links_checked20502 : (cuts20502.take 1).map (fun c => (2691170305-1+2*2^9*c.k,100341897452367+c.lower,100342278010119+c.upper)) = pointBounds20502 := by
 decide +kernel
def cuts20503 : List PrefixCut := [⟨28,138995262,138995345⟩,
⟨111,540807588,540807901⟩,
⟨128,619348784,619349144⟩]
theorem checked20503 : checkPrefixCuts (2^48) 2691301377 9 Manual.Count131072.C020503.packed 128 cuts20503 = true := by
 decide +kernel
def pointBounds20503 : List (Nat × Nat × Nat) := [(2691330048,100342673083668,100343053641878),(2691415040,100343074895994,100343455454434)]
theorem point_links_checked20503 : (cuts20503.take 2).map (fun c => (2691301377-1+2*2^9*c.k,100342534088406+c.lower,100342914646533+c.upper)) = pointBounds20503 := by
 decide +kernel
def cuts20504 : List PrefixCut := [⟨66,328487334,328487525⟩,
⟨128,633122982,633123350⟩]
theorem checked20504 : checkPrefixCuts (2^48) 2691432449 9 Manual.Count131072.C020504.packed 128 cuts20504 = true := by
 decide +kernel
def pointBounds20504 : List (Nat × Nat × Nat) := [(2691500032,100343481924524,100343862483202)]
theorem point_links_checked20504 : (cuts20504.take 1).map (fun c => (2691432449-1+2*2^9*c.k,100343153437190+c.lower,100343533995677+c.upper)) = pointBounds20504 := by
 decide +kernel
def cuts20505 : List PrefixCut := [⟨21,102798502,102798563⟩,
⟨104,515971281,515971585⟩,
⟨128,637274926,637275300⟩]
theorem checked20505 : checkPrefixCuts (2^48) 2691563521 9 Manual.Count131072.C020505.packed 128 cuts20505 = true := by
 decide +kernel
def pointBounds20505 : List (Nat × Nat × Nat) := [(2691585024,100343889358674,100344269917590),(2691670016,100344302531453,100344683090612)]
theorem point_links_checked20505 : (cuts20505.take 2).map (fun c => (2691563521-1+2*2^9*c.k,100343786560172+c.lower,100344167119027+c.upper)) = pointBounds20505 := by
 decide +kernel
def cuts20506 : List PrefixCut := [⟨59,291228712,291228881⟩,
⟨128,628146482,628146846⟩]
theorem checked20506 : checkPrefixCuts (2^48) 2691694593 9 Manual.Count131072.C020506.packed 128 cuts20506 = true := by
 decide +kernel
def pointBounds20506 : List (Nat × Nat × Nat) := [(2691755008,100344715063810,100345095623208)]
theorem point_links_checked20506 : (cuts20506.take 1).map (fun c => (2691694593-1+2*2^9*c.k,100344423835098+c.lower,100344804394327+c.upper)) = pointBounds20506 := by
 decide +kernel
def cuts20507 : List PrefixCut := [⟨14,67549804,67549844⟩,
⟨97,478592200,478592483⟩,
⟨128,633030380,633030751⟩]
theorem checked20507 : checkPrefixCuts (2^48) 2691825665 9 Manual.Count131072.C020507.packed 128 cuts20507 = true := by
 decide +kernel
def pointBounds20507 : List (Nat × Nat × Nat) := [(2691840000,100345119531384,100345500091017),(2691924992,100345530573780,100345911133656)]
theorem point_links_checked20507 : (cuts20507.take 2).map (fun c => (2691825665-1+2*2^9*c.k,100345051981580+c.lower,100345432541173+c.upper)) = pointBounds20507 := by
 decide +kernel
def cuts20508 : List PrefixCut := [⟨52,265374361,265374516⟩,
⟨128,638436848,638437217⟩]
theorem checked20508 : checkPrefixCuts (2^48) 2691956737 9 Manual.Count131072.C020508.packed 128 cuts20508 = true := by
 decide +kernel
def pointBounds20508 : List (Nat × Nat × Nat) := [(2692009984,100345950386321,100346330946440)]
theorem point_links_checked20508 : (cuts20508.take 1).map (fun c => (2691956737-1+2*2^9*c.k,100345685011960+c.lower,100346065571924+c.upper)) = pointBounds20508 := by
 decide +kernel
def cuts20509 : List PrefixCut := [⟨7,33248877,33248896⟩,
⟨90,443938635,443938889⟩,
⟨128,628577493,628577857⟩]
theorem checked20509 : checkPrefixCuts (2^48) 2692087809 9 Manual.Count131072.C020509.packed 128 cuts20509 = true := by
 decide +kernel
def pointBounds20509 : List (Nat × Nat × Nat) := [(2692094976,100346356697685,100346737258037),(2692179968,100346767387443,100347147948030)]
theorem point_links_checked20509 : (cuts20509.take 2).map (fun c => (2692087809-1+2*2^9*c.k,100346323448808+c.lower,100346704009141+c.upper)) = pointBounds20509 := by
 decide +kernel
def cuts20510 : List PrefixCut := [⟨45,218614820,218614951⟩,
⟨128,630846892,630847264⟩]
theorem checked20510 : checkPrefixCuts (2^48) 2692218881 9 Manual.Count131072.C020510.packed 128 cuts20510 = true := by
 decide +kernel
def pointBounds20510 : List (Nat × Nat × Nat) := [(2692264960,100347170641121,100347551201949),(2692349952,100347582873193,100347963434262)]
theorem point_links_checked20510 : (cuts20510.take 2).map (fun c => (2692218881-1+2*2^9*c.k,100346952026301+c.lower,100347332586998+c.upper)) = pointBounds20510 := by
 decide +kernel
def cuts20511 : List PrefixCut := [⟨83,408559993,408560232⟩,
⟨128,631652574,631652946⟩]
theorem checked20511 : checkPrefixCuts (2^48) 2692349953 9 Manual.Count131072.C020511.packed 128 cuts20511 = true := by
 decide +kernel
def pointBounds20511 : List (Nat × Nat × Nat) := [(2692434944,100347991433186,100348371994494)]
theorem point_links_checked20511 : (cuts20511.take 1).map (fun c => (2692349953-1+2*2^9*c.k,100347582873193+c.lower,100347963434262+c.upper)) = pointBounds20511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000015
