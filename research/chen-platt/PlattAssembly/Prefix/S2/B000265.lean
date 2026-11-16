import PlattAssemblyKernel
import PlattCertificates.Count131072.C018480
import PlattCertificates.Count131072.C018481
import PlattCertificates.Count131072.C018482
import PlattCertificates.Count131072.C018483
import PlattCertificates.Count131072.C018484
import PlattCertificates.Count131072.C018485
import PlattCertificates.Count131072.C018486
import PlattCertificates.Count131072.C018487
import PlattCertificates.Count131072.C018488
import PlattCertificates.Count131072.C018489
import PlattCertificates.Count131072.C018490
import PlattCertificates.Count131072.C018491
import PlattCertificates.Count131072.C018492
import PlattCertificates.Count131072.C018493
import PlattCertificates.Count131072.C018494
import PlattCertificates.Count131072.C018495
import PlattCertificates.Count131072.C018496
import PlattCertificates.Count131072.C018497
import PlattCertificates.Count131072.C018498
import PlattCertificates.Count131072.C018499
import PlattCertificates.Count131072.C018500
import PlattCertificates.Count131072.C018501
import PlattCertificates.Count131072.C018502
import PlattCertificates.Count131072.C018503
import PlattCertificates.Count131072.C018504
import PlattCertificates.Count131072.C018505
import PlattCertificates.Count131072.C018506
import PlattCertificates.Count131072.C018507
import PlattCertificates.Count131072.C018508
import PlattCertificates.Count131072.C018509
import PlattCertificates.Count131072.C018510
import PlattCertificates.Count131072.C018511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000265
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18480 : List PrefixCut := [⟨12,68914196,68914239⟩,
⟨87,480883524,480883818⟩,
⟨128,712327861,712328294⟩]
theorem checked18480 : checkPrefixCuts (2^48) 2426142721 9 Manual.Count131072.C018480.packed 128 cuts18480 = true := by
 decide +kernel
def pointBounds18480 : List (Nat × Nat × Nat) := [(2426155008,98994725691297,98995105449719),(2426231808,98995137660625,98995517419298)]
theorem point_links_checked18480 : (cuts18480.take 2).map (fun c => (2426142721-1+2*2^9*c.k,98994656777101+c.lower,98995036535480+c.upper)) = pointBounds18480 := by
 decide +kernel
def cuts18481 : List PrefixCut := [⟨34,186660630,186660742⟩,
⟨109,598139872,598140232⟩,
⟨128,702660710,702661134⟩]
theorem checked18481 : checkPrefixCuts (2^48) 2426273793 9 Manual.Count131072.C018481.packed 128 cuts18481 = true := by
 decide +kernel
def pointBounds18481 : List (Nat × Nat × Nat) := [(2426308608,98995555765592,98995935524516),(2426385408,98995967244834,98996347004006)]
theorem point_links_checked18481 : (cuts18481.take 2).map (fun c => (2426273793-1+2*2^9*c.k,98995369104962+c.lower,98995748863774+c.upper)) = pointBounds18481 := by
 decide +kernel
def cuts18482 : List PrefixCut := [⟨56,309729464,309729651⟩,
⟨128,699142839,699143265⟩]
theorem checked18482 : checkPrefixCuts (2^48) 2426404865 9 Manual.Count131072.C018482.packed 128 cuts18482 = true := by
 decide +kernel
def pointBounds18482 : List (Nat × Nat × Nat) := [(2426462208,98996381495136,98996761254559)]
theorem point_links_checked18482 : (cuts18482.take 1).map (fun c => (2426404865-1+2*2^9*c.k,98996071765672+c.lower,98996451524908+c.upper)) = pointBounds18482 := by
 decide +kernel
def cuts18483 : List PrefixCut := [⟨3,17283788,17283798⟩,
⟨78,438815677,438815940⟩,
⟨128,716272350,716272776⟩]
theorem checked18483 : checkPrefixCuts (2^48) 2426535937 9 Manual.Count131072.C018483.packed 128 cuts18483 = true := by
 decide +kernel
def pointBounds18483 : List (Nat × Nat × Nat) := [(2426539008,98996788192299,98997167951971),(2426615808,98997209724188,98997589484113)]
theorem point_links_checked18483 : (cuts18483.take 2).map (fun c => (2426535937-1+2*2^9*c.k,98996770908511+c.lower,98997150668173+c.upper)) = pointBounds18483 := by
 decide +kernel
def cuts18484 : List PrefixCut := [⟨25,135594376,135594457⟩,
⟨100,555359820,555360157⟩,
⟨128,706258687,706259117⟩]
theorem checked18484 : checkPrefixCuts (2^48) 2426667009 9 Manual.Count131072.C018484.packed 128 cuts18484 = true := by
 decide +kernel
def pointBounds18484 : List (Nat × Nat × Nat) := [(2426692608,98997622775237,98998002535406),(2426769408,98998042540681,98998422301106)]
theorem point_links_checked18484 : (cuts18484.take 2).map (fun c => (2426667009-1+2*2^9*c.k,98997487180861+c.lower,98997866940949+c.upper)) = pointBounds18484 := by
 decide +kernel
def cuts18485 : List PrefixCut := [⟨47,260966144,260966306⟩,
⟨122,664815379,664815789⟩,
⟨128,699841338,699841768⟩]
theorem checked18485 : checkPrefixCuts (2^48) 2426798081 9 Manual.Count131072.C018485.packed 128 cuts18485 = true := by
 decide +kernel
def pointBounds18485 : List (Nat × Nat × Nat) := [(2426846208,98998454405692,98998834166372),(2426923008,98998858254927,98999238015855)]
theorem point_links_checked18485 : (cuts18485.take 2).map (fun c => (2426798081-1+2*2^9*c.k,98998193439548+c.lower,98998573200066+c.upper)) = pointBounds18485 := by
 decide +kernel
def cuts18486 : List PrefixCut := [⟨69,375653274,375653503⟩,
⟨128,703978620,703979045⟩]
theorem checked18486 : checkPrefixCuts (2^48) 2426929153 9 Manual.Count131072.C018486.packed 128 cuts18486 = true := by
 decide +kernel
def pointBounds18486 : List (Nat × Nat × Nat) := [(2426999808,98999268934160,98999648695337)]
theorem point_links_checked18486 : (cuts18486.take 1).map (fun c => (2426929153-1+2*2^9*c.k,98998893280886+c.lower,98999273041834+c.upper)) = pointBounds18486 := by
 decide +kernel
def cuts18487 : List PrefixCut := [⟨16,88023662,88023714⟩,
⟨91,499488663,499488962⟩,
⟨128,703824688,703825112⟩]
theorem checked18487 : checkPrefixCuts (2^48) 2427060225 9 Manual.Count131072.C018487.packed 128 cuts18487 = true := by
 decide +kernel
def pointBounds18487 : List (Nat × Nat × Nat) := [(2427076608,98999685283168,99000065044593),(2427153408,99000096748169,99000476509841)]
theorem point_links_checked18487 : (cuts18487.take 2).map (fun c => (2427060225-1+2*2^9*c.k,98999597259506+c.lower,98999977020879+c.upper)) = pointBounds18487 := by
 decide +kernel
def cuts18488 : List PrefixCut := [⟨38,207927748,207927879⟩,
⟨113,624701077,624701463⟩,
⟨128,707033697,707034134⟩]
theorem checked18488 : checkPrefixCuts (2^48) 2427191297 9 Manual.Count131072.C018488.packed 128 cuts18488 = true := by
 decide +kernel
def pointBounds18488 : List (Nat × Nat × Nat) := [(2427230208,99000509011942,99000888773870),(2427307008,99000925785271,99001305547454)]
theorem point_links_checked18488 : (cuts18488.take 2).map (fun c => (2427191297-1+2*2^9*c.k,99000301084194+c.lower,99000680845991+c.upper)) = pointBounds18488 := by
 decide +kernel
def cuts18489 : List PrefixCut := [⟨60,329673155,329673348⟩,
⟨128,707459339,707459757⟩]
theorem checked18489 : checkPrefixCuts (2^48) 2427322369 9 Manual.Count131072.C018489.packed 128 cuts18489 = true := by
 decide +kernel
def pointBounds18489 : List (Nat × Nat × Nat) := [(2427383808,99001337791046,99001717553473)]
theorem point_links_checked18489 : (cuts18489.take 1).map (fun c => (2427322369-1+2*2^9*c.k,99001008117891+c.lower,99001387880125+c.upper)) = pointBounds18489 := by
 decide +kernel
def cuts18490 : List PrefixCut := [⟨7,35714027,35714048⟩,
⟨82,450708466,450708738⟩,
⟨128,706261518,706261946⟩]
theorem checked18490 : checkPrefixCuts (2^48) 2427453441 9 Manual.Count131072.C018490.packed 128 cuts18490 = true := by
 decide +kernel
def pointBounds18490 : List (Nat × Nat × Nat) := [(2427460608,99001751291257,99002131053930),(2427537408,99002166285696,99002546048620)]
theorem point_links_checked18490 : (cuts18490.take 2).map (fun c => (2427453441-1+2*2^9*c.k,99001715577230+c.lower,99002095339882+c.upper)) = pointBounds18490 := by
 decide +kernel
def cuts18491 : List PrefixCut := [⟨29,162906689,162906787⟩,
⟨104,574048643,574048991⟩,
⟨128,701585802,701586226⟩]
theorem checked18491 : checkPrefixCuts (2^48) 2427584513 9 Manual.Count131072.C018491.packed 128 cuts18491 = true := by
 decide +kernel
def pointBounds18491 : List (Nat × Nat × Nat) := [(2427614208,99002584745437,99002964508615),(2427691008,99002995887391,99003375650819)]
theorem point_links_checked18491 : (cuts18491.take 2).map (fun c => (2427584513-1+2*2^9*c.k,99002421838748+c.lower,99002801601828+c.upper)) = pointBounds18491 := by
 decide +kernel
def cuts18492 : List PrefixCut := [⟨51,277099054,277099225⟩,
⟨126,682765931,682766346⟩,
⟨128,692968306,692968727⟩]
theorem checked18492 : checkPrefixCuts (2^48) 2427715585 9 Manual.Count131072.C018492.packed 128 cuts18492 = true := by
 decide +kernel
def pointBounds18492 : List (Nat × Nat × Nat) := [(2427767808,99003400523604,99003780287279),(2427844608,99003806190481,99004185954400)]
theorem point_links_checked18492 : (cuts18492.take 2).map (fun c => (2427715585-1+2*2^9*c.k,99003123424550+c.lower,99003503188054+c.upper)) = pointBounds18492 := by
 decide +kernel
def cuts18493 : List PrefixCut := [⟨73,400320963,400321201⟩,
⟨128,704292322,704292743⟩]
theorem checked18493 : checkPrefixCuts (2^48) 2427846657 9 Manual.Count131072.C018493.packed 128 cuts18493 = true := by
 decide +kernel
def pointBounds18493 : List (Nat × Nat × Nat) := [(2427921408,99004216713819,99004596477982)]
theorem point_links_checked18493 : (cuts18493.take 1).map (fun c => (2427846657-1+2*2^9*c.k,99003816392856+c.lower,99004196156781+c.upper)) = pointBounds18493 := by
 decide +kernel
def cuts18494 : List PrefixCut := [⟨20,107466441,107466508⟩,
⟨95,517847902,517848219⟩,
⟨128,700892394,700892820⟩]
theorem checked18494 : checkPrefixCuts (2^48) 2427977729 9 Manual.Count131072.C018494.packed 128 cuts18494 = true := by
 decide +kernel
def pointBounds18494 : List (Nat × Nat × Nat) := [(2427998208,99004628151619,99005007916032),(2428075008,99005038533080,99005418297743)]
theorem point_links_checked18494 : (cuts18494.take 2).map (fun c => (2427977729-1+2*2^9*c.k,99004520685178+c.lower,99004900449524+c.upper)) = pointBounds18494 := by
 decide +kernel
def cuts18495 : List PrefixCut := [⟨42,234858949,234859090⟩,
⟨117,640925337,640925727⟩,
⟨128,700043273,700043698⟩]
theorem checked18495 : checkPrefixCuts (2^48) 2428108801 9 Manual.Count131072.C018495.packed 128 cuts18495 = true := by
 decide +kernel
def pointBounds18495 : List (Nat × Nat × Nat) := [(2428151808,99005456436521,99005836201434),(2428228608,99005862502909,99006242268071)]
theorem point_links_checked18495 : (cuts18495.take 2).map (fun c => (2428108801-1+2*2^9*c.k,99005221577572+c.lower,99005601342344+c.upper)) = pointBounds18495 := by
 decide +kernel
def cuts18496 : List PrefixCut := [⟨64,347862904,347863115⟩,
⟨128,700005188,700005611⟩]
theorem checked18496 : checkPrefixCuts (2^48) 2428239873 9 Manual.Count131072.C018496.packed 128 cuts18496 = true := by
 decide +kernel
def pointBounds18496 : List (Nat × Nat × Nat) := [(2428305408,99006269483749,99006649249157)]
theorem point_links_checked18496 : (cuts18496.take 1).map (fun c => (2428239873-1+2*2^9*c.k,99005921620845+c.lower,99006301386042+c.upper)) = pointBounds18496 := by
 decide +kernel
def cuts18497 : List PrefixCut := [⟨11,61200862,61200898⟩,
⟨86,474183322,474183605⟩,
⟨128,707153915,707154338⟩]
theorem checked18497 : checkPrefixCuts (2^48) 2428370945 9 Manual.Count131072.C018497.packed 128 cuts18497 = true := by
 decide +kernel
def pointBounds18497 : List (Nat × Nat × Nat) := [(2428382208,99006682826895,99007062592551),(2428459008,99007095809355,99007475575258)]
theorem point_links_checked18497 : (cuts18497.take 2).map (fun c => (2428370945-1+2*2^9*c.k,99006621626033+c.lower,99007001391653+c.upper)) = pointBounds18497 := by
 decide +kernel
def cuts18498 : List PrefixCut := [⟨33,179535184,179535291⟩,
⟨108,593534634,593534996⟩,
⟨128,703175060,703175489⟩]
theorem checked18498 : checkPrefixCuts (2^48) 2428502017 9 Manual.Count131072.C018498.packed 128 cuts18498 = true := by
 decide +kernel
def pointBounds18498 : List (Nat × Nat × Nat) := [(2428535808,99007508315132,99007888081282),(2428612608,99007922314582,99008302080987)]
theorem point_links_checked18498 : (cuts18498.take 2).map (fun c => (2428502017-1+2*2^9*c.k,99007328779948+c.lower,99007708545991+c.upper)) = pointBounds18498 := by
 decide +kernel
def cuts18499 : List PrefixCut := [⟨55,300521269,300521454⟩,
⟨128,704875571,704875996⟩]
theorem checked18499 : checkPrefixCuts (2^48) 2428633089 9 Manual.Count131072.C018499.packed 128 cuts18499 = true := by
 decide +kernel
def pointBounds18499 : List (Nat × Nat × Nat) := [(2428689408,99008332476277,99008712242934)]
theorem point_links_checked18499 : (cuts18499.take 1).map (fun c => (2428633089-1+2*2^9*c.k,99008031955008+c.lower,99008411721480+c.upper)) = pointBounds18499 := by
 decide +kernel
def cuts18500 : List PrefixCut := [⟨2,9850835,9850841⟩,
⟨77,425665163,425665416⟩,
⟨128,700897271,700897695⟩]
theorem checked18500 : checkPrefixCuts (2^48) 2428764161 9 Manual.Count131072.C018500.packed 128 cuts18500 = true := by
 decide +kernel
def pointBounds18500 : List (Nat × Nat × Nat) := [(2428766208,99008746681414,99009126448317),(2428843008,99009162495742,99009542262892)]
theorem point_links_checked18500 : (cuts18500.take 2).map (fun c => (2428764161-1+2*2^9*c.k,99008736830579+c.lower,99009116597476+c.upper)) = pointBounds18500 := by
 decide +kernel
def cuts18501 : List PrefixCut := [⟨24,125735650,125735726⟩,
⟨99,537699661,537699981⟩,
⟨128,696455841,696456260⟩]
theorem checked18501 : checkPrefixCuts (2^48) 2428895233 9 Manual.Count131072.C018501.packed 128 cuts18501 = true := by
 decide +kernel
def pointBounds18501 : List (Nat × Nat × Nat) := [(2428919808,99009563463500,99009943230897),(2428996608,99009975427511,99010355195152)]
theorem point_links_checked18501 : (cuts18501.take 2).map (fun c => (2428895233-1+2*2^9*c.k,99009437727850+c.lower,99009817495171+c.upper)) = pointBounds18501 := by
 decide +kernel
def cuts18502 : List PrefixCut := [⟨46,254353521,254353671⟩,
⟨121,662351608,662352005⟩,
⟨128,701980394,701980815⟩]
theorem checked18502 : checkPrefixCuts (2^48) 2429026305 9 Manual.Count131072.C018502.packed 128 cuts18502 = true := by
 decide +kernel
def pointBounds18502 : List (Nat × Nat × Nat) := [(2429073408,99010388537212,99010768305102),(2429150208,99010796535299,99011176303436)]
theorem point_links_checked18502 : (cuts18502.take 2).map (fun c => (2429026305-1+2*2^9*c.k,99010134183691+c.lower,99010513951431+c.upper)) = pointBounds18502 := by
 decide +kernel
def cuts18503 : List PrefixCut := [⟨68,373223073,373223301⟩,
⟨128,699045764,699046187⟩]
theorem checked18503 : checkPrefixCuts (2^48) 2429157377 9 Manual.Count131072.C018503.packed 128 cuts18503 = true := by
 decide +kernel
def pointBounds18503 : List (Nat × Nat × Nat) := [(2429227008,99011209387158,99011589155547)]
theorem point_links_checked18503 : (cuts18503.take 1).map (fun c => (2429157377-1+2*2^9*c.k,99010836164085+c.lower,99011215932246+c.upper)) = pointBounds18503 := by
 decide +kernel
def cuts18504 : List PrefixCut := [⟨15,80179867,80179914⟩,
⟨90,496829178,496829476⟩,
⟨128,708393001,708393426⟩]
theorem checked18504 : checkPrefixCuts (2^48) 2429288449 9 Manual.Count131072.C018504.packed 128 cuts18504 = true := by
 decide +kernel
def pointBounds18504 : List (Nat × Nat × Nat) := [(2429303808,99011615389716,99011995158347),(2429380608,99012032039027,99012411807909)]
theorem point_links_checked18504 : (cuts18504.take 2).map (fun c => (2429288449-1+2*2^9*c.k,99011535209849+c.lower,99011914978433+c.upper)) = pointBounds18504 := by
 decide +kernel
def cuts18505 : List PrefixCut := [⟨37,202870976,202871100⟩,
⟨112,616597548,616597922⟩,
⟨128,703257165,703257594⟩]
theorem checked18505 : checkPrefixCuts (2^48) 2429419521 9 Manual.Count131072.C018505.packed 128 cuts18505 = true := by
 decide +kernel
def pointBounds18505 : List (Nat × Nat × Nat) := [(2429457408,99012446473826,99012826242959),(2429534208,99012860200398,99013239969781)]
theorem point_links_checked18505 : (cuts18505.take 2).map (fun c => (2429419521-1+2*2^9*c.k,99012243602850+c.lower,99012623371859+c.upper)) = pointBounds18505 := by
 decide +kernel
def cuts18506 : List PrefixCut := [⟨59,320797680,320797874⟩,
⟨128,699511856,699512277⟩]
theorem checked18506 : checkPrefixCuts (2^48) 2429550593 9 Manual.Count131072.C018506.packed 128 cuts18506 = true := by
 decide +kernel
def pointBounds18506 : List (Nat × Nat × Nat) := [(2429611008,99013267657695,99013647427327)]
theorem point_links_checked18506 : (cuts18506.take 1).map (fun c => (2429550593-1+2*2^9*c.k,99012946860015+c.lower,99013326629453+c.upper)) = pointBounds18506 := by
 decide +kernel
def cuts18507 : List PrefixCut := [⟨6,32900920,32900942⟩,
⟨81,447051523,447051790⟩,
⟨128,708162482,708162906⟩]
theorem checked18507 : checkPrefixCuts (2^48) 2429681665 9 Manual.Count131072.C018507.packed 128 cuts18507 = true := by
 decide +kernel
def pointBounds18507 : List (Nat × Nat × Nat) := [(2429687808,99013679272791,99014059042672),(2429764608,99014093423394,99014473193520)]
theorem point_links_checked18507 : (cuts18507.take 2).map (fun c => (2429681665-1+2*2^9*c.k,99013646371871+c.lower,99014026141730+c.upper)) = pointBounds18507 := by
 decide +kernel
def cuts18508 : List PrefixCut := [⟨28,155111797,155111888⟩,
⟨103,563791802,563792140⟩,
⟨128,701058142,701058562⟩]
theorem checked18508 : checkPrefixCuts (2^48) 2429812737 9 Manual.Count131072.C018508.packed 128 cuts18508 = true := by
 decide +kernel
def pointBounds18508 : List (Nat × Nat × Nat) := [(2429841408,99014509646150,99014889416524),(2429918208,99014918326155,99015298096776)]
theorem point_links_checked18508 : (cuts18508.take 2).map (fun c => (2429812737-1+2*2^9*c.k,99014354534353+c.lower,99014734304636+c.upper)) = pointBounds18508 := by
 decide +kernel
def cuts18509 : List PrefixCut := [⟨50,271053279,271053445⟩,
⟨125,678549207,678549617⟩,
⟨128,693607079,693607499⟩]
theorem checked18509 : checkPrefixCuts (2^48) 2429943809 9 Manual.Count131072.C018509.packed 128 cuts18509 = true := by
 decide +kernel
def pointBounds18509 : List (Nat × Nat × Nat) := [(2429995008,99015326645774,99015706416643),(2430071808,99015734141702,99016113912815)]
theorem point_links_checked18509 : (cuts18509.take 2).map (fun c => (2429943809-1+2*2^9*c.k,99015055592495+c.lower,99015435363198+c.upper)) = pointBounds18509 := by
 decide +kernel
def cuts18510 : List PrefixCut := [⟨72,399027398,399027642⟩,
⟨128,712912694,712913124⟩]
theorem checked18510 : checkPrefixCuts (2^48) 2430074881 9 Manual.Count131072.C018510.packed 128 cuts18510 = true := by
 decide +kernel
def pointBounds18510 : List (Nat × Nat × Nat) := [(2430148608,99016148226972,99016527998339)]
theorem point_links_checked18510 : (cuts18510.take 1).map (fun c => (2430074881-1+2*2^9*c.k,99015749199574+c.lower,99016128970697+c.upper)) = pointBounds18510 := by
 decide +kernel
def cuts18511 : List PrefixCut := [⟨19,102850832,102850893⟩,
⟨94,510771353,510771661⟩,
⟨128,691331692,691332110⟩]
theorem checked18511 : checkPrefixCuts (2^48) 2430205953 9 Manual.Count131072.C018511.packed 128 cuts18511 = true := by
 decide +kernel
def pointBounds18511 : List (Nat × Nat × Nat) := [(2430225408,99016564963100,99016944734714),(2430302208,99016972883621,99017352655482)]
theorem point_links_checked18511 : (cuts18511.take 2).map (fun c => (2430205953-1+2*2^9*c.k,99016462112268+c.lower,99016841883821+c.upper)) = pointBounds18511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000265
