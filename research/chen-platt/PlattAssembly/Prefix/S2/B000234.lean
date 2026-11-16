import PlattAssemblyKernel
import PlattCertificates.Count131072.C017488
import PlattCertificates.Count131072.C017489
import PlattCertificates.Count131072.C017490
import PlattCertificates.Count131072.C017491
import PlattCertificates.Count131072.C017492
import PlattCertificates.Count131072.C017493
import PlattCertificates.Count131072.C017494
import PlattCertificates.Count131072.C017495
import PlattCertificates.Count131072.C017496
import PlattCertificates.Count131072.C017497
import PlattCertificates.Count131072.C017498
import PlattCertificates.Count131072.C017499
import PlattCertificates.Count131072.C017500
import PlattCertificates.Count131072.C017501
import PlattCertificates.Count131072.C017502
import PlattCertificates.Count131072.C017503
import PlattCertificates.Count131072.C017504
import PlattCertificates.Count131072.C017505
import PlattCertificates.Count131072.C017506
import PlattCertificates.Count131072.C017507
import PlattCertificates.Count131072.C017508
import PlattCertificates.Count131072.C017509
import PlattCertificates.Count131072.C017510
import PlattCertificates.Count131072.C017511
import PlattCertificates.Count131072.C017512
import PlattCertificates.Count131072.C017513
import PlattCertificates.Count131072.C017514
import PlattCertificates.Count131072.C017515
import PlattCertificates.Count131072.C017516
import PlattCertificates.Count131072.C017517
import PlattCertificates.Count131072.C017518
import PlattCertificates.Count131072.C017519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000234
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17488 : List PrefixCut := [⟨54,312838784,312838977⟩,
⟨125,723734802,723735252⟩,
⟨128,742612169,742612631⟩]
theorem checked17488 : checkPrefixCuts (2^48) 2296119297 9 Manual.Count131072.C017488.packed 128 cuts17488 = true := by
 decide +kernel
def pointBounds17488 : List (Nat × Nat × Nat) := [(2296174592,98276724198315,98277103518218),(2296247296,98277135094333,98277514414493)]
theorem point_links_checked17488 : (cuts17488.take 2).map (fun c => (2296119297-1+2*2^9*c.k,98276411359531+c.lower,98276790679241+c.upper)) = pointBounds17488 := by
 decide +kernel
def cuts17489 : List PrefixCut := [⟨68,399482827,399483066⟩,
⟨128,750537229,750537681⟩]
theorem checked17489 : checkPrefixCuts (2^48) 2296250369 9 Manual.Count131072.C017489.packed 128 cuts17489 = true := by
 decide +kernel
def pointBounds17489 : List (Nat × Nat × Nat) := [(2296320000,98277553454527,98277932774938)]
theorem point_links_checked17489 : (cuts17489.take 1).map (fun c => (2296250369-1+2*2^9*c.k,98277153971700+c.lower,98277533291872+c.upper)) = pointBounds17489 := by
 decide +kernel
def cuts17490 : List PrefixCut := [⟨11,66066806,66066847⟩,
⟨82,490651616,490651919⟩,
⟨128,754171747,754172219⟩]
theorem checked17490 : checkPrefixCuts (2^48) 2296381441 9 Manual.Count131072.C017490.packed 128 cuts17490 = true := by
 decide +kernel
def pointBounds17490 : List (Nat × Nat × Nat) := [(2296392704,98277970575735,98278349896400),(2296465408,98278395160545,98278774481472)]
theorem point_links_checked17490 : (cuts17490.take 2).map (fun c => (2296381441-1+2*2^9*c.k,98277904508929+c.lower,98278283829553+c.upper)) = pointBounds17490 := by
 decide +kernel
def cuts17491 : List PrefixCut := [⟨25,146588380,146588470⟩,
⟨96,565876068,565876420⟩,
⟨128,751432095,751432562⟩]
theorem checked17491 : checkPrefixCuts (2^48) 2296512513 9 Manual.Count131072.C017491.packed 128 cuts17491 = true := by
 decide +kernel
def pointBounds17491 : List (Nat × Nat × Nat) := [(2296538112,98278805269056,98279184590242),(2296610816,98279224556744,98279603878192)]
theorem point_links_checked17491 : (cuts17491.take 2).map (fun c => (2296512513-1+2*2^9*c.k,98278658680676+c.lower,98279038001772+c.upper)) = pointBounds17491 := by
 decide +kernel
def cuts17492 : List PrefixCut := [⟨39,225016788,225016929⟩,
⟨110,633370541,633370943⟩,
⟨128,737050134,737050603⟩]
theorem checked17492 : checkPrefixCuts (2^48) 2296643585 9 Manual.Count131072.C017492.packed 128 cuts17492 = true := by
 decide +kernel
def pointBounds17492 : List (Nat × Nat × Nat) := [(2296683520,98279635129559,98280014451263),(2296756224,98280043483312,98280422805277)]
theorem point_links_checked17492 : (cuts17492.take 2).map (fun c => (2296643585-1+2*2^9*c.k,98279410112771+c.lower,98279789434334+c.upper)) = pointBounds17492 := by
 decide +kernel
def cuts17493 : List PrefixCut := [⟨53,310298672,310298862⟩,
⟨124,720709936,720710382⟩,
⟨128,743503374,743503834⟩]
theorem checked17493 : checkPrefixCuts (2^48) 2296774657 9 Manual.Count131072.C017493.packed 128 cuts17493 = true := by
 decide +kernel
def pointBounds17493 : List (Nat × Nat × Nat) := [(2296828928,98280457461577,98280836783799),(2296901632,98280867872841,98281247195319)]
theorem point_links_checked17493 : (cuts17493.take 2).map (fun c => (2296774657-1+2*2^9*c.k,98280147162905+c.lower,98280526484937+c.upper)) = pointBounds17493 := by
 decide +kernel
def cuts17494 : List PrefixCut := [⟨67,388585227,388585464⟩,
⟨128,751793539,751793999⟩]
theorem checked17494 : checkPrefixCuts (2^48) 2296905729 9 Manual.Count131072.C017494.packed 128 cuts17494 = true := by
 decide +kernel
def pointBounds17494 : List (Nat × Nat × Nat) := [(2296974336,98281279251506,98281658574235)]
theorem point_links_checked17494 : (cuts17494.take 1).map (fun c => (2296905729-1+2*2^9*c.k,98280890666279+c.lower,98281269988771+c.upper)) = pointBounds17494 := by
 decide +kernel
def cuts17495 : List PrefixCut := [⟨10,57715392,57715428⟩,
⟨81,469190530,469190821⟩,
⟨128,743295840,743296303⟩]
theorem checked17495 : checkPrefixCuts (2^48) 2297036801 9 Manual.Count131072.C017495.packed 128 cuts17495 = true := by
 decide +kernel
def pointBounds17495 : List (Nat × Nat × Nat) := [(2297047040,98281700175210,98282079498198),(2297119744,98282111650348,98282490973591)]
theorem point_links_checked17495 : (cuts17495.take 2).map (fun c => (2297036801-1+2*2^9*c.k,98281642459818+c.lower,98282021782770+c.upper)) = pointBounds17495 := by
 decide +kernel
def cuts17496 : List PrefixCut := [⟨24,141400328,141400416⟩,
⟨95,546845463,546845800⟩,
⟨128,729898066,729898516⟩]
theorem checked17496 : checkPrefixCuts (2^48) 2297167873 9 Manual.Count131072.C017496.packed 128 cuts17496 = true := by
 decide +kernel
def pointBounds17496 : List (Nat × Nat × Nat) := [(2297192448,98282527155986,98282906479489),(2297265152,98282932601121,98283311924873)]
theorem point_links_checked17496 : (cuts17496.take 2).map (fun c => (2297167873-1+2*2^9*c.k,98282385755658+c.lower,98282765079073+c.upper)) = pointBounds17496 := by
 decide +kernel
def cuts17497 : List PrefixCut := [⟨38,221522020,221522157⟩,
⟨109,634905376,634905775⟩,
⟨128,746396571,746397040⟩]
theorem checked17497 : checkPrefixCuts (2^48) 2297298945 9 Manual.Count131072.C017497.packed 128 cuts17497 = true := by
 decide +kernel
def pointBounds17497 : List (Nat × Nat × Nat) := [(2297337856,98283337175744,98283716499746),(2297410560,98283750559100,98284129883364)]
theorem point_links_checked17497 : (cuts17497.take 2).map (fun c => (2297298945-1+2*2^9*c.k,98283115653724+c.lower,98283494977589+c.upper)) = pointBounds17497 := by
 decide +kernel
def cuts17498 : List PrefixCut := [⟨52,293548036,293548216⟩,
⟨123,710703261,710703699⟩,
⟨128,739615726,739616180⟩]
theorem checked17498 : checkPrefixCuts (2^48) 2297430017 9 Manual.Count131072.C017498.packed 128 cuts17498 = true := by
 decide +kernel
def pointBounds17498 : List (Nat × Nat × Nat) := [(2297483264,98284155598331,98284534922845),(2297555968,98284572753556,98284952078328)]
theorem point_links_checked17498 : (cuts17498.take 2).map (fun c => (2297430017-1+2*2^9*c.k,98283862050295+c.lower,98284241374629+c.upper)) = pointBounds17498 := by
 decide +kernel
def cuts17499 : List PrefixCut := [⟨66,387616843,387617085⟩,
⟨128,752069169,752069632⟩]
theorem checked17499 : checkPrefixCuts (2^48) 2297561089 9 Manual.Count131072.C017499.packed 128 cuts17499 = true := by
 decide +kernel
def pointBounds17499 : List (Nat × Nat × Nat) := [(2297628672,98284989282864,98285368607894)]
theorem point_links_checked17499 : (cuts17499.take 1).map (fun c => (2297561089-1+2*2^9*c.k,98284601666021+c.lower,98284980990809+c.upper)) = pointBounds17499 := by
 decide +kernel
def cuts17500 : List PrefixCut := [⟨9,52921321,52921353⟩,
⟨80,460849343,460849631⟩,
⟨128,733284030,733284489⟩]
theorem checked17500 : checkPrefixCuts (2^48) 2297692161 9 Manual.Count131072.C017500.packed 128 cuts17500 = true := by
 decide +kernel
def pointBounds17500 : List (Nat × Nat × Nat) := [(2297701376,98285406656511,98285785981794),(2297774080,98285814584533,98286193910072)]
theorem point_links_checked17500 : (cuts17500.take 2).map (fun c => (2297692161-1+2*2^9*c.k,98285353735190+c.lower,98285733060441+c.upper)) = pointBounds17500 := by
 decide +kernel
def cuts17501 : List PrefixCut := [⟨23,135725232,135725317⟩,
⟨94,553304199,553304544⟩,
⟨128,749778589,749779053⟩]
theorem checked17501 : checkPrefixCuts (2^48) 2297823233 9 Manual.Count131072.C017501.packed 128 cuts17501 = true := by
 decide +kernel
def pointBounds17501 : List (Nat × Nat × Nat) := [(2297846784,98286222744452,98286602070247),(2297919488,98286640323419,98287019649474)]
theorem point_links_checked17501 : (cuts17501.take 2).map (fun c => (2297823233-1+2*2^9*c.k,98286087019220+c.lower,98286466344930+c.upper)) = pointBounds17501 := by
 decide +kernel
def cuts17502 : List PrefixCut := [⟨37,210189949,210190081⟩,
⟨108,617943794,617944172⟩,
⟨128,732465299,732465748⟩]
theorem checked17502 : checkPrefixCuts (2^48) 2297954305 9 Manual.Count131072.C017502.packed 128 cuts17502 = true := by
 decide +kernel
def pointBounds17502 : List (Nat × Nat × Nat) := [(2297992192,98287046987758,98287426314064),(2298064896,98287454741603,98287834068155)]
theorem point_links_checked17502 : (cuts17502.take 2).map (fun c => (2297954305-1+2*2^9*c.k,98286836797809+c.lower,98287216123983+c.upper)) = pointBounds17502 := by
 decide +kernel
def cuts17503 : List PrefixCut := [⟨51,295056571,295056753⟩,
⟨122,708663526,708663967⟩,
⟨128,743324101,743324562⟩]
theorem checked17503 : checkPrefixCuts (2^48) 2298085377 9 Manual.Count131072.C017503.packed 128 cuts17503 = true := by
 decide +kernel
def pointBounds17503 : List (Nat × Nat × Nat) := [(2298137600,98287864319679,98288243646484),(2298210304,98288277926634,98288657253698)]
theorem point_links_checked17503 : (cuts17503.take 2).map (fun c => (2298085377-1+2*2^9*c.k,98287569263108+c.lower,98287948589731+c.upper)) = pointBounds17503 := by
 decide +kernel
def cuts17504 : List PrefixCut := [⟨65,386526665,386526902⟩,
⟨128,756998741,756999202⟩]
theorem checked17504 : checkPrefixCuts (2^48) 2298216449 9 Manual.Count131072.C017504.packed 128 cuts17504 = true := by
 decide +kernel
def pointBounds17504 : List (Nat × Nat × Nat) := [(2298283008,98288699113874,98289078441195)]
theorem point_links_checked17504 : (cuts17504.take 1).map (fun c => (2298216449-1+2*2^9*c.k,98288312587209+c.lower,98288691914293+c.upper)) = pointBounds17504 := by
 decide +kernel
def cuts17505 : List PrefixCut := [⟨8,46292966,46292995⟩,
⟨79,461085320,461085608⟩,
⟨128,739443129,739443588⟩]
theorem checked17505 : checkPrefixCuts (2^48) 2298347521 9 Manual.Count131072.C017505.packed 128 cuts17505 = true := by
 decide +kernel
def pointBounds17505 : List (Nat × Nat × Nat) := [(2298355712,98289115878916,98289495206490),(2298428416,98289530671270,98289909999103)]
theorem point_links_checked17505 : (cuts17505.take 2).map (fun c => (2298347521-1+2*2^9*c.k,98289069585950+c.lower,98289448913495+c.upper)) = pointBounds17505 := by
 decide +kernel
def cuts17506 : List PrefixCut := [⟨22,131767807,131767890⟩,
⟨93,549350471,549350805⟩,
⟨128,750544617,750545080⟩]
theorem checked17506 : checkPrefixCuts (2^48) 2298478593 9 Manual.Count131072.C017506.packed 128 cuts17506 = true := by
 decide +kernel
def pointBounds17506 : List (Nat × Nat × Nat) := [(2298501120,98289940796886,98290320124973),(2298573824,98290358379550,98290737707888)]
theorem point_links_checked17506 : (cuts17506.take 2).map (fun c => (2298478593-1+2*2^9*c.k,98289809029079+c.lower,98290188357083+c.upper)) = pointBounds17506 := by
 decide +kernel
def cuts17507 : List PrefixCut := [⟨36,209762723,209762852⟩,
⟨107,624012782,624013164⟩,
⟨128,742787339,742787796⟩]
theorem checked17507 : checkPrefixCuts (2^48) 2298609665 9 Manual.Count131072.C017507.packed 128 cuts17507 = true := by
 decide +kernel
def pointBounds17507 : List (Nat × Nat × Nat) := [(2298646528,98290769336419,98291148665015),(2298719232,98291183586478,98291562915327)]
theorem point_links_checked17507 : (cuts17507.take 2).map (fun c => (2298609665-1+2*2^9*c.k,98290559573696+c.lower,98290938902163+c.upper)) = pointBounds17507 := by
 decide +kernel
def cuts17508 : List PrefixCut := [⟨50,290564514,290564692⟩,
⟨121,702094638,702095069⟩,
⟨128,742132726,742133182⟩]
theorem checked17508 : checkPrefixCuts (2^48) 2298740737 9 Manual.Count131072.C017508.packed 128 cuts17508 = true := by
 decide +kernel
def pointBounds17508 : List (Nat × Nat × Nat) := [(2298791936,98291592925549,98291972254651),(2298864640,98292004455673,98292383785028)]
theorem point_links_checked17508 : (cuts17508.take 2).map (fun c => (2298740737-1+2*2^9*c.k,98291302361035+c.lower,98291681689959+c.upper)) = pointBounds17508 := by
 decide +kernel
def cuts17509 : List PrefixCut := [⟨64,376499030,376499265⟩,
⟨128,748579690,748580153⟩]
theorem checked17509 : checkPrefixCuts (2^48) 2298871809 9 Manual.Count131072.C017509.packed 128 cuts17509 = true := by
 decide +kernel
def pointBounds17509 : List (Nat × Nat × Nat) := [(2298937344,98292420992791,98292800322406)]
theorem point_links_checked17509 : (cuts17509.take 1).map (fun c => (2298871809-1+2*2^9*c.k,98292044493761+c.lower,98292423823141+c.upper)) = pointBounds17509 := by
 decide +kernel
def cuts17510 : List PrefixCut := [⟨7,40158114,40158138⟩,
⟨78,444793022,444793300⟩,
⟨128,731274225,731274683⟩]
theorem checked17510 : checkPrefixCuts (2^48) 2299002881 9 Manual.Count131072.C017510.packed 128 cuts17510 = true := by
 decide +kernel
def pointBounds17510 : List (Nat × Nat × Nat) := [(2299010048,98292833231565,98293212561432),(2299082752,98293237866473,98293617196594)]
theorem point_links_checked17510 : (cuts17510.take 2).map (fun c => (2299002881-1+2*2^9*c.k,98292793073451+c.lower,98293172403294+c.upper)) = pointBounds17510 := by
 decide +kernel
def cuts17511 : List PrefixCut := [⟨21,123405318,123405389⟩,
⟨92,539400061,539400382⟩,
⟨128,750208148,750208600⟩]
theorem checked17511 : checkPrefixCuts (2^48) 2299133953 9 Manual.Count131072.C017511.packed 128 cuts17511 = true := by
 decide +kernel
def pointBounds17511 : List (Nat × Nat × Nat) := [(2299155456,98293647752994,98294027083366),(2299228160,98294063747737,98294443078359)]
theorem point_links_checked17511 : (cuts17511.take 2).map (fun c => (2299133953-1+2*2^9*c.k,98293524347676+c.lower,98293903677977+c.upper)) = pointBounds17511 := by
 decide +kernel
def cuts17512 : List PrefixCut := [⟨35,203949287,203949417⟩,
⟨106,618938366,618938748⟩,
⟨128,751022126,751022590⟩]
theorem checked17512 : checkPrefixCuts (2^48) 2299265025 9 Manual.Count131072.C017512.packed 128 cuts17512 = true := by
 decide +kernel
def pointBounds17512 : List (Nat × Nat × Nat) := [(2299300864,98294478505111,98294857835994),(2299373568,98294893494190,98295272825325)]
theorem point_links_checked17512 : (cuts17512.take 2).map (fun c => (2299265025-1+2*2^9*c.k,98294274555824+c.lower,98294653886577+c.upper)) = pointBounds17512 := by
 decide +kernel
def cuts17513 : List PrefixCut := [⟨49,288278330,288278510⟩,
⟨120,701527432,701527865⟩,
⟨128,746450349,746450810⟩]
theorem checked17513 : checkPrefixCuts (2^48) 2299396097 9 Manual.Count131072.C017513.packed 128 cuts17513 = true := by
 decide +kernel
def pointBounds17513 : List (Nat × Nat × Nat) := [(2299446272,98295313856280,98295693187677),(2299518976,98295727105382,98296106437032)]
theorem point_links_checked17513 : (cuts17513.take 2).map (fun c => (2299396097-1+2*2^9*c.k,98295025577950+c.lower,98295404909167+c.upper)) = pointBounds17513 := by
 decide +kernel
def cuts17514 : List PrefixCut := [⟨63,365008210,365008436⟩,
⟨128,748610968,748611434⟩]
theorem checked17514 : checkPrefixCuts (2^48) 2299527169 9 Manual.Count131072.C017514.packed 128 cuts17514 = true := by
 decide +kernel
def pointBounds17514 : List (Nat × Nat × Nat) := [(2299591680,98296137036509,98296516368413)]
theorem point_links_checked17514 : (cuts17514.take 1).map (fun c => (2299527169-1+2*2^9*c.k,98295772028299+c.lower,98296151359977+c.upper)) = pointBounds17514 := by
 decide +kernel
def cuts17515 : List PrefixCut := [⟨6,34393954,34393975⟩,
⟨77,448093433,448093712⟩,
⟨128,749914556,749915020⟩]
theorem checked17515 : checkPrefixCuts (2^48) 2299658241 9 Manual.Count131072.C017515.packed 128 cuts17515 = true := by
 decide +kernel
def pointBounds17515 : List (Nat × Nat × Nat) := [(2299664384,98296555033221,98296934365386),(2299737088,98296968732700,98297348065123)]
theorem point_links_checked17515 : (cuts17515.take 2).map (fun c => (2299658241-1+2*2^9*c.k,98296520639267+c.lower,98296899971411+c.upper)) = pointBounds17515 := by
 decide +kernel
def cuts17516 : List PrefixCut := [⟨20,115169986,115170058⟩,
⟨91,521989611,521989937⟩,
⟨128,739346516,739346973⟩]
theorem checked17516 : checkPrefixCuts (2^48) 2299789313 9 Manual.Count131072.C017516.packed 128 cuts17516 = true := by
 decide +kernel
def pointBounds17516 : List (Nat × Nat × Nat) := [(2299809792,98297385723809,98297765056489),(2299882496,98297792543434,98298171876368)]
theorem point_links_checked17516 : (cuts17516.take 2).map (fun c => (2299789313-1+2*2^9*c.k,98297270553823+c.lower,98297649886431+c.upper)) = pointBounds17516 := by
 decide +kernel
def cuts17517 : List PrefixCut := [⟨34,199118307,199118429⟩,
⟨105,610195492,610195862⟩,
⟨128,745423484,745423938⟩]
theorem checked17517 : checkPrefixCuts (2^48) 2299920385 9 Manual.Count131072.C017517.packed 128 cuts17517 = true := by
 decide +kernel
def pointBounds17517 : List (Nat × Nat × Nat) := [(2299955200,98298209018646,98298588351833),(2300027904,98298620095831,98298999429266)]
theorem point_links_checked17517 : (cuts17517.take 2).map (fun c => (2299920385-1+2*2^9*c.k,98298009900339+c.lower,98298389233404+c.upper)) = pointBounds17517 := by
 decide +kernel
def cuts17518 : List PrefixCut := [⟨48,280241810,280241984⟩,
⟨119,688233697,688234128⟩,
⟨128,739751856,739752318⟩]
theorem checked17518 : checkPrefixCuts (2^48) 2300051457 9 Manual.Count131072.C017518.packed 128 cuts17518 = true := by
 decide +kernel
def pointBounds17518 : List (Nat × Nat × Nat) := [(2300100608,98299035565633,98299414899326),(2300173312,98299443557520,98299822891470)]
theorem point_links_checked17518 : (cuts17518.take 2).map (fun c => (2300051457-1+2*2^9*c.k,98298755323823+c.lower,98299134657342+c.upper)) = pointBounds17518 := by
 decide +kernel
def cuts17519 : List PrefixCut := [⟨62,357684568,357684795⟩,
⟨128,749498948,749499418⟩]
theorem checked17519 : checkPrefixCuts (2^48) 2300182529 9 Manual.Count131072.C017519.packed 128 cuts17519 = true := by
 decide +kernel
def pointBounds17519 : List (Nat × Nat × Nat) := [(2300246016,98299852760247,98300232094455)]
theorem point_links_checked17519 : (cuts17519.take 1).map (fun c => (2300182529-1+2*2^9*c.k,98299495075679+c.lower,98299874409660+c.upper)) = pointBounds17519 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000234
