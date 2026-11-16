import PlattAssemblyKernel
import PlattCertificates.Count131072.C015472
import PlattCertificates.Count131072.C015473
import PlattCertificates.Count131072.C015474
import PlattCertificates.Count131072.C015475
import PlattCertificates.Count131072.C015476
import PlattCertificates.Count131072.C015477
import PlattCertificates.Count131072.C015478
import PlattCertificates.Count131072.C015479
import PlattCertificates.Count131072.C015480
import PlattCertificates.Count131072.C015481
import PlattCertificates.Count131072.C015482
import PlattCertificates.Count131072.C015483
import PlattCertificates.Count131072.C015484
import PlattCertificates.Count131072.C015485
import PlattCertificates.Count131072.C015486
import PlattCertificates.Count131072.C015487
import PlattCertificates.Count131072.C015488
import PlattCertificates.Count131072.C015489
import PlattCertificates.Count131072.C015490
import PlattCertificates.Count131072.C015491
import PlattCertificates.Count131072.C015492
import PlattCertificates.Count131072.C015493
import PlattCertificates.Count131072.C015494
import PlattCertificates.Count131072.C015495
import PlattCertificates.Count131072.C015496
import PlattCertificates.Count131072.C015497
import PlattCertificates.Count131072.C015498
import PlattCertificates.Count131072.C015499
import PlattCertificates.Count131072.C015500
import PlattCertificates.Count131072.C015501
import PlattCertificates.Count131072.C015502
import PlattCertificates.Count131072.C015503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000171
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15472 : List PrefixCut := [⟨30,198095548,198095677⟩,
⟨93,620874192,620874598⟩,
⟨128,855114416,855114974⟩]
theorem checked15472 : checkPrefixCuts (2^48) 2031878145 9 Manual.Count131072.C015472.packed 128 cuts15472 = true := by
 decide +kernel
def pointBounds15472 : List (Nat × Nat × Nat) := [(2031908864,96675417304591,96675795607168),(2031973376,96675840083235,96676218386089)]
theorem point_links_checked15472 : (cuts15472.take 2).map (fun c => (2031878145-1+2*2^9*c.k,96675219209043+c.lower,96675597511491+c.upper)) = pointBounds15472 := by
 decide +kernel
def cuts15473 : List PrefixCut := [⟨28,183261300,183261420⟩,
⟨91,591191950,591192337⟩,
⟨128,835528579,835529121⟩]
theorem checked15473 : checkPrefixCuts (2^48) 2032009217 9 Manual.Count131072.C015473.packed 128 cuts15473 = true := by
 decide +kernel
def pointBounds15473 : List (Nat × Nat × Nat) := [(2032037888,96676257584759,96676635887885),(2032102400,96676665515409,96677043818802)]
theorem point_links_checked15473 : (cuts15473.take 2).map (fun c => (2032009217-1+2*2^9*c.k,96676074323459+c.lower,96676452626465+c.upper)) = pointBounds15473 := by
 decide +kernel
def cuts15474 : List PrefixCut := [⟨26,175908506,175908622⟩,
⟨89,597248509,597248897⟩,
⟨128,854034878,854035434⟩]
theorem checked15474 : checkPrefixCuts (2^48) 2032140289 9 Manual.Count131072.C015474.packed 128 cuts15474 = true := by
 decide +kernel
def pointBounds15474 : List (Nat × Nat × Nat) := [(2032166912,96677085760544,96677464064208),(2032231424,96677507100547,96677885404483)]
theorem point_links_checked15474 : (cuts15474.take 2).map (fun c => (2032140289-1+2*2^9*c.k,96676909852038+c.lower,96677288155586+c.upper)) = pointBounds15474 := by
 decide +kernel
def cuts15475 : List PrefixCut := [⟨24,158723026,158723130⟩,
⟨87,579066713,579067090⟩,
⟨128,847747190,847747742⟩]
theorem checked15475 : checkPrefixCuts (2^48) 2032271361 9 Manual.Count131072.C015475.packed 128 cuts15475 = true := by
 decide +kernel
def pointBounds15475 : List (Nat × Nat × Nat) := [(2032295936,96677922609942,96678300914150),(2032360448,96678342953629,96678721258110)]
theorem point_links_checked15475 : (cuts15475.take 2).map (fun c => (2032271361-1+2*2^9*c.k,96677763886916+c.lower,96678142191020+c.upper)) = pointBounds15475 := by
 decide +kernel
def cuts15476 : List PrefixCut := [⟨22,144032645,144032742⟩,
⟨85,570858694,570859075⟩,
⟨128,859187052,859187621⟩]
theorem checked15476 : checkPrefixCuts (2^48) 2032402433 9 Manual.Count131072.C015476.packed 128 cuts15476 = true := by
 decide +kernel
def pointBounds15476 : List (Nat × Nat × Nat) := [(2032424960,96678755666751,96679133971504),(2032489472,96679182492800,96679560797837)]
theorem point_links_checked15476 : (cuts15476.take 2).map (fun c => (2032402433-1+2*2^9*c.k,96678611634106+c.lower,96678989938762+c.upper)) = pointBounds15476 := by
 decide +kernel
def cuts15477 : List PrefixCut := [⟨20,130313488,130313571⟩,
⟨83,539109863,539110218⟩,
⟨128,841544520,841545073⟩]
theorem checked15477 : checkPrefixCuts (2^48) 2032533505 9 Manual.Count131072.C015477.packed 128 cuts15477 = true := by
 decide +kernel
def pointBounds15477 : List (Nat × Nat × Nat) := [(2032553984,96679601134646,96679979439954),(2032618496,96680009931021,96680388236601)]
theorem point_links_checked15477 : (cuts15477.take 2).map (fun c => (2032533505-1+2*2^9*c.k,96679470821158+c.lower,96679849126383+c.upper)) = pointBounds15477 := by
 decide +kernel
def cuts15478 : List PrefixCut := [⟨18,118534741,118534818⟩,
⟨81,542121711,542122061⟩,
⟨128,851044986,851045543⟩]
theorem checked15478 : checkPrefixCuts (2^48) 2032664577 9 Manual.Count131072.C015478.packed 128 cuts15478 = true := by
 decide +kernel
def pointBounds15478 : List (Nat × Nat × Nat) := [(2032683008,96680430900419,96680809206274),(2032747520,96680854487389,96681232793517)]
theorem point_links_checked15478 : (cuts15478.take 2).map (fun c => (2032664577-1+2*2^9*c.k,96680312365678+c.lower,96680690671456+c.upper)) = pointBounds15478 := by
 decide +kernel
def cuts15479 : List PrefixCut := [⟨16,102880488,102880556⟩,
⟨79,517855719,517856056⟩,
⟨128,840328280,840328828⟩]
theorem checked15479 : checkPrefixCuts (2^48) 2032795649 9 Manual.Count131072.C015479.packed 128 cuts15479 = true := by
 decide +kernel
def pointBounds15479 : List (Nat × Nat × Nat) := [(2032812032,96681266291152,96681644597555),(2032876544,96681681266383,96682059573055)]
theorem point_links_checked15479 : (cuts15479.take 2).map (fun c => (2032795649-1+2*2^9*c.k,96681163410664+c.lower,96681541716999+c.upper)) = pointBounds15479 := by
 decide +kernel
def cuts15480 : List PrefixCut := [⟨14,92628055,92628118⟩,
⟨77,504531085,504531419⟩,
⟨128,846919922,846920483⟩]
theorem checked15480 : checkPrefixCuts (2^48) 2032926721 9 Manual.Count131072.C015480.packed 128 cuts15480 = true := by
 decide +kernel
def pointBounds15480 : List (Nat × Nat × Nat) := [(2032941056,96682096366999,96682474673945),(2033005568,96682508270029,96682886577246)]
theorem point_links_checked15480 : (cuts15480.take 2).map (fun c => (2032926721-1+2*2^9*c.k,96682003738944+c.lower,96682382045827+c.upper)) = pointBounds15480 := by
 decide +kernel
def cuts15481 : List PrefixCut := [⟨12,77946570,77946619⟩,
⟨75,493422984,493423305⟩,
⟨128,844096519,844097067⟩]
theorem checked15481 : checkPrefixCuts (2^48) 2033057793 9 Manual.Count131072.C015481.packed 128 cuts15481 = true := by
 decide +kernel
def pointBounds15481 : List (Nat × Nat × Nat) := [(2033070080,96682928605436,96683306912929),(2033134592,96683344081850,96683722389615)]
theorem point_links_checked15481 : (cuts15481.take 2).map (fun c => (2033057793-1+2*2^9*c.k,96682850658866+c.lower,96683228966310+c.upper)) = pointBounds15481 := by
 decide +kernel
def cuts15482 : List PrefixCut := [⟨10,66451083,66451130⟩,
⟨73,476086850,476087169⟩,
⟨128,839889022,839889579⟩]
theorem checked15482 : checkPrefixCuts (2^48) 2033188865 9 Manual.Count131072.C015482.packed 128 cuts15482 = true := by
 decide +kernel
def pointBounds15482 : List (Nat × Nat × Nat) := [(2033199104,96683761206468,96684139514507),(2033263616,96684170842235,96684549150546)]
theorem point_links_checked15482 : (cuts15482.take 2).map (fun c => (2033188865-1+2*2^9*c.k,96683694755385+c.lower,96684073063377+c.upper)) = pointBounds15482 := by
 decide +kernel
def cuts15483 : List PrefixCut := [⟨8,53157467,53157502⟩,
⟨71,471626596,471626902⟩,
⟨128,850493804,850494357⟩]
theorem checked15483 : checkPrefixCuts (2^48) 2033319937 9 Manual.Count131072.C015483.packed 128 cuts15483 = true := by
 decide +kernel
def pointBounds15483 : List (Nat × Nat × Nat) := [(2033328128,96684587801874,96684966110458),(2033392640,96685006271003,96685384579858)]
theorem point_links_checked15483 : (cuts15483.take 2).map (fun c => (2033319937-1+2*2^9*c.k,96684534644407+c.lower,96684912952956+c.upper)) = pointBounds15483 := by
 decide +kernel
def cuts15484 : List PrefixCut := [⟨6,39588709,39588734⟩,
⟨69,452909816,452910111⟩,
⟨128,851407761,851408315⟩]
theorem checked15484 : checkPrefixCuts (2^48) 2033451009 9 Manual.Count131072.C015484.packed 128 cuts15484 = true := by
 decide +kernel
def pointBounds15484 : List (Nat × Nat × Nat) := [(2033457152,96685424726920,96685803036047),(2033521664,96685838048027,96686216357424)]
theorem point_links_checked15484 : (cuts15484.take 2).map (fun c => (2033451009-1+2*2^9*c.k,96685385138211+c.lower,96685763447313+c.upper)) = pointBounds15484 := by
 decide +kernel
def cuts15485 : List PrefixCut := [⟨4,28651532,28651551⟩,
⟨67,443745790,443746083⟩,
⟨128,847200897,847201455⟩]
theorem checked15485 : checkPrefixCuts (2^48) 2033582081 9 Manual.Count131072.C015485.packed 128 cuts15485 = true := by
 decide +kernel
def pointBounds15485 : List (Nat × Nat × Nat) := [(2033586176,96686265197504,96686643507179),(2033650688,96686680291762,96687058601711)]
theorem point_links_checked15485 : (cuts15485.take 2).map (fun c => (2033582081-1+2*2^9*c.k,96686236545972+c.lower,96686614855628+c.upper)) = pointBounds15485 := by
 decide +kernel
def cuts15486 : List PrefixCut := [⟨2,13148412,13148421⟩,
⟨65,432368381,432368670⟩,
⟨128,847284640,847285205⟩]
theorem checked15486 : checkPrefixCuts (2^48) 2033713153 9 Manual.Count131072.C015486.packed 128 cuts15486 = true := by
 decide +kernel
def pointBounds15486 : List (Nat × Nat × Nat) := [(2033715200,96687096895281,96687475205504),(2033779712,96687516115250,96687894425753),(2033844224,96687931031509,96688309342288)]
theorem point_links_checked15486 : (cuts15486.take 3).map (fun c => (2033713153-1+2*2^9*c.k,96687083746869+c.lower,96687462057083+c.upper)) = pointBounds15486 := by
 decide +kernel
def cuts15487 : List PrefixCut := [⟨63,415733517,415733781⟩,
⟨126,838096527,838097071⟩,
⟨128,850828098,850828651⟩]
theorem checked15487 : checkPrefixCuts (2^48) 2033844225 9 Manual.Count131072.C015487.packed 128 cuts15487 = true := by
 decide +kernel
def pointBounds15487 : List (Nat × Nat × Nat) := [(2033908736,96688346765026,96688725076069),(2033973248,96688769128036,96689147439359)]
theorem point_links_checked15487 : (cuts15487.take 2).map (fun c => (2033844225-1+2*2^9*c.k,96687931031509+c.lower,96688309342288+c.upper)) = pointBounds15487 := by
 decide +kernel
def cuts15488 : List PrefixCut := [⟨61,409202900,409203166⟩,
⟨124,827249227,827249762⟩,
⟨128,852710743,852711295⟩]
theorem checked15488 : checkPrefixCuts (2^48) 2033975297 9 Manual.Count131072.C015488.packed 128 cuts15488 = true := by
 decide +kernel
def pointBounds15488 : List (Nat × Nat × Nat) := [(2034037760,96689191062507,96689569374105),(2034102272,96689609108834,96689987420701)]
theorem point_links_checked15488 : (cuts15488.take 2).map (fun c => (2033975297-1+2*2^9*c.k,96688781859607+c.lower,96689160170939+c.upper)) = pointBounds15488 := by
 decide +kernel
def cuts15489 : List PrefixCut := [⟨59,394785680,394785941⟩,
⟨122,817925335,817925870⟩,
⟨128,856668642,856669203⟩]
theorem checked15489 : checkPrefixCuts (2^48) 2034106369 9 Manual.Count131072.C015489.packed 128 cuts15489 = true := by
 decide +kernel
def pointBounds15489 : List (Nat × Nat × Nat) := [(2034166784,96690029356030,96690407668175),(2034231296,96690452495685,96690830808104)]
theorem point_links_checked15489 : (cuts15489.take 2).map (fun c => (2034106369-1+2*2^9*c.k,96689634570350+c.lower,96690012882234+c.upper)) = pointBounds15489 := by
 decide +kernel
def cuts15490 : List PrefixCut := [⟨57,381338673,381338922⟩,
⟨120,797118284,797118806⟩,
⟨128,851908888,851909445⟩]
theorem checked15490 : checkPrefixCuts (2^48) 2034237441 9 Manual.Count131072.C015490.packed 128 cuts15490 = true := by
 decide +kernel
def pointBounds15490 : List (Nat × Nat × Nat) := [(2034295808,96690872577665,96691250890359),(2034360320,96691288357276,96691666670243)]
theorem point_links_checked15490 : (cuts15490.take 2).map (fun c => (2034237441-1+2*2^9*c.k,96690491238992+c.lower,96690869551437+c.upper)) = pointBounds15490 := by
 decide +kernel
def cuts15491 : List PrefixCut := [⟨55,369000549,369000787⟩,
⟨118,784892081,784892588⟩,
⟨128,851715742,851716292⟩]
theorem checked15491 : checkPrefixCuts (2^48) 2034368513 9 Manual.Count131072.C015491.packed 128 cuts15491 = true := by
 decide +kernel
def pointBounds15491 : List (Nat × Nat × Nat) := [(2034424832,96691712148429,96692090461669),(2034489344,96692128039961,96692506353470)]
theorem point_links_checked15491 : (cuts15491.take 2).map (fun c => (2034368513-1+2*2^9*c.k,96691343147880+c.lower,96691721460882+c.upper)) = pointBounds15491 := by
 decide +kernel
def cuts15492 : List PrefixCut := [⟨53,352790162,352790393⟩,
⟨116,771145542,771146049⟩,
⟨128,854151000,854151560⟩]
theorem checked15492 : checkPrefixCuts (2^48) 2034499585 9 Manual.Count131072.C015492.packed 128 cuts15492 = true := by
 decide +kernel
def pointBounds15492 : List (Nat × Nat × Nat) := [(2034553856,96692547653784,96692925967567),(2034618368,96692966009164,96693344323223)]
theorem point_links_checked15492 : (cuts15492.take 2).map (fun c => (2034499585-1+2*2^9*c.k,96692194863622+c.lower,96692573177174+c.upper)) = pointBounds15492 := by
 decide +kernel
def cuts15493 : List PrefixCut := [⟨51,329803148,329803369⟩,
⟨114,742460228,742460719⟩,
⟨128,834175390,834175942⟩]
theorem checked15493 : checkPrefixCuts (2^48) 2034630657 9 Manual.Count131072.C015493.packed 128 cuts15493 = true := by
 decide +kernel
def pointBounds15493 : List (Nat × Nat × Nat) := [(2034682880,96693378817770,96693757132103),(2034747392,96693791474850,96694169789453)]
theorem point_links_checked15493 : (cuts15493.take 2).map (fun c => (2034630657-1+2*2^9*c.k,96693049014622+c.lower,96693427328734+c.upper)) = pointBounds15493 := by
 decide +kernel
def cuts15494 : List PrefixCut := [⟨49,333517042,333517262⟩,
⟨112,748637831,748638318⟩,
⟨128,856669458,856670015⟩]
theorem checked15494 : checkPrefixCuts (2^48) 2034761729 9 Manual.Count131072.C015494.packed 128 cuts15494 = true := by
 decide +kernel
def pointBounds15494 : List (Nat × Nat × Nat) := [(2034811904,96694216707054,96694595021938),(2034876416,96694631827843,96695010142994)]
theorem point_links_checked15494 : (cuts15494.take 2).map (fun c => (2034761729-1+2*2^9*c.k,96693883190012+c.lower,96694261504676+c.upper)) = pointBounds15494 := by
 decide +kernel
def cuts15495 : List PrefixCut := [⟨47,303341318,303341519⟩,
⟨110,726873213,726873685⟩,
⟨128,842366993,842367542⟩]
theorem checked15495 : checkPrefixCuts (2^48) 2034892801 9 Manual.Count131072.C015495.packed 128 cuts15495 = true := by
 decide +kernel
def pointBounds15495 : List (Nat × Nat × Nat) := [(2034940928,96695043200788,96695421516210),(2035005440,96695466732683,96695845048376)]
theorem point_links_checked15495 : (cuts15495.take 2).map (fun c => (2034892801-1+2*2^9*c.k,96694739859470+c.lower,96695118174691+c.upper)) = pointBounds15495 := by
 decide +kernel
def cuts15496 : List PrefixCut := [⟨45,291980266,291980458⟩,
⟨108,715761979,715762444⟩,
⟨128,841483096,841483643⟩]
theorem checked15496 : checkPrefixCuts (2^48) 2035023873 9 Manual.Count131072.C015496.packed 128 cuts15496 = true := by
 decide +kernel
def pointBounds15496 : List (Nat × Nat × Nat) := [(2035069952,96695874206729,96696252522691),(2035134464,96696297988442,96696676304677)]
theorem point_links_checked15496 : (cuts15496.take 2).map (fun c => (2035023873-1+2*2^9*c.k,96695582226463+c.lower,96695960542233+c.upper)) = pointBounds15496 := by
 decide +kernel
def cuts15497 : List PrefixCut := [⟨43,278131073,278131255⟩,
⟨106,695524049,695524505⟩,
⟨128,837556321,837556871⟩]
theorem checked15497 : checkPrefixCuts (2^48) 2035154945 9 Manual.Count131072.C015497.packed 128 cuts15497 = true := by
 decide +kernel
def pointBounds15497 : List (Nat × Nat × Nat) := [(2035198976,96696701840632,96697080157131),(2035263488,96697119233608,96697497550381)]
theorem point_links_checked15497 : (cuts15497.take 2).map (fun c => (2035154945-1+2*2^9*c.k,96696423709559+c.lower,96696802025876+c.upper)) = pointBounds15497 := by
 decide +kernel
def cuts15498 : List PrefixCut := [⟨41,277421848,277422030⟩,
⟨104,689533281,689533732⟩,
⟨128,843587654,843588207⟩]
theorem checked15498 : checkPrefixCuts (2^48) 2035286017 9 Manual.Count131072.C015498.packed 128 cuts15498 = true := by
 decide +kernel
def pointBounds15498 : List (Nat × Nat × Nat) := [(2035328000,96697538687728,96697917004777),(2035392512,96697950799161,96698329116479)]
theorem point_links_checked15498 : (cuts15498.take 2).map (fun c => (2035286017-1+2*2^9*c.k,96697261265880+c.lower,96697639582747+c.upper)) = pointBounds15498 := by
 decide +kernel
def cuts15499 : List PrefixCut := [⟨39,251406145,251406311⟩,
⟨102,669022752,669023196⟩,
⟨128,843671075,843671632⟩]
theorem checked15499 : checkPrefixCuts (2^48) 2035417089 9 Manual.Count131072.C015499.packed 128 cuts15499 = true := by
 decide +kernel
def pointBounds15499 : List (Nat × Nat × Nat) := [(2035457024,96698356259679,96698734577265),(2035521536,96698773876286,96699152194150)]
theorem point_links_checked15499 : (cuts15499.take 2).map (fun c => (2035417089-1+2*2^9*c.k,96698104853534+c.lower,96698483170954+c.upper)) = pointBounds15499 := by
 decide +kernel
def cuts15500 : List PrefixCut := [⟨37,242401962,242402120⟩,
⟨100,657088358,657088789⟩,
⟨128,846797122,846797676⟩]
theorem checked15500 : checkPrefixCuts (2^48) 2035548161 9 Manual.Count131072.C015500.packed 128 cuts15500 = true := by
 decide +kernel
def pointBounds15500 : List (Nat × Nat × Nat) := [(2035586048,96699190926571,96699569244706),(2035650560,96699605612967,96699983931375)]
theorem point_links_checked15500 : (cuts15500.take 2).map (fun c => (2035548161-1+2*2^9*c.k,96698948524609+c.lower,96699326842586+c.upper)) = pointBounds15500 := by
 decide +kernel
def cuts15501 : List PrefixCut := [⟨35,234643385,234643542⟩,
⟨98,649994822,649995255⟩,
⟨128,848678585,848679148⟩]
theorem checked15501 : checkPrefixCuts (2^48) 2035679233 9 Manual.Count131072.C015501.packed 128 cuts15501 = true := by
 decide +kernel
def pointBounds15501 : List (Nat × Nat × Nat) := [(2035715072,96700029965116,96700408283804),(2035779584,96700445316553,96700823635517)]
theorem point_links_checked15501 : (cuts15501.take 2).map (fun c => (2035679233-1+2*2^9*c.k,96699795321731+c.lower,96700173640262+c.upper)) = pointBounds15501 := by
 decide +kernel
def cuts15502 : List PrefixCut := [⟨33,217207565,217207709⟩,
⟨96,623407731,623408141⟩,
⟨128,834245178,834245724⟩]
theorem checked15502 : checkPrefixCuts (2^48) 2035810305 9 Manual.Count131072.C015502.packed 128 cuts15502 = true := by
 decide +kernel
def pointBounds15502 : List (Nat × Nat × Nat) := [(2035844096,96700861207881,96701239527119),(2035908608,96701267408047,96701645727551)]
theorem point_links_checked15502 : (cuts15502.take 2).map (fun c => (2035810305-1+2*2^9*c.k,96700644000316+c.lower,96701022319410+c.upper)) = pointBounds15502 := by
 decide +kernel
def cuts15503 : List PrefixCut := [⟨31,204197997,204198132⟩,
⟨94,622676487,622676902⟩,
⟨128,847324950,847325512⟩]
theorem checked15503 : checkPrefixCuts (2^48) 2035941377 9 Manual.Count131072.C015503.packed 128 cuts15503 = true := by
 decide +kernel
def pointBounds15503 : List (Nat × Nat × Nat) := [(2035973120,96701682443491,96702060763266),(2036037632,96702100921981,96702479242036)]
theorem point_links_checked15503 : (cuts15503.take 2).map (fun c => (2035941377-1+2*2^9*c.k,96701478245494+c.lower,96701856565134+c.upper)) = pointBounds15503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000171
