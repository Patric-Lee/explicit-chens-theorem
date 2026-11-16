import PlattAssemblyKernel
import PlattCertificates.Count131072.C015376
import PlattCertificates.Count131072.C015377
import PlattCertificates.Count131072.C015378
import PlattCertificates.Count131072.C015379
import PlattCertificates.Count131072.C015380
import PlattCertificates.Count131072.C015381
import PlattCertificates.Count131072.C015382
import PlattCertificates.Count131072.C015383
import PlattCertificates.Count131072.C015384
import PlattCertificates.Count131072.C015385
import PlattCertificates.Count131072.C015386
import PlattCertificates.Count131072.C015387
import PlattCertificates.Count131072.C015388
import PlattCertificates.Count131072.C015389
import PlattCertificates.Count131072.C015390
import PlattCertificates.Count131072.C015391
import PlattCertificates.Count131072.C015392
import PlattCertificates.Count131072.C015393
import PlattCertificates.Count131072.C015394
import PlattCertificates.Count131072.C015395
import PlattCertificates.Count131072.C015396
import PlattCertificates.Count131072.C015397
import PlattCertificates.Count131072.C015398
import PlattCertificates.Count131072.C015399
import PlattCertificates.Count131072.C015400
import PlattCertificates.Count131072.C015401
import PlattCertificates.Count131072.C015402
import PlattCertificates.Count131072.C015403
import PlattCertificates.Count131072.C015404
import PlattCertificates.Count131072.C015405
import PlattCertificates.Count131072.C015406
import PlattCertificates.Count131072.C015407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000168
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15376 : List PrefixCut := [⟨38,255504252,255504423⟩,
⟨100,660146989,660147424⟩,
⟨128,843298315,843298871⟩]
theorem checked15376 : checkPrefixCuts (2^48) 2019295233 9 Manual.Count131072.C015376.packed 128 cuts15376 = true := by
 decide +kernel
def pointBounds15376 : List (Nat × Nat × Nat) := [(2019334144,96593950710352,96594328959483),(2019397632,96594355353089,96594733602484)]
theorem point_links_checked15376 : (cuts15376.take 2).map (fun c => (2019295233-1+2*2^9*c.k,96593695206100+c.lower,96594073455060+c.upper)) = pointBounds15376 := by
 decide +kernel
def cuts15377 : List PrefixCut := [⟨34,222036122,222036268⟩,
⟨96,645051411,645051837⟩,
⟨128,854951184,854951747⟩]
theorem checked15377 : checkPrefixCuts (2^48) 2019426305 9 Manual.Count131072.C015377.packed 128 cuts15377 = true := by
 decide +kernel
def pointBounds15377 : List (Nat × Nat × Nat) := [(2019461120,96594760540537,96595138790199),(2019524608,96595183555826,96595561805768)]
theorem point_links_checked15377 : (cuts15377.take 2).map (fun c => (2019426305-1+2*2^9*c.k,96594538504415+c.lower,96594916753931+c.upper)) = pointBounds15377 := by
 decide +kernel
def cuts15378 : List PrefixCut := [⟨30,201394660,201394795⟩,
⟨92,614766784,614767195⟩,
⟨128,854616968,854617532⟩]
theorem checked15378 : checkPrefixCuts (2^48) 2019557377 9 Manual.Count131072.C015378.packed 128 cuts15378 = true := by
 decide +kernel
def pointBounds15378 : List (Nat × Nat × Nat) := [(2019588096,96595594850259,96595973100473),(2019651584,96596008222383,96596386472873)]
theorem point_links_checked15378 : (cuts15378.take 2).map (fun c => (2019557377-1+2*2^9*c.k,96595393455599+c.lower,96595771705678+c.upper)) = pointBounds15378 := by
 decide +kernel
def cuts15379 : List PrefixCut := [⟨26,176296196,176296310⟩,
⟨88,584764645,584765021⟩,
⟨128,855258261,855258812⟩]
theorem checked15379 : checkPrefixCuts (2^48) 2019688449 9 Manual.Count131072.C015379.packed 128 cuts15379 = true := by
 decide +kernel
def pointBounds15379 : List (Nat × Nat × Nat) := [(2019715072,96596424368763,96596802619520),(2019778560,96596832837212,96597211088231)]
theorem point_links_checked15379 : (cuts15379.take 2).map (fun c => (2019688449-1+2*2^9*c.k,96596248072567+c.lower,96596626323210+c.upper)) = pointBounds15379 := by
 decide +kernel
def cuts15380 : List PrefixCut := [⟨22,144790542,144790634⟩,
⟨84,550446240,550446603⟩,
⟨128,847956279,847956839⟩]
theorem checked15380 : checkPrefixCuts (2^48) 2019819521 9 Manual.Count131072.C015380.packed 128 cuts15380 = true := by
 decide +kernel
def pointBounds15380 : List (Nat × Nat × Nat) := [(2019842048,96597248121370,96597626372656),(2019905536,96597653777068,96598032028625)]
theorem point_links_checked15380 : (cuts15380.take 2).map (fun c => (2019819521-1+2*2^9*c.k,96597103330828+c.lower,96597481582022+c.upper)) = pointBounds15380 := by
 decide +kernel
def cuts15381 : List PrefixCut := [⟨18,118166059,118166136⟩,
⟨80,529230684,529231026⟩,
⟨128,853753739,853754296⟩]
theorem checked15381 : checkPrefixCuts (2^48) 2019950593 9 Manual.Count131072.C015381.packed 128 cuts15381 = true := by
 decide +kernel
def pointBounds15381 : List (Nat × Nat × Nat) := [(2019969024,96598069453166,96598447704997),(2020032512,96598480517791,96598858769887)]
theorem point_links_checked15381 : (cuts15381.take 2).map (fun c => (2019950593-1+2*2^9*c.k,96597951287107+c.lower,96598329538861+c.upper)) = pointBounds15381 := by
 decide +kernel
def cuts15382 : List PrefixCut := [⟨14,90987630,90987690⟩,
⟨76,499100340,499100664⟩,
⟨128,853280223,853280779⟩]
theorem checked15382 : checkPrefixCuts (2^48) 2020081665 9 Manual.Count131072.C015382.packed 128 cuts15382 = true := by
 decide +kernel
def pointBounds15382 : List (Nat × Nat × Nat) := [(2020096000,96598896028476,96599274280847),(2020159488,96599304141186,96599682393821)]
theorem point_links_checked15382 : (cuts15382.take 2).map (fun c => (2020081665-1+2*2^9*c.k,96598805040846+c.lower,96599183293157+c.upper)) = pointBounds15382 := by
 decide +kernel
def cuts15383 : List PrefixCut := [⟨10,66459922,66459967⟩,
⟨72,471899791,471900103⟩,
⟨128,843611619,843612176⟩]
theorem checked15383 : checkPrefixCuts (2^48) 2020212737 9 Manual.Count131072.C015383.packed 128 cuts15383 = true := by
 decide +kernel
def pointBounds15383 : List (Nat × Nat × Nat) := [(2020222976,96599724780991,96600103033903),(2020286464,96600130220860,96600508474039)]
theorem point_links_checked15383 : (cuts15383.take 2).map (fun c => (2020212737-1+2*2^9*c.k,96599658321069+c.lower,96600036573936+c.upper)) = pointBounds15383 := by
 decide +kernel
def cuts15384 : List PrefixCut := [⟨6,40681463,40681490⟩,
⟨68,460445538,460445839⟩,
⟨128,861528788,861529348⟩]
theorem checked15384 : checkPrefixCuts (2^48) 2020343809 9 Manual.Count131072.C015384.packed 128 cuts15384 = true := by
 decide +kernel
def pointBounds15384 : List (Nat × Nat × Nat) := [(2020349952,96600542614151,96600920867602),(2020413440,96600962378226,96601340631951)]
theorem point_links_checked15384 : (cuts15384.take 2).map (fun c => (2020343809-1+2*2^9*c.k,96600501932688+c.lower,96600880186112+c.upper)) = pointBounds15384 := by
 decide +kernel
def cuts15385 : List PrefixCut := [⟨2,13652495,13652505⟩,
⟨64,426285462,426285744⟩,
⟨126,834169209,834169755⟩,
⟨128,848935252,848935806⟩]
theorem checked15385 : checkPrefixCuts (2^48) 2020474881 9 Manual.Count131072.C015385.packed 128 cuts15385 = true := by
 decide +kernel
def pointBounds15385 : List (Nat × Nat × Nat) := [(2020476928,96601377113971,96601755367965),(2020540416,96601789746938,96602168001204),(2020603904,96602197630685,96602575885215)]
theorem point_links_checked15385 : (cuts15385.take 3).map (fun c => (2020474881-1+2*2^9*c.k,96601363461476+c.lower,96601741715460+c.upper)) = pointBounds15385 := by
 decide +kernel
def cuts15386 : List PrefixCut := [⟨60,394637083,394637343⟩,
⟨122,811828062,811828594⟩,
⟨128,848462223,848462778⟩]
theorem checked15386 : checkPrefixCuts (2^48) 2020605953 9 Manual.Count131072.C015386.packed 128 cuts15386 = true := by
 decide +kernel
def pointBounds15386 : List (Nat × Nat × Nat) := [(2020667392,96602607033811,96602985288609),(2020730880,96603024224790,96603402479860)]
theorem point_links_checked15386 : (cuts15386.take 2).map (fun c => (2020605953-1+2*2^9*c.k,96602212396728+c.lower,96602590651266+c.upper)) = pointBounds15386 := by
 decide +kernel
def cuts15387 : List PrefixCut := [⟨56,375668422,375668673⟩,
⟨118,791022419,791022941⟩,
⟨128,855093287,855093849⟩]
theorem checked15387 : checkPrefixCuts (2^48) 2020737025 9 Manual.Count131072.C015387.packed 128 cuts15387 = true := by
 decide +kernel
def pointBounds15387 : List (Nat × Nat × Nat) := [(2020794368,96603436527373,96603814782717),(2020857856,96603851881370,96604230136985)]
theorem point_links_checked15387 : (cuts15387.take 2).map (fun c => (2020737025-1+2*2^9*c.k,96603060858951+c.lower,96603439114044+c.upper)) = pointBounds15387 := by
 decide +kernel
def cuts15388 : List PrefixCut := [⟨52,336227517,336227738⟩,
⟨114,751973135,751973632⟩,
⟨128,844591423,844591982⟩]
theorem checked15388 : checkPrefixCuts (2^48) 2020868097 9 Manual.Count131072.C015388.packed 128 cuts15388 = true := by
 decide +kernel
def pointBounds15388 : List (Nat × Nat × Nat) := [(2020921344,96604252179755,96604630435631),(2020984832,96604667925373,96605046181525)]
theorem point_links_checked15388 : (cuts15388.take 2).map (fun c => (2020868097-1+2*2^9*c.k,96603915952238+c.lower,96604294207893+c.upper)) = pointBounds15388 := by
 decide +kernel
def cuts15389 : List PrefixCut := [⟨48,321582351,321582563⟩,
⟨110,731731159,731731644⟩,
⟨128,853032467,853033030⟩]
theorem checked15389 : checkPrefixCuts (2^48) 2020999169 9 Manual.Count131072.C015389.packed 128 cuts15389 = true := by
 decide +kernel
def pointBounds15389 : List (Nat × Nat × Nat) := [(2021048320,96605082126012,96605460382438),(2021111808,96605492274820,96605870531519)]
theorem point_links_checked15389 : (cuts15389.take 2).map (fun c => (2020999169-1+2*2^9*c.k,96604760543661+c.lower,96605138799875+c.upper)) = pointBounds15389 := by
 decide +kernel
def cuts15390 : List PrefixCut := [⟨44,291062813,291063006⟩,
⟨106,706756198,706756668⟩,
⟨128,846849587,846850153⟩]
theorem checked15390 : checkPrefixCuts (2^48) 2021130241 9 Manual.Count131072.C015390.packed 128 cuts15390 = true := by
 decide +kernel
def pointBounds15390 : List (Nat × Nat × Nat) := [(2021175296,96605904638941,96606282895911),(2021238784,96606320332326,96606698589573)]
theorem point_links_checked15390 : (cuts15390.take 2).map (fun c => (2021130241-1+2*2^9*c.k,96605613576128+c.lower,96605991832905+c.upper)) = pointBounds15390 := by
 decide +kernel
def cuts15391 : List PrefixCut := [⟨40,263889442,263889613⟩,
⟨102,678025059,678025498⟩,
⟨128,849022759,849023310⟩]
theorem checked15391 : checkPrefixCuts (2^48) 2021261313 9 Manual.Count131072.C015391.packed 128 cuts15391 = true := by
 decide +kernel
def pointBounds15391 : List (Nat × Nat × Nat) := [(2021302272,96606724315157,96607102572671),(2021365760,96607138450774,96607516708556)]
theorem point_links_checked15391 : (cuts15391.take 2).map (fun c => (2021261313-1+2*2^9*c.k,96606460425715+c.lower,96606838683058+c.upper)) = pointBounds15391 := by
 decide +kernel
def cuts15392 : List PrefixCut := [⟨36,236441014,236441173⟩,
⟨98,649854314,649854739⟩,
⟨128,853423273,853423829⟩]
theorem checked15392 : checkPrefixCuts (2^48) 2021392385 9 Manual.Count131072.C015392.packed 128 cuts15392 = true := by
 decide +kernel
def pointBounds15392 : List (Nat × Nat × Nat) := [(2021429248,96607545889488,96607924147541),(2021492736,96607959302788,96608337561107)]
theorem point_links_checked15392 : (cuts15392.take 2).map (fun c => (2021392385-1+2*2^9*c.k,96607309448474+c.lower,96607687706368+c.upper)) = pointBounds15392 := by
 decide +kernel
def cuts15393 : List PrefixCut := [⟨32,215540182,215540321⟩,
⟨94,628509842,628510252⟩,
⟨128,857684337,857684894⟩]
theorem checked15393 : checkPrefixCuts (2^48) 2021523457 9 Manual.Count131072.C015393.packed 128 cuts15393 = true := by
 decide +kernel
def pointBounds15393 : List (Nat × Nat × Nat) := [(2021556224,96608378411929,96608756670518),(2021619712,96608791381589,96609169640449)]
theorem point_links_checked15393 : (cuts15393.take 2).map (fun c => (2021523457-1+2*2^9*c.k,96608162871747+c.lower,96608541130197+c.upper)) = pointBounds15393 := by
 decide +kernel
def cuts15394 : List PrefixCut := [⟨28,188655273,188655397⟩,
⟨90,601042089,601042484⟩,
⟨128,851363709,851364269⟩]
theorem checked15394 : checkPrefixCuts (2^48) 2021654529 9 Manual.Count131072.C015394.packed 128 cuts15394 = true := by
 decide +kernel
def pointBounds15394 : List (Nat × Nat × Nat) := [(2021683200,96609209211357,96609587470488),(2021746688,96609621598173,96609999857575)]
theorem point_links_checked15394 : (cuts15394.take 2).map (fun c => (2021654529-1+2*2^9*c.k,96609020556084+c.lower,96609398815091+c.upper)) = pointBounds15394 := by
 decide +kernel
def cuts15395 : List PrefixCut := [⟨24,152724451,152724550⟩,
⟨86,565363804,565364177⟩,
⟨128,839892613,839893169⟩]
theorem checked15395 : checkPrefixCuts (2^48) 2021785601 9 Manual.Count131072.C015395.packed 128 cuts15395 = true := by
 decide +kernel
def pointBounds15395 : List (Nat × Nat × Nat) := [(2021810176,96610024644244,96610402903910),(2021873664,96610437283597,96610815543537)]
theorem point_links_checked15395 : (cuts15395.take 2).map (fun c => (2021785601-1+2*2^9*c.k,96609871919793+c.lower,96610250179360+c.upper)) = pointBounds15395 := by
 decide +kernel
def cuts15396 : List PrefixCut := [⟨20,132111423,132111510⟩,
⟨82,545003300,545003655⟩,
⟨128,849721928,849722481⟩]
theorem checked15396 : checkPrefixCuts (2^48) 2021916673 9 Manual.Count131072.C015396.packed 128 cuts15396 = true := by
 decide +kernel
def pointBounds15396 : List (Nat × Nat × Nat) := [(2021937152,96610843923829,96611222184039),(2022000640,96611256815706,96611635076184)]
theorem point_links_checked15396 : (cuts15396.take 2).map (fun c => (2021916673-1+2*2^9*c.k,96610711812406+c.lower,96611090072529+c.upper)) = pointBounds15396 := by
 decide +kernel
def cuts15397 : List PrefixCut := [⟨16,101756892,101756962⟩,
⟨78,507523676,507524016⟩,
⟨128,840201266,840201820⟩]
theorem checked15397 : checkPrefixCuts (2^48) 2022047745 9 Manual.Count131072.C015397.packed 128 cuts15397 = true := by
 decide +kernel
def pointBounds15397 : List (Nat × Nat × Nat) := [(2022064128,96611663291226,96612041551972),(2022127616,96612069058010,96612447319026)]
theorem point_links_checked15397 : (cuts15397.take 2).map (fun c => (2022047745-1+2*2^9*c.k,96611561534334+c.lower,96611939795010+c.upper)) = pointBounds15397 := by
 decide +kernel
def cuts15398 : List PrefixCut := [⟨12,81149779,81149835⟩,
⟨74,493015389,493015718⟩,
⟨128,857267214,857267781⟩]
theorem checked15398 : checkPrefixCuts (2^48) 2022178817 9 Manual.Count131072.C015398.packed 128 cuts15398 = true := by
 decide +kernel
def pointBounds15398 : List (Nat × Nat × Nat) := [(2022191104,96612482885379,96612861146665),(2022254592,96612894750989,96613273012548)]
theorem point_links_checked15398 : (cuts15398.take 2).map (fun c => (2022178817-1+2*2^9*c.k,96612401735600+c.lower,96612779996830+c.upper)) = pointBounds15398 := by
 decide +kernel
def cuts15399 : List PrefixCut := [⟨8,51915843,51915877⟩,
⟨70,470714789,470715099⟩,
⟨128,853871436,853871997⟩]
theorem checked15399 : checkPrefixCuts (2^48) 2022309889 9 Manual.Count131072.C015399.packed 128 cuts15399 = true := by
 decide +kernel
def pointBounds15399 : List (Nat × Nat × Nat) := [(2022318080,96613310918657,96613689180488),(2022381568,96613729717603,96614107979710)]
theorem point_links_checked15399 : (cuts15399.take 2).map (fun c => (2022309889-1+2*2^9*c.k,96613259002814+c.lower,96613637264611+c.upper)) = pointBounds15399 := by
 decide +kernel
def cuts15400 : List PrefixCut := [⟨4,26304204,26304222⟩,
⟨66,441875837,441876127⟩,
⟨128,857434444,857435002⟩]
theorem checked15400 : checkPrefixCuts (2^48) 2022440961 9 Manual.Count131072.C015400.packed 128 cuts15400 = true := by
 decide +kernel
def pointBounds15400 : List (Nat × Nat × Nat) := [(2022445056,96614139178454,96614517440830),(2022508544,96614554750087,96614933012735),(2022572032,96614970308694,96615348571610)]
theorem point_links_checked15400 : (cuts15400.take 3).map (fun c => (2022440961-1+2*2^9*c.k,96614112874250+c.lower,96614491136608+c.upper)) = pointBounds15400 := by
 decide +kernel
def cuts15401 : List PrefixCut := [⟨62,417215557,417215833⟩,
⟨124,830382355,830382908⟩,
⟨128,855848255,855848825⟩]
theorem checked15401 : checkPrefixCuts (2^48) 2022572033 9 Manual.Count131072.C015401.packed 128 cuts15401 = true := by
 decide +kernel
def pointBounds15401 : List (Nat × Nat × Nat) := [(2022635520,96615387524251,96615765787443),(2022699008,96615800691049,96616178954518)]
theorem point_links_checked15401 : (cuts15401.take 2).map (fun c => (2022572033-1+2*2^9*c.k,96614970308694+c.lower,96615348571610+c.upper)) = pointBounds15401 := by
 decide +kernel
def cuts15402 : List PrefixCut := [⟨58,386852986,386853241⟩,
⟨120,798602313,798602837⟩,
⟨128,854818528,854819088⟩]
theorem checked15402 : checkPrefixCuts (2^48) 2022703105 9 Manual.Count131072.C015402.packed 128 cuts15402 = true := by
 decide +kernel
def pointBounds15402 : List (Nat × Nat × Nat) := [(2022762496,96616213009935,96616591273676),(2022825984,96616624759262,96617003023272)]
theorem point_links_checked15402 : (cuts15402.take 2).map (fun c => (2022703105-1+2*2^9*c.k,96615826156949+c.lower,96616204420435+c.upper)) = pointBounds15402 := by
 decide +kernel
def cuts15403 : List PrefixCut := [⟨54,357746613,357746847⟩,
⟨116,766687186,766687688⟩,
⟨128,852119255,852119814⟩]
theorem checked15403 : checkPrefixCuts (2^48) 2022834177 9 Manual.Count131072.C015403.packed 128 cuts15403 = true := by
 decide +kernel
def pointBounds15403 : List (Nat × Nat × Nat) := [(2022889472,96617038722090,96617416986370),(2022952960,96617447662663,96617825927211)]
theorem point_links_checked15403 : (cuts15403.take 2).map (fun c => (2022834177-1+2*2^9*c.k,96616680975477+c.lower,96617059239523+c.upper)) = pointBounds15403 := by
 decide +kernel
def cuts15404 : List PrefixCut := [⟨50,327809123,327809341⟩,
⟨112,741315444,741315934⟩,
⟨128,844968263,844968822⟩]
theorem checked15404 : checkPrefixCuts (2^48) 2022965249 9 Manual.Count131072.C015404.packed 128 cuts15404 = true := by
 decide +kernel
def pointBounds15404 : List (Nat × Nat × Nat) := [(2023016448,96617860903855,96618239168678),(2023079936,96618274410176,96618652675271)]
theorem point_links_checked15404 : (cuts15404.take 2).map (fun c => (2022965249-1+2*2^9*c.k,96617533094732+c.lower,96617911359337+c.upper)) = pointBounds15404 := by
 decide +kernel
def cuts15405 : List PrefixCut := [⟨46,305944953,305945154⟩,
⟨108,722625228,722625697⟩,
⟨128,855904514,855905071⟩]
theorem checked15405 : checkPrefixCuts (2^48) 2023096321 9 Manual.Count131072.C015405.packed 128 cuts15405 = true := by
 decide +kernel
def pointBounds15405 : List (Nat × Nat × Nat) := [(2023143424,96618684007948,96619062273313),(2023206912,96619100688223,96619478953856)]
theorem point_links_checked15405 : (cuts15405.take 2).map (fun c => (2023096321-1+2*2^9*c.k,96618378062995+c.lower,96618756328159+c.upper)) = pointBounds15405 := by
 decide +kernel
def cuts15406 : List PrefixCut := [⟨42,278936077,278936256⟩,
⟨104,679591899,679592340⟩,
⟨128,836651088,836651636⟩]
theorem checked15406 : checkPrefixCuts (2^48) 2023227393 9 Manual.Count131072.C015406.packed 128 cuts15406 = true := by
 decide +kernel
def pointBounds15406 : List (Nat × Nat × Nat) := [(2023270400,96619512903586,96619891169486),(2023333888,96619913559408,96620291825570)]
theorem point_links_checked15406 : (cuts15406.take 2).map (fun c => (2023227393-1+2*2^9*c.k,96619233967509+c.lower,96619612233230+c.upper)) = pointBounds15406 := by
 decide +kernel
def cuts15407 : List PrefixCut := [⟨38,256799643,256799813⟩,
⟨100,664803006,664803443⟩,
⟨128,847586575,847587133⟩]
theorem checked15407 : checkPrefixCuts (2^48) 2023358465 9 Manual.Count131072.C015407.packed 128 cuts15407 = true := by
 decide +kernel
def pointBounds15407 : List (Nat × Nat × Nat) := [(2023397376,96620327418240,96620705684679),(2023460864,96620735421603,96621113688309)]
theorem point_links_checked15407 : (cuts15407.take 2).map (fun c => (2023358465-1+2*2^9*c.k,96620070618597+c.lower,96620448884866+c.upper)) = pointBounds15407 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000168
