import PlattAssemblyKernel
import PlattCertificates.Count131072.C028352
import PlattCertificates.Count131072.C028353
import PlattCertificates.Count131072.C028354
import PlattCertificates.Count131072.C028355
import PlattCertificates.Count131072.C028356
import PlattCertificates.Count131072.C028357
import PlattCertificates.Count131072.C028358
import PlattCertificates.Count131072.C028359
import PlattCertificates.Count131072.C028360
import PlattCertificates.Count131072.C028361
import PlattCertificates.Count131072.C028362
import PlattCertificates.Count131072.C028363
import PlattCertificates.Count131072.C028364
import PlattCertificates.Count131072.C028365
import PlattCertificates.Count131072.C028366
import PlattCertificates.Count131072.C028367
import PlattCertificates.Count131072.C028368
import PlattCertificates.Count131072.C028369
import PlattCertificates.Count131072.C028370
import PlattCertificates.Count131072.C028371
import PlattCertificates.Count131072.C028372
import PlattCertificates.Count131072.C028373
import PlattCertificates.Count131072.C028374
import PlattCertificates.Count131072.C028375
import PlattCertificates.Count131072.C028376
import PlattCertificates.Count131072.C028377
import PlattCertificates.Count131072.C028378
import PlattCertificates.Count131072.C028379
import PlattCertificates.Count131072.C028380
import PlattCertificates.Count131072.C028381
import PlattCertificates.Count131072.C028382
import PlattCertificates.Count131072.C028383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000261
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28352 : List PrefixCut := [⟨79,281465382,281465537⟩,
⟨128,452081844,452082095⟩]
theorem checked28352 : checkPrefixCuts (2^48) 3720085505 9 Manual.Count131072.C028352.packed 128 cuts28352 = true := by
 decide +kernel
def pointBounds28352 : List (Nat × Nat × Nat) := [(3720166400,104508283216746,104508666134641)]
theorem point_links_checked28352 : (cuts28352.take 1).map (fun c => (3720085505-1+2*2^9*c.k,104508001751364+c.lower,104508384669104+c.upper)) = pointBounds28352 := by
 decide +kernel
def cuts28353 : List PrefixCut := [⟨65,231671580,231671707⟩,
⟨128,453579079,453579329⟩]
theorem checked28353 : checkPrefixCuts (2^48) 3720216577 9 Manual.Count131072.C028353.packed 128 cuts28353 = true := by
 decide +kernel
def pointBounds28353 : List (Nat × Nat × Nat) := [(3720283136,104508685504788,104509068422906)]
theorem point_links_checked28353 : (cuts28353.take 1).map (fun c => (3720216577-1+2*2^9*c.k,104508453833208+c.lower,104508836751199+c.upper)) = pointBounds28353 := by
 decide +kernel
def cuts28354 : List PrefixCut := [⟨51,174088343,174088444⟩,
⟨128,443576274,443576524⟩]
theorem checked28354 : checkPrefixCuts (2^48) 3720347649 9 Manual.Count131072.C028354.packed 128 cuts28354 = true := by
 decide +kernel
def pointBounds28354 : List (Nat × Nat × Nat) := [(3720399872,104509081500630,104509464418972)]
theorem point_links_checked28354 : (cuts28354.take 1).map (fun c => (3720347649-1+2*2^9*c.k,104508907412287+c.lower,104509290330528+c.upper)) = pointBounds28354 := by
 decide +kernel
def cuts28355 : List PrefixCut := [⟨37,129597315,129597388⟩,
⟨128,450445247,450445500⟩]
theorem checked28355 : checkPrefixCuts (2^48) 3720478721 9 Manual.Count131072.C028355.packed 128 cuts28355 = true := by
 decide +kernel
def pointBounds28355 : List (Nat × Nat × Nat) := [(3720516608,104509480585876,104509863504440)]
theorem point_links_checked28355 : (cuts28355.take 1).map (fun c => (3720478721-1+2*2^9*c.k,104509350988561+c.lower,104509733907052+c.upper)) = pointBounds28355 := by
 decide +kernel
def cuts28356 : List PrefixCut := [⟨23,83369228,83369275⟩,
⟨128,454514595,454514846⟩]
theorem checked28356 : checkPrefixCuts (2^48) 3720609793 9 Manual.Count131072.C028356.packed 128 cuts28356 = true := by
 decide +kernel
def pointBounds28356 : List (Nat × Nat × Nat) := [(3720633344,104509884803036,104510267721827)]
theorem point_links_checked28356 : (cuts28356.take 1).map (fun c => (3720609793-1+2*2^9*c.k,104509801433808+c.lower,104510184352552+c.upper)) = pointBounds28356 := by
 decide +kernel
def cuts28357 : List PrefixCut := [⟨9,31924356,31924374⟩,
⟨123,435662259,435662501⟩,
⟨128,453136858,453137110⟩]
theorem checked28357 : checkPrefixCuts (2^48) 3720740865 9 Manual.Count131072.C028357.packed 128 cuts28357 = true := by
 decide +kernel
def pointBounds28357 : List (Nat × Nat × Nat) := [(3720750080,104510287872759,104510670791772),(3720866816,104510691610662,104511074529899)]
theorem point_links_checked28357 : (cuts28357.take 2).map (fun c => (3720740865-1+2*2^9*c.k,104510255948403+c.lower,104510638867398+c.upper)) = pointBounds28357 := by
 decide +kernel
def cuts28358 : List PrefixCut := [⟨109,376719213,376719427⟩,
⟨128,444497217,444497469⟩]
theorem checked28358 : checkPrefixCuts (2^48) 3720871937 9 Manual.Count131072.C028358.packed 128 cuts28358 = true := by
 decide +kernel
def pointBounds28358 : List (Nat × Nat × Nat) := [(3720983552,104511085804474,104511468723935)]
theorem point_links_checked28358 : (cuts28358.take 1).map (fun c => (3720871937-1+2*2^9*c.k,104510709085261+c.lower,104511092004508+c.upper)) = pointBounds28358 := by
 decide +kernel
def cuts28359 : List PrefixCut := [⟨95,337220534,337220720⟩,
⟨128,454012683,454012931⟩]
theorem checked28359 : checkPrefixCuts (2^48) 3721003009 9 Manual.Count131072.C028359.packed 128 cuts28359 = true := by
 decide +kernel
def pointBounds28359 : List (Nat × Nat × Nat) := [(3721100288,104511490803012,104511873722697)]
theorem point_links_checked28359 : (cuts28359.take 1).map (fun c => (3721003009-1+2*2^9*c.k,104511153582478+c.lower,104511536501977+c.upper)) = pointBounds28359 := by
 decide +kernel
def cuts28360 : List PrefixCut := [⟨81,288723175,288723335⟩,
⟨128,452862109,452862360⟩]
theorem checked28360 : checkPrefixCuts (2^48) 3721134081 9 Manual.Count131072.C028360.packed 128 cuts28360 = true := by
 decide +kernel
def pointBounds28360 : List (Nat × Nat × Nat) := [(3721217024,104511896318336,104512279238243)]
theorem point_links_checked28360 : (cuts28360.take 1).map (fun c => (3721134081-1+2*2^9*c.k,104511607595161+c.lower,104511990514908+c.upper)) = pointBounds28360 := by
 decide +kernel
def cuts28361 : List PrefixCut := [⟨67,239397035,239397169⟩,
⟨128,453678188,453678445⟩]
theorem checked28361 : checkPrefixCuts (2^48) 3721265153 9 Manual.Count131072.C028361.packed 128 cuts28361 = true := by
 decide +kernel
def pointBounds28361 : List (Nat × Nat × Nat) := [(3721333760,104512299854305,104512682774437)]
theorem point_links_checked28361 : (cuts28361.take 1).map (fun c => (3721265153-1+2*2^9*c.k,104512060457270+c.lower,104512443377268+c.upper)) = pointBounds28361 := by
 decide +kernel
def cuts28362 : List PrefixCut := [⟨53,190452337,190452440⟩,
⟨128,454569863,454570110⟩]
theorem checked28362 : checkPrefixCuts (2^48) 3721396225 9 Manual.Count131072.C028362.packed 128 cuts28362 = true := by
 decide +kernel
def pointBounds28362 : List (Nat × Nat × Nat) := [(3721450496,104512704587795,104513087508153)]
theorem point_links_checked28362 : (cuts28362.take 1).map (fun c => (3721396225-1+2*2^9*c.k,104512514135458+c.lower,104512897055713+c.upper)) = pointBounds28362 := by
 decide +kernel
def cuts28363 : List PrefixCut := [⟨39,140452035,140452113⟩,
⟨128,456444685,456444939⟩]
theorem checked28363 : checkPrefixCuts (2^48) 3721527297 9 Manual.Count131072.C028363.packed 128 cuts28363 = true := by
 decide +kernel
def pointBounds28363 : List (Nat × Nat × Nat) := [(3721567232,104513109157356,104513492077936)]
theorem point_links_checked28363 : (cuts28363.take 1).map (fun c => (3721527297-1+2*2^9*c.k,104512968705321+c.lower,104513351625823+c.upper)) = pointBounds28363 := by
 decide +kernel
def cuts28364 : List PrefixCut := [⟨25,89169329,89169376⟩,
⟨128,451588211,451588461⟩]
theorem checked28364 : checkPrefixCuts (2^48) 3721658369 9 Manual.Count131072.C028364.packed 128 cuts28364 = true := by
 decide +kernel
def pointBounds28364 : List (Nat × Nat × Nat) := [(3721683968,104513514319335,104513897240138)]
theorem point_links_checked28364 : (cuts28364.take 1).map (fun c => (3721658369-1+2*2^9*c.k,104513425150006+c.lower,104513808070762+c.upper)) = pointBounds28364 := by
 decide +kernel
def cuts28365 : List PrefixCut := [⟨11,36906855,36906876⟩,
⟨125,434707448,434707689⟩,
⟨128,444614490,444614737⟩]
theorem checked28365 : checkPrefixCuts (2^48) 3721789441 9 Manual.Count131072.C028365.packed 128 cuts28365 = true := by
 decide +kernel
def pointBounds28365 : List (Nat × Nat × Nat) := [(3721800704,104513913645072,104514296566099),(3721917440,104514311445665,104514694366912)]
theorem point_links_checked28365 : (cuts28365.take 2).map (fun c => (3721789441-1+2*2^9*c.k,104513876738217+c.lower,104514259659223+c.upper)) = pointBounds28365 := by
 decide +kernel
def cuts28366 : List PrefixCut := [⟨111,390679293,390679513⟩,
⟨128,452539536,452539791⟩]
theorem checked28366 : checkPrefixCuts (2^48) 3721920513 9 Manual.Count131072.C028366.packed 128 cuts28366 = true := by
 decide +kernel
def pointBounds28366 : List (Nat × Nat × Nat) := [(3722034176,104514712032000,104515094953473)]
theorem point_links_checked28366 : (cuts28366.take 1).map (fun c => (3721920513-1+2*2^9*c.k,104514321352707+c.lower,104514704273960+c.upper)) = pointBounds28366 := by
 decide +kernel
def cuts28367 : List PrefixCut := [⟨97,341360259,341360452⟩,
⟨128,449196152,449196406⟩]
theorem checked28367 : checkPrefixCuts (2^48) 3722051585 9 Manual.Count131072.C028367.packed 128 cuts28367 = true := by
 decide +kernel
def pointBounds28367 : List (Nat × Nat × Nat) := [(3722150912,104515115252502,104515498174203)]
theorem point_links_checked28367 : (cuts28367.take 1).map (fun c => (3722051585-1+2*2^9*c.k,104514773892243+c.lower,104515156813751+c.upper)) = pointBounds28367 := by
 decide +kernel
def cuts28368 : List PrefixCut := [⟨83,296430605,296430763⟩,
⟨128,455305554,455305802⟩]
theorem checked28368 : checkPrefixCuts (2^48) 3722182657 9 Manual.Count131072.C028368.packed 128 cuts28368 = true := by
 decide +kernel
def pointBounds28368 : List (Nat × Nat × Nat) := [(3722267648,104515519519000,104515902440920)]
theorem point_links_checked28368 : (cuts28368.take 1).map (fun c => (3722182657-1+2*2^9*c.k,104515223088395+c.lower,104515606010157+c.upper)) = pointBounds28368 := by
 decide +kernel
def cuts28369 : List PrefixCut := [⟨69,244395940,244396075⟩,
⟨128,449618360,449618611⟩]
theorem checked28369 : checkPrefixCuts (2^48) 3722313729 9 Manual.Count131072.C028369.packed 128 cuts28369 = true := by
 decide +kernel
def pointBounds28369 : List (Nat × Nat × Nat) := [(3722384384,104515922789889,104516305712034)]
theorem point_links_checked28369 : (cuts28369.take 1).map (fun c => (3722313729-1+2*2^9*c.k,104515678393949+c.lower,104516061315959+c.upper)) = pointBounds28369 := by
 decide +kernel
def cuts28370 : List PrefixCut := [⟨55,190096174,190096280⟩,
⟨128,447258357,447258611⟩]
theorem checked28370 : checkPrefixCuts (2^48) 3722444801 9 Manual.Count131072.C028370.packed 128 cuts28370 = true := by
 decide +kernel
def pointBounds28370 : List (Nat × Nat × Nat) := [(3722501120,104516318108483,104516701030850)]
theorem point_links_checked28370 : (cuts28370.take 1).map (fun c => (3722444801-1+2*2^9*c.k,104516128012309+c.lower,104516510934570+c.upper)) = pointBounds28370 := by
 decide +kernel
def cuts28371 : List PrefixCut := [⟨41,145856548,145856632⟩,
⟨128,454955061,454955316⟩]
theorem checked28371 : checkPrefixCuts (2^48) 3722575873 9 Manual.Count131072.C028371.packed 128 cuts28371 = true := by
 decide +kernel
def pointBounds28371 : List (Nat × Nat × Nat) := [(3722617856,104516721127214,104517104049813)]
theorem point_links_checked28371 : (cuts28371.take 1).map (fun c => (3722575873-1+2*2^9*c.k,104516575270666+c.lower,104516958193181+c.upper)) = pointBounds28371 := by
 decide +kernel
def cuts28372 : List PrefixCut := [⟨27,99956418,99956475⟩,
⟨128,453956153,453956408⟩]
theorem checked28372 : checkPrefixCuts (2^48) 3722706945 9 Manual.Count131072.C028372.packed 128 cuts28372 = true := by
 decide +kernel
def pointBounds28372 : List (Nat × Nat × Nat) := [(3722734592,104517130182145,104517513104972)]
theorem point_links_checked28372 : (cuts28372.take 1).map (fun c => (3722706945-1+2*2^9*c.k,104517030225727+c.lower,104517413148497+c.upper)) = pointBounds28372 := by
 decide +kernel
def cuts28373 : List PrefixCut := [⟨13,44305982,44306007⟩,
⟨127,446908803,446909054⟩,
⟨128,450311026,450311279⟩]
theorem checked28373 : checkPrefixCuts (2^48) 3722838017 9 Manual.Count131072.C028373.packed 128 cuts28373 = true := by
 decide +kernel
def pointBounds28373 : List (Nat × Nat × Nat) := [(3722851328,104517528487862,104517911410912),(3722968064,104517931090683,104518314013959)]
theorem point_links_checked28373 : (cuts28373.take 2).map (fun c => (3722838017-1+2*2^9*c.k,104517484181880+c.lower,104517867104905+c.upper)) = pointBounds28373 := by
 decide +kernel
def cuts28374 : List PrefixCut := [⟨113,398205061,398205282⟩,
⟨128,450748763,450749014⟩]
theorem checked28374 : checkPrefixCuts (2^48) 3722969089 9 Manual.Count131072.C028374.packed 128 cuts28374 = true := by
 decide +kernel
def pointBounds28374 : List (Nat × Nat × Nat) := [(3723084800,104518332697967,104518715621466)]
theorem point_links_checked28374 : (cuts28374.take 1).map (fun c => (3722969089-1+2*2^9*c.k,104517934492906+c.lower,104518317416184+c.upper)) = pointBounds28374 := by
 decide +kernel
def cuts28375 : List PrefixCut := [⟨99,343607726,343607918⟩,
⟨128,448994019,448994270⟩]
theorem checked28375 : checkPrefixCuts (2^48) 3723100161 9 Manual.Count131072.C028375.packed 128 cuts28375 = true := by
 decide +kernel
def pointBounds28375 : List (Nat × Nat × Nat) := [(3723201536,104518728849395,104519111773116)]
theorem point_links_checked28375 : (cuts28375.take 1).map (fun c => (3723100161-1+2*2^9*c.k,104518385241669+c.lower,104518768165198+c.upper)) = pointBounds28375 := by
 decide +kernel
def cuts28376 : List PrefixCut := [⟨85,297934673,297934839⟩,
⟨128,449280687,449280937⟩]
theorem checked28376 : checkPrefixCuts (2^48) 3723231233 9 Manual.Count131072.C028376.packed 128 cuts28376 = true := by
 decide +kernel
def pointBounds28376 : List (Nat × Nat × Nat) := [(3723318272,104519132170361,104519515094307)]
theorem point_links_checked28376 : (cuts28376.take 1).map (fun c => (3723231233-1+2*2^9*c.k,104518834235688+c.lower,104519217159468+c.upper)) = pointBounds28376 := by
 decide +kernel
def cuts28377 : List PrefixCut := [⟨71,244553778,244553917⟩,
⟨128,445409436,445409690⟩]
theorem checked28377 : checkPrefixCuts (2^48) 3723362305 9 Manual.Count131072.C028377.packed 128 cuts28377 = true := by
 decide +kernel
def pointBounds28377 : List (Nat × Nat × Nat) := [(3723435008,104519528070153,104519910994322)]
theorem point_links_checked28377 : (cuts28377.take 1).map (fun c => (3723362305-1+2*2^9*c.k,104519283516375+c.lower,104519666440405+c.upper)) = pointBounds28377 := by
 decide +kernel
def cuts28378 : List PrefixCut := [⟨57,199265037,199265148⟩,
⟨128,448795489,448795736⟩]
theorem checked28378 : checkPrefixCuts (2^48) 3723493377 9 Manual.Count131072.C028378.packed 128 cuts28378 = true := by
 decide +kernel
def pointBounds28378 : List (Nat × Nat × Nat) := [(3723551744,104519928190848,104520311115243)]
theorem point_links_checked28378 : (cuts28378.take 1).map (fun c => (3723493377-1+2*2^9*c.k,104519728925811+c.lower,104520111850095+c.upper)) = pointBounds28378 := by
 decide +kernel
def cuts28379 : List PrefixCut := [⟨43,147856370,147856453⟩,
⟨128,446738725,446738971⟩]
theorem checked28379 : checkPrefixCuts (2^48) 3723624449 9 Manual.Count131072.C028379.packed 128 cuts28379 = true := by
 decide +kernel
def pointBounds28379 : List (Nat × Nat × Nat) := [(3723668480,104520325577670,104520708502284)]
theorem point_links_checked28379 : (cuts28379.take 1).map (fun c => (3723624449-1+2*2^9*c.k,104520177721300+c.lower,104520560645831+c.upper)) = pointBounds28379 := by
 decide +kernel
def cuts28380 : List PrefixCut := [⟨29,102347085,102347140⟩,
⟨128,450578013,450578266⟩]
theorem checked28380 : checkPrefixCuts (2^48) 3723755521 9 Manual.Count131072.C028380.packed 128 cuts28380 = true := by
 decide +kernel
def pointBounds28380 : List (Nat × Nat × Nat) := [(3723785216,104520726807110,104521109731942)]
theorem point_links_checked28380 : (cuts28380.take 1).map (fun c => (3723755521-1+2*2^9*c.k,104520624460025+c.lower,104521007384802+c.upper)) = pointBounds28380 := by
 decide +kernel
def cuts28381 : List PrefixCut := [⟨15,53137079,53137108⟩,
⟨128,450033059,450033311⟩]
theorem checked28381 : checkPrefixCuts (2^48) 3723886593 9 Manual.Count131072.C028381.packed 128 cuts28381 = true := by
 decide +kernel
def pointBounds28381 : List (Nat × Nat × Nat) := [(3723901952,104521128175117,104521511100176)]
theorem point_links_checked28381 : (cuts28381.take 1).map (fun c => (3723886593-1+2*2^9*c.k,104521075038038+c.lower,104521457963068+c.upper)) = pointBounds28381 := by
 decide +kernel
def cuts28382 : List PrefixCut := [⟨1,3628015,3628017⟩,
⟨115,406104550,406104779⟩,
⟨128,451528815,451529069⟩]
theorem checked28382 : checkPrefixCuts (2^48) 3724017665 9 Manual.Count131072.C028382.packed 128 cuts28382 = true := by
 decide +kernel
def pointBounds28382 : List (Nat × Nat × Nat) := [(3724018688,104521528699112,104521911624396),(3724135424,104521931175647,104522314101158)]
theorem point_links_checked28382 : (cuts28382.take 2).map (fun c => (3724017665-1+2*2^9*c.k,104521525071097+c.lower,104521907996379+c.upper)) = pointBounds28382 := by
 decide +kernel
def cuts28383 : List PrefixCut := [⟨101,352202598,352202795⟩,
⟨128,442443465,442443717⟩]
theorem checked28383 : checkPrefixCuts (2^48) 3724148737 9 Manual.Count131072.C028383.packed 128 cuts28383 = true := by
 decide +kernel
def pointBounds28383 : List (Nat × Nat × Nat) := [(3724252160,104522328802510,104522711728243)]
theorem point_links_checked28383 : (cuts28383.take 1).map (fun c => (3724148737-1+2*2^9*c.k,104521976599912+c.lower,104522359525448+c.upper)) = pointBounds28383 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000261
