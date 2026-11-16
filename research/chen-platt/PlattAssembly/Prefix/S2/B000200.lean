import PlattAssemblyKernel
import PlattCertificates.Count131072.C016400
import PlattCertificates.Count131072.C016401
import PlattCertificates.Count131072.C016402
import PlattCertificates.Count131072.C016403
import PlattCertificates.Count131072.C016404
import PlattCertificates.Count131072.C016405
import PlattCertificates.Count131072.C016406
import PlattCertificates.Count131072.C016407
import PlattCertificates.Count131072.C016408
import PlattCertificates.Count131072.C016409
import PlattCertificates.Count131072.C016410
import PlattCertificates.Count131072.C016411
import PlattCertificates.Count131072.C016412
import PlattCertificates.Count131072.C016413
import PlattCertificates.Count131072.C016414
import PlattCertificates.Count131072.C016415
import PlattCertificates.Count131072.C016416
import PlattCertificates.Count131072.C016417
import PlattCertificates.Count131072.C016418
import PlattCertificates.Count131072.C016419
import PlattCertificates.Count131072.C016420
import PlattCertificates.Count131072.C016421
import PlattCertificates.Count131072.C016422
import PlattCertificates.Count131072.C016423
import PlattCertificates.Count131072.C016424
import PlattCertificates.Count131072.C016425
import PlattCertificates.Count131072.C016426
import PlattCertificates.Count131072.C016427
import PlattCertificates.Count131072.C016428
import PlattCertificates.Count131072.C016429
import PlattCertificates.Count131072.C016430
import PlattCertificates.Count131072.C016431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16400 : List PrefixCut := [⟨11,67835707,67835750⟩,
⟨77,477979357,477979660⟩,
⟨128,798452357,798452865⟩]
theorem checked16400 : checkPrefixCuts (2^48) 2153512961 9 Manual.Count131072.C016400.packed 128 cuts16400 = true := by
 decide +kernel
def pointBounds16400 : List (Nat × Nat × Nat) := [(2153524224,97437790181443,97438168975845),(2153591808,97438200325093,97438579119755)]
theorem point_links_checked16400 : (cuts16400.take 2).map (fun c => (2153512961-1+2*2^9*c.k,97437722345736+c.lower,97438101140095+c.upper)) = pointBounds16400 := by
 decide +kernel
def cuts16401 : List PrefixCut := [⟨15,94755010,94755071⟩,
⟨81,504742304,504742623⟩,
⟨128,802063271,802063781⟩]
theorem checked16401 : checkPrefixCuts (2^48) 2153644033 9 Manual.Count131072.C016401.packed 128 cuts16401 = true := by
 decide +kernel
def pointBounds16401 : List (Nat × Nat × Nat) := [(2153659392,97438615553103,97438994348031),(2153726976,97439025540397,97439404335583)]
theorem point_links_checked16401 : (cuts16401.take 2).map (fun c => (2153644033-1+2*2^9*c.k,97438520798093+c.lower,97438899592960+c.upper)) = pointBounds16401 := by
 decide +kernel
def cuts16402 : List PrefixCut := [⟨19,119187893,119187970⟩,
⟨85,518041123,518041451⟩,
⟨128,788815174,788815671⟩]
theorem checked16402 : checkPrefixCuts (2^48) 2153775105 9 Manual.Count131072.C016402.packed 128 cuts16402 = true := by
 decide +kernel
def pointBounds16402 : List (Nat × Nat × Nat) := [(2153794560,97439442049257,97439820844711),(2153862144,97439840902487,97440219698192)]
theorem point_links_checked16402 : (cuts16402.take 2).map (fun c => (2153775105-1+2*2^9*c.k,97439322861364+c.lower,97439701656741+c.upper)) = pointBounds16402 := by
 decide +kernel
def cuts16403 : List PrefixCut := [⟨23,140220106,140220199⟩,
⟨89,557865904,557866260⟩,
⟨128,798306763,798307269⟩]
theorem checked16403 : checkPrefixCuts (2^48) 2153906177 9 Manual.Count131072.C016403.packed 128 cuts16403 = true := by
 decide +kernel
def pointBounds16403 : List (Nat × Nat × Nat) := [(2153929728,97440251896644,97440630692611),(2153997312,97440669542442,97441048338672)]
theorem point_links_checked16403 : (cuts16403.take 2).map (fun c => (2153906177-1+2*2^9*c.k,97440111676538+c.lower,97440490472412+c.upper)) = pointBounds16403 := by
 decide +kernel
def cuts16404 : List PrefixCut := [⟨27,170527386,170527493⟩,
⟨93,579784172,579784543⟩,
⟨128,798519546,798520056⟩]
theorem checked16404 : checkPrefixCuts (2^48) 2154037249 9 Manual.Count131072.C016404.packed 128 cuts16404 = true := by
 decide +kernel
def pointBounds16404 : List (Nat × Nat × Nat) := [(2154064896,97441080510687,97441459307174),(2154132480,97441489767473,97441868564224)]
theorem point_links_checked16404 : (cuts16404.take 2).map (fun c => (2154037249-1+2*2^9*c.k,97440909983301+c.lower,97441288779681+c.upper)) = pointBounds16404 := by
 decide +kernel
def cuts16405 : List PrefixCut := [⟨31,194689709,194689834⟩,
⟨97,609931095,609931478⟩,
⟨128,803174621,803175127⟩]
theorem checked16405 : checkPrefixCuts (2^48) 2154168321 9 Manual.Count131072.C016405.packed 128 cuts16405 = true := by
 decide +kernel
def pointBounds16405 : List (Nat × Nat × Nat) := [(2154200064,97441903192556,97442281989571),(2154267648,97442318433942,97442697231215)]
theorem point_links_checked16405 : (cuts16405.take 2).map (fun c => (2154168321-1+2*2^9*c.k,97441708502847+c.lower,97442087299737+c.upper)) = pointBounds16405 := by
 decide +kernel
def cuts16406 : List PrefixCut := [⟨35,215190739,215190876⟩,
⟨101,627139731,627140132⟩,
⟨128,796984949,796985456⟩]
theorem checked16406 : checkPrefixCuts (2^48) 2154299393 9 Manual.Count131072.C016406.packed 128 cuts16406 = true := by
 decide +kernel
def pointBounds16406 : List (Nat × Nat × Nat) := [(2154335232,97442726868207,97443105665740),(2154402816,97443138817199,97443517614996)]
theorem point_links_checked16406 : (cuts16406.take 2).map (fun c => (2154299393-1+2*2^9*c.k,97442511677468+c.lower,97442890474864+c.upper)) = pointBounds16406 := by
 decide +kernel
def cuts16407 : List PrefixCut := [⟨39,243005502,243005655⟩,
⟨105,652838451,652838867⟩,
⟨128,795368986,795369491⟩]
theorem checked16407 : checkPrefixCuts (2^48) 2154430465 9 Manual.Count131072.C016407.packed 128 cuts16407 = true := by
 decide +kernel
def pointBounds16407 : List (Nat × Nat × Nat) := [(2154470400,97443551667919,97443930465975),(2154537984,97443961500868,97444340299187)]
theorem point_links_checked16407 : (cuts16407.take 2).map (fun c => (2154430465-1+2*2^9*c.k,97443308662417+c.lower,97443687460320+c.upper)) = pointBounds16407 := by
 decide +kernel
def cuts16408 : List PrefixCut := [⟨43,266505661,266505835⟩,
⟨109,675529048,675529478⟩,
⟨128,795189816,795190319⟩]
theorem checked16408 : checkPrefixCuts (2^48) 2154561537 9 Manual.Count131072.C016408.packed 128 cuts16408 = true := by
 decide +kernel
def pointBounds16408 : List (Nat × Nat × Nat) := [(2154605568,97444370537064,97444749335646),(2154673152,97444779560451,97445158359289)]
theorem point_links_checked16408 : (cuts16408.take 2).map (fun c => (2154561537-1+2*2^9*c.k,97444104031403+c.lower,97444482829811+c.upper)) = pointBounds16408 := by
 decide +kernel
def cuts16409 : List PrefixCut := [⟨47,290394868,290395054⟩,
⟨113,709581567,709582020⟩,
⟨128,801411611,801412124⟩]
theorem checked16409 : checkPrefixCuts (2^48) 2154692609 9 Manual.Count131072.C016409.packed 128 cuts16409 = true := by
 decide +kernel
def pointBounds16409 : List (Nat × Nat × Nat) := [(2154740736,97445189616087,97445568415184),(2154808320,97445608802786,97445987602150)]
theorem point_links_checked16409 : (cuts16409.take 2).map (fun c => (2154692609-1+2*2^9*c.k,97444899221219+c.lower,97445278020130+c.upper)) = pointBounds16409 := by
 decide +kernel
def cuts16410 : List PrefixCut := [⟨51,319375420,319375623⟩,
⟨117,733049752,733050218⟩,
⟨128,799664873,799665382⟩]
theorem checked16410 : checkPrefixCuts (2^48) 2154823681 9 Manual.Count131072.C016410.packed 128 cuts16410 = true := by
 decide +kernel
def pointBounds16410 : List (Nat × Nat × Nat) := [(2154875904,97446020008250,97446398807877),(2154943488,97446433682582,97446812482472)]
theorem point_links_checked16410 : (cuts16410.take 2).map (fun c => (2154823681-1+2*2^9*c.k,97445700632830+c.lower,97446079432254+c.upper)) = pointBounds16410 := by
 decide +kernel
def cuts16411 : List PrefixCut := [⟨55,341037938,341038156⟩,
⟨121,755208874,755209353⟩,
⟨128,796612186,796612692⟩]
theorem checked16411 : checkPrefixCuts (2^48) 2154954753 9 Manual.Count131072.C016411.packed 128 cuts16411 = true := by
 decide +kernel
def pointBounds16411 : List (Nat × Nat × Nat) := [(2155011072,97446841335641,97447220135792),(2155078656,97447255506577,97447634306989)]
theorem point_links_checked16411 : (cuts16411.take 2).map (fun c => (2154954753-1+2*2^9*c.k,97446500297703+c.lower,97446879097636+c.upper)) = pointBounds16411 := by
 decide +kernel
def cuts16412 : List PrefixCut := [⟨59,364918163,364918395⟩,
⟨125,780760926,780761421⟩,
⟨128,799175773,799176279⟩]
theorem checked16412 : checkPrefixCuts (2^48) 2155085825 9 Manual.Count131072.C016412.packed 128 cuts16412 = true := by
 decide +kernel
def pointBounds16412 : List (Nat × Nat × Nat) := [(2155146240,97447661828052,97448040628723),(2155213824,97448077670815,97448456471749)]
theorem point_links_checked16412 : (cuts16412.take 2).map (fun c => (2155085825-1+2*2^9*c.k,97447296909889+c.lower,97447675710328+c.upper)) = pointBounds16412 := by
 decide +kernel
def cuts16413 : List PrefixCut := [⟨63,398459678,398459938⟩,
⟨128,802392204,802392719⟩]
theorem checked16413 : checkPrefixCuts (2^48) 2155216897 9 Manual.Count131072.C016413.packed 128 cuts16413 = true := by
 decide +kernel
def pointBounds16413 : List (Nat × Nat × Nat) := [(2155281408,97448494545340,97448873346545)]
theorem point_links_checked16413 : (cuts16413.take 1).map (fun c => (2155216897-1+2*2^9*c.k,97448096085662+c.lower,97448474886607+c.upper)) = pointBounds16413 := by
 decide +kernel
def cuts16414 : List PrefixCut := [⟨1,5746122,5746126⟩,
⟨67,414889577,414889848⟩,
⟨128,793985507,793986023⟩]
theorem checked16414 : checkPrefixCuts (2^48) 2155347969 9 Manual.Count131072.C016414.packed 128 cuts16414 = true := by
 decide +kernel
def pointBounds16414 : List (Nat × Nat × Nat) := [(2155348992,97448904223988,97449283025452),(2155416576,97449313367443,97449692169174)]
theorem point_links_checked16414 : (cuts16414.take 2).map (fun c => (2155347969-1+2*2^9*c.k,97448898477866+c.lower,97449277279326+c.upper)) = pointBounds16414 := by
 decide +kernel
def cuts16415 : List PrefixCut := [⟨5,30165276,30165296⟩,
⟨71,437063134,437063412⟩,
⟨128,792239602,792240105⟩]
theorem checked16415 : checkPrefixCuts (2^48) 2155479041 9 Manual.Count131072.C016415.packed 128 cuts16415 = true := by
 decide +kernel
def pointBounds16415 : List (Nat × Nat × Nat) := [(2155484160,97449722628649,97450101430645),(2155551744,97450129526507,97450508328761)]
theorem point_links_checked16415 : (cuts16415.take 2).map (fun c => (2155479041-1+2*2^9*c.k,97449692463373+c.lower,97450071265349+c.upper)) = pointBounds16415 := by
 decide +kernel
def cuts16416 : List PrefixCut := [⟨9,58237592,58237628⟩,
⟨75,467721544,467721837⟩,
⟨128,793628125,793628622⟩]
theorem checked16416 : checkPrefixCuts (2^48) 2155610113 9 Manual.Count131072.C016416.packed 128 cuts16416 = true := by
 decide +kernel
def pointBounds16416 : List (Nat × Nat × Nat) := [(2155619328,97450542940567,97450921743082),(2155686912,97450952424519,97451331227291)]
theorem point_links_checked16416 : (cuts16416.take 2).map (fun c => (2155610113-1+2*2^9*c.k,97450484702975+c.lower,97450863505454+c.upper)) = pointBounds16416 := by
 decide +kernel
def cuts16417 : List PrefixCut := [⟨13,80691945,80691994⟩,
⟨79,495242327,495242636⟩,
⟨128,800499710,800500211⟩]
theorem checked16417 : checkPrefixCuts (2^48) 2155741185 9 Manual.Count131072.C016417.packed 128 cuts16417 = true := by
 decide +kernel
def pointBounds16417 : List (Nat × Nat × Nat) := [(2155754496,97451359023045,97451737826070),(2155822080,97451773573427,97452152376712)]
theorem point_links_checked16417 : (cuts16417.take 2).map (fun c => (2155741185-1+2*2^9*c.k,97451278331100+c.lower,97451657134076+c.upper)) = pointBounds16417 := by
 decide +kernel
def cuts16418 : List PrefixCut := [⟨17,106538122,106538189⟩,
⟨83,516492929,516493262⟩,
⟨128,796664840,796665352⟩]
theorem checked16418 : checkPrefixCuts (2^48) 2155872257 9 Manual.Count131072.C016418.packed 128 cuts16418 = true := by
 decide +kernel
def pointBounds16418 : List (Nat × Nat × Nat) := [(2155889664,97452185368932,97452564172476),(2155957248,97452595323739,97452974127549)]
theorem point_links_checked16418 : (cuts16418.take 2).map (fun c => (2155872257-1+2*2^9*c.k,97452078830810+c.lower,97452457634287+c.upper)) = pointBounds16418 := by
 decide +kernel
def cuts16419 : List PrefixCut := [⟨21,127942305,127942384⟩,
⟨87,536435385,536435723⟩,
⟨128,784475342,784475839⟩]
theorem checked16419 : checkPrefixCuts (2^48) 2156003329 9 Manual.Count131072.C016419.packed 128 cuts16419 = true := by
 decide +kernel
def pointBounds16419 : List (Nat × Nat × Nat) := [(2156024832,97453003437955,97453382242023),(2156092416,97453411931035,97453790735362)]
theorem point_links_checked16419 : (cuts16419.take 2).map (fun c => (2156003329-1+2*2^9*c.k,97452875495650+c.lower,97453254299639+c.upper)) = pointBounds16419 := by
 decide +kernel
def cuts16420 : List PrefixCut := [⟨25,155348918,155349019⟩,
⟨91,566949356,566949713⟩,
⟨128,798134438,798134940⟩]
theorem checked16420 : checkPrefixCuts (2^48) 2156134401 9 Manual.Count131072.C016420.packed 128 cuts16420 = true := by
 decide +kernel
def pointBounds16420 : List (Nat × Nat × Nat) := [(2156160000,97453815319910,97454194124497),(2156227584,97454226920348,97454605725191)]
theorem point_links_checked16420 : (cuts16420.take 2).map (fun c => (2156134401-1+2*2^9*c.k,97453659970992+c.lower,97454038775478+c.upper)) = pointBounds16420 := by
 decide +kernel
def cuts16421 : List PrefixCut := [⟨29,183274287,183274406⟩,
⟨95,594196281,594196661⟩,
⟨128,796911247,796911761⟩]
theorem checked16421 : checkPrefixCuts (2^48) 2156265473 9 Manual.Count131072.C016421.packed 128 cuts16421 = true := by
 decide +kernel
def pointBounds16421 : List (Nat × Nat × Nat) := [(2156295168,97454641379717,97455020184824),(2156362752,97455052301711,97455431107079)]
theorem point_links_checked16421 : (cuts16421.take 2).map (fun c => (2156265473-1+2*2^9*c.k,97454458105430+c.lower,97454836910418+c.upper)) = pointBounds16421 := by
 decide +kernel
def cuts16422 : List PrefixCut := [⟨33,202189692,202189819⟩,
⟨99,611650144,611650529⟩,
⟨128,795818332,795818833⟩]
theorem checked16422 : checkPrefixCuts (2^48) 2156396545 9 Manual.Count131072.C016422.packed 128 cuts16422 = true := by
 decide +kernel
def pointBounds16422 : List (Nat × Nat × Nat) := [(2156430336,97455457206369,97455836011998),(2156497920,97455866666821,97456245472708)]
theorem point_links_checked16422 : (cuts16422.take 2).map (fun c => (2156396545-1+2*2^9*c.k,97455255016677+c.lower,97455633822179+c.upper)) = pointBounds16422 := by
 decide +kernel
def cuts16423 : List PrefixCut := [⟨37,234154923,234155072⟩,
⟨103,636672168,636672573⟩,
⟨128,792115694,792116198⟩]
theorem checked16423 : checkPrefixCuts (2^48) 2156527617 9 Manual.Count131072.C016423.packed 128 cuts16423 = true := by
 decide +kernel
def pointBounds16423 : List (Nat × Nat × Nat) := [(2156565504,97456284989932,97456663796084),(2156633088,97456687507177,97457066313585)]
theorem point_links_checked16423 : (cuts16423.take 2).map (fun c => (2156527617-1+2*2^9*c.k,97456050835009+c.lower,97456429641012+c.upper)) = pointBounds16423 := by
 decide +kernel
def cuts16424 : List PrefixCut := [⟨41,252542800,252542962⟩,
⟨107,667041784,667042208⟩,
⟨128,797548834,797549344⟩]
theorem checked16424 : checkPrefixCuts (2^48) 2156658689 9 Manual.Count131072.C016424.packed 128 cuts16424 = true := by
 decide +kernel
def pointBounds16424 : List (Nat × Nat × Nat) := [(2156700672,97457095493503,97457474300172),(2156768256,97457509992487,97457888799418)]
theorem point_links_checked16424 : (cuts16424.take 2).map (fun c => (2156658689-1+2*2^9*c.k,97456842950703+c.lower,97457221757210+c.upper)) = pointBounds16424 := by
 decide +kernel
def cuts16425 : List PrefixCut := [⟨45,281238320,281238499⟩,
⟨111,688403326,688403762⟩,
⟨128,795281998,795282504⟩]
theorem checked16425 : checkPrefixCuts (2^48) 2156789761 9 Manual.Count131072.C016425.packed 128 cuts16425 = true := by
 decide +kernel
def pointBounds16425 : List (Nat × Nat × Nat) := [(2156835840,97457921737857,97458300545053),(2156903424,97458328902863,97458707710316)]
theorem point_links_checked16425 : (cuts16425.take 2).map (fun c => (2156789761-1+2*2^9*c.k,97457640499537+c.lower,97458019306554+c.upper)) = pointBounds16425 := by
 decide +kernel
def cuts16426 : List PrefixCut := [⟨49,297141570,297141759⟩,
⟨115,707282317,707282768⟩,
⟨128,786881789,786882292⟩]
theorem checked16426 : checkPrefixCuts (2^48) 2156920833 9 Manual.Count131072.C016426.packed 128 cuts16426 = true := by
 decide +kernel
def pointBounds16426 : List (Nat × Nat × Nat) := [(2156971008,97458732923105,97459111730817),(2157038592,97459143063852,97459521871826)]
theorem point_links_checked16426 : (cuts16426.take 2).map (fun c => (2156920833-1+2*2^9*c.k,97458435781535+c.lower,97458814589058+c.upper)) = pointBounds16426 := by
 decide +kernel
def cuts16427 : List PrefixCut := [⟨53,325178356,325178562⟩,
⟨119,732031201,732031664⟩,
⟨128,791139953,791140453⟩]
theorem checked16427 : checkPrefixCuts (2^48) 2157051905 9 Manual.Count131072.C016427.packed 128 cuts16427 = true := by
 decide +kernel
def pointBounds16427 : List (Nat × Nat × Nat) := [(2157106176,97459547841680,97459926649912),(2157173760,97459954694525,97460333503014)]
theorem point_links_checked16427 : (cuts16427.take 2).map (fun c => (2157051905-1+2*2^9*c.k,97459222663324+c.lower,97459601471350+c.upper)) = pointBounds16427 := by
 decide +kernel
def cuts16428 : List PrefixCut := [⟨57,358430888,358431114⟩,
⟨123,767084987,767085474⟩,
⟨128,798398952,798399459⟩]
theorem checked16428 : checkPrefixCuts (2^48) 2157182977 9 Manual.Count131072.C016428.packed 128 cuts16428 = true := by
 decide +kernel
def pointBounds16428 : List (Nat × Nat × Nat) := [(2157241344,97460372234165,97460751042917),(2157308928,97460780888264,97461159697277)]
theorem point_links_checked16428 : (cuts16428.take 2).map (fun c => (2157182977-1+2*2^9*c.k,97460013803277+c.lower,97460392611803+c.upper)) = pointBounds16428 := by
 decide +kernel
def cuts16429 : List PrefixCut := [⟨61,385416636,385416884⟩,
⟨127,805917779,805918291⟩,
⟨128,811397384,811397900⟩]
theorem checked16429 : checkPrefixCuts (2^48) 2157314049 9 Manual.Count131072.C016429.packed 128 cuts16429 = true := by
 decide +kernel
def pointBounds16429 : List (Nat × Nat × Nat) := [(2157376512,97461197618865,97461576428146),(2157444096,97461618120008,97461996929553)]
theorem point_links_checked16429 : (cuts16429.take 2).map (fun c => (2157314049-1+2*2^9*c.k,97460812202229+c.lower,97461191011262+c.upper)) = pointBounds16429 := by
 decide +kernel
def cuts16430 : List PrefixCut := [⟨65,403136041,403136300⟩,
⟨128,794909791,794910297⟩]
theorem checked16430 : checkPrefixCuts (2^48) 2157445121 9 Manual.Count131072.C016430.packed 128 cuts16430 = true := by
 decide +kernel
def pointBounds16430 : List (Nat × Nat × Nat) := [(2157511680,97462026735654,97462405545462)]
theorem point_links_checked16430 : (cuts16430.take 1).map (fun c => (2157445121-1+2*2^9*c.k,97461623599613+c.lower,97462002409162+c.upper)) = pointBounds16430 := by
 decide +kernel
def cuts16431 : List PrefixCut := [⟨3,18394683,18394695⟩,
⟨69,423723377,423723649⟩,
⟨128,791991470,791991979⟩]
theorem checked16431 : checkPrefixCuts (2^48) 2157576193 9 Manual.Count131072.C016431.packed 128 cuts16431 = true := by
 decide +kernel
def pointBounds16431 : List (Nat × Nat × Nat) := [(2157579264,97462436904087,97462815714154),(2157646848,97462842232781,97463221043108)]
theorem point_links_checked16431 : (cuts16431.take 2).map (fun c => (2157576193-1+2*2^9*c.k,97462418509404+c.lower,97462797319459+c.upper)) = pointBounds16431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000200
