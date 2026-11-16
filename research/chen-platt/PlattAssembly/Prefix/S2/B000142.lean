import PlattAssemblyKernel
import PlattCertificates.Count131072.C014544
import PlattCertificates.Count131072.C014545
import PlattCertificates.Count131072.C014546
import PlattCertificates.Count131072.C014547
import PlattCertificates.Count131072.C014548
import PlattCertificates.Count131072.C014549
import PlattCertificates.Count131072.C014550
import PlattCertificates.Count131072.C014551
import PlattCertificates.Count131072.C014552
import PlattCertificates.Count131072.C014553
import PlattCertificates.Count131072.C014554
import PlattCertificates.Count131072.C014555
import PlattCertificates.Count131072.C014556
import PlattCertificates.Count131072.C014557
import PlattCertificates.Count131072.C014558
import PlattCertificates.Count131072.C014559
import PlattCertificates.Count131072.C014560
import PlattCertificates.Count131072.C014561
import PlattCertificates.Count131072.C014562
import PlattCertificates.Count131072.C014563
import PlattCertificates.Count131072.C014564
import PlattCertificates.Count131072.C014565
import PlattCertificates.Count131072.C014566
import PlattCertificates.Count131072.C014567
import PlattCertificates.Count131072.C014568
import PlattCertificates.Count131072.C014569
import PlattCertificates.Count131072.C014570
import PlattCertificates.Count131072.C014571
import PlattCertificates.Count131072.C014572
import PlattCertificates.Count131072.C014573
import PlattCertificates.Count131072.C014574
import PlattCertificates.Count131072.C014575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000142
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14544 : List PrefixCut := [⟨28,203341854,203341991⟩,
⟨87,620477578,620477998⟩,
⟨128,904405132,904405744⟩]
theorem checked14544 : checkPrefixCuts (2^48) 1910243329 9 Manual.Count131072.C014544.packed 128 cuts14544 = true := by
 decide +kernel
def pointBounds14544 : List (Nat × Nat × Nat) := [(1910272000,95863506170783,95863883932537),(1910332416,95863923306507,95864301068544)]
theorem point_links_checked14544 : (cuts14544.take 2).map (fun c => (1910243329-1+2*2^9*c.k,95863302828929+c.lower,95863680590546+c.upper)) = pointBounds14544 := by
 decide +kernel
def cuts14545 : List PrefixCut := [⟨18,124207156,124207240⟩,
⟨77,548536029,548536402⟩,
⟨128,907878865,907879485⟩]
theorem checked14545 : checkPrefixCuts (2^48) 1910374401 9 Manual.Count131072.C014545.packed 128 cuts14545 = true := by
 decide +kernel
def pointBounds14545 : List (Nat × Nat × Nat) := [(1910392832,95864331441217,95864709203530),(1910453248,95864755770090,95865133532692)]
theorem point_links_checked14545 : (cuts14545.take 2).map (fun c => (1910374401-1+2*2^9*c.k,95864207234061+c.lower,95864584996290+c.upper)) = pointBounds14545 := by
 decide +kernel
def cuts14546 : List PrefixCut := [⟨8,53922685,53922723⟩,
⟨67,466880600,466880919⟩,
⟨126,884539726,884540337⟩,
⟨128,898977089,898977710⟩]
theorem checked14546 : checkPrefixCuts (2^48) 1910505473 9 Manual.Count131072.C014546.packed 128 cuts14546 = true := by
 decide +kernel
def pointBounds14546 : List (Nat × Nat × Nat) := [(1910513664,95865169035611,95865546798498),(1910574080,95865581993526,95865959756694),(1910634496,95865999652652,95866377416112)]
theorem point_links_checked14546 : (cuts14546.take 3).map (fun c => (1910505473-1+2*2^9*c.k,95865115112926+c.lower,95865492875775+c.upper)) = pointBounds14546 := by
 decide +kernel
def cuts14547 : List PrefixCut := [⟨57,408511917,408512193⟩,
⟨116,824229508,824230061⟩,
⟨128,907017906,907018514⟩]
theorem checked14547 : checkPrefixCuts (2^48) 1910636545 9 Manual.Count131072.C014547.packed 128 cuts14547 = true := by
 decide +kernel
def pointBounds14547 : List (Nat × Nat × Nat) := [(1910694912,95866422601932,95866800365678),(1910755328,95866838319523,95867216083546)]
theorem point_links_checked14547 : (cuts14547.take 2).map (fun c => (1910636545-1+2*2^9*c.k,95866014090015+c.lower,95866391853485+c.upper)) = pointBounds14547 := by
 decide +kernel
def cuts14548 : List PrefixCut := [⟨47,325697975,325698196⟩,
⟨106,742273210,742273714⟩,
⟨128,897380731,897381341⟩]
theorem checked14548 : checkPrefixCuts (2^48) 1910767617 9 Manual.Count131072.C014548.packed 128 cuts14548 = true := by
 decide +kernel
def pointBounds14548 : List (Nat × Nat × Nat) := [(1910815744,95867246805896,95867624570195),(1910876160,95867663381131,95868041145713)]
theorem point_links_checked14548 : (cuts14548.take 2).map (fun c => (1910767617-1+2*2^9*c.k,95866921107921+c.lower,95867298871999+c.upper)) = pointBounds14548 := by
 decide +kernel
def cuts14549 : List PrefixCut := [⟨37,260128774,260128952⟩,
⟨96,677708717,677709180⟩,
⟨128,904389455,904390074⟩]
theorem checked14549 : checkPrefixCuts (2^48) 1910898689 9 Manual.Count131072.C014549.packed 128 cuts14549 = true := by
 decide +kernel
def pointBounds14549 : List (Nat × Nat × Nat) := [(1910936576,95868078617426,95868456382292),(1910996992,95868496197369,95868873962520)]
theorem point_links_checked14549 : (cuts14549.take 2).map (fun c => (1910898689-1+2*2^9*c.k,95867818488652+c.lower,95868196253340+c.upper)) = pointBounds14549 := by
 decide +kernel
def cuts14550 : List PrefixCut := [⟨27,184994465,184994591⟩,
⟨86,609175769,609176179⟩,
⟨128,906831050,906831663⟩]
theorem checked14550 : checkPrefixCuts (2^48) 1911029761 9 Manual.Count131072.C014550.packed 128 cuts14550 = true := by
 decide +kernel
def pointBounds14550 : List (Nat × Nat × Nat) := [(1911057408,95868907872572,95869285638005),(1911117824,95869332053876,95869709819593)]
theorem point_links_checked14550 : (cuts14550.take 2).map (fun c => (1911029761-1+2*2^9*c.k,95868722878107+c.lower,95869100643414+c.upper)) = pointBounds14550 := by
 decide +kernel
def cuts14551 : List PrefixCut := [⟨17,119148594,119148674⟩,
⟨76,524009967,524010322⟩,
⟨128,897343171,897343776⟩]
theorem checked14551 : checkPrefixCuts (2^48) 1911160833 9 Manual.Count131072.C014551.packed 128 cuts14551 = true := by
 decide +kernel
def pointBounds14551 : List (Nat × Nat × Nat) := [(1911178240,95869748857751,95870126623751),(1911238656,95870153719124,95870531485399)]
theorem point_links_checked14551 : (cuts14551.take 2).map (fun c => (1911160833-1+2*2^9*c.k,95869629709157+c.lower,95870007475077+c.upper)) = pointBounds14551 := by
 decide +kernel
def cuts14552 : List PrefixCut := [⟨7,49776978,49777012⟩,
⟨66,466394138,466394449⟩,
⟨125,881525538,881526132⟩,
⟨128,904350754,904351363⟩]
theorem checked14552 : checkPrefixCuts (2^48) 1911291905 9 Manual.Count131072.C014552.packed 128 cuts14552 = true := by
 decide +kernel
def pointBounds14552 : List (Nat × Nat × Nat) := [(1911299072,95870576829306,95870954595865),(1911359488,95870993446466,95871371213302),(1911419904,95871408577866,95871786344985)]
theorem point_links_checked14552 : (cuts14552.take 3).map (fun c => (1911291905-1+2*2^9*c.k,95870527052328+c.lower,95870904818853+c.upper)) = pointBounds14552 := by
 decide +kernel
def cuts14553 : List PrefixCut := [⟨56,400097705,400097977⟩,
⟨115,813435742,813436293⟩,
⟨128,900018604,900019215⟩]
theorem checked14553 : checkPrefixCuts (2^48) 1911422977 9 Manual.Count131072.C014553.packed 128 cuts14553 = true := by
 decide +kernel
def pointBounds14553 : List (Nat × Nat × Nat) := [(1911480320,95871831500787,95872209268193),(1911540736,95872244838824,95872622606509)]
theorem point_links_checked14553 : (cuts14553.take 2).map (fun c => (1911422977-1+2*2^9*c.k,95871431403082+c.lower,95871809170216+c.upper)) = pointBounds14553 := by
 decide +kernel
def cuts14554 : List PrefixCut := [⟨46,329392457,329392674⟩,
⟨105,743440527,743441019⟩,
⟨128,898926017,898926614⟩]
theorem checked14554 : checkPrefixCuts (2^48) 1911554049 9 Manual.Count131072.C014554.packed 128 cuts14554 = true := by
 decide +kernel
def pointBounds14554 : List (Nat × Nat × Nat) := [(1911601152,95872660814143,95873038582105),(1911661568,95873074862213,95873452630450)]
theorem point_links_checked14554 : (cuts14554.take 2).map (fun c => (1911554049-1+2*2^9*c.k,95872331421686+c.lower,95872709189431+c.upper)) = pointBounds14554 := by
 decide +kernel
def cuts14555 : List PrefixCut := [⟨36,253396117,253396288⟩,
⟨95,665651248,665651700⟩,
⟨128,898864143,898864757⟩]
theorem checked14555 : checkPrefixCuts (2^48) 1911685121 9 Manual.Count131072.C014555.packed 128 cuts14555 = true := by
 decide +kernel
def pointBounds14555 : List (Nat × Nat × Nat) := [(1911721984,95873483743820,95873861512333),(1911782400,95873895998951,95874273767745)]
theorem point_links_checked14555 : (cuts14555.take 2).map (fun c => (1911685121-1+2*2^9*c.k,95873230347703+c.lower,95873608116045+c.upper)) = pointBounds14555 := by
 decide +kernel
def cuts14556 : List PrefixCut := [⟨26,183740576,183740699⟩,
⟨85,597294685,597295092⟩,
⟨128,905427502,905428119⟩]
theorem checked14556 : checkPrefixCuts (2^48) 1911816193 9 Manual.Count131072.C014556.packed 128 cuts14556 = true := by
 decide +kernel
def pointBounds14556 : List (Nat × Nat × Nat) := [(1911842816,95874312952422,95874690721501),(1911903232,95874726506531,95875104275894)]
theorem point_links_checked14556 : (cuts14556.take 2).map (fun c => (1911816193-1+2*2^9*c.k,95874129211846+c.lower,95874506980802+c.upper)) = pointBounds14556 := by
 decide +kernel
def cuts14557 : List PrefixCut := [⟨16,108794328,108794403⟩,
⟨75,513931081,513931433⟩,
⟨128,891085558,891086168⟩]
theorem checked14557 : checkPrefixCuts (2^48) 1911947265 9 Manual.Count131072.C014557.packed 128 cuts14557 = true := by
 decide +kernel
def pointBounds14557 : List (Nat × Nat × Nat) := [(1911963648,95875143433676,95875521203324),(1912024064,95875548570429,95875926340354)]
theorem point_links_checked14557 : (cuts14557.take 2).map (fun c => (1911947265-1+2*2^9*c.k,95875034639348+c.lower,95875412408921+c.upper)) = pointBounds14557 := by
 decide +kernel
def cuts14558 : List PrefixCut := [⟨6,44309798,44309828⟩,
⟨65,462963858,462964168⟩,
⟨124,879249567,879250159⟩,
⟨128,906922966,906923577⟩]
theorem checked14558 : checkPrefixCuts (2^48) 1912078337 9 Manual.Count131072.C014558.packed 128 cuts14558 = true := by
 decide +kernel
def pointBounds14558 : List (Nat × Nat × Nat) := [(1912084480,95875970034704,95876347804917),(1912144896,95876388688764,95876766459257),(1912205312,95876804974473,95877182745248)]
theorem point_links_checked14558 : (cuts14558.take 3).map (fun c => (1912078337-1+2*2^9*c.k,95875925724906+c.lower,95876303495089+c.upper)) = pointBounds14558 := by
 decide +kernel
def cuts14559 : List PrefixCut := [⟨55,392131727,392131984⟩,
⟨114,812218041,812218584⟩,
⟨128,913337058,913337668⟩]
theorem checked14559 : checkPrefixCuts (2^48) 1912209409 9 Manual.Count131072.C014559.packed 128 cuts14559 = true := by
 decide +kernel
def pointBounds14559 : List (Nat × Nat × Nat) := [(1912265728,95877224779599,95877602550650),(1912326144,95877644865913,95878022637250)]
theorem point_links_checked14559 : (cuts14559.take 2).map (fun c => (1912209409-1+2*2^9*c.k,95876832647872+c.lower,95877210418666+c.upper)) = pointBounds14559 := by
 decide +kernel
def cuts14560 : List PrefixCut := [⟨45,320720322,320720537⟩,
⟨104,735187111,735187609⟩,
⟨128,902677424,902678035⟩]
theorem checked14560 : checkPrefixCuts (2^48) 1912340481 9 Manual.Count131072.C014560.packed 128 cuts14560 = true := by
 decide +kernel
def pointBounds14560 : List (Nat × Nat × Nat) := [(1912386560,95878066705252,95878444476871),(1912446976,95878481172041,95878858943943)]
theorem point_links_checked14560 : (cuts14560.take 2).map (fun c => (1912340481-1+2*2^9*c.k,95877745984930+c.lower,95878123756334+c.upper)) = pointBounds14560 := by
 decide +kernel
def cuts14561 : List PrefixCut := [⟨35,246374690,246374860⟩,
⟨94,660520949,660521399⟩,
⟨128,902762548,902763162⟩]
theorem checked14561 : checkPrefixCuts (2^48) 1912471553 9 Manual.Count131072.C014561.packed 128 cuts14561 = true := by
 decide +kernel
def pointBounds14561 : List (Nat × Nat × Nat) := [(1912507392,95878895037044,95879272809229),(1912567808,95879309183303,95879686955768)]
theorem point_links_checked14561 : (cuts14561.take 2).map (fun c => (1912471553-1+2*2^9*c.k,95878648662354+c.lower,95879026434369+c.upper)) = pointBounds14561 := by
 decide +kernel
def cuts14562 : List PrefixCut := [⟨25,175570848,175570966⟩,
⟨84,583510114,583510506⟩,
⟨128,889897559,889898162⟩]
theorem checked14562 : checkPrefixCuts (2^48) 1912602625 9 Manual.Count131072.C014562.packed 128 cuts14562 = true := by
 decide +kernel
def pointBounds14562 : List (Nat × Nat × Nat) := [(1912628224,95879726995750,95880104768497),(1912688640,95880134935016,95880512708037)]
theorem point_links_checked14562 : (cuts14562.take 2).map (fun c => (1912602625-1+2*2^9*c.k,95879551424902+c.lower,95879929197531+c.upper)) = pointBounds14562 := by
 decide +kernel
def cuts14563 : List PrefixCut := [⟨15,103746280,103746349⟩,
⟨74,520783250,520783607⟩,
⟨128,907200330,907200950⟩]
theorem checked14563 : checkPrefixCuts (2^48) 1912733697 9 Manual.Count131072.C014563.packed 128 cuts14563 = true := by
 decide +kernel
def pointBounds14563 : List (Nat × Nat × Nat) := [(1912749056,95880545068741,95880922842042),(1912809472,95880962105711,95881339879300)]
theorem point_links_checked14563 : (cuts14563.take 2).map (fun c => (1912733697-1+2*2^9*c.k,95880441322461+c.lower,95880819095693+c.upper)) = pointBounds14563 := by
 decide +kernel
def cuts14564 : List PrefixCut := [⟨5,34726966,34726989⟩,
⟨64,446440293,446440594⟩,
⟨123,864909307,864909886⟩,
⟨128,901105369,901105973⟩]
theorem checked14564 : checkPrefixCuts (2^48) 1912864769 9 Manual.Count131072.C014564.packed 128 cuts14564 = true := by
 decide +kernel
def pointBounds14564 : List (Nat × Nat × Nat) := [(1912869888,95881383249757,95881761023632),(1912930304,95881794963084,95882172737237),(1912990720,95882213432098,95882591206529)]
theorem point_links_checked14564 : (cuts14564.take 3).map (fun c => (1912864769-1+2*2^9*c.k,95881348522791+c.lower,95881726296643+c.upper)) = pointBounds14564 := by
 decide +kernel
def cuts14565 : List PrefixCut := [⟨54,381376786,381377044⟩,
⟨113,799819334,799819874⟩,
⟨128,909283128,909283740⟩]
theorem checked14565 : checkPrefixCuts (2^48) 1912995841 9 Manual.Count131072.C014565.packed 128 cuts14565 = true := by
 decide +kernel
def pointBounds14565 : List (Nat × Nat × Nat) := [(1913051136,95882631004946,95883008779660),(1913111552,95883049447494,95883427222490)]
theorem point_links_checked14565 : (cuts14565.take 2).map (fun c => (1912995841-1+2*2^9*c.k,95882249628160+c.lower,95882627402616+c.upper)) = pointBounds14565 := by
 decide +kernel
def cuts14566 : List PrefixCut := [⟨44,308965502,308965712⟩,
⟨103,728999953,729000451⟩,
⟨128,905837100,905837716⟩]
theorem checked14566 : checkPrefixCuts (2^48) 1913126913 9 Manual.Count131072.C014566.packed 128 cuts14566 = true := by
 decide +kernel
def pointBounds14566 : List (Nat × Nat × Nat) := [(1913171968,95883467876790,95883845652068),(1913232384,95883887911241,95884265686807)]
theorem point_links_checked14566 : (cuts14566.take 2).map (fun c => (1913126913-1+2*2^9*c.k,95883158911288+c.lower,95883536686356+c.upper)) = pointBounds14566 := by
 decide +kernel
def cuts14567 : List PrefixCut := [⟨34,238476343,238476506⟩,
⟨93,643037382,643037820⟩,
⟨128,891063818,891064426⟩]
theorem checked14567 : checkPrefixCuts (2^48) 1913257985 9 Manual.Count131072.C014567.packed 128 cuts14567 = true := by
 decide +kernel
def pointBounds14567 : List (Nat × Nat × Nat) := [(1913292800,95884303224731,95884681000578),(1913353216,95884707785770,95885085561892)]
theorem point_links_checked14567 : (cuts14567.take 2).map (fun c => (1913257985-1+2*2^9*c.k,95884064748388+c.lower,95884442524072+c.upper)) = pointBounds14567 := by
 decide +kernel
def cuts14568 : List PrefixCut := [⟨24,172115259,172115376⟩,
⟨83,586800834,586801232⟩,
⟨128,899976190,899976802⟩]
theorem checked14568 : checkPrefixCuts (2^48) 1913389057 9 Manual.Count131072.C014568.packed 128 cuts14568 = true := by
 decide +kernel
def pointBounds14568 : List (Nat × Nat × Nat) := [(1913413632,95885127927465,95885505703874),(1913474048,95885542613040,95885920389730)]
theorem point_links_checked14568 : (cuts14568.take 2).map (fun c => (1913389057-1+2*2^9*c.k,95884955812206+c.lower,95885333588498+c.upper)) = pointBounds14568 := by
 decide +kernel
def cuts14569 : List PrefixCut := [⟨14,97525576,97525641⟩,
⟨73,518657159,518657502⟩,
⟨128,906386495,906387098⟩]
theorem checked14569 : checkPrefixCuts (2^48) 1913520129 9 Manual.Count131072.C014569.packed 128 cuts14569 = true := by
 decide +kernel
def pointBounds14569 : List (Nat × Nat × Nat) := [(1913534464,95885953313972,95886331090941),(1913594880,95886374445555,95886752222802)]
theorem point_links_checked14569 : (cuts14569.take 2).map (fun c => (1913520129-1+2*2^9*c.k,95885855788396+c.lower,95886233565300+c.upper)) = pointBounds14569 := by
 decide +kernel
def cuts14570 : List PrefixCut := [⟨4,30594243,30594264⟩,
⟨63,446404183,446404486⟩,
⟨122,856612083,856612667⟩,
⟨128,897646851,897647464⟩]
theorem checked14570 : checkPrefixCuts (2^48) 1913651201 9 Manual.Count131072.C014570.packed 128 cuts14570 = true := by
 decide +kernel
def pointBounds14570 : List (Nat × Nat × Nat) := [(1913655296,95886792769134,95887170546662),(1913715712,95887208579074,95887586356884),(1913776128,95887618786974,95887996565065)]
theorem point_links_checked14570 : (cuts14570.take 3).map (fun c => (1913651201-1+2*2^9*c.k,95886762174891+c.lower,95887139952398+c.upper)) = pointBounds14570 := by
 decide +kernel
def cuts14571 : List PrefixCut := [⟨53,371660346,371660597⟩,
⟨112,792137215,792137749⟩,
⟨128,902732614,902733224⟩]
theorem checked14571 : checkPrefixCuts (2^48) 1913782273 9 Manual.Count131072.C014571.packed 128 cuts14571 = true := by
 decide +kernel
def pointBounds14571 : List (Nat × Nat × Nat) := [(1913836544,95888031482088,95888409260459),(1913896960,95888451958957,95888829737611)]
theorem point_links_checked14571 : (cuts14571.take 2).map (fun c => (1913782273-1+2*2^9*c.k,95887659821742+c.lower,95888037599862+c.upper)) = pointBounds14571 := by
 decide +kernel
def cuts14572 : List PrefixCut := [⟨43,305603203,305603408⟩,
⟨102,711494425,711494909⟩,
⟨128,895464833,895465443⟩]
theorem checked14572 : checkPrefixCuts (2^48) 1913913345 9 Manual.Count131072.C014572.packed 128 cuts14572 = true := by
 decide +kernel
def pointBounds14572 : List (Nat × Nat × Nat) := [(1913957376,95888868157559,95889245936494),(1914017792,95889274048781,95889651827995)]
theorem point_links_checked14572 : (cuts14572.take 2).map (fun c => (1913913345-1+2*2^9*c.k,95888562554356+c.lower,95888940333086+c.upper)) = pointBounds14572 := by
 decide +kernel
def cuts14573 : List PrefixCut := [⟨33,233231376,233231531⟩,
⟨92,647331923,647332361⟩,
⟨128,898197540,898198145⟩]
theorem checked14573 : checkPrefixCuts (2^48) 1914044417 9 Manual.Count131072.C014573.packed 128 cuts14573 = true := by
 decide +kernel
def pointBounds14573 : List (Nat × Nat × Nat) := [(1914078208,95889691250565,95890069030060),(1914138624,95890105351112,95890483130890)]
theorem point_links_checked14573 : (cuts14573.take 2).map (fun c => (1914044417-1+2*2^9*c.k,95889458019189+c.lower,95889835798529+c.upper)) = pointBounds14573 := by
 decide +kernel
def cuts14574 : List PrefixCut := [⟨23,161898395,161898507⟩,
⟨82,584207132,584207530⟩,
⟨128,905488114,905488728⟩]
theorem checked14574 : checkPrefixCuts (2^48) 1914175489 9 Manual.Count131072.C014574.packed 128 cuts14574 = true := by
 decide +kernel
def pointBounds14574 : List (Nat × Nat × Nat) := [(1914199040,95890518115124,95890895895181),(1914259456,95890940423861,95891318204204)]
theorem point_links_checked14574 : (cuts14574.take 2).map (fun c => (1914175489-1+2*2^9*c.k,95890356216729+c.lower,95890733996674+c.upper)) = pointBounds14574 := by
 decide +kernel
def cuts14575 : List PrefixCut := [⟨13,92633316,92633378⟩,
⟨72,509916369,509916718⟩,
⟨128,905573169,905573786⟩]
theorem checked14575 : checkPrefixCuts (2^48) 1914306561 9 Manual.Count131072.C014575.packed 128 cuts14575 = true := by
 decide +kernel
def pointBounds14575 : List (Nat × Nat × Nat) := [(1914319872,95891354338159,95891732118780),(1914380288,95891771621212,95892149402120)]
theorem point_links_checked14575 : (cuts14575.take 2).map (fun c => (1914306561-1+2*2^9*c.k,95891261704843+c.lower,95891639485402+c.upper)) = pointBounds14575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000142
