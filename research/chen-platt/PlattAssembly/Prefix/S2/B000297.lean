import PlattAssemblyKernel
import PlattCertificates.Count131072.C019504
import PlattCertificates.Count131072.C019505
import PlattCertificates.Count131072.C019506
import PlattCertificates.Count131072.C019507
import PlattCertificates.Count131072.C019508
import PlattCertificates.Count131072.C019509
import PlattCertificates.Count131072.C019510
import PlattCertificates.Count131072.C019511
import PlattCertificates.Count131072.C019512
import PlattCertificates.Count131072.C019513
import PlattCertificates.Count131072.C019514
import PlattCertificates.Count131072.C019515
import PlattCertificates.Count131072.C019516
import PlattCertificates.Count131072.C019517
import PlattCertificates.Count131072.C019518
import PlattCertificates.Count131072.C019519
import PlattCertificates.Count131072.C019520
import PlattCertificates.Count131072.C019521
import PlattCertificates.Count131072.C019522
import PlattCertificates.Count131072.C019523
import PlattCertificates.Count131072.C019524
import PlattCertificates.Count131072.C019525
import PlattCertificates.Count131072.C019526
import PlattCertificates.Count131072.C019527
import PlattCertificates.Count131072.C019528
import PlattCertificates.Count131072.C019529
import PlattCertificates.Count131072.C019530
import PlattCertificates.Count131072.C019531
import PlattCertificates.Count131072.C019532
import PlattCertificates.Count131072.C019533
import PlattCertificates.Count131072.C019534
import PlattCertificates.Count131072.C019535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000297
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19504 : List PrefixCut := [⟨43,221408478,221408612⟩,
⟨122,624419284,624419653⟩,
⟨128,656848680,656849068⟩]
theorem checked19504 : checkPrefixCuts (2^48) 2560360449 9 Manual.Count131072.C019504.packed 128 cuts19504 = true := by
 decide +kernel
def pointBounds19504 : List (Nat × Nat × Nat) := [(2560404480,99695451437301,99695831614978),(2560485376,99695854448107,99696234626019)]
theorem point_links_checked19504 : (cuts19504.take 2).map (fun c => (2560360449-1+2*2^9*c.k,99695230028823+c.lower,99695610206366+c.upper)) = pointBounds19504 := by
 decide +kernel
def cuts19505 : List PrefixCut := [⟨73,378373581,378373805⟩,
⟨128,660552651,660553043⟩]
theorem checked19505 : checkPrefixCuts (2^48) 2560491521 9 Manual.Count131072.C019505.packed 128 cuts19505 = true := by
 decide +kernel
def pointBounds19505 : List (Nat × Nat × Nat) := [(2560566272,99696265251084,99696645429239)]
theorem point_links_checked19505 : (cuts19505.take 1).map (fun c => (2560491521-1+2*2^9*c.k,99695886877503+c.lower,99696267055434+c.upper)) = pointBounds19505 := by
 decide +kernel
def cuts19506 : List PrefixCut := [⟨24,121136113,121136184⟩,
⟨103,530703998,530704315⟩,
⟨128,661398061,661398455⟩]
theorem checked19506 : checkPrefixCuts (2^48) 2560622593 9 Manual.Count131072.C019506.packed 128 cuts19506 = true := by
 decide +kernel
def pointBounds19506 : List (Nat × Nat × Nat) := [(2560647168,99696668566267,99697048744661),(2560728064,99697078134152,99697458312792)]
theorem point_links_checked19506 : (cuts19506.take 2).map (fun c => (2560622593-1+2*2^9*c.k,99696547430154+c.lower,99696927608477+c.upper)) = pointBounds19506 := by
 decide +kernel
def cuts19507 : List PrefixCut := [⟨54,276332880,276333042⟩,
⟨128,663452730,663453124⟩]
theorem checked19507 : checkPrefixCuts (2^48) 2560753665 9 Manual.Count131072.C019507.packed 128 cuts19507 = true := by
 decide +kernel
def pointBounds19507 : List (Nat × Nat × Nat) := [(2560808960,99697485161095,99697865339974)]
theorem point_links_checked19507 : (cuts19507.take 1).map (fun c => (2560753665-1+2*2^9*c.k,99697208828215+c.lower,99697589006932+c.upper)) = pointBounds19507 := by
 decide +kernel
def cuts19508 : List PrefixCut := [⟨5,26269216,26269232⟩,
⟨84,435358632,435358892⟩,
⟨128,667705194,667705592⟩]
theorem checked19508 : checkPrefixCuts (2^48) 2560884737 9 Manual.Count131072.C019508.packed 128 cuts19508 = true := by
 decide +kernel
def pointBounds19508 : List (Nat × Nat × Nat) := [(2560889856,99697898550161,99698278729288),(2560970752,99698307639577,99698687818948)]
theorem point_links_checked19508 : (cuts19508.take 2).map (fun c => (2560884737-1+2*2^9*c.k,99697872280945+c.lower,99698252460056+c.upper)) = pointBounds19508 := by
 decide +kernel
def cuts19509 : List PrefixCut := [⟨35,181675818,181675926⟩,
⟨114,589310685,589311041⟩,
⟨128,660747113,660747511⟩]
theorem checked19509 : checkPrefixCuts (2^48) 2561015809 9 Manual.Count131072.C019509.packed 128 cuts19509 = true := by
 decide +kernel
def pointBounds19509 : List (Nat × Nat × Nat) := [(2561051648,99698721661957,99699101841574),(2561132544,99699129296824,99699509476689)]
theorem point_links_checked19509 : (cuts19509.take 2).map (fun c => (2561015809-1+2*2^9*c.k,99698539986139+c.lower,99698920165648+c.upper)) = pointBounds19509 := by
 decide +kernel
def cuts19510 : List PrefixCut := [⟨65,343548864,343549066⟩,
⟨128,668296401,668296796⟩]
theorem checked19510 : checkPrefixCuts (2^48) 2561146881 9 Manual.Count131072.C019510.packed 128 cuts19510 = true := by
 decide +kernel
def pointBounds19510 : List (Nat × Nat × Nat) := [(2561213440,99699544282116,99699924462225)]
theorem point_links_checked19510 : (cuts19510.take 1).map (fun c => (2561146881-1+2*2^9*c.k,99699200733252+c.lower,99699580913159+c.upper)) = pointBounds19510 := by
 decide +kernel
def cuts19511 : List PrefixCut := [⟨16,87696941,87696993⟩,
⟨95,492655735,492656027⟩,
⟨128,662767572,662767966⟩]
theorem checked19511 : checkPrefixCuts (2^48) 2561277953 9 Manual.Count131072.C019511.packed 128 cuts19511 = true := by
 decide +kernel
def pointBounds19511 : List (Nat × Nat × Nat) := [(2561294336,99699956726594,99700336906948),(2561375232,99700361685388,99700741865982)]
theorem point_links_checked19511 : (cuts19511.take 2).map (fun c => (2561277953-1+2*2^9*c.k,99699869029653+c.lower,99700249209955+c.upper)) = pointBounds19511 := by
 decide +kernel
def cuts19512 : List PrefixCut := [⟨46,236922005,236922151⟩,
⟨125,649327497,649327883⟩,
⟨128,664711410,664711804⟩]
theorem checked19512 : checkPrefixCuts (2^48) 2561409025 9 Manual.Count131072.C019512.packed 128 cuts19512 = true := by
 decide +kernel
def pointBounds19512 : List (Nat × Nat × Nat) := [(2561456128,99700768719230,99701148900072),(2561537024,99701181124722,99701561305804)]
theorem point_links_checked19512 : (cuts19512.take 2).map (fun c => (2561409025-1+2*2^9*c.k,99700531797225+c.lower,99700911977921+c.upper)) = pointBounds19512 := by
 decide +kernel
def cuts19513 : List PrefixCut := [⟨76,397448068,397448302⟩,
⟨128,671709879,671710276⟩]
theorem checked19513 : checkPrefixCuts (2^48) 2561540097 9 Manual.Count131072.C019513.packed 128 cuts19513 = true := by
 decide +kernel
def pointBounds19513 : List (Nat × Nat × Nat) := [(2561617920,99701593956703,99701974138027)]
theorem point_links_checked19513 : (cuts19513.take 1).map (fun c => (2561540097-1+2*2^9*c.k,99701196508635+c.lower,99701576689725+c.upper)) = pointBounds19513 := by
 decide +kernel
def cuts19514 : List PrefixCut := [⟨27,139765844,139765925⟩,
⟨106,558615026,558615354⟩,
⟨128,672115146,672115540⟩]
theorem checked19514 : checkPrefixCuts (2^48) 2561671169 9 Manual.Count131072.C019514.packed 128 cuts19514 = true := by
 decide +kernel
def pointBounds19514 : List (Nat × Nat × Nat) := [(2561698816,99702007984358,99702388165926),(2561779712,99702426833540,99702807015355)]
theorem point_links_checked19514 : (cuts19514.take 2).map (fun c => (2561671169-1+2*2^9*c.k,99701868218514+c.lower,99702248400001+c.upper)) = pointBounds19514 := by
 decide +kernel
def cuts19515 : List PrefixCut := [⟨57,298523671,298523853⟩,
⟨128,665378707,665379101⟩]
theorem checked19515 : checkPrefixCuts (2^48) 2561802241 9 Manual.Count131072.C019515.packed 128 cuts19515 = true := by
 decide +kernel
def pointBounds19515 : List (Nat × Nat × Nat) := [(2561860608,99702838857331,99703219039394)]
theorem point_links_checked19515 : (cuts19515.take 1).map (fun c => (2561802241-1+2*2^9*c.k,99702540333660+c.lower,99702920515541+c.upper)) = pointBounds19515 := by
 decide +kernel
def cuts19516 : List PrefixCut := [⟨8,43727455,43727480⟩,
⟨87,461108662,461108932⟩,
⟨128,676331109,676331509⟩]
theorem checked19516 : checkPrefixCuts (2^48) 2561933313 9 Manual.Count131072.C019516.packed 128 cuts19516 = true := by
 decide +kernel
def pointBounds19516 : List (Nat × Nat × Nat) := [(2561941504,99703249439822,99703629622122),(2562022400,99703666821029,99704047003574)]
theorem point_links_checked19516 : (cuts19516.take 2).map (fun c => (2561933313-1+2*2^9*c.k,99703205712367+c.lower,99703585894642+c.upper)) = pointBounds19516 := by
 decide +kernel
def cuts19517 : List PrefixCut := [⟨38,193905883,193906000⟩,
⟨117,606317095,606317459⟩,
⟨128,663662533,663662931⟩]
theorem checked19517 : checkPrefixCuts (2^48) 2562064385 9 Manual.Count131072.C019517.packed 128 cuts19517 = true := by
 decide +kernel
def pointBounds19517 : List (Nat × Nat × Nat) := [(2562103296,99704075949359,99704456132151),(2562184192,99704488360571,99704868543610)]
theorem point_links_checked19517 : (cuts19517.take 2).map (fun c => (2562064385-1+2*2^9*c.k,99703882043476+c.lower,99704262226151+c.upper)) = pointBounds19517 := by
 decide +kernel
def cuts19518 : List PrefixCut := [⟨68,354393657,354393864⟩,
⟨128,662310521,662310915⟩]
theorem checked19518 : checkPrefixCuts (2^48) 2562195457 9 Manual.Count131072.C019518.packed 128 cuts19518 = true := by
 decide +kernel
def pointBounds19518 : List (Nat × Nat × Nat) := [(2562265088,99704900099666,99705280282946)]
theorem point_links_checked19518 : (cuts19518.take 1).map (fun c => (2562195457-1+2*2^9*c.k,99704545706009+c.lower,99704925889082+c.upper)) = pointBounds19518 := by
 decide +kernel
def cuts19519 : List PrefixCut := [⟨19,98426385,98426442⟩,
⟨98,499703827,499704123⟩,
⟨128,654257645,654258035⟩]
theorem checked19519 : checkPrefixCuts (2^48) 2562326529 9 Manual.Count131072.C019519.packed 128 cuts19519 = true := by
 decide +kernel
def pointBounds19519 : List (Nat × Nat × Nat) := [(2562345984,99705306442915,99705686626439),(2562426880,99705707720357,99706087904120)]
theorem point_links_checked19519 : (cuts19519.take 2).map (fun c => (2562326529-1+2*2^9*c.k,99705208016530+c.lower,99705588199997+c.upper)) = pointBounds19519 := by
 decide +kernel
def cuts19520 : List PrefixCut := [⟨49,251763863,251764010⟩,
⟨128,657629268,657629661⟩]
theorem checked19520 : checkPrefixCuts (2^48) 2562457601 9 Manual.Count131072.C019520.packed 128 cuts19520 = true := by
 decide +kernel
def pointBounds19520 : List (Nat × Nat × Nat) := [(2562507776,99706114038038,99706494222042),(2562588672,99706519903443,99706900087693)]
theorem point_links_checked19520 : (cuts19520.take 2).map (fun c => (2562457601-1+2*2^9*c.k,99705862274175+c.lower,99706242458032+c.upper)) = pointBounds19520 := by
 decide +kernel
def cuts19521 : List PrefixCut := [⟨79,406511676,406511920⟩,
⟨128,661439926,661440322⟩]
theorem checked19521 : checkPrefixCuts (2^48) 2562588673 9 Manual.Count131072.C019521.packed 128 cuts19521 = true := by
 decide +kernel
def pointBounds19521 : List (Nat × Nat × Nat) := [(2562669568,99706926415119,99707306599613)]
theorem point_links_checked19521 : (cuts19521.take 1).map (fun c => (2562588673-1+2*2^9*c.k,99706519903443+c.lower,99706900087693+c.upper)) = pointBounds19521 := by
 decide +kernel
def cuts19522 : List PrefixCut := [⟨30,153327973,153328064⟩,
⟨109,565415348,565415690⟩,
⟨128,666348424,666348826⟩]
theorem checked19522 : checkPrefixCuts (2^48) 2562719745 9 Manual.Count131072.C019522.packed 128 cuts19522 = true := by
 decide +kernel
def pointBounds19522 : List (Nat × Nat × Nat) := [(2562750464,99707334671342,99707714856079),(2562831360,99707746758717,99708126943705)]
theorem point_links_checked19522 : (cuts19522.take 2).map (fun c => (2562719745-1+2*2^9*c.k,99707181343369+c.lower,99707561528015+c.upper)) = pointBounds19522 := by
 decide +kernel
def cuts19523 : List PrefixCut := [⟨60,313667369,313667552⟩,
⟨128,663239356,663239746⟩]
theorem checked19523 : checkPrefixCuts (2^48) 2562850817 9 Manual.Count131072.C019523.packed 128 cuts19523 = true := by
 decide +kernel
def pointBounds19523 : List (Nat × Nat × Nat) := [(2562912256,99708161359162,99708541544393)]
theorem point_links_checked19523 : (cuts19523.take 1).map (fun c => (2562850817-1+2*2^9*c.k,99707847691793+c.lower,99708227876841+c.upper)) = pointBounds19523 := by
 decide +kernel
def cuts19524 : List PrefixCut := [⟨11,55021304,55021338⟩,
⟨90,464543767,464544046⟩,
⟨128,671551478,671551876⟩]
theorem checked19524 : checkPrefixCuts (2^48) 2562981889 9 Manual.Count131072.C019524.packed 128 cuts19524 = true := by
 decide +kernel
def pointBounds19524 : List (Nat × Nat × Nat) := [(2562993152,99708565952453,99708946137925),(2563074048,99708975474916,99709355660633)]
theorem point_links_checked19524 : (cuts19524.take 2).map (fun c => (2562981889-1+2*2^9*c.k,99708510931149+c.lower,99708891116587+c.upper)) = pointBounds19524 := by
 decide +kernel
def cuts19525 : List PrefixCut := [⟨41,211287314,211287441⟩,
⟨120,616061952,616062316⟩,
⟨128,656472826,656473213⟩]
theorem checked19525 : checkPrefixCuts (2^48) 2563112961 9 Manual.Count131072.C019525.packed 128 cuts19525 = true := by
 decide +kernel
def pointBounds19525 : List (Nat × Nat × Nat) := [(2563154944,99709393769941,99709773955904),(2563235840,99709798544579,99710178730779)]
theorem point_links_checked19525 : (cuts19525.take 2).map (fun c => (2563112961-1+2*2^9*c.k,99709182482627+c.lower,99709562668463+c.upper)) = pointBounds19525 := by
 decide +kernel
def cuts19526 : List PrefixCut := [⟨71,369072794,369073015⟩,
⟨128,661819840,661820237⟩]
theorem checked19526 : checkPrefixCuts (2^48) 2563244033 9 Manual.Count131072.C019526.packed 128 cuts19526 = true := by
 decide +kernel
def pointBounds19526 : List (Nat × Nat × Nat) := [(2563316736,99710208028247,99710588214691)]
theorem point_links_checked19526 : (cuts19526.take 1).map (fun c => (2563244033-1+2*2^9*c.k,99709838955453+c.lower,99710219141676+c.upper)) = pointBounds19526 := by
 decide +kernel
def cuts19527 : List PrefixCut := [⟨22,112880447,112880514⟩,
⟨101,527938291,527938602⟩,
⟨128,666617373,666617766⟩]
theorem checked19527 : checkPrefixCuts (2^48) 2563375105 9 Manual.Count131072.C019527.packed 128 cuts19527 = true := by
 decide +kernel
def pointBounds19527 : List (Nat × Nat × Nat) := [(2563397632,99710613655740,99710993842427),(2563478528,99711028713584,99711408900515)]
theorem point_links_checked19527 : (cuts19527.take 2).map (fun c => (2563375105-1+2*2^9*c.k,99710500775293+c.lower,99710880961913+c.upper)) = pointBounds19527 := by
 decide +kernel
def cuts19528 : List PrefixCut := [⟨52,270765813,270765979⟩,
⟨128,670645792,670646193⟩]
theorem checked19528 : checkPrefixCuts (2^48) 2563506177 9 Manual.Count131072.C019528.packed 128 cuts19528 = true := by
 decide +kernel
def pointBounds19528 : List (Nat × Nat × Nat) := [(2563559424,99711438158479,99711818345658)]
theorem point_links_checked19528 : (cuts19528.take 1).map (fun c => (2563506177-1+2*2^9*c.k,99711167392666+c.lower,99711547579679+c.upper)) = pointBounds19528 := by
 decide +kernel
def cuts19529 : List PrefixCut := [⟨3,14492948,14492958⟩,
⟨82,428852774,428853029⟩,
⟨128,670282166,670282566⟩]
theorem checked19529 : checkPrefixCuts (2^48) 2563637249 9 Manual.Count131072.C019529.packed 128 cuts19529 = true := by
 decide +kernel
def pointBounds19529 : List (Nat × Nat × Nat) := [(2563640320,99711852531406,99712232718830),(2563721216,99712266891232,99712647078901)]
theorem point_links_checked19529 : (cuts19529.take 2).map (fun c => (2563637249-1+2*2^9*c.k,99711838038458+c.lower,99712218225872+c.upper)) = pointBounds19529 := by
 decide +kernel
def cuts19530 : List PrefixCut := [⟨33,169953062,169953163⟩,
⟨112,577919167,577919512⟩,
⟨128,662233468,662233862⟩]
theorem checked19530 : checkPrefixCuts (2^48) 2563768321 9 Manual.Count131072.C019530.packed 128 cuts19530 = true := by
 decide +kernel
def pointBounds19530 : List (Nat × Nat × Nat) := [(2563802112,99712678273686,99713058461601),(2563883008,99713086239791,99713466427950)]
theorem point_links_checked19530 : (cuts19530.take 2).map (fun c => (2563768321-1+2*2^9*c.k,99712508320624+c.lower,99712888508438+c.upper)) = pointBounds19530 := by
 decide +kernel
def cuts19531 : List PrefixCut := [⟨63,322321522,322321712⟩,
⟨128,662748392,662748781⟩]
theorem checked19531 : checkPrefixCuts (2^48) 2563899393 9 Manual.Count131072.C019531.packed 128 cuts19531 = true := by
 decide +kernel
def pointBounds19531 : List (Nat × Nat × Nat) := [(2563963904,99713492875614,99713873064012)]
theorem point_links_checked19531 : (cuts19531.take 1).map (fun c => (2563899393-1+2*2^9*c.k,99713170554092+c.lower,99713550742300+c.upper)) = pointBounds19531 := by
 decide +kernel
def cuts19532 : List PrefixCut := [⟨14,73990363,73990407⟩,
⟨93,479502751,479503036⟩,
⟨128,665129694,665130090⟩]
theorem checked19532 : checkPrefixCuts (2^48) 2564030465 9 Manual.Count131072.C019532.packed 128 cuts19532 = true := by
 decide +kernel
def pointBounds19532 : List (Nat × Nat × Nat) := [(2564044800,99713907292847,99714287481488),(2564125696,99714312805235,99714692994117)]
theorem point_links_checked19532 : (cuts19532.take 2).map (fun c => (2564030465-1+2*2^9*c.k,99713833302484+c.lower,99714213491081+c.upper)) = pointBounds19532 := by
 decide +kernel
def cuts19533 : List PrefixCut := [⟨44,223495232,223495369⟩,
⟨123,639958915,639959300⟩,
⟨128,667620247,667620647⟩]
theorem checked19533 : checkPrefixCuts (2^48) 2564161537 9 Manual.Count131072.C019533.packed 128 cuts19533 = true := by
 decide +kernel
def pointBounds19533 : List (Nat × Nat × Nat) := [(2564206592,99714721927410,99715102116540),(2564287488,99715138391093,99715518580471)]
theorem point_links_checked19533 : (cuts19533.take 2).map (fun c => (2564161537-1+2*2^9*c.k,99714498432178+c.lower,99714878621171+c.upper)) = pointBounds19533 := by
 decide +kernel
def cuts19534 : List PrefixCut := [⟨74,389118509,389118732⟩,
⟨128,670879193,670879582⟩]
theorem checked19534 : checkPrefixCuts (2^48) 2564292609 9 Manual.Count131072.C019534.packed 128 cuts19534 = true := by
 decide +kernel
def pointBounds19534 : List (Nat × Nat × Nat) := [(2564368384,99715555170934,99715935360550)]
theorem point_links_checked19534 : (cuts19534.take 1).map (fun c => (2564292609-1+2*2^9*c.k,99715166052425+c.lower,99715546241818+c.upper)) = pointBounds19534 := by
 decide +kernel
def cuts19535 : List PrefixCut := [⟨25,131932622,131932698⟩,
⟨104,538039541,538039855⟩,
⟨128,664039875,664040262⟩]
theorem checked19535 : checkPrefixCuts (2^48) 2564423681 9 Manual.Count131072.C019535.packed 128 cuts19535 = true := by
 decide +kernel
def pointBounds19535 : List (Nat × Nat × Nat) := [(2564449280,99715968864240,99716349054098),(2564530176,99716374971159,99716755161255)]
theorem point_links_checked19535 : (cuts19535.take 2).map (fun c => (2564423681-1+2*2^9*c.k,99715836931618+c.lower,99716217121400+c.upper)) = pointBounds19535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000297
