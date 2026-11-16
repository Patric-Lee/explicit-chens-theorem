import PlattAssemblyKernel
import PlattCertificates.Count131072.C013456
import PlattCertificates.Count131072.C013457
import PlattCertificates.Count131072.C013458
import PlattCertificates.Count131072.C013459
import PlattCertificates.Count131072.C013460
import PlattCertificates.Count131072.C013461
import PlattCertificates.Count131072.C013462
import PlattCertificates.Count131072.C013463
import PlattCertificates.Count131072.C013464
import PlattCertificates.Count131072.C013465
import PlattCertificates.Count131072.C013466
import PlattCertificates.Count131072.C013467
import PlattCertificates.Count131072.C013468
import PlattCertificates.Count131072.C013469
import PlattCertificates.Count131072.C013470
import PlattCertificates.Count131072.C013471
import PlattCertificates.Count131072.C013472
import PlattCertificates.Count131072.C013473
import PlattCertificates.Count131072.C013474
import PlattCertificates.Count131072.C013475
import PlattCertificates.Count131072.C013476
import PlattCertificates.Count131072.C013477
import PlattCertificates.Count131072.C013478
import PlattCertificates.Count131072.C013479
import PlattCertificates.Count131072.C013480
import PlattCertificates.Count131072.C013481
import PlattCertificates.Count131072.C013482
import PlattCertificates.Count131072.C013483
import PlattCertificates.Count131072.C013484
import PlattCertificates.Count131072.C013485
import PlattCertificates.Count131072.C013486
import PlattCertificates.Count131072.C013487
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13456 : List PrefixCut := [⟨36,277867272,277867473⟩,
⟨90,676902945,676903431⟩,
⟨128,959054753,959055442⟩]
theorem checked13456 : checkPrefixCuts (2^48) 1767636993 9 Manual.Count131072.C013456.packed 128 cuts13456 = true := by
 decide +kernel
def pointBounds13456 : List (Nat × Nat × Nat) := [(1767673856,94839900553868,94840277605742),(1767729152,94840299589541,94840676641700)]
theorem point_links_checked13456 : (cuts13456.take 2).map (fun c => (1767636993-1+2*2^9*c.k,94839622686596+c.lower,94839999738269+c.upper)) = pointBounds13456 := by
 decide +kernel
def cuts13457 : List PrefixCut := [⟨16,125788076,125788166⟩,
⟨70,537058866,537059249⟩,
⟨124,953411757,953412435⟩,
⟨128,984777016,984777718⟩]
theorem checked13457 : checkPrefixCuts (2^48) 1767768065 9 Manual.Count131072.C013457.packed 128 cuts13457 = true := by
 decide +kernel
def pointBounds13457 : List (Nat × Nat × Nat) := [(1767784448,94840707529425,94841084581877),(1767839744,94841118800215,94841495852960),(1767895040,94841535153106,94841912206146)]
theorem point_links_checked13457 : (cuts13457.take 3).map (fun c => (1767768065-1+2*2^9*c.k,94840581741349+c.lower,94840958793711+c.upper)) = pointBounds13457 := by
 decide +kernel
def cuts13458 : List PrefixCut := [⟨50,379243103,379243373⟩,
⟨104,793181875,793182438⟩,
⟨128,977221252,977221944⟩]
theorem checked13458 : checkPrefixCuts (2^48) 1767899137 9 Manual.Count131072.C013458.packed 128 cuts13458 = true := by
 decide +kernel
def pointBounds13458 : List (Nat × Nat × Nat) := [(1767950336,94841945761468,94842322814802),(1768005632,94842359700240,94842736753867)]
theorem point_links_checked13458 : (cuts13458.take 2).map (fun c => (1767899137-1+2*2^9*c.k,94841566518365+c.lower,94841943571429+c.upper)) = pointBounds13458 := by
 decide +kernel
def cuts13459 : List PrefixCut := [⟨30,226065627,226065785⟩,
⟨84,647142403,647142857⟩,
⟨128,981924724,981925416⟩]
theorem checked13459 : checkPrefixCuts (2^48) 1768030209 9 Manual.Count131072.C013459.packed 128 cuts13459 = true := by
 decide +kernel
def pointBounds13459 : List (Nat × Nat × Nat) := [(1768060928,94842769805244,94843146859158),(1768116224,94843190882020,94843567936230)]
theorem point_links_checked13459 : (cuts13459.take 2).map (fun c => (1768030209-1+2*2^9*c.k,94842543739617+c.lower,94842920793373+c.upper)) = pointBounds13459 := by
 decide +kernel
def cuts13460 : List PrefixCut := [⟨10,78958370,78958424⟩,
⟨64,498735255,498735605⟩,
⟨118,914519586,914520229⟩,
⟨128,992358300,992358998⟩]
theorem checked13460 : checkPrefixCuts (2^48) 1768161281 9 Manual.Count131072.C013460.packed 128 cuts13460 = true := by
 decide +kernel
def pointBounds13460 : List (Nat × Nat × Nat) := [(1768171520,94843604622711,94843981677213),(1768226816,94844024399596,94844401454394),(1768282112,94844440183927,94844817239018)]
theorem point_links_checked13460 : (cuts13460.take 3).map (fun c => (1768161281-1+2*2^9*c.k,94843525664341+c.lower,94843902718789+c.upper)) = pointBounds13460 := by
 decide +kernel
def cuts13461 : List PrefixCut := [⟨44,338887643,338887885⟩,
⟨98,747005605,747006140⟩,
⟨128,975253256,975253952⟩]
theorem checked13461 : checkPrefixCuts (2^48) 1768292353 9 Manual.Count131072.C013461.packed 128 cuts13461 = true := by
 decide +kernel
def pointBounds13461 : List (Nat × Nat × Nat) := [(1768337408,94844856910284,94845233965672),(1768392704,94845265028246,94845642083927)]
theorem point_links_checked13461 : (cuts13461.take 2).map (fun c => (1768292353-1+2*2^9*c.k,94844518022641+c.lower,94844895077787+c.upper)) = pointBounds13461 := by
 decide +kernel
def cuts13462 : List PrefixCut := [⟨24,184791768,184791901⟩,
⟨78,601638217,601638642⟩,
⟨128,993484285,993484986⟩]
theorem checked13462 : checkPrefixCuts (2^48) 1768423425 9 Manual.Count131072.C013462.packed 128 cuts13462 = true := by
 decide +kernel
def pointBounds13462 : List (Nat × Nat × Nat) := [(1768448000,94845678067665,94846055123640),(1768503296,94846094914114,94846471970381)]
theorem point_links_checked13462 : (cuts13462.take 2).map (fun c => (1768423425-1+2*2^9*c.k,94845493275897+c.lower,94845870331739+c.upper)) = pointBounds13462 := by
 decide +kernel
def cuts13463 : List PrefixCut := [⟨4,31671873,31671897⟩,
⟨58,446900609,446900929⟩,
⟨112,863389668,863390284⟩,
⟨128,983861883,983862584⟩]
theorem checked13463 : checkPrefixCuts (2^48) 1768554497 9 Manual.Count131072.C013463.packed 128 cuts13463 = true := by
 decide +kernel
def pointBounds13463 : List (Nat × Nat × Nat) := [(1768558592,94846518432055,94846895488622),(1768613888,94846933660791,94847310717654),(1768669184,94847350149850,94847727207009)]
theorem point_links_checked13463 : (cuts13463.take 3).map (fun c => (1768554497-1+2*2^9*c.k,94846486760182+c.lower,94846863816725+c.upper)) = pointBounds13463 := by
 decide +kernel
def cuts13464 : List PrefixCut := [⟨38,285977781,285977986⟩,
⟨92,691301112,691301606⟩,
⟨128,959281775,959282457⟩]
theorem checked13464 : checkPrefixCuts (2^48) 1768685569 9 Manual.Count131072.C013464.packed 128 cuts13464 = true := by
 decide +kernel
def pointBounds13464 : List (Nat × Nat × Nat) := [(1768724480,94847756599846,94848133657295),(1768779776,94848161923177,94848538980915)]
theorem point_links_checked13464 : (cuts13464.take 2).map (fun c => (1768685569-1+2*2^9*c.k,94847470622065+c.lower,94847847679309+c.upper)) = pointBounds13464 := by
 decide +kernel
def cuts13465 : List PrefixCut := [⟨18,135102146,135102242⟩,
⟨72,546128715,546129104⟩,
⟨126,967008054,967008741⟩,
⟨128,980374138,980374835⟩]
theorem checked13465 : checkPrefixCuts (2^48) 1768816641 9 Manual.Count131072.C013465.packed 128 cuts13465 = true := by
 decide +kernel
def pointBounds13465 : List (Nat × Nat × Nat) := [(1768835072,94848565005986,94848942064008),(1768890368,94848976032555,94849353090870),(1768945664,94849396911894,94849773970507)]
theorem point_links_checked13465 : (cuts13465.take 3).map (fun c => (1768816641-1+2*2^9*c.k,94848429903840+c.lower,94848806961766+c.upper)) = pointBounds13465 := by
 decide +kernel
def cuts13466 : List PrefixCut := [⟨52,387928655,387928930⟩,
⟨106,811168374,811168945⟩,
⟨128,975050849,975051539⟩]
theorem checked13466 : checkPrefixCuts (2^48) 1768947713 9 Manual.Count131072.C013466.packed 128 cuts13466 = true := by
 decide +kernel
def pointBounds13466 : List (Nat × Nat × Nat) := [(1769000960,94849798206633,94850175265531),(1769056256,94850221446352,94850598505546)]
theorem point_links_checked13466 : (cuts13466.take 2).map (fun c => (1768947713-1+2*2^9*c.k,94849410277978+c.lower,94849787336601+c.upper)) = pointBounds13466 := by
 decide +kernel
def cuts13467 : List PrefixCut := [⟨32,242796807,242796984⟩,
⟨86,656304861,656305333⟩,
⟨128,971319545,971320240⟩]
theorem checked13467 : checkPrefixCuts (2^48) 1769078785 9 Manual.Count131072.C013467.packed 128 cuts13467 = true := by
 decide +kernel
def pointBounds13467 : List (Nat × Nat × Nat) := [(1769111552,94850628125634,94851005185124),(1769166848,94851041633688,94851418693473)]
theorem point_links_checked13467 : (cuts13467.take 2).map (fun c => (1769078785-1+2*2^9*c.k,94850385328827+c.lower,94850762388140+c.upper)) = pointBounds13467 := by
 decide +kernel
def cuts13468 : List PrefixCut := [⟨12,92911968,92912034⟩,
⟨66,511644214,511644576⟩,
⟨120,918431751,918432401⟩,
⟨128,983815669,983816365⟩]
theorem checked13468 : checkPrefixCuts (2^48) 1769209857 9 Manual.Count131072.C013468.packed 128 cuts13468 = true := by
 decide +kernel
def pointBounds13468 : List (Nat × Nat × Nat) := [(1769222144,94851449560340,94851826620414),(1769277440,94851868292586,94852245352956),(1769332736,94852275080123,94852652140781)]
theorem point_links_checked13468 : (cuts13468.take 3).map (fun c => (1769209857-1+2*2^9*c.k,94851356648372+c.lower,94851733708380+c.upper)) = pointBounds13468 := by
 decide +kernel
def cuts13469 : List PrefixCut := [⟨46,343140886,343141129⟩,
⟨100,762470117,762470652⟩,
⟨128,974038671,974039359⟩]
theorem checked13469 : checkPrefixCuts (2^48) 1769340929 9 Manual.Count131072.C013469.packed 128 cuts13469 = true := by
 decide +kernel
def pointBounds13469 : List (Nat × Nat × Nat) := [(1769388032,94852683604927,94853060665874),(1769443328,94853102934158,94853479995397)]
theorem point_links_checked13469 : (cuts13469.take 2).map (fun c => (1769340929-1+2*2^9*c.k,94852340464041+c.lower,94852717524745+c.upper)) = pointBounds13469 := by
 decide +kernel
def cuts13470 : List PrefixCut := [⟨26,202339094,202339237⟩,
⟨80,615756664,615757102⟩,
⟨128,987487384,987488086⟩]
theorem checked13470 : checkPrefixCuts (2^48) 1769472001 9 Manual.Count131072.C013470.packed 128 cuts13470 = true := by
 decide +kernel
def pointBounds13470 : List (Nat × Nat × Nat) := [(1769498624,94853516841806,94853893903341),(1769553920,94853930259376,94854307321206)]
theorem point_links_checked13470 : (cuts13470.take 2).map (fun c => (1769472001-1+2*2^9*c.k,94853314502712+c.lower,94853691564104+c.upper)) = pointBounds13470 := by
 decide +kernel
def cuts13471 : List PrefixCut := [⟨7,54716878,54716916⟩,
⟨62,474311473,474311807⟩,
⟨117,887530624,887531247⟩,
⟨128,971031742,971032424⟩]
theorem checked13471 : checkPrefixCuts (2^48) 1769603073 9 Manual.Count131072.C013471.packed 128 cuts13471 = true := by
 decide +kernel
def pointBounds13471 : List (Nat × Nat × Nat) := [(1769610240,94854356706974,94854733769106),(1769666560,94854776301569,94855153363997),(1769722880,94855189520720,94855566583437)]
theorem point_links_checked13471 : (cuts13471.take 3).map (fun c => (1769603073-1+2*2^9*c.k,94854301990096+c.lower,94854679052190+c.upper)) = pointBounds13471 := by
 decide +kernel
def cuts13472 : List PrefixCut := [⟨44,339406716,339406955⟩,
⟨99,756098373,756098909⟩,
⟨128,976685192,976685886⟩]
theorem checked13472 : checkPrefixCuts (2^48) 1769734145 9 Manual.Count131072.C013472.packed 128 cuts13472 = true := by
 decide +kernel
def pointBounds13472 : List (Nat × Nat × Nat) := [(1769779200,94855612428554,94855989491569),(1769835520,94856029120211,94856406183523)]
theorem point_links_checked13472 : (cuts13472.take 2).map (fun c => (1769734145-1+2*2^9*c.k,94855273021838+c.lower,94855650084614+c.upper)) = pointBounds13472 := by
 decide +kernel
def cuts13473 : List PrefixCut := [⟨26,200544749,200544891⟩,
⟨81,622617110,622617554⟩,
⟨128,983292310,983293012⟩]
theorem checked13473 : checkPrefixCuts (2^48) 1769865217 9 Manual.Count131072.C013473.packed 128 cuts13473 = true := by
 decide +kernel
def pointBounds13473 : List (Nat × Nat × Nat) := [(1769891840,94856450251779,94856827315391),(1769948160,94856872324140,94857249388054)]
theorem point_links_checked13473 : (cuts13473.take 2).map (fun c => (1769865217-1+2*2^9*c.k,94856249707030+c.lower,94856626770500+c.upper)) = pointBounds13473 := by
 decide +kernel
def cuts13474 : List PrefixCut := [⟨8,58521320,58521362⟩,
⟨63,474523993,474524335⟩,
⟨118,882244559,882245191⟩,
⟨128,958889478,958890163⟩]
theorem checked13474 : checkPrefixCuts (2^48) 1769996289 9 Manual.Count131072.C013474.packed 128 cuts13474 = true := by
 decide +kernel
def pointBounds13474 : List (Nat × Nat × Nat) := [(1770004480,94857291520660,94857668584874),(1770060800,94857707523333,94858084587847),(1770117120,94858115243899,94858492308703)]
theorem point_links_checked13474 : (cuts13474.take 3).map (fun c => (1769996289-1+2*2^9*c.k,94857232999340+c.lower,94857610063512+c.upper)) = pointBounds13474 := by
 decide +kernel
def cuts13475 : List PrefixCut := [⟨45,341080429,341080669⟩,
⟨100,762767597,762768134⟩,
⟨128,978058234,978058922⟩]
theorem checked13475 : checkPrefixCuts (2^48) 1770127361 9 Manual.Count131072.C013475.packed 128 cuts13475 = true := by
 decide +kernel
def pointBounds13475 : List (Nat × Nat × Nat) := [(1770173440,94858532969247,94858910034344),(1770229760,94858954656415,94859331721809)]
theorem point_links_checked13475 : (cuts13475.take 2).map (fun c => (1770127361-1+2*2^9*c.k,94858191888818+c.lower,94858568953675+c.upper)) = pointBounds13475 := by
 decide +kernel
def cuts13476 : List PrefixCut := [⟨27,207973200,207973350⟩,
⟨82,622319708,622320153⟩,
⟨128,974488049,974488747⟩]
theorem checked13476 : checkPrefixCuts (2^48) 1770258433 9 Manual.Count131072.C013476.packed 128 cuts13476 = true := by
 decide +kernel
def pointBounds13476 : List (Nat × Nat × Nat) := [(1770286080,94859377920252,94859754985947),(1770342400,94859792266760,94860169332750)]
theorem point_links_checked13476 : (cuts13476.take 2).map (fun c => (1770258433-1+2*2^9*c.k,94859169947052+c.lower,94859547012597+c.upper)) = pointBounds13476 := by
 decide +kernel
def cuts13477 : List PrefixCut := [⟨9,69001638,69001688⟩,
⟨64,487137541,487137890⟩,
⟨119,902080354,902080997⟩,
⟨128,970282351,970283042⟩]
theorem checked13477 : checkPrefixCuts (2^48) 1770389505 9 Manual.Count131072.C013477.packed 128 cuts13477 = true := by
 decide +kernel
def pointBounds13477 : List (Nat × Nat × Nat) := [(1770398720,94860213436739,94860590503032),(1770455040,94860631572642,94861008639234),(1770511360,94861046515455,94861423582341)]
theorem point_links_checked13477 : (cuts13477.take 3).map (fun c => (1770389505-1+2*2^9*c.k,94860144435101+c.lower,94860521501344+c.upper)) = pointBounds13477 := by
 decide +kernel
def cuts13478 : List PrefixCut := [⟨46,352609844,352610092⟩,
⟨101,779926177,779926725⟩,
⟨128,986584676,986585368⟩]
theorem checked13478 : checkPrefixCuts (2^48) 1770520577 9 Manual.Count131072.C013478.packed 128 cuts13478 = true := by
 decide +kernel
def pointBounds13478 : List (Nat × Nat × Nat) := [(1770567680,94861467327296,94861844394478),(1770624000,94861894643629,94862271711111)]
theorem point_links_checked13478 : (cuts13478.take 2).map (fun c => (1770520577-1+2*2^9*c.k,94861114717452+c.lower,94861491784386+c.upper)) = pointBounds13478 := by
 decide +kernel
def cuts13479 : List PrefixCut := [⟨28,215239339,215239488⟩,
⟨83,641892580,641893029⟩,
⟨128,995731200,995731899⟩]
theorem checked13479 : checkPrefixCuts (2^48) 1770651649 9 Manual.Count131072.C013479.packed 128 cuts13479 = true := by
 decide +kernel
def pointBounds13479 : List (Nat × Nat × Nat) := [(1770680320,94862316541467,94862693609242),(1770736640,94862743194708,94863120262783)]
theorem point_links_checked13479 : (cuts13479.take 2).map (fun c => (1770651649-1+2*2^9*c.k,94862101302128+c.lower,94862478369754+c.upper)) = pointBounds13479 := by
 decide +kernel
def cuts13480 : List PrefixCut := [⟨10,76775081,76775135⟩,
⟨65,496725229,496725576⟩,
⟨120,912370523,912371166⟩,
⟨128,973563832,973564518⟩]
theorem checked13480 : checkPrefixCuts (2^48) 1770782721 9 Manual.Count131072.C013480.packed 128 cuts13480 = true := by
 decide +kernel
def pointBounds13480 : List (Nat × Nat × Nat) := [(1770792960,94863173808409,94863550876788),(1770849280,94863593758557,94863970827229),(1770905600,94864009403851,94864386472819)]
theorem point_links_checked13480 : (cuts13480.take 3).map (fun c => (1770782721-1+2*2^9*c.k,94863097033328+c.lower,94863474101653+c.upper)) = pointBounds13480 := by
 decide +kernel
def cuts13481 : List PrefixCut := [⟨47,358412212,358412467⟩,
⟨102,784361918,784362475⟩,
⟨128,984299296,984299994⟩]
theorem checked13481 : checkPrefixCuts (2^48) 1770913793 9 Manual.Count131072.C013481.packed 128 cuts13481 = true := by
 decide +kernel
def pointBounds13481 : List (Nat × Nat × Nat) := [(1770961920,94864429009372,94864806078638),(1771018240,94864854959078,94865232028646)]
theorem point_links_checked13481 : (cuts13481.take 2).map (fun c => (1770913793-1+2*2^9*c.k,94864070597160+c.lower,94864447666171+c.upper)) = pointBounds13481 := by
 decide +kernel
def cuts13482 : List PrefixCut := [⟨29,236806015,236806180⟩,
⟨84,662092913,662093379⟩,
⟨128,984545205,984545906⟩]
theorem checked13482 : checkPrefixCuts (2^48) 1771044865 9 Manual.Count131072.C013482.packed 128 cuts13482 = true := by
 decide +kernel
def pointBounds13482 : List (Nat × Nat × Nat) := [(1771074560,94865291702471,94865668772345),(1771130880,94865716989369,94866094059544)]
theorem point_links_checked13482 : (cuts13482.take 2).map (fun c => (1771044865-1+2*2^9*c.k,94865054896456+c.lower,94865431966165+c.upper)) = pointBounds13482 := by
 decide +kernel
def cuts13483 : List PrefixCut := [⟨11,87246672,87246734⟩,
⟨66,508374722,508375084⟩,
⟨121,929966016,929966674⟩,
⟨128,982723589,982724282⟩]
theorem checked13483 : checkPrefixCuts (2^48) 1771175937 9 Manual.Count131072.C013483.packed 128 cuts13483 = true := by
 decide +kernel
def pointBounds13483 : List (Nat × Nat × Nat) := [(1771187200,94866126688333,94866503758805),(1771243520,94866547816383,94866924887155),(1771299840,94866969407677,94867346478745)]
theorem point_links_checked13483 : (cuts13483.take 3).map (fun c => (1771175937-1+2*2^9*c.k,94866039441661+c.lower,94866416512071+c.upper)) = pointBounds13483 := by
 decide +kernel
def cuts13484 : List PrefixCut := [⟨48,358491534,358491794⟩,
⟨103,772905496,772906050⟩,
⟨128,961993402,961994089⟩]
theorem checked13484 : checkPrefixCuts (2^48) 1771307009 9 Manual.Count131072.C013484.packed 128 cuts13484 = true := by
 decide +kernel
def pointBounds13484 : List (Nat × Nat × Nat) := [(1771356160,94867380656784,94867757728147),(1771412480,94867795070746,94868172142403)]
theorem point_links_checked13484 : (cuts13484.take 2).map (fun c => (1771307009-1+2*2^9*c.k,94867022165250+c.lower,94867399236353+c.upper)) = pointBounds13484 := by
 decide +kernel
def cuts13485 : List PrefixCut := [⟨30,231033152,231033316⟩,
⟨85,643514054,643514509⟩,
⟨128,973521263,973521953⟩]
theorem checked13485 : checkPrefixCuts (2^48) 1771438081 9 Manual.Count131072.C013485.packed 128 cuts13485 = true := by
 decide +kernel
def pointBounds13485 : List (Nat × Nat × Nat) := [(1771468800,94868215191804,94868592263758),(1771525120,94868627672706,94869004744951)]
theorem point_links_checked13485 : (cuts13485.take 2).map (fun c => (1771438081-1+2*2^9*c.k,94867984158652+c.lower,94868361230442+c.upper)) = pointBounds13485 := by
 decide +kernel
def cuts13486 : List PrefixCut := [⟨12,94535935,94536003⟩,
⟨67,521131098,521131469⟩,
⟨122,940404439,940405110⟩,
⟨128,985206634,985207335⟩]
theorem checked13486 : checkPrefixCuts (2^48) 1771569153 9 Manual.Count131072.C013486.packed 128 cuts13486 = true := by
 decide +kernel
def pointBounds13486 : List (Nat × Nat × Nat) := [(1771581440,94869052215850,94869429288398),(1771637760,94869478811013,94869855883864),(1771694080,94869898084354,94870275157505)]
theorem point_links_checked13486 : (cuts13486.take 3).map (fun c => (1771569153-1+2*2^9*c.k,94868957679915+c.lower,94869334752395+c.upper)) = pointBounds13486 := by
 decide +kernel
def cuts13487 : List PrefixCut := [⟨49,380653676,380653944⟩,
⟨104,795293258,795293820⟩,
⟨128,981003049,981003742⟩]
theorem checked13487 : checkPrefixCuts (2^48) 1771700225 9 Manual.Count131072.C013487.packed 128 cuts13487 = true := by
 decide +kernel
def pointBounds13487 : List (Nat × Nat × Nat) := [(1771750400,94870323540225,94870700613674),(1771806720,94870738179807,94871115253550)]
theorem point_links_checked13487 : (cuts13487.take 2).map (fun c => (1771700225-1+2*2^9*c.k,94869942886549+c.lower,94870319959730+c.upper)) = pointBounds13487 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000108
