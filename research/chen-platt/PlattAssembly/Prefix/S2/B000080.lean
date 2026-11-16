import PlattAssemblyKernel
import PlattCertificates.Count131072.C012560
import PlattCertificates.Count131072.C012561
import PlattCertificates.Count131072.C012562
import PlattCertificates.Count131072.C012563
import PlattCertificates.Count131072.C012564
import PlattCertificates.Count131072.C012565
import PlattCertificates.Count131072.C012566
import PlattCertificates.Count131072.C012567
import PlattCertificates.Count131072.C012568
import PlattCertificates.Count131072.C012569
import PlattCertificates.Count131072.C012570
import PlattCertificates.Count131072.C012571
import PlattCertificates.Count131072.C012572
import PlattCertificates.Count131072.C012573
import PlattCertificates.Count131072.C012574
import PlattCertificates.Count131072.C012575
import PlattCertificates.Count131072.C012576
import PlattCertificates.Count131072.C012577
import PlattCertificates.Count131072.C012578
import PlattCertificates.Count131072.C012579
import PlattCertificates.Count131072.C012580
import PlattCertificates.Count131072.C012581
import PlattCertificates.Count131072.C012582
import PlattCertificates.Count131072.C012583
import PlattCertificates.Count131072.C012584
import PlattCertificates.Count131072.C012585
import PlattCertificates.Count131072.C012586
import PlattCertificates.Count131072.C012587
import PlattCertificates.Count131072.C012588
import PlattCertificates.Count131072.C012589
import PlattCertificates.Count131072.C012590
import PlattCertificates.Count131072.C012591
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12560 : List PrefixCut := [⟨44,354611256,354611520⟩,
⟨95,773002733,773003308⟩,
⟨128,1049307867,1049308648⟩]
theorem checked12560 : checkPrefixCuts (2^48) 1650196481 9 Manual.Count131072.C012560.packed 128 cuts12560 = true := by
 decide +kernel
def pointBounds12560 : List (Nat × Nat × Nat) := [(1650241536,93929723456724,93930099848043),(1650293760,93930141848201,93930518239831)]
theorem point_links_checked12560 : (cuts12560.take 2).map (fun c => (1650196481-1+2*2^9*c.k,93929368845468+c.lower,93929745236523+c.upper)) = pointBounds12560 := by
 decide +kernel
def cuts12561 : List PrefixCut := [⟨18,143437631,143437738⟩,
⟨69,561973208,561973630⟩,
⟨120,986464544,986465274⟩,
⟨128,1051612300,1051613077⟩]
theorem checked12561 : checkPrefixCuts (2^48) 1650327553 9 Manual.Count131072.C012561.packed 128 cuts12561 = true := by
 decide +kernel
def pointBounds12561 : List (Nat × Nat × Nat) := [(1650345984,93930561590966,93930937982909),(1650398208,93930980126543,93931356518801),(1650450432,93931404617879,93931781010445)]
theorem point_links_checked12561 : (cuts12561.take 3).map (fun c => (1650327553-1+2*2^9*c.k,93930418153335+c.lower,93930794545171+c.upper)) = pointBounds12561 := by
 decide +kernel
def cuts12562 : List PrefixCut := [⟨43,355407799,355408063⟩,
⟨94,772880361,772880934⟩,
⟨128,1056304067,1056304849⟩]
theorem checked12562 : checkPrefixCuts (2^48) 1650458625 9 Manual.Count131072.C012562.packed 128 cuts12562 = true := by
 decide +kernel
def pointBounds12562 : List (Nat × Nat × Nat) := [(1650502656,93931825173434,93932201566311),(1650554880,93932242645996,93932619039182)]
theorem point_links_checked12562 : (cuts12562.take 2).map (fun c => (1650458625-1+2*2^9*c.k,93931469765635+c.lower,93931846158248+c.upper)) = pointBounds12562 := by
 decide +kernel
def cuts12563 : List PrefixCut := [⟨17,135229483,135229582⟩,
⟨68,553187222,553187631⟩,
⟨119,966868750,966869472⟩,
⟨128,1043089773,1043090549⟩]
theorem checked12563 : checkPrefixCuts (2^48) 1650589697 9 Manual.Count131072.C012563.packed 128 cuts12563 = true := by
 decide +kernel
def pointBounds12563 : List (Nat × Nat × Nat) := [(1650607104,93932661299185,93933037692679),(1650659328,93933079256924,93933455650728),(1650711552,93933492938452,93933869332569)]
theorem point_links_checked12563 : (cuts12563.take 3).map (fun c => (1650589697-1+2*2^9*c.k,93932526069702+c.lower,93932902463097+c.upper)) = pointBounds12563 := by
 decide +kernel
def cuts12564 : List PrefixCut := [⟨42,348871973,348872234⟩,
⟨93,779237139,779237717⟩,
⟨128,1065855456,1065856247⟩]
theorem checked12564 : checkPrefixCuts (2^48) 1650720769 9 Manual.Count131072.C012564.packed 128 cuts12564 = true := by
 decide +kernel
def pointBounds12564 : List (Nat × Nat × Nat) := [(1650763776,93933918031448,93934294425880),(1650816000,93934348396614,93934724791363)]
theorem point_links_checked12564 : (cuts12564.take 2).map (fun c => (1650720769-1+2*2^9*c.k,93933569159475+c.lower,93933945553646+c.upper)) = pointBounds12564 := by
 decide +kernel
def cuts12565 : List PrefixCut := [⟨16,130604504,130604601⟩,
⟨67,550542132,550542540⟩,
⟨118,966204122,966204841⟩,
⟨128,1052130973,1052131756⟩]
theorem checked12565 : checkPrefixCuts (2^48) 1650851841 9 Manual.Count131072.C012565.packed 128 cuts12565 = true := by
 decide +kernel
def pointBounds12565 : List (Nat × Nat × Nat) := [(1650868224,93934765619435,93935142014494),(1650920448,93935185557063,93935561952433),(1650972672,93935601219053,93935977614734)]
theorem point_links_checked12565 : (cuts12565.take 3).map (fun c => (1650851841-1+2*2^9*c.k,93934635014931+c.lower,93935011409893+c.upper)) = pointBounds12565 := by
 decide +kernel
def cuts12566 : List PrefixCut := [⟨41,337734933,337735183⟩,
⟨92,752859251,752859811⟩,
⟨128,1045228444,1045229223⟩]
theorem checked12566 : checkPrefixCuts (2^48) 1650982913 9 Manual.Count131072.C012566.packed 128 cuts12566 = true := by
 decide +kernel
def pointBounds12566 : List (Nat × Nat × Nat) := [(1651024896,93936024880837,93936401276832),(1651077120,93936440005155,93936816401460)]
theorem point_links_checked12566 : (cuts12566.take 2).map (fun c => (1650982913-1+2*2^9*c.k,93935687145904+c.lower,93936063541649+c.upper)) = pointBounds12566 := by
 decide +kernel
def cuts12567 : List PrefixCut := [⟨15,123594334,123594426⟩,
⟨66,546193046,546193454⟩,
⟨117,975426553,975427280⟩,
⟨128,1063726270,1063727064⟩]
theorem checked12567 : checkPrefixCuts (2^48) 1651113985 9 Manual.Count131072.C012567.packed 128 cuts12567 = true := by
 decide +kernel
def pointBounds12567 : List (Nat × Nat × Nat) := [(1651129344,93936855968682,93937232365298),(1651181568,93937278567394,93937654964326),(1651233792,93937707800901,93938084198152)]
theorem point_links_checked12567 : (cuts12567.take 3).map (fun c => (1651113985-1+2*2^9*c.k,93936732374348+c.lower,93937108770872+c.upper)) = pointBounds12567 := by
 decide +kernel
def cuts12568 : List PrefixCut := [⟨40,316373860,316374095⟩,
⟨91,735864287,735864833⟩,
⟨128,1041482255,1041483026⟩]
theorem checked12568 : checkPrefixCuts (2^48) 1651245057 9 Manual.Count131072.C012568.packed 128 cuts12568 = true := by
 decide +kernel
def pointBounds12568 : List (Nat × Nat × Nat) := [(1651286016,93938112474478,93938488872031),(1651338240,93938531964905,93938908362769)]
theorem point_links_checked12568 : (cuts12568.take 2).map (fun c => (1651245057-1+2*2^9*c.k,93937796100618+c.lower,93938172497936+c.upper)) = pointBounds12568 := by
 decide +kernel
def cuts12569 : List PrefixCut := [⟨14,114370564,114370651⟩,
⟨65,538266095,538266498⟩,
⟨116,958569019,958569737⟩,
⟨128,1058103514,1058104305⟩]
theorem checked12569 : checkPrefixCuts (2^48) 1651376129 9 Manual.Count131072.C012569.packed 128 cuts12569 = true := by
 decide +kernel
def pointBounds12569 : List (Nat × Nat × Nat) := [(1651390464,93938951953437,93939328351613),(1651442688,93939375848968,93939752247460),(1651494912,93939796151892,93940172550699)]
theorem point_links_checked12569 : (cuts12569.take 3).map (fun c => (1651376129-1+2*2^9*c.k,93938837582873+c.lower,93939213980962+c.upper)) = pointBounds12569 := by
 decide +kernel
def cuts12570 : List PrefixCut := [⟨39,316323837,316324073⟩,
⟨90,732680190,732680737⟩,
⟨128,1041658215,1041658995⟩]
theorem checked12570 : checkPrefixCuts (2^48) 1651507201 9 Manual.Count131072.C012570.packed 128 cuts12570 = true := by
 decide +kernel
def pointBounds12570 : List (Nat × Nat × Nat) := [(1651547136,93940212010224,93940588409340),(1651599360,93940628366577,93941004766004)]
theorem point_links_checked12570 : (cuts12570.take 2).map (fun c => (1651507201-1+2*2^9*c.k,93939895686387+c.lower,93940272085267+c.upper)) = pointBounds12570 := by
 decide +kernel
def cuts12571 : List PrefixCut := [⟨13,109751085,109751168⟩,
⟨64,522161542,522161934⟩,
⟨115,944953985,944954687⟩,
⟨128,1051629876,1051630658⟩]
theorem checked12571 : checkPrefixCuts (2^48) 1651638273 9 Manual.Count131072.C012571.packed 128 cuts12571 = true := by
 decide +kernel
def pointBounds12571 : List (Nat × Nat × Nat) := [(1651651584,93941047095687,93941423495430),(1651703808,93941459506144,93941835906196),(1651756032,93941882298587,93942258698949)]
theorem point_links_checked12571 : (cuts12571.take 3).map (fun c => (1651638273-1+2*2^9*c.k,93940937344602+c.lower,93941313744262+c.upper)) = pointBounds12571 := by
 decide +kernel
def cuts12572 : List PrefixCut := [⟨38,309287096,309287326⟩,
⟨89,725407258,725407797⟩,
⟨128,1044389724,1044390500⟩]
theorem checked12572 : checkPrefixCuts (2^48) 1651769345 9 Manual.Count131072.C012572.packed 128 cuts12572 = true := by
 decide +kernel
def pointBounds12572 : List (Nat × Nat × Nat) := [(1651808256,93942298261574,93942674662246),(1651860480,93942714381736,93943090782717)]
theorem point_links_checked12572 : (cuts12572.take 2).map (fun c => (1651769345-1+2*2^9*c.k,93941988974478+c.lower,93942365374920+c.upper)) = pointBounds12572 := by
 decide +kernel
def cuts12573 : List PrefixCut := [⟨12,98998884,98998957⟩,
⟨63,518671090,518671475⟩,
⟨114,935603674,935604371⟩,
⟨128,1053678253,1053679037⟩]
theorem checked12573 : checkPrefixCuts (2^48) 1651900417 9 Manual.Count131072.C012573.packed 128 cuts12573 = true := by
 decide +kernel
def pointBounds12573 : List (Nat × Nat × Nat) := [(1651912704,93943132363086,93943508764377),(1651964928,93943552035292,93943928436895),(1652017152,93943968967876,93944345369791)]
theorem point_links_checked12573 : (cuts12573.take 3).map (fun c => (1651900417-1+2*2^9*c.k,93943033364202+c.lower,93943409765420+c.upper)) = pointBounds12573 := by
 decide +kernel
def cuts12574 : List PrefixCut := [⟨37,301230147,301230375⟩,
⟨88,718647584,718648121⟩,
⟨128,1050357278,1050358059⟩]
theorem checked12574 : checkPrefixCuts (2^48) 1652031489 9 Manual.Count131072.C012574.packed 128 cuts12574 = true := by
 decide +kernel
def pointBounds12574 : List (Nat × Nat × Nat) := [(1652069376,93944388272602,93944764674832),(1652121600,93944805690039,93945182092578)]
theorem point_links_checked12574 : (cuts12574.take 2).map (fun c => (1652031489-1+2*2^9*c.k,93944087042455+c.lower,93944463444457+c.upper)) = pointBounds12574 := by
 decide +kernel
def cuts12575 : List PrefixCut := [⟨11,94212915,94212984⟩,
⟨62,506663493,506663872⟩,
⟨113,925063537,925064222⟩,
⟨128,1048230058,1048230834⟩]
theorem checked12575 : checkPrefixCuts (2^48) 1652162561 9 Manual.Count131072.C012575.packed 128 cuts12575 = true := by
 decide +kernel
def pointBounds12575 : List (Nat × Nat × Nat) := [(1652173824,93945231612648,93945608015500),(1652226048,93945644063226,93946020466388),(1652278272,93946062463270,93946438866738)]
theorem point_links_checked12575 : (cuts12575.take 3).map (fun c => (1652162561-1+2*2^9*c.k,93945137399733+c.lower,93945513802516+c.upper)) = pointBounds12575 := by
 decide +kernel
def cuts12576 : List PrefixCut := [⟨36,292835367,292835586⟩,
⟨87,707801928,707802454⟩,
⟨128,1038777815,1038778587⟩]
theorem checked12576 : checkPrefixCuts (2^48) 1652293633 9 Manual.Count131072.C012576.packed 128 cuts12576 = true := by
 decide +kernel
def pointBounds12576 : List (Nat × Nat × Nat) := [(1652330496,93946478465158,93946854868936),(1652382720,93946893431719,93947269835804)]
theorem point_links_checked12576 : (cuts12576.take 2).map (fun c => (1652293633-1+2*2^9*c.k,93946185629791+c.lower,93946562033350+c.upper)) = pointBounds12576 := by
 decide +kernel
def cuts12577 : List PrefixCut := [⟨10,82444551,82444614⟩,
⟨61,509478848,509479221⟩,
⟨112,939224948,939225636⟩,
⟨128,1063904924,1063905708⟩]
theorem checked12577 : checkPrefixCuts (2^48) 1652424705 9 Manual.Count131072.C012577.packed 128 cuts12577 = true := by
 decide +kernel
def pointBounds12577 : List (Nat × Nat × Nat) := [(1652434944,93947306852157,93947683256551),(1652487168,93947733886454,93948110291158),(1652539392,93948163632554,93948540037573)]
theorem point_links_checked12577 : (cuts12577.take 3).map (fun c => (1652424705-1+2*2^9*c.k,93947224407606+c.lower,93947600811937+c.upper)) = pointBounds12577 := by
 decide +kernel
def cuts12578 : List PrefixCut := [⟨35,291085664,291085883⟩,
⟨86,713651051,713651581⟩,
⟨128,1052408991,1052409770⟩]
theorem checked12578 : checkPrefixCuts (2^48) 1652555777 9 Manual.Count131072.C012578.packed 128 cuts12578 = true := by
 decide +kernel
def pointBounds12578 : List (Nat × Nat × Nat) := [(1652591616,93948579398194,93948955803528),(1652643840,93949001963581,93949378369226)]
theorem point_links_checked12578 : (cuts12578.take 2).map (fun c => (1652555777-1+2*2^9*c.k,93948288312530+c.lower,93948664717645+c.upper)) = pointBounds12578 := by
 decide +kernel
def cuts12579 : List PrefixCut := [⟨9,76981481,76981539⟩,
⟨60,491345353,491345718⟩,
⟨111,912508325,912509000⟩,
⟨128,1052665955,1052666735⟩]
theorem checked12579 : checkPrefixCuts (2^48) 1652686849 9 Manual.Count131072.C012579.packed 128 cuts12579 = true := by
 decide +kernel
def pointBounds12579 : List (Nat × Nat × Nat) := [(1652696064,93949417703002,93949794108954),(1652748288,93949832066874,93950208473133),(1652800512,93950253229846,93950629636415)]
theorem point_links_checked12579 : (cuts12579.take 3).map (fun c => (1652686849-1+2*2^9*c.k,93949340721521+c.lower,93949717127415+c.upper)) = pointBounds12579 := by
 decide +kernel
def cuts12580 : List PrefixCut := [⟨34,276223628,276223834⟩,
⟨85,685950243,685950755⟩,
⟨128,1039810287,1039811064⟩]
theorem checked12580 : checkPrefixCuts (2^48) 1652817921 9 Manual.Count131072.C012580.packed 128 cuts12580 = true := by
 decide +kernel
def pointBounds12580 : List (Nat × Nat × Nat) := [(1652852736,93950669611104,93951046017984),(1652904960,93951079337719,93951455744905)]
theorem point_links_checked12580 : (cuts12580.take 2).map (fun c => (1652817921-1+2*2^9*c.k,93950393387476+c.lower,93950769794150+c.upper)) = pointBounds12580 := by
 decide +kernel
def cuts12581 : List PrefixCut := [⟨8,66070998,66071048⟩,
⟨59,489735066,489735427⟩,
⟨110,913385650,913386322⟩,
⟨128,1063907804,1063908589⟩]
theorem checked12581 : checkPrefixCuts (2^48) 1652948993 9 Manual.Count131072.C012581.packed 128 cuts12581 = true := by
 decide +kernel
def pointBounds12581 : List (Nat × Nat × Nat) := [(1652957184,93951499268761,93951875676262),(1653009408,93951922932829,93952299340641),(1653061632,93952346583413,93952722991536)]
theorem point_links_checked12581 : (cuts12581.take 3).map (fun c => (1652948993-1+2*2^9*c.k,93951433197763+c.lower,93951809605214+c.upper)) = pointBounds12581 := by
 decide +kernel
def cuts12582 : List PrefixCut := [⟨33,259152810,259153001⟩,
⟨84,676136269,676136769⟩,
⟨128,1031302312,1031303076⟩]
theorem checked12582 : checkPrefixCuts (2^48) 1653080065 9 Manual.Count131072.C012582.packed 128 cuts12582 = true := by
 decide +kernel
def pointBounds12582 : List (Nat × Nat × Nat) := [(1653113856,93952756258377,93953132666804),(1653166080,93953173241836,93953549650572)]
theorem point_links_checked12582 : (cuts12582.take 2).map (fun c => (1653080065-1+2*2^9*c.k,93952497105567+c.lower,93952873513803+c.upper)) = pointBounds12582 := by
 decide +kernel
def cuts12583 : List PrefixCut := [⟨7,58909656,58909701⟩,
⟨58,476547727,476548083⟩,
⟨109,894342887,894343552⟩,
⟨128,1043309005,1043309778⟩]
theorem checked12583 : checkPrefixCuts (2^48) 1653211137 9 Manual.Count131072.C012583.packed 128 cuts12583 = true := by
 decide +kernel
def pointBounds12583 : List (Nat × Nat × Nat) := [(1653218304,93953587317535,93953963726580),(1653270528,93954004955606,93954381364962),(1653322752,93954422750766,93954799160431)]
theorem point_links_checked12583 : (cuts12583.take 3).map (fun c => (1653211137-1+2*2^9*c.k,93953528407879+c.lower,93953904816879+c.upper)) = pointBounds12583 := by
 decide +kernel
def cuts12584 : List PrefixCut := [⟨32,266602580,266602776⟩,
⟨83,684882028,684882533⟩,
⟨128,1058377403,1058378186⟩]
theorem checked12584 : checkPrefixCuts (2^48) 1653342209 9 Manual.Count131072.C012584.packed 128 cuts12584 = true := by
 decide +kernel
def pointBounds12584 : List (Nat × Nat × Nat) := [(1653374976,93954838319464,93955214729433),(1653427200,93955256598912,93955633009190)]
theorem point_links_checked12584 : (cuts12584.take 2).map (fun c => (1653342209-1+2*2^9*c.k,93954571716884+c.lower,93954948126657+c.upper)) = pointBounds12584 := by
 decide +kernel
def cuts12585 : List PrefixCut := [⟨6,51580350,51580388⟩,
⟨57,467450197,467450546⟩,
⟨108,885860235,885860896⟩,
⟨128,1049441713,1049442497⟩]
theorem checked12585 : checkPrefixCuts (2^48) 1653473281 9 Manual.Count131072.C012585.packed 128 cuts12585 = true := by
 decide +kernel
def pointBounds12585 : List (Nat × Nat × Nat) := [(1653479424,93955681674637,93956058085231),(1653531648,93956097544484,93956473955389),(1653583872,93956515954522,93956892365739)]
theorem point_links_checked12585 : (cuts12585.take 3).map (fun c => (1653473281-1+2*2^9*c.k,93955630094287+c.lower,93956006504843+c.upper)) = pointBounds12585 := by
 decide +kernel
def cuts12586 : List PrefixCut := [⟨31,263836938,263837135⟩,
⟨82,680007744,680008248⟩,
⟨128,1051741791,1051742569⟩]
theorem checked12586 : checkPrefixCuts (2^48) 1653604353 9 Manual.Count131072.C012586.packed 128 cuts12586 = true := by
 decide +kernel
def pointBounds12586 : List (Nat × Nat × Nat) := [(1653636096,93956943372938,93957319784475),(1653688320,93957359543744,93957735955588)]
theorem point_links_checked12586 : (cuts12586.take 2).map (fun c => (1653604353-1+2*2^9*c.k,93956679536000+c.lower,93957055947340+c.upper)) = pointBounds12586 := by
 decide +kernel
def cuts12587 : List PrefixCut := [⟨5,40508847,40508878⟩,
⟨56,447632785,447633117⟩,
⟨107,865806663,865807304⟩,
⟨128,1036340185,1036340952⟩]
theorem checked12587 : checkPrefixCuts (2^48) 1653735425 9 Manual.Count131072.C012587.packed 128 cuts12587 = true := by
 decide +kernel
def pointBounds12587 : List (Nat × Nat × Nat) := [(1653740544,93957771786638,93958148198787),(1653792768,93958178910576,93958555323026),(1653844992,93958597084454,93958973497213)]
theorem point_links_checked12587 : (cuts12587.take 3).map (fun c => (1653735425-1+2*2^9*c.k,93957731277791+c.lower,93958107689909+c.upper)) = pointBounds12587 := by
 decide +kernel
def cuts12588 : List PrefixCut := [⟨30,249158833,249159019⟩,
⟨81,668497695,668498194⟩,
⟨128,1049703216,1049703995⟩]
theorem checked12588 : checkPrefixCuts (2^48) 1653866497 9 Manual.Count131072.C012588.packed 128 cuts12588 = true := by
 decide +kernel
def pointBounds12588 : List (Nat × Nat × Nat) := [(1653897216,93959016776809,93959393189880),(1653949440,93959436115671,93959812529055)]
theorem point_links_checked12588 : (cuts12588.take 2).map (fun c => (1653866497-1+2*2^9*c.k,93958767617976+c.lower,93959144030861+c.upper)) = pointBounds12588 := by
 decide +kernel
def cuts12589 : List PrefixCut := [⟨4,32844416,32844440⟩,
⟨55,456751359,456751697⟩,
⟨106,872476771,872477422⟩,
⟨128,1050300456,1050301239⟩]
theorem checked12589 : checkPrefixCuts (2^48) 1653997569 9 Manual.Count131072.C012589.packed 128 cuts12589 = true := by
 decide +kernel
def pointBounds12589 : List (Nat × Nat × Nat) := [(1654001664,93959850165608,93960226579296),(1654053888,93960274072551,93960650486553),(1654106112,93960689797963,93961066212278)]
theorem point_links_checked12589 : (cuts12589.take 3).map (fun c => (1653997569-1+2*2^9*c.k,93959817321192+c.lower,93960193734856+c.upper)) = pointBounds12589 := by
 decide +kernel
def cuts12590 : List PrefixCut := [⟨29,239930564,239930741⟩,
⟨80,664818320,664818814⟩,
⟨128,1060936966,1060937757⟩]
theorem checked12590 : checkPrefixCuts (2^48) 1654128641 9 Manual.Count131072.C012590.packed 128 cuts12590 = true := by
 decide +kernel
def pointBounds12590 : List (Nat × Nat × Nat) := [(1654158336,93961107552212,93961483966836),(1654210560,93961532439968,93961908854909)]
theorem point_links_checked12590 : (cuts12590.take 2).map (fun c => (1654128641-1+2*2^9*c.k,93960867621648+c.lower,93961244036095+c.upper)) = pointBounds12590 := by
 decide +kernel
def cuts12591 : List PrefixCut := [⟨3,25522711,25522730⟩,
⟨54,436091199,436091519⟩,
⟨105,847667572,847668200⟩,
⟨128,1032268714,1032269477⟩]
theorem checked12591 : checkPrefixCuts (2^48) 1654259713 9 Manual.Count131072.C012591.packed 128 cuts12591 = true := by
 decide +kernel
def pointBounds12591 : List (Nat × Nat × Nat) := [(1654262784,93961954081325,93962330496582),(1654315008,93962364649813,93962741065371),(1654367232,93962776226186,93963152642052)]
theorem point_links_checked12591 : (cuts12591.take 3).map (fun c => (1654259713-1+2*2^9*c.k,93961928558614+c.lower,93962304973852+c.upper)) = pointBounds12591 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000080
