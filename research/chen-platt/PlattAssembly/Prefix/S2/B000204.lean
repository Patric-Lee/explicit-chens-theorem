import PlattAssemblyKernel
import PlattCertificates.Count131072.C016528
import PlattCertificates.Count131072.C016529
import PlattCertificates.Count131072.C016530
import PlattCertificates.Count131072.C016531
import PlattCertificates.Count131072.C016532
import PlattCertificates.Count131072.C016533
import PlattCertificates.Count131072.C016534
import PlattCertificates.Count131072.C016535
import PlattCertificates.Count131072.C016536
import PlattCertificates.Count131072.C016537
import PlattCertificates.Count131072.C016538
import PlattCertificates.Count131072.C016539
import PlattCertificates.Count131072.C016540
import PlattCertificates.Count131072.C016541
import PlattCertificates.Count131072.C016542
import PlattCertificates.Count131072.C016543
import PlattCertificates.Count131072.C016544
import PlattCertificates.Count131072.C016545
import PlattCertificates.Count131072.C016546
import PlattCertificates.Count131072.C016547
import PlattCertificates.Count131072.C016548
import PlattCertificates.Count131072.C016549
import PlattCertificates.Count131072.C016550
import PlattCertificates.Count131072.C016551
import PlattCertificates.Count131072.C016552
import PlattCertificates.Count131072.C016553
import PlattCertificates.Count131072.C016554
import PlattCertificates.Count131072.C016555
import PlattCertificates.Count131072.C016556
import PlattCertificates.Count131072.C016557
import PlattCertificates.Count131072.C016558
import PlattCertificates.Count131072.C016559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000204
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16528 : List PrefixCut := [⟨39,242137537,242137689⟩,
⟨106,664408677,664409101⟩,
⟨128,802525789,802526301⟩]
theorem checked16528 : checkPrefixCuts (2^48) 2170290177 9 Manual.Count131072.C016528.packed 128 cuts16528 = true := by
 decide +kernel
def pointBounds16528 : List (Nat × Nat × Nat) := [(2170330112,97539585879694,97539964738672),(2170398720,97540008150834,97540387010084)]
theorem point_links_checked16528 : (cuts16528.take 2).map (fun c => (2170290177-1+2*2^9*c.k,97539343742157+c.lower,97539722600983+c.upper)) = pointBounds16528 := by
 decide +kernel
def cuts16529 : List PrefixCut := [⟨45,274673672,274673842⟩,
⟨112,691212062,691212492⟩,
⟨128,788990334,788990824⟩]
theorem checked16529 : checkPrefixCuts (2^48) 2170421249 9 Manual.Count131072.C016529.packed 128 cuts16529 = true := by
 decide +kernel
def pointBounds16529 : List (Nat × Nat × Nat) := [(2170467328,97540420941618,97540799801126),(2170535936,97540837480008,97541216339776)]
theorem point_links_checked16529 : (cuts16529.take 2).map (fun c => (2170421249-1+2*2^9*c.k,97540146267946+c.lower,97540525127284+c.upper)) = pointBounds16529 := by
 decide +kernel
def cuts16530 : List PrefixCut := [⟨51,313041150,313041353⟩,
⟨118,732795057,732795521⟩,
⟨128,793870283,793870787⟩]
theorem checked16530 : checkPrefixCuts (2^48) 2170552321 9 Manual.Count131072.C016530.packed 128 cuts16530 = true := by
 decide +kernel
def pointBounds16530 : List (Nat × Nat × Nat) := [(2170604544,97541248299430,97541627159461),(2170673152,97541668053337,97542046913629)]
theorem point_links_checked16530 : (cuts16530.take 2).map (fun c => (2170552321-1+2*2^9*c.k,97540935258280+c.lower,97541314118108+c.upper)) = pointBounds16530 := by
 decide +kernel
def cuts16531 : List PrefixCut := [⟨57,353997316,353997539⟩,
⟨124,769705017,769705498⟩,
⟨128,793952070,793952566⟩]
theorem checked16531 : checkPrefixCuts (2^48) 2170683393 9 Manual.Count131072.C016531.packed 128 cuts16531 = true := by
 decide +kernel
def pointBounds16531 : List (Nat × Nat × Nat) := [(2170741760,97542083125879,97542461986434),(2170810368,97542498833580,97542877694393)]
theorem point_links_checked16531 : (cuts16531.take 2).map (fun c => (2170683393-1+2*2^9*c.k,97541729128563+c.lower,97542107988895+c.upper)) = pointBounds16531 := by
 decide +kernel
def cuts16532 : List PrefixCut := [⟨63,398060315,398060562⟩,
⟨128,807518441,807518946⟩]
theorem checked16532 : checkPrefixCuts (2^48) 2170814465 9 Manual.Count131072.C016532.packed 128 cuts16532 = true := by
 decide +kernel
def pointBounds16532 : List (Nat × Nat × Nat) := [(2170878976,97542921140948,97543300002023)]
theorem point_links_checked16532 : (cuts16532.take 1).map (fun c => (2170814465-1+2*2^9*c.k,97542523080633+c.lower,97542901941461+c.upper)) = pointBounds16532 := by
 decide +kernel
def cuts16533 : List PrefixCut := [⟨2,11539329,11539335⟩,
⟨69,418520928,418521194⟩,
⟨128,782835778,782836273⟩]
theorem checked16533 : checkPrefixCuts (2^48) 2170945537 9 Manual.Count131072.C016533.packed 128 cuts16533 = true := by
 decide +kernel
def pointBounds16533 : List (Nat × Nat × Nat) := [(2170947584,97543342138403,97543720999742),(2171016192,97543749120002,97544127981601)]
theorem point_links_checked16533 : (cuts16533.take 2).map (fun c => (2170945537-1+2*2^9*c.k,97543330599074+c.lower,97543709460407+c.upper)) = pointBounds16533 := by
 decide +kernel
def cuts16534 : List PrefixCut := [⟨8,51729297,51729330⟩,
⟨75,465685967,465686259⟩,
⟨128,789011633,789012127⟩]
theorem checked16534 : checkPrefixCuts (2^48) 2171076609 9 Manual.Count131072.C016534.packed 128 cuts16534 = true := by
 decide +kernel
def pointBounds16534 : List (Nat × Nat × Nat) := [(2171084800,97544165164149,97544544026010),(2171153408,97544579120819,97544957982939)]
theorem point_links_checked16534 : (cuts16534.take 2).map (fun c => (2171076609-1+2*2^9*c.k,97544113434852+c.lower,97544492296680+c.upper)) = pointBounds16534 := by
 decide +kernel
def cuts16535 : List PrefixCut := [⟨14,87636200,87636255⟩,
⟨81,496381313,496381623⟩,
⟨128,780019187,780019674⟩]
theorem checked16535 : checkPrefixCuts (2^48) 2171207681 9 Manual.Count131072.C016535.packed 128 cuts16535 = true := by
 decide +kernel
def pointBounds16535 : List (Nat × Nat × Nat) := [(2171222016,97544990082685,97545368945062),(2171290624,97545398827798,97545777690430)]
theorem point_links_checked16535 : (cuts16535.take 2).map (fun c => (2171207681-1+2*2^9*c.k,97544902446485+c.lower,97545281308807+c.upper)) = pointBounds16535 := by
 decide +kernel
def cuts16536 : List PrefixCut := [⟨20,127168332,127168409⟩,
⟨87,533165353,533165691⟩,
⟨128,791897630,791898131⟩]
theorem checked16536 : checkPrefixCuts (2^48) 2171338753 9 Manual.Count131072.C016536.packed 128 cuts16536 = true := by
 decide +kernel
def pointBounds16536 : List (Nat × Nat × Nat) := [(2171359232,97545809634004,97546188496890),(2171427840,97546215631025,97546594494172)]
theorem point_links_checked16536 : (cuts16536.take 2).map (fun c => (2171338753-1+2*2^9*c.k,97545682465672+c.lower,97546061328481+c.upper)) = pointBounds16536 := by
 decide +kernel
def cuts16537 : List PrefixCut := [⟨26,160862559,160862662⟩,
⟨93,576296185,576296551⟩,
⟨128,788220642,788221142⟩]
theorem checked16537 : checkPrefixCuts (2^48) 2171469825 9 Manual.Count131072.C016537.packed 128 cuts16537 = true := by
 decide +kernel
def pointBounds16537 : List (Nat × Nat × Nat) := [(2171496448,97546635225861,97547014089274),(2171565056,97547050659487,97547429523163)]
theorem point_links_checked16537 : (cuts16537.take 2).map (fun c => (2171469825-1+2*2^9*c.k,97546474363302+c.lower,97546853226612+c.upper)) = pointBounds16537 := by
 decide +kernel
def cuts16538 : List PrefixCut := [⟨32,200255670,200255796⟩,
⟨99,618255349,618255740⟩,
⟨128,797505119,797505624⟩]
theorem checked16538 : checkPrefixCuts (2^48) 2171600897 9 Manual.Count131072.C016538.packed 128 cuts16538 = true := by
 decide +kernel
def pointBounds16538 : List (Nat × Nat × Nat) := [(2171633664,97547462839614,97547841703550),(2171702272,97547880839293,97548259703494)]
theorem point_links_checked16538 : (cuts16538.take 2).map (fun c => (2171600897-1+2*2^9*c.k,97547262583944+c.lower,97547641447754+c.upper)) = pointBounds16538 := by
 decide +kernel
def cuts16539 : List PrefixCut := [⟨38,229534558,229534701⟩,
⟨105,642323586,642323992⟩,
⟨128,783200258,783200755⟩]
theorem checked16539 : checkPrefixCuts (2^48) 2171731969 9 Manual.Count131072.C016539.packed 128 cuts16539 = true := by
 decide +kernel
def pointBounds16539 : List (Nat × Nat × Nat) := [(2171770880,97548289623621,97548668488079),(2171839488,97548702412649,97549081277370)]
theorem point_links_checked16539 : (cuts16539.take 2).map (fun c => (2171731969-1+2*2^9*c.k,97548060089063+c.lower,97548438953378+c.upper)) = pointBounds16539 := by
 decide +kernel
def cuts16540 : List PrefixCut := [⟨44,268659423,268659593⟩,
⟨111,684143975,684144414⟩,
⟨128,789114597,789115101⟩]
theorem checked16540 : checkPrefixCuts (2^48) 2171863041 9 Manual.Count131072.C016540.packed 128 cuts16540 = true := by
 decide +kernel
def pointBounds16540 : List (Nat × Nat × Nat) := [(2171908096,97549111948744,97549490813726),(2171976704,97549527433296,97549906298547)]
theorem point_links_checked16540 : (cuts16540.take 2).map (fun c => (2171863041-1+2*2^9*c.k,97548843289321+c.lower,97549222154133+c.upper)) = pointBounds16540 := by
 decide +kernel
def cuts16541 : List PrefixCut := [⟨50,311148687,311148880⟩,
⟨117,727384405,727384862⟩,
⟨128,795027960,795028461⟩]
theorem checked16541 : checkPrefixCuts (2^48) 2171994113 9 Manual.Count131072.C016541.packed 128 cuts16541 = true := by
 decide +kernel
def pointBounds16541 : List (Nat × Nat × Nat) := [(2172045312,97549943552605,97550322418114),(2172113920,97550359788323,97550738654096)]
theorem point_links_checked16541 : (cuts16541.take 2).map (fun c => (2171994113-1+2*2^9*c.k,97549632403918+c.lower,97550011269234+c.upper)) = pointBounds16541 := by
 decide +kernel
def cuts16542 : List PrefixCut := [⟨56,341970273,341970491⟩,
⟨123,747424715,747425194⟩,
⟨128,777486662,777487160⟩]
theorem checked16542 : checkPrefixCuts (2^48) 2172125185 9 Manual.Count131072.C016542.packed 128 cuts16542 = true := by
 decide +kernel
def pointBounds16542 : List (Nat × Nat × Nat) := [(2172182528,97550769402151,97551148268186),(2172251136,97551174856593,97551553722889)]
theorem point_links_checked16542 : (cuts16542.take 2).map (fun c => (2172125185-1+2*2^9*c.k,97550427431878+c.lower,97550806297695+c.upper)) = pointBounds16542 := by
 decide +kernel
def cuts16543 : List PrefixCut := [⟨62,384579480,384579723⟩,
⟨128,787287278,787287776⟩]
theorem checked16543 : checkPrefixCuts (2^48) 2172256257 9 Manual.Count131072.C016543.packed 128 cuts16543 = true := by
 decide +kernel
def pointBounds16543 : List (Nat × Nat × Nat) := [(2172319744,97551589498020,97551968364578)]
theorem point_links_checked16543 : (cuts16543.take 1).map (fun c => (2172256257-1+2*2^9*c.k,97551204918540+c.lower,97551583784855+c.upper)) = pointBounds16543 := by
 decide +kernel
def cuts16544 : List PrefixCut := [⟨1,6219329,6219333⟩,
⟨68,418631948,418632213⟩,
⟨128,782575496,782575988⟩]
theorem checked16544 : checkPrefixCuts (2^48) 2172387329 9 Manual.Count131072.C016544.packed 128 cuts16544 = true := by
 decide +kernel
def pointBounds16544 : List (Nat × Nat × Nat) := [(2172388352,97551998425147,97552377291964),(2172456960,97552410837766,97552789704844)]
theorem point_links_checked16544 : (cuts16544.take 2).map (fun c => (2172387329-1+2*2^9*c.k,97551992205818+c.lower,97552371072631+c.upper)) = pointBounds16544 := by
 decide +kernel
def cuts16545 : List PrefixCut := [⟨7,40811825,40811852⟩,
⟨74,449441166,449441457⟩,
⟨128,779548320,779548824⟩]
theorem checked16545 : checkPrefixCuts (2^48) 2172518401 9 Manual.Count131072.C016545.packed 128 cuts16545 = true := by
 decide +kernel
def pointBounds16545 : List (Nat × Nat × Nat) := [(2172525568,97552815593139,97553194460471),(2172594176,97553224222480,97553603090076)]
theorem point_links_checked16545 : (cuts16545.take 2).map (fun c => (2172518401-1+2*2^9*c.k,97552774781314+c.lower,97553153648619+c.upper)) = pointBounds16545 := by
 decide +kernel
def cuts16546 : List PrefixCut := [⟨13,76566025,76566075⟩,
⟨80,499808819,499809136⟩,
⟨128,792715460,792715962⟩]
theorem checked16546 : checkPrefixCuts (2^48) 2172649473 9 Manual.Count131072.C016546.packed 128 cuts16546 = true := by
 decide +kernel
def pointBounds16546 : List (Nat × Nat × Nat) := [(2172662784,97553630895659,97554009763518),(2172731392,97554054138453,97554433006579)]
theorem point_links_checked16546 : (cuts16546.take 2).map (fun c => (2172649473-1+2*2^9*c.k,97553554329634+c.lower,97553933197443+c.upper)) = pointBounds16546 := by
 decide +kernel
def cuts16547 : List PrefixCut := [⟨19,119699910,119699986⟩,
⟨86,538511567,538511909⟩,
⟨128,798497131,798497637⟩]
theorem checked16547 : checkPrefixCuts (2^48) 2172780545 9 Manual.Count131072.C016547.packed 128 cuts16547 = true := by
 decide +kernel
def pointBounds16547 : List (Nat × Nat × Nat) := [(2172800000,97554466745004,97554845613391),(2172868608,97554885556661,97555264425314)]
theorem point_links_checked16547 : (cuts16547.take 2).map (fun c => (2172780545-1+2*2^9*c.k,97554347045094+c.lower,97554725913405+c.upper)) = pointBounds16547 := by
 decide +kernel
def cuts16548 : List PrefixCut := [⟨25,153242703,153242802⟩,
⟨92,571380265,571380629⟩,
⟨128,794174299,794174805⟩]
theorem checked16548 : checkPrefixCuts (2^48) 2172911617 9 Manual.Count131072.C016548.packed 128 cuts16548 = true := by
 decide +kernel
def pointBounds16548 : List (Nat × Nat × Nat) := [(2172937216,97555298784928,97555677653844),(2173005824,97555716922490,97556095791671)]
theorem point_links_checked16548 : (cuts16548.take 2).map (fun c => (2172911617-1+2*2^9*c.k,97555145542225+c.lower,97555524411042+c.upper)) = pointBounds16548 := by
 decide +kernel
def cuts16549 : List PrefixCut := [⟨31,195459785,195459907⟩,
⟨98,618233821,618234206⟩,
⟨128,806172293,806172797⟩]
theorem checked16549 : checkPrefixCuts (2^48) 2173042689 9 Manual.Count131072.C016549.packed 128 cuts16549 = true := by
 decide +kernel
def pointBounds16549 : List (Nat × Nat × Nat) := [(2173074432,97556135176309,97556514045754),(2173143040,97556557950345,97556936820053)]
theorem point_links_checked16549 : (cuts16549.take 2).map (fun c => (2173042689-1+2*2^9*c.k,97555939716524+c.lower,97556318585847+c.upper)) = pointBounds16549 := by
 decide +kernel
def cuts16550 : List PrefixCut := [⟨37,223424353,223424496⟩,
⟨104,632572323,632572728⟩,
⟨128,777111513,777112008⟩]
theorem checked16550 : checkPrefixCuts (2^48) 2173173761 9 Manual.Count131072.C016550.packed 128 cuts16550 = true := by
 decide +kernel
def pointBounds16550 : List (Nat × Nat × Nat) := [(2173211648,97556969313170,97557348183140),(2173280256,97557378461140,97557757331372)]
theorem point_links_checked16550 : (cuts16550.take 2).map (fun c => (2173173761-1+2*2^9*c.k,97556745888817+c.lower,97557124758644+c.upper)) = pointBounds16550 := by
 decide +kernel
def cuts16551 : List PrefixCut := [⟨43,258897238,258897402⟩,
⟨110,671386584,671387012⟩,
⟨128,786130159,786130659⟩]
theorem checked16551 : checkPrefixCuts (2^48) 2173304833 9 Manual.Count131072.C016551.packed 128 cuts16551 = true := by
 decide +kernel
def pointBounds16551 : List (Nat × Nat × Nat) := [(2173348864,97557781897568,97558160768054),(2173417472,97558194386914,97558573257664)]
theorem point_links_checked16551 : (cuts16551.take 2).map (fun c => (2173304833-1+2*2^9*c.k,97557523000330+c.lower,97557901870652+c.upper)) = pointBounds16551 := by
 decide +kernel
def cuts16552 : List PrefixCut := [⟨49,303172115,303172307⟩,
⟨116,714987970,714988426⟩,
⟨128,790486138,790486641⟩]
theorem checked16552 : checkPrefixCuts (2^48) 2173435905 9 Manual.Count131072.C016552.packed 128 cuts16552 = true := by
 decide +kernel
def pointBounds16552 : List (Nat × Nat × Nat) := [(2173486080,97558612302604,97558991173618),(2173554688,97559024118459,97559402989737)]
theorem point_links_checked16552 : (cuts16552.take 2).map (fun c => (2173435905-1+2*2^9*c.k,97558309130489+c.lower,97558688001311+c.upper)) = pointBounds16552 := by
 decide +kernel
def cuts16553 : List PrefixCut := [⟨55,342132110,342132326⟩,
⟨122,752109025,752109506⟩,
⟨128,790050017,790050521⟩]
theorem checked16553 : checkPrefixCuts (2^48) 2173566977 9 Manual.Count131072.C016553.packed 128 cuts16553 = true := by
 decide +kernel
def pointBounds16553 : List (Nat × Nat × Nat) := [(2173623296,97559441748737,97559820620278),(2173691904,97559851725652,97560230597458)]
theorem point_links_checked16553 : (cuts16553.take 2).map (fun c => (2173566977-1+2*2^9*c.k,97559099616627+c.lower,97559478487952+c.upper)) = pointBounds16553 := by
 decide +kernel
def cuts16554 : List PrefixCut := [⟨61,369821719,369821958⟩,
⟨128,784952146,784952650⟩]
theorem checked16554 : checkPrefixCuts (2^48) 2173698049 9 Manual.Count131072.C016554.packed 128 cuts16554 = true := by
 decide +kernel
def pointBounds16554 : List (Nat × Nat × Nat) := [(2173760512,97560259488363,97560638360431),(2173829120,97560674618790,97561053491123)]
theorem point_links_checked16554 : (cuts16554.take 2).map (fun c => (2173698049-1+2*2^9*c.k,97559889666644+c.lower,97560268538473+c.upper)) = pointBounds16554 := by
 decide +kernel
def cuts16555 : List PrefixCut := [⟨67,412268713,412268980⟩,
⟨128,787624007,787624511⟩]
theorem checked16555 : checkPrefixCuts (2^48) 2173829121 9 Manual.Count131072.C016555.packed 128 cuts16555 = true := by
 decide +kernel
def pointBounds16555 : List (Nat × Nat × Nat) := [(2173897728,97561086887503,97561465760103)]
theorem point_links_checked16555 : (cuts16555.take 1).map (fun c => (2173829121-1+2*2^9*c.k,97560674618790+c.lower,97561053491123+c.upper)) = pointBounds16555 := by
 decide +kernel
def cuts16556 : List PrefixCut := [⟨6,37159457,37159480⟩,
⟨73,457170580,457170864⟩,
⟨128,791719785,791720274⟩]
theorem checked16556 : checkPrefixCuts (2^48) 2173960193 9 Manual.Count131072.C016556.packed 128 cuts16556 = true := by
 decide +kernel
def pointBounds16556 : List (Nat × Nat × Nat) := [(2173966336,97561499402254,97561878275114),(2174034944,97561919413377,97562298286498)]
theorem point_links_checked16556 : (cuts16556.take 2).map (fun c => (2173960193-1+2*2^9*c.k,97561462242797+c.lower,97561841115634+c.upper)) = pointBounds16556 := by
 decide +kernel
def cuts16557 : List PrefixCut := [⟨12,73408053,73408101⟩,
⟨79,488214150,488214461⟩,
⟨128,788694391,788694891⟩]
theorem checked16557 : checkPrefixCuts (2^48) 2174091265 9 Manual.Count131072.C016557.packed 128 cuts16557 = true := by
 decide +kernel
def pointBounds16557 : List (Nat × Nat × Nat) := [(2174103552,97562327370635,97562706244009),(2174172160,97562742176732,97563121050369)]
theorem point_links_checked16557 : (cuts16557.take 2).map (fun c => (2174091265-1+2*2^9*c.k,97562253962582+c.lower,97562632835908+c.upper)) = pointBounds16557 := by
 decide +kernel
def cuts16558 : List PrefixCut := [⟨18,106027314,106027382⟩,
⟨85,519512606,519512940⟩,
⟨128,786316361,786316862⟩]
theorem checked16558 : checkPrefixCuts (2^48) 2174222337 9 Manual.Count131072.C016558.packed 128 cuts16558 = true := by
 decide +kernel
def pointBounds16558 : List (Nat × Nat × Nat) := [(2174240768,97563148684287,97563527558181),(2174309376,97563562169579,97563941043739)]
theorem point_links_checked16558 : (cuts16558.take 2).map (fun c => (2174222337-1+2*2^9*c.k,97563042656973+c.lower,97563421530799+c.upper)) = pointBounds16558 := by
 decide +kernel
def cuts16559 : List PrefixCut := [⟨24,150293197,150293293⟩,
⟨91,570742672,570743034⟩,
⟨128,794812953,794813457⟩]
theorem checked16559 : checkPrefixCuts (2^48) 2174353409 9 Manual.Count131072.C016559.packed 128 cuts16559 = true := by
 decide +kernel
def pointBounds16559 : List (Nat × Nat × Nat) := [(2174377984,97563979266531,97564358140954),(2174446592,97564399716006,97564778590695)]
theorem point_links_checked16559 : (cuts16559.take 2).map (fun c => (2174353409-1+2*2^9*c.k,97563828973334+c.lower,97564207847661+c.upper)) = pointBounds16559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000204
