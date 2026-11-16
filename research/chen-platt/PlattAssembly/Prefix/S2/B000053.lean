import PlattAssemblyKernel
import PlattCertificates.Count131072.C011696
import PlattCertificates.Count131072.C011697
import PlattCertificates.Count131072.C011698
import PlattCertificates.Count131072.C011699
import PlattCertificates.Count131072.C011700
import PlattCertificates.Count131072.C011701
import PlattCertificates.Count131072.C011702
import PlattCertificates.Count131072.C011703
import PlattCertificates.Count131072.C011704
import PlattCertificates.Count131072.C011705
import PlattCertificates.Count131072.C011706
import PlattCertificates.Count131072.C011707
import PlattCertificates.Count131072.C011708
import PlattCertificates.Count131072.C011709
import PlattCertificates.Count131072.C011710
import PlattCertificates.Count131072.C011711
import PlattCertificates.Count131072.C011712
import PlattCertificates.Count131072.C011713
import PlattCertificates.Count131072.C011714
import PlattCertificates.Count131072.C011715
import PlattCertificates.Count131072.C011716
import PlattCertificates.Count131072.C011717
import PlattCertificates.Count131072.C011718
import PlattCertificates.Count131072.C011719
import PlattCertificates.Count131072.C011720
import PlattCertificates.Count131072.C011721
import PlattCertificates.Count131072.C011722
import PlattCertificates.Count131072.C011723
import PlattCertificates.Count131072.C011724
import PlattCertificates.Count131072.C011725
import PlattCertificates.Count131072.C011726
import PlattCertificates.Count131072.C011727
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11696 : List PrefixCut := [⟨43,378175759,378176051⟩,
⟨90,800474549,800475167⟩,
⟨128,1138706887,1138707772⟩]
theorem checked11696 : checkPrefixCuts (2^48) 1536950273 9 Manual.Count131072.C011696.packed 128 cuts11696 = true := by
 decide +kernel
def pointBounds11696 : List (Nat × Nat × Nat) := [(1536994304,92985358634587,92985734308021),(1537042432,92985780933377,92986156607137)]
theorem point_links_checked11696 : (cuts11696.take 2).map (fun c => (1536950273-1+2*2^9*c.k,92984980458828+c.lower,92985356131970+c.upper)) = pointBounds11696 := by
 decide +kernel
def cuts11697 : List PrefixCut := [⟨9,79108881,79108944⟩,
⟨56,495155176,495155559⟩,
⟨103,916681896,916682601⟩,
⟨128,1135863183,1135864059⟩]
theorem checked11697 : checkPrefixCuts (2^48) 1537081345 9 Manual.Count131072.C011697.packed 128 cuts11697 = true := by
 decide +kernel
def pointBounds11697 : List (Nat × Nat × Nat) := [(1537090560,92986198274596,92986573948686),(1537138688,92986614320891,92986989995301),(1537186816,92987035847611,92987411522343)]
theorem point_links_checked11697 : (cuts11697.take 3).map (fun c => (1537081345-1+2*2^9*c.k,92986119165715+c.lower,92986494839742+c.upper)) = pointBounds11697 := by
 decide +kernel
def cuts11698 : List PrefixCut := [⟨22,197388241,197388396⟩,
⟨69,622184430,622184913⟩,
⟨116,1042572943,1042573757⟩,
⟨128,1150414384,1150415283⟩]
theorem checked11698 : checkPrefixCuts (2^48) 1537212417 9 Manual.Count131072.C011698.packed 128 cuts11698 = true := by
 decide +kernel
def pointBounds11698 : List (Nat × Nat × Nat) := [(1537234944,92987452417139,92987828092197),(1537283072,92987877213328,92988252888714),(1537331200,92988297601841,92988673277558)]
theorem point_links_checked11698 : (cuts11698.take 3).map (fun c => (1537212417-1+2*2^9*c.k,92987255028898+c.lower,92987630703801+c.upper)) = pointBounds11698 := by
 decide +kernel
def cuts11699 : List PrefixCut := [⟨35,311984625,311984865⟩,
⟨82,723741846,723742400⟩,
⟨128,1124318494,1124319362⟩]
theorem checked11699 : checkPrefixCuts (2^48) 1537343489 9 Manual.Count131072.C011699.packed 128 cuts11699 = true := by
 decide +kernel
def pointBounds11699 : List (Nat × Nat × Nat) := [(1537379328,92988717427907,92989093103949),(1537427456,92989129185128,92989504861484)]
theorem point_links_checked11699 : (cuts11699.take 2).map (fun c => (1537343489-1+2*2^9*c.k,92988405443282+c.lower,92988781119084+c.upper)) = pointBounds11699 := by
 decide +kernel
def cuts11700 : List PrefixCut := [⟨1,8604574,8604581⟩,
⟨48,415209992,415210322⟩,
⟨95,840109485,840110142⟩,
⟨128,1132826395,1132827280⟩]
theorem checked11700 : checkPrefixCuts (2^48) 1537474561 9 Manual.Count131072.C011700.packed 128 cuts11700 = true := by
 decide +kernel
def pointBounds11700 : List (Nat × Nat × Nat) := [(1537475584,92989538366350,92989914043027),(1537523712,92989944971768,92990320648768),(1537571840,92990369871261,92990745548588)]
theorem point_links_checked11700 : (cuts11700.take 3).map (fun c => (1537474561-1+2*2^9*c.k,92989529761776+c.lower,92989905438446+c.upper)) = pointBounds11700 := by
 decide +kernel
def cuts11701 : List PrefixCut := [⟨14,118805710,118805804⟩,
⟨61,531962976,531963388⟩,
⟨108,951880171,951880910⟩,
⟨128,1126872266,1126873142⟩]
theorem checked11701 : checkPrefixCuts (2^48) 1537605633 9 Manual.Count131072.C011701.packed 128 cuts11701 = true := by
 decide +kernel
def pointBounds11701 : List (Nat × Nat × Nat) := [(1537619968,92990781393881,92991157071530),(1537668096,92991194551147,92991570229114),(1537716224,92991614468342,92991990146636)]
theorem point_links_checked11701 : (cuts11701.take 3).map (fun c => (1537605633-1+2*2^9*c.k,92990662588171+c.lower,92991038265726+c.upper)) = pointBounds11701 := by
 decide +kernel
def cuts11702 : List PrefixCut := [⟨27,237773193,237773376⟩,
⟨74,653820305,653820809⟩,
⟨121,1071501610,1071502441⟩,
⟨128,1130071130,1130072008⟩]
theorem checked11702 : checkPrefixCuts (2^48) 1537736705 9 Manual.Count131072.C011702.packed 128 cuts11702 = true := by
 decide +kernel
def pointBounds11702 : List (Nat × Nat × Nat) := [(1537764352,92992027233630,92992402912244),(1537812480,92992443280742,92992818959677),(1537860608,92992860962047,92993236641309)]
theorem point_links_checked11702 : (cuts11702.take 3).map (fun c => (1537736705-1+2*2^9*c.k,92991789460437+c.lower,92992165138868+c.upper)) = pointBounds11702 := by
 decide +kernel
def cuts11703 : List PrefixCut := [⟨40,353424911,353425186⟩,
⟨87,779865122,779865728⟩,
⟨128,1131805238,1131806117⟩]
theorem checked11703 : checkPrefixCuts (2^48) 1537867777 9 Manual.Count131072.C011703.packed 128 cuts11703 = true := by
 decide +kernel
def pointBounds11703 : List (Nat × Nat × Nat) := [(1537908736,92993272956478,92993648636062),(1537956864,92993699396689,92994075076604)]
theorem point_links_checked11703 : (cuts11703.take 2).map (fun c => (1537867777-1+2*2^9*c.k,92992919531567+c.lower,92993295210876+c.upper)) = pointBounds11703 := by
 decide +kernel
def cuts11704 : List PrefixCut := [⟨6,54720991,54721034⟩,
⟨53,468140807,468141169⟩,
⟨100,883743794,883744477⟩,
⟨128,1126218568,1126219439⟩]
theorem checked11704 : checkPrefixCuts (2^48) 1537998849 9 Manual.Count131072.C011704.packed 128 cuts11704 = true := by
 decide +kernel
def pointBounds11704 : List (Nat × Nat × Nat) := [(1538004992,92994106057796,92994481738027),(1538053120,92994519477612,92994895158162),(1538101248,92994935080599,92995310761470)]
theorem point_links_checked11704 : (cuts11704.take 3).map (fun c => (1537998849-1+2*2^9*c.k,92994051336805+c.lower,92994427016993+c.upper)) = pointBounds11704 := by
 decide +kernel
def cuts11705 : List PrefixCut := [⟨19,172017159,172017293⟩,
⟨66,589607108,589607566⟩,
⟨113,995472828,995473607⟩,
⟨128,1133076356,1133077244⟩]
theorem checked11705 : checkPrefixCuts (2^48) 1538129921 9 Manual.Count131072.C011705.packed 128 cuts11705 = true := by
 decide +kernel
def pointBounds11705 : List (Nat × Nat × Nat) := [(1538149376,92995349572532,92995725253725),(1538197504,92995767162481,92996142843998),(1538245632,92996173028201,92996548710039)]
theorem point_links_checked11705 : (cuts11705.take 3).map (fun c => (1538129921-1+2*2^9*c.k,92995177555373+c.lower,92995553236432+c.upper)) = pointBounds11705 := by
 decide +kernel
def cuts11706 : List PrefixCut := [⟨32,277947444,277947660⟩,
⟨79,697693804,697694345⟩,
⟨126,1109742378,1109743244⟩,
⟨128,1128405016,1128405897⟩]
theorem checked11706 : checkPrefixCuts (2^48) 1538260993 9 Manual.Count131072.C011706.packed 128 cuts11706 = true := by
 decide +kernel
def pointBounds11706 : List (Nat × Nat × Nat) := [(1538293760,92996588579173,92996964261336),(1538341888,92997008325533,92997384008021),(1538390016,92997420374107,92997796056920)]
theorem point_links_checked11706 : (cuts11706.take 3).map (fun c => (1538260993-1+2*2^9*c.k,92996310631729+c.lower,92996686313676+c.upper)) = pointBounds11706 := by
 decide +kernel
def cuts11707 : List PrefixCut := [⟨45,397947101,397947410⟩,
⟨92,811982269,811982903⟩,
⟨128,1130321456,1130322339⟩]
theorem checked11707 : checkPrefixCuts (2^48) 1538392065 9 Manual.Count131072.C011707.packed 128 cuts11707 = true := by
 decide +kernel
def pointBounds11707 : List (Nat × Nat × Nat) := [(1538438144,92997836983846,92998212666983),(1538486272,92998251019014,92998626702476)]
theorem point_links_checked11707 : (cuts11707.take 2).map (fun c => (1538392065-1+2*2^9*c.k,92997439036745+c.lower,92997814719573+c.upper)) = pointBounds11707 := by
 decide +kernel
def cuts11708 : List PrefixCut := [⟨11,99342213,99342290⟩,
⟨58,518839960,518840362⟩,
⟨105,925884714,925885433⟩,
⟨128,1125835030,1125835904⟩]
theorem checked11708 : checkPrefixCuts (2^48) 1538523137 9 Manual.Count131072.C011708.packed 128 cuts11708 = true := by
 decide +kernel
def pointBounds11708 : List (Nat × Nat × Nat) := [(1538534400,92998668700414,92999044384202),(1538582528,92999088198161,92999463882274),(1538630656,92999495242915,92999870927345)]
theorem point_links_checked11708 : (cuts11708.take 3).map (fun c => (1538523137-1+2*2^9*c.k,92998569358201+c.lower,92998945041912+c.upper)) = pointBounds11708 := by
 decide +kernel
def cuts11709 : List PrefixCut := [⟨24,216411269,216411437⟩,
⟨71,634223390,634223887⟩,
⟨118,1047815175,1047815990⟩,
⟨128,1135800073,1135800957⟩]
theorem checked11709 : checkPrefixCuts (2^48) 1538654209 9 Manual.Count131072.C011709.packed 128 cuts11709 = true := by
 decide +kernel
def pointBounds11709 : List (Nat × Nat × Nat) := [(1538678784,92999911604500,93000287289253),(1538726912,93000329416621,93000705101703),(1538775040,93000743008406,93001118693806)]
theorem point_links_checked11709 : (cuts11709.take 3).map (fun c => (1538654209-1+2*2^9*c.k,92999695193231+c.lower,93000070877816+c.upper)) = pointBounds11709 := by
 decide +kernel
def cuts11710 : List PrefixCut := [⟨37,328337740,328337996⟩,
⟨84,750134629,750135211⟩,
⟨128,1132227866,1132228744⟩]
theorem checked11710 : checkPrefixCuts (2^48) 1538785281 9 Manual.Count131072.C011710.packed 128 cuts11710 = true := by
 decide +kernel
def pointBounds11710 : List (Nat × Nat × Nat) := [(1538823168,93001159331044,93001535016769),(1538871296,93001581127933,93001956813984)]
theorem point_links_checked11710 : (cuts11710.take 2).map (fun c => (1538785281-1+2*2^9*c.k,93000830993304+c.lower,93001206678773+c.upper)) = pointBounds11710 := by
 decide +kernel
def cuts11711 : List PrefixCut := [⟨3,28533088,28533110⟩,
⟨50,444450713,444451061⟩,
⟨97,864013247,864013921⟩,
⟨128,1138349583,1138350472⟩]
theorem checked11711 : checkPrefixCuts (2^48) 1538916353 9 Manual.Count131072.C011711.packed 128 cuts11711 = true := by
 decide +kernel
def pointBounds11711 : List (Nat × Nat × Nat) := [(1538919424,93001991754258,93002367440627),(1538967552,93002407671883,93002783358578),(1539015680,93002827234417,93003202921438)]
theorem point_links_checked11711 : (cuts11711.take 3).map (fun c => (1538916353-1+2*2^9*c.k,93001963221170+c.lower,93002338907517+c.upper)) = pointBounds11711 := by
 decide +kernel
def cuts11712 : List PrefixCut := [⟨16,141372447,141372556⟩,
⟨63,557068195,557068630⟩,
⟨110,971470893,971471655⟩,
⟨128,1130937484,1130938372⟩]
theorem checked11712 : checkPrefixCuts (2^48) 1539047425 9 Manual.Count131072.C011712.packed 128 cuts11712 = true := by
 decide +kernel
def pointBounds11712 : List (Nat × Nat × Nat) := [(1539063808,93003242943200,93003618630545),(1539111936,93003658638948,93004034326619),(1539160064,93004073041646,93004448729644)]
theorem point_links_checked11712 : (cuts11712.take 3).map (fun c => (1539047425-1+2*2^9*c.k,93003101570753+c.lower,93003477257989+c.upper)) = pointBounds11712 := by
 decide +kernel
def cuts11713 : List PrefixCut := [⟨29,251082842,251083038⟩,
⟨76,671676981,671677502⟩,
⟨123,1080737777,1080738615⟩,
⟨128,1126452321,1126453195⟩]
theorem checked11713 : checkPrefixCuts (2^48) 1539178497 9 Manual.Count131072.C011713.packed 128 cuts11713 = true := by
 decide +kernel
def pointBounds11713 : List (Nat × Nat × Nat) := [(1539208192,93004483591079,93004859279399),(1539256320,93004904185218,93005279873863),(1539304448,93005313246014,93005688934976)]
theorem point_links_checked11713 : (cuts11713.take 3).map (fun c => (1539178497-1+2*2^9*c.k,93004232508237+c.lower,93004608196361+c.upper)) = pointBounds11713 := by
 decide +kernel
def cuts11714 : List PrefixCut := [⟨42,374487632,374487923⟩,
⟨89,786996944,786997556⟩,
⟨128,1126905205,1126906080⟩]
theorem checked11714 : checkPrefixCuts (2^48) 1539309569 9 Manual.Count131072.C011714.packed 128 cuts11714 = true := by
 decide +kernel
def pointBounds11714 : List (Nat × Nat × Nat) := [(1539352576,93005733448190,93006109137479),(1539400704,93006145957502,93006521647112)]
theorem point_links_checked11714 : (cuts11714.take 2).map (fun c => (1539309569-1+2*2^9*c.k,93005358960558+c.lower,93005734649556+c.upper)) = pointBounds11714 := by
 decide +kernel
def cuts11715 : List PrefixCut := [⟨8,75513673,75513731⟩,
⟨55,495859343,495859730⟩,
⟨102,919299907,919300622⟩,
⟨128,1150212027,1150212922⟩]
theorem checked11715 : checkPrefixCuts (2^48) 1539440641 9 Manual.Count131072.C011715.packed 128 cuts11715 = true := by
 decide +kernel
def pointBounds11715 : List (Nat × Nat × Nat) := [(1539448832,93006561379436,93006937069367),(1539496960,93006981725106,93007357415366),(1539545088,93007405165670,93007780856258)]
theorem point_links_checked11715 : (cuts11715.take 3).map (fun c => (1539440641-1+2*2^9*c.k,93006485865763+c.lower,93006861555636+c.upper)) = pointBounds11715 := by
 decide +kernel
def cuts11716 : List PrefixCut := [⟨21,186481999,186482142⟩,
⟨68,596367383,596367843⟩,
⟨115,1023607442,1023608229⟩,
⟨128,1135488368,1135489239⟩]
theorem checked11716 : checkPrefixCuts (2^48) 1539571713 9 Manual.Count131072.C011716.packed 128 cuts11716 = true := by
 decide +kernel
def pointBounds11716 : List (Nat × Nat × Nat) := [(1539593216,93007822559789,93008198250700),(1539641344,93008232445173,93008608136401),(1539689472,93008659685232,93009035376787)]
theorem point_links_checked11716 : (cuts11716.take 3).map (fun c => (1539571713-1+2*2^9*c.k,93007636077790+c.lower,93008011768558+c.upper)) = pointBounds11716 := by
 decide +kernel
def cuts11717 : List PrefixCut := [⟨34,303280319,303280552⟩,
⟨81,719525384,719525942⟩,
⟨128,1135574702,1135575579⟩]
theorem checked11717 : checkPrefixCuts (2^48) 1539702785 9 Manual.Count131072.C011717.packed 128 cuts11717 = true := by
 decide +kernel
def pointBounds11717 : List (Nat × Nat × Nat) := [(1539737600,93009074846477,93009450538349),(1539785728,93009491091542,93009866783739),(1539833856,93009907140860,93010282833376)]
theorem point_links_checked11717 : (cuts11717.take 3).map (fun c => (1539702785-1+2*2^9*c.k,93008771566158+c.lower,93009147257797+c.upper)) = pointBounds11717 := by
 decide +kernel
def cuts11718 : List PrefixCut := [⟨47,423896479,423896807⟩,
⟨94,838457503,838458148⟩,
⟨128,1146993669,1146994553⟩]
theorem checked11718 : checkPrefixCuts (2^48) 1539833857 9 Manual.Count131072.C011718.packed 128 cuts11718 = true := by
 decide +kernel
def pointBounds11718 : List (Nat × Nat × Nat) := [(1539881984,93010331037339,93010706730183),(1539930112,93010745598363,93011121291524)]
theorem point_links_checked11718 : (cuts11718.take 2).map (fun c => (1539833857-1+2*2^9*c.k,93009907140860+c.lower,93010282833376+c.upper)) = pointBounds11718 := by
 decide +kernel
def cuts11719 : List PrefixCut := [⟨13,115333717,115333807⟩,
⟨60,526761658,526762072⟩,
⟨107,937811161,937811893⟩,
⟨128,1125146069,1125146945⟩]
theorem checked11719 : checkPrefixCuts (2^48) 1539964929 9 Manual.Count131072.C011719.packed 128 cuts11719 = true := by
 decide +kernel
def pointBounds11719 : List (Nat × Nat × Nat) := [(1539978240,93011169468246,93011545161736),(1540026368,93011580896187,93011956590001),(1540074496,93011991945690,93012367639822)]
theorem point_links_checked11719 : (cuts11719.take 3).map (fun c => (1539964929-1+2*2^9*c.k,93011054134529+c.lower,93011429827929+c.upper)) = pointBounds11719 := by
 decide +kernel
def cuts11720 : List PrefixCut := [⟨26,227174305,227174482⟩,
⟨73,630522255,630522745⟩,
⟨121,1062732522,1062733348⟩,
⟨128,1122857053,1122857927⟩]
theorem checked11720 : checkPrefixCuts (2^48) 1540096001 9 Manual.Count131072.C011720.packed 128 cuts11720 = true := by
 decide +kernel
def pointBounds11720 : List (Nat × Nat × Nat) := [(1540122624,93012406454903,93012782149356),(1540170752,93012809802853,93013185497619),(1540219904,93013242013120,93013617708222)]
theorem point_links_checked11720 : (cuts11720.take 3).map (fun c => (1540096001-1+2*2^9*c.k,93012179280598+c.lower,93012554974874+c.upper)) = pointBounds11720 := by
 decide +kernel
def cuts11721 : List PrefixCut := [⟨41,362386220,362386504⟩,
⟨89,787442000,787442616⟩,
⟨128,1126234070,1126234948⟩]
theorem checked11721 : checkPrefixCuts (2^48) 1540227073 9 Manual.Count131072.C011721.packed 128 cuts11721 = true := by
 decide +kernel
def pointBounds11721 : List (Nat × Nat × Nat) := [(1540269056,93013664523871,93014040219305),(1540318208,93014089579651,93014465275417)]
theorem point_links_checked11721 : (cuts11721.take 2).map (fun c => (1540227073-1+2*2^9*c.k,93013302137651+c.lower,93013677832801+c.upper)) = pointBounds11721 := by
 decide +kernel
def cuts11722 : List PrefixCut := [⟨9,79488796,79488856⟩,
⟨57,502690016,502690409⟩,
⟨105,937206638,937207367⟩,
⟨128,1132168057,1132168938⟩]
theorem checked11722 : checkPrefixCuts (2^48) 1540358145 9 Manual.Count131072.C011722.packed 128 cuts11722 = true := by
 decide +kernel
def pointBounds11722 : List (Nat × Nat × Nat) := [(1540367360,93014507860517,93014883556605),(1540416512,93014931061737,93015306758158),(1540465664,93015365578359,93015741275116)]
theorem point_links_checked11722 : (cuts11722.take 3).map (fun c => (1540358145-1+2*2^9*c.k,93014428371721+c.lower,93014804067749+c.upper)) = pointBounds11722 := by
 decide +kernel
def cuts11723 : List PrefixCut := [⟨25,219625021,219625192⟩,
⟨73,643699386,643699886⟩,
⟨121,1066481226,1066482056⟩,
⟨128,1124215288,1124216163⟩]
theorem checked11723 : checkPrefixCuts (2^48) 1540489217 9 Manual.Count131072.C011723.packed 128 cuts11723 = true := by
 decide +kernel
def pointBounds11723 : List (Nat × Nat × Nat) := [(1540514816,93015780164799,93016155861879),(1540563968,93016204239164,93016579936573),(1540613120,93016627021004,93017002718743)]
theorem point_links_checked11723 : (cuts11723.take 3).map (fun c => (1540489217-1+2*2^9*c.k,93015560539778+c.lower,93015936236687+c.upper)) = pointBounds11723 := by
 decide +kernel
def cuts11724 : List PrefixCut := [⟨41,361745662,361745943⟩,
⟨89,789433290,789433906⟩,
⟨128,1132523485,1132524368⟩]
theorem checked11724 : checkPrefixCuts (2^48) 1540620289 9 Manual.Count131072.C011724.packed 128 cuts11724 = true := by
 decide +kernel
def pointBounds11724 : List (Nat × Nat × Nat) := [(1540662272,93017046500728,93017422198793),(1540711424,93017474188356,93017849886756)]
theorem point_links_checked11724 : (cuts11724.take 2).map (fun c => (1540620289-1+2*2^9*c.k,93016684755066+c.lower,93017060452850+c.upper)) = pointBounds11724 := by
 decide +kernel
def cuts11725 : List PrefixCut := [⟨9,82574173,82574237⟩,
⟨57,514070867,514071264⟩,
⟨105,938246671,938247405⟩,
⟨128,1139917228,1139918118⟩]
theorem checked11725 : checkPrefixCuts (2^48) 1540751361 9 Manual.Count131072.C011725.packed 128 cuts11725 = true := by
 decide +kernel
def pointBounds11725 : List (Nat × Nat × Nat) := [(1540760576,93017899852724,93018275551455),(1540809728,93018331349418,93018707048482),(1540858880,93018755525222,93019131224623)]
theorem point_links_checked11725 : (cuts11725.take 3).map (fun c => (1540751361-1+2*2^9*c.k,93017817278551+c.lower,93018192977218+c.upper)) = pointBounds11725 := by
 decide +kernel
def cuts11726 : List PrefixCut := [⟨25,218655629,218655793⟩,
⟨73,652485690,652486190⟩,
⟨121,1075342299,1075343130⟩,
⟨128,1139454585,1139455466⟩]
theorem checked11726 : checkPrefixCuts (2^48) 1540882433 9 Manual.Count131072.C011726.packed 128 cuts11726 = true := by
 decide +kernel
def pointBounds11726 : List (Nat × Nat × Nat) := [(1540908032,93019175851408,93019551551129),(1540957184,93019609681469,93019985381526),(1541006336,93020032538078,93020408238466)]
theorem point_links_checked11726 : (cuts11726.take 3).map (fun c => (1540882433-1+2*2^9*c.k,93018957195779+c.lower,93019332895336+c.upper)) = pointBounds11726 := by
 decide +kernel
def cuts11727 : List PrefixCut := [⟨41,360922713,360922995⟩,
⟨89,775350535,775351142⟩,
⟨128,1119631679,1119632547⟩]
theorem checked11727 : checkPrefixCuts (2^48) 1541013505 9 Manual.Count131072.C011727.packed 128 cuts11727 = true := by
 decide +kernel
def pointBounds11727 : List (Nat × Nat × Nat) := [(1541055488,93020457573077,93020833273797),(1541104640,93020872000899,93021247701944)]
theorem point_links_checked11727 : (cuts11727.take 2).map (fun c => (1541013505-1+2*2^9*c.k,93020096650364+c.lower,93020472350802+c.upper)) = pointBounds11727 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000053
