import PlattAssemblyKernel
import PlattCertificates.Count131072.C017616
import PlattCertificates.Count131072.C017617
import PlattCertificates.Count131072.C017618
import PlattCertificates.Count131072.C017619
import PlattCertificates.Count131072.C017620
import PlattCertificates.Count131072.C017621
import PlattCertificates.Count131072.C017622
import PlattCertificates.Count131072.C017623
import PlattCertificates.Count131072.C017624
import PlattCertificates.Count131072.C017625
import PlattCertificates.Count131072.C017626
import PlattCertificates.Count131072.C017627
import PlattCertificates.Count131072.C017628
import PlattCertificates.Count131072.C017629
import PlattCertificates.Count131072.C017630
import PlattCertificates.Count131072.C017631
import PlattCertificates.Count131072.C017632
import PlattCertificates.Count131072.C017633
import PlattCertificates.Count131072.C017634
import PlattCertificates.Count131072.C017635
import PlattCertificates.Count131072.C017636
import PlattCertificates.Count131072.C017637
import PlattCertificates.Count131072.C017638
import PlattCertificates.Count131072.C017639
import PlattCertificates.Count131072.C017640
import PlattCertificates.Count131072.C017641
import PlattCertificates.Count131072.C017642
import PlattCertificates.Count131072.C017643
import PlattCertificates.Count131072.C017644
import PlattCertificates.Count131072.C017645
import PlattCertificates.Count131072.C017646
import PlattCertificates.Count131072.C017647
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000238
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17616 : List PrefixCut := [⟨71,403544245,403544497⟩,
⟨128,740876323,740876776⟩]
theorem checked17616 : checkPrefixCuts (2^48) 2312896513 9 Manual.Count131072.C017616.packed 128 cuts17616 = true := by
 decide +kernel
def pointBounds17616 : List (Nat × Nat × Nat) := [(2312969216,98371842088016,98372221466668)]
theorem point_links_checked17616 : (cuts17616.take 1).map (fun c => (2312896513-1+2*2^9*c.k,98371438543771+c.lower,98371817922171+c.upper)) = pointBounds17616 := by
 decide +kernel
def cuts17617 : List PrefixCut := [⟨14,78490521,78490571⟩,
⟨85,494665023,494665329⟩,
⟨128,739009275,739009735⟩]
theorem checked17617 : checkPrefixCuts (2^48) 2313027585 9 Manual.Count131072.C017617.packed 128 cuts17617 = true := by
 decide +kernel
def pointBounds17617 : List (Nat × Nat × Nat) := [(2313041920,98372257910615,98372637289518),(2313114624,98372674085117,98373053464276)]
theorem point_links_checked17617 : (cuts17617.take 2).map (fun c => (2313027585-1+2*2^9*c.k,98372179420094+c.lower,98372558798947+c.upper)) = pointBounds17617 := by
 decide +kernel
def cuts17618 : List PrefixCut := [⟨28,164394347,164394448⟩,
⟨99,575432040,575432395⟩,
⟨128,740670900,740671355⟩]
theorem checked17618 : checkPrefixCuts (2^48) 2313158657 9 Manual.Count131072.C017618.packed 128 cuts17618 = true := by
 decide +kernel
def pointBounds17618 : List (Nat × Nat × Nat) := [(2313187328,98373082823716,98373462203130),(2313260032,98373493861409,98373873241077)]
theorem point_links_checked17618 : (cuts17618.take 2).map (fun c => (2313158657-1+2*2^9*c.k,98372918429369+c.lower,98373297808682+c.upper)) = pointBounds17618 := by
 decide +kernel
def cuts17619 : List PrefixCut := [⟨42,242013920,242014066⟩,
⟨113,655824291,655824691⟩,
⟨128,742210576,742211031⟩]
theorem checked17619 : checkPrefixCuts (2^48) 2313289729 9 Manual.Count131072.C017619.packed 128 cuts17619 = true := by
 decide +kernel
def pointBounds17619 : List (Nat × Nat × Nat) := [(2313332736,98373901114189,98374280494103),(2313405440,98374314924560,98374694304728)]
theorem point_links_checked17619 : (cuts17619.take 2).map (fun c => (2313289729-1+2*2^9*c.k,98373659100269+c.lower,98374038480037+c.upper)) = pointBounds17619 := by
 decide +kernel
def cuts17620 : List PrefixCut := [⟨56,319380926,319381115⟩,
⟨127,729271936,729272373⟩,
⟨128,734746796,734747237⟩]
theorem checked17620 : checkPrefixCuts (2^48) 2313420801 9 Manual.Count131072.C017620.packed 128 cuts17620 = true := by
 decide +kernel
def pointBounds17620 : List (Nat × Nat × Nat) := [(2313478144,98374720691771,98375100072183),(2313550848,98375130582781,98375509963441)]
theorem point_links_checked17620 : (cuts17620.take 2).map (fun c => (2313420801-1+2*2^9*c.k,98374401310845+c.lower,98374780691068+c.upper)) = pointBounds17620 := by
 decide +kernel
def cuts17621 : List PrefixCut := [⟨70,404646699,404646949⟩,
⟨128,736651918,736652372⟩]
theorem checked17621 : checkPrefixCuts (2^48) 2313551873 9 Manual.Count131072.C017621.packed 128 cuts17621 = true := by
 decide +kernel
def pointBounds17621 : List (Nat × Nat × Nat) := [(2313623552,98375540704340,98375920085254)]
theorem point_links_checked17621 : (cuts17621.take 1).map (fun c => (2313551873-1+2*2^9*c.k,98375136057641+c.lower,98375515438305+c.upper)) = pointBounds17621 := by
 decide +kernel
def cuts17622 : List PrefixCut := [⟨13,76521810,76521853⟩,
⟨84,488928928,488929226⟩,
⟨128,738191679,738192131⟩]
theorem checked17622 : checkPrefixCuts (2^48) 2313682945 9 Manual.Count131072.C017622.packed 128 cuts17622 = true := by
 decide +kernel
def pointBounds17622 : List (Nat × Nat × Nat) := [(2313696256,98375949231369,98376328612530),(2313768960,98376361638487,98376741019903)]
theorem point_links_checked17622 : (cuts17622.take 2).map (fun c => (2313682945-1+2*2^9*c.k,98375872709559+c.lower,98376252090677+c.upper)) = pointBounds17622 := by
 decide +kernel
def cuts17623 : List PrefixCut := [⟨27,153399410,153399507⟩,
⟨98,564199199,564199557⟩,
⟨128,739852653,739853121⟩]
theorem checked17623 : checkPrefixCuts (2^48) 2313814017 9 Manual.Count131072.C017623.packed 128 cuts17623 = true := by
 decide +kernel
def pointBounds17623 : List (Nat × Nat × Nat) := [(2313841664,98376764300648,98377143682315),(2313914368,98377175100437,98377554482365)]
theorem point_links_checked17623 : (cuts17623.take 2).map (fun c => (2313814017-1+2*2^9*c.k,98376610901238+c.lower,98376990282808+c.upper)) = pointBounds17623 := by
 decide +kernel
def cuts17624 : List PrefixCut := [⟨41,241945445,241945595⟩,
⟨112,654665794,654666194⟩,
⟨128,745528193,745528647⟩]
theorem checked17624 : checkPrefixCuts (2^48) 2313945089 9 Manual.Count131072.C017624.packed 128 cuts17624 = true := by
 decide +kernel
def pointBounds17624 : List (Nat × Nat × Nat) := [(2313987072,98377592699336,98377972081524),(2314059776,98378005419685,98378384802123)]
theorem point_links_checked17624 : (cuts17624.take 2).map (fun c => (2313945089-1+2*2^9*c.k,98377350753891+c.lower,98377730135929+c.upper)) = pointBounds17624 := by
 decide +kernel
def cuts17625 : List PrefixCut := [⟨55,321358298,321358497⟩,
⟨126,734539114,734539560⟩,
⟨128,745120848,745121300⟩]
theorem checked17625 : checkPrefixCuts (2^48) 2314076161 9 Manual.Count131072.C017625.packed 128 cuts17625 = true := by
 decide +kernel
def pointBounds17625 : List (Nat × Nat × Nat) := [(2314132480,98378417640382,98378797023073),(2314205184,98378830821198,98379210204136)]
theorem point_links_checked17625 : (cuts17625.take 2).map (fun c => (2314076161-1+2*2^9*c.k,98378096282084+c.lower,98378475664576+c.upper)) = pointBounds17625 := by
 decide +kernel
def cuts17626 : List PrefixCut := [⟨69,404532137,404532386⟩,
⟨128,739484019,739484477⟩]
theorem checked17626 : checkPrefixCuts (2^48) 2314207233 9 Manual.Count131072.C017626.packed 128 cuts17626 = true := by
 decide +kernel
def pointBounds17626 : List (Nat × Nat × Nat) := [(2314277888,98379245935069,98379625318262)]
theorem point_links_checked17626 : (cuts17626.take 1).map (fun c => (2314207233-1+2*2^9*c.k,98378841402932+c.lower,98379220785876+c.upper)) = pointBounds17626 := by
 decide +kernel
def cuts17627 : List PrefixCut := [⟨12,72486632,72486676⟩,
⟨83,492925696,492925998⟩,
⟨128,751968867,751969327⟩]
theorem checked17627 : checkPrefixCuts (2^48) 2314338305 9 Manual.Count131072.C017627.packed 128 cuts17627 = true := by
 decide +kernel
def pointBounds17627 : List (Nat × Nat × Nat) := [(2314350592,98379653373583,98380032757029),(2314423296,98380073812647,98380453196351)]
theorem point_links_checked17627 : (cuts17627.take 2).map (fun c => (2314338305-1+2*2^9*c.k,98379580886951+c.lower,98379960270353+c.upper)) = pointBounds17627 := by
 decide +kernel
def cuts17628 : List PrefixCut := [⟨26,151653399,151653491⟩,
⟨97,561607491,561607833⟩,
⟨128,742197215,742197667⟩]
theorem checked17628 : checkPrefixCuts (2^48) 2314469377 9 Manual.Count131072.C017628.packed 128 cuts17628 = true := by
 decide +kernel
def pointBounds17628 : List (Nat × Nat × Nat) := [(2314496000,98380484509217,98380863893171),(2314568704,98380894463309,98381273847513)]
theorem point_links_checked17628 : (cuts17628.take 2).map (fun c => (2314469377-1+2*2^9*c.k,98380332855818+c.lower,98380712239680+c.upper)) = pointBounds17628 := by
 decide +kernel
def cuts17629 : List PrefixCut := [⟨40,231540362,231540508⟩,
⟨111,639766199,639766598⟩,
⟨128,739479835,739480297⟩]
theorem checked17629 : checkPrefixCuts (2^48) 2314600449 9 Manual.Count131072.C017629.packed 128 cuts17629 = true := by
 decide +kernel
def pointBounds17629 : List (Nat × Nat × Nat) := [(2314641408,98381306593395,98381685977855),(2314714112,98381714819232,98382094203945)]
theorem point_links_checked17629 : (cuts17629.take 2).map (fun c => (2314600449-1+2*2^9*c.k,98381075053033+c.lower,98381454437347+c.upper)) = pointBounds17629 := by
 decide +kernel
def cuts17630 : List PrefixCut := [⟨54,311296268,311296462⟩,
⟨125,725089807,725090252⟩,
⟨128,744909747,744910203⟩]
theorem checked17630 : checkPrefixCuts (2^48) 2314731521 9 Manual.Count131072.C017630.packed 128 cuts17630 = true := by
 decide +kernel
def pointBounds17630 : List (Nat × Nat × Nat) := [(2314786816,98382125829136,98382505214106),(2314859520,98382539622675,98382919007896)]
theorem point_links_checked17630 : (cuts17630.take 2).map (fun c => (2314731521-1+2*2^9*c.k,98381814532868+c.lower,98382193917644+c.upper)) = pointBounds17630 := by
 decide +kernel
def cuts17631 : List PrefixCut := [⟨68,393231182,393231421⟩,
⟨128,743773405,743773858⟩]
theorem checked17631 : checkPrefixCuts (2^48) 2314862593 9 Manual.Count131072.C017631.packed 128 cuts17631 = true := by
 decide +kernel
def pointBounds17631 : List (Nat × Nat × Nat) := [(2314932224,98382952673797,98383332059268)]
theorem point_links_checked17631 : (cuts17631.take 1).map (fun c => (2314862593-1+2*2^9*c.k,98382559442615+c.lower,98382938827847+c.upper)) = pointBounds17631 := by
 decide +kernel
def cuts17632 : List PrefixCut := [⟨11,62131195,62131235⟩,
⟨82,465551056,465551339⟩,
⟨128,730843213,730843657⟩]
theorem checked17632 : checkPrefixCuts (2^48) 2314993665 9 Manual.Count131072.C017632.packed 128 cuts17632 = true := by
 decide +kernel
def pointBounds17632 : List (Nat × Nat × Nat) := [(2315004928,98383365347215,98383744732940),(2315077632,98383768767076,98384148153044)]
theorem point_links_checked17632 : (cuts17632.take 2).map (fun c => (2314993665-1+2*2^9*c.k,98383303216020+c.lower,98383682601705+c.upper)) = pointBounds17632 := by
 decide +kernel
def cuts17633 : List PrefixCut := [⟨25,142856763,142856849⟩,
⟨96,553181208,553181549⟩,
⟨128,744540013,744540471⟩]
theorem checked17633 : checkPrefixCuts (2^48) 2315124737 9 Manual.Count131072.C017633.packed 128 cuts17633 = true := by
 decide +kernel
def pointBounds17633 : List (Nat × Nat × Nat) := [(2315150336,98384176915996,98384556302211),(2315223040,98384587240441,98384966626911)]
theorem point_links_checked17633 : (cuts17633.take 2).map (fun c => (2315124737-1+2*2^9*c.k,98384034059233+c.lower,98384413445362+c.upper)) = pointBounds17633 := by
 decide +kernel
def cuts17634 : List PrefixCut := [⟨39,223207933,223208072⟩,
⟨110,630832082,630832471⟩,
⟨128,732584162,732584614⟩]
theorem checked17634 : checkPrefixCuts (2^48) 2315255809 9 Manual.Count131072.C017634.packed 128 cuts17634 = true := by
 decide +kernel
def pointBounds17634 : List (Nat × Nat × Nat) := [(2315295744,98385001807179,98385381193905),(2315368448,98385409431328,98385788818304)]
theorem point_links_checked17634 : (cuts17634.take 2).map (fun c => (2315255809-1+2*2^9*c.k,98384778599246+c.lower,98385157985833+c.upper)) = pointBounds17634 := by
 decide +kernel
def cuts17635 : List PrefixCut := [⟨53,305980833,305981022⟩,
⟨124,717955623,717956060⟩,
⟨128,742146131,742146583⟩]
theorem checked17635 : checkPrefixCuts (2^48) 2315386881 9 Manual.Count131072.C017635.packed 128 cuts17635 = true := by
 decide +kernel
def pointBounds17635 : List (Nat × Nat × Nat) := [(2315441152,98385817164241,98386196551469),(2315513856,98386229139031,98386608526507)]
theorem point_links_checked17635 : (cuts17635.take 2).map (fun c => (2315386881-1+2*2^9*c.k,98385511183408+c.lower,98385890570447+c.upper)) = pointBounds17635 := by
 decide +kernel
def cuts17636 : List PrefixCut := [⟨67,391661237,391661475⟩,
⟨128,741861169,741861620⟩]
theorem checked17636 : checkPrefixCuts (2^48) 2315517953 9 Manual.Count131072.C017636.packed 128 cuts17636 = true := by
 decide +kernel
def pointBounds17636 : List (Nat × Nat × Nat) := [(2315586560,98386644990776,98387024378505)]
theorem point_links_checked17636 : (cuts17636.take 1).map (fun c => (2315517953-1+2*2^9*c.k,98386253329539+c.lower,98386632717030+c.upper)) = pointBounds17636 := by
 decide +kernel
def cuts17637 : List PrefixCut := [⟨10,57980817,57980851⟩,
⟨81,469430587,469430875⟩,
⟨128,742183673,742184126⟩]
theorem checked17637 : checkPrefixCuts (2^48) 2315649025 9 Manual.Count131072.C017637.packed 128 cuts17637 = true := by
 decide +kernel
def pointBounds17637 : List (Nat × Nat × Nat) := [(2315659264,98387053171525,98387432559501),(2315731968,98387464621295,98387844009525)]
theorem point_links_checked17637 : (cuts17637.take 2).map (fun c => (2315649025-1+2*2^9*c.k,98386995190708+c.lower,98387374578650+c.upper)) = pointBounds17637 := by
 decide +kernel
def cuts17638 : List PrefixCut := [⟨24,138683778,138683862⟩,
⟨95,551201687,551202025⟩,
⟨128,741898710,741899163⟩]
theorem checked17638 : checkPrefixCuts (2^48) 2315780097 9 Manual.Count131072.C017638.packed 128 cuts17638 = true := by
 decide +kernel
def pointBounds17638 : List (Nat × Nat × Nat) := [(2315804672,98387876058159,98388255446638),(2315877376,98388288576068,98388667964801)]
theorem point_links_checked17638 : (cuts17638.take 2).map (fun c => (2315780097-1+2*2^9*c.k,98387737374381+c.lower,98388116762776+c.upper)) = pointBounds17638 := by
 decide +kernel
def cuts17639 : List PrefixCut := [⟨38,214637120,214637252⟩,
⟨109,627250641,627251023⟩,
⟨128,737359731,737360184⟩]
theorem checked17639 : checkPrefixCuts (2^48) 2315911169 9 Manual.Count131072.C017639.packed 128 cuts17639 = true := by
 decide +kernel
def pointBounds17639 : List (Nat × Nat × Nat) := [(2315950080,98388693910211,98389073299191),(2316022784,98389106523732,98389485912962)]
theorem point_links_checked17639 : (cuts17639.take 2).map (fun c => (2315911169-1+2*2^9*c.k,98388479273091+c.lower,98388858661939+c.upper)) = pointBounds17639 := by
 decide +kernel
def cuts17640 : List PrefixCut := [⟨52,302369854,302370040⟩,
⟨123,710339347,710339785⟩,
⟨128,739991682,739992139⟩]
theorem checked17640 : checkPrefixCuts (2^48) 2316042241 9 Manual.Count131072.C017640.packed 128 cuts17640 = true := by
 decide +kernel
def pointBounds17640 : List (Nat × Nat × Nat) := [(2316095488,98389519002676,98389898392163),(2316168192,98389926972169,98390306361908)]
theorem point_links_checked17640 : (cuts17640.take 2).map (fun c => (2316042241-1+2*2^9*c.k,98389216632822+c.lower,98389596022123+c.upper)) = pointBounds17640 := by
 decide +kernel
def cuts17641 : List PrefixCut := [⟨66,380491824,380492057⟩,
⟨128,742623273,742623730⟩]
theorem checked17641 : checkPrefixCuts (2^48) 2316173313 9 Manual.Count131072.C017641.packed 128 cuts17641 = true := by
 decide +kernel
def pointBounds17641 : List (Nat × Nat × Nat) := [(2316240896,98390337116328,98390716506319)]
theorem point_links_checked17641 : (cuts17641.take 1).map (fun c => (2316173313-1+2*2^9*c.k,98389956624504+c.lower,98390336014262+c.upper)) = pointBounds17641 := by
 decide +kernel
def cuts17642 : List PrefixCut := [⟨9,50065711,50065742⟩,
⟨80,466988987,466989274⟩,
⟨128,737842342,737842796⟩]
theorem checked17642 : checkPrefixCuts (2^48) 2316304385 9 Manual.Count131072.C017642.packed 128 cuts17642 = true := by
 decide +kernel
def pointBounds17642 : List (Nat × Nat × Nat) := [(2316313600,98390749313488,98391128703734),(2316386304,98391166236764,98391545627266)]
theorem point_links_checked17642 : (cuts17642.take 2).map (fun c => (2316304385-1+2*2^9*c.k,98390699247777+c.lower,98391078637992+c.upper)) = pointBounds17642 := by
 decide +kernel
def cuts17643 : List PrefixCut := [⟨23,133905618,133905699⟩,
⟨94,539867012,539867344⟩,
⟨128,739866096,739866548⟩]
theorem checked17643 : checkPrefixCuts (2^48) 2316435457 9 Manual.Count131072.C017643.packed 128 cuts17643 = true := by
 decide +kernel
def pointBounds17643 : List (Nat × Nat × Nat) := [(2316459008,98391570995737,98391950386487),(2316531712,98391976957131,98392356348132)]
theorem point_links_checked17643 : (cuts17643.take 2).map (fun c => (2316435457-1+2*2^9*c.k,98391437090119+c.lower,98391816480788+c.upper)) = pointBounds17643 := by
 decide +kernel
def cuts17644 : List PrefixCut := [⟨37,211052825,211052955⟩,
⟨108,619540216,619540602⟩,
⟨128,734235151,734235610⟩]
theorem checked17644 : checkPrefixCuts (2^48) 2316566529 9 Manual.Count131072.C017644.packed 128 cuts17644 = true := by
 decide +kernel
def pointBounds17644 : List (Nat × Nat × Nat) := [(2316604416,98392388009040,98392767400291),(2316677120,98392796496431,98393175887938)]
theorem point_links_checked17644 : (cuts17644.take 2).map (fun c => (2316566529-1+2*2^9*c.k,98392176956215+c.lower,98392556347336+c.upper)) = pointBounds17644 := by
 decide +kernel
def cuts17645 : List PrefixCut := [⟨51,299247000,299247186⟩,
⟨122,706858363,706858800⟩,
⟨128,740997508,740997967⟩]
theorem checked17645 : checkPrefixCuts (2^48) 2316697601 9 Manual.Count131072.C017645.packed 128 cuts17645 = true := by
 decide +kernel
def pointBounds17645 : List (Nat × Nat × Nat) := [(2316749824,98393210438366,98393589830132),(2316822528,98393618049729,98393997441746)]
theorem point_links_checked17645 : (cuts17645.take 2).map (fun c => (2316697601-1+2*2^9*c.k,98392911191366+c.lower,98393290582946+c.upper)) = pointBounds17645 := by
 decide +kernel
def cuts17646 : List PrefixCut := [⟨65,369207256,369207481⟩,
⟨128,737796590,737797044⟩]
theorem checked17646 : checkPrefixCuts (2^48) 2316828673 9 Manual.Count131072.C017646.packed 128 cuts17646 = true := by
 decide +kernel
def pointBounds17646 : List (Nat × Nat × Nat) := [(2316895232,98394021396130,98394400788394)]
theorem point_links_checked17646 : (cuts17646.take 1).map (fun c => (2316828673-1+2*2^9*c.k,98393652188874+c.lower,98394031580913+c.upper)) = pointBounds17646 := by
 decide +kernel
def cuts17647 : List PrefixCut := [⟨8,47986324,47986353⟩,
⟨79,455437838,455438115⟩,
⟨128,732895970,732896421⟩]
theorem checked17647 : checkPrefixCuts (2^48) 2316959745 9 Manual.Count131072.C017647.packed 128 cuts17647 = true := by
 decide +kernel
def pointBounds17647 : List (Nat × Nat × Nat) := [(2316967936,98394437971788,98394817364310),(2317040640,98394845423302,98395224816072)]
theorem point_links_checked17647 : (cuts17647.take 2).map (fun c => (2316959745-1+2*2^9*c.k,98394389985464+c.lower,98394769377957+c.upper)) = pointBounds17647 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000238
