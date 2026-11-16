import PlattAssemblyKernel
import PlattCertificates.Count131072.C021536
import PlattCertificates.Count131072.C021537
import PlattCertificates.Count131072.C021538
import PlattCertificates.Count131072.C021539
import PlattCertificates.Count131072.C021540
import PlattCertificates.Count131072.C021541
import PlattCertificates.Count131072.C021542
import PlattCertificates.Count131072.C021543
import PlattCertificates.Count131072.C021544
import PlattCertificates.Count131072.C021545
import PlattCertificates.Count131072.C021546
import PlattCertificates.Count131072.C021547
import PlattCertificates.Count131072.C021548
import PlattCertificates.Count131072.C021549
import PlattCertificates.Count131072.C021550
import PlattCertificates.Count131072.C021551
import PlattCertificates.Count131072.C021552
import PlattCertificates.Count131072.C021553
import PlattCertificates.Count131072.C021554
import PlattCertificates.Count131072.C021555
import PlattCertificates.Count131072.C021556
import PlattCertificates.Count131072.C021557
import PlattCertificates.Count131072.C021558
import PlattCertificates.Count131072.C021559
import PlattCertificates.Count131072.C021560
import PlattCertificates.Count131072.C021561
import PlattCertificates.Count131072.C021562
import PlattCertificates.Count131072.C021563
import PlattCertificates.Count131072.C021564
import PlattCertificates.Count131072.C021565
import PlattCertificates.Count131072.C021566
import PlattCertificates.Count131072.C021567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21536 : List PrefixCut := [⟨2,9559413,9559418⟩,
⟨89,416724116,416724347⟩,
⟨128,594761256,594761590⟩]
theorem checked21536 : checkPrefixCuts (2^48) 2826698753 9 Manual.Count131072.C021536.packed 128 cuts21536 = true := by
 decide +kernel
def pointBounds21536 : List (Nat × Nat × Nat) := [(2826700800,100978093938861,100978474865197),(2826789888,100978501103564,100978882030126)]
theorem point_links_checked21536 : (cuts21536.take 2).map (fun c => (2826698753-1+2*2^9*c.k,100978084379448+c.lower,100978465305779+c.upper)) = pointBounds21536 := by
 decide +kernel
def cuts21537 : List PrefixCut := [⟨48,224036482,224036605⟩,
⟨128,597322399,597322740⟩]
theorem checked21537 : checkPrefixCuts (2^48) 2826829825 9 Manual.Count131072.C021537.packed 128 cuts21537 = true := by
 decide +kernel
def pointBounds21537 : List (Nat × Nat × Nat) := [(2826878976,100978903177186,100979284103974)]
theorem point_links_checked21537 : (cuts21537.take 1).map (fun c => (2826829825-1+2*2^9*c.k,100978679140704+c.lower,100979060067369+c.upper)) = pointBounds21537 := by
 decide +kernel
def cuts21538 : List PrefixCut := [⟨7,33554380,33554399⟩,
⟨94,436697938,436698192⟩,
⟨128,595004703,595005050⟩]
theorem checked21538 : checkPrefixCuts (2^48) 2826960897 9 Manual.Count131072.C021538.packed 128 cuts21538 = true := by
 decide +kernel
def pointBounds21538 : List (Nat × Nat × Nat) := [(2826968064,100979310017483,100979690944508),(2827057152,100979713161041,100980094088301)]
theorem point_links_checked21538 : (cuts21538.take 2).map (fun c => (2826960897-1+2*2^9*c.k,100979276463103+c.lower,100979657390109+c.upper)) = pointBounds21538 := by
 decide +kernel
def cuts21539 : List PrefixCut := [⟨53,249503476,249503620⟩,
⟨128,604634505,604634852⟩]
theorem checked21539 : checkPrefixCuts (2^48) 2827091969 9 Manual.Count131072.C021539.packed 128 cuts21539 = true := by
 decide +kernel
def pointBounds21539 : List (Nat × Nat × Nat) := [(2827146240,100980120971282,100980501898779)]
theorem point_links_checked21539 : (cuts21539.take 1).map (fun c => (2827091969-1+2*2^9*c.k,100979871467806+c.lower,100980252395159+c.upper)) = pointBounds21539 := by
 decide +kernel
def cuts21540 : List PrefixCut := [⟨12,56549266,56549300⟩,
⟨99,458758663,458758930⟩,
⟨128,594650821,594651165⟩]
theorem checked21540 : checkPrefixCuts (2^48) 2827223041 9 Manual.Count131072.C021540.packed 128 cuts21540 = true := by
 decide +kernel
def pointBounds21540 : List (Nat × Nat × Nat) := [(2827235328,100980532651577,100980913579311),(2827324416,100980934860974,100981315788941)]
theorem point_links_checked21540 : (cuts21540.take 2).map (fun c => (2827223041-1+2*2^9*c.k,100980476102311+c.lower,100980857030011+c.upper)) = pointBounds21540 := by
 decide +kernel
def cuts21541 : List PrefixCut := [⟨58,277554151,277554310⟩,
⟨128,608958859,608959208⟩]
theorem checked21541 : checkPrefixCuts (2^48) 2827354113 9 Manual.Count131072.C021541.packed 128 cuts21541 = true := by
 decide +kernel
def pointBounds21541 : List (Nat × Nat × Nat) := [(2827413504,100981348307283,100981729235486)]
theorem point_links_checked21541 : (cuts21541.take 1).map (fun c => (2827354113-1+2*2^9*c.k,100981070753132+c.lower,100981451681176+c.upper)) = pointBounds21541 := by
 decide +kernel
def cuts21542 : List PrefixCut := [⟨17,77648412,77648460⟩,
⟨104,485991755,485992038⟩,
⟨128,599373944,599374292⟩]
theorem checked21542 : checkPrefixCuts (2^48) 2827485185 9 Manual.Count131072.C021542.packed 128 cuts21542 = true := by
 decide +kernel
def pointBounds21542 : List (Nat × Nat × Nat) := [(2827502592,100981757360403,100982138288844),(2827591680,100982165703746,100982546632422)]
theorem point_links_checked21542 : (cuts21542.take 2).map (fun c => (2827485185-1+2*2^9*c.k,100981679711991+c.lower,100982060640384+c.upper)) = pointBounds21542 := by
 decide +kernel
def cuts21543 : List PrefixCut := [⟨63,296142850,296143019⟩,
⟨128,599843962,599844306⟩]
theorem checked21543 : checkPrefixCuts (2^48) 2827616257 9 Manual.Count131072.C021543.packed 128 cuts21543 = true := by
 decide +kernel
def pointBounds21543 : List (Nat × Nat × Nat) := [(2827680768,100982575228785,100982956157695)]
theorem point_links_checked21543 : (cuts21543.take 1).map (fun c => (2827616257-1+2*2^9*c.k,100982279085935+c.lower,100982660014676+c.upper)) = pointBounds21543 := by
 decide +kernel
def cuts21544 : List PrefixCut := [⟨22,100535326,100535387⟩,
⟨109,505256734,505257033⟩,
⟨128,599119238,599119590⟩]
theorem checked21544 : checkPrefixCuts (2^48) 2827747329 9 Manual.Count131072.C021544.packed 128 cuts21544 = true := by
 decide +kernel
def pointBounds21544 : List (Nat × Nat × Nat) := [(2827769856,100982979465223,100983360394369),(2827858944,100983384186631,100983765116015)]
theorem point_links_checked21544 : (cuts21544.take 2).map (fun c => (2827747329-1+2*2^9*c.k,100982878929897+c.lower,100983259858982+c.upper)) = pointBounds21544 := by
 decide +kernel
def cuts21545 : List PrefixCut := [⟨68,319007988,319008171⟩,
⟨128,600982637,600982978⟩]
theorem checked21545 : checkPrefixCuts (2^48) 2827878401 9 Manual.Count131072.C021545.packed 128 cuts21545 = true := by
 decide +kernel
def pointBounds21545 : List (Nat × Nat × Nat) := [(2827948032,100983797057123,100984177986743)]
theorem point_links_checked21545 : (cuts21545.take 1).map (fun c => (2827878401-1+2*2^9*c.k,100983478049135+c.lower,100983858978572+c.upper)) = pointBounds21545 := by
 decide +kernel
def cuts21546 : List PrefixCut := [⟨27,126403878,126403950⟩,
⟨114,535466283,535466590⟩,
⟨128,600258192,600258534⟩]
theorem checked21546 : checkPrefixCuts (2^48) 2828009473 9 Manual.Count131072.C021546.packed 128 cuts21546 = true := by
 decide +kernel
def pointBounds21546 : List (Nat × Nat × Nat) := [(2828037120,100984205435650,100984586365500),(2828126208,100984614498055,100984995428140)]
theorem point_links_checked21546 : (cuts21546.take 2).map (fun c => (2828009473-1+2*2^9*c.k,100984079031772+c.lower,100984459961550+c.upper)) = pointBounds21546 := by
 decide +kernel
def cuts21547 : List PrefixCut := [⟨73,344257602,344257803⟩,
⟨128,604310865,604311214⟩]
theorem checked21547 : checkPrefixCuts (2^48) 2828140545 9 Manual.Count131072.C021547.packed 128 cuts21547 = true := by
 decide +kernel
def pointBounds21547 : List (Nat × Nat × Nat) := [(2828215296,100985023547566,100985404477887)]
theorem point_links_checked21547 : (cuts21547.take 1).map (fun c => (2828140545-1+2*2^9*c.k,100984679289964+c.lower,100985060220084+c.upper)) = pointBounds21547 := by
 decide +kernel
def cuts21548 : List PrefixCut := [⟨32,147590097,147590185⟩,
⟨119,562087352,562087678⟩,
⟨128,603486600,603486950⟩]
theorem checked21548 : checkPrefixCuts (2^48) 2828271617 9 Manual.Count131072.C021548.packed 128 cuts21548 = true := by
 decide +kernel
def pointBounds21548 : List (Nat × Nat × Nat) := [(2828304384,100985431190926,100985812121483),(2828393472,100985845688181,100986226618976)]
theorem point_links_checked21548 : (cuts21548.take 2).map (fun c => (2828271617-1+2*2^9*c.k,100985283600829+c.lower,100985664531298+c.upper)) = pointBounds21548 := by
 decide +kernel
def cuts21549 : List PrefixCut := [⟨78,366815447,366815658⟩,
⟨128,598184463,598184800⟩]
theorem checked21549 : checkPrefixCuts (2^48) 2828402689 9 Manual.Count131072.C021549.packed 128 cuts21549 = true := by
 decide +kernel
def pointBounds21549 : List (Nat × Nat × Nat) := [(2828482560,100986253902876,100986634833906)]
theorem point_links_checked21549 : (cuts21549.take 1).map (fun c => (2828402689-1+2*2^9*c.k,100985887087429+c.lower,100986268018248+c.upper)) = pointBounds21549 := by
 decide +kernel
def cuts21550 : List PrefixCut := [⟨37,171260121,171260219⟩,
⟨124,578553546,578553874⟩,
⟨128,595967466,595967804⟩]
theorem checked21550 : checkPrefixCuts (2^48) 2828533761 9 Manual.Count131072.C021550.packed 128 cuts21550 = true := by
 decide +kernel
def pointBounds21550 : List (Nat × Nat × Nat) := [(2828571648,100986656532013,100987037463267),(2828660736,100987063825438,100987444756922)]
theorem point_links_checked21550 : (cuts21550.take 2).map (fun c => (2828533761-1+2*2^9*c.k,100986485271892+c.lower,100986866203048+c.upper)) = pointBounds21550 := by
 decide +kernel
def cuts21551 : List PrefixCut := [⟨83,383697243,383697469⟩,
⟨128,590168546,590168890⟩]
theorem checked21551 : checkPrefixCuts (2^48) 2828664833 9 Manual.Count131072.C021551.packed 128 cuts21551 = true := by
 decide +kernel
def pointBounds21551 : List (Nat × Nat × Nat) := [(2828749824,100987464936601,100987845868321)]
theorem point_links_checked21551 : (cuts21551.take 1).map (fun c => (2828664833-1+2*2^9*c.k,100987081239358+c.lower,100987462170852+c.upper)) = pointBounds21551 := by
 decide +kernel
def cuts21552 : List PrefixCut := [⟨42,194328729,194328842⟩,
⟨128,598797765,598798116⟩]
theorem checked21552 : checkPrefixCuts (2^48) 2828795905 9 Manual.Count131072.C021552.packed 128 cuts21552 = true := by
 decide +kernel
def pointBounds21552 : List (Nat × Nat × Nat) := [(2828838912,100987865736633,100988246668584)]
theorem point_links_checked21552 : (cuts21552.take 1).map (fun c => (2828795905-1+2*2^9*c.k,100987671407904+c.lower,100988052339742+c.upper)) = pointBounds21552 := by
 decide +kernel
def cuts21553 : List PrefixCut := [⟨1,5571933,5571936⟩,
⟨88,411620037,411620275⟩,
⟨128,598670519,598670865⟩]
theorem checked21553 : checkPrefixCuts (2^48) 2828926977 9 Manual.Count131072.C021553.packed 128 cuts21553 = true := by
 decide +kernel
def pointBounds21553 : List (Nat × Nat × Nat) := [(2828928000,100988275777602,100988656709794),(2829017088,100988681825706,100989062758133)]
theorem point_links_checked21553 : (cuts21553.take 2).map (fun c => (2828926977-1+2*2^9*c.k,100988270205669+c.lower,100988651137858+c.upper)) = pointBounds21553 := by
 decide +kernel
def cuts21554 : List PrefixCut := [⟨47,219780850,219780975⟩,
⟨128,604313835,604314181⟩]
theorem checked21554 : checkPrefixCuts (2^48) 2829058049 9 Manual.Count131072.C021554.packed 128 cuts21554 = true := by
 decide +kernel
def pointBounds21554 : List (Nat × Nat × Nat) := [(2829106176,100989088657038,100989469589698)]
theorem point_links_checked21554 : (cuts21554.take 1).map (fun c => (2829058049-1+2*2^9*c.k,100988868876188+c.lower,100989249808723+c.upper)) = pointBounds21554 := by
 decide +kernel
def cuts21555 : List PrefixCut := [⟨6,29946337,29946354⟩,
⟨93,433170471,433170716⟩,
⟨128,597321749,597322085⟩]
theorem checked21555 : checkPrefixCuts (2^48) 2829189121 9 Manual.Count131072.C021555.packed 128 cuts21555 = true := by
 decide +kernel
def pointBounds21555 : List (Nat × Nat × Nat) := [(2829195264,100989503136360,100989884069258),(2829284352,100989906360494,100990287293620)]
theorem point_links_checked21555 : (cuts21555.take 2).map (fun c => (2829189121-1+2*2^9*c.k,100989473190023+c.lower,100989854122904+c.upper)) = pointBounds21555 := by
 decide +kernel
def cuts21556 : List PrefixCut := [⟨52,241248871,241249005⟩,
⟨128,603561405,603561743⟩]
theorem checked21556 : checkPrefixCuts (2^48) 2829320193 9 Manual.Count131072.C021556.packed 128 cuts21556 = true := by
 decide +kernel
def pointBounds21556 : List (Nat × Nat × Nat) := [(2829373440,100990311760643,100990692693994)]
theorem point_links_checked21556 : (cuts21556.take 1).map (fun c => (2829320193-1+2*2^9*c.k,100990070511772+c.lower,100990451444989+c.upper)) = pointBounds21556 := by
 decide +kernel
def cuts21557 : List PrefixCut := [⟨11,50336974,50337000⟩,
⟨98,463868866,463869133⟩,
⟨128,602041459,602041808⟩]
theorem checked21557 : checkPrefixCuts (2^48) 2829451265 9 Manual.Count131072.C021557.packed 128 cuts21557 = true := by
 decide +kernel
def pointBounds21557 : List (Nat × Nat × Nat) := [(2829462528,100990724410151,100991105343732),(2829551616,100991137942043,100991518875865)]
theorem point_links_checked21557 : (cuts21557.take 2).map (fun c => (2829451265-1+2*2^9*c.k,100990674073177+c.lower,100991055006732+c.upper)) = pointBounds21557 := by
 decide +kernel
def cuts21558 : List PrefixCut := [⟨57,264801784,264801930⟩,
⟨128,594851355,594851691⟩]
theorem checked21558 : checkPrefixCuts (2^48) 2829582337 9 Manual.Count131072.C021558.packed 128 cuts21558 = true := by
 decide +kernel
def pointBounds21558 : List (Nat × Nat × Nat) := [(2829640704,100991540916420,100991921850470)]
theorem point_links_checked21558 : (cuts21558.take 1).map (fun c => (2829582337-1+2*2^9*c.k,100991276114636+c.lower,100991657048540+c.upper)) = pointBounds21558 := by
 decide +kernel
def cuts21559 : List PrefixCut := [⟨16,77487820,77487862⟩,
⟨103,486405020,486405293⟩,
⟨128,605367555,605367891⟩]
theorem checked21559 : checkPrefixCuts (2^48) 2829713409 9 Manual.Count131072.C021559.packed 128 cuts21559 = true := by
 decide +kernel
def pointBounds21559 : List (Nat × Nat × Nat) := [(2829729792,100991948453811,100992329388093),(2829818880,100992357371011,100992738305524)]
theorem point_links_checked21559 : (cuts21559.take 2).map (fun c => (2829713409-1+2*2^9*c.k,100991870965991+c.lower,100992251900231+c.upper)) = pointBounds21559 := by
 decide +kernel
def cuts21560 : List PrefixCut := [⟨62,289742842,289743008⟩,
⟨128,597879679,597880022⟩]
theorem checked21560 : checkPrefixCuts (2^48) 2829844481 9 Manual.Count131072.C021560.packed 128 cuts21560 = true := by
 decide +kernel
def pointBounds21560 : List (Nat × Nat × Nat) := [(2829907968,100992766076388,100993147011130)]
theorem point_links_checked21560 : (cuts21560.take 1).map (fun c => (2829844481-1+2*2^9*c.k,100992476333546+c.lower,100992857268122+c.upper)) = pointBounds21560 := by
 decide +kernel
def cuts21561 : List PrefixCut := [⟨21,100257270,100257330⟩,
⟨108,511920678,511920976⟩,
⟨128,607897365,607897718⟩]
theorem checked21561 : checkPrefixCuts (2^48) 2829975553 9 Manual.Count131072.C021561.packed 128 cuts21561 = true := by
 decide +kernel
def pointBounds21561 : List (Nat × Nat × Nat) := [(2829997056,100993174470495,100993555405474),(2830086144,100993586133903,100993967069120)]
theorem point_links_checked21561 : (cuts21561.take 2).map (fun c => (2829975553-1+2*2^9*c.k,100993074213225+c.lower,100993455148144+c.upper)) = pointBounds21561 := by
 decide +kernel
def cuts21562 : List PrefixCut := [⟨67,310104255,310104434⟩,
⟨128,595835115,595835459⟩]
theorem checked21562 : checkPrefixCuts (2^48) 2830106625 9 Manual.Count131072.C021562.packed 128 cuts21562 = true := by
 decide +kernel
def pointBounds21562 : List (Nat × Nat × Nat) := [(2830175232,100993992214845,100994373150296)]
theorem point_links_checked21562 : (cuts21562.take 1).map (fun c => (2830106625-1+2*2^9*c.k,100993682110590+c.lower,100994063045862+c.upper)) = pointBounds21562 := by
 decide +kernel
def cuts21563 : List PrefixCut := [⟨26,122624652,122624722⟩,
⟨113,530072334,530072641⟩,
⟨128,599586771,599587119⟩]
theorem checked21563 : checkPrefixCuts (2^48) 2830237697 9 Manual.Count131072.C021563.packed 128 cuts21563 = true := by
 decide +kernel
def pointBounds21563 : List (Nat × Nat × Nat) := [(2830264320,100994400570357,100994781506043),(2830353408,100994808018039,100995188953962)]
theorem point_links_checked21563 : (cuts21563.take 2).map (fun c => (2830237697-1+2*2^9*c.k,100994277945705+c.lower,100994658881321+c.upper)) = pointBounds21563 := by
 decide +kernel
def cuts21564 : List PrefixCut := [⟨72,333445215,333445407⟩,
⟨128,595680461,595680807⟩]
theorem checked21564 : checkPrefixCuts (2^48) 2830368769 9 Manual.Count131072.C021564.packed 128 cuts21564 = true := by
 decide +kernel
def pointBounds21564 : List (Nat × Nat × Nat) := [(2830442496,100995210977691,100995591913847)]
theorem point_links_checked21564 : (cuts21564.take 1).map (fun c => (2830368769-1+2*2^9*c.k,100994877532476+c.lower,100995258468440+c.upper)) = pointBounds21564 := by
 decide +kernel
def cuts21565 : List PrefixCut := [⟨31,142998988,142999067⟩,
⟨118,553490864,553491176⟩,
⟨128,600525556,600525896⟩]
theorem checked21565 : checkPrefixCuts (2^48) 2830499841 9 Manual.Count131072.C021565.packed 128 cuts21565 = true := by
 decide +kernel
def pointBounds21565 : List (Nat × Nat × Nat) := [(2830531584,100995616211925,100995997148314),(2830620672,100996026703801,100996407640423)]
theorem point_links_checked21565 : (cuts21565.take 2).map (fun c => (2830499841-1+2*2^9*c.k,100995473212937+c.lower,100995854149247+c.upper)) = pointBounds21565 := by
 decide +kernel
def cuts21566 : List PrefixCut := [⟨77,357975093,357975297⟩,
⟨128,596719096,596719440⟩]
theorem checked21566 : checkPrefixCuts (2^48) 2830630913 9 Manual.Count131072.C021566.packed 128 cuts21566 = true := by
 decide +kernel
def pointBounds21566 : List (Nat × Nat × Nat) := [(2830709760,100996431713586,100996812650440)]
theorem point_links_checked21566 : (cuts21566.take 1).map (fun c => (2830630913-1+2*2^9*c.k,100996073738493+c.lower,100996454675143+c.upper)) = pointBounds21566 := by
 decide +kernel
def cuts21567 : List PrefixCut := [⟨36,162772916,162773009⟩,
⟨123,576208939,576209260⟩,
⟨128,599077796,599078130⟩]
theorem checked21567 : checkPrefixCuts (2^48) 2830761985 9 Manual.Count131072.C021567.packed 128 cuts21567 = true := by
 decide +kernel
def pointBounds21567 : List (Nat × Nat × Nat) := [(2830798848,100996833230505,100997214167592),(2830887936,100997246666528,100997627603843)]
theorem point_links_checked21567 : (cuts21567.take 2).map (fun c => (2830761985-1+2*2^9*c.k,100996670457589+c.lower,100997051394583+c.upper)) = pointBounds21567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000048
