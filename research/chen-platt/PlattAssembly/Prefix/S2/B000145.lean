import PlattAssemblyKernel
import PlattCertificates.Count131072.C014640
import PlattCertificates.Count131072.C014641
import PlattCertificates.Count131072.C014642
import PlattCertificates.Count131072.C014643
import PlattCertificates.Count131072.C014644
import PlattCertificates.Count131072.C014645
import PlattCertificates.Count131072.C014646
import PlattCertificates.Count131072.C014647
import PlattCertificates.Count131072.C014648
import PlattCertificates.Count131072.C014649
import PlattCertificates.Count131072.C014650
import PlattCertificates.Count131072.C014651
import PlattCertificates.Count131072.C014652
import PlattCertificates.Count131072.C014653
import PlattCertificates.Count131072.C014654
import PlattCertificates.Count131072.C014655
import PlattCertificates.Count131072.C014656
import PlattCertificates.Count131072.C014657
import PlattCertificates.Count131072.C014658
import PlattCertificates.Count131072.C014659
import PlattCertificates.Count131072.C014660
import PlattCertificates.Count131072.C014661
import PlattCertificates.Count131072.C014662
import PlattCertificates.Count131072.C014663
import PlattCertificates.Count131072.C014664
import PlattCertificates.Count131072.C014665
import PlattCertificates.Count131072.C014666
import PlattCertificates.Count131072.C014667
import PlattCertificates.Count131072.C014668
import PlattCertificates.Count131072.C014669
import PlattCertificates.Count131072.C014670
import PlattCertificates.Count131072.C014671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14640 : List PrefixCut := [⟨12,84610854,84610911⟩,
⟨71,498288547,498288886⟩,
⟨128,898340344,898340954⟩]
theorem checked14640 : checkPrefixCuts (2^48) 1922826241 9 Manual.Count131072.C014640.packed 128 cuts14640 = true := by
 decide +kernel
def pointBounds14640 : List (Nat × Nat × Nat) := [(1922838528,95949786171580,95950163991706),(1922898944,95950199849273,95950577669681)]
theorem point_links_checked14640 : (cuts14640.take 2).map (fun c => (1922826241-1+2*2^9*c.k,95949701560726+c.lower,95950079380795+c.upper)) = pointBounds14640 := by
 decide +kernel
def cuts14641 : List PrefixCut := [⟨2,12881085,12881093⟩,
⟨61,418335953,418336235⟩,
⟨120,824070808,824071366⟩,
⟨128,882324624,882325220⟩]
theorem checked14641 : checkPrefixCuts (2^48) 1922957313 9 Manual.Count131072.C014641.packed 128 cuts14641 = true := by
 decide +kernel
def pointBounds14641 : List (Nat × Nat × Nat) := [(1922959360,95950612782155,95950990602842),(1923019776,95951018237023,95951396057984),(1923080192,95951423971878,95951801793115)]
theorem point_links_checked14641 : (cuts14641.take 3).map (fun c => (1922957313-1+2*2^9*c.k,95950599901070+c.lower,95950977721749+c.upper)) = pointBounds14641 := by
 decide +kernel
def cuts14642 : List PrefixCut := [⟨51,362104751,362104992⟩,
⟨110,778498354,778498876⟩,
⟨128,903340696,903341305⟩]
theorem checked14642 : checkPrefixCuts (2^48) 1923088385 9 Manual.Count131072.C014642.packed 128 cuts14642 = true := by
 decide +kernel
def pointBounds14642 : List (Nat × Nat × Nat) := [(1923140608,95951844330445,95952222151961),(1923201024,95952260724048,95952638545845)]
theorem point_links_checked14642 : (cuts14642.take 2).map (fun c => (1923088385-1+2*2^9*c.k,95951482225694+c.lower,95951860046969+c.upper)) = pointBounds14642 := by
 decide +kernel
def cuts14643 : List PrefixCut := [⟨41,291538167,291538362⟩,
⟨100,702051642,702052108⟩,
⟨128,899620353,899620956⟩]
theorem checked14643 : checkPrefixCuts (2^48) 1923219457 9 Manual.Count131072.C014643.packed 128 cuts14643 = true := by
 decide +kernel
def pointBounds14643 : List (Nat × Nat × Nat) := [(1923261440,95952677104557,95953054926636),(1923321856,95953087618032,95953465440382)]
theorem point_links_checked14643 : (cuts14643.take 2).map (fun c => (1923219457-1+2*2^9*c.k,95952385566390+c.lower,95952763388274+c.upper)) = pointBounds14643 := by
 decide +kernel
def cuts14644 : List PrefixCut := [⟨31,223322321,223322474⟩,
⟨90,632931918,632932345⟩,
⟨128,903363882,903364495⟩]
theorem checked14644 : checkPrefixCuts (2^48) 1923350529 9 Manual.Count131072.C014644.packed 128 cuts14644 = true := by
 decide +kernel
def pointBounds14644 : List (Nat × Nat × Nat) := [(1923382272,95953508509064,95953886331704),(1923442688,95953918118661,95954295941575)]
theorem point_links_checked14644 : (cuts14644.take 2).map (fun c => (1923350529-1+2*2^9*c.k,95953285186743+c.lower,95953663009230+c.upper)) = pointBounds14644 := by
 decide +kernel
def cuts14645 : List PrefixCut := [⟨21,145164651,145164748⟩,
⟨80,565430790,565431170⟩,
⟨128,908131054,908131663⟩]
theorem checked14645 : checkPrefixCuts (2^48) 1923481601 9 Manual.Count131072.C014645.packed 128 cuts14645 = true := by
 decide +kernel
def pointBounds14645 : List (Nat × Nat × Nat) := [(1923503104,95954333715276,95954711538473),(1923563520,95954753981415,95955131804895)]
theorem point_links_checked14645 : (cuts14645.take 2).map (fun c => (1923481601-1+2*2^9*c.k,95954188550625+c.lower,95954566373725+c.upper)) = pointBounds14645 := by
 decide +kernel
def cuts14646 : List PrefixCut := [⟨11,74918779,74918830⟩,
⟨70,485501203,485501532⟩,
⟨128,900314021,900314630⟩]
theorem checked14646 : checkPrefixCuts (2^48) 1923612673 9 Manual.Count131072.C014646.packed 128 cuts14646 = true := by
 decide +kernel
def pointBounds14646 : List (Nat × Nat × Nat) := [(1923623936,95955171600458,95955549424218),(1923684352,95955582182882,95955960006920)]
theorem point_links_checked14646 : (cuts14646.take 2).map (fun c => (1923612673-1+2*2^9*c.k,95955096681679+c.lower,95955474505388+c.upper)) = pointBounds14646 := by
 decide +kernel
def cuts14647 : List PrefixCut := [⟨1,7169492,7169497⟩,
⟨60,415092408,415092683⟩,
⟨119,830318068,830318623⟩,
⟨128,897619099,897619699⟩]
theorem checked14647 : checkPrefixCuts (2^48) 1923743745 9 Manual.Count131072.C014647.packed 128 cuts14647 = true := by
 decide +kernel
def pointBounds14647 : List (Nat × Nat × Nat) := [(1923744768,95956004165192,95956381989515),(1923805184,95956412088108,95956789912701),(1923865600,95956827313768,95957205138641)]
theorem point_links_checked14647 : (cuts14647.take 3).map (fun c => (1923743745-1+2*2^9*c.k,95955996995700+c.lower,95956374820018+c.upper)) = pointBounds14647 := by
 decide +kernel
def cuts14648 : List PrefixCut := [⟨50,349520994,349521231⟩,
⟨109,765305651,765306165⟩,
⟨128,899313714,899314319⟩]
theorem checked14648 : checkPrefixCuts (2^48) 1923874817 9 Manual.Count131072.C014648.packed 128 cuts14648 = true := by
 decide +kernel
def pointBounds14648 : List (Nat × Nat × Nat) := [(1923926016,95957244135793,95957621960948),(1923986432,95957659920450,95958037745882)]
theorem point_links_checked14648 : (cuts14648.take 2).map (fun c => (1923874817-1+2*2^9*c.k,95956894614799+c.lower,95957272439717+c.upper)) = pointBounds14648 := by
 decide +kernel
def cuts14649 : List PrefixCut := [⟨40,277960012,277960194⟩,
⟨99,685672636,685673095⟩,
⟨128,896472841,896473439⟩]
theorem checked14649 : checkPrefixCuts (2^48) 1924005889 9 Manual.Count131072.C014649.packed 128 cuts14649 = true := by
 decide +kernel
def pointBounds14649 : List (Nat × Nat × Nat) := [(1924046848,95958071888525,95958449714230),(1924107264,95958479601149,95958857427131)]
theorem point_links_checked14649 : (cuts14649.take 2).map (fun c => (1924005889-1+2*2^9*c.k,95957793928513+c.lower,95958171754036+c.upper)) = pointBounds14649 := by
 decide +kernel
def cuts14650 : List PrefixCut := [⟨30,210211739,210211880⟩,
⟨89,623311209,623311632⟩,
⟨128,899630054,899630666⟩]
theorem checked14650 : checkPrefixCuts (2^48) 1924136961 9 Manual.Count131072.C014650.packed 128 cuts14650 = true := by
 decide +kernel
def pointBounds14650 : List (Nat × Nat × Nat) := [(1924167680,95958900613093,95959278439355),(1924228096,95959313712563,95959691539107)]
theorem point_links_checked14650 : (cuts14650.take 2).map (fun c => (1924136961-1+2*2^9*c.k,95958690401354+c.lower,95959068227475+c.upper)) = pointBounds14650 := by
 decide +kernel
def cuts14651 : List PrefixCut := [⟨20,137060199,137060293⟩,
⟨79,542966289,542966660⟩,
⟨128,886257926,886258530⟩]
theorem checked14651 : checkPrefixCuts (2^48) 1924268033 9 Manual.Count131072.C014651.packed 128 cuts14651 = true := by
 decide +kernel
def pointBounds14651 : List (Nat × Nat × Nat) := [(1924288512,95959727091607,95960104918434),(1924348928,95960132997697,95960510824801)]
theorem point_links_checked14651 : (cuts14651.take 2).map (fun c => (1924268033-1+2*2^9*c.k,95959590031408+c.lower,95959967858141+c.upper)) = pointBounds14651 := by
 decide +kernel
def cuts14652 : List PrefixCut := [⟨10,69622608,69622653⟩,
⟨69,490129533,490129862⟩,
⟨128,898776325,898776932⟩]
theorem checked14652 : checkPrefixCuts (2^48) 1924399105 9 Manual.Count131072.C014652.packed 128 cuts14652 = true := by
 decide +kernel
def pointBounds14652 : List (Nat × Nat × Nat) := [(1924409344,95960545911942,95960923739324),(1924469760,95960966418867,95961344246533),(1924530176,95961375065659,95961752893603)]
theorem point_links_checked14652 : (cuts14652.take 3).map (fun c => (1924399105-1+2*2^9*c.k,95960476289334+c.lower,95960854116671+c.upper)) = pointBounds14652 := by
 decide +kernel
def cuts14653 : List PrefixCut := [⟨59,407171425,407171703⟩,
⟨118,824128926,824129484⟩,
⟨128,893888670,893889275⟩]
theorem checked14653 : checkPrefixCuts (2^48) 1924530177 9 Manual.Count131072.C014653.packed 128 cuts14653 = true := by
 decide +kernel
def pointBounds14653 : List (Nat × Nat × Nat) := [(1924590592,95961782237084,95962160065306),(1924651008,95962199194585,95962577023087)]
theorem point_links_checked14653 : (cuts14653.take 2).map (fun c => (1924530177-1+2*2^9*c.k,95961375065659+c.lower,95961752893603+c.upper)) = pointBounds14653 := by
 decide +kernel
def cuts14654 : List PrefixCut := [⟨49,344113398,344113629⟩,
⟨108,763676971,763677485⟩,
⟨128,907281963,907282574⟩]
theorem checked14654 : checkPrefixCuts (2^48) 1924661249 9 Manual.Count131072.C014654.packed 128 cuts14654 = true := by
 decide +kernel
def pointBounds14654 : List (Nat × Nat × Nat) := [(1924711424,95962613067727,95962990896507),(1924771840,95963032631300,95963410460363)]
theorem point_links_checked14654 : (cuts14654.take 2).map (fun c => (1924661249-1+2*2^9*c.k,95962268954329+c.lower,95962646782878+c.upper)) = pointBounds14654 := by
 decide +kernel
def cuts14655 : List PrefixCut := [⟨39,269218597,269218777⟩,
⟨98,682906621,682907084⟩,
⟨128,885285754,885286355⟩]
theorem checked14655 : checkPrefixCuts (2^48) 1924792321 9 Manual.Count131072.C014655.packed 128 cuts14655 = true := by
 decide +kernel
def pointBounds14655 : List (Nat × Nat × Nat) := [(1924832256,95963445454889,95963823284229),(1924892672,95963859142913,95964236972536)]
theorem point_links_checked14655 : (cuts14655.take 2).map (fun c => (1924792321-1+2*2^9*c.k,95963176236292+c.lower,95963554065452+c.upper)) = pointBounds14655 := by
 decide +kernel
def cuts14656 : List PrefixCut := [⟨29,201059938,201060069⟩,
⟨88,606972182,606972590⟩,
⟨128,885663963,885664557⟩]
theorem checked14656 : checkPrefixCuts (2^48) 1924923393 9 Manual.Count131072.C014656.packed 128 cuts14656 = true := by
 decide +kernel
def pointBounds14656 : List (Nat × Nat × Nat) := [(1924953088,95964262581984,95964640411876),(1925013504,95964668494228,95965046324397)]
theorem point_links_checked14656 : (cuts14656.take 2).map (fun c => (1924923393-1+2*2^9*c.k,95964061522046+c.lower,95964439351807+c.upper)) = pointBounds14656 := by
 decide +kernel
def cuts14657 : List PrefixCut := [⟨19,132471540,132471630⟩,
⟨78,548446947,548447317⟩,
⟨128,899493695,899494303⟩]
theorem checked14657 : checkPrefixCuts (2^48) 1925054465 9 Manual.Count131072.C014657.packed 128 cuts14657 = true := by
 decide +kernel
def pointBounds14657 : List (Nat × Nat × Nat) := [(1925073920,95965079657549,95965457487994),(1925134336,95965495632956,95965873463681)]
theorem point_links_checked14657 : (cuts14657.take 2).map (fun c => (1925054465-1+2*2^9*c.k,95964947186009+c.lower,95965325016364+c.upper)) = pointBounds14657 := by
 decide +kernel
def cuts14658 : List PrefixCut := [⟨9,63599729,63599772⟩,
⟨68,474870579,474870898⟩,
⟨127,887151904,887152503⟩,
⟨128,893438363,893438966⟩]
theorem checked14658 : checkPrefixCuts (2^48) 1925185537 9 Manual.Count131072.C014658.packed 128 cuts14658 = true := by
 decide +kernel
def pointBounds14658 : List (Nat × Nat × Nat) := [(1925194752,95965910279433,95966288110439),(1925255168,95966321550283,95966699381565),(1925315584,95966733831608,95967111663170)]
theorem point_links_checked14658 : (cuts14658.take 3).map (fun c => (1925185537-1+2*2^9*c.k,95965846679704+c.lower,95966224510667+c.upper)) = pointBounds14658 := by
 decide +kernel
def cuts14659 : List PrefixCut := [⟨58,406712918,406713187⟩,
⟨117,828763102,828763653⟩,
⟨128,906827043,906827646⟩]
theorem checked14659 : checkPrefixCuts (2^48) 1925316609 9 Manual.Count131072.C014659.packed 128 cuts14659 = true := by
 decide +kernel
def pointBounds14659 : List (Nat × Nat × Nat) := [(1925376000,95967146830985,95967524662820),(1925436416,95967568881169,95967946713286)]
theorem point_links_checked14659 : (cuts14659.take 2).map (fun c => (1925316609-1+2*2^9*c.k,95966740118067+c.lower,95967117949633+c.upper)) = pointBounds14659 := by
 decide +kernel
def cuts14660 : List PrefixCut := [⟨48,330377744,330377968⟩,
⟨107,741730206,741730706⟩,
⟨128,889077204,889077804⟩]
theorem checked14660 : checkPrefixCuts (2^48) 1925447681 9 Manual.Count131072.C014660.packed 128 cuts14660 = true := by
 decide +kernel
def pointBounds14660 : List (Nat × Nat × Nat) := [(1925496832,95967977322854,95968355155247),(1925557248,95968388675316,95968766507985)]
theorem point_links_checked14660 : (cuts14660.take 2).map (fun c => (1925447681-1+2*2^9*c.k,95967646945110+c.lower,95968024777279+c.upper)) = pointBounds14660 := by
 decide +kernel
def cuts14661 : List PrefixCut := [⟨38,263261714,263261890⟩,
⟨97,676196257,676196712⟩,
⟨128,891063308,891063910⟩]
theorem checked14661 : checkPrefixCuts (2^48) 1925578753 9 Manual.Count131072.C014661.packed 128 cuts14661 = true := by
 decide +kernel
def pointBounds14661 : List (Nat × Nat × Nat) := [(1925617664,95968799284028,95969177116973),(1925678080,95969212218571,95969590051795)]
theorem point_links_checked14661 : (cuts14661.take 2).map (fun c => (1925578753-1+2*2^9*c.k,95968536022314+c.lower,95968913855083+c.upper)) = pointBounds14661 := by
 decide +kernel
def cuts14662 : List PrefixCut := [⟨28,201416391,201416527⟩,
⟨87,614471161,614471578⟩,
⟨128,901380212,901380823⟩]
theorem checked14662 : checkPrefixCuts (2^48) 1925709825 9 Manual.Count131072.C014662.packed 128 cuts14662 = true := by
 decide +kernel
def pointBounds14662 : List (Nat × Nat × Nat) := [(1925738496,95969628502013,95970006335520),(1925798912,95970041556783,95970419390571)]
theorem point_links_checked14662 : (cuts14662.take 2).map (fun c => (1925709825-1+2*2^9*c.k,95969427085622+c.lower,95969804918993+c.upper)) = pointBounds14662 := by
 decide +kernel
def cuts14663 : List PrefixCut := [⟨18,123501974,123502058⟩,
⟨77,538430803,538431163⟩,
⟨128,894011073,894011670⟩]
theorem checked14663 : checkPrefixCuts (2^48) 1925840897 9 Manual.Count131072.C014663.packed 128 cuts14663 = true := by
 decide +kernel
def pointBounds14663 : List (Nat × Nat × Nat) := [(1925859328,95970451967808,95970829801874),(1925919744,95970866896637,95971244730979)]
theorem point_links_checked14663 : (cuts14663.take 2).map (fun c => (1925840897-1+2*2^9*c.k,95970328465834+c.lower,95970706299816+c.upper)) = pointBounds14663 := by
 decide +kernel
def cuts14664 : List PrefixCut := [⟨8,57143324,57143362⟩,
⟨67,471315498,471315812⟩,
⟨126,871152984,871153574⟩,
⟨128,884597593,884598192⟩]
theorem checked14664 : checkPrefixCuts (2^48) 1925971969 9 Manual.Count131072.C014664.packed 128 cuts14664 = true := by
 decide +kernel
def pointBounds14664 : List (Nat × Nat × Nat) := [(1925980160,95971279620231,95971657454848),(1926040576,95971693792405,95972071627298),(1926100992,95972093629891,95972471465060)]
theorem point_links_checked14664 : (cuts14664.take 3).map (fun c => (1925971969-1+2*2^9*c.k,95971222476907+c.lower,95971600311486+c.upper)) = pointBounds14664 := by
 decide +kernel
def cuts14665 : List PrefixCut := [⟨57,408300504,408300779⟩,
⟨116,812496813,812497359⟩,
⟨128,896081742,896082344⟩]
theorem checked14665 : checkPrefixCuts (2^48) 1926103041 9 Manual.Count131072.C014665.packed 128 cuts14665 = true := by
 decide +kernel
def pointBounds14665 : List (Nat × Nat × Nat) := [(1926161408,95972515375004,95972893210457),(1926221824,95972919571313,95973297407037)]
theorem point_links_checked14665 : (cuts14665.take 2).map (fun c => (1926103041-1+2*2^9*c.k,95972107074500+c.lower,95972484909678+c.upper)) = pointBounds14665 := by
 decide +kernel
def cuts14666 : List PrefixCut := [⟨47,335065135,335065357⟩,
⟨106,746249851,746250349⟩,
⟨128,901427141,901427741⟩]
theorem checked14666 : checkPrefixCuts (2^48) 1926234113 9 Manual.Count131072.C014666.packed 128 cuts14666 = true := by
 decide +kernel
def pointBounds14666 : List (Nat × Nat × Nat) := [(1926282240,95973338221377,95973716057379),(1926342656,95973749406093,95974127242371)]
theorem point_links_checked14666 : (cuts14666.take 2).map (fun c => (1926234113-1+2*2^9*c.k,95973003156242+c.lower,95973380992022+c.upper)) = pointBounds14666 := by
 decide +kernel
def cuts14667 : List PrefixCut := [⟨37,253364580,253364753⟩,
⟨96,659117455,659117898⟩,
⟨128,885731577,885732172⟩]
theorem checked14667 : checkPrefixCuts (2^48) 1926365185 9 Manual.Count131072.C014667.packed 128 cuts14667 = true := by
 decide +kernel
def pointBounds14667 : List (Nat × Nat × Nat) := [(1926403072,95974157947963,95974535784516),(1926463488,95974563700838,95974941537661)]
theorem point_links_checked14667 : (cuts14667.take 2).map (fun c => (1926365185-1+2*2^9*c.k,95973904583383+c.lower,95974282419763+c.upper)) = pointBounds14667 := by
 decide +kernel
def cuts14668 : List PrefixCut := [⟨27,190522367,190522493⟩,
⟨86,604431512,604431915⟩,
⟨128,895022156,895022753⟩]
theorem checked14668 : checkPrefixCuts (2^48) 1926496257 9 Manual.Count131072.C014668.packed 128 cuts14668 = true := by
 decide +kernel
def pointBounds14668 : List (Nat × Nat × Nat) := [(1926523904,95974980837327,95975358674428),(1926584320,95975394746472,95975772583850)]
theorem point_links_checked14668 : (cuts14668.take 2).map (fun c => (1926496257-1+2*2^9*c.k,95974790314960+c.lower,95975168151935+c.upper)) = pointBounds14668 := by
 decide +kernel
def cuts14669 : List PrefixCut := [⟨17,115562386,115562463⟩,
⟨76,526377563,526377920⟩,
⟨128,887948554,887949157⟩]
theorem checked14669 : checkPrefixCuts (2^48) 1926627329 9 Manual.Count131072.C014669.packed 128 cuts14669 = true := by
 decide +kernel
def pointBounds14669 : List (Nat × Nat × Nat) := [(1926644736,95975800899502,95976178737151),(1926705152,95976211714679,95976589552608)]
theorem point_links_checked14669 : (cuts14669.take 2).map (fun c => (1926627329-1+2*2^9*c.k,95975685337116+c.lower,95976063174688+c.upper)) = pointBounds14669 := by
 decide +kernel
def cuts14670 : List PrefixCut := [⟨7,50253931,50253964⟩,
⟨66,460897358,460897672⟩,
⟨125,870213225,870213813⟩,
⟨128,889203294,889203894⟩]
theorem checked14670 : checkPrefixCuts (2^48) 1926758401 9 Manual.Count131072.C014670.packed 128 cuts14670 = true := by
 decide +kernel
def pointBounds14670 : List (Nat × Nat × Nat) := [(1926765568,95976623539601,95977001377809),(1926825984,95977034183028,95977412021517),(1926886400,95977443498895,95977821337658)]
theorem point_links_checked14670 : (cuts14670.take 3).map (fun c => (1926758401-1+2*2^9*c.k,95976573285670+c.lower,95976951123845+c.upper)) = pointBounds14670 := by
 decide +kernel
def cuts14671 : List PrefixCut := [⟨56,400538182,400538452⟩,
⟨115,809536116,809536661⟩,
⟨128,903019570,903020174⟩]
theorem checked14671 : checkPrefixCuts (2^48) 1926889473 9 Manual.Count131072.C014671.packed 128 cuts14671 = true := by
 decide +kernel
def pointBounds14671 : List (Nat × Nat × Nat) := [(1926946816,95977863027146,95978240866191),(1927007232,95978272025080,95978649864400)]
theorem point_links_checked14671 : (cuts14671.take 2).map (fun c => (1926889473-1+2*2^9*c.k,95977462488964+c.lower,95977840327739+c.upper)) = pointBounds14671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000145
