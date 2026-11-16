import PlattAssemblyKernel
import PlattCertificates.Count131072.C014704
import PlattCertificates.Count131072.C014705
import PlattCertificates.Count131072.C014706
import PlattCertificates.Count131072.C014707
import PlattCertificates.Count131072.C014708
import PlattCertificates.Count131072.C014709
import PlattCertificates.Count131072.C014710
import PlattCertificates.Count131072.C014711
import PlattCertificates.Count131072.C014712
import PlattCertificates.Count131072.C014713
import PlattCertificates.Count131072.C014714
import PlattCertificates.Count131072.C014715
import PlattCertificates.Count131072.C014716
import PlattCertificates.Count131072.C014717
import PlattCertificates.Count131072.C014718
import PlattCertificates.Count131072.C014719
import PlattCertificates.Count131072.C014720
import PlattCertificates.Count131072.C014721
import PlattCertificates.Count131072.C014722
import PlattCertificates.Count131072.C014723
import PlattCertificates.Count131072.C014724
import PlattCertificates.Count131072.C014725
import PlattCertificates.Count131072.C014726
import PlattCertificates.Count131072.C014727
import PlattCertificates.Count131072.C014728
import PlattCertificates.Count131072.C014729
import PlattCertificates.Count131072.C014730
import PlattCertificates.Count131072.C014731
import PlattCertificates.Count131072.C014732
import PlattCertificates.Count131072.C014733
import PlattCertificates.Count131072.C014734
import PlattCertificates.Count131072.C014735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000147
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14704 : List PrefixCut := [⟨21,148955833,148955932⟩,
⟨80,558357062,558357434⟩,
⟨128,896916032,896916634⟩]
theorem checked14704 : checkPrefixCuts (2^48) 1931214849 9 Manual.Count131072.C014704.packed 128 cuts14704 = true := by
 decide +kernel
def pointBounds14704 : List (Nat × Nat × Nat) := [(1931236352,96007175020572,96007552879315),(1931296768,96007584421801,96007962280817)]
theorem point_links_checked14704 : (cuts14704.take 2).map (fun c => (1931214849-1+2*2^9*c.k,96007026064739+c.lower,96007403923383+c.upper)) = pointBounds14704 := by
 decide +kernel
def cuts14705 : List PrefixCut := [⟨11,75930469,75930519⟩,
⟨70,490844053,490844377⟩,
⟨128,898020945,898021540⟩]
theorem checked14705 : checkPrefixCuts (2^48) 1931345921 9 Manual.Count131072.C014705.packed 128 cuts14705 = true := by
 decide +kernel
def pointBounds14705 : List (Nat × Nat × Nat) := [(1931357184,96007998911240,96008376770536),(1931417600,96008413824824,96008791684394)]
theorem point_links_checked14705 : (cuts14705.take 2).map (fun c => (1931345921-1+2*2^9*c.k,96007922980771+c.lower,96008300840017+c.upper)) = pointBounds14705 := by
 decide +kernel
def cuts14706 : List PrefixCut := [⟨1,6266405,6266409⟩,
⟨60,411244564,411244841⟩,
⟨119,820581806,820582358⟩,
⟨128,882221717,882222309⟩]
theorem checked14706 : checkPrefixCuts (2^48) 1931476993 9 Manual.Count131072.C014706.packed 128 cuts14706 = true := by
 decide +kernel
def pointBounds14706 : List (Nat × Nat × Nat) := [(1931478016,96008827268121,96009205127966),(1931538432,96009232246280,96009610106398),(1931598848,96009641583522,96010019443915)]
theorem point_links_checked14706 : (cuts14706.take 3).map (fun c => (1931476993-1+2*2^9*c.k,96008821001716+c.lower,96009198861557+c.upper)) = pointBounds14706 := by
 decide +kernel
def cuts14707 : List PrefixCut := [⟨50,344624428,344624658⟩,
⟨109,755101710,755102221⟩,
⟨128,889447547,889448147⟩]
theorem checked14707 : checkPrefixCuts (2^48) 1931608065 9 Manual.Count131072.C014707.packed 128 cuts14707 = true := by
 decide +kernel
def pointBounds14707 : List (Nat × Nat × Nat) := [(1931659264,96010047847861,96010425708524),(1931719680,96010458325143,96010836186087)]
theorem point_links_checked14707 : (cuts14707.take 2).map (fun c => (1931608065-1+2*2^9*c.k,96009703223433+c.lower,96010081083866+c.upper)) = pointBounds14707 := by
 decide +kernel
def cuts14708 : List PrefixCut := [⟨40,276118744,276118928⟩,
⟨99,688027366,688027825⟩,
⟨128,890552907,890553503⟩]
theorem checked14708 : checkPrefixCuts (2^48) 1931739137 9 Manual.Count131072.C014708.packed 128 cuts14708 = true := by
 decide +kernel
def pointBounds14708 : List (Nat × Nat × Nat) := [(1931780096,96010868789724,96011246650941),(1931840512,96011280698346,96011658559838)]
theorem point_links_checked14708 : (cuts14708.take 2).map (fun c => (1931739137-1+2*2^9*c.k,96010592670980+c.lower,96010970532013+c.upper)) = pointBounds14708 := by
 decide +kernel
def cuts14709 : List PrefixCut := [⟨30,209515933,209516074⟩,
⟨89,626061169,626061588⟩,
⟨128,904333565,904334171⟩]
theorem checked14709 : checkPrefixCuts (2^48) 1931870209 9 Manual.Count131072.C014709.packed 128 cuts14709 = true := by
 decide +kernel
def pointBounds14709 : List (Nat × Nat × Nat) := [(1931900928,96011692739820,96012070601590),(1931961344,96012109285056,96012487147104)]
theorem point_links_checked14709 : (cuts14709.take 2).map (fun c => (1931870209-1+2*2^9*c.k,96011483223887+c.lower,96011861085516+c.upper)) = pointBounds14709 := by
 decide +kernel
def cuts14710 : List PrefixCut := [⟨20,138114193,138114286⟩,
⟨79,551719592,551719964⟩,
⟨128,896842321,896842923⟩]
theorem checked14710 : checkPrefixCuts (2^48) 1932001281 9 Manual.Count131072.C014710.packed 128 cuts14710 = true := by
 decide +kernel
def pointBounds14710 : List (Nat × Nat × Nat) := [(1932021760,96012525671645,96012903533973),(1932082176,96012939277044,96013317139651)]
theorem point_links_checked14710 : (cuts14710.take 2).map (fun c => (1932001281-1+2*2^9*c.k,96012387557452+c.lower,96012765419687+c.upper)) = pointBounds14710 := by
 decide +kernel
def cuts14711 : List PrefixCut := [⟨10,68615546,68615593⟩,
⟨69,478553121,478553440⟩,
⟨128,881922614,881923212⟩]
theorem checked14711 : checkPrefixCuts (2^48) 1932132353 9 Manual.Count131072.C014711.packed 128 cuts14711 = true := by
 decide +kernel
def pointBounds14711 : List (Nat × Nat × Nat) := [(1932142592,96013353015319,96013730878203),(1932203008,96013762952894,96014140816050),(1932263424,96014166322387,96014544185822)]
theorem point_links_checked14711 : (cuts14711.take 3).map (fun c => (1932132353-1+2*2^9*c.k,96013284399773+c.lower,96013662262610+c.upper)) = pointBounds14711 := by
 decide +kernel
def cuts14712 : List PrefixCut := [⟨59,414427586,414427863⟩,
⟨118,825055011,825055568⟩,
⟨128,894389922,894390528⟩]
theorem checked14712 : checkPrefixCuts (2^48) 1932263425 9 Manual.Count131072.C014712.packed 128 cuts14712 = true := by
 decide +kernel
def pointBounds14712 : List (Nat × Nat × Nat) := [(1932323840,96014580749973,96014958613685),(1932384256,96014991377398,96015369241390)]
theorem point_links_checked14712 : (cuts14712.take 2).map (fun c => (1932263425-1+2*2^9*c.k,96014166322387+c.lower,96014544185822+c.upper)) = pointBounds14712 := by
 decide +kernel
def cuts14713 : List PrefixCut := [⟨49,343318957,343319187⟩,
⟨108,749842376,749842885⟩,
⟨128,889231412,889232016⟩]
theorem checked14713 : checkPrefixCuts (2^48) 1932394497 9 Manual.Count131072.C014713.packed 128 cuts14713 = true := by
 decide +kernel
def pointBounds14713 : List (Nat × Nat × Nat) := [(1932444672,96015404031266,96015781895537),(1932505088,96015810554685,96016188419235)]
theorem point_links_checked14713 : (cuts14713.take 2).map (fun c => (1932394497-1+2*2^9*c.k,96015060712309+c.lower,96015438576350+c.upper)) = pointBounds14713 := by
 decide +kernel
def cuts14714 : List PrefixCut := [⟨39,275278166,275278352⟩,
⟨98,687893357,687893817⟩,
⟨128,889754002,889754598⟩]
theorem checked14714 : checkPrefixCuts (2^48) 1932525569 9 Manual.Count131072.C014714.packed 128 cuts14714 = true := by
 decide +kernel
def pointBounds14714 : List (Nat × Nat × Nat) := [(1932565504,96016225221887,96016603086718),(1932625920,96016637837078,96017015702183)]
theorem point_links_checked14714 : (cuts14714.take 2).map (fun c => (1932525569-1+2*2^9*c.k,96015949943721+c.lower,96016327808366+c.upper)) = pointBounds14714 := by
 decide +kernel
def cuts14715 : List PrefixCut := [⟨29,206081055,206081191⟩,
⟨88,617214031,617214443⟩,
⟨128,901198593,901199195⟩]
theorem checked14715 : checkPrefixCuts (2^48) 1932656641 9 Manual.Count131072.C014715.packed 128 cuts14715 = true := by
 decide +kernel
def pointBounds14715 : List (Nat × Nat × Nat) := [(1932686336,96017045778778,96017423644155),(1932746752,96017456911754,96017834777407)]
theorem point_links_checked14715 : (cuts14715.take 2).map (fun c => (1932656641-1+2*2^9*c.k,96016839697723+c.lower,96017217562964+c.upper)) = pointBounds14715 := by
 decide +kernel
def cuts14716 : List PrefixCut := [⟨19,129611437,129611526⟩,
⟨78,548000132,548000507⟩,
⟨128,901137355,901137966⟩]
theorem checked14716 : checkPrefixCuts (2^48) 1932787713 9 Manual.Count131072.C014716.packed 128 cuts14716 = true := by
 decide +kernel
def pointBounds14716 : List (Nat × Nat × Nat) := [(1932807168,96017870507753,96018248373685),(1932867584,96018288896448,96018666762666)]
theorem point_links_checked14716 : (cuts14716.take 2).map (fun c => (1932787713-1+2*2^9*c.k,96017740896316+c.lower,96018118762159+c.upper)) = pointBounds14716 := by
 decide +kernel
def cuts14717 : List PrefixCut := [⟨9,63782145,63782188⟩,
⟨68,471368917,471369238⟩,
⟨127,886078070,886078672⟩,
⟨128,893504274,893504881⟩]
theorem checked14717 : checkPrefixCuts (2^48) 1932918785 9 Manual.Count131072.C014717.packed 128 cuts14717 = true := by
 decide +kernel
def pointBounds14717 : List (Nat × Nat × Nat) := [(1932928000,96018705815816,96019083682313),(1932988416,96019113402588,96019491269363),(1933048832,96019528111741,96019905978797)]
theorem point_links_checked14717 : (cuts14717.take 3).map (fun c => (1932918785-1+2*2^9*c.k,96018642033671+c.lower,96019019900125+c.upper)) = pointBounds14717 := by
 decide +kernel
def cuts14718 : List PrefixCut := [⟨58,406105071,406105347⟩,
⟨117,817439318,817439865⟩,
⟨128,894899776,894900374⟩]
theorem checked14718 : checkPrefixCuts (2^48) 1933049857 9 Manual.Count131072.C014718.packed 128 cuts14718 = true := by
 decide +kernel
def pointBounds14718 : List (Nat × Nat × Nat) := [(1933109248,96019941643016,96020319510353),(1933169664,96020352977263,96020730844871)]
theorem point_links_checked14718 : (cuts14718.take 2).map (fun c => (1933049857-1+2*2^9*c.k,96019535537945+c.lower,96019913405006+c.upper)) = pointBounds14718 := by
 decide +kernel
def cuts14719 : List PrefixCut := [⟨48,340849807,340850035⟩,
⟨107,751721567,751722073⟩,
⟨128,900808653,900809259⟩]
theorem checked14719 : checkPrefixCuts (2^48) 1933180929 9 Manual.Count131072.C014719.packed 128 cuts14719 = true := by
 decide +kernel
def pointBounds14719 : List (Nat × Nat × Nat) := [(1933230080,96020771287528,96021149155415),(1933290496,96021182159288,96021560027453)]
theorem point_links_checked14719 : (cuts14719.take 2).map (fun c => (1933180929-1+2*2^9*c.k,96020430437721+c.lower,96020808305380+c.upper)) = pointBounds14719 := by
 decide +kernel
def cuts14720 : List PrefixCut := [⟨38,261626317,261626494⟩,
⟨98,686594223,686594678⟩,
⟨128,892303508,892304104⟩]
theorem checked14720 : checkPrefixCuts (2^48) 1933312001 9 Manual.Count131072.C014720.packed 128 cuts14720 = true := by
 decide +kernel
def pointBounds14720 : List (Nat × Nat × Nat) := [(1933350912,96021592872691,96021970741133),(1933412352,96022017840597,96022395709317)]
theorem point_links_checked14720 : (cuts14720.take 2).map (fun c => (1933312001-1+2*2^9*c.k,96021331246374+c.lower,96021709114639+c.upper)) = pointBounds14720 := by
 decide +kernel
def cuts14721 : List PrefixCut := [⟨30,208035293,208035434⟩,
⟨90,621184394,621184814⟩,
⟨128,884236280,884236878⟩]
theorem checked14721 : checkPrefixCuts (2^48) 1933443073 9 Manual.Count131072.C014721.packed 128 cuts14721 = true := by
 decide +kernel
def pointBounds14721 : List (Nat × Nat × Nat) := [(1933473792,96022431585175,96022809454177),(1933535232,96022844734276,96023222603557)]
theorem point_links_checked14721 : (cuts14721.take 2).map (fun c => (1933443073-1+2*2^9*c.k,96022223549882+c.lower,96022601418743+c.upper)) = pointBounds14721 := by
 decide +kernel
def cuts14722 : List PrefixCut := [⟨22,148046209,148046310⟩,
⟨82,574997972,574998359⟩,
⟨128,896840558,896841160⟩]
theorem checked14722 : checkPrefixCuts (2^48) 1933574145 9 Manual.Count131072.C014722.packed 128 cuts14722 = true := by
 decide +kernel
def pointBounds14722 : List (Nat × Nat × Nat) := [(1933596672,96023255832371,96023633701931),(1933658112,96023682784134,96024060653980)]
theorem point_links_checked14722 : (cuts14722.take 2).map (fun c => (1933574145-1+2*2^9*c.k,96023107786162+c.lower,96023485655621+c.upper)) = pointBounds14722 := by
 decide +kernel
def cuts14723 : List PrefixCut := [⟨14,100001037,100001104⟩,
⟨74,507275274,507275614⟩,
⟨128,878439608,878440202⟩]
theorem checked14723 : checkPrefixCuts (2^48) 1933705217 9 Manual.Count131072.C014723.packed 128 cuts14723 = true := by
 decide +kernel
def pointBounds14723 : List (Nat × Nat × Nat) := [(1933719552,96024104627757,96024482497885),(1933780992,96024511901994,96024889772395)]
theorem point_links_checked14723 : (cuts14723.take 2).map (fun c => (1933705217-1+2*2^9*c.k,96024004626720+c.lower,96024382496781+c.upper)) = pointBounds14723 := by
 decide +kernel
def cuts14724 : List PrefixCut := [⟨6,39444688,39444715⟩,
⟨66,458628289,458628600⟩,
⟨126,876634126,876634719⟩,
⟨128,889441892,889442494⟩]
theorem checked14724 : checkPrefixCuts (2^48) 1933836289 9 Manual.Count131072.C014724.packed 128 cuts14724 = true := by
 decide +kernel
def pointBounds14724 : List (Nat × Nat × Nat) := [(1933842432,96024922511016,96025300381698),(1933903872,96025341694617,96025719565583),(1933965312,96025759700454,96026137571702)]
theorem point_links_checked14724 : (cuts14724.take 3).map (fun c => (1933836289-1+2*2^9*c.k,96024883066328+c.lower,96025260936983+c.upper)) = pointBounds14724 := by
 decide +kernel
def cuts14725 : List PrefixCut := [⟨58,408823322,408823591⟩,
⟨118,833060580,833061137⟩,
⟨128,900442481,900443085⟩]
theorem checked14725 : checkPrefixCuts (2^48) 1933967361 9 Manual.Count131072.C014725.packed 128 cuts14725 = true := by
 decide +kernel
def pointBounds14725 : List (Nat × Nat × Nat) := [(1934026752,96026181331542,96026559203068),(1934088192,96026605568800,96026983440614)]
theorem point_links_checked14725 : (cuts14725.take 2).map (fun c => (1933967361-1+2*2^9*c.k,96025772508220+c.lower,96026150379477+c.upper)) = pointBounds14725 := by
 decide +kernel
def cuts14726 : List PrefixCut := [⟨50,342579838,342580068⟩,
⟨110,766499117,766499630⟩,
⟨128,892668146,892668745⟩]
theorem checked14726 : checkPrefixCuts (2^48) 1934098433 9 Manual.Count131072.C014726.packed 128 cuts14726 = true := by
 decide +kernel
def pointBounds14726 : List (Nat × Nat × Nat) := [(1934149632,96027015530539,96027393402630),(1934211072,96027439449818,96027817322192)]
theorem point_links_checked14726 : (cuts14726.take 2).map (fun c => (1934098433-1+2*2^9*c.k,96026672950701+c.lower,96027050822562+c.upper)) = pointBounds14726 := by
 decide +kernel
def cuts14727 : List PrefixCut := [⟨42,292497977,292498179⟩,
⟨102,716681362,716681846⟩,
⟨128,897991977,897992586⟩]
theorem checked14727 : checkPrefixCuts (2^48) 1934229505 9 Manual.Count131072.C014727.packed 128 cuts14727 = true := by
 decide +kernel
def pointBounds14727 : List (Nat × Nat × Nat) := [(1934272512,96027858116824,96028235989486),(1934333952,96028282300209,96028660173153)]
theorem point_links_checked14727 : (cuts14727.take 2).map (fun c => (1934229505-1+2*2^9*c.k,96027565618847+c.lower,96027943491307+c.upper)) = pointBounds14727 := by
 decide +kernel
def cuts14728 : List PrefixCut := [⟨34,237038779,237038945⟩,
⟨94,643879826,643880267⟩,
⟨128,886144985,886145584⟩]
theorem checked14728 : checkPrefixCuts (2^48) 1934360577 9 Manual.Count131072.C014728.packed 128 cuts14728 = true := by
 decide +kernel
def pointBounds14728 : List (Nat × Nat × Nat) := [(1934395392,96028700649603,96029078522838),(1934456832,96029107490650,96029485364160)]
theorem point_links_checked14728 : (cuts14728.take 2).map (fun c => (1934360577-1+2*2^9*c.k,96028463610824+c.lower,96028841483893+c.upper)) = pointBounds14728 := by
 decide +kernel
def cuts14729 : List PrefixCut := [⟨26,178676800,178676924⟩,
⟨86,599314311,599314709⟩,
⟨128,889867966,889868562⟩]
theorem checked14729 : checkPrefixCuts (2^48) 1934491649 9 Manual.Count131072.C014729.packed 128 cuts14729 = true := by
 decide +kernel
def pointBounds14729 : List (Nat × Nat × Nat) := [(1934518272,96029528432609,96029906306401),(1934579712,96029949070120,96030326944186)]
theorem point_links_checked14729 : (cuts14729.take 2).map (fun c => (1934491649-1+2*2^9*c.k,96029349755809+c.lower,96029727629477+c.upper)) = pointBounds14729 := by
 decide +kernel
def cuts14730 : List PrefixCut := [⟨18,126578669,126578753⟩,
⟨78,547044052,547044414⟩,
⟨128,890244361,890244952⟩]
theorem checked14730 : checkPrefixCuts (2^48) 1934622721 9 Manual.Count131072.C014730.packed 128 cuts14730 = true := by
 decide +kernel
def pointBounds14730 : List (Nat × Nat × Nat) := [(1934641152,96030366202444,96030744076792),(1934702592,96030786667827,96031164542453)]
theorem point_links_checked14730 : (cuts14730.take 2).map (fun c => (1934622721-1+2*2^9*c.k,96030239623775+c.lower,96030617498039+c.upper)) = pointBounds14730 := by
 decide +kernel
def cuts14731 : List PrefixCut := [⟨10,71868685,71868732⟩,
⟨70,485324213,485324535⟩,
⟨128,885092090,885092680⟩]
theorem checked14731 : checkPrefixCuts (2^48) 1934753793 9 Manual.Count131072.C014731.packed 128 cuts14731 = true := by
 decide +kernel
def pointBounds14731 : List (Nat × Nat × Nat) := [(1934764032,96031201736821,96031579611723),(1934825472,96031615192349,96031993067526)]
theorem point_links_checked14731 : (cuts14731.take 2).map (fun c => (1934753793-1+2*2^9*c.k,96031129868136+c.lower,96031507742991+c.upper)) = pointBounds14731 := by
 decide +kernel
def cuts14732 : List PrefixCut := [⟨2,14838310,14838320⟩,
⟨62,436414001,436414300⟩,
⟨122,854485130,854485711⟩,
⟨128,899433532,899434143⟩]
theorem checked14732 : checkPrefixCuts (2^48) 1934884865 9 Manual.Count131072.C014732.packed 128 cuts14732 = true := by
 decide +kernel
def pointBounds14732 : List (Nat × Nat × Nat) := [(1934886912,96032029798536,96032407673991),(1934948352,96032451374227,96032829249971),(1935009792,96032869445356,96033247321382)]
theorem point_links_checked14732 : (cuts14732.take 3).map (fun c => (1934884865-1+2*2^9*c.k,96032014960226+c.lower,96032392835671+c.upper)) = pointBounds14732 := by
 decide +kernel
def cuts14733 : List PrefixCut := [⟨54,394928676,394928939⟩,
⟨114,811664071,811664614⟩,
⟨128,909409535,909410144⟩]
theorem checked14733 : checkPrefixCuts (2^48) 1935015937 9 Manual.Count131072.C014733.packed 128 cuts14733 = true := by
 decide +kernel
def pointBounds14733 : List (Nat × Nat × Nat) := [(1935071232,96033309322434,96033687198753),(1935132672,96033726057829,96034103934428)]
theorem point_links_checked14733 : (cuts14733.take 2).map (fun c => (1935015937-1+2*2^9*c.k,96032914393758+c.lower,96033292269814+c.upper)) = pointBounds14733 := by
 decide +kernel
def cuts14734 : List PrefixCut := [⟨46,321449449,321449658⟩,
⟨106,739612904,739613392⟩,
⟨128,894366398,894366992⟩]
theorem checked14734 : checkPrefixCuts (2^48) 1935147009 9 Manual.Count131072.C014734.packed 128 cuts14734 = true := by
 decide +kernel
def pointBounds14734 : List (Nat × Nat × Nat) := [(1935194112,96034145252742,96034523129616),(1935255552,96034563416197,96034941293350)]
theorem point_links_checked14734 : (cuts14734.take 2).map (fun c => (1935147009-1+2*2^9*c.k,96033823803293+c.lower,96034201679958+c.upper)) = pointBounds14734 := by
 decide +kernel
def cuts14735 : List PrefixCut := [⟨38,262378572,262378747⟩,
⟨98,676297766,676298220⟩,
⟨128,893432899,893433500⟩]
theorem checked14735 : checkPrefixCuts (2^48) 1935278081 9 Manual.Count131072.C014735.packed 128 cuts14735 = true := by
 decide +kernel
def pointBounds14735 : List (Nat × Nat × Nat) := [(1935316992,96034980548263,96035358425697),(1935378432,96035394467457,96035772345170)]
theorem point_links_checked14735 : (cuts14735.take 2).map (fun c => (1935278081-1+2*2^9*c.k,96034718169691+c.lower,96035096046950+c.upper)) = pointBounds14735 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000147
