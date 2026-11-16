import PlattAssemblyKernel
import PlattCertificates.Count131072.C014736
import PlattCertificates.Count131072.C014737
import PlattCertificates.Count131072.C014738
import PlattCertificates.Count131072.C014739
import PlattCertificates.Count131072.C014740
import PlattCertificates.Count131072.C014741
import PlattCertificates.Count131072.C014742
import PlattCertificates.Count131072.C014743
import PlattCertificates.Count131072.C014744
import PlattCertificates.Count131072.C014745
import PlattCertificates.Count131072.C014746
import PlattCertificates.Count131072.C014747
import PlattCertificates.Count131072.C014748
import PlattCertificates.Count131072.C014749
import PlattCertificates.Count131072.C014750
import PlattCertificates.Count131072.C014751
import PlattCertificates.Count131072.C014752
import PlattCertificates.Count131072.C014753
import PlattCertificates.Count131072.C014754
import PlattCertificates.Count131072.C014755
import PlattCertificates.Count131072.C014756
import PlattCertificates.Count131072.C014757
import PlattCertificates.Count131072.C014758
import PlattCertificates.Count131072.C014759
import PlattCertificates.Count131072.C014760
import PlattCertificates.Count131072.C014761
import PlattCertificates.Count131072.C014762
import PlattCertificates.Count131072.C014763
import PlattCertificates.Count131072.C014764
import PlattCertificates.Count131072.C014765
import PlattCertificates.Count131072.C014766
import PlattCertificates.Count131072.C014767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14736 : List PrefixCut := [⟨30,207096818,207096957⟩,
⟨90,618953625,618954045⟩,
⟨128,883337925,883338523⟩]
theorem checked14736 : checkPrefixCuts (2^48) 1935409153 9 Manual.Count131072.C014736.packed 128 cuts14736 = true := by
 decide +kernel
def pointBounds14736 : List (Nat × Nat × Nat) := [(1935439872,96035818699408,96036196577407),(1935501312,96036230556215,96036608434495)]
theorem point_links_checked14736 : (cuts14736.take 2).map (fun c => (1935409153-1+2*2^9*c.k,96035611602590+c.lower,96035989480450+c.upper)) = pointBounds14736 := by
 decide +kernel
def cuts14737 : List PrefixCut := [⟨22,151095119,151095219⟩,
⟨82,568451772,568452153⟩,
⟨128,893166526,893167127⟩]
theorem checked14737 : checkPrefixCuts (2^48) 1935540225 9 Manual.Count131072.C014737.packed 128 cuts14737 = true := by
 decide +kernel
def pointBounds14737 : List (Nat × Nat × Nat) := [(1935562752,96036646035634,96037023914192),(1935624192,96037063392287,96037441271126)]
theorem point_links_checked14737 : (cuts14737.take 2).map (fun c => (1935540225-1+2*2^9*c.k,96036494940515+c.lower,96036872818973+c.upper)) = pointBounds14737 := by
 decide +kernel
def cuts14738 : List PrefixCut := [⟨14,94373727,94373792⟩,
⟨74,509959015,509959360⟩,
⟨128,885254045,885254642⟩]
theorem checked14738 : checkPrefixCuts (2^48) 1935671297 9 Manual.Count131072.C014738.packed 128 cuts14738 = true := by
 decide +kernel
def pointBounds14738 : List (Nat × Nat × Nat) := [(1935685632,96037482480768,96037860359892),(1935747072,96037898066056,96038275945460)]
theorem point_links_checked14738 : (cuts14738.take 2).map (fun c => (1935671297-1+2*2^9*c.k,96037388107041+c.lower,96037765986100+c.upper)) = pointBounds14738 := by
 decide +kernel
def cuts14739 : List PrefixCut := [⟨6,40567865,40567894⟩,
⟨66,461070375,461070691⟩,
⟨126,877343038,877343636⟩,
⟨128,892318723,892319330⟩]
theorem checked14739 : checkPrefixCuts (2^48) 1935802369 9 Manual.Count131072.C014739.packed 128 cuts14739 = true := by
 decide +kernel
def pointBounds14739 : List (Nat × Nat × Nat) := [(1935808512,96038313928951,96038691808636),(1935869952,96038734431461,96039112311433),(1935931392,96039150704124,96039528584378)]
theorem point_links_checked14739 : (cuts14739.take 3).map (fun c => (1935802369-1+2*2^9*c.k,96038273361086+c.lower,96038651240742+c.upper)) = pointBounds14739 := by
 decide +kernel
def cuts14740 : List PrefixCut := [⟨58,400847662,400847934⟩,
⟨118,815930908,815931461⟩,
⟨128,892258271,892258875⟩]
theorem checked14740 : checkPrefixCuts (2^48) 1935933441 9 Manual.Count131072.C014740.packed 128 cuts14740 = true := by
 decide +kernel
def pointBounds14740 : List (Nat × Nat × Nat) := [(1935992832,96039566527471,96039944408006),(1936054272,96039981610717,96040359491533)]
theorem point_links_checked14740 : (cuts14740.take 2).map (fun c => (1935933441-1+2*2^9*c.k,96039165679809+c.lower,96039543560072+c.upper)) = pointBounds14740 := by
 decide +kernel
def cuts14741 : List PrefixCut := [⟨50,346011913,346012146⟩,
⟨110,759469609,759470119⟩,
⟨128,888708798,888709393⟩]
theorem checked14741 : checkPrefixCuts (2^48) 1936064513 9 Manual.Count131072.C014741.packed 128 cuts14741 = true := by
 decide +kernel
def pointBounds14741 : List (Nat × Nat × Nat) := [(1936115712,96040403949993,96040781831093),(1936177152,96040817407689,96041195289066)]
theorem point_links_checked14741 : (cuts14741.take 2).map (fun c => (1936064513-1+2*2^9*c.k,96040057938080+c.lower,96040435818947+c.upper)) = pointBounds14741 := by
 decide +kernel
def cuts14742 : List PrefixCut := [⟨42,292637078,292637275⟩,
⟨102,713773107,713773592⟩,
⟨128,891410868,891411474⟩]
theorem checked14742 : checkPrefixCuts (2^48) 1936195585 9 Manual.Count131072.C014742.packed 128 cuts14742 = true := by
 decide +kernel
def pointBounds14742 : List (Nat × Nat × Nat) := [(1936238592,96041239283956,96041617165615),(1936300032,96041660419985,96042038301932)]
theorem point_links_checked14742 : (cuts14742.take 2).map (fun c => (1936195585-1+2*2^9*c.k,96040946646878+c.lower,96041324528340+c.upper)) = pointBounds14742 := by
 decide +kernel
def cuts14743 : List PrefixCut := [⟨34,239269322,239269486⟩,
⟨94,659070363,659070811⟩,
⟨128,903560637,903561246⟩]
theorem checked14743 : checkPrefixCuts (2^48) 1936326657 9 Manual.Count131072.C014743.packed 128 cuts14743 = true := by
 decide +kernel
def pointBounds14743 : List (Nat × Nat × Nat) := [(1936361472,96042077327068,96042455209300),(1936422912,96042497128109,96042875010625)]
theorem point_links_checked14743 : (cuts14743.take 2).map (fun c => (1936326657-1+2*2^9*c.k,96041838057746+c.lower,96042215939814+c.upper)) = pointBounds14743 := by
 decide +kernel
def cuts14744 : List PrefixCut := [⟨26,179512876,179512994⟩,
⟨86,593182568,593182965⟩,
⟨128,886638769,886639365⟩]
theorem checked14744 : checkPrefixCuts (2^48) 1936457729 9 Manual.Count131072.C014744.packed 128 cuts14744 = true := by
 decide +kernel
def pointBounds14744 : List (Nat × Nat × Nat) := [(1936484352,96042921131259,96043299014054),(1936545792,96043334800951,96043712684025)]
theorem point_links_checked14744 : (cuts14744.take 2).map (fun c => (1936457729-1+2*2^9*c.k,96042741618383+c.lower,96043119501060+c.upper)) = pointBounds14744 := by
 decide +kernel
def cuts14745 : List PrefixCut := [⟨18,124560680,124560766⟩,
⟨78,546052592,546052960⟩,
⟨128,895008604,895009207⟩]
theorem checked14745 : checkPrefixCuts (2^48) 1936588801 9 Manual.Count131072.C014745.packed 128 cuts14745 = true := by
 decide +kernel
def pointBounds14745 : List (Nat × Nat × Nat) := [(1936607232,96043752817832,96044130701191),(1936668672,96044174309744,96044552193385)]
theorem point_links_checked14745 : (cuts14745.take 2).map (fun c => (1936588801-1+2*2^9*c.k,96043628257152+c.lower,96044006140425+c.upper)) = pointBounds14745 := by
 decide +kernel
def cuts14746 : List PrefixCut := [⟨10,70051709,70051756⟩,
⟨70,495731450,495731783⟩,
⟨128,893494933,893495533⟩]
theorem checked14746 : checkPrefixCuts (2^48) 1936719873 9 Manual.Count131072.C014746.packed 128 cuts14746 = true := by
 decide +kernel
def pointBounds14746 : List (Nat × Nat × Nat) := [(1936730112,96044593317465,96044971201388),(1936791552,96045018997206,96045396881415)]
theorem point_links_checked14746 : (cuts14746.take 2).map (fun c => (1936719873-1+2*2^9*c.k,96044523265756+c.lower,96044901149632+c.upper)) = pointBounds14746 := by
 decide +kernel
def cuts14747 : List PrefixCut := [⟨2,12498033,12498041⟩,
⟨62,435971038,435971330⟩,
⟨122,849694051,849694624⟩,
⟨128,891981134,891981736⟩]
theorem checked14747 : checkPrefixCuts (2^48) 1936850945 9 Manual.Count131072.C014747.packed 128 cuts14747 = true := by
 decide +kernel
def pointBounds14747 : List (Nat × Nat × Nat) := [(1936852992,96045429258722,96045807143206),(1936914432,96045852731727,96046230616495),(1936975872,96046266454740,96046644339789)]
theorem point_links_checked14747 : (cuts14747.take 3).map (fun c => (1936850945-1+2*2^9*c.k,96045416760689+c.lower,96045794645165+c.upper)) = pointBounds14747 := by
 decide +kernel
def cuts14748 : List PrefixCut := [⟨54,371132314,371132563⟩,
⟨114,792675910,792676442⟩,
⟨128,890176862,890177460⟩]
theorem checked14748 : checkPrefixCuts (2^48) 1936982017 9 Manual.Count131072.C014748.packed 128 cuts14748 = true := by
 decide +kernel
def pointBounds14748 : List (Nat × Nat × Nat) := [(1937037312,96046679874137,96047057759464),(1937098752,96047101417733,96047479303343)]
theorem point_links_checked14748 : (cuts14748.take 2).map (fun c => (1936982017-1+2*2^9*c.k,96046308741823+c.lower,96046686626901+c.upper)) = pointBounds14748 := by
 decide +kernel
def cuts14749 : List PrefixCut := [⟨46,312840834,312841043⟩,
⟨106,729126807,729127298⟩,
⟨128,884595007,884595603⟩]
theorem checked14749 : checkPrefixCuts (2^48) 1937113089 9 Manual.Count131072.C014749.packed 128 cuts14749 = true := by
 decide +kernel
def pointBounds14749 : List (Nat × Nat × Nat) := [(1937160192,96047511759519,96047889645404),(1937221632,96047928045492,96048305931659)]
theorem point_links_checked14749 : (cuts14749.take 2).map (fun c => (1937113089-1+2*2^9*c.k,96047198918685+c.lower,96047576804361+c.upper)) = pointBounds14749 := by
 decide +kernel
def cuts14750 : List PrefixCut := [⟨38,261531148,261531323⟩,
⟨98,678662568,678663025⟩,
⟨128,889329953,889330551⟩]
theorem checked14750 : checkPrefixCuts (2^48) 1937244161 9 Manual.Count131072.C014750.packed 128 cuts14750 = true := by
 decide +kernel
def pointBounds14750 : List (Nat × Nat × Nat) := [(1937283072,96048345044840,96048722931287),(1937344512,96048762176260,96049140062989)]
theorem point_links_checked14750 : (cuts14750.take 2).map (fun c => (1937244161-1+2*2^9*c.k,96048083513692+c.lower,96048461399964+c.upper)) = pointBounds14750 := by
 decide +kernel
def cuts14751 : List PrefixCut := [⟨30,202673360,202673500⟩,
⟨90,620650006,620650429⟩,
⟨128,880843546,880844141⟩]
theorem checked14751 : checkPrefixCuts (2^48) 1937375233 9 Manual.Count131072.C014751.packed 128 cuts14751 = true := by
 decide +kernel
def pointBounds14751 : List (Nat × Nat × Nat) := [(1937405952,96049175517005,96049553404015),(1937467392,96049593493651,96049971380944)]
theorem point_links_checked14751 : (cuts14751.take 2).map (fun c => (1937375233-1+2*2^9*c.k,96048972843645+c.lower,96049350730515+c.upper)) = pointBounds14751 := by
 decide +kernel
def cuts14752 : List PrefixCut := [⟨22,153556783,153556888⟩,
⟨82,565986555,565986936⟩,
⟨128,884706299,884706896⟩]
theorem checked14752 : checkPrefixCuts (2^48) 1937506305 9 Manual.Count131072.C014752.packed 128 cuts14752 = true := by
 decide +kernel
def pointBounds14752 : List (Nat × Nat × Nat) := [(1937528832,96050007243974,96050385131544),(1937590272,96050419673746,96050797561592)]
theorem point_links_checked14752 : (cuts14752.take 2).map (fun c => (1937506305-1+2*2^9*c.k,96049853687191+c.lower,96050231574656+c.upper)) = pointBounds14752 := by
 decide +kernel
def cuts14753 : List PrefixCut := [⟨14,95004299,95004363⟩,
⟨74,513218388,513218736⟩,
⟨128,877673924,877674516⟩]
theorem checked14753 : checkPrefixCuts (2^48) 1937637377 9 Manual.Count131072.C014753.packed 128 cuts14753 = true := by
 decide +kernel
def pointBounds14753 : List (Nat × Nat × Nat) := [(1937651712,96050833397789,96051211285915),(1937713152,96051251611878,96051629500288)]
theorem point_links_checked14753 : (cuts14753.take 2).map (fun c => (1937637377-1+2*2^9*c.k,96050738393490+c.lower,96051116281552+c.upper)) = pointBounds14753 := by
 decide +kernel
def cuts14754 : List PrefixCut := [⟨6,39509904,39509932⟩,
⟨66,460747803,460748115⟩,
⟨126,880084190,880084779⟩,
⟨128,894027949,894028548⟩]
theorem checked14754 : checkPrefixCuts (2^48) 1937768449 9 Manual.Count131072.C014754.packed 128 cuts14754 = true := by
 decide +kernel
def pointBounds14754 : List (Nat × Nat × Nat) := [(1937774592,96051655577318,96052033466000),(1937836032,96052076815217,96052454704183),(1937897472,96052496151604,96052874040847)]
theorem point_links_checked14754 : (cuts14754.take 3).map (fun c => (1937768449-1+2*2^9*c.k,96051616067414+c.lower,96051993956068+c.upper)) = pointBounds14754 := by
 decide +kernel
def cuts14755 : List PrefixCut := [⟨58,406831712,406831979⟩,
⟨118,821784244,821784789⟩,
⟨128,892660370,892660963⟩]
theorem checked14755 : checkPrefixCuts (2^48) 1937899521 9 Manual.Count131072.C014755.packed 128 cuts14755 = true := by
 decide +kernel
def pointBounds14755 : List (Nat × Nat × Nat) := [(1937958912,96052916927075,96053294816595),(1938020352,96053331879607,96053709769405)]
theorem point_links_checked14755 : (cuts14755.take 2).map (fun c => (1937899521-1+2*2^9*c.k,96052510095363+c.lower,96052887984616+c.upper)) = pointBounds14755 := by
 decide +kernel
def cuts14756 : List PrefixCut := [⟨50,349872779,349873014⟩,
⟨110,761603882,761604394⟩,
⟨128,892454713,892455312⟩]
theorem checked14756 : checkPrefixCuts (2^48) 1938030593 9 Manual.Count131072.C014756.packed 128 cuts14756 = true := by
 decide +kernel
def pointBounds14756 : List (Nat × Nat × Nat) := [(1938081792,96053752628512,96054130518593),(1938143232,96054164359615,96054542249973)]
theorem point_links_checked14756 : (cuts14756.take 2).map (fun c => (1938030593-1+2*2^9*c.k,96053402755733+c.lower,96053780645579+c.upper)) = pointBounds14756 := by
 decide +kernel
def cuts14757 : List PrefixCut := [⟨42,288709602,288709797⟩,
⟨102,705352162,705352635⟩,
⟨128,885278469,885279066⟩]
theorem checked14757 : checkPrefixCuts (2^48) 1938161665 9 Manual.Count131072.C014757.packed 128 cuts14757 = true := by
 decide +kernel
def pointBounds14757 : List (Nat × Nat × Nat) := [(1938204672,96054583920048,96054961810688),(1938266112,96055000562608,96055378453526)]
theorem point_links_checked14757 : (cuts14757.take 2).map (fun c => (1938161665-1+2*2^9*c.k,96054295210446+c.lower,96054673100891+c.upper)) = pointBounds14757 := by
 decide +kernel
def cuts14758 : List PrefixCut := [⟨34,235686585,235686746⟩,
⟨94,647946410,647946848⟩,
⟨128,880136316,880136910⟩]
theorem checked14758 : checkPrefixCuts (2^48) 1938292737 9 Manual.Count131072.C014758.packed 128 cuts14758 = true := by
 decide +kernel
def pointBounds14758 : List (Nat × Nat × Nat) := [(1938327552,96055416175500,96055794066703),(1938388992,96055828435325,96056206326805)]
theorem point_links_checked14758 : (cuts14758.take 2).map (fun c => (1938292737-1+2*2^9*c.k,96055180488915+c.lower,96055558379957+c.upper)) = pointBounds14758 := by
 decide +kernel
def cuts14759 : List PrefixCut := [⟨26,182380137,182380261⟩,
⟨86,603906757,603907170⟩,
⟨128,893725777,893726385⟩]
theorem checked14759 : checkPrefixCuts (2^48) 1938423809 9 Manual.Count131072.C014759.packed 128 cuts14759 = true := by
 decide +kernel
def pointBounds14759 : List (Nat × Nat × Nat) := [(1938450432,96056243005368,96056620897128),(1938511872,96056664531988,96057042424037)]
theorem point_links_checked14759 : (cuts14759.take 2).map (fun c => (1938423809-1+2*2^9*c.k,96056060625231+c.lower,96056438516867+c.upper)) = pointBounds14759 := by
 decide +kernel
def cuts14760 : List PrefixCut := [⟨18,124579554,124579638⟩,
⟨78,543175774,543176136⟩,
⟨128,888874125,888874718⟩]
theorem checked14760 : checkPrefixCuts (2^48) 1938554881 9 Manual.Count131072.C014760.packed 128 cuts14760 = true := by
 decide +kernel
def pointBounds14760 : List (Nat × Nat × Nat) := [(1938573312,96057078930562,96057456822890),(1938634752,96057497526782,96057875419388)]
theorem point_links_checked14760 : (cuts14760.take 2).map (fun c => (1938554881-1+2*2^9*c.k,96056954351008+c.lower,96057332243252+c.upper)) = pointBounds14760 := by
 decide +kernel
def cuts14761 : List PrefixCut := [⟨10,71577740,71577790⟩,
⟨70,488695354,488695686⟩,
⟨128,894330727,894331331⟩]
theorem checked14761 : checkPrefixCuts (2^48) 1938685953 9 Manual.Count131072.C014761.packed 128 cuts14761 = true := by
 decide +kernel
def pointBounds14761 : List (Nat × Nat × Nat) := [(1938696192,96057914802873,96058292695760),(1938757632,96058331920487,96058709813656)]
theorem point_links_checked14761 : (cuts14761.take 2).map (fun c => (1938685953-1+2*2^9*c.k,96057843225133+c.lower,96058221117970+c.upper)) = pointBounds14761 := by
 decide +kernel
def cuts14762 : List PrefixCut := [⟨2,13356431,13356440⟩,
⟨62,422898510,422898799⟩,
⟨122,849412764,849413339⟩,
⟨128,892382813,892383416⟩]
theorem checked14762 : checkPrefixCuts (2^48) 1938817025 9 Manual.Count131072.C014762.packed 128 cuts14762 = true := by
 decide +kernel
def pointBounds14762 : List (Nat × Nat × Nat) := [(1938819072,96058750912291,96059128805741),(1938880512,96059160454370,96059538348100),(1938941952,96059586968624,96059964862640)]
theorem point_links_checked14762 : (cuts14762.take 3).map (fun c => (1938817025-1+2*2^9*c.k,96058737555860+c.lower,96059115449301+c.upper)) = pointBounds14762 := by
 decide +kernel
def cuts14763 : List PrefixCut := [⟨54,370175325,370175574⟩,
⟨114,787226897,787227428⟩,
⟨128,885354783,885355381⟩]
theorem checked14763 : checkPrefixCuts (2^48) 1938948097 9 Manual.Count131072.C014763.packed 128 cuts14763 = true := by
 decide +kernel
def pointBounds14763 : List (Nat × Nat × Nat) := [(1939003392,96060000113998,96060378008291),(1939064832,96060417165570,96060795060145)]
theorem point_links_checked14763 : (cuts14763.take 2).map (fun c => (1938948097-1+2*2^9*c.k,96059629938673+c.lower,96060007832717+c.upper)) = pointBounds14763 := by
 decide +kernel
def cuts14764 : List PrefixCut := [⟨46,319926660,319926878⟩,
⟨106,730274753,730275248⟩,
⟨128,880359933,880360533⟩]
theorem checked14764 : checkPrefixCuts (2^48) 1939079169 9 Manual.Count131072.C014764.packed 128 cuts14764 = true := by
 decide +kernel
def pointBounds14764 : List (Nat × Nat × Nat) := [(1939126272,96060835220116,96061213114976),(1939187712,96061245568209,96061623463346)]
theorem point_links_checked14764 : (cuts14764.take 2).map (fun c => (1939079169-1+2*2^9*c.k,96060515293456+c.lower,96060893188098+c.upper)) = pointBounds14764 := by
 decide +kernel
def cuts14765 : List PrefixCut := [⟨38,255460069,255460245⟩,
⟨98,672749069,672749521⟩,
⟨128,883928593,883929189⟩]
theorem checked14765 : checkPrefixCuts (2^48) 1939210241 9 Manual.Count131072.C014765.packed 128 cuts14765 = true := by
 decide +kernel
def pointBounds14765 : List (Nat × Nat × Nat) := [(1939249152,96061651113458,96062029008876),(1939310592,96062068402458,96062446298152)]
theorem point_links_checked14765 : (cuts14765.take 2).map (fun c => (1939210241-1+2*2^9*c.k,96061395653389+c.lower,96061773548631+c.upper)) = pointBounds14765 := by
 decide +kernel
def cuts14766 : List PrefixCut := [⟨30,206531756,206531899⟩,
⟨90,631486533,631486960⟩,
⟨128,896640978,896641589⟩]
theorem checked14766 : checkPrefixCuts (2^48) 1939341313 9 Manual.Count131072.C014766.packed 128 cuts14766 = true := by
 decide +kernel
def pointBounds14766 : List (Nat × Nat × Nat) := [(1939372032,96062486113738,96062864009719),(1939433472,96062911068515,96063288964780)]
theorem point_links_checked14766 : (cuts14766.take 2).map (fun c => (1939341313-1+2*2^9*c.k,96062279581982+c.lower,96062657477820+c.upper)) = pointBounds14766 := by
 decide +kernel
def cuts14767 : List PrefixCut := [⟨22,148902119,148902219⟩,
⟨82,567444411,567444788⟩,
⟨128,890339918,890340513⟩]
theorem checked14767 : checkPrefixCuts (2^48) 1939472385 9 Manual.Count131072.C014767.packed 128 cuts14767 = true := by
 decide +kernel
def pointBounds14767 : List (Nat × Nat × Nat) := [(1939494912,96063325125079,96063703021628),(1939556352,96063743667371,96064121564197)]
theorem point_links_checked14767 : (cuts14767.take 2).map (fun c => (1939472385-1+2*2^9*c.k,96063176222960+c.lower,96063554119409+c.upper)) = pointBounds14767 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000148
