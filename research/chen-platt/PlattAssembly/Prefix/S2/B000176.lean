import PlattAssemblyKernel
import PlattCertificates.Count131072.C015632
import PlattCertificates.Count131072.C015633
import PlattCertificates.Count131072.C015634
import PlattCertificates.Count131072.C015635
import PlattCertificates.Count131072.C015636
import PlattCertificates.Count131072.C015637
import PlattCertificates.Count131072.C015638
import PlattCertificates.Count131072.C015639
import PlattCertificates.Count131072.C015640
import PlattCertificates.Count131072.C015641
import PlattCertificates.Count131072.C015642
import PlattCertificates.Count131072.C015643
import PlattCertificates.Count131072.C015644
import PlattCertificates.Count131072.C015645
import PlattCertificates.Count131072.C015646
import PlattCertificates.Count131072.C015647
import PlattCertificates.Count131072.C015648
import PlattCertificates.Count131072.C015649
import PlattCertificates.Count131072.C015650
import PlattCertificates.Count131072.C015651
import PlattCertificates.Count131072.C015652
import PlattCertificates.Count131072.C015653
import PlattCertificates.Count131072.C015654
import PlattCertificates.Count131072.C015655
import PlattCertificates.Count131072.C015656
import PlattCertificates.Count131072.C015657
import PlattCertificates.Count131072.C015658
import PlattCertificates.Count131072.C015659
import PlattCertificates.Count131072.C015660
import PlattCertificates.Count131072.C015661
import PlattCertificates.Count131072.C015662
import PlattCertificates.Count131072.C015663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000176
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15632 : List PrefixCut := [⟨25,165632929,165633037⟩,
⟨88,572713620,572713995⟩,
⟨128,837604048,837604595⟩]
theorem checked15632 : checkPrefixCuts (2^48) 2052849665 9 Manual.Count131072.C015632.packed 128 cuts15632 = true := by
 decide +kernel
def pointBounds15632 : List (Nat × Nat × Nat) := [(2052875264,96810247746648,96810626137366),(2052939776,96810654827339,96811033218324)]
theorem point_links_checked15632 : (cuts15632.take 2).map (fun c => (2052849665-1+2*2^9*c.k,96810082113719+c.lower,96810460504329+c.upper)) = pointBounds15632 := by
 decide +kernel
def cuts15633 : List PrefixCut := [⟨23,150129642,150129739⟩,
⟨86,560886428,560886792⟩,
⟨128,831792395,831792935⟩]
theorem checked15633 : checkPrefixCuts (2^48) 2052980737 9 Manual.Count131072.C015633.packed 128 cuts15633 = true := by
 decide +kernel
def pointBounds15633 : List (Nat × Nat × Nat) := [(2053004288,96811069847409,96811448238663),(2053068800,96811480604195,96811858995716)]
theorem point_links_checked15633 : (cuts15633.take 2).map (fun c => (2052980737-1+2*2^9*c.k,96810919717767+c.lower,96811298108924+c.upper)) = pointBounds15633 := by
 decide +kernel
def cuts15634 : List PrefixCut := [⟨21,137507289,137507381⟩,
⟨84,529730705,529731056⟩,
⟨128,817070238,817070774⟩]
theorem checked15634 : checkPrefixCuts (2^48) 2053111809 9 Manual.Count131072.C015634.packed 128 cuts15634 = true := by
 decide +kernel
def pointBounds15634 : List (Nat × Nat × Nat) := [(2053133312,96811889017451,96812267409240),(2053197824,96812281240867,96812659632915)]
theorem point_links_checked15634 : (cuts15634.take 2).map (fun c => (2053111809-1+2*2^9*c.k,96811751510162+c.lower,96812129901859+c.upper)) = pointBounds15634 := by
 decide +kernel
def cuts15635 : List PrefixCut := [⟨19,127765387,127765471⟩,
⟨82,532438864,532439214⟩,
⟨128,829081713,829082251⟩]
theorem checked15635 : checkPrefixCuts (2^48) 2053242881 9 Manual.Count131072.C015635.packed 128 cuts15635 = true := by
 decide +kernel
def pointBounds15635 : List (Nat × Nat × Nat) := [(2053262336,96812696345787,96813074738104),(2053326848,96813101019264,96813479411847)]
theorem point_links_checked15635 : (cuts15635.take 2).map (fun c => (2053242881-1+2*2^9*c.k,96812568580400+c.lower,96812946972633+c.upper)) = pointBounds15635 := by
 decide +kernel
def cuts15636 : List PrefixCut := [⟨17,110211214,110211288⟩,
⟨80,523906235,523906582⟩,
⟨128,846848087,846848641⟩]
theorem checked15636 : checkPrefixCuts (2^48) 2053373953 9 Manual.Count131072.C015636.packed 128 cuts15636 = true := by
 decide +kernel
def pointBounds15636 : List (Nat × Nat × Nat) := [(2053391360,96813507873327,96813886266172),(2053455872,96813921568348,96814299961466)]
theorem point_links_checked15636 : (cuts15636.take 2).map (fun c => (2053373953-1+2*2^9*c.k,96813397662113+c.lower,96813776054884+c.upper)) = pointBounds15636 := by
 decide +kernel
def cuts15637 : List PrefixCut := [⟨15,98416221,98416285⟩,
⟨78,507150801,507151133⟩,
⟨128,838844273,838844821⟩]
theorem checked15637 : checkPrefixCuts (2^48) 2053505025 9 Manual.Count131072.C015637.packed 128 cuts15637 = true := by
 decide +kernel
def pointBounds15637 : List (Nat × Nat × Nat) := [(2053520384,96814342926421,96814721319810),(2053584896,96814751661001,96815130054658)]
theorem point_links_checked15637 : (cuts15637.take 2).map (fun c => (2053505025-1+2*2^9*c.k,96814244510200+c.lower,96814622903525+c.upper)) = pointBounds15637 := by
 decide +kernel
def cuts15638 : List PrefixCut := [⟨13,86622723,86622777⟩,
⟨76,499580510,499580828⟩,
⟨128,843450888,843451432⟩]
theorem checked15638 : checkPrefixCuts (2^48) 2053636097 9 Manual.Count131072.C015638.packed 128 cuts15638 = true := by
 decide +kernel
def pointBounds15638 : List (Nat × Nat × Nat) := [(2053649408,96815169977196,96815548371123),(2053713920,96815582934983,96815961329174)]
theorem point_links_checked15638 : (cuts15638.take 2).map (fun c => (2053636097-1+2*2^9*c.k,96815083354473+c.lower,96815461748346+c.upper)) = pointBounds15638 := by
 decide +kernel
def cuts15639 : List PrefixCut := [⟨11,75515978,75516026⟩,
⟨74,485980937,485981244⟩,
⟨128,839011619,839012158⟩]
theorem checked15639 : checkPrefixCuts (2^48) 2053767169 9 Manual.Count131072.C015639.packed 128 cuts15639 = true := by
 decide +kernel
def pointBounds15639 : List (Nat × Nat × Nat) := [(2053778432,96816002321339,96816380715804),(2053842944,96816412786298,96816791181022)]
theorem point_links_checked15639 : (cuts15639.take 2).map (fun c => (2053767169-1+2*2^9*c.k,96815926805361+c.lower,96816305199778+c.upper)) = pointBounds15639 := by
 decide +kernel
def cuts15640 : List PrefixCut := [⟨9,61532715,61532755⟩,
⟨72,474849700,474850014⟩,
⟨128,841424778,841425323⟩]
theorem checked15640 : checkPrefixCuts (2^48) 2053898241 9 Manual.Count131072.C015640.packed 128 cuts15640 = true := by
 decide +kernel
def pointBounds15640 : List (Nat × Nat × Nat) := [(2053907456,96816827349695,96817205744691),(2053971968,96817240666680,96817619061950)]
theorem point_links_checked15640 : (cuts15640.take 2).map (fun c => (2053898241-1+2*2^9*c.k,96816765816980+c.lower,96817144211936+c.upper)) = pointBounds15640 := by
 decide +kernel
def cuts15641 : List PrefixCut := [⟨7,47414190,47414219⟩,
⟨70,467282845,467283145⟩,
⟨128,840274993,840275535⟩]
theorem checked15641 : checkPrefixCuts (2^48) 2054029313 9 Manual.Count131072.C015641.packed 128 cuts15641 = true := by
 decide +kernel
def pointBounds15641 : List (Nat × Nat × Nat) := [(2054036480,96817654655948,96818033051478),(2054100992,96818074524603,96818452920404)]
theorem point_links_checked15641 : (cuts15641.take 2).map (fun c => (2054029313-1+2*2^9*c.k,96817607241758+c.lower,96817985637259+c.upper)) = pointBounds15641 := by
 decide +kernel
def cuts15642 : List PrefixCut := [⟨5,31379082,31379102⟩,
⟨68,441218547,441218833⟩,
⟨128,828300246,828300786⟩]
theorem checked15642 : checkPrefixCuts (2^48) 2054160385 9 Manual.Count131072.C015642.packed 128 cuts15642 = true := by
 decide +kernel
def pointBounds15642 : List (Nat × Nat × Nat) := [(2054165504,96818478895833,96818857291896),(2054230016,96818888735298,96819267131627)]
theorem point_links_checked15642 : (cuts15642.take 2).map (fun c => (2054160385-1+2*2^9*c.k,96818447516751+c.lower,96818825912794+c.upper)) = pointBounds15642 := by
 decide +kernel
def cuts15643 : List PrefixCut := [⟨3,20963738,20963751⟩,
⟨66,435984068,435984352⟩,
⟨128,837153483,837154031⟩]
theorem checked15643 : checkPrefixCuts (2^48) 2054291457 9 Manual.Count131072.C015643.packed 128 cuts15643 = true := by
 decide +kernel
def pointBounds15643 : List (Nat × Nat × Nat) := [(2054294528,96819296780735,96819675177331),(2054359040,96819711801065,96820090197932)]
theorem point_links_checked15643 : (cuts15643.take 2).map (fun c => (2054291457-1+2*2^9*c.k,96819275816997+c.lower,96819654213580+c.upper)) = pointBounds15643 := by
 decide +kernel
def cuts15644 : List PrefixCut := [⟨1,7261488,7261493⟩,
⟨64,421022709,421022984⟩,
⟨127,822577792,822578332⟩,
⟨128,828331815,828332359⟩]
theorem checked15644 : checkPrefixCuts (2^48) 2054422529 9 Manual.Count131072.C015644.packed 128 cuts15644 = true := by
 decide +kernel
def pointBounds15644 : List (Nat × Nat × Nat) := [(2054423552,96820120231968,96820498629104),(2054488064,96820533993189,96820912390595),(2054552576,96820935548272,96821313945943)]
theorem point_links_checked15644 : (cuts15644.take 3).map (fun c => (2054422529-1+2*2^9*c.k,96820112970480+c.lower,96820491367611+c.upper)) = pointBounds15644 := by
 decide +kernel
def cuts15645 : List PrefixCut := [⟨62,405926252,405926513⟩,
⟨125,819922561,819923092⟩,
⟨128,839786383,839786926⟩]
theorem checked15645 : checkPrefixCuts (2^48) 2054553601 9 Manual.Count131072.C015645.packed 128 cuts15645 = true := by
 decide +kernel
def pointBounds15645 : List (Nat × Nat × Nat) := [(2054617088,96821347228547,96821725626483),(2054681600,96821761224856,96822139623062)]
theorem point_links_checked15645 : (cuts15645.take 2).map (fun c => (2054553601-1+2*2^9*c.k,96820941302295+c.lower,96821319699970+c.upper)) = pointBounds15645 := by
 decide +kernel
def cuts15646 : List PrefixCut := [⟨60,390831681,390831940⟩,
⟨123,803843053,803843582⟩,
⟨128,837951872,837952423⟩]
theorem checked15646 : checkPrefixCuts (2^48) 2054684673 9 Manual.Count131072.C015646.packed 128 cuts15646 = true := by
 decide +kernel
def pointBounds15646 : List (Nat × Nat × Nat) := [(2054746112,96822171920359,96822550318836),(2054810624,96822584931731,96822963330478)]
theorem point_links_checked15646 : (cuts15646.take 2).map (fun c => (2054684673-1+2*2^9*c.k,96821781088678+c.lower,96822159486896+c.upper)) = pointBounds15646 := by
 decide +kernel
def cuts15647 : List PrefixCut := [⟨58,388889232,388889488⟩,
⟨121,806257978,806258510⟩,
⟨128,851870500,851871061⟩]
theorem checked15647 : checkPrefixCuts (2^48) 2054815745 9 Manual.Count131072.C015647.packed 128 cuts15647 = true := by
 decide +kernel
def pointBounds15647 : List (Nat × Nat × Nat) := [(2054875136,96823007929782,96823386328807),(2054939648,96823425298528,96823803697829)]
theorem point_links_checked15647 : (cuts15647.take 2).map (fun c => (2054815745-1+2*2^9*c.k,96822619040550+c.lower,96822997439319+c.upper)) = pointBounds15647 := by
 decide +kernel
def cuts15648 : List PrefixCut := [⟨56,368729648,368729892⟩,
⟨119,783332770,783333289⟩,
⟨128,841680225,841680784⟩]
theorem checked15648 : checkPrefixCuts (2^48) 2054946817 9 Manual.Count131072.C015648.packed 128 cuts15648 = true := by
 decide +kernel
def pointBounds15648 : List (Nat × Nat × Nat) := [(2055004160,96823839640698,96824218040272),(2055068672,96824254243820,96824632643669)]
theorem point_links_checked15648 : (cuts15648.take 2).map (fun c => (2054946817-1+2*2^9*c.k,96823470911050+c.lower,96823849310380+c.upper)) = pointBounds15648 := by
 decide +kernel
def cuts15649 : List PrefixCut := [⟨54,351448772,351449000⟩,
⟨117,771230331,771230833⟩,
⟨128,838476309,838476857⟩]
theorem checked15649 : checkPrefixCuts (2^48) 2055077889 9 Manual.Count131072.C015649.packed 128 cuts15649 = true := by
 decide +kernel
def pointBounds15649 : List (Nat × Nat × Nat) := [(2055133184,96824664040047,96825042440164),(2055197696,96825083821606,96825462221997)]
theorem point_links_checked15649 : (cuts15649.take 2).map (fun c => (2055077889-1+2*2^9*c.k,96824312591275+c.lower,96824690991164+c.upper)) = pointBounds15649 := by
 decide +kernel
def cuts15650 : List PrefixCut := [⟨52,339374610,339374831⟩,
⟨115,745982469,745982952⟩,
⟨128,828973272,828973810⟩]
theorem checked15650 : checkPrefixCuts (2^48) 2055208961 9 Manual.Count131072.C015650.packed 128 cuts15650 = true := by
 decide +kernel
def pointBounds15650 : List (Nat × Nat × Nat) := [(2055262208,96825490442194,96825868842852),(2055326720,96825897050053,96826275450973)]
theorem point_links_checked15650 : (cuts15650.take 2).map (fun c => (2055208961-1+2*2^9*c.k,96825151067584+c.lower,96825529468021+c.upper)) = pointBounds15650 := by
 decide +kernel
def cuts15651 : List PrefixCut := [⟨50,332368913,332369125⟩,
⟨113,734021333,734021810⟩,
⟨128,829468430,829468969⟩]
theorem checked15651 : checkPrefixCuts (2^48) 2055340033 9 Manual.Count131072.C015651.packed 128 cuts15651 = true := by
 decide +kernel
def pointBounds15651 : List (Nat × Nat × Nat) := [(2055391232,96826312409769,96826690810956),(2055455744,96826714062189,96827092463641)]
theorem point_links_checked15651 : (cuts15651.take 2).map (fun c => (2055340033-1+2*2^9*c.k,96825980040856+c.lower,96826358441831+c.upper)) = pointBounds15651 := by
 decide +kernel
def cuts15652 : List PrefixCut := [⟨48,313039641,313039841⟩,
⟨111,726717000,726717469⟩,
⟨128,834618782,834619323⟩]
theorem checked15652 : checkPrefixCuts (2^48) 2055471105 9 Manual.Count131072.C015652.packed 128 cuts15652 = true := by
 decide +kernel
def pointBounds15652 : List (Nat × Nat × Nat) := [(2055520256,96827122548927,96827500950641),(2055584768,96827536226286,96827914628269)]
theorem point_links_checked15652 : (cuts15652.take 2).map (fun c => (2055471105-1+2*2^9*c.k,96826809509286+c.lower,96827187910800+c.upper)) = pointBounds15652 := by
 decide +kernel
def cuts15653 : List PrefixCut := [⟨46,302613217,302613414⟩,
⟨109,711883029,711883495⟩,
⟨128,841274823,841275374⟩]
theorem checked15653 : checkPrefixCuts (2^48) 2055602177 9 Manual.Count131072.C015653.packed 128 cuts15653 = true := by
 decide +kernel
def pointBounds15653 : List (Nat × Nat × Nat) := [(2055649280,96827946741285,96828325143537),(2055713792,96828356011097,96828734413618)]
theorem point_links_checked15653 : (cuts15653.take 2).map (fun c => (2055602177-1+2*2^9*c.k,96827644128068+c.lower,96828022530123+c.upper)) = pointBounds15653 := by
 decide +kernel
def cuts15654 : List PrefixCut := [⟨44,286985182,286985368⟩,
⟨107,705676569,705677027⟩,
⟨128,844917974,844918523⟩]
theorem checked15654 : checkPrefixCuts (2^48) 2055733249 9 Manual.Count131072.C015654.packed 128 cuts15654 = true := by
 decide +kernel
def pointBounds15654 : List (Nat × Nat × Nat) := [(2055778304,96828772388073,96829150790865),(2055842816,96829191079460,96829569482524)]
theorem point_links_checked15654 : (cuts15654.take 2).map (fun c => (2055733249-1+2*2^9*c.k,96828485402891+c.lower,96828863805497+c.upper)) = pointBounds15654 := by
 decide +kernel
def cuts15655 : List PrefixCut := [⟨42,274781848,274782025⟩,
⟨105,693994573,693995022⟩,
⟨128,840893874,840894419⟩]
theorem checked15655 : checkPrefixCuts (2^48) 2055864321 9 Manual.Count131072.C015655.packed 128 cuts15655 = true := by
 decide +kernel
def pointBounds15655 : List (Nat × Nat × Nat) := [(2055907328,96829605102713,96829983506045),(2055971840,96830024315438,96830402719042)]
theorem point_links_checked15655 : (cuts15655.take 2).map (fun c => (2055864321-1+2*2^9*c.k,96829330320865+c.lower,96829708724020+c.upper)) = pointBounds15655 := by
 decide +kernel
def cuts15656 : List PrefixCut := [⟨40,265728837,265729004⟩,
⟨103,676838246,676838679⟩,
⟨128,838239281,838239820⟩]
theorem checked15656 : checkPrefixCuts (2^48) 2055995393 9 Manual.Count131072.C015656.packed 128 cuts15656 = true := by
 decide +kernel
def pointBounds15656 : List (Nat × Nat × Nat) := [(2056036352,96830436943576,96830815347443),(2056100864,96830848052985,96831226457118)]
theorem point_links_checked15656 : (cuts15656.take 2).map (fun c => (2055995393-1+2*2^9*c.k,96830171214739+c.lower,96830549618439+c.upper)) = pointBounds15656 := by
 decide +kernel
def cuts15657 : List PrefixCut := [⟨38,246409947,246410106⟩,
⟨101,657767342,657767775⟩,
⟨128,835037167,835037718⟩]
theorem checked15657 : checkPrefixCuts (2^48) 2056126465 9 Manual.Count131072.C015657.packed 128 cuts15657 = true := by
 decide +kernel
def pointBounds15657 : List (Nat × Nat × Nat) := [(2056165376,96831255863967,96831634268365),(2056229888,96831667221362,96832045626034)]
theorem point_links_checked15657 : (cuts15657.take 2).map (fun c => (2056126465-1+2*2^9*c.k,96831009454020+c.lower,96831387858259+c.upper)) = pointBounds15657 := by
 decide +kernel
def cuts15658 : List PrefixCut := [⟨36,237496742,237496895⟩,
⟨99,647322573,647322996⟩,
⟨128,838132254,838132799⟩]
theorem checked15658 : checkPrefixCuts (2^48) 2056257537 9 Manual.Count131072.C015658.packed 128 cuts15658 = true := by
 decide +kernel
def pointBounds15658 : List (Nat × Nat × Nat) := [(2056294400,96832081987929,96832460392872),(2056358912,96832491813760,96832870218973)]
theorem point_links_checked15658 : (cuts15658.take 2).map (fun c => (2056257537-1+2*2^9*c.k,96831844491187+c.lower,96832222895977+c.upper)) = pointBounds15658 := by
 decide +kernel
def cuts15659 : List PrefixCut := [⟨34,218592739,218592879⟩,
⟨97,625381522,625381923⟩,
⟨128,829318689,829319221⟩]
theorem checked15659 : checkPrefixCuts (2^48) 2056388609 9 Manual.Count131072.C015659.packed 128 cuts15659 = true := by
 decide +kernel
def pointBounds15659 : List (Nat × Nat × Nat) := [(2056423424,96832901216180,96833279621655),(2056487936,96833308004963,96833686410699)]
theorem point_links_checked15659 : (cuts15659.take 2).map (fun c => (2056388609-1+2*2^9*c.k,96832682623441+c.lower,96833061028776+c.upper)) = pointBounds15659 := by
 decide +kernel
def cuts15660 : List PrefixCut := [⟨32,205986994,205987131⟩,
⟨95,625889466,625889880⟩,
⟨128,835835653,835836203⟩]
theorem checked15660 : checkPrefixCuts (2^48) 2056519681 9 Manual.Count131072.C015660.packed 128 cuts15660 = true := by
 decide +kernel
def pointBounds15660 : List (Nat × Nat × Nat) := [(2056552448,96833717929124,96834096335128),(2056616960,96834137831596,96834516237877)]
theorem point_links_checked15660 : (cuts15660.take 2).map (fun c => (2056519681-1+2*2^9*c.k,96833511942130+c.lower,96833890347997+c.upper)) = pointBounds15660 := by
 decide +kernel
def cuts15661 : List PrefixCut := [⟨30,197488655,197488782⟩,
⟨93,606963638,606964032⟩,
⟨128,832634700,832635243⟩]
theorem checked15661 : checkPrefixCuts (2^48) 2056650753 9 Manual.Count131072.C015661.packed 128 cuts15661 = true := by
 decide +kernel
def pointBounds15661 : List (Nat × Nat × Nat) := [(2056681472,96834545266438,96834923672982),(2056745984,96834954741421,96835333148232)]
theorem point_links_checked15661 : (cuts15661.take 2).map (fun c => (2056650753-1+2*2^9*c.k,96834347777783+c.lower,96834726184200+c.upper)) = pointBounds15661 := by
 decide +kernel
def cuts15662 : List PrefixCut := [⟨28,182969954,182970074⟩,
⟨91,595019430,595019822⟩,
⟨128,840381851,840382402⟩]
theorem checked15662 : checkPrefixCuts (2^48) 2056781825 9 Manual.Count131072.C015662.packed 128 cuts15662 = true := by
 decide +kernel
def pointBounds15662 : List (Nat × Nat × Nat) := [(2056810496,96835363382437,96835741789517),(2056875008,96835775431913,96836153839265)]
theorem point_links_checked15662 : (cuts15662.take 2).map (fun c => (2056781825-1+2*2^9*c.k,96835180412483+c.lower,96835558819443+c.upper)) = pointBounds15662 := by
 decide +kernel
def cuts15663 : List PrefixCut := [⟨26,169000455,169000564⟩,
⟨89,579792396,579792771⟩,
⟨128,844296360,844296907⟩]
theorem checked15663 : checkPrefixCuts (2^48) 2056912897 9 Manual.Count131072.C015663.packed 128 cuts15663 = true := by
 decide +kernel
def pointBounds15663 : List (Nat × Nat × Nat) := [(2056939520,96836189794789,96836568202409),(2057004032,96836600586730,96836978994616)]
theorem point_links_checked15663 : (cuts15663.take 2).map (fun c => (2056912897-1+2*2^9*c.k,96836020794334+c.lower,96836399201845+c.upper)) = pointBounds15663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000176
