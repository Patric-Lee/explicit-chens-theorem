import PlattAssemblyKernel
import PlattCertificates.Count131072.C015504
import PlattCertificates.Count131072.C015505
import PlattCertificates.Count131072.C015506
import PlattCertificates.Count131072.C015507
import PlattCertificates.Count131072.C015508
import PlattCertificates.Count131072.C015509
import PlattCertificates.Count131072.C015510
import PlattCertificates.Count131072.C015511
import PlattCertificates.Count131072.C015512
import PlattCertificates.Count131072.C015513
import PlattCertificates.Count131072.C015514
import PlattCertificates.Count131072.C015515
import PlattCertificates.Count131072.C015516
import PlattCertificates.Count131072.C015517
import PlattCertificates.Count131072.C015518
import PlattCertificates.Count131072.C015519
import PlattCertificates.Count131072.C015520
import PlattCertificates.Count131072.C015521
import PlattCertificates.Count131072.C015522
import PlattCertificates.Count131072.C015523
import PlattCertificates.Count131072.C015524
import PlattCertificates.Count131072.C015525
import PlattCertificates.Count131072.C015526
import PlattCertificates.Count131072.C015527
import PlattCertificates.Count131072.C015528
import PlattCertificates.Count131072.C015529
import PlattCertificates.Count131072.C015530
import PlattCertificates.Count131072.C015531
import PlattCertificates.Count131072.C015532
import PlattCertificates.Count131072.C015533
import PlattCertificates.Count131072.C015534
import PlattCertificates.Count131072.C015535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15504 : List PrefixCut := [⟨29,194369727,194369853⟩,
⟨92,614342362,614342758⟩,
⟨128,845473640,845474186⟩]
theorem checked15504 : checkPrefixCuts (2^48) 2036072449 9 Manual.Count131072.C015504.packed 128 cuts15504 = true := by
 decide +kernel
def pointBounds15504 : List (Nat × Nat × Nat) := [(2036102144,96702519940171,96702898260499),(2036166656,96702939912806,96703318233404)]
theorem point_links_checked15504 : (cuts15504.take 2).map (fun c => (2036072449-1+2*2^9*c.k,96702325570444+c.lower,96702703890646+c.upper)) = pointBounds15504 := by
 decide +kernel
def cuts15505 : List PrefixCut := [⟨27,174866249,174866364⟩,
⟨90,593568188,593568579⟩,
⟨128,839475046,839475596⟩]
theorem checked15505 : checkPrefixCuts (2^48) 2036203521 9 Manual.Count131072.C015505.packed 128 cuts15505 = true := by
 decide +kernel
def pointBounds15505 : List (Nat × Nat × Nat) := [(2036231168,96703345910333,96703724231196),(2036295680,96703764612272,96704142933411)]
theorem point_links_checked15505 : (cuts15505.take 2).map (fun c => (2036203521-1+2*2^9*c.k,96703171044084+c.lower,96703549364832+c.upper)) = pointBounds15505 := by
 decide +kernel
def cuts15506 : List PrefixCut := [⟨25,163797078,163797189⟩,
⟨88,580675694,580676076⟩,
⟨128,846332132,846332687⟩]
theorem checked15506 : checkPrefixCuts (2^48) 2036334593 9 Manual.Count131072.C015506.packed 128 cuts15506 = true := by
 decide +kernel
def pointBounds15506 : List (Nat × Nat × Nat) := [(2036360192,96704174316208,96704552637617),(2036424704,96704591194824,96704969516504)]
theorem point_links_checked15506 : (cuts15506.take 2).map (fun c => (2036334593-1+2*2^9*c.k,96704010519130+c.lower,96704388840428+c.upper)) = pointBounds15506 := by
 decide +kernel
def cuts15507 : List PrefixCut := [⟨23,153834991,153835091⟩,
⟨86,563914643,563915014⟩,
⟨128,844619019,844619578⟩]
theorem checked15507 : checkPrefixCuts (2^48) 2036465665 9 Manual.Count131072.C015507.packed 128 cuts15507 = true := by
 decide +kernel
def pointBounds15507 : List (Nat × Nat × Nat) := [(2036489216,96705010686253,96705389008206),(2036553728,96705420765905,96705799088129)]
theorem point_links_checked15507 : (cuts15507.take 2).map (fun c => (2036465665-1+2*2^9*c.k,96704856851262+c.lower,96705235173115+c.upper)) = pointBounds15507 := by
 decide +kernel
def cuts15508 : List PrefixCut := [⟨21,138207730,138207821⟩,
⟨84,555033446,555033810⟩,
⟨128,845393900,845394458⟩]
theorem checked15508 : checkPrefixCuts (2^48) 2036596737 9 Manual.Count131072.C015508.packed 128 cuts15508 = true := by
 decide +kernel
def pointBounds15508 : List (Nat × Nat × Nat) := [(2036618240,96705839678011,96706218000514),(2036682752,96706256503727,96706634826503)]
theorem point_links_checked15508 : (cuts15508.take 2).map (fun c => (2036596737-1+2*2^9*c.k,96705701470281+c.lower,96706079792693+c.upper)) = pointBounds15508 := by
 decide +kernel
def cuts15509 : List PrefixCut := [⟨19,125760993,125761077⟩,
⟨82,533439341,533439697⟩,
⟨128,841746277,841746834⟩]
theorem checked15509 : checkPrefixCuts (2^48) 2036727809 9 Manual.Count131072.C015509.packed 128 cuts15509 = true := by
 decide +kernel
def pointBounds15509 : List (Nat × Nat × Nat) := [(2036747264,96706672625174,96707050948228),(2036811776,96707080303522,96707458626848)]
theorem point_links_checked15509 : (cuts15509.take 2).map (fun c => (2036727809-1+2*2^9*c.k,96706546864181+c.lower,96706925187151+c.upper)) = pointBounds15509 := by
 decide +kernel
def cuts15510 : List PrefixCut := [⟨17,114283198,114283270⟩,
⟨80,533958006,533958356⟩,
⟨128,847634388,847634946⟩]
theorem checked15510 : checkPrefixCuts (2^48) 2036858881 9 Manual.Count131072.C015510.packed 128 cuts15510 = true := by
 decide +kernel
def pointBounds15510 : List (Nat × Nat × Nat) := [(2036876288,96707502893656,96707881217255),(2036940800,96707922568464,96708300892341)]
theorem point_links_checked15510 : (cuts15510.take 2).map (fun c => (2036858881-1+2*2^9*c.k,96707388610458+c.lower,96707766933985+c.upper)) = pointBounds15510 := by
 decide +kernel
def cuts15511 : List PrefixCut := [⟨15,101563224,101563287⟩,
⟨78,512229776,512230110⟩,
⟨128,843987037,843987589⟩]
theorem checked15511 : checkPrefixCuts (2^48) 2036989953 9 Manual.Count131072.C015511.packed 128 cuts15511 = true := by
 decide +kernel
def pointBounds15511 : List (Nat × Nat × Nat) := [(2037005312,96708337808070,96708716132218),(2037069824,96708748474622,96709126799041)]
theorem point_links_checked15511 : (cuts15511.take 2).map (fun c => (2036989953-1+2*2^9*c.k,96708236244846+c.lower,96708614568931+c.upper)) = pointBounds15511 := by
 decide +kernel
def cuts15512 : List PrefixCut := [⟨13,86910467,86910523⟩,
⟨76,495478509,495478837⟩,
⟨128,835504475,835505032⟩]
theorem checked15512 : checkPrefixCuts (2^48) 2037121025 9 Manual.Count131072.C015512.packed 128 cuts15512 = true := by
 decide +kernel
def pointBounds15512 : List (Nat × Nat × Nat) := [(2037134336,96709167142350,96709545467043),(2037198848,96709575710392,96709954035357)]
theorem point_links_checked15512 : (cuts15512.take 2).map (fun c => (2037121025-1+2*2^9*c.k,96709080231883+c.lower,96709458556520+c.upper)) = pointBounds15512 := by
 decide +kernel
def cuts15513 : List PrefixCut := [⟨11,72674062,72674109⟩,
⟨74,489367853,489368175⟩,
⟨128,840839151,840839703⟩]
theorem checked15513 : checkPrefixCuts (2^48) 2037252097 9 Manual.Count131072.C015513.packed 128 cuts15513 = true := by
 decide +kernel
def pointBounds15513 : List (Nat × Nat × Nat) := [(2037263360,96709988410420,96710366735661),(2037327872,96710405104211,96710783429727)]
theorem point_links_checked15513 : (cuts15513.take 2).map (fun c => (2037252097-1+2*2^9*c.k,96709915736358+c.lower,96710294061552+c.upper)) = pointBounds15513 := by
 decide +kernel
def cuts15514 : List PrefixCut := [⟨9,60373641,60373681⟩,
⟨72,473172654,473172961⟩,
⟨128,843824196,843824746⟩]
theorem checked15514 : checkPrefixCuts (2^48) 2037383169 9 Manual.Count131072.C015514.packed 128 cuts15514 = true := by
 decide +kernel
def pointBounds15514 : List (Nat × Nat × Nat) := [(2037392384,96710816949150,96711195274936),(2037456896,96711229748163,96711608074216)]
theorem point_links_checked15514 : (cuts15514.take 2).map (fun c => (2037383169-1+2*2^9*c.k,96710756575509+c.lower,96711134901255+c.upper)) = pointBounds15514 := by
 decide +kernel
def cuts15515 : List PrefixCut := [⟨7,48765530,48765560⟩,
⟨70,470241458,470241768⟩,
⟨128,846671179,846671737⟩]
theorem checked15515 : checkPrefixCuts (2^48) 2037514241 9 Manual.Count131072.C015515.packed 128 cuts15515 = true := by
 decide +kernel
def pointBounds15515 : List (Nat × Nat × Nat) := [(2037521408,96711649165235,96712027491561),(2037585920,96712070641163,96712448967769)]
theorem point_links_checked15515 : (cuts15515.take 2).map (fun c => (2037514241-1+2*2^9*c.k,96711600399705+c.lower,96711978726001+c.upper)) = pointBounds15515 := by
 decide +kernel
def cuts15516 : List PrefixCut := [⟨5,34258015,34258037⟩,
⟨68,454878510,454878804⟩,
⟨128,847031071,847031627⟩]
theorem checked15516 : checkPrefixCuts (2^48) 2037645313 9 Manual.Count131072.C015516.packed 128 cuts15516 = true := by
 decide +kernel
def pointBounds15516 : List (Nat × Nat × Nat) := [(2037650432,96712481328899,96712859655775),(2037714944,96712901949394,96713280276542)]
theorem point_links_checked15516 : (cuts15516.take 2).map (fun c => (2037645313-1+2*2^9*c.k,96712447070884+c.lower,96712825397738+c.upper)) = pointBounds15516 := by
 decide +kernel
def cuts15517 : List PrefixCut := [⟨3,19476096,19476109⟩,
⟨66,443799338,443799624⟩,
⟨128,843799811,843800360⟩]
theorem checked15517 : checkPrefixCuts (2^48) 2037776385 9 Manual.Count131072.C015517.packed 128 cuts15517 = true := by
 decide +kernel
def pointBounds15517 : List (Nat × Nat × Nat) := [(2037779456,96713313578051,96713691905474),(2037843968,96713737901293,96714116228989)]
theorem point_links_checked15517 : (cuts15517.take 2).map (fun c => (2037776385-1+2*2^9*c.k,96713294101955+c.lower,96713672429365+c.upper)) = pointBounds15517 := by
 decide +kernel
def cuts15518 : List PrefixCut := [⟨1,6767857,6767861⟩,
⟨64,414766356,414766630⟩,
⟨127,835596398,835596941⟩,
⟨128,842087602,842088149⟩]
theorem checked15518 : checkPrefixCuts (2^48) 2037907457 9 Manual.Count131072.C015518.packed 128 cuts15518 = true := by
 decide +kernel
def pointBounds15518 : List (Nat × Nat × Nat) := [(2037908480,96714144669623,96714522997586),(2037972992,96714552668122,96714930996355),(2038037504,96714973498164,96715351826666)]
theorem point_links_checked15518 : (cuts15518.take 3).map (fun c => (2037907457-1+2*2^9*c.k,96714137901766+c.lower,96714516229725+c.upper)) = pointBounds15518 := by
 decide +kernel
def cuts15519 : List PrefixCut := [⟨62,415982888,415983164⟩,
⟨125,827533364,827533908⟩,
⟨128,846867630,846868188⟩]
theorem checked15519 : checkPrefixCuts (2^48) 2038038529 9 Manual.Count131072.C015519.packed 128 cuts15519 = true := by
 decide +kernel
def pointBounds15519 : List (Nat × Nat × Nat) := [(2038102016,96715395972256,96715774301038),(2038166528,96715807522732,96716185851782)]
theorem point_links_checked15519 : (cuts15519.take 2).map (fun c => (2038038529-1+2*2^9*c.k,96714979989368+c.lower,96715358317874+c.upper)) = pointBounds15519 := by
 decide +kernel
def cuts15520 : List PrefixCut := [⟨60,397312898,397313158⟩,
⟨123,811737310,811737841⟩,
⟨128,846674863,846675417⟩]
theorem checked15520 : checkPrefixCuts (2^48) 2038169601 9 Manual.Count131072.C015520.packed 128 cuts15520 = true := by
 decide +kernel
def pointBounds15520 : List (Nat × Nat × Nat) := [(2038231040,96716224169896,96716602499220),(2038295552,96716638594308,96717016923903)]
theorem point_links_checked15520 : (cuts15520.take 2).map (fun c => (2038169601-1+2*2^9*c.k,96715826856998+c.lower,96716205186062+c.upper)) = pointBounds15520 := by
 decide +kernel
def cuts15521 : List PrefixCut := [⟨58,385964054,385964313⟩,
⟨121,795667353,795667881⟩,
⟨128,838611565,838612120⟩]
theorem checked15521 : checkPrefixCuts (2^48) 2038300673 9 Manual.Count131072.C015521.packed 128 cuts15521 = true := by
 decide +kernel
def pointBounds15521 : List (Nat × Nat × Nat) := [(2038360064,96717059495915,96717437825792),(2038424576,96717469199214,96717847529360)]
theorem point_links_checked15521 : (cuts15521.take 2).map (fun c => (2038300673-1+2*2^9*c.k,96716673531861+c.lower,96717051861479+c.upper)) = pointBounds15521 := by
 decide +kernel
def cuts15522 : List PrefixCut := [⟨56,363432074,363432318⟩,
⟨119,778632553,778633067⟩,
⟨128,838557309,838557863⟩]
theorem checked15522 : checkPrefixCuts (2^48) 2038431745 9 Manual.Count131072.C015522.packed 128 cuts15522 = true := by
 decide +kernel
def pointBounds15522 : List (Nat × Nat × Nat) := [(2038489088,96717875575500,96718253905917),(2038553600,96718290775979,96718669106666)]
theorem point_links_checked15522 : (cuts15522.take 2).map (fun c => (2038431745-1+2*2^9*c.k,96717512143426+c.lower,96717890473599+c.upper)) = pointBounds15522 := by
 decide +kernel
def cuts15523 : List PrefixCut := [⟨54,367551070,367551310⟩,
⟨117,776788249,776788762⟩,
⟨128,845131247,845131807⟩]
theorem checked15523 : checkPrefixCuts (2^48) 2038562817 9 Manual.Count131072.C015523.packed 128 cuts15523 = true := by
 decide +kernel
def pointBounds15523 : List (Nat × Nat × Nat) := [(2038618112,96718718251805,96719096582772),(2038682624,96719127488984,96719505820224)]
theorem point_links_checked15523 : (cuts15523.take 2).map (fun c => (2038562817-1+2*2^9*c.k,96718350700735+c.lower,96718729031462+c.upper)) = pointBounds15523 := by
 decide +kernel
def cuts15524 : List PrefixCut := [⟨52,346127675,346127902⟩,
⟨115,758928534,758929036⟩,
⟨128,849770595,849771155⟩]
theorem checked15524 : checkPrefixCuts (2^48) 2038693889 9 Manual.Count131072.C015524.packed 128 cuts15524 = true := by
 decide +kernel
def pointBounds15524 : List (Nat × Nat × Nat) := [(2038747136,96719541959657,96719920291171),(2038811648,96719954760516,96720333092305)]
theorem point_links_checked15524 : (cuts15524.take 2).map (fun c => (2038693889-1+2*2^9*c.k,96719195831982+c.lower,96719574163269+c.upper)) = pointBounds15524 := by
 decide +kernel
def cuts15525 : List PrefixCut := [⟨50,337546116,337546337⟩,
⟨113,749906738,749907232⟩,
⟨128,850406453,850407013⟩]
theorem checked15525 : checkPrefixCuts (2^48) 2038824961 9 Manual.Count131072.C015525.packed 128 cuts15525 = true := by
 decide +kernel
def pointBounds15525 : List (Nat × Nat × Nat) := [(2038876160,96720383148693,96720761480761),(2038940672,96720795509315,96721173841656)]
theorem point_links_checked15525 : (cuts15525.take 2).map (fun c => (2038824961-1+2*2^9*c.k,96720045602577+c.lower,96720423934424+c.upper)) = pointBounds15525 := by
 decide +kernel
def cuts15526 : List PrefixCut := [⟨48,313780531,313780740⟩,
⟨111,733707395,733707885⟩,
⟨128,843311354,843311917⟩]
theorem checked15526 : checkPrefixCuts (2^48) 2038956033 9 Manual.Count131072.C015526.packed 128 cuts15526 = true := by
 decide +kernel
def pointBounds15526 : List (Nat × Nat × Nat) := [(2039005184,96721209789561,96721588122177),(2039069696,96721629716425,96722008049322)]
theorem point_links_checked15526 : (cuts15526.take 2).map (fun c => (2038956033-1+2*2^9*c.k,96720896009030+c.lower,96721274341437+c.upper)) = pointBounds15526 := by
 decide +kernel
def cuts15527 : List PrefixCut := [⟨46,303545664,303545866⟩,
⟨109,722203698,722204177⟩,
⟨128,852229324,852229888⟩]
theorem checked15527 : checkPrefixCuts (2^48) 2039087105 9 Manual.Count131072.C015527.packed 128 cuts15527 = true := by
 decide +kernel
def pointBounds15527 : List (Nat × Nat × Nat) := [(2039134208,96722042866048,96722421199220),(2039198720,96722461524082,96722839857531)]
theorem point_links_checked15527 : (cuts15527.take 2).map (fun c => (2039087105-1+2*2^9*c.k,96721739320384+c.lower,96722117653354+c.upper)) = pointBounds15527 := by
 decide +kernel
def cuts15528 : List PrefixCut := [⟨44,290827630,290827819⟩,
⟨107,706836623,706837081⟩,
⟨128,843064965,843065511⟩]
theorem checked15528 : checkPrefixCuts (2^48) 2039218177 9 Manual.Count131072.C015528.packed 128 cuts15528 = true := by
 decide +kernel
def pointBounds15528 : List (Nat × Nat × Nat) := [(2039263232,96722882377338,96723260711061),(2039327744,96723298386331,96723676720323)]
theorem point_links_checked15528 : (cuts15528.take 2).map (fun c => (2039218177-1+2*2^9*c.k,96722591549708+c.lower,96722969883242+c.upper)) = pointBounds15528 := by
 decide +kernel
def cuts15529 : List PrefixCut := [⟨42,282113804,282113985⟩,
⟨105,692851848,692852297⟩,
⟨128,848669501,848670051⟩]
theorem checked15529 : checkPrefixCuts (2^48) 2039349249 9 Manual.Count131072.C015529.packed 128 cuts15529 = true := by
 decide +kernel
def pointBounds15529 : List (Nat × Nat × Nat) := [(2039392256,96723716728477,96724095062738),(2039456768,96724127466521,96724505801050)]
theorem point_links_checked15529 : (cuts15529.take 2).map (fun c => (2039349249-1+2*2^9*c.k,96723434614673+c.lower,96723812948753+c.upper)) = pointBounds15529 := by
 decide +kernel
def cuts15530 : List PrefixCut := [⟨40,265672464,265672630⟩,
⟨103,674590432,674590863⟩,
⟨128,840610502,840611037⟩]
theorem checked15530 : checkPrefixCuts (2^48) 2039480321 9 Manual.Count131072.C015530.packed 128 cuts15530 = true := by
 decide +kernel
def pointBounds15530 : List (Nat × Nat × Nat) := [(2039521280,96724548956638,96724927291434),(2039585792,96724957874606,96725336209667)]
theorem point_links_checked15530 : (cuts15530.take 2).map (fun c => (2039480321-1+2*2^9*c.k,96724283284174+c.lower,96724661618804+c.upper)) = pointBounds15530 := by
 decide +kernel
def cuts15531 : List PrefixCut := [⟨38,249509135,249509297⟩,
⟨101,658125170,658125607⟩,
⟨128,839590229,839590785⟩]
theorem checked15531 : checkPrefixCuts (2^48) 2039611393 9 Manual.Count131072.C015531.packed 128 cuts15531 = true := by
 decide +kernel
def pointBounds15531 : List (Nat × Nat × Nat) := [(2039650304,96725373403811,96725751739138),(2039714816,96725782019846,96726160355448)]
theorem point_links_checked15531 : (cuts15531.take 2).map (fun c => (2039611393-1+2*2^9*c.k,96725123894676+c.lower,96725502229841+c.upper)) = pointBounds15531 := by
 decide +kernel
def cuts15532 : List PrefixCut := [⟨36,235969836,235969989⟩,
⟨99,658497158,658497582⟩,
⟨128,856647109,856647665⟩]
theorem checked15532 : checkPrefixCuts (2^48) 2039742465 9 Manual.Count131072.C015532.packed 128 cuts15532 = true := by
 decide +kernel
def pointBounds15532 : List (Nat × Nat × Nat) := [(2039779328,96726199454741,96726577790615),(2039843840,96726621982063,96727000318208)]
theorem point_links_checked15532 : (cuts15532.take 2).map (fun c => (2039742465-1+2*2^9*c.k,96725963484905+c.lower,96726341820626+c.upper)) = pointBounds15532 := by
 decide +kernel
def cuts15533 : List PrefixCut := [⟨34,224639989,224640136⟩,
⟨97,632376406,632376821⟩,
⟨128,835342965,835343516⟩]
theorem checked15533 : checkPrefixCuts (2^48) 2039873537 9 Manual.Count131072.C015533.packed 128 cuts15533 = true := by
 decide +kernel
def pointBounds15533 : List (Nat × Nat × Nat) := [(2039908352,96727044772003,96727423108427),(2039972864,96727452508420,96727830845112)]
theorem point_links_checked15533 : (cuts15533.take 2).map (fun c => (2039873537-1+2*2^9*c.k,96726820132014+c.lower,96727198468291+c.upper)) = pointBounds15533 := by
 decide +kernel
def cuts15534 : List PrefixCut := [⟨32,204343180,204343313⟩,
⟨95,621574034,621574433⟩,
⟨128,844257373,844257917⟩]
theorem checked15534 : checkPrefixCuts (2^48) 2040004609 9 Manual.Count131072.C015534.packed 128 cuts15534 = true := by
 decide +kernel
def pointBounds15534 : List (Nat × Nat × Nat) := [(2040037376,96727859818159,96728238155120),(2040101888,96728277049013,96728655386240)]
theorem point_links_checked15534 : (cuts15534.take 2).map (fun c => (2040004609-1+2*2^9*c.k,96727655474979+c.lower,96728033811807+c.upper)) = pointBounds15534 := by
 decide +kernel
def cuts15535 : List PrefixCut := [⟨30,192878771,192878896⟩,
⟨93,608979519,608979915⟩,
⟨128,836615266,836615812⟩]
theorem checked15535 : checkPrefixCuts (2^48) 2040135681 9 Manual.Count131072.C015535.packed 128 cuts15535 = true := by
 decide +kernel
def pointBounds15535 : List (Nat × Nat × Nat) := [(2040166400,96728692611123,96729070948620),(2040230912,96729108711871,96729487049639)]
theorem point_links_checked15535 : (cuts15535.take 2).map (fun c => (2040135681-1+2*2^9*c.k,96728499732352+c.lower,96728878069724+c.upper)) = pointBounds15535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000172
