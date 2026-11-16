import PlattAssemblyKernel
import PlattCertificates.Count131072.C021504
import PlattCertificates.Count131072.C021505
import PlattCertificates.Count131072.C021506
import PlattCertificates.Count131072.C021507
import PlattCertificates.Count131072.C021508
import PlattCertificates.Count131072.C021509
import PlattCertificates.Count131072.C021510
import PlattCertificates.Count131072.C021511
import PlattCertificates.Count131072.C021512
import PlattCertificates.Count131072.C021513
import PlattCertificates.Count131072.C021514
import PlattCertificates.Count131072.C021515
import PlattCertificates.Count131072.C021516
import PlattCertificates.Count131072.C021517
import PlattCertificates.Count131072.C021518
import PlattCertificates.Count131072.C021519
import PlattCertificates.Count131072.C021520
import PlattCertificates.Count131072.C021521
import PlattCertificates.Count131072.C021522
import PlattCertificates.Count131072.C021523
import PlattCertificates.Count131072.C021524
import PlattCertificates.Count131072.C021525
import PlattCertificates.Count131072.C021526
import PlattCertificates.Count131072.C021527
import PlattCertificates.Count131072.C021528
import PlattCertificates.Count131072.C021529
import PlattCertificates.Count131072.C021530
import PlattCertificates.Count131072.C021531
import PlattCertificates.Count131072.C021532
import PlattCertificates.Count131072.C021533
import PlattCertificates.Count131072.C021534
import PlattCertificates.Count131072.C021535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21504 : List PrefixCut := [⟨9,42482878,42482901⟩,
⟨96,456334635,456334899⟩,
⟨128,608110269,608110622⟩]
theorem checked21504 : checkPrefixCuts (2^48) 2822504449 9 Manual.Count131072.C021504.packed 128 cuts21504 = true := by
 decide +kernel
def pointBounds21504 : List (Nat × Nat × Nat) := [(2822513664,100958915198964,100959296114196),(2822602752,100959329050721,100959709966194)]
theorem point_links_checked21504 : (cuts21504.take 2).map (fun c => (2822504449-1+2*2^9*c.k,100958872716086+c.lower,100959253631295+c.upper)) = pointBounds21504 := by
 decide +kernel
def cuts21505 : List PrefixCut := [⟨55,258273757,258273904⟩,
⟨128,596315381,596315723⟩]
theorem checked21505 : checkPrefixCuts (2^48) 2822635521 9 Manual.Count131072.C021505.packed 128 cuts21505 = true := by
 decide +kernel
def pointBounds21505 : List (Nat × Nat × Nat) := [(2822691840,100959739100112,100960120015821)]
theorem point_links_checked21505 : (cuts21505.take 1).map (fun c => (2822635521-1+2*2^9*c.k,100959480826355+c.lower,100959861741917+c.upper)) = pointBounds21505 := by
 decide +kernel
def cuts21506 : List PrefixCut := [⟨14,63319474,63319511⟩,
⟨101,474340086,474340360⟩,
⟨128,602669204,602669549⟩]
theorem checked21506 : checkPrefixCuts (2^48) 2822766593 9 Manual.Count131072.C021506.packed 128 cuts21506 = true := by
 decide +kernel
def pointBounds21506 : List (Nat × Nat × Nat) := [(2822780928,100960140461210,100960521377151),(2822870016,100960551481822,100960932398000)]
theorem point_links_checked21506 : (cuts21506.take 2).map (fun c => (2822766593-1+2*2^9*c.k,100960077141736+c.lower,100960458057640+c.upper)) = pointBounds21506 := by
 decide +kernel
def cuts21507 : List PrefixCut := [⟨60,284373629,284373790⟩,
⟨128,602741053,602741400⟩]
theorem checked21507 : checkPrefixCuts (2^48) 2822897665 9 Manual.Count131072.C021507.packed 128 cuts21507 = true := by
 decide +kernel
def pointBounds21507 : List (Nat × Nat × Nat) := [(2822959104,100960964184569,100961345100979)]
theorem point_links_checked21507 : (cuts21507.take 1).map (fun c => (2822897665-1+2*2^9*c.k,100960679810940+c.lower,100961060727189+c.upper)) = pointBounds21507 := by
 decide +kernel
def cuts21508 : List PrefixCut := [⟨19,90234262,90234315⟩,
⟨106,501913996,501914286⟩,
⟨128,602812900,602813249⟩]
theorem checked21508 : checkPrefixCuts (2^48) 2823028737 9 Manual.Count131072.C021508.packed 128 cuts21508 = true := by
 decide +kernel
def pointBounds21508 : List (Nat × Nat × Nat) := [(2823048192,100961372786255,100961753702904),(2823137280,100961784465989,100962165382875)]
theorem point_links_checked21508 : (cuts21508.take 2).map (fun c => (2823028737-1+2*2^9*c.k,100961282551993+c.lower,100961663468589+c.upper)) = pointBounds21508 := by
 decide +kernel
def cuts21509 : List PrefixCut := [⟨65,307377836,307378010⟩,
⟨128,598896532,598896879⟩]
theorem checked21509 : checkPrefixCuts (2^48) 2823159809 9 Manual.Count131072.C021509.packed 128 cuts21509 = true := by
 decide +kernel
def pointBounds21509 : List (Nat × Nat × Nat) := [(2823226368,100962192742729,100962573659848)]
theorem point_links_checked21509 : (cuts21509.take 1).map (fun c => (2823159809-1+2*2^9*c.k,100961885364893+c.lower,100962266281838+c.upper)) = pointBounds21509 := by
 decide +kernel
def cuts21510 : List PrefixCut := [⟨24,112757317,112757383⟩,
⟨111,510540389,510540691⟩,
⟨128,592388451,592388798⟩]
theorem checked21510 : checkPrefixCuts (2^48) 2823290881 9 Manual.Count131072.C021510.packed 128 cuts21510 = true := by
 decide +kernel
def pointBounds21510 : List (Nat × Nat × Nat) := [(2823315456,100962597018742,100962977936100),(2823404544,100962994801814,100963375719408)]
theorem point_links_checked21510 : (cuts21510.take 2).map (fun c => (2823290881-1+2*2^9*c.k,100962484261425+c.lower,100962865178717+c.upper)) = pointBounds21510 := by
 decide +kernel
def cuts21511 : List PrefixCut := [⟨70,329580251,329580446⟩,
⟨128,604224134,604224489⟩]
theorem checked21511 : checkPrefixCuts (2^48) 2823421953 9 Manual.Count131072.C021511.packed 128 cuts21511 = true := by
 decide +kernel
def pointBounds21511 : List (Nat × Nat × Nat) := [(2823493632,100963406230127,100963787147961)]
theorem point_links_checked21511 : (cuts21511.take 1).map (fun c => (2823421953-1+2*2^9*c.k,100963076649876+c.lower,100963457567515+c.upper)) = pointBounds21511 := by
 decide +kernel
def cuts21512 : List PrefixCut := [⟨29,137568973,137569053⟩,
⟨116,546578905,546579223⟩,
⟨128,603398656,603399010⟩]
theorem checked21512 : checkPrefixCuts (2^48) 2823553025 9 Manual.Count131072.C021512.packed 128 cuts21512 = true := by
 decide +kernel
def pointBounds21512 : List (Nat × Nat × Nat) := [(2823582720,100963818442983,100964199361057),(2823671808,100964227452915,100964608371227)]
theorem point_links_checked21512 : (cuts21512.take 2).map (fun c => (2823553025-1+2*2^9*c.k,100963680874010+c.lower,100964061792004+c.upper)) = pointBounds21512 := by
 decide +kernel
def cuts21513 : List PrefixCut := [⟨75,361647077,361647283⟩,
⟨128,607956064,607956416⟩]
theorem checked21513 : checkPrefixCuts (2^48) 2823684097 9 Manual.Count131072.C021513.packed 128 cuts21513 = true := by
 decide +kernel
def pointBounds21513 : List (Nat × Nat × Nat) := [(2823760896,100964645919743,100965026838297)]
theorem point_links_checked21513 : (cuts21513.take 1).map (fun c => (2823684097-1+2*2^9*c.k,100964284272666+c.lower,100964665191014+c.upper)) = pointBounds21513 := by
 decide +kernel
def cuts21514 : List PrefixCut := [⟨34,160083383,160083475⟩,
⟨121,568356832,568357159⟩,
⟨128,599654608,599654954⟩]
theorem checked21514 : checkPrefixCuts (2^48) 2823815169 9 Manual.Count131072.C021514.packed 128 cuts21514 = true := by
 decide +kernel
def pointBounds21514 : List (Nat × Nat × Nat) := [(2823849984,100965052312113,100965433230905),(2823939072,100965460585562,100965841504589)]
theorem point_links_checked21514 : (cuts21514.take 2).map (fun c => (2823815169-1+2*2^9*c.k,100964892228730+c.lower,100965273147430+c.upper)) = pointBounds21514 := by
 decide +kernel
def cuts21515 : List PrefixCut := [⟨80,377162158,377162377⟩,
⟨128,602018934,602019283⟩]
theorem checked21515 : checkPrefixCuts (2^48) 2823946241 9 Manual.Count131072.C021515.packed 128 cuts21515 = true := by
 decide +kernel
def pointBounds21515 : List (Nat × Nat × Nat) := [(2824028160,100965869045496,100966249964761)]
theorem point_links_checked21515 : (cuts21515.take 1).map (fun c => (2823946241-1+2*2^9*c.k,100965491883338+c.lower,100965872802384+c.upper)) = pointBounds21515 := by
 decide +kernel
def cuts21516 : List PrefixCut := [⟨39,180998880,180998985⟩,
⟨126,589532717,589533057⟩,
⟨128,599499227,599499572⟩]
theorem checked21516 : checkPrefixCuts (2^48) 2824077313 9 Manual.Count131072.C021516.packed 128 cuts21516 = true := by
 decide +kernel
def pointBounds21516 : List (Nat × Nat × Nat) := [(2824117248,100966274901152,100966655820652),(2824206336,100966683434989,100967064354724)]
theorem point_links_checked21516 : (cuts21516.take 2).map (fun c => (2824077313-1+2*2^9*c.k,100966093902272+c.lower,100966474821667+c.upper)) = pointBounds21516 := by
 decide +kernel
def cuts21517 : List PrefixCut := [⟨85,398155786,398156010⟩,
⟨128,593691072,593691411⟩]
theorem checked21517 : checkPrefixCuts (2^48) 2824208385 9 Manual.Count131072.C021517.packed 128 cuts21517 = true := by
 decide +kernel
def pointBounds21517 : List (Nat × Nat × Nat) := [(2824295424,100967091557285,100967472477249)]
theorem point_links_checked21517 : (cuts21517.take 1).map (fun c => (2824208385-1+2*2^9*c.k,100966693401499+c.lower,100967074321239+c.upper)) = pointBounds21517 := by
 decide +kernel
def cuts21518 : List PrefixCut := [⟨44,208189000,208189120⟩,
⟨128,604027894,604028242⟩]
theorem checked21518 : checkPrefixCuts (2^48) 2824339457 9 Manual.Count131072.C021518.packed 128 cuts21518 = true := by
 decide +kernel
def pointBounds21518 : List (Nat × Nat × Nat) := [(2824384512,100967495281571,100967876201770)]
theorem point_links_checked21518 : (cuts21518.take 1).map (fun c => (2824339457-1+2*2^9*c.k,100967287092571+c.lower,100967668012650+c.upper)) = pointBounds21518 := by
 decide +kernel
def cuts21519 : List PrefixCut := [⟨3,14549741,14549749⟩,
⟨90,429409921,429410165⟩,
⟨128,607188878,607189219⟩]
theorem checked21519 : checkPrefixCuts (2^48) 2824470529 9 Manual.Count131072.C021519.packed 128 cuts21519 = true := by
 decide +kernel
def pointBounds21519 : List (Nat × Nat × Nat) := [(2824473600,100967905670206,100968286590641),(2824562688,100968320530386,100968701451057)]
theorem point_links_checked21519 : (cuts21519.take 2).map (fun c => (2824470529-1+2*2^9*c.k,100967891120465+c.lower,100968272040892+c.upper)) = pointBounds21519 := by
 decide +kernel
def cuts21520 : List PrefixCut := [⟨49,231288345,231288478⟩,
⟨128,598790120,598790470⟩]
theorem checked21520 : checkPrefixCuts (2^48) 2824601601 9 Manual.Count131072.C021520.packed 128 cuts21520 = true := by
 decide +kernel
def pointBounds21520 : List (Nat × Nat × Nat) := [(2824651776,100968729597688,100969110518589)]
theorem point_links_checked21520 : (cuts21520.take 1).map (fun c => (2824601601-1+2*2^9*c.k,100968498309343+c.lower,100968879230111+c.upper)) = pointBounds21520 := by
 decide +kernel
def cuts21521 : List PrefixCut := [⟨8,35374476,35374498⟩,
⟨95,440729163,440729416⟩,
⟨128,591089733,591090069⟩]
theorem checked21521 : checkPrefixCuts (2^48) 2824732673 9 Manual.Count131072.C021521.packed 128 cuts21521 = true := by
 decide +kernel
def pointBounds21521 : List (Nat × Nat × Nat) := [(2824740864,100969132473939,100969513395079),(2824829952,100969537828626,100969918749997)]
theorem point_links_checked21521 : (cuts21521.take 2).map (fun c => (2824732673-1+2*2^9*c.k,100969097099463+c.lower,100969478020581+c.upper)) = pointBounds21521 := by
 decide +kernel
def cuts21522 : List PrefixCut := [⟨54,251991978,251992120⟩,
⟨128,597738083,597738422⟩]
theorem checked21522 : checkPrefixCuts (2^48) 2824863745 9 Manual.Count131072.C021522.packed 128 cuts21522 = true := by
 decide +kernel
def pointBounds21522 : List (Nat × Nat × Nat) := [(2824919040,100969940181174,100970321102770)]
theorem point_links_checked21522 : (cuts21522.take 1).map (fun c => (2824863745-1+2*2^9*c.k,100969688189196+c.lower,100970069110650+c.upper)) = pointBounds21522 := by
 decide +kernel
def cuts21523 : List PrefixCut := [⟨13,61974265,61974300⟩,
⟨100,469183627,469183899⟩,
⟨128,599902378,599902729⟩]
theorem checked21523 : checkPrefixCuts (2^48) 2824994817 9 Manual.Count131072.C021523.packed 128 cuts21523 = true := by
 decide +kernel
def pointBounds21523 : List (Nat × Nat × Nat) := [(2825008128,100970347901544,100970728823372),(2825097216,100970755110906,100971136032971)]
theorem point_links_checked21523 : (cuts21523.take 2).map (fun c => (2824994817-1+2*2^9*c.k,100970285927279+c.lower,100970666849072+c.upper)) = pointBounds21523 := by
 decide +kernel
def cuts21524 : List PrefixCut := [⟨59,276975887,276976046⟩,
⟨128,604756357,604756707⟩]
theorem checked21524 : checkPrefixCuts (2^48) 2825125889 9 Manual.Count131072.C021524.packed 128 cuts21524 = true := by
 decide +kernel
def pointBounds21524 : List (Nat × Nat × Nat) := [(2825186304,100971162805544,100971543727847)]
theorem point_links_checked21524 : (cuts21524.take 1).map (fun c => (2825125889-1+2*2^9*c.k,100970885829657+c.lower,100971266751801+c.upper)) = pointBounds21524 := by
 decide +kernel
def cuts21525 : List PrefixCut := [⟨18,79702193,79702241⟩,
⟨105,488168163,488168447⟩,
⟨128,596658557,596658901⟩]
theorem checked21525 : checkPrefixCuts (2^48) 2825256961 9 Manual.Count131072.C021525.packed 128 cuts21525 = true := by
 decide +kernel
def pointBounds21525 : List (Nat × Nat × Nat) := [(2825275392,100971570288207,100971951210749),(2825364480,100971978754177,100972359676955)]
theorem point_links_checked21525 : (cuts21525.take 2).map (fun c => (2825256961-1+2*2^9*c.k,100971490586014+c.lower,100971871508508+c.upper)) = pointBounds21525 := by
 decide +kernel
def cuts21526 : List PrefixCut := [⟨64,298169525,298169701⟩,
⟨128,600914653,600915007⟩]
theorem checked21526 : checkPrefixCuts (2^48) 2825388033 9 Manual.Count131072.C021526.packed 128 cuts21526 = true := by
 decide +kernel
def pointBounds21526 : List (Nat × Nat × Nat) := [(2825453568,100972385414096,100972766337110)]
theorem point_links_checked21526 : (cuts21526.take 1).map (fun c => (2825388033-1+2*2^9*c.k,100972087244571+c.lower,100972468167409+c.upper)) = pointBounds21526 := by
 decide +kernel
def cuts21527 : List PrefixCut := [⟨23,103702767,103702826⟩,
⟨110,517808222,517808519⟩,
⟨128,603177876,603178223⟩]
theorem checked21527 : checkPrefixCuts (2^48) 2825519105 9 Manual.Count131072.C021527.packed 128 cuts21527 = true := by
 decide +kernel
def pointBounds21527 : List (Nat × Nat × Nat) := [(2825542656,100972791861991,100973172785242),(2825631744,100973205967446,100973586890935)]
theorem point_links_checked21527 : (cuts21527.take 2).map (fun c => (2825519105-1+2*2^9*c.k,100972688159224+c.lower,100973069082416+c.upper)) = pointBounds21527 := by
 decide +kernel
def cuts21528 : List PrefixCut := [⟨69,318462598,318462783⟩,
⟨128,592790307,592790655⟩]
theorem checked21528 : checkPrefixCuts (2^48) 2825650177 9 Manual.Count131072.C021528.packed 128 cuts21528 = true := by
 decide +kernel
def pointBounds21528 : List (Nat × Nat × Nat) := [(2825720832,100973609799698,100973990723422)]
theorem point_links_checked21528 : (cuts21528.take 1).map (fun c => (2825650177-1+2*2^9*c.k,100973291337100+c.lower,100973672260639+c.upper)) = pointBounds21528 := by
 decide +kernel
def cuts21529 : List PrefixCut := [⟨28,131982039,131982118⟩,
⟨115,542462512,542462834⟩,
⟨128,603719704,603720063⟩]
theorem checked21529 : checkPrefixCuts (2^48) 2825781249 9 Manual.Count131072.C021529.packed 128 cuts21529 = true := by
 decide +kernel
def pointBounds21529 : List (Nat × Nat × Nat) := [(2825809920,100974016109446,100974397033412),(2825899008,100974426589919,100974807514128)]
theorem point_links_checked21529 : (cuts21529.take 2).map (fun c => (2825781249-1+2*2^9*c.k,100973884127407+c.lower,100974265051294+c.upper)) = pointBounds21529 := by
 decide +kernel
def cuts21530 : List PrefixCut := [⟨74,349807927,349808129⟩,
⟨128,600404851,600405198⟩]
theorem checked21530 : checkPrefixCuts (2^48) 2825912321 9 Manual.Count131072.C021530.packed 128 cuts21530 = true := by
 decide +kernel
def pointBounds21530 : List (Nat × Nat × Nat) := [(2825988096,100974837655038,100975218579486)]
theorem point_links_checked21530 : (cuts21530.take 1).map (fun c => (2825912321-1+2*2^9*c.k,100974487847111+c.lower,100974868771357+c.upper)) = pointBounds21530 := by
 decide +kernel
def cuts21531 : List PrefixCut := [⟨33,151790019,151790108⟩,
⟨120,553566711,553567043⟩,
⟨128,589321630,589321983⟩]
theorem checked21531 : checkPrefixCuts (2^48) 2826043393 9 Manual.Count131072.C021531.packed 128 cuts21531 = true := by
 decide +kernel
def pointBounds21531 : List (Nat × Nat × Nat) := [(2826077184,100975240041981,100975620966663),(2826166272,100975641818673,100976022743598)]
theorem point_links_checked21531 : (cuts21531.take 2).map (fun c => (2826043393-1+2*2^9*c.k,100975088251962+c.lower,100975469176555+c.upper)) = pointBounds21531 := by
 decide +kernel
def cuts21532 : List PrefixCut := [⟨79,366307857,366308069⟩,
⟨128,597162127,597162473⟩]
theorem checked21532 : checkPrefixCuts (2^48) 2826174465 9 Manual.Count131072.C021532.packed 128 cuts21532 = true := by
 decide +kernel
def pointBounds21532 : List (Nat × Nat × Nat) := [(2826255360,100976043881449,100976424806607)]
theorem point_links_checked21532 : (cuts21532.take 1).map (fun c => (2826174465-1+2*2^9*c.k,100975677573592+c.lower,100976058498538+c.upper)) = pointBounds21532 := by
 decide +kernel
def cuts21533 : List PrefixCut := [⟨38,179860298,179860402⟩,
⟨125,591557776,591558116⟩,
⟨128,605201133,605201480⟩]
theorem checked21533 : checkPrefixCuts (2^48) 2826305537 9 Manual.Count131072.C021533.packed 128 cuts21533 = true := by
 decide +kernel
def pointBounds21533 : List (Nat × Nat × Nat) := [(2826344448,100976454596017,100976835521413),(2826433536,100976866293495,100977247219127)]
theorem point_links_checked21533 : (cuts21533.take 2).map (fun c => (2826305537-1+2*2^9*c.k,100976274735719+c.lower,100976655661011+c.upper)) = pointBounds21533 := by
 decide +kernel
def cuts21534 : List PrefixCut := [⟨84,393858607,393858835⟩,
⟨128,599596394,599596740⟩]
theorem checked21534 : checkPrefixCuts (2^48) 2826436609 9 Manual.Count131072.C021534.packed 128 cuts21534 = true := by
 decide +kernel
def pointBounds21534 : List (Nat × Nat × Nat) := [(2826522624,100977273795459,100977654721326)]
theorem point_links_checked21534 : (cuts21534.take 1).map (fun c => (2826436609-1+2*2^9*c.k,100976879936852+c.lower,100977260862491+c.upper)) = pointBounds21534 := by
 decide +kernel
def cuts21535 : List PrefixCut := [⟨43,202547907,202548026⟩,
⟨128,604846202,604846548⟩]
theorem checked21535 : checkPrefixCuts (2^48) 2826567681 9 Manual.Count131072.C021535.packed 128 cuts21535 = true := by
 decide +kernel
def pointBounds21535 : List (Nat × Nat × Nat) := [(2826611712,100977682081153,100978063007257)]
theorem point_links_checked21535 : (cuts21535.take 1).map (fun c => (2826567681-1+2*2^9*c.k,100977479533246+c.lower,100977860459231+c.upper)) = pointBounds21535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000047
