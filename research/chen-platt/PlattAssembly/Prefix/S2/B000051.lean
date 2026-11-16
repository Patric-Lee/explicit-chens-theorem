import PlattAssemblyKernel
import PlattCertificates.Count131072.C011632
import PlattCertificates.Count131072.C011633
import PlattCertificates.Count131072.C011634
import PlattCertificates.Count131072.C011635
import PlattCertificates.Count131072.C011636
import PlattCertificates.Count131072.C011637
import PlattCertificates.Count131072.C011638
import PlattCertificates.Count131072.C011639
import PlattCertificates.Count131072.C011640
import PlattCertificates.Count131072.C011641
import PlattCertificates.Count131072.C011642
import PlattCertificates.Count131072.C011643
import PlattCertificates.Count131072.C011644
import PlattCertificates.Count131072.C011645
import PlattCertificates.Count131072.C011646
import PlattCertificates.Count131072.C011647
import PlattCertificates.Count131072.C011648
import PlattCertificates.Count131072.C011649
import PlattCertificates.Count131072.C011650
import PlattCertificates.Count131072.C011651
import PlattCertificates.Count131072.C011652
import PlattCertificates.Count131072.C011653
import PlattCertificates.Count131072.C011654
import PlattCertificates.Count131072.C011655
import PlattCertificates.Count131072.C011656
import PlattCertificates.Count131072.C011657
import PlattCertificates.Count131072.C011658
import PlattCertificates.Count131072.C011659
import PlattCertificates.Count131072.C011660
import PlattCertificates.Count131072.C011661
import PlattCertificates.Count131072.C011662
import PlattCertificates.Count131072.C011663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11632 : List PrefixCut := [⟨10,87467919,87467990⟩,
⟨57,505096260,505096656⟩,
⟨104,915162070,915162788⟩,
⟨128,1126910749,1126911630⟩]
theorem checked11632 : checkPrefixCuts (2^48) 1528561665 9 Manual.Count131072.C011632.packed 128 cuts11632 = true := by
 decide +kernel
def pointBounds11632 : List (Nat × Nat × Nat) := [(1528571904,92912256382023,92912631998367),(1528620032,92912674010364,92913049627033),(1528668160,92913084076174,92913459693165)]
theorem point_links_checked11632 : (cuts11632.take 3).map (fun c => (1528561665-1+2*2^9*c.k,92912168914104+c.lower,92912544530377+c.upper)) = pointBounds11632 := by
 decide +kernel
def cuts11633 : List PrefixCut := [⟨23,202354941,202355098⟩,
⟨70,627492804,627493298⟩,
⟨117,1040649711,1040650531⟩,
⟨128,1137308882,1137309778⟩]
theorem checked11633 : checkPrefixCuts (2^48) 1528692737 9 Manual.Count131072.C011633.packed 128 cuts11633 = true := by
 decide +kernel
def pointBounds11633 : List (Nat × Nat × Nat) := [(1528716288,92913498179794,92913873797105),(1528764416,92913923317657,92914298935305),(1528812544,92914336474564,92914712092538)]
theorem point_links_checked11633 : (cuts11633.take 3).map (fun c => (1528692737-1+2*2^9*c.k,92913295824853+c.lower,92913671442007+c.upper)) = pointBounds11633 := by
 decide +kernel
def cuts11634 : List PrefixCut := [⟨36,323296833,323297086⟩,
⟨83,744528465,744529044⟩,
⟨128,1144391561,1144392451⟩]
theorem checked11634 : checkPrefixCuts (2^48) 1528823809 9 Manual.Count131072.C011634.packed 128 cuts11634 = true := by
 decide +kernel
def pointBounds11634 : List (Nat × Nat × Nat) := [(1528860672,92914756430568,92915132048871),(1528908800,92915177662200,92915553280829)]
theorem point_links_checked11634 : (cuts11634.take 2).map (fun c => (1528823809-1+2*2^9*c.k,92914433133735+c.lower,92914808751785+c.upper)) = pointBounds11634 := by
 decide +kernel
def cuts11635 : List PrefixCut := [⟨2,18041421,18041434⟩,
⟨49,427096331,427096663⟩,
⟨96,844974513,844975174⟩,
⟨128,1135272462,1135273352⟩]
theorem checked11635 : checkPrefixCuts (2^48) 1528954881 9 Manual.Count131072.C011635.packed 128 cuts11635 = true := by
 decide +kernel
def pointBounds11635 : List (Nat × Nat × Nat) := [(1528956928,92915595566717,92915971185670),(1529005056,92916004621627,92916380240899),(1529053184,92916422499809,92916798119410)]
theorem point_links_checked11635 : (cuts11635.take 3).map (fun c => (1528954881-1+2*2^9*c.k,92915577525296+c.lower,92915953144236+c.upper)) = pointBounds11635 := by
 decide +kernel
def cuts11636 : List PrefixCut := [⟨15,140268605,140268712⟩,
⟨62,571558034,571558480⟩,
⟨109,998416176,998416957⟩,
⟨128,1170701805,1170702721⟩]
theorem checked11636 : checkPrefixCuts (2^48) 1529085953 9 Manual.Count131072.C011636.packed 128 cuts11636 = true := by
 decide +kernel
def pointBounds11636 : List (Nat × Nat × Nat) := [(1529101312,92916853066363,92917228686300),(1529149440,92917284355792,92917659976068),(1529197568,92917711213934,92918086834545)]
theorem point_links_checked11636 : (cuts11636.take 3).map (fun c => (1529085953-1+2*2^9*c.k,92916712797758+c.lower,92917088417588+c.upper)) = pointBounds11636 := by
 decide +kernel
def cuts11637 : List PrefixCut := [⟨28,249589393,249589590⟩,
⟨75,666481593,666482115⟩,
⟨122,1092195212,1092196068⟩,
⟨128,1145201407,1145202306⟩]
theorem checked11637 : checkPrefixCuts (2^48) 1529217025 9 Manual.Count131072.C011637.packed 128 cuts11637 = true := by
 decide +kernel
def pointBounds11637 : List (Nat × Nat × Nat) := [(1529245696,92918133088956,92918508709899),(1529293824,92918549981156,92918925602424),(1529341952,92918975694775,92919351316377)]
theorem point_links_checked11637 : (cuts11637.take 3).map (fun c => (1529217025-1+2*2^9*c.k,92917883499563+c.lower,92918259120309+c.upper)) = pointBounds11637 := by
 decide +kernel
def cuts11638 : List PrefixCut := [⟨41,363307582,363307868⟩,
⟨88,785497546,785498166⟩,
⟨128,1148599790,1148600689⟩]
theorem checked11638 : checkPrefixCuts (2^48) 1529348097 9 Manual.Count131072.C011638.packed 128 cuts11638 = true := by
 decide +kernel
def pointBounds11638 : List (Nat × Nat × Nat) := [(1529390080,92919392008552,92919767630483),(1529438208,92919814198516,92920189820781)]
theorem point_links_checked11638 : (cuts11638.take 2).map (fun c => (1529348097-1+2*2^9*c.k,92919028700970+c.lower,92919404322615+c.upper)) = pointBounds11638 := by
 decide +kernel
def cuts11639 : List PrefixCut := [⟨7,66619848,66619902⟩,
⟨54,486022725,486023106⟩,
⟨101,907804774,907805484⟩,
⟨128,1141140908,1141141802⟩]
theorem checked11639 : checkPrefixCuts (2^48) 1529479169 9 Manual.Count131072.C011639.packed 128 cuts11639 = true := by
 decide +kernel
def pointBounds11639 : List (Nat × Nat × Nat) := [(1529486336,92920243920608,92920619543206),(1529534464,92920663323485,92921038946410),(1529582592,92921085105534,92921460728788)]
theorem point_links_checked11639 : (cuts11639.take 3).map (fun c => (1529479169-1+2*2^9*c.k,92920177300760+c.lower,92920552923304+c.upper)) = pointBounds11639 := by
 decide +kernel
def cuts11640 : List PrefixCut := [⟨20,175367400,175367536⟩,
⟨67,607611630,607612103⟩,
⟨114,1033217990,1033218797⟩,
⟨128,1157051655,1157052559⟩]
theorem checked11640 : checkPrefixCuts (2^48) 1529610241 9 Manual.Count131072.C011640.packed 128 cuts11640 = true := by
 decide +kernel
def pointBounds11640 : List (Nat × Nat × Nat) := [(1529630720,92921493809068,92921869432642),(1529678848,92921926053298,92922301677209),(1529726976,92922351659658,92922727283903)]
theorem point_links_checked11640 : (cuts11640.take 3).map (fun c => (1529610241-1+2*2^9*c.k,92921318441668+c.lower,92921694065106+c.upper)) = pointBounds11640 := by
 decide +kernel
def cuts11641 : List PrefixCut := [⟨33,300655246,300655482⟩,
⟨80,722555032,722555598⟩,
⟨127,1132298275,1132299165⟩,
⟨128,1142601486,1142602384⟩]
theorem checked11641 : checkPrefixCuts (2^48) 1529741313 9 Manual.Count131072.C011641.packed 128 cuts11641 = true := by
 decide +kernel
def pointBounds11641 : List (Nat × Nat × Nat) := [(1529775104,92922776148569,92923151773147),(1529823232,92923198048355,92923573673263),(1529871360,92923607791598,92923983416830)]
theorem point_links_checked11641 : (cuts11641.take 3).map (fun c => (1529741313-1+2*2^9*c.k,92922475493323+c.lower,92922851117665+c.upper)) = pointBounds11641 := by
 decide +kernel
def cuts11642 : List PrefixCut := [⟨46,418929341,418929664⟩,
⟨93,837661621,837662275⟩,
⟨128,1149126679,1149127576⟩]
theorem checked11642 : checkPrefixCuts (2^48) 1529872385 9 Manual.Count131072.C011642.packed 128 cuts11642 = true := by
 decide +kernel
def pointBounds11642 : List (Nat × Nat × Nat) := [(1529919488,92924037024150,92924412649713),(1529967616,92924455756430,92924831382324)]
theorem point_links_checked11642 : (cuts11642.take 2).map (fun c => (1529872385-1+2*2^9*c.k,92923618094809+c.lower,92923993720049+c.upper)) = pointBounds11642 := by
 decide +kernel
def cuts11643 : List PrefixCut := [⟨12,111485433,111485520⟩,
⟨59,516578025,516578434⟩,
⟨106,933431368,933432098⟩,
⟨128,1131919539,1131920424⟩]
theorem checked11643 : checkPrefixCuts (2^48) 1530003457 9 Manual.Count131072.C011643.packed 128 cuts11643 = true := by
 decide +kernel
def pointBounds11643 : List (Nat × Nat × Nat) := [(1530015744,92924878706921,92925254333145),(1530063872,92925283799513,92925659426059),(1530112000,92925700652856,92926076279723)]
theorem point_links_checked11643 : (cuts11643.take 3).map (fun c => (1530003457-1+2*2^9*c.k,92924767221488+c.lower,92925142847625+c.upper)) = pointBounds11643 := by
 decide +kernel
def cuts11644 : List PrefixCut := [⟨25,222950741,222950917⟩,
⟨72,647503579,647504084⟩,
⟨119,1071123355,1071124197⟩,
⟨128,1148745658,1148746562⟩]
theorem checked11644 : checkPrefixCuts (2^48) 1530134529 9 Manual.Count131072.C011644.packed 128 cuts11644 = true := by
 decide +kernel
def pointBounds11644 : List (Nat × Nat × Nat) := [(1530160128,92926122091768,92926497718966),(1530208256,92926546644606,92926922272133),(1530256384,92926970264382,92927345892246)]
theorem point_links_checked11644 : (cuts11644.take 3).map (fun c => (1530134529-1+2*2^9*c.k,92925899141027+c.lower,92926274768049+c.upper)) = pointBounds11644 := by
 decide +kernel
def cuts11645 : List PrefixCut := [⟨38,335315786,335316051⟩,
⟨85,750999876,751000468⟩,
⟨128,1128966596,1128967487⟩]
theorem checked11645 : checkPrefixCuts (2^48) 1530265601 9 Manual.Count131072.C011645.packed 128 cuts11645 = true := by
 decide +kernel
def pointBounds11645 : List (Nat × Nat × Nat) := [(1530304512,92927383202471,92927758830662),(1530352640,92927798886561,92928174515079)]
theorem point_links_checked11645 : (cuts11645.take 2).map (fun c => (1530265601-1+2*2^9*c.k,92927047886685+c.lower,92927423514611+c.upper)) = pointBounds11645 := by
 decide +kernel
def cuts11646 : List PrefixCut := [⟨4,36048824,36048852⟩,
⟨51,460534841,460535200⟩,
⟨98,873972641,873973321⟩,
⟨128,1142663559,1142664450⟩]
theorem checked11646 : checkPrefixCuts (2^48) 1530396673 9 Manual.Count131072.C011646.packed 128 cuts11646 = true := by
 decide +kernel
def pointBounds11646 : List (Nat × Nat × Nat) := [(1530400768,92928212902105,92928588530950),(1530448896,92928637388122,92929013017298),(1530497024,92929050825922,92929426455419)]
theorem point_links_checked11646 : (cuts11646.take 3).map (fun c => (1530396673-1+2*2^9*c.k,92928176853281+c.lower,92928552482098+c.upper)) = pointBounds11646 := by
 decide +kernel
def cuts11647 : List PrefixCut := [⟨17,151906372,151906485⟩,
⟨64,570467539,570467979⟩,
⟨111,991406266,991407036⟩,
⟨128,1144220813,1144221702⟩]
theorem checked11647 : checkPrefixCuts (2^48) 1530527745 9 Manual.Count131072.C011647.packed 128 cuts11647 = true := by
 decide +kernel
def pointBounds11647 : List (Nat × Nat × Nat) := [(1530545152,92929471423212,92929847053033),(1530593280,92929889984379,92930265614527),(1530641408,92930310923106,92930686553584)]
theorem point_links_checked11647 : (cuts11647.take 3).map (fun c => (1530527745-1+2*2^9*c.k,92929319516840+c.lower,92929695146548+c.upper)) = pointBounds11647 := by
 decide +kernel
def cuts11648 : List PrefixCut := [⟨30,266639751,266639961⟩,
⟨77,684793541,684794079⟩,
⟨124,1103118171,1103119034⟩,
⟨128,1141548216,1141549107⟩]
theorem checked11648 : checkPrefixCuts (2^48) 1530658817 9 Manual.Count131072.C011648.packed 128 cuts11648 = true := by
 decide +kernel
def pointBounds11648 : List (Nat × Nat × Nat) := [(1530689536,92930730377404,92931106008211),(1530737664,92931148531194,92931524162329),(1530785792,92931566855824,92931942487284)]
theorem point_links_checked11648 : (cuts11648.take 3).map (fun c => (1530658817-1+2*2^9*c.k,92930463737653+c.lower,92930839368250+c.upper)) = pointBounds11648 := by
 decide +kernel
def cuts11649 : List PrefixCut := [⟨43,381536339,381536638⟩,
⟨90,788802609,788803229⟩,
⟨128,1122880140,1122881020⟩]
theorem checked11649 : checkPrefixCuts (2^48) 1530789889 9 Manual.Count131072.C011649.packed 128 cuts11649 = true := by
 decide +kernel
def pointBounds11649 : List (Nat × Nat × Nat) := [(1530833920,92931986822208,92932362453995),(1530882048,92932394088478,92932769720586)]
theorem point_links_checked11649 : (cuts11649.take 2).map (fun c => (1530789889-1+2*2^9*c.k,92931605285869+c.lower,92931980917357+c.upper)) = pointBounds11649 := by
 decide +kernel
def cuts11650 : List PrefixCut := [⟨9,78691775,78691833⟩,
⟨56,490344944,490345325⟩,
⟨103,911729254,911729968⟩,
⟨128,1121313266,1121314143⟩]
theorem checked11650 : checkPrefixCuts (2^48) 1530920961 9 Manual.Count131072.C011650.packed 128 cuts11650 = true := by
 decide +kernel
def pointBounds11650 : List (Nat × Nat × Nat) := [(1530930176,92932806857784,92933182490210),(1530978304,92933218510953,92933594143702),(1531026432,92933639895263,92934015528345)]
theorem point_links_checked11650 : (cuts11650.take 3).map (fun c => (1530920961-1+2*2^9*c.k,92932728166009+c.lower,92933103798377+c.upper)) = pointBounds11650 := by
 decide +kernel
def cuts11651 : List PrefixCut := [⟨22,196160197,196160350⟩,
⟨69,612370513,612370988⟩,
⟨116,1027097143,1027097948⟩,
⟨128,1137026939,1137027829⟩]
theorem checked11651 : checkPrefixCuts (2^48) 1531052033 9 Manual.Count131072.C011651.packed 128 cuts11651 = true := by
 decide +kernel
def pointBounds11651 : List (Nat × Nat × Nat) := [(1531074560,92934045639472,92934421272870),(1531122688,92934461849788,92934837483508),(1531170816,92934876576418,92935252210468)]
theorem point_links_checked11651 : (cuts11651.take 3).map (fun c => (1531052033-1+2*2^9*c.k,92933849479275+c.lower,92934225112520+c.upper)) = pointBounds11651 := by
 decide +kernel
def cuts11652 : List PrefixCut := [⟨35,308644215,308644454⟩,
⟨82,723712399,723712962⟩,
⟨128,1133069388,1133070265⟩]
theorem checked11652 : checkPrefixCuts (2^48) 1531183105 9 Manual.Count131072.C011652.packed 128 cuts11652 = true := by
 decide +kernel
def pointBounds11652 : List (Nat × Nat × Nat) := [(1531218944,92935295150429,92935670784803),(1531267072,92935710218613,92936085853311)]
theorem point_links_checked11652 : (cuts11652.take 2).map (fun c => (1531183105-1+2*2^9*c.k,92934986506214+c.lower,92935362140349+c.upper)) = pointBounds11652 := by
 decide +kernel
def cuts11653 : List PrefixCut := [⟨1,9558253,9558260⟩,
⟨48,429930875,429931208⟩,
⟨95,842386638,842387300⟩,
⟨128,1134626946,1134627837⟩]
theorem checked11653 : checkPrefixCuts (2^48) 1531314177 9 Manual.Count131072.C011653.packed 128 cuts11653 = true := by
 decide +kernel
def pointBounds11653 : List (Nat × Nat × Nat) := [(1531315200,92936129133855,92936504768874),(1531363328,92936549506477,92936925141822),(1531411456,92936961962240,92937337597914)]
theorem point_links_checked11653 : (cuts11653.take 3).map (fun c => (1531314177-1+2*2^9*c.k,92936119575602+c.lower,92936495210614+c.upper)) = pointBounds11653 := by
 decide +kernel
def cuts11654 : List PrefixCut := [⟨14,125532672,125532772⟩,
⟨61,543292514,543292939⟩,
⟨108,951298461,951299209⟩,
⟨128,1133610599,1133611490⟩]
theorem checked11654 : checkPrefixCuts (2^48) 1531445249 9 Manual.Count131072.C011654.packed 128 cuts11654 = true := by
 decide +kernel
def pointBounds11654 : List (Nat × Nat × Nat) := [(1531459584,92937379735220,92937755371223),(1531507712,92937797495062,92938173131390),(1531555840,92938205501009,92938581137660)]
theorem point_links_checked11654 : (cuts11654.take 3).map (fun c => (1531445249-1+2*2^9*c.k,92937254202548+c.lower,92937629838451+c.upper)) = pointBounds11654 := by
 decide +kernel
def cuts11655 : List PrefixCut := [⟨27,241302454,241302641⟩,
⟨74,659390435,659390944⟩,
⟨121,1077832807,1077833646⟩,
⟨128,1139026842,1139027729⟩]
theorem checked11655 : checkPrefixCuts (2^48) 1531576321 9 Manual.Count131072.C011655.packed 128 cuts11655 = true := by
 decide +kernel
def pointBounds11655 : List (Nat × Nat × Nat) := [(1531603968,92938629115601,92939004752582),(1531652096,92939047203582,92939422840885),(1531700224,92939465645954,92939841283587)]
theorem point_links_checked11655 : (cuts11655.take 3).map (fun c => (1531576321-1+2*2^9*c.k,92938387813147+c.lower,92938763449941+c.upper)) = pointBounds11655 := by
 decide +kernel
def cuts11656 : List PrefixCut := [⟨40,353743731,353744008⟩,
⟨87,762420692,762421291⟩,
⟨128,1130108886,1130109769⟩]
theorem checked11656 : checkPrefixCuts (2^48) 1531707393 9 Manual.Count131072.C011656.packed 128 cuts11656 = true := by
 decide +kernel
def pointBounds11656 : List (Nat × Nat × Nat) := [(1531748352,92939880583720,92940256221678),(1531796480,92940289260681,92940664898961)]
theorem point_links_checked11656 : (cuts11656.take 2).map (fun c => (1531707393-1+2*2^9*c.k,92939526839989+c.lower,92939902477670+c.upper)) = pointBounds11656 := by
 decide +kernel
def cuts11657 : List PrefixCut := [⟨6,49244818,49244855⟩,
⟨53,480129379,480129753⟩,
⟨100,899424811,899425515⟩,
⟨128,1142690894,1142691788⟩]
theorem checked11657 : checkPrefixCuts (2^48) 1531838465 9 Manual.Count131072.C011657.packed 128 cuts11657 = true := by
 decide +kernel
def pointBounds11657 : List (Nat × Nat × Nat) := [(1531844608,92940706193693,92941081832294),(1531892736,92941137078254,92941512717192),(1531940864,92941556373686,92941932012954)]
theorem point_links_checked11657 : (cuts11657.take 3).map (fun c => (1531838465-1+2*2^9*c.k,92940656948875+c.lower,92941032587439+c.upper)) = pointBounds11657 := by
 decide +kernel
def cuts11658 : List PrefixCut := [⟨19,169217912,169218042⟩,
⟨66,585179864,585180319⟩,
⟨113,1006456802,1006457585⟩,
⟨128,1143327582,1143328474⟩]
theorem checked11658 : checkPrefixCuts (2^48) 1531969537 9 Manual.Count131072.C011658.packed 128 cuts11658 = true := by
 decide +kernel
def pointBounds11658 : List (Nat × Nat × Nat) := [(1531988992,92941968857681,92942344497269),(1532037120,92942384819633,92942760459546),(1532085248,92942806096571,92943181736812)]
theorem point_links_checked11658 : (cuts11658.take 3).map (fun c => (1531969537-1+2*2^9*c.k,92941799639769+c.lower,92942175279227+c.upper)) = pointBounds11658 := by
 decide +kernel
def cuts11659 : List PrefixCut := [⟨32,291741488,291741715⟩,
⟨79,709317595,709318150⟩,
⟨126,1125410901,1125411785⟩,
⟨128,1140107114,1140108011⟩]
theorem checked11659 : checkPrefixCuts (2^48) 1532100609 9 Manual.Count131072.C011659.packed 128 cuts11659 = true := by
 decide +kernel
def pointBounds11659 : List (Nat × Nat × Nat) := [(1532133376,92943234708839,92943610349416),(1532181504,92943652284946,92944027925851),(1532229632,92944068378252,92944444019486)]
theorem point_links_checked11659 : (cuts11659.take 3).map (fun c => (1532100609-1+2*2^9*c.k,92942942967351+c.lower,92943318607701+c.upper)) = pointBounds11659 := by
 decide +kernel
def cuts11660 : List PrefixCut := [⟨45,403588413,403588724⟩,
⟨92,823880546,823881182⟩,
⟨128,1140193109,1140193993⟩]
theorem checked11660 : checkPrefixCuts (2^48) 1532231681 9 Manual.Count131072.C011660.packed 128 cuts11660 = true := by
 decide +kernel
def pointBounds11660 : List (Nat × Nat × Nat) := [(1532277760,92944486662878,92944862304436),(1532325888,92944906955011,92945282596894)]
theorem point_links_checked11660 : (cuts11660.take 2).map (fun c => (1532231681-1+2*2^9*c.k,92944083074465+c.lower,92944458715712+c.upper)) = pointBounds11660 := by
 decide +kernel
def cuts11661 : List PrefixCut := [⟨11,97353664,97353739⟩,
⟨58,503108544,503108939⟩,
⟨105,916565090,916565813⟩,
⟨128,1120992655,1120993537⟩]
theorem checked11661 : checkPrefixCuts (2^48) 1532362753 9 Manual.Count131072.C011661.packed 128 cuts11661 = true := by
 decide +kernel
def pointBounds11661 : List (Nat × Nat × Nat) := [(1532374016,92945320621238,92945696263444),(1532422144,92945726376118,92946102018644),(1532470272,92946139832664,92946515475518)]
theorem point_links_checked11661 : (cuts11661.take 3).map (fun c => (1532362753-1+2*2^9*c.k,92945223267574+c.lower,92945598909705+c.upper)) = pointBounds11661 := by
 decide +kernel
def cuts11662 : List PrefixCut := [⟨24,212322151,212322319⟩,
⟨71,631629987,631630482⟩,
⟨118,1051108308,1051109126⟩,
⟨128,1142385367,1142386258⟩]
theorem checked11662 : checkPrefixCuts (2^48) 1532493825 9 Manual.Count131072.C011662.packed 128 cuts11662 = true := by
 decide +kernel
def pointBounds11662 : List (Nat × Nat × Nat) := [(1532518400,92946556582380,92946932225561),(1532566528,92946975890216,92947351533724),(1532614656,92947395368537,92947771012368)]
theorem point_links_checked11662 : (cuts11662.take 3).map (fun c => (1532493825-1+2*2^9*c.k,92946344260229+c.lower,92946719903242+c.upper)) = pointBounds11662 := by
 decide +kernel
def cuts11663 : List PrefixCut := [⟨37,330208295,330208555⟩,
⟨84,749109363,749109952⟩,
⟨128,1138063962,1138064858⟩]
theorem checked11663 : checkPrefixCuts (2^48) 1532624897 9 Manual.Count131072.C011663.packed 128 cuts11663 = true := by
 decide +kernel
def pointBounds11663 : List (Nat × Nat × Nat) := [(1532662784,92947816853891,92948192498055),(1532710912,92948235754959,92948611399452)]
theorem point_links_checked11663 : (cuts11663.take 2).map (fun c => (1532624897-1+2*2^9*c.k,92947486645596+c.lower,92947862289500+c.upper)) = pointBounds11663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000051
