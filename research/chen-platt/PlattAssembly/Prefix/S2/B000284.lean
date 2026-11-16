import PlattAssemblyKernel
import PlattCertificates.Count131072.C019088
import PlattCertificates.Count131072.C019089
import PlattCertificates.Count131072.C019090
import PlattCertificates.Count131072.C019091
import PlattCertificates.Count131072.C019092
import PlattCertificates.Count131072.C019093
import PlattCertificates.Count131072.C019094
import PlattCertificates.Count131072.C019095
import PlattCertificates.Count131072.C019096
import PlattCertificates.Count131072.C019097
import PlattCertificates.Count131072.C019098
import PlattCertificates.Count131072.C019099
import PlattCertificates.Count131072.C019100
import PlattCertificates.Count131072.C019101
import PlattCertificates.Count131072.C019102
import PlattCertificates.Count131072.C019103
import PlattCertificates.Count131072.C019104
import PlattCertificates.Count131072.C019105
import PlattCertificates.Count131072.C019106
import PlattCertificates.Count131072.C019107
import PlattCertificates.Count131072.C019108
import PlattCertificates.Count131072.C019109
import PlattCertificates.Count131072.C019110
import PlattCertificates.Count131072.C019111
import PlattCertificates.Count131072.C019112
import PlattCertificates.Count131072.C019113
import PlattCertificates.Count131072.C019114
import PlattCertificates.Count131072.C019115
import PlattCertificates.Count131072.C019116
import PlattCertificates.Count131072.C019117
import PlattCertificates.Count131072.C019118
import PlattCertificates.Count131072.C019119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000284
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19088 : List PrefixCut := [⟨26,138611771,138611855⟩,
⟨103,545901651,545901978⟩,
⟨128,678891498,678891906⟩]
theorem checked19088 : checkPrefixCuts (2^48) 2505834497 9 Manual.Count131072.C019088.packed 128 cuts19088 = true := by
 decide +kernel
def pointBounds19088 : List (Nat × Nat × Nat) := [(2505861120,99415407449045,99415787460087),(2505939968,99415814738925,99416194750210)]
theorem point_links_checked19088 : (cuts19088.take 2).map (fun c => (2505834497-1+2*2^9*c.k,99415268837274+c.lower,99415648848232+c.upper)) = pointBounds19088 := by
 decide +kernel
def cuts19089 : List PrefixCut := [⟨52,278667767,278667931⟩,
⟨128,682899502,682899904⟩]
theorem checked19089 : checkPrefixCuts (2^48) 2505965569 9 Manual.Count131072.C019089.packed 128 cuts19089 = true := by
 decide +kernel
def pointBounds19089 : List (Nat × Nat × Nat) := [(2506018816,99416226396539,99416606408069)]
theorem point_links_checked19089 : (cuts19089.take 1).map (fun c => (2505965569-1+2*2^9*c.k,99415947728772+c.lower,99416327740138+c.upper)) = pointBounds19089 := by
 decide +kernel
def cuts19090 : List PrefixCut := [⟨1,5166538,5166541⟩,
⟨78,417809029,417809282⟩,
⟨128,680729855,680730265⟩]
theorem checked19090 : checkPrefixCuts (2^48) 2506096641 9 Manual.Count131072.C019090.packed 128 cuts19090 = true := by
 decide +kernel
def pointBounds19090 : List (Nat × Nat × Nat) := [(2506097664,99416635794812,99417015806583),(2506176512,99417048437303,99417428449324)]
theorem point_links_checked19090 : (cuts19090.take 2).map (fun c => (2506096641-1+2*2^9*c.k,99416630628274+c.lower,99417010640042+c.upper)) = pointBounds19090 := by
 decide +kernel
def cuts19091 : List PrefixCut := [⟨27,146339375,146339462⟩,
⟨104,547163673,547164006⟩,
⟨128,674292778,674293190⟩]
theorem checked19091 : checkPrefixCuts (2^48) 2506227713 9 Manual.Count131072.C019091.packed 128 cuts19091 = true := by
 decide +kernel
def pointBounds19091 : List (Nat × Nat × Nat) := [(2506255360,99417457697504,99417837709769),(2506334208,99417858521802,99418238534313)]
theorem point_links_checked19091 : (cuts19091.take 2).map (fun c => (2506227713-1+2*2^9*c.k,99417311358129+c.lower,99417691370307+c.upper)) = pointBounds19091 := by
 decide +kernel
def cuts19092 : List PrefixCut := [⟨53,282442370,282442533⟩,
⟨128,685487589,685487988⟩]
theorem checked19092 : checkPrefixCuts (2^48) 2506358785 9 Manual.Count131072.C019092.packed 128 cuts19092 = true := by
 decide +kernel
def pointBounds19092 : List (Nat × Nat × Nat) := [(2506413056,99418268093277,99418648106030)]
theorem point_links_checked19092 : (cuts19092.take 1).map (fun c => (2506358785-1+2*2^9*c.k,99417985650907+c.lower,99418365663497+c.upper)) = pointBounds19092 := by
 decide +kernel
def cuts19093 : List PrefixCut := [⟨2,11229839,11229846⟩,
⟨79,412914750,412914996⟩,
⟨128,671863998,671864400⟩]
theorem checked19093 : checkPrefixCuts (2^48) 2506489857 9 Manual.Count131072.C019093.packed 128 cuts19093 = true := by
 decide +kernel
def pointBounds19093 : List (Nat × Nat × Nat) := [(2506491904,99418682368335,99419062381331),(2506570752,99419084053246,99419464066481)]
theorem point_links_checked19093 : (cuts19093.take 2).map (fun c => (2506489857-1+2*2^9*c.k,99418671138496+c.lower,99419051151485+c.upper)) = pointBounds19093 := by
 decide +kernel
def cuts19094 : List PrefixCut := [⟨28,150022000,150022091⟩,
⟨105,563022895,563023235⟩,
⟨128,682945663,682946076⟩]
theorem checked19094 : checkPrefixCuts (2^48) 2506620929 9 Manual.Count131072.C019094.packed 128 cuts19094 = true := by
 decide +kernel
def pointBounds19094 : List (Nat × Nat × Nat) := [(2506649600,99419493024494,99419873037976),(2506728448,99419906025389,99420286039120)]
theorem point_links_checked19094 : (cuts19094.take 2).map (fun c => (2506620929-1+2*2^9*c.k,99419343002494+c.lower,99419723015885+c.upper)) = pointBounds19094 := by
 decide +kernel
def cuts19095 : List PrefixCut := [⟨54,285654194,285654366⟩,
⟨128,675611415,675611816⟩]
theorem checked19095 : checkPrefixCuts (2^48) 2506752001 9 Manual.Count131072.C019095.packed 128 cuts19095 = true := by
 decide +kernel
def pointBounds19095 : List (Nat × Nat × Nat) := [(2506807296,99420311602351,99420691616327)]
theorem point_links_checked19095 : (cuts19095.take 1).map (fun c => (2506752001-1+2*2^9*c.k,99420025948157+c.lower,99420405961961+c.upper)) = pointBounds19095 := by
 decide +kernel
def cuts19096 : List PrefixCut := [⟨3,16056148,16056158⟩,
⟨80,420821690,420821940⟩,
⟨128,677821589,677821992⟩]
theorem checked19096 : checkPrefixCuts (2^48) 2506883073 9 Manual.Count131072.C019096.packed 128 cuts19096 = true := by
 decide +kernel
def pointBounds19096 : List (Nat × Nat × Nat) := [(2506886144,99420717615720,99421097629935),(2506964992,99421122381262,99421502395717)]
theorem point_links_checked19096 : (cuts19096.take 2).map (fun c => (2506883073-1+2*2^9*c.k,99420701559572+c.lower,99421081573777+c.upper)) = pointBounds19096 := by
 decide +kernel
def cuts19097 : List PrefixCut := [⟨29,155050796,155050890⟩,
⟨106,562597659,562598000⟩,
⟨128,685645121,685645538⟩]
theorem checked19097 : checkPrefixCuts (2^48) 2507014145 9 Manual.Count131072.C019097.packed 128 cuts19097 = true := by
 decide +kernel
def pointBounds19097 : List (Nat × Nat × Nat) := [(2507043840,99421534431957,99421914446659),(2507122688,99421941978820,99422321993769)]
theorem point_links_checked19097 : (cuts19097.take 2).map (fun c => (2507014145-1+2*2^9*c.k,99421379381161+c.lower,99421759395769+c.upper)) = pointBounds19097 := by
 decide +kernel
def cuts19098 : List PrefixCut := [⟨55,293355789,293355967⟩,
⟨128,690099884,690100297⟩]
theorem checked19098 : checkPrefixCuts (2^48) 2507145217 9 Manual.Count131072.C019098.packed 128 cuts19098 = true := by
 decide +kernel
def pointBounds19098 : List (Nat × Nat × Nat) := [(2507201536,99422358382071,99422738397274)]
theorem point_links_checked19098 : (cuts19098.take 1).map (fun c => (2507145217-1+2*2^9*c.k,99422065026282+c.lower,99422445041307+c.upper)) = pointBounds19098 := by
 decide +kernel
def cuts19099 : List PrefixCut := [⟨4,20993202,20993215⟩,
⟨81,423337569,423337823⟩,
⟨128,672326747,672327150⟩]
theorem checked19099 : checkPrefixCuts (2^48) 2507276289 9 Manual.Count131072.C019099.packed 128 cuts19099 = true := by
 decide +kernel
def pointBounds19099 : List (Nat × Nat × Nat) := [(2507280384,99422776119368,99423156134819),(2507359232,99423178463735,99423558479427)]
theorem point_links_checked19099 : (cuts19099.take 2).map (fun c => (2507276289-1+2*2^9*c.k,99422755126166+c.lower,99423135141604+c.upper)) = pointBounds19099 := by
 decide +kernel
def cuts19100 : List PrefixCut := [⟨30,160190248,160190341⟩,
⟨107,572948907,572949251⟩,
⟨128,684751869,684752275⟩]
theorem checked19100 : checkPrefixCuts (2^48) 2507407361 9 Manual.Count131072.C019100.packed 128 cuts19100 = true := by
 decide +kernel
def pointBounds19100 : List (Nat × Nat × Nat) := [(2507438080,99423587643161,99423967659095),(2507516928,99424000401820,99424380418005)]
theorem point_links_checked19100 : (cuts19100.take 2).map (fun c => (2507407361-1+2*2^9*c.k,99423427452913+c.lower,99423807468754+c.upper)) = pointBounds19100 := by
 decide +kernel
def cuts19101 : List PrefixCut := [⟨56,301279560,301279744⟩,
⟨128,696277725,696278137⟩]
theorem checked19101 : checkPrefixCuts (2^48) 2507538433 9 Manual.Count131072.C019101.packed 128 cuts19101 = true := by
 decide +kernel
def pointBounds19101 : List (Nat × Nat × Nat) := [(2507595776,99424413484342,99424793500773)]
theorem point_links_checked19101 : (cuts19101.take 1).map (fun c => (2507538433-1+2*2^9*c.k,99424112204782+c.lower,99424492221029+c.upper)) = pointBounds19101 := by
 decide +kernel
def cuts19102 : List PrefixCut := [⟨5,24245027,24245041⟩,
⟨82,429893459,429893710⟩,
⟨128,675476293,675476689⟩]
theorem checked19102 : checkPrefixCuts (2^48) 2507669505 9 Manual.Count131072.C019102.packed 128 cuts19102 = true := by
 decide +kernel
def pointBounds19102 : List (Nat × Nat × Nat) := [(2507674624,99424832727534,99425212744207),(2507753472,99425238375966,99425618392876)]
theorem point_links_checked19102 : (cuts19102.take 2).map (fun c => (2507669505-1+2*2^9*c.k,99424808482507+c.lower,99425188499166+c.upper)) = pointBounds19102 := by
 decide +kernel
def cuts19103 : List PrefixCut := [⟨31,169705428,169705525⟩,
⟨108,571624552,571624894⟩,
⟨128,678471647,678472053⟩]
theorem checked19103 : checkPrefixCuts (2^48) 2507800577 9 Manual.Count131072.C019103.packed 128 cuts19103 = true := by
 decide +kernel
def pointBounds19103 : List (Nat × Nat × Nat) := [(2507832320,99425653664228,99426033681380),(2507911168,99426055583352,99426435600749)]
theorem point_links_checked19103 : (cuts19103.take 2).map (fun c => (2507800577-1+2*2^9*c.k,99425483958800+c.lower,99425863975855+c.upper)) = pointBounds19103 := by
 decide +kernel
def cuts19104 : List PrefixCut := [⟨57,304262501,304262677⟩,
⟨128,677762734,677763128⟩]
theorem checked19104 : checkPrefixCuts (2^48) 2507931649 9 Manual.Count131072.C019104.packed 128 cuts19104 = true := by
 decide +kernel
def pointBounds19104 : List (Nat × Nat × Nat) := [(2507990016,99426466692948,99426846710585)]
theorem point_links_checked19104 : (cuts19104.take 1).map (fun c => (2507931649-1+2*2^9*c.k,99426162430447+c.lower,99426542447908+c.upper)) = pointBounds19104 := by
 decide +kernel
def cuts19105 : List PrefixCut := [⟨6,31311577,31311596⟩,
⟨83,441273054,441273313⟩,
⟨128,678737329,678737729⟩]
theorem checked19105 : checkPrefixCuts (2^48) 2508062721 9 Manual.Count131072.C019105.packed 128 cuts19105 = true := by
 decide +kernel
def pointBounds19105 : List (Nat × Nat × Nat) := [(2508068864,99426871504758,99427251522632),(2508147712,99427281466235,99427661484349)]
theorem point_links_checked19105 : (cuts19105.take 2).map (fun c => (2508062721-1+2*2^9*c.k,99426840193181+c.lower,99427220211036+c.upper)) = pointBounds19105 := by
 decide +kernel
def cuts19106 : List PrefixCut := [⟨32,176075400,176075506⟩,
⟨109,586123302,586123653⟩,
⟨128,687342786,687343197⟩]
theorem checked19106 : checkPrefixCuts (2^48) 2508193793 9 Manual.Count131072.C019106.packed 128 cuts19106 = true := by
 decide +kernel
def pointBounds19106 : List (Nat × Nat × Nat) := [(2508226560,99427695005910,99428075024271),(2508305408,99428105053812,99428485072418)]
theorem point_links_checked19106 : (cuts19106.take 2).map (fun c => (2508193793-1+2*2^9*c.k,99427518930510+c.lower,99427898948765+c.upper)) = pointBounds19106 := by
 decide +kernel
def cuts19107 : List PrefixCut := [⟨58,309039944,309040123⟩,
⟨128,684052459,684052862⟩]
theorem checked19107 : checkPrefixCuts (2^48) 2508324865 9 Manual.Count131072.C019107.packed 128 cuts19107 = true := by
 decide +kernel
def pointBounds19107 : List (Nat × Nat × Nat) := [(2508384256,99428515313240,99428895332085)]
theorem point_links_checked19107 : (cuts19107.take 1).map (fun c => (2508324865-1+2*2^9*c.k,99428206273296+c.lower,99428586291962+c.upper)) = pointBounds19107 := by
 decide +kernel
def cuts19108 : List PrefixCut := [⟨7,35795073,35795094⟩,
⟨84,441877038,441877301⟩,
⟨128,681435919,681436327⟩]
theorem checked19108 : checkPrefixCuts (2^48) 2508455937 9 Manual.Count131072.C019108.packed 128 cuts19108 = true := by
 decide +kernel
def pointBounds19108 : List (Nat × Nat × Nat) := [(2508463104,99428926120828,99429306139918),(2508541952,99429332202793,99429712222125)]
theorem point_links_checked19108 : (cuts19108.take 2).map (fun c => (2508455937-1+2*2^9*c.k,99428890325755+c.lower,99429270344824+c.upper)) = pointBounds19108 := by
 decide +kernel
def cuts19109 : List PrefixCut := [⟨33,167632477,167632581⟩,
⟨110,581542881,581543231⟩,
⟨128,678482916,678483321⟩]
theorem checked19109 : checkPrefixCuts (2^48) 2508587009 9 Manual.Count131072.C019109.packed 128 cuts19109 = true := by
 decide +kernel
def pointBounds19109 : List (Nat × Nat × Nat) := [(2508620800,99429739394151,99430119413732),(2508699648,99430153304555,99430533324382)]
theorem point_links_checked19109 : (cuts19109.take 2).map (fun c => (2508587009-1+2*2^9*c.k,99429571761674+c.lower,99429951781151+c.upper)) = pointBounds19109 := by
 decide +kernel
def cuts19110 : List PrefixCut := [⟨59,303493805,303493990⟩,
⟨128,668237867,668238272⟩]
theorem checked19110 : checkPrefixCuts (2^48) 2508718081 9 Manual.Count131072.C019110.packed 128 cuts19110 = true := by
 decide +kernel
def pointBounds19110 : List (Nat × Nat × Nat) := [(2508778496,99430553738395,99430933758462)]
theorem point_links_checked19110 : (cuts19110.take 1).map (fun c => (2508718081-1+2*2^9*c.k,99430250244590+c.lower,99430630264472+c.upper)) = pointBounds19110 := by
 decide +kernel
def cuts19111 : List PrefixCut := [⟨8,43755133,43755160⟩,
⟨85,458524155,458524430⟩,
⟨128,689182583,689182996⟩]
theorem checked19111 : checkPrefixCuts (2^48) 2508849153 9 Manual.Count131072.C019111.packed 128 cuts19111 = true := by
 decide +kernel
def pointBounds19111 : List (Nat × Nat × Nat) := [(2508857344,99430962237590,99431342257904),(2508936192,99431377006612,99431757027174)]
theorem point_links_checked19111 : (cuts19111.take 2).map (fun c => (2508849153-1+2*2^9*c.k,99430918482457+c.lower,99431298502744+c.upper)) = pointBounds19111 := by
 decide +kernel
def cuts19112 : List PrefixCut := [⟨34,173103286,173103392⟩,
⟨111,581115270,581115620⟩,
⟨128,670075202,670075603⟩]
theorem checked19112 : checkPrefixCuts (2^48) 2508980225 9 Manual.Count131072.C019112.packed 128 cuts19112 = true := by
 decide +kernel
def pointBounds19112 : List (Nat × Nat × Nat) := [(2509015040,99431780768326,99432160789132),(2509093888,99432188780310,99432568801360)]
theorem point_links_checked19112 : (cuts19112.take 2).map (fun c => (2508980225-1+2*2^9*c.k,99431607665040+c.lower,99431987685740+c.upper)) = pointBounds19112 := by
 decide +kernel
def cuts19113 : List PrefixCut := [⟨60,328125737,328125930⟩,
⟨128,688662034,688662443⟩]
theorem checked19113 : checkPrefixCuts (2^48) 2509111297 9 Manual.Count131072.C019113.packed 128 cuts19113 = true := by
 decide +kernel
def pointBounds19113 : List (Nat × Nat × Nat) := [(2509172736,99432605865979,99432985887273)]
theorem point_links_checked19113 : (cuts19113.take 1).map (fun c => (2509111297-1+2*2^9*c.k,99432277740242+c.lower,99432657761343+c.upper)) = pointBounds19113 := by
 decide +kernel
def cuts19114 : List PrefixCut := [⟨9,47898747,47898775⟩,
⟨86,456096634,456096905⟩,
⟨128,677408743,677409145⟩]
theorem checked19114 : checkPrefixCuts (2^48) 2509242369 9 Manual.Count131072.C019114.packed 128 cuts19114 = true := by
 decide +kernel
def pointBounds19114 : List (Nat × Nat × Nat) := [(2509251584,99433014301023,99433394322561),(2509330432,99433422498910,99433802520691)]
theorem point_links_checked19114 : (cuts19114.take 2).map (fun c => (2509242369-1+2*2^9*c.k,99432966402276+c.lower,99433346423786+c.upper)) = pointBounds19114 := by
 decide +kernel
def cuts19115 : List PrefixCut := [⟨35,180815770,180815879⟩,
⟨112,591231280,591231633⟩,
⟨128,676812332,676812737⟩]
theorem checked19115 : checkPrefixCuts (2^48) 2509373441 9 Manual.Count131072.C019115.packed 128 cuts19115 = true := by
 decide +kernel
def pointBounds19115 : List (Nat × Nat × Nat) := [(2509409280,99433824626789,99434204648810),(2509488128,99434235042299,99434615064564)]
theorem point_links_checked19115 : (cuts19115.take 2).map (fun c => (2509373441-1+2*2^9*c.k,99433643811019+c.lower,99434023832931+c.upper)) = pointBounds19115 := by
 decide +kernel
def cuts19116 : List PrefixCut := [⟨61,327625599,327625795⟩,
⟨128,678010972,678011387⟩]
theorem checked19116 : checkPrefixCuts (2^48) 2509504513 9 Manual.Count131072.C019116.packed 128 cuts19116 = true := by
 decide +kernel
def pointBounds19116 : List (Nat × Nat × Nat) := [(2509566976,99434648248950,99435028271463)]
theorem point_links_checked19116 : (cuts19116.take 1).map (fun c => (2509504513-1+2*2^9*c.k,99434320623351+c.lower,99434700645668+c.upper)) = pointBounds19116 := by
 decide +kernel
def cuts19117 : List PrefixCut := [⟨10,53050469,53050501⟩,
⟨87,461632764,461633041⟩,
⟨128,679433390,679433801⟩]
theorem checked19117 : checkPrefixCuts (2^48) 2509635585 9 Manual.Count131072.C019117.packed 128 cuts19117 = true := by
 decide +kernel
def pointBounds19117 : List (Nat × Nat × Nat) := [(2509645824,99435051684792,99435431707556),(2509724672,99435460267087,99435840290096)]
theorem point_links_checked19117 : (cuts19117.take 2).map (fun c => (2509635585-1+2*2^9*c.k,99434998634323+c.lower,99435378657055+c.upper)) = pointBounds19117 := by
 decide +kernel
def cuts19118 : List PrefixCut := [⟨36,186394923,186395030⟩,
⟨113,598988949,598989297⟩,
⟨128,678052093,678052487⟩]
theorem checked19118 : checkPrefixCuts (2^48) 2509766657 9 Manual.Count131072.C019118.packed 128 cuts19118 = true := by
 decide +kernel
def pointBounds19118 : List (Nat × Nat × Nat) := [(2509803520,99435864462636,99436244485886),(2509882368,99436277056662,99436657080153)]
theorem point_links_checked19118 : (cuts19118.take 2).map (fun c => (2509766657-1+2*2^9*c.k,99435678067713+c.lower,99436058090856+c.upper)) = pointBounds19118 := by
 decide +kernel
def cuts19119 : List PrefixCut := [⟨62,326901363,326901558⟩,
⟨128,676446795,676447202⟩]
theorem checked19119 : checkPrefixCuts (2^48) 2509897729 9 Manual.Count131072.C019119.packed 128 cuts19119 = true := by
 decide +kernel
def pointBounds19119 : List (Nat × Nat × Nat) := [(2509961216,99436683021169,99437063044901)]
theorem point_links_checked19119 : (cuts19119.take 1).map (fun c => (2509897729-1+2*2^9*c.k,99436356119806+c.lower,99436736143343+c.upper)) = pointBounds19119 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000284
