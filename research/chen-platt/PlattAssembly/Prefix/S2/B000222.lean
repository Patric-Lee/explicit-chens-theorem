import PlattAssemblyKernel
import PlattCertificates.Count131072.C017104
import PlattCertificates.Count131072.C017105
import PlattCertificates.Count131072.C017106
import PlattCertificates.Count131072.C017107
import PlattCertificates.Count131072.C017108
import PlattCertificates.Count131072.C017109
import PlattCertificates.Count131072.C017110
import PlattCertificates.Count131072.C017111
import PlattCertificates.Count131072.C017112
import PlattCertificates.Count131072.C017113
import PlattCertificates.Count131072.C017114
import PlattCertificates.Count131072.C017115
import PlattCertificates.Count131072.C017116
import PlattCertificates.Count131072.C017117
import PlattCertificates.Count131072.C017118
import PlattCertificates.Count131072.C017119
import PlattCertificates.Count131072.C017120
import PlattCertificates.Count131072.C017121
import PlattCertificates.Count131072.C017122
import PlattCertificates.Count131072.C017123
import PlattCertificates.Count131072.C017124
import PlattCertificates.Count131072.C017125
import PlattCertificates.Count131072.C017126
import PlattCertificates.Count131072.C017127
import PlattCertificates.Count131072.C017128
import PlattCertificates.Count131072.C017129
import PlattCertificates.Count131072.C017130
import PlattCertificates.Count131072.C017131
import PlattCertificates.Count131072.C017132
import PlattCertificates.Count131072.C017133
import PlattCertificates.Count131072.C017134
import PlattCertificates.Count131072.C017135
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000222
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17104 : List PrefixCut := [⟨40,236754879,236755026⟩,
⟨109,652976893,652977297⟩,
⟨128,772163660,772164139⟩]
theorem checked17104 : checkPrefixCuts (2^48) 2245787649 9 Manual.Count131072.C017104.packed 128 cuts17104 = true := by
 decide +kernel
def pointBounds17104 : List (Nat × Nat × Nat) := [(2245828608,97986883221626,97987262361563),(2245899264,97987299443640,97987678583834)]
theorem point_links_checked17104 : (cuts17104.take 2).map (fun c => (2245787649-1+2*2^9*c.k,97986646466747+c.lower,97987025606537+c.upper)) = pointBounds17104 := by
 decide +kernel
def cuts17105 : List PrefixCut := [⟨50,305168445,305168631⟩,
⟨119,713970258,713970697⟩,
⟨128,770113719,770114192⟩]
theorem checked17105 : checkPrefixCuts (2^48) 2245918721 9 Manual.Count131072.C017105.packed 128 cuts17105 = true := by
 decide +kernel
def pointBounds17105 : List (Nat × Nat × Nat) := [(2245969920,97987723798852,97988102939307),(2246040576,97988132600665,97988511741373)]
theorem point_links_checked17105 : (cuts17105.take 2).map (fun c => (2245918721-1+2*2^9*c.k,97987418630407+c.lower,97987797770676+c.upper)) = pointBounds17105 := by
 decide +kernel
def cuts17106 : List PrefixCut := [⟨60,354650627,354650851⟩,
⟨128,762925554,762926030⟩]
theorem checked17106 : checkPrefixCuts (2^48) 2246049793 9 Manual.Count131072.C017106.packed 128 cuts17106 = true := by
 decide +kernel
def pointBounds17106 : List (Nat × Nat × Nat) := [(2246111232,97988543394753,97988922535719)]
theorem point_links_checked17106 : (cuts17106.take 1).map (fun c => (2246049793-1+2*2^9*c.k,97988188744126+c.lower,97988567884868+c.upper)) = pointBounds17106 := by
 decide +kernel
def cuts17107 : List PrefixCut := [⟨1,6766882,6766886⟩,
⟨70,418662988,418663251⟩,
⟨128,763382523,763383001⟩]
theorem checked17107 : checkPrefixCuts (2^48) 2246180865 9 Manual.Count131072.C017107.packed 128 cuts17107 = true := by
 decide +kernel
def pointBounds17107 : List (Nat × Nat × Nat) := [(2246181888,97988958436562,97989337577784),(2246252544,97989370332668,97989749474149)]
theorem point_links_checked17107 : (cuts17107.take 2).map (fun c => (2246180865-1+2*2^9*c.k,97988951669680+c.lower,97989330810898+c.upper)) = pointBounds17107 := by
 decide +kernel
def cuts17108 : List PrefixCut := [⟨11,64030870,64030911⟩,
⟨80,467129783,467130075⟩,
⟨128,766595350,766595826⟩]
theorem checked17108 : checkPrefixCuts (2^48) 2246311937 9 Manual.Count131072.C017108.packed 128 cuts17108 = true := by
 decide +kernel
def pointBounds17108 : List (Nat × Nat × Nat) := [(2246323200,97989779083073,97990158224810),(2246393856,97990182181986,97990561323974)]
theorem point_links_checked17108 : (cuts17108.take 2).map (fun c => (2246311937-1+2*2^9*c.k,97989715052203+c.lower,97990094193899+c.upper)) = pointBounds17108 := by
 decide +kernel
def cuts17109 : List PrefixCut := [⟨21,127176893,127176973⟩,
⟨90,542905200,542905543⟩,
⟨128,773567401,773567888⟩]
theorem checked17109 : checkPrefixCuts (2^48) 2246443009 9 Manual.Count131072.C017109.packed 128 cuts17109 = true := by
 decide +kernel
def pointBounds17109 : List (Nat × Nat × Nat) := [(2246464512,97990608824446,97990987966698),(2246535168,97991024552753,97991403695268)]
theorem point_links_checked17109 : (cuts17109.take 2).map (fun c => (2246443009-1+2*2^9*c.k,97990481647553+c.lower,97990860789725+c.upper)) = pointBounds17109 := by
 decide +kernel
def cuts17110 : List PrefixCut := [⟨31,184426628,184426741⟩,
⟨100,588978361,588978727⟩,
⟨128,759114344,759114816⟩]
theorem checked17110 : checkPrefixCuts (2^48) 2246574081 9 Manual.Count131072.C017110.packed 128 cuts17110 = true := by
 decide +kernel
def pointBounds17110 : List (Nat × Nat × Nat) := [(2246605824,97991439641582,97991818784354),(2246676480,97991844193315,97992223336340)]
theorem point_links_checked17110 : (cuts17110.take 2).map (fun c => (2246574081-1+2*2^9*c.k,97991255214954+c.lower,97991634357613+c.upper)) = pointBounds17110 := by
 decide +kernel
def cuts17111 : List PrefixCut := [⟨41,245302610,245302758⟩,
⟨110,651582809,651583208⟩,
⟨128,759445985,759446454⟩]
theorem checked17111 : checkPrefixCuts (2^48) 2246705153 9 Manual.Count131072.C017111.packed 128 cuts17111 = true := by
 decide +kernel
def pointBounds17111 : List (Nat × Nat × Nat) := [(2246747136,97992259631908,97992638775187),(2246817792,97992665912107,97993045055637)]
theorem point_links_checked17111 : (cuts17111.take 2).map (fun c => (2246705153-1+2*2^9*c.k,97992014329298+c.lower,97992393472429+c.upper)) = pointBounds17111 := by
 decide +kernel
def cuts17112 : List PrefixCut := [⟨51,303415246,303415435⟩,
⟨120,718939917,718940361⟩,
⟨128,771803447,771803924⟩]
theorem checked17112 : checkPrefixCuts (2^48) 2246836225 9 Manual.Count131072.C017112.packed 128 cuts17112 = true := by
 decide +kernel
def pointBounds17112 : List (Nat × Nat × Nat) := [(2246888448,97993077190529,97993456334318),(2246959104,97993492715200,97993871859244)]
theorem point_links_checked17112 : (cuts17112.take 2).map (fun c => (2246836225-1+2*2^9*c.k,97992773775283+c.lower,97993152918883+c.upper)) = pointBounds17112 := by
 decide +kernel
def cuts17113 : List PrefixCut := [⟨61,356259468,356259690⟩,
⟨128,753469748,753470217⟩]
theorem checked17113 : checkPrefixCuts (2^48) 2246967297 9 Manual.Count131072.C017113.packed 128 cuts17113 = true := by
 decide +kernel
def pointBounds17113 : List (Nat × Nat × Nat) := [(2247029760,97993901838198,97994280982497)]
theorem point_links_checked17113 : (cuts17113.take 1).map (fun c => (2246967297-1+2*2^9*c.k,97993545578730+c.lower,97993924722807+c.upper)) = pointBounds17113 := by
 decide +kernel
def cuts17114 : List PrefixCut := [⟨2,11023006,11023013⟩,
⟨71,416237255,416237520⟩,
⟨128,762068575,762069060⟩]
theorem checked17114 : checkPrefixCuts (2^48) 2247098369 9 Manual.Count131072.C017114.packed 128 cuts17114 = true := by
 decide +kernel
def pointBounds17114 : List (Nat × Nat × Nat) := [(2247100416,97994310071484,97994689216037),(2247171072,97994715285733,97995094430544)]
theorem point_links_checked17114 : (cuts17114.take 2).map (fun c => (2247098369-1+2*2^9*c.k,97994299048478+c.lower,97994678193024+c.upper)) = pointBounds17114 := by
 decide +kernel
def cuts17115 : List PrefixCut := [⟨12,71895708,71895752⟩,
⟨81,490361035,490361338⟩,
⟨128,768036306,768036781⟩]
theorem checked17115 : checkPrefixCuts (2^48) 2247229441 9 Manual.Count131072.C017115.packed 128 cuts17115 = true := by
 decide +kernel
def pointBounds17115 : List (Nat × Nat × Nat) := [(2247241728,97995133012761,97995512157836),(2247312384,97995551478088,97995930623422)]
theorem point_links_checked17115 : (cuts17115.take 2).map (fun c => (2247229441-1+2*2^9*c.k,97995061117053+c.lower,97995440262084+c.upper)) = pointBounds17115 := by
 decide +kernel
def cuts17116 : List PrefixCut := [⟨22,131007574,131007653⟩,
⟨91,537673701,537674038⟩,
⟨128,766363098,766363572⟩]
theorem checked17116 : checkPrefixCuts (2^48) 2247360513 9 Manual.Count131072.C017116.packed 128 cuts17116 = true := by
 decide +kernel
def pointBounds17116 : List (Nat × Nat × Nat) := [(2247383040,97995960160933,97996339306518),(2247453696,97996366827060,97996745972903)]
theorem point_links_checked17116 : (cuts17116.take 2).map (fun c => (2247360513-1+2*2^9*c.k,97995829153359+c.lower,97996208298865+c.upper)) = pointBounds17116 := by
 decide +kernel
def cuts17117 : List PrefixCut := [⟨32,191489903,191490023⟩,
⟨101,598130501,598130876⟩,
⟨128,758178318,758178796⟩]
theorem checked17117 : checkPrefixCuts (2^48) 2247491585 9 Manual.Count131072.C017117.packed 128 cuts17117 = true := by
 decide +kernel
def pointBounds17117 : List (Nat × Nat × Nat) := [(2247524352,97996787006360,97997166152460),(2247595008,97997193646958,97997572793313)]
theorem point_links_checked17117 : (cuts17117.take 2).map (fun c => (2247491585-1+2*2^9*c.k,97996595516457+c.lower,97996974662437+c.upper)) = pointBounds17117 := by
 decide +kernel
def cuts17118 : List PrefixCut := [⟨42,254594763,254594919⟩,
⟨111,658579995,658580407⟩,
⟨128,763518925,763519400⟩]
theorem checked17118 : checkPrefixCuts (2^48) 2247622657 9 Manual.Count131072.C017118.packed 128 cuts17118 = true := by
 decide +kernel
def pointBounds17118 : List (Nat × Nat × Nat) := [(2247665664,97997608289538,97997987436152),(2247736320,97998012274770,97998391421640)]
theorem point_links_checked17118 : (cuts17118.take 2).map (fun c => (2247622657-1+2*2^9*c.k,97997353694775+c.lower,97997732841233+c.upper)) = pointBounds17118 := by
 decide +kernel
def cuts17119 : List PrefixCut := [⟨52,312808273,312808466⟩,
⟨121,722903862,722904309⟩,
⟨128,763850104,763850577⟩]
theorem checked17119 : checkPrefixCuts (2^48) 2247753729 9 Manual.Count131072.C017119.packed 128 cuts17119 = true := by
 decide +kernel
def pointBounds17119 : List (Nat × Nat × Nat) := [(2247806976,97998430021973,97998809169099),(2247877632,97998840117562,97999219264942)]
theorem point_links_checked17119 : (cuts17119.take 2).map (fun c => (2247753729-1+2*2^9*c.k,97998117213700+c.lower,97998496360633+c.upper)) = pointBounds17119 := by
 decide +kernel
def cuts17120 : List PrefixCut := [⟨62,370388627,370388859⟩,
⟨128,763930720,763931195⟩]
theorem checked17120 : checkPrefixCuts (2^48) 2247884801 9 Manual.Count131072.C017120.packed 128 cuts17120 = true := by
 decide +kernel
def pointBounds17120 : List (Nat × Nat × Nat) := [(2247948288,97999251452431,97999630600069)]
theorem point_links_checked17120 : (cuts17120.take 1).map (fun c => (2247884801-1+2*2^9*c.k,97998881063804+c.lower,97999260211210+c.upper)) = pointBounds17120 := by
 decide +kernel
def cuts17121 : List PrefixCut := [⟨3,19157172,19157184⟩,
⟨72,430215796,430216064⟩,
⟨128,764261856,764262326⟩]
theorem checked17121 : checkPrefixCuts (2^48) 2248015873 9 Manual.Count131072.C017121.packed 128 cuts17121 = true := by
 decide +kernel
def pointBounds17121 : List (Nat × Nat × Nat) := [(2248018944,97999664151696,98000043299589),(2248089600,98000075210320,98000454358469)]
theorem point_links_checked17121 : (cuts17121.take 2).map (fun c => (2248015873-1+2*2^9*c.k,97999644994524+c.lower,98000024142405+c.upper)) = pointBounds17121 := by
 decide +kernel
def cuts17122 : List PrefixCut := [⟨13,76123244,76123291⟩,
⟨82,485152780,485153085⟩,
⟨128,754576892,754577370⟩]
theorem checked17122 : checkPrefixCuts (2^48) 2248146945 9 Manual.Count131072.C017122.packed 128 cuts17122 = true := by
 decide +kernel
def pointBounds17122 : List (Nat × Nat × Nat) := [(2248160256,98000485379624,98000864528022),(2248230912,98000894409160,98001273557816)]
theorem point_links_checked17122 : (cuts17122.take 2).map (fun c => (2248146945-1+2*2^9*c.k,98000409256380+c.lower,98000788404731+c.upper)) = pointBounds17122 := by
 decide +kernel
def cuts17123 : List PrefixCut := [⟨23,134334366,134334448⟩,
⟨92,537454216,537454552⟩,
⟨128,752780129,752780598⟩]
theorem checked17123 : checkPrefixCuts (2^48) 2248278017 9 Manual.Count131072.C017123.packed 128 cuts17123 = true := by
 decide +kernel
def pointBounds17123 : List (Nat × Nat × Nat) := [(2248301568,98001298167638,98001677316549),(2248372224,98001701287488,98002080436653)]
theorem point_links_checked17123 : (cuts17123.take 2).map (fun c => (2248278017-1+2*2^9*c.k,98001163833272+c.lower,98001542982101+c.upper)) = pointBounds17123 := by
 decide +kernel
def cuts17124 : List PrefixCut := [⟨33,194165857,194165978⟩,
⟨102,601516662,601517040⟩,
⟨128,759746606,759747077⟩]
theorem checked17124 : checkPrefixCuts (2^48) 2248409089 9 Manual.Count131072.C017124.packed 128 cuts17124 = true := by
 decide +kernel
def pointBounds17124 : List (Nat × Nat × Nat) := [(2248442880,98002110779258,98002489928677),(2248513536,98002518130063,98002897279739)]
theorem point_links_checked17124 : (cuts17124.take 2).map (fun c => (2248409089-1+2*2^9*c.k,98001916613401+c.lower,98002295762699+c.upper)) = pointBounds17124 := by
 decide +kernel
def cuts17125 : List PrefixCut := [⟨43,264380029,264380191⟩,
⟨112,673958374,673958791⟩,
⟨128,768214644,768215120⟩]
theorem checked17125 : checkPrefixCuts (2^48) 2248540161 9 Manual.Count131072.C017125.packed 128 cuts17125 = true := by
 decide +kernel
def pointBounds17125 : List (Nat × Nat × Nat) := [(2248584192,98002940740036,98003319889967),(2248654848,98003350318381,98003729468567)]
theorem point_links_checked17125 : (cuts17125.take 2).map (fun c => (2248540161-1+2*2^9*c.k,98002676360007+c.lower,98003055509776+c.upper)) = pointBounds17125 := by
 decide +kernel
def cuts17126 : List PrefixCut := [⟨53,318814002,318814204⟩,
⟨122,731495905,731496367⟩,
⟨128,768420096,768420581⟩]
theorem checked17126 : checkPrefixCuts (2^48) 2248671233 9 Manual.Count131072.C017126.packed 128 cuts17126 = true := by
 decide +kernel
def pointBounds17126 : List (Nat × Nat × Nat) := [(2248725504,98003763388653,98004142539100),(2248796160,98004176070556,98004555221263)]
theorem point_links_checked17126 : (cuts17126.take 2).map (fun c => (2248671233-1+2*2^9*c.k,98003444574651+c.lower,98003823724896+c.upper)) = pointBounds17126 := by
 decide +kernel
def cuts17127 : List PrefixCut := [⟨63,377121450,377121682⟩,
⟨128,765997131,765997609⟩]
theorem checked17127 : checkPrefixCuts (2^48) 2248802305 9 Manual.Count131072.C017127.packed 128 cuts17127 = true := by
 decide +kernel
def pointBounds17127 : List (Nat × Nat × Nat) := [(2248866816,98004590116197,98004969267159)]
theorem point_links_checked17127 : (cuts17127.take 1).map (fun c => (2248802305-1+2*2^9*c.k,98004212994747+c.lower,98004592145477+c.upper)) = pointBounds17127 := by
 decide +kernel
def cuts17128 : List PrefixCut := [⟨4,21277058,21277071⟩,
⟨73,429414305,429414577⟩,
⟨128,753311673,753312152⟩]
theorem checked17128 : checkPrefixCuts (2^48) 2248933377 9 Manual.Count131072.C017128.packed 128 cuts17128 = true := by
 decide +kernel
def pointBounds17128 : List (Nat × Nat × Nat) := [(2248937472,98005000268936,98005379420157),(2249008128,98005408406183,98005787557663)]
theorem point_links_checked17128 : (cuts17128.take 2).map (fun c => (2248933377-1+2*2^9*c.k,98004978991878+c.lower,98005358143086+c.upper)) = pointBounds17128 := by
 decide +kernel
def cuts17129 : List PrefixCut := [⟨14,80847931,80847983⟩,
⟨83,501349377,501349691⟩,
⟨128,763279919,763280397⟩]
theorem checked17129 : checkPrefixCuts (2^48) 2249064449 9 Manual.Count131072.C017129.packed 128 cuts17129 = true := by
 decide +kernel
def pointBounds17129 : List (Nat × Nat × Nat) := [(2249078784,98005813151482,98006192303221),(2249149440,98006233652928,98006612804929)]
theorem point_links_checked17129 : (cuts17129.take 2).map (fun c => (2249064449-1+2*2^9*c.k,98005732303551+c.lower,98006111455238+c.upper)) = pointBounds17129 := by
 decide +kernel
def cuts17130 : List PrefixCut := [⟨24,139785856,139785944⟩,
⟨93,553503251,553503601⟩,
⟨128,756602896,756603379⟩]
theorem checked17130 : checkPrefixCuts (2^48) 2249195521 9 Manual.Count131072.C017130.packed 128 cuts17130 = true := by
 decide +kernel
def pointBounds17130 : List (Nat × Nat × Nat) := [(2249220096,98006635369326,98007014521579),(2249290752,98007049086721,98007428239236)]
theorem point_links_checked17130 : (cuts17130.take 2).map (fun c => (2249195521-1+2*2^9*c.k,98006495583470+c.lower,98006874735635+c.upper)) = pointBounds17130 := by
 decide +kernel
def cuts17131 : List PrefixCut := [⟨34,201845093,201845219⟩,
⟨103,611031668,611032052⟩,
⟨128,754556715,754557190⟩]
theorem checked17131 : checkPrefixCuts (2^48) 2249326593 9 Manual.Count131072.C017131.packed 128 cuts17131 = true := by
 decide +kernel
def pointBounds17131 : List (Nat × Nat × Nat) := [(2249361408,98007454031459,98007833184233),(2249432064,98007863218034,98008242371066)]
theorem point_links_checked17131 : (cuts17131.take 2).map (fun c => (2249326593-1+2*2^9*c.k,98007252186366+c.lower,98007631339014+c.upper)) = pointBounds17131 := by
 decide +kernel
def cuts17132 : List PrefixCut := [⟨44,261894692,261894858⟩,
⟨113,672056531,672056959⟩,
⟨128,763896992,763897478⟩]
theorem checked17132 : checkPrefixCuts (2^48) 2249457665 9 Manual.Count131072.C017132.packed 128 cuts17132 = true := by
 decide +kernel
def pointBounds17132 : List (Nat × Nat × Nat) := [(2249502720,98008268637773,98008647791062),(2249573376,98008678799612,98009057953163)]
theorem point_links_checked17132 : (cuts17132.take 2).map (fun c => (2249457665-1+2*2^9*c.k,98008006743081+c.lower,98008385896204+c.upper)) = pointBounds17132 := by
 decide +kernel
def cuts17133 : List PrefixCut := [⟨54,321061231,321061430⟩,
⟨123,731948051,731948506⟩,
⟨128,762476277,762476751⟩]
theorem checked17133 : checkPrefixCuts (2^48) 2249588737 9 Manual.Count131072.C017133.packed 128 cuts17133 = true := by
 decide +kernel
def pointBounds17133 : List (Nat × Nat × Nat) := [(2249644032,98009091701304,98009470855112),(2249714688,98009502588124,98009881742188)]
theorem point_links_checked17133 : (cuts17133.take 2).map (fun c => (2249588737-1+2*2^9*c.k,98008770640073+c.lower,98009149793682+c.upper)) = pointBounds17133 := by
 decide +kernel
def cuts17134 : List PrefixCut := [⟨64,377468053,377468289⟩,
⟨128,758177968,758178445⟩]
theorem checked17134 : checkPrefixCuts (2^48) 2249719809 9 Manual.Count131072.C017134.packed 128 cuts17134 = true := by
 decide +kernel
def pointBounds17134 : List (Nat × Nat × Nat) := [(2249785344,98009910584403,98010289738722)]
theorem point_links_checked17134 : (cuts17134.take 1).map (fun c => (2249719809-1+2*2^9*c.k,98009533116350+c.lower,98009912270433+c.upper)) = pointBounds17134 := by
 decide +kernel
def cuts17135 : List PrefixCut := [⟨5,31402134,31402154⟩,
⟨74,439748105,439748372⟩,
⟨128,765765201,765765671⟩]
theorem checked17135 : checkPrefixCuts (2^48) 2249850881 9 Manual.Count131072.C017135.packed 128 cuts17135 = true := by
 decide +kernel
def pointBounds17135 : List (Nat × Nat × Nat) := [(2249856000,98010322696452,98010701851032),(2249926656,98010731042423,98011110197250)]
theorem point_links_checked17135 : (cuts17135.take 2).map (fun c => (2249850881-1+2*2^9*c.k,98010291294318+c.lower,98010670448878+c.upper)) = pointBounds17135 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000222
