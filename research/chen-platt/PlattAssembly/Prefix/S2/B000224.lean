import PlattAssemblyKernel
import PlattCertificates.Count131072.C017168
import PlattCertificates.Count131072.C017169
import PlattCertificates.Count131072.C017170
import PlattCertificates.Count131072.C017171
import PlattCertificates.Count131072.C017172
import PlattCertificates.Count131072.C017173
import PlattCertificates.Count131072.C017174
import PlattCertificates.Count131072.C017175
import PlattCertificates.Count131072.C017176
import PlattCertificates.Count131072.C017177
import PlattCertificates.Count131072.C017178
import PlattCertificates.Count131072.C017179
import PlattCertificates.Count131072.C017180
import PlattCertificates.Count131072.C017181
import PlattCertificates.Count131072.C017182
import PlattCertificates.Count131072.C017183
import PlattCertificates.Count131072.C017184
import PlattCertificates.Count131072.C017185
import PlattCertificates.Count131072.C017186
import PlattCertificates.Count131072.C017187
import PlattCertificates.Count131072.C017188
import PlattCertificates.Count131072.C017189
import PlattCertificates.Count131072.C017190
import PlattCertificates.Count131072.C017191
import PlattCertificates.Count131072.C017192
import PlattCertificates.Count131072.C017193
import PlattCertificates.Count131072.C017194
import PlattCertificates.Count131072.C017195
import PlattCertificates.Count131072.C017196
import PlattCertificates.Count131072.C017197
import PlattCertificates.Count131072.C017198
import PlattCertificates.Count131072.C017199
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000224
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17168 : List PrefixCut := [⟨59,353996544,353996764⟩,
⟨128,767417531,767418009⟩]
theorem checked17168 : checkPrefixCuts (2^48) 2254176257 9 Manual.Count131072.C017168.packed 128 cuts17168 = true := by
 decide +kernel
def pointBounds17168 : List (Nat × Nat × Nat) := [(2254236672,98035763696852,98036142867272),(2254307328,98036177117839,98036556288517)]
theorem point_links_checked17168 : (cuts17168.take 2).map (fun c => (2254176257-1+2*2^9*c.k,98035409700308+c.lower,98035788870508+c.upper)) = pointBounds17168 := by
 decide +kernel
def cuts17169 : List PrefixCut := [⟨69,416529528,416529786⟩,
⟨128,769745299,769745777⟩]
theorem checked17169 : checkPrefixCuts (2^48) 2254307329 9 Manual.Count131072.C017169.packed 128 cuts17169 = true := by
 decide +kernel
def pointBounds17169 : List (Nat × Nat × Nat) := [(2254377984,98036593647367,98036972818303)]
theorem point_links_checked17169 : (cuts17169.take 1).map (fun c => (2254307329-1+2*2^9*c.k,98036177117839+c.lower,98036556288517+c.upper)) = pointBounds17169 := by
 decide +kernel
def cuts17170 : List PrefixCut := [⟨10,57557409,57557445⟩,
⟨79,464697019,464697303⟩,
⟨128,755842076,755842540⟩]
theorem checked17170 : checkPrefixCuts (2^48) 2254438401 9 Manual.Count131072.C017170.packed 128 cuts17170 = true := by
 decide +kernel
def pointBounds17170 : List (Nat × Nat × Nat) := [(2254448640,98037004420547,98037383591739),(2254519296,98037411560157,98037790731597)]
theorem point_links_checked17170 : (cuts17170.take 2).map (fun c => (2254438401-1+2*2^9*c.k,98036946863138+c.lower,98037326034294+c.upper)) = pointBounds17170 := by
 decide +kernel
def cuts17171 : List PrefixCut := [⟨20,119851998,119852073⟩,
⟨89,524094623,524094953⟩,
⟨128,750430026,750430498⟩]
theorem checked17171 : checkPrefixCuts (2^48) 2254569473 9 Manual.Count131072.C017171.packed 128 cuts17171 = true := by
 decide +kernel
def pointBounds17171 : List (Nat × Nat × Nat) := [(2254589952,98037822557212,98038201728907),(2254660608,98038226799837,98038605971787)]
theorem point_links_checked17171 : (cuts17171.take 2).map (fun c => (2254569473-1+2*2^9*c.k,98037702705214+c.lower,98038081876834+c.upper)) = pointBounds17171 := by
 decide +kernel
def cuts17172 : List PrefixCut := [⟨30,180141651,180141760⟩,
⟨99,583609974,583610341⟩,
⟨128,755254947,755255422⟩]
theorem checked17172 : checkPrefixCuts (2^48) 2254700545 9 Manual.Count131072.C017172.packed 128 cuts17172 = true := by
 decide +kernel
def pointBounds17172 : List (Nat × Nat × Nat) := [(2254731264,98038633276891,98039012449092),(2254801920,98039036745214,98039415917673)]
theorem point_links_checked17172 : (cuts17172.take 2).map (fun c => (2254700545-1+2*2^9*c.k,98038453135240+c.lower,98038832307332+c.upper)) = pointBounds17172 := by
 decide +kernel
def cuts17173 : List PrefixCut := [⟨40,245417233,245417382⟩,
⟨109,655600899,655601305⟩,
⟨128,771438652,771439130⟩]
theorem checked17173 : checkPrefixCuts (2^48) 2254831617 9 Manual.Count131072.C017173.packed 128 cuts17173 = true := by
 decide +kernel
def pointBounds17173 : List (Nat × Nat × Nat) := [(2254872576,98039453807420,98039832980136),(2254943232,98039863991086,98040243164059)]
theorem point_links_checked17173 : (cuts17173.take 2).map (fun c => (2254831617-1+2*2^9*c.k,98039208390187+c.lower,98039587562754+c.upper)) = pointBounds17173 := by
 decide +kernel
def cuts17174 : List PrefixCut := [⟨50,294707607,294707787⟩,
⟨119,705240059,705240498⟩,
⟨128,758662002,758662475⟩]
theorem checked17174 : checkPrefixCuts (2^48) 2254962689 9 Manual.Count131072.C017174.packed 128 cuts17174 = true := by
 decide +kernel
def pointBounds17174 : List (Nat × Nat × Nat) := [(2255013888,98040274536446,98040653709671),(2255084544,98040685068898,98041064242382)]
theorem point_links_checked17174 : (cuts17174.take 2).map (fun c => (2254962689-1+2*2^9*c.k,98039979828839+c.lower,98040359001884+c.upper)) = pointBounds17174 := by
 decide +kernel
def cuts17175 : List PrefixCut := [⟨60,359593918,359594142⟩,
⟨128,764234571,764235049⟩]
theorem checked17175 : checkPrefixCuts (2^48) 2255093761 9 Manual.Count131072.C017175.packed 128 cuts17175 = true := by
 decide +kernel
def pointBounds17175 : List (Nat × Nat × Nat) := [(2255155200,98041098084759,98041477258501)]
theorem point_links_checked17175 : (cuts17175.take 1).map (fun c => (2255093761-1+2*2^9*c.k,98040738490841+c.lower,98041117664359+c.upper)) = pointBounds17175 := by
 decide +kernel
def cuts17176 : List PrefixCut := [⟨1,6490125,6490129⟩,
⟨70,418232063,418232318⟩,
⟨128,762692538,762693013⟩]
theorem checked17176 : checkPrefixCuts (2^48) 2255224833 9 Manual.Count131072.C017176.packed 128 cuts17176 = true := by
 decide +kernel
def pointBounds17176 : List (Nat × Nat × Nat) := [(2255225856,98041509215537,98041888389537),(2255296512,98041920957475,98042300131726)]
theorem point_links_checked17176 : (cuts17176.take 2).map (fun c => (2255224833-1+2*2^9*c.k,98041502725412+c.lower,98041881899408+c.upper)) = pointBounds17176 := by
 decide +kernel
def cuts17177 : List PrefixCut := [⟨11,63274896,63274938⟩,
⟨80,467877444,467877737⟩,
⟨128,747048296,747048762⟩]
theorem checked17177 : checkPrefixCuts (2^48) 2255355905 9 Manual.Count131072.C017177.packed 128 cuts17177 = true := by
 decide +kernel
def pointBounds17177 : List (Nat × Nat × Nat) := [(2255367168,98042328692846,98042707867359),(2255437824,98042733295394,98043112470158)]
theorem point_links_checked17177 : (cuts17177.take 2).map (fun c => (2255355905-1+2*2^9*c.k,98042265417950+c.lower,98042644592421+c.upper)) = pointBounds17177 := by
 decide +kernel
def cuts17178 : List PrefixCut := [⟨21,126167755,126167832⟩,
⟨90,532492024,532492355⟩,
⟨128,758735271,758735741⟩]
theorem checked17178 : checkPrefixCuts (2^48) 2255486977 9 Manual.Count131072.C017178.packed 128 cuts17178 = true := by
 decide +kernel
def pointBounds17178 : List (Nat × Nat × Nat) := [(2255508480,98043138634001,98043517809015),(2255579136,98043544958270,98043924133538)]
theorem point_links_checked17178 : (cuts17178.take 2).map (fun c => (2255486977-1+2*2^9*c.k,98043012466246+c.lower,98043391641183+c.upper)) = pointBounds17178 := by
 decide +kernel
def cuts17179 : List PrefixCut := [⟨31,183188060,183188173⟩,
⟨100,591733063,591733428⟩,
⟨128,755322161,755322628⟩]
theorem checked17179 : checkPrefixCuts (2^48) 2255618049 9 Manual.Count131072.C017179.packed 128 cuts17179 = true := by
 decide +kernel
def pointBounds17179 : List (Nat × Nat × Nat) := [(2255649792,98043954389577,98044333565097),(2255720448,98044362934580,98044742110352)]
theorem point_links_checked17179 : (cuts17179.take 2).map (fun c => (2255618049-1+2*2^9*c.k,98043771201517+c.lower,98044150376924+c.upper)) = pointBounds17179 := by
 decide +kernel
def cuts17180 : List PrefixCut := [⟨41,245192631,245192785⟩,
⟨110,659451747,659452156⟩,
⟨128,766632943,766633421⟩]
theorem checked17180 : checkPrefixCuts (2^48) 2255749121 9 Manual.Count131072.C017180.packed 128 cuts17180 = true := by
 decide +kernel
def pointBounds17180 : List (Nat × Nat × Nat) := [(2255791104,98044771716309,98045150892337),(2255861760,98045185975425,98045565151708)]
theorem point_links_checked17180 : (cuts17180.take 2).map (fun c => (2255749121-1+2*2^9*c.k,98044526523678+c.lower,98044905699552+c.upper)) = pointBounds17180 := by
 decide +kernel
def cuts17181 : List PrefixCut := [⟨51,301949245,301949429⟩,
⟨120,703206455,703206894⟩,
⟨128,749994019,749994490⟩]
theorem checked17181 : checkPrefixCuts (2^48) 2255880193 9 Manual.Count131072.C017181.packed 128 cuts17181 = true := by
 decide +kernel
def pointBounds17181 : List (Nat × Nat × Nat) := [(2255932416,98045595105866,98045974282402),(2256003072,98045996363076,98046375539867)]
theorem point_links_checked17181 : (cuts17181.take 2).map (fun c => (2255880193-1+2*2^9*c.k,98045293156621+c.lower,98045672332973+c.upper)) = pointBounds17181 := by
 decide +kernel
def cuts17182 : List PrefixCut := [⟨61,359821954,359822181⟩,
⟨128,753318962,753319441⟩]
theorem checked17182 : checkPrefixCuts (2^48) 2256011265 9 Manual.Count131072.C017182.packed 128 cuts17182 = true := by
 decide +kernel
def pointBounds17182 : List (Nat × Nat × Nat) := [(2256073728,98046402972594,98046782149644)]
theorem point_links_checked17182 : (cuts17182.take 1).map (fun c => (2256011265-1+2*2^9*c.k,98046043150640+c.lower,98046422327463+c.upper)) = pointBounds17182 := by
 decide +kernel
def cuts17183 : List PrefixCut := [⟨2,11852134,11852142⟩,
⟨71,418560958,418561216⟩,
⟨128,763505021,763505491⟩]
theorem checked17183 : checkPrefixCuts (2^48) 2256142337 9 Manual.Count131072.C017183.packed 128 cuts17183 = true := by
 decide +kernel
def pointBounds17183 : List (Nat × Nat × Nat) := [(2256144384,98046808321736,98047187499046),(2256215040,98047215030560,98047594208120)]
theorem point_links_checked17183 : (cuts17183.take 2).map (fun c => (2256142337-1+2*2^9*c.k,98046796469602+c.lower,98047175646904+c.upper)) = pointBounds17183 := by
 decide +kernel
def cuts17184 : List PrefixCut := [⟨12,72106529,72106575⟩,
⟨81,483156107,483156408⟩,
⟨128,762587610,762588089⟩]
theorem checked17184 : checkPrefixCuts (2^48) 2256273409 9 Manual.Count131072.C017184.packed 128 cuts17184 = true := by
 decide +kernel
def pointBounds17184 : List (Nat × Nat × Nat) := [(2256285696,98047632081152,98048011258970),(2256356352,98048043130730,98048422308803)]
theorem point_links_checked17184 : (cuts17184.take 2).map (fun c => (2256273409-1+2*2^9*c.k,98047559974623+c.lower,98047939152395+c.upper)) = pointBounds17184 := by
 decide +kernel
def cuts17185 : List PrefixCut := [⟨22,130856710,130856790⟩,
⟨91,539510419,539510757⟩,
⟨128,758426797,758427272⟩]
theorem checked17185 : checkPrefixCuts (2^48) 2256404481 9 Manual.Count131072.C017185.packed 128 cuts17185 = true := by
 decide +kernel
def pointBounds17185 : List (Nat × Nat × Nat) := [(2256427008,98048453418943,98048832597274),(2256497664,98048862072652,98049241251241)]
theorem point_links_checked17185 : (cuts17185.take 2).map (fun c => (2256404481-1+2*2^9*c.k,98048322562233+c.lower,98048701740484+c.upper)) = pointBounds17185 := by
 decide +kernel
def cuts17186 : List PrefixCut := [⟨32,191096651,191096771⟩,
⟨101,603840977,603841357⟩,
⟨128,769109736,769110218⟩]
theorem checked17186 : checkPrefixCuts (2^48) 2256535553 9 Manual.Count131072.C017186.packed 128 cuts17186 = true := by
 decide +kernel
def pointBounds17186 : List (Nat × Nat × Nat) := [(2256568320,98049272085681,98049651264527),(2256638976,98049684830007,98050064009113)]
theorem point_links_checked17186 : (cuts17186.take 2).map (fun c => (2256535553-1+2*2^9*c.k,98049080989030+c.lower,98049460167756+c.upper)) = pointBounds17186 := by
 decide +kernel
def cuts17187 : List PrefixCut := [⟨42,247712198,247712351⟩,
⟨111,656688978,656689387⟩,
⟨128,753474519,753474987⟩]
theorem checked17187 : checkPrefixCuts (2^48) 2256666625 9 Manual.Count131072.C017187.packed 128 cuts17187 = true := by
 decide +kernel
def pointBounds17187 : List (Nat × Nat × Nat) := [(2256709632,98050097810964,98050476990325),(2256780288,98050506787744,98050885967361)]
theorem point_links_checked17187 : (cuts17187.take 2).map (fun c => (2256666625-1+2*2^9*c.k,98049850098766+c.lower,98050229277974+c.upper)) = pointBounds17187 := by
 decide +kernel
def cuts17188 : List PrefixCut := [⟨52,309933364,309933557⟩,
⟨121,724870918,724871366⟩,
⟨128,767773254,767773729⟩]
theorem checked17188 : checkPrefixCuts (2^48) 2256797697 9 Manual.Count131072.C017188.packed 128 cuts17188 = true := by
 decide +kernel
def pointBounds17188 : List (Nat × Nat × Nat) := [(2256850944,98050913506649,98051292686518),(2256921600,98051328444203,98051707624327)]
theorem point_links_checked17188 : (cuts17188.take 2).map (fun c => (2256797697-1+2*2^9*c.k,98050603573285+c.lower,98050982752961+c.upper)) = pointBounds17188 := by
 decide +kernel
def cuts17189 : List PrefixCut := [⟨62,360548603,360548824⟩,
⟨128,748522965,748523428⟩]
theorem checked17189 : checkPrefixCuts (2^48) 2256928769 9 Manual.Count131072.C017189.packed 128 cuts17189 = true := by
 decide +kernel
def pointBounds17189 : List (Nat × Nat × Nat) := [(2256992256,98051731895142,98052111075514)]
theorem point_links_checked17189 : (cuts17189.take 1).map (fun c => (2256928769-1+2*2^9*c.k,98051371346539+c.lower,98051750526690+c.upper)) = pointBounds17189 := by
 decide +kernel
def cuts17190 : List PrefixCut := [⟨3,15339153,15339164⟩,
⟨72,416395417,416395679⟩,
⟨128,744488990,744489457⟩]
theorem checked17190 : checkPrefixCuts (2^48) 2257059841 9 Manual.Count131072.C017190.packed 128 cuts17190 = true := by
 decide +kernel
def pointBounds17190 : List (Nat × Nat × Nat) := [(2257062912,98052135208657,98052514389282),(2257133568,98052536264921,98052915445797)]
theorem point_links_checked17190 : (cuts17190.take 2).map (fun c => (2257059841-1+2*2^9*c.k,98052119869504+c.lower,98052499050118+c.upper)) = pointBounds17190 := by
 decide +kernel
def cuts17191 : List PrefixCut := [⟨13,81180388,81180438⟩,
⟨82,489818082,489818390⟩,
⟨128,760282554,760283031⟩]
theorem checked17191 : checkPrefixCuts (2^48) 2257190913 9 Manual.Count131072.C017191.packed 128 cuts17191 = true := by
 decide +kernel
def pointBounds17191 : List (Nat × Nat × Nat) := [(2257204224,98052945538882,98053324720013),(2257274880,98053354176576,98053733357965)]
theorem point_links_checked17191 : (cuts17191.take 2).map (fun c => (2257190913-1+2*2^9*c.k,98052864358494+c.lower,98053243539575+c.upper)) = pointBounds17191 := by
 decide +kernel
def cuts17192 : List PrefixCut := [⟨23,136788781,136788865⟩,
⟨92,545650275,545650618⟩,
⟨128,761360443,761360919⟩]
theorem checked17192 : checkPrefixCuts (2^48) 2257321985 9 Manual.Count131072.C017192.packed 128 cuts17192 = true := by
 decide +kernel
def pointBounds17192 : List (Nat × Nat × Nat) := [(2257345536,98053761429829,98054140611471),(2257416192,98054170291323,98054549473224)]
theorem point_links_checked17192 : (cuts17192.take 2).map (fun c => (2257321985-1+2*2^9*c.k,98053624641048+c.lower,98054003822606+c.upper)) = pointBounds17192 := by
 decide +kernel
def cuts17193 : List PrefixCut := [⟨33,197751981,197752105⟩,
⟨102,607710038,607710415⟩,
⟨128,761440997,761441472⟩]
theorem checked17193 : checkPrefixCuts (2^48) 2257453057 9 Manual.Count131072.C017193.packed 128 cuts17193 = true := by
 decide +kernel
def pointBounds17193 : List (Nat × Nat × Nat) := [(2257486848,98054583753472,98054962935630),(2257557504,98054993711529,98055372893940)]
theorem point_links_checked17193 : (cuts17193.take 2).map (fun c => (2257453057-1+2*2^9*c.k,98054386001491+c.lower,98054765183525+c.upper)) = pointBounds17193 := by
 decide +kernel
def cuts17194 : List PrefixCut := [⟨43,255840233,255840390⟩,
⟨112,665398641,665399057⟩,
⟨128,758404624,758405097⟩]
theorem checked17194 : checkPrefixCuts (2^48) 2257584129 9 Manual.Count131072.C017194.packed 128 cuts17194 = true := by
 decide +kernel
def pointBounds17194 : List (Nat × Nat × Nat) := [(2257628160,98055403282721,98055782465387),(2257698816,98055812841129,98056192024054)]
theorem point_links_checked17194 : (cuts17194.take 2).map (fun c => (2257584129-1+2*2^9*c.k,98055147442488+c.lower,98055526624997+c.upper)) = pointBounds17194 := by
 decide +kernel
def cuts17195 : List PrefixCut := [⟨53,306441198,306441390⟩,
⟨122,717095994,717096438⟩,
⟨128,752874956,752875423⟩]
theorem checked17195 : checkPrefixCuts (2^48) 2257715201 9 Manual.Count131072.C017195.packed 128 cuts17195 = true := by
 decide +kernel
def pointBounds17195 : List (Nat × Nat × Nat) := [(2257769472,98056212288310,98056591471484),(2257840128,98056622943106,98057002126532)]
theorem point_links_checked17195 : (cuts17195.take 2).map (fun c => (2257715201-1+2*2^9*c.k,98055905847112+c.lower,98056285030094+c.upper)) = pointBounds17195 := by
 decide +kernel
def cuts17196 : List PrefixCut := [⟨63,370749061,370749294⟩,
⟨128,757942446,757942922⟩]
theorem checked17196 : checkPrefixCuts (2^48) 2257846273 9 Manual.Count131072.C017196.packed 128 cuts17196 = true := by
 decide +kernel
def pointBounds17196 : List (Nat × Nat × Nat) := [(2257910784,98057029471129,98057408654811)]
theorem point_links_checked17196 : (cuts17196.take 1).map (fun c => (2257846273-1+2*2^9*c.k,98056658722068+c.lower,98057037905517+c.upper)) = pointBounds17196 := by
 decide +kernel
def cuts17197 : List PrefixCut := [⟨4,20568548,20568560⟩,
⟨73,425699893,425700156⟩,
⟨128,747676782,747677246⟩]
theorem checked17197 : checkPrefixCuts (2^48) 2257977345 9 Manual.Count131072.C017197.packed 128 cuts17197 = true := by
 decide +kernel
def pointBounds17197 : List (Nat × Nat × Nat) := [(2257981440,98057437233062,98057816416999),(2258052096,98057842364407,98058221548595)]
theorem point_links_checked17197 : (cuts17197.take 2).map (fun c => (2257977345-1+2*2^9*c.k,98057416664514+c.lower,98057795848439+c.upper)) = pointBounds17197 := by
 decide +kernel
def cuts17198 : List PrefixCut := [⟨14,83141788,83141839⟩,
⟨83,496973127,496973437⟩,
⟨128,759599671,759600150⟩]
theorem checked17198 : checkPrefixCuts (2^48) 2258108417 9 Manual.Count131072.C017198.packed 128 cuts17198 = true := by
 decide +kernel
def pointBounds17198 : List (Nat × Nat × Nat) := [(2258122752,98058247483084,98058626667524),(2258193408,98058661314423,98059040499122)]
theorem point_links_checked17198 : (cuts17198.take 2).map (fun c => (2258108417-1+2*2^9*c.k,98058164341296+c.lower,98058543525685+c.upper)) = pointBounds17198 := by
 decide +kernel
def cuts17199 : List PrefixCut := [⟨24,134489624,134489706⟩,
⟨93,545926966,545927304⟩,
⟨128,755192931,755193402⟩]
theorem checked17199 : checkPrefixCuts (2^48) 2258239489 9 Manual.Count131072.C017199.packed 128 cuts17199 = true := by
 decide +kernel
def pointBounds17199 : List (Nat × Nat × Nat) := [(2258264064,98059058430591,98059437615541),(2258334720,98059469867933,98059849053139)]
theorem point_links_checked17199 : (cuts17199.take 2).map (fun c => (2258239489-1+2*2^9*c.k,98058923940967+c.lower,98059303125835+c.upper)) = pointBounds17199 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000224
