import PlattAssemblyKernel
import PlattCertificates.Count131072.C013200
import PlattCertificates.Count131072.C013201
import PlattCertificates.Count131072.C013202
import PlattCertificates.Count131072.C013203
import PlattCertificates.Count131072.C013204
import PlattCertificates.Count131072.C013205
import PlattCertificates.Count131072.C013206
import PlattCertificates.Count131072.C013207
import PlattCertificates.Count131072.C013208
import PlattCertificates.Count131072.C013209
import PlattCertificates.Count131072.C013210
import PlattCertificates.Count131072.C013211
import PlattCertificates.Count131072.C013212
import PlattCertificates.Count131072.C013213
import PlattCertificates.Count131072.C013214
import PlattCertificates.Count131072.C013215
import PlattCertificates.Count131072.C013216
import PlattCertificates.Count131072.C013217
import PlattCertificates.Count131072.C013218
import PlattCertificates.Count131072.C013219
import PlattCertificates.Count131072.C013220
import PlattCertificates.Count131072.C013221
import PlattCertificates.Count131072.C013222
import PlattCertificates.Count131072.C013223
import PlattCertificates.Count131072.C013224
import PlattCertificates.Count131072.C013225
import PlattCertificates.Count131072.C013226
import PlattCertificates.Count131072.C013227
import PlattCertificates.Count131072.C013228
import PlattCertificates.Count131072.C013229
import PlattCertificates.Count131072.C013230
import PlattCertificates.Count131072.C013231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13200 : List PrefixCut := [⟨21,168810915,168811036⟩,
⟨74,587420385,587420808⟩,
⟨127,1004069142,1004069865⟩,
⟨128,1012184490,1012185219⟩]
theorem checked13200 : checkPrefixCuts (2^48) 1734082561 9 Manual.Count131072.C013200.packed 128 cuts13200 = true := by
 decide +kernel
def pointBounds13200 : List (Nat × Nat × Nat) := [(1734104064,94586300120676,94586676991400),(1734158336,94586718730146,94587095601172),(1734212608,94587135378903,94587512250229)]
theorem point_links_checked13200 : (cuts13200.take 3).map (fun c => (1734082561-1+2*2^9*c.k,94586131309761+c.lower,94586508180364+c.upper)) = pointBounds13200 := by
 decide +kernel
def cuts13201 : List PrefixCut := [⟨52,405274099,405274395⟩,
⟨105,813619334,813619921⟩,
⟨128,995390569,995391289⟩]
theorem checked13201 : checkPrefixCuts (2^48) 1734213633 9 Manual.Count131072.C013201.packed 128 cuts13201 = true := by
 decide +kernel
def pointBounds13201 : List (Nat × Nat × Nat) := [(1734266880,94587548768350,94587925639978),(1734321152,94587957113585,94588333985504)]
theorem point_links_checked13201 : (cuts13201.take 2).map (fun c => (1734213633-1+2*2^9*c.k,94587143494251+c.lower,94587520365583+c.upper)) = pointBounds13201 := by
 decide +kernel
def cuts13202 : List PrefixCut := [⟨30,235812008,235812178⟩,
⟨83,656141250,656141719⟩,
⟨128,1002618820,1002619540⟩]
theorem checked13202 : checkPrefixCuts (2^48) 1734344705 9 Manual.Count131072.C013202.packed 128 cuts13202 = true := by
 decide +kernel
def pointBounds13202 : List (Nat × Nat × Nat) := [(1734375424,94588374696828,94588751569050),(1734429696,94588795026070,94589171898591)]
theorem point_links_checked13202 : (cuts13202.take 2).map (fun c => (1734344705-1+2*2^9*c.k,94588138884820+c.lower,94588515756872+c.upper)) = pointBounds13202 := by
 decide +kernel
def cuts13203 : List PrefixCut := [⟨8,63614549,63614593⟩,
⟨61,472395670,472396011⟩,
⟨114,884896173,884896815⟩,
⟨128,990372199,990372914⟩]
theorem checked13203 : checkPrefixCuts (2^48) 1734475777 9 Manual.Count131072.C013203.packed 128 cuts13203 = true := by
 decide +kernel
def pointBounds13203 : List (Nat × Nat × Nat) := [(1734483968,94589205118189,94589581991005),(1734538240,94589613899310,94589990772423),(1734592512,94590026399813,94590403273227)]
theorem point_links_checked13203 : (cuts13203.take 3).map (fun c => (1734475777-1+2*2^9*c.k,94589141503640+c.lower,94589518376412+c.upper)) = pointBounds13203 := by
 decide +kernel
def cuts13204 : List PrefixCut := [⟨39,302468054,302468268⟩,
⟨92,722082300,722082815⟩,
⟨128,1001980147,1001980865⟩]
theorem checked13204 : checkPrefixCuts (2^48) 1734606849 9 Manual.Count131072.C013204.packed 128 cuts13204 = true := by
 decide +kernel
def pointBounds13204 : List (Nat × Nat × Nat) := [(1734646784,94590434343893,94590811217594),(1734701056,94590853958139,94591230832141)]
theorem point_links_checked13204 : (cuts13204.take 2).map (fun c => (1734606849-1+2*2^9*c.k,94590131875839+c.lower,94590508749326+c.upper)) = pointBounds13204 := by
 decide +kernel
def cuts13205 : List PrefixCut := [⟨17,132239489,132239586⟩,
⟨70,536251239,536251621⟩,
⟨123,957286439,957287121⟩,
⟨128,995251966,995252677⟩]
theorem checked13205 : checkPrefixCuts (2^48) 1734737921 9 Manual.Count131072.C013205.packed 128 cuts13205 = true := by
 decide +kernel
def pointBounds13205 : List (Nat × Nat × Nat) := [(1734755328,94591266095475,94591642969777),(1734809600,94591670107225,94592046981812),(1734863872,94592091142425,94592468017312)]
theorem point_links_checked13205 : (cuts13205.take 3).map (fun c => (1734737921-1+2*2^9*c.k,94591133855986+c.lower,94591510730191+c.upper)) = pointBounds13205 := by
 decide +kernel
def cuts13206 : List PrefixCut := [⟨48,374457536,374457806⟩,
⟨101,792546105,792546673⟩,
⟨128,1000855394,1000856108⟩]
theorem checked13206 : checkPrefixCuts (2^48) 1734868993 9 Manual.Count131072.C013206.packed 128 cuts13206 = true := by
 decide +kernel
def pointBounds13206 : List (Nat × Nat × Nat) := [(1734918144,94592503565488,94592880440674),(1734972416,94592921654057,94593298529541)]
theorem point_links_checked13206 : (cuts13206.take 2).map (fun c => (1734868993-1+2*2^9*c.k,94592129107952+c.lower,94592505982868+c.upper)) = pointBounds13206 := by
 decide +kernel
def cuts13207 : List PrefixCut := [⟨26,204899149,204899296⟩,
⟨79,609983243,609983679⟩,
⟨128,988288317,988289022⟩]
theorem checked13207 : checkPrefixCuts (2^48) 1735000065 9 Manual.Count131072.C013207.packed 128 cuts13207 = true := by
 decide +kernel
def pointBounds13207 : List (Nat × Nat × Nat) := [(1735026688,94593334862495,94593711738272),(1735080960,94593739946589,94594116822655)]
theorem point_links_checked13207 : (cuts13207.take 2).map (fun c => (1735000065-1+2*2^9*c.k,94593129963346+c.lower,94593506838976+c.upper)) = pointBounds13207 := by
 decide +kernel
def cuts13208 : List PrefixCut := [⟨4,26442007,26442027⟩,
⟨57,429391859,429392170⟩,
⟨110,847414967,847415579⟩,
⟨128,991943810,991944525⟩]
theorem checked13208 : checkPrefixCuts (2^48) 1735131137 9 Manual.Count131072.C013208.packed 128 cuts13208 = true := by
 decide +kernel
def pointBounds13208 : List (Nat × Nat × Nat) := [(1735135232,94594144693670,94594521570025),(1735189504,94594547643522,94594924520168),(1735243776,94594965666630,94595342543577)]
theorem point_links_checked13208 : (cuts13208.take 3).map (fun c => (1735131137-1+2*2^9*c.k,94594118251663+c.lower,94594495127998+c.upper)) = pointBounds13208 := by
 decide +kernel
def cuts13209 : List PrefixCut := [⟨35,270074975,270075169⟩,
⟨88,683692406,683692897⟩,
⟨128,997708723,997709437⟩]
theorem checked13209 : checkPrefixCuts (2^48) 1735262209 9 Manual.Count131072.C013209.packed 128 cuts13209 = true := by
 decide +kernel
def pointBounds13209 : List (Nat × Nat × Nat) := [(1735298048,94595380270448,94595757147692),(1735352320,94595793887879,94596170765420)]
theorem point_links_checked13209 : (cuts13209.take 2).map (fun c => (1735262209-1+2*2^9*c.k,94595110195473+c.lower,94595487072523+c.upper)) = pointBounds13209 := by
 decide +kernel
def cuts13210 : List PrefixCut := [⟨13,97317583,97317656⟩,
⟨66,510584846,510585216⟩,
⟨119,934057004,934057676⟩,
⟨128,1005093933,1005094657⟩]
theorem checked13210 : checkPrefixCuts (2^48) 1735393281 9 Manual.Count131072.C013210.packed 128 cuts13210 = true := by
 decide +kernel
def pointBounds13210 : List (Nat × Nat × Nat) := [(1735406592,94596205221779,94596582099616),(1735460864,94596618489042,94596995367176),(1735515136,94597041961200,94597418839636)]
theorem point_links_checked13210 : (cuts13210.take 3).map (fun c => (1735393281-1+2*2^9*c.k,94596107904196+c.lower,94596484781960+c.upper)) = pointBounds13210 := by
 decide +kernel
def cuts13211 : List PrefixCut := [⟨44,336852466,336852710⟩,
⟨97,752838014,752838556⟩,
⟨128,1000152739,1000153458⟩]
theorem checked13211 : checkPrefixCuts (2^48) 1735524353 9 Manual.Count131072.C013211.packed 128 cuts13211 = true := by
 decide +kernel
def pointBounds13211 : List (Nat × Nat × Nat) := [(1735569408,94597449850595,94597826729327),(1735623680,94597865836143,94598242715173)]
theorem point_links_checked13211 : (cuts13211.take 2).map (fun c => (1735524353-1+2*2^9*c.k,94597112998129+c.lower,94597489876617+c.upper)) = pointBounds13211 := by
 decide +kernel
def cuts13212 : List PrefixCut := [⟨22,176766429,176766556⟩,
⟨75,589482585,589483012⟩,
⟨128,998456142,998456860⟩]
theorem checked13212 : checkPrefixCuts (2^48) 1735655425 9 Manual.Count131072.C013212.packed 128 cuts13212 = true := by
 decide +kernel
def pointBounds13212 : List (Nat × Nat × Nat) := [(1735677952,94598289917297,94598666796631),(1735732224,94598702633453,94599079513087),(1735786496,94599111607010,94599488486935)]
theorem point_links_checked13212 : (cuts13212.take 3).map (fun c => (1735655425-1+2*2^9*c.k,94598113150868+c.lower,94598490030075+c.upper)) = pointBounds13212 := by
 decide +kernel
def cuts13213 : List PrefixCut := [⟨53,411393066,411393363⟩,
⟨106,823746207,823746802⟩,
⟨128,994813047,994813762⟩]
theorem checked13213 : checkPrefixCuts (2^48) 1735786497 9 Manual.Count131072.C013213.packed 128 cuts13213 = true := by
 decide +kernel
def pointBounds13213 : List (Nat × Nat × Nat) := [(1735840768,94599523000076,94599899880298),(1735895040,94599935353217,94600312233737)]
theorem point_links_checked13213 : (cuts13213.take 2).map (fun c => (1735786497-1+2*2^9*c.k,94599111607010+c.lower,94599488486935+c.upper)) = pointBounds13213 := by
 decide +kernel
def cuts13214 : List PrefixCut := [⟨31,232031127,232031293⟩,
⟨84,648736268,648736733⟩,
⟨128,994737623,994738335⟩]
theorem checked13214 : checkPrefixCuts (2^48) 1735917569 9 Manual.Count131072.C013214.packed 128 cuts13214 = true := by
 decide +kernel
def pointBounds13214 : List (Nat × Nat × Nat) := [(1735949312,94600338451184,94600715331990),(1736003584,94600755156325,94601132037430)]
theorem point_links_checked13214 : (cuts13214.take 2).map (fun c => (1735917569-1+2*2^9*c.k,94600106420057+c.lower,94600483300697+c.upper)) = pointBounds13214 := by
 decide +kernel
def cuts13215 : List PrefixCut := [⟨9,67934533,67934582⟩,
⟨62,487694200,487694549⟩,
⟨115,904522519,904523164⟩,
⟨128,1003255877,1003256593⟩]
theorem checked13215 : checkPrefixCuts (2^48) 1736048641 9 Manual.Count131072.C013215.packed 128 cuts13215 = true := by
 decide +kernel
def pointBounds13215 : List (Nat × Nat × Nat) := [(1736057856,94601169092213,94601545973614),(1736112128,94601588851880,94601965733581),(1736166400,94602005680199,94602382562196)]
theorem point_links_checked13215 : (cuts13215.take 3).map (fun c => (1736048641-1+2*2^9*c.k,94601101157680+c.lower,94601478039032+c.upper)) = pointBounds13215 := by
 decide +kernel
def cuts13216 : List PrefixCut := [⟨40,317271169,317271395⟩,
⟨93,729047707,729048227⟩,
⟨128,995884994,995885703⟩]
theorem checked13216 : checkPrefixCuts (2^48) 1736179713 9 Manual.Count131072.C013216.packed 128 cuts13216 = true := by
 decide +kernel
def pointBounds13216 : List (Nat × Nat × Nat) := [(1736220672,94602421684726,94602798567020),(1736274944,94602833461264,94603210343852)]
theorem point_links_checked13216 : (cuts13216.take 2).map (fun c => (1736179713-1+2*2^9*c.k,94602104413557+c.lower,94602481295625+c.upper)) = pointBounds13216 := by
 decide +kernel
def cuts13217 : List PrefixCut := [⟨18,140387259,140387359⟩,
⟨71,548571767,548572164⟩,
⟨124,965334881,965335575⟩,
⟨128,996133658,996134375⟩]
theorem checked13217 : checkPrefixCuts (2^48) 1736310785 9 Manual.Count131072.C013217.packed 128 cuts13217 = true := by
 decide +kernel
def pointBounds13217 : List (Nat × Nat × Nat) := [(1736329216,94603240685810,94603617568687),(1736383488,94603648870318,94604025753492),(1736437760,94604065633432,94604442516903)]
theorem point_links_checked13217 : (cuts13217.take 3).map (fun c => (1736310785-1+2*2^9*c.k,94603100298551+c.lower,94603477181328+c.upper)) = pointBounds13217 := by
 decide +kernel
def cuts13218 : List PrefixCut := [⟨49,380439990,380440266⟩,
⟨102,793286865,793287440⟩,
⟨128,999948598,999949317⟩]
theorem checked13218 : checkPrefixCuts (2^48) 1736441857 9 Manual.Count131072.C013218.packed 128 cuts13218 = true := by
 decide +kernel
def pointBounds13218 : List (Nat × Nat × Nat) := [(1736492032,94604476872199,94604853755969),(1736546304,94604889719074,94605266603143)]
theorem point_links_checked13218 : (cuts13218.take 2).map (fun c => (1736441857-1+2*2^9*c.k,94604096432209+c.lower,94604473315703+c.upper)) = pointBounds13218 := by
 decide +kernel
def cuts13219 : List PrefixCut := [⟨27,210386490,210386645⟩,
⟨80,624342201,624342653⟩,
⟨128,992904149,992904866⟩]
theorem checked13219 : checkPrefixCuts (2^48) 1736572929 9 Manual.Count131072.C013219.packed 128 cuts13219 = true := by
 decide +kernel
def pointBounds13219 : List (Nat × Nat × Nat) := [(1736600576,94605306767297,94605683651665),(1736654848,94605720723008,94606097607673)]
theorem point_links_checked13219 : (cuts13219.take 2).map (fun c => (1736572929-1+2*2^9*c.k,94605096380807+c.lower,94605473265020+c.upper)) = pointBounds13219 := by
 decide +kernel
def cuts13220 : List PrefixCut := [⟨5,38897746,38897774⟩,
⟨58,458824078,458824404⟩,
⟨112,876630391,876631019⟩,
⟨128,1001904854,1001905572⟩]
theorem checked13220 : checkPrefixCuts (2^48) 1736704001 9 Manual.Count131072.C013220.packed 128 cuts13220 = true := by
 decide +kernel
def pointBounds13220 : List (Nat × Nat × Nat) := [(1736709120,94606128182702,94606505067660),(1736763392,94606548109034,94606924994290),(1736818688,94606965915347,94607342800905)]
theorem point_links_checked13220 : (cuts13220.take 3).map (fun c => (1736704001-1+2*2^9*c.k,94606089284956+c.lower,94606466169886+c.upper)) = pointBounds13220 := by
 decide +kernel
def cuts13221 : List PrefixCut := [⟨38,292356510,292356721⟩,
⟨92,711108559,711109068⟩,
⟨128,997777596,997778316⟩]
theorem checked13221 : checkPrefixCuts (2^48) 1736835073 9 Manual.Count131072.C013221.packed 128 cuts13221 = true := by
 decide +kernel
def pointBounds13221 : List (Nat × Nat × Nat) := [(1736873984,94607383546320,94607760432179),(1736929280,94607802298369,94608179184526)]
theorem point_links_checked13221 : (cuts13221.take 2).map (fun c => (1736835073-1+2*2^9*c.k,94607091189810+c.lower,94607468075458+c.upper)) = pointBounds13221 := by
 decide +kernel
def cuts13222 : List PrefixCut := [⟨18,147140359,147140465⟩,
⟨72,567324126,567324535⟩,
⟨126,982633372,982634081⟩,
⟨128,997378792,997379512⟩]
theorem checked13222 : checkPrefixCuts (2^48) 1736966145 9 Manual.Count131072.C013222.packed 128 cuts13222 = true := by
 decide +kernel
def pointBounds13222 : List (Nat × Nat × Nat) := [(1736984576,94608236107765,94608612994239),(1737039872,94608656291532,94609033178309),(1737095168,94609071600778,94609448487855)]
theorem point_links_checked13222 : (cuts13222.take 3).map (fun c => (1736966145-1+2*2^9*c.k,94608088967406+c.lower,94608465853774+c.upper)) = pointBounds13222 := by
 decide +kernel
def cuts13223 : List PrefixCut := [⟨52,403629232,403629520⟩,
⟨106,814051016,814051602⟩,
⟨128,988391344,988392056⟩]
theorem checked13223 : checkPrefixCuts (2^48) 1737097217 9 Manual.Count131072.C013223.packed 128 cuts13223 = true := by
 decide +kernel
def pointBounds13223 : List (Nat × Nat × Nat) := [(1737150464,94609489975430,94609866862806),(1737205760,94609900397214,94610277284888)]
theorem point_links_checked13223 : (cuts13223.take 2).map (fun c => (1737097217-1+2*2^9*c.k,94609086346198+c.lower,94609463233286+c.upper)) = pointBounds13223 := by
 decide +kernel
def cuts13224 : List PrefixCut := [⟨32,245141912,245142089⟩,
⟨86,679192632,679193120⟩,
⟨128,1002250601,1002251322⟩]
theorem checked13224 : checkPrefixCuts (2^48) 1737228289 9 Manual.Count131072.C013224.packed 128 cuts13224 = true := by
 decide +kernel
def pointBounds13224 : List (Nat × Nat × Nat) := [(1737261056,94610319879454,94610696767431),(1737316352,94610753930174,94611130818462)]
theorem point_links_checked13224 : (cuts13224.take 2).map (fun c => (1737228289-1+2*2^9*c.k,94610074737542+c.lower,94610451625342+c.upper)) = pointBounds13224 := by
 decide +kernel
def cuts13225 : List PrefixCut := [⟨12,94939309,94939376⟩,
⟨66,523939987,523940365⟩,
⟨120,952117043,952117728⟩,
⟨128,1016593525,1016594256⟩]
theorem checked13225 : checkPrefixCuts (2^48) 1737359361 9 Manual.Count131072.C013225.packed 128 cuts13225 = true := by
 decide +kernel
def pointBounds13225 : List (Nat × Nat × Nat) := [(1737371648,94611171927452,94611548816040),(1737426944,94611600928130,94611977817029),(1737482240,94612029105186,94612405994392)]
theorem point_links_checked13225 : (cuts13225.take 3).map (fun c => (1737359361-1+2*2^9*c.k,94611076988143+c.lower,94611453876664+c.upper)) = pointBounds13225 := by
 decide +kernel
def cuts13226 : List PrefixCut := [⟨46,352023060,352023314⟩,
⟨100,774341000,774341556⟩,
⟨128,994809309,994810023⟩]
theorem checked13226 : checkPrefixCuts (2^48) 1737490433 9 Manual.Count131072.C013226.packed 128 cuts13226 = true := by
 decide +kernel
def pointBounds13226 : List (Nat × Nat × Nat) := [(1737537536,94612445604728,94612822494234),(1737592832,94612867922668,94613244812476)]
theorem point_links_checked13226 : (cuts13226.take 2).map (fun c => (1737490433-1+2*2^9*c.k,94612093581668+c.lower,94612470470920+c.upper)) = pointBounds13226 := by
 decide +kernel
def cuts13227 : List PrefixCut := [⟨26,201188328,201188476⟩,
⟨80,619753873,619754326⟩,
⟨128,993600658,993601380⟩]
theorem checked13227 : checkPrefixCuts (2^48) 1737621505 9 Manual.Count131072.C013227.packed 128 cuts13227 = true := by
 decide +kernel
def pointBounds13227 : List (Nat × Nat × Nat) := [(1737648128,94613289579305,94613666469419),(1737703424,94613708144850,94614085035269)]
theorem point_links_checked13227 : (cuts13227.take 2).map (fun c => (1737621505-1+2*2^9*c.k,94613088390977+c.lower,94613465280943+c.upper)) = pointBounds13227 := by
 decide +kernel
def cuts13228 : List PrefixCut := [⟨6,48592826,48592859⟩,
⟨60,476850136,476850473⟩,
⟨114,902016376,902017018⟩,
⟨128,1009399076,1009399797⟩]
theorem checked13228 : checkPrefixCuts (2^48) 1737752577 9 Manual.Count131072.C013228.packed 128 cuts13228 = true := by
 decide +kernel
def pointBounds13228 : List (Nat × Nat × Nat) := [(1737758720,94614130584461,94614507475182),(1737814016,94614558841771,94614935732796),(1737869312,94614984008011,94615360899341)]
theorem point_links_checked13228 : (cuts13228.take 3).map (fun c => (1737752577-1+2*2^9*c.k,94614081991635+c.lower,94614458882323+c.upper)) = pointBounds13228 := by
 decide +kernel
def cuts13229 : List PrefixCut := [⟨40,309185987,309186208⟩,
⟨94,734487119,734487639⟩,
⟨128,1003006151,1003006862⟩]
theorem checked13229 : checkPrefixCuts (2^48) 1737883649 9 Manual.Count131072.C013229.packed 128 cuts13229 = true := by
 decide +kernel
def pointBounds13229 : List (Nat × Nat × Nat) := [(1737924608,94615400576698,94615777468328),(1737979904,94615825877830,94616202769759)]
theorem point_links_checked13229 : (cuts13229.take 2).map (fun c => (1737883649-1+2*2^9*c.k,94615091390711+c.lower,94615468282120+c.upper)) = pointBounds13229 := by
 decide +kernel
def cuts13230 : List PrefixCut := [⟨20,154015401,154015511⟩,
⟨74,587872682,587873104⟩,
⟨128,1002121061,1002121780⟩]
theorem checked13230 : checkPrefixCuts (2^48) 1738014721 9 Manual.Count131072.C013230.packed 128 cuts13230 = true := by
 decide +kernel
def pointBounds13230 : List (Nat × Nat × Nat) := [(1738035200,94616248412263,94616625304493),(1738090496,94616682269544,94617059162086),(1738145792,94617096517923,94617473410762)]
theorem point_links_checked13230 : (cuts13230.take 3).map (fun c => (1738014721-1+2*2^9*c.k,94616094396862+c.lower,94616471288982+c.upper)) = pointBounds13230 := by
 decide +kernel
def cuts13231 : List PrefixCut := [⟨54,414073382,414073676⟩,
⟨108,834125064,834125664⟩,
⟨128,990386042,990386752⟩]
theorem checked13231 : checkPrefixCuts (2^48) 1738145793 9 Manual.Count131072.C013231.packed 128 cuts13231 = true := by
 decide +kernel
def pointBounds13231 : List (Nat × Nat × Nat) := [(1738201088,94617510591305,94617887484438),(1738256384,94617930642987,94618307536426)]
theorem point_links_checked13231 : (cuts13231.take 2).map (fun c => (1738145793-1+2*2^9*c.k,94617096517923+c.lower,94617473410762+c.upper)) = pointBounds13231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000100
