import PlattAssemblyKernel
import PlattCertificates.Count131072.C031504
import PlattCertificates.Count131072.C031505
import PlattCertificates.Count131072.C031506
import PlattCertificates.Count131072.C031507
import PlattCertificates.Count131072.C031508
import PlattCertificates.Count131072.C031509
import PlattCertificates.Count131072.C031510
import PlattCertificates.Count131072.C031511
import PlattCertificates.Count131072.C031512
import PlattCertificates.Count131072.C031513
import PlattCertificates.Count131072.C031514
import PlattCertificates.Count131072.C031515
import PlattCertificates.Count131072.C031516
import PlattCertificates.Count131072.C031517
import PlattCertificates.Count131072.C031518
import PlattCertificates.Count131072.C031519
import PlattCertificates.Count131072.C031520
import PlattCertificates.Count131072.C031521
import PlattCertificates.Count131072.C031522
import PlattCertificates.Count131072.C031523
import PlattCertificates.Count131072.C031524
import PlattCertificates.Count131072.C031525
import PlattCertificates.Count131072.C031526
import PlattCertificates.Count131072.C031527
import PlattCertificates.Count131072.C031528
import PlattCertificates.Count131072.C031529
import PlattCertificates.Count131072.C031530
import PlattCertificates.Count131072.C031531
import PlattCertificates.Count131072.C031532
import PlattCertificates.Count131072.C031533
import PlattCertificates.Count131072.C031534
import PlattCertificates.Count131072.C031535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts31504 : List PrefixCut := [⟨65,203210424,203210535⟩,
⟨128,403012709,403012934⟩]
theorem checked31504 : checkPrefixCuts (2^48) 4133224449 9 Manual.Count131072.C031504.packed 128 cuts31504 = true := by
 decide +kernel
def pointBounds31504 : List (Nat × Nat × Nat) := [(4133291008,105850095225469,105850478897010)]
theorem point_links_checked31504 : (cuts31504.take 1).map (fun c => (4133224449-1+2*2^9*c.k,105849892015045+c.lower,105850275686475+c.upper)) = pointBounds31504 := by
 decide +kernel
def cuts31505 : List PrefixCut := [⟨64,203544482,203544595⟩,
⟨128,402591377,402591599⟩]
theorem checked31505 : checkPrefixCuts (2^48) 4133355521 9 Manual.Count131072.C031505.packed 128 cuts31505 = true := by
 decide +kernel
def pointBounds31505 : List (Nat × Nat × Nat) := [(4133421056,105850498572236,105850882244004)]
theorem point_links_checked31505 : (cuts31505.take 1).map (fun c => (4133355521-1+2*2^9*c.k,105850295027754+c.lower,105850678699409+c.upper)) = pointBounds31505 := by
 decide +kernel
def cuts31506 : List PrefixCut := [⟨63,200609966,200610079⟩,
⟨128,402510555,402510785⟩]
theorem checked31506 : checkPrefixCuts (2^48) 4133486593 9 Manual.Count131072.C031506.packed 128 cuts31506 = true := by
 decide +kernel
def pointBounds31506 : List (Nat × Nat × Nat) := [(4133551104,105850898229097,105851281901087)]
theorem point_links_checked31506 : (cuts31506.take 1).map (fun c => (4133486593-1+2*2^9*c.k,105850697619131+c.lower,105851081291008+c.upper)) = pointBounds31506 := by
 decide +kernel
def cuts31507 : List PrefixCut := [⟨62,193453807,193453922⟩,
⟨128,403995760,403995994⟩]
theorem checked31507 : checkPrefixCuts (2^48) 4133617665 9 Manual.Count131072.C031507.packed 128 cuts31507 = true := by
 decide +kernel
def pointBounds31507 : List (Nat × Nat × Nat) := [(4133681152,105851293583493,105851677255715)]
theorem point_links_checked31507 : (cuts31507.take 1).map (fun c => (4133617665-1+2*2^9*c.k,105851100129686+c.lower,105851483801793+c.upper)) = pointBounds31507 := by
 decide +kernel
def cuts31508 : List PrefixCut := [⟨61,190247394,190247495⟩,
⟨128,401123116,401123338⟩]
theorem checked31508 : checkPrefixCuts (2^48) 4133748737 9 Manual.Count131072.C031508.packed 128 cuts31508 = true := by
 decide +kernel
def pointBounds31508 : List (Nat × Nat × Nat) := [(4133811200,105851694372840,105852078045282)]
theorem point_links_checked31508 : (cuts31508.take 1).map (fun c => (4133748737-1+2*2^9*c.k,105851504125446+c.lower,105851887797787+c.upper)) = pointBounds31508 := by
 decide +kernel
def cuts31509 : List PrefixCut := [⟨60,188402976,188403084⟩,
⟨128,398795452,398795682⟩]
theorem checked31509 : checkPrefixCuts (2^48) 4133879809 9 Manual.Count131072.C031509.packed 128 cuts31509 = true := by
 decide +kernel
def pointBounds31509 : List (Nat × Nat × Nat) := [(4133941248,105852093651538,105852477324209)]
theorem point_links_checked31509 : (cuts31509.take 1).map (fun c => (4133879809-1+2*2^9*c.k,105851905248562+c.lower,105852288921125+c.upper)) = pointBounds31509 := by
 decide +kernel
def cuts31510 : List PrefixCut := [⟨59,185877824,185877926⟩,
⟨128,404025434,404025659⟩]
theorem checked31510 : checkPrefixCuts (2^48) 4134010881 9 Manual.Count131072.C031510.packed 128 cuts31510 = true := by
 decide +kernel
def pointBounds31510 : List (Nat × Nat × Nat) := [(4134071296,105852489921838,105852873594733)]
theorem point_links_checked31510 : (cuts31510.take 1).map (fun c => (4134010881-1+2*2^9*c.k,105852304044014+c.lower,105852687716807+c.upper)) = pointBounds31510 := by
 decide +kernel
def cuts31511 : List PrefixCut := [⟨58,185599595,185599695⟩,
⟨128,410344440,410344665⟩]
theorem checked31511 : checkPrefixCuts (2^48) 4134141953 9 Manual.Count131072.C031511.packed 128 cuts31511 = true := by
 decide +kernel
def pointBounds31511 : List (Nat × Nat × Nat) := [(4134201344,105852893669043,105853277342161)]
theorem point_links_checked31511 : (cuts31511.take 1).map (fun c => (4134141953-1+2*2^9*c.k,105852708069448+c.lower,105853091742466+c.upper)) = pointBounds31511 := by
 decide +kernel
def cuts31512 : List PrefixCut := [⟨57,179193944,179194046⟩,
⟨128,403727464,403727693⟩]
theorem checked31512 : checkPrefixCuts (2^48) 4134273025 9 Manual.Count131072.C031512.packed 128 cuts31512 = true := by
 decide +kernel
def pointBounds31512 : List (Nat × Nat × Nat) := [(4134331392,105853297607832,105853681281177)]
theorem point_links_checked31512 : (cuts31512.take 1).map (fun c => (4134273025-1+2*2^9*c.k,105853118413888+c.lower,105853502087131+c.upper)) = pointBounds31512 := by
 decide +kernel
def cuts31513 : List PrefixCut := [⟨56,174899189,174899290⟩,
⟨128,403714656,403714884⟩]
theorem checked31513 : checkPrefixCuts (2^48) 4134404097 9 Manual.Count131072.C031513.packed 128 cuts31513 = true := by
 decide +kernel
def pointBounds31513 : List (Nat × Nat × Nat) := [(4134461440,105853697040541,105854080714114)]
theorem point_links_checked31513 : (cuts31513.take 1).map (fun c => (4134404097-1+2*2^9*c.k,105853522141352+c.lower,105853905814824+c.upper)) = pointBounds31513 := by
 decide +kernel
def cuts31514 : List PrefixCut := [⟨55,177616838,177616936⟩,
⟨128,408943928,408944155⟩]
theorem checked31514 : checkPrefixCuts (2^48) 4134535169 9 Manual.Count131072.C031514.packed 128 cuts31514 = true := by
 decide +kernel
def pointBounds31514 : List (Nat × Nat × Nat) := [(4134591488,105854103472846,105854487146644)]
theorem point_links_checked31514 : (cuts31514.take 1).map (fun c => (4134535169-1+2*2^9*c.k,105853925856008+c.lower,105854309529708+c.upper)) = pointBounds31514 := by
 decide +kernel
def cuts31515 : List PrefixCut := [⟨54,170531286,170531385⟩,
⟨128,405799453,405799679⟩]
theorem checked31515 : checkPrefixCuts (2^48) 4134666241 9 Manual.Count131072.C031515.packed 128 cuts31515 = true := by
 decide +kernel
def pointBounds31515 : List (Nat × Nat × Nat) := [(4134721536,105854505331222,105854889005248)]
theorem point_links_checked31515 : (cuts31515.take 1).map (fun c => (4134666241-1+2*2^9*c.k,105854334799936+c.lower,105854718473863+c.upper)) = pointBounds31515 := by
 decide +kernel
def cuts31516 : List PrefixCut := [⟨53,167598689,167598781⟩,
⟨128,400953400,400953624⟩]
theorem checked31516 : checkPrefixCuts (2^48) 4134797313 9 Manual.Count131072.C031516.packed 128 cuts31516 = true := by
 decide +kernel
def pointBounds31516 : List (Nat × Nat × Nat) := [(4134851584,105854908198078,105855291872323)]
theorem point_links_checked31516 : (cuts31516.take 1).map (fun c => (4134797313-1+2*2^9*c.k,105854740599389+c.lower,105855124273542+c.upper)) = pointBounds31516 := by
 decide +kernel
def cuts31517 : List PrefixCut := [⟨52,161603068,161603160⟩,
⟨128,399443094,399443319⟩]
theorem checked31517 : checkPrefixCuts (2^48) 4134928385 9 Manual.Count131072.C031517.packed 128 cuts31517 = true := by
 decide +kernel
def pointBounds31517 : List (Nat × Nat × Nat) := [(4134981632,105855303155857,105855686830326)]
theorem point_links_checked31517 : (cuts31517.take 1).map (fun c => (4134928385-1+2*2^9*c.k,105855141552789+c.lower,105855525227166+c.upper)) = pointBounds31517 := by
 decide +kernel
def cuts31518 : List PrefixCut := [⟨51,159964279,159964367⟩,
⟨128,399498498,399498715⟩]
theorem checked31518 : checkPrefixCuts (2^48) 4135059457 9 Manual.Count131072.C031518.packed 128 cuts31518 = true := by
 decide +kernel
def pointBounds31518 : List (Nat × Nat × Nat) := [(4135111680,105855700960162,105856084634852)]
theorem point_links_checked31518 : (cuts31518.take 1).map (fun c => (4135059457-1+2*2^9*c.k,105855540995883+c.lower,105855924670485+c.upper)) = pointBounds31518 := by
 decide +kernel
def cuts31519 : List PrefixCut := [⟨50,154445743,154445836⟩,
⟨128,400710989,400711226⟩]
theorem checked31519 : checkPrefixCuts (2^48) 4135190529 9 Manual.Count131072.C031519.packed 128 cuts31519 = true := by
 decide +kernel
def pointBounds31519 : List (Nat × Nat × Nat) := [(4135241728,105856094940124,105856478615036)]
theorem point_links_checked31519 : (cuts31519.take 1).map (fun c => (4135190529-1+2*2^9*c.k,105855940494381+c.lower,105856324169200+c.upper)) = pointBounds31519 := by
 decide +kernel
def cuts31520 : List PrefixCut := [⟨49,155461848,155461939⟩,
⟨128,403080605,403080838⟩]
theorem checked31520 : checkPrefixCuts (2^48) 4135321601 9 Manual.Count131072.C031520.packed 128 cuts31520 = true := by
 decide +kernel
def pointBounds31520 : List (Nat × Nat × Nat) := [(4135371776,105856496667218,105856880342365)]
theorem point_links_checked31520 : (cuts31520.take 1).map (fun c => (4135321601-1+2*2^9*c.k,105856341205370+c.lower,105856724880426+c.upper)) = pointBounds31520 := by
 decide +kernel
def cuts31521 : List PrefixCut := [⟨48,154231793,154231880⟩,
⟨128,404905572,404905798⟩]
theorem checked31521 : checkPrefixCuts (2^48) 4135452673 9 Manual.Count131072.C031521.packed 128 cuts31521 = true := by
 decide +kernel
def pointBounds31521 : List (Nat × Nat × Nat) := [(4135501824,105856898517768,105857282193144)]
theorem point_links_checked31521 : (cuts31521.take 1).map (fun c => (4135452673-1+2*2^9*c.k,105856744285975+c.lower,105857127961264+c.upper)) = pointBounds31521 := by
 decide +kernel
def cuts31522 : List PrefixCut := [⟨47,146536016,146536101⟩,
⟨128,400128436,400128669⟩]
theorem checked31522 : checkPrefixCuts (2^48) 4135583745 9 Manual.Count131072.C031522.packed 128 cuts31522 = true := by
 decide +kernel
def pointBounds31522 : List (Nat × Nat × Nat) := [(4135631872,105857295727563,105857679403163)]
theorem point_links_checked31522 : (cuts31522.take 1).map (fun c => (4135583745-1+2*2^9*c.k,105857149191547+c.lower,105857532867062+c.upper)) = pointBounds31522 := by
 decide +kernel
def cuts31523 : List PrefixCut := [⟨46,144149311,144149390⟩,
⟨128,401476919,401477140⟩]
theorem checked31523 : checkPrefixCuts (2^48) 4135714817 9 Manual.Count131072.C031523.packed 128 cuts31523 = true := by
 decide +kernel
def pointBounds31523 : List (Nat × Nat × Nat) := [(4135761920,105857693469294,105858077145121)]
theorem point_links_checked31523 : (cuts31523.take 1).map (fun c => (4135714817-1+2*2^9*c.k,105857549319983+c.lower,105857932995731+c.upper)) = pointBounds31523 := by
 decide +kernel
def cuts31524 : List PrefixCut := [⟨45,143804471,143804552⟩,
⟨128,403505941,403506165⟩]
theorem checked31524 : checkPrefixCuts (2^48) 4135845889 9 Manual.Count131072.C031524.packed 128 cuts31524 = true := by
 decide +kernel
def pointBounds31524 : List (Nat × Nat × Nat) := [(4135891968,105858094601373,105858478277423)]
theorem point_links_checked31524 : (cuts31524.take 1).map (fun c => (4135845889-1+2*2^9*c.k,105857950796902+c.lower,105858334472871+c.upper)) = pointBounds31524 := by
 decide +kernel
def cuts31525 : List PrefixCut := [⟨44,137198620,137198698⟩,
⟨128,403629186,403629410⟩]
theorem checked31525 : checkPrefixCuts (2^48) 4135976961 9 Manual.Count131072.C031525.packed 128 cuts31525 = true := by
 decide +kernel
def pointBounds31525 : List (Nat × Nat × Nat) := [(4136022016,105858491501463,105858875177734)]
theorem point_links_checked31525 : (cuts31525.take 1).map (fun c => (4135976961-1+2*2^9*c.k,105858354302843+c.lower,105858737979036+c.upper)) = pointBounds31525 := by
 decide +kernel
def cuts31526 : List PrefixCut := [⟨43,136717905,136717984⟩,
⟨128,400758295,400758525⟩]
theorem checked31526 : checkPrefixCuts (2^48) 4136108033 9 Manual.Count131072.C031526.packed 128 cuts31526 = true := by
 decide +kernel
def pointBounds31526 : List (Nat × Nat × Nat) := [(4136152064,105858894649934,105859278326430)]
theorem point_links_checked31526 : (cuts31526.take 1).map (fun c => (4136108033-1+2*2^9*c.k,105858757932029+c.lower,105859141608446+c.upper)) = pointBounds31526 := by
 decide +kernel
def cuts31527 : List PrefixCut := [⟨42,131133458,131133527⟩,
⟨128,399860944,399861161⟩]
theorem checked31527 : checkPrefixCuts (2^48) 4136239105 9 Manual.Count131072.C031527.packed 128 cuts31527 = true := by
 decide +kernel
def pointBounds31527 : List (Nat × Nat × Nat) := [(4136282112,105859289823782,105859673500498)]
theorem point_links_checked31527 : (cuts31527.take 1).map (fun c => (4136239105-1+2*2^9*c.k,105859158690324+c.lower,105859542366971+c.upper)) = pointBounds31527 := by
 decide +kernel
def cuts31528 : List PrefixCut := [⟨41,129428101,129428176⟩,
⟨128,400188523,400188758⟩]
theorem checked31528 : checkPrefixCuts (2^48) 4136370177 9 Manual.Count131072.C031528.packed 128 cuts31528 = true := by
 decide +kernel
def pointBounds31528 : List (Nat × Nat × Nat) := [(4136412160,105859687979369,105860071656308)]
theorem point_links_checked31528 : (cuts31528.take 1).map (fun c => (4136370177-1+2*2^9*c.k,105859558551268+c.lower,105859942228132+c.upper)) = pointBounds31528 := by
 decide +kernel
def cuts31529 : List PrefixCut := [⟨40,125409281,125409353⟩,
⟨128,400107758,400107988⟩]
theorem checked31529 : checkPrefixCuts (2^48) 4136501249 9 Manual.Count131072.C031529.packed 128 cuts31529 = true := by
 decide +kernel
def pointBounds31529 : List (Nat × Nat × Nat) := [(4136542208,105860084149072,105860467826243)]
theorem point_links_checked31529 : (cuts31529.take 1).map (fun c => (4136501249-1+2*2^9*c.k,105859958739791+c.lower,105860342416890+c.upper)) = pointBounds31529 := by
 decide +kernel
def cuts31530 : List PrefixCut := [⟨39,124316623,124316693⟩,
⟨128,401455997,401456227⟩]
theorem checked31530 : checkPrefixCuts (2^48) 4136632321 9 Manual.Count131072.C031530.packed 128 cuts31530 = true := by
 decide +kernel
def pointBounds31530 : List (Nat × Nat × Nat) := [(4136672256,105860483164172,105860866841571)]
theorem point_links_checked31530 : (cuts31530.take 1).map (fun c => (4136632321-1+2*2^9*c.k,105860358847549+c.lower,105860742524878+c.upper)) = pointBounds31530 := by
 decide +kernel
def cuts31531 : List PrefixCut := [⟨38,118801290,118801361⟩,
⟨128,408111174,408111413⟩]
theorem checked31531 : checkPrefixCuts (2^48) 4136763393 9 Manual.Count131072.C031531.packed 128 cuts31531 = true := by
 decide +kernel
def pointBounds31531 : List (Nat × Nat × Nat) := [(4136802304,105860879104836,105861262782466)]
theorem point_links_checked31531 : (cuts31531.take 1).map (fun c => (4136763393-1+2*2^9*c.k,105860760303546+c.lower,105861143981105+c.upper)) = pointBounds31531 := by
 decide +kernel
def cuts31532 : List PrefixCut := [⟨37,118117145,118117208⟩,
⟨128,398640946,398641174⟩]
theorem checked31532 : checkPrefixCuts (2^48) 4136894465 9 Manual.Count131072.C031532.packed 128 cuts31532 = true := by
 decide +kernel
def pointBounds31532 : List (Nat × Nat × Nat) := [(4136932352,105861286531865,105861670209726)]
theorem point_links_checked31532 : (cuts31532.take 1).map (fun c => (4136894465-1+2*2^9*c.k,105861168414720+c.lower,105861552092518+c.upper)) = pointBounds31532 := by
 decide +kernel
def cuts31533 : List PrefixCut := [⟨36,113146672,113146733⟩,
⟨128,397539685,397539914⟩]
theorem checked31533 : checkPrefixCuts (2^48) 4137025537 9 Manual.Count131072.C031533.packed 128 cuts31533 = true := by
 decide +kernel
def pointBounds31533 : List (Nat × Nat × Nat) := [(4137062400,105861680202338,105862063880425)]
theorem point_links_checked31533 : (cuts31533.take 1).map (fun c => (4137025537-1+2*2^9*c.k,105861567055666+c.lower,105861950733692+c.upper)) = pointBounds31533 := by
 decide +kernel
def cuts31534 : List PrefixCut := [⟨35,107836327,107836386⟩,
⟨128,402221404,402221633⟩]
theorem checked31534 : checkPrefixCuts (2^48) 4137156609 9 Manual.Count131072.C031534.packed 128 cuts31534 = true := by
 decide +kernel
def pointBounds31534 : List (Nat × Nat × Nat) := [(4137192448,105862072431678,105862456109992)]
theorem point_links_checked31534 : (cuts31534.take 1).map (fun c => (4137156609-1+2*2^9*c.k,105861964595351+c.lower,105862348273606+c.upper)) = pointBounds31534 := by
 decide +kernel
def cuts31535 : List PrefixCut := [⟨34,105315693,105315755⟩,
⟨128,404521799,404522030⟩]
theorem checked31535 : checkPrefixCuts (2^48) 4137287681 9 Manual.Count131072.C031535.packed 128 cuts31535 = true := by
 decide +kernel
def pointBounds31535 : List (Nat × Nat × Nat) := [(4137322496,105862472132448,105862855810994)]
theorem point_links_checked31535 : (cuts31535.take 1).map (fun c => (4137287681-1+2*2^9*c.k,105862366816755+c.lower,105862750495239+c.upper)) = pointBounds31535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000047
