import PlattAssemblyKernel
import PlattCertificates.Count131072.C025504
import PlattCertificates.Count131072.C025505
import PlattCertificates.Count131072.C025506
import PlattCertificates.Count131072.C025507
import PlattCertificates.Count131072.C025508
import PlattCertificates.Count131072.C025509
import PlattCertificates.Count131072.C025510
import PlattCertificates.Count131072.C025511
import PlattCertificates.Count131072.C025512
import PlattCertificates.Count131072.C025513
import PlattCertificates.Count131072.C025514
import PlattCertificates.Count131072.C025515
import PlattCertificates.Count131072.C025516
import PlattCertificates.Count131072.C025517
import PlattCertificates.Count131072.C025518
import PlattCertificates.Count131072.C025519
import PlattCertificates.Count131072.C025520
import PlattCertificates.Count131072.C025521
import PlattCertificates.Count131072.C025522
import PlattCertificates.Count131072.C025523
import PlattCertificates.Count131072.C025524
import PlattCertificates.Count131072.C025525
import PlattCertificates.Count131072.C025526
import PlattCertificates.Count131072.C025527
import PlattCertificates.Count131072.C025528
import PlattCertificates.Count131072.C025529
import PlattCertificates.Count131072.C025530
import PlattCertificates.Count131072.C025531
import PlattCertificates.Count131072.C025532
import PlattCertificates.Count131072.C025533
import PlattCertificates.Count131072.C025534
import PlattCertificates.Count131072.C025535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25504 : List PrefixCut := [⟨82,325305919,325306100⟩,
⟨128,502336811,502337087⟩]
theorem checked25504 : checkPrefixCuts (2^48) 3346792449 9 Manual.Count131072.C025504.packed 128 cuts25504 = true := by
 decide +kernel
def pointBounds25504 : List (Nat × Nat × Nat) := [(3346876416,103154323585692,103154705745936)]
theorem point_links_checked25504 : (cuts25504.take 1).map (fun c => (3346792449-1+2*2^9*c.k,103153998279773+c.lower,103154380439836+c.upper)) = pointBounds25504 := by
 decide +kernel
def cuts25505 : List PrefixCut := [⟨57,222105095,222105218⟩,
⟨128,499625915,499626194⟩]
theorem checked25505 : checkPrefixCuts (2^48) 3346923521 9 Manual.Count131072.C025505.packed 128 cuts25505 = true := by
 decide +kernel
def pointBounds25505 : List (Nat × Nat × Nat) := [(3346981888,103154722721679,103155104882141)]
theorem point_links_checked25505 : (cuts25505.take 1).map (fun c => (3346923521-1+2*2^9*c.k,103154500616584+c.lower,103154882776923+c.upper)) = pointBounds25505 := by
 decide +kernel
def cuts25506 : List PrefixCut := [⟨32,125302879,125302951⟩,
⟨128,499438185,499438466⟩]
theorem checked25506 : checkPrefixCuts (2^48) 3347054593 9 Manual.Count131072.C025506.packed 128 cuts25506 = true := by
 decide +kernel
def pointBounds25506 : List (Nat × Nat × Nat) := [(3347087360,103155125545378,103155507706068)]
theorem point_links_checked25506 : (cuts25506.take 1).map (fun c => (3347054593-1+2*2^9*c.k,103155000242499+c.lower,103155382403117+c.upper)) = pointBounds25506 := by
 decide +kernel
def cuts25507 : List PrefixCut := [⟨7,25227873,25227889⟩,
⟨110,432062536,432062783⟩,
⟨128,502025374,502025659⟩]
theorem checked25507 : checkPrefixCuts (2^48) 3347185665 9 Manual.Count131072.C025507.packed 128 cuts25507 = true := by
 decide +kernel
def pointBounds25507 : List (Nat × Nat × Nat) := [(3347192832,103155524908557,103155907069472),(3347298304,103155931743220,103156313904366)]
theorem point_links_checked25507 : (cuts25507.take 2).map (fun c => (3347185665-1+2*2^9*c.k,103155499680684+c.lower,103155881841583+c.upper)) = pointBounds25507 := by
 decide +kernel
def cuts25508 : List PrefixCut := [⟨85,335765829,335766018⟩,
⟨128,504948804,504949087⟩]
theorem checked25508 : checkPrefixCuts (2^48) 3347316737 9 Manual.Count131072.C025508.packed 128 cuts25508 = true := by
 decide +kernel
def pointBounds25508 : List (Nat × Nat × Nat) := [(3347403776,103156337471887,103156719633260)]
theorem point_links_checked25508 : (cuts25508.take 1).map (fun c => (3347316737-1+2*2^9*c.k,103156001706058+c.lower,103156383867242+c.upper)) = pointBounds25508 := by
 decide +kernel
def cuts25509 : List PrefixCut := [⟨60,233589949,233590080⟩,
⟨128,497025152,497025432⟩]
theorem checked25509 : checkPrefixCuts (2^48) 3347447809 9 Manual.Count131072.C025509.packed 128 cuts25509 = true := by
 decide +kernel
def pointBounds25509 : List (Nat × Nat × Nat) := [(3347509248,103156740244811,103157122406409)]
theorem point_links_checked25509 : (cuts25509.take 1).map (fun c => (3347447809-1+2*2^9*c.k,103156506654862+c.lower,103156888816329+c.upper)) = pointBounds25509 := by
 decide +kernel
def cuts25510 : List PrefixCut := [⟨35,138231922,138231997⟩,
⟨128,501798298,501798573⟩]
theorem checked25510 : checkPrefixCuts (2^48) 3347578881 9 Manual.Count131072.C025510.packed 128 cuts25510 = true := by
 decide +kernel
def pointBounds25510 : List (Nat × Nat × Nat) := [(3347614720,103157141911936,103157524073758)]
theorem point_links_checked25510 : (cuts25510.take 1).map (fun c => (3347578881-1+2*2^9*c.k,103157003680014+c.lower,103157385841761+c.upper)) = pointBounds25510 := by
 decide +kernel
def cuts25511 : List PrefixCut := [⟨10,39769703,39769725⟩,
⟨113,441243429,441243671⟩,
⟨128,499424528,499424802⟩]
theorem checked25511 : checkPrefixCuts (2^48) 3347709953 9 Manual.Count131072.C025511.packed 128 cuts25511 = true := by
 decide +kernel
def pointBounds25511 : List (Nat × Nat × Nat) := [(3347720192,103157545248015,103157927410059),(3347825664,103157946721741,103158328884005)]
theorem point_links_checked25511 : (cuts25511.take 2).map (fun c => (3347709953-1+2*2^9*c.k,103157505478312+c.lower,103157887640334+c.upper)) = pointBounds25511 := by
 decide +kernel
def cuts25512 : List PrefixCut := [⟨88,343363961,343364152⟩,
⟨128,503188196,503188477⟩]
theorem checked25512 : checkPrefixCuts (2^48) 3347841025 9 Manual.Count131072.C025512.packed 128 cuts25512 = true := by
 decide +kernel
def pointBounds25512 : List (Nat × Nat × Nat) := [(3347931136,103158348266801,103158730429288)]
theorem point_links_checked25512 : (cuts25512.take 1).map (fun c => (3347841025-1+2*2^9*c.k,103158004902840+c.lower,103158387065136+c.upper)) = pointBounds25512 := by
 decide +kernel
def cuts25513 : List PrefixCut := [⟨63,244650817,244650957⟩,
⟨128,500394165,500394450⟩]
theorem checked25513 : checkPrefixCuts (2^48) 3347972097 9 Manual.Count131072.C025513.packed 128 cuts25513 = true := by
 decide +kernel
def pointBounds25513 : List (Nat × Nat × Nat) := [(3348036608,103158752741853,103159134904570)]
theorem point_links_checked25513 : (cuts25513.take 1).map (fun c => (3347972097-1+2*2^9*c.k,103158508091036+c.lower,103158890253613+c.upper)) = pointBounds25513 := by
 decide +kernel
def cuts25514 : List PrefixCut := [⟨38,149139239,149139322⟩,
⟨128,501803769,501804055⟩]
theorem checked25514 : checkPrefixCuts (2^48) 3348103169 9 Manual.Count131072.C025514.packed 128 cuts25514 = true := by
 decide +kernel
def pointBounds25514 : List (Nat × Nat × Nat) := [(3348142080,103159157624440,103159539787385)]
theorem point_links_checked25514 : (cuts25514.take 1).map (fun c => (3348103169-1+2*2^9*c.k,103159008485201+c.lower,103159390648063+c.upper)) = pointBounds25514 := by
 decide +kernel
def cuts25515 : List PrefixCut := [⟨13,48842639,48842665⟩,
⟨116,456053529,456053780⟩,
⟨128,503381299,503381577⟩]
theorem checked25515 : checkPrefixCuts (2^48) 3348234241 9 Manual.Count131072.C025515.packed 128 cuts25515 = true := by
 decide +kernel
def pointBounds25515 : List (Nat × Nat × Nat) := [(3348247552,103159559131609,103159941294783),(3348353024,103159966342499,103160348505898)]
theorem point_links_checked25515 : (cuts25515.take 2).map (fun c => (3348234241-1+2*2^9*c.k,103159510288970+c.lower,103159892452118+c.upper)) = pointBounds25515 := by
 decide +kernel
def cuts25516 : List PrefixCut := [⟨91,356591836,356592037⟩,
⟨128,498906366,498906647⟩]
theorem checked25516 : checkPrefixCuts (2^48) 3348365313 9 Manual.Count131072.C025516.packed 128 cuts25516 = true := by
 decide +kernel
def pointBounds25516 : List (Nat × Nat × Nat) := [(3348458496,103160370262105,103160752425732)]
theorem point_links_checked25516 : (cuts25516.take 1).map (fun c => (3348365313-1+2*2^9*c.k,103160013670269+c.lower,103160395833695+c.upper)) = pointBounds25516 := by
 decide +kernel
def cuts25517 : List PrefixCut := [⟨66,262601060,262601203⟩,
⟨128,512336171,512336453⟩]
theorem checked25517 : checkPrefixCuts (2^48) 3348496385 9 Manual.Count131072.C025517.packed 128 cuts25517 = true := by
 decide +kernel
def pointBounds25517 : List (Nat × Nat × Nat) := [(3348563968,103160775177695,103161157341545)]
theorem point_links_checked25517 : (cuts25517.take 1).map (fun c => (3348496385-1+2*2^9*c.k,103160512576635+c.lower,103160894740342+c.upper)) = pointBounds25517 := by
 decide +kernel
def cuts25518 : List PrefixCut := [⟨41,159706899,159706990⟩,
⟨128,499623749,499624032⟩]
theorem checked25518 : checkPrefixCuts (2^48) 3348627457 9 Manual.Count131072.C025518.packed 128 cuts25518 = true := by
 decide +kernel
def pointBounds25518 : List (Nat × Nat × Nat) := [(3348669440,103161184619705,103161566783785)]
theorem point_links_checked25518 : (cuts25518.take 1).map (fun c => (3348627457-1+2*2^9*c.k,103161024912806+c.lower,103161407076795+c.upper)) = pointBounds25518 := by
 decide +kernel
def cuts25519 : List PrefixCut := [⟨16,61695120,61695155⟩,
⟨119,471867715,471867973⟩,
⟨128,506832656,506832932⟩]
theorem checked25519 : checkPrefixCuts (2^48) 3348758529 9 Manual.Count131072.C025519.packed 128 cuts25519 = true := by
 decide +kernel
def pointBounds25519 : List (Nat × Nat × Nat) := [(3348774912,103161586231675,103161968395982),(3348880384,103161996404270,103162378568800)]
theorem point_links_checked25519 : (cuts25519.take 2).map (fun c => (3348758529-1+2*2^9*c.k,103161524536555+c.lower,103161906700827+c.upper)) = pointBounds25519 := by
 decide +kernel
def cuts25520 : List PrefixCut := [⟨94,365865350,365865553⟩,
⟨128,498324002,498324277⟩]
theorem checked25520 : checkPrefixCuts (2^48) 3348889601 9 Manual.Count131072.C025520.packed 128 cuts25520 = true := by
 decide +kernel
def pointBounds25520 : List (Nat × Nat × Nat) := [(3348985856,103162397234561,103162779399312)]
theorem point_links_checked25520 : (cuts25520.take 1).map (fun c => (3348889601-1+2*2^9*c.k,103162031369211+c.lower,103162413533759+c.upper)) = pointBounds25520 := by
 decide +kernel
def cuts25521 : List PrefixCut := [⟨69,273317727,273317882⟩,
⟨128,503095132,503095420⟩]
theorem checked25521 : checkPrefixCuts (2^48) 3349020673 9 Manual.Count131072.C025521.packed 128 cuts25521 = true := by
 decide +kernel
def pointBounds25521 : List (Nat × Nat × Nat) := [(3349091328,103162803010940,103163185175918)]
theorem point_links_checked25521 : (cuts25521.take 1).map (fun c => (3349020673-1+2*2^9*c.k,103162529693213+c.lower,103162911858036+c.upper)) = pointBounds25521 := by
 decide +kernel
def cuts25522 : List PrefixCut := [⟨44,173464886,173464986⟩,
⟨128,503999831,504000112⟩]
theorem checked25522 : checkPrefixCuts (2^48) 3349151745 9 Manual.Count131072.C025522.packed 128 cuts25522 = true := by
 decide +kernel
def pointBounds25522 : List (Nat × Nat × Nat) := [(3349196800,103163206253231,103163588418442)]
theorem point_links_checked25522 : (cuts25522.take 1).map (fun c => (3349151745-1+2*2^9*c.k,103163032788345+c.lower,103163414953456+c.upper)) = pointBounds25522 := by
 decide +kernel
def cuts25523 : List PrefixCut := [⟨19,73030851,73030895⟩,
⟨122,469104467,469104737⟩,
⟨128,492298717,492299000⟩]
theorem checked25523 : checkPrefixCuts (2^48) 3349282817 9 Manual.Count131072.C025523.packed 128 cuts25523 = true := by
 decide +kernel
def pointBounds25523 : List (Nat × Nat × Nat) := [(3349302272,103163609819027,103163991984463),(3349407744,103164005892643,103164388058305)]
theorem point_links_checked25523 : (cuts25523.take 2).map (fun c => (3349282817-1+2*2^9*c.k,103163536788176+c.lower,103163918953568+c.upper)) = pointBounds25523 := by
 decide +kernel
def cuts25524 : List PrefixCut := [⟨97,385472315,385472531⟩,
⟨128,508498344,508498625⟩]
theorem checked25524 : checkPrefixCuts (2^48) 3349413889 9 Manual.Count131072.C025524.packed 128 cuts25524 = true := by
 decide +kernel
def pointBounds25524 : List (Nat × Nat × Nat) := [(3349513216,103164414559208,103164796725099)]
theorem point_links_checked25524 : (cuts25524.take 1).map (fun c => (3349413889-1+2*2^9*c.k,103164029086893+c.lower,103164411252568+c.upper)) = pointBounds25524 := by
 decide +kernel
def cuts25525 : List PrefixCut := [⟨72,287980579,287980732⟩,
⟨128,506797822,506798098⟩]
theorem checked25525 : checkPrefixCuts (2^48) 3349544961 9 Manual.Count131072.C025525.packed 128 cuts25525 = true := by
 decide +kernel
def pointBounds25525 : List (Nat × Nat × Nat) := [(3349618688,103164825565816,103165207731925)]
theorem point_links_checked25525 : (cuts25525.take 1).map (fun c => (3349544961-1+2*2^9*c.k,103164537585237+c.lower,103164919751193+c.upper)) = pointBounds25525 := by
 decide +kernel
def cuts25526 : List PrefixCut := [⟨47,186966479,186966581⟩,
⟨128,504593209,504593491⟩]
theorem checked25526 : checkPrefixCuts (2^48) 3349676033 9 Manual.Count131072.C025526.packed 128 cuts25526 = true := by
 decide +kernel
def pointBounds25526 : List (Nat × Nat × Nat) := [(3349724160,103165231349538,103165613515872)]
theorem point_links_checked25526 : (cuts25526.take 1).map (fun c => (3349676033-1+2*2^9*c.k,103165044383059+c.lower,103165426549291+c.upper)) = pointBounds25526 := by
 decide +kernel
def cuts25527 : List PrefixCut := [⟨22,89320603,89320655⟩,
⟨125,494994840,494995118⟩,
⟨128,507346361,507346645⟩]
theorem checked25527 : checkPrefixCuts (2^48) 3349807105 9 Manual.Count131072.C025527.packed 128 cuts25527 = true := by
 decide +kernel
def pointBounds25527 : List (Nat × Nat × Nat) := [(3349829632,103165638296871,103166020463437),(3349935104,103166043971108,103166426137900)]
theorem point_links_checked25527 : (cuts25527.take 2).map (fun c => (3349807105-1+2*2^9*c.k,103165548976268+c.lower,103165931142782+c.upper)) = pointBounds25527 := by
 decide +kernel
def cuts25528 : List PrefixCut := [⟨100,391881450,391881672⟩,
⟨128,500856668,500856950⟩]
theorem checked25528 : checkPrefixCuts (2^48) 3349938177 9 Manual.Count131072.C025528.packed 128 cuts25528 = true := by
 decide +kernel
def pointBounds25528 : List (Nat × Nat × Nat) := [(3350040576,103166448204079,103166830371099)]
theorem point_links_checked25528 : (cuts25528.take 1).map (fun c => (3349938177-1+2*2^9*c.k,103166056322629+c.lower,103166438489427+c.upper)) = pointBounds25528 := by
 decide +kernel
def cuts25529 : List PrefixCut := [⟨75,296337307,296337472⟩,
⟨128,501677353,501677632⟩]
theorem checked25529 : checkPrefixCuts (2^48) 3350069249 9 Manual.Count131072.C025529.packed 128 cuts25529 = true := by
 decide +kernel
def pointBounds25529 : List (Nat × Nat × Nat) := [(3350146048,103166853516604,103167235683849)]
theorem point_links_checked25529 : (cuts25529.take 1).map (fun c => (3350069249-1+2*2^9*c.k,103166557179297+c.lower,103166939346377+c.upper)) = pointBounds25529 := by
 decide +kernel
def cuts25530 : List PrefixCut := [⟨50,193742491,193742599⟩,
⟨128,500397405,500397679⟩]
theorem checked25530 : checkPrefixCuts (2^48) 3350200321 9 Manual.Count131072.C025530.packed 128 cuts25530 = true := by
 decide +kernel
def pointBounds25530 : List (Nat × Nat × Nat) := [(3350251520,103167252599141,103167634766608)]
theorem point_links_checked25530 : (cuts25530.take 1).map (fun c => (3350200321-1+2*2^9*c.k,103167058856650+c.lower,103167441024009+c.upper)) = pointBounds25530 := by
 decide +kernel
def cuts25531 : List PrefixCut := [⟨25,100900474,100900532⟩,
⟨128,503906427,503906709⟩]
theorem checked25531 : checkPrefixCuts (2^48) 3350331393 9 Manual.Count131072.C025531.packed 128 cuts25531 = true := by
 decide +kernel
def pointBounds25531 : List (Nat × Nat × Nat) := [(3350356992,103167660154529,103168042322220),(3350462464,103168063160482,103168445328397)]
theorem point_links_checked25531 : (cuts25531.take 2).map (fun c => (3350331393-1+2*2^9*c.k,103167559254055+c.lower,103167941421688+c.upper)) = pointBounds25531 := by
 decide +kernel
def cuts25532 : List PrefixCut := [⟨103,410050041,410050269⟩,
⟨128,508171138,508171425⟩]
theorem checked25532 : checkPrefixCuts (2^48) 3350462465 9 Manual.Count131072.C025532.packed 128 cuts25532 = true := by
 decide +kernel
def pointBounds25532 : List (Nat × Nat × Nat) := [(3350567936,103168473210523,103168855378666)]
theorem point_links_checked25532 : (cuts25532.take 1).map (fun c => (3350462465-1+2*2^9*c.k,103168063160482+c.lower,103168445328397+c.upper)) = pointBounds25532 := by
 decide +kernel
def cuts25533 : List PrefixCut := [⟨78,302423291,302423458⟩,
⟨128,498994590,498994866⟩]
theorem checked25533 : checkPrefixCuts (2^48) 3350593537 9 Manual.Count131072.C025533.packed 128 cuts25533 = true := by
 decide +kernel
def pointBounds25533 : List (Nat × Nat × Nat) := [(3350673408,103168873754911,103169255923280)]
theorem point_links_checked25533 : (cuts25533.take 1).map (fun c => (3350593537-1+2*2^9*c.k,103168571331620+c.lower,103168953499822+c.upper)) = pointBounds25533 := by
 decide +kernel
def cuts25534 : List PrefixCut := [⟨53,205472576,205472691⟩,
⟨128,500487126,500487405⟩]
theorem checked25534 : checkPrefixCuts (2^48) 3350724609 9 Manual.Count131072.C025534.packed 128 cuts25534 = true := by
 decide +kernel
def pointBounds25534 : List (Nat × Nat × Nat) := [(3350778880,103169275798786,103169657967379)]
theorem point_links_checked25534 : (cuts25534.take 1).map (fun c => (3350724609-1+2*2^9*c.k,103169070326210+c.lower,103169452494688+c.upper)) = pointBounds25534 := by
 decide +kernel
def cuts25535 : List PrefixCut := [⟨28,107184699,107184764⟩,
⟨128,500467509,500467795⟩]
theorem checked25535 : checkPrefixCuts (2^48) 3350855681 9 Manual.Count131072.C025535.packed 128 cuts25535 = true := by
 decide +kernel
def pointBounds25535 : List (Nat × Nat × Nat) := [(3350884352,103169677998035,103170060166857)]
theorem point_links_checked25535 : (cuts25535.take 1).map (fun c => (3350855681-1+2*2^9*c.k,103169570813336+c.lower,103169952982093+c.upper)) = pointBounds25535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000172
