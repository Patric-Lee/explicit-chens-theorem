import PlattAssemblyKernel
import PlattCertificates.Count131072.C014000
import PlattCertificates.Count131072.C014001
import PlattCertificates.Count131072.C014002
import PlattCertificates.Count131072.C014003
import PlattCertificates.Count131072.C014004
import PlattCertificates.Count131072.C014005
import PlattCertificates.Count131072.C014006
import PlattCertificates.Count131072.C014007
import PlattCertificates.Count131072.C014008
import PlattCertificates.Count131072.C014009
import PlattCertificates.Count131072.C014010
import PlattCertificates.Count131072.C014011
import PlattCertificates.Count131072.C014012
import PlattCertificates.Count131072.C014013
import PlattCertificates.Count131072.C014014
import PlattCertificates.Count131072.C014015
import PlattCertificates.Count131072.C014016
import PlattCertificates.Count131072.C014017
import PlattCertificates.Count131072.C014018
import PlattCertificates.Count131072.C014019
import PlattCertificates.Count131072.C014020
import PlattCertificates.Count131072.C014021
import PlattCertificates.Count131072.C014022
import PlattCertificates.Count131072.C014023
import PlattCertificates.Count131072.C014024
import PlattCertificates.Count131072.C014025
import PlattCertificates.Count131072.C014026
import PlattCertificates.Count131072.C014027
import PlattCertificates.Count131072.C014028
import PlattCertificates.Count131072.C014029
import PlattCertificates.Count131072.C014030
import PlattCertificates.Count131072.C014031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14000 : List PrefixCut := [⟨46,338419462,338419698⟩,
⟨103,759633242,759633767⟩,
⟨128,947277190,947277844⟩]
theorem checked14000 : checkPrefixCuts (2^48) 1838940161 9 Manual.Count131072.C014000.packed 128 cuts14000 = true := by
 decide +kernel
def pointBounds14000 : List (Nat × Nat × Nat) := [(1838987264,95362224308695,95362601726981),(1839045632,95362645522475,95363022941050)]
theorem point_links_checked14000 : (cuts14000.take 2).map (fun c => (1838940161-1+2*2^9*c.k,95361885889233+c.lower,95362263307283+c.upper)) = pointBounds14000 := by
 decide +kernel
def cuts14001 : List PrefixCut := [⟨32,231872803,231872964⟩,
⟨89,656885889,656886345⟩,
⟨128,940322436,940323088⟩]
theorem checked14001 : checkPrefixCuts (2^48) 1839071233 9 Manual.Count131072.C014001.packed 128 cuts14001 = true := by
 decide +kernel
def pointBounds14001 : List (Nat × Nat × Nat) := [(1839104000,95363065039226,95363442458091),(1839162368,95363490052312,95363867471472)]
theorem point_links_checked14001 : (cuts14001.take 2).map (fun c => (1839071233-1+2*2^9*c.k,95362833166423+c.lower,95363210585127+c.upper)) = pointBounds14001 := by
 decide +kernel
def cuts14002 : List PrefixCut := [⟨18,125187590,125187678⟩,
⟨75,547113012,547113395⟩,
⟨128,930920249,930920902⟩]
theorem checked14002 : checkPrefixCuts (2^48) 1839202305 9 Manual.Count131072.C014002.packed 128 cuts14002 = true := by
 decide +kernel
def pointBounds14002 : List (Nat × Nat × Nat) := [(1839220736,95363898676449,95364276095893),(1839279104,95364320601871,95364698021610)]
theorem point_links_checked14002 : (cuts14002.take 2).map (fun c => (1839202305-1+2*2^9*c.k,95363773488859+c.lower,95364150908215+c.upper)) = pointBounds14002 := by
 decide +kernel
def cuts14003 : List PrefixCut := [⟨4,29534931,29534953⟩,
⟨61,450821511,450821824⟩,
⟨118,860311830,860312429⟩,
⟨128,935138831,935139481⟩]
theorem checked14003 : checkPrefixCuts (2^48) 1839333377 9 Manual.Count131072.C014003.packed 128 cuts14003 = true := by
 decide +kernel
def pointBounds14003 : List (Nat × Nat × Nat) := [(1839337472,95364733944039,95365111364070),(1839395840,95365155230619,95365532650941),(1839454208,95365564720938,95365942141546)]
theorem point_links_checked14003 : (cuts14003.take 3).map (fun c => (1839333377-1+2*2^9*c.k,95364704409108+c.lower,95365081829117+c.upper)) = pointBounds14003 := by
 decide +kernel
def cuts14004 : List PrefixCut := [⟨47,343984527,343984761⟩,
⟨104,760793608,760794134⟩,
⟨128,943028690,943029343⟩]
theorem checked14004 : checkPrefixCuts (2^48) 1839464449 9 Manual.Count131072.C014004.packed 128 cuts14004 = true := by
 decide +kernel
def pointBounds14004 : List (Nat × Nat × Nat) := [(1839512576,95365983532466,95366360953359),(1839570944,95366400341547,95366777762732)]
theorem point_links_checked14004 : (cuts14004.take 2).map (fun c => (1839464449-1+2*2^9*c.k,95365639547939+c.lower,95366016968598+c.upper)) = pointBounds14004 := by
 decide +kernel
def cuts14005 : List PrefixCut := [⟨33,243894275,243894442⟩,
⟨90,662512925,662513377⟩,
⟨128,938524610,938525254⟩]
theorem checked14005 : checkPrefixCuts (2^48) 1839595521 9 Manual.Count131072.C014005.packed 128 cuts14005 = true := by
 decide +kernel
def pointBounds14005 : List (Nat × Nat × Nat) := [(1839629312,95366826470904,95367203892383),(1839687680,95367245089554,95367622511318)]
theorem point_links_checked14005 : (cuts14005.take 2).map (fun c => (1839595521-1+2*2^9*c.k,95366582576629+c.lower,95366959997941+c.upper)) = pointBounds14005 := by
 decide +kernel
def cuts14006 : List PrefixCut := [⟨19,146724519,146724621⟩,
⟨76,572966310,572966705⟩,
⟨128,951768278,951768936⟩]
theorem checked14006 : checkPrefixCuts (2^48) 1839726593 9 Manual.Count131072.C014006.packed 128 cuts14006 = true := by
 decide +kernel
def pointBounds14006 : List (Nat × Nat × Nat) := [(1839746048,95367667825758,95368045247816),(1839804416,95368094067549,95368471489900)]
theorem point_links_checked14006 : (cuts14006.take 2).map (fun c => (1839726593-1+2*2^9*c.k,95367521101239+c.lower,95367898523195+c.upper)) = pointBounds14006 := by
 decide +kernel
def cuts14007 : List PrefixCut := [⟨5,39317684,39317710⟩,
⟨62,453293627,453293945⟩,
⟨119,877659085,877659694⟩,
⟨128,945427807,945428463⟩]
theorem checked14007 : checkPrefixCuts (2^48) 1839857665 9 Manual.Count131072.C014007.packed 128 cuts14007 = true := by
 decide +kernel
def pointBounds14007 : List (Nat × Nat × Nat) := [(1839862784,95368512187201,95368889609841),(1839921152,95368926163144,95369303586076),(1839979520,95369350528602,95369727951825)]
theorem point_links_checked14007 : (cuts14007.take 3).map (fun c => (1839857665-1+2*2^9*c.k,95368472869517+c.lower,95368850292131+c.upper)) = pointBounds14007 := by
 decide +kernel
def cuts14008 : List PrefixCut := [⟨48,348322659,348322903⟩,
⟨105,774955580,774956122⟩,
⟨128,942606869,942607525⟩]
theorem checked14008 : checkPrefixCuts (2^48) 1839988737 9 Manual.Count131072.C014008.packed 128 cuts14008 = true := by
 decide +kernel
def pointBounds14008 : List (Nat × Nat × Nat) := [(1840037888,95369766619983,95370144043497),(1840096256,95370193252904,95370570676716)]
theorem point_links_checked14008 : (cuts14008.take 2).map (fun c => (1839988737-1+2*2^9*c.k,95369418297324+c.lower,95369795720594+c.upper)) = pointBounds14008 := by
 decide +kernel
def cuts14009 : List PrefixCut := [⟨34,248260706,248260876⟩,
⟨91,655287816,655288268⟩,
⟨128,924184790,924185428⟩]
theorem checked14009 : checkPrefixCuts (2^48) 1840119809 9 Manual.Count131072.C014009.packed 128 cuts14009 = true := by
 decide +kernel
def pointBounds14009 : List (Nat × Nat × Nat) := [(1840154624,95370609164899,95370986588995),(1840212992,95371016192009,95371393616387)]
theorem point_links_checked14009 : (cuts14009.take 2).map (fun c => (1840119809-1+2*2^9*c.k,95370360904193+c.lower,95370738328119+c.upper)) = pointBounds14009 := by
 decide +kernel
def cuts14010 : List PrefixCut := [⟨20,147753354,147753458⟩,
⟨77,567602451,567602850⟩,
⟨128,938496307,938496962⟩]
theorem checked14010 : checkPrefixCuts (2^48) 1840250881 9 Manual.Count131072.C014010.packed 128 cuts14010 = true := by
 decide +kernel
def pointBounds14010 : List (Nat × Nat × Nat) := [(1840271360,95371432842337,95371810267005),(1840329728,95371852691434,95372230116397)]
theorem point_links_checked14010 : (cuts14010.take 2).map (fun c => (1840250881-1+2*2^9*c.k,95371285088983+c.lower,95371662513547+c.upper)) = pointBounds14010 := by
 decide +kernel
def cuts14011 : List PrefixCut := [⟨6,44506553,44506583⟩,
⟨63,463411312,463411636⟩,
⟨120,884138055,884138668⟩,
⟨128,945770126,945770780⟩]
theorem checked14011 : checkPrefixCuts (2^48) 1840381953 9 Manual.Count131072.C014011.packed 128 cuts14011 = true := by
 decide +kernel
def pointBounds14011 : List (Nat × Nat × Nat) := [(1840388096,95372268091843,95372645517092),(1840446464,95372686996602,95373064422145),(1840504832,95373107723345,95373485149177)]
theorem point_links_checked14011 : (cuts14011.take 3).map (fun c => (1840381953-1+2*2^9*c.k,95372223585290+c.lower,95372601010509+c.upper)) = pointBounds14011 := by
 decide +kernel
def cuts14012 : List PrefixCut := [⟨49,359846028,359846274⟩,
⟨106,777487605,777488142⟩,
⟨128,936833249,936833898⟩]
theorem checked14012 : checkPrefixCuts (2^48) 1840513025 9 Manual.Count131072.C014012.packed 128 cuts14012 = true := by
 decide +kernel
def pointBounds14012 : List (Nat × Nat × Nat) := [(1840563200,95373529201444,95373906627563),(1840621568,95373946843021,95374324269431)]
theorem point_links_checked14012 : (cuts14012.take 2).map (fun c => (1840513025-1+2*2^9*c.k,95373169355416+c.lower,95373546781289+c.upper)) = pointBounds14012 := by
 decide +kernel
def cuts14013 : List PrefixCut := [⟨35,254000850,254001025⟩,
⟨92,675897593,675898058⟩,
⟨128,938448498,938449148⟩]
theorem checked14013 : checkPrefixCuts (2^48) 1840644097 9 Manual.Count131072.C014013.packed 128 cuts14013 = true := by
 decide +kernel
def pointBounds14013 : List (Nat × Nat × Nat) := [(1840679936,95374360189515,95374737616212),(1840738304,95374782086258,95375159513245)]
theorem point_links_checked14013 : (cuts14013.take 2).map (fun c => (1840644097-1+2*2^9*c.k,95374106188665+c.lower,95374483615187+c.upper)) = pointBounds14013 := by
 decide +kernel
def cuts14014 : List PrefixCut := [⟨21,155203820,155203927⟩,
⟨78,572333813,572334209⟩,
⟨128,939605181,939605829⟩]
theorem checked14014 : checkPrefixCuts (2^48) 1840775169 9 Manual.Count131072.C014014.packed 128 cuts14014 = true := by
 decide +kernel
def pointBounds14014 : List (Nat × Nat × Nat) := [(1840796672,95375199840983,95375577268262),(1840855040,95375616970976,95375994398544)]
theorem point_links_checked14014 : (cuts14014.take 2).map (fun c => (1840775169-1+2*2^9*c.k,95375044637163+c.lower,95375422064335+c.upper)) = pointBounds14014 := by
 decide +kernel
def cuts14015 : List PrefixCut := [⟨7,49692460,49692495⟩,
⟨64,472453107,472453435⟩,
⟨121,890307815,890308433⟩,
⟨128,943513389,943514043⟩]
theorem checked14015 : checkPrefixCuts (2^48) 1840906241 9 Manual.Count131072.C014015.packed 128 cuts14015 = true := by
 decide +kernel
def pointBounds14015 : List (Nat × Nat × Nat) := [(1840913408,95376033934804,95376411362659),(1840971776,95376456695451,95376834123599),(1841030144,95376874550159,95377251978597)]
theorem point_links_checked14015 : (cuts14015.take 3).map (fun c => (1840906241-1+2*2^9*c.k,95375984242344+c.lower,95376361670164+c.upper)) = pointBounds14015 := by
 decide +kernel
def cuts14016 : List PrefixCut := [⟨50,367234916,367235169⟩,
⟨107,784757301,784757845⟩,
⟨128,944057529,944058179⟩]
theorem checked14016 : checkPrefixCuts (2^48) 1841037313 9 Manual.Count131072.C014016.packed 128 cuts14016 = true := by
 decide +kernel
def pointBounds14016 : List (Nat × Nat × Nat) := [(1841088512,95377294990649,95377672419376),(1841146880,95377712513034,95378089942052)]
theorem point_links_checked14016 : (cuts14016.take 2).map (fun c => (1841037313-1+2*2^9*c.k,95376927755733+c.lower,95377305184207+c.upper)) = pointBounds14016 := by
 decide +kernel
def cuts14017 : List PrefixCut := [⟨36,262795352,262795539⟩,
⟨93,684113076,684113553⟩,
⟨128,941544476,941545130⟩]
theorem checked14017 : checkPrefixCuts (2^48) 1841168385 9 Manual.Count131072.C014017.packed 128 cuts14017 = true := by
 decide +kernel
def pointBounds14017 : List (Nat × Nat × Nat) := [(1841205248,95378134608614,95378512037925),(1841263616,95378555926338,95378933355939)]
theorem point_links_checked14017 : (cuts14017.take 2).map (fun c => (1841168385-1+2*2^9*c.k,95377871813262+c.lower,95378249242386+c.upper)) = pointBounds14017 := by
 decide +kernel
def cuts14018 : List PrefixCut := [⟨22,154089504,154089612⟩,
⟨79,570641783,570642181⟩,
⟨128,925885481,925886130⟩]
theorem checked14018 : checkPrefixCuts (2^48) 1841299457 9 Manual.Count131072.C014018.packed 128 cuts14018 = true := by
 decide +kernel
def pointBounds14018 : List (Nat × Nat × Nat) := [(1841321984,95378967447242,95379344877128),(1841380352,95379383999521,95379761429697)]
theorem point_links_checked14018 : (cuts14018.take 2).map (fun c => (1841299457-1+2*2^9*c.k,95378813357738+c.lower,95379190787516+c.upper)) = pointBounds14018 := by
 decide +kernel
def cuts14019 : List PrefixCut := [⟨8,58238254,58238295⟩,
⟨65,476903991,476904320⟩,
⟨122,890665378,890665991⟩,
⟨128,935907799,935908443⟩]
theorem checked14019 : checkPrefixCuts (2^48) 1841430529 9 Manual.Count131072.C014019.packed 128 cuts14019 = true := by
 decide +kernel
def pointBounds14019 : List (Nat × Nat × Nat) := [(1841438720,95379797481473,95380174911941),(1841497088,95380216147210,95380593577966),(1841555456,95380629908597,95381007339637)]
theorem point_links_checked14019 : (cuts14019.take 3).map (fun c => (1841430529-1+2*2^9*c.k,95379739243219+c.lower,95380116673646+c.upper)) = pointBounds14019 := by
 decide +kernel
def cuts14020 : List PrefixCut := [⟨51,370492897,370493158⟩,
⟨108,797830779,797831334⟩,
⟨128,945011580,945012235⟩]
theorem checked14020 : checkPrefixCuts (2^48) 1841561601 9 Manual.Count131072.C014020.packed 128 cuts14020 = true := by
 decide +kernel
def pointBounds14020 : List (Nat × Nat × Nat) := [(1841613824,95381045643915,95381423075247),(1841672192,95381472981797,95381850413423)]
theorem point_links_checked14020 : (cuts14020.take 2).map (fun c => (1841561601-1+2*2^9*c.k,95380675151018+c.lower,95381052582089+c.upper)) = pointBounds14020 := by
 decide +kernel
def cuts14021 : List PrefixCut := [⟨37,275405610,275405802⟩,
⟨94,699506964,699507449⟩,
⟨128,944333330,944333984⟩]
theorem checked14021 : checkPrefixCuts (2^48) 1841692673 9 Manual.Count131072.C014021.packed 128 cuts14021 = true := by
 decide +kernel
def pointBounds14021 : List (Nat × Nat × Nat) := [(1841730560,95381895568208,95382273000126),(1841788928,95382319669562,95382697101773)]
theorem point_links_checked14021 : (cuts14021.take 2).map (fun c => (1841692673-1+2*2^9*c.k,95381620162598+c.lower,95381997594324+c.upper)) = pointBounds14021 := by
 decide +kernel
def cuts14022 : List PrefixCut := [⟨23,165660136,165660249⟩,
⟨80,586219732,586220138⟩,
⟨128,937694545,937695195⟩]
theorem checked14022 : checkPrefixCuts (2^48) 1841823745 9 Manual.Count131072.C014022.packed 128 cuts14022 = true := by
 decide +kernel
def pointBounds14022 : List (Nat × Nat × Nat) := [(1841847296,95382730156064,95383107588557),(1841905664,95383150715660,95383528148446)]
theorem point_links_checked14022 : (cuts14022.take 2).map (fun c => (1841823745-1+2*2^9*c.k,95382564495928+c.lower,95382941928308+c.upper)) = pointBounds14022 := by
 decide +kernel
def cuts14023 : List PrefixCut := [⟨9,64639793,64639838⟩,
⟨66,487923270,487923610⟩,
⟨123,903705922,903706554⟩,
⟨128,940072909,940073566⟩]
theorem checked14023 : checkPrefixCuts (2^48) 1841954817 9 Manual.Count131072.C014023.packed 128 cuts14023 = true := by
 decide +kernel
def pointBounds14023 : List (Nat × Nat × Nat) := [(1841964032,95383566830266,95383944263341),(1842022400,95383990113743,95384367547113),(1842080768,95384405896395,95384783330057)]
theorem point_links_checked14023 : (cuts14023.take 3).map (fun c => (1841954817-1+2*2^9*c.k,95383502190473+c.lower,95383879623503+c.upper)) = pointBounds14023 := by
 decide +kernel
def cuts14024 : List PrefixCut := [⟨52,378944125,378944386⟩,
⟨109,793019698,793020249⟩,
⟨128,929921498,929922145⟩]
theorem checked14024 : checkPrefixCuts (2^48) 1842085889 9 Manual.Count131072.C014024.packed 128 cuts14024 = true := by
 decide +kernel
def pointBounds14024 : List (Nat × Nat × Nat) := [(1842139136,95384821207507,95385198641455),(1842197504,95385235283080,95385612717318)]
theorem point_links_checked14024 : (cuts14024.take 2).map (fun c => (1842085889-1+2*2^9*c.k,95384442263382+c.lower,95384819697069+c.upper)) = pointBounds14024 := by
 decide +kernel
def cuts14025 : List PrefixCut := [⟨38,273188103,273188292⟩,
⟨95,696251742,696252222⟩,
⟨128,942383416,942384067⟩]
theorem checked14025 : checkPrefixCuts (2^48) 1842216961 9 Manual.Count131072.C014025.packed 128 cuts14025 = true := by
 decide +kernel
def pointBounds14025 : List (Nat × Nat × Nat) := [(1842255872,95385645372983,95386022807506),(1842314240,95386068436622,95386445871436)]
theorem point_links_checked14025 : (cuts14025.take 2).map (fun c => (1842216961-1+2*2^9*c.k,95385372184880+c.lower,95385749619214+c.upper)) = pointBounds14025 := by
 decide +kernel
def cuts14026 : List PrefixCut := [⟨24,174015819,174015942⟩,
⟨81,588191669,588192078⟩,
⟨128,933761105,933761753⟩]
theorem checked14026 : checkPrefixCuts (2^48) 1842348033 9 Manual.Count131072.C014026.packed 128 cuts14026 = true := by
 decide +kernel
def pointBounds14026 : List (Nat × Nat × Nat) := [(1842372608,95386488584115,95386866019223),(1842430976,95386902759965,95387280195359)]
theorem point_links_checked14026 : (cuts14026.take 2).map (fun c => (1842348033-1+2*2^9*c.k,95386314568296+c.lower,95386692003281+c.upper)) = pointBounds14026 := by
 decide +kernel
def cuts14027 : List PrefixCut := [⟨10,76537376,76537431⟩,
⟨67,491909229,491909573⟩,
⟨124,905129268,905129901⟩,
⟨128,931556568,931557219⟩]
theorem checked14027 : checkPrefixCuts (2^48) 1842479105 9 Manual.Count131072.C014027.packed 128 cuts14027 = true := by
 decide +kernel
def pointBounds14027 : List (Nat × Nat × Nat) := [(1842489344,95387324866777,95387702302465),(1842547712,95387740238630,95388117674607),(1842606080,95388153458669,95388530894935)]
theorem point_links_checked14027 : (cuts14027.take 3).map (fun c => (1842479105-1+2*2^9*c.k,95387248329401+c.lower,95387625765034+c.upper)) = pointBounds14027 := by
 decide +kernel
def cuts14028 : List PrefixCut := [⟨53,393195330,393195602⟩,
⟨110,817540021,817540587⟩,
⟨128,944168676,944169330⟩]
theorem checked14028 : checkPrefixCuts (2^48) 1842610177 9 Manual.Count131072.C014028.packed 128 cuts14028 = true := by
 decide +kernel
def pointBounds14028 : List (Nat × Nat × Nat) := [(1842664448,95388573081299,95388950517855),(1842722816,95388997425990,95389374862840)]
theorem point_links_checked14028 : (cuts14028.take 2).map (fun c => (1842610177-1+2*2^9*c.k,95388179885969+c.lower,95388557322253+c.upper)) = pointBounds14028 := by
 decide +kernel
def cuts14029 : List PrefixCut := [⟨39,287468415,287468611⟩,
⟨96,707051168,707051653⟩,
⟨128,949294287,949294937⟩]
theorem checked14029 : checkPrefixCuts (2^48) 1842741249 9 Manual.Count131072.C014029.packed 128 cuts14029 = true := by
 decide +kernel
def pointBounds14029 : List (Nat × Nat × Nat) := [(1842781184,95389411523060,95389788960194),(1842839552,95389831105813,95390208543236)]
theorem point_links_checked14029 : (cuts14029.take 2).map (fun c => (1842741249-1+2*2^9*c.k,95389124054645+c.lower,95389501491583+c.upper)) = pointBounds14029 := by
 decide +kernel
def cuts14030 : List PrefixCut := [⟨25,175035466,175035588⟩,
⟨82,591842527,591842939⟩,
⟨128,931662653,931663296⟩]
theorem checked14030 : checkPrefixCuts (2^48) 1842872321 9 Manual.Count131072.C014030.packed 128 cuts14030 = true := by
 decide +kernel
def pointBounds14030 : List (Nat × Nat × Nat) := [(1842897920,95390248384398,95390625822108),(1842956288,95390665191459,95391042629459)]
theorem point_links_checked14030 : (cuts14030.take 2).map (fun c => (1842872321-1+2*2^9*c.k,95390073348932+c.lower,95390450786520+c.upper)) = pointBounds14030 := by
 decide +kernel
def cuts14031 : List PrefixCut := [⟨11,81402816,81402871⟩,
⟨68,509637653,509638002⟩,
⟨125,928543128,928543767⟩,
⟨128,951603162,951603817⟩]
theorem checked14031 : checkPrefixCuts (2^48) 1843003393 9 Manual.Count131072.C014031.packed 128 cuts14031 = true := by
 decide +kernel
def pointBounds14031 : List (Nat × Nat × Nat) := [(1843014656,95391086414401,95391463852687),(1843073024,95391514649238,95391892087818),(1843131392,95391933554713,95392310993583)]
theorem point_links_checked14031 : (cuts14031.take 3).map (fun c => (1843003393-1+2*2^9*c.k,95391005011585+c.lower,95391382449816+c.upper)) = pointBounds14031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000125
