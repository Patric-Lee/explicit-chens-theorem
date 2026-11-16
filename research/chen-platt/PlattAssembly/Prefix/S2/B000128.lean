import PlattAssemblyKernel
import PlattCertificates.Count131072.C014096
import PlattCertificates.Count131072.C014097
import PlattCertificates.Count131072.C014098
import PlattCertificates.Count131072.C014099
import PlattCertificates.Count131072.C014100
import PlattCertificates.Count131072.C014101
import PlattCertificates.Count131072.C014102
import PlattCertificates.Count131072.C014103
import PlattCertificates.Count131072.C014104
import PlattCertificates.Count131072.C014105
import PlattCertificates.Count131072.C014106
import PlattCertificates.Count131072.C014107
import PlattCertificates.Count131072.C014108
import PlattCertificates.Count131072.C014109
import PlattCertificates.Count131072.C014110
import PlattCertificates.Count131072.C014111
import PlattCertificates.Count131072.C014112
import PlattCertificates.Count131072.C014113
import PlattCertificates.Count131072.C014114
import PlattCertificates.Count131072.C014115
import PlattCertificates.Count131072.C014116
import PlattCertificates.Count131072.C014117
import PlattCertificates.Count131072.C014118
import PlattCertificates.Count131072.C014119
import PlattCertificates.Count131072.C014120
import PlattCertificates.Count131072.C014121
import PlattCertificates.Count131072.C014122
import PlattCertificates.Count131072.C014123
import PlattCertificates.Count131072.C014124
import PlattCertificates.Count131072.C014125
import PlattCertificates.Count131072.C014126
import PlattCertificates.Count131072.C014127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000128
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14096 : List PrefixCut := [⟨13,96230485,96230551⟩,
⟨70,505924238,505924587⟩,
⟨127,917125240,917125878⟩,
⟨128,924877888,924878531⟩]
theorem checked14096 : checkPrefixCuts (2^48) 1851523073 9 Manual.Count131072.C014096.packed 128 cuts14096 = true := by
 decide +kernel
def pointBounds14096 : List (Nat × Nat × Nat) := [(1851536384,95451904599159,95452282079523),(1851594752,95452314292912,95452691773559),(1851653120,95452725493914,95453102974850)]
theorem point_links_checked14096 : (cuts14096.take 3).map (fun c => (1851523073-1+2*2^9*c.k,95451808368674+c.lower,95452185848972+c.upper)) = pointBounds14096 := by
 decide +kernel
def cuts14097 : List PrefixCut := [⟨56,411795923,411796204⟩,
⟨113,837259459,837260038⟩,
⟨128,942293206,942293862⟩]
theorem checked14097 : checkPrefixCuts (2^48) 1851654145 9 Manual.Count131072.C014097.packed 128 cuts14097 = true := by
 decide +kernel
def pointBounds14097 : List (Nat × Nat × Nat) := [(1851711488,95453145042485,95453522523707),(1851769856,95453570506021,95453947987541)]
theorem point_links_checked14097 : (cuts14097.take 2).map (fun c => (1851654145-1+2*2^9*c.k,95452733246562+c.lower,95453110727503+c.upper)) = pointBounds14097 := by
 decide +kernel
def cuts14098 : List PrefixCut := [⟨42,306128291,306128503⟩,
⟨99,726701182,726701689⟩,
⟨128,941770374,941771032⟩]
theorem checked14098 : checkPrefixCuts (2^48) 1851785217 9 Manual.Count131072.C014098.packed 128 cuts14098 = true := by
 decide +kernel
def pointBounds14098 : List (Nat × Nat × Nat) := [(1851828224,95453981668059,95454359149868),(1851886592,95454402240950,95454779723054)]
theorem point_links_checked14098 : (cuts14098.take 2).map (fun c => (1851785217-1+2*2^9*c.k,95453675539768+c.lower,95454053021365+c.upper)) = pointBounds14098 := by
 decide +kernel
def cuts14099 : List PrefixCut := [⟨28,214001889,214002032⟩,
⟨85,622997306,622997732⟩,
⟨128,930761221,930761859⟩]
theorem checked14099 : checkPrefixCuts (2^48) 1851916289 9 Manual.Count131072.C014099.packed 128 cuts14099 = true := by
 decide +kernel
def pointBounds14099 : List (Nat × Nat × Nat) := [(1851944960,95454831312031,95455208794429),(1852003328,95455240307448,95455617790129)]
theorem point_links_checked14099 : (cuts14099.take 2).map (fun c => (1851916289-1+2*2^9*c.k,95454617310142+c.lower,95454994792397+c.upper)) = pointBounds14099 := by
 decide +kernel
def cuts14100 : List PrefixCut := [⟨14,103498240,103498315⟩,
⟨71,517787083,517787445⟩,
⟨128,944372540,944373193⟩]
theorem checked14100 : checkPrefixCuts (2^48) 1852047361 9 Manual.Count131072.C014100.packed 128 cuts14100 = true := by
 decide +kernel
def pointBounds14100 : List (Nat × Nat × Nat) := [(1852061696,95455651569603,95456029052571),(1852120064,95456065858446,95456443341701),(1852178432,95456492443903,95456869927449)]
theorem point_links_checked14100 : (cuts14100.take 3).map (fun c => (1852047361-1+2*2^9*c.k,95455548071363+c.lower,95455925554256+c.upper)) = pointBounds14100 := by
 decide +kernel
def cuts14101 : List PrefixCut := [⟨57,415326394,415326680⟩,
⟨114,834590744,834591321⟩,
⟨128,933364408,933365054⟩]
theorem checked14101 : checkPrefixCuts (2^48) 1852178433 9 Manual.Count131072.C014101.packed 128 cuts14101 = true := by
 decide +kernel
def pointBounds14101 : List (Nat × Nat × Nat) := [(1852236800,95456907770297,95457285254129),(1852295168,95457327034647,95457704518770)]
theorem point_links_checked14101 : (cuts14101.take 2).map (fun c => (1852178433-1+2*2^9*c.k,95456492443903+c.lower,95456869927449+c.upper)) = pointBounds14101 := by
 decide +kernel
def cuts14102 : List PrefixCut := [⟨43,315007060,315007270⟩,
⟨100,737283997,737284500⟩,
⟨128,934818069,934818708⟩]
theorem checked14102 : checkPrefixCuts (2^48) 1852309505 9 Manual.Count131072.C014102.packed 128 cuts14102 = true := by
 decide +kernel
def pointBounds14102 : List (Nat × Nat × Nat) := [(1852353536,95457740815371,95458118299773),(1852411904,95458163092308,95458540577003)]
theorem point_links_checked14102 : (cuts14102.take 2).map (fun c => (1852309505-1+2*2^9*c.k,95457425808311+c.lower,95457803292503+c.upper)) = pointBounds14102 := by
 decide +kernel
def cuts14103 : List PrefixCut := [⟨29,213485429,213485575⟩,
⟨86,626467295,626467726⟩,
⟨128,931105244,931105886⟩]
theorem checked14103 : checkPrefixCuts (2^48) 1852440577 9 Manual.Count131072.C014103.packed 128 cuts14103 = true := by
 decide +kernel
def pointBounds14103 : List (Nat × Nat × Nat) := [(1852470272,95458574111809,95458951596786),(1852528640,95458987093675,95459364578937)]
theorem point_links_checked14103 : (cuts14103.take 2).map (fun c => (1852440577-1+2*2^9*c.k,95458360626380+c.lower,95458738111211+c.upper)) = pointBounds14103 := by
 decide +kernel
def cuts14104 : List PrefixCut := [⟨15,112433189,112433266⟩,
⟨72,512778569,512778926⟩,
⟨128,917517442,917518081⟩]
theorem checked14104 : checkPrefixCuts (2^48) 1852571649 9 Manual.Count131072.C014104.packed 128 cuts14104 = true := by
 decide +kernel
def pointBounds14104 : List (Nat × Nat × Nat) := [(1852587008,95459404164813,95459781650363),(1852645376,95459804510193,95460181996023)]
theorem point_links_checked14104 : (cuts14104.take 2).map (fun c => (1852571649-1+2*2^9*c.k,95459291731624+c.lower,95459669217097+c.upper)) = pointBounds14104 := by
 decide +kernel
def cuts14105 : List PrefixCut := [⟨1,8507889,8507895⟩,
⟨58,425995508,425995802⟩,
⟨115,841798797,841799376⟩,
⟨128,936138897,936139542⟩]
theorem checked14105 : checkPrefixCuts (2^48) 1852702721 9 Manual.Count131072.C014105.packed 128 cuts14105 = true := by
 decide +kernel
def pointBounds14105 : List (Nat × Nat × Nat) := [(1852703744,95460217756955,95460595243073),(1852762112,95460635244574,95461012730980),(1852820480,95461051047863,95461428534554)]
theorem point_links_checked14105 : (cuts14105.take 3).map (fun c => (1852702721-1+2*2^9*c.k,95460209249066+c.lower,95460586735178+c.upper)) = pointBounds14105 := by
 decide +kernel
def cuts14106 : List PrefixCut := [⟨44,326311374,326311597⟩,
⟨101,746797670,746798180⟩,
⟨128,942756778,942757422⟩]
theorem checked14106 : checkPrefixCuts (2^48) 1852833793 9 Manual.Count131072.C014106.packed 128 cuts14106 = true := by
 decide +kernel
def pointBounds14106 : List (Nat × Nat × Nat) := [(1852878848,95461471699337,95461849186317),(1852937216,95461892185633,95462269672900)]
theorem point_links_checked14106 : (cuts14106.take 2).map (fun c => (1852833793-1+2*2^9*c.k,95461145387963+c.lower,95461522874720+c.upper)) = pointBounds14106 := by
 decide +kernel
def cuts14107 : List PrefixCut := [⟨30,215551617,215551765⟩,
⟨87,639201383,639201824⟩,
⟨128,934943106,934943755⟩]
theorem checked14107 : checkPrefixCuts (2^48) 1852964865 9 Manual.Count131072.C014107.packed 128 cuts14107 = true := by
 decide +kernel
def pointBounds14107 : List (Nat × Nat × Nat) := [(1852995584,95462303696358,95462681183907),(1853053952,95462727346124,95463104833966)]
theorem point_links_checked14107 : (cuts14107.take 2).map (fun c => (1852964865-1+2*2^9*c.k,95462088144741+c.lower,95462465632142+c.upper)) = pointBounds14107 := by
 decide +kernel
def cuts14108 : List PrefixCut := [⟨16,115591118,115591197⟩,
⟨73,527214802,527215168⟩,
⟨128,920903249,920903886⟩]
theorem checked14108 : checkPrefixCuts (2^48) 1853095937 9 Manual.Count131072.C014108.packed 128 cuts14108 = true := by
 decide +kernel
def pointBounds14108 : List (Nat × Nat × Nat) := [(1853112320,95463138678965,95463516167094),(1853170688,95463550302649,95463927791065)]
theorem point_links_checked14108 : (cuts14108.take 2).map (fun c => (1853095937-1+2*2^9*c.k,95463023087847+c.lower,95463400575897+c.upper)) = pointBounds14108 := by
 decide +kernel
def cuts14109 : List PrefixCut := [⟨2,13973287,13973298⟩,
⟨59,434987664,434987964⟩,
⟨116,858266941,858267535⟩,
⟨128,946201655,946202310⟩]
theorem checked14109 : checkPrefixCuts (2^48) 1853227009 9 Manual.Count131072.C014109.packed 128 cuts14109 = true := by
 decide +kernel
def pointBounds14109 : List (Nat × Nat × Nat) := [(1853229056,95463957964383,95464335453081),(1853287424,95464378978760,95464756467747),(1853345792,95464802258037,95465179747318)]
theorem point_links_checked14109 : (cuts14109.take 3).map (fun c => (1853227009-1+2*2^9*c.k,95463943991096+c.lower,95464321479783+c.upper)) = pointBounds14109 := by
 decide +kernel
def cuts14110 : List PrefixCut := [⟨45,324548369,324548593⟩,
⟨102,731854970,731855473⟩,
⟨128,921835892,921836525⟩]
theorem checked14110 : checkPrefixCuts (2^48) 1853358081 9 Manual.Count131072.C014110.packed 128 cuts14110 = true := by
 decide +kernel
def pointBounds14110 : List (Nat × Nat × Nat) := [(1853404160,95465214741120,95465592230686),(1853462528,95465622047721,95465999537566)]
theorem point_links_checked14110 : (cuts14110.take 2).map (fun c => (1853358081-1+2*2^9*c.k,95464890192751+c.lower,95465267682093+c.upper)) = pointBounds14110 := by
 decide +kernel
def cuts14111 : List PrefixCut := [⟨31,222628034,222628186⟩,
⟨88,637349984,637350415⟩,
⟨128,922985703,922986332⟩]
theorem checked14111 : checkPrefixCuts (2^48) 1853489153 9 Manual.Count131072.C014111.packed 128 cuts14111 = true := by
 decide +kernel
def pointBounds14111 : List (Nat × Nat × Nat) := [(1853520896,95466034656677,95466412146804),(1853579264,95466449378627,95466826869033)]
theorem point_links_checked14111 : (cuts14111.take 2).map (fun c => (1853489153-1+2*2^9*c.k,95465812028643+c.lower,95466189518618+c.upper)) = pointBounds14111 := by
 decide +kernel
def cuts14112 : List PrefixCut := [⟨17,122239822,122239908⟩,
⟨74,538454164,538454536⟩,
⟨128,925349988,925350629⟩]
theorem checked14112 : checkPrefixCuts (2^48) 1853620225 9 Manual.Count131072.C014112.packed 128 cuts14112 = true := by
 decide +kernel
def pointBounds14112 : List (Nat × Nat × Nat) := [(1853637632,95466857254168,95467234744858),(1853696000,95467273468510,95467650959486)]
theorem point_links_checked14112 : (cuts14112.take 2).map (fun c => (1853620225-1+2*2^9*c.k,95466735014346+c.lower,95467112504950+c.upper)) = pointBounds14112 := by
 decide +kernel
def cuts14113 : List PrefixCut := [⟨3,22168722,22168737⟩,
⟨60,431372335,431372635⟩,
⟨117,842840454,842841039⟩,
⟨128,919818474,919819112⟩]
theorem checked14113 : checkPrefixCuts (2^48) 1853751297 9 Manual.Count131072.C014113.packed 128 cuts14113 = true := by
 decide +kernel
def pointBounds14113 : List (Nat × Nat × Nat) := [(1853754368,95467682533056,95468060024316),(1853812736,95468091736669,95468469228214),(1853871104,95468503204788,95468880696618)]
theorem point_links_checked14113 : (cuts14113.take 3).map (fun c => (1853751297-1+2*2^9*c.k,95467660364334+c.lower,95468037855579+c.upper)) = pointBounds14113 := by
 decide +kernel
def cuts14114 : List PrefixCut := [⟨46,341157576,341157813⟩,
⟨103,761861055,761861580⟩,
⟨128,946170837,946171490⟩]
theorem checked14114 : checkPrefixCuts (2^48) 1853882369 9 Manual.Count131072.C014114.packed 128 cuts14114 = true := by
 decide +kernel
def pointBounds14114 : List (Nat × Nat × Nat) := [(1853929472,95468921340384,95469298832504),(1853987840,95469342043863,95469719536271)]
theorem point_links_checked14114 : (cuts14114.take 2).map (fun c => (1853882369-1+2*2^9*c.k,95468580182808+c.lower,95468957674691+c.upper)) = pointBounds14114 := by
 decide +kernel
def cuts14115 : List PrefixCut := [⟨32,235317713,235317875⟩,
⟨89,649922227,649922677⟩,
⟨128,933199914,933200557⟩]
theorem checked14115 : checkPrefixCuts (2^48) 1854013441 9 Manual.Count131072.C014115.packed 128 cuts14115 = true := by
 decide +kernel
def pointBounds14115 : List (Nat × Nat × Nat) := [(1854046208,95469761671358,95470139164056),(1854104576,95470176275872,95470553768858)]
theorem point_links_checked14115 : (cuts14115.take 2).map (fun c => (1854013441-1+2*2^9*c.k,95469526353645+c.lower,95469903846181+c.upper)) = pointBounds14115 := by
 decide +kernel
def cuts14116 : List PrefixCut := [⟨18,133590813,133590904⟩,
⟨75,550142596,550142973⟩,
⟨128,937839796,937840438⟩]
theorem checked14116 : checkPrefixCuts (2^48) 1854144513 9 Manual.Count131072.C014116.packed 128 cuts14116 = true := by
 decide +kernel
def pointBounds14116 : List (Nat × Nat × Nat) := [(1854162944,95470593144372,95470970637642),(1854221312,95471009696155,95471387189711)]
theorem point_links_checked14116 : (cuts14116.take 2).map (fun c => (1854144513-1+2*2^9*c.k,95470459553559+c.lower,95470837046738+c.upper)) = pointBounds14116 := by
 decide +kernel
def cuts14117 : List PrefixCut := [⟨4,28537949,28537969⟩,
⟨61,450224592,450224902⟩,
⟨118,865522749,865523344⟩,
⟨128,940657540,940658187⟩]
theorem checked14117 : checkPrefixCuts (2^48) 1854275585 9 Manual.Count131072.C014117.packed 128 cuts14117 = true := by
 decide +kernel
def pointBounds14117 : List (Nat × Nat × Nat) := [(1854279680,95471425931304,95471803425145),(1854338048,95471847617947,95472225112078),(1854396416,95472262916104,95472640410520)]
theorem point_links_checked14117 : (cuts14117.take 3).map (fun c => (1854275585-1+2*2^9*c.k,95471397393355+c.lower,95471774887176+c.upper)) = pointBounds14117 := by
 decide +kernel
def cuts14118 : List PrefixCut := [⟨47,337266352,337266587⟩,
⟨104,748136578,748137088⟩,
⟨128,918582487,918583115⟩]
theorem checked14118 : checkPrefixCuts (2^48) 1854406657 9 Manual.Count131072.C014118.packed 128 cuts14118 = true := by
 decide +kernel
def pointBounds14118 : List (Nat × Nat × Nat) := [(1854454784,95472675317247,95473052811950),(1854513152,95473086187473,95473463682451)]
theorem point_links_checked14118 : (cuts14118.take 2).map (fun c => (1854406657-1+2*2^9*c.k,95472338050895+c.lower,95472715545363+c.upper)) = pointBounds14118 := by
 decide +kernel
def cuts14119 : List PrefixCut := [⟨33,235858254,235858418⟩,
⟨90,646247383,646247835⟩,
⟨128,923070740,923071382⟩]
theorem checked14119 : checkPrefixCuts (2^48) 1854537729 9 Manual.Count131072.C014119.packed 128 cuts14119 = true := by
 decide +kernel
def pointBounds14119 : List (Nat × Nat × Nat) := [(1854571520,95473492491636,95473869986896),(1854629888,95473902880765,95474280376313)]
theorem point_links_checked14119 : (cuts14119.take 2).map (fun c => (1854537729-1+2*2^9*c.k,95473256633382+c.lower,95473634128478+c.upper)) = pointBounds14119 := by
 decide +kernel
def cuts14120 : List PrefixCut := [⟨19,140837719,140837817⟩,
⟨76,556664472,556664855⟩,
⟨128,926951664,926952304⟩]
theorem checked14120 : checkPrefixCuts (2^48) 1854668801 9 Manual.Count131072.C014120.packed 128 cuts14120 = true := by
 decide +kernel
def pointBounds14120 : List (Nat × Nat × Nat) := [(1854688256,95474320541841,95474698037677),(1854746624,95474736368594,95475113864715)]
theorem point_links_checked14120 : (cuts14120.take 2).map (fun c => (1854668801-1+2*2^9*c.k,95474179704122+c.lower,95474557199860+c.upper)) = pointBounds14120 := by
 decide +kernel
def cuts14121 : List PrefixCut := [⟨5,38090417,38090441⟩,
⟨62,460112915,460113229⟩,
⟨119,881515120,881515731⟩,
⟨128,948434446,948435104⟩]
theorem checked14121 : checkPrefixCuts (2^48) 1854799873 9 Manual.Count131072.C014121.packed 128 cuts14121 = true := by
 decide +kernel
def pointBounds14121 : List (Nat × Nat × Nat) := [(1854804992,95475144746203,95475522242605),(1854863360,95475566768701,95475944265393),(1854921728,95475988170906,95476365667895)]
theorem point_links_checked14121 : (cuts14121.take 3).map (fun c => (1854799873-1+2*2^9*c.k,95475106655786+c.lower,95475484152164+c.upper)) = pointBounds14121 := by
 decide +kernel
def cuts14122 : List PrefixCut := [⟨48,347185987,347186223⟩,
⟨105,756877845,756878365⟩,
⟨128,924240850,924241487⟩]
theorem checked14122 : checkPrefixCuts (2^48) 1854930945 9 Manual.Count131072.C014122.packed 128 cuts14122 = true := by
 decide +kernel
def pointBounds14122 : List (Nat × Nat × Nat) := [(1854980096,95476402276219,95476779773491),(1855038464,95476811968077,95477189465633)]
theorem point_links_checked14122 : (cuts14122.take 2).map (fun c => (1854930945-1+2*2^9*c.k,95476055090232+c.lower,95476432587268+c.upper)) = pointBounds14122 := by
 decide +kernel
def cuts14123 : List PrefixCut := [⟨34,254606244,254606419⟩,
⟨91,670038092,670038551⟩,
⟨128,940107185,940107830⟩]
theorem checked14123 : checkPrefixCuts (2^48) 1855062017 9 Manual.Count131072.C014123.packed 128 cuts14123 = true := by
 decide +kernel
def pointBounds14123 : List (Nat × Nat × Nat) := [(1855096832,95477233937326,95477611435174),(1855155200,95477649369174,95478026867306)]
theorem point_links_checked14123 : (cuts14123.take 2).map (fun c => (1855062017-1+2*2^9*c.k,95476979331082+c.lower,95477356828755+c.upper)) = pointBounds14123 := by
 decide +kernel
def cuts14124 : List PrefixCut := [⟨20,148535689,148535790⟩,
⟨77,558327716,558328102⟩,
⟨128,928054967,928055609⟩]
theorem checked14124 : checkPrefixCuts (2^48) 1855193089 9 Manual.Count131072.C014124.packed 128 cuts14124 = true := by
 decide +kernel
def pointBounds14124 : List (Nat × Nat × Nat) := [(1855213568,95478067973956,95478445472375),(1855271936,95478477765983,95478855264687)]
theorem point_links_checked14124 : (cuts14124.take 2).map (fun c => (1855193089-1+2*2^9*c.k,95477919438267+c.lower,95478296936585+c.upper)) = pointBounds14124 := by
 decide +kernel
def cuts14125 : List PrefixCut := [⟨6,42327565,42327595⟩,
⟨63,453610813,453611124⟩,
⟨120,876562506,876563110⟩,
⟨128,934664217,934664864⟩]
theorem checked14125 : checkPrefixCuts (2^48) 1855324161 9 Manual.Count131072.C014125.packed 128 cuts14125 = true := by
 decide +kernel
def pointBounds14125 : List (Nat × Nat × Nat) := [(1855330304,95478889820799,95479267319789),(1855388672,95479301104047,95479678603318),(1855447040,95479724055740,95480101555304)]
theorem point_links_checked14125 : (cuts14125.take 3).map (fun c => (1855324161-1+2*2^9*c.k,95478847493234+c.lower,95479224992194+c.upper)) = pointBounds14125 := by
 decide +kernel
def cuts14126 : List PrefixCut := [⟨49,356038069,356038316⟩,
⟨106,771074980,771075516⟩,
⟨128,934901759,934902408⟩]
theorem checked14126 : checkPrefixCuts (2^48) 1855455233 9 Manual.Count131072.C014126.packed 128 cuts14126 = true := by
 decide +kernel
def pointBounds14126 : List (Nat × Nat × Nat) := [(1855505408,95480138195520,95480515695374),(1855563776,95480553232431,95480930732574)]
theorem point_links_checked14126 : (cuts14126.take 2).map (fun c => (1855455233-1+2*2^9*c.k,95479782157451+c.lower,95480159657058+c.upper)) = pointBounds14126 := by
 decide +kernel
def cuts14127 : List PrefixCut := [⟨35,260450180,260450364⟩,
⟨92,677887885,677888356⟩,
⟨128,943330241,943330896⟩]
theorem checked14127 : checkPrefixCuts (2^48) 1855586305 9 Manual.Count131072.C014127.packed 128 cuts14127 = true := by
 decide +kernel
def pointBounds14127 : List (Nat × Nat × Nat) := [(1855622144,95480977509390,95481355009830),(1855680512,95481394947095,95481772447822)]
theorem point_links_checked14127 : (cuts14127.take 2).map (fun c => (1855586305-1+2*2^9*c.k,95480717059210+c.lower,95481094559466+c.upper)) = pointBounds14127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000128
