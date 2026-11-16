import PlattAssemblyKernel
import PlattCertificates.Count131072.C012080
import PlattCertificates.Count131072.C012081
import PlattCertificates.Count131072.C012082
import PlattCertificates.Count131072.C012083
import PlattCertificates.Count131072.C012084
import PlattCertificates.Count131072.C012085
import PlattCertificates.Count131072.C012086
import PlattCertificates.Count131072.C012087
import PlattCertificates.Count131072.C012088
import PlattCertificates.Count131072.C012089
import PlattCertificates.Count131072.C012090
import PlattCertificates.Count131072.C012091
import PlattCertificates.Count131072.C012092
import PlattCertificates.Count131072.C012093
import PlattCertificates.Count131072.C012094
import PlattCertificates.Count131072.C012095
import PlattCertificates.Count131072.C012096
import PlattCertificates.Count131072.C012097
import PlattCertificates.Count131072.C012098
import PlattCertificates.Count131072.C012099
import PlattCertificates.Count131072.C012100
import PlattCertificates.Count131072.C012101
import PlattCertificates.Count131072.C012102
import PlattCertificates.Count131072.C012103
import PlattCertificates.Count131072.C012104
import PlattCertificates.Count131072.C012105
import PlattCertificates.Count131072.C012106
import PlattCertificates.Count131072.C012107
import PlattCertificates.Count131072.C012108
import PlattCertificates.Count131072.C012109
import PlattCertificates.Count131072.C012110
import PlattCertificates.Count131072.C012111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12080 : List PrefixCut := [⟨24,198609592,198609743⟩,
⟨73,610537480,610537946⟩,
⟨122,1029899763,1029900546⟩,
⟨128,1084336101,1084336925⟩]
theorem checked12080 : checkPrefixCuts (2^48) 1587281921 9 Manual.Count131072.C012080.packed 128 cuts12080 = true := by
 decide +kernel
def pointBounds12080 : List (Nat × Nat × Nat) := [(1587306496,93413588691604,93413964694967),(1587356672,93414000619492,93414376623170),(1587406848,93414419981775,93414795985770)]
theorem point_links_checked12080 : (cuts12080.take 3).map (fun c => (1587281921-1+2*2^9*c.k,93413390082012+c.lower,93413766085224+c.upper)) = pointBounds12080 := by
 decide +kernel
def cuts12081 : List PrefixCut := [⟨43,371650628,371650908⟩,
⟨92,797724157,797724757⟩,
⟨128,1106942610,1106943444⟩]
theorem checked12081 : checkPrefixCuts (2^48) 1587412993 9 Manual.Count131072.C012081.packed 128 cuts12081 = true := by
 decide +kernel
def pointBounds12081 : List (Nat × Nat × Nat) := [(1587457024,93414846068741,93415222073057),(1587507200,93415272142270,93415648146906)]
theorem point_links_checked12081 : (cuts12081.take 2).map (fun c => (1587412993-1+2*2^9*c.k,93414474418113+c.lower,93414850422149+c.upper)) = pointBounds12081 := by
 decide +kernel
def cuts12082 : List PrefixCut := [⟨13,116486976,116487064⟩,
⟨62,540406009,540406418⟩,
⟨111,949773774,949774497⟩,
⟨128,1094441116,1094441948⟩]
theorem checked12082 : checkPrefixCuts (2^48) 1587544065 9 Manual.Count131072.C012082.packed 128 cuts12082 = true := by
 decide +kernel
def pointBounds12082 : List (Nat × Nat × Nat) := [(1587557376,93415697847699,93416073852657),(1587607552,93416121766732,93416497772011),(1587657728,93416531134497,93416907140090)]
theorem point_links_checked12082 : (cuts12082.take 3).map (fun c => (1587544065-1+2*2^9*c.k,93415581360723+c.lower,93415957365593+c.upper)) = pointBounds12082 := by
 decide +kernel
def cuts12083 : List PrefixCut := [⟨32,281706836,281707046⟩,
⟨81,701508188,701508716⟩,
⟨128,1101973509,1101974341⟩]
theorem checked12083 : checkPrefixCuts (2^48) 1587675137 9 Manual.Count131072.C012083.packed 128 cuts12083 = true := by
 decide +kernel
def pointBounds12083 : List (Nat × Nat × Nat) := [(1587707904,93416957508675,93417333514587),(1587758080,93417377310027,93417753316257)]
theorem point_links_checked12083 : (cuts12083.take 2).map (fun c => (1587675137-1+2*2^9*c.k,93416675801839+c.lower,93417051807541+c.upper)) = pointBounds12083 := by
 decide +kernel
def cuts12084 : List PrefixCut := [⟨2,17904542,17904556⟩,
⟨51,444770116,444770459⟩,
⟨100,867722524,867723187⟩,
⟨128,1104364325,1104365166⟩]
theorem checked12084 : checkPrefixCuts (2^48) 1587806209 9 Manual.Count131072.C012084.packed 128 cuts12084 = true := by
 decide +kernel
def pointBounds12084 : List (Nat × Nat × Nat) := [(1587808256,93417795679890,93418171686438),(1587858432,93418222545464,93418598552341),(1587908608,93418645497872,93419021505069)]
theorem point_links_checked12084 : (cuts12084.take 3).map (fun c => (1587806209-1+2*2^9*c.k,93417777775348+c.lower,93418153781882+c.upper)) = pointBounds12084 := by
 decide +kernel
def cuts12085 : List PrefixCut := [⟨21,182220164,182220299⟩,
⟨70,600005376,600005834⟩,
⟨119,1021499656,1021500431⟩,
⟨128,1098069086,1098069920⟩]
theorem checked12085 : checkPrefixCuts (2^48) 1587937281 9 Manual.Count131072.C012085.packed 128 cuts12085 = true := by
 decide +kernel
def pointBounds12085 : List (Nat × Nat × Nat) := [(1587958784,93419064359837,93419440367347),(1588008960,93419482145049,93419858152882),(1588059136,93419903639329,93420279647479)]
theorem point_links_checked12085 : (cuts12085.take 3).map (fun c => (1587937281-1+2*2^9*c.k,93418882139673+c.lower,93419258147048+c.upper)) = pointBounds12085 := by
 decide +kernel
def cuts12086 : List PrefixCut := [⟨40,341012227,341012489⟩,
⟨89,762834323,762834909⟩,
⟨128,1102763695,1102764539⟩]
theorem checked12086 : checkPrefixCuts (2^48) 1588068353 9 Manual.Count131072.C012086.packed 128 cuts12086 = true := by
 decide +kernel
def pointBounds12086 : List (Nat × Nat × Nat) := [(1588109312,93420321220986,93420697229457),(1588159488,93420743043082,93421119051877)]
theorem point_links_checked12086 : (cuts12086.take 2).map (fun c => (1588068353-1+2*2^9*c.k,93419980208759+c.lower,93420356216968+c.upper)) = pointBounds12086 := by
 decide +kernel
def cuts12087 : List PrefixCut := [⟨10,90032005,90032074⟩,
⟨59,515903565,515903959⟩,
⟨108,924571380,924572083⟩,
⟨128,1094520983,1094521815⟩]
theorem checked12087 : checkPrefixCuts (2^48) 1588199425 9 Manual.Count131072.C012087.packed 128 cuts12087 = true := by
 decide +kernel
def pointBounds12087 : List (Nat × Nat × Nat) := [(1588209664,93421173004459,93421549013581),(1588259840,93421598876019,93421974885466),(1588310016,93422007543834,93422383553590)]
theorem point_links_checked12087 : (cuts12087.take 3).map (fun c => (1588199425-1+2*2^9*c.k,93421082972454+c.lower,93421458981507+c.upper)) = pointBounds12087 := by
 decide +kernel
def cuts12088 : List PrefixCut := [⟨29,248452111,248452300⟩,
⟨78,671979685,671980196⟩,
⟨127,1093190229,1093191059⟩,
⟨128,1101695816,1101696652⟩]
theorem checked12088 : checkPrefixCuts (2^48) 1588330497 9 Manual.Count131072.C012088.packed 128 cuts12088 = true := by
 decide +kernel
def pointBounds12088 : List (Nat × Nat × Nat) := [(1588360192,93422425945548,93422801955622),(1588410368,93422849473122,93423225483518),(1588460544,93423270683666,93423646694381)]
theorem point_links_checked12088 : (cuts12088.take 3).map (fun c => (1588330497-1+2*2^9*c.k,93422177493437+c.lower,93422553503322+c.upper)) = pointBounds12088 := by
 decide +kernel
def cuts12089 : List PrefixCut := [⟨48,416944359,416944676⟩,
⟨97,837596675,837597313⟩,
⟨128,1106743431,1106744278⟩]
theorem checked12089 : checkPrefixCuts (2^48) 1588461569 9 Manual.Count131072.C012089.packed 128 cuts12089 = true := by
 decide +kernel
def pointBounds12089 : List (Nat × Nat × Nat) := [(1588510720,93423696133612,93424072144650),(1588560896,93424116785928,93424492797287)]
theorem point_links_checked12089 : (cuts12089.take 2).map (fun c => (1588461569-1+2*2^9*c.k,93423279189253+c.lower,93423655199974+c.upper)) = pointBounds12089 := by
 decide +kernel
def cuts12090 : List PrefixCut := [⟨18,149897695,149897806⟩,
⟨67,561310075,561310498⟩,
⟨116,972709463,972710199⟩,
⟨128,1078834964,1078835779⟩]
theorem checked12090 : checkPrefixCuts (2^48) 1588592641 9 Manual.Count131072.C012090.packed 128 cuts12090 = true := by
 decide +kernel
def pointBounds12090 : List (Nat × Nat × Nat) := [(1588611072,93424535830379,93424911842058),(1588661248,93424947242759,93425323254750),(1588711424,93425358642147,93425734654451)]
theorem point_links_checked12090 : (cuts12090.take 3).map (fun c => (1588592641-1+2*2^9*c.k,93424385932684+c.lower,93424761944252+c.upper)) = pointBounds12090 := by
 decide +kernel
def cuts12091 : List PrefixCut := [⟨37,315182481,315182726⟩,
⟨86,735236884,735237448⟩,
⟨128,1089198973,1089199807⟩]
theorem checked12091 : checkPrefixCuts (2^48) 1588723713 9 Manual.Count131072.C012091.packed 128 cuts12091 = true := by
 decide +kernel
def pointBounds12091 : List (Nat × Nat × Nat) := [(1588761600,93425779950129,93426155962757),(1588811776,93426200004532,93426576017479)]
theorem point_links_checked12091 : (cuts12091.take 2).map (fun c => (1588723713-1+2*2^9*c.k,93425464767648+c.lower,93425840780031+c.upper)) = pointBounds12091 := by
 decide +kernel
def cuts12092 : List PrefixCut := [⟨7,61472928,61472973⟩,
⟨56,483095300,483095666⟩,
⟨105,904349948,904350631⟩,
⟨128,1102395252,1102396087⟩]
theorem checked12092 : checkPrefixCuts (2^48) 1588854785 9 Manual.Count131072.C012092.packed 128 cuts12092 = true := by
 decide +kernel
def pointBounds12092 : List (Nat × Nat × Nat) := [(1588861952,93426615439549,93426991452811),(1588912128,93427037061921,93427413075504),(1588962304,93427458316569,93427834330469)]
theorem point_links_checked12092 : (cuts12092.take 3).map (fun c => (1588854785-1+2*2^9*c.k,93426553966621+c.lower,93426929979838+c.upper)) = pointBounds12092 := by
 decide +kernel
def cuts12093 : List PrefixCut := [⟨26,227270273,227270445⟩,
⟨75,647081257,647081747⟩,
⟨124,1061742243,1061743047⟩,
⟨128,1095750596,1095751426⟩]
theorem checked12093 : checkPrefixCuts (2^48) 1588985857 9 Manual.Count131072.C012093.packed 128 cuts12093 = true := by
 decide +kernel
def pointBounds12093 : List (Nat × Nat × Nat) := [(1589012480,93427883632146,93428259646370),(1589062656,93428303443130,93428679457672),(1589112832,93428718104116,93429094118972)]
theorem point_links_checked12093 : (cuts12093.take 3).map (fun c => (1588985857-1+2*2^9*c.k,93427656361873+c.lower,93428032375925+c.upper)) = pointBounds12093 := by
 decide +kernel
def cuts12094 : List PrefixCut := [⟨45,395517889,395518192⟩,
⟨94,808204407,808205022⟩,
⟨128,1094420503,1094421338⟩]
theorem checked12094 : checkPrefixCuts (2^48) 1589116929 9 Manual.Count131072.C012094.packed 128 cuts12094 = true := by
 decide +kernel
def pointBounds12094 : List (Nat × Nat × Nat) := [(1589163008,93429147630358,93429523645543),(1589213184,93429560316876,93429936332373)]
theorem point_links_checked12094 : (cuts12094.take 2).map (fun c => (1589116929-1+2*2^9*c.k,93428752112469+c.lower,93429128127351+c.upper)) = pointBounds12094 := by
 decide +kernel
def cuts12095 : List PrefixCut := [⟨15,122560889,122560984⟩,
⟨64,547618801,547619215⟩,
⟨113,976205467,976206208⟩,
⟨128,1105664287,1105665127⟩]
theorem checked12095 : checkPrefixCuts (2^48) 1589248001 9 Manual.Count131072.C012095.packed 128 cuts12095 = true := by
 decide +kernel
def pointBounds12095 : List (Nat × Nat × Nat) := [(1589263360,93429969093861,93430345109673),(1589313536,93430394151773,93430770167904),(1589363712,93430822738439,93431198754897)]
theorem point_links_checked12095 : (cuts12095.take 3).map (fun c => (1589248001-1+2*2^9*c.k,93429846532972+c.lower,93430222548689+c.upper)) = pointBounds12095 := by
 decide +kernel
def cuts12096 : List PrefixCut := [⟨34,294155501,294155726⟩,
⟨83,706599798,706600333⟩,
⟨128,1095125084,1095125918⟩]
theorem checked12096 : checkPrefixCuts (2^48) 1589379073 9 Manual.Count131072.C012096.packed 128 cuts12096 = true := by
 decide +kernel
def pointBounds12096 : List (Nat × Nat × Nat) := [(1589413888,93431246352760,93431622369542),(1589464064,93431658797057,93432034814149)]
theorem point_links_checked12096 : (cuts12096.take 2).map (fun c => (1589379073-1+2*2^9*c.k,93430952197259+c.lower,93431328213816+c.upper)) = pointBounds12096 := by
 decide +kernel
def cuts12097 : List PrefixCut := [⟨4,33468600,33468626⟩,
⟨53,452792845,452793191⟩,
⟨102,865552155,865552817⟩,
⟨128,1086889238,1086890067⟩]
theorem checked12097 : checkPrefixCuts (2^48) 1589510145 9 Manual.Count131072.C012097.packed 128 cuts12097 = true := by
 decide +kernel
def pointBounds12097 : List (Nat × Nat × Nat) := [(1589514240,93432080790943,93432456808360),(1589564416,93432500115188,93432876132925),(1589614592,93432912874498,93433288892551)]
theorem point_links_checked12097 : (cuts12097.take 3).map (fun c => (1589510145-1+2*2^9*c.k,93432047322343+c.lower,93432423339734+c.upper)) = pointBounds12097 := by
 decide +kernel
def cuts12098 : List PrefixCut := [⟨23,197960793,197960948⟩,
⟨72,618838999,618839478⟩,
⟨121,1042890936,1042891736⟩,
⟨128,1097246510,1097247351⟩]
theorem checked12098 : checkPrefixCuts (2^48) 1589641217 9 Manual.Count131072.C012098.packed 128 cuts12098 = true := by
 decide +kernel
def pointBounds12098 : List (Nat × Nat × Nat) := [(1589664768,93433332172374,93433708190749),(1589714944,93433753050580,93434129069279),(1589765120,93434177102517,93434553121537)]
theorem point_links_checked12098 : (cuts12098.take 3).map (fun c => (1589641217-1+2*2^9*c.k,93433134211581+c.lower,93433510229801+c.upper)) = pointBounds12098 := by
 decide +kernel
def cuts12099 : List PrefixCut := [⟨42,359059791,359060066⟩,
⟨91,772462195,772462788⟩,
⟨128,1092021428,1092022257⟩]
theorem checked12099 : checkPrefixCuts (2^48) 1589772289 9 Manual.Count131072.C012099.packed 128 cuts12099 = true := by
 decide +kernel
def pointBounds12099 : List (Nat × Nat × Nat) := [(1589815296,93434590517882,93434966537218),(1589865472,93435003920286,93435379939940)]
theorem point_links_checked12099 : (cuts12099.take 2).map (fun c => (1589772289-1+2*2^9*c.k,93434231458091+c.lower,93434607477152+c.upper)) = pointBounds12099 := by
 decide +kernel
def cuts12100 : List PrefixCut := [⟨12,104629632,104629713⟩,
⟨61,524910229,524910633⟩,
⟨110,940574838,940575560⟩,
⟨128,1092462636,1092463473⟩]
theorem checked12100 : checkPrefixCuts (2^48) 1589903361 9 Manual.Count131072.C012100.packed 128 cuts12100 = true := by
 decide +kernel
def pointBounds12100 : List (Nat × Nat × Nat) := [(1589915648,93435428109151,93435804129122),(1589965824,93435848389748,93436224410042),(1590016000,93436264054357,93436640074969)]
theorem point_links_checked12100 : (cuts12100.take 3).map (fun c => (1589903361-1+2*2^9*c.k,93435323479519+c.lower,93435699499409+c.upper)) = pointBounds12100 := by
 decide +kernel
def cuts12101 : List PrefixCut := [⟨31,269605481,269605685⟩,
⟨80,679048244,679048763⟩,
⟨128,1095735695,1095736529⟩]
theorem checked12101 : checkPrefixCuts (2^48) 1590034433 9 Manual.Count131072.C012101.packed 128 cuts12101 = true := by
 decide +kernel
def pointBounds12101 : List (Nat × Nat × Nat) := [(1590066176,93436685547636,93437061568567),(1590116352,93437094990399,93437471011645)]
theorem point_links_checked12101 : (cuts12101.take 2).map (fun c => (1590034433-1+2*2^9*c.k,93436415942155+c.lower,93436791962882+c.upper)) = pointBounds12101 := by
 decide +kernel
def cuts12102 : List PrefixCut := [⟨1,8850487,8850494⟩,
⟨50,429241837,429242165⟩,
⟨99,848204009,848204655⟩,
⟨128,1094052641,1094053472⟩]
theorem checked12102 : checkPrefixCuts (2^48) 1590165505 9 Manual.Count131072.C012102.packed 128 cuts12102 = true := by
 decide +kernel
def pointBounds12102 : List (Nat × Nat × Nat) := [(1590166528,93437520528337,93437896549905),(1590216704,93437940919687,93438316941576),(1590266880,93438359881859,93438735904066)]
theorem point_links_checked12102 : (cuts12102.take 3).map (fun c => (1590165505-1+2*2^9*c.k,93437511677850+c.lower,93437887699411+c.upper)) = pointBounds12102 := by
 decide +kernel
def cuts12103 : List PrefixCut := [⟨20,170622266,170622395⟩,
⟨69,583717202,583717645⟩,
⟨118,1001931779,1001932542⟩,
⟨128,1085997848,1085998673⟩]
theorem checked12103 : checkPrefixCuts (2^48) 1590296577 9 Manual.Count131072.C012103.packed 128 cuts12103 = true := by
 decide +kernel
def pointBounds12103 : List (Nat × Nat × Nat) := [(1590317056,93438776352757,93439152375278),(1590367232,93439189447693,93439565470528),(1590417408,93439607662270,93439983685425)]
theorem point_links_checked12103 : (cuts12103.take 3).map (fun c => (1590296577-1+2*2^9*c.k,93438605730491+c.lower,93438981752883+c.upper)) = pointBounds12103 := by
 decide +kernel
def cuts12104 : List PrefixCut := [⟨39,340683413,340683668⟩,
⟨88,767366230,767366808⟩,
⟨128,1106437479,1106438317⟩]
theorem checked12104 : checkPrefixCuts (2^48) 1590427649 9 Manual.Count131072.C012104.packed 128 cuts12104 = true := by
 decide +kernel
def pointBounds12104 : List (Nat × Nat × Nat) := [(1590467584,93440032411752,93440408435224),(1590517760,93440459094569,93440835118364)]
theorem point_links_checked12104 : (cuts12104.take 2).map (fun c => (1590427649-1+2*2^9*c.k,93439691728339+c.lower,93440067751556+c.upper)) = pointBounds12104 := by
 decide +kernel
def cuts12105 : List PrefixCut := [⟨9,76803038,76803097⟩,
⟨58,490540740,490541117⟩,
⟨107,908512273,908512964⟩,
⟨128,1087765310,1087766136⟩]
theorem checked12105 : checkPrefixCuts (2^48) 1590558721 9 Manual.Count131072.C012105.packed 128 cuts12105 = true := by
 decide +kernel
def pointBounds12105 : List (Nat × Nat × Nat) := [(1590567936,93440874968856,93441250992970),(1590618112,93441288706558,93441664730990),(1590668288,93441706678091,93442082702837)]
theorem point_links_checked12105 : (cuts12105.take 3).map (fun c => (1590558721-1+2*2^9*c.k,93440798165818+c.lower,93441174189873+c.upper)) = pointBounds12105 := by
 decide +kernel
def cuts12106 : List PrefixCut := [⟨28,239413165,239413344⟩,
⟨77,657004385,657004883⟩,
⟨126,1075644235,1075645051⟩,
⟨128,1092453249,1092454077⟩]
theorem checked12106 : checkPrefixCuts (2^48) 1590689793 9 Manual.Count131072.C012106.packed 128 cuts12106 = true := by
 decide +kernel
def pointBounds12106 : List (Nat × Nat × Nat) := [(1590718464,93442125344293,93442501369353),(1590768640,93442542935513,93442918960892),(1590818816,93442961575363,93443337601060)]
theorem point_links_checked12106 : (cuts12106.take 3).map (fun c => (1590689793-1+2*2^9*c.k,93441885931128+c.lower,93442261956009+c.upper)) = pointBounds12106 := by
 decide +kernel
def cuts12107 : List PrefixCut := [⟨47,405710148,405710456⟩,
⟨96,819369449,819370070⟩,
⟨128,1092540284,1092541113⟩]
theorem checked12107 : checkPrefixCuts (2^48) 1590820865 9 Manual.Count131072.C012107.packed 128 cuts12107 = true := by
 decide +kernel
def pointBounds12107 : List (Nat × Nat × Nat) := [(1590868992,93443384094525,93443760120542),(1590919168,93443797753826,93444173780156)]
theorem point_links_checked12107 : (cuts12107.take 2).map (fun c => (1590820865-1+2*2^9*c.k,93442978384377+c.lower,93443354410086+c.upper)) = pointBounds12107 := by
 decide +kernel
def cuts12108 : List PrefixCut := [⟨17,157106140,157106258⟩,
⟨66,574985461,574985896⟩,
⟨115,990551760,990552515⟩,
⟨128,1100942649,1100943489⟩]
theorem checked12108 : checkPrefixCuts (2^48) 1590951937 9 Manual.Count131072.C012108.packed 128 cuts12108 = true := by
 decide +kernel
def pointBounds12108 : List (Nat × Nat × Nat) := [(1590969344,93444228030801,93444604057457),(1591019520,93444645910122,93445021937095),(1591069696,93445061476421,93445437503714)]
theorem point_links_checked12108 : (cuts12108.take 3).map (fun c => (1590951937-1+2*2^9*c.k,93444070924661+c.lower,93444446951199+c.upper)) = pointBounds12108 := by
 decide +kernel
def cuts12109 : List PrefixCut := [⟨36,307108243,307108476⟩,
⟨85,724771050,724771602⟩,
⟨128,1097843843,1097844676⟩]
theorem checked12109 : checkPrefixCuts (2^48) 1591083009 9 Manual.Count131072.C012109.packed 128 cuts12109 = true := by
 decide +kernel
def pointBounds12109 : List (Nat × Nat × Nat) := [(1591119872,93445478975553,93445855003164),(1591170048,93445896638360,93446272666290)]
theorem point_links_checked12109 : (cuts12109.take 2).map (fun c => (1591083009-1+2*2^9*c.k,93445171867310+c.lower,93445547894688+c.upper)) = pointBounds12109 := by
 decide +kernel
def cuts12110 : List PrefixCut := [⟨6,52183383,52183422⟩,
⟨55,476895587,476895945⟩,
⟨104,898056609,898057282⟩,
⟨128,1103944846,1103945678⟩]
theorem checked12110 : checkPrefixCuts (2^48) 1591214081 9 Manual.Count131072.C012110.packed 128 cuts12110 = true := by
 decide +kernel
def pointBounds12110 : List (Nat × Nat × Nat) := [(1591220224,93446321894536,93446697922786),(1591270400,93446746606740,93447122635309),(1591320576,93447167767762,93447543796646)]
theorem point_links_checked12110 : (cuts12110.take 3).map (fun c => (1591214081-1+2*2^9*c.k,93446269711153+c.lower,93446645739364+c.upper)) = pointBounds12110 := by
 decide +kernel
def cuts12111 : List PrefixCut := [⟨25,210837602,210837763⟩,
⟨74,629495857,629496339⟩,
⟨123,1043365534,1043366329⟩,
⟨128,1087581610,1087582439⟩]
theorem checked12111 : checkPrefixCuts (2^48) 1591345153 9 Manual.Count131072.C012111.packed 128 cuts12111 = true := by
 decide +kernel
def pointBounds12111 : List (Nat × Nat × Nat) := [(1591370752,93447584493601,93447960522805),(1591420928,93448003151856,93448379181381),(1591471104,93448417021533,93448793051371)]
theorem point_links_checked12111 : (cuts12111.take 3).map (fun c => (1591345153-1+2*2^9*c.k,93447373655999+c.lower,93447749685042+c.upper)) = pointBounds12111 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000065
