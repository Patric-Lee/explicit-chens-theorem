import PlattAssemblyKernel
import PlattCertificates.Count131072.C012112
import PlattCertificates.Count131072.C012113
import PlattCertificates.Count131072.C012114
import PlattCertificates.Count131072.C012115
import PlattCertificates.Count131072.C012116
import PlattCertificates.Count131072.C012117
import PlattCertificates.Count131072.C012118
import PlattCertificates.Count131072.C012119
import PlattCertificates.Count131072.C012120
import PlattCertificates.Count131072.C012121
import PlattCertificates.Count131072.C012122
import PlattCertificates.Count131072.C012123
import PlattCertificates.Count131072.C012124
import PlattCertificates.Count131072.C012125
import PlattCertificates.Count131072.C012126
import PlattCertificates.Count131072.C012127
import PlattCertificates.Count131072.C012128
import PlattCertificates.Count131072.C012129
import PlattCertificates.Count131072.C012130
import PlattCertificates.Count131072.C012131
import PlattCertificates.Count131072.C012132
import PlattCertificates.Count131072.C012133
import PlattCertificates.Count131072.C012134
import PlattCertificates.Count131072.C012135
import PlattCertificates.Count131072.C012136
import PlattCertificates.Count131072.C012137
import PlattCertificates.Count131072.C012138
import PlattCertificates.Count131072.C012139
import PlattCertificates.Count131072.C012140
import PlattCertificates.Count131072.C012141
import PlattCertificates.Count131072.C012142
import PlattCertificates.Count131072.C012143
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12112 : List PrefixCut := [⟨44,378483627,378483913⟩,
⟨93,794626242,794626842⟩,
⟨128,1091913446,1091914269⟩]
theorem checked12112 : checkPrefixCuts (2^48) 1591476225 9 Manual.Count131072.C012112.packed 128 cuts12112 = true := by
 decide +kernel
def pointBounds12112 : List (Nat × Nat × Nat) := [(1591521280,93448839721236,93449215751394),(1591571456,93449255863851,93449631894323)]
theorem point_links_checked12112 : (cuts12112.take 2).map (fun c => (1591476225-1+2*2^9*c.k,93448461237609+c.lower,93448837267481+c.upper)) = pointBounds12112 := by
 decide +kernel
def cuts12113 : List PrefixCut := [⟨14,123970894,123970986⟩,
⟨63,537257767,537258176⟩,
⟨112,962026233,962026963⟩,
⟨128,1100311825,1100312662⟩]
theorem checked12113 : checkPrefixCuts (2^48) 1591607297 9 Manual.Count131072.C012113.packed 128 cuts12113 = true := by
 decide +kernel
def pointBounds12113 : List (Nat × Nat × Nat) := [(1591621632,93449677121949,93450053152736),(1591671808,93450090408822,93450466439926),(1591721984,93450515177288,93450891208713)]
theorem point_links_checked12113 : (cuts12113.take 3).map (fun c => (1591607297-1+2*2^9*c.k,93449553151055+c.lower,93449929181750+c.upper)) = pointBounds12113 := by
 decide +kernel
def cuts12114 : List PrefixCut := [⟨33,281341248,281341462⟩,
⟨82,706259823,706260359⟩,
⟨128,1105349200,1105350035⟩]
theorem checked12114 : checkPrefixCuts (2^48) 1591738369 9 Manual.Count131072.C012114.packed 128 cuts12114 = true := by
 decide +kernel
def pointBounds12114 : List (Nat × Nat × Nat) := [(1591772160,93450934804128,93451310835874),(1591822336,93451359722703,93451735754771)]
theorem point_links_checked12114 : (cuts12114.take 2).map (fun c => (1591738369-1+2*2^9*c.k,93450653462880+c.lower,93451029494412+c.upper)) = pointBounds12114 := by
 decide +kernel
def cuts12115 : List PrefixCut := [⟨3,23517079,23517097⟩,
⟨52,444165180,444165521⟩,
⟨101,869220316,869220982⟩,
⟨128,1100130637,1100131480⟩]
theorem checked12115 : checkPrefixCuts (2^48) 1591869441 9 Manual.Count131072.C012115.packed 128 cuts12115 = true := by
 decide +kernel
def pointBounds12115 : List (Nat × Nat × Nat) := [(1591872512,93451782329159,93452158361544),(1591922688,93452202977260,93452579009968),(1591972864,93452628032396,93453004065429)]
theorem point_links_checked12115 : (cuts12115.take 3).map (fun c => (1591869441-1+2*2^9*c.k,93451758812080+c.lower,93452134844447+c.upper)) = pointBounds12115 := by
 decide +kernel
def cuts12116 : List PrefixCut := [⟨22,184760737,184760877⟩,
⟨71,609435501,609435963⟩,
⟨120,1030384125,1030384907⟩,
⟨128,1100570412,1100571247⟩]
theorem checked12116 : checkPrefixCuts (2^48) 1592000513 9 Manual.Count131072.C012116.packed 128 cuts12116 = true := by
 decide +kernel
def pointBounds12116 : List (Nat × Nat × Nat) := [(1592023040,93453043703454,93453419736804),(1592073216,93453468378218,93453844411890),(1592123392,93453889326842,93454265360834)]
theorem point_links_checked12116 : (cuts12116.take 3).map (fun c => (1592000513-1+2*2^9*c.k,93452858942717+c.lower,93453234975927+c.upper)) = pointBounds12116 := by
 decide +kernel
def cuts12117 : List PrefixCut := [⟨41,357290344,357290613⟩,
⟨90,772025034,772025618⟩,
⟨128,1101540749,1101541582⟩]
theorem checked12117 : checkPrefixCuts (2^48) 1592131585 9 Manual.Count131072.C012117.packed 128 cuts12117 = true := by
 decide +kernel
def pointBounds12117 : List (Nat × Nat × Nat) := [(1592173568,93454316803473,93454692837787),(1592223744,93454731538163,93455107572792)]
theorem point_links_checked12117 : (cuts12117.take 2).map (fun c => (1592131585-1+2*2^9*c.k,93453959513129+c.lower,93454335547174+c.upper)) = pointBounds12117 := by
 decide +kernel
def cuts12118 : List PrefixCut := [⟨11,96166166,96166241⟩,
⟨60,515470751,515471148⟩,
⟨109,927514816,927515527⟩,
⟨128,1085717846,1085718679⟩]
theorem checked12118 : checkPrefixCuts (2^48) 1592262657 9 Manual.Count131072.C012118.packed 128 cuts12118 = true := by
 decide +kernel
def pointBounds12118 : List (Nat × Nat × Nat) := [(1592273920,93455157220044,93455533254997),(1592324096,93455576524629,93455952559904),(1592374272,93455988568694,93456364604283)]
theorem point_links_checked12118 : (cuts12118.take 3).map (fun c => (1592262657-1+2*2^9*c.k,93455061053878+c.lower,93455437088756+c.upper)) = pointBounds12118 := by
 decide +kernel
def cuts12119 : List PrefixCut := [⟨30,251706783,251706976⟩,
⟨79,671148500,671149011⟩,
⟨128,1093581812,1093582643⟩]
theorem checked12119 : checkPrefixCuts (2^48) 1592393729 9 Manual.Count131072.C012119.packed 128 cuts12119 = true := by
 decide +kernel
def pointBounds12119 : List (Nat × Nat × Nat) := [(1592424448,93456398478507,93456774514411),(1592474624,93456817920224,93457193956446),(1592524800,93457240353536,93457616390078)]
theorem point_links_checked12119 : (cuts12119.take 3).map (fun c => (1592393729-1+2*2^9*c.k,93456146771724+c.lower,93456522807435+c.upper)) = pointBounds12119 := by
 decide +kernel
def cuts12120 : List PrefixCut := [⟨49,415350194,415350508⟩,
⟨98,832101262,832101893⟩,
⟨128,1089250293,1089251120⟩]
theorem checked12120 : checkPrefixCuts (2^48) 1592524801 9 Manual.Count131072.C012120.packed 128 cuts12120 = true := by
 decide +kernel
def pointBounds12120 : List (Nat × Nat × Nat) := [(1592574976,93457655703730,93458031740586),(1592625152,93458072454798,93458448491971)]
theorem point_links_checked12120 : (cuts12120.take 2).map (fun c => (1592524801-1+2*2^9*c.k,93457240353536+c.lower,93457616390078+c.upper)) = pointBounds12120 := by
 decide +kernel
def cuts12121 : List PrefixCut := [⟨19,156231022,156231141⟩,
⟨68,568007511,568007939⟩,
⟨117,990020820,990021568⟩,
⟨128,1081384590,1081385409⟩]
theorem checked12121 : checkPrefixCuts (2^48) 1592655873 9 Manual.Count131072.C012121.packed 128 cuts12121 = true := by
 decide +kernel
def pointBounds12121 : List (Nat × Nat × Nat) := [(1592675328,93458485834851,93458861872339),(1592725504,93458897611340,93459273649137),(1592775680,93459319624649,93459695662766)]
theorem point_links_checked12121 : (cuts12121.take 3).map (fun c => (1592655873-1+2*2^9*c.k,93458329603829+c.lower,93458705641198+c.upper)) = pointBounds12121 := by
 decide +kernel
def cuts12122 : List PrefixCut := [⟨38,336291163,336291417⟩,
⟨87,752269731,752270301⟩,
⟨128,1096670167,1096671003⟩]
theorem checked12122 : checkPrefixCuts (2^48) 1592786945 9 Manual.Count131072.C012122.packed 128 cuts12122 = true := by
 decide +kernel
def pointBounds12122 : List (Nat × Nat × Nat) := [(1592825856,93459747279582,93460123318024),(1592876032,93460163258150,93460539296908)]
theorem point_links_checked12122 : (cuts12122.take 2).map (fun c => (1592786945-1+2*2^9*c.k,93459410988419+c.lower,93459787026607+c.upper)) = pointBounds12122 := by
 decide +kernel
def cuts12123 : List PrefixCut := [⟨8,64496769,64496817⟩,
⟨57,486810331,486810707⟩,
⟨106,906990176,906990872⟩,
⟨128,1092692061,1092692900⟩]
theorem checked12123 : checkPrefixCuts (2^48) 1592918017 9 Manual.Count131072.C012123.packed 128 cuts12123 = true := by
 decide +kernel
def pointBounds12123 : List (Nat × Nat × Nat) := [(1592926208,93460572155355,93460948194427),(1592976384,93460994468917,93461370508317),(1593026560,93461414648762,93461790688482)]
theorem point_links_checked12123 : (cuts12123.take 3).map (fun c => (1592918017-1+2*2^9*c.k,93460507658586+c.lower,93460883697610+c.upper)) = pointBounds12123 := by
 decide +kernel
def cuts12124 : List PrefixCut := [⟨27,232167877,232168048⟩,
⟨76,650377801,650378290⟩,
⟨125,1066277739,1066278545⟩,
⟨128,1090305542,1090306365⟩]
theorem checked12124 : checkPrefixCuts (2^48) 1593049089 9 Manual.Count131072.C012124.packed 128 cuts12124 = true := by
 decide +kernel
def pointBounds12124 : List (Nat × Nat × Nat) := [(1593076736,93461832518524,93462208558558),(1593126912,93462250728448,93462626768800),(1593177088,93462666628386,93463042669055)]
theorem point_links_checked12124 : (cuts12124.take 3).map (fun c => (1593049089-1+2*2^9*c.k,93461600350647+c.lower,93461976390510+c.upper)) = pointBounds12124 := by
 decide +kernel
def cuts12125 : List PrefixCut := [⟨46,392742431,392742729⟩,
⟨95,813032780,813033398⟩,
⟨128,1092865690,1092866521⟩]
theorem checked12125 : checkPrefixCuts (2^48) 1593180161 9 Manual.Count131072.C012125.packed 128 cuts12125 = true := by
 decide +kernel
def pointBounds12125 : List (Nat × Nat × Nat) := [(1593227264,93463083398620,93463459439604),(1593277440,93463503688969,93463879730273)]
theorem point_links_checked12125 : (cuts12125.take 2).map (fun c => (1593180161-1+2*2^9*c.k,93462690656189+c.lower,93463066696875+c.upper)) = pointBounds12125 := by
 decide +kernel
def cuts12126 : List PrefixCut := [⟨16,143800764,143800876⟩,
⟨65,557351775,557352203⟩,
⟨114,971949633,971950378⟩,
⟨128,1091892654,1091893488⟩]
theorem checked12126 : checkPrefixCuts (2^48) 1593311233 9 Manual.Count131072.C012126.packed 128 cuts12126 = true := by
 decide +kernel
def pointBounds12126 : List (Nat × Nat × Nat) := [(1593327616,93463927322643,93464303364272),(1593377792,93464340873654,93464716915599),(1593427968,93464755471512,93465131513774)]
theorem point_links_checked12126 : (cuts12126.take 3).map (fun c => (1593311233-1+2*2^9*c.k,93463783521879+c.lower,93464159563396+c.upper)) = pointBounds12126 := by
 decide +kernel
def cuts12127 : List PrefixCut := [⟨35,302590919,302591150⟩,
⟨84,717162736,717163279⟩,
⟨128,1088976794,1088977621⟩]
theorem checked12127 : checkPrefixCuts (2^48) 1593442305 9 Manual.Count131072.C012127.packed 128 cuts12127 = true := by
 decide +kernel
def pointBounds12127 : List (Nat × Nat × Nat) := [(1593478144,93465178005452,93465554048034),(1593528320,93465592577269,93465968620163)]
theorem point_links_checked12127 : (cuts12127.take 2).map (fun c => (1593442305-1+2*2^9*c.k,93464875414533+c.lower,93465251456884+c.upper)) = pointBounds12127 := by
 decide +kernel
def cuts12128 : List PrefixCut := [⟨5,42921326,42921359⟩,
⟨54,464708889,464709241⟩,
⟨103,873589670,873590334⟩,
⟨128,1083235412,1083236239⟩]
theorem checked12128 : checkPrefixCuts (2^48) 1593573377 9 Manual.Count131072.C012128.packed 128 cuts12128 = true := by
 decide +kernel
def pointBounds12128 : List (Nat × Nat × Nat) := [(1593578496,93466007312653,93466383355864),(1593628672,93466429100216,93466805143746),(1593678848,93466837980997,93467214024839)]
theorem point_links_checked12128 : (cuts12128.take 3).map (fun c => (1593573377-1+2*2^9*c.k,93465964391327+c.lower,93466340434505+c.upper)) = pointBounds12128 := by
 decide +kernel
def cuts12129 : List PrefixCut := [⟨24,200458471,200458623⟩,
⟨73,609666607,609667067⟩,
⟨122,1030341307,1030342087⟩,
⟨128,1078730408,1078731223⟩]
theorem checked12129 : checkPrefixCuts (2^48) 1593704449 9 Manual.Count131072.C012129.packed 128 cuts12129 = true := by
 decide +kernel
def pointBounds12129 : List (Nat × Nat × Nat) := [(1593729024,93467248085210,93467624129367),(1593779200,93467657293346,93468033337811),(1593829376,93468077968046,93468454012831)]
theorem point_links_checked12129 : (cuts12129.take 3).map (fun c => (1593704449-1+2*2^9*c.k,93467047626739+c.lower,93467423670744+c.upper)) = pointBounds12129 := by
 decide +kernel
def cuts12130 : List PrefixCut := [⟨43,377570264,377570546⟩,
⟨92,790801458,790802055⟩,
⟨128,1100010145,1100010982⟩]
theorem checked12130 : checkPrefixCuts (2^48) 1593835521 9 Manual.Count131072.C012130.packed 128 cuts12130 = true := by
 decide +kernel
def pointBounds12130 : List (Nat × Nat × Nat) := [(1593879552,93468503927411,93468879972513),(1593929728,93468917158605,93469293204022)]
theorem point_links_checked12130 : (cuts12130.take 2).map (fun c => (1593835521-1+2*2^9*c.k,93468126357147+c.lower,93468502401967+c.upper)) = pointBounds12130 := by
 decide +kernel
def cuts12131 : List PrefixCut := [⟨13,109483896,109483978⟩,
⟨62,523572135,523572532⟩,
⟨111,937294113,937294823⟩,
⟨128,1079789443,1079790261⟩]
theorem checked12131 : checkPrefixCuts (2^48) 1593966593 9 Manual.Count131072.C012131.packed 128 cuts12131 = true := by
 decide +kernel
def pointBounds12131 : List (Nat × Nat × Nat) := [(1593979904,93469335851188,93469711896927),(1594030080,93469749939427,93470125985481),(1594080256,93470163661405,93470539707772)]
theorem point_links_checked12131 : (cuts12131.take 3).map (fun c => (1593966593-1+2*2^9*c.k,93469226367292+c.lower,93469602412949+c.upper)) = pointBounds12131 := by
 decide +kernel
def cuts12132 : List PrefixCut := [⟨32,264503859,264504061⟩,
⟨81,686851467,686851989⟩,
⟨128,1095414414,1095415247⟩]
theorem checked12132 : checkPrefixCuts (2^48) 1594097665 9 Manual.Count131072.C012132.packed 128 cuts12132 = true := by
 decide +kernel
def pointBounds12132 : List (Nat × Nat × Nat) := [(1594130432,93470570660594,93470946707271),(1594180608,93470993008202,93471369055199)]
theorem point_links_checked12132 : (cuts12132.take 2).map (fun c => (1594097665-1+2*2^9*c.k,93470306156735+c.lower,93470682203210+c.upper)) = pointBounds12132 := by
 decide +kernel
def cuts12133 : List PrefixCut := [⟨2,15007475,15007486⟩,
⟨51,424086975,424087294⟩,
⟨100,852397499,852398142⟩,
⟨128,1087379871,1087380694⟩]
theorem checked12133 : checkPrefixCuts (2^48) 1594228737 9 Manual.Count131072.C012133.packed 128 cuts12133 = true := by
 decide +kernel
def pointBounds12133 : List (Nat × Nat × Nat) := [(1594230784,93471416578624,93471792625943),(1594280960,93471825658124,93472201705751),(1594331136,93472253968648,93472630016599)]
theorem point_links_checked12133 : (cuts12133.take 3).map (fun c => (1594228737-1+2*2^9*c.k,93471401571149+c.lower,93471777618457+c.upper)) = pointBounds12133 := by
 decide +kernel
def cuts12134 : List PrefixCut := [⟨21,172129377,172129508⟩,
⟨70,586819420,586819868⟩,
⟨119,1000084134,1000084902⟩,
⟨128,1074579853,1074580678⟩]
theorem checked12134 : checkPrefixCuts (2^48) 1594359809 9 Manual.Count131072.C012134.packed 128 cuts12134 = true := by
 decide +kernel
def pointBounds12134 : List (Nat × Nat × Nat) := [(1594381312,93472661080397,93473037128659),(1594431488,93473075770440,93473451819019),(1594481664,93473489035154,93473865084053)]
theorem point_links_checked12134 : (cuts12134.take 3).map (fun c => (1594359809-1+2*2^9*c.k,93472488951020+c.lower,93472864999151+c.upper)) = pointBounds12134 := by
 decide +kernel
def cuts12135 : List PrefixCut := [⟨40,336108023,336108276⟩,
⟨89,747228546,747229109⟩,
⟨128,1084553101,1084553920⟩]
theorem checked12135 : checkPrefixCuts (2^48) 1594490881 9 Manual.Count131072.C012135.packed 128 cuts12135 = true := by
 decide +kernel
def pointBounds12135 : List (Nat × Nat × Nat) := [(1594531840,93473899638896,93474275688105),(1594582016,93474310759419,93474686808938)]
theorem point_links_checked12135 : (cuts12135.take 2).map (fun c => (1594490881-1+2*2^9*c.k,93473563530873+c.lower,93473939579829+c.upper)) = pointBounds12135 := by
 decide +kernel
def cuts12136 : List PrefixCut := [⟨10,75901258,75901317⟩,
⟨59,498998585,498998963⟩,
⟨108,923671131,923671831⟩,
⟨128,1096289855,1096290683⟩]
theorem checked12136 : checkPrefixCuts (2^48) 1594621953 9 Manual.Count131072.C012136.packed 128 cuts12136 = true := by
 decide +kernel
def pointBounds12136 : List (Nat × Nat × Nat) := [(1594632192,93474723985232,93475100035066),(1594682368,93475147082559,93475523132712),(1594732544,93475571755105,93475947805580)]
theorem point_links_checked12136 : (cuts12136.take 3).map (fun c => (1594621953-1+2*2^9*c.k,93474648083974+c.lower,93475024133749+c.upper)) = pointBounds12136 := by
 decide +kernel
def cuts12137 : List PrefixCut := [⟨29,254864485,254864678⟩,
⟨78,665743820,665744326⟩,
⟨127,1092670615,1092671446⟩,
⟨128,1100612492,1100613329⟩]
theorem checked12137 : checkPrefixCuts (2^48) 1594753025 9 Manual.Count131072.C012137.packed 128 cuts12137 = true := by
 decide +kernel
def pointBounds12137 : List (Nat × Nat × Nat) := [(1594782720,93475999238314,93476375289110),(1594832896,93476410117649,93476786168758),(1594883072,93476837044444,93477213095878)]
theorem point_links_checked12137 : (cuts12137.take 3).map (fun c => (1594753025-1+2*2^9*c.k,93475744373829+c.lower,93476120424432+c.upper)) = pointBounds12137 := by
 decide +kernel
def cuts12138 : List PrefixCut := [⟨48,407323645,407323949⟩,
⟨97,832105914,832106540⟩,
⟨128,1091521751,1091522574⟩]
theorem checked12138 : checkPrefixCuts (2^48) 1594884097 9 Manual.Count131072.C012138.packed 128 cuts12138 = true := by
 decide +kernel
def pointBounds12138 : List (Nat × Nat × Nat) := [(1594933248,93477252309966,93477628361710),(1594983424,93477677092235,93478053144301)]
theorem point_links_checked12138 : (cuts12138.take 2).map (fun c => (1594884097-1+2*2^9*c.k,93476844986321+c.lower,93477221037761+c.upper)) = pointBounds12138 := by
 decide +kernel
def cuts12139 : List PrefixCut := [⟨18,158117635,158117756⟩,
⟨67,581814344,581814784⟩,
⟨116,1007791783,1007792545⟩,
⟨128,1107666882,1107667720⟩]
theorem checked12139 : checkPrefixCuts (2^48) 1595015169 9 Manual.Count131072.C012139.packed 128 cuts12139 = true := by
 decide +kernel
def pointBounds12139 : List (Nat × Nat × Nat) := [(1595033600,93478094625707,93478470678091),(1595083776,93478518322416,93478894375119),(1595133952,93478944299855,93479320352880)]
theorem point_links_checked12139 : (cuts12139.take 3).map (fun c => (1595015169-1+2*2^9*c.k,93477936508072+c.lower,93478312560335+c.upper)) = pointBounds12139 := by
 decide +kernel
def cuts12140 : List PrefixCut := [⟨37,318148326,318148566⟩,
⟨86,733335461,733336012⟩,
⟨128,1089224976,1089225794⟩]
theorem checked12140 : checkPrefixCuts (2^48) 1595146241 9 Manual.Count131072.C012140.packed 128 cuts12140 = true := by
 decide +kernel
def pointBounds12140 : List (Nat × Nat × Nat) := [(1595184128,93479362323280,93479738376621),(1595234304,93479777510415,93480153564067)]
theorem point_links_checked12140 : (cuts12140.take 2).map (fun c => (1595146241-1+2*2^9*c.k,93479044174954+c.lower,93479420228055+c.upper)) = pointBounds12140 := by
 decide +kernel
def cuts12141 : List PrefixCut := [⟨7,60696116,60696163⟩,
⟨56,483091079,483091446⟩,
⟨105,904767041,904767726⟩,
⟨128,1104132255,1104133091⟩]
theorem checked12141 : checkPrefixCuts (2^48) 1595277313 9 Manual.Count131072.C012141.packed 128 cuts12141 = true := by
 decide +kernel
def pointBounds12141 : List (Nat × Nat × Nat) := [(1595284480,93480194096046,93480570150012),(1595334656,93480616491009,93480992545295),(1595384832,93481038166971,93481414221575)]
theorem point_links_checked12141 : (cuts12141.take 3).map (fun c => (1595277313-1+2*2^9*c.k,93480133399930+c.lower,93480509453849+c.upper)) = pointBounds12141 := by
 decide +kernel
def cuts12142 : List PrefixCut := [⟨26,220533261,220533429⟩,
⟨75,641124162,641124647⟩,
⟨124,1061349060,1061349863⟩,
⟨128,1092750719,1092751546⟩]
theorem checked12142 : checkPrefixCuts (2^48) 1595408385 9 Manual.Count131072.C012142.packed 128 cuts12142 = true := by
 decide +kernel
def pointBounds12142 : List (Nat × Nat × Nat) := [(1595435008,93481458065446,93481834120369),(1595485184,93481878656347,93482254711587),(1595535360,93482298881245,93482674936803)]
theorem point_links_checked12142 : (cuts12142.take 3).map (fun c => (1595408385-1+2*2^9*c.k,93481237532185+c.lower,93481613586940+c.upper)) = pointBounds12142 := by
 decide +kernel
def cuts12143 : List PrefixCut := [⟨45,390221185,390221480⟩,
⟨94,815359108,815359732⟩,
⟨128,1097777221,1097778060⟩]
theorem checked12143 : checkPrefixCuts (2^48) 1595539457 9 Manual.Count131072.C012143.packed 128 cuts12143 = true := by
 decide +kernel
def pointBounds12143 : List (Nat × Nat × Nat) := [(1595585536,93482720504089,93483096559966),(1595635712,93483145642012,93483521698218)]
theorem point_links_checked12143 : (cuts12143.take 2).map (fun c => (1595539457-1+2*2^9*c.k,93482330282904+c.lower,93482706338486+c.upper)) = pointBounds12143 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000066
