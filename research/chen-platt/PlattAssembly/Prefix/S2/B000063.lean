import PlattAssemblyKernel
import PlattCertificates.Count131072.C012016
import PlattCertificates.Count131072.C012017
import PlattCertificates.Count131072.C012018
import PlattCertificates.Count131072.C012019
import PlattCertificates.Count131072.C012020
import PlattCertificates.Count131072.C012021
import PlattCertificates.Count131072.C012022
import PlattCertificates.Count131072.C012023
import PlattCertificates.Count131072.C012024
import PlattCertificates.Count131072.C012025
import PlattCertificates.Count131072.C012026
import PlattCertificates.Count131072.C012027
import PlattCertificates.Count131072.C012028
import PlattCertificates.Count131072.C012029
import PlattCertificates.Count131072.C012030
import PlattCertificates.Count131072.C012031
import PlattCertificates.Count131072.C012032
import PlattCertificates.Count131072.C012033
import PlattCertificates.Count131072.C012034
import PlattCertificates.Count131072.C012035
import PlattCertificates.Count131072.C012036
import PlattCertificates.Count131072.C012037
import PlattCertificates.Count131072.C012038
import PlattCertificates.Count131072.C012039
import PlattCertificates.Count131072.C012040
import PlattCertificates.Count131072.C012041
import PlattCertificates.Count131072.C012042
import PlattCertificates.Count131072.C012043
import PlattCertificates.Count131072.C012044
import PlattCertificates.Count131072.C012045
import PlattCertificates.Count131072.C012046
import PlattCertificates.Count131072.C012047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12016 : List PrefixCut := [⟨33,284343237,284343454⟩,
⟨82,700952902,700953439⟩,
⟨128,1092236637,1092237473⟩]
theorem checked12016 : checkPrefixCuts (2^48) 1578893313 9 Manual.Count131072.C012016.packed 128 cuts12016 = true := by
 decide +kernel
def pointBounds12016 : List (Nat × Nat × Nat) := [(1578927104,93343277752916,93343653702588),(1578977280,93343694362581,93344070312573)]
theorem point_links_checked12016 : (cuts12016.take 2).map (fun c => (1578893313-1+2*2^9*c.k,93342993409679+c.lower,93343369359134+c.upper)) = pointBounds12016 := by
 decide +kernel
def cuts12017 : List PrefixCut := [⟨3,24421420,24421439⟩,
⟨52,447065326,447065672⟩,
⟨101,861674416,861675074⟩,
⟨128,1091254636,1091255466⟩]
theorem checked12017 : checkPrefixCuts (2^48) 1579024385 9 Manual.Count131072.C012017.packed 128 cuts12017 = true := by
 decide +kernel
def pointBounds12017 : List (Nat × Nat × Nat) := [(1579027456,93344110067736,93344486018046),(1579077632,93344532711642,93344908662279),(1579127808,93344947320732,93345323271681)]
theorem point_links_checked12017 : (cuts12017.take 3).map (fun c => (1579024385-1+2*2^9*c.k,93344085646316+c.lower,93344461596607+c.upper)) = pointBounds12017 := by
 decide +kernel
def cuts12018 : List PrefixCut := [⟨22,194819248,194819398⟩,
⟨71,623483009,623483486⟩,
⟨120,1046607889,1046608693⟩,
⟨128,1114156905,1114157762⟩]
theorem checked12018 : checkPrefixCuts (2^48) 1579155457 9 Manual.Count131072.C012018.packed 128 cuts12018 = true := by
 decide +kernel
def pointBounds12018 : List (Nat × Nat × Nat) := [(1579177984,93345371720200,93345747671471),(1579228160,93345800383961,93346176335559),(1579278336,93346223508841,93346599460766)]
theorem point_links_checked12018 : (cuts12018.take 3).map (fun c => (1579155457-1+2*2^9*c.k,93345176900952+c.lower,93345552852073+c.upper)) = pointBounds12018 := by
 decide +kernel
def cuts12019 : List PrefixCut := [⟨41,346472838,346473103⟩,
⟨90,767253940,767254526⟩,
⟨128,1097489203,1097490047⟩]
theorem checked12019 : checkPrefixCuts (2^48) 1579286529 9 Manual.Count131072.C012019.packed 128 cuts12019 = true := by
 decide +kernel
def pointBounds12019 : List (Nat × Nat × Nat) := [(1579328512,93346637530695,93347013482938),(1579378688,93347058311797,93347434264361)]
theorem point_links_checked12019 : (cuts12019.take 2).map (fun c => (1579286529-1+2*2^9*c.k,93346291057857+c.lower,93346667009835+c.upper)) = pointBounds12019 := by
 decide +kernel
def cuts12020 : List PrefixCut := [⟨11,88750421,88750489⟩,
⟨60,510752285,510752675⟩,
⟨109,930423991,930424702⟩,
⟨128,1090626342,1090627174⟩]
theorem checked12020 : checkPrefixCuts (2^48) 1579417601 9 Manual.Count131072.C012020.packed 128 cuts12020 = true := by
 decide +kernel
def pointBounds12020 : List (Nat × Nat × Nat) := [(1579428864,93347477297481,93347853250371),(1579479040,93347899299345,93348275252557),(1579529216,93348318971051,93348694924584)]
theorem point_links_checked12020 : (cuts12020.take 3).map (fun c => (1579417601-1+2*2^9*c.k,93347388547060+c.lower,93347764499882+c.upper)) = pointBounds12020 := by
 decide +kernel
def cuts12021 : List PrefixCut := [⟨30,257852271,257852467⟩,
⟨79,679635742,679636265⟩,
⟨128,1107642310,1107643159⟩]
theorem checked12021 : checkPrefixCuts (2^48) 1579548673 9 Manual.Count131072.C012021.packed 128 cuts12021 = true := by
 decide +kernel
def pointBounds12021 : List (Nat × Nat × Nat) := [(1579579392,93348737025673,93349112979523),(1579629568,93349158809144,93349534763321),(1579679744,93349586815712,93349962770215)]
theorem point_links_checked12021 : (cuts12021.take 3).map (fun c => (1579548673-1+2*2^9*c.k,93348479173402+c.lower,93348855127056+c.upper)) = pointBounds12021 := by
 decide +kernel
def cuts12022 : List PrefixCut := [⟨49,425498509,425498829⟩,
⟨98,849736285,849736927⟩,
⟨128,1111114216,1111115059⟩]
theorem checked12022 : checkPrefixCuts (2^48) 1579679745 9 Manual.Count131072.C012022.packed 128 cuts12022 = true := by
 decide +kernel
def pointBounds12022 : List (Nat × Nat × Nat) := [(1579729920,93350012314221,93350388269044),(1579780096,93350436551997,93350812507142)]
theorem point_links_checked12022 : (cuts12022.take 2).map (fun c => (1579679745-1+2*2^9*c.k,93349586815712+c.lower,93349962770215+c.upper)) = pointBounds12022 := by
 decide +kernel
def cuts12023 : List PrefixCut := [⟨19,166766076,166766201⟩,
⟨68,588304300,588304751⟩,
⟨117,1018380829,1018381609⟩,
⟨128,1118148090,1118148945⟩]
theorem checked12023 : checkPrefixCuts (2^48) 1579810817 9 Manual.Count131072.C012023.packed 128 cuts12023 = true := by
 decide +kernel
def pointBounds12023 : List (Nat × Nat × Nat) := [(1579830272,93350864696004,93351240651475),(1579880448,93351286234228,93351662190025),(1579930624,93351716310757,93352092266883)]
theorem point_links_checked12023 : (cuts12023.take 3).map (fun c => (1579810817-1+2*2^9*c.k,93350697929928+c.lower,93351073885274+c.upper)) = pointBounds12023 := by
 decide +kernel
def cuts12024 : List PrefixCut := [⟨38,324594726,324594970⟩,
⟨87,744133195,744133759⟩,
⟨128,1092758628,1092759460⟩]
theorem checked12024 : checkPrefixCuts (2^48) 1579941889 9 Manual.Count131072.C012024.packed 128 cuts12024 = true := by
 decide +kernel
def pointBounds12024 : List (Nat × Nat × Nat) := [(1579980800,93352140672744,93352516629189),(1580030976,93352560211213,93352936167978)]
theorem point_links_checked12024 : (cuts12024.take 2).map (fun c => (1579941889-1+2*2^9*c.k,93351816078018+c.lower,93352192034219+c.upper)) = pointBounds12024 := by
 decide +kernel
def cuts12025 : List PrefixCut := [⟨8,71434128,71434182⟩,
⟨57,498427751,498428132⟩,
⟨106,917570019,917570724⟩,
⟨128,1109412730,1109413582⟩]
theorem checked12025 : checkPrefixCuts (2^48) 1580072961 9 Manual.Count131072.C012025.packed 128 cuts12025 = true := by
 decide +kernel
def pointBounds12025 : List (Nat × Nat × Nat) := [(1580081152,93352980270774,93353356227861),(1580131328,93353407264397,93353783221811),(1580181504,93353826406665,93354202364403)]
theorem point_links_checked12025 : (cuts12025.take 3).map (fun c => (1580072961-1+2*2^9*c.k,93352908836646+c.lower,93353284793679+c.upper)) = pointBounds12025 := by
 decide +kernel
def cuts12026 : List PrefixCut := [⟨27,236726954,236727131⟩,
⟨76,665995484,665995991⟩,
⟨125,1077973285,1077974109⟩,
⟨128,1103621275,1103622119⟩]
theorem checked12026 : checkPrefixCuts (2^48) 1580204033 9 Manual.Count131072.C012026.packed 128 cuts12026 = true := by
 decide +kernel
def pointBounds12026 : List (Nat × Nat × Nat) := [(1580231680,93354254976330,93354630934392),(1580281856,93354684244860,93355060203252),(1580332032,93355096222661,93355472181370)]
theorem point_links_checked12026 : (cuts12026.take 3).map (fun c => (1580204033-1+2*2^9*c.k,93354018249376+c.lower,93354394207261+c.upper)) = pointBounds12026 := by
 decide +kernel
def cuts12027 : List PrefixCut := [⟨46,384535582,384535872⟩,
⟨95,803789459,803790066⟩,
⟨128,1085540508,1085541331⟩]
theorem checked12027 : checkPrefixCuts (2^48) 1580335105 9 Manual.Count131072.C012027.packed 128 cuts12027 = true := by
 decide +kernel
def pointBounds12027 : List (Nat × Nat × Nat) := [(1580382208,93355506406233,93355882365252),(1580432384,93355925660110,93356301619446)]
theorem point_links_checked12027 : (cuts12027.take 2).map (fun c => (1580335105-1+2*2^9*c.k,93355121870651+c.lower,93355497829380+c.upper)) = pointBounds12027 := by
 decide +kernel
def cuts12028 : List PrefixCut := [⟨16,136064722,136064828⟩,
⟨65,563306183,563306618⟩,
⟨114,977533825,977534578⟩,
⟨128,1096492684,1096493529⟩]
theorem checked12028 : checkPrefixCuts (2^48) 1580466177 9 Manual.Count131072.C012028.packed 128 cuts12028 = true := by
 decide +kernel
def pointBounds12028 : List (Nat × Nat × Nat) := [(1580482560,93356343475881,93356719435539),(1580532736,93356770717342,93357146677329),(1580582912,93357184944984,93357560905289)]
theorem point_links_checked12028 : (cuts12028.take 3).map (fun c => (1580466177-1+2*2^9*c.k,93356207411159+c.lower,93356583370711+c.upper)) = pointBounds12028 := by
 decide +kernel
def cuts12029 : List PrefixCut := [⟨35,299885531,299885759⟩,
⟨84,719072770,719073324⟩,
⟨128,1098716081,1098716927⟩]
theorem checked12029 : checkPrefixCuts (2^48) 1580597249 9 Manual.Count131072.C012029.packed 128 cuts12029 = true := by
 decide +kernel
def pointBounds12029 : List (Nat × Nat × Nat) := [(1580633088,93357603789374,93357979749999),(1580683264,93358022976613,93358398937564)]
theorem point_links_checked12029 : (cuts12029.take 2).map (fun c => (1580597249-1+2*2^9*c.k,93357303903843+c.lower,93357679864240+c.upper)) = pointBounds12029 := by
 decide +kernel
def cuts12030 : List PrefixCut := [⟨5,45941100,45941137⟩,
⟨54,475963613,475963975⟩,
⟨103,893152365,893153049⟩,
⟨128,1110555365,1110556213⟩]
theorem checked12030 : checkPrefixCuts (2^48) 1580728321 9 Manual.Count131072.C012030.packed 128 cuts12030 = true := by
 decide +kernel
def pointBounds12030 : List (Nat × Nat × Nat) := [(1580733440,93358448561024,93358824522304),(1580783616,93358878583537,93359254545142),(1580833792,93359295772289,93359671734216)]
theorem point_links_checked12030 : (cuts12030.take 3).map (fun c => (1580728321-1+2*2^9*c.k,93358402619924+c.lower,93358778581167+c.upper)) = pointBounds12030 := by
 decide +kernel
def cuts12031 : List PrefixCut := [⟨24,207072653,207072811⟩,
⟨73,631000641,631001124⟩,
⟨122,1053134786,1053135589⟩,
⟨128,1107436190,1107437034⟩]
theorem checked12031 : checkPrefixCuts (2^48) 1580859393 9 Manual.Count131072.C012031.packed 128 cuts12031 = true := by
 decide +kernel
def pointBounds12031 : List (Nat × Nat × Nat) := [(1580883968,93359720247942,93360096210191),(1580934144,93360144175930,93360520138504),(1580984320,93360566310075,93360942272969)]
theorem point_links_checked12031 : (cuts12031.take 3).map (fun c => (1580859393-1+2*2^9*c.k,93359513175289+c.lower,93359889137380+c.upper)) = pointBounds12031 := by
 decide +kernel
def cuts12032 : List PrefixCut := [⟨43,373516506,373516794⟩,
⟨92,800786705,800787316⟩,
⟨128,1107344621,1107345465⟩]
theorem checked12032 : checkPrefixCuts (2^48) 1580990465 9 Manual.Count131072.C012032.packed 128 cuts12032 = true := by
 decide +kernel
def pointBounds12032 : List (Nat × Nat × Nat) := [(1581034496,93360994127985,93361370091208),(1581084672,93361421398184,93361797361730)]
theorem point_links_checked12032 : (cuts12032.take 2).map (fun c => (1580990465-1+2*2^9*c.k,93360620611479+c.lower,93360996574414+c.upper)) = pointBounds12032 := by
 decide +kernel
def cuts12033 : List PrefixCut := [⟨13,111085439,111085524⟩,
⟨62,531563962,531564368⟩,
⟨111,962175759,962176495⟩,
⟨128,1103870535,1103871380⟩]
theorem checked12033 : checkPrefixCuts (2^48) 1581121537 9 Manual.Count131072.C012033.packed 128 cuts12033 = true := by
 decide +kernel
def pointBounds12033 : List (Nat × Nat × Nat) := [(1581134848,93361839041539,93362215005403),(1581185024,93362259520062,93362635484247),(1581235200,93362690131859,93363066096374)]
theorem point_links_checked12033 : (cuts12033.take 3).map (fun c => (1581121537-1+2*2^9*c.k,93361727956100+c.lower,93362103919879+c.upper)) = pointBounds12033 := by
 decide +kernel
def cuts12034 : List PrefixCut := [⟨32,275196822,275197031⟩,
⟨81,697415129,697415655⟩,
⟨128,1099328979,1099329815⟩]
theorem checked12034 : checkPrefixCuts (2^48) 1581252609 9 Manual.Count131072.C012034.packed 128 cuts12034 = true := by
 decide +kernel
def pointBounds12034 : List (Nat × Nat × Nat) := [(1581285376,93363107023457,93363482988290),(1581335552,93363529241764,93363905206914)]
theorem point_links_checked12034 : (cuts12034.take 2).map (fun c => (1581252609-1+2*2^9*c.k,93362831826635+c.lower,93363207791259+c.upper)) = pointBounds12034 := by
 decide +kernel
def cuts12035 : List PrefixCut := [⟨2,17977260,17977273⟩,
⟨51,440880861,440881196⟩,
⟨100,864838944,864839607⟩,
⟨128,1101729795,1101730639⟩]
theorem checked12035 : checkPrefixCuts (2^48) 1581383681 9 Manual.Count131072.C012035.packed 128 cuts12035 = true := by
 decide +kernel
def pointBounds12035 : List (Nat × Nat × Nat) := [(1581385728,93363949132874,93364325098347),(1581435904,93364372036475,93364748002270),(1581486080,93364795994558,93365171960681)]
theorem point_links_checked12035 : (cuts12035.take 3).map (fun c => (1581383681-1+2*2^9*c.k,93363931155614+c.lower,93364307121074+c.upper)) = pointBounds12035 := by
 decide +kernel
def cuts12036 : List PrefixCut := [⟨21,183672079,183672223⟩,
⟨70,607425210,607425680⟩,
⟨119,1022444618,1022445403⟩,
⟨128,1104307963,1104308809⟩]
theorem checked12036 : checkPrefixCuts (2^48) 1581514753 9 Manual.Count131072.C012036.packed 128 cuts12036 = true := by
 decide +kernel
def pointBounds12036 : List (Nat × Nat × Nat) := [(1581536256,93365216557488,93365592523936),(1581586432,93365640310619,93366016277393),(1581636608,93366055330027,93366431297116)]
theorem point_links_checked12036 : (cuts12036.take 3).map (fun c => (1581514753-1+2*2^9*c.k,93365032885409+c.lower,93365408851713+c.upper)) = pointBounds12036 := by
 decide +kernel
def cuts12037 : List PrefixCut := [⟨40,349515323,349515588⟩,
⟨89,774651866,774652456⟩,
⟨128,1117385027,1117385876⟩]
theorem checked12037 : checkPrefixCuts (2^48) 1581645825 9 Manual.Count131072.C012037.packed 128 cuts12037 = true := by
 decide +kernel
def pointBounds12037 : List (Nat × Nat × Nat) := [(1581686784,93366486708695,93366862676110),(1581736960,93366911845238,93367287812978)]
theorem point_links_checked12037 : (cuts12037.take 2).map (fun c => (1581645825-1+2*2^9*c.k,93366137193372+c.lower,93366513160522+c.upper)) = pointBounds12037 := by
 decide +kernel
def cuts12038 : List PrefixCut := [⟨10,86838608,86838675⟩,
⟨59,506075993,506076380⟩,
⟨108,919783920,919784623⟩,
⟨128,1087042752,1087043582⟩]
theorem checked12038 : checkPrefixCuts (2^48) 1581776897 9 Manual.Count131072.C012038.packed 128 cuts12038 = true := by
 decide +kernel
def pointBounds12038 : List (Nat × Nat × Nat) := [(1581787136,93367341417007,93367717385073),(1581837312,93367760654392,93368136622778),(1581887488,93368174362319,93368550331021)]
theorem point_links_checked12038 : (cuts12038.take 3).map (fun c => (1581776897-1+2*2^9*c.k,93367254578399+c.lower,93367630546398+c.upper)) = pointBounds12038 := by
 decide +kernel
def cuts12039 : List PrefixCut := [⟨29,252663564,252663758⟩,
⟨78,670615554,670616069⟩,
⟨127,1086597124,1086597956⟩,
⟨128,1097806027,1097806868⟩]
theorem checked12039 : checkPrefixCuts (2^48) 1581907969 9 Manual.Count131072.C012039.packed 128 cuts12039 = true := by
 decide +kernel
def pointBounds12039 : List (Nat × Nat × Nat) := [(1581937664,93368594284715,93368970253738),(1581987840,93369012236705,93369388206049),(1582038016,93369428218275,93369804187936)]
theorem point_links_checked12039 : (cuts12039.take 3).map (fun c => (1581907969-1+2*2^9*c.k,93368341621151+c.lower,93368717589980+c.upper)) = pointBounds12039 := by
 decide +kernel
def cuts12040 : List PrefixCut := [⟨48,410096977,410097292⟩,
⟨97,832456993,832457635⟩,
⟨128,1094690589,1094691432⟩]
theorem checked12040 : checkPrefixCuts (2^48) 1582039041 9 Manual.Count131072.C012040.packed 128 cuts12040 = true := by
 decide +kernel
def pointBounds12040 : List (Nat × Nat × Nat) := [(1582088192,93369849524155,93370225494140),(1582138368,93370271884171,93370647854483)]
theorem point_links_checked12040 : (cuts12040.take 2).map (fun c => (1582039041-1+2*2^9*c.k,93369439427178+c.lower,93369815396848+c.upper)) = pointBounds12040 := by
 decide +kernel
def cuts12041 : List PrefixCut := [⟨18,154597931,154598050⟩,
⟨67,574796366,574796807⟩,
⟨116,991957264,991958020⟩,
⟨128,1093710499,1093711334⟩]
theorem checked12041 : checkPrefixCuts (2^48) 1582170113 9 Manual.Count131072.C012041.packed 128 cuts12041 = true := by
 decide +kernel
def pointBounds12041 : List (Nat × Nat × Nat) := [(1582188544,93370688715698,93371064686330),(1582238720,93371108914133,93371484885087),(1582288896,93371526075031,93371902046300)]
theorem point_links_checked12041 : (cuts12041.take 3).map (fun c => (1582170113-1+2*2^9*c.k,93370534117767+c.lower,93370910088280+c.upper)) = pointBounds12041 := by
 decide +kernel
def cuts12042 : List PrefixCut := [⟨37,312903956,312904193⟩,
⟨86,731461336,731461897⟩,
⟨128,1101801843,1101802690⟩]
theorem checked12042 : checkPrefixCuts (2^48) 1582301185 9 Manual.Count131072.C012042.packed 128 cuts12042 = true := by
 decide +kernel
def pointBounds12042 : List (Nat × Nat × Nat) := [(1582339072,93371940732222,93372316703807),(1582389248,93372359289602,93372735261511)]
theorem point_links_checked12042 : (cuts12042.take 2).map (fun c => (1582301185-1+2*2^9*c.k,93371627828266+c.lower,93372003799614+c.upper)) = pointBounds12042 := by
 decide +kernel
def cuts12043 : List PrefixCut := [⟨7,64568421,64568472⟩,
⟨56,487368316,487368689⟩,
⟨105,904996715,904997405⟩,
⟨128,1099043510,1099044352⟩]
theorem checked12043 : checkPrefixCuts (2^48) 1582432257 9 Manual.Count131072.C012043.packed 128 cuts12043 = true := by
 decide +kernel
def pointBounds12043 : List (Nat × Nat × Nat) := [(1582439424,93372794198530,93373170170776),(1582489600,93373216998425,93373592970993),(1582539776,93373634626824,93374010599709)]
theorem point_links_checked12043 : (cuts12043.take 3).map (fun c => (1582432257-1+2*2^9*c.k,93372729630109+c.lower,93373105602304+c.upper)) = pointBounds12043 := by
 decide +kernel
def cuts12044 : List PrefixCut := [⟨26,221256060,221256231⟩,
⟨75,641525740,641526230⟩,
⟨124,1063916263,1063917073⟩,
⟨128,1098774002,1098774839⟩]
theorem checked12044 : checkPrefixCuts (2^48) 1582563329 9 Manual.Count131072.C012044.packed 128 cuts12044 = true := by
 decide +kernel
def pointBounds12044 : List (Nat × Nat × Nat) := [(1582589952,93374049929679,93374425902887),(1582640128,93374470199359,93374846172886),(1582690304,93374892589882,93375268563729)]
theorem point_links_checked12044 : (cuts12044.take 3).map (fun c => (1582563329-1+2*2^9*c.k,93373828673619+c.lower,93374204646656+c.upper)) = pointBounds12044 := by
 decide +kernel
def cuts12045 : List PrefixCut := [⟨45,390898473,390898776⟩,
⟨94,815751892,815752520⟩,
⟨128,1110420427,1110421278⟩]
theorem checked12045 : checkPrefixCuts (2^48) 1582694401 9 Manual.Count131072.C012045.packed 128 cuts12045 = true := by
 decide +kernel
def pointBounds12045 : List (Nat × Nat × Nat) := [(1582740480,93375318346094,93375694320271),(1582790656,93375743199513,93376119174015)]
theorem point_links_checked12045 : (cuts12045.take 2).map (fun c => (1582694401-1+2*2^9*c.k,93374927447621+c.lower,93375303421495+c.upper)) = pointBounds12045 := by
 decide +kernel
def cuts12046 : List PrefixCut := [⟨15,131949706,131949805⟩,
⟨64,558732323,558732750⟩,
⟨113,974476559,974477301⟩,
⟨128,1101971179,1101972020⟩]
theorem checked12046 : checkPrefixCuts (2^48) 1582825473 9 Manual.Count131072.C012046.packed 128 cuts12046 = true := by
 decide +kernel
def pointBounds12046 : List (Nat × Nat × Nat) := [(1582840832,93376169817754,93376545792578),(1582891008,93376596600371,93376972575523),(1582941184,93377012344607,93377388320074)]
theorem point_links_checked12046 : (cuts12046.take 3).map (fun c => (1582825473-1+2*2^9*c.k,93376037868048+c.lower,93376413842773+c.upper)) = pointBounds12046 := by
 decide +kernel
def cuts12047 : List PrefixCut := [⟨34,285569254,285569475⟩,
⟨83,716045207,716045753⟩,
⟨128,1111480786,1111481634⟩]
theorem checked12047 : checkPrefixCuts (2^48) 1582956545 9 Manual.Count131072.C012047.packed 128 cuts12047 = true := by
 decide +kernel
def pointBounds12047 : List (Nat × Nat × Nat) := [(1582991360,93377425408481,93377801384268),(1583041536,93377855884434,93378231860546)]
theorem point_links_checked12047 : (cuts12047.take 2).map (fun c => (1582956545-1+2*2^9*c.k,93377139839227+c.lower,93377515814793+c.upper)) = pointBounds12047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000063
