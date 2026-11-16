import PlattAssemblyKernel
import PlattCertificates.Count131072.C011984
import PlattCertificates.Count131072.C011985
import PlattCertificates.Count131072.C011986
import PlattCertificates.Count131072.C011987
import PlattCertificates.Count131072.C011988
import PlattCertificates.Count131072.C011989
import PlattCertificates.Count131072.C011990
import PlattCertificates.Count131072.C011991
import PlattCertificates.Count131072.C011992
import PlattCertificates.Count131072.C011993
import PlattCertificates.Count131072.C011994
import PlattCertificates.Count131072.C011995
import PlattCertificates.Count131072.C011996
import PlattCertificates.Count131072.C011997
import PlattCertificates.Count131072.C011998
import PlattCertificates.Count131072.C011999
import PlattCertificates.Count131072.C012000
import PlattCertificates.Count131072.C012001
import PlattCertificates.Count131072.C012002
import PlattCertificates.Count131072.C012003
import PlattCertificates.Count131072.C012004
import PlattCertificates.Count131072.C012005
import PlattCertificates.Count131072.C012006
import PlattCertificates.Count131072.C012007
import PlattCertificates.Count131072.C012008
import PlattCertificates.Count131072.C012009
import PlattCertificates.Count131072.C012010
import PlattCertificates.Count131072.C012011
import PlattCertificates.Count131072.C012012
import PlattCertificates.Count131072.C012013
import PlattCertificates.Count131072.C012014
import PlattCertificates.Count131072.C012015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11984 : List PrefixCut := [⟨13,111538511,111538598⟩,
⟨62,539630504,539630917⟩,
⟨111,966815108,966815850⟩,
⟨128,1113377381,1113378234⟩]
theorem checked11984 : checkPrefixCuts (2^48) 1574699009 9 Manual.Count131072.C011984.packed 128 cuts11984 = true := by
 decide +kernel
def pointBounds11984 : List (Nat × Nat × Nat) := [(1574712320,93307661125981,93308037048390),(1574762496,93308089217974,93308465140709),(1574812672,93308516402578,93308892325642)]
theorem point_links_checked11984 : (cuts11984.take 3).map (fun c => (1574699009-1+2*2^9*c.k,93307549587470+c.lower,93307925509792+c.upper)) = pointBounds11984 := by
 decide +kernel
def cuts11985 : List PrefixCut := [⟨32,286328056,286328276⟩,
⟨81,712413016,712413561⟩,
⟨128,1119540280,1119541133⟩]
theorem checked11985 : checkPrefixCuts (2^48) 1574830081 9 Manual.Count131072.C011985.packed 128 cuts11985 = true := by
 decide +kernel
def pointBounds11985 : List (Nat × Nat × Nat) := [(1574862848,93308949292907,93309325216302),(1574913024,93309375377867,93309751301587)]
theorem point_links_checked11985 : (cuts11985.take 2).map (fun c => (1574830081-1+2*2^9*c.k,93308662964851+c.lower,93309038888026+c.upper)) = pointBounds11985 := by
 decide +kernel
def cuts11986 : List PrefixCut := [⟨2,16263383,16263396⟩,
⟨51,439283076,439283409⟩,
⟨100,867650571,867651234⟩,
⟨128,1108724061,1108724907⟩]
theorem checked11986 : checkPrefixCuts (2^48) 1574961153 9 Manual.Count131072.C011986.packed 128 cuts11986 = true := by
 decide +kernel
def pointBounds11986 : List (Nat × Nat × Nat) := [(1574963200,93309798768514,93310174692555),(1575013376,93310221788207,93310597712568),(1575063552,93310650155702,93311026080393)]
theorem point_links_checked11986 : (cuts11986.take 3).map (fun c => (1574961153-1+2*2^9*c.k,93309782505131+c.lower,93310158429159+c.upper)) = pointBounds11986 := by
 decide +kernel
def cuts11987 : List PrefixCut := [⟨21,181204377,181204515⟩,
⟨70,596499536,596499996⟩,
⟨119,1023217868,1023218659⟩,
⟨128,1103092026,1103092881⟩]
theorem checked11987 : checkPrefixCuts (2^48) 1575092225 9 Manual.Count131072.C011987.packed 128 cuts11987 = true := by
 decide +kernel
def pointBounds11987 : List (Nat × Nat × Nat) := [(1575113728,93311072433569,93311448358581),(1575163904,93311487728728,93311863654062),(1575214080,93311914447060,93312290372725)]
theorem point_links_checked11987 : (cuts11987.take 3).map (fun c => (1575092225-1+2*2^9*c.k,93310891229192+c.lower,93311267154066+c.upper)) = pointBounds11987 := by
 decide +kernel
def cuts11988 : List PrefixCut := [⟨40,338789709,338789971⟩,
⟨89,770841346,770841938⟩,
⟨128,1101749724,1101750570⟩]
theorem checked11988 : checkPrefixCuts (2^48) 1575223297 9 Manual.Count131072.C011988.packed 128 cuts11988 = true := by
 decide +kernel
def pointBounds11988 : List (Nat × Nat × Nat) := [(1575264256,93312333110927,93312709036918),(1575314432,93312765162564,93313141088885)]
theorem point_links_checked11988 : (cuts11988.take 2).map (fun c => (1575223297-1+2*2^9*c.k,93311994321218+c.lower,93312370246947+c.upper)) = pointBounds11988 := by
 decide +kernel
def cuts11989 : List PrefixCut := [⟨10,87907321,87907388⟩,
⟨59,509747185,509747579⟩,
⟨108,942293467,942294192⟩,
⟨128,1112199412,1112200267⟩]
theorem checked11989 : checkPrefixCuts (2^48) 1575354369 9 Manual.Count131072.C011989.packed 128 cuts11989 = true := by
 decide +kernel
def pointBounds11989 : List (Nat × Nat × Nat) := [(1575364608,93313183978263,93313559904905),(1575414784,93313605818127,93313981745096),(1575464960,93314038364409,93314414291709)]
theorem point_links_checked11989 : (cuts11989.take 3).map (fun c => (1575354369-1+2*2^9*c.k,93313096070942+c.lower,93313471997517+c.upper)) = pointBounds11989 := by
 decide +kernel
def cuts11990 : List PrefixCut := [⟨29,254944206,254944402⟩,
⟨78,669240295,669240810⟩,
⟨127,1097993699,1097994540⟩,
⟨128,1106925916,1106926763⟩]
theorem checked11990 : checkPrefixCuts (2^48) 1575485441 9 Manual.Count131072.C011990.packed 128 cuts11990 = true := by
 decide +kernel
def pointBounds11990 : List (Nat × Nat × Nat) := [(1575515136,93314463214560,93314839142186),(1575565312,93314877510649,93315253438594),(1575615488,93315306264053,93315682192324)]
theorem point_links_checked11990 : (cuts11990.take 3).map (fun c => (1575485441-1+2*2^9*c.k,93314208270354+c.lower,93314584197784+c.upper)) = pointBounds11990 := by
 decide +kernel
def cuts11991 : List PrefixCut := [⟨48,412483261,412483574⟩,
⟨97,843352980,843353625⟩,
⟨128,1112371601,1112372450⟩]
theorem checked11991 : checkPrefixCuts (2^48) 1575616513 9 Manual.Count131072.C011991.packed 128 cuts11991 = true := by
 decide +kernel
def pointBounds11991 : List (Nat × Nat × Nat) := [(1575665664,93315727679531,93316103608121),(1575715840,93316158549250,93316534478172)]
theorem point_links_checked11991 : (cuts11991.take 2).map (fun c => (1575616513-1+2*2^9*c.k,93315315196270+c.lower,93315691124547+c.upper)) = pointBounds11991 := by
 decide +kernel
def cuts11992 : List PrefixCut := [⟨18,163623596,163623720⟩,
⟨67,570708796,570709235⟩,
⟨116,992784939,992785702⟩,
⟨128,1097453482,1097454325⟩]
theorem checked11992 : checkPrefixCuts (2^48) 1575747585 9 Manual.Count131072.C011992.packed 128 cuts11992 = true := by
 decide +kernel
def pointBounds11992 : List (Nat × Nat × Nat) := [(1575766016,93316591191467,93316967120717),(1575816192,93316998276667,93317374206232),(1575866368,93317420352810,93317796282699)]
theorem point_links_checked11992 : (cuts11992.take 3).map (fun c => (1575747585-1+2*2^9*c.k,93316427567871+c.lower,93316803496997+c.upper)) = pointBounds11992 := by
 decide +kernel
def cuts11993 : List PrefixCut := [⟨37,320430695,320430937⟩,
⟨86,741051142,741051705⟩,
⟨128,1101470218,1101471060⟩]
theorem checked11993 : checkPrefixCuts (2^48) 1575878657 9 Manual.Count131072.C011993.packed 128 cuts11993 = true := by
 decide +kernel
def pointBounds11993 : List (Nat × Nat × Nat) := [(1575916544,93317845452048,93318221382259),(1575966720,93318266072495,93318642003027)]
theorem point_links_checked11993 : (cuts11993.take 2).map (fun c => (1575878657-1+2*2^9*c.k,93317525021353+c.lower,93317900951322+c.upper)) = pointBounds11993 := by
 decide +kernel
def cuts11994 : List PrefixCut := [⟨7,56973173,56973217⟩,
⟨56,471315952,471316315⟩,
⟨105,888324457,888325138⟩,
⟨128,1088698131,1088698961⟩]
theorem checked11994 : checkPrefixCuts (2^48) 1576009729 9 Manual.Count131072.C011994.packed 128 cuts11994 = true := by
 decide +kernel
def pointBounds11994 : List (Nat × Nat × Nat) := [(1576016896,93318683464744,93319059395599),(1576067072,93319097807523,93319473738697),(1576117248,93319514816028,93319890747520)]
theorem point_links_checked11994 : (cuts11994.take 3).map (fun c => (1576009729-1+2*2^9*c.k,93318626491571+c.lower,93319002422382+c.upper)) = pointBounds11994 := by
 decide +kernel
def cuts11995 : List PrefixCut := [⟨26,218407419,218407587⟩,
⟨75,653604346,653604847⟩,
⟨124,1079144494,1079145324⟩,
⟨128,1114679970,1114680828⟩]
theorem checked11995 : checkPrefixCuts (2^48) 1576140801 9 Manual.Count131072.C011995.packed 128 cuts11995 = true := by
 decide +kernel
def pointBounds11995 : List (Nat × Nat × Nat) := [(1576167424,93319933597121,93320309528930),(1576217600,93320368794048,93320744726190),(1576267776,93320794334196,93321170266667)]
theorem point_links_checked11995 : (cuts11995.take 3).map (fun c => (1576140801-1+2*2^9*c.k,93319715189702+c.lower,93320091121343+c.upper)) = pointBounds11995 := by
 decide +kernel
def cuts11996 : List PrefixCut := [⟨45,379991477,379991772⟩,
⟨94,806754496,806755111⟩,
⟨128,1096731329,1096732168⟩]
theorem checked11996 : checkPrefixCuts (2^48) 1576271873 9 Manual.Count131072.C011996.packed 128 cuts11996 = true := by
 decide +kernel
def pointBounds11996 : List (Nat × Nat × Nat) := [(1576317952,93321209861149,93321585793943),(1576368128,93321636624168,93322012557282)]
theorem point_links_checked11996 : (cuts11996.take 2).map (fun c => (1576271873-1+2*2^9*c.k,93320829869672+c.lower,93321205802171+c.upper)) = pointBounds11996 := by
 decide +kernel
def cuts11997 : List PrefixCut := [⟨15,136236921,136237025⟩,
⟨64,563329984,563330421⟩,
⟨113,995944240,995945006⟩,
⟨128,1131814068,1131814939⟩]
theorem checked11997 : checkPrefixCuts (2^48) 1576402945 9 Manual.Count131072.C011997.packed 128 cuts11997 = true := by
 decide +kernel
def pointBounds11997 : List (Nat × Nat × Nat) := [(1576418304,93322062837922,93322438771364),(1576468480,93322489930985,93322865864760),(1576518656,93322922545241,93323298479345)]
theorem point_links_checked11997 : (cuts11997.take 3).map (fun c => (1576402945-1+2*2^9*c.k,93321926601001+c.lower,93322302534339+c.upper)) = pointBounds11997 := by
 decide +kernel
def cuts11998 : List PrefixCut := [⟨34,294231165,294231391⟩,
⟨83,720390744,720391297⟩,
⟨128,1111188736,1111189585⟩]
theorem checked11998 : checkPrefixCuts (2^48) 1576534017 9 Manual.Count131072.C011998.packed 128 cuts11998 = true := by
 decide +kernel
def pointBounds11998 : List (Nat × Nat × Nat) := [(1576568832,93323352646234,93323728580669),(1576619008,93323778805813,93324154740575)]
theorem point_links_checked11998 : (cuts11998.take 2).map (fun c => (1576534017-1+2*2^9*c.k,93323058415069+c.lower,93323434349278+c.upper)) = pointBounds11998 := by
 decide +kernel
def cuts11999 : List PrefixCut := [⟨4,34455370,34455397⟩,
⟨53,462908561,462908917⟩,
⟨102,892776246,892776925⟩,
⟨128,1117880042,1117880893⟩]
theorem checked11999 : checkPrefixCuts (2^48) 1576665089 9 Manual.Count131072.C011999.packed 128 cuts11999 = true := by
 decide +kernel
def pointBounds11999 : List (Nat × Nat × Nat) := [(1576669184,93324204059175,93324579994260),(1576719360,93324632512366,93325008447780),(1576769536,93325062380051,93325438315788)]
theorem point_links_checked11999 : (cuts11999.take 3).map (fun c => (1576665089-1+2*2^9*c.k,93324169603805+c.lower,93324545538863+c.upper)) = pointBounds11999 := by
 decide +kernel
def cuts12000 : List PrefixCut := [⟨23,190469418,190469566⟩,
⟨72,605493820,605494289⟩,
⟨121,1036569924,1036570725⟩,
⟨128,1096187653,1096188501⟩]
theorem checked12000 : checkPrefixCuts (2^48) 1576796161 9 Manual.Count131072.C012000.packed 128 cuts12000 = true := by
 decide +kernel
def pointBounds12000 : List (Nat × Nat × Nat) := [(1576819712,93325477953265,93325853889322),(1576869888,93325892977667,93326268914045),(1576920064,93326324053771,93326699990481)]
theorem point_links_checked12000 : (cuts12000.take 3).map (fun c => (1576796161-1+2*2^9*c.k,93325287483847+c.lower,93325663419756+c.upper)) = pointBounds12000 := by
 decide +kernel
def cuts12001 : List PrefixCut := [⟨42,365554350,365554632⟩,
⟨91,787143340,787143947⟩,
⟨128,1110554696,1110555548⟩]
theorem checked12001 : checkPrefixCuts (2^48) 1576927233 9 Manual.Count131072.C012001.packed 128 cuts12001 = true := by
 decide +kernel
def pointBounds12001 : List (Nat × Nat × Nat) := [(1576970240,93326749225850,93327125162889),(1577020416,93327170814840,93327546752204)]
theorem point_links_checked12001 : (cuts12001.take 2).map (fun c => (1576927233-1+2*2^9*c.k,93326383671500+c.lower,93326759608257+c.upper)) = pointBounds12001 := by
 decide +kernel
def cuts12002 : List PrefixCut := [⟨12,103161597,103161676⟩,
⟨61,522581844,522582246⟩,
⟨110,935563802,935564520⟩,
⟨128,1090473329,1090474163⟩]
theorem checked12002 : checkPrefixCuts (2^48) 1577058305 9 Manual.Count131072.C012002.packed 128 cuts12002 = true := by
 decide +kernel
def pointBounds12002 : List (Nat × Nat × Nat) := [(1577070592,93327597387793,93327973325481),(1577120768,93328016808040,93328392746051),(1577170944,93328429789998,93328805728325)]
theorem point_links_checked12002 : (cuts12002.take 3).map (fun c => (1577058305-1+2*2^9*c.k,93327494226196+c.lower,93327870163805+c.upper)) = pointBounds12002 := by
 decide +kernel
def cuts12003 : List PrefixCut := [⟨31,261985616,261985821⟩,
⟨80,680651991,680652515⟩,
⟨128,1092167000,1092167842⟩]
theorem checked12003 : checkPrefixCuts (2^48) 1577189377 9 Manual.Count131072.C012003.packed 128 cuts12003 = true := by
 decide +kernel
def pointBounds12003 : List (Nat × Nat × Nat) := [(1577221120,93328846685141,93329222623789),(1577271296,93329265351516,93329641290483)]
theorem point_links_checked12003 : (cuts12003.take 2).map (fun c => (1577189377-1+2*2^9*c.k,93328584699525+c.lower,93328960637968+c.upper)) = pointBounds12003 := by
 decide +kernel
def cuts12004 : List PrefixCut := [⟨1,8208757,8208763⟩,
⟨50,420959658,420959986⟩,
⟨99,845831609,845832258⟩,
⟨128,1102961012,1102961860⟩]
theorem checked12004 : checkPrefixCuts (2^48) 1577320449 9 Manual.Count131072.C012004.packed 128 cuts12004 = true := by
 decide +kernel
def pointBounds12004 : List (Nat × Nat × Nat) := [(1577321472,93329685075282,93330061014573),(1577371648,93330097826183,93330473765796),(1577421824,93330522698134,93330898638068)]
theorem point_links_checked12004 : (cuts12004.take 3).map (fun c => (1577320449-1+2*2^9*c.k,93329676866525+c.lower,93330052805810+c.upper)) = pointBounds12004 := by
 decide +kernel
def cuts12005 : List PrefixCut := [⟨20,182539308,182539446⟩,
⟨69,610417518,610417983⟩,
⟨118,1035962754,1035963540⟩,
⟨128,1121783830,1121784682⟩]
theorem checked12005 : checkPrefixCuts (2^48) 1577451521 9 Manual.Count131072.C012005.packed 128 cuts12005 = true := by
 decide +kernel
def pointBounds12005 : List (Nat × Nat × Nat) := [(1577472000,93330962366845,93331338307116),(1577522176,93331390245055,93331766185653),(1577572352,93331815790291,93332191731210)]
theorem point_links_checked12005 : (cuts12005.take 3).map (fun c => (1577451521-1+2*2^9*c.k,93330779827537+c.lower,93331155767670+c.upper)) = pointBounds12005 := by
 decide +kernel
def cuts12006 : List PrefixCut := [⟨39,335785234,335785493⟩,
⟨88,767726245,767726834⟩,
⟨128,1111520697,1111521550⟩]
theorem checked12006 : checkPrefixCuts (2^48) 1577582593 9 Manual.Count131072.C012006.packed 128 cuts12006 = true := by
 decide +kernel
def pointBounds12006 : List (Nat × Nat × Nat) := [(1577622528,93332237396601,93332613337845),(1577672704,93332669337612,93333045279186)]
theorem point_links_checked12006 : (cuts12006.take 2).map (fun c => (1577582593-1+2*2^9*c.k,93331901611367+c.lower,93332277552352+c.upper)) = pointBounds12006 := by
 decide +kernel
def cuts12007 : List PrefixCut := [⟨9,82602115,82602178⟩,
⟨58,515942831,515943228⟩,
⟨107,945523454,945524179⟩,
⟨128,1123381507,1123382371⟩]
theorem checked12007 : checkPrefixCuts (2^48) 1577713665 9 Manual.Count131072.C012007.packed 128 cuts12007 = true := by
 decide +kernel
def pointBounds12007 : List (Nat × Nat × Nat) := [(1577722880,93333095734179,93333471676080),(1577773056,93333529074895,93333905017130),(1577823232,93333958655518,93334334598081)]
theorem point_links_checked12007 : (cuts12007.take 3).map (fun c => (1577713665-1+2*2^9*c.k,93333013132064+c.lower,93333389073902+c.upper)) = pointBounds12007 := by
 decide +kernel
def cuts12008 : List PrefixCut := [⟨28,243681229,243681412⟩,
⟨77,669845190,669845700⟩,
⟨126,1096709071,1096709907⟩,
⟨128,1114903555,1114904405⟩]
theorem checked12008 : checkPrefixCuts (2^48) 1577844737 9 Manual.Count131072.C012008.packed 128 cuts12008 = true := by
 decide +kernel
def pointBounds12008 : List (Nat × Nat × Nat) := [(1577873408,93334380194800,93334756137685),(1577923584,93334806358761,93335182301973),(1577973760,93335233222642,93335609166180)]
theorem point_links_checked12008 : (cuts12008.take 3).map (fun c => (1577844737-1+2*2^9*c.k,93334136513571+c.lower,93334512456273+c.upper)) = pointBounds12008 := by
 decide +kernel
def cuts12009 : List PrefixCut := [⟨47,404196473,404196781⟩,
⟨96,825503786,825504412⟩,
⟨128,1098044295,1098045133⟩]
theorem checked12009 : checkPrefixCuts (2^48) 1577975809 9 Manual.Count131072.C012009.packed 128 cuts12009 = true := by
 decide +kernel
def pointBounds12009 : List (Nat × Nat × Nat) := [(1578023936,93335655613599,93336031557459),(1578074112,93336076920912,93336452865090)]
theorem point_links_checked12009 : (cuts12009.take 2).map (fun c => (1577975809-1+2*2^9*c.k,93335251417126+c.lower,93335627360678+c.upper)) = pointBounds12009 := by
 decide +kernel
def cuts12010 : List PrefixCut := [⟨17,143402531,143402640⟩,
⟨66,571282383,571282815⟩,
⟨115,996294971,996295730⟩,
⟨128,1108832755,1108833599⟩]
theorem checked12010 : checkPrefixCuts (2^48) 1578106881 9 Manual.Count131072.C012010.packed 128 cuts12010 = true := by
 decide +kernel
def pointBounds12010 : List (Nat × Nat × Nat) := [(1578124288,93336492863952,93336868808451),(1578174464,93336920743804,93337296688626),(1578224640,93337345756392,93337721701541)]
theorem point_links_checked12010 : (cuts12010.take 3).map (fun c => (1578106881-1+2*2^9*c.k,93336349461421+c.lower,93336725405811+c.upper)) = pointBounds12010 := by
 decide +kernel
def cuts12011 : List PrefixCut := [⟨36,305862469,305862703⟩,
⟨85,727994451,727995006⟩,
⟨128,1094295049,1094295885⟩]
theorem checked12011 : checkPrefixCuts (2^48) 1578237953 9 Manual.Count131072.C012011.packed 128 cuts12011 = true := by
 decide +kernel
def pointBounds12011 : List (Nat × Nat × Nat) := [(1578274816,93337764156645,93338140102113),(1578324992,93338186288627,93338562234416)]
theorem point_links_checked12011 : (cuts12011.take 2).map (fun c => (1578237953-1+2*2^9*c.k,93337458294176+c.lower,93337834239410+c.upper)) = pointBounds12011 := by
 decide +kernel
def cuts12012 : List PrefixCut := [⟨6,50646396,50646437⟩,
⟨55,480776513,480776879⟩,
⟨104,911427942,911428634⟩,
⟨128,1127907606,1127908466⟩]
theorem checked12012 : checkPrefixCuts (2^48) 1578369025 9 Manual.Count131072.C012012.packed 128 cuts12012 = true := by
 decide +kernel
def pointBounds12012 : List (Nat × Nat × Nat) := [(1578375168,93338603235621,93338979181732),(1578425344,93339033365738,93339409312174),(1578475520,93339464017167,93339839963929)]
theorem point_links_checked12012 : (cuts12012.take 3).map (fun c => (1578369025-1+2*2^9*c.k,93338552589225+c.lower,93338928535295+c.upper)) = pointBounds12012 := by
 decide +kernel
def cuts12013 : List PrefixCut := [⟨25,216832878,216833042⟩,
⟨74,629625637,629626116⟩,
⟨123,1056669838,1056670642⟩,
⟨128,1098214534,1098215369⟩]
theorem checked12013 : checkPrefixCuts (2^48) 1578500097 9 Manual.Count131072.C012013.packed 128 cuts12013 = true := by
 decide +kernel
def pointBounds12013 : List (Nat × Nat × Nat) := [(1578525696,93339897329709,93340273276803),(1578575872,93340310122468,93340686069877),(1578626048,93340737166669,93341113114403)]
theorem point_links_checked12013 : (cuts12013.take 3).map (fun c => (1578500097-1+2*2^9*c.k,93339680496831+c.lower,93340056443761+c.upper)) = pointBounds12013 := by
 decide +kernel
def cuts12014 : List PrefixCut := [⟨44,387982057,387982349⟩,
⟨93,805549405,805550018⟩,
⟨128,1114169948,1114170793⟩]
theorem checked12014 : checkPrefixCuts (2^48) 1578631169 9 Manual.Count131072.C012014.packed 128 cuts12014 = true := by
 decide +kernel
def pointBounds12014 : List (Nat × Nat × Nat) := [(1578676224,93341166693422,93341542641479),(1578726400,93341584260770,93341960209148)]
theorem point_links_checked12014 : (cuts12014.take 2).map (fun c => (1578631169-1+2*2^9*c.k,93340778711365+c.lower,93341154659130+c.upper)) = pointBounds12014 := by
 decide +kernel
def cuts12015 : List PrefixCut := [⟨14,123909813,123909907⟩,
⟨63,545372930,545373348⟩,
⟨112,961652563,961653303⟩,
⟨128,1100528366,1100529211⟩]
theorem checked12015 : checkPrefixCuts (2^48) 1578762241 9 Manual.Count131072.C012015.packed 128 cuts12015 = true := by
 decide +kernel
def pointBounds12015 : List (Nat × Nat × Nat) := [(1578776576,93342016791126,93342392739830),(1578826752,93342438254243,93342814203271),(1578876928,93342854533876,93343230483226)]
theorem point_links_checked12015 : (cuts12015.take 3).map (fun c => (1578762241-1+2*2^9*c.k,93341892881313+c.lower,93342268829923+c.upper)) = pointBounds12015 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000062
