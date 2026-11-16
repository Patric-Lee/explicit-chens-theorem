import PlattAssemblyKernel
import PlattCertificates.Count131072.C012336
import PlattCertificates.Count131072.C012337
import PlattCertificates.Count131072.C012338
import PlattCertificates.Count131072.C012339
import PlattCertificates.Count131072.C012340
import PlattCertificates.Count131072.C012341
import PlattCertificates.Count131072.C012342
import PlattCertificates.Count131072.C012343
import PlattCertificates.Count131072.C012344
import PlattCertificates.Count131072.C012345
import PlattCertificates.Count131072.C012346
import PlattCertificates.Count131072.C012347
import PlattCertificates.Count131072.C012348
import PlattCertificates.Count131072.C012349
import PlattCertificates.Count131072.C012350
import PlattCertificates.Count131072.C012351
import PlattCertificates.Count131072.C012352
import PlattCertificates.Count131072.C012353
import PlattCertificates.Count131072.C012354
import PlattCertificates.Count131072.C012355
import PlattCertificates.Count131072.C012356
import PlattCertificates.Count131072.C012357
import PlattCertificates.Count131072.C012358
import PlattCertificates.Count131072.C012359
import PlattCertificates.Count131072.C012360
import PlattCertificates.Count131072.C012361
import PlattCertificates.Count131072.C012362
import PlattCertificates.Count131072.C012363
import PlattCertificates.Count131072.C012364
import PlattCertificates.Count131072.C012365
import PlattCertificates.Count131072.C012366
import PlattCertificates.Count131072.C012367
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12336 : List PrefixCut := [⟨40,339154217,339154474⟩,
⟨90,758526601,758527171⟩,
⟨128,1078386769,1078387580⟩]
theorem checked12336 : checkPrefixCuts (2^48) 1620836353 9 Manual.Count131072.C012336.packed 128 cuts12336 = true := by
 decide +kernel
def pointBounds12336 : List (Nat × Nat × Nat) := [(1620877312,93691480094980,93691856308498),(1620928512,93691899467364,93692275681195)]
theorem point_links_checked12336 : (cuts12336.take 2).map (fun c => (1620836353-1+2*2^9*c.k,93691140940763+c.lower,93691517154024+c.upper)) = pointBounds12336 := by
 decide +kernel
def cuts12337 : List PrefixCut := [⟨12,97936106,97936181⟩,
⟨62,527874052,527874448⟩,
⟨112,945470423,945471131⟩,
⟨128,1079167890,1079168702⟩]
theorem checked12337 : checkPrefixCuts (2^48) 1620967425 9 Manual.Count131072.C012337.packed 128 cuts12337 = true := by
 decide +kernel
def pointBounds12337 : List (Nat × Nat × Nat) := [(1620979712,93692317263638,93692693477785),(1621030912,93692747201584,93693123416052),(1621082112,93693164797955,93693541012735)]
theorem point_links_checked12337 : (cuts12337.take 3).map (fun c => (1620967425-1+2*2^9*c.k,93692219327532+c.lower,93692595541604+c.upper)) = pointBounds12337 := by
 decide +kernel
def cuts12338 : List PrefixCut := [⟨34,286490001,286490214⟩,
⟨84,711004825,711005350⟩,
⟨128,1082552866,1082553667⟩]
theorem checked12338 : checkPrefixCuts (2^48) 1621098497 9 Manual.Count131072.C012338.packed 128 cuts12338 = true := by
 decide +kernel
def pointBounds12338 : List (Nat × Nat × Nat) := [(1621133312,93693584985423,93693961200520),(1621184512,93694009500247,93694385715656)]
theorem point_links_checked12338 : (cuts12338.take 2).map (fun c => (1621098497-1+2*2^9*c.k,93693298495422+c.lower,93693674710306+c.upper)) = pointBounds12338 := by
 decide +kernel
def cuts12339 : List PrefixCut := [⟨6,47918519,47918555⟩,
⟨56,477094244,477094595⟩,
⟨106,887159414,887160072⟩,
⟨128,1070660236,1070661030⟩]
theorem checked12339 : checkPrefixCuts (2^48) 1621229569 9 Manual.Count131072.C012339.packed 128 cuts12339 = true := by
 decide +kernel
def pointBounds12339 : List (Nat × Nat × Nat) := [(1621235712,93694428966807,93694805182528),(1621286912,93694858142532,93695234358568),(1621338112,93695268207702,93695644424045)]
theorem point_links_checked12339 : (cuts12339.take 3).map (fun c => (1621229569-1+2*2^9*c.k,93694381048288+c.lower,93694757263973+c.upper)) = pointBounds12339 := by
 decide +kernel
def cuts12340 : List PrefixCut := [⟨28,242870018,242870199⟩,
⟨78,661936291,661936792⟩,
⟨128,1086370620,1086371442⟩]
theorem checked12340 : checkPrefixCuts (2^48) 1621360641 9 Manual.Count131072.C012340.packed 128 cuts12340 = true := by
 decide +kernel
def pointBounds12340 : List (Nat × Nat × Nat) := [(1621389312,93695694578542,93696070795202),(1621440512,93696113644815,93696489861795),(1621491712,93696538079144,93696914296445)]
theorem point_links_checked12340 : (cuts12340.take 3).map (fun c => (1621360641-1+2*2^9*c.k,93695451708524+c.lower,93695827925003+c.upper)) = pointBounds12340 := by
 decide +kernel
def cuts12341 : List PrefixCut := [⟨50,417304023,417304337⟩,
⟨100,839628540,839629172⟩,
⟨128,1065800120,1065800922⟩]
theorem checked12341 : checkPrefixCuts (2^48) 1621491713 9 Manual.Count131072.C012341.packed 128 cuts12341 = true := by
 decide +kernel
def pointBounds12341 : List (Nat × Nat × Nat) := [(1621542912,93696955383167,93697331600782),(1621594112,93697377707684,93697753925617)]
theorem point_links_checked12341 : (cuts12341.take 2).map (fun c => (1621491713-1+2*2^9*c.k,93696538079144+c.lower,93696914296445+c.upper)) = pointBounds12341 := by
 decide +kernel
def cuts12342 : List PrefixCut := [⟨22,183815767,183815907⟩,
⟨72,608543831,608544296⟩,
⟨122,1034299721,1034300505⟩,
⟨128,1082897175,1082897995⟩]
theorem checked12342 : checkPrefixCuts (2^48) 1621622785 9 Manual.Count131072.C012342.packed 128 cuts12342 = true := by
 decide +kernel
def pointBounds12342 : List (Nat × Nat × Nat) := [(1621645312,93697787695031,93698163913274),(1621696512,93698212423095,93698588641663),(1621747712,93698638178985,93699014397872)]
theorem point_links_checked12342 : (cuts12342.take 3).map (fun c => (1621622785-1+2*2^9*c.k,93697603879264+c.lower,93697980097367+c.upper)) = pointBounds12342 := by
 decide +kernel
def cuts12343 : List PrefixCut := [⟨44,371244037,371244316⟩,
⟨94,799749853,799750455⟩,
⟨128,1082115485,1082116298⟩]
theorem checked12343 : checkPrefixCuts (2^48) 1621753857 9 Manual.Count131072.C012343.packed 128 cuts12343 = true := by
 decide +kernel
def pointBounds12343 : List (Nat × Nat × Nat) := [(1621798912,93699058020476,93699434239678),(1621850112,93699486526292,93699862745817)]
theorem point_links_checked12343 : (cuts12343.take 2).map (fun c => (1621753857-1+2*2^9*c.k,93698686776439+c.lower,93699062995362+c.upper)) = pointBounds12343 := by
 decide +kernel
def cuts12344 : List PrefixCut := [⟨16,128424868,128424965⟩,
⟨66,543020300,543020709⟩,
⟨116,969403115,969403845⟩,
⟨128,1067103106,1067103910⟩]
theorem checked12344 : checkPrefixCuts (2^48) 1621884929 9 Manual.Count131072.C012344.packed 128 cuts12344 = true := by
 decide +kernel
def pointBounds12344 : List (Nat × Nat × Nat) := [(1621901312,93699897316792,93700273536625),(1621952512,93700311912224,93700688132369),(1622003712,93700738295039,93701114515505)]
theorem point_links_checked12344 : (cuts12344.take 3).map (fun c => (1621884929-1+2*2^9*c.k,93699768891924+c.lower,93700145111660+c.upper)) = pointBounds12344 := by
 decide +kernel
def cuts12345 : List PrefixCut := [⟨38,308192602,308192836⟩,
⟨88,727780967,727781515⟩,
⟨128,1064934474,1064935277⟩]
theorem checked12345 : checkPrefixCuts (2^48) 1622016001 9 Manual.Count131072.C012345.packed 128 cuts12345 = true := by
 decide +kernel
def pointBounds12345 : List (Nat × Nat × Nat) := [(1622054912,93701144187632,93701520408406),(1622106112,93701563775997,93701939997085)]
theorem point_links_checked12345 : (cuts12345.take 2).map (fun c => (1622016001-1+2*2^9*c.k,93700835995030+c.lower,93701212215570+c.upper)) = pointBounds12345 := by
 decide +kernel
def cuts12346 : List PrefixCut := [⟨10,79298365,79298424⟩,
⟨60,498513268,498513644⟩,
⟨110,922052783,922053476⟩,
⟨128,1073697803,1073698607⟩]
theorem checked12346 : checkPrefixCuts (2^48) 1622147073 9 Manual.Count131072.C012346.packed 128 cuts12346 = true := by
 decide +kernel
def pointBounds12346 : List (Nat × Nat × Nat) := [(1622157312,93701980227869,93702356449271),(1622208512,93702399442772,93702775664491),(1622259712,93702822982287,93703199204323)]
theorem point_links_checked12346 : (cuts12346.take 3).map (fun c => (1622147073-1+2*2^9*c.k,93701900929504+c.lower,93702277150847+c.upper)) = pointBounds12346 := by
 decide +kernel
def cuts12347 : List PrefixCut := [⟨32,267196419,267196621⟩,
⟨82,687586179,687586697⟩,
⟨128,1076040132,1076040938⟩]
theorem checked12347 : checkPrefixCuts (2^48) 1622278145 9 Manual.Count131072.C012347.packed 128 cuts12347 = true := by
 decide +kernel
def pointBounds12347 : List (Nat × Nat × Nat) := [(1622310912,93703241823726,93703618046075),(1622362112,93703662213486,93704038436151)]
theorem point_links_checked12347 : (cuts12347.take 2).map (fun c => (1622278145-1+2*2^9*c.k,93702974627307+c.lower,93703350849454+c.upper)) = pointBounds12347 := by
 decide +kernel
def cuts12348 : List PrefixCut := [⟨4,33136913,33136938⟩,
⟨54,448122022,448122360⟩,
⟨104,862400028,862400676⟩,
⟨128,1066931995,1066932795⟩]
theorem checked12348 : checkPrefixCuts (2^48) 1622409217 9 Manual.Count131072.C012348.packed 128 cuts12348 = true := by
 decide +kernel
def pointBounds12348 : List (Nat × Nat × Nat) := [(1622413312,93704083804352,93704460027330),(1622464512,93704498789461,93704875012752),(1622515712,93704913067467,93705289291068)]
theorem point_links_checked12348 : (cuts12348.take 3).map (fun c => (1622409217-1+2*2^9*c.k,93704050667439+c.lower,93704426890392+c.upper)) = pointBounds12348 := by
 decide +kernel
def cuts12349 : List PrefixCut := [⟨26,218406893,218407057⟩,
⟨76,636648627,636649111⟩,
⟨126,1062336178,1062336981⟩,
⟨128,1078294865,1078295681⟩]
theorem checked12349 : checkPrefixCuts (2^48) 1622540289 9 Manual.Count131072.C012349.packed 128 cuts12349 = true := by
 decide +kernel
def pointBounds12349 : List (Nat × Nat × Nat) := [(1622566912,93705336006327,93705712230244),(1622618112,93705754248061,93706130472298),(1622669312,93706179935612,93706556160168)]
theorem point_links_checked12349 : (cuts12349.take 3).map (fun c => (1622540289-1+2*2^9*c.k,93705117599434+c.lower,93705493823187+c.upper)) = pointBounds12349 := by
 decide +kernel
def cuts12350 : List PrefixCut := [⟨48,395144700,395145003⟩,
⟨98,814907916,814908533⟩,
⟨128,1070401997,1070402807⟩]
theorem checked12350 : checkPrefixCuts (2^48) 1622671361 9 Manual.Count131072.C012350.packed 128 cuts12350 = true := by
 decide +kernel
def pointBounds12350 : List (Nat × Nat × Nat) := [(1622720512,93706591038999,93706967263871),(1622771712,93707010802215,93707387027401)]
theorem point_links_checked12350 : (cuts12350.take 2).map (fun c => (1622671361-1+2*2^9*c.k,93706195894299+c.lower,93706572118868+c.upper)) = pointBounds12350 := by
 decide +kernel
def cuts12351 : List PrefixCut := [⟨20,166163961,166164086⟩,
⟨70,584513095,584513528⟩,
⟨120,1006664812,1006665562⟩,
⟨128,1078987751,1078988554⟩]
theorem checked12351 : checkPrefixCuts (2^48) 1622802433 9 Manual.Count131072.C012351.packed 128 cuts12351 = true := by
 decide +kernel
def pointBounds12351 : List (Nat × Nat × Nat) := [(1622822912,93707432460257,93707808685761),(1622874112,93707850809391,93708227035203),(1622925312,93708272961108,93708649187237)]
theorem point_links_checked12351 : (cuts12351.take 3).map (fun c => (1622802433-1+2*2^9*c.k,93707266296296+c.lower,93707642521675+c.upper)) = pointBounds12351 := by
 decide +kernel
def cuts12352 : List PrefixCut := [⟨42,349121700,349121963⟩,
⟨92,762401803,762402375⟩,
⟨128,1060690755,1060691551⟩]
theorem checked12352 : checkPrefixCuts (2^48) 1622933505 9 Manual.Count131072.C012352.packed 128 cuts12352 = true := by
 decide +kernel
def pointBounds12352 : List (Nat × Nat × Nat) := [(1622976512,93708694405747,93709070632192),(1623027712,93709107685850,93709483912604)]
theorem point_links_checked12352 : (cuts12352.take 2).map (fun c => (1622933505-1+2*2^9*c.k,93708345284047+c.lower,93708721510229+c.upper)) = pointBounds12352 := by
 decide +kernel
def cuts12353 : List PrefixCut := [⟨14,116538979,116539065⟩,
⟨64,536903180,536903581⟩,
⟨114,951358140,951358852⟩,
⟨128,1065807843,1065808639⟩]
theorem checked12353 : checkPrefixCuts (2^48) 1623064577 9 Manual.Count131072.C012353.packed 128 cuts12353 = true := by
 decide +kernel
def pointBounds12353 : List (Nat × Nat × Nat) := [(1623078912,93709522513781,93709898740845),(1623130112,93709942877982,93710319105361),(1623181312,93710357332942,93710733560632)]
theorem point_links_checked12353 : (cuts12353.take 3).map (fun c => (1623064577-1+2*2^9*c.k,93709405974802+c.lower,93709782201780+c.upper)) = pointBounds12353 := by
 decide +kernel
def cuts12354 : List PrefixCut := [⟨36,297217693,297217915⟩,
⟨86,722917618,722918159⟩,
⟨128,1077686073,1077686880⟩]
theorem checked12354 : checkPrefixCuts (2^48) 1623195649 9 Manual.Count131072.C012354.packed 128 cuts12354 = true := by
 decide +kernel
def pointBounds12354 : List (Nat × Nat × Nat) := [(1623232512,93710769000338,93711145228334),(1623283712,93711194700263,93711570928578)]
theorem point_links_checked12354 : (cuts12354.take 2).map (fun c => (1623195649-1+2*2^9*c.k,93710471782645+c.lower,93710848010419+c.upper)) = pointBounds12354 := by
 decide +kernel
def cuts12355 : List PrefixCut := [⟨8,67276640,67276691⟩,
⟨58,480292178,480292537⟩,
⟨108,898149510,898150181⟩,
⟨128,1064941959,1064942755⟩]
theorem checked12355 : checkPrefixCuts (2^48) 1623326721 9 Manual.Count131072.C012355.packed 128 cuts12355 = true := by
 decide +kernel
def pointBounds12355 : List (Nat × Nat × Nat) := [(1623334912,93711616745358,93711992973990),(1623386112,93712029760896,93712405989836),(1623437312,93712447618228,93712823847480)]
theorem point_links_checked12355 : (cuts12355.take 3).map (fun c => (1623326721-1+2*2^9*c.k,93711549468718+c.lower,93711925697299+c.upper)) = pointBounds12355 := by
 decide +kernel
def cuts12356 : List PrefixCut := [⟨30,247064013,247064199⟩,
⟨80,657959963,657960454⟩,
⟨128,1062255231,1062256024⟩]
theorem checked12356 : checkPrefixCuts (2^48) 1623457793 9 Manual.Count131072.C012356.packed 128 cuts12356 = true := by
 decide +kernel
def pointBounds12356 : List (Nat × Nat × Nat) := [(1623488512,93712861474690,93713237704253),(1623539712,93713272370640,93713648600508)]
theorem point_links_checked12356 : (cuts12356.take 2).map (fun c => (1623457793-1+2*2^9*c.k,93712614410677+c.lower,93712990640054+c.upper)) = pointBounds12356 := by
 decide +kernel
def cuts12357 : List PrefixCut := [⟨2,17336574,17336587⟩,
⟨52,435487747,435488078⟩,
⟨102,854492656,854493302⟩,
⟨128,1071357598,1071358404⟩]
theorem checked12357 : checkPrefixCuts (2^48) 1623588865 9 Manual.Count131072.C012357.packed 128 cuts12357 = true := by
 decide +kernel
def pointBounds12357 : List (Nat × Nat × Nat) := [(1623590912,93713694002482,93714070232665),(1623642112,93714112153655,93714488384156),(1623693312,93714531158564,93714907389380)]
theorem point_links_checked12357 : (cuts12357.take 3).map (fun c => (1623588865-1+2*2^9*c.k,93713676665908+c.lower,93714052896078+c.upper)) = pointBounds12357 := by
 decide +kernel
def cuts12358 : List PrefixCut := [⟨24,194846025,194846169⟩,
⟨74,612091122,612091577⟩,
⟨124,1030536482,1030537252⟩,
⟨128,1065030759,1065031555⟩]
theorem checked12358 : checkPrefixCuts (2^48) 1623719937 9 Manual.Count131072.C012358.packed 128 cuts12358 = true := by
 decide +kernel
def pointBounds12358 : List (Nat × Nat × Nat) := [(1623744512,93714942869531,93715319100651),(1623795712,93715360114628,93715736346059),(1623846912,93715778559988,93716154791734)]
theorem point_links_checked12358 : (cuts12358.take 3).map (fun c => (1623719937-1+2*2^9*c.k,93714748023506+c.lower,93715124254482+c.upper)) = pointBounds12358 := by
 decide +kernel
def cuts12359 : List PrefixCut := [⟨46,381164420,381164709⟩,
⟨96,806689905,806690517⟩,
⟨128,1075864579,1075865392⟩]
theorem checked12359 : checkPrefixCuts (2^48) 1623851009 9 Manual.Count131072.C012359.packed 128 cuts12359 = true := by
 decide +kernel
def pointBounds12359 : List (Nat × Nat × Nat) := [(1623898112,93716194218685,93716570450746),(1623949312,93716619744170,93716995976554)]
theorem point_links_checked12359 : (cuts12359.take 2).map (fun c => (1623851009-1+2*2^9*c.k,93715813054265+c.lower,93716189286037+c.upper)) = pointBounds12359 := by
 decide +kernel
def cuts12360 : List PrefixCut := [⟨18,150444295,150444408⟩,
⟨68,567970179,567970606⟩,
⟨118,976470545,976471280⟩,
⟨128,1061739280,1061740079⟩]
theorem checked12360 : checkPrefixCuts (2^48) 1623982081 9 Manual.Count131072.C012360.packed 128 cuts12360 = true := by
 decide +kernel
def pointBounds12360 : List (Nat × Nat × Nat) := [(1624000512,93717039363139,93717415595837),(1624051712,93717456889023,93717833122035),(1624102912,93717865389389,93718241622709)]
theorem point_links_checked12360 : (cuts12360.take 3).map (fun c => (1623982081-1+2*2^9*c.k,93716888918844+c.lower,93717265151429+c.upper)) = pointBounds12360 := by
 decide +kernel
def cuts12361 : List PrefixCut := [⟨40,337430068,337430325⟩,
⟨90,755089769,755090343⟩,
⟨128,1077597260,1077598072⟩]
theorem checked12361 : checkPrefixCuts (2^48) 1624113153 9 Manual.Count131072.C012361.packed 128 cuts12361 = true := by
 decide +kernel
def pointBounds12361 : List (Nat × Nat × Nat) := [(1624154112,93718288088192,93718664321833),(1624205312,93718705747893,93719081981851)]
theorem point_links_checked12361 : (cuts12361.take 2).map (fun c => (1624113153-1+2*2^9*c.k,93717950658124+c.lower,93718326891508+c.upper)) = pointBounds12361 := by
 decide +kernel
def cuts12362 : List PrefixCut := [⟨12,95312388,95312460⟩,
⟨62,510173022,510173406⟩,
⟨112,936284269,936284974⟩,
⟨128,1071098283,1071099085⟩]
theorem checked12362 : checkPrefixCuts (2^48) 1624244225 9 Manual.Count131072.C012362.packed 128 cuts12362 = true := by
 decide +kernel
def pointBounds12362 : List (Nat × Nat × Nat) := [(1624256512,93719123567772,93719499802040),(1624307712,93719538428406,93719914662986),(1624358912,93719964539653,93720340774554)]
theorem point_links_checked12362 : (cuts12362.take 3).map (fun c => (1624244225-1+2*2^9*c.k,93719028255384+c.lower,93719404489580+c.upper)) = pointBounds12362 := by
 decide +kernel
def cuts12363 : List PrefixCut := [⟨34,289550953,289551174⟩,
⟨84,712343226,712343760⟩,
⟨128,1080022825,1080023640⟩]
theorem checked12363 : checkPrefixCuts (2^48) 1624375297 9 Manual.Count131072.C012363.packed 128 cuts12363 = true := by
 decide +kernel
def pointBounds12363 : List (Nat × Nat × Nat) := [(1624410112,93720388904620,93720765139839),(1624461312,93720811696893,93721187932425)]
theorem point_links_checked12363 : (cuts12363.take 2).map (fun c => (1624375297-1+2*2^9*c.k,93720099353667+c.lower,93720475588665+c.upper)) = pointBounds12363 := by
 decide +kernel
def cuts12364 : List PrefixCut := [⟨6,49727807,49727845⟩,
⟨56,460538078,460538425⟩,
⟨106,874280858,874281513⟩,
⟨128,1059837115,1059837908⟩]
theorem checked12364 : checkPrefixCuts (2^48) 1624506369 9 Manual.Count131072.C012364.packed 128 cuts12364 = true := by
 decide +kernel
def pointBounds12364 : List (Nat × Nat × Nat) := [(1624512512,93721229104299,93721605340150),(1624563712,93721639914570,93722016150730),(1624614912,93722053657350,93722429893818)]
theorem point_links_checked12364 : (cuts12364.take 3).map (fun c => (1624506369-1+2*2^9*c.k,93721179376492+c.lower,93721555612305+c.upper)) = pointBounds12364 := by
 decide +kernel
def cuts12365 : List PrefixCut := [⟨28,231291991,231292164⟩,
⟨78,653324574,653325060⟩,
⟨128,1075690374,1075691175⟩]
theorem checked12365 : checkPrefixCuts (2^48) 1624637441 9 Manual.Count131072.C012365.packed 128 cuts12365 = true := by
 decide +kernel
def pointBounds12365 : List (Nat × Nat × Nat) := [(1624666112,93722470505598,93722846742377),(1624717312,93722892538181,93723268775273),(1624768512,93723314903981,93723691141388)]
theorem point_links_checked12365 : (cuts12365.take 3).map (fun c => (1624637441-1+2*2^9*c.k,93722239213607+c.lower,93722615450213+c.upper)) = pointBounds12365 := by
 decide +kernel
def cuts12366 : List PrefixCut := [⟨50,417848244,417848559⟩,
⟨100,837242409,837243037⟩,
⟨128,1075430301,1075431106⟩]
theorem checked12366 : checkPrefixCuts (2^48) 1624768513 9 Manual.Count131072.C012366.packed 128 cuts12366 = true := by
 decide +kernel
def pointBounds12366 : List (Nat × Nat × Nat) := [(1624819712,93723732752225,93724108989947),(1624870912,93724152146390,93724528384425)]
theorem point_links_checked12366 : (cuts12366.take 2).map (fun c => (1624768513-1+2*2^9*c.k,93723314903981+c.lower,93723691141388+c.upper)) = pointBounds12366 := by
 decide +kernel
def cuts12367 : List PrefixCut := [⟨22,178594748,178594883⟩,
⟨72,593978309,593978758⟩,
⟨122,1010041717,1010042485⟩,
⟨128,1063391129,1063391935⟩]
theorem checked12367 : checkPrefixCuts (2^48) 1624899585 9 Manual.Count131072.C012367.packed 128 cuts12367 = true := by
 decide +kernel
def pointBounds12367 : List (Nat × Nat × Nat) := [(1624922112,93724568929030,93724945167377),(1624973312,93724984312591,93725360551252),(1625024512,93725400375999,93725776614979)]
theorem point_links_checked12367 : (cuts12367.take 3).map (fun c => (1624899585-1+2*2^9*c.k,93724390334282+c.lower,93724766572494+c.upper)) = pointBounds12367 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000073
