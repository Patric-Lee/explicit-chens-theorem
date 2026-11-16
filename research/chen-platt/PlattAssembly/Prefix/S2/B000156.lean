import PlattAssemblyKernel
import PlattCertificates.Count131072.C014992
import PlattCertificates.Count131072.C014993
import PlattCertificates.Count131072.C014994
import PlattCertificates.Count131072.C014995
import PlattCertificates.Count131072.C014996
import PlattCertificates.Count131072.C014997
import PlattCertificates.Count131072.C014998
import PlattCertificates.Count131072.C014999
import PlattCertificates.Count131072.C015000
import PlattCertificates.Count131072.C015001
import PlattCertificates.Count131072.C015002
import PlattCertificates.Count131072.C015003
import PlattCertificates.Count131072.C015004
import PlattCertificates.Count131072.C015005
import PlattCertificates.Count131072.C015006
import PlattCertificates.Count131072.C015007
import PlattCertificates.Count131072.C015008
import PlattCertificates.Count131072.C015009
import PlattCertificates.Count131072.C015010
import PlattCertificates.Count131072.C015011
import PlattCertificates.Count131072.C015012
import PlattCertificates.Count131072.C015013
import PlattCertificates.Count131072.C015014
import PlattCertificates.Count131072.C015015
import PlattCertificates.Count131072.C015016
import PlattCertificates.Count131072.C015017
import PlattCertificates.Count131072.C015018
import PlattCertificates.Count131072.C015019
import PlattCertificates.Count131072.C015020
import PlattCertificates.Count131072.C015021
import PlattCertificates.Count131072.C015022
import PlattCertificates.Count131072.C015023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14992 : List PrefixCut := [⟨7,48747856,48747888⟩,
⟨68,466456709,466457022⟩,
⟨128,878005753,878006340⟩]
theorem checked14992 : checkPrefixCuts (2^48) 1968963585 9 Manual.Count131072.C014992.packed 128 cuts14992 = true := by
 decide +kernel
def pointBounds14992 : List (Nat × Nat × Nat) := [(1968970752,96261793853077,96262171882406),(1969033216,96262211561930,96262589591540)]
theorem point_links_checked14992 : (cuts14992.take 2).map (fun c => (1968963585-1+2*2^9*c.k,96261745105221+c.lower,96262123134518+c.upper)) = pointBounds14992 := by
 decide +kernel
def cuts14993 : List PrefixCut := [⟨1,8433832,8433838⟩,
⟨62,427402734,427403023⟩,
⟨123,835066124,835066683⟩,
⟨128,865654643,865655222⟩]
theorem checked14993 : checkPrefixCuts (2^48) 1969094657 9 Manual.Count131072.C014993.packed 128 cuts14993 = true := by
 decide +kernel
def pointBounds14993 : List (Nat × Nat × Nat) := [(1969095680,96262631544806,96263009574696),(1969158144,96263050513708,96263428543881),(1969220608,96263458177098,96263836207541)]
theorem point_links_checked14993 : (cuts14993.take 3).map (fun c => (1969094657-1+2*2^9*c.k,96262623110974+c.lower,96263001140858+c.upper)) = pointBounds14993 := by
 decide +kernel
def cuts14994 : List PrefixCut := [⟨56,380492317,380492566⟩,
⟨117,800421857,800422385⟩,
⟨128,877888689,877889267⟩]
theorem checked14994 : checkPrefixCuts (2^48) 1969225729 9 Manual.Count131072.C014994.packed 128 cuts14994 = true := by
 decide +kernel
def pointBounds14994 : List (Nat × Nat × Nat) := [(1969283072,96263869257934,96264247288646),(1969345536,96264289187474,96264667218465)]
theorem point_links_checked14994 : (cuts14994.take 2).map (fun c => (1969225729-1+2*2^9*c.k,96263488765617+c.lower,96263866796080+c.upper)) = pointBounds14994 := by
 decide +kernel
def cuts14995 : List PrefixCut := [⟨50,345307907,345308138⟩,
⟨111,763781604,763782108⟩,
⟨128,873542966,873543544⟩]
theorem checked14995 : checkPrefixCuts (2^48) 1969356801 9 Manual.Count131072.C014995.packed 128 cuts14995 = true := by
 decide +kernel
def pointBounds14995 : List (Nat × Nat × Nat) := [(1969408000,96264711962213,96265089993485),(1969470464,96265130435910,96265508467455)]
theorem point_links_checked14995 : (cuts14995.take 2).map (fun c => (1969356801-1+2*2^9*c.k,96264366654306+c.lower,96264744685347+c.upper)) = pointBounds14995 := by
 decide +kernel
def cuts14996 : List PrefixCut := [⟨44,305411905,305412109⟩,
⟨105,720857897,720858375⟩,
⟨128,883059796,883060382⟩]
theorem checked14996 : checkPrefixCuts (2^48) 1969487873 9 Manual.Count131072.C014996.packed 128 cuts14996 = true := by
 decide +kernel
def pointBounds14996 : List (Nat × Nat × Nat) := [(1969532928,96265545609177,96265923641000),(1969595392,96265961055169,96266339087266)]
theorem point_links_checked14996 : (cuts14996.take 2).map (fun c => (1969487873-1+2*2^9*c.k,96265240197272+c.lower,96265618228891+c.upper)) = pointBounds14996 := by
 decide +kernel
def cuts14997 : List PrefixCut := [⟨38,261948364,261948541⟩,
⟨99,676939252,676939704⟩,
⟨128,875712946,875713529⟩]
theorem checked14997 : checkPrefixCuts (2^48) 1969618945 9 Manual.Count131072.C014997.packed 128 cuts14997 = true := by
 decide +kernel
def pointBounds14997 : List (Nat × Nat × Nat) := [(1969657856,96266385205432,96266763237814),(1969720320,96266800196320,96267178228977)]
theorem point_links_checked14997 : (cuts14997.take 2).map (fun c => (1969618945-1+2*2^9*c.k,96266123257068+c.lower,96266501289273+c.upper)) = pointBounds14997 := by
 decide +kernel
def cuts14998 : List PrefixCut := [⟨32,218490427,218490573⟩,
⟨93,636455710,636456132⟩,
⟨128,882084661,882085245⟩]
theorem checked14998 : checkPrefixCuts (2^48) 1969750017 9 Manual.Count131072.C014998.packed 128 cuts14998 = true := by
 decide +kernel
def pointBounds14998 : List (Nat × Nat × Nat) := [(1969782784,96267217460441,96267595493375),(1969845248,96267635425724,96268013458934)]
theorem point_links_checked14998 : (cuts14998.take 2).map (fun c => (1969750017-1+2*2^9*c.k,96266998970014+c.lower,96267377002802+c.upper)) = pointBounds14998 := by
 decide +kernel
def cuts14999 : List PrefixCut := [⟨26,176467053,176467170⟩,
⟨87,598978232,598978633⟩,
⟨128,875024874,875025460⟩]
theorem checked14999 : checkPrefixCuts (2^48) 1969881089 9 Manual.Count131072.C014999.packed 128 cuts14999 = true := by
 decide +kernel
def pointBounds14999 : List (Nat × Nat × Nat) := [(1969907712,96268057521728,96268435555217),(1969970176,96268480032907,96268858066680)]
theorem point_links_checked14999 : (cuts14999.take 2).map (fun c => (1969881089-1+2*2^9*c.k,96267881054675+c.lower,96268259088047+c.upper)) = pointBounds14999 := by
 decide +kernel
def cuts15000 : List PrefixCut := [⟨20,136592346,136592438⟩,
⟨81,548932477,548932849⟩,
⟨128,871966078,871966667⟩]
theorem checked15000 : checkPrefixCuts (2^48) 1970012161 9 Manual.Count131072.C015000.packed 128 cuts15000 = true := by
 decide +kernel
def pointBounds15000 : List (Nat × Nat × Nat) := [(1970032640,96268892671895,96269270705945),(1970095104,96269305012026,96269683046356)]
theorem point_links_checked15000 : (cuts15000.take 2).map (fun c => (1970012161-1+2*2^9*c.k,96268756079549+c.lower,96269134113507+c.upper)) = pointBounds15000 := by
 decide +kernel
def cuts15001 : List PrefixCut := [⟨14,94579771,94579836⟩,
⟨75,502893552,502893889⟩,
⟨128,861050471,861051046⟩]
theorem checked15001 : checkPrefixCuts (2^48) 1970143233 9 Manual.Count131072.C015001.packed 128 cuts15001 = true := by
 decide +kernel
def pointBounds15001 : List (Nat × Nat × Nat) := [(1970157568,96269722625398,96270100660010),(1970220032,96270130939179,96270508974063)]
theorem point_links_checked15001 : (cuts15001.take 2).map (fun c => (1970143233-1+2*2^9*c.k,96269628045627+c.lower,96270006080174+c.upper)) = pointBounds15001 := by
 decide +kernel
def cuts15002 : List PrefixCut := [⟨8,54715556,54715594⟩,
⟨69,472003392,472003707⟩,
⟨128,873278699,873279282⟩]
theorem checked15002 : checkPrefixCuts (2^48) 1970274305 9 Manual.Count131072.C015002.packed 128 cuts15002 = true := by
 decide +kernel
def pointBounds15002 : List (Nat × Nat × Nat) := [(1970282496,96270543811654,96270921846814),(1970344960,96270961099490,96271339134927)]
theorem point_links_checked15002 : (cuts15002.take 2).map (fun c => (1970274305-1+2*2^9*c.k,96270489096098+c.lower,96270867131220+c.upper)) = pointBounds15002 := by
 decide +kernel
def cuts15003 : List PrefixCut := [⟨2,12999458,12999466⟩,
⟨63,421975670,421975959⟩,
⟨124,840366623,840367193⟩,
⟨128,867649426,867650015⟩]
theorem checked15003 : checkPrefixCuts (2^48) 1970405377 9 Manual.Count131072.C015003.packed 128 cuts15003 = true := by
 decide +kernel
def pointBounds15003 : List (Nat × Nat × Nat) := [(1970407424,96271375374255,96271753409968),(1970469888,96271784350467,96272162386461),(1970532352,96272202741420,96272580777695)]
theorem point_links_checked15003 : (cuts15003.take 3).map (fun c => (1970405377-1+2*2^9*c.k,96271362374797+c.lower,96271740410502+c.upper)) = pointBounds15003 := by
 decide +kernel
def cuts15004 : List PrefixCut := [⟨57,387238324,387238579⟩,
⟨118,795318712,795319238⟩,
⟨128,867020690,867021264⟩]
theorem checked15004 : checkPrefixCuts (2^48) 1970536449 9 Manual.Count131072.C015004.packed 128 cuts15004 = true := by
 decide +kernel
def pointBounds15004 : List (Nat × Nat × Nat) := [(1970594816,96272617262547,96272995299096),(1970657280,96273025342935,96273403379755)]
theorem point_links_checked15004 : (cuts15004.take 2).map (fun c => (1970536449-1+2*2^9*c.k,96272230024223+c.lower,96272608060517+c.upper)) = pointBounds15004 := by
 decide +kernel
def cuts15005 : List PrefixCut := [⟨51,345792275,345792503⟩,
⟨112,759131187,759131695⟩,
⟨128,873389867,873390447⟩]
theorem checked15005 : checkPrefixCuts (2^48) 1970667521 9 Manual.Count131072.C015005.packed 128 cuts15005 = true := by
 decide +kernel
def pointBounds15005 : List (Nat × Nat × Nat) := [(1970719744,96273442837188,96273820874284),(1970782208,96273856176100,96274234213476)]
theorem point_links_checked15005 : (cuts15005.take 2).map (fun c => (1970667521-1+2*2^9*c.k,96273097044913+c.lower,96273475081781+c.upper)) = pointBounds15005 := by
 decide +kernel
def cuts15006 : List PrefixCut := [⟨45,314634878,314635088⟩,
⟨106,723663186,723663670⟩,
⟨128,879044892,879045478⟩]
theorem checked15006 : checkPrefixCuts (2^48) 1970798593 9 Manual.Count131072.C015006.packed 128 cuts15006 = true := by
 decide +kernel
def pointBounds15006 : List (Nat × Nat × Nat) := [(1970844672,96274285069658,96274663107316),(1970907136,96274694097966,96275072135898)]
theorem point_links_checked15006 : (cuts15006.take 2).map (fun c => (1970798593-1+2*2^9*c.k,96273970434780+c.lower,96274348472228+c.upper)) = pointBounds15006 := by
 decide +kernel
def cuts15007 : List PrefixCut := [⟨39,269057487,269057664⟩,
⟨100,694482829,694483286⟩,
⟨128,886269670,886270251⟩]
theorem checked15007 : checkPrefixCuts (2^48) 1970929665 9 Manual.Count131072.C015007.packed 128 cuts15007 = true := by
 decide +kernel
def pointBounds15007 : List (Nat × Nat × Nat) := [(1970969600,96275118537159,96275496575370),(1971032064,96275543962501,96275922000992)]
theorem point_links_checked15007 : (cuts15007.take 2).map (fun c => (1970929665-1+2*2^9*c.k,96274849479672+c.lower,96275227517706+c.upper)) = pointBounds15007 := by
 decide +kernel
def cuts15008 : List PrefixCut := [⟨33,229198050,229198206⟩,
⟨94,638888497,638888924⟩,
⟨128,876357442,876358032⟩]
theorem checked15008 : checkPrefixCuts (2^48) 1971060737 9 Manual.Count131072.C015008.packed 128 cuts15008 = true := by
 decide +kernel
def pointBounds15008 : List (Nat × Nat × Nat) := [(1971094528,96275964947392,96276342986163),(1971156992,96276374637839,96276752676881)]
theorem point_links_checked15008 : (cuts15008.take 2).map (fun c => (1971060737-1+2*2^9*c.k,96275735749342+c.lower,96276113787957+c.upper)) = pointBounds15008 := by
 decide +kernel
def cuts15009 : List PrefixCut := [⟨27,182775384,182775507⟩,
⟨88,599436579,599436976⟩,
⟨128,877155815,877156392⟩]
theorem checked15009 : checkPrefixCuts (2^48) 1971191809 9 Manual.Count131072.C015009.packed 128 cuts15009 = true := by
 decide +kernel
def pointBounds15009 : List (Nat × Nat × Nat) := [(1971219456,96276794882168,96277172921496),(1971281920,96277211543363,96277589582965)]
theorem point_links_checked15009 : (cuts15009.take 2).map (fun c => (1971191809-1+2*2^9*c.k,96276612106784+c.lower,96276990145989+c.upper)) = pointBounds15009 := by
 decide +kernel
def cuts15010 : List PrefixCut := [⟨21,146353593,146353688⟩,
⟨82,569127965,569128345⟩,
⟨128,884950644,884951233⟩]
theorem checked15010 : checkPrefixCuts (2^48) 1971322881 9 Manual.Count131072.C015010.packed 128 cuts15010 = true := by
 decide +kernel
def pointBounds15010 : List (Nat × Nat × Nat) := [(1971344384,96277635616192,96278013656069),(1971406848,96278058390564,96278436430726)]
theorem point_links_checked15010 : (cuts15010.take 2).map (fun c => (1971322881-1+2*2^9*c.k,96277489262599+c.lower,96277867302381+c.upper)) = pointBounds15010 := by
 decide +kernel
def cuts15011 : List PrefixCut := [⟨15,106795494,106795562⟩,
⟨76,521690584,521690927⟩,
⟨128,881465161,881465743⟩]
theorem checked15011 : checkPrefixCuts (2^48) 1971453953 9 Manual.Count131072.C015011.packed 128 cuts15011 = true := by
 decide +kernel
def pointBounds15011 : List (Nat × Nat × Nat) := [(1971469312,96278481008737,96278859049176),(1971531776,96278895903827,96279273944541)]
theorem point_links_checked15011 : (cuts15011.take 2).map (fun c => (1971453953-1+2*2^9*c.k,96278374213243+c.lower,96278752253614+c.upper)) = pointBounds15011 := by
 decide +kernel
def cuts15012 : List PrefixCut := [⟨9,66243172,66243217⟩,
⟨70,485537714,485538039⟩,
⟨128,882977200,882977792⟩]
theorem checked15012 : checkPrefixCuts (2^48) 1971585025 9 Manual.Count131072.C015012.packed 128 cuts15012 = true := by
 decide +kernel
def pointBounds15012 : List (Nat × Nat × Nat) := [(1971594240,96279321921576,96279699962574),(1971656704,96279741216118,96280119257396)]
theorem point_links_checked15012 : (cuts15012.take 2).map (fun c => (1971585025-1+2*2^9*c.k,96279255678404+c.lower,96279633719357+c.upper)) = pointBounds15012 := by
 decide +kernel
def cuts15013 : List PrefixCut := [⟨3,20985160,20985174⟩,
⟨64,431973314,431973601⟩,
⟨125,844090594,844091152⟩,
⟨128,867072849,867073421⟩]
theorem checked15013 : checkPrefixCuts (2^48) 1971716097 9 Manual.Count131072.C015013.packed 128 cuts15013 = true := by
 decide +kernel
def pointBounds15013 : List (Nat × Nat × Nat) := [(1971719168,96280159640764,96280537682323),(1971781632,96280570628918,96280948670750),(1971844096,96280982746198,96281360788301)]
theorem point_links_checked15013 : (cuts15013.take 3).map (fun c => (1971716097-1+2*2^9*c.k,96280138655604+c.lower,96280516697149+c.upper)) = pointBounds15013 := by
 decide +kernel
def cuts15014 : List PrefixCut := [⟨58,392262359,392262622⟩,
⟨119,810348522,810349070⟩,
⟨128,874152256,874152847⟩]
theorem checked15014 : checkPrefixCuts (2^48) 1971847169 9 Manual.Count131072.C015014.packed 128 cuts15014 = true := by
 decide +kernel
def pointBounds15014 : List (Nat × Nat × Nat) := [(1971906560,96281397990812,96281776033192),(1971969024,96281816076975,96282194119640)]
theorem point_links_checked15014 : (cuts15014.take 2).map (fun c => (1971847169-1+2*2^9*c.k,96281005728453+c.lower,96281383770570+c.upper)) = pointBounds15014 := by
 decide +kernel
def cuts15015 : List PrefixCut := [⟨52,355839281,355839517⟩,
⟨113,773328059,773328575⟩,
⟨128,875378847,875379431⟩]
theorem checked15015 : checkPrefixCuts (2^48) 1971978241 9 Manual.Count131072.C015015.packed 128 cuts15015 = true := by
 decide +kernel
def pointBounds15015 : List (Nat × Nat × Nat) := [(1972031488,96282235719990,96282613762934),(1972093952,96282653208768,96283031251992)]
theorem point_links_checked15015 : (cuts15015.take 2).map (fun c => (1971978241-1+2*2^9*c.k,96281879880709+c.lower,96282257923417+c.upper)) = pointBounds15015 := by
 decide +kernel
def cuts15016 : List PrefixCut := [⟨46,320562842,320563055⟩,
⟨107,735598980,735599470⟩,
⟨128,881457937,881458524⟩]
theorem checked15016 : checkPrefixCuts (2^48) 1972109313 9 Manual.Count131072.C015016.packed 128 cuts15016 = true := by
 decide +kernel
def pointBounds15016 : List (Nat × Nat × Nat) := [(1972156416,96283075822398,96283453865903),(1972218880,96283490858536,96283868902318)]
theorem point_links_checked15016 : (cuts15016.take 2).map (fun c => (1972109313-1+2*2^9*c.k,96282755259556+c.lower,96283133302848+c.upper)) = pointBounds15016 := by
 decide +kernel
def cuts15017 : List PrefixCut := [⟨40,273873676,273873858⟩,
⟨101,684744787,684745244⟩,
⟨128,869696771,869697351⟩]
theorem checked15017 : checkPrefixCuts (2^48) 1972240385 9 Manual.Count131072.C015017.packed 128 cuts15017 = true := by
 decide +kernel
def pointBounds15017 : List (Nat × Nat × Nat) := [(1972281344,96283910591169,96284288635230),(1972343808,96284321462280,96284699506616)]
theorem point_links_checked15017 : (cuts15017.take 2).map (fun c => (1972240385-1+2*2^9*c.k,96283636717493+c.lower,96284014761372+c.upper)) = pointBounds15017 := by
 decide +kernel
def cuts15018 : List PrefixCut := [⟨34,233041513,233041671⟩,
⟨95,648024986,648025424⟩,
⟨128,876916712,876917300⟩]
theorem checked15018 : checkPrefixCuts (2^48) 1972371457 9 Manual.Count131072.C015018.packed 128 cuts15018 = true := by
 decide +kernel
def pointBounds15018 : List (Nat × Nat × Nat) := [(1972406272,96284739455777,96285117500394),(1972468736,96285154439250,96285532484147)]
theorem point_links_checked15018 : (cuts15018.take 2).map (fun c => (1972371457-1+2*2^9*c.k,96284506414264+c.lower,96284884458723+c.upper)) = pointBounds15018 := by
 decide +kernel
def cuts15019 : List PrefixCut := [⟨28,192214691,192214817⟩,
⟨89,617588619,617589022⟩,
⟨128,886419155,886419740⟩]
theorem checked15019 : checkPrefixCuts (2^48) 1972502529 9 Manual.Count131072.C015019.packed 128 cuts15019 = true := by
 decide +kernel
def pointBounds15019 : List (Nat × Nat × Nat) := [(1972531200,96285575545667,96285953590840),(1972593664,96286000919595,96286378965045)]
theorem point_links_checked15019 : (cuts15019.take 2).map (fun c => (1972502529-1+2*2^9*c.k,96285383330976+c.lower,96285761376023+c.upper)) = pointBounds15019 := by
 decide +kernel
def cuts15020 : List PrefixCut := [⟨22,148682013,148682110⟩,
⟨83,564326332,564326704⟩,
⟨128,877941538,877942118⟩]
theorem checked15020 : checkPrefixCuts (2^48) 1972633601 9 Manual.Count131072.C015020.packed 128 cuts15020 = true := by
 decide +kernel
def pointBounds15020 : List (Nat × Nat × Nat) := [(1972656128,96286418432144,96286796477873),(1972718592,96286834076463,96287212122467)]
theorem point_links_checked15020 : (cuts15020.take 2).map (fun c => (1972633601-1+2*2^9*c.k,96286269750131+c.lower,96286647795763+c.upper)) = pointBounds15020 := by
 decide +kernel
def cuts15021 : List PrefixCut := [⟨16,110291495,110291568⟩,
⟨77,524910699,524911050⟩,
⟨128,870464317,870464894⟩]
theorem checked15021 : checkPrefixCuts (2^48) 1972764673 9 Manual.Count131072.C015021.packed 128 cuts15021 = true := by
 decide +kernel
def pointBounds15021 : List (Nat × Nat × Nat) := [(1972781056,96287257983164,96287636029449),(1972843520,96287672602368,96288050648931)]
theorem point_links_checked15021 : (cuts15021.take 2).map (fun c => (1972764673-1+2*2^9*c.k,96287147691669+c.lower,96287525737881+c.upper)) = pointBounds15021 := by
 decide +kernel
def cuts15022 : List PrefixCut := [⟨10,68339196,68339243⟩,
⟨71,482646886,482647210⟩,
⟨128,869978442,869979026⟩]
theorem checked15022 : checkPrefixCuts (2^48) 1972895745 9 Manual.Count131072.C015022.packed 128 cuts15022 = true := by
 decide +kernel
def pointBounds15022 : List (Nat × Nat × Nat) := [(1972905984,96288086495182,96288464542018),(1972968448,96288500802872,96288878849985)]
theorem point_links_checked15022 : (cuts15022.take 2).map (fun c => (1972895745-1+2*2^9*c.k,96288018155986+c.lower,96288396202775+c.upper)) = pointBounds15022 := by
 decide +kernel
def cuts15023 : List PrefixCut := [⟨4,25964358,25964375⟩,
⟨65,444810919,444811213⟩,
⟨126,860933742,860934313⟩,
⟨128,872631210,872631789⟩]
theorem checked15023 : checkPrefixCuts (2^48) 1973026817 9 Manual.Count131072.C015023.packed 128 cuts15023 = true := by
 decide +kernel
def pointBounds15023 : List (Nat × Nat × Nat) := [(1973030912,96288914098786,96289292146176),(1973093376,96289332945347,96289710993014),(1973155840,96289749068170,96290127116114)]
theorem point_links_checked15023 : (cuts15023.take 3).map (fun c => (1973026817-1+2*2^9*c.k,96288888134428+c.lower,96289266181801+c.upper)) = pointBounds15023 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000156
