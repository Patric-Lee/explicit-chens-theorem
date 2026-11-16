import PlattAssemblyKernel
import PlattCertificates.Count131072.C014960
import PlattCertificates.Count131072.C014961
import PlattCertificates.Count131072.C014962
import PlattCertificates.Count131072.C014963
import PlattCertificates.Count131072.C014964
import PlattCertificates.Count131072.C014965
import PlattCertificates.Count131072.C014966
import PlattCertificates.Count131072.C014967
import PlattCertificates.Count131072.C014968
import PlattCertificates.Count131072.C014969
import PlattCertificates.Count131072.C014970
import PlattCertificates.Count131072.C014971
import PlattCertificates.Count131072.C014972
import PlattCertificates.Count131072.C014973
import PlattCertificates.Count131072.C014974
import PlattCertificates.Count131072.C014975
import PlattCertificates.Count131072.C014976
import PlattCertificates.Count131072.C014977
import PlattCertificates.Count131072.C014978
import PlattCertificates.Count131072.C014979
import PlattCertificates.Count131072.C014980
import PlattCertificates.Count131072.C014981
import PlattCertificates.Count131072.C014982
import PlattCertificates.Count131072.C014983
import PlattCertificates.Count131072.C014984
import PlattCertificates.Count131072.C014985
import PlattCertificates.Count131072.C014986
import PlattCertificates.Count131072.C014987
import PlattCertificates.Count131072.C014988
import PlattCertificates.Count131072.C014989
import PlattCertificates.Count131072.C014990
import PlattCertificates.Count131072.C014991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000155
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14960 : List PrefixCut := [⟨38,259729701,259729878⟩,
⟨98,671447375,671447826⟩,
⟨128,875009307,875009893⟩]
theorem checked14960 : checkPrefixCuts (2^48) 1964769281 9 Manual.Count131072.C014960.packed 128 cuts14960 = true := by
 decide +kernel
def pointBounds14960 : List (Nat × Nat × Nat) := [(1964808192,96233963049879,96234341060651),(1964869632,96234374767553,96234752778599)]
theorem point_links_checked14960 : (cuts14960.take 2).map (fun c => (1964769281-1+2*2^9*c.k,96233703320178+c.lower,96234081330773+c.upper)) = pointBounds14960 := by
 decide +kernel
def cuts14961 : List PrefixCut := [⟨30,207856280,207856414⟩,
⟨90,622986125,622986535⟩,
⟨128,884691751,884692334⟩]
theorem checked14961 : checkPrefixCuts (2^48) 1964900353 9 Manual.Count131072.C014961.packed 128 cuts14961 = true := by
 decide +kernel
def pointBounds14961 : List (Nat × Nat × Nat) := [(1964931072,96234786185765,96235164197080),(1964992512,96235201315610,96235579327201)]
theorem point_links_checked14961 : (cuts14961.take 2).map (fun c => (1964900353-1+2*2^9*c.k,96234578329485+c.lower,96234956340666+c.upper)) = pointBounds14961 := by
 decide +kernel
def cuts14962 : List PrefixCut := [⟨22,154413911,154414017⟩,
⟨82,565793544,565793923⟩,
⟨128,878616788,878617373⟩]
theorem checked14962 : checkPrefixCuts (2^48) 1965031425 9 Manual.Count131072.C014962.packed 128 cuts14962 = true := by
 decide +kernel
def pointBounds14962 : List (Nat × Nat × Nat) := [(1965053952,96235617435147,96235995447017),(1965115392,96236028814780,96236406826923)]
theorem point_links_checked14962 : (cuts14962.take 2).map (fun c => (1965031425-1+2*2^9*c.k,96235463021236+c.lower,96235841033000+c.upper)) = pointBounds14962 := by
 decide +kernel
def cuts14963 : List PrefixCut := [⟨14,95105949,95106010⟩,
⟨74,502019766,502020103⟩,
⟨128,871826327,871826912⟩]
theorem checked14963 : checkPrefixCuts (2^48) 1965162497 9 Manual.Count131072.C014963.packed 128 cuts14963 = true := by
 decide +kernel
def pointBounds14963 : List (Nat × Nat × Nat) := [(1965176832,96236436743973,96236814756383),(1965238272,96236843657790,96237221670476)]
theorem point_links_checked14963 : (cuts14963.take 2).map (fun c => (1965162497-1+2*2^9*c.k,96236341638024+c.lower,96236719650373+c.upper)) = pointBounds14963 := by
 decide +kernel
def cuts14964 : List PrefixCut := [⟨6,40675220,40675248⟩,
⟨66,447133937,447134235⟩,
⟨126,858735701,858736272⟩,
⟨128,872054542,872055122⟩]
theorem checked14964 : checkPrefixCuts (2^48) 1965293569 9 Manual.Count131072.C014964.packed 128 cuts14964 = true := by
 decide +kernel
def pointBounds14964 : List (Nat × Nat × Nat) := [(1965299712,96237254139571,96237632152533),(1965361152,96237660598288,96238038611520),(1965422592,96238072200052,96238450213557)]
theorem point_links_checked14964 : (cuts14964.take 3).map (fun c => (1965293569-1+2*2^9*c.k,96237213464351+c.lower,96237591477285+c.upper)) = pointBounds14964 := by
 decide +kernel
def cuts14965 : List PrefixCut := [⟨58,400131811,400132078⟩,
⟨118,816576921,816577470⟩,
⟨128,888465374,888465969⟩]
theorem checked14965 : checkPrefixCuts (2^48) 1965424641 9 Manual.Count131072.C014965.packed 128 cuts14965 = true := by
 decide +kernel
def pointBounds14965 : List (Nat × Nat × Nat) := [(1965484032,96238485650704,96238863664485),(1965545472,96238902095814,96239280109877)]
theorem point_links_checked14965 : (cuts14965.take 2).map (fun c => (1965424641-1+2*2^9*c.k,96238085518893+c.lower,96238463532407+c.upper)) = pointBounds14965 := by
 decide +kernel
def cuts14966 : List PrefixCut := [⟨50,340104369,340104593⟩,
⟨110,748217955,748218453⟩,
⟨128,872654278,872654856⟩]
theorem checked14966 : checkPrefixCuts (2^48) 1965555713 9 Manual.Count131072.C014966.packed 128 cuts14966 = true := by
 decide +kernel
def pointBounds14966 : List (Nat × Nat × Nat) := [(1965606912,96239314088636,96239692102969),(1965668352,96239722202222,96240100216829)]
theorem point_links_checked14966 : (cuts14966.take 2).map (fun c => (1965555713-1+2*2^9*c.k,96238973984267+c.lower,96239351998376+c.upper)) = pointBounds14966 := by
 decide +kernel
def cuts14967 : List PrefixCut := [⟨42,292112916,292113106⟩,
⟨102,702492059,702492526⟩,
⟨128,876462561,876463145⟩]
theorem checked14967 : checkPrefixCuts (2^48) 1965686785 9 Manual.Count131072.C014967.packed 128 cuts14967 = true := by
 decide +kernel
def pointBounds14967 : List (Nat × Nat × Nat) := [(1965729792,96240138751461,96240516766338),(1965791232,96240549130604,96240927145758)]
theorem point_links_checked14967 : (cuts14967.take 2).map (fun c => (1965686785-1+2*2^9*c.k,96239846638545+c.lower,96240224653232+c.upper)) = pointBounds14967 := by
 decide +kernel
def cuts14968 : List PrefixCut := [⟨34,227947878,227948031⟩,
⟨94,639733084,639733513⟩,
⟨128,874971838,874972424⟩]
theorem checked14968 : checkPrefixCuts (2^48) 1965817857 9 Manual.Count131072.C014968.packed 128 cuts14968 = true := by
 decide +kernel
def pointBounds14968 : List (Nat × Nat × Nat) := [(1965852672,96240951048984,96241329064408),(1965914112,96241362834190,96241740849890)]
theorem point_links_checked14968 : (cuts14968.take 2).map (fun c => (1965817857-1+2*2^9*c.k,96240723101106+c.lower,96241101116377+c.upper)) = pointBounds14968 := by
 decide +kernel
def cuts14969 : List PrefixCut := [⟨26,180685730,180685849⟩,
⟨86,586432030,586432418⟩,
⟨128,879638261,879638842⟩]
theorem checked14969 : checkPrefixCuts (2^48) 1965948929 9 Manual.Count131072.C014969.packed 128 cuts14969 = true := by
 decide +kernel
def pointBounds14969 : List (Nat × Nat × Nat) := [(1965975552,96241778758674,96242156774650),(1966036992,96242184504974,96242562521219)]
theorem point_links_checked14969 : (cuts14969.take 2).map (fun c => (1965948929-1+2*2^9*c.k,96241598072944+c.lower,96241976088801+c.upper)) = pointBounds14969 := by
 decide +kernel
def cuts14970 : List PrefixCut := [⟨18,124982923,124983006⟩,
⟨78,544733762,544734132⟩,
⟨128,886308395,886308992⟩]
theorem checked14970 : checkPrefixCuts (2^48) 1966080001 9 Manual.Count131072.C014970.packed 128 cuts14970 = true := by
 decide +kernel
def pointBounds14970 : List (Nat × Nat × Nat) := [(1966098432,96242602694128,96242980710649),(1966159872,96243022444967,96243400461775)]
theorem point_links_checked14970 : (cuts14970.take 2).map (fun c => (1966080001-1+2*2^9*c.k,96242477711205+c.lower,96242855727643+c.upper)) = pointBounds14970 := by
 decide +kernel
def cuts14971 : List PrefixCut := [⟨11,73152498,73152546⟩,
⟨72,489870541,489870868⟩,
⟨128,871218304,871218885⟩]
theorem checked14971 : checkPrefixCuts (2^48) 1966211073 9 Manual.Count131072.C014971.packed 128 cuts14971 = true := by
 decide +kernel
def pointBounds14971 : List (Nat × Nat × Nat) := [(1966222336,96243437172098,96243815189181),(1966284800,96243853890141,96244231907503)]
theorem point_links_checked14971 : (cuts14971.take 2).map (fun c => (1966211073-1+2*2^9*c.k,96243364019600+c.lower,96243742036635+c.upper)) = pointBounds14971 := by
 decide +kernel
def cuts14972 : List PrefixCut := [⟨5,32064762,32064783⟩,
⟨66,449042575,449042873⟩,
⟨127,860281618,860282191⟩,
⟨128,867295328,867295906⟩]
theorem checked14972 : checkPrefixCuts (2^48) 1966342145 9 Manual.Count131072.C014972.packed 128 cuts14972 = true := by
 decide +kernel
def pointBounds14972 : List (Nat × Nat × Nat) := [(1966347264,96244267302666,96244645320303),(1966409728,96244684280479,96245062298393),(1966472192,96245095519522,96245473537711)]
theorem point_links_checked14972 : (cuts14972.take 3).map (fun c => (1966342145-1+2*2^9*c.k,96244235237904+c.lower,96244613255520+c.upper)) = pointBounds14972 := by
 decide +kernel
def cuts14973 : List PrefixCut := [⟨60,414804224,414804498⟩,
⟨121,832314838,832315389⟩,
⟨128,881550738,881551322⟩]
theorem checked14973 : checkPrefixCuts (2^48) 1966473217 9 Manual.Count131072.C014973.packed 128 cuts14973 = true := by
 decide +kernel
def pointBounds14973 : List (Nat × Nat × Nat) := [(1966534656,96245517337456,96245895355924),(1966597120,96245934848070,96246312866815)]
theorem point_links_checked14973 : (cuts14973.take 2).map (fun c => (1966473217-1+2*2^9*c.k,96245102533232+c.lower,96245480551426+c.upper)) = pointBounds14973 := by
 decide +kernel
def cuts14974 : List PrefixCut := [⟨54,374272733,374272983⟩,
⟨115,790611926,790612454⟩,
⟨128,880633336,880633924⟩]
theorem checked14974 : checkPrefixCuts (2^48) 1966604289 9 Manual.Count131072.C014974.packed 128 cuts14974 = true := by
 decide +kernel
def pointBounds14974 : List (Nat × Nat × Nat) := [(1966659584,96246358356703,96246736375731),(1966722048,96246774695896,96247152715202)]
theorem point_links_checked14974 : (cuts14974.take 2).map (fun c => (1966604289-1+2*2^9*c.k,96245984083970+c.lower,96246362102748+c.upper)) = pointBounds14974 := by
 decide +kernel
def cuts14975 : List PrefixCut := [⟨48,321581706,321581918⟩,
⟨109,732885562,732886045⟩,
⟨128,866406256,866406827⟩]
theorem checked14975 : checkPrefixCuts (2^48) 1966735361 9 Manual.Count131072.C014975.packed 128 cuts14975 = true := by
 decide +kernel
def pointBounds14975 : List (Nat × Nat × Nat) := [(1966784512,96247186299012,96247564318590),(1966846976,96247597602868,96247975622717)]
theorem point_links_checked14975 : (cuts14975.take 2).map (fun c => (1966735361-1+2*2^9*c.k,96246864717306+c.lower,96247242736672+c.upper)) = pointBounds14975 := by
 decide +kernel
def cuts14976 : List PrefixCut := [⟨42,284782395,284782585⟩,
⟨103,700782515,700782983⟩,
⟨128,871071132,871071717⟩]
theorem checked14976 : checkPrefixCuts (2^48) 1966866433 9 Manual.Count131072.C014976.packed 128 cuts14976 = true := by
 decide +kernel
def pointBounds14976 : List (Nat × Nat × Nat) := [(1966909440,96248015905957,96248393926084),(1966971904,96248431906077,96248809926482)]
theorem point_links_checked14976 : (cuts14976.take 2).map (fun c => (1966866433-1+2*2^9*c.k,96247731123562+c.lower,96248109143499+c.upper)) = pointBounds14976 := by
 decide +kernel
def cuts14977 : List PrefixCut := [⟨36,249132604,249132770⟩,
⟨97,664820075,664820515⟩,
⟨128,874733620,874734201⟩]
theorem checked14977 : checkPrefixCuts (2^48) 1966997505 9 Manual.Count131072.C014977.packed 128 cuts14977 = true := by
 decide +kernel
def pointBounds14977 : List (Nat × Nat × Nat) := [(1967034368,96248851327298,96249229347986),(1967096832,96249267014769,96249645035731)]
theorem point_links_checked14977 : (cuts14977.take 2).map (fun c => (1966997505-1+2*2^9*c.k,96248602194694+c.lower,96248980215216+c.upper)) = pointBounds14977 := by
 decide +kernel
def cuts14978 : List PrefixCut := [⟨30,197032302,197032431⟩,
⟨91,608973236,608973644⟩,
⟨128,863514424,863515004⟩]
theorem checked14978 : checkPrefixCuts (2^48) 1967128577 9 Manual.Count131072.C014978.packed 128 cuts14978 = true := by
 decide +kernel
def pointBounds14978 : List (Nat × Nat × Nat) := [(1967159296,96249673960616,96250051981848),(1967221760,96250085901550,96250463923061)]
theorem point_links_checked14978 : (cuts14978.take 2).map (fun c => (1967128577-1+2*2^9*c.k,96249476928314+c.lower,96249854949417+c.upper)) = pointBounds14978 := by
 decide +kernel
def cuts14979 : List PrefixCut := [⟨24,167116036,167116151⟩,
⟨85,588903034,588903427⟩,
⟨128,881198645,881199240⟩]
theorem checked14979 : checkPrefixCuts (2^48) 1967259649 9 Manual.Count131072.C014979.packed 128 cuts14979 = true := by
 decide +kernel
def pointBounds14979 : List (Nat × Nat × Nat) := [(1967284224,96250507558774,96250885580572),(1967346688,96250929345772,96251307367848)]
theorem point_links_checked14979 : (cuts14979.take 2).map (fun c => (1967259649-1+2*2^9*c.k,96250340442738+c.lower,96250718464421+c.upper)) = pointBounds14979 := by
 decide +kernel
def cuts14980 : List PrefixCut := [⟨18,120893709,120893790⟩,
⟨79,535357423,535357779⟩,
⟨128,865259391,865259973⟩]
theorem checked14980 : checkPrefixCuts (2^48) 1967390721 9 Manual.Count131072.C014980.packed 128 cuts14980 = true := by
 decide +kernel
def pointBounds14980 : List (Nat × Nat × Nat) := [(1967409152,96251342535092,96251720557451),(1967471616,96251756998806,96252135021440)]
theorem point_links_checked14980 : (cuts14980.take 2).map (fun c => (1967390721-1+2*2^9*c.k,96251221641383+c.lower,96251599663661+c.upper)) = pointBounds14980 := by
 decide +kernel
def cuts14981 : List PrefixCut := [⟨12,84405508,84405564⟩,
⟨73,503277692,503278027⟩,
⟨128,878219992,878220577⟩]
theorem checked14981 : checkPrefixCuts (2^48) 1967521793 9 Manual.Count131072.C014981.packed 128 cuts14981 = true := by
 decide +kernel
def pointBounds14981 : List (Nat × Nat × Nat) := [(1967534080,96252171306282,96252549329198),(1967596544,96252590178466,96252968201661)]
theorem point_links_checked14981 : (cuts14981.take 2).map (fun c => (1967521793-1+2*2^9*c.k,96252086900774+c.lower,96252464923634+c.upper)) = pointBounds14981 := by
 decide +kernel
def cuts14982 : List PrefixCut := [⟨6,41913903,41913929⟩,
⟨67,455895846,455896151⟩,
⟨128,873583782,873584367⟩]
theorem checked14982 : checkPrefixCuts (2^48) 1967652865 9 Manual.Count131072.C014982.packed 128 cuts14982 = true := by
 decide +kernel
def pointBounds14982 : List (Nat × Nat × Nat) := [(1967659008,96253007034669,96253385058140),(1967721472,96253421016612,96253799040362),(1967783936,96253838704548,96254216728578)]
theorem point_links_checked14982 : (cuts14982.take 3).map (fun c => (1967652865-1+2*2^9*c.k,96252965120766+c.lower,96253343144211+c.upper)) = pointBounds14982 := by
 decide +kernel
def cuts14983 : List PrefixCut := [⟨61,421250673,421250952⟩,
⟨122,843203189,843203746⟩,
⟨128,884539509,884540093⟩]
theorem checked14983 : checkPrefixCuts (2^48) 1967783937 9 Manual.Count131072.C014983.packed 128 cuts14983 = true := by
 decide +kernel
def pointBounds14983 : List (Nat × Nat × Nat) := [(1967846400,96254259955221,96254637979530),(1967908864,96254681907737,96255059932324)]
theorem point_links_checked14983 : (cuts14983.take 2).map (fun c => (1967783937-1+2*2^9*c.k,96253838704548+c.lower,96254216728578+c.upper)) = pointBounds14983 := by
 decide +kernel
def cuts14984 : List PrefixCut := [⟨55,376168827,376169080⟩,
⟨116,798952683,798953213⟩,
⟨128,877901352,877901935⟩]
theorem checked14984 : checkPrefixCuts (2^48) 1967915009 9 Manual.Count131072.C014984.packed 128 cuts14984 = true := by
 decide +kernel
def pointBounds14984 : List (Nat × Nat × Nat) := [(1967971328,96255099412884,96255477437751),(1968033792,96255522196740,96255900221884)]
theorem point_links_checked14984 : (cuts14984.take 2).map (fun c => (1967915009-1+2*2^9*c.k,96254723244057+c.lower,96255101268671+c.upper)) = pointBounds14984 := by
 decide +kernel
def cuts14985 : List PrefixCut := [⟨49,337528763,337528990⟩,
⟨110,751275878,751276383⟩,
⟨128,874410636,874411223⟩]
theorem checked14985 : checkPrefixCuts (2^48) 1968046081 9 Manual.Count131072.C014985.packed 128 cuts14985 = true := by
 decide +kernel
def pointBounds14985 : List (Nat × Nat × Nat) := [(1968096256,96255938674172,96256316699596),(1968158720,96256352421287,96256730446989)]
theorem point_links_checked14985 : (cuts14985.take 2).map (fun c => (1968046081-1+2*2^9*c.k,96255601145409+c.lower,96255979170606+c.upper)) = pointBounds14985 := by
 decide +kernel
def cuts14986 : List PrefixCut := [⟨43,292029231,292029429⟩,
⟨104,712328235,712328714⟩,
⟨128,879643309,879643898⟩]
theorem checked14986 : checkPrefixCuts (2^48) 1968177153 9 Manual.Count131072.C014986.packed 128 cuts14986 = true := by
 decide +kernel
def pointBounds14986 : List (Nat × Nat × Nat) := [(1968221184,96256767585276,96257145611258),(1968283648,96257187884280,96257565910543)]
theorem point_links_checked14986 : (cuts14986.take 2).map (fun c => (1968177153-1+2*2^9*c.k,96256475556045+c.lower,96256853581829+c.upper)) = pointBounds14986 := by
 decide +kernel
def cuts14987 : List PrefixCut := [⟨37,256688747,256688918⟩,
⟨98,676532257,676532709⟩,
⟨128,876010382,876010969⟩]
theorem checked14987 : checkPrefixCuts (2^48) 1968308225 9 Manual.Count131072.C014987.packed 128 cuts14987 = true := by
 decide +kernel
def pointBounds14987 : List (Nat × Nat × Nat) := [(1968346112,96257611888101,96257989914645),(1968408576,96258031731611,96258409758436)]
theorem point_links_checked14987 : (cuts14987.take 2).map (fun c => (1968308225-1+2*2^9*c.k,96257355199354+c.lower,96257733225727+c.upper)) = pointBounds14987 := by
 decide +kernel
def cuts14988 : List PrefixCut := [⟨31,217635003,217635151⟩,
⟨92,635306919,635307345⟩,
⟨128,887676778,887677366⟩]
theorem checked14988 : checkPrefixCuts (2^48) 1968439297 9 Manual.Count131072.C014988.packed 128 cuts14988 = true := by
 decide +kernel
def pointBounds14988 : List (Nat × Nat × Nat) := [(1968471040,96258448844739,96258826871847),(1968533504,96258866516655,96259244544041)]
theorem point_links_checked14988 : (cuts14988.take 2).map (fun c => (1968439297-1+2*2^9*c.k,96258231209736+c.lower,96258609236696+c.upper)) = pointBounds14988 := by
 decide +kernel
def cuts14989 : List PrefixCut := [⟨25,172438091,172438206⟩,
⟨86,588510742,588511135⟩,
⟨128,873748788,873749367⟩]
theorem checked14989 : checkPrefixCuts (2^48) 1968570369 9 Manual.Count131072.C014989.packed 128 cuts14989 = true := by
 decide +kernel
def pointBounds14989 : List (Nat × Nat × Nat) := [(1968595968,96259291324605,96259669352268),(1968658432,96259707397256,96260085425197)]
theorem point_links_checked14989 : (cuts14989.take 2).map (fun c => (1968570369-1+2*2^9*c.k,96259118886514+c.lower,96259496914062+c.upper)) = pointBounds14989 := by
 decide +kernel
def cuts14990 : List PrefixCut := [⟨19,131679230,131679318⟩,
⟨80,553301411,553301780⟩,
⟨128,880696174,880696758⟩]
theorem checked14990 : checkPrefixCuts (2^48) 1968701441 9 Manual.Count131072.C014990.packed 128 cuts14990 = true := by
 decide +kernel
def pointBounds14990 : List (Nat × Nat × Nat) := [(1968720896,96260124314532,96260502342747),(1968783360,96260545936713,96260923965209)]
theorem point_links_checked14990 : (cuts14990.take 2).map (fun c => (1968701441-1+2*2^9*c.k,96259992635302+c.lower,96260370663429+c.upper)) = pointBounds14990 := by
 decide +kernel
def cuts14991 : List PrefixCut := [⟨13,86922657,86922717⟩,
⟨74,502799493,502799829⟩,
⟨128,871773745,871774331⟩]
theorem checked14991 : checkPrefixCuts (2^48) 1968832513 9 Manual.Count131072.C014991.packed 128 cuts14991 = true := by
 decide +kernel
def pointBounds14991 : List (Nat × Nat × Nat) := [(1968845824,96260960254133,96261338282904),(1968908288,96261376130969,96261754160016)]
theorem point_links_checked14991 : (cuts14991.take 2).map (fun c => (1968832513-1+2*2^9*c.k,96260873331476+c.lower,96261251360187+c.upper)) = pointBounds14991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000155
