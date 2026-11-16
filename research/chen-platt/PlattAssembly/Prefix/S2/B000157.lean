import PlattAssemblyKernel
import PlattCertificates.Count131072.C015024
import PlattCertificates.Count131072.C015025
import PlattCertificates.Count131072.C015026
import PlattCertificates.Count131072.C015027
import PlattCertificates.Count131072.C015028
import PlattCertificates.Count131072.C015029
import PlattCertificates.Count131072.C015030
import PlattCertificates.Count131072.C015031
import PlattCertificates.Count131072.C015032
import PlattCertificates.Count131072.C015033
import PlattCertificates.Count131072.C015034
import PlattCertificates.Count131072.C015035
import PlattCertificates.Count131072.C015036
import PlattCertificates.Count131072.C015037
import PlattCertificates.Count131072.C015038
import PlattCertificates.Count131072.C015039
import PlattCertificates.Count131072.C015040
import PlattCertificates.Count131072.C015041
import PlattCertificates.Count131072.C015042
import PlattCertificates.Count131072.C015043
import PlattCertificates.Count131072.C015044
import PlattCertificates.Count131072.C015045
import PlattCertificates.Count131072.C015046
import PlattCertificates.Count131072.C015047
import PlattCertificates.Count131072.C015048
import PlattCertificates.Count131072.C015049
import PlattCertificates.Count131072.C015050
import PlattCertificates.Count131072.C015051
import PlattCertificates.Count131072.C015052
import PlattCertificates.Count131072.C015053
import PlattCertificates.Count131072.C015054
import PlattCertificates.Count131072.C015055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15024 : List PrefixCut := [⟨59,401701817,401702079⟩,
⟨120,817798400,817798936⟩,
⟨128,873286446,873287018⟩]
theorem checked15024 : checkPrefixCuts (2^48) 1973157889 9 Manual.Count131072.C015024.packed 128 cuts15024 = true := by
 decide +kernel
def pointBounds15024 : List (Nat × Nat × Nat) := [(1973218304,96290162467455,96290540515669),(1973280768,96290578564038,96290956612526)]
theorem point_links_checked15024 : (cuts15024.take 2).map (fun c => (1973157889-1+2*2^9*c.k,96289760765638+c.lower,96290138813590+c.upper)) = pointBounds15024 := by
 decide +kernel
def cuts15025 : List PrefixCut := [⟨53,361593760,361594003⟩,
⟨114,772386393,772386906⟩,
⟨128,867237707,867238281⟩]
theorem checked15025 : checkPrefixCuts (2^48) 1973288961 9 Manual.Count131072.C015025.packed 128 cuts15025 = true := by
 decide +kernel
def pointBounds15025 : List (Nat × Nat × Nat) := [(1973343232,96290995645844,96291373694611),(1973405696,96291406438477,96291784487514)]
theorem point_links_checked15025 : (cuts15025.take 2).map (fun c => (1973288961-1+2*2^9*c.k,96290634052084+c.lower,96291012100608+c.upper)) = pointBounds15025 := by
 decide +kernel
def cuts15026 : List PrefixCut := [⟨47,314501975,314502182⟩,
⟨108,726837509,726837992⟩,
⟨128,865325703,865326277⟩]
theorem checked15026 : checkPrefixCuts (2^48) 1973420033 9 Manual.Count131072.C015026.packed 128 cuts15026 = true := by
 decide +kernel
def pointBounds15026 : List (Nat × Nat × Nat) := [(1973468160,96291815791766,96292193841071),(1973530624,96292228127300,96292606176881)]
theorem point_links_checked15026 : (cuts15026.take 2).map (fun c => (1973420033-1+2*2^9*c.k,96291501289791+c.lower,96291879338889+c.upper)) = pointBounds15026 := by
 decide +kernel
def cuts15027 : List PrefixCut := [⟨41,278112980,278113164⟩,
⟨102,695128803,695129270⟩,
⟨128,877390832,877391421⟩]
theorem checked15027 : checkPrefixCuts (2^48) 1973551105 9 Manual.Count131072.C015027.packed 128 cuts15027 = true := by
 decide +kernel
def pointBounds15027 : List (Nat × Nat × Nat) := [(1973593088,96292644728474,96293022778330),(1973655552,96293061744297,96293439794436)]
theorem point_links_checked15027 : (cuts15027.take 2).map (fun c => (1973551105-1+2*2^9*c.k,96292366615494+c.lower,96292744665166+c.upper)) = pointBounds15027 := by
 decide +kernel
def cuts15028 : List PrefixCut := [⟨35,234740674,234740829⟩,
⟨96,650446597,650447032⟩,
⟨128,867635232,867635814⟩]
theorem checked15028 : checkPrefixCuts (2^48) 1973682177 9 Manual.Count131072.C015028.packed 128 cuts15028 = true := by
 decide +kernel
def pointBounds15028 : List (Nat × Nat × Nat) := [(1973718016,96293478747000,96293856797416),(1973780480,96293894452923,96294272503619)]
theorem point_links_checked15028 : (cuts15028.take 2).map (fun c => (1973682177-1+2*2^9*c.k,96293244006326+c.lower,96293622056587+c.upper)) = pointBounds15028 := by
 decide +kernel
def cuts15029 : List PrefixCut := [⟨29,205491720,205491855⟩,
⟨90,617321108,617321515⟩,
⟨128,879413587,879414168⟩]
theorem checked15029 : checkPrefixCuts (2^48) 1973813249 9 Manual.Count131072.C015029.packed 128 cuts15029 = true := by
 decide +kernel
def pointBounds15029 : List (Nat × Nat × Nat) := [(1973842944,96294317133278,96294695184256),(1973905408,96294728962666,96295107013916)]
theorem point_links_checked15029 : (cuts15029.take 2).map (fun c => (1973813249-1+2*2^9*c.k,96294111641558+c.lower,96294489692401+c.upper)) = pointBounds15029 := by
 decide +kernel
def cuts15030 : List PrefixCut := [⟨23,161274158,161274268⟩,
⟨84,577070102,577070491⟩,
⟨128,884488335,884488929⟩]
theorem checked15030 : checkPrefixCuts (2^48) 1973944321 9 Manual.Count131072.C015030.packed 128 cuts15030 = true := by
 decide +kernel
def pointBounds15030 : List (Nat × Nat × Nat) := [(1973967872,96295152329303,96295530380837),(1974030336,96295568125247,96295946177060)]
theorem point_links_checked15030 : (cuts15030.take 2).map (fun c => (1973944321-1+2*2^9*c.k,96294991055145+c.lower,96295369106569+c.upper)) = pointBounds15030 := by
 decide +kernel
def cuts15031 : List PrefixCut := [⟨17,120912128,120912208⟩,
⟨78,533402350,533402706⟩,
⟨128,872025289,872025871⟩]
theorem checked15031 : checkPrefixCuts (2^48) 1974075393 9 Manual.Count131072.C015031.packed 128 cuts15031 = true := by
 decide +kernel
def pointBounds15031 : List (Nat × Nat × Nat) := [(1974092800,96295996455608,96296374507706),(1974155264,96296408945830,96296786998204)]
theorem point_links_checked15031 : (cuts15031.take 2).map (fun c => (1974075393-1+2*2^9*c.k,96295875543480+c.lower,96296253595498+c.upper)) = pointBounds15031 := by
 decide +kernel
def cuts15032 : List PrefixCut := [⟨11,71145326,71145373⟩,
⟨72,494444946,494445273⟩,
⟨128,876101709,876102289⟩]
theorem checked15032 : checkPrefixCuts (2^48) 1974206465 9 Manual.Count131072.C015032.packed 128 cuts15032 = true := by
 decide +kernel
def pointBounds15032 : List (Nat × Nat × Nat) := [(1974217728,96296818714095,96297196766742),(1974280192,96297242013715,96297620066642)]
theorem point_links_checked15032 : (cuts15032.take 2).map (fun c => (1974206465-1+2*2^9*c.k,96296747568769+c.lower,96297125621369+c.upper)) = pointBounds15032 := by
 decide +kernel
def cuts15033 : List PrefixCut := [⟨5,35213938,35213961⟩,
⟨66,445798569,445798866⟩,
⟨127,865636641,865637219⟩,
⟨128,871909163,871909745⟩]
theorem checked15033 : checkPrefixCuts (2^48) 1974337537 9 Manual.Count131072.C015033.packed 128 cuts15033 = true := by
 decide +kernel
def pointBounds15033 : List (Nat × Nat × Nat) := [(1974342656,96297658884416,96298036937619),(1974405120,96298069469047,96298447522524),(1974467584,96298489307119,96298867360877)]
theorem point_links_checked15033 : (cuts15033.take 3).map (fun c => (1974337537-1+2*2^9*c.k,96297623670478+c.lower,96298001723658+c.upper)) = pointBounds15033 := by
 decide +kernel
def cuts15034 : List PrefixCut := [⟨60,417401309,417401580⟩,
⟨121,832936351,832936890⟩,
⟨128,878551735,878552304⟩]
theorem checked15034 : checkPrefixCuts (2^48) 1974468609 9 Manual.Count131072.C015034.packed 128 cuts15034 = true := by
 decide +kernel
def pointBounds15034 : List (Nat × Nat × Nat) := [(1974530048,96298912980950,96299291034983),(1974592512,96299328515992,96299706570293)]
theorem point_links_checked15034 : (cuts15034.take 2).map (fun c => (1974468609-1+2*2^9*c.k,96298495579641+c.lower,96298873633403+c.upper)) = pointBounds15034 := by
 decide +kernel
def cuts15035 : List PrefixCut := [⟨54,369336200,369336452⟩,
⟨115,793967629,793968158⟩,
⟨128,880061090,880061672⟩]
theorem checked15035 : checkPrefixCuts (2^48) 1974599681 9 Manual.Count131072.C015035.packed 128 cuts15035 = true := by
 decide +kernel
def pointBounds15035 : List (Nat × Nat × Nat) := [(1974654976,96299743467576,96300121522159),(1974717440,96300168099005,96300546153865)]
theorem point_links_checked15035 : (cuts15035.take 2).map (fun c => (1974599681-1+2*2^9*c.k,96299374131376+c.lower,96299752185707+c.upper)) = pointBounds15035 := by
 decide +kernel
def cuts15036 : List PrefixCut := [⟨48,326266235,326266452⟩,
⟨109,733909347,733909835⟩,
⟨128,863468749,863469320⟩]
theorem checked15036 : checkPrefixCuts (2^48) 1974730753 9 Manual.Count131072.C015036.packed 128 cuts15036 = true := by
 decide +kernel
def pointBounds15036 : List (Nat × Nat × Nat) := [(1974779904,96300580458701,96300958513831),(1974842368,96300988101813,96301366157214)]
theorem point_links_checked15036 : (cuts15036.take 2).map (fun c => (1974730753-1+2*2^9*c.k,96300254192466+c.lower,96300632247379+c.upper)) = pointBounds15036 := by
 decide +kernel
def cuts15037 : List PrefixCut := [⟨42,292181037,292181233⟩,
⟨103,710345070,710345542⟩,
⟨128,883649846,883650431⟩]
theorem checked15037 : checkPrefixCuts (2^48) 1974861825 9 Manual.Count131072.C015037.packed 128 cuts15037 = true := by
 decide +kernel
def pointBounds15037 : List (Nat × Nat × Nat) := [(1974904832,96301409842252,96301787897932),(1974967296,96301828006285,96302206062241)]
theorem point_links_checked15037 : (cuts15037.take 2).map (fun c => (1974861825-1+2*2^9*c.k,96301117661215+c.lower,96301495716699+c.upper)) = pointBounds15037 := by
 decide +kernel
def cuts15038 : List PrefixCut := [⟨36,251116897,251117061⟩,
⟨97,662556282,662556724⟩,
⟨128,872475173,872475756⟩]
theorem checked15038 : checkPrefixCuts (2^48) 1974992897 9 Manual.Count131072.C015038.packed 128 cuts15038 = true := by
 decide +kernel
def pointBounds15038 : List (Nat × Nat × Nat) := [(1975029760,96302252427958,96302630484191),(1975092224,96302663867343,96303041923854)]
theorem point_links_checked15038 : (cuts15038.take 2).map (fun c => (1974992897-1+2*2^9*c.k,96302001311061+c.lower,96302379367130+c.upper)) = pointBounds15038 := by
 decide +kernel
def cuts15039 : List PrefixCut := [⟨30,203787673,203787813⟩,
⟨91,620473847,620474262⟩,
⟨128,865149598,865150177⟩]
theorem checked15039 : checkPrefixCuts (2^48) 1975123969 9 Manual.Count131072.C015039.packed 128 cuts15039 = true := by
 decide +kernel
def pointBounds15039 : List (Nat × Nat × Nat) := [(1975154688,96303077573907,96303455630699),(1975217152,96303494260081,96303872317148)]
theorem point_links_checked15039 : (cuts15039.take 2).map (fun c => (1975123969-1+2*2^9*c.k,96302873786234+c.lower,96303251842886+c.upper)) = pointBounds15039 := by
 decide +kernel
def cuts15040 : List PrefixCut := [⟨24,164444558,164444672⟩,
⟨85,584524186,584524580⟩,
⟨128,873356855,873357441⟩]
theorem checked15040 : checkPrefixCuts (2^48) 1975255041 9 Manual.Count131072.C015040.packed 128 cuts15040 = true := by
 decide +kernel
def pointBounds15040 : List (Nat × Nat × Nat) := [(1975279616,96303903380390,96304281437735),(1975342080,96304323460018,96304701517643)]
theorem point_links_checked15040 : (cuts15040.take 2).map (fun c => (1975255041-1+2*2^9*c.k,96303738935832+c.lower,96304116993063+c.upper)) = pointBounds15040 := by
 decide +kernel
def cuts15041 : List PrefixCut := [⟨18,120831859,120831942⟩,
⟨79,543734662,543735024⟩,
⟨128,882275300,882275887⟩]
theorem checked15041 : checkPrefixCuts (2^48) 1975386113 9 Manual.Count131072.C015041.packed 128 cuts15041 = true := by
 decide +kernel
def pointBounds15041 : List (Nat × Nat × Nat) := [(1975404544,96304733124546,96305111182446),(1975467008,96305156027349,96305534085528)]
theorem point_links_checked15041 : (cuts15041.take 2).map (fun c => (1975386113-1+2*2^9*c.k,96304612292687+c.lower,96304990350504+c.upper)) = pointBounds15041 := by
 decide +kernel
def cuts15042 : List PrefixCut := [⟨12,78934561,78934612⟩,
⟨73,495256639,495256968⟩,
⟨128,872813309,872813883⟩]
theorem checked15042 : checkPrefixCuts (2^48) 1975517185 9 Manual.Count131072.C015042.packed 128 cuts15042 = true := by
 decide +kernel
def pointBounds15042 : List (Nat × Nat × Nat) := [(1975529472,96305573502548,96305951561003),(1975591936,96305989824626,96306367883359)]
theorem point_links_checked15042 : (cuts15042.take 2).map (fun c => (1975517185-1+2*2^9*c.k,96305494567987+c.lower,96305872626391+c.upper)) = pointBounds15042 := by
 decide +kernel
def cuts15043 : List PrefixCut := [⟨6,39892149,39892175⟩,
⟨67,451201532,451201831⟩,
⟨128,863210214,863210785⟩]
theorem checked15043 : checkPrefixCuts (2^48) 1975648257 9 Manual.Count131072.C015043.packed 128 cuts15043 = true := by
 decide +kernel
def pointBounds15043 : List (Nat × Nat × Nat) := [(1975654400,96306407273445,96306785332449),(1975716864,96306818582828,96307196642105),(1975779328,96307230591510,96307608651059)]
theorem point_links_checked15043 : (cuts15043.take 3).map (fun c => (1975648257-1+2*2^9*c.k,96306367381296+c.lower,96306745440274+c.upper)) = pointBounds15043 := by
 decide +kernel
def cuts15044 : List PrefixCut := [⟨61,412707987,412708259⟩,
⟨122,830531282,830531833⟩,
⟨128,873979596,873980174⟩]
theorem checked15044 : checkPrefixCuts (2^48) 1975779329 9 Manual.Count131072.C015044.packed 128 cuts15044 = true := by
 decide +kernel
def pointBounds15044 : List (Nat × Nat × Nat) := [(1975841792,96307643299497,96308021359318),(1975904256,96308061122792,96308439182892)]
theorem point_links_checked15044 : (cuts15044.take 2).map (fun c => (1975779329-1+2*2^9*c.k,96307230591510+c.lower,96307608651059+c.upper)) = pointBounds15044 := by
 decide +kernel
def cuts15045 : List PrefixCut := [⟨55,366669475,366669717⟩,
⟨116,782472110,782472633⟩,
⟨128,864947340,864947918⟩]
theorem checked15045 : checkPrefixCuts (2^48) 1975910401 9 Manual.Count131072.C015045.packed 128 cuts15045 = true := by
 decide +kernel
def pointBounds15045 : List (Nat × Nat × Nat) := [(1975966720,96308471240581,96308849300950),(1976029184,96308887043216,96309265103866)]
theorem point_links_checked15045 : (cuts15045.take 2).map (fun c => (1975910401-1+2*2^9*c.k,96308104571106+c.lower,96308482631233+c.upper)) = pointBounds15045 := by
 decide +kernel
def cuts15046 : List PrefixCut := [⟨49,332602058,332602281⟩,
⟨110,743535569,743536064⟩,
⟨128,869448151,869448730⟩]
theorem checked15046 : checkPrefixCuts (2^48) 1976041473 9 Manual.Count131072.C015046.packed 128 cuts15046 = true := by
 decide +kernel
def pointBounds15046 : List (Nat × Nat × Nat) := [(1976091648,96309302120504,96309680181432),(1976154112,96309713054015,96310091115215)]
theorem point_links_checked15046 : (cuts15046.take 2).map (fun c => (1976041473-1+2*2^9*c.k,96308969518446+c.lower,96309347579151+c.upper)) = pointBounds15046 := by
 decide +kernel
def cuts15047 : List PrefixCut := [⟨43,290277924,290278115⟩,
⟨104,709303825,709304286⟩,
⟨128,871099537,871100103⟩]
theorem checked15047 : checkPrefixCuts (2^48) 1976172545 9 Manual.Count131072.C015047.packed 128 cuts15047 = true := by
 decide +kernel
def pointBounds15047 : List (Nat × Nat × Nat) := [(1976216576,96310129244521,96310507305996),(1976279040,96310548270422,96310926332167)]
theorem point_links_checked15047 : (cuts15047.take 2).map (fun c => (1976172545-1+2*2^9*c.k,96309838966597+c.lower,96310217027881+c.upper)) = pointBounds15047 := by
 decide +kernel
def cuts15048 : List PrefixCut := [⟨37,258641215,258641385⟩,
⟨98,677355801,677356246⟩,
⟨128,887847472,887848055⟩]
theorem checked15048 : checkPrefixCuts (2^48) 1976303617 9 Manual.Count131072.C015048.packed 128 cuts15048 = true := by
 decide +kernel
def pointBounds15048 : List (Nat × Nat × Nat) := [(1976341504,96310968707349,96311346769369),(1976403968,96311387421935,96311765484230)]
theorem point_links_checked15048 : (cuts15048.take 2).map (fun c => (1976303617-1+2*2^9*c.k,96310710066134+c.lower,96311088127984+c.upper)) = pointBounds15048 := by
 decide +kernel
def cuts15049 : List PrefixCut := [⟨31,206785629,206785770⟩,
⟨92,621343862,621344277⟩,
⟨128,869132691,869133270⟩]
theorem checked15049 : checkPrefixCuts (2^48) 1976434689 9 Manual.Count131072.C015049.packed 128 cuts15049 = true := by
 decide +kernel
def pointBounds15049 : List (Nat × Nat × Nat) := [(1976466432,96311804699235,96312182761809),(1976528896,96312219257468,96312597320316)]
theorem point_links_checked15049 : (cuts15049.take 2).map (fun c => (1976434689-1+2*2^9*c.k,96311597913606+c.lower,96311975976039+c.upper)) = pointBounds15049 := by
 decide +kernel
def cuts15050 : List PrefixCut := [⟨25,173734246,173734358⟩,
⟨86,589120695,589121080⟩,
⟨128,869360293,869360863⟩]
theorem checked15050 : checkPrefixCuts (2^48) 1976565761 9 Manual.Count131072.C015050.packed 128 cuts15050 = true := by
 decide +kernel
def pointBounds15050 : List (Nat × Nat × Nat) := [(1976591360,96312640780543,96313018843667),(1976653824,96313056166992,96313434230389)]
theorem point_links_checked15050 : (cuts15050.take 2).map (fun c => (1976565761-1+2*2^9*c.k,96312467046297+c.lower,96312845109309+c.upper)) = pointBounds15050 := by
 decide +kernel
def cuts15051 : List PrefixCut := [⟨19,134564119,134564210⟩,
⟨80,555762443,555762812⟩,
⟨128,878130940,878131527⟩]
theorem checked15051 : checkPrefixCuts (2^48) 1976696833 9 Manual.Count131072.C015051.packed 128 cuts15051 = true := by
 decide +kernel
def pointBounds15051 : List (Nat × Nat × Nat) := [(1976716288,96313470970709,96313849034382),(1976778752,96313892169033,96314270232984)]
theorem point_links_checked15051 : (cuts15051.take 2).map (fun c => (1976696833-1+2*2^9*c.k,96313336406590+c.lower,96313714470172+c.upper)) = pointBounds15051 := by
 decide +kernel
def cuts15052 : List PrefixCut := [⟨13,89561203,89561264⟩,
⟨74,493789237,493789566⟩,
⟨128,861413574,861414150⟩]
theorem checked15052 : checkPrefixCuts (2^48) 1976827905 9 Manual.Count131072.C015052.packed 128 cuts15052 = true := by
 decide +kernel
def pointBounds15052 : List (Nat × Nat × Nat) := [(1976841216,96314304098733,96314682162963),(1976903680,96314708326767,96315086391265)]
theorem point_links_checked15052 : (cuts15052.take 2).map (fun c => (1976827905-1+2*2^9*c.k,96314214537530+c.lower,96314592601699+c.upper)) = pointBounds15052 := by
 decide +kernel
def cuts15053 : List PrefixCut := [⟨7,54245807,54245842⟩,
⟨68,463573738,463574049⟩,
⟨128,870326142,870326718⟩]
theorem checked15053 : checkPrefixCuts (2^48) 1976958977 9 Manual.Count131072.C015053.packed 128 cuts15053 = true := by
 decide +kernel
def pointBounds15053 : List (Nat × Nat × Nat) := [(1976966144,96315130196911,96315508261691),(1977028608,96315539524842,96315917589898)]
theorem point_links_checked15053 : (cuts15053.take 2).map (fun c => (1976958977-1+2*2^9*c.k,96315075951104+c.lower,96315454015849+c.upper)) = pointBounds15053 := by
 decide +kernel
def cuts15054 : List PrefixCut := [⟨1,6833675,6833680⟩,
⟨62,428663948,428664231⟩,
⟨123,839661431,839661989⟩,
⟨128,872119285,872119866⟩]
theorem checked15054 : checkPrefixCuts (2^48) 1977090049 9 Manual.Count131072.C015054.packed 128 cuts15054 = true := by
 decide +kernel
def pointBounds15054 : List (Nat × Nat × Nat) := [(1977091072,96315953110921,96316331176247),(1977153536,96316374941194,96316753006798),(1977216000,96316785938677,96317164004556)]
theorem point_links_checked15054 : (cuts15054.take 3).map (fun c => (1977090049-1+2*2^9*c.k,96315946277246+c.lower,96316324342567+c.upper)) = pointBounds15054 := by
 decide +kernel
def cuts15055 : List PrefixCut := [⟨56,385644440,385644696⟩,
⟨117,806580689,806581221⟩,
⟨128,879748492,879749073⟩]
theorem checked15055 : checkPrefixCuts (2^48) 1977221121 9 Manual.Count131072.C015055.packed 128 cuts15055 = true := by
 decide +kernel
def pointBounds15055 : List (Nat × Nat × Nat) := [(1977278464,96317204040971,96317582107129),(1977340928,96317624977220,96318003043654)]
theorem point_links_checked15055 : (cuts15055.take 2).map (fun c => (1977221121-1+2*2^9*c.k,96316818396531+c.lower,96317196462433+c.upper)) = pointBounds15055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000157
