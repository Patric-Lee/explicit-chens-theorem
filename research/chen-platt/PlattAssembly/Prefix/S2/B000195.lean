import PlattAssemblyKernel
import PlattCertificates.Count131072.C016240
import PlattCertificates.Count131072.C016241
import PlattCertificates.Count131072.C016242
import PlattCertificates.Count131072.C016243
import PlattCertificates.Count131072.C016244
import PlattCertificates.Count131072.C016245
import PlattCertificates.Count131072.C016246
import PlattCertificates.Count131072.C016247
import PlattCertificates.Count131072.C016248
import PlattCertificates.Count131072.C016249
import PlattCertificates.Count131072.C016250
import PlattCertificates.Count131072.C016251
import PlattCertificates.Count131072.C016252
import PlattCertificates.Count131072.C016253
import PlattCertificates.Count131072.C016254
import PlattCertificates.Count131072.C016255
import PlattCertificates.Count131072.C016256
import PlattCertificates.Count131072.C016257
import PlattCertificates.Count131072.C016258
import PlattCertificates.Count131072.C016259
import PlattCertificates.Count131072.C016260
import PlattCertificates.Count131072.C016261
import PlattCertificates.Count131072.C016262
import PlattCertificates.Count131072.C016263
import PlattCertificates.Count131072.C016264
import PlattCertificates.Count131072.C016265
import PlattCertificates.Count131072.C016266
import PlattCertificates.Count131072.C016267
import PlattCertificates.Count131072.C016268
import PlattCertificates.Count131072.C016269
import PlattCertificates.Count131072.C016270
import PlattCertificates.Count131072.C016271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000195
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16240 : List PrefixCut := [⟨31,193232412,193232536⟩,
⟨97,618624210,618624602⟩,
⟨128,810527807,810528322⟩]
theorem checked16240 : checkPrefixCuts (2^48) 2132541441 9 Manual.Count131072.C016240.packed 128 cuts16240 = true := by
 decide +kernel
def pointBounds16240 : List (Nat × Nat × Nat) := [(2132573184,97309690121951,97310068834841),(2132640768,97310115513749,97310494226907)]
theorem point_links_checked16240 : (cuts16240.take 2).map (fun c => (2132541441-1+2*2^9*c.k,97309496889539+c.lower,97309875602305+c.upper)) = pointBounds16240 := by
 decide +kernel
def cuts16241 : List PrefixCut := [⟨35,214337357,214337496⟩,
⟨101,635742898,635743306⟩,
⟨128,802955207,802955722⟩]
theorem checked16241 : checkPrefixCuts (2^48) 2132672513 9 Manual.Count131072.C016241.packed 128 cuts16241 = true := by
 decide +kernel
def pointBounds16241 : List (Nat × Nat × Nat) := [(2132708352,97310521754703,97310900468123),(2132775936,97310943160244,97311321873933)]
theorem point_links_checked16241 : (cuts16241.take 2).map (fun c => (2132672513-1+2*2^9*c.k,97310307417346+c.lower,97310686130627+c.upper)) = pointBounds16241 := by
 decide +kernel
def cuts16242 : List PrefixCut := [⟨39,242038300,242038454⟩,
⟨105,660513771,660514194⟩,
⟨128,806337017,806337533⟩]
theorem checked16242 : checkPrefixCuts (2^48) 2132803585 9 Manual.Count131072.C016242.packed 128 cuts16242 = true := by
 decide +kernel
def pointBounds16242 : List (Nat × Nat × Nat) := [(2132843520,97311352410853,97311731124803),(2132911104,97311770886324,97312149600543)]
theorem point_links_checked16242 : (cuts16242.take 2).map (fun c => (2132803585-1+2*2^9*c.k,97311110372553+c.lower,97311489086349+c.upper)) = pointBounds16242 := by
 decide +kernel
def cuts16243 : List PrefixCut := [⟨43,269603827,269604002⟩,
⟨109,686469297,686469737⟩,
⟨128,805891750,805892263⟩]
theorem checked16243 : checkPrefixCuts (2^48) 2132934657 9 Manual.Count131072.C016243.packed 128 cuts16243 = true := by
 decide +kernel
def pointBounds16243 : List (Nat × Nat × Nat) := [(2132978688,97312186313397,97312565027884),(2133046272,97312603178867,97312981893619)]
theorem point_links_checked16243 : (cuts16243.take 2).map (fun c => (2132934657-1+2*2^9*c.k,97311916709570+c.lower,97312295423882+c.upper)) = pointBounds16243 := by
 decide +kernel
def cuts16244 : List PrefixCut := [⟨47,290831948,290832132⟩,
⟨113,705691644,705692088⟩,
⟨128,797660974,797661476⟩]
theorem checked16244 : checkPrefixCuts (2^48) 2133065729 9 Manual.Count131072.C016244.packed 128 cuts16244 = true := by
 decide +kernel
def pointBounds16244 : List (Nat × Nat × Nat) := [(2133113856,97313013433268,97313392148277),(2133181440,97313428292964,97313807008233)]
theorem point_links_checked16244 : (cuts16244.take 2).map (fun c => (2133065729-1+2*2^9*c.k,97312722601320+c.lower,97313101316145+c.upper)) = pointBounds16244 := by
 decide +kernel
def cuts16245 : List PrefixCut := [⟨51,322877213,322877418⟩,
⟨117,731509251,731509716⟩,
⟨128,799327456,799327967⟩]
theorem checked16245 : checkPrefixCuts (2^48) 2133196801 9 Manual.Count131072.C016245.packed 128 cuts16245 = true := by
 decide +kernel
def pointBounds16245 : List (Nat × Nat × Nat) := [(2133249024,97313843139507,97314221855039),(2133316608,97314251771545,97314630487337)]
theorem point_links_checked16245 : (cuts16245.take 2).map (fun c => (2133196801-1+2*2^9*c.k,97313520262294+c.lower,97313898977621+c.upper)) = pointBounds16245 := by
 decide +kernel
def cuts16246 : List PrefixCut := [⟨55,345682684,345682906⟩,
⟨121,762864717,762865202⟩,
⟨128,809965088,809965603⟩]
theorem checked16246 : checkPrefixCuts (2^48) 2133327873 9 Manual.Count131072.C016246.packed 128 cuts16246 = true := by
 decide +kernel
def pointBounds16246 : List (Nat × Nat × Nat) := [(2133384192,97314665272434,97315043988494),(2133451776,97315082454467,97315461170790)]
theorem point_links_checked16246 : (cuts16246.take 2).map (fun c => (2133327873-1+2*2^9*c.k,97314319589750+c.lower,97314698305588+c.upper)) = pointBounds16246 := by
 decide +kernel
def cuts16247 : List PrefixCut := [⟨59,363339896,363340131⟩,
⟨125,775746149,775746644⟩,
⟨128,795007284,795007791⟩]
theorem checked16247 : checkPrefixCuts (2^48) 2133458945 9 Manual.Count131072.C016247.packed 128 cuts16247 = true := by
 decide +kernel
def pointBounds16247 : List (Nat × Nat × Nat) := [(2133519360,97315492894734,97315871611322),(2133586944,97315905300987,97316284017835)]
theorem point_links_checked16247 : (cuts16247.take 2).map (fun c => (2133458945-1+2*2^9*c.k,97315129554838+c.lower,97315508271191+c.upper)) = pointBounds16247 := by
 decide +kernel
def cuts16248 : List PrefixCut := [⟨63,395242798,395243049⟩,
⟨128,809997580,809998091⟩]
theorem checked16248 : checkPrefixCuts (2^48) 2133590017 9 Manual.Count131072.C016248.packed 128 cuts16248 = true := by
 decide +kernel
def pointBounds16248 : List (Nat × Nat × Nat) := [(2133654528,97316319804920,97316698522031)]
theorem point_links_checked16248 : (cuts16248.take 1).map (fun c => (2133590017-1+2*2^9*c.k,97315924562122+c.lower,97316303278982+c.upper)) = pointBounds16248 := by
 decide +kernel
def cuts16249 : List PrefixCut := [⟨1,7255454,7255458⟩,
⟨67,422128824,422129096⟩,
⟨128,812058373,812058891⟩]
theorem checked16249 : checkPrefixCuts (2^48) 2133721089 9 Manual.Count131072.C016249.packed 128 cuts16249 = true := by
 decide +kernel
def pointBounds16249 : List (Nat × Nat × Nat) := [(2133722112,97316741815156,97317120532531),(2133789696,97317156688526,97317535406169)]
theorem point_links_checked16249 : (cuts16249.take 2).map (fun c => (2133721089-1+2*2^9*c.k,97316734559702+c.lower,97317113277073+c.upper)) = pointBounds16249 := by
 decide +kernel
def cuts16250 : List PrefixCut := [⟨5,31658186,31658207⟩,
⟨71,441888504,441888788⟩,
⟨128,800136986,800137504⟩]
theorem checked16250 : checkPrefixCuts (2^48) 2133852161 9 Manual.Count131072.C016250.packed 128 cuts16250 = true := by
 decide +kernel
def pointBounds16250 : List (Nat × Nat × Nat) := [(2133857280,97317578276261,97317956994171),(2133924864,97317988506579,97318367224752)]
theorem point_links_checked16250 : (cuts16250.take 2).map (fun c => (2133852161-1+2*2^9*c.k,97317546618075+c.lower,97317925335964+c.upper)) = pointBounds16250 := by
 decide +kernel
def cuts16251 : List PrefixCut := [⟨9,58432091,58432129⟩,
⟨75,471010552,471010851⟩,
⟨128,797186289,797186797⟩]
theorem checked16251 : checkPrefixCuts (2^48) 2133983233 9 Manual.Count131072.C016251.packed 128 cuts16251 = true := by
 decide +kernel
def pointBounds16251 : List (Nat × Nat × Nat) := [(2133992448,97318405187152,97318783905597),(2134060032,97318817765613,97319196484319)]
theorem point_links_checked16251 : (cuts16251.take 2).map (fun c => (2133983233-1+2*2^9*c.k,97318346755061+c.lower,97318725473468+c.upper)) = pointBounds16251 := by
 decide +kernel
def cuts16252 : List PrefixCut := [⟨13,82169135,82169185⟩,
⟨79,492611298,492611613⟩,
⟨128,800830087,800830601⟩]
theorem checked16252 : checkPrefixCuts (2^48) 2134114305 9 Manual.Count131072.C016252.packed 128 cuts16252 = true := by
 decide +kernel
def pointBounds16252 : List (Nat × Nat × Nat) := [(2134127616,97319226110485,97319604829450),(2134195200,97319636552648,97320015271878)]
theorem point_links_checked16252 : (cuts16252.take 2).map (fun c => (2134114305-1+2*2^9*c.k,97319143941350+c.lower,97319522660265+c.upper)) = pointBounds16252 := by
 decide +kernel
def cuts16253 : List PrefixCut := [⟨17,104188697,104188761⟩,
⟨83,518956927,518957258⟩,
⟨128,805264677,805265186⟩]
theorem checked16253 : checkPrefixCuts (2^48) 2134245377 9 Manual.Count131072.C016253.packed 128 cuts16253 = true := by
 decide +kernel
def pointBounds16253 : List (Nat × Nat × Nat) := [(2134262784,97320048960134,97320427679627),(2134330368,97320463728364,97320842448124)]
theorem point_links_checked16253 : (cuts16253.take 2).map (fun c => (2134245377-1+2*2^9*c.k,97319944771437+c.lower,97320323490866+c.upper)) = pointBounds16253 := by
 decide +kernel
def cuts16254 : List PrefixCut := [⟨21,130029933,130030015⟩,
⟨87,544640066,544640409⟩,
⟨128,797434947,797435453⟩]
theorem checked16254 : checkPrefixCuts (2^48) 2134376449 9 Manual.Count131072.C016254.packed 128 cuts16254 = true := by
 decide +kernel
def pointBounds16254 : List (Nat × Nat × Nat) := [(2134397952,97320880066047,97321258786067),(2134465536,97321294676180,97321673396461)]
theorem point_links_checked16254 : (cuts16254.take 2).map (fun c => (2134376449-1+2*2^9*c.k,97320750036114+c.lower,97321128756052+c.upper)) = pointBounds16254 := by
 decide +kernel
def cuts16255 : List PrefixCut := [⟨25,161802021,161802123⟩,
⟨91,583770326,583770693⟩,
⟨128,812418769,812419282⟩]
theorem checked16255 : checkPrefixCuts (2^48) 2134507521 9 Manual.Count131072.C016255.packed 128 cuts16255 = true := by
 decide +kernel
def pointBounds16255 : List (Nat × Nat × Nat) := [(2134533120,97321709273082,97322087993628),(2134600704,97322131241387,97322509962198)]
theorem point_links_checked16255 : (cuts16255.take 2).map (fun c => (2134507521-1+2*2^9*c.k,97321547471061+c.lower,97321926191505+c.upper)) = pointBounds16255 := by
 decide +kernel
def cuts16256 : List PrefixCut := [⟨29,180252284,180252397⟩,
⟨95,602853251,602853630⟩,
⟨128,807358208,807358719⟩]
theorem checked16256 : checkPrefixCuts (2^48) 2134638593 9 Manual.Count131072.C016256.packed 128 cuts16256 = true := by
 decide +kernel
def pointBounds16256 : List (Nat × Nat × Nat) := [(2134668288,97322540142114,97322918863184),(2134735872,97322962743081,97323341464417)]
theorem point_links_checked16256 : (cuts16256.take 2).map (fun c => (2134638593-1+2*2^9*c.k,97322359889830+c.lower,97322738610787+c.upper)) = pointBounds16256 := by
 decide +kernel
def cuts16257 : List PrefixCut := [⟨33,205820268,205820395⟩,
⟨99,623252273,623252670⟩,
⟨128,809022438,809022952⟩]
theorem checked16257 : checkPrefixCuts (2^48) 2134769665 9 Manual.Count131072.C016257.packed 128 cuts16257 = true := by
 decide +kernel
def pointBounds16257 : List (Nat × Nat × Nat) := [(2134803456,97323373068306,97323751789901),(2134871040,97323790500311,97324169222176)]
theorem point_links_checked16257 : (cuts16257.take 2).map (fun c => (2134769665-1+2*2^9*c.k,97323167248038+c.lower,97323545969506+c.upper)) = pointBounds16257 := by
 decide +kernel
def cuts16258 : List PrefixCut := [⟨37,238504549,238504704⟩,
⟨103,652350510,652350928⟩,
⟨128,808050214,808050732⟩]
theorem checked16258 : checkPrefixCuts (2^48) 2134900737 9 Manual.Count131072.C016258.packed 128 cuts16258 = true := by
 decide +kernel
def pointBounds16258 : List (Nat × Nat × Nat) := [(2134938624,97324214775025,97324593497162),(2135006208,97324628620986,97325007343386)]
theorem point_links_checked16258 : (cuts16258.take 2).map (fun c => (2134900737-1+2*2^9*c.k,97323976270476+c.lower,97324354992458+c.upper)) = pointBounds16258 := by
 decide +kernel
def cuts16259 : List PrefixCut := [⟨41,256814740,256814901⟩,
⟨107,666415798,666416218⟩,
⟨128,794817207,794817712⟩]
theorem checked16259 : checkPrefixCuts (2^48) 2135031809 9 Manual.Count131072.C016259.packed 128 cuts16259 = true := by
 decide +kernel
def pointBounds16259 : List (Nat × Nat × Nat) := [(2135073792,97325041135430,97325419858091),(2135141376,97325450736488,97325829459408)]
theorem point_links_checked16259 : (cuts16259.take 2).map (fun c => (2135031809-1+2*2^9*c.k,97324784320690+c.lower,97325163043190+c.upper)) = pointBounds16259 := by
 decide +kernel
def cuts16260 : List PrefixCut := [⟨45,286459839,286460021⟩,
⟨111,697880482,697880926⟩,
⟨128,803996169,803996681⟩]
theorem checked16260 : checkPrefixCuts (2^48) 2135162881 9 Manual.Count131072.C016260.packed 128 cuts16260 = true := by
 decide +kernel
def pointBounds16260 : List (Nat × Nat × Nat) := [(2135208960,97325865597736,97326244320923),(2135276544,97326277018379,97326655741828)]
theorem point_links_checked16260 : (cuts16260.take 2).map (fun c => (2135162881-1+2*2^9*c.k,97325579137897+c.lower,97325957860902+c.upper)) = pointBounds16260 := by
 decide +kernel
def cuts16261 : List PrefixCut := [⟨49,309510155,309510347⟩,
⟨115,725254690,725255146⟩,
⟨128,801310521,801311026⟩]
theorem checked16261 : checkPrefixCuts (2^48) 2135293953 9 Manual.Count131072.C016261.packed 128 cuts16261 = true := by
 decide +kernel
def pointBounds16261 : List (Nat × Nat × Nat) := [(2135344128,97326692644221,97327071367930),(2135411712,97327108388756,97327487112729)]
theorem point_links_checked16261 : (cuts16261.take 2).map (fun c => (2135293953-1+2*2^9*c.k,97326383134066+c.lower,97326761857583+c.upper)) = pointBounds16261 := by
 decide +kernel
def cuts16262 : List PrefixCut := [⟨53,327680763,327680975⟩,
⟨119,739444850,739445323⟩,
⟨128,795329877,795330386⟩]
theorem checked16262 : checkPrefixCuts (2^48) 2135425025 9 Manual.Count131072.C016262.packed 128 cuts16262 = true := by
 decide +kernel
def pointBounds16262 : List (Nat × Nat × Nat) := [(2135479296,97327512125350,97327890849584),(2135546880,97327923889437,97328302613932)]
theorem point_links_checked16262 : (cuts16262.take 2).map (fun c => (2135425025-1+2*2^9*c.k,97327184444587+c.lower,97327563168609+c.upper)) = pointBounds16262 := by
 decide +kernel
def cuts16263 : List PrefixCut := [⟨57,358633877,358634106⟩,
⟨123,772875998,772876489⟩,
⟨128,805297835,805298348⟩]
theorem checked16263 : checkPrefixCuts (2^48) 2135556097 9 Manual.Count131072.C016263.packed 128 cuts16263 = true := by
 decide +kernel
def pointBounds16263 : List (Nat × Nat × Nat) := [(2135614464,97328338408341,97328717133101),(2135682048,97328752650462,97329131375484)]
theorem point_links_checked16263 : (cuts16263.take 2).map (fun c => (2135556097-1+2*2^9*c.k,97327979774464+c.lower,97328358498995+c.upper)) = pointBounds16263 := by
 decide +kernel
def cuts16264 : List PrefixCut := [⟨61,384574944,384575185⟩,
⟨127,790751661,790752161⟩,
⟨128,796682115,796682619⟩]
theorem checked16264 : checkPrefixCuts (2^48) 2135687169 9 Manual.Count131072.C016264.packed 128 cuts16264 = true := by
 decide +kernel
def pointBounds16264 : List (Nat × Nat × Nat) := [(2135749632,97329169647243,97329548372528),(2135817216,97329575823960,97329954549504)]
theorem point_links_checked16264 : (cuts16264.take 2).map (fun c => (2135687169-1+2*2^9*c.k,97328785072299+c.lower,97329163797343+c.upper)) = pointBounds16264 := by
 decide +kernel
def cuts16265 : List PrefixCut := [⟨65,409194824,409195084⟩,
⟨128,804276485,804276993⟩]
theorem checked16265 : checkPrefixCuts (2^48) 2135818241 9 Manual.Count131072.C016265.packed 128 cuts16265 = true := by
 decide +kernel
def pointBounds16265 : List (Nat × Nat × Nat) := [(2135884800,97329990949238,97330369675046)]
theorem point_links_checked16265 : (cuts16265.take 1).map (fun c => (2135818241-1+2*2^9*c.k,97329581754414+c.lower,97329960479962+c.upper)) = pointBounds16265 := by
 decide +kernel
def cuts16266 : List PrefixCut := [⟨3,19108052,19108064⟩,
⟨69,433416433,433416712⟩,
⟨128,803699993,803700509⟩]
theorem checked16266 : checkPrefixCuts (2^48) 2135949313 9 Manual.Count131072.C016266.packed 128 cuts16266 = true := by
 decide +kernel
def pointBounds16266 : List (Nat × Nat × Nat) := [(2135952384,97330405138951,97330783865019),(2136019968,97330819447332,97331198173667)]
theorem point_links_checked16266 : (cuts16266.take 2).map (fun c => (2135949313-1+2*2^9*c.k,97330386030899+c.lower,97330764756955+c.upper)) = pointBounds16266 := by
 decide +kernel
def cuts16267 : List PrefixCut := [⟨7,45988239,45988267⟩,
⟨73,454999664,454999959⟩,
⟨128,798116605,798117118⟩]
theorem checked16267 : checkPrefixCuts (2^48) 2136080385 9 Manual.Count131072.C016267.packed 128 cuts16267 = true := by
 decide +kernel
def pointBounds16267 : List (Nat × Nat × Nat) := [(2136087552,97331235719131,97331614445731),(2136155136,97331644730556,97332023457423)]
theorem point_links_checked16267 : (cuts16267.take 2).map (fun c => (2136080385-1+2*2^9*c.k,97331189730892+c.lower,97331568457464+c.upper)) = pointBounds16267 := by
 decide +kernel
def cuts16268 : List PrefixCut := [⟨11,71942733,71942779⟩,
⟨77,484881165,484881472⟩,
⟨128,810321236,810321747⟩]
theorem checked16268 : checkPrefixCuts (2^48) 2136211457 9 Manual.Count131072.C016268.packed 128 cuts16268 = true := by
 decide +kernel
def pointBounds16268 : List (Nat × Nat × Nat) := [(2136222720,97332059790230,97332438517361),(2136290304,97332472728662,97332851456054)]
theorem point_links_checked16268 : (cuts16268.take 2).map (fun c => (2136211457-1+2*2^9*c.k,97331987847497+c.lower,97332366574582+c.upper)) = pointBounds16268 := by
 decide +kernel
def cuts16269 : List PrefixCut := [⟨15,92228527,92228588⟩,
⟨81,517789016,517789351⟩,
⟨128,806055608,806056129⟩]
theorem checked16269 : checkPrefixCuts (2^48) 2136342529 9 Manual.Count131072.C016269.packed 128 cuts16269 = true := by
 decide +kernel
def pointBounds16269 : List (Nat × Nat × Nat) := [(2136357888,97332890397260,97333269124917),(2136425472,97333315957749,97333694685680)]
theorem point_links_checked16269 : (cuts16269.take 2).map (fun c => (2136342529-1+2*2^9*c.k,97332798168733+c.lower,97333176896329+c.upper)) = pointBounds16269 := by
 decide +kernel
def cuts16270 : List PrefixCut := [⟨19,120811845,120811922⟩,
⟨85,534356765,534357109⟩,
⟨128,812461380,812461898⟩]
theorem checked16270 : checkPrefixCuts (2^48) 2136473601 9 Manual.Count131072.C016270.packed 128 cuts16270 = true := by
 decide +kernel
def pointBounds16270 : List (Nat × Nat × Nat) := [(2136493056,97333725036186,97334103764380),(2136560640,97334138581106,97334517309567)]
theorem point_links_checked16270 : (cuts16270.take 2).map (fun c => (2136473601-1+2*2^9*c.k,97333604224341+c.lower,97333982952458+c.upper)) = pointBounds16270 := by
 decide +kernel
def cuts16271 : List PrefixCut := [⟨23,136085986,136086075⟩,
⟨89,543281397,543281744⟩,
⟨128,791201960,791202464⟩]
theorem checked16271 : checkPrefixCuts (2^48) 2136604673 9 Manual.Count131072.C016271.packed 128 cuts16271 = true := by
 decide +kernel
def pointBounds16271 : List (Nat × Nat × Nat) := [(2136628224,97334552771707,97334931500431),(2136695808,97334959967118,97335338696100)]
theorem point_links_checked16271 : (cuts16271.take 2).map (fun c => (2136604673-1+2*2^9*c.k,97334416685721+c.lower,97334795414356+c.upper)) = pointBounds16271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000195
