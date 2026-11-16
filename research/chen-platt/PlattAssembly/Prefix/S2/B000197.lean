import PlattAssemblyKernel
import PlattCertificates.Count131072.C016304
import PlattCertificates.Count131072.C016305
import PlattCertificates.Count131072.C016306
import PlattCertificates.Count131072.C016307
import PlattCertificates.Count131072.C016308
import PlattCertificates.Count131072.C016309
import PlattCertificates.Count131072.C016310
import PlattCertificates.Count131072.C016311
import PlattCertificates.Count131072.C016312
import PlattCertificates.Count131072.C016313
import PlattCertificates.Count131072.C016314
import PlattCertificates.Count131072.C016315
import PlattCertificates.Count131072.C016316
import PlattCertificates.Count131072.C016317
import PlattCertificates.Count131072.C016318
import PlattCertificates.Count131072.C016319
import PlattCertificates.Count131072.C016320
import PlattCertificates.Count131072.C016321
import PlattCertificates.Count131072.C016322
import PlattCertificates.Count131072.C016323
import PlattCertificates.Count131072.C016324
import PlattCertificates.Count131072.C016325
import PlattCertificates.Count131072.C016326
import PlattCertificates.Count131072.C016327
import PlattCertificates.Count131072.C016328
import PlattCertificates.Count131072.C016329
import PlattCertificates.Count131072.C016330
import PlattCertificates.Count131072.C016331
import PlattCertificates.Count131072.C016332
import PlattCertificates.Count131072.C016333
import PlattCertificates.Count131072.C016334
import PlattCertificates.Count131072.C016335
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000197
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16304 : List PrefixCut := [⟨23,141069956,141070046⟩,
⟨89,557171443,557171797⟩,
⟨128,796966100,796966608⟩]
theorem checked16304 : checkPrefixCuts (2^48) 2140930049 9 Manual.Count131072.C016304.packed 128 cuts16304 = true := by
 decide +kernel
def pointBounds16304 : List (Nat × Nat × Nat) := [(2140953600,97361049910333,97361428655966),(2141021184,97361466011820,97361844757717)]
theorem point_links_checked16304 : (cuts16304.take 2).map (fun c => (2140930049-1+2*2^9*c.k,97360908840377+c.lower,97361287585920+c.upper)) = pointBounds16304 := by
 decide +kernel
def cuts16305 : List PrefixCut := [⟨27,169325991,169326099⟩,
⟨93,588819267,588819641⟩,
⟨128,809931918,809932434⟩]
theorem checked16305 : checkPrefixCuts (2^48) 2141061121 9 Manual.Count131072.C016305.packed 128 cuts16305 = true := by
 decide +kernel
def pointBounds16305 : List (Nat × Nat × Nat) := [(2141088768,97361875132468,97362253878627),(2141156352,97362294625744,97362673372169)]
theorem point_links_checked16305 : (cuts16305.take 2).map (fun c => (2141061121-1+2*2^9*c.k,97361705806477+c.lower,97362084552528+c.upper)) = pointBounds16305 := by
 decide +kernel
def cuts16306 : List PrefixCut := [⟨31,188639546,188639670⟩,
⟨97,601402232,601402618⟩,
⟨128,796079690,796080199⟩]
theorem checked16306 : checkPrefixCuts (2^48) 2141192193 9 Manual.Count131072.C016306.packed 128 cuts16306 = true := by
 decide +kernel
def pointBounds16306 : List (Nat × Nat × Nat) := [(2141223936,97362704377941,97363083124632),(2141291520,97363117140627,97363495887580)]
theorem point_links_checked16306 : (cuts16306.take 2).map (fun c => (2141192193-1+2*2^9*c.k,97362515738395+c.lower,97362894484962+c.upper)) = pointBounds16306 := by
 decide +kernel
def cuts16307 : List PrefixCut := [⟨35,224250189,224250330⟩,
⟨101,640009958,640010364⟩,
⟨128,807992625,807993139⟩]
theorem checked16307 : checkPrefixCuts (2^48) 2141323265 9 Manual.Count131072.C016307.packed 128 cuts16307 = true := by
 decide +kernel
def pointBounds16307 : List (Nat × Nat × Nat) := [(2141359104,97363536068274,97363914815491),(2141426688,97363951828043,97364330575525)]
theorem point_links_checked16307 : (cuts16307.take 2).map (fun c => (2141323265-1+2*2^9*c.k,97363311818085+c.lower,97363690565161+c.upper)) = pointBounds16307 := by
 decide +kernel
def cuts16308 : List PrefixCut := [⟨39,244740837,244740993⟩,
⟨105,664548900,664549322⟩,
⟨128,810440282,810440797⟩]
theorem checked16308 : checkPrefixCuts (2^48) 2141454337 9 Manual.Count131072.C016308.packed 128 cuts16308 = true := by
 decide +kernel
def pointBounds16308 : List (Nat × Nat × Nat) := [(2141494272,97364364551547,97364743299293),(2141561856,97364784359610,97365163107622)]
theorem point_links_checked16308 : (cuts16308.take 2).map (fun c => (2141454337-1+2*2^9*c.k,97364119810710+c.lower,97364498558300+c.upper)) = pointBounds16308 := by
 decide +kernel
def cuts16309 : List PrefixCut := [⟨43,267594703,267594872⟩,
⟨109,674496257,674496684⟩,
⟨128,798036236,798036741⟩]
theorem checked16309 : checkPrefixCuts (2^48) 2141585409 9 Manual.Count131072.C016309.packed 128 cuts16309 = true := by
 decide +kernel
def pointBounds16309 : List (Nat × Nat × Nat) := [(2141629440,97365197845695,97365576593969),(2141697024,97365604747249,97365983495781)]
theorem point_links_checked16309 : (cuts16309.take 2).map (fun c => (2141585409-1+2*2^9*c.k,97364930250992+c.lower,97365308999097+c.upper)) = pointBounds16309 := by
 decide +kernel
def cuts16310 : List PrefixCut := [⟨47,293468508,293468696⟩,
⟨113,691276459,691276906⟩,
⟨128,787079694,787080201⟩]
theorem checked16310 : checkPrefixCuts (2^48) 2141716481 9 Manual.Count131072.C016310.packed 128 cuts16310 = true := by
 decide +kernel
def pointBounds16310 : List (Nat × Nat × Nat) := [(2141764608,97366021755736,97366400504534),(2141832192,97366419563687,97366798312744)]
theorem point_links_checked16310 : (cuts16310.take 2).map (fun c => (2141716481-1+2*2^9*c.k,97365728287228+c.lower,97366107035838+c.upper)) = pointBounds16310 := by
 decide +kernel
def cuts16311 : List PrefixCut := [⟨51,331035085,331035289⟩,
⟨117,748398257,748398724⟩,
⟨128,814759887,814760396⟩]
theorem checked16311 : checkPrefixCuts (2^48) 2141847553 9 Manual.Count131072.C016311.packed 128 cuts16311 = true := by
 decide +kernel
def pointBounds16311 : List (Nat × Nat × Nat) := [(2141899776,97366846402007,97367225151328),(2141967360,97367263765179,97367642514763)]
theorem point_links_checked16311 : (cuts16311.take 2).map (fun c => (2141847553-1+2*2^9*c.k,97366515366922+c.lower,97366894116039+c.upper)) = pointBounds16311 := by
 decide +kernel
def cuts16312 : List PrefixCut := [⟨55,347046169,347046387⟩,
⟨121,764908632,764909116⟩,
⟨128,808270961,808271473⟩]
theorem checked16312 : checkPrefixCuts (2^48) 2141978625 9 Manual.Count131072.C016312.packed 128 cuts16312 = true := by
 decide +kernel
def pointBounds16312 : List (Nat × Nat × Nat) := [(2142034944,97367677172978,97368055922822),(2142102528,97368095035441,97368473785551)]
theorem point_links_checked16312 : (cuts16312.take 2).map (fun c => (2141978625-1+2*2^9*c.k,97367330126809+c.lower,97367708876435+c.upper)) = pointBounds16312 := by
 decide +kernel
def cuts16313 : List PrefixCut := [⟨59,366997183,366997419⟩,
⟨125,786278702,786279203⟩,
⟨128,806381806,806382319⟩]
theorem checked16313 : checkPrefixCuts (2^48) 2142109697 9 Manual.Count131072.C016313.packed 128 cuts16313 = true := by
 decide +kernel
def pointBounds16313 : List (Nat × Nat × Nat) := [(2142170112,97368505394953,97368884145327),(2142237696,97368924676472,97369303427111)]
theorem point_links_checked16313 : (cuts16313.take 2).map (fun c => (2142109697-1+2*2^9*c.k,97368138397770+c.lower,97368517147908+c.upper)) = pointBounds16313 := by
 decide +kernel
def cuts16314 : List PrefixCut := [⟨63,391150260,391150512⟩,
⟨128,797266696,797267205⟩]
theorem checked16314 : checkPrefixCuts (2^48) 2142240769 9 Manual.Count131072.C016314.packed 128 cuts16314 = true := by
 decide +kernel
def pointBounds16314 : List (Nat × Nat × Nat) := [(2142305280,97369335929836,97369714680739)]
theorem point_links_checked16314 : (cuts16314.take 1).map (fun c => (2142240769-1+2*2^9*c.k,97368944779576+c.lower,97369323530227+c.upper)) = pointBounds16314 := by
 decide +kernel
def cuts16315 : List PrefixCut := [⟨1,6963388,6963392⟩,
⟨67,409125390,409125650⟩,
⟨128,796692232,796692743⟩]
theorem checked16315 : checkPrefixCuts (2^48) 2142371841 9 Manual.Count131072.C016315.packed 128 cuts16315 = true := by
 decide +kernel
def pointBounds16315 : List (Nat × Nat × Nat) := [(2142372864,97369749009660,97370127760824),(2142440448,97370151171662,97370529923082)]
theorem point_links_checked16315 : (cuts16315.take 2).map (fun c => (2142371841-1+2*2^9*c.k,97369742046272+c.lower,97370120797432+c.upper)) = pointBounds16315 := by
 decide +kernel
def cuts16316 : List PrefixCut := [⟨5,29822468,29822487⟩,
⟨71,440235725,440236011⟩,
⟨128,803737710,803738226⟩]
theorem checked16316 : checkPrefixCuts (2^48) 2142502913 9 Manual.Count131072.C016316.packed 128 cuts16316 = true := by
 decide +kernel
def pointBounds16316 : List (Nat × Nat × Nat) := [(2142508032,97370568560972,97370947312662),(2142575616,97370978974229,97371357726186)]
theorem point_links_checked16316 : (cuts16316.take 2).map (fun c => (2142502913-1+2*2^9*c.k,97370538738504+c.lower,97370917490175+c.upper)) = pointBounds16316 := by
 decide +kernel
def cuts16317 : List PrefixCut := [⟨9,60298075,60298113⟩,
⟨75,468583548,468583847⟩,
⟨128,805002275,805002788⟩]
theorem checked16317 : checkPrefixCuts (2^48) 2142633985 9 Manual.Count131072.C016317.packed 128 cuts16317 = true := by
 decide +kernel
def pointBounds16317 : List (Nat × Nat × Nat) := [(2142643200,97371402774289,97371781526514),(2142710784,97371811059762,97372189812248)]
theorem point_links_checked16317 : (cuts16317.take 2).map (fun c => (2142633985-1+2*2^9*c.k,97371342476214+c.lower,97371721228401+c.upper)) = pointBounds16317 := by
 decide +kernel
def cuts16318 : List PrefixCut := [⟨13,81049238,81049287⟩,
⟨79,483660666,483660971⟩,
⟨128,791948698,791949205⟩]
theorem checked16318 : checkPrefixCuts (2^48) 2142765057 9 Manual.Count131072.C016318.packed 128 cuts16318 = true := by
 decide +kernel
def pointBounds16318 : List (Nat × Nat × Nat) := [(2142778368,97372228527727,97372607280476),(2142845952,97372631139155,97373009892160)]
theorem point_links_checked16318 : (cuts16318.take 2).map (fun c => (2142765057-1+2*2^9*c.k,97372147478489+c.lower,97372526231189+c.upper)) = pointBounds16318 := by
 decide +kernel
def cuts16319 : List PrefixCut := [⟨17,109022179,109022245⟩,
⟨83,516730731,516731061⟩,
⟨128,799518540,799519051⟩]
theorem checked16319 : checkPrefixCuts (2^48) 2142896129 9 Manual.Count131072.C016319.packed 128 cuts16319 = true := by
 decide +kernel
def pointBounds16319 : List (Nat × Nat × Nat) := [(2142913536,97373048449366,97373427202639),(2142981120,97373456157918,97373834911455)]
theorem point_links_checked16319 : (cuts16319.take 2).map (fun c => (2142896129-1+2*2^9*c.k,97372939427187+c.lower,97373318180394+c.upper)) = pointBounds16319 := by
 decide +kernel
def cuts16320 : List PrefixCut := [⟨21,132657318,132657403⟩,
⟨87,548483449,548483800⟩,
⟨128,804460753,804461271⟩]
theorem checked16320 : checkPrefixCuts (2^48) 2143027201 9 Manual.Count131072.C016320.packed 128 cuts16320 = true := by
 decide +kernel
def pointBounds16320 : List (Nat × Nat × Nat) := [(2143048704,97373871603045,97374250356848),(2143116288,97374287429176,97374666183245)]
theorem point_links_checked16320 : (cuts16320.take 2).map (fun c => (2143027201-1+2*2^9*c.k,97373738945727+c.lower,97374117699445+c.upper)) = pointBounds16320 := by
 decide +kernel
def cuts16321 : List PrefixCut := [⟨25,161148955,161149055⟩,
⟨91,582989985,582990356⟩,
⟨128,812291517,812292030⟩]
theorem checked16321 : checkPrefixCuts (2^48) 2143158273 9 Manual.Count131072.C016321.packed 128 cuts16321 = true := by
 decide +kernel
def pointBounds16321 : List (Nat × Nat × Nat) := [(2143183872,97374704555435,97375083309771),(2143251456,97375126396465,97375505151072)]
theorem point_links_checked16321 : (cuts16321.take 2).map (fun c => (2143158273-1+2*2^9*c.k,97374543406480+c.lower,97374922160716+c.upper)) = pointBounds16321 := by
 decide +kernel
def cuts16322 : List PrefixCut := [⟨29,179918742,179918862⟩,
⟨95,602258610,602258998⟩,
⟨128,802129863,802130378⟩]
theorem checked16322 : checkPrefixCuts (2^48) 2143289345 9 Manual.Count131072.C016322.packed 128 cuts16322 = true := by
 decide +kernel
def pointBounds16322 : List (Nat × Nat × Nat) := [(2143319040,97375535616739,97375914371608),(2143386624,97375957956607,97376336711744)]
theorem point_links_checked16322 : (cuts16322.take 2).map (fun c => (2143289345-1+2*2^9*c.k,97375355697997+c.lower,97375734452746+c.upper)) = pointBounds16322 := by
 decide +kernel
def cuts16323 : List PrefixCut := [⟨33,202494508,202494640⟩,
⟨99,616928686,616929076⟩,
⟨128,799979455,799979964⟩]
theorem checked16323 : checkPrefixCuts (2^48) 2143420417 9 Manual.Count131072.C016323.packed 128 cuts16323 = true := by
 decide +kernel
def pointBounds16323 : List (Nat × Nat × Nat) := [(2143454208,97376360322368,97376739077764),(2143521792,97376774756546,97377153512200)]
theorem point_links_checked16323 : (cuts16323.take 2).map (fun c => (2143420417-1+2*2^9*c.k,97376157827860+c.lower,97376536583124+c.upper)) = pointBounds16323 := by
 decide +kernel
def cuts16324 : List PrefixCut := [⟨37,229269415,229269557⟩,
⟨103,634223393,634223790⟩,
⟨128,794809585,794810082⟩]
theorem checked16324 : checkPrefixCuts (2^48) 2143551489 9 Manual.Count131072.C016324.packed 128 cuts16324 = true := by
 decide +kernel
def pointBounds16324 : List (Nat × Nat × Nat) := [(2143589376,97377187076730,97377565832645),(2143656960,97377592030708,97377970786878)]
theorem point_links_checked16324 : (cuts16324.take 2).map (fun c => (2143551489-1+2*2^9*c.k,97376957807315+c.lower,97377336563088+c.upper)) = pointBounds16324 := by
 decide +kernel
def cuts16325 : List PrefixCut := [⟨41,260242697,260242861⟩,
⟨107,673836808,673837231⟩,
⟨128,808678821,808679330⟩]
theorem checked16325 : checkPrefixCuts (2^48) 2143682561 9 Manual.Count131072.C016325.packed 128 cuts16325 = true := by
 decide +kernel
def pointBounds16325 : List (Nat × Nat × Nat) := [(2143724544,97378012859597,97378391616031),(2143792128,97378426453708,97378805210401)]
theorem point_links_checked16325 : (cuts16325.take 2).map (fun c => (2143682561-1+2*2^9*c.k,97377752616900+c.lower,97378131373170+c.upper)) = pointBounds16325 := by
 decide +kernel
def cuts16326 : List PrefixCut := [⟨45,276638443,276638622⟩,
⟨111,694145238,694145683⟩,
⟨128,799438898,799439408⟩]
theorem checked16326 : checkPrefixCuts (2^48) 2143813633 9 Manual.Count131072.C016326.packed 128 cuts16326 = true := by
 decide +kernel
def pointBounds16326 : List (Nat × Nat × Nat) := [(2143859712,97378837934164,97379216691122),(2143927296,97379255440959,97379634198183)]
theorem point_links_checked16326 : (cuts16326.take 2).map (fun c => (2143813633-1+2*2^9*c.k,97378561295721+c.lower,97378940052500+c.upper)) = pointBounds16326 := by
 decide +kernel
def cuts16327 : List PrefixCut := [⟨49,302616020,302616217⟩,
⟨115,723247311,723247774⟩,
⟨128,804247499,804248016⟩]
theorem checked16327 : checkPrefixCuts (2^48) 2143944705 9 Manual.Count131072.C016327.packed 128 cuts16327 = true := by
 decide +kernel
def pointBounds16327 : List (Nat × Nat × Nat) := [(2143994880,97379663350639,97380042108125),(2144062464,97380083981930,97380462739682)]
theorem point_links_checked16327 : (cuts16327.take 2).map (fun c => (2143944705-1+2*2^9*c.k,97379360734619+c.lower,97379739491908+c.upper)) = pointBounds16327 := by
 decide +kernel
def cuts16328 : List PrefixCut := [⟨53,331478499,331478708⟩,
⟨119,740399725,740400198⟩,
⟨128,795009098,795009607⟩]
theorem checked16328 : checkPrefixCuts (2^48) 2144075777 9 Manual.Count131072.C016328.packed 128 cuts16328 = true := by
 decide +kernel
def pointBounds16328 : List (Nat × Nat × Nat) := [(2144130048,97380496460617,97380875218632),(2144197632,97380905381843,97381284140122)]
theorem point_links_checked16328 : (cuts16328.take 2).map (fun c => (2144075777-1+2*2^9*c.k,97380164982118+c.lower,97380543739924+c.upper)) = pointBounds16328 := by
 decide +kernel
def cuts16329 : List PrefixCut := [⟨57,357580739,357580965⟩,
⟨123,772777025,772777516⟩,
⟨128,803624156,803624667⟩]
theorem checked16329 : checkPrefixCuts (2^48) 2144206849 9 Manual.Count131072.C016329.packed 128 cuts16329 = true := by
 decide +kernel
def pointBounds16329 : List (Nat × Nat × Nat) := [(2144265216,97381317571955,97381696330496),(2144332800,97381732768241,97382111527047)]
theorem point_links_checked16329 : (cuts16329.take 2).map (fun c => (2144206849-1+2*2^9*c.k,97380959991216+c.lower,97381338749531+c.upper)) = pointBounds16329 := by
 decide +kernel
def cuts16330 : List PrefixCut := [⟨61,381317085,381317330⟩,
⟨127,795174701,795175212⟩,
⟨128,802262538,802263054⟩]
theorem checked16330 : checkPrefixCuts (2^48) 2144337921 9 Manual.Count131072.C016330.packed 128 cuts16330 = true := by
 decide +kernel
def pointBounds16330 : List (Nat × Nat × Nat) := [(2144400384,97382144932457,97382523691528),(2144467968,97382558790073,97382937549410)]
theorem point_links_checked16330 : (cuts16330.take 2).map (fun c => (2144337921-1+2*2^9*c.k,97381763615372+c.lower,97382142374198+c.upper)) = pointBounds16330 := by
 decide +kernel
def cuts16331 : List PrefixCut := [⟨65,408987979,408988236⟩,
⟨128,805232254,805232768⟩]
theorem checked16331 : checkPrefixCuts (2^48) 2144468993 9 Manual.Count131072.C016331.packed 128 cuts16331 = true := by
 decide +kernel
def pointBounds16331 : List (Nat × Nat × Nat) := [(2144535552,97382974865889,97383353625488)]
theorem point_links_checked16331 : (cuts16331.take 1).map (fun c => (2144468993-1+2*2^9*c.k,97382565877910+c.lower,97382944637252+c.upper)) = pointBounds16331 := by
 decide +kernel
def cuts16332 : List PrefixCut := [⟨3,18899726,18899737⟩,
⟨69,426812033,426812301⟩,
⟨128,795208376,795208876⟩]
theorem checked16332 : checkPrefixCuts (2^48) 2144600065 9 Manual.Count131072.C016332.packed 128 cuts16332 = true := by
 decide +kernel
def pointBounds16332 : List (Nat × Nat × Nat) := [(2144603136,97383390009890,97383768769757),(2144670720,97383797922197,97384176682321)]
theorem point_links_checked16332 : (cuts16332.take 2).map (fun c => (2144600065-1+2*2^9*c.k,97383371110164+c.lower,97383749870020+c.upper)) = pointBounds16332 := by
 decide +kernel
def cuts16333 : List PrefixCut := [⟨7,43440425,43440452⟩,
⟨73,458545178,458545470⟩,
⟨128,804477696,804478202⟩]
theorem checked16333 : checkPrefixCuts (2^48) 2144731137 9 Manual.Count131072.C016333.packed 128 cuts16333 = true := by
 decide +kernel
def pointBounds16333 : List (Nat × Nat × Nat) := [(2144738304,97384209758965,97384588519348),(2144805888,97384624863718,97385003624366)]
theorem point_links_checked16333 : (cuts16333.take 2).map (fun c => (2144731137-1+2*2^9*c.k,97384166318540+c.lower,97384545078896+c.upper)) = pointBounds16333 := by
 decide +kernel
def cuts16334 : List PrefixCut := [⟨11,69159160,69159205⟩,
⟨77,487518479,487518787⟩,
⟨128,797342354,797342863⟩]
theorem checked16334 : checkPrefixCuts (2^48) 2144862209 9 Manual.Count131072.C016334.packed 128 cuts16334 = true := by
 decide +kernel
def pointBounds16334 : List (Nat × Nat × Nat) := [(2144873472,97385039955396,97385418716303),(2144941056,97385458314715,97385837075885)]
theorem point_links_checked16334 : (cuts16334.take 2).map (fun c => (2144862209-1+2*2^9*c.k,97384970796236+c.lower,97385349557098+c.upper)) = pointBounds16334 := by
 decide +kernel
def cuts16335 : List PrefixCut := [⟨15,94743481,94743542⟩,
⟨81,508352490,508352817⟩,
⟨128,801754946,801755460⟩]
theorem checked16335 : checkPrefixCuts (2^48) 2144993281 9 Manual.Count131072.C016335.packed 128 cuts16335 = true := by
 decide +kernel
def pointBounds16335 : List (Nat × Nat × Nat) := [(2145008640,97385862882071,97386241643503),(2145076224,97386276491080,97386655252778)]
theorem point_links_checked16335 : (cuts16335.take 2).map (fun c => (2144993281-1+2*2^9*c.k,97385768138590+c.lower,97386146899961+c.upper)) = pointBounds16335 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000197
