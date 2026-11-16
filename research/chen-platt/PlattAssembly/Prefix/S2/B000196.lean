import PlattAssemblyKernel
import PlattCertificates.Count131072.C016272
import PlattCertificates.Count131072.C016273
import PlattCertificates.Count131072.C016274
import PlattCertificates.Count131072.C016275
import PlattCertificates.Count131072.C016276
import PlattCertificates.Count131072.C016277
import PlattCertificates.Count131072.C016278
import PlattCertificates.Count131072.C016279
import PlattCertificates.Count131072.C016280
import PlattCertificates.Count131072.C016281
import PlattCertificates.Count131072.C016282
import PlattCertificates.Count131072.C016283
import PlattCertificates.Count131072.C016284
import PlattCertificates.Count131072.C016285
import PlattCertificates.Count131072.C016286
import PlattCertificates.Count131072.C016287
import PlattCertificates.Count131072.C016288
import PlattCertificates.Count131072.C016289
import PlattCertificates.Count131072.C016290
import PlattCertificates.Count131072.C016291
import PlattCertificates.Count131072.C016292
import PlattCertificates.Count131072.C016293
import PlattCertificates.Count131072.C016294
import PlattCertificates.Count131072.C016295
import PlattCertificates.Count131072.C016296
import PlattCertificates.Count131072.C016297
import PlattCertificates.Count131072.C016298
import PlattCertificates.Count131072.C016299
import PlattCertificates.Count131072.C016300
import PlattCertificates.Count131072.C016301
import PlattCertificates.Count131072.C016302
import PlattCertificates.Count131072.C016303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000196
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16272 : List PrefixCut := [⟨27,174279330,174279439⟩,
⟨93,593436165,593436542⟩,
⟨128,809463983,809464496⟩]
theorem checked16272 : checkPrefixCuts (2^48) 2136735745 9 Manual.Count131072.C016272.packed 128 cuts16272 = true := by
 decide +kernel
def pointBounds16272 : List (Nat × Nat × Nat) := [(2136763392,97335382167011,97335760896259),(2136830976,97335801323846,97336180053362)]
theorem point_links_checked16272 : (cuts16272.take 2).map (fun c => (2136735745-1+2*2^9*c.k,97335207887681+c.lower,97335586616820+c.upper)) = pointBounds16272 := by
 decide +kernel
def cuts16273 : List PrefixCut := [⟨31,195344021,195344149⟩,
⟨97,607756666,607757056⟩,
⟨128,808228549,808229064⟩]
theorem checked16273 : checkPrefixCuts (2^48) 2136866817 9 Manual.Count131072.C016273.packed 128 cuts16273 = true := by
 decide +kernel
def pointBounds16273 : List (Nat × Nat × Nat) := [(2136898560,97336212695685,97336591425465),(2136966144,97336625108330,97337003838372)]
theorem point_links_checked16273 : (cuts16273.take 2).map (fun c => (2136866817-1+2*2^9*c.k,97336017351664+c.lower,97336396081316+c.upper)) = pointBounds16273 := by
 decide +kernel
def cuts16274 : List PrefixCut := [⟨35,221147812,221147956⟩,
⟨101,634061157,634061559⟩,
⟨128,806861896,806862408⟩]
theorem checked16274 : checkPrefixCuts (2^48) 2136997889 9 Manual.Count131072.C016274.packed 128 cuts16274 = true := by
 decide +kernel
def pointBounds16274 : List (Nat × Nat × Nat) := [(2137033728,97337046728025,97337425458336),(2137101312,97337459641370,97337838371939)]
theorem point_links_checked16274 : (cuts16274.take 2).map (fun c => (2136997889-1+2*2^9*c.k,97336825580213+c.lower,97337204310380+c.upper)) = pointBounds16274 := by
 decide +kernel
def cuts16275 : List PrefixCut := [⟨39,247606868,247607030⟩,
⟨105,654435781,654436203⟩,
⟨128,801544312,801544828⟩]
theorem checked16275 : checkPrefixCuts (2^48) 2137128961 9 Manual.Count131072.C016275.packed 128 cuts16275 = true := by
 decide +kernel
def pointBounds16275 : List (Nat × Nat × Nat) := [(2137168896,97337880048977,97338258779818),(2137236480,97338286877890,97338665608991)]
theorem point_links_checked16275 : (cuts16275.take 2).map (fun c => (2137128961-1+2*2^9*c.k,97337632442109+c.lower,97338011172788+c.upper)) = pointBounds16275 := by
 decide +kernel
def cuts16276 : List PrefixCut := [⟨43,268531350,268531523⟩,
⟨109,675334549,675334985⟩,
⟨128,796622396,796622908⟩]
theorem checked16276 : checkPrefixCuts (2^48) 2137260033 9 Manual.Count131072.C016276.packed 128 cuts16276 = true := by
 decide +kernel
def pointBounds16276 : List (Nat × Nat × Nat) := [(2137304064,97338702517771,97339081249139),(2137371648,97339109320970,97339488052601)]
theorem point_links_checked16276 : (cuts16276.take 2).map (fun c => (2137260033-1+2*2^9*c.k,97338433986421+c.lower,97338812717616+c.upper)) = pointBounds16276 := by
 decide +kernel
def cuts16277 : List PrefixCut := [⟨47,297091263,297091450⟩,
⟨113,708872769,708873215⟩,
⟨128,801709471,801709974⟩]
theorem checked16277 : checkPrefixCuts (2^48) 2137391105 9 Manual.Count131072.C016277.packed 128 cuts16277 = true := by
 decide +kernel
def pointBounds16277 : List (Nat × Nat × Nat) := [(2137439232,97339527700080,97339906431974),(2137506816,97339939481586,97340318213739)]
theorem point_links_checked16277 : (cuts16277.take 2).map (fun c => (2137391105-1+2*2^9*c.k,97339230608817+c.lower,97339609340524+c.upper)) = pointBounds16277 := by
 decide +kernel
def cuts16278 : List PrefixCut := [⟨51,325515911,325516117⟩,
⟨117,731214322,731214788⟩,
⟨128,799026980,799027489⟩]
theorem checked16278 : checkPrefixCuts (2^48) 2137522177 9 Manual.Count131072.C016278.packed 128 cuts16278 = true := by
 decide +kernel
def pointBounds16278 : List (Nat × Nat × Nat) := [(2137574400,97340357834199,97340736566615),(2137641984,97340763532610,97341142265286)]
theorem point_links_checked16278 : (cuts16278.take 2).map (fun c => (2137522177-1+2*2^9*c.k,97340032318288+c.lower,97340411050498+c.upper)) = pointBounds16278 := by
 decide +kernel
def cuts16279 : List PrefixCut := [⟨55,341164687,341164907⟩,
⟨121,754605880,754606366⟩,
⟨128,796739278,796739790⟩]
theorem checked16279 : checkPrefixCuts (2^48) 2137653249 9 Manual.Count131072.C016279.packed 128 cuts16279 = true := by
 decide +kernel
def pointBounds16279 : List (Nat × Nat × Nat) := [(2137709568,97341172509955,97341551242894),(2137777152,97341585951148,97341964684353)]
theorem point_links_checked16279 : (cuts16279.take 2).map (fun c => (2137653249-1+2*2^9*c.k,97340831345268+c.lower,97341210077987+c.upper)) = pointBounds16279 := by
 decide +kernel
def cuts16280 : List PrefixCut := [⟨59,369056393,369056626⟩,
⟨125,776678374,776678871⟩,
⟨128,797480444,797480954⟩]
theorem checked16280 : checkPrefixCuts (2^48) 2137784321 9 Manual.Count131072.C016280.packed 128 cuts16280 = true := by
 decide +kernel
def pointBounds16280 : List (Nat × Nat × Nat) := [(2137844736,97341997140939,97342375874403),(2137912320,97342404762920,97342783496648)]
theorem point_links_checked16280 : (cuts16280.take 2).map (fun c => (2137784321-1+2*2^9*c.k,97341628084546+c.lower,97342006817777+c.upper)) = pointBounds16280 := by
 decide +kernel
def cuts16281 : List PrefixCut := [⟨63,401289335,401289587⟩,
⟨128,811913558,811914075⟩]
theorem checked16281 : checkPrefixCuts (2^48) 2137915393 9 Manual.Count131072.C016281.packed 128 cuts16281 = true := by
 decide +kernel
def pointBounds16281 : List (Nat × Nat × Nat) := [(2137979904,97342826854325,97343205588318)]
theorem point_links_checked16281 : (cuts16281.take 1).map (fun c => (2137915393-1+2*2^9*c.k,97342425564990+c.lower,97342804298731+c.upper)) = pointBounds16281 := by
 decide +kernel
def cuts16282 : List PrefixCut := [⟨1,6450873,6450877⟩,
⟨67,419826748,419827017⟩,
⟨128,799883996,799884507⟩]
theorem checked16282 : checkPrefixCuts (2^48) 2138046465 9 Manual.Count131072.C016282.packed 128 cuts16282 = true := by
 decide +kernel
def pointBounds16282 : List (Nat × Nat × Nat) := [(2138047488,97343243929421,97343622663683),(2138115072,97343657305296,97344036039823)]
theorem point_links_checked16282 : (cuts16282.take 2).map (fun c => (2138046465-1+2*2^9*c.k,97343237478548+c.lower,97343616212806+c.upper)) = pointBounds16282 := by
 decide +kernel
def cuts16283 : List PrefixCut := [⟨5,33173854,33173875⟩,
⟨71,449288039,449288322⟩,
⟨128,803389273,803389780⟩]
theorem checked16283 : checkPrefixCuts (2^48) 2138177537 9 Manual.Count131072.C016283.packed 128 cuts16283 = true := by
 decide +kernel
def pointBounds16283 : List (Nat × Nat × Nat) := [(2138182656,97344070536398,97344449271188),(2138250240,97344486650583,97344865385635)]
theorem point_links_checked16283 : (cuts16283.take 2).map (fun c => (2138177537-1+2*2^9*c.k,97344037362544+c.lower,97344416097313+c.upper)) = pointBounds16283 := by
 decide +kernel
def cuts16284 : List PrefixCut := [⟨9,59761876,59761914⟩,
⟨75,476639595,476639902⟩,
⟨128,810316440,810316963⟩]
theorem checked16284 : checkPrefixCuts (2^48) 2138308609 9 Manual.Count131072.C016284.packed 128 cuts16284 = true := by
 decide +kernel
def pointBounds16284 : List (Nat × Nat × Nat) := [(2138317824,97344900513693,97345279249007),(2138385408,97345317391412,97345696126995)]
theorem point_links_checked16284 : (cuts16284.take 2).map (fun c => (2138308609-1+2*2^9*c.k,97344840751817+c.lower,97345219487093+c.upper)) = pointBounds16284 := by
 decide +kernel
def cuts16285 : List PrefixCut := [⟨13,79765282,79765334⟩,
⟨79,493984072,493984391⟩,
⟨128,800394864,800395382⟩]
theorem checked16285 : checkPrefixCuts (2^48) 2138439681 9 Manual.Count131072.C016285.packed 128 cuts16285 = true := by
 decide +kernel
def pointBounds16285 : List (Nat × Nat × Nat) := [(2138452992,97345730833539,97346109569390),(2138520576,97346145052329,97346523788447)]
theorem point_links_checked16285 : (cuts16285.take 2).map (fun c => (2138439681-1+2*2^9*c.k,97345651068257+c.lower,97346029804056+c.upper)) = pointBounds16285 := by
 decide +kernel
def cuts16286 : List PrefixCut := [⟨17,102135334,102135401⟩,
⟨83,516064810,516065144⟩,
⟨128,794028480,794028995⟩]
theorem checked16286 : checkPrefixCuts (2^48) 2138570753 9 Manual.Count131072.C016286.packed 128 cuts16286 = true := by
 decide +kernel
def pointBounds16286 : List (Nat × Nat × Nat) := [(2138588160,97346553598455,97346932334839),(2138655744,97346967527931,97347346264582)]
theorem point_links_checked16286 : (cuts16286.take 2).map (fun c => (2138570753-1+2*2^9*c.k,97346451463121+c.lower,97346830199438+c.upper)) = pointBounds16286 := by
 decide +kernel
def cuts16287 : List PrefixCut := [⟨21,123844555,123844639⟩,
⟨87,536431812,536432161⟩,
⟨128,796480137,796480649⟩]
theorem checked16287 : checkPrefixCuts (2^48) 2138701825 9 Manual.Count131072.C016287.packed 128 cuts16287 = true := by
 decide +kernel
def pointBounds16287 : List (Nat × Nat × Nat) := [(2138723328,97347369336156,97347748073072),(2138790912,97347781923413,97348160660594)]
theorem point_links_checked16287 : (cuts16287.take 2).map (fun c => (2138701825-1+2*2^9*c.k,97347245491601+c.lower,97347624228433+c.upper)) = pointBounds16287 := by
 decide +kernel
def cuts16288 : List PrefixCut := [⟨25,150815105,150815203⟩,
⟨91,560349462,560349815⟩,
⟨128,798668367,798668870⟩]
theorem checked16288 : checkPrefixCuts (2^48) 2138832897 9 Manual.Count131072.C016288.packed 128 cuts16288 = true := by
 decide +kernel
def pointBounds16288 : List (Nat × Nat × Nat) := [(2138858496,97348192786843,97348571524285),(2138926080,97348602321200,97348981058897)]
theorem point_links_checked16288 : (cuts16288.take 2).map (fun c => (2138832897-1+2*2^9*c.k,97348041971738+c.lower,97348420709082+c.upper)) = pointBounds16288 := by
 decide +kernel
def cuts16289 : List PrefixCut := [⟨29,182388050,182388165⟩,
⟨95,591896498,591896877⟩,
⟨128,802304116,802304633⟩]
theorem checked16289 : checkPrefixCuts (2^48) 2138963969 9 Manual.Count131072.C016289.packed 128 cuts16289 = true := by
 decide +kernel
def pointBounds16289 : List (Nat × Nat × Nat) := [(2138993664,97349023028155,97349401766117),(2139061248,97349432536603,97349811274829)]
theorem point_links_checked16289 : (cuts16289.take 2).map (fun c => (2138963969-1+2*2^9*c.k,97348840640105+c.lower,97349219377952+c.upper)) = pointBounds16289 := by
 decide +kernel
def cuts16290 : List PrefixCut := [⟨33,199877488,199877614⟩,
⟨99,617912908,617913296⟩,
⟨128,803833778,803834286⟩]
theorem checked16290 : checkPrefixCuts (2^48) 2139095041 9 Manual.Count131072.C016290.packed 128 cuts16290 = true := by
 decide +kernel
def pointBounds16290 : List (Nat × Nat × Nat) := [(2139128832,97349842821709,97350221560199),(2139196416,97350260857129,97350639595881)]
theorem point_links_checked16290 : (cuts16290.take 2).map (fun c => (2139095041-1+2*2^9*c.k,97349642944221+c.lower,97350021682585+c.upper)) = pointBounds16290 := by
 decide +kernel
def cuts16291 : List PrefixCut := [⟨37,231575048,231575194⟩,
⟨103,649978816,649979227⟩,
⟨128,802863899,802864409⟩]
theorem checked16291 : checkPrefixCuts (2^48) 2139226113 9 Manual.Count131072.C016291.packed 128 cuts16291 = true := by
 decide +kernel
def pointBounds16291 : List (Nat × Nat × Nat) := [(2139264000,97350678353047,97351057092065),(2139331584,97351096756815,97351475496098)]
theorem point_links_checked16291 : (cuts16291.take 2).map (fun c => (2139226113-1+2*2^9*c.k,97350446777999+c.lower,97350825516871+c.upper)) = pointBounds16291 := by
 decide +kernel
def cuts16292 : List PrefixCut := [⟨41,254585154,254585320⟩,
⟨107,663752830,663753254⟩,
⟨128,796894035,796894542⟩]
theorem checked16292 : checkPrefixCuts (2^48) 2139357185 9 Manual.Count131072.C016292.packed 128 cuts16292 = true := by
 decide +kernel
def pointBounds16292 : List (Nat × Nat × Nat) := [(2139399168,97351504227052,97351882966600),(2139466752,97351913394728,97352292134534)]
theorem point_links_checked16292 : (cuts16292.take 2).map (fun c => (2139357185-1+2*2^9*c.k,97351249641898+c.lower,97351628381280+c.upper)) = pointBounds16292 := by
 decide +kernel
def cuts16293 : List PrefixCut := [⟨45,280223574,280223752⟩,
⟨111,693969957,693970397⟩,
⟨128,802107554,802108062⟩]
theorem checked16293 : checkPrefixCuts (2^48) 2139488257 9 Manual.Count131072.C016293.packed 128 cuts16293 = true := by
 decide +kernel
def pointBounds16293 : List (Nat × Nat × Nat) := [(2139534336,97352326759507,97352705499574),(2139601920,97352740505890,97353119246219)]
theorem point_links_checked16293 : (cuts16293.take 2).map (fun c => (2139488257-1+2*2^9*c.k,97352046535933+c.lower,97352425275822+c.upper)) = pointBounds16293 := by
 decide +kernel
def cuts16294 : List PrefixCut := [⟨49,317698505,317698710⟩,
⟨115,724972873,724973339⟩,
⟨128,809425456,809425972⟩]
theorem checked16294 : checkPrefixCuts (2^48) 2139619329 9 Manual.Count131072.C016294.packed 128 cuts16294 = true := by
 decide +kernel
def pointBounds16294 : List (Nat × Nat × Nat) := [(2139669504,97353166341992,97353545082594),(2139737088,97353573616360,97353952357223)]
theorem point_links_checked16294 : (cuts16294.take 2).map (fun c => (2139619329-1+2*2^9*c.k,97352848643487+c.lower,97353227383884+c.upper)) = pointBounds16294 := by
 decide +kernel
def cuts16295 : List PrefixCut := [⟨53,338462686,338462903⟩,
⟨119,756366114,756366600⟩,
⟨128,809507424,809507945⟩]
theorem checked16295 : checkPrefixCuts (2^48) 2139750401 9 Manual.Count131072.C016295.packed 128 cuts16295 = true := by
 decide +kernel
def pointBounds16295 : List (Nat × Nat × Nat) := [(2139804672,97353996531629,97354375272759),(2139872256,97354414435057,97354793176456)]
theorem point_links_checked16295 : (cuts16295.take 2).map (fun c => (2139750401-1+2*2^9*c.k,97353658068943+c.lower,97354036809856+c.upper)) = pointBounds16295 := by
 decide +kernel
def cuts16296 : List PrefixCut := [⟨57,357382775,357383001⟩,
⟨123,776969699,776970196⟩,
⟨128,807616119,807616637⟩]
theorem checked16296 : checkPrefixCuts (2^48) 2139881473 9 Manual.Count131072.C016296.packed 128 cuts16296 = true := by
 decide +kernel
def pointBounds16296 : List (Nat × Nat × Nat) := [(2139939840,97354824959142,97355203700802),(2140007424,97355244546066,97355623287997)]
theorem point_links_checked16296 : (cuts16296.take 2).map (fun c => (2139881473-1+2*2^9*c.k,97354467576367+c.lower,97354846317801+c.upper)) = pointBounds16296 := by
 decide +kernel
def cuts16297 : List PrefixCut := [⟨61,390242489,390242739⟩,
⟨127,798360292,798360801⟩,
⟨128,804541804,804542317⟩]
theorem checked16297 : checkPrefixCuts (2^48) 2140012545 9 Manual.Count131072.C016297.packed 128 cuts16297 = true := by
 decide +kernel
def pointBounds16297 : List (Nat × Nat × Nat) := [(2140075008,97355665434975,97356044177177),(2140142592,97356073552778,97356452295239)]
theorem point_links_checked16297 : (cuts16297.take 2).map (fun c => (2140012545-1+2*2^9*c.k,97355275192486+c.lower,97355653934438+c.upper)) = pointBounds16297 := by
 decide +kernel
def cuts16298 : List PrefixCut := [⟨65,405079929,405080189⟩,
⟨128,800415389,800415903⟩]
theorem checked16298 : checkPrefixCuts (2^48) 2140143617 9 Manual.Count131072.C016298.packed 128 cuts16298 = true := by
 decide +kernel
def pointBounds16298 : List (Nat × Nat × Nat) := [(2140210176,97356484814219,97356863556944)]
theorem point_links_checked16298 : (cuts16298.take 1).map (fun c => (2140143617-1+2*2^9*c.k,97356079734290+c.lower,97356458476755+c.upper)) = pointBounds16298 := by
 decide +kernel
def cuts16299 : List PrefixCut := [⟨3,18148841,18148852⟩,
⟨69,426885597,426885869⟩,
⟨128,803522330,803522842⟩]
theorem checked16299 : checkPrefixCuts (2^48) 2140274689 9 Manual.Count131072.C016299.packed 128 cuts16299 = true := by
 decide +kernel
def pointBounds16299 : List (Nat × Nat × Nat) := [(2140277760,97356898298520,97357277041510),(2140345344,97357307035276,97357685778527)]
theorem point_links_checked16299 : (cuts16299.take 2).map (fun c => (2140274689-1+2*2^9*c.k,97356880149679+c.lower,97357258892658+c.upper)) = pointBounds16299 := by
 decide +kernel
def cuts16300 : List PrefixCut := [⟨7,43922726,43922755⟩,
⟨73,455132246,455132536⟩,
⟨128,802815737,802816245⟩]
theorem checked16300 : checkPrefixCuts (2^48) 2140405761 9 Manual.Count131072.C016300.packed 128 cuts16300 = true := by
 decide +kernel
def pointBounds16300 : List (Nat × Nat × Nat) := [(2140412928,97357727594735,97358106338255),(2140480512,97358138804255,97358517548036)]
theorem point_links_checked16300 : (cuts16300.take 2).map (fun c => (2140405761-1+2*2^9*c.k,97357683672009+c.lower,97358062415500+c.upper)) = pointBounds16300 := by
 decide +kernel
def cuts16301 : List PrefixCut := [⟨11,69824899,69824945⟩,
⟨77,480350915,480351225⟩,
⟨128,801320196,801320713⟩]
theorem checked16301 : checkPrefixCuts (2^48) 2140536833 9 Manual.Count131072.C016301.packed 128 cuts16301 = true := by
 decide +kernel
def pointBounds16301 : List (Nat × Nat × Nat) := [(2140548096,97358556312645,97358935056690),(2140615680,97358966838661,97359345582970)]
theorem point_links_checked16301 : (cuts16301.take 2).map (fun c => (2140536833-1+2*2^9*c.k,97358486487746+c.lower,97358865231745+c.upper)) = pointBounds16301 := by
 decide +kernel
def cuts16302 : List PrefixCut := [⟨15,96775773,96775833⟩,
⟨81,514507648,514507971⟩,
⟨128,815208574,815209089⟩]
theorem checked16302 : checkPrefixCuts (2^48) 2140667905 9 Manual.Count131072.C016302.packed 128 cuts16302 = true := by
 decide +kernel
def pointBounds16302 : List (Nat × Nat × Nat) := [(2140683264,97359384583715,97359763328291),(2140750848,97359802315590,97360181060429)]
theorem point_links_checked16302 : (cuts16302.take 2).map (fun c => (2140667905-1+2*2^9*c.k,97359287807942+c.lower,97359666552458+c.upper)) = pointBounds16302 := by
 decide +kernel
def cuts16303 : List PrefixCut := [⟨19,118989977,118990053⟩,
⟨85,536958424,536958765⟩,
⟨128,805823861,805824373⟩]
theorem checked16303 : checkPrefixCuts (2^48) 2140798977 9 Manual.Count131072.C016303.packed 128 cuts16303 = true := by
 decide +kernel
def pointBounds16303 : List (Nat × Nat × Nat) := [(2140818432,97360222006493,97360600751600),(2140886016,97360639974940,97361018720312)]
theorem point_links_checked16303 : (cuts16303.take 2).map (fun c => (2140798977-1+2*2^9*c.k,97360103016516+c.lower,97360481761547+c.upper)) = pointBounds16303 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000196
