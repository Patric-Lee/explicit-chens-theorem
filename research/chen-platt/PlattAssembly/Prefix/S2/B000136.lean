import PlattAssemblyKernel
import PlattCertificates.Count131072.C014352
import PlattCertificates.Count131072.C014353
import PlattCertificates.Count131072.C014354
import PlattCertificates.Count131072.C014355
import PlattCertificates.Count131072.C014356
import PlattCertificates.Count131072.C014357
import PlattCertificates.Count131072.C014358
import PlattCertificates.Count131072.C014359
import PlattCertificates.Count131072.C014360
import PlattCertificates.Count131072.C014361
import PlattCertificates.Count131072.C014362
import PlattCertificates.Count131072.C014363
import PlattCertificates.Count131072.C014364
import PlattCertificates.Count131072.C014365
import PlattCertificates.Count131072.C014366
import PlattCertificates.Count131072.C014367
import PlattCertificates.Count131072.C014368
import PlattCertificates.Count131072.C014369
import PlattCertificates.Count131072.C014370
import PlattCertificates.Count131072.C014371
import PlattCertificates.Count131072.C014372
import PlattCertificates.Count131072.C014373
import PlattCertificates.Count131072.C014374
import PlattCertificates.Count131072.C014375
import PlattCertificates.Count131072.C014376
import PlattCertificates.Count131072.C014377
import PlattCertificates.Count131072.C014378
import PlattCertificates.Count131072.C014379
import PlattCertificates.Count131072.C014380
import PlattCertificates.Count131072.C014381
import PlattCertificates.Count131072.C014382
import PlattCertificates.Count131072.C014383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000136
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14352 : List PrefixCut := [⟨26,191124949,191125080⟩,
⟨84,606662808,606663222⟩,
⟨128,917075812,917076438⟩]
theorem checked14352 : checkPrefixCuts (2^48) 1885077505 9 Manual.Count131072.C014352.packed 128 cuts14352 = true := by
 decide +kernel
def pointBounds14352 : List (Nat × Nat × Nat) := [(1885104128,95688719509396,95689097152368),(1885163520,95689135047255,95689512690510)]
theorem point_links_checked14352 : (cuts14352.take 2).map (fun c => (1885077505-1+2*2^9*c.k,95688528384447+c.lower,95688906027288+c.upper)) = pointBounds14352 := by
 decide +kernel
def cuts14353 : List PrefixCut := [⟨14,103469376,103469445⟩,
⟨72,512262499,512262849⟩,
⟨128,917609010,917609635⟩]
theorem checked14353 : checkPrefixCuts (2^48) 1885208577 9 Manual.Count131072.C014353.packed 128 cuts14353 = true := by
 decide +kernel
def pointBounds14353 : List (Nat × Nat × Nat) := [(1885222912,95689548929635,95689926573171),(1885282304,95689957722758,95690335366575)]
theorem point_links_checked14353 : (cuts14353.take 2).map (fun c => (1885208577-1+2*2^9*c.k,95689445460259+c.lower,95689823103726+c.upper)) = pointBounds14353 := by
 decide +kernel
def cuts14354 : List PrefixCut := [⟨2,15377546,15377557⟩,
⟨60,429519386,429519681⟩,
⟨118,842752504,842753082⟩,
⟨128,916947975,916948604⟩]
theorem checked14354 : checkPrefixCuts (2^48) 1885339649 9 Manual.Count131072.C014354.packed 128 cuts14354 = true := by
 decide +kernel
def pointBounds14354 : List (Nat × Nat × Nat) := [(1885341696,95690378446815,95690756090918),(1885401088,95690792588655,95691170233042),(1885460480,95691205821773,95691583466443)]
theorem point_links_checked14354 : (cuts14354.take 3).map (fun c => (1885339649-1+2*2^9*c.k,95690363069269+c.lower,95690740713361+c.upper)) = pointBounds14354 := by
 decide +kernel
def cuts14355 : List PrefixCut := [⟨48,340219022,340219249⟩,
⟨106,757605889,757606397⟩,
⟨128,912256652,912257267⟩]
theorem checked14355 : checkPrefixCuts (2^48) 1885470721 9 Manual.Count131072.C014355.packed 128 cuts14355 = true := by
 decide +kernel
def pointBounds14355 : List (Nat × Nat × Nat) := [(1885519872,95691620236266,95691997881214),(1885579264,95692037623133,95692415268362)]
theorem point_links_checked14355 : (cuts14355.take 2).map (fun c => (1885470721-1+2*2^9*c.k,95691280017244+c.lower,95691657661965+c.upper)) = pointBounds14355 := by
 decide +kernel
def cuts14356 : List PrefixCut := [⟨36,260782505,260782685⟩,
⟨94,682322710,682323176⟩,
⟨128,923090239,923090871⟩]
theorem checked14356 : checkPrefixCuts (2^48) 1885601793 9 Manual.Count131072.C014356.packed 128 cuts14356 = true := by
 decide +kernel
def pointBounds14356 : List (Nat × Nat × Nat) := [(1885638656,95692453056401,95692830701917),(1885698048,95692874596606,95693252242408)]
theorem point_links_checked14356 : (cuts14356.take 2).map (fun c => (1885601793-1+2*2^9*c.k,95692192273896+c.lower,95692569919232+c.upper)) = pointBounds14356 := by
 decide +kernel
def cuts14357 : List PrefixCut := [⟨24,170161587,170161704⟩,
⟨82,582719574,582719974⟩,
⟨128,909144553,909145176⟩]
theorem checked14357 : checkPrefixCuts (2^48) 1885732865 9 Manual.Count131072.C014357.packed 128 cuts14357 = true := by
 decide +kernel
def pointBounds14357 : List (Nat × Nat × Nat) := [(1885757440,95693285525722,95693663171807),(1885816832,95693698083709,95694075730077)]
theorem point_links_checked14357 : (cuts14357.take 2).map (fun c => (1885732865-1+2*2^9*c.k,95693115364135+c.lower,95693493010103+c.upper)) = pointBounds14357 := by
 decide +kernel
def cuts14358 : List PrefixCut := [⟨12,81194533,81194586⟩,
⟨70,502532438,502532777⟩,
⟨128,910424770,910425389⟩]
theorem checked14358 : checkPrefixCuts (2^48) 1885863937 9 Manual.Count131072.C014358.packed 128 cuts14358 = true := by
 decide +kernel
def pointBounds14358 : List (Nat × Nat × Nat) := [(1885876224,95694105703221,95694483349865),(1885935616,95694527041126,95694904688056),(1885995008,95694934933458,95695312580668)]
theorem point_links_checked14358 : (cuts14358.take 3).map (fun c => (1885863937-1+2*2^9*c.k,95694024508688+c.lower,95694402155279+c.upper)) = pointBounds14358 := by
 decide +kernel
def cuts14359 : List PrefixCut := [⟨58,411312052,411312334⟩,
⟨116,831565383,831565948⟩,
⟨128,917524671,917525296⟩]
theorem checked14359 : checkPrefixCuts (2^48) 1885995009 9 Manual.Count131072.C014359.packed 128 cuts14359 = true := by
 decide +kernel
def pointBounds14359 : List (Nat × Nat × Nat) := [(1886054400,95695346245510,95695723893002),(1886113792,95695766498841,95696144146616)]
theorem point_links_checked14359 : (cuts14359.take 2).map (fun c => (1885995009-1+2*2^9*c.k,95694934933458+c.lower,95695312580668+c.upper)) = pointBounds14359 := by
 decide +kernel
def cuts14360 : List PrefixCut := [⟨46,325476162,325476381⟩,
⟨104,747792296,747792806⟩,
⟨128,923280901,923281529⟩]
theorem checked14360 : checkPrefixCuts (2^48) 1886126081 9 Manual.Count131072.C014360.packed 128 cuts14360 = true := by
 decide +kernel
def pointBounds14360 : List (Nat × Nat × Nat) := [(1886173184,95696177934291,95696555582345),(1886232576,95696600250425,95696977898770)]
theorem point_links_checked14360 : (cuts14360.take 2).map (fun c => (1886126081-1+2*2^9*c.k,95695852458129+c.lower,95696230105964+c.upper)) = pointBounds14360 := by
 decide +kernel
def cuts14361 : List PrefixCut := [⟨34,240994567,240994734⟩,
⟨92,652092709,652093154⟩,
⟨128,910682472,910683096⟩]
theorem checked14361 : checkPrefixCuts (2^48) 1886257153 9 Manual.Count131072.C014361.packed 128 cuts14361 = true := by
 decide +kernel
def pointBounds14361 : List (Nat × Nat × Nat) := [(1886291968,95697016733597,95697394382227),(1886351360,95697427831739,95697805480647)]
theorem point_links_checked14361 : (cuts14361.take 2).map (fun c => (1886257153-1+2*2^9*c.k,95696775739030+c.lower,95697153387493+c.upper)) = pointBounds14361 := by
 decide +kernel
def cuts14362 : List PrefixCut := [⟨22,152943091,152943198⟩,
⟨80,558345381,558345769⟩,
⟨128,903606252,903606872⟩]
theorem checked14362 : checkPrefixCuts (2^48) 1886388225 9 Manual.Count131072.C014362.packed 128 cuts14362 = true := by
 decide +kernel
def pointBounds14362 : List (Nat × Nat × Nat) := [(1886410752,95697839364593,95698217013787),(1886470144,95698244766883,95698622416358)]
theorem point_links_checked14362 : (cuts14362.take 2).map (fun c => (1886388225-1+2*2^9*c.k,95697686421502+c.lower,95698064070589+c.upper)) = pointBounds14362 := by
 decide +kernel
def cuts14363 : List PrefixCut := [⟨10,67290502,67290550⟩,
⟨68,476098827,476099150⟩,
⟨126,897128430,897129039⟩,
⟨128,913390468,913391088⟩]
theorem checked14363 : checkPrefixCuts (2^48) 1886519297 9 Manual.Count131072.C014363.packed 128 cuts14363 = true := by
 decide +kernel
def pointBounds14363 : List (Nat × Nat × Nat) := [(1886529536,95698657318256,95699034968011),(1886588928,95699066126581,95699443776611),(1886648320,95699487156184,95699864806500)]
theorem point_links_checked14363 : (cuts14363.take 3).map (fun c => (1886519297-1+2*2^9*c.k,95698590027754+c.lower,95698967677461+c.upper)) = pointBounds14363 := by
 decide +kernel
def cuts14364 : List PrefixCut := [⟨56,392073018,392073284⟩,
⟨114,806064218,806064769⟩,
⟨128,904525085,904525702⟩]
theorem checked14364 : checkPrefixCuts (2^48) 1886650369 9 Manual.Count131072.C014364.packed 128 cuts14364 = true := by
 decide +kernel
def pointBounds14364 : List (Nat × Nat × Nat) := [(1886707712,95699895491240,95700273141833),(1886767104,95700309482440,95700687133318)]
theorem point_links_checked14364 : (cuts14364.take 2).map (fun c => (1886650369-1+2*2^9*c.k,95699503418222+c.lower,95699881068549+c.upper)) = pointBounds14364 := by
 decide +kernel
def cuts14365 : List PrefixCut := [⟨44,317904284,317904505⟩,
⟨102,736046452,736046955⟩,
⟨128,925794847,925795481⟩]
theorem checked14365 : checkPrefixCuts (2^48) 1886781441 9 Manual.Count131072.C014365.packed 128 cuts14365 = true := by
 decide +kernel
def pointBounds14365 : List (Nat × Nat × Nat) := [(1886826496,95700725847591,95701103498756),(1886885888,95701143989759,95701521641206)]
theorem point_links_checked14365 : (cuts14365.take 2).map (fun c => (1886781441-1+2*2^9*c.k,95700407943307+c.lower,95700785594251+c.upper)) = pointBounds14365 := by
 decide +kernel
def cuts14366 : List PrefixCut := [⟨32,228678985,228679140⟩,
⟨90,651120654,651121094⟩,
⟨128,920658859,920659481⟩]
theorem checked14366 : checkPrefixCuts (2^48) 1886912513 9 Manual.Count131072.C014366.packed 128 cuts14366 = true := by
 decide +kernel
def pointBounds14366 : List (Nat × Nat × Nat) := [(1886945280,95701562417139,95701940068872),(1887004672,95701984858808,95702362510826)]
theorem point_links_checked14366 : (cuts14366.take 2).map (fun c => (1886912513-1+2*2^9*c.k,95701333738154+c.lower,95701711389732+c.upper)) = pointBounds14366 := by
 decide +kernel
def cuts14367 : List PrefixCut := [⟨20,146774459,146774561⟩,
⟨78,555765349,555765729⟩,
⟨128,916567749,916568375⟩]
theorem checked14367 : checkPrefixCuts (2^48) 1887043585 9 Manual.Count131072.C014367.packed 128 cuts14367 = true := by
 decide +kernel
def pointBounds14367 : List (Nat × Nat × Nat) := [(1887064064,95702401171472,95702778823774),(1887123456,95702810162362,95703187814942)]
theorem point_links_checked14367 : (cuts14367.take 2).map (fun c => (1887043585-1+2*2^9*c.k,95702254397013+c.lower,95702632049213+c.upper)) = pointBounds14367 := by
 decide +kernel
def cuts14368 : List PrefixCut := [⟨8,56528290,56528328⟩,
⟨66,475188080,475188402⟩,
⟨124,890105990,890106593⟩,
⟨128,917995410,917996032⟩]
theorem checked14368 : checkPrefixCuts (2^48) 1887174657 9 Manual.Count131072.C014368.packed 128 cuts14368 = true := by
 decide +kernel
def pointBounds14368 : List (Nat × Nat × Nat) := [(1887182848,95703227493052,95703605145916),(1887242240,95703646152842,95704023805990),(1887301632,95704061070752,95704438724181)]
theorem point_links_checked14368 : (cuts14368.take 3).map (fun c => (1887174657-1+2*2^9*c.k,95703170964762+c.lower,95703548617588+c.upper)) = pointBounds14368 := by
 decide +kernel
def cuts14369 : List PrefixCut := [⟨54,378216260,378216520⟩,
⟨112,801608860,801609409⟩,
⟨128,914650455,914651081⟩]
theorem checked14369 : checkPrefixCuts (2^48) 1887305729 9 Manual.Count131072.C014369.packed 128 cuts14369 = true := by
 decide +kernel
def pointBounds14369 : List (Nat × Nat × Nat) := [(1887361024,95704467176432,95704844830140),(1887420416,95704890569032,95705268223029)]
theorem point_links_checked14369 : (cuts14369.take 2).map (fun c => (1887305729-1+2*2^9*c.k,95704088960172+c.lower,95704466613620+c.upper)) = pointBounds14369 := by
 decide +kernel
def cuts14370 : List PrefixCut := [⟨42,295424599,295424803⟩,
⟨100,710290480,710290964⟩,
⟨128,913244907,913245527⟩]
theorem checked14370 : checkPrefixCuts (2^48) 1887436801 9 Manual.Count131072.C014370.packed 128 cuts14370 = true := by
 decide +kernel
def pointBounds14370 : List (Nat × Nat × Nat) := [(1887479808,95705299035226,95705676689504),(1887539200,95705713901107,95706091555665)]
theorem point_links_checked14370 : (cuts14370.take 2).map (fun c => (1887436801-1+2*2^9*c.k,95705003610627+c.lower,95705381264701+c.upper)) = pointBounds14370 := by
 decide +kernel
def cuts14371 : List PrefixCut := [⟨30,213687778,213687921⟩,
⟨88,632404379,632404809⟩,
⟨128,913778104,913778726⟩]
theorem checked14371 : checkPrefixCuts (2^48) 1887567873 9 Manual.Count131072.C014371.packed 128 cuts14371 = true := by
 decide +kernel
def pointBounds14371 : List (Nat × Nat × Nat) := [(1887598592,95706130543312,95706508198149),(1887657984,95706549259913,95706926915037)]
theorem point_links_checked14371 : (cuts14371.take 2).map (fun c => (1887567873-1+2*2^9*c.k,95705916855534+c.lower,95706294510228+c.upper)) = pointBounds14371 := by
 decide +kernel
def cuts14372 : List PrefixCut := [⟨18,126295594,126295679⟩,
⟨76,544538612,544538982⟩,
⟨128,911925451,911926071⟩]
theorem checked14372 : checkPrefixCuts (2^48) 1887698945 9 Manual.Count131072.C014372.packed 128 cuts14372 = true := by
 decide +kernel
def pointBounds14372 : List (Nat × Nat × Nat) := [(1887717376,95706956929232,95707334584633),(1887776768,95707375172250,95707752827936)]
theorem point_links_checked14372 : (cuts14372.take 2).map (fun c => (1887698945-1+2*2^9*c.k,95706830633638+c.lower,95707208288954+c.upper)) = pointBounds14372 := by
 decide +kernel
def cuts14373 : List PrefixCut := [⟨6,44431641,44431671⟩,
⟨64,449676964,449677272⟩,
⟨122,868625894,868626485⟩,
⟨128,909774621,909775240⟩]
theorem checked14373 : checkPrefixCuts (2^48) 1887830017 9 Manual.Count131072.C014373.packed 128 cuts14373 = true := by
 decide +kernel
def pointBounds14373 : List (Nat × Nat × Nat) := [(1887836160,95707786990730,95708164646696),(1887895552,95708192236053,95708569892297),(1887954944,95708611184983,95708988841510)]
theorem point_links_checked14373 : (cuts14373.take 3).map (fun c => (1887830017-1+2*2^9*c.k,95707742559089+c.lower,95708120215025+c.upper)) = pointBounds14373 := by
 decide +kernel
def cuts14374 : List PrefixCut := [⟨52,377190688,377190949⟩,
⟨110,798498734,798499282⟩,
⟨128,923129387,923130020⟩]
theorem checked14374 : checkPrefixCuts (2^48) 1887961089 9 Manual.Count131072.C014374.packed 128 cuts14374 = true := by
 decide +kernel
def pointBounds14374 : List (Nat × Nat × Nat) := [(1888014336,95709029524398,95709407181214),(1888073728,95709450832444,95709828489547)]
theorem point_links_checked14374 : (cuts14374.take 2).map (fun c => (1887961089-1+2*2^9*c.k,95708652333710+c.lower,95709029990265+c.upper)) = pointBounds14374 := by
 decide +kernel
def cuts14375 : List PrefixCut := [⟨40,284737749,284737947⟩,
⟨98,700205494,700205977⟩,
⟨128,925599160,925599795⟩]
theorem checked14375 : checkPrefixCuts (2^48) 1888092161 9 Manual.Count131072.C014375.packed 128 cuts14375 = true := by
 decide +kernel
def pointBounds14375 : List (Nat × Nat × Nat) := [(1888133120,95709860200846,95710237858232),(1888192512,95710275668591,95710653326262)]
theorem point_links_checked14375 : (cuts14375.take 2).map (fun c => (1888092161-1+2*2^9*c.k,95709575463097+c.lower,95709953120285+c.upper)) = pointBounds14375 := by
 decide +kernel
def cuts14376 : List PrefixCut := [⟨28,207800116,207800258⟩,
⟨86,632185458,632185888⟩,
⟨128,935522520,935523158⟩]
theorem checked14376 : checkPrefixCuts (2^48) 1888223233 9 Manual.Count131072.C014376.packed 128 cuts14376 = true := by
 decide +kernel
def pointBounds14376 : List (Nat × Nat × Nat) := [(1888251904,95710708862373,95711086520338),(1888311296,95711133247715,95711510905968)]
theorem point_links_checked14376 : (cuts14376.take 2).map (fun c => (1888223233-1+2*2^9*c.k,95710501062257+c.lower,95710878720080+c.upper)) = pointBounds14376 := by
 decide +kernel
def cuts14377 : List PrefixCut := [⟨16,112836637,112836716⟩,
⟨74,528102930,528103294⟩,
⟨128,911459873,911460497⟩]
theorem checked14377 : checkPrefixCuts (2^48) 1888354305 9 Manual.Count131072.C014377.packed 128 cuts14377 = true := by
 decide +kernel
def pointBounds14377 : List (Nat × Nat × Nat) := [(1888370688,95711549421414,95711927079954),(1888430080,95711964687707,95712342346532)]
theorem point_links_checked14377 : (cuts14377.take 2).map (fun c => (1888354305-1+2*2^9*c.k,95711436584777+c.lower,95711814243238+c.upper)) = pointBounds14377 := by
 decide +kernel
def cuts14378 : List PrefixCut := [⟨4,26977649,26977668⟩,
⟨62,441025475,441025773⟩,
⟨120,862214200,862214781⟩,
⟨128,918252462,918253081⟩]
theorem checked14378 : checkPrefixCuts (2^48) 1888485377 9 Manual.Count131072.C014378.packed 128 cuts14378 = true := by
 decide +kernel
def pointBounds14378 : List (Nat × Nat × Nat) := [(1888489472,95712375022299,95712752681403),(1888548864,95712789070125,95713166729508),(1888608256,95713210258850,95713587918516)]
theorem point_links_checked14378 : (cuts14378.take 3).map (fun c => (1888485377-1+2*2^9*c.k,95712348044650+c.lower,95712725703735+c.upper)) = pointBounds14378 := by
 decide +kernel
def cuts14379 : List PrefixCut := [⟨50,356940236,356940480⟩,
⟨108,776016041,776016569⟩,
⟨128,915804386,915805008⟩]
theorem checked14379 : checkPrefixCuts (2^48) 1888616449 9 Manual.Count131072.C014379.packed 128 cuts14379 = true := by
 decide +kernel
def pointBounds14379 : List (Nat × Nat × Nat) := [(1888667648,95713623237348,95714000897296),(1888727040,95714042313153,95714419973385)]
theorem point_links_checked14379 : (cuts14379.take 2).map (fun c => (1888616449-1+2*2^9*c.k,95713266297112+c.lower,95713643956816+c.upper)) = pointBounds14379 := by
 decide +kernel
def cuts14380 : List PrefixCut := [⟨38,271822966,271823155⟩,
⟨96,686401817,686402291⟩,
⟨128,914548727,914549361⟩]
theorem checked14380 : checkPrefixCuts (2^48) 1888747521 9 Manual.Count131072.C014380.packed 128 cuts14380 = true := by
 decide +kernel
def pointBounds14380 : List (Nat × Nat × Nat) := [(1888786432,95714453924464,95714831584979),(1888845824,95714868503315,95715246164115)]
theorem point_links_checked14380 : (cuts14380.take 2).map (fun c => (1888747521-1+2*2^9*c.k,95714182101498+c.lower,95714559761824+c.upper)) = pointBounds14380 := by
 decide +kernel
def cuts14381 : List PrefixCut := [⟨26,191485442,191485568⟩,
⟨84,605442208,605442614⟩,
⟨128,918657810,918658432⟩]
theorem checked14381 : checkPrefixCuts (2^48) 1888878593 9 Manual.Count131072.C014381.packed 128 cuts14381 = true := by
 decide +kernel
def pointBounds14381 : List (Nat × Nat × Nat) := [(1888905216,95715288135667,95715665796753),(1888964608,95715702092433,95716079753799)]
theorem point_links_checked14381 : (cuts14381.take 2).map (fun c => (1888878593-1+2*2^9*c.k,95715096650225+c.lower,95715474311185+c.upper)) = pointBounds14381 := by
 decide +kernel
def cuts14382 : List PrefixCut := [⟨14,103112151,103112220⟩,
⟨72,527919956,527920308⟩,
⟨128,930215899,930216524⟩]
theorem checked14382 : checkPrefixCuts (2^48) 1889009665 9 Manual.Count131072.C014382.packed 128 cuts14382 = true := by
 decide +kernel
def pointBounds14382 : List (Nat × Nat × Nat) := [(1889024000,95716118420186,95716496081837),(1889083392,95716543227991,95716920889925)]
theorem point_links_checked14382 : (cuts14382.take 2).map (fun c => (1889009665-1+2*2^9*c.k,95716015308035+c.lower,95716392969617+c.upper)) = pointBounds14382 := by
 decide +kernel
def cuts14383 : List PrefixCut := [⟨2,15942590,15942601⟩,
⟨60,427761240,427761534⟩,
⟨118,841503973,841504554⟩,
⟨128,909441731,909442358⟩]
theorem checked14383 : checkPrefixCuts (2^48) 1889140737 9 Manual.Count131072.C014383.packed 128 cuts14383 = true := by
 decide +kernel
def pointBounds14383 : List (Nat × Nat × Nat) := [(1889142784,95716961466524,95717339128742),(1889202176,95717373285174,95717750947675),(1889261568,95717787027907,95718164690695)]
theorem point_links_checked14383 : (cuts14383.take 3).map (fun c => (1889140737-1+2*2^9*c.k,95716945523934+c.lower,95717323186141+c.upper)) = pointBounds14383 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000136
