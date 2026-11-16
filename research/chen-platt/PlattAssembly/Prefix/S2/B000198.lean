import PlattAssemblyKernel
import PlattCertificates.Count131072.C016336
import PlattCertificates.Count131072.C016337
import PlattCertificates.Count131072.C016338
import PlattCertificates.Count131072.C016339
import PlattCertificates.Count131072.C016340
import PlattCertificates.Count131072.C016341
import PlattCertificates.Count131072.C016342
import PlattCertificates.Count131072.C016343
import PlattCertificates.Count131072.C016344
import PlattCertificates.Count131072.C016345
import PlattCertificates.Count131072.C016346
import PlattCertificates.Count131072.C016347
import PlattCertificates.Count131072.C016348
import PlattCertificates.Count131072.C016349
import PlattCertificates.Count131072.C016350
import PlattCertificates.Count131072.C016351
import PlattCertificates.Count131072.C016352
import PlattCertificates.Count131072.C016353
import PlattCertificates.Count131072.C016354
import PlattCertificates.Count131072.C016355
import PlattCertificates.Count131072.C016356
import PlattCertificates.Count131072.C016357
import PlattCertificates.Count131072.C016358
import PlattCertificates.Count131072.C016359
import PlattCertificates.Count131072.C016360
import PlattCertificates.Count131072.C016361
import PlattCertificates.Count131072.C016362
import PlattCertificates.Count131072.C016363
import PlattCertificates.Count131072.C016364
import PlattCertificates.Count131072.C016365
import PlattCertificates.Count131072.C016366
import PlattCertificates.Count131072.C016367
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000198
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16336 : List PrefixCut := [⟨19,115600870,115600943⟩,
⟨85,530364671,530365008⟩,
⟨128,799868918,799869428⟩]
theorem checked16336 : checkPrefixCuts (2^48) 2145124353 9 Manual.Count131072.C016336.packed 128 cuts16336 = true := by
 decide +kernel
def pointBounds16336 : List (Nat × Nat × Nat) := [(2145143808,97386685494406,97387064256364),(2145211392,97387100258207,97387479020429)]
theorem point_links_checked16336 : (cuts16336.take 2).map (fun c => (2145124353-1+2*2^9*c.k,97386569893536+c.lower,97386948655421+c.upper)) = pointBounds16336 := by
 decide +kernel
def cuts16337 : List PrefixCut := [⟨23,146689848,146689940⟩,
⟨89,562870879,562871233⟩,
⟨128,809398120,809398629⟩]
theorem checked16337 : checkPrefixCuts (2^48) 2145255425 9 Manual.Count131072.C016337.packed 128 cuts16337 = true := by
 decide +kernel
def pointBounds16337 : List (Nat × Nat × Nat) := [(2145278976,97387516452302,97387895214789),(2145346560,97387932633333,97388311396082)]
theorem point_links_checked16337 : (cuts16337.take 2).map (fun c => (2145255425-1+2*2^9*c.k,97387369762454+c.lower,97387748524849+c.upper)) = pointBounds16337 := by
 decide +kernel
def cuts16338 : List PrefixCut := [⟨27,169115799,169115906⟩,
⟨93,584876947,584877313⟩,
⟨128,803707156,803707663⟩]
theorem checked16338 : checkPrefixCuts (2^48) 2145386497 9 Manual.Count131072.C016338.packed 128 cuts16338 = true := by
 decide +kernel
def pointBounds16338 : List (Nat × Nat × Nat) := [(2145414144,97388348276373,97388727039384),(2145481728,97388764037521,97389142800791)]
theorem point_links_checked16338 : (cuts16338.take 2).map (fun c => (2145386497-1+2*2^9*c.k,97388179160574+c.lower,97388557923478+c.upper)) = pointBounds16338 := by
 decide +kernel
def cuts16339 : List PrefixCut := [⟨31,194556384,194556507⟩,
⟨97,607667641,607668025⟩,
⟨128,805232298,805232808⟩]
theorem checked16339 : checkPrefixCuts (2^48) 2145517569 9 Manual.Count131072.C016339.packed 128 cuts16339 = true := by
 decide +kernel
def pointBounds16339 : List (Nat × Nat × Nat) := [(2145549312,97389177424114,97389556187648),(2145616896,97389590535371,97389969299166)]
theorem point_links_checked16339 : (cuts16339.take 2).map (fun c => (2145517569-1+2*2^9*c.k,97388982867730+c.lower,97389361631141+c.upper)) = pointBounds16339 := by
 decide +kernel
def cuts16340 : List PrefixCut := [⟨35,216451881,216452018⟩,
⟨101,626913427,626913822⟩,
⟨128,796000466,796000968⟩]
theorem checked16340 : checkPrefixCuts (2^48) 2145648641 9 Manual.Count131072.C016340.packed 128 cuts16340 = true := by
 decide +kernel
def pointBounds16340 : List (Nat × Nat × Nat) := [(2145684480,97390004551909,97390383315967),(2145752064,97390415013455,97390793777771)]
theorem point_links_checked16340 : (cuts16340.take 2).map (fun c => (2145648641-1+2*2^9*c.k,97389788100028+c.lower,97390166863949+c.upper)) = pointBounds16340 := by
 decide +kernel
def cuts16341 : List PrefixCut := [⟨39,252905021,252905183⟩,
⟨105,663996592,663997014⟩,
⟨128,808675725,808676241⟩]
theorem checked16341 : checkPrefixCuts (2^48) 2145779713 9 Manual.Count131072.C016341.packed 128 cuts16341 = true := by
 decide +kernel
def pointBounds16341 : List (Nat × Nat × Nat) := [(2145819648,97390837005515,97391215770100),(2145887232,97391248097086,97391626861931)]
theorem point_links_checked16341 : (cuts16341.take 2).map (fun c => (2145779713-1+2*2^9*c.k,97390584100494+c.lower,97390962864917+c.upper)) = pointBounds16341 := by
 decide +kernel
def cuts16342 : List PrefixCut := [⟨43,273613671,273613843⟩,
⟨109,688089609,688090041⟩,
⟨128,806002996,806003502⟩]
theorem checked16342 : checkPrefixCuts (2^48) 2145910785 9 Manual.Count131072.C016342.packed 128 cuts16342 = true := by
 decide +kernel
def pointBounds16342 : List (Nat × Nat × Nat) := [(2145954816,97391666389890,97392045155001),(2146022400,97392080865828,97392459631199)]
theorem point_links_checked16342 : (cuts16342.take 2).map (fun c => (2145910785-1+2*2^9*c.k,97391392776219+c.lower,97391771541158+c.upper)) = pointBounds16342 := by
 decide +kernel
def cuts16343 : List PrefixCut := [⟨47,296811811,296811996⟩,
⟨113,711392813,711393261⟩,
⟨128,805953740,805954248⟩]
theorem checked16343 : checkPrefixCuts (2^48) 2146041857 9 Manual.Count131072.C016343.packed 128 cuts16343 = true := by
 decide +kernel
def pointBounds16343 : List (Nat × Nat × Nat) := [(2146089984,97392495591026,97392874356656),(2146157568,97392910172028,97393288937921)]
theorem point_links_checked16343 : (cuts16343.take 2).map (fun c => (2146041857-1+2*2^9*c.k,97392198779215+c.lower,97392577544660+c.upper)) = pointBounds16343 := by
 decide +kernel
def cuts16344 : List PrefixCut := [⟨51,311088818,311089015⟩,
⟨117,729315780,729316245⟩,
⟨128,794887951,794888456⟩]
theorem checked16344 : checkPrefixCuts (2^48) 2146172929 9 Manual.Count131072.C016344.packed 128 cuts16344 = true := by
 decide +kernel
def pointBounds16344 : List (Nat × Nat × Nat) := [(2146225152,97393315821773,97393694587923),(2146292736,97393734048735,97394112815153)]
theorem point_links_checked16344 : (cuts16344.take 2).map (fun c => (2146172929-1+2*2^9*c.k,97393004732955+c.lower,97393383498908+c.upper)) = pointBounds16344 := by
 decide +kernel
def cuts16345 : List PrefixCut := [⟨55,345822196,345822415⟩,
⟨121,753925212,753925686⟩,
⟨128,798773796,798774298⟩]
theorem checked16345 : checkPrefixCuts (2^48) 2146304001 9 Manual.Count131072.C016345.packed 128 cuts16345 = true := by
 decide +kernel
def pointBounds16345 : List (Nat × Nat × Nat) := [(2146360320,97394145443102,97394524209779),(2146427904,97394553546118,97394932313050)]
theorem point_links_checked16345 : (cuts16345.take 2).map (fun c => (2146304001-1+2*2^9*c.k,97393799620906+c.lower,97394178387364+c.upper)) = pointBounds16345 := by
 decide +kernel
def cuts16346 : List PrefixCut := [⟨59,359832037,359832269⟩,
⟨125,769876284,769876779⟩,
⟨128,789938880,789939388⟩]
theorem checked16346 : checkPrefixCuts (2^48) 2146435073 9 Manual.Count131072.C016346.packed 128 cuts16346 = true := by
 decide +kernel
def pointBounds16346 : List (Nat × Nat × Nat) := [(2146495488,97394958226739,97395336993931),(2146563072,97395368270986,97395747038441)]
theorem point_links_checked16346 : (cuts16346.take 2).map (fun c => (2146435073-1+2*2^9*c.k,97394598394702+c.lower,97394977161662+c.upper)) = pointBounds16346 := by
 decide +kernel
def cuts16347 : List PrefixCut := [⟨63,398491974,398492220⟩,
⟨128,802085506,802086010⟩]
theorem checked16347 : checkPrefixCuts (2^48) 2146566145 9 Manual.Count131072.C016347.packed 128 cuts16347 = true := by
 decide +kernel
def pointBounds16347 : List (Nat × Nat × Nat) := [(2146630656,97395786825556,97396165593270)]
theorem point_links_checked16347 : (cuts16347.take 1).map (fun c => (2146566145-1+2*2^9*c.k,97395388333582+c.lower,97395767101050+c.upper)) = pointBounds16347 := by
 decide +kernel
def cuts16348 : List PrefixCut := [⟨1,5900397,5900401⟩,
⟨67,421150677,421150947⟩,
⟨128,806232086,806232607⟩]
theorem checked16348 : checkPrefixCuts (2^48) 2146697217 9 Manual.Count131072.C016348.packed 128 cuts16348 = true := by
 decide +kernel
def pointBounds16348 : List (Nat × Nat × Nat) := [(2146698240,97396196319485,97396575087461),(2146765824,97396611569765,97396990338007)]
theorem point_links_checked16348 : (cuts16348.take 2).map (fun c => (2146697217-1+2*2^9*c.k,97396190419088+c.lower,97396569187060+c.upper)) = pointBounds16348 := by
 decide +kernel
def cuts16349 : List PrefixCut := [⟨5,30417942,30417961⟩,
⟨71,451279751,451280040⟩,
⟨128,807494041,807494551⟩]
theorem checked16349 : checkPrefixCuts (2^48) 2146828289 9 Manual.Count131072.C016349.packed 128 cuts16349 = true := by
 decide +kernel
def pointBounds16349 : List (Nat × Nat × Nat) := [(2146833408,97397027069116,97397405837628),(2146900992,97397447930925,97397826699707)]
theorem point_links_checked16349 : (cuts16349.take 2).map (fun c => (2146828289-1+2*2^9*c.k,97396996651174+c.lower,97397375419667+c.upper)) = pointBounds16349 := by
 decide +kernel
def cuts16350 : List PrefixCut := [⟨9,55325758,55325791⟩,
⟨75,467115094,467115386⟩,
⟨128,791319475,791319971⟩]
theorem checked16350 : checkPrefixCuts (2^48) 2146959361 9 Manual.Count131072.C016350.packed 128 cuts16350 = true := by
 decide +kernel
def pointBounds16350 : List (Nat × Nat × Nat) := [(2146968576,97397859470973,97398238240009),(2147036160,97398271260309,97398650029604)]
theorem point_links_checked16350 : (cuts16350.take 2).map (fun c => (2146959361-1+2*2^9*c.k,97397804145215+c.lower,97398182914218+c.upper)) = pointBounds16350 := by
 decide +kernel
def cuts16351 : List PrefixCut := [⟨13,76428710,76428760⟩,
⟨79,490420708,490421021⟩,
⟨128,797825592,797826095⟩]
theorem checked16351 : checkPrefixCuts (2^48) 2147090433 9 Manual.Count131072.C016351.packed 128 cuts16351 = true := by
 decide +kernel
def pointBounds16351 : List (Nat × Nat × Nat) := [(2147103744,97398671893400,97399050662949),(2147171328,97399085885398,97399464655210)]
theorem point_links_checked16351 : (cuts16351.take 2).map (fun c => (2147090433-1+2*2^9*c.k,97398595464690+c.lower,97398974234189+c.upper)) = pointBounds16351 := by
 decide +kernel
def cuts16352 : List PrefixCut := [⟨17,107098432,107098500⟩,
⟨83,520671068,520671400⟩,
⟨128,799874335,799874843⟩]
theorem checked16352 : checkPrefixCuts (2^48) 2147221505 9 Manual.Count131072.C016352.packed 128 cuts16352 = true := by
 decide +kernel
def pointBounds16352 : List (Nat × Nat × Nat) := [(2147238912,97399500388714,97399879158784),(2147306496,97399913961350,97400292731684)]
theorem point_links_checked16352 : (cuts16352.take 2).map (fun c => (2147221505-1+2*2^9*c.k,97399393290282+c.lower,97399772060284+c.upper)) = pointBounds16352 := by
 decide +kernel
def cuts16353 : List PrefixCut := [⟨21,135667071,135667156⟩,
⟨87,547116500,547116846⟩,
⟨128,802316089,802316597⟩]
theorem checked16353 : checkPrefixCuts (2^48) 2147352577 9 Manual.Count131072.C016353.packed 128 cuts16353 = true := by
 decide +kernel
def pointBounds16353 : List (Nat × Nat × Nat) := [(2147374080,97400328831688,97400707602283),(2147441664,97400740281117,97401119051973)]
theorem point_links_checked16353 : (cuts16353.take 2).map (fun c => (2147352577-1+2*2^9*c.k,97400193164617+c.lower,97400571935127+c.upper)) = pointBounds16353 := by
 decide +kernel
def cuts16354 : List PrefixCut := [⟨25,158465070,158465172⟩,
⟨91,570937070,570937437⟩,
⟨128,797679714,797680228⟩]
theorem checked16354 : checkPrefixCuts (2^48) 2147483649 9 Manual.Count131072.C016354.packed 128 cuts16354 = true := by
 decide +kernel
def pointBounds16354 : List (Nat × Nat × Nat) := [(2147509248,97401153945776,97401532716896),(2147576832,97401566417776,97401945189161)]
theorem point_links_checked16354 : (cuts16354.take 2).map (fun c => (2147483649-1+2*2^9*c.k,97400995480706+c.lower,97401374251724+c.upper)) = pointBounds16354 := by
 decide +kernel
def cuts16355 : List PrefixCut := [⟨29,180211696,180211808⟩,
⟨95,592264604,592264976⟩,
⟨128,799727810,799728313⟩]
theorem checked16355 : checkPrefixCuts (2^48) 2147614721 9 Manual.Count131072.C016355.packed 128 cuts16355 = true := by
 decide +kernel
def pointBounds16355 : List (Nat × Nat × Nat) := [(2147644416,97401973372116,97402352143760),(2147712000,97402385425024,97402764196928)]
theorem point_links_checked16355 : (cuts16355.take 2).map (fun c => (2147614721-1+2*2^9*c.k,97401793160420+c.lower,97402171931952+c.upper)) = pointBounds16355 := by
 decide +kernel
def cuts16356 : List PrefixCut := [⟨33,204314631,204314763⟩,
⟨99,623680552,623680952⟩,
⟨128,806886877,806887395⟩]
theorem checked16356 : checkPrefixCuts (2^48) 2147745793 9 Manual.Count131072.C016356.packed 128 cuts16356 = true := by
 decide +kernel
def pointBounds16356 : List (Nat × Nat × Nat) := [(2147779584,97402797202861,97403175975028),(2147847168,97403216568782,97403595341217)]
theorem point_links_checked16356 : (cuts16356.take 2).map (fun c => (2147745793-1+2*2^9*c.k,97402592888230+c.lower,97402971660265+c.upper)) = pointBounds16356 := by
 decide +kernel
def cuts16357 : List PrefixCut := [⟨37,232083879,232084029⟩,
⟨103,643822842,643823246⟩,
⟨128,799368207,799368707⟩]
theorem checked16357 : checkPrefixCuts (2^48) 2147876865 9 Manual.Count131072.C016357.packed 128 cuts16357 = true := by
 decide +kernel
def pointBounds16357 : List (Nat × Nat × Nat) := [(2147914752,97403631858986,97404010631689),(2147982336,97404043597949,97404422370906)]
theorem point_links_checked16357 : (cuts16357.take 2).map (fun c => (2147876865-1+2*2^9*c.k,97403399775107+c.lower,97403778547660+c.upper)) = pointBounds16357 := by
 decide +kernel
def cuts16358 : List PrefixCut := [⟨41,263518777,263518941⟩,
⟨107,669859335,669859757⟩,
⟨128,801285056,801285561⟩]
theorem checked16358 : checkPrefixCuts (2^48) 2148007937 9 Manual.Count131072.C016358.packed 128 cuts16358 = true := by
 decide +kernel
def pointBounds16358 : List (Nat × Nat × Nat) := [(2148049920,97404462662091,97404841435308),(2148117504,97404869002649,97405247776124)]
theorem point_links_checked16358 : (cuts16358.take 2).map (fun c => (2148007937-1+2*2^9*c.k,97404199143314+c.lower,97404577916367+c.upper)) = pointBounds16358 := by
 decide +kernel
def cuts16359 : List PrefixCut := [⟨45,282894992,282895169⟩,
⟨111,696023429,696023868⟩,
⟨128,799794837,799795343⟩]
theorem checked16359 : checkPrefixCuts (2^48) 2148139009 9 Manual.Count131072.C016359.packed 128 cuts16359 = true := by
 decide +kernel
def pointBounds16359 : List (Nat × Nat × Nat) := [(2148185088,97405283323362,97405662097097),(2148252672,97405696451799,97406075225796)]
theorem point_links_checked16359 : (cuts16359.take 2).map (fun c => (2148139009-1+2*2^9*c.k,97405000428370+c.lower,97405379201928+c.upper)) = pointBounds16359 := by
 decide +kernel
def cuts16360 : List PrefixCut := [⟨49,296241779,296241970⟩,
⟨115,713929930,713930387⟩,
⟨128,792670778,792671286⟩]
theorem checked16360 : checkPrefixCuts (2^48) 2148270081 9 Manual.Count131072.C016360.packed 128 cuts16360 = true := by
 decide +kernel
def pointBounds16360 : List (Nat × Nat × Nat) := [(2148320256,97406096464986,97406475239241),(2148387840,97406514153137,97406892927658)]
theorem point_links_checked16360 : (cuts16360.take 2).map (fun c => (2148270081-1+2*2^9*c.k,97405800223207+c.lower,97406178997271+c.upper)) = pointBounds16360 := by
 decide +kernel
def cuts16361 : List PrefixCut := [⟨53,334086555,334086768⟩,
⟨119,751355401,751355875⟩,
⟨128,805461813,805462323⟩]
theorem checked16361 : checkPrefixCuts (2^48) 2148401153 9 Manual.Count131072.C016361.packed 128 cuts16361 = true := by
 decide +kernel
def pointBounds16361 : List (Nat × Nat × Nat) := [(2148455424,97406926980540,97407305755325),(2148523008,97407344249386,97407723024432)]
theorem point_links_checked16361 : (cuts16361.take 2).map (fun c => (2148401153-1+2*2^9*c.k,97406592893985+c.lower,97406971668557+c.upper)) = pointBounds16361 := by
 decide +kernel
def cuts16362 : List PrefixCut := [⟨57,361184126,361184359⟩,
⟨123,774758651,774759142⟩,
⟨128,804757688,804758198⟩]
theorem checked16362 : checkPrefixCuts (2^48) 2148532225 9 Manual.Count131072.C016362.packed 128 cuts16362 = true := by
 decide +kernel
def pointBounds16362 : List (Nat × Nat × Nat) := [(2148590592,97407759539924,97408138315239),(2148658176,97408173114449,97408551890022)]
theorem point_links_checked16362 : (cuts16362.take 2).map (fun c => (2148532225-1+2*2^9*c.k,97407398355798+c.lower,97407777130880+c.upper)) = pointBounds16362 := by
 decide +kernel
def cuts16363 : List PrefixCut := [⟨61,376095520,376095758⟩,
⟨127,788072172,788072671⟩,
⟨128,794228798,794229301⟩]
theorem checked16363 : checkPrefixCuts (2^48) 2148663297 9 Manual.Count131072.C016363.packed 128 cuts16363 = true := by
 decide +kernel
def pointBounds16363 : List (Nat × Nat × Nat) := [(2148725760,97408579209006,97408957984836),(2148793344,97408991185658,97409369961749)]
theorem point_links_checked16363 : (cuts16363.take 2).map (fun c => (2148663297-1+2*2^9*c.k,97408203113486+c.lower,97408581889078+c.upper)) = pointBounds16363 := by
 decide +kernel
def cuts16364 : List PrefixCut := [⟨65,404627983,404628241⟩,
⟨128,788154867,788155368⟩]
theorem checked16364 : checkPrefixCuts (2^48) 2148794369 9 Manual.Count131072.C016364.packed 128 cuts16364 = true := by
 decide +kernel
def pointBounds16364 : List (Nat × Nat × Nat) := [(2148860928,97409401970267,97409780746620)]
theorem point_links_checked16364 : (cuts16364.take 1).map (fun c => (2148794369-1+2*2^9*c.k,97408997342284+c.lower,97409376118379+c.upper)) = pointBounds16364 := by
 decide +kernel
def cuts16365 : List PrefixCut := [⟨3,19647588,19647600⟩,
⟨69,437217463,437217744⟩,
⟨128,796751738,796752247⟩]
theorem checked16365 : checkPrefixCuts (2^48) 2148925441 9 Manual.Count131072.C016365.packed 128 cuts16365 = true := by
 decide +kernel
def pointBounds16365 : List (Nat × Nat × Nat) := [(2148928512,97409805144739,97410183921347),(2148996096,97410222714614,97410601491491)]
theorem point_links_checked16365 : (cuts16365.take 2).map (fun c => (2148925441-1+2*2^9*c.k,97409785497151+c.lower,97410164273747+c.upper)) = pointBounds16365 := by
 decide +kernel
def cuts16366 : List PrefixCut := [⟨7,45841533,45841561⟩,
⟨73,453955077,453955367⟩,
⟨128,799191427,799191933⟩]
theorem checked16366 : checkPrefixCuts (2^48) 2149056513 9 Manual.Count131072.C016366.packed 128 cuts16366 = true := by
 decide +kernel
def pointBounds16366 : List (Nat × Nat × Nat) := [(2149063680,97410628090422,97411006867555),(2149131264,97411036203966,97411414981361)]
theorem point_links_checked16366 : (cuts16366.take 2).map (fun c => (2149056513-1+2*2^9*c.k,97410582248889+c.lower,97410961025994+c.upper)) = pointBounds16366 := by
 decide +kernel
def cuts16367 : List PrefixCut := [⟨11,69805784,69805829⟩,
⟨77,475274396,475274705⟩,
⟨128,793249280,793249787⟩]
theorem checked16367 : checkPrefixCuts (2^48) 2149187585 9 Manual.Count131072.C016367.packed 128 cuts16367 = true := by
 decide +kernel
def pointBounds16367 : List (Nat × Nat × Nat) := [(2149198848,97411451246100,97411830023756),(2149266432,97411856714712,97412235492632)]
theorem point_links_checked16367 : (cuts16367.take 2).map (fun c => (2149187585-1+2*2^9*c.k,97411381440316+c.lower,97411760217927+c.upper)) = pointBounds16367 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000198
