import PlattAssemblyKernel
import PlattCertificates.Count131072.C016464
import PlattCertificates.Count131072.C016465
import PlattCertificates.Count131072.C016466
import PlattCertificates.Count131072.C016467
import PlattCertificates.Count131072.C016468
import PlattCertificates.Count131072.C016469
import PlattCertificates.Count131072.C016470
import PlattCertificates.Count131072.C016471
import PlattCertificates.Count131072.C016472
import PlattCertificates.Count131072.C016473
import PlattCertificates.Count131072.C016474
import PlattCertificates.Count131072.C016475
import PlattCertificates.Count131072.C016476
import PlattCertificates.Count131072.C016477
import PlattCertificates.Count131072.C016478
import PlattCertificates.Count131072.C016479
import PlattCertificates.Count131072.C016480
import PlattCertificates.Count131072.C016481
import PlattCertificates.Count131072.C016482
import PlattCertificates.Count131072.C016483
import PlattCertificates.Count131072.C016484
import PlattCertificates.Count131072.C016485
import PlattCertificates.Count131072.C016486
import PlattCertificates.Count131072.C016487
import PlattCertificates.Count131072.C016488
import PlattCertificates.Count131072.C016489
import PlattCertificates.Count131072.C016490
import PlattCertificates.Count131072.C016491
import PlattCertificates.Count131072.C016492
import PlattCertificates.Count131072.C016493
import PlattCertificates.Count131072.C016494
import PlattCertificates.Count131072.C016495
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000202
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16464 : List PrefixCut := [⟨3,15233135,15233144⟩,
⟨69,420401864,420402127⟩,
⟨128,790406773,790407268⟩]
theorem checked16464 : checkPrefixCuts (2^48) 2161901569 9 Manual.Count131072.C016464.packed 128 cuts16464 = true := by
 decide +kernel
def pointBounds16464 : List (Nat × Nat × Nat) := [(2161904640,97488663453760,97489042280470),(2161972224,97489068622489,97489447449453)]
theorem point_links_checked16464 : (cuts16464.take 2).map (fun c => (2161901569-1+2*2^9*c.k,97488648220625+c.lower,97489027047326+c.upper)) = pointBounds16464 := by
 decide +kernel
def cuts16465 : List PrefixCut := [⟨7,43092796,43092823⟩,
⟨73,451881466,451881753⟩,
⟨128,797649500,797650005⟩]
theorem checked16465 : checkPrefixCuts (2^48) 2162032641 9 Manual.Count131072.C016465.packed 128 cuts16465 = true := by
 decide +kernel
def pointBounds16465 : List (Nat × Nat × Nat) := [(2162039808,97489481720194,97489860547417),(2162107392,97489890508864,97490269336347)]
theorem point_links_checked16465 : (cuts16465.take 2).map (fun c => (2162032641-1+2*2^9*c.k,97489438627398+c.lower,97489817454594+c.upper)) = pointBounds16465 := by
 decide +kernel
def cuts16466 : List PrefixCut := [⟨11,67824663,67824707⟩,
⟨77,475546314,475546618⟩,
⟨128,791222426,791222931⟩]
theorem checked16466 : checkPrefixCuts (2^48) 2162163713 9 Manual.Count131072.C016466.packed 128 cuts16466 = true := by
 decide +kernel
def pointBounds16466 : List (Nat × Nat × Nat) := [(2162174976,97490304101561,97490682929306),(2162242560,97490711823212,97491090651217)]
theorem point_links_checked16466 : (cuts16466.take 2).map (fun c => (2162163713-1+2*2^9*c.k,97490236276898+c.lower,97490615104599+c.upper)) = pointBounds16466 := by
 decide +kernel
def cuts16467 : List PrefixCut := [⟨15,93074191,93074249⟩,
⟨81,500249713,500250026⟩,
⟨128,788701384,788701881⟩]
theorem checked16467 : checkPrefixCuts (2^48) 2162294785 9 Manual.Count131072.C016467.packed 128 cuts16467 = true := by
 decide +kernel
def pointBounds16467 : List (Nat × Nat × Nat) := [(2162310144,97491120573515,97491499401779),(2162377728,97491527749037,97491906577556)]
theorem point_links_checked16467 : (cuts16467.take 2).map (fun c => (2162294785-1+2*2^9*c.k,97491027499324+c.lower,97491406327530+c.upper)) = pointBounds16467 := by
 decide +kernel
def cuts16468 : List PrefixCut := [⟨19,118841256,118841332⟩,
⟨85,529505680,529506013⟩,
⟨128,796983830,796984336⟩]
theorem checked16468 : checkPrefixCuts (2^48) 2162425857 9 Manual.Count131072.C016468.packed 128 cuts16468 = true := by
 decide +kernel
def pointBounds16468 : List (Nat × Nat × Nat) := [(2162445312,97491935041964,97492313870743),(2162512896,97492345706388,97492724535424)]
theorem point_links_checked16468 : (cuts16468.take 2).map (fun c => (2162425857-1+2*2^9*c.k,97491816200708+c.lower,97492195029411+c.upper)) = pointBounds16468 := by
 decide +kernel
def cuts16469 : List PrefixCut := [⟨23,141871842,141871934⟩,
⟨89,557456502,557456851⟩,
⟨128,796284842,796285341⟩]
theorem checked16469 : checkPrefixCuts (2^48) 2162556929 9 Manual.Count131072.C016469.packed 128 cuts16469 = true := by
 decide +kernel
def pointBounds16469 : List (Nat × Nat × Nat) := [(2162580480,97492755056380,97493133885681),(2162648064,97493170641040,97493549470598)]
theorem point_links_checked16469 : (cuts16469.take 2).map (fun c => (2162556929-1+2*2^9*c.k,97492613184538+c.lower,97492992013747+c.upper)) = pointBounds16469 := by
 decide +kernel
def cuts16470 : List PrefixCut := [⟨27,167502582,167502688⟩,
⟨93,578245816,578246175⟩,
⟨128,797407740,797408238⟩]
theorem checked16470 : checkPrefixCuts (2^48) 2162688001 9 Manual.Count131072.C016470.packed 128 cuts16470 = true := by
 decide +kernel
def pointBounds16470 : List (Nat × Nat × Nat) := [(2162715648,97493576971962,97493955801776),(2162783232,97493987715196,97494366545263)]
theorem point_links_checked16470 : (cuts16470.take 2).map (fun c => (2162688001-1+2*2^9*c.k,97493409469380+c.lower,97493788299088+c.upper)) = pointBounds16470 := by
 decide +kernel
def cuts16471 : List PrefixCut := [⟨32,197034415,197034539⟩,
⟨99,615299802,615300193⟩,
⟨128,798010195,798010703⟩]
theorem checked16471 : checkPrefixCuts (2^48) 2162819073 9 Manual.Count131072.C016471.packed 128 cuts16471 = true := by
 decide +kernel
def pointBounds16471 : List (Nat × Nat × Nat) := [(2162851840,97494403911535,97494782741865),(2162920448,97494822176922,97495201007519)]
theorem point_links_checked16471 : (cuts16471.take 2).map (fun c => (2162819073-1+2*2^9*c.k,97494206877120+c.lower,97494585707326+c.upper)) = pointBounds16471 := by
 decide +kernel
def cuts16472 : List PrefixCut := [⟨38,232548622,232548775⟩,
⟨105,657424088,657424510⟩,
⟨128,799653480,799653994⟩]
theorem checked16472 : checkPrefixCuts (2^48) 2162950145 9 Manual.Count131072.C016472.packed 128 cuts16472 = true := by
 decide +kernel
def pointBounds16472 : List (Nat × Nat × Nat) := [(2162989056,97495237435937,97495616266804),(2163057664,97495662311403,97496041142539)]
theorem point_links_checked16472 : (cuts16472.take 2).map (fun c => (2162950145-1+2*2^9*c.k,97495004887315+c.lower,97495383718029+c.upper)) = pointBounds16472 := by
 decide +kernel
def cuts16473 : List PrefixCut := [⟨44,268058445,268058616⟩,
⟨111,672868165,672868600⟩,
⟨128,776573369,776573868⟩]
theorem checked16473 : checkPrefixCuts (2^48) 2163081217 9 Manual.Count131072.C016473.packed 128 cuts16473 = true := by
 decide +kernel
def pointBounds16473 : List (Nat × Nat × Nat) := [(2163126272,97496072599240,97496451430639),(2163194880,97496477408960,97496856240623)]
theorem point_links_checked16473 : (cuts16473.take 2).map (fun c => (2163081217-1+2*2^9*c.k,97495804540795+c.lower,97496183372023+c.upper)) = pointBounds16473 := by
 decide +kernel
def cuts16474 : List PrefixCut := [⟨50,310069744,310069938⟩,
⟨117,722660628,722661083⟩,
⟨128,788887323,788887820⟩]
theorem checked16474 : checkPrefixCuts (2^48) 2163212289 9 Manual.Count131072.C016474.packed 128 cuts16474 = true := by
 decide +kernel
def pointBounds16474 : List (Nat × Nat × Nat) := [(2163263488,97496891183908,97497270015829),(2163332096,97497303774792,97497682606974)]
theorem point_links_checked16474 : (cuts16474.take 2).map (fun c => (2163212289-1+2*2^9*c.k,97496581114164+c.lower,97496959945891+c.upper)) = pointBounds16474 := by
 decide +kernel
def cuts16475 : List PrefixCut := [⟨56,352466190,352466412⟩,
⟨123,764380334,764380815⟩,
⟨128,792742859,792743359⟩]
theorem checked16475 : checkPrefixCuts (2^48) 2163343361 9 Manual.Count131072.C016475.packed 128 cuts16475 = true := by
 decide +kernel
def pointBounds16475 : List (Nat × Nat × Nat) := [(2163400704,97497722467677,97498101300123),(2163469312,97498134381821,97498513214526)]
theorem point_links_checked16475 : (cuts16475.take 2).map (fun c => (2163343361-1+2*2^9*c.k,97497370001487+c.lower,97497748833711+c.upper)) = pointBounds16475 := by
 decide +kernel
def cuts16476 : List PrefixCut := [⟨62,382757916,382758162⟩,
⟨128,795686894,795687399⟩]
theorem checked16476 : checkPrefixCuts (2^48) 2163474433 9 Manual.Count131072.C016476.packed 128 cuts16476 = true := by
 decide +kernel
def pointBounds16476 : List (Nat × Nat × Nat) := [(2163537920,97498545502262,97498924335232)]
theorem point_links_checked16476 : (cuts16476.take 1).map (fun c => (2163474433-1+2*2^9*c.k,97498162744346+c.lower,97498541577070+c.upper)) = pointBounds16476 := by
 decide +kernel
def cuts16477 : List PrefixCut := [⟨1,7155239,7155244⟩,
⟨68,432820039,432820314⟩,
⟨128,808647892,808648404⟩]
theorem checked16477 : checkPrefixCuts (2^48) 2163605505 9 Manual.Count131072.C016477.packed 128 cuts16477 = true := by
 decide +kernel
def pointBounds16477 : List (Nat × Nat × Nat) := [(2163606528,97498965586479,97499344419713),(2163675136,97499391251279,97499770084783)]
theorem point_links_checked16477 : (cuts16477.take 2).map (fun c => (2163605505-1+2*2^9*c.k,97498958431240+c.lower,97499337264469+c.upper)) = pointBounds16477 := by
 decide +kernel
def cuts16478 : List PrefixCut := [⟨7,44359734,44359762⟩,
⟨74,455427955,455428240⟩,
⟨128,786094380,786094876⟩]
theorem checked16478 : checkPrefixCuts (2^48) 2163736577 9 Manual.Count131072.C016478.packed 128 cuts16478 = true := by
 decide +kernel
def pointBounds16478 : List (Nat × Nat × Nat) := [(2163743744,97499811438866,97500190272635),(2163812352,97500222507087,97500601341113)]
theorem point_links_checked16478 : (cuts16478.take 2).map (fun c => (2163736577-1+2*2^9*c.k,97499767079132+c.lower,97500145912873+c.upper)) = pointBounds16478 := by
 decide +kernel
def cuts16479 : List PrefixCut := [⟨13,77657237,77657288⟩,
⟨80,498585393,498585705⟩,
⟨128,792940810,792941311⟩]
theorem checked16479 : checkPrefixCuts (2^48) 2163867649 9 Manual.Count131072.C016479.packed 128 cuts16479 = true := by
 decide +kernel
def pointBounds16479 : List (Nat × Nat × Nat) := [(2163880960,97500630830749,97501009665037),(2163949568,97501051758905,97501430593454)]
theorem point_links_checked16479 : (cuts16479.take 2).map (fun c => (2163867649-1+2*2^9*c.k,97500553173512+c.lower,97500932007749+c.upper)) = pointBounds16479 := by
 decide +kernel
def cuts16480 : List PrefixCut := [⟨19,114332461,114332533⟩,
⟨86,513512346,513512670⟩,
⟨128,774813047,774813533⟩]
theorem checked16480 : checkPrefixCuts (2^48) 2163998721 9 Manual.Count131072.C016480.packed 128 cuts16480 = true := by
 decide +kernel
def pointBounds16480 : List (Nat × Nat × Nat) := [(2164018176,97501460446783,97501839281593),(2164086784,97501859626668,97502238461730)]
theorem point_links_checked16480 : (cuts16480.take 2).map (fun c => (2163998721-1+2*2^9*c.k,97501346114322+c.lower,97501724949060+c.upper)) = pointBounds16480 := by
 decide +kernel
def cuts16481 : List PrefixCut := [⟨25,157116116,157116217⟩,
⟨92,578641145,578641510⟩,
⟨128,798047288,798047790⟩]
theorem checked16481 : checkPrefixCuts (2^48) 2164129793 9 Manual.Count131072.C016481.packed 128 cuts16481 = true := by
 decide +kernel
def pointBounds16481 : List (Nat × Nat × Nat) := [(2164155392,97502278043485,97502656878810),(2164224000,97502699568514,97503078404103)]
theorem point_links_checked16481 : (cuts16481.take 2).map (fun c => (2164129793-1+2*2^9*c.k,97502120927369+c.lower,97502499762593+c.upper)) = pointBounds16481 := by
 decide +kernel
def cuts16482 : List PrefixCut := [⟨31,195212470,195212595⟩,
⟨98,608127284,608127668⟩,
⟨128,793577066,793577567⟩]
theorem checked16482 : checkPrefixCuts (2^48) 2164260865 9 Manual.Count131072.C016482.packed 128 cuts16482 = true := by
 decide +kernel
def pointBounds16482 : List (Nat × Nat × Nat) := [(2164292608,97503114187127,97503493022978),(2164361216,97503527101941,97503905938051)]
theorem point_links_checked16482 : (cuts16482.take 2).map (fun c => (2164260865-1+2*2^9*c.k,97502918974657+c.lower,97503297810383+c.upper)) = pointBounds16482 := by
 decide +kernel
def cuts16483 : List PrefixCut := [⟨37,229662774,229662921⟩,
⟨104,644892331,644892739⟩,
⟨128,793008889,793009390⟩]
theorem checked16483 : checkPrefixCuts (2^48) 2164391937 9 Manual.Count131072.C016483.packed 128 cuts16483 = true := by
 decide +kernel
def pointBounds16483 : List (Nat × Nat × Nat) := [(2164429824,97503942214497,97504321050871),(2164498432,97504357444054,97504736280689)]
theorem point_links_checked16483 : (cuts16483.take 2).map (fun c => (2164391937-1+2*2^9*c.k,97503712551723+c.lower,97504091387950+c.upper)) = pointBounds16483 := by
 decide +kernel
def cuts16484 : List PrefixCut := [⟨43,272301291,272301468⟩,
⟨110,684773746,684774180⟩,
⟨128,793481194,793481699⟩]
theorem checked16484 : checkPrefixCuts (2^48) 2164523009 9 Manual.Count131072.C016484.packed 128 cuts16484 = true := by
 decide +kernel
def pointBounds16484 : List (Nat × Nat × Nat) := [(2164567040,97504777861903,97505156698808),(2164635648,97505190334358,97505569171520)]
theorem point_links_checked16484 : (cuts16484.take 2).map (fun c => (2164523009-1+2*2^9*c.k,97504505560612+c.lower,97504884397340+c.upper)) = pointBounds16484 := by
 decide +kernel
def cuts16485 : List PrefixCut := [⟨49,303491789,303491982⟩,
⟨116,720749041,720749502⟩,
⟨128,795383252,795383759⟩]
theorem checked16485 : checkPrefixCuts (2^48) 2164654081 9 Manual.Count131072.C016485.packed 128 cuts16485 = true := by
 decide +kernel
def pointBounds16485 : List (Nat × Nat × Nat) := [(2164704256,97505602533595,97505981371021),(2164772864,97506019790847,97506398628541)]
theorem point_links_checked16485 : (cuts16485.take 2).map (fun c => (2164654081-1+2*2^9*c.k,97505299041806+c.lower,97505677879039+c.upper)) = pointBounds16485 := by
 decide +kernel
def cuts16486 : List PrefixCut := [⟨55,340659455,340659674⟩,
⟨122,758670374,758670855⟩,
⟨128,791824635,791825138⟩]
theorem checked16486 : checkPrefixCuts (2^48) 2164785153 9 Manual.Count131072.C016486.packed 128 cuts16486 = true := by
 decide +kernel
def pointBounds16486 : List (Nat × Nat × Nat) := [(2164841472,97506435084513,97506813922472),(2164910080,97506853095432,97507231933653)]
theorem point_links_checked16486 : (cuts16486.take 2).map (fun c => (2164785153-1+2*2^9*c.k,97506094425058+c.lower,97506473262798+c.upper)) = pointBounds16486 := by
 decide +kernel
def cuts16487 : List PrefixCut := [⟨61,376782470,376782708⟩,
⟨128,790216454,790216960⟩]
theorem checked16487 : checkPrefixCuts (2^48) 2164916225 9 Manual.Count131072.C016487.packed 128 cuts16487 = true := by
 decide +kernel
def pointBounds16487 : List (Nat × Nat × Nat) := [(2164978688,97507263032163,97507641870644),(2165047296,97507676466147,97508055304896)]
theorem point_links_checked16487 : (cuts16487.take 2).map (fun c => (2164916225-1+2*2^9*c.k,97506886249693+c.lower,97507265087936+c.upper)) = pointBounds16487 := by
 decide +kernel
def cuts16488 : List PrefixCut := [⟨67,420311267,420311532⟩,
⟨128,790428813,790429311⟩]
theorem checked16488 : checkPrefixCuts (2^48) 2165047297 9 Manual.Count131072.C016488.packed 128 cuts16488 = true := by
 decide +kernel
def pointBounds16488 : List (Nat × Nat × Nat) := [(2165115904,97508096777414,97508475616428)]
theorem point_links_checked16488 : (cuts16488.take 1).map (fun c => (2165047297-1+2*2^9*c.k,97507676466147+c.lower,97508055304896+c.upper)) = pointBounds16488 := by
 decide +kernel
def cuts16489 : List PrefixCut := [⟨6,37310173,37310196⟩,
⟨73,450964918,450965206⟩,
⟨128,794020620,794021128⟩]
theorem checked16489 : checkPrefixCuts (2^48) 2165178369 9 Manual.Count131072.C016489.packed 128 cuts16489 = true := by
 decide +kernel
def pointBounds16489 : List (Nat × Nat × Nat) := [(2165184512,97508504205133,97508883044403),(2165253120,97508917859878,97509296699413)]
theorem point_links_checked16489 : (cuts16489.take 2).map (fun c => (2165178369-1+2*2^9*c.k,97508466894960+c.lower,97508845734207+c.upper)) = pointBounds16489 := by
 decide +kernel
def cuts16490 : List PrefixCut := [⟨12,71495899,71495945⟩,
⟨79,490194053,490194372⟩,
⟨128,792022791,792023301⟩]
theorem checked16490 : checkPrefixCuts (2^48) 2165309441 9 Manual.Count131072.C016490.packed 128 cuts16490 = true := by
 decide +kernel
def pointBounds16490 : List (Nat × Nat × Nat) := [(2165321728,97509332411479,97509711251280),(2165390336,97509751109633,97510129949707)]
theorem point_links_checked16490 : (cuts16490.take 2).map (fun c => (2165309441-1+2*2^9*c.k,97509260915580+c.lower,97509639755335+c.upper)) = pointBounds16490 := by
 decide +kernel
def cuts16491 : List PrefixCut := [⟨18,111786661,111786733⟩,
⟨85,528898525,528898859⟩,
⟨128,799773717,799774224⟩]
theorem checked16491 : checkPrefixCuts (2^48) 2165440513 9 Manual.Count131072.C016491.packed 128 cuts16491 = true := by
 decide +kernel
def pointBounds16491 : List (Nat × Nat × Nat) := [(2165458944,97510164725032,97510543565369),(2165527552,97510581836896,97510960677495)]
theorem point_links_checked16491 : (cuts16491.take 2).map (fun c => (2165440513-1+2*2^9*c.k,97510052938371+c.lower,97510431778636+c.upper)) = pointBounds16491 := by
 decide +kernel
def cuts16492 : List PrefixCut := [⟨24,153242236,153242334⟩,
⟨91,557330299,557330657⟩,
⟨128,782699040,782699540⟩]
theorem checked16492 : checkPrefixCuts (2^48) 2165571585 9 Manual.Count131072.C016492.packed 128 cuts16492 = true := by
 decide +kernel
def pointBounds16492 : List (Nat × Nat × Nat) := [(2165596160,97511005954324,97511384795194),(2165664768,97511410042387,97511788883517)]
theorem point_links_checked16492 : (cuts16492.take 2).map (fun c => (2165571585-1+2*2^9*c.k,97510852712088+c.lower,97511231552860+c.upper)) = pointBounds16492 := by
 decide +kernel
def cuts16493 : List PrefixCut := [⟨30,187284432,187284548⟩,
⟨97,600314465,600314849⟩,
⟨128,787590306,787590811⟩]
theorem checked16493 : checkPrefixCuts (2^48) 2165702657 9 Manual.Count131072.C016493.packed 128 cuts16493 = true := by
 decide +kernel
def pointBounds16493 : List (Nat × Nat × Nat) := [(2165733376,97511822695560,97512201536948),(2165801984,97512235725593,97512614567249)]
theorem point_links_checked16493 : (cuts16493.take 2).map (fun c => (2165702657-1+2*2^9*c.k,97511635411128+c.lower,97512014252400+c.upper)) = pointBounds16493 := by
 decide +kernel
def cuts16494 : List PrefixCut := [⟨36,218333389,218333523⟩,
⟨103,639394661,639395062⟩,
⟨128,794950004,794950502⟩]
theorem checked16494 : checkPrefixCuts (2^48) 2165833729 9 Manual.Count131072.C016494.packed 128 cuts16494 = true := by
 decide +kernel
def pointBounds16494 : List (Nat × Nat × Nat) := [(2165870592,97512641334823,97513020176734),(2165939200,97513062396095,97513441238273)]
theorem point_links_checked16494 : (cuts16494.take 2).map (fun c => (2165833729-1+2*2^9*c.k,97512423001434+c.lower,97512801843211+c.upper)) = pointBounds16494 := by
 decide +kernel
def cuts16495 : List PrefixCut := [⟨42,265102693,265102861⟩,
⟨109,685097658,685098089⟩,
⟨128,799320444,799320946⟩]
theorem checked16495 : checkPrefixCuts (2^48) 2165964801 9 Manual.Count131072.C016495.packed 128 cuts16495 = true := by
 decide +kernel
def pointBounds16495 : List (Nat × Nat × Nat) := [(2166007808,97513483054131,97513861896574),(2166076416,97513903049096,97514281891802)]
theorem point_links_checked16495 : (cuts16495.take 2).map (fun c => (2165964801-1+2*2^9*c.k,97513217951438+c.lower,97513596793713+c.upper)) = pointBounds16495 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000202
