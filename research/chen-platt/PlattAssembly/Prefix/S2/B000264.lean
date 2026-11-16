import PlattAssemblyKernel
import PlattCertificates.Count131072.C018448
import PlattCertificates.Count131072.C018449
import PlattCertificates.Count131072.C018450
import PlattCertificates.Count131072.C018451
import PlattCertificates.Count131072.C018452
import PlattCertificates.Count131072.C018453
import PlattCertificates.Count131072.C018454
import PlattCertificates.Count131072.C018455
import PlattCertificates.Count131072.C018456
import PlattCertificates.Count131072.C018457
import PlattCertificates.Count131072.C018458
import PlattCertificates.Count131072.C018459
import PlattCertificates.Count131072.C018460
import PlattCertificates.Count131072.C018461
import PlattCertificates.Count131072.C018462
import PlattCertificates.Count131072.C018463
import PlattCertificates.Count131072.C018464
import PlattCertificates.Count131072.C018465
import PlattCertificates.Count131072.C018466
import PlattCertificates.Count131072.C018467
import PlattCertificates.Count131072.C018468
import PlattCertificates.Count131072.C018469
import PlattCertificates.Count131072.C018470
import PlattCertificates.Count131072.C018471
import PlattCertificates.Count131072.C018472
import PlattCertificates.Count131072.C018473
import PlattCertificates.Count131072.C018474
import PlattCertificates.Count131072.C018475
import PlattCertificates.Count131072.C018476
import PlattCertificates.Count131072.C018477
import PlattCertificates.Count131072.C018478
import PlattCertificates.Count131072.C018479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000264
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18448 : List PrefixCut := [⟨22,121447614,121447688⟩,
⟨96,525761196,525761514⟩,
⟨128,706820824,706821251⟩]
theorem checked18448 : checkPrefixCuts (2^48) 2421948417 9 Manual.Count131072.C018448.packed 128 cuts18448 = true := by
 decide +kernel
def pointBounds18448 : List (Nat × Nat × Nat) := [(2421970944,98972203749520,98972583494362),(2422046720,98972608063102,98972987808188)]
theorem point_links_checked18448 : (cuts18448.take 2).map (fun c => (2421948417-1+2*2^9*c.k,98972082301906+c.lower,98972462046674+c.upper)) = pointBounds18448 := by
 decide +kernel
def cuts18449 : List PrefixCut := [⟨42,232886929,232887072⟩,
⟨116,637640073,637640460⟩,
⟨128,706317872,706318299⟩]
theorem checked18449 : checkPrefixCuts (2^48) 2422079489 9 Manual.Count131072.C018449.packed 128 cuts18449 = true := by
 decide +kernel
def pointBounds18449 : List (Nat × Nat × Nat) := [(2422122496,98973022009659,98973401754997),(2422198272,98973426762803,98973806508385)]
theorem point_links_checked18449 : (cuts18449.take 2).map (fun c => (2422079489-1+2*2^9*c.k,98972789122730+c.lower,98973168867925+c.upper)) = pointBounds18449 := by
 decide +kernel
def cuts18450 : List PrefixCut := [⟨62,335133133,335133337⟩,
⟨128,701399135,701399556⟩]
theorem checked18450 : checkPrefixCuts (2^48) 2422210561 9 Manual.Count131072.C018450.packed 128 cuts18450 = true := by
 decide +kernel
def pointBounds18450 : List (Nat × Nat × Nat) := [(2422274048,98973830573735,98974210319561)]
theorem point_links_checked18450 : (cuts18450.take 1).map (fun c => (2422210561-1+2*2^9*c.k,98973495440602+c.lower,98973875186224+c.upper)) = pointBounds18450 := by
 decide +kernel
def cuts18451 : List PrefixCut := [⟨8,43923338,43923365⟩,
⟨82,450265371,450265645⟩,
⟨128,705428153,705428579⟩]
theorem checked18451 : checkPrefixCuts (2^48) 2422341633 9 Manual.Count131072.C018451.packed 128 cuts18451 = true := by
 decide +kernel
def pointBounds18451 : List (Nat × Nat × Nat) := [(2422349824,98974240763075,98974620509145),(2422425600,98974647105108,98975026851425)]
theorem point_links_checked18451 : (cuts18451.take 2).map (fun c => (2422341633-1+2*2^9*c.k,98974196839737+c.lower,98974576585780+c.upper)) = pointBounds18451 := by
 decide +kernel
def cuts18452 : List PrefixCut := [⟨28,155117027,155117123⟩,
⟨102,555043065,555043404⟩,
⟨128,701555570,701555996⟩]
theorem checked18452 : checkPrefixCuts (2^48) 2422472705 9 Manual.Count131072.C018452.packed 128 cuts18452 = true := by
 decide +kernel
def pointBounds18452 : List (Nat × Nat × Nat) := [(2422501376,98975057384917,98975437131482),(2422577152,98975457310955,98975837057763)]
theorem point_links_checked18452 : (cuts18452.take 2).map (fun c => (2422472705-1+2*2^9*c.k,98974902267890+c.lower,98975282014359+c.upper)) = pointBounds18452 := by
 decide +kernel
def cuts18453 : List PrefixCut := [⟨48,269202411,269202574⟩,
⟨122,676655346,676655757⟩,
⟨128,708372702,708373132⟩]
theorem checked18453 : checkPrefixCuts (2^48) 2422603777 9 Manual.Count131072.C018453.packed 128 cuts18453 = true := by
 decide +kernel
def pointBounds18453 : List (Nat × Nat × Nat) := [(2422652928,98975873025871,98976252772929),(2422728704,98976280478806,98976660226112)]
theorem point_links_checked18453 : (cuts18453.take 2).map (fun c => (2422603777-1+2*2^9*c.k,98975603823460+c.lower,98975983570355+c.upper)) = pointBounds18453 := by
 decide +kernel
def cuts18454 : List PrefixCut := [⟨68,381647936,381648168⟩,
⟨128,709263804,709264234⟩]
theorem checked18454 : checkPrefixCuts (2^48) 2422734849 9 Manual.Count131072.C018454.packed 128 cuts18454 = true := by
 decide +kernel
def pointBounds18454 : List (Nat × Nat × Nat) := [(2422804480,98976693844098,98977073591655)]
theorem point_links_checked18454 : (cuts18454.take 1).map (fun c => (2422734849-1+2*2^9*c.k,98976312196162+c.lower,98976691943487+c.upper)) = pointBounds18454 := by
 decide +kernel
def cuts18455 : List PrefixCut := [⟨14,76674850,76674897⟩,
⟨88,478048538,478048826⟩,
⟨128,700396109,700396533⟩]
theorem checked18455 : checkPrefixCuts (2^48) 2422865921 9 Manual.Count131072.C018455.packed 128 cuts18455 = true := by
 decide +kernel
def pointBounds18455 : List (Nat × Nat × Nat) := [(2422880256,98977098134816,98977477882618),(2422956032,98977499508504,98977879256547)]
theorem point_links_checked18455 : (cuts18455.take 2).map (fun c => (2422865921-1+2*2^9*c.k,98977021459966+c.lower,98977401207721+c.upper)) = pointBounds18455 := by
 decide +kernel
def cuts18456 : List PrefixCut := [⟨34,187377796,187377909⟩,
⟨108,598832794,598833154⟩,
⟨128,710697067,710697495⟩]
theorem checked18456 : checkPrefixCuts (2^48) 2422996993 9 Manual.Count131072.C018456.packed 128 cuts18456 = true := by
 decide +kernel
def pointBounds18456 : List (Nat × Nat × Nat) := [(2423031808,98977909233871,98978288982163),(2423107584,98978320688869,98978700437408)]
theorem point_links_checked18456 : (cuts18456.take 2).map (fun c => (2422996993-1+2*2^9*c.k,98977721856075+c.lower,98978101604254+c.upper)) = pointBounds18456 := by
 decide +kernel
def cuts18457 : List PrefixCut := [⟨54,302830312,302830494⟩,
⟨128,702759976,702760402⟩]
theorem checked18457 : checkPrefixCuts (2^48) 2423128065 9 Manual.Count131072.C018457.packed 128 cuts18457 = true := by
 decide +kernel
def pointBounds18457 : List (Nat × Nat × Nat) := [(2423183360,98978735383454,98979115132243),(2423259136,98979135313118,98979515062151)]
theorem point_links_checked18457 : (cuts18457.take 2).map (fun c => (2423128065-1+2*2^9*c.k,98978432553142+c.lower,98978812301749+c.upper)) = pointBounds18457 := by
 decide +kernel
def cuts18458 : List PrefixCut := [⟨74,413971812,413972058⟩,
⟨128,711665644,711666071⟩]
theorem checked18458 : checkPrefixCuts (2^48) 2423259137 9 Manual.Count131072.C018458.packed 128 cuts18458 = true := by
 decide +kernel
def pointBounds18458 : List (Nat × Nat × Nat) := [(2423334912,98979549284930,98979929034209)]
theorem point_links_checked18458 : (cuts18458.take 1).map (fun c => (2423259137-1+2*2^9*c.k,98979135313118+c.lower,98979515062151+c.upper)) = pointBounds18458 := by
 decide +kernel
def cuts18459 : List PrefixCut := [⟨20,112780428,112780492⟩,
⟨94,527655476,527655793⟩,
⟨128,716737556,716737987⟩]
theorem checked18459 : checkPrefixCuts (2^48) 2423390209 9 Manual.Count131072.C018459.packed 128 cuts18459 = true := by
 decide +kernel
def pointBounds18459 : List (Nat × Nat × Nat) := [(2423410688,98979959759190,98980339508714),(2423486464,98980374634238,98980754384015)]
theorem point_links_checked18459 : (cuts18459.take 2).map (fun c => (2423390209-1+2*2^9*c.k,98979846978762+c.lower,98980226728222+c.upper)) = pointBounds18459 := by
 decide +kernel
def cuts18460 : List PrefixCut := [⟨40,219740628,219740754⟩,
⟨114,628202215,628202585⟩,
⟨128,708336753,708337173⟩]
theorem checked18460 : checkPrefixCuts (2^48) 2423521281 9 Manual.Count131072.C018460.packed 128 cuts18460 = true := by
 decide +kernel
def pointBounds18460 : List (Nat × Nat × Nat) := [(2423562240,98980783456946,98981163206963),(2423638016,98981191918533,98981571668794)]
theorem point_links_checked18460 : (cuts18460.take 2).map (fun c => (2423521281-1+2*2^9*c.k,98980563716318+c.lower,98980943466209+c.upper)) = pointBounds18460 := by
 decide +kernel
def cuts18461 : List PrefixCut := [⟨60,330636848,330637048⟩,
⟨128,702491603,702492027⟩]
theorem checked18461 : checkPrefixCuts (2^48) 2423652353 9 Manual.Count131072.C018461.packed 128 cuts18461 = true := by
 decide +kernel
def pointBounds18461 : List (Nat × Nat × Nat) := [(2423713792,98981602689919,98981982440430)]
theorem point_links_checked18461 : (cuts18461.take 1).map (fun c => (2423652353-1+2*2^9*c.k,98981272053071+c.lower,98981651803382+c.upper)) = pointBounds18461 := by
 decide +kernel
def cuts18462 : List PrefixCut := [⟨6,30542253,30542273⟩,
⟨80,443029848,443030115⟩,
⟨128,703034344,703034769⟩]
theorem checked18462 : checkPrefixCuts (2^48) 2423783425 9 Manual.Count131072.C018462.packed 128 cuts18462 = true := by
 decide +kernel
def pointBounds18462 : List (Nat × Nat × Nat) := [(2423789568,98982005086927,98982384837682),(2423865344,98982417574522,98982797325524)]
theorem point_links_checked18462 : (cuts18462.take 2).map (fun c => (2423783425-1+2*2^9*c.k,98981974544674+c.lower,98982354295409+c.upper)) = pointBounds18462 := by
 decide +kernel
def cuts18463 : List PrefixCut := [⟨26,145502707,145502796⟩,
⟨100,548790922,548791254⟩,
⟨128,701022300,701022722⟩]
theorem checked18463 : checkPrefixCuts (2^48) 2423914497 9 Manual.Count131072.C018463.packed 128 cuts18463 = true := by
 decide +kernel
def pointBounds18463 : List (Nat × Nat × Nat) := [(2423941120,98982823081725,98983202832974),(2424016896,98983226369940,98983606121432)]
theorem point_links_checked18463 : (cuts18463.take 2).map (fun c => (2423914497-1+2*2^9*c.k,98982677579018+c.lower,98983057330178+c.upper)) = pointBounds18463 := by
 decide +kernel
def cuts18464 : List PrefixCut := [⟨46,251857114,251857266⟩,
⟨120,654887880,654888271⟩,
⟨128,698545892,698546309⟩]
theorem checked18464 : checkPrefixCuts (2^48) 2424045569 9 Manual.Count131072.C018464.packed 128 cuts18464 = true := by
 decide +kernel
def pointBounds18464 : List (Nat × Nat × Nat) := [(2424092672,98983630458432,98984010210166),(2424168448,98984033489198,98984413241171)]
theorem point_links_checked18464 : (cuts18464.take 2).map (fun c => (2424045569-1+2*2^9*c.k,98983378601318+c.lower,98983758352900+c.upper)) = pointBounds18464 := by
 decide +kernel
def cuts18465 : List PrefixCut := [⟨66,363888503,363888724⟩,
⟨128,702107587,702108018⟩]
theorem checked18465 : checkPrefixCuts (2^48) 2424176641 9 Manual.Count131072.C018465.packed 128 cuts18465 = true := by
 decide +kernel
def pointBounds18465 : List (Nat × Nat × Nat) := [(2424244224,98984441035713,98984820787933)]
theorem point_links_checked18465 : (cuts18465.take 1).map (fun c => (2424176641-1+2*2^9*c.k,98984077147210+c.lower,98984456899209+c.upper)) = pointBounds18465 := by
 decide +kernel
def cuts18466 : List PrefixCut := [⟨12,66063728,66063767⟩,
⟨86,476139041,476139325⟩,
⟨128,706945891,706946317⟩]
theorem checked18466 : checkPrefixCuts (2^48) 2424307713 9 Manual.Count131072.C018466.packed 128 cuts18466 = true := by
 decide +kernel
def pointBounds18466 : List (Nat × Nat × Nat) := [(2424320000,98984845318525,98985225070994),(2424395776,98985255393838,98985635146552)]
theorem point_links_checked18466 : (cuts18466.take 2).map (fun c => (2424307713-1+2*2^9*c.k,98984779254797+c.lower,98985159007227+c.upper)) = pointBounds18466 := by
 decide +kernel
def cuts18467 : List PrefixCut := [⟨32,180416602,180416710⟩,
⟨106,590466279,590466633⟩,
⟨128,712828575,712829003⟩]
theorem checked18467 : checkPrefixCuts (2^48) 2424438785 9 Manual.Count131072.C018467.packed 128 cuts18467 = true := by
 decide +kernel
def pointBounds18467 : List (Nat × Nat × Nat) := [(2424471552,98985666617290,98986046370254),(2424547328,98986076666967,98986456420177)]
theorem point_links_checked18467 : (cuts18467.take 2).map (fun c => (2424438785-1+2*2^9*c.k,98985486200688+c.lower,98985865953544+c.upper)) = pointBounds18467 := by
 decide +kernel
def cuts18468 : List PrefixCut := [⟨52,281869954,281870123⟩,
⟨126,690152642,690153060⟩,
⟨128,701877377,701877802⟩]
theorem checked18468 : checkPrefixCuts (2^48) 2424569857 9 Manual.Count131072.C018468.packed 128 cuts18468 = true := by
 decide +kernel
def pointBounds18468 : List (Nat × Nat × Nat) := [(2424623104,98986480899217,98986860652670),(2424698880,98986889181905,98987268935607)]
theorem point_links_checked18468 : (cuts18468.take 2).map (fun c => (2424569857-1+2*2^9*c.k,98986199029263+c.lower,98986578782547+c.upper)) = pointBounds18468 := by
 decide +kernel
def cuts18469 : List PrefixCut := [⟨72,390741004,390741236⟩,
⟨128,699634027,699634449⟩]
theorem checked18469 : checkPrefixCuts (2^48) 2424700929 9 Manual.Count131072.C018469.packed 128 cuts18469 = true := by
 decide +kernel
def pointBounds18469 : List (Nat × Nat × Nat) := [(2424774656,98987291647644,98987671401585)]
theorem point_links_checked18469 : (cuts18469.take 1).map (fun c => (2424700929-1+2*2^9*c.k,98986900906640+c.lower,98987280660349+c.upper)) = pointBounds18469 := by
 decide +kernel
def cuts18470 : List PrefixCut := [⟨18,98551689,98551748⟩,
⟨92,514109088,514109392⟩,
⟨128,710855831,710856250⟩]
theorem checked18470 : checkPrefixCuts (2^48) 2424832001 9 Manual.Count131072.C018470.packed 128 cuts18470 = true := by
 decide +kernel
def pointBounds18470 : List (Nat × Nat × Nat) := [(2424850432,98987699092356,98988078846546),(2424926208,98988114649755,98988494404190)]
theorem point_links_checked18470 : (cuts18470.take 2).map (fun c => (2424832001-1+2*2^9*c.k,98987600540667+c.lower,98987980294798+c.upper)) = pointBounds18470 := by
 decide +kernel
def cuts18471 : List PrefixCut := [⟨39,215315295,215315425⟩,
⟨114,634676667,634677052⟩,
⟨128,710236908,710237338⟩]
theorem checked18471 : checkPrefixCuts (2^48) 2424963073 9 Manual.Count131072.C018471.packed 128 cuts18471 = true := by
 decide +kernel
def pointBounds18471 : List (Nat × Nat × Nat) := [(2425003008,98988526711793,98988906466473),(2425079808,98988946073165,98989325828100)]
theorem point_links_checked18471 : (cuts18471.take 2).map (fun c => (2424963073-1+2*2^9*c.k,98988311396498+c.lower,98988691151048+c.upper)) = pointBounds18471 := by
 decide +kernel
def cuts18472 : List PrefixCut := [⟨61,339725565,339725769⟩,
⟨128,710546860,710547291⟩]
theorem checked18472 : checkPrefixCuts (2^48) 2425094145 9 Manual.Count131072.C018472.packed 128 cuts18472 = true := by
 decide +kernel
def pointBounds18472 : List (Nat × Nat × Nat) := [(2425156608,98989361358971,98989741114155)]
theorem point_links_checked18472 : (cuts18472.take 1).map (fun c => (2425094145-1+2*2^9*c.k,98989021633406+c.lower,98989401388386+c.upper)) = pointBounds18472 := by
 decide +kernel
def cuts18473 : List PrefixCut := [⟨8,45379906,45379935⟩,
⟨83,461103653,461103932⟩,
⟨128,711552876,711553307⟩]
theorem checked18473 : checkPrefixCuts (2^48) 2425225217 9 Manual.Count131072.C018473.packed 128 cuts18473 = true := by
 decide +kernel
def pointBounds18473 : List (Nat × Nat × Nat) := [(2425233408,98989777560172,98990157315612),(2425310208,98990193283919,98990573039609)]
theorem point_links_checked18473 : (cuts18473.take 2).map (fun c => (2425225217-1+2*2^9*c.k,98989732180266+c.lower,98990111935677+c.upper)) = pointBounds18473 := by
 decide +kernel
def cuts18474 : List PrefixCut := [⟨30,159806836,159806933⟩,
⟨105,572486924,572487267⟩,
⟨128,700837513,700837932⟩]
theorem checked18474 : checkPrefixCuts (2^48) 2425356289 9 Manual.Count131072.C018474.packed 128 cuts18474 = true := by
 decide +kernel
def pointBounds18474 : List (Nat × Nat × Nat) := [(2425387008,98990603539978,98990983295917),(2425463808,98991016220066,98991395976251)]
theorem point_links_checked18474 : (cuts18474.take 2).map (fun c => (2425356289-1+2*2^9*c.k,98990443733142+c.lower,98990823488984+c.upper)) = pointBounds18474 := by
 decide +kernel
def cuts18475 : List PrefixCut := [⟨52,287217562,287217733⟩,
⟨127,691748456,691748873⟩,
⟨128,697086413,697086834⟩]
theorem checked18475 : checkPrefixCuts (2^48) 2425487361 9 Manual.Count131072.C018475.packed 128 cuts18475 = true := by
 decide +kernel
def pointBounds18475 : List (Nat × Nat × Nat) := [(2425540608,98991431788217,98991811544649),(2425617408,98991836319111,98992216075789)]
theorem point_links_checked18475 : (cuts18475.take 2).map (fun c => (2425487361-1+2*2^9*c.k,98991144570655+c.lower,98991524326916+c.upper)) = pointBounds18475 := by
 decide +kernel
def cuts18476 : List PrefixCut := [⟨74,407651048,407651295⟩,
⟨128,703895019,703895445⟩]
theorem checked18476 : checkPrefixCuts (2^48) 2425618433 9 Manual.Count131072.C018476.packed 128 cuts18476 = true := by
 decide +kernel
def pointBounds18476 : List (Nat × Nat × Nat) := [(2425694208,98992249308116,98992629065045)]
theorem point_links_checked18476 : (cuts18476.take 1).map (fun c => (2425618433-1+2*2^9*c.k,98991841657068+c.lower,98992221413750+c.upper)) = pointBounds18476 := by
 decide +kernel
def cuts18477 : List PrefixCut := [⟨21,115223493,115223562⟩,
⟨96,528766520,528766843⟩,
⟨128,705133297,705133732⟩]
theorem checked18477 : checkPrefixCuts (2^48) 2425749505 9 Manual.Count131072.C018477.packed 128 cuts18477 = true := by
 decide +kernel
def pointBounds18477 : List (Nat × Nat × Nat) := [(2425771008,98992660775580,98993040532757),(2425847808,98993074318607,98993454076038)]
theorem point_links_checked18477 : (cuts18477.take 2).map (fun c => (2425749505-1+2*2^9*c.k,98992545552087+c.lower,98992925309195+c.upper)) = pointBounds18477 := by
 decide +kernel
def cuts18478 : List PrefixCut := [⟨43,236350948,236351086⟩,
⟨118,650563917,650564298⟩,
⟨128,707879757,707880171⟩]
theorem checked18478 : checkPrefixCuts (2^48) 2425880577 9 Manual.Count131072.C018478.packed 128 cuts18478 = true := by
 decide +kernel
def pointBounds18478 : List (Nat × Nat × Nat) := [(2425924608,98993487036332,98993866794013),(2426001408,98993901249301,98994281007225)]
theorem point_links_checked18478 : (cuts18478.take 2).map (fun c => (2425880577-1+2*2^9*c.k,98993250685384+c.lower,98993630442927+c.upper)) = pointBounds18478 := by
 decide +kernel
def cuts18479 : List PrefixCut := [⟨65,358160274,358160491⟩,
⟨128,698211960,698212382⟩]
theorem checked18479 : checkPrefixCuts (2^48) 2426011649 9 Manual.Count131072.C018479.packed 128 cuts18479 = true := by
 decide +kernel
def pointBounds18479 : List (Nat × Nat × Nat) := [(2426078208,98994316725415,98994696483589)]
theorem point_links_checked18479 : (cuts18479.take 1).map (fun c => (2426011649-1+2*2^9*c.k,98993958565141+c.lower,98994338323098+c.upper)) = pointBounds18479 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000264
