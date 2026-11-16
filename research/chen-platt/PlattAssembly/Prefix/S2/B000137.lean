import PlattAssemblyKernel
import PlattCertificates.Count131072.C014384
import PlattCertificates.Count131072.C014385
import PlattCertificates.Count131072.C014386
import PlattCertificates.Count131072.C014387
import PlattCertificates.Count131072.C014388
import PlattCertificates.Count131072.C014389
import PlattCertificates.Count131072.C014390
import PlattCertificates.Count131072.C014391
import PlattCertificates.Count131072.C014392
import PlattCertificates.Count131072.C014393
import PlattCertificates.Count131072.C014394
import PlattCertificates.Count131072.C014395
import PlattCertificates.Count131072.C014396
import PlattCertificates.Count131072.C014397
import PlattCertificates.Count131072.C014398
import PlattCertificates.Count131072.C014399
import PlattCertificates.Count131072.C014400
import PlattCertificates.Count131072.C014401
import PlattCertificates.Count131072.C014402
import PlattCertificates.Count131072.C014403
import PlattCertificates.Count131072.C014404
import PlattCertificates.Count131072.C014405
import PlattCertificates.Count131072.C014406
import PlattCertificates.Count131072.C014407
import PlattCertificates.Count131072.C014408
import PlattCertificates.Count131072.C014409
import PlattCertificates.Count131072.C014410
import PlattCertificates.Count131072.C014411
import PlattCertificates.Count131072.C014412
import PlattCertificates.Count131072.C014413
import PlattCertificates.Count131072.C014414
import PlattCertificates.Count131072.C014415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000137
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14384 : List PrefixCut := [⟨48,347877629,347877869⟩,
⟨106,764871769,764872290⟩,
⟨128,915040033,915040656⟩]
theorem checked14384 : checkPrefixCuts (2^48) 1889271809 9 Manual.Count131072.C014384.packed 128 cuts14384 = true := by
 decide +kernel
def pointBounds14384 : List (Nat × Nat × Nat) := [(1889320960,95718202843294,95718580506368),(1889380352,95718619837434,95718997500789)]
theorem point_links_checked14384 : (cuts14384.take 2).map (fun c => (1889271809-1+2*2^9*c.k,95717854965665+c.lower,95718232628499+c.upper)) = pointBounds14384 := by
 decide +kernel
def cuts14385 : List PrefixCut := [⟨36,258321085,258321259⟩,
⟨94,678864298,678864752⟩,
⟨128,922126784,922127407⟩]
theorem checked14385 : checkPrefixCuts (2^48) 1889402881 9 Manual.Count131072.C014385.packed 128 cuts14385 = true := by
 decide +kernel
def pointBounds14385 : List (Nat × Nat × Nat) := [(1889439744,95719028326783,95719405990414),(1889499136,95719448869996,95719826533907)]
theorem point_links_checked14385 : (cuts14385.take 2).map (fun c => (1889402881-1+2*2^9*c.k,95718770005698+c.lower,95719147669155+c.upper)) = pointBounds14385 := by
 decide +kernel
def cuts14386 : List PrefixCut := [⟨24,167733754,167733869⟩,
⟨82,577972291,577972689⟩,
⟨128,907911517,907912137⟩]
theorem checked14386 : checkPrefixCuts (2^48) 1889533953 9 Manual.Count131072.C014386.packed 128 cuts14386 = true := by
 decide +kernel
def pointBounds14386 : List (Nat × Nat × Nat) := [(1889558528,95719859866236,95720237530431),(1889617920,95720270104773,95720647769251)]
theorem point_links_checked14386 : (cuts14386.take 2).map (fun c => (1889533953-1+2*2^9*c.k,95719692132482+c.lower,95720069796562+c.upper)) = pointBounds14386 := by
 decide +kernel
def cuts14387 : List PrefixCut := [⟨12,87287291,87287352⟩,
⟨70,502117525,502117869⟩,
⟨128,915594140,915594764⟩]
theorem checked14387 : checkPrefixCuts (2^48) 1889665025 9 Manual.Count131072.C014387.packed 128 cuts14387 = true := by
 decide +kernel
def pointBounds14387 : List (Nat × Nat × Nat) := [(1889677312,95720687331290,95721064996051),(1889736704,95721102161524,95721479826568),(1889796096,95721515638139,95721893303463)]
theorem point_links_checked14387 : (cuts14387.take 3).map (fun c => (1889665025-1+2*2^9*c.k,95720600043999+c.lower,95720977708699+c.upper)) = pointBounds14387 := by
 decide +kernel
def cuts14388 : List PrefixCut := [⟨58,419421351,419421637⟩,
⟨116,827957023,827957585⟩,
⟨128,913147685,913148306⟩]
theorem checked14388 : checkPrefixCuts (2^48) 1889796097 9 Manual.Count131072.C014388.packed 128 cuts14388 = true := by
 decide +kernel
def pointBounds14388 : List (Nat × Nat × Nat) := [(1889855488,95721935059490,95722312725100),(1889914880,95722343595162,95722721261048)]
theorem point_links_checked14388 : (cuts14388.take 2).map (fun c => (1889796097-1+2*2^9*c.k,95721515638139+c.lower,95721893303463+c.upper)) = pointBounds14388 := by
 decide +kernel
def cuts14389 : List PrefixCut := [⟨46,328544836,328545063⟩,
⟨104,739884492,739884996⟩,
⟨128,912190565,912191185⟩]
theorem checked14389 : checkPrefixCuts (2^48) 1889927169 9 Manual.Count131072.C014389.packed 128 cuts14389 = true := by
 decide +kernel
def pointBounds14389 : List (Nat × Nat × Nat) := [(1889974272,95722757330660,95723134996832),(1890033664,95723168670316,95723546336765)]
theorem point_links_checked14389 : (cuts14389.take 2).map (fun c => (1889927169-1+2*2^9*c.k,95722428785824+c.lower,95722806451769+c.upper)) = pointBounds14389 := by
 decide +kernel
def cuts14390 : List PrefixCut := [⟨34,246317926,246318091⟩,
⟨92,664035219,664035673⟩,
⟨128,920317992,920318616⟩]
theorem checked14390 : checkPrefixCuts (2^48) 1890058241 9 Manual.Count131072.C014390.packed 128 cuts14390 = true := by
 decide +kernel
def pointBounds14390 : List (Nat × Nat × Nat) := [(1890093056,95723587294315,95723964961045),(1890152448,95724005011608,95724382678627)]
theorem point_links_checked14390 : (cuts14390.take 2).map (fun c => (1890058241-1+2*2^9*c.k,95723340976389+c.lower,95723718642954+c.upper)) = pointBounds14390 := by
 decide +kernel
def cuts14391 : List PrefixCut := [⟨22,155464859,155464966⟩,
⟨80,574198268,574198657⟩,
⟨128,907894859,907895475⟩]
theorem checked14391 : checkPrefixCuts (2^48) 1890189313 9 Manual.Count131072.C014391.packed 128 cuts14391 = true := by
 decide +kernel
def pointBounds14391 : List (Nat × Nat × Nat) := [(1890211840,95724416759240,95724794426536),(1890271232,95724835492649,95725213160227)]
theorem point_links_checked14391 : (cuts14391.take 2).map (fun c => (1890189313-1+2*2^9*c.k,95724261294381+c.lower,95724638961570+c.upper)) = pointBounds14391 := by
 decide +kernel
def cuts14392 : List PrefixCut := [⟨10,71324466,71324514⟩,
⟨68,484820047,484820381⟩,
⟨126,903663001,903663618⟩,
⟨128,917510052,917510679⟩]
theorem checked14392 : checkPrefixCuts (2^48) 1890320385 9 Manual.Count131072.C014392.packed 128 cuts14392 = true := by
 decide +kernel
def pointBounds14392 : List (Nat × Nat × Nat) := [(1890330624,95725240513706,95725618181559),(1890390016,95725654009287,95726031677426),(1890449408,95726072852241,95726450520663)]
theorem point_links_checked14392 : (cuts14392.take 3).map (fun c => (1890320385-1+2*2^9*c.k,95725169189240+c.lower,95725546857045+c.upper)) = pointBounds14392 := by
 decide +kernel
def cuts14393 : List PrefixCut := [⟨56,389944642,389944913⟩,
⟨114,798636891,798637439⟩,
⟨128,899877447,899878064⟩]
theorem checked14393 : checkPrefixCuts (2^48) 1890451457 9 Manual.Count131072.C014393.packed 128 cuts14393 = true := by
 decide +kernel
def pointBounds14393 : List (Nat × Nat × Nat) := [(1890508800,95726476643934,95726854312637),(1890568192,95726885336183,95727263005163)]
theorem point_links_checked14393 : (cuts14393.take 2).map (fun c => (1890451457-1+2*2^9*c.k,95726086699292+c.lower,95726464367724+c.upper)) = pointBounds14393 := by
 decide +kernel
def cuts14394 : List PrefixCut := [⟨44,317413977,317414194⟩,
⟨102,728760413,728760909⟩,
⟨128,921700261,921700888⟩]
theorem checked14394 : checkPrefixCuts (2^48) 1890582529 9 Manual.Count131072.C014394.packed 128 cuts14394 = true := by
 decide +kernel
def pointBounds14394 : List (Nat × Nat × Nat) := [(1890627584,95727303990716,95727681659982),(1890686976,95727715337152,95728093006697)]
theorem point_links_checked14394 : (cuts14394.take 2).map (fun c => (1890582529-1+2*2^9*c.k,95726986576739+c.lower,95727364245788+c.upper)) = pointBounds14394 := by
 decide +kernel
def cuts14395 : List PrefixCut := [⟨32,225986204,225986357⟩,
⟨90,642517165,642517601⟩,
⟨128,910322618,910323235⟩]
theorem checked14395 : checkPrefixCuts (2^48) 1890713601 9 Manual.Count131072.C014395.packed 128 cuts14395 = true := by
 decide +kernel
def pointBounds14395 : List (Nat × Nat × Nat) := [(1890746368,95728134263204,95728511933033),(1890805760,95728550794165,95728928464277)]
theorem point_links_checked14395 : (cuts14395.take 2).map (fun c => (1890713601-1+2*2^9*c.k,95727908277000+c.lower,95728285946676+c.upper)) = pointBounds14395 := by
 decide +kernel
def cuts14396 : List PrefixCut := [⟨20,147521408,147521505⟩,
⟨78,559411597,559411978⟩,
⟨128,909515470,909516091⟩]
theorem checked14396 : checkPrefixCuts (2^48) 1890844673 9 Manual.Count131072.C014396.packed 128 cuts14396 = true := by
 decide +kernel
def pointBounds14396 : List (Nat × Nat × Nat) := [(1890865152,95728966121026,95729343791416),(1890924544,95729378011215,95729755681889)]
theorem point_links_checked14396 : (cuts14396.take 2).map (fun c => (1890844673-1+2*2^9*c.k,95728818599618+c.lower,95729196269911+c.upper)) = pointBounds14396 := by
 decide +kernel
def cuts14397 : List PrefixCut := [⟨8,56712362,56712400⟩,
⟨66,465599639,465599955⟩,
⟨124,881320861,881321456⟩,
⟨128,911982213,911982828⟩]
theorem checked14397 : checkPrefixCuts (2^48) 1890975745 9 Manual.Count131072.C014397.packed 128 cuts14397 = true := by
 decide +kernel
def pointBounds14397 : List (Nat × Nat × Nat) := [(1890983936,95729784827450,95730162498402),(1891043328,95730193714727,95730571385957),(1891102720,95730609435949,95730987107458)]
theorem point_links_checked14397 : (cuts14397.take 3).map (fun c => (1890975745-1+2*2^9*c.k,95729728115088+c.lower,95730105786002+c.upper)) = pointBounds14397 := by
 decide +kernel
def cuts14398 : List PrefixCut := [⟨54,382219121,382219384⟩,
⟨112,798211891,798212435⟩,
⟨128,913854103,913854725⟩]
theorem checked14398 : checkPrefixCuts (2^48) 1891106817 9 Manual.Count131072.C014398.packed 128 cuts14398 = true := by
 decide +kernel
def pointBounds14398 : List (Nat × Nat × Nat) := [(1891162112,95731022316422,95731399988214),(1891221504,95731438309192,95731815981265)]
theorem point_links_checked14398 : (cuts14398.take 2).map (fun c => (1891106817-1+2*2^9*c.k,95730640097301+c.lower,95731017768830+c.upper)) = pointBounds14398 := by
 decide +kernel
def cuts14399 : List PrefixCut := [⟨42,293789085,293789286⟩,
⟨100,710499943,710500426⟩,
⟨128,914088232,914088853⟩]
theorem checked14399 : checkPrefixCuts (2^48) 1891237889 9 Manual.Count131072.C014399.packed 128 cuts14399 = true := by
 decide +kernel
def pointBounds14399 : List (Nat × Nat × Nat) := [(1891280896,95731847740489,95732225412841),(1891340288,95732264451347,95732642123981)]
theorem point_links_checked14399 : (cuts14399.take 2).map (fun c => (1891237889-1+2*2^9*c.k,95731553951404+c.lower,95731931623555+c.upper)) = pointBounds14399 := by
 decide +kernel
def cuts14400 : List PrefixCut := [⟨30,208793772,208793915⟩,
⟨88,612977949,612978365⟩,
⟨128,897953012,897953618⟩]
theorem checked14400 : checkPrefixCuts (2^48) 1891368961 9 Manual.Count131072.C014400.packed 128 cuts14400 = true := by
 decide +kernel
def pointBounds14400 : List (Nat × Nat × Nat) := [(1891399680,95732676833408,95733054506323),(1891459072,95733081017585,95733458690773)]
theorem point_links_checked14400 : (cuts14400.take 2).map (fun c => (1891368961-1+2*2^9*c.k,95732468039636+c.lower,95732845712408+c.upper)) = pointBounds14400 := by
 decide +kernel
def cuts14401 : List PrefixCut := [⟨18,130357266,130357352⟩,
⟨76,534962411,534962777⟩,
⟨128,913812725,913813353⟩]
theorem checked14401 : checkPrefixCuts (2^48) 1891500033 9 Manual.Count131072.C014401.packed 128 cuts14401 = true := by
 decide +kernel
def pointBounds14401 : List (Nat × Nat × Nat) := [(1891518464,95733496349914,95733874023378),(1891577856,95733900955059,95734278628803)]
theorem point_links_checked14401 : (cuts14401.take 2).map (fun c => (1891500033-1+2*2^9*c.k,95733365992648+c.lower,95733743666026+c.upper)) = pointBounds14401 := by
 decide +kernel
def cuts14402 : List PrefixCut := [⟨6,45830351,45830381⟩,
⟨64,468414630,468414944⟩,
⟨122,882206846,882207445⟩,
⟨128,925355953,925356581⟩]
theorem checked14402 : checkPrefixCuts (2^48) 1891631105 9 Manual.Count131072.C014402.packed 128 cuts14402 = true := by
 decide +kernel
def pointBounds14402 : List (Nat × Nat × Nat) := [(1891637248,95734325635724,95734703309760),(1891696640,95734748220003,95735125894323),(1891756032,95735162012219,95735539686824)]
theorem point_links_checked14402 : (cuts14402.take 3).map (fun c => (1891631105-1+2*2^9*c.k,95734279805373+c.lower,95734657479379+c.upper)) = pointBounds14402 := by
 decide +kernel
def cuts14403 : List PrefixCut := [⟨52,369291006,369291259⟩,
⟨110,774427796,774428323⟩,
⟨128,896427561,896428170⟩]
theorem checked14403 : checkPrefixCuts (2^48) 1891762177 9 Manual.Count131072.C014403.packed 128 cuts14403 = true := by
 decide +kernel
def pointBounds14403 : List (Nat × Nat × Nat) := [(1891815424,95735574452332,95735952127219),(1891874816,95735979589122,95736357264283)]
theorem point_links_checked14403 : (cuts14403.take 2).map (fun c => (1891762177-1+2*2^9*c.k,95735205161326+c.lower,95735582835960+c.upper)) = pointBounds14403 := by
 decide +kernel
def cuts14404 : List PrefixCut := [⟨40,296514317,296514514⟩,
⟨98,710105798,710106279⟩,
⟨128,925525322,925525952⟩]
theorem checked14404 : checkPrefixCuts (2^48) 1891893249 9 Manual.Count131072.C014404.packed 128 cuts14404 = true := by
 decide +kernel
def pointBounds14404 : List (Nat × Nat × Nat) := [(1891934208,95736398103204,95736775778644),(1891993600,95736811694685,95737189370409)]
theorem point_links_checked14404 : (cuts14404.take 2).map (fun c => (1891893249-1+2*2^9*c.k,95736101588887+c.lower,95736479264130+c.upper)) = pointBounds14404 := by
 decide +kernel
def cuts14405 : List PrefixCut := [⟨28,197712739,197712873⟩,
⟨86,627196098,627196524⟩,
⟨128,931708946,931709577⟩]
theorem checked14405 : checkPrefixCuts (2^48) 1892024321 9 Manual.Count131072.C014405.packed 128 cuts14405 = true := by
 decide +kernel
def pointBounds14405 : List (Nat × Nat × Nat) := [(1892052992,95737224826948,95737602502955),(1892112384,95737654310307,95738031986606)]
theorem point_links_checked14405 : (cuts14405.take 2).map (fun c => (1892024321-1+2*2^9*c.k,95737027114209+c.lower,95737404790082+c.upper)) = pointBounds14405 := by
 decide +kernel
def cuts14406 : List PrefixCut := [⟨16,109932309,109932384⟩,
⟨74,519306743,519307099⟩,
⟨128,907694934,907695552⟩]
theorem checked14406 : checkPrefixCuts (2^48) 1892155393 9 Manual.Count131072.C014406.packed 128 cuts14406 = true := by
 decide +kernel
def pointBounds14406 : List (Nat × Nat × Nat) := [(1892171776,95738068755464,95738446432043),(1892231168,95738478129898,95738855806758)]
theorem point_links_checked14406 : (cuts14406.take 2).map (fun c => (1892155393-1+2*2^9*c.k,95737958823155+c.lower,95738336499659+c.upper)) = pointBounds14406 := by
 decide +kernel
def cuts14407 : List PrefixCut := [⟨4,32278402,32278424⟩,
⟨62,450403170,450403478⟩,
⟨120,864052568,864053154⟩,
⟨128,918342149,918342771⟩]
theorem checked14407 : checkPrefixCuts (2^48) 1892286465 9 Manual.Count131072.C014407.packed 128 cuts14407 = true := by
 decide +kernel
def pointBounds14407 : List (Nat × Nat × Nat) := [(1892290560,95738898796491,95739276473635),(1892349952,95739316921259,95739694598689),(1892409344,95739730570657,95740108248365)]
theorem point_links_checked14407 : (cuts14407.take 3).map (fun c => (1892286465-1+2*2^9*c.k,95738866518089+c.lower,95739244195211+c.upper)) = pointBounds14407 := by
 decide +kernel
def cuts14408 : List PrefixCut := [⟨50,359197964,359198212⟩,
⟨108,768061962,768062490⟩,
⟨128,911585220,911585848⟩]
theorem checked14408 : checkPrefixCuts (2^48) 1892417537 9 Manual.Count131072.C014408.packed 128 cuts14408 = true := by
 decide +kernel
def pointBounds14408 : List (Nat × Nat × Nat) := [(1892468736,95740144058202,95740521736194),(1892528128,95740552922200,95740930600472)]
theorem point_links_checked14408 : (cuts14408.take 2).map (fun c => (1892417537-1+2*2^9*c.k,95739784860238+c.lower,95740162537982+c.upper)) = pointBounds14408 := by
 decide +kernel
def cuts14409 : List PrefixCut := [⟨38,275887510,275887696⟩,
⟨96,693946574,693947048⟩,
⟨128,920445548,920446175⟩]
theorem checked14409 : checkPrefixCuts (2^48) 1892548609 9 Manual.Count131072.C014409.packed 128 cuts14409 = true := by
 decide +kernel
def pointBounds14409 : List (Nat × Nat × Nat) := [(1892587520,95740972332968,95741350011526),(1892646912,95741390392032,95741768070878)]
theorem point_links_checked14409 : (cuts14409.take 2).map (fun c => (1892548609-1+2*2^9*c.k,95740696445458+c.lower,95741074123830+c.upper)) = pointBounds14409 := by
 decide +kernel
def cuts14410 : List PrefixCut := [⟨26,183516267,183516394⟩,
⟨84,595600573,595600978⟩,
⟨128,906848753,906849373⟩]
theorem checked14410 : checkPrefixCuts (2^48) 1892679681 9 Manual.Count131072.C014410.packed 128 cuts14410 = true := by
 decide +kernel
def pointBounds14410 : List (Nat × Nat × Nat) := [(1892706304,95741800407273,95742178086399),(1892765696,95742212491579,95742590170983)]
theorem point_links_checked14410 : (cuts14410.take 2).map (fun c => (1892679681-1+2*2^9*c.k,95741616891006+c.lower,95741994570005+c.upper)) = pointBounds14410 := by
 decide +kernel
def cuts14411 : List PrefixCut := [⟨14,104243474,104243541⟩,
⟨72,516748076,516748428⟩,
⟨128,908273354,908273976⟩]
theorem checked14411 : checkPrefixCuts (2^48) 1892810753 9 Manual.Count131072.C014411.packed 128 cuts14411 = true := by
 decide +kernel
def pointBounds14411 : List (Nat × Nat × Nat) := [(1892825088,95742627983233,95743005662919),(1892884480,95743040487835,95743418167806)]
theorem point_links_checked14411 : (cuts14411.take 2).map (fun c => (1892810753-1+2*2^9*c.k,95742523739759+c.lower,95742901419378+c.upper)) = pointBounds14411 := by
 decide +kernel
def cuts14412 : List PrefixCut := [⟨2,14869698,14869708⟩,
⟨60,430322314,430322609⟩,
⟨118,838773473,838774045⟩,
⟨128,911778873,911779494⟩]
theorem checked14412 : checkPrefixCuts (2^48) 1892941825 9 Manual.Count131072.C014412.packed 128 cuts14412 = true := by
 decide +kernel
def pointBounds14412 : List (Nat × Nat × Nat) := [(1892943872,95743446882811,95743824563062),(1893003264,95743862335427,95744240015963),(1893062656,95744270786586,95744648467399)]
theorem point_links_checked14412 : (cuts14412.take 3).map (fun c => (1892941825-1+2*2^9*c.k,95743432013113+c.lower,95743809693354+c.upper)) = pointBounds14412 := by
 decide +kernel
def cuts14413 : List PrefixCut := [⟨48,345543534,345543774⟩,
⟨106,758875482,758876004⟩,
⟨128,914094620,914095250⟩]
theorem checked14413 : checkPrefixCuts (2^48) 1893072897 9 Manual.Count131072.C014413.packed 128 cuts14413 = true := by
 decide +kernel
def pointBounds14413 : List (Nat × Nat × Nat) := [(1893122048,95744689335520,95745067016622),(1893181440,95745102667468,95745480348852)]
theorem point_links_checked14413 : (cuts14413.take 2).map (fun c => (1893072897-1+2*2^9*c.k,95744343791986+c.lower,95744721472848+c.upper)) = pointBounds14413 := by
 decide +kernel
def cuts14414 : List PrefixCut := [⟨36,252152824,252152998⟩,
⟨94,664269580,664270033⟩,
⟨128,911057711,911058337⟩]
theorem checked14414 : checkPrefixCuts (2^48) 1893203969 9 Manual.Count131072.C014414.packed 128 cuts14414 = true := by
 decide +kernel
def pointBounds14414 : List (Nat × Nat × Nat) := [(1893240832,95745510039430,95745887721096),(1893300224,95745922156186,95746299838131)]
theorem point_links_checked14414 : (cuts14414.take 2).map (fun c => (1893203969-1+2*2^9*c.k,95745257886606+c.lower,95745635568098+c.upper)) = pointBounds14414 := by
 decide +kernel
def cuts14415 : List PrefixCut := [⟨24,171708321,171708439⟩,
⟨82,582015266,582015665⟩,
⟨128,913967988,913968610⟩]
theorem checked14415 : checkPrefixCuts (2^48) 1893335041 9 Manual.Count131072.C014415.packed 128 cuts14415 = true := by
 decide +kernel
def pointBounds14415 : List (Nat × Nat × Nat) := [(1893359616,95746340652638,95746718334874),(1893419008,95746750959583,95747128642100)]
theorem point_links_checked14415 : (cuts14415.take 2).map (fun c => (1893335041-1+2*2^9*c.k,95746168944317+c.lower,95746546626435+c.upper)) = pointBounds14415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000137
