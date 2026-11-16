import PlattAssemblyKernel
import PlattCertificates.Count131072.C013360
import PlattCertificates.Count131072.C013361
import PlattCertificates.Count131072.C013362
import PlattCertificates.Count131072.C013363
import PlattCertificates.Count131072.C013364
import PlattCertificates.Count131072.C013365
import PlattCertificates.Count131072.C013366
import PlattCertificates.Count131072.C013367
import PlattCertificates.Count131072.C013368
import PlattCertificates.Count131072.C013369
import PlattCertificates.Count131072.C013370
import PlattCertificates.Count131072.C013371
import PlattCertificates.Count131072.C013372
import PlattCertificates.Count131072.C013373
import PlattCertificates.Count131072.C013374
import PlattCertificates.Count131072.C013375
import PlattCertificates.Count131072.C013376
import PlattCertificates.Count131072.C013377
import PlattCertificates.Count131072.C013378
import PlattCertificates.Count131072.C013379
import PlattCertificates.Count131072.C013380
import PlattCertificates.Count131072.C013381
import PlattCertificates.Count131072.C013382
import PlattCertificates.Count131072.C013383
import PlattCertificates.Count131072.C013384
import PlattCertificates.Count131072.C013385
import PlattCertificates.Count131072.C013386
import PlattCertificates.Count131072.C013387
import PlattCertificates.Count131072.C013388
import PlattCertificates.Count131072.C013389
import PlattCertificates.Count131072.C013390
import PlattCertificates.Count131072.C013391
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000105
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13360 : List PrefixCut := [⟨12,89170749,89170815⟩,
⟨66,510157642,510158008⟩,
⟨120,925357858,925358518⟩,
⟨128,983090344,983091046⟩]
theorem checked13360 : checkPrefixCuts (2^48) 1755054081 9 Manual.Count131072.C013360.packed 128 cuts13360 = true := by
 decide +kernel
def pointBounds13360 : List (Nat × Nat × Nat) := [(1755066368,94745241603949,94745618588444),(1755121664,94745662590842,94746039575637),(1755176960,94746077791058,94746454776147)]
theorem point_links_checked13360 : (cuts13360.take 3).map (fun c => (1755054081-1+2*2^9*c.k,94745152433200+c.lower,94745529417629+c.upper)) = pointBounds13360 := by
 decide +kernel
def cuts13361 : List PrefixCut := [⟨46,368680228,368680494⟩,
⟨100,784976904,784977466⟩,
⟨128,997770600,997771317⟩]
theorem checked13361 : checkPrefixCuts (2^48) 1755185153 9 Manual.Count131072.C013361.packed 128 cuts13361 = true := by
 decide +kernel
def pointBounds13361 : List (Nat × Nat × Nat) := [(1755232256,94746504203772,94746881189169),(1755287552,94746920500448,94747297486141)]
theorem point_links_checked13361 : (cuts13361.take 2).map (fun c => (1755185153-1+2*2^9*c.k,94746135523544+c.lower,94746512508675+c.upper)) = pointBounds13361 := by
 decide +kernel
def cuts13362 : List PrefixCut := [⟨26,202046569,202046710⟩,
⟨80,621363689,621364129⟩,
⟨128,999299015,999299729⟩]
theorem checked13362 : checkPrefixCuts (2^48) 1755316225 9 Manual.Count131072.C013362.packed 128 cuts13362 = true := by
 decide +kernel
def pointBounds13362 : List (Nat × Nat × Nat) := [(1755342848,94747335340713,94747712326702),(1755398144,94747754657833,94748131644121)]
theorem point_links_checked13362 : (cuts13362.take 2).map (fun c => (1755316225-1+2*2^9*c.k,94747133294144+c.lower,94747510279992+c.upper)) = pointBounds13362 := by
 decide +kernel
def cuts13363 : List PrefixCut := [⟨6,46178899,46178931⟩,
⟨60,466271236,466271570⟩,
⟨114,882662545,882663176⟩,
⟨128,986397583,986398288⟩]
theorem checked13363 : checkPrefixCuts (2^48) 1755447297 9 Manual.Count131072.C013363.packed 128 cuts13363 = true := by
 decide +kernel
def pointBounds13363 : List (Nat × Nat × Nat) := [(1755453440,94748178772058,94748555758652),(1755508736,94748598864395,94748975851291),(1755564032,94749015255704,94749392242897)]
theorem point_links_checked13363 : (cuts13363.take 3).map (fun c => (1755447297-1+2*2^9*c.k,94748132593159+c.lower,94748509579721+c.upper)) = pointBounds13363 := by
 decide +kernel
def cuts13364 : List PrefixCut := [⟨40,307031647,307031865⟩,
⟨94,722434935,722435449⟩,
⟨128,981033258,981033957⟩]
theorem checked13364 : checkPrefixCuts (2^48) 1755578369 9 Manual.Count131072.C013364.packed 128 cuts13364 = true := by
 decide +kernel
def pointBounds13364 : List (Nat × Nat × Nat) := [(1755619328,94749426022389,94749803009874),(1755674624,94749841425677,94750218413458)]
theorem point_links_checked13364 : (cuts13364.take 2).map (fun c => (1755578369-1+2*2^9*c.k,94749118990742+c.lower,94749495978009+c.upper)) = pointBounds13364 := by
 decide +kernel
def cuts13365 : List PrefixCut := [⟨20,155990205,155990315⟩,
⟨74,570886296,570886701⟩,
⟨128,991380203,991380905⟩]
theorem checked13365 : checkPrefixCuts (2^48) 1755709441 9 Manual.Count131072.C013365.packed 128 cuts13365 = true := by
 decide +kernel
def pointBounds13365 : List (Nat × Nat × Nat) := [(1755729920,94750256014205,94750633002281),(1755785216,94750670910296,94751047898667),(1755840512,94751091404203,94751468392871)]
theorem point_links_checked13365 : (cuts13365.take 3).map (fun c => (1755709441-1+2*2^9*c.k,94750100024000+c.lower,94750477011966+c.upper)) = pointBounds13365 := by
 decide +kernel
def cuts13366 : List PrefixCut := [⟨54,413427205,413427501⟩,
⟨108,835657925,835658521⟩,
⟨128,988100140,988100845⟩]
theorem checked13366 : checkPrefixCuts (2^48) 1755840513 9 Manual.Count131072.C013366.packed 128 cuts13366 = true := by
 decide +kernel
def pointBounds13366 : List (Nat × Nat × Nat) := [(1755895808,94751504831408,94751881820372),(1755951104,94751927062128,94752304051392)]
theorem point_links_checked13366 : (cuts13366.take 2).map (fun c => (1755840513-1+2*2^9*c.k,94751091404203+c.lower,94751468392871+c.upper)) = pointBounds13366 := by
 decide +kernel
def cuts13367 : List PrefixCut := [⟨34,258234000,258234187⟩,
⟨88,674988324,674988808⟩,
⟨128,976646041,976646746⟩]
theorem checked13367 : checkPrefixCuts (2^48) 1755971585 9 Manual.Count131072.C013367.packed 128 cuts13367 = true := by
 decide +kernel
def pointBounds13367 : List (Nat × Nat × Nat) := [(1756006400,94752337738343,94752714727903),(1756061696,94752754492667,94753131482524)]
theorem point_links_checked13367 : (cuts13367.take 2).map (fun c => (1755971585-1+2*2^9*c.k,94752079504343+c.lower,94752456493716+c.upper)) = pointBounds13367 := by
 decide +kernel
def cuts13368 : List PrefixCut := [⟨14,109152845,109152924⟩,
⟨68,518828619,518828990⟩,
⟨122,930574928,930575592⟩,
⟨128,977534667,977535365⟩]
theorem checked13368 : checkPrefixCuts (2^48) 1756102657 9 Manual.Count131072.C013368.packed 128 cuts13368 = true := by
 decide +kernel
def pointBounds13368 : List (Nat × Nat × Nat) := [(1756116992,94753165303229,94753542293386),(1756172288,94753574979003,94753951969452),(1756227584,94753986725312,94754363716054)]
theorem point_links_checked13368 : (cuts13368.take 3).map (fun c => (1756102657-1+2*2^9*c.k,94753056150384+c.lower,94753433140462+c.upper)) = pointBounds13368 := by
 decide +kernel
def cuts13369 : List PrefixCut := [⟨48,375511725,375511990⟩,
⟨102,785629491,785630050⟩,
⟨128,983391743,983392443⟩]
theorem checked13369 : checkPrefixCuts (2^48) 1756233729 9 Manual.Count131072.C013369.packed 128 cuts13369 = true := by
 decide +kernel
def pointBounds13369 : List (Nat × Nat × Nat) := [(1756282880,94754409196776,94754786187817),(1756338176,94754819314542,94755196305877)]
theorem point_links_checked13369 : (cuts13369.take 2).map (fun c => (1756233729-1+2*2^9*c.k,94754033685051+c.lower,94754410675827+c.upper)) = pointBounds13369 := by
 decide +kernel
def cuts13370 : List PrefixCut := [⟨28,222919748,222919907⟩,
⟨82,641985959,641986420⟩,
⟨128,1000465448,1000466162⟩]
theorem checked13370 : checkPrefixCuts (2^48) 1756364801 9 Manual.Count131072.C013370.packed 128 cuts13370 = true := by
 decide +kernel
def pointBounds13370 : List (Nat × Nat × Nat) := [(1756393472,94755239996542,94755616988177),(1756448768,94755659062753,94756036054690)]
theorem point_links_checked13370 : (cuts13370.take 2).map (fun c => (1756364801-1+2*2^9*c.k,94755017076794+c.lower,94755394068270+c.upper)) = pointBounds13370 := by
 decide +kernel
def cuts13371 : List PrefixCut := [⟨8,60573583,60573625⟩,
⟨62,475286855,475287191⟩,
⟨116,886301522,886302153⟩,
⟨128,976354466,976355159⟩]
theorem checked13371 : checkPrefixCuts (2^48) 1756495873 9 Manual.Count131072.C013371.packed 128 cuts13371 = true := by
 decide +kernel
def pointBounds13371 : List (Nat × Nat × Nat) := [(1756504064,94756078115825,94756455108057),(1756559360,94756492829097,94756869821623),(1756614656,94756903843764,94757280836585)]
theorem point_links_checked13371 : (cuts13371.take 3).map (fun c => (1756495873-1+2*2^9*c.k,94756017542242+c.lower,94756394534432+c.upper)) = pointBounds13371 := by
 decide +kernel
def cuts13372 : List PrefixCut := [⟨42,330562828,330563064⟩,
⟨96,742673214,742673743⟩,
⟨128,994708000,994708711⟩]
theorem checked13372 : checkPrefixCuts (2^48) 1756626945 9 Manual.Count131072.C013372.packed 128 cuts13372 = true := by
 decide +kernel
def pointBounds13372 : List (Nat × Nat × Nat) := [(1756669952,94757324459536,94757701452655),(1756725248,94757736569922,94758113563334)]
theorem point_links_checked13372 : (cuts13372.take 2).map (fun c => (1756626945-1+2*2^9*c.k,94756993896708+c.lower,94757370889591+c.upper)) = pointBounds13372 := by
 decide +kernel
def cuts13373 : List PrefixCut := [⟨22,166471724,166471841⟩,
⟨76,573909884,573910297⟩,
⟨128,979733184,979733887⟩]
theorem checked13373 : checkPrefixCuts (2^48) 1756758017 9 Manual.Count131072.C013373.packed 128 cuts13373 = true := by
 decide +kernel
def pointBounds13373 : List (Nat × Nat × Nat) := [(1756780544,94758155076432,94758532070143),(1756835840,94758562514592,94758939508599)]
theorem point_links_checked13373 : (cuts13373.take 2).map (fun c => (1756758017-1+2*2^9*c.k,94757988604708+c.lower,94758365598302+c.upper)) = pointBounds13373 := by
 decide +kernel
def cuts13374 : List PrefixCut := [⟨2,14419080,14419091⟩,
⟨56,432245149,432245458⟩,
⟨110,839805014,839805614⟩,
⟨128,975815649,975816350⟩]
theorem checked13374 : checkPrefixCuts (2^48) 1756889089 9 Manual.Count131072.C013374.packed 128 cuts13374 = true := by
 decide +kernel
def pointBounds13374 : List (Nat × Nat × Nat) := [(1756891136,94758982756972,94759359751280),(1756946432,94759400583041,94759777577647),(1757001728,94759808142906,94760185137803)]
theorem point_links_checked13374 : (cuts13374.take 3).map (fun c => (1756889089-1+2*2^9*c.k,94758968337892+c.lower,94759345332189+c.upper)) = pointBounds13374 := by
 decide +kernel
def cuts13375 : List PrefixCut := [⟨36,271055797,271055990⟩,
⟨90,690444404,690444898⟩,
⟨128,974301077,974301773⟩]
theorem checked13375 : checkPrefixCuts (2^48) 1757020161 9 Manual.Count131072.C013375.packed 128 cuts13375 = true := by
 decide +kernel
def pointBounds13375 : List (Nat × Nat × Nat) := [(1757057024,94760215209338,94760592204529),(1757112320,94760634597945,94761011593437)]
theorem point_links_checked13375 : (cuts13375.take 2).map (fun c => (1757020161-1+2*2^9*c.k,94759944153541+c.lower,94760321148539+c.upper)) = pointBounds13375 := by
 decide +kernel
def cuts13376 : List PrefixCut := [⟨16,124786014,124786104⟩,
⟨70,540464004,540464390⟩,
⟨124,961735228,961735911⟩,
⟨128,991207692,991208396⟩]
theorem checked13376 : checkPrefixCuts (2^48) 1757151233 9 Manual.Count131072.C013376.packed 128 cuts13376 = true := by
 decide +kernel
def pointBounds13376 : List (Nat × Nat × Nat) := [(1757167616,94761043240632,94761420236416),(1757222912,94761458918622,94761835914702),(1757278208,94761880189846,94762257186223)]
theorem point_links_checked13376 : (cuts13376.take 3).map (fun c => (1757151233-1+2*2^9*c.k,94760918454618+c.lower,94761295450312+c.upper)) = pointBounds13376 := by
 decide +kernel
def cuts13377 : List PrefixCut := [⟨50,387300417,387300695⟩,
⟨104,799575541,799576109⟩,
⟨128,980242127,980242825⟩]
theorem checked13377 : checkPrefixCuts (2^48) 1757282305 9 Manual.Count131072.C013377.packed 128 cuts13377 = true := by
 decide +kernel
def pointBounds13377 : List (Nat × Nat × Nat) := [(1757333504,94762296962727,94762673959403),(1757388800,94762709237851,94763086234817)]
theorem point_links_checked13377 : (cuts13377.take 2).map (fun c => (1757282305-1+2*2^9*c.k,94761909662310+c.lower,94762286658708+c.upper)) = pointBounds13377 := by
 decide +kernel
def cuts13378 : List PrefixCut := [⟨30,231275208,231275374⟩,
⟨84,649770583,649771050⟩,
⟨128,990899373,990900078⟩]
theorem checked13378 : checkPrefixCuts (2^48) 1757413377 9 Manual.Count131072.C013378.packed 128 cuts13378 = true := by
 decide +kernel
def pointBounds13378 : List (Nat × Nat × Nat) := [(1757444096,94763121179645,94763498176907),(1757499392,94763539675020,94763916672583)]
theorem point_links_checked13378 : (cuts13378.take 2).map (fun c => (1757413377-1+2*2^9*c.k,94762889904437+c.lower,94763266901533+c.upper)) = pointBounds13378 := by
 decide +kernel
def cuts13379 : List PrefixCut := [⟨10,78154114,78154171⟩,
⟨64,492459339,492459687⟩,
⟨118,913477531,913478183⟩,
⟨128,993227687,993228396⟩]
theorem checked13379 : checkPrefixCuts (2^48) 1757544449 9 Manual.Count131072.C013379.packed 128 cuts13379 = true := by
 decide +kernel
def pointBounds13379 : List (Nat × Nat × Nat) := [(1757554688,94763958957924,94764335955782),(1757609984,94764373263149,94764750261298),(1757665280,94764794281341,94765171279794)]
theorem point_links_checked13379 : (cuts13379.take 3).map (fun c => (1757544449-1+2*2^9*c.k,94763880803810+c.lower,94764257801611+c.upper)) = pointBounds13379 := by
 decide +kernel
def cuts13380 : List PrefixCut := [⟨44,333568183,333568417⟩,
⟨98,760805106,760805643⟩,
⟨128,982584961,982585657⟩]
theorem checked13380 : checkPrefixCuts (2^48) 1757675521 9 Manual.Count131072.C013380.packed 128 cuts13380 = true := by
 decide +kernel
def pointBounds13380 : List (Nat × Nat × Nat) := [(1757720576,94765207599680,94765584598424),(1757775872,94765634836603,94766011835650)]
theorem point_links_checked13380 : (cuts13380.take 2).map (fun c => (1757675521-1+2*2^9*c.k,94764874031497+c.lower,94765251030007+c.upper)) = pointBounds13380 := by
 decide +kernel
def cuts13381 : List PrefixCut := [⟨24,189110396,189110531⟩,
⟨78,604631403,604631838⟩,
⟨128,990357696,990358404⟩]
theorem checked13381 : checkPrefixCuts (2^48) 1757806593 9 Manual.Count131072.C013381.packed 128 cuts13381 = true := by
 decide +kernel
def pointBounds13381 : List (Nat × Nat × Nat) := [(1757831168,94766045726854,94766422726195),(1757886464,94766461247861,94766838247502)]
theorem point_links_checked13381 : (cuts13381.take 2).map (fun c => (1757806593-1+2*2^9*c.k,94765856616458+c.lower,94766233615664+c.upper)) = pointBounds13381 := by
 decide +kernel
def cuts13382 : List PrefixCut := [⟨4,32823850,32823873⟩,
⟨58,443195196,443195511⟩,
⟨112,861238756,861239371⟩,
⟨128,981477876,981478575⟩]
theorem checked13382 : checkPrefixCuts (2^48) 1757937665 9 Manual.Count131072.C013382.packed 128 cuts13382 = true := by
 decide +kernel
def pointBounds13382 : List (Nat × Nat × Nat) := [(1757941760,94766879798004,94767256797941),(1757997056,94767290169350,94767667169579),(1758052352,94767708212910,94768085213439)]
theorem point_links_checked13382 : (cuts13382.take 3).map (fun c => (1757937665-1+2*2^9*c.k,94766846974154+c.lower,94767223974068+c.upper)) = pointBounds13382 := by
 decide +kernel
def cuts13383 : List PrefixCut := [⟨38,293948732,293948941⟩,
⟨92,711325608,711326115⟩,
⟨128,995012764,995013474⟩]
theorem checked13383 : checkPrefixCuts (2^48) 1758068737 9 Manual.Count131072.C013383.packed 128 cuts13383 = true := by
 decide +kernel
def pointBounds13383 : List (Nat × Nat × Nat) := [(1758107648,94768122400762,94768499401584),(1758162944,94768539777638,94768916778758)]
theorem point_links_checked13383 : (cuts13383.take 2).map (fun c => (1758068737-1+2*2^9*c.k,94767828452030+c.lower,94768205452643+c.upper)) = pointBounds13383 := by
 decide +kernel
def cuts13384 : List PrefixCut := [⟨18,136718417,136718515⟩,
⟨72,554549291,554549688⟩,
⟨126,964843146,964843836⟩,
⟨128,980531066,980531767⟩]
theorem checked13384 : checkPrefixCuts (2^48) 1758199809 9 Manual.Count131072.C013384.packed 128 cuts13384 = true := by
 decide +kernel
def pointBounds13384 : List (Nat × Nat × Nat) := [(1758218240,94768960183211,94769337184632),(1758273536,94769378014085,94769755015805),(1758328832,94769788307940,94770165309953)]
theorem point_links_checked13384 : (cuts13384.take 3).map (fun c => (1758199809-1+2*2^9*c.k,94768823464794+c.lower,94769200466117+c.upper)) = pointBounds13384 := by
 decide +kernel
def cuts13385 : List PrefixCut := [⟨52,403397260,403397551⟩,
⟨106,817667185,817667767⟩,
⟨128,987181105,987181807⟩]
theorem checked13385 : checkPrefixCuts (2^48) 1758330881 9 Manual.Count131072.C013385.packed 128 cuts13385 = true := by
 decide +kernel
def pointBounds13385 : List (Nat × Nat × Nat) := [(1758384128,94770207393120,94770584395435),(1758439424,94770621663045,94770998665651)]
theorem point_links_checked13385 : (cuts13385.take 2).map (fun c => (1758330881-1+2*2^9*c.k,94769803995860+c.lower,94770180997884+c.upper)) = pointBounds13385 := by
 decide +kernel
def cuts13386 : List PrefixCut := [⟨32,244742860,244743033⟩,
⟨86,655465233,655465699⟩,
⟨128,979584360,979585059⟩]
theorem checked13386 : checkPrefixCuts (2^48) 1758461953 9 Manual.Count131072.C013386.packed 128 cuts13386 = true := by
 decide +kernel
def pointBounds13386 : List (Nat × Nat × Nat) := [(1758494720,94771035919825,94771412922724),(1758550016,94771446642198,94771823645390)]
theorem point_links_checked13386 : (cuts13386.take 2).map (fun c => (1758461953-1+2*2^9*c.k,94770791176965+c.lower,94771168179691+c.upper)) = pointBounds13386 := by
 decide +kernel
def cuts13387 : List PrefixCut := [⟨12,96033792,96033857⟩,
⟨66,516493585,516493951⟩,
⟨120,935819917,935820578⟩,
⟨128,997277313,997278018⟩]
theorem checked13387 : checkPrefixCuts (2^48) 1758593025 9 Manual.Count131072.C013387.packed 128 cuts13387 = true := by
 decide +kernel
def pointBounds13387 : List (Nat × Nat × Nat) := [(1758605312,94771866795117,94772243798607),(1758660608,94772287254910,94772664258701),(1758715904,94772706581242,94773083585328)]
theorem point_links_checked13387 : (cuts13387.take 3).map (fun c => (1758593025-1+2*2^9*c.k,94771770761325+c.lower,94772147764750+c.upper)) = pointBounds13387 := by
 decide +kernel
def cuts13388 : List PrefixCut := [⟨46,357855733,357855988⟩,
⟨100,764352545,764353091⟩,
⟨128,978638496,978639192⟩]
theorem checked13388 : checkPrefixCuts (2^48) 1758724097 9 Manual.Count131072.C013388.packed 128 cuts13388 = true := by
 decide +kernel
def pointBounds13388 : List (Nat × Nat × Nat) := [(1758771200,94773125894371,94773502898756),(1758826496,94773532391183,94773909395859)]
theorem point_links_checked13388 : (cuts13388.take 2).map (fun c => (1758724097-1+2*2^9*c.k,94772768038638+c.lower,94773145042768+c.upper)) = pointBounds13388 := by
 decide +kernel
def cuts13389 : List PrefixCut := [⟨26,209321589,209321737⟩,
⟨80,625874614,625875055⟩,
⟨128,997768818,997769524⟩]
theorem checked13389 : checkPrefixCuts (2^48) 1758855169 9 Manual.Count131072.C013389.packed 128 cuts13389 = true := by
 decide +kernel
def pointBounds13389 : List (Nat × Nat × Nat) := [(1758881792,94773955998723,94774333003697),(1758937088,94774372551748,94774749557015)]
theorem point_links_checked13389 : (cuts13389.take 2).map (fun c => (1758855169-1+2*2^9*c.k,94773746677134+c.lower,94774123681960+c.upper)) = pointBounds13389 := by
 decide +kernel
def cuts13390 : List PrefixCut := [⟨6,48486303,48486338⟩,
⟨60,458132402,458132729⟩,
⟨114,873686120,873686745⟩,
⟨128,982492784,982493485⟩]
theorem checked13390 : checkPrefixCuts (2^48) 1758986241 9 Manual.Count131072.C013390.packed 128 cuts13390 = true := by
 decide +kernel
def pointBounds13390 : List (Nat × Nat × Nat) := [(1758992384,94774792932255,94775169937822),(1759047680,94775202578354,94775579584213),(1759102976,94775618132072,94775995138229)]
theorem point_links_checked13390 : (cuts13390.take 3).map (fun c => (1758986241-1+2*2^9*c.k,94774744445952+c.lower,94775121451484+c.upper)) = pointBounds13390 := by
 decide +kernel
def cuts13391 : List PrefixCut := [⟨40,309934135,309934359⟩,
⟨94,726261762,726262284⟩,
⟨128,991379749,991380460⟩]
theorem checked13391 : checkPrefixCuts (2^48) 1759117313 9 Manual.Count131072.C013391.packed 128 cuts13391 = true := by
 decide +kernel
def pointBounds13391 : List (Nat × Nat × Nat) := [(1759158272,94776036872871,94776413879328),(1759213568,94776453200498,94776830207253)]
theorem point_links_checked13391 : (cuts13391.take 2).map (fun c => (1759117313-1+2*2^9*c.k,94775726938736+c.lower,94776103944969+c.upper)) = pointBounds13391 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000105
