import PlattAssemblyKernel
import PlattCertificates.Count131072.C019440
import PlattCertificates.Count131072.C019441
import PlattCertificates.Count131072.C019442
import PlattCertificates.Count131072.C019443
import PlattCertificates.Count131072.C019444
import PlattCertificates.Count131072.C019445
import PlattCertificates.Count131072.C019446
import PlattCertificates.Count131072.C019447
import PlattCertificates.Count131072.C019448
import PlattCertificates.Count131072.C019449
import PlattCertificates.Count131072.C019450
import PlattCertificates.Count131072.C019451
import PlattCertificates.Count131072.C019452
import PlattCertificates.Count131072.C019453
import PlattCertificates.Count131072.C019454
import PlattCertificates.Count131072.C019455
import PlattCertificates.Count131072.C019456
import PlattCertificates.Count131072.C019457
import PlattCertificates.Count131072.C019458
import PlattCertificates.Count131072.C019459
import PlattCertificates.Count131072.C019460
import PlattCertificates.Count131072.C019461
import PlattCertificates.Count131072.C019462
import PlattCertificates.Count131072.C019463
import PlattCertificates.Count131072.C019464
import PlattCertificates.Count131072.C019465
import PlattCertificates.Count131072.C019466
import PlattCertificates.Count131072.C019467
import PlattCertificates.Count131072.C019468
import PlattCertificates.Count131072.C019469
import PlattCertificates.Count131072.C019470
import PlattCertificates.Count131072.C019471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000295
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19440 : List PrefixCut := [⟨68,355372140,355372352⟩,
⟨128,671029753,671030150⟩]
theorem checked19440 : checkPrefixCuts (2^48) 2551971841 9 Manual.Count131072.C019440.packed 128 cuts19440 = true := by
 decide +kernel
def pointBounds19440 : List (Nat × Nat × Nat) := [(2552041472,99652921241653,99653301394002)]
theorem point_links_checked19440 : (cuts19440.take 1).map (fun c => (2551971841-1+2*2^9*c.k,99652565869513+c.lower,99652946021650+c.upper)) = pointBounds19440 := by
 decide +kernel
def cuts19441 : List PrefixCut := [⟨18,93306152,93306207⟩,
⟨96,500933698,500933993⟩,
⟨128,667686753,667687146⟩]
theorem checked19441 : checkPrefixCuts (2^48) 2552102913 9 Manual.Count131072.C019441.packed 128 cuts19441 = true := by
 decide +kernel
def pointBounds19441 : List (Nat × Nat × Nat) := [(2552121344,99653330205418,99653710358007),(2552201216,99653737832964,99654117985793)]
theorem point_links_checked19441 : (cuts19441.take 2).map (fun c => (2552102913-1+2*2^9*c.k,99653236899266+c.lower,99653617051800+c.upper)) = pointBounds19441 := by
 decide +kernel
def cuts19442 : List PrefixCut := [⟨46,237884058,237884200⟩,
⟨124,636773767,636774141⟩,
⟨128,657506429,657506814⟩]
theorem checked19442 : checkPrefixCuts (2^48) 2552233985 9 Manual.Count131072.C019442.packed 128 cuts19442 = true := by
 decide +kernel
def pointBounds19442 : List (Nat × Nat × Nat) := [(2552281088,99654142470077,99654522623146),(2552360960,99654541359786,99654921513087)]
theorem point_links_checked19442 : (cuts19442.take 2).map (fun c => (2552233985-1+2*2^9*c.k,99653904586019+c.lower,99654284738946+c.upper)) = pointBounds19442 := by
 decide +kernel
def cuts19443 : List PrefixCut := [⟨74,385643514,385643745⟩,
⟨128,676660681,676661085⟩]
theorem checked19443 : checkPrefixCuts (2^48) 2552365057 9 Manual.Count131072.C019443.packed 128 cuts19443 = true := by
 decide +kernel
def pointBounds19443 : List (Nat × Nat × Nat) := [(2552440832,99654947735962,99655327889505)]
theorem point_links_checked19443 : (cuts19443.take 1).map (fun c => (2552365057-1+2*2^9*c.k,99654562092448+c.lower,99654942245760+c.upper)) = pointBounds19443 := by
 decide +kernel
def cuts19444 : List PrefixCut := [⟨24,126484085,126484161⟩,
⟨102,540443582,540443901⟩,
⟨128,673538615,673539014⟩]
theorem checked19444 : checkPrefixCuts (2^48) 2552496129 9 Manual.Count131072.C019444.packed 128 cuts19444 = true := by
 decide +kernel
def pointBounds19444 : List (Nat × Nat × Nat) := [(2552520704,99655365237214,99655745391006),(2552600576,99655779196711,99656159350746)]
theorem point_links_checked19444 : (cuts19444.take 2).map (fun c => (2552496129-1+2*2^9*c.k,99655238753129+c.lower,99655618906845+c.upper)) = pointBounds19444 := by
 decide +kernel
def cuts19445 : List PrefixCut := [⟨52,272360850,272361010⟩,
⟨128,659059266,659059657⟩]
theorem checked19445 : checkPrefixCuts (2^48) 2552627201 9 Manual.Count131072.C019445.packed 128 cuts19445 = true := by
 decide +kernel
def pointBounds19445 : List (Nat × Nat × Nat) := [(2552680448,99656184652594,99656564806869)]
theorem point_links_checked19445 : (cuts19445.take 1).map (fun c => (2552627201-1+2*2^9*c.k,99655912291744+c.lower,99656292445859+c.upper)) = pointBounds19445 := by
 decide +kernel
def cuts19446 : List PrefixCut := [⟨2,10144196,10144202⟩,
⟨80,415795301,415795549⟩,
⟨128,664538334,664538730⟩]
theorem checked19446 : checkPrefixCuts (2^48) 2552758273 9 Manual.Count131072.C019446.packed 128 cuts19446 = true := by
 decide +kernel
def pointBounds19446 : List (Nat × Nat × Nat) := [(2552760320,99656581495206,99656961649718),(2552840192,99656987146311,99657367301065)]
theorem point_links_checked19446 : (cuts19446.take 2).map (fun c => (2552758273-1+2*2^9*c.k,99656571351010+c.lower,99656951505516+c.upper)) = pointBounds19446 := by
 decide +kernel
def cuts19447 : List PrefixCut := [⟨30,154690179,154690270⟩,
⟨108,560646599,560646934⟩,
⟨128,666378424,666378821⟩]
theorem checked19447 : checkPrefixCuts (2^48) 2552889345 9 Manual.Count131072.C019447.packed 128 cuts19447 = true := by
 decide +kernel
def pointBounds19447 : List (Nat × Nat × Nat) := [(2552920064,99657390579523,99657770734516),(2552999936,99657796535943,99658176691180)]
theorem point_links_checked19447 : (cuts19447.take 2).map (fun c => (2552889345-1+2*2^9*c.k,99657235889344+c.lower,99657616044246+c.upper)) = pointBounds19447 := by
 decide +kernel
def cuts19448 : List PrefixCut := [⟨58,296794168,296794347⟩,
⟨128,667005604,667005998⟩]
theorem checked19448 : checkPrefixCuts (2^48) 2553020417 9 Manual.Count131072.C019448.packed 128 cuts19448 = true := by
 decide +kernel
def pointBounds19448 : List (Nat × Nat × Nat) := [(2553079808,99658199061936,99658579217414)]
theorem point_links_checked19448 : (cuts19448.take 1).map (fun c => (2553020417-1+2*2^9*c.k,99657902267768+c.lower,99658282423067+c.upper)) = pointBounds19448 := by
 decide +kernel
def cuts19449 : List PrefixCut := [⟨8,40680732,40680755⟩,
⟨86,446709318,446709580⟩,
⟨128,656939543,656939934⟩]
theorem checked19449 : checkPrefixCuts (2^48) 2553151489 9 Manual.Count131072.C019449.packed 128 cuts19449 = true := by
 decide +kernel
def pointBounds19449 : List (Nat × Nat × Nat) := [(2553159680,99658609954104,99658990109820),(2553239552,99659015982690,99659396138645)]
theorem point_links_checked19449 : (cuts19449.take 2).map (fun c => (2553151489-1+2*2^9*c.k,99658569273372+c.lower,99658949429065+c.upper)) = pointBounds19449 := by
 decide +kernel
def cuts19450 : List PrefixCut := [⟨36,189722373,189722489⟩,
⟨114,599583861,599584222⟩,
⟨128,668811474,668811876⟩]
theorem checked19450 : checkPrefixCuts (2^48) 2553282561 9 Manual.Count131072.C019450.packed 128 cuts19450 = true := by
 decide +kernel
def pointBounds19450 : List (Nat × Nat × Nat) := [(2553319424,99659415935288,99659796091488),(2553399296,99659825796776,99660205953221)]
theorem point_links_checked19450 : (cuts19450.take 2).map (fun c => (2553282561-1+2*2^9*c.k,99659226212915+c.lower,99659606368999+c.upper)) = pointBounds19450 := by
 decide +kernel
def cuts19451 : List PrefixCut := [⟨64,330700040,330700238⟩,
⟨128,663816594,663816993⟩]
theorem checked19451 : checkPrefixCuts (2^48) 2553413633 9 Manual.Count131072.C019451.packed 128 cuts19451 = true := by
 decide +kernel
def pointBounds19451 : List (Nat × Nat × Nat) := [(2553479168,99660225724429,99660605881113)]
theorem point_links_checked19451 : (cuts19451.take 1).map (fun c => (2553413633-1+2*2^9*c.k,99659895024389+c.lower,99660275180875+c.upper)) = pointBounds19451 := by
 decide +kernel
def cuts19452 : List PrefixCut := [⟨14,72750988,72751032⟩,
⟨92,482243329,482243613⟩,
⟨128,667971154,667971546⟩]
theorem checked19452 : checkPrefixCuts (2^48) 2553544705 9 Manual.Count131072.C019452.packed 128 cuts19452 = true := by
 decide +kernel
def pointBounds19452 : List (Nat × Nat × Nat) := [(2553559040,99660631591971,99661011748900),(2553638912,99661041084312,99661421241481)]
theorem point_links_checked19452 : (cuts19452.take 2).map (fun c => (2553544705-1+2*2^9*c.k,99660558840983+c.lower,99660938997868+c.upper)) = pointBounds19452 := by
 decide +kernel
def cuts19453 : List PrefixCut := [⟨42,220665446,220665577⟩,
⟨120,633659195,633659575⟩,
⟨128,676533976,676534380⟩]
theorem checked19453 : checkPrefixCuts (2^48) 2553675777 9 Manual.Count131072.C019453.packed 128 cuts19453 = true := by
 decide +kernel
def pointBounds19453 : List (Nat × Nat × Nat) := [(2553718784,99661447477583,99661827634991),(2553798656,99661860471332,99662240628989)]
theorem point_links_checked19453 : (cuts19453.take 2).map (fun c => (2553675777-1+2*2^9*c.k,99661226812137+c.lower,99661606969414+c.upper)) = pointBounds19453 := by
 decide +kernel
def cuts19454 : List PrefixCut := [⟨70,358864034,358864248⟩,
⟨128,664375588,664375982⟩]
theorem checked19454 : checkPrefixCuts (2^48) 2553806849 9 Manual.Count131072.C019454.packed 128 cuts19454 = true := by
 decide +kernel
def pointBounds19454 : List (Nat × Nat × Nat) := [(2553878528,99662262210147,99662642368042)]
theorem point_links_checked19454 : (cuts19454.take 1).map (fun c => (2553806849-1+2*2^9*c.k,99661903346113+c.lower,99662283503794+c.upper)) = pointBounds19454 := by
 decide +kernel
def cuts19455 : List PrefixCut := [⟨20,104811300,104811360⟩,
⟨98,519088791,519089100⟩,
⟨128,674591026,674591433⟩]
theorem checked19455 : checkPrefixCuts (2^48) 2553937921 9 Manual.Count131072.C019455.packed 128 cuts19455 = true := by
 decide +kernel
def pointBounds19455 : List (Nat × Nat × Nat) := [(2553958400,99662672533001,99663052691136),(2554038272,99663086810492,99663466968876)]
theorem point_links_checked19455 : (cuts19455.take 2).map (fun c => (2553937921-1+2*2^9*c.k,99662567721701+c.lower,99662947879776+c.upper)) = pointBounds19455 := by
 decide +kernel
def cuts19456 : List PrefixCut := [⟨48,247190724,247190875⟩,
⟨126,650642473,650642867⟩,
⟨128,661993160,661993560⟩]
theorem checked19456 : checkPrefixCuts (2^48) 2554068993 9 Manual.Count131072.C019456.packed 128 cuts19456 = true := by
 decide +kernel
def pointBounds19456 : List (Nat × Nat × Nat) := [(2554118144,99663489503451,99663869662084),(2554198016,99663892955200,99664273114076)]
theorem point_links_checked19456 : (cuts19456.take 2).map (fun c => (2554068993-1+2*2^9*c.k,99663242312727+c.lower,99663622471209+c.upper)) = pointBounds19456 := by
 decide +kernel
def cuts19457 : List PrefixCut := [⟨76,402006394,402006630⟩,
⟨128,670334395,670334788⟩]
theorem checked19457 : checkPrefixCuts (2^48) 2554200065 9 Manual.Count131072.C019457.packed 128 cuts19457 = true := by
 decide +kernel
def pointBounds19457 : List (Nat × Nat × Nat) := [(2554277888,99664306312281,99664686471399)]
theorem point_links_checked19457 : (cuts19457.take 1).map (fun c => (2554200065-1+2*2^9*c.k,99663904305887+c.lower,99664284464769+c.upper)) = pointBounds19457 := by
 decide +kernel
def cuts19458 : List PrefixCut := [⟨26,137633032,137633113⟩,
⟨104,533443671,533443991⟩,
⟨128,658729730,658730124⟩]
theorem checked19458 : checkPrefixCuts (2^48) 2554331137 9 Manual.Count131072.C019458.packed 128 cuts19458 = true := by
 decide +kernel
def pointBounds19458 : List (Nat × Nat × Nat) := [(2554357760,99664712273314,99665092432670),(2554437632,99665108083953,99665488243548)]
theorem point_links_checked19458 : (cuts19458.take 2).map (fun c => (2554331137-1+2*2^9*c.k,99664574640282+c.lower,99664954799557+c.upper)) = pointBounds19458 := by
 decide +kernel
def cuts19459 : List PrefixCut := [⟨54,281200525,281200692⟩,
⟨128,665086697,665087092⟩]
theorem checked19459 : checkPrefixCuts (2^48) 2554462209 9 Manual.Count131072.C019459.packed 128 cuts19459 = true := by
 decide +kernel
def pointBounds19459 : List (Nat × Nat × Nat) := [(2554517504,99665514570537,99665894730373)]
theorem point_links_checked19459 : (cuts19459.take 1).map (fun c => (2554462209-1+2*2^9*c.k,99665233370012+c.lower,99665613529681+c.upper)) = pointBounds19459 := by
 decide +kernel
def cuts19460 : List PrefixCut := [⟨4,23689506,23689520⟩,
⟨82,430260831,430261089⟩,
⟨128,670782050,670782452⟩]
theorem checked19460 : checkPrefixCuts (2^48) 2554593281 9 Manual.Count131072.C019460.packed 128 cuts19460 = true := by
 decide +kernel
def pointBounds19460 : List (Nat × Nat × Nat) := [(2554597376,99665922146215,99666302306293),(2554677248,99666328717540,99666708877862)]
theorem point_links_checked19460 : (cuts19460.take 2).map (fun c => (2554593281-1+2*2^9*c.k,99665898456709+c.lower,99666278616773+c.upper)) = pointBounds19460 := by
 decide +kernel
def cuts19461 : List PrefixCut := [⟨32,168791907,168792007⟩,
⟨110,576659889,576660230⟩,
⟨128,672730693,672731092⟩]
theorem checked19461 : checkPrefixCuts (2^48) 2554724353 9 Manual.Count131072.C019461.packed 128 cuts19461 = true := by
 decide +kernel
def pointBounds19461 : List (Nat × Nat × Nat) := [(2554757120,99666738030666,99667118191232),(2554836992,99667145898648,99667526059455)]
theorem point_links_checked19461 : (cuts19461.take 2).map (fun c => (2554724353-1+2*2^9*c.k,99666569238759+c.lower,99666949399225+c.upper)) = pointBounds19461 := by
 decide +kernel
def cuts19462 : List PrefixCut := [⟨60,314208316,314208499⟩,
⟨128,665204758,665205150⟩]
theorem checked19462 : checkPrefixCuts (2^48) 2554855425 9 Manual.Count131072.C019462.packed 128 cuts19462 = true := by
 decide +kernel
def pointBounds19462 : List (Nat × Nat × Nat) := [(2554916864,99667556177768,99667936338816)]
theorem point_links_checked19462 : (cuts19462.take 1).map (fun c => (2554855425-1+2*2^9*c.k,99667241969452+c.lower,99667622130317+c.upper)) = pointBounds19462 := by
 decide +kernel
def cuts19463 : List PrefixCut := [⟨10,50015664,50015693⟩,
⟨88,458616582,458616850⟩,
⟨128,664950241,664950633⟩]
theorem checked19463 : checkPrefixCuts (2^48) 2554986497 9 Manual.Count131072.C019463.packed 128 cuts19463 = true := by
 decide +kernel
def pointBounds19463 : List (Nat × Nat × Nat) := [(2554996736,99667957189874,99668337351160),(2555076608,99668365790792,99668745952317)]
theorem point_links_checked19463 : (cuts19463.take 2).map (fun c => (2554986497-1+2*2^9*c.k,99667907174210+c.lower,99668287335467+c.upper)) = pointBounds19463 := by
 decide +kernel
def cuts19464 : List PrefixCut := [⟨38,199169983,199170102⟩,
⟨116,600585103,600585460⟩,
⟨128,663814556,663814950⟩]
theorem checked19464 : checkPrefixCuts (2^48) 2555117569 9 Manual.Count131072.C019464.packed 128 cuts19464 = true := by
 decide +kernel
def pointBounds19464 : List (Nat × Nat × Nat) := [(2555156480,99668771294434,99669151456202),(2555236352,99669172709554,99669552871560)]
theorem point_links_checked19464 : (cuts19464.take 2).map (fun c => (2555117569-1+2*2^9*c.k,99668572124451+c.lower,99668952286100+c.upper)) = pointBounds19464 := by
 decide +kernel
def cuts19465 : List PrefixCut := [⟨66,348527696,348527902⟩,
⟨128,660476124,660476526⟩]
theorem checked19465 : checkPrefixCuts (2^48) 2555248641 9 Manual.Count131072.C019465.packed 128 cuts19465 = true := by
 decide +kernel
def pointBounds19465 : List (Nat × Nat × Nat) := [(2555316224,99669584466703,99669964628952)]
theorem point_links_checked19465 : (cuts19465.take 1).map (fun c => (2555248641-1+2*2^9*c.k,99669235939007+c.lower,99669616101050+c.upper)) = pointBounds19465 := by
 decide +kernel
def cuts19466 : List PrefixCut := [⟨16,83383232,83383281⟩,
⟨94,491369571,491369861⟩,
⟨128,666720443,666720838⟩]
theorem checked19466 : checkPrefixCuts (2^48) 2555379713 9 Manual.Count131072.C019466.packed 128 cuts19466 = true := by
 decide +kernel
def pointBounds19466 : List (Nat × Nat × Nat) := [(2555396096,99669979798363,99670359960857),(2555475968,99670387784702,99670767947437)]
theorem point_links_checked19466 : (cuts19466.take 2).map (fun c => (2555379713-1+2*2^9*c.k,99669896415131+c.lower,99670276577576+c.upper)) = pointBounds19466 := by
 decide +kernel
def cuts19467 : List PrefixCut := [⟨44,229318344,229318481⟩,
⟨122,640583411,640583794⟩,
⟨128,671862820,671863222⟩]
theorem checked19467 : checkPrefixCuts (2^48) 2555510785 9 Manual.Count131072.C019467.packed 128 cuts19467 = true := by
 decide +kernel
def pointBounds19467 : List (Nat × Nat × Nat) := [(2555555840,99670792453918,99671172616895),(2555635712,99671203718985,99671583882208)]
theorem point_links_checked19467 : (cuts19467.take 2).map (fun c => (2555510785-1+2*2^9*c.k,99670563135574+c.lower,99670943298414+c.upper)) = pointBounds19467 := by
 decide +kernel
def cuts19468 : List PrefixCut := [⟨72,377219382,377219608⟩,
⟨128,662907551,662907946⟩]
theorem checked19468 : checkPrefixCuts (2^48) 2555641857 9 Manual.Count131072.C019468.packed 128 cuts19468 = true := by
 decide +kernel
def pointBounds19468 : List (Nat × Nat × Nat) := [(2555715584,99671612217776,99671992381244)]
theorem point_links_checked19468 : (cuts19468.take 1).map (fun c => (2555641857-1+2*2^9*c.k,99671234998394+c.lower,99671615161636+c.upper)) = pointBounds19468 := by
 decide +kernel
def cuts19469 : List PrefixCut := [⟨22,117841775,117841843⟩,
⟨100,527526468,527526779⟩,
⟨128,677851122,677851522⟩]
theorem checked19469 : checkPrefixCuts (2^48) 2555772929 9 Manual.Count131072.C019469.packed 128 cuts19469 = true := by
 decide +kernel
def pointBounds19469 : List (Nat × Nat × Nat) := [(2555795456,99672015747720,99672395911425),(2555875328,99672425432413,99672805596361)]
theorem point_links_checked19469 : (cuts19469.take 2).map (fun c => (2555772929-1+2*2^9*c.k,99671897905945+c.lower,99672278069582+c.upper)) = pointBounds19469 := by
 decide +kernel
def cuts19470 : List PrefixCut := [⟨50,263972570,263972729⟩,
⟨128,674622786,674623185⟩]
theorem checked19470 : checkPrefixCuts (2^48) 2555904001 9 Manual.Count131072.C019470.packed 128 cuts19470 = true := by
 decide +kernel
def pointBounds19470 : List (Nat × Nat × Nat) := [(2555955200,99672839729637,99673219893833)]
theorem point_links_checked19470 : (cuts19470.take 1).map (fun c => (2555904001-1+2*2^9*c.k,99672575757067+c.lower,99672955921104+c.upper)) = pointBounds19470 := by
 decide +kernel
def cuts19471 : List PrefixCut := [⟨1,4735232,4735234⟩,
⟨80,417134272,417134521⟩,
⟨128,669082205,669082604⟩]
theorem checked19471 : checkPrefixCuts (2^48) 2556035073 9 Manual.Count131072.C019471.packed 128 cuts19471 = true := by
 decide +kernel
def pointBounds19471 : List (Nat × Nat × Nat) := [(2556036096,99673255115085,99673635279523),(2556116992,99673667514125,99674047678810)]
theorem point_links_checked19471 : (cuts19471.take 2).map (fun c => (2556035073-1+2*2^9*c.k,99673250379853+c.lower,99673630544289+c.upper)) = pointBounds19471 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000295
