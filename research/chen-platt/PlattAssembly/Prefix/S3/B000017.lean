import PlattAssemblyKernel
import PlattCertificates.Count131072.C020544
import PlattCertificates.Count131072.C020545
import PlattCertificates.Count131072.C020546
import PlattCertificates.Count131072.C020547
import PlattCertificates.Count131072.C020548
import PlattCertificates.Count131072.C020549
import PlattCertificates.Count131072.C020550
import PlattCertificates.Count131072.C020551
import PlattCertificates.Count131072.C020552
import PlattCertificates.Count131072.C020553
import PlattCertificates.Count131072.C020554
import PlattCertificates.Count131072.C020555
import PlattCertificates.Count131072.C020556
import PlattCertificates.Count131072.C020557
import PlattCertificates.Count131072.C020558
import PlattCertificates.Count131072.C020559
import PlattCertificates.Count131072.C020560
import PlattCertificates.Count131072.C020561
import PlattCertificates.Count131072.C020562
import PlattCertificates.Count131072.C020563
import PlattCertificates.Count131072.C020564
import PlattCertificates.Count131072.C020565
import PlattCertificates.Count131072.C020566
import PlattCertificates.Count131072.C020567
import PlattCertificates.Count131072.C020568
import PlattCertificates.Count131072.C020569
import PlattCertificates.Count131072.C020570
import PlattCertificates.Count131072.C020571
import PlattCertificates.Count131072.C020572
import PlattCertificates.Count131072.C020573
import PlattCertificates.Count131072.C020574
import PlattCertificates.Count131072.C020575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20544 : List PrefixCut := [⟨9,47283376,47283404⟩,
⟨92,449341579,449341840⟩,
⟨128,626360098,626360462⟩]
theorem checked20544 : checkPrefixCuts (2^48) 2696675329 9 Manual.Count131072.C020544.packed 128 cuts20544 = true := by
 decide +kernel
def pointBounds20544 : List (Nat × Nat × Nat) := [(2696684544,100368434438360,100368815011634),(2696769536,100368836496563,100369217070070)]
theorem point_links_checked20544 : (cuts20544.take 2).map (fun c => (2696675329-1+2*2^9*c.k,100368387154984+c.lower,100368767728230+c.upper)) = pointBounds20544 := by
 decide +kernel
def cuts20545 : List PrefixCut := [⟨47,233168135,233168268⟩,
⟨128,635305499,635305870⟩]
theorem checked20545 : checkPrefixCuts (2^48) 2696806401 9 Manual.Count131072.C020545.packed 128 cuts20545 = true := by
 decide +kernel
def pointBounds20545 : List (Nat × Nat × Nat) := [(2696854528,100369246683217,100369627256960)]
theorem point_links_checked20545 : (cuts20545.take 1).map (fun c => (2696806401-1+2*2^9*c.k,100369013515082+c.lower,100369394088692+c.upper)) = pointBounds20545 := by
 decide +kernel
def cuts20546 : List PrefixCut := [⟨2,10749936,10749942⟩,
⟨85,420284529,420284778⟩,
⟨128,631726227,631726599⟩]
theorem checked20546 : checkPrefixCuts (2^48) 2696937473 9 Manual.Count131072.C020546.packed 128 cuts20546 = true := by
 decide +kernel
def pointBounds20546 : List (Nat × Nat × Nat) := [(2696939520,100369659570517,100370040144504),(2697024512,100370069105110,100370449679340)]
theorem point_links_checked20546 : (cuts20546.take 2).map (fun c => (2696937473-1+2*2^9*c.k,100369648820581+c.lower,100370029394562+c.upper)) = pointBounds20546 := by
 decide +kernel
def cuts20547 : List PrefixCut := [⟨40,194427277,194427391⟩,
⟨123,604562203,604562556⟩,
⟨128,629712554,629712921⟩]
theorem checked20547 : checkPrefixCuts (2^48) 2697068545 9 Manual.Count131072.C020547.packed 128 cuts20547 = true := by
 decide +kernel
def pointBounds20547 : List (Nat × Nat × Nat) := [(2697109504,100370474974085,100370855548552),(2697194496,100370885109011,100371265683717)]
theorem point_links_checked20547 : (cuts20547.take 2).map (fun c => (2697068545-1+2*2^9*c.k,100370280546808+c.lower,100370661121161+c.upper)) = pointBounds20547 := by
 decide +kernel
def cuts20548 : List PrefixCut := [⟨78,396137830,396138054⟩,
⟨128,641683078,641683449⟩]
theorem checked20548 : checkPrefixCuts (2^48) 2697199617 9 Manual.Count131072.C020548.packed 128 cuts20548 = true := by
 decide +kernel
def pointBounds20548 : List (Nat × Nat × Nat) := [(2697279488,100371306397192,100371686972136)]
theorem point_links_checked20548 : (cuts20548.take 1).map (fun c => (2697199617-1+2*2^9*c.k,100370910259362+c.lower,100371290834082+c.upper)) = pointBounds20548 := by
 decide +kernel
def cuts20549 : List PrefixCut := [⟨33,163520322,163520416⟩,
⟨116,568399083,568399416⟩,
⟨128,627668908,627669276⟩]
theorem checked20549 : checkPrefixCuts (2^48) 2697330689 9 Manual.Count131072.C020549.packed 128 cuts20549 = true := by
 decide +kernel
def pointBounds20549 : List (Nat × Nat × Nat) := [(2697364480,100371715462762,100372096037947),(2697449472,100372120341523,100372500916947)]
theorem point_links_checked20549 : (cuts20549.take 2).map (fun c => (2697330689-1+2*2^9*c.k,100371551942440+c.lower,100371932517531+c.upper)) = pointBounds20549 := by
 decide +kernel
def cuts20550 : List PrefixCut := [⟨71,352065574,352065780⟩,
⟨128,634942494,634942863⟩]
theorem checked20550 : checkPrefixCuts (2^48) 2697461761 9 Manual.Count131072.C020550.packed 128 cuts20550 = true := by
 decide +kernel
def pointBounds20550 : List (Nat × Nat × Nat) := [(2697534464,100372531676922,100372912252587)]
theorem point_links_checked20550 : (cuts20550.take 1).map (fun c => (2697461761-1+2*2^9*c.k,100372179611348+c.lower,100372560186807+c.upper)) = pointBounds20550 := by
 decide +kernel
def cuts20551 : List PrefixCut := [⟨26,128445584,128445661⟩,
⟨109,527338635,527338943⟩,
⟨128,624268913,624269278⟩]
theorem checked20551 : checkPrefixCuts (2^48) 2697592833 9 Manual.Count131072.C020551.packed 128 cuts20551 = true := by
 decide +kernel
def pointBounds20551 : List (Nat × Nat × Nat) := [(2697619456,100372942999426,100373323575331),(2697704448,100373341892477,100373722468613)]
theorem point_links_checked20551 : (cuts20551.take 2).map (fun c => (2697592833-1+2*2^9*c.k,100372814553842+c.lower,100373195129670+c.upper)) = pointBounds20551 := by
 decide +kernel
def cuts20552 : List PrefixCut := [⟨64,317496453,317496640⟩,
⟨128,638428202,638428575⟩]
theorem checked20552 : checkPrefixCuts (2^48) 2697723905 9 Manual.Count131072.C020552.packed 128 cuts20552 = true := by
 decide +kernel
def pointBounds20552 : List (Nat × Nat × Nat) := [(2697789440,100373756319208,100374136895588)]
theorem point_links_checked20552 : (cuts20552.take 1).map (fun c => (2697723905-1+2*2^9*c.k,100373438822755+c.lower,100373819398948+c.upper)) = pointBounds20552 := by
 decide +kernel
def cuts20553 : List PrefixCut := [⟨19,92542899,92542953⟩,
⟨102,498388363,498388662⟩,
⟨128,624416947,624417322⟩]
theorem checked20553 : checkPrefixCuts (2^48) 2697854977 9 Manual.Count131072.C020553.packed 128 cuts20553 = true := by
 decide +kernel
def pointBounds20553 : List (Nat × Nat × Nat) := [(2697874432,100374169793856,100374550370476),(2697959424,100374575639320,100374956216185)]
theorem point_links_checked20553 : (cuts20553.take 2).map (fun c => (2697854977-1+2*2^9*c.k,100374077250957+c.lower,100374457827523+c.upper)) = pointBounds20553 := by
 decide +kernel
def cuts20554 : List PrefixCut := [⟨57,277404592,277404750⟩,
⟨128,625951528,625951886⟩]
theorem checked20554 : checkPrefixCuts (2^48) 2697986049 9 Manual.Count131072.C020554.packed 128 cuts20554 = true := by
 decide +kernel
def pointBounds20554 : List (Nat × Nat × Nat) := [(2698044416,100374979072496,100375359649595)]
theorem point_links_checked20554 : (cuts20554.take 1).map (fun c => (2697986049-1+2*2^9*c.k,100374701667904+c.lower,100375082244845+c.upper)) = pointBounds20554 := by
 decide +kernel
def cuts20555 : List PrefixCut := [⟨12,61758906,61758943⟩,
⟨95,470069715,470069983⟩,
⟨128,631867394,631867753⟩]
theorem checked20555 : checkPrefixCuts (2^48) 2698117121 9 Manual.Count131072.C020555.packed 128 cuts20555 = true := by
 decide +kernel
def pointBounds20555 : List (Nat × Nat × Nat) := [(2698129408,100375389378338,100375769955674),(2698214400,100375797689147,100376178266714)]
theorem point_links_checked20555 : (cuts20555.take 2).map (fun c => (2698117121-1+2*2^9*c.k,100375327619432+c.lower,100375708196731+c.upper)) = pointBounds20555 := by
 decide +kernel
def cuts20556 : List PrefixCut := [⟨50,251820418,251820565⟩,
⟨128,636009363,636009727⟩]
theorem checked20556 : checkPrefixCuts (2^48) 2698248193 9 Manual.Count131072.C020556.packed 128 cuts20556 = true := by
 decide +kernel
def pointBounds20556 : List (Nat × Nat × Nat) := [(2698299392,100376211307244,100376591885049)]
theorem point_links_checked20556 : (cuts20556.take 1).map (fun c => (2698248193-1+2*2^9*c.k,100375959486826+c.lower,100376340064484+c.upper)) = pointBounds20556 := by
 decide +kernel
def cuts20557 : List PrefixCut := [⟨5,25660870,25660885⟩,
⟨88,426109852,426110100⟩,
⟨128,626694717,626695075⟩]
theorem checked20557 : checkPrefixCuts (2^48) 2698379265 9 Manual.Count131072.C020557.packed 128 cuts20557 = true := by
 decide +kernel
def pointBounds20557 : List (Nat × Nat × Nat) := [(2698384384,100376621157059,100377001735096),(2698469376,100377021606041,100377402184311)]
theorem point_links_checked20557 : (cuts20557.take 2).map (fun c => (2698379265-1+2*2^9*c.k,100376595496189+c.lower,100376976074211+c.upper)) = pointBounds20557 := by
 decide +kernel
def cuts20558 : List PrefixCut := [⟨43,211116665,211116785⟩,
⟨126,622283690,622284046⟩,
⟨128,633339754,633340116⟩]
theorem checked20558 : checkPrefixCuts (2^48) 2698510337 9 Manual.Count131072.C020558.packed 128 cuts20558 = true := by
 decide +kernel
def pointBounds20558 : List (Nat × Nat × Nat) := [(2698554368,100377433307571,100377813886071),(2698639360,100377844474596,100378225053332)]
theorem point_links_checked20558 : (cuts20558.take 2).map (fun c => (2698510337-1+2*2^9*c.k,100377222190906+c.lower,100377602769286+c.upper)) = pointBounds20558 := by
 decide +kernel
def cuts20559 : List PrefixCut := [⟨81,395195913,395196149⟩,
⟨128,626842470,626842840⟩]
theorem checked20559 : checkPrefixCuts (2^48) 2698641409 9 Manual.Count131072.C020559.packed 128 cuts20559 = true := by
 decide +kernel
def pointBounds20559 : List (Nat × Nat × Nat) := [(2698724352,100378250726573,100378631305551)]
theorem point_links_checked20559 : (cuts20559.take 1).map (fun c => (2698641409-1+2*2^9*c.k,100377855530660+c.lower,100378236109402+c.upper)) = pointBounds20559 := by
 decide +kernel
def cuts20560 : List PrefixCut := [⟨36,176991432,176991536⟩,
⟨119,584990746,584991088⟩,
⟨128,626916327,626916693⟩]
theorem checked20560 : checkPrefixCuts (2^48) 2698772481 9 Manual.Count131072.C020560.packed 128 cuts20560 = true := by
 decide +kernel
def pointBounds20560 : List (Nat × Nat × Nat) := [(2698809344,100378659364562,100379039943778),(2698894336,100379067363876,100379447943330)]
theorem point_links_checked20560 : (cuts20560.take 2).map (fun c => (2698772481-1+2*2^9*c.k,100378482373130+c.lower,100378862952242+c.upper)) = pointBounds20560 := by
 decide +kernel
def cuts20561 : List PrefixCut := [⟨74,367103840,367104056⟩,
⟨128,632204779,632205149⟩]
theorem checked20561 : checkPrefixCuts (2^48) 2698903553 9 Manual.Count131072.C020561.packed 128 cuts20561 = true := by
 decide +kernel
def pointBounds20561 : List (Nat × Nat × Nat) := [(2698979328,100379476393297,100379856972991)]
theorem point_links_checked20561 : (cuts20561.take 1).map (fun c => (2698903553-1+2*2^9*c.k,100379109289457+c.lower,100379489868935+c.upper)) = pointBounds20561 := by
 decide +kernel
def cuts20562 : List PrefixCut := [⟨29,142038447,142038529⟩,
⟨112,549165035,549165353⟩,
⟨128,627689756,627690120⟩]
theorem checked20562 : checkPrefixCuts (2^48) 2699034625 9 Manual.Count131072.C020562.packed 128 cuts20562 = true := by
 decide +kernel
def pointBounds20562 : List (Nat × Nat × Nat) := [(2699064320,100379883532683,100380264112613),(2699149312,100380290659271,100380671239437)]
theorem point_links_checked20562 : (cuts20562.take 2).map (fun c => (2699034625-1+2*2^9*c.k,100379741494236+c.lower,100380122074084+c.upper)) = pointBounds20562 := by
 decide +kernel
def cuts20563 : List PrefixCut := [⟨67,332134551,332134744⟩,
⟨128,632977542,632977910⟩]
theorem checked20563 : checkPrefixCuts (2^48) 2699165697 9 Manual.Count131072.C020563.packed 128 cuts20563 = true := by
 decide +kernel
def pointBounds20563 : List (Nat × Nat × Nat) := [(2699234304,100380701318543,100381081898948)]
theorem point_links_checked20563 : (cuts20563.take 1).map (fun c => (2699165697-1+2*2^9*c.k,100380369183992+c.lower,100380749764204+c.upper)) = pointBounds20563 := by
 decide +kernel
def cuts20564 : List PrefixCut := [⟨22,106779328,106779392⟩,
⟨105,516995643,516995945⟩,
⟨128,630027042,630027410⟩]
theorem checked20564 : checkPrefixCuts (2^48) 2699296769 9 Manual.Count131072.C020564.packed 128 cuts20564 = true := by
 decide +kernel
def pointBounds20564 : List (Nat × Nat × Nat) := [(2699319296,100381108940862,100381489521506),(2699404288,100381519157177,100381899738059)]
theorem point_links_checked20564 : (cuts20564.take 2).map (fun c => (2699296769-1+2*2^9*c.k,100381002161534+c.lower,100381382742114+c.upper)) = pointBounds20564 := by
 decide +kernel
def cuts20565 : List PrefixCut := [⟨60,297484795,297484965⟩,
⟨128,624887355,624887719⟩]
theorem checked20565 : checkPrefixCuts (2^48) 2699427841 9 Manual.Count131072.C020565.packed 128 cuts20565 = true := by
 decide +kernel
def pointBounds20565 : List (Nat × Nat × Nat) := [(2699489280,100381929673371,100382310254489)]
theorem point_links_checked20565 : (cuts20565.take 1).map (fun c => (2699427841-1+2*2^9*c.k,100381632188576+c.lower,100382012769524+c.upper)) = pointBounds20565 := by
 decide +kernel
def cuts20566 : List PrefixCut := [⟨15,70901357,70901398⟩,
⟨98,477951063,477951338⟩,
⟨128,622875982,622876337⟩]
theorem checked20566 : checkPrefixCuts (2^48) 2699558913 9 Manual.Count131072.C020566.packed 128 cuts20566 = true := by
 decide +kernel
def pointBounds20566 : List (Nat × Nat × Nat) := [(2699574272,100382327977288,100382708558641),(2699659264,100382735026994,100383115608581)]
theorem point_links_checked20566 : (cuts20566.take 2).map (fun c => (2699558913-1+2*2^9*c.k,100382257075931+c.lower,100382637657243+c.upper)) = pointBounds20566 := by
 decide +kernel
def cuts20567 : List PrefixCut := [⟨53,258358462,258358618⟩,
⟨128,629622451,629622822⟩]
theorem checked20567 : checkPrefixCuts (2^48) 2699689985 9 Manual.Count131072.C020567.packed 128 cuts20567 = true := by
 decide +kernel
def pointBounds20567 : List (Nat × Nat × Nat) := [(2699744256,100383138310375,100383518892198)]
theorem point_links_checked20567 : (cuts20567.take 1).map (fun c => (2699689985-1+2*2^9*c.k,100382879951913+c.lower,100383260533580+c.upper)) = pointBounds20567 := by
 decide +kernel
def cuts20568 : List PrefixCut := [⟨8,39096266,39096291⟩,
⟨91,450381846,450382114⟩,
⟨128,628757931,628758305⟩]
theorem checked20568 : checkPrefixCuts (2^48) 2699821057 9 Manual.Count131072.C020568.packed 128 cuts20568 = true := by
 decide +kernel
def pointBounds20568 : List (Nat × Nat × Nat) := [(2699829248,100383548670630,100383929252693),(2699914240,100383959956210,100384340538516)]
theorem point_links_checked20568 : (cuts20568.take 2).map (fun c => (2699821057-1+2*2^9*c.k,100383509574364+c.lower,100383890156402+c.upper)) = pointBounds20568 := by
 decide +kernel
def cuts20569 : List PrefixCut := [⟨46,225181943,225182076⟩,
⟨128,629874134,629874501⟩]
theorem checked20569 : checkPrefixCuts (2^48) 2699952129 9 Manual.Count131072.C020569.packed 128 cuts20569 = true := by
 decide +kernel
def pointBounds20569 : List (Nat × Nat × Nat) := [(2699999232,100384363514238,100384744096783)]
theorem point_links_checked20569 : (cuts20569.take 1).map (fun c => (2699952129-1+2*2^9*c.k,100384138332295+c.lower,100384518914707+c.upper)) = pointBounds20569 := by
 decide +kernel
def cuts20570 : List PrefixCut := [⟨1,5733570,5733573⟩,
⟨84,413853030,413853269⟩,
⟨128,630886040,630886406⟩]
theorem checked20570 : checkPrefixCuts (2^48) 2700083201 9 Manual.Count131072.C020570.packed 128 cuts20570 = true := by
 decide +kernel
def pointBounds20570 : List (Nat × Nat × Nat) := [(2700084224,100384773939999,100385154522781),(2700169216,100385182059459,100385562642477)]
theorem point_links_checked20570 : (cuts20570.take 2).map (fun c => (2700083201-1+2*2^9*c.k,100384768206429+c.lower,100385148789208+c.upper)) = pointBounds20570 := by
 decide +kernel
def cuts20571 : List PrefixCut := [⟨39,193158422,193158535⟩,
⟨122,606776800,606777148⟩,
⟨128,637109694,637110059⟩]
theorem checked20571 : checkPrefixCuts (2^48) 2700214273 9 Manual.Count131072.C020571.packed 128 cuts20571 = true := by
 decide +kernel
def pointBounds20571 : List (Nat × Nat × Nat) := [(2700254208,100385592250891,100385972834149),(2700339200,100386005869269,100386386452762)]
theorem point_links_checked20571 : (cuts20571.take 2).map (fun c => (2700214273-1+2*2^9*c.k,100385399092469+c.lower,100385779675614+c.upper)) = pointBounds20571 := by
 decide +kernel
def cuts20572 : List PrefixCut := [⟨77,375976012,375976231⟩,
⟨128,625821490,625821856⟩]
theorem checked20572 : checkPrefixCuts (2^48) 2700345345 9 Manual.Count131072.C020572.packed 128 cuts20572 = true := by
 decide +kernel
def pointBounds20572 : List (Nat × Nat × Nat) := [(2700424192,100386412178175,100386792761904)]
theorem point_links_checked20572 : (cuts20572.take 1).map (fun c => (2700345345-1+2*2^9*c.k,100386036202163+c.lower,100386416785673+c.upper)) = pointBounds20572 := by
 decide +kernel
def cuts20573 : List PrefixCut := [⟨32,156242177,156242270⟩,
⟨115,558147912,558148242⟩,
⟨128,624227682,624228053⟩]
theorem checked20573 : checkPrefixCuts (2^48) 2700476417 9 Manual.Count131072.C020573.packed 128 cuts20573 = true := by
 decide +kernel
def pointBounds20573 : List (Nat × Nat × Nat) := [(2700509184,100386818265830,100387198849799),(2700594176,100387220171565,100387600755771)]
theorem point_links_checked20573 : (cuts20573.take 2).map (fun c => (2700476417-1+2*2^9*c.k,100386662023653+c.lower,100387042607529+c.upper)) = pointBounds20573 := by
 decide +kernel
def cuts20574 : List PrefixCut := [⟨70,340607726,340607924⟩,
⟨128,630346576,630346938⟩]
theorem checked20574 : checkPrefixCuts (2^48) 2700607489 9 Manual.Count131072.C020574.packed 128 cuts20574 = true := by
 decide +kernel
def pointBounds20574 : List (Nat × Nat × Nat) := [(2700679168,100387626859061,100388007443506)]
theorem point_links_checked20574 : (cuts20574.take 1).map (fun c => (2700607489-1+2*2^9*c.k,100387286251335+c.lower,100387666835582+c.upper)) = pointBounds20574 := by
 decide +kernel
def cuts20575 : List PrefixCut := [⟨25,123606049,123606121⟩,
⟨108,530163806,530164117⟩,
⟨128,629065539,629065906⟩]
theorem checked20575 : checkPrefixCuts (2^48) 2700738561 9 Manual.Count131072.C020575.packed 128 cuts20575 = true := by
 decide +kernel
def pointBounds20575 : List (Nat × Nat × Nat) := [(2700764160,100388040203960,100388420788641),(2700849152,100388446761717,100388827346637)]
theorem point_links_checked20575 : (cuts20575.take 2).map (fun c => (2700738561-1+2*2^9*c.k,100387916597911+c.lower,100388297182520+c.upper)) = pointBounds20575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000017
