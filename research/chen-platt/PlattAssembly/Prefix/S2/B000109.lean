import PlattAssemblyKernel
import PlattCertificates.Count131072.C013488
import PlattCertificates.Count131072.C013489
import PlattCertificates.Count131072.C013490
import PlattCertificates.Count131072.C013491
import PlattCertificates.Count131072.C013492
import PlattCertificates.Count131072.C013493
import PlattCertificates.Count131072.C013494
import PlattCertificates.Count131072.C013495
import PlattCertificates.Count131072.C013496
import PlattCertificates.Count131072.C013497
import PlattCertificates.Count131072.C013498
import PlattCertificates.Count131072.C013499
import PlattCertificates.Count131072.C013500
import PlattCertificates.Count131072.C013501
import PlattCertificates.Count131072.C013502
import PlattCertificates.Count131072.C013503
import PlattCertificates.Count131072.C013504
import PlattCertificates.Count131072.C013505
import PlattCertificates.Count131072.C013506
import PlattCertificates.Count131072.C013507
import PlattCertificates.Count131072.C013508
import PlattCertificates.Count131072.C013509
import PlattCertificates.Count131072.C013510
import PlattCertificates.Count131072.C013511
import PlattCertificates.Count131072.C013512
import PlattCertificates.Count131072.C013513
import PlattCertificates.Count131072.C013514
import PlattCertificates.Count131072.C013515
import PlattCertificates.Count131072.C013516
import PlattCertificates.Count131072.C013517
import PlattCertificates.Count131072.C013518
import PlattCertificates.Count131072.C013519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000109
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13488 : List PrefixCut := [⟨31,235747603,235747769⟩,
⟨86,646865960,646866423⟩,
⟨128,973464028,973464720⟩]
theorem checked13488 : checkPrefixCuts (2^48) 1771831297 9 Manual.Count131072.C013488.packed 128 cuts13488 = true := by
 decide +kernel
def pointBounds13488 : List (Nat × Nat × Nat) := [(1771863040,94871159637201,94871536711241),(1771919360,94871570755558,94871947829895)]
theorem point_links_checked13488 : (cuts13488.take 2).map (fun c => (1771831297-1+2*2^9*c.k,94870923889598+c.lower,94871300963472+c.upper)) = pointBounds13488 := by
 decide +kernel
def cuts13489 : List PrefixCut := [⟨13,101504274,101504347⟩,
⟨68,525145260,525145635⟩,
⟨123,942577942,942578615⟩,
⟨128,980222483,980223183⟩]
theorem checked13489 : checkPrefixCuts (2^48) 1771962369 9 Manual.Count131072.C013489.packed 128 cuts13489 = true := by
 decide +kernel
def pointBounds13489 : List (Nat × Nat × Nat) := [(1771975680,94871998857900,94872375932539),(1772032000,94872422498886,94872799573827),(1772088320,94872839931568,94873217006807)]
theorem point_links_checked13489 : (cuts13489.take 3).map (fun c => (1771962369-1+2*2^9*c.k,94871897353626+c.lower,94872274428192+c.upper)) = pointBounds13489 := by
 decide +kernel
def cuts13490 : List PrefixCut := [⟨50,378504244,378504515⟩,
⟨105,804804934,804805505⟩,
⟨128,986026314,986027012⟩]
theorem checked13490 : checkPrefixCuts (2^48) 1772093441 9 Manual.Count131072.C013490.packed 128 cuts13490 = true := by
 decide +kernel
def pointBounds13490 : List (Nat × Nat × Nat) := [(1772144640,94873256080353,94873633155890),(1772200960,94873682381043,94874059456880)]
theorem point_links_checked13490 : (cuts13490.take 2).map (fun c => (1772093441-1+2*2^9*c.k,94872877576109+c.lower,94873254651375+c.upper)) = pointBounds13490 := by
 decide +kernel
def cuts13491 : List PrefixCut := [⟨32,248559983,248560157⟩,
⟨87,673404279,673404758⟩,
⟨128,986906808,986907508⟩]
theorem checked13491 : checkPrefixCuts (2^48) 1772224513 9 Manual.Count131072.C013491.packed 128 cuts13491 = true := by
 decide +kernel
def pointBounds13491 : List (Nat × Nat × Nat) := [(1772257280,94874112162406,94874489238544),(1772313600,94874537006702,94874914083145)]
theorem point_links_checked13491 : (cuts13491.take 2).map (fun c => (1772224513-1+2*2^9*c.k,94873863602423+c.lower,94874240678387+c.upper)) = pointBounds13491 := by
 decide +kernel
def cuts13492 : List PrefixCut := [⟨14,107199022,107199098⟩,
⟨69,518835142,518835507⟩,
⟨124,938398313,938398980⟩,
⟨128,971270418,971271109⟩]
theorem checked13492 : checkPrefixCuts (2^48) 1772355585 9 Manual.Count131072.C013492.packed 128 cuts13492 = true := by
 decide +kernel
def pointBounds13492 : List (Nat × Nat × Nat) := [(1772369920,94874957708253,94875334784993),(1772426240,94875369344373,94875746421402),(1772482560,94875788907544,94876165984875)]
theorem point_links_checked13492 : (cuts13492.take 3).map (fun c => (1772355585-1+2*2^9*c.k,94874850509231+c.lower,94875227585895+c.upper)) = pointBounds13492 := by
 decide +kernel
def cuts13493 : List PrefixCut := [⟨51,385724901,385725172⟩,
⟨106,799862426,799862995⟩,
⟨128,966434699,966435387⟩]
theorem checked13493 : checkPrefixCuts (2^48) 1772486657 9 Manual.Count131072.C013493.packed 128 cuts13493 = true := by
 decide +kernel
def pointBounds13493 : List (Nat × Nat × Nat) := [(1772538880,94876207504550,94876584582176),(1772595200,94876621642075,94876998719999)]
theorem point_links_checked13493 : (cuts13493.take 2).map (fun c => (1772486657-1+2*2^9*c.k,94875821779649+c.lower,94876198857004+c.upper)) = pointBounds13493 := by
 decide +kernel
def cuts13494 : List PrefixCut := [⟨33,255650289,255650474⟩,
⟨88,668491215,668491692⟩,
⟨128,975414206,975414896⟩]
theorem checked13494 : checkPrefixCuts (2^48) 1772617729 9 Manual.Count131072.C013494.packed 128 cuts13494 = true := by
 decide +kernel
def pointBounds13494 : List (Nat × Nat × Nat) := [(1772651520,94877043864637,94877420942865),(1772707840,94877456705563,94877833784083)]
theorem point_links_checked13494 : (cuts13494.take 2).map (fun c => (1772617729-1+2*2^9*c.k,94876788214348+c.lower,94877165292391+c.upper)) = pointBounds13494 := by
 decide +kernel
def cuts13495 : List PrefixCut := [⟨15,119718674,119718762⟩,
⟨70,533327332,533327715⟩,
⟨125,965816354,965817045⟩,
⟨128,988202526,988203232⟩]
theorem checked13495 : checkPrefixCuts (2^48) 1772748801 9 Manual.Count131072.C013495.packed 128 cuts13495 = true := by
 decide +kernel
def pointBounds13495 : List (Nat × Nat × Nat) := [(1772764160,94877883347228,94878260426049),(1772820480,94878296955886,94878674035002),(1772876800,94878729444908,94879106524332)]
theorem point_links_checked13495 : (cuts13495.take 3).map (fun c => (1772748801-1+2*2^9*c.k,94877763628554+c.lower,94878140707287+c.upper)) = pointBounds13495 := by
 decide +kernel
def cuts13496 : List PrefixCut := [⟨52,393101309,393101588⟩,
⟨107,806194115,806194687⟩,
⟨128,968601778,968602467⟩]
theorem checked13496 : checkPrefixCuts (2^48) 1772879873 9 Manual.Count131072.C013496.packed 128 cuts13496 = true := by
 decide +kernel
def pointBounds13496 : List (Nat × Nat × Nat) := [(1772933120,94879144932389,94879522012107),(1772989440,94879558025195,94879935105206)]
theorem point_links_checked13496 : (cuts13496.take 2).map (fun c => (1772879873-1+2*2^9*c.k,94878751831080+c.lower,94879128910519+c.upper)) = pointBounds13496 := by
 decide +kernel
def cuts13497 : List PrefixCut := [⟨34,260514870,260515054⟩,
⟨89,681360235,681360719⟩,
⟨128,982182720,982183417⟩]
theorem checked13497 : checkPrefixCuts (2^48) 1773010945 9 Manual.Count131072.C013497.packed 128 cuts13497 = true := by
 decide +kernel
def pointBounds13497 : List (Nat × Nat × Nat) := [(1773045760,94879980947728,94880358028040),(1773102080,94880401793093,94880778873705)]
theorem point_links_checked13497 : (cuts13497.take 2).map (fun c => (1773010945-1+2*2^9*c.k,94879720432858+c.lower,94880097512986+c.upper)) = pointBounds13497 := by
 decide +kernel
def cuts13498 : List PrefixCut := [⟨16,116517241,116517322⟩,
⟨71,530986306,530986682⟩,
⟨126,949886712,949887385⟩,
⟨128,965601172,965601856⟩]
theorem checked13498 : checkPrefixCuts (2^48) 1773142017 9 Manual.Count131072.C013498.packed 128 cuts13498 = true := by
 decide +kernel
def pointBounds13498 : List (Nat × Nat × Nat) := [(1773158400,94880819132819,94881196213725),(1773214720,94881233601884,94881610683085),(1773271040,94881652502290,94882029583788)]
theorem point_links_checked13498 : (cuts13498.take 3).map (fun c => (1773142017-1+2*2^9*c.k,94880702615578+c.lower,94881079696403+c.upper)) = pointBounds13498 := by
 decide +kernel
def cuts13499 : List PrefixCut := [⟨53,401902891,401903177⟩,
⟨108,822998882,822999470⟩,
⟨128,974101282,974101976⟩]
theorem checked13499 : checkPrefixCuts (2^48) 1773273089 9 Manual.Count131072.C013499.packed 128 cuts13499 = true := by
 decide +kernel
def pointBounds13499 : List (Nat × Nat × Nat) := [(1773327360,94882070119641,94882447201436),(1773383680,94882491215632,94882868297729)]
theorem point_links_checked13499 : (cuts13499.take 2).map (fun c => (1773273089-1+2*2^9*c.k,94881668216750+c.lower,94882045298259+c.upper)) = pointBounds13499 := by
 decide +kernel
def cuts13500 : List PrefixCut := [⟨35,268234268,268234455⟩,
⟨90,681685154,681685634⟩,
⟨128,968950436,968951116⟩]
theorem checked13500 : checkPrefixCuts (2^48) 1773404161 9 Manual.Count131072.C013500.packed 128 cuts13500 = true := by
 decide +kernel
def pointBounds13500 : List (Nat × Nat × Nat) := [(1773440000,94882910552300,94883287634690),(1773496320,94883324003186,94883701085869)]
theorem point_links_checked13500 : (cuts13500.take 2).map (fun c => (1773404161-1+2*2^9*c.k,94882642318032+c.lower,94883019400235+c.upper)) = pointBounds13500 := by
 decide +kernel
def cuts13501 : List PrefixCut := [⟨17,126648651,126648744⟩,
⟨72,548167311,548167696⟩,
⟨127,966657274,966657955⟩,
⟨128,975861682,975862369⟩]
theorem checked13501 : checkPrefixCuts (2^48) 1773535233 9 Manual.Count131072.C013501.packed 128 cuts13501 = true := by
 decide +kernel
def pointBounds13501 : List (Nat × Nat × Nat) := [(1773552640,94883737917119,94884115000095),(1773608960,94884159435779,94884536519047),(1773665280,94884577925742,94884955009306)]
theorem point_links_checked13501 : (cuts13501.take 3).map (fun c => (1773535233-1+2*2^9*c.k,94883611268468+c.lower,94883988351351+c.upper)) = pointBounds13501 := by
 decide +kernel
def cuts13502 : List PrefixCut := [⟨54,403083172,403083456⟩,
⟨109,827894096,827894683⟩,
⟨128,970869972,970870666⟩]
theorem checked13502 : checkPrefixCuts (2^48) 1773666305 9 Manual.Count131072.C013502.packed 128 cuts13502 = true := by
 decide +kernel
def pointBounds13502 : List (Nat × Nat × Nat) := [(1773721600,94884990213322,94885367297176),(1773777920,94885415024246,94885792108403)]
theorem point_links_checked13502 : (cuts13502.take 2).map (fun c => (1773666305-1+2*2^9*c.k,94884587130150+c.lower,94884964213720+c.upper)) = pointBounds13502 := by
 decide +kernel
def cuts13503 : List PrefixCut := [⟨36,274045943,274046135⟩,
⟨91,698671192,698671680⟩,
⟨128,978256272,978256955⟩]
theorem checked13503 : checkPrefixCuts (2^48) 1773797377 9 Manual.Count131072.C013503.packed 128 cuts13503 = true := by
 decide +kernel
def pointBounds13503 : List (Nat × Nat × Nat) := [(1773834240,94885832046065,94886209130521),(1773890560,94886256671314,94886633756066)]
theorem point_links_checked13503 : (cuts13503.take 2).map (fun c => (1773797377-1+2*2^9*c.k,94885558000122+c.lower,94885935084386+c.upper)) = pointBounds13503 := by
 decide +kernel
def cuts13504 : List PrefixCut := [⟨18,137886269,137886368⟩,
⟨73,556455184,556455578⟩,
⟨128,977866670,977867366⟩]
theorem checked13504 : checkPrefixCuts (2^48) 1773928449 9 Manual.Count131072.C013504.packed 128 cuts13504 = true := by
 decide +kernel
def pointBounds13504 : List (Nat × Nat × Nat) := [(1773946880,94886674142663,94887051227709),(1774003200,94887092711578,94887469796919),(1774059520,94887514123064,94887891208707)]
theorem point_links_checked13504 : (cuts13504.take 3).map (fun c => (1773928449-1+2*2^9*c.k,94886536256394+c.lower,94886913341341+c.upper)) = pointBounds13504 := by
 decide +kernel
def cuts13505 : List PrefixCut := [⟨55,417748956,417749250⟩,
⟨110,830883698,830884288⟩,
⟨128,967799149,967799835⟩]
theorem checked13505 : checkPrefixCuts (2^48) 1774059521 9 Manual.Count131072.C013505.packed 128 cuts13505 = true := by
 decide +kernel
def pointBounds13505 : List (Nat × Nat × Nat) := [(1774115840,94887931872020,94888308957957),(1774172160,94888345006762,94888722092995)]
theorem point_links_checked13505 : (cuts13505.take 2).map (fun c => (1774059521-1+2*2^9*c.k,94887514123064+c.lower,94887891208707+c.upper)) = pointBounds13505 := by
 decide +kernel
def cuts13506 : List PrefixCut := [⟨37,293657513,293657723⟩,
⟨92,723265009,723265524⟩,
⟨128,999298057,999298763⟩]
theorem checked13506 : checkPrefixCuts (2^48) 1774190593 9 Manual.Count131072.C013506.packed 128 cuts13506 = true := by
 decide +kernel
def pointBounds13506 : List (Nat × Nat × Nat) := [(1774228480,94888775579726,94889152666265),(1774284800,94889205187222,94889582274066)]
theorem point_links_checked13506 : (cuts13506.take 2).map (fun c => (1774190593-1+2*2^9*c.k,94888481922213+c.lower,94888859008542+c.upper)) = pointBounds13506 := by
 decide +kernel
def cuts13507 : List PrefixCut := [⟨19,148801649,148801752⟩,
⟨74,566008399,566008798⟩,
⟨128,972891198,972891880⟩]
theorem checked13507 : checkPrefixCuts (2^48) 1774321665 9 Manual.Count131072.C013507.packed 128 cuts13507 = true := by
 decide +kernel
def pointBounds13507 : List (Nat × Nat × Nat) := [(1774341120,94889630021919,94890007109057),(1774397440,94890047228669,94890424316103)]
theorem point_links_checked13507 : (cuts13507.take 2).map (fun c => (1774321665-1+2*2^9*c.k,94889481220270+c.lower,94889858307305+c.upper)) = pointBounds13507 := by
 decide +kernel
def cuts13508 : List PrefixCut := [⟨1,6503676,6503681⟩,
⟨56,427649516,427649817⟩,
⟨111,842437273,842437868⟩,
⟨128,977577564,977578254⟩]
theorem checked13508 : checkPrefixCuts (2^48) 1774452737 9 Manual.Count131072.C013508.packed 128 cuts13508 = true := by
 decide +kernel
def pointBounds13508 : List (Nat × Nat × Nat) := [(1774453760,94890460615144,94890837702866),(1774510080,94890881760984,94891258849002),(1774566400,94891296548741,94891673637053)]
theorem point_links_checked13508 : (cuts13508.take 3).map (fun c => (1774452737-1+2*2^9*c.k,94890454111468+c.lower,94890831199185+c.upper)) = pointBounds13508 := by
 decide +kernel
def cuts13509 : List PrefixCut := [⟨38,287406461,287406665⟩,
⟨93,704071170,704071667⟩,
⟨128,973698742,973699428⟩]
theorem checked13509 : checkPrefixCuts (2^48) 1774583809 9 Manual.Count131072.C013509.packed 128 cuts13509 = true := by
 decide +kernel
def pointBounds13509 : List (Nat × Nat × Nat) := [(1774622720,94891719095493,94892096184104),(1774679040,94892135760202,94892512849106)]
theorem point_links_checked13509 : (cuts13509.take 2).map (fun c => (1774583809-1+2*2^9*c.k,94891431689032+c.lower,94891808777439+c.upper)) = pointBounds13509 := by
 decide +kernel
def cuts13510 : List PrefixCut := [⟨20,146706810,146706914⟩,
⟨75,565406912,565407313⟩,
⟨128,963476748,963477432⟩]
theorem checked13510 : checkPrefixCuts (2^48) 1774714881 9 Manual.Count131072.C013510.packed 128 cuts13510 = true := by
 decide +kernel
def pointBounds13510 : List (Nat × Nat × Nat) := [(1774735360,94892552094584,94892929183781),(1774791680,94892970794686,94893347884180)]
theorem point_links_checked13510 : (cuts13510.take 2).map (fun c => (1774714881-1+2*2^9*c.k,94892405387774+c.lower,94892782476867+c.upper)) = pointBounds13510 := by
 decide +kernel
def cuts13511 : List PrefixCut := [⟨2,14748969,14748979⟩,
⟨57,434056742,434057048⟩,
⟨112,851765508,851766113⟩,
⟨128,972445023,972445711⟩]
theorem checked13511 : checkPrefixCuts (2^48) 1774845953 9 Manual.Count131072.C013511.packed 128 cuts13511 = true := by
 decide +kernel
def pointBounds13511 : List (Nat × Nat × Nat) := [(1774848000,94893383613491,94893760703278),(1774904320,94893802921264,94894180011347),(1774960640,94894220630030,94894597720412)]
theorem point_links_checked13511 : (cuts13511.take 3).map (fun c => (1774845953-1+2*2^9*c.k,94893368864522+c.lower,94893745954299+c.upper)) = pointBounds13511 := by
 decide +kernel
def cuts13512 : List PrefixCut := [⟨39,295747343,295747553⟩,
⟨94,705342389,705342894⟩,
⟨128,963493172,963493864⟩]
theorem checked13512 : checkPrefixCuts (2^48) 1774977025 9 Manual.Count131072.C013512.packed 128 cuts13512 = true := by
 decide +kernel
def pointBounds13512 : List (Nat × Nat × Nat) := [(1775016960,94894637056888,94895014147563),(1775073280,94895046651934,94895423742904)]
theorem point_links_checked13512 : (cuts13512.take 2).map (fun c => (1774977025-1+2*2^9*c.k,94894341309545+c.lower,94894718400010+c.upper)) = pointBounds13512 := by
 decide +kernel
def cuts13513 : List PrefixCut := [⟨21,158725342,158725454⟩,
⟨76,582247919,582248327⟩,
⟨128,976424050,976424736⟩]
theorem checked13513 : checkPrefixCuts (2^48) 1775108097 9 Manual.Count131072.C013513.packed 128 cuts13513 = true := by
 decide +kernel
def pointBounds13513 : List (Nat × Nat × Nat) := [(1775129600,94895463528059,94895840619328),(1775185920,94895887050636,94896264142201)]
theorem point_links_checked13513 : (cuts13513.take 2).map (fun c => (1775108097-1+2*2^9*c.k,94895304802717+c.lower,94895681893874+c.upper)) = pointBounds13513 := by
 decide +kernel
def cuts13514 : List PrefixCut := [⟨3,24417607,24417625⟩,
⟨58,439192901,439193210⟩,
⟨113,852369575,852370180⟩,
⟨128,970168530,970169219⟩]
theorem checked13514 : checkPrefixCuts (2^48) 1775239169 9 Manual.Count131072.C013514.packed 128 cuts13514 = true := by
 decide +kernel
def pointBounds13514 : List (Nat × Nat × Nat) := [(1775242240,94896305644374,94896682736235),(1775298560,94896720419668,94897097511820),(1775354880,94897133596342,94897510688790)]
theorem point_links_checked13514 : (cuts13514.take 3).map (fun c => (1775239169-1+2*2^9*c.k,94896281226767+c.lower,94896658318610+c.upper)) = pointBounds13514 := by
 decide +kernel
def cuts13515 : List PrefixCut := [⟨40,310109121,310109340⟩,
⟨95,724527852,724528366⟩,
⟨128,972633748,972634436⟩]
theorem checked13515 : checkPrefixCuts (2^48) 1775370241 9 Manual.Count131072.C013515.packed 128 cuts13515 = true := by
 decide +kernel
def pointBounds13515 : List (Nat × Nat × Nat) := [(1775411200,94897561504418,94897938597169),(1775467520,94897975923149,94898353016195)]
theorem point_links_checked13515 : (cuts13515.take 2).map (fun c => (1775370241-1+2*2^9*c.k,94897251395297+c.lower,94897628487829+c.upper)) = pointBounds13515 := by
 decide +kernel
def cuts13516 : List PrefixCut := [⟨22,172957998,172958118⟩,
⟨77,594484117,594484535⟩,
⟨128,988414395,988415088⟩]
theorem checked13516 : checkPrefixCuts (2^48) 1775501313 9 Manual.Count131072.C013516.packed 128 cuts13516 = true := by
 decide +kernel
def pointBounds13516 : List (Nat × Nat × Nat) := [(1775523840,94898396987043,94898774080383),(1775580160,94898818513162,94899195606800)]
theorem point_links_checked13516 : (cuts13516.take 2).map (fun c => (1775501313-1+2*2^9*c.k,94898224029045+c.lower,94898601122265+c.upper)) = pointBounds13516 := by
 decide +kernel
def cuts13517 : List PrefixCut := [⟨4,29960418,29960440⟩,
⟨59,446228733,446229054⟩,
⟨114,877859620,877860248⟩,
⟨128,983902715,983903421⟩]
theorem checked13517 : checkPrefixCuts (2^48) 1775632385 9 Manual.Count131072.C013517.packed 128 cuts13517 = true := by
 decide +kernel
def pointBounds13517 : List (Nat × Nat × Nat) := [(1775636480,94899242403858,94899619497793),(1775692800,94899658672173,94900035766407),(1775749120,94900090303060,94900467397601)]
theorem point_links_checked13517 : (cuts13517.take 3).map (fun c => (1775632385-1+2*2^9*c.k,94899212443440+c.lower,94899589537353+c.upper)) = pointBounds13517 := by
 decide +kernel
def cuts13518 : List PrefixCut := [⟨41,308138243,308138461⟩,
⟨96,717709937,717710454⟩,
⟨128,959420850,959421541⟩]
theorem checked13518 : checkPrefixCuts (2^48) 1775763457 9 Manual.Count131072.C013518.packed 128 cuts13518 = true := by
 decide +kernel
def pointBounds13518 : List (Nat × Nat × Nat) := [(1775805440,94900504484398,94900881579235),(1775861760,94900914056092,94901291151228)]
theorem point_links_checked13518 : (cuts13518.take 2).map (fun c => (1775763457-1+2*2^9*c.k,94900196346155+c.lower,94900573440774+c.upper)) = pointBounds13518 := by
 decide +kernel
def cuts13519 : List PrefixCut := [⟨23,177357569,177357692⟩,
⟨78,605605420,605605845⟩,
⟨128,989622012,989622707⟩]
theorem checked13519 : checkPrefixCuts (2^48) 1775894529 9 Manual.Count131072.C013519.packed 128 cuts13519 = true := by
 decide +kernel
def pointBounds13519 : List (Nat × Nat × Nat) := [(1775918080,94901333124574,94901710220007),(1775974400,94901761372425,94902138468160)]
theorem point_links_checked13519 : (cuts13519.take 2).map (fun c => (1775894529-1+2*2^9*c.k,94901155767005+c.lower,94901532862315+c.upper)) = pointBounds13519 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000109
