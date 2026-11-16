import PlattAssemblyKernel
import PlattCertificates.Count131072.C018544
import PlattCertificates.Count131072.C018545
import PlattCertificates.Count131072.C018546
import PlattCertificates.Count131072.C018547
import PlattCertificates.Count131072.C018548
import PlattCertificates.Count131072.C018549
import PlattCertificates.Count131072.C018550
import PlattCertificates.Count131072.C018551
import PlattCertificates.Count131072.C018552
import PlattCertificates.Count131072.C018553
import PlattCertificates.Count131072.C018554
import PlattCertificates.Count131072.C018555
import PlattCertificates.Count131072.C018556
import PlattCertificates.Count131072.C018557
import PlattCertificates.Count131072.C018558
import PlattCertificates.Count131072.C018559
import PlattCertificates.Count131072.C018560
import PlattCertificates.Count131072.C018561
import PlattCertificates.Count131072.C018562
import PlattCertificates.Count131072.C018563
import PlattCertificates.Count131072.C018564
import PlattCertificates.Count131072.C018565
import PlattCertificates.Count131072.C018566
import PlattCertificates.Count131072.C018567
import PlattCertificates.Count131072.C018568
import PlattCertificates.Count131072.C018569
import PlattCertificates.Count131072.C018570
import PlattCertificates.Count131072.C018571
import PlattCertificates.Count131072.C018572
import PlattCertificates.Count131072.C018573
import PlattCertificates.Count131072.C018574
import PlattCertificates.Count131072.C018575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000267
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18544 : List PrefixCut := [⟨70,377486216,377486449⟩,
⟨128,691953271,691953692⟩]
theorem checked18544 : checkPrefixCuts (2^48) 2434531329 9 Manual.Count131072.C018544.packed 128 cuts18544 = true := by
 decide +kernel
def pointBounds18544 : List (Nat × Nat × Nat) := [(2434603008,99039976875190,99040356660964)]
theorem point_links_checked18544 : (cuts18544.take 1).map (fun c => (2434531329-1+2*2^9*c.k,99039599388974+c.lower,99039979174515+c.upper)) = pointBounds18544 := by
 decide +kernel
def cuts18545 : List PrefixCut := [⟨17,96997671,96997729⟩,
⟨92,516541996,516542310⟩,
⟨128,710760278,710760710⟩]
theorem checked18545 : checkPrefixCuts (2^48) 2434662401 9 Manual.Count131072.C018545.packed 128 cuts18545 = true := by
 decide +kernel
def pointBounds18545 : List (Nat × Nat × Nat) := [(2434679808,99040388339916,99040768125936),(2434756608,99040807884241,99041187670517)]
theorem point_links_checked18545 : (cuts18545.take 2).map (fun c => (2434662401-1+2*2^9*c.k,99040291342245+c.lower,99040671128207+c.upper)) = pointBounds18545 := by
 decide +kernel
def cuts18546 : List PrefixCut := [⟨39,218492144,218492276⟩,
⟨114,624369108,624369476⟩,
⟨128,699046301,699046713⟩]
theorem checked18546 : checkPrefixCuts (2^48) 2434793473 9 Manual.Count131072.C018546.packed 128 cuts18546 = true := by
 decide +kernel
def pointBounds18546 : List (Nat × Nat × Nat) := [(2434833408,99041220594667,99041600381193),(2434910208,99041626471631,99042006258393)]
theorem point_links_checked18546 : (cuts18546.take 2).map (fun c => (2434793473-1+2*2^9*c.k,99041002102523+c.lower,99041381888917+c.upper)) = pointBounds18546 := by
 decide +kernel
def cuts18547 : List PrefixCut := [⟨61,334423717,334423920⟩,
⟨128,697505858,697506281⟩]
theorem checked18547 : checkPrefixCuts (2^48) 2434924545 9 Manual.Count131072.C018547.packed 128 cuts18547 = true := by
 decide +kernel
def pointBounds18547 : List (Nat × Nat × Nat) := [(2434987008,99042035572541,99042415359550)]
theorem point_links_checked18547 : (cuts18547.take 1).map (fun c => (2434924545-1+2*2^9*c.k,99041701148824+c.lower,99042080935630+c.upper)) = pointBounds18547 := by
 decide +kernel
def cuts18548 : List PrefixCut := [⟨8,43231633,43231659⟩,
⟨83,454965300,454965575⟩,
⟨128,702900848,702901271⟩]
theorem checked18548 : checkPrefixCuts (2^48) 2435055617 9 Manual.Count131072.C018548.packed 128 cuts18548 = true := by
 decide +kernel
def pointBounds18548 : List (Nat × Nat × Nat) := [(2435063808,99042441886315,99042821673570),(2435140608,99042853619982,99043233407486)]
theorem point_links_checked18548 : (cuts18548.take 2).map (fun c => (2435055617-1+2*2^9*c.k,99042398654682+c.lower,99042778441911+c.upper)) = pointBounds18548 := by
 decide +kernel
def cuts18549 : List PrefixCut := [⟨30,164825403,164825505⟩,
⟨105,561969685,561970028⟩,
⟨128,688993098,688993516⟩]
theorem checked18549 : checkPrefixCuts (2^48) 2435186689 9 Manual.Count131072.C018549.packed 128 cuts18549 = true := by
 decide +kernel
def pointBounds18549 : List (Nat × Nat × Nat) := [(2435217408,99043266380933,99043646168687),(2435294208,99043663525215,99044043313210)]
theorem point_links_checked18549 : (cuts18549.take 2).map (fun c => (2435186689-1+2*2^9*c.k,99043101555530+c.lower,99043481343182+c.upper)) = pointBounds18549 := by
 decide +kernel
def cuts18550 : List PrefixCut := [⟨52,287445181,287445354⟩,
⟨127,705830364,705830786⟩,
⟨128,712649240,712649665⟩]
theorem checked18550 : checkPrefixCuts (2^48) 2435317761 9 Manual.Count131072.C018550.packed 128 cuts18550 = true := by
 decide +kernel
def pointBounds18550 : List (Nat × Nat × Nat) := [(2435371008,99044077993809,99044457782052),(2435447808,99044496378992,99044876167484)]
theorem point_links_checked18550 : (cuts18550.take 2).map (fun c => (2435317761-1+2*2^9*c.k,99043790548628+c.lower,99044170336698+c.upper)) = pointBounds18550 := by
 decide +kernel
def cuts18551 : List PrefixCut := [⟨74,403231899,403232136⟩,
⟨128,701400573,701400988⟩]
theorem checked18551 : checkPrefixCuts (2^48) 2435448833 9 Manual.Count131072.C018551.packed 128 cuts18551 = true := by
 decide +kernel
def pointBounds18551 : List (Nat × Nat × Nat) := [(2435524608,99044906429767,99045286218499)]
theorem point_links_checked18551 : (cuts18551.take 1).map (fun c => (2435448833-1+2*2^9*c.k,99044503197868+c.lower,99044882986363+c.upper)) = pointBounds18551 := by
 decide +kernel
def cuts18552 : List PrefixCut := [⟨21,116491941,116492013⟩,
⟨96,531023813,531024134⟩,
⟨128,699976158,699976582⟩]
theorem checked18552 : checkPrefixCuts (2^48) 2435579905 9 Manual.Count131072.C018552.packed 128 cuts18552 = true := by
 decide +kernel
def pointBounds18552 : List (Nat × Nat × Nat) := [(2435601408,99045321090382,99045700879364),(2435678208,99045735622254,99046115411485)]
theorem point_links_checked18552 : (cuts18552.take 2).map (fun c => (2435579905-1+2*2^9*c.k,99045204598441+c.lower,99045584387351+c.upper)) = pointBounds18552 := by
 decide +kernel
def cuts18553 : List PrefixCut := [⟨43,241290642,241290781⟩,
⟨118,642507330,642507724⟩,
⟨128,696934074,696934501⟩]
theorem checked18553 : checkPrefixCuts (2^48) 2435710977 9 Manual.Count131072.C018553.packed 128 cuts18553 = true := by
 decide +kernel
def pointBounds18553 : List (Nat × Nat × Nat) := [(2435755008,99046145865241,99046525654714),(2435831808,99046547081929,99046926871657)]
theorem point_links_checked18553 : (cuts18553.take 2).map (fun c => (2435710977-1+2*2^9*c.k,99045904574599+c.lower,99046284363933+c.upper)) = pointBounds18553 := by
 decide +kernel
def cuts18554 : List PrefixCut := [⟨65,352670533,352670750⟩,
⟨128,695509692,695510114⟩]
theorem checked18554 : checkPrefixCuts (2^48) 2435842049 9 Manual.Count131072.C018554.packed 128 cuts18554 = true := by
 decide +kernel
def pointBounds18554 : List (Nat × Nat × Nat) := [(2435908608,99046954179206,99047333969184)]
theorem point_links_checked18554 : (cuts18554.take 1).map (fun c => (2435842049-1+2*2^9*c.k,99046601508673+c.lower,99046981298434+c.upper)) = pointBounds18554 := by
 decide +kernel
def cuts18555 : List PrefixCut := [⟨12,65285169,65285210⟩,
⟨87,475938727,475939014⟩,
⟨128,699516442,699516862⟩]
theorem checked18555 : checkPrefixCuts (2^48) 2435973121 9 Manual.Count131072.C018555.packed 128 cuts18555 = true := by
 decide +kernel
def pointBounds18555 : List (Nat × Nat × Nat) := [(2435985408,99047362303534,99047742093758),(2436062208,99047772957092,99048152747562)]
theorem point_links_checked18555 : (cuts18555.take 2).map (fun c => (2435973121-1+2*2^9*c.k,99047297018365+c.lower,99047676808548+c.upper)) = pointBounds18555 := by
 decide +kernel
def cuts18556 : List PrefixCut := [⟨34,186254042,186254151⟩,
⟨109,588100671,588101025⟩,
⟨128,691044393,691044808⟩]
theorem checked18556 : checkPrefixCuts (2^48) 2436104193 9 Manual.Count131072.C018556.packed 128 cuts18556 = true := by
 decide +kernel
def pointBounds18556 : List (Nat × Nat × Nat) := [(2436139008,99048182788849,99048562579561),(2436215808,99048584635478,99048964426435)]
theorem point_links_checked18556 : (cuts18556.take 2).map (fun c => (2436104193-1+2*2^9*c.k,99047996534807+c.lower,99048376325410+c.upper)) = pointBounds18556 := by
 decide +kernel
def cuts18557 : List PrefixCut := [⟨56,309981603,309981797⟩,
⟨128,703022737,703023164⟩]
theorem checked18557 : checkPrefixCuts (2^48) 2436235265 9 Manual.Count131072.C018557.packed 128 cuts18557 = true := by
 decide +kernel
def pointBounds18557 : List (Nat × Nat × Nat) := [(2436292608,99048997560803,99049377352015)]
theorem point_links_checked18557 : (cuts18557.take 1).map (fun c => (2436235265-1+2*2^9*c.k,99048687579200+c.lower,99049067370218+c.upper)) = pointBounds18557 := by
 decide +kernel
def cuts18558 : List PrefixCut := [⟨3,18369356,18369367⟩,
⟨78,428033940,428034202⟩,
⟨128,704024585,704025010⟩]
theorem checked18558 : checkPrefixCuts (2^48) 2436366337 9 Manual.Count131072.C018558.packed 128 cuts18558 = true := by
 decide +kernel
def pointBounds18558 : List (Nat × Nat × Nat) := [(2436369408,99049408971293,99049788762749),(2436446208,99049818635877,99050198427584)]
theorem point_links_checked18558 : (cuts18558.take 2).map (fun c => (2436366337-1+2*2^9*c.k,99049390601937+c.lower,99049770393382+c.upper)) = pointBounds18558 := by
 decide +kernel
def cuts18559 : List PrefixCut := [⟨25,135855984,135856065⟩,
⟨100,551501887,551502217⟩,
⟨128,704102305,704102724⟩]
theorem checked18559 : checkPrefixCuts (2^48) 2436497409 9 Manual.Count131072.C018559.packed 128 cuts18559 = true := by
 decide +kernel
def pointBounds18559 : List (Nat × Nat × Nat) := [(2436523008,99050230482506,99050610274457),(2436599808,99050646128409,99051025920609)]
theorem point_links_checked18559 : (cuts18559.take 2).map (fun c => (2436497409-1+2*2^9*c.k,99050094626522+c.lower,99050474418392+c.upper)) = pointBounds18559 := by
 decide +kernel
def cuts18560 : List PrefixCut := [⟨47,260837538,260837698⟩,
⟨122,671605621,671606029⟩,
⟨128,704873110,704873538⟩]
theorem checked18560 : checkPrefixCuts (2^48) 2436628481 9 Manual.Count131072.C018560.packed 128 cuts18560 = true := by
 decide +kernel
def pointBounds18560 : List (Nat × Nat × Nat) := [(2436676608,99051059566365,99051439358814),(2436753408,99051470334448,99051850127145)]
theorem point_links_checked18560 : (cuts18560.take 2).map (fun c => (2436628481-1+2*2^9*c.k,99050798728827+c.lower,99051178521116+c.upper)) = pointBounds18560 := by
 decide +kernel
def cuts18561 : List PrefixCut := [⟨69,381299452,381299681⟩,
⟨128,706914227,706914647⟩]
theorem checked18561 : checkPrefixCuts (2^48) 2436759553 9 Manual.Count131072.C018561.packed 128 cuts18561 = true := by
 decide +kernel
def pointBounds18561 : List (Nat × Nat × Nat) := [(2436830208,99051884901389,99052264694335)]
theorem point_links_checked18561 : (cuts18561.take 1).map (fun c => (2436759553-1+2*2^9*c.k,99051503601937+c.lower,99051883394654+c.upper)) = pointBounds18561 := by
 decide +kernel
def cuts18562 : List PrefixCut := [⟨16,83510382,83510432⟩,
⟨91,492391586,492391880⟩,
⟨128,691283335,691283755⟩]
theorem checked18562 : checkPrefixCuts (2^48) 2436890625 9 Manual.Count131072.C018562.packed 128 cuts18562 = true := by
 decide +kernel
def pointBounds18562 : List (Nat × Nat × Nat) := [(2436907008,99052294026546,99052673819733),(2436983808,99052702907750,99053082701181)]
theorem point_links_checked18562 : (cuts18562.take 2).map (fun c => (2436890625-1+2*2^9*c.k,99052210516164+c.lower,99052590309301+c.upper)) = pointBounds18562 := by
 decide +kernel
def cuts18563 : List PrefixCut := [⟨38,211016015,211016141⟩,
⟨113,625646242,625646615⟩,
⟨128,706838313,706838734⟩]
theorem checked18563 : checkPrefixCuts (2^48) 2437021697 9 Manual.Count131072.C018563.packed 128 cuts18563 = true := by
 decide +kernel
def pointBounds18563 : List (Nat × Nat × Nat) := [(2437060608,99053112815514,99053492609197),(2437137408,99053527445741,99053907239671)]
theorem point_links_checked18563 : (cuts18563.take 2).map (fun c => (2437021697-1+2*2^9*c.k,99052901799499+c.lower,99053281593056+c.upper)) = pointBounds18563 := by
 decide +kernel
def cuts18564 : List PrefixCut := [⟨60,330191264,330191459⟩,
⟨128,708301469,708301890⟩]
theorem checked18564 : checkPrefixCuts (2^48) 2437152769 9 Manual.Count131072.C018564.packed 128 cuts18564 = true := by
 decide +kernel
def pointBounds18564 : List (Nat × Nat × Nat) := [(2437214208,99053938829076,99054318623249)]
theorem point_links_checked18564 : (cuts18564.take 1).map (fun c => (2437152769-1+2*2^9*c.k,99053608637812+c.lower,99053988431790+c.upper)) = pointBounds18564 := by
 decide +kernel
def cuts18565 : List PrefixCut := [⟨7,37648747,37648768⟩,
⟨82,449699072,449699339⟩,
⟨128,696946085,696946501⟩]
theorem checked18565 : checkPrefixCuts (2^48) 2437283841 9 Manual.Count131072.C018565.packed 128 cuts18565 = true := by
 decide +kernel
def pointBounds18565 : List (Nat × Nat × Nat) := [(2437291008,99054354588028,99054734382448),(2437367808,99054766638353,99055146433019)]
theorem point_links_checked18565 : (cuts18565.take 2).map (fun c => (2437283841-1+2*2^9*c.k,99054316939281+c.lower,99054696733680+c.upper)) = pointBounds18565 := by
 decide +kernel
def cuts18566 : List PrefixCut := [⟨29,155551839,155551930⟩,
⟨104,566421456,566421794⟩,
⟨128,698871608,698872028⟩]
theorem checked18566 : checkPrefixCuts (2^48) 2437414913 9 Manual.Count131072.C018566.packed 128 cuts18566 = true := by
 decide +kernel
def pointBounds18566 : List (Nat × Nat × Nat) := [(2437444608,99055169437205,99055549232111),(2437521408,99055580306822,99055960101975)]
theorem point_links_checked18566 : (cuts18566.take 2).map (fun c => (2437414913-1+2*2^9*c.k,99055013885366+c.lower,99055393680181+c.upper)) = pointBounds18566 := by
 decide +kernel
def cuts18567 : List PrefixCut := [⟨51,276674442,276674605⟩,
⟨126,695601079,695601493⟩,
⟨128,705993248,705993668⟩]
theorem checked18567 : checkPrefixCuts (2^48) 2437545985 9 Manual.Count131072.C018567.packed 128 cuts18567 = true := by
 decide +kernel
def pointBounds18567 : List (Nat × Nat × Nat) := [(2437598208,99055989431416,99056369226814),(2437675008,99056408358053,99056788153702)]
theorem point_links_checked18567 : (cuts18567.take 2).map (fun c => (2437545985-1+2*2^9*c.k,99055712756974+c.lower,99056092552209+c.upper)) = pointBounds18567 := by
 decide +kernel
def cuts18568 : List PrefixCut := [⟨73,397782914,397783152⟩,
⟨128,695679056,695679474⟩]
theorem checked18568 : checkPrefixCuts (2^48) 2437677057 9 Manual.Count131072.C018568.packed 128 cuts18568 = true := by
 decide +kernel
def pointBounds18568 : List (Nat × Nat × Nat) := [(2437751808,99056816533136,99057196329029)]
theorem point_links_checked18568 : (cuts18568.take 1).map (fun c => (2437677057-1+2*2^9*c.k,99056418750222+c.lower,99056798545877+c.upper)) = pointBounds18568 := by
 decide +kernel
def cuts18569 : List PrefixCut := [⟨20,112459802,112459871⟩,
⟨95,526035761,526036079⟩,
⟨128,702915712,702916137⟩]
theorem checked18569 : checkPrefixCuts (2^48) 2437808129 9 Manual.Count131072.C018569.packed 128 cuts18569 = true := by
 decide +kernel
def pointBounds18569 : List (Nat × Nat × Nat) := [(2437828608,99057226889080,99057606685222),(2437905408,99057640465039,99058020261430)]
theorem point_links_checked18569 : (cuts18569.take 2).map (fun c => (2437808129-1+2*2^9*c.k,99057114429278+c.lower,99057494225351+c.upper)) = pointBounds18569 := by
 decide +kernel
def cuts18570 : List PrefixCut := [⟨42,232180106,232180243⟩,
⟨117,646769014,646769397⟩,
⟨128,707264881,707265300⟩]
theorem checked18570 : checkPrefixCuts (2^48) 2437939201 9 Manual.Count131072.C018570.packed 128 cuts18570 = true := by
 decide +kernel
def pointBounds18570 : List (Nat × Nat × Nat) := [(2437982208,99058049525096,99058429321731),(2438059008,99058464114004,99058843910885)]
theorem point_links_checked18570 : (cuts18570.take 2).map (fun c => (2437939201-1+2*2^9*c.k,99057817344990+c.lower,99058197141488+c.upper)) = pointBounds18570 := by
 decide +kernel
def cuts18571 : List PrefixCut := [⟨64,351309214,351309423⟩,
⟨128,701685420,701685839⟩]
theorem checked18571 : checkPrefixCuts (2^48) 2438070273 9 Manual.Count131072.C018571.packed 128 cuts18571 = true := by
 decide +kernel
def pointBounds18571 : List (Nat × Nat × Nat) := [(2438135808,99058875919085,99059255716211)]
theorem point_links_checked18571 : (cuts18571.take 1).map (fun c => (2438070273-1+2*2^9*c.k,99058524609871+c.lower,99058904406788+c.upper)) = pointBounds18571 := by
 decide +kernel
def cuts18572 : List PrefixCut := [⟨11,60376889,60376925⟩,
⟨86,461766296,461766579⟩,
⟨128,695875536,695875960⟩]
theorem checked18572 : checkPrefixCuts (2^48) 2438201345 9 Manual.Count131072.C018572.packed 128 cuts18572 = true := by
 decide +kernel
def pointBounds18572 : List (Nat × Nat × Nat) := [(2438212608,99059286672180,99059666469552),(2438289408,99059688061587,99060067859206)]
theorem point_links_checked18572 : (cuts18572.take 2).map (fun c => (2438201345-1+2*2^9*c.k,99059226295291+c.lower,99059606092627+c.upper)) = pointBounds18572 := by
 decide +kernel
def cuts18573 : List PrefixCut := [⟨33,179388572,179388680⟩,
⟨108,593796779,593797136⟩,
⟨128,704495805,704496227⟩]
theorem checked18573 : checkPrefixCuts (2^48) 2438332417 9 Manual.Count131072.C018573.packed 128 cuts18573 = true := by
 decide +kernel
def pointBounds18573 : List (Nat × Nat × Nat) := [(2438366208,99060101559399,99060481357267),(2438443008,99060515967606,99060895765723)]
theorem point_links_checked18573 : (cuts18573.take 2).map (fun c => (2438332417-1+2*2^9*c.k,99059922170827+c.lower,99060301968587+c.upper)) = pointBounds18573 := by
 decide +kernel
def cuts18574 : List PrefixCut := [⟨55,297809194,297809375⟩,
⟨128,695454630,695455051⟩]
theorem checked18574 : checkPrefixCuts (2^48) 2438463489 9 Manual.Count131072.C018574.packed 128 cuts18574 = true := by
 decide +kernel
def pointBounds18574 : List (Nat × Nat × Nat) := [(2438519808,99060924475826,99061304274189)]
theorem point_links_checked18574 : (cuts18574.take 1).map (fun c => (2438463489-1+2*2^9*c.k,99060626666632+c.lower,99061006464814+c.upper)) = pointBounds18574 := by
 decide +kernel
def cuts18575 : List PrefixCut := [⟨2,9580275,9580281⟩,
⟨77,427873723,427873983⟩,
⟨128,703381469,703381900⟩]
theorem checked18575 : checkPrefixCuts (2^48) 2438594561 9 Manual.Count131072.C018575.packed 128 cuts18575 = true := by
 decide +kernel
def pointBounds18575 : List (Nat × Nat × Nat) := [(2438596608,99061331701537,99061711500146),(2438673408,99061749994985,99062129793848)]
theorem point_links_checked18575 : (cuts18575.take 2).map (fun c => (2438594561-1+2*2^9*c.k,99061322121262+c.lower,99061701919865+c.upper)) = pointBounds18575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000267
