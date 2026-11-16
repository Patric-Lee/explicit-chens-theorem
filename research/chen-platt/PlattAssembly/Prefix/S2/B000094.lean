import PlattAssemblyKernel
import PlattCertificates.Count131072.C013008
import PlattCertificates.Count131072.C013009
import PlattCertificates.Count131072.C013010
import PlattCertificates.Count131072.C013011
import PlattCertificates.Count131072.C013012
import PlattCertificates.Count131072.C013013
import PlattCertificates.Count131072.C013014
import PlattCertificates.Count131072.C013015
import PlattCertificates.Count131072.C013016
import PlattCertificates.Count131072.C013017
import PlattCertificates.Count131072.C013018
import PlattCertificates.Count131072.C013019
import PlattCertificates.Count131072.C013020
import PlattCertificates.Count131072.C013021
import PlattCertificates.Count131072.C013022
import PlattCertificates.Count131072.C013023
import PlattCertificates.Count131072.C013024
import PlattCertificates.Count131072.C013025
import PlattCertificates.Count131072.C013026
import PlattCertificates.Count131072.C013027
import PlattCertificates.Count131072.C013028
import PlattCertificates.Count131072.C013029
import PlattCertificates.Count131072.C013030
import PlattCertificates.Count131072.C013031
import PlattCertificates.Count131072.C013032
import PlattCertificates.Count131072.C013033
import PlattCertificates.Count131072.C013034
import PlattCertificates.Count131072.C013035
import PlattCertificates.Count131072.C013036
import PlattCertificates.Count131072.C013037
import PlattCertificates.Count131072.C013038
import PlattCertificates.Count131072.C013039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13008 : List PrefixCut := [⟨5,43318543,43318573⟩,
⟨58,464802311,464802646⟩,
⟨111,890554866,890555510⟩,
⟨128,1025771710,1025772452⟩]
theorem checked13008 : checkPrefixCuts (2^48) 1708916737 9 Manual.Count131072.C013008.packed 128 cuts13008 = true := by
 decide +kernel
def pointBounds13008 : List (Nat × Nat × Nat) := [(1708921856,94392686554865,94393063285737),(1708976128,94393108038633,94393484769810),(1709030400,94393533791188,94393910522674)]
theorem point_links_checked13008 : (cuts13008.take 3).map (fun c => (1708916737-1+2*2^9*c.k,94392643236322+c.lower,94393019967164+c.upper)) = pointBounds13008 := by
 decide +kernel
def cuts13009 : List PrefixCut := [⟨36,286898890,286899102⟩,
⟨89,709989429,709989952⟩,
⟨128,1019105380,1019106124⟩]
theorem checked13009 : checkPrefixCuts (2^48) 1709047809 9 Manual.Count131072.C013009.packed 128 cuts13009 = true := by
 decide +kernel
def pointBounds13009 : List (Nat × Nat × Nat) := [(1709084672,94393955906922,94394332638718),(1709138944,94394378997461,94394755729568)]
theorem point_links_checked13009 : (cuts13009.take 2).map (fun c => (1709047809-1+2*2^9*c.k,94393669008032+c.lower,94394045739616+c.upper)) = pointBounds13009 := by
 decide +kernel
def cuts13010 : List PrefixCut := [⟨14,110337998,110338081⟩,
⟨67,546740785,546741185⟩,
⟨120,969461566,969462271⟩,
⟨128,1032201615,1032202366⟩]
theorem checked13010 : checkPrefixCuts (2^48) 1709178881 9 Manual.Count131072.C013010.packed 128 cuts13010 = true := by
 decide +kernel
def pointBounds13010 : List (Nat × Nat × Nat) := [(1709193216,94394798451410,94395175183821),(1709247488,94395234854197,94395611586925),(1709301760,94395657574978,94396034308011)]
theorem point_links_checked13010 : (cuts13010.take 3).map (fun c => (1709178881-1+2*2^9*c.k,94394688113412+c.lower,94395064845740+c.upper)) = pointBounds13010 := by
 decide +kernel
def cuts13011 : List PrefixCut := [⟨45,360955360,360955623⟩,
⟨98,782661354,782661927⟩,
⟨128,1017467172,1017467920⟩]
theorem checked13011 : checkPrefixCuts (2^48) 1709309953 9 Manual.Count131072.C013011.packed 128 cuts13011 = true := by
 decide +kernel
def pointBounds13011 : List (Nat × Nat × Nat) := [(1709356032,94396081270387,94396458003729),(1709410304,94396502976381,94396879710033)]
theorem point_links_checked13011 : (cuts13011.take 2).map (fun c => (1709309953-1+2*2^9*c.k,94395720315027+c.lower,94396097048106+c.upper)) = pointBounds13011 := by
 decide +kernel
def cuts13012 : List PrefixCut := [⟨23,183758192,183758322⟩,
⟨76,606260626,606261067⟩,
⟨128,1028255890,1028256637⟩]
theorem checked13012 : checkPrefixCuts (2^48) 1709441025 9 Manual.Count131072.C013012.packed 128 cuts13012 = true := by
 decide +kernel
def pointBounds13012 : List (Nat × Nat × Nat) := [(1709464576,94396921540391,94397298274348),(1709518848,94397344042825,94397720777093)]
theorem point_links_checked13012 : (cuts13012.take 2).map (fun c => (1709441025-1+2*2^9*c.k,94396737782199+c.lower,94397114516026+c.upper)) = pointBounds13012 := by
 decide +kernel
def cuts13013 : List PrefixCut := [⟨1,8561610,8561616⟩,
⟨54,432683738,432684053⟩,
⟨107,856298410,856299034⟩,
⟨128,1032951553,1032952303⟩]
theorem checked13013 : checkPrefixCuts (2^48) 1709572097 9 Manual.Count131072.C013013.packed 128 cuts13013 = true := by
 decide +kernel
def pointBounds13013 : List (Nat × Nat × Nat) := [(1709573120,94397774599699,94398151334279),(1709627392,94398198721827,94398575456716),(1709681664,94398622336499,94398999071697)]
theorem point_links_checked13013 : (cuts13013.take 3).map (fun c => (1709572097-1+2*2^9*c.k,94397766038089+c.lower,94398142772663+c.upper)) = pointBounds13013 := by
 decide +kernel
def cuts13014 : List PrefixCut := [⟨32,246125072,246125251⟩,
⟨85,669712930,669713415⟩,
⟨128,1012458527,1012459256⟩]
theorem checked13014 : checkPrefixCuts (2^48) 1709703169 9 Manual.Count131072.C013014.packed 128 cuts13014 = true := by
 decide +kernel
def pointBounds13014 : List (Nat × Nat × Nat) := [(1709735936,94399045114714,94399421850217),(1709790208,94399468702572,94399845438381)]
theorem point_links_checked13014 : (cuts13014.take 2).map (fun c => (1709703169-1+2*2^9*c.k,94398798989642+c.lower,94399175724966+c.upper)) = pointBounds13014 := by
 decide +kernel
def cuts13015 : List PrefixCut := [⟨10,81816464,81816522⟩,
⟨63,499615841,499616202⟩,
⟨116,918883502,918884170⟩,
⟨128,1008760087,1008760821⟩]
theorem checked13015 : checkPrefixCuts (2^48) 1709834241 9 Manual.Count131072.C013015.packed 128 cuts13015 = true := by
 decide +kernel
def pointBounds13015 : List (Nat × Nat × Nat) := [(1709844480,94399893264633,94400270000744),(1709898752,94400311064010,94400687800424),(1709953024,94400730331671,94401107068392)]
theorem point_links_checked13015 : (cuts13015.take 3).map (fun c => (1709834241-1+2*2^9*c.k,94399811448169+c.lower,94400188184222+c.upper)) = pointBounds13015 := by
 decide +kernel
def cuts13016 : List PrefixCut := [⟨41,332175870,332176107⟩,
⟨94,756519478,756520017⟩,
⟨128,1022015383,1022016115⟩]
theorem checked13016 : checkPrefixCuts (2^48) 1709965313 9 Manual.Count131072.C013016.packed 128 cuts13016 = true := by
 decide +kernel
def pointBounds13016 : List (Nat × Nat × Nat) := [(1710007296,94401152384126,94401529121150),(1710061568,94401576727734,94401953465060)]
theorem point_links_checked13016 : (cuts13016.take 2).map (fun c => (1709965313-1+2*2^9*c.k,94400820208256+c.lower,94401196945043+c.upper)) = pointBounds13016 := by
 decide +kernel
def cuts13017 : List PrefixCut := [⟨19,152250343,152250455⟩,
⟨72,570477243,570477659⟩,
⟨125,985399114,985399831⟩,
⟨128,1009428296,1009429032⟩]
theorem checked13017 : checkPrefixCuts (2^48) 1710096385 9 Manual.Count131072.C013017.packed 128 cuts13017 = true := by
 decide +kernel
def pointBounds13017 : List (Nat × Nat × Nat) := [(1710115840,94401994473982,94402371211613),(1710170112,94402412700882,94402789438817),(1710224384,94402827622753,94403204360989)]
theorem point_links_checked13017 : (cuts13017.take 3).map (fun c => (1710096385-1+2*2^9*c.k,94401842223639+c.lower,94402218961158+c.upper)) = pointBounds13017 := by
 decide +kernel
def cuts13018 : List PrefixCut := [⟨50,396639798,396640083⟩,
⟨103,813510223,813510812⟩,
⟨128,1008857139,1008857871⟩]
theorem checked13018 : checkPrefixCuts (2^48) 1710227457 9 Manual.Count131072.C013018.packed 128 cuts13018 = true := by
 decide +kernel
def pointBounds13018 : List (Nat × Nat × Nat) := [(1710278656,94403248291733,94403625030273),(1710332928,94403665162158,94404041901002)]
theorem point_links_checked13018 : (cuts13018.take 2).map (fun c => (1710227457-1+2*2^9*c.k,94402851651935+c.lower,94403228390190+c.upper)) = pointBounds13018 := by
 decide +kernel
def cuts13019 : List PrefixCut := [⟨28,217725194,217725350⟩,
⟨81,639341540,639342008⟩,
⟨128,1011248037,1011248772⟩]
theorem checked13019 : checkPrefixCuts (2^48) 1710358529 9 Manual.Count131072.C013019.packed 128 cuts13019 = true := by
 decide +kernel
def pointBounds13019 : List (Nat × Nat × Nat) := [(1710387200,94404078234268,94404454973411),(1710441472,94404499850614,94404876590069)]
theorem point_links_checked13019 : (cuts13019.take 2).map (fun c => (1710358529-1+2*2^9*c.k,94403860509074+c.lower,94404237248061+c.upper)) = pointBounds13019 := by
 decide +kernel
def cuts13020 : List PrefixCut := [⟨6,49367331,49367368⟩,
⟨59,479184618,479184966⟩,
⟨112,897634344,897634996⟩,
⟨128,1022689498,1022690243⟩]
theorem checked13020 : checkPrefixCuts (2^48) 1710489601 9 Manual.Count131072.C013020.packed 128 cuts13020 = true := by
 decide +kernel
def pointBounds13020 : List (Nat × Nat × Nat) := [(1710495744,94404921124442,94405297864201),(1710550016,94405350941729,94405727681799),(1710604288,94405769391455,94406146131829)]
theorem point_links_checked13020 : (cuts13020.take 3).map (fun c => (1710489601-1+2*2^9*c.k,94404871757111+c.lower,94405248496833+c.upper)) = pointBounds13020 := by
 decide +kernel
def cuts13021 : List PrefixCut := [⟨37,299798546,299798761⟩,
⟨90,717563716,717564235⟩,
⟨128,1022940201,1022940945⟩]
theorem checked13021 : checkPrefixCuts (2^48) 1710620673 9 Manual.Count131072.C013021.packed 128 cuts13021 = true := by
 decide +kernel
def pointBounds13021 : List (Nat × Nat × Nat) := [(1710658560,94406194245155,94406570985837),(1710712832,94406612010325,94406988751311)]
theorem point_links_checked13021 : (cuts13021.take 2).map (fun c => (1710620673-1+2*2^9*c.k,94405894446609+c.lower,94406271187076+c.upper)) = pointBounds13021 := by
 decide +kernel
def cuts13022 : List PrefixCut := [⟨15,113362633,113362716⟩,
⟨68,534062658,534063046⟩,
⟨121,945371514,945372200⟩,
⟨128,1001473039,1001473766⟩]
theorem checked13022 : checkPrefixCuts (2^48) 1710751745 9 Manual.Count131072.C013022.packed 128 cuts13022 = true := by
 decide +kernel
def pointBounds13022 : List (Nat × Nat × Nat) := [(1710767104,94407030749443,94407407490737),(1710821376,94407451449468,94407828191067),(1710875648,94407862758324,94408239500221)]
theorem point_links_checked13022 : (cuts13022.take 3).map (fun c => (1710751745-1+2*2^9*c.k,94406917386810+c.lower,94407294128021+c.upper)) = pointBounds13022 := by
 decide +kernel
def cuts13023 : List PrefixCut := [⟨46,353878267,353878525⟩,
⟨99,776183468,776184035⟩,
⟨128,1005015577,1005016312⟩]
theorem checked13023 : checkPrefixCuts (2^48) 1710882817 9 Manual.Count131072.C013023.packed 128 cuts13023 = true := by
 decide +kernel
def pointBounds13023 : List (Nat × Nat × Nat) := [(1710929920,94408272738116,94408649480312),(1710984192,94408695043317,94409071785822)]
theorem point_links_checked13023 : (cuts13023.take 2).map (fun c => (1710882817-1+2*2^9*c.k,94407918859849+c.lower,94408295601787+c.upper)) = pointBounds13023 := by
 decide +kernel
def cuts13024 : List PrefixCut := [⟨24,188195360,188195497⟩,
⟨77,612612323,612612766⟩,
⟨128,1020401770,1020402508⟩]
theorem checked13024 : checkPrefixCuts (2^48) 1711013889 9 Manual.Count131072.C013024.packed 128 cuts13024 = true := by
 decide +kernel
def pointBounds13024 : List (Nat × Nat × Nat) := [(1711038464,94409112070786,94409488813596),(1711092736,94409536487749,94409913230865)]
theorem point_links_checked13024 : (cuts13024.take 2).map (fun c => (1711013889-1+2*2^9*c.k,94408923875426+c.lower,94409300618099+c.upper)) = pointBounds13024 := by
 decide +kernel
def cuts13025 : List PrefixCut := [⟨2,15956011,15956023⟩,
⟨55,440839537,440839857⟩,
⟨108,871137610,871138241⟩,
⟨128,1030028623,1030029370⟩]
theorem checked13025 : checkPrefixCuts (2^48) 1711144961 9 Manual.Count131072.C013025.packed 128 cuts13025 = true := by
 decide +kernel
def pointBounds13025 : List (Nat × Nat × Nat) := [(1711147008,94409960233207,94410336976630),(1711201280,94410385116733,94410761860464),(1711255552,94410815414806,94411192158848)]
theorem point_links_checked13025 : (cuts13025.take 3).map (fun c => (1711144961-1+2*2^9*c.k,94409944277196+c.lower,94410321020607+c.upper)) = pointBounds13025 := by
 decide +kernel
def cuts13026 : List PrefixCut := [⟨33,260208665,260208849⟩,
⟨86,678472665,678473150⟩,
⟨128,1010048111,1010048838⟩]
theorem checked13026 : checkPrefixCuts (2^48) 1711276033 9 Manual.Count131072.C013026.packed 128 cuts13026 = true := by
 decide +kernel
def pointBounds13026 : List (Nat × Nat × Nat) := [(1711309824,94411234514484,94411611258826),(1711364096,94411652778484,94412029523127)]
theorem point_links_checked13026 : (cuts13026.take 2).map (fun c => (1711276033-1+2*2^9*c.k,94410974305819+c.lower,94411351049977+c.upper)) = pointBounds13026 := by
 decide +kernel
def cuts13027 : List PrefixCut := [⟨11,85852984,85853046⟩,
⟨64,505077124,505077493⟩,
⟨117,924287966,924288637⟩,
⟨128,1014246383,1014247116⟩]
theorem checked13027 : checkPrefixCuts (2^48) 1711407105 9 Manual.Count131072.C013027.packed 128 cuts13027 = true := by
 decide +kernel
def pointBounds13027 : List (Nat × Nat × Nat) := [(1711418368,94412070206914,94412446951861),(1711472640,94412489431054,94412866176308),(1711526912,94412908641896,94413285387452)]
theorem point_links_checked13027 : (cuts13027.take 3).map (fun c => (1711407105-1+2*2^9*c.k,94411984353930+c.lower,94412361098815+c.upper)) = pointBounds13027 := by
 decide +kernel
def cuts13028 : List PrefixCut := [⟨42,326114679,326114917⟩,
⟨95,742667881,742668418⟩,
⟨128,1006604174,1006604903⟩]
theorem checked13028 : checkPrefixCuts (2^48) 1711538177 9 Manual.Count131072.C013028.packed 128 cuts13028 = true := by
 decide +kernel
def pointBounds13028 : List (Nat × Nat × Nat) := [(1711581184,94413324714992,94413701460848),(1711635456,94413741268194,94414118014349)]
theorem point_links_checked13028 : (cuts13028.take 2).map (fun c => (1711538177-1+2*2^9*c.k,94412998600313+c.lower,94413375345931+c.upper)) = pointBounds13028 := by
 decide +kernel
def cuts13029 : List PrefixCut := [⟨20,159839246,159839361⟩,
⟨73,568143831,568144246⟩,
⟨126,991728068,991728792⟩,
⟨128,1007842420,1007843156⟩]
theorem checked13029 : checkPrefixCuts (2^48) 1711669249 9 Manual.Count131072.C013029.packed 128 cuts13029 = true := by
 decide +kernel
def pointBounds13029 : List (Nat × Nat × Nat) := [(1711689728,94414165043733,94414541790195),(1711744000,94414573348318,94414950095080),(1711798272,94414996932555,94415373679626)]
theorem point_links_checked13029 : (cuts13029.take 3).map (fun c => (1711669249-1+2*2^9*c.k,94414005204487+c.lower,94414381950834+c.upper)) = pointBounds13029 := by
 decide +kernel
def cuts13030 : List PrefixCut := [⟨51,413047118,413047419⟩,
⟨104,834795776,834796380⟩,
⟨128,1021577619,1021578361⟩]
theorem checked13030 : checkPrefixCuts (2^48) 1711800321 9 Manual.Count131072.C013030.packed 128 cuts13030 = true := by
 decide +kernel
def pointBounds13030 : List (Nat × Nat × Nat) := [(1711852544,94415426094025,94415802841409),(1711906816,94415847842683,94416224590370)]
theorem point_links_checked13030 : (cuts13030.take 2).map (fun c => (1711800321-1+2*2^9*c.k,94415013046907+c.lower,94415389793990+c.upper)) = pointBounds13030 := by
 decide +kernel
def cuts13031 : List PrefixCut := [⟨29,232158294,232158462⟩,
⟨82,652236200,652236669⟩,
⟨128,1012127860,1012128589⟩]
theorem checked13031 : checkPrefixCuts (2^48) 1711931393 9 Manual.Count131072.C013031.packed 128 cuts13031 = true := by
 decide +kernel
def pointBounds13031 : List (Nat × Nat × Nat) := [(1711961088,94416266782820,94416643530813),(1712015360,94416686860726,94417063609020)]
theorem point_links_checked13031 : (cuts13031.take 2).map (fun c => (1711931393-1+2*2^9*c.k,94416034624526+c.lower,94416411372351+c.upper)) = pointBounds13031 := by
 decide +kernel
def cuts13032 : List PrefixCut := [⟨7,53267715,53267753⟩,
⟨60,468715563,468715902⟩,
⟨113,884972337,884972979⟩,
⟨128,997418557,997419280⟩]
theorem checked13032 : checkPrefixCuts (2^48) 1712062465 9 Manual.Count131072.C013032.packed 128 cuts13032 = true := by
 decide +kernel
def pointBounds13032 : List (Nat × Nat × Nat) := [(1712069632,94417100020101,94417476768693),(1712123904,94417515467949,94417892216842),(1712178176,94417931724723,94418308473919)]
theorem point_links_checked13032 : (cuts13032.take 3).map (fun c => (1712062465-1+2*2^9*c.k,94417046752386+c.lower,94417423500940+c.upper)) = pointBounds13032 := by
 decide +kernel
def cuts13033 : List PrefixCut := [⟨38,308071410,308071629⟩,
⟨91,720685237,720685754⟩,
⟨128,1005890729,1005891454⟩]
theorem checked13033 : checkPrefixCuts (2^48) 1712193537 9 Manual.Count131072.C013033.packed 128 cuts13033 = true := by
 decide +kernel
def pointBounds13033 : List (Nat × Nat × Nat) := [(1712232448,94418352242353,94418728991849),(1712286720,94418764856180,94419141605974)]
theorem point_links_checked13033 : (cuts13033.take 2).map (fun c => (1712193537-1+2*2^9*c.k,94418044170943+c.lower,94418420920220+c.upper)) = pointBounds13033 := by
 decide +kernel
def cuts13034 : List PrefixCut := [⟨16,123121312,123121402⟩,
⟨69,546557895,546558289⟩,
⟨122,972610993,972611700⟩,
⟨128,1022414936,1022415677⟩]
theorem checked13034 : checkPrefixCuts (2^48) 1712324609 9 Manual.Count131072.C013034.packed 128 cuts13034 = true := by
 decide +kernel
def pointBounds13034 : List (Nat × Nat × Nat) := [(1712340992,94419173182984,94419549933076),(1712395264,94419596619567,94419973369963),(1712449536,94420022672665,94420399423374)]
theorem point_links_checked13034 : (cuts13034.take 3).map (fun c => (1712324609-1+2*2^9*c.k,94419050061672+c.lower,94419426811674+c.upper)) = pointBounds13034 := by
 decide +kernel
def cuts13035 : List PrefixCut := [⟨47,367524225,367524495⟩,
⟨100,794865249,794865824⟩,
⟨128,1011489047,1011489779⟩]
theorem checked13035 : checkPrefixCuts (2^48) 1712455681 9 Manual.Count131072.C013035.packed 128 cuts13035 = true := by
 decide +kernel
def pointBounds13035 : List (Nat × Nat × Nat) := [(1712503808,94420440000833,94420816751846),(1712558080,94420867341857,94421244093175)]
theorem point_links_checked13035 : (cuts13035.take 2).map (fun c => (1712455681-1+2*2^9*c.k,94420072476608+c.lower,94420449227351+c.upper)) = pointBounds13035 := by
 decide +kernel
def cuts13036 : List PrefixCut := [⟨25,198541250,198541396⟩,
⟨78,613857457,613857905⟩,
⟨128,1008124547,1008125280⟩]
theorem checked13036 : checkPrefixCuts (2^48) 1712586753 9 Manual.Count131072.C013036.packed 128 cuts13036 = true := by
 decide +kernel
def pointBounds13036 : List (Nat × Nat × Nat) := [(1712612352,94421282506905,94421659258526),(1712666624,94421697823112,94422074575035)]
theorem point_links_checked13036 : (cuts13036.take 2).map (fun c => (1712586753-1+2*2^9*c.k,94421083965655+c.lower,94421460717130+c.upper)) = pointBounds13036 := by
 decide +kernel
def cuts13037 : List PrefixCut := [⟨3,23336825,23336842⟩,
⟨56,448980295,448980621⟩,
⟨109,876417994,876418629⟩,
⟨128,1024317123,1024317867⟩]
theorem checked13037 : checkPrefixCuts (2^48) 1712717825 9 Manual.Count131072.C013037.packed 128 cuts13037 = true := by
 decide +kernel
def pointBounds13037 : List (Nat × Nat × Nat) := [(1712720896,94422115427027,94422492179252),(1712775168,94422541070497,94422917823031),(1712829440,94422968508196,94423345261039)]
theorem point_links_checked13037 : (cuts13037.take 3).map (fun c => (1712717825-1+2*2^9*c.k,94422092090202+c.lower,94422468842410+c.upper)) = pointBounds13037 := by
 decide +kernel
def cuts13038 : List PrefixCut := [⟨34,279196233,279196433⟩,
⟨87,692146145,692146646⟩,
⟨128,1013886303,1013887036⟩]
theorem checked13038 : checkPrefixCuts (2^48) 1712848897 9 Manual.Count131072.C013038.packed 128 cuts13038 = true := by
 decide +kernel
def pointBounds13038 : List (Nat × Nat × Nat) := [(1712883712,94423395603558,94423772356710),(1712937984,94423808553470,94424185306923)]
theorem point_links_checked13038 : (cuts13038.take 2).map (fun c => (1712848897-1+2*2^9*c.k,94423116407325+c.lower,94423493160277+c.upper)) = pointBounds13038 := by
 decide +kernel
def cuts13039 : List PrefixCut := [⟨12,92839809,92839877⟩,
⟨65,509049878,509050246⟩,
⟨118,932969369,932970044⟩,
⟨128,1010522159,1010522890⟩]
theorem checked13039 : checkPrefixCuts (2^48) 1712979969 9 Manual.Count131072.C013039.packed 128 cuts13039 = true := by
 decide +kernel
def pointBounds13039 : List (Nat × Nat × Nat) := [(1712992256,94424223133437,94424599887190),(1713046528,94424639343506,94425016097559),(1713100800,94425063262997,94425440017357)]
theorem point_links_checked13039 : (cuts13039.take 3).map (fun c => (1712979969-1+2*2^9*c.k,94424130293628+c.lower,94424507047313+c.upper)) = pointBounds13039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000094
