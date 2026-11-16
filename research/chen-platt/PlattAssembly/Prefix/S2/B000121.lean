import PlattAssemblyKernel
import PlattCertificates.Count131072.C013872
import PlattCertificates.Count131072.C013873
import PlattCertificates.Count131072.C013874
import PlattCertificates.Count131072.C013875
import PlattCertificates.Count131072.C013876
import PlattCertificates.Count131072.C013877
import PlattCertificates.Count131072.C013878
import PlattCertificates.Count131072.C013879
import PlattCertificates.Count131072.C013880
import PlattCertificates.Count131072.C013881
import PlattCertificates.Count131072.C013882
import PlattCertificates.Count131072.C013883
import PlattCertificates.Count131072.C013884
import PlattCertificates.Count131072.C013885
import PlattCertificates.Count131072.C013886
import PlattCertificates.Count131072.C013887
import PlattCertificates.Count131072.C013888
import PlattCertificates.Count131072.C013889
import PlattCertificates.Count131072.C013890
import PlattCertificates.Count131072.C013891
import PlattCertificates.Count131072.C013892
import PlattCertificates.Count131072.C013893
import PlattCertificates.Count131072.C013894
import PlattCertificates.Count131072.C013895
import PlattCertificates.Count131072.C013896
import PlattCertificates.Count131072.C013897
import PlattCertificates.Count131072.C013898
import PlattCertificates.Count131072.C013899
import PlattCertificates.Count131072.C013900
import PlattCertificates.Count131072.C013901
import PlattCertificates.Count131072.C013902
import PlattCertificates.Count131072.C013903
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000121
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13872 : List PrefixCut := [⟨11,82024879,82024937⟩,
⟨67,491214753,491215105⟩,
⟨123,905489068,905489711⟩,
⟨128,942559962,942560631⟩]
theorem checked13872 : checkPrefixCuts (2^48) 1822162945 9 Manual.Count131072.C013872.packed 128 cuts13872 = true := by
 decide +kernel
def pointBounds13872 : List (Nat × Nat × Nat) := [(1822174208,95241017892945,95241395226925),(1822231552,95241427082819,95241804417093),(1822288896,95241841357134,95242218691699)]
theorem point_links_checked13872 : (cuts13872.take 3).map (fun c => (1822162945-1+2*2^9*c.k,95240935868066+c.lower,95241313201988+c.upper)) = pointBounds13872 := by
 decide +kernel
def cuts13873 : List PrefixCut := [⟨51,385994651,385994918⟩,
⟨107,800551804,800552365⟩,
⟨128,951296603,951297271⟩]
theorem checked13873 : checkPrefixCuts (2^48) 1822294017 9 Manual.Count131072.C013873.packed 128 cuts13873 = true := by
 decide +kernel
def pointBounds13873 : List (Nat × Nat × Nat) := [(1822346240,95242264422679,95242641757537),(1822403584,95242678979832,95243056314984)]
theorem point_links_checked13873 : (cuts13873.take 2).map (fun c => (1822294017-1+2*2^9*c.k,95241878428028+c.lower,95242255762619+c.upper)) = pointBounds13873 := by
 decide +kernel
def cuts13874 : List PrefixCut := [⟨35,254686747,254686925⟩,
⟨91,670607807,670608271⟩,
⟨128,944277605,944278258⟩]
theorem checked13874 : checkPrefixCuts (2^48) 1822425089 9 Manual.Count131072.C013874.packed 128 cuts13874 = true := by
 decide +kernel
def pointBounds13874 : List (Nat × Nat × Nat) := [(1822460928,95243084411378,95243461746815),(1822518272,95243500332438,95243877668161)]
theorem point_links_checked13874 : (cuts13874.take 2).map (fun c => (1822425089-1+2*2^9*c.k,95242829724631+c.lower,95243207059890+c.upper)) = pointBounds13874 := by
 decide +kernel
def cuts13875 : List PrefixCut := [⟨19,141311503,141311604⟩,
⟨75,546704800,546705187⟩,
⟨128,944209673,944210338⟩]
theorem checked13875 : checkPrefixCuts (2^48) 1822556161 9 Manual.Count131072.C013875.packed 128 cuts13875 = true := by
 decide +kernel
def pointBounds13875 : List (Nat × Nat × Nat) := [(1822575616,95243915313739,95244292649752),(1822632960,95244320707036,95244698043335)]
theorem point_links_checked13875 : (cuts13875.take 2).map (fun c => (1822556161-1+2*2^9*c.k,95243774002236+c.lower,95244151338148+c.upper)) = pointBounds13875 := by
 decide +kernel
def cuts13876 : List PrefixCut := [⟨3,21465545,21465559⟩,
⟨59,435789996,435790298⟩,
⟨115,853344274,853344866⟩,
⟨128,947539234,947539893⟩]
theorem checked13876 : checkPrefixCuts (2^48) 1822687233 9 Manual.Count131072.C013876.packed 128 cuts13876 = true := by
 decide +kernel
def pointBounds13876 : List (Nat × Nat × Nat) := [(1822690304,95244739677454,95245117014045),(1822747648,95245154001905,95245531338784),(1822804992,95245571556183,95245948893352)]
theorem point_links_checked13876 : (cuts13876.take 3).map (fun c => (1822687233-1+2*2^9*c.k,95244718211909+c.lower,95245095548486+c.upper)) = pointBounds13876 := by
 decide +kernel
def cuts13877 : List PrefixCut := [⟨43,323191754,323191980⟩,
⟨99,740102141,740102656⟩,
⟨128,949324372,949325034⟩]
theorem checked13877 : checkPrefixCuts (2^48) 1822818305 9 Manual.Count131072.C013877.packed 128 cuts13877 = true := by
 decide +kernel
def pointBounds13877 : List (Nat × Nat × Nat) := [(1822862336,95245988942897,95246366280359),(1822919680,95246405853284,95246783191035)]
theorem point_links_checked13877 : (cuts13877.take 2).map (fun c => (1822818305-1+2*2^9*c.k,95245665751143+c.lower,95246043088379+c.upper)) = pointBounds13877 := by
 decide +kernel
def cuts13878 : List PrefixCut := [⟨27,193624025,193624160⟩,
⟨83,606493723,606494144⟩,
⟨128,931499730,931500377⟩]
theorem checked13878 : checkPrefixCuts (2^48) 1822949377 9 Manual.Count131072.C013878.packed 128 cuts13878 = true := by
 decide +kernel
def pointBounds13878 : List (Nat × Nat × Nat) := [(1822977024,95246808699540,95247186037573),(1823034368,95247221569238,95247598907557)]
theorem point_links_checked13878 : (cuts13878.take 2).map (fun c => (1822949377-1+2*2^9*c.k,95246615075515+c.lower,95246992413413+c.upper)) = pointBounds13878 := by
 decide +kernel
def cuts13879 : List PrefixCut := [⟨11,83218767,83218825⟩,
⟨67,500385478,500385832⟩,
⟨123,914605773,914606415⟩,
⟨128,952893086,952893753⟩]
theorem checked13879 : checkPrefixCuts (2^48) 1823080449 9 Manual.Count131072.C013879.packed 128 cuts13879 = true := by
 decide +kernel
def pointBounds13879 : List (Nat × Nat × Nat) := [(1823091712,95247629794012,95248007132615),(1823149056,95248046960723,95248424299622),(1823206400,95248461181018,95248838520205)]
theorem point_links_checked13879 : (cuts13879.take 3).map (fun c => (1823080449-1+2*2^9*c.k,95247546575245+c.lower,95247923913790+c.upper)) = pointBounds13879 := by
 decide +kernel
def cuts13880 : List PrefixCut := [⟨51,382249520,382249790⟩,
⟨107,792429889,792430449⟩,
⟨128,948810674,948811341⟩]
theorem checked13880 : checkPrefixCuts (2^48) 1823211521 9 Manual.Count131072.C013880.packed 128 cuts13880 = true := by
 decide +kernel
def pointBounds13880 : List (Nat × Nat × Nat) := [(1823263744,95248881717851,95249259057333),(1823321088,95249291898220,95249669237992)]
theorem point_links_checked13880 : (cuts13880.take 2).map (fun c => (1823211521-1+2*2^9*c.k,95248499468331+c.lower,95248876807543+c.upper)) = pointBounds13880 := by
 decide +kernel
def cuts13881 : List PrefixCut := [⟨35,257182909,257183090⟩,
⟨91,671968569,671969034⟩,
⟨128,945192009,945192666⟩]
theorem checked13881 : checkPrefixCuts (2^48) 1823342593 9 Manual.Count131072.C013881.packed 128 cuts13881 = true := by
 decide +kernel
def pointBounds13881 : List (Nat × Nat × Nat) := [(1823378432,95249705461914,95250082801974),(1823435776,95250120247574,95250497587918)]
theorem point_links_checked13881 : (cuts13881.take 2).map (fun c => (1823342593-1+2*2^9*c.k,95249448279005+c.lower,95249825618884+c.upper)) = pointBounds13881 := by
 decide +kernel
def cuts13882 : List PrefixCut := [⟨19,138924981,138925075⟩,
⟨75,561248027,561248413⟩,
⟨128,957163941,957164600⟩]
theorem checked13882 : checkPrefixCuts (2^48) 1823473665 9 Manual.Count131072.C013882.packed 128 cuts13882 = true := by
 decide +kernel
def pointBounds13882 : List (Nat × Nat × Nat) := [(1823493120,95250532395995,95250909736625),(1823550464,95250954719041,95251332059963)]
theorem point_links_checked13882 : (cuts13882.take 2).map (fun c => (1823473665-1+2*2^9*c.k,95250393471014+c.lower,95250770811550+c.upper)) = pointBounds13882 := by
 decide +kernel
def cuts13883 : List PrefixCut := [⟨3,22843900,22843916⟩,
⟨59,436959897,436960201⟩,
⟨115,858471474,858472076⟩,
⟨128,954162459,954163128⟩]
theorem checked13883 : checkPrefixCuts (2^48) 1823604737 9 Manual.Count131072.C013883.packed 128 cuts13883 = true := by
 decide +kernel
def pointBounds13883 : List (Nat × Nat × Nat) := [(1823607808,95251373478855,95251750820066),(1823665152,95251787594852,95252164936351),(1823722496,95252209106429,95252586448226)]
theorem point_links_checked13883 : (cuts13883.take 3).map (fun c => (1823604737-1+2*2^9*c.k,95251350634955+c.lower,95251727976150+c.upper)) = pointBounds13883 := by
 decide +kernel
def cuts13884 : List PrefixCut := [⟨43,316855619,316855835⟩,
⟨99,735408206,735408715⟩,
⟨128,951007017,951007677⟩]
theorem checked13884 : checkPrefixCuts (2^48) 1823735809 9 Manual.Count131072.C013884.packed 128 cuts13884 = true := by
 decide +kernel
def pointBounds13884 : List (Nat × Nat × Nat) := [(1823779840,95252621653033,95252998995113),(1823837184,95253040205620,95253417547993)]
theorem point_links_checked13884 : (cuts13884.take 2).map (fun c => (1823735809-1+2*2^9*c.k,95252304797414+c.lower,95252682139278+c.upper)) = pointBounds13884 := by
 decide +kernel
def cuts13885 : List PrefixCut := [⟨27,200934344,200934487⟩,
⟨83,631806510,631806946⟩,
⟨128,961895890,961896561⟩]
theorem checked13885 : checkPrefixCuts (2^48) 1823866881 9 Manual.Count131072.C013885.packed 128 cuts13885 = true := by
 decide +kernel
def pointBounds13885 : List (Nat × Nat × Nat) := [(1823894528,95253456738775,95253834081442),(1823951872,95253887610941,95254264953901)]
theorem point_links_checked13885 : (cuts13885.take 2).map (fun c => (1823866881-1+2*2^9*c.k,95253255804431+c.lower,95253633146955+c.upper)) = pointBounds13885 := by
 decide +kernel
def cuts13886 : List PrefixCut := [⟨11,78701708,78701761⟩,
⟨67,487479895,487480238⟩,
⟨123,902726241,902726871⟩,
⟨128,938525388,938526043⟩]
theorem checked13886 : checkPrefixCuts (2^48) 1823997953 9 Manual.Count131072.C013886.packed 128 cuts13886 = true := by
 decide +kernel
def pointBounds13886 : List (Nat × Nat × Nat) := [(1824009216,95254296402029,95254673745277),(1824066560,95254705180216,95255082523754),(1824123904,95255120426562,95255497770387)]
theorem point_links_checked13886 : (cuts13886.take 3).map (fun c => (1823997953-1+2*2^9*c.k,95254217700321+c.lower,95254595043516+c.upper)) = pointBounds13886 := by
 decide +kernel
def cuts13887 : List PrefixCut := [⟨51,383291742,383292008⟩,
⟨107,801752272,801752834⟩,
⟨128,960831712,960832382⟩]
theorem checked13887 : checkPrefixCuts (2^48) 1824129025 9 Manual.Count131072.C013887.packed 128 cuts13887 = true := by
 decide +kernel
def pointBounds13887 : List (Nat × Nat × Nat) := [(1824181248,95255539517451,95255916861567),(1824238592,95255957977981,95256335322393)]
theorem point_links_checked13887 : (cuts13887.take 2).map (fun c => (1824129025-1+2*2^9*c.k,95255156225709+c.lower,95255533569559+c.upper)) = pointBounds13887 := by
 decide +kernel
def cuts13888 : List PrefixCut := [⟨35,261836625,261836810⟩,
⟨91,676413601,676414074⟩,
⟨128,950733883,950734551⟩]
theorem checked13888 : checkPrefixCuts (2^48) 1824260097 9 Manual.Count131072.C013888.packed 128 cuts13888 = true := by
 decide +kernel
def pointBounds13888 : List (Nat × Nat × Nat) := [(1824295936,95256378894046,95256756238751),(1824353280,95256793471022,95257170816015)]
theorem point_links_checked13888 : (cuts13888.take 2).map (fun c => (1824260097-1+2*2^9*c.k,95256117057421+c.lower,95256494401941+c.upper)) = pointBounds13888 := by
 decide +kernel
def cuts13889 : List PrefixCut := [⟨19,142557920,142558019⟩,
⟨75,555565984,555566373⟩,
⟨128,951128368,951129035⟩]
theorem checked13889 : checkPrefixCuts (2^48) 1824391169 9 Manual.Count131072.C013889.packed 128 cuts13889 = true := by
 decide +kernel
def pointBounds13889 : List (Nat × Nat × Nat) := [(1824410624,95257210349224,95257587694511),(1824467968,95257623357288,95258000702865)]
theorem point_links_checked13889 : (cuts13889.take 2).map (fun c => (1824391169-1+2*2^9*c.k,95257067791304+c.lower,95257445136492+c.upper)) = pointBounds13889 := by
 decide +kernel
def cuts13890 : List PrefixCut := [⟨3,22369595,22369611⟩,
⟨59,439362807,439363108⟩,
⟨115,855108788,855109383⟩,
⟨128,953682648,953683311⟩]
theorem checked13890 : checkPrefixCuts (2^48) 1824522241 9 Manual.Count131072.C013890.packed 128 cuts13890 = true := by
 decide +kernel
def pointBounds13890 : List (Nat × Nat × Nat) := [(1824525312,95258041289267,95258418635138),(1824582656,95258458282479,95258835628635),(1824640000,95258874028460,95259251374910)]
theorem point_links_checked13890 : (cuts13890.take 3).map (fun c => (1824522241-1+2*2^9*c.k,95258018919672+c.lower,95258396265527+c.upper)) = pointBounds13890 := by
 decide +kernel
def cuts13891 : List PrefixCut := [⟨43,305898119,305898335⟩,
⟨99,728250895,728251399⟩,
⟨128,936491481,936492128⟩]
theorem checked13891 : checkPrefixCuts (2^48) 1824653313 9 Manual.Count131072.C013891.packed 128 cuts13891 = true := by
 decide +kernel
def pointBounds13891 : List (Nat × Nat × Nat) := [(1824697344,95259278500439,95259655847173),(1824754688,95259700853215,95260078200237)]
theorem point_links_checked13891 : (cuts13891.take 2).map (fun c => (1824653313-1+2*2^9*c.k,95258972602320+c.lower,95259349948838+c.upper)) = pointBounds13891 := by
 decide +kernel
def cuts13892 : List PrefixCut := [⟨27,200524847,200524985⟩,
⟨83,618378034,618378459⟩,
⟨128,950152363,950153019⟩]
theorem checked13892 : checkPrefixCuts (2^48) 1824784385 9 Manual.Count131072.C013892.packed 128 cuts13892 = true := by
 decide +kernel
def pointBounds13892 : List (Nat × Nat × Nat) := [(1824812032,95260109618648,95260486965951),(1824869376,95260527471835,95260904819425)]
theorem point_links_checked13892 : (cuts13892.take 2).map (fun c => (1824784385-1+2*2^9*c.k,95259909093801+c.lower,95260286440966+c.upper)) = pointBounds13892 := by
 decide +kernel
def cuts13893 : List PrefixCut := [⟨11,80667242,80667300⟩,
⟨67,500653428,500653781⟩,
⟨123,914148709,914149349⟩,
⟨128,951626379,951627045⟩]
theorem checked13893 : checkPrefixCuts (2^48) 1824915457 9 Manual.Count131072.C013893.packed 128 cuts13893 = true := by
 decide +kernel
def pointBounds13893 : List (Nat × Nat × Nat) := [(1824926720,95260939913406,95261317261285),(1824984064,95261359899592,95261737247766),(1825041408,95261773394873,95262150743334)]
theorem point_links_checked13893 : (cuts13893.take 3).map (fun c => (1824915457-1+2*2^9*c.k,95260859246164+c.lower,95261236593985+c.upper)) = pointBounds13893 := by
 decide +kernel
def cuts13894 : List PrefixCut := [⟨51,373537015,373537278⟩,
⟨107,787160531,787161084⟩,
⟨128,941225047,941225709⟩]
theorem checked13894 : checkPrefixCuts (2^48) 1825046529 9 Manual.Count131072.C013894.packed 128 cuts13894 = true := by
 decide +kernel
def pointBounds13894 : List (Nat × Nat × Nat) := [(1825098752,95262184409558,95262561758308),(1825156096,95262598033074,95262975382114)]
theorem point_links_checked13894 : (cuts13894.take 2).map (fun c => (1825046529-1+2*2^9*c.k,95261810872543+c.lower,95262188221030+c.upper)) = pointBounds13894 := by
 decide +kernel
def cuts13895 : List PrefixCut := [⟨35,260779704,260779881⟩,
⟨91,677615722,677616189⟩,
⟨128,954419662,954420320⟩]
theorem checked13895 : checkPrefixCuts (2^48) 1825177601 9 Manual.Count131072.C013895.packed 128 cuts13895 = true := by
 decide +kernel
def pointBounds13895 : List (Nat × Nat × Nat) := [(1825213440,95263012877294,95263390226620),(1825270784,95263429713312,95263807062928)]
theorem point_links_checked13895 : (cuts13895.take 2).map (fun c => (1825177601-1+2*2^9*c.k,95262752097590+c.lower,95263129446739+c.upper)) = pointBounds13895 := by
 decide +kernel
def cuts13896 : List PrefixCut := [⟨19,143719917,143720019⟩,
⟨75,553744866,553745258⟩,
⟨128,952500794,952501464⟩]
theorem checked13896 : checkPrefixCuts (2^48) 1825308673 9 Manual.Count131072.C013896.packed 128 cuts13896 = true := by
 decide +kernel
def pointBounds13896 : List (Nat × Nat × Nat) := [(1825328128,95263850237169,95264227587078),(1825385472,95264260262118,95264637612317)]
theorem point_links_checked13896 : (cuts13896.take 2).map (fun c => (1825308673-1+2*2^9*c.k,95263706517252+c.lower,95264083867059+c.upper)) = pointBounds13896 := by
 decide +kernel
def cuts13897 : List PrefixCut := [⟨3,19120245,19120259⟩,
⟨59,427885814,427886114⟩,
⟨115,848510998,848511586⟩,
⟨128,944722534,944723191⟩]
theorem checked13897 : checkPrefixCuts (2^48) 1825439745 9 Manual.Count131072.C013897.packed 128 cuts13897 = true := by
 decide +kernel
def pointBounds13897 : List (Nat × Nat × Nat) := [(1825442816,95264678138291,95265055488782),(1825500160,95265086903860,95265464254637),(1825557504,95265507529044,95265884880109)]
theorem point_links_checked13897 : (cuts13897.take 3).map (fun c => (1825439745-1+2*2^9*c.k,95264659018046+c.lower,95265036368523+c.upper)) = pointBounds13897 := by
 decide +kernel
def cuts13898 : List PrefixCut := [⟨43,318695716,318695941⟩,
⟨99,736827659,736828172⟩,
⟨128,951438949,951439609⟩]
theorem checked13898 : checkPrefixCuts (2^48) 1825570817 9 Manual.Count131072.C013898.packed 128 cuts13898 = true := by
 decide +kernel
def pointBounds13898 : List (Nat × Nat × Nat) := [(1825614848,95265922436296,95266299787655),(1825672192,95266340568239,95266717919886)]
theorem point_links_checked13898 : (cuts13898.take 2).map (fun c => (1825570817-1+2*2^9*c.k,95265603740580+c.lower,95265981091714+c.upper)) = pointBounds13898 := by
 decide +kernel
def cuts13899 : List PrefixCut := [⟨27,195644721,195644855⟩,
⟨83,602650322,602650741⟩,
⟨128,935028760,935029407⟩]
theorem checked13899 : checkPrefixCuts (2^48) 1825701889 9 Manual.Count131072.C013899.packed 128 cuts13899 = true := by
 decide +kernel
def pointBounds13899 : List (Nat × Nat × Nat) := [(1825729536,95266750824250,95267128176178),(1825786880,95267157829851,95267535182064)]
theorem point_links_checked13899 : (cuts13899.take 2).map (fun c => (1825701889-1+2*2^9*c.k,95266555179529+c.lower,95266932531323+c.upper)) = pointBounds13899 := by
 decide +kernel
def cuts13900 : List PrefixCut := [⟨11,77389306,77389360⟩,
⟨67,487914950,487915291⟩,
⟨123,901819105,901819732⟩,
⟨128,937273975,937274626⟩]
theorem checked13900 : checkPrefixCuts (2^48) 1825832961 9 Manual.Count131072.C013900.packed 128 cuts13900 = true := by
 decide +kernel
def pointBounds13900 : List (Nat × Nat × Nat) := [(1825844224,95267567597595,95267944950090),(1825901568,95267978123239,95268355476021),(1825958912,95268392027394,95268769380462)]
theorem point_links_checked13900 : (cuts13900.take 3).map (fun c => (1825832961-1+2*2^9*c.k,95267490208289+c.lower,95267867560730+c.upper)) = pointBounds13900 := by
 decide +kernel
def cuts13901 : List PrefixCut := [⟨51,385218876,385219136⟩,
⟨107,796476547,796477096⟩,
⟨128,950463649,950464305⟩]
theorem checked13901 : checkPrefixCuts (2^48) 1825964033 9 Manual.Count131072.C013901.packed 128 cuts13901 = true := by
 decide +kernel
def pointBounds13901 : List (Nat × Nat × Nat) := [(1826016256,95268812701140,95269190054492),(1826073600,95269223958811,95269601312452)]
theorem point_links_checked13901 : (cuts13901.take 2).map (fun c => (1825964033-1+2*2^9*c.k,95268427482264+c.lower,95268804835356+c.upper)) = pointBounds13901 := by
 decide +kernel
def cuts13902 : List PrefixCut := [⟨35,256024559,256024741⟩,
⟨91,661399317,661399784⟩,
⟨128,937601815,937602476⟩]
theorem checked13902 : checkPrefixCuts (2^48) 1826095105 9 Manual.Count131072.C013902.packed 128 cuts13902 = true := by
 decide +kernel
def pointBounds13902 : List (Nat × Nat × Nat) := [(1826130944,95269633970472,95270011324402),(1826188288,95270039345230,95270416699445)]
theorem point_links_checked13902 : (cuts13902.take 2).map (fun c => (1826095105-1+2*2^9*c.k,95269377945913+c.lower,95269755299661+c.upper)) = pointBounds13902 := by
 decide +kernel
def cuts13903 : List PrefixCut := [⟨19,143801832,143801930⟩,
⟨75,554237242,554237627⟩,
⟨128,947244525,947245181⟩]
theorem checked13903 : checkPrefixCuts (2^48) 1826226177 9 Manual.Count131072.C013903.packed 128 cuts13903 = true := by
 decide +kernel
def pointBounds13903 : List (Nat × Nat × Nat) := [(1826245632,95270459349560,95270836704067),(1826302976,95270869784970,95271247139764)]
theorem point_links_checked13903 : (cuts13903.take 2).map (fun c => (1826226177-1+2*2^9*c.k,95270315547728+c.lower,95270692902137+c.upper)) = pointBounds13903 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000121
