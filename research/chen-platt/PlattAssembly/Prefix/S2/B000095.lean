import PlattAssemblyKernel
import PlattCertificates.Count131072.C013040
import PlattCertificates.Count131072.C013041
import PlattCertificates.Count131072.C013042
import PlattCertificates.Count131072.C013043
import PlattCertificates.Count131072.C013044
import PlattCertificates.Count131072.C013045
import PlattCertificates.Count131072.C013046
import PlattCertificates.Count131072.C013047
import PlattCertificates.Count131072.C013048
import PlattCertificates.Count131072.C013049
import PlattCertificates.Count131072.C013050
import PlattCertificates.Count131072.C013051
import PlattCertificates.Count131072.C013052
import PlattCertificates.Count131072.C013053
import PlattCertificates.Count131072.C013054
import PlattCertificates.Count131072.C013055
import PlattCertificates.Count131072.C013056
import PlattCertificates.Count131072.C013057
import PlattCertificates.Count131072.C013058
import PlattCertificates.Count131072.C013059
import PlattCertificates.Count131072.C013060
import PlattCertificates.Count131072.C013061
import PlattCertificates.Count131072.C013062
import PlattCertificates.Count131072.C013063
import PlattCertificates.Count131072.C013064
import PlattCertificates.Count131072.C013065
import PlattCertificates.Count131072.C013066
import PlattCertificates.Count131072.C013067
import PlattCertificates.Count131072.C013068
import PlattCertificates.Count131072.C013069
import PlattCertificates.Count131072.C013070
import PlattCertificates.Count131072.C013071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13040 : List PrefixCut := [⟨43,336330640,336330887⟩,
⟨96,761373205,761373759⟩,
⟨128,1015702270,1015703010⟩]
theorem checked13040 : checkPrefixCuts (2^48) 1713111041 9 Manual.Count131072.C013040.packed 128 cuts13040 = true := by
 decide +kernel
def pointBounds13040 : List (Nat × Nat × Nat) := [(1713155072,94425477146427,94425853901090),(1713209344,94425902188992,94426278943962)]
theorem point_links_checked13040 : (cuts13040.take 2).map (fun c => (1713111041-1+2*2^9*c.k,94425140815787+c.lower,94425517570203+c.upper)) = pointBounds13040 := by
 decide +kernel
def cuts13041 : List PrefixCut := [⟨21,171685830,171685957⟩,
⟨74,591608625,591609054⟩,
⟨127,1010203835,1010204568⟩,
⟨128,1018582175,1018582914⟩]
theorem checked13041 : checkPrefixCuts (2^48) 1713242113 9 Manual.Count131072.C013041.packed 128 cuts13041 = true := by
 decide +kernel
def pointBounds13041 : List (Nat × Nat × Nat) := [(1713263616,94426328203887,94426704959170),(1713317888,94426748126682,94427124882267),(1713372160,94427166721892,94427543477781)]
theorem point_links_checked13041 : (cuts13041.take 3).map (fun c => (1713242113-1+2*2^9*c.k,94426156518057+c.lower,94426533273213+c.upper)) = pointBounds13041 := by
 decide +kernel
def cuts13042 : List PrefixCut := [⟨52,408396521,408396814⟩,
⟨105,821872701,821873289⟩,
⟨128,1003719252,1003719973⟩]
theorem checked13042 : checkPrefixCuts (2^48) 1713373185 9 Manual.Count131072.C013042.packed 128 cuts13042 = true := by
 decide +kernel
def pointBounds13042 : List (Nat × Nat × Nat) := [(1713426432,94427583496753,94427960252941),(1713480704,94427996972933,94428373729416)]
theorem point_links_checked13042 : (cuts13042.take 2).map (fun c => (1713373185-1+2*2^9*c.k,94427175100232+c.lower,94427551856127+c.upper)) = pointBounds13042 := by
 decide +kernel
def cuts13043 : List PrefixCut := [⟨30,240322773,240322946⟩,
⟨83,648352029,648352498⟩,
⟨128,1001671383,1001672106⟩]
theorem checked13043 : checkPrefixCuts (2^48) 1713504257 9 Manual.Count131072.C013043.packed 128 cuts13043 = true := by
 decide +kernel
def pointBounds13043 : List (Nat × Nat × Nat) := [(1713534976,94428419142257,94428795899046),(1713589248,94428827171513,94429203928598)]
theorem point_links_checked13043 : (cuts13043.take 2).map (fun c => (1713504257-1+2*2^9*c.k,94428178819484+c.lower,94428555576100+c.upper)) = pointBounds13043 := by
 decide +kernel
def cuts13044 : List PrefixCut := [⟨8,63566921,63566967⟩,
⟨61,474526912,474527263⟩,
⟨114,893357772,893358429⟩,
⟨128,1004058317,1004059055⟩]
theorem checked13044 : checkPrefixCuts (2^48) 1713635329 9 Manual.Count131072.C013044.packed 128 cuts13044 = true := by
 decide +kernel
def pointBounds13044 : List (Nat × Nat × Nat) := [(1713643520,94429244057788,94429620815173),(1713697792,94429655017779,94430031775469),(1713752064,94430073848639,94430450606635)]
theorem point_links_checked13044 : (cuts13044.take 3).map (fun c => (1713635329-1+2*2^9*c.k,94429180490867+c.lower,94429557248206+c.upper)) = pointBounds13044 := by
 decide +kernel
def cuts13045 : List PrefixCut := [⟨39,309759538,309759762⟩,
⟨92,725114894,725115423⟩,
⟨128,1009237358,1009238094⟩]
theorem checked13045 : checkPrefixCuts (2^48) 1713766401 9 Manual.Count131072.C013045.packed 128 cuts13045 = true := by
 decide +kernel
def pointBounds13045 : List (Nat × Nat × Nat) := [(1713806336,94430494308722,94430871067023),(1713860608,94430909664078,94431286422684)]
theorem point_links_checked13045 : (cuts13045.take 2).map (fun c => (1713766401-1+2*2^9*c.k,94430184549184+c.lower,94430561307261+c.upper)) = pointBounds13045 := by
 decide +kernel
def cuts13046 : List PrefixCut := [⟨17,131876722,131876815⟩,
⟨70,541622046,541622438⟩,
⟨123,971882111,971882812⟩,
⟨128,1012115658,1012116388⟩]
theorem checked13046 : checkPrefixCuts (2^48) 1713897473 9 Manual.Count131072.C013046.packed 128 cuts13046 = true := by
 decide +kernel
def pointBounds13046 : List (Nat × Nat × Nat) := [(1713914880,94431325663264,94431702422170),(1713969152,94431735408588,94432112167793),(1714023424,94432165668653,94432542428167)]
theorem point_links_checked13046 : (cuts13046.take 3).map (fun c => (1713897473-1+2*2^9*c.k,94431193786542+c.lower,94431570545355+c.upper)) = pointBounds13046 := by
 decide +kernel
def cuts13047 : List PrefixCut := [⟨48,381145167,381145446⟩,
⟨101,803824277,803824865⟩,
⟨128,1011217825,1011218565⟩]
theorem checked13047 : checkPrefixCuts (2^48) 1714028545 9 Manual.Count131072.C013047.packed 128 cuts13047 = true := by
 decide +kernel
def pointBounds13047 : List (Nat × Nat × Nat) := [(1714077696,94432587047367,94432963807189),(1714131968,94433009726477,94433386486608)]
theorem point_links_checked13047 : (cuts13047.take 2).map (fun c => (1714028545-1+2*2^9*c.k,94432205902200+c.lower,94432582661743+c.upper)) = pointBounds13047 := by
 decide +kernel
def cuts13048 : List PrefixCut := [⟨26,202464126,202464274⟩,
⟨79,619369486,619369933⟩,
⟨128,1010319292,1010320022⟩]
theorem checked13048 : checkPrefixCuts (2^48) 1714159617 9 Manual.Count131072.C013048.packed 128 cuts13048 = true := by
 decide +kernel
def pointBounds13048 : List (Nat × Nat × Nat) := [(1714186240,94433419584151,94433796344582),(1714240512,94433836489511,94434213250241)]
theorem point_links_checked13048 : (cuts13048.take 2).map (fun c => (1714159617-1+2*2^9*c.k,94433217120025+c.lower,94433593880308+c.upper)) = pointBounds13048 := by
 decide +kernel
def cuts13049 : List PrefixCut := [⟨4,33495373,33495397⟩,
⟨57,453329608,453329936⟩,
⟨110,873643257,873643890⟩,
⟨128,1010242302,1010243034⟩]
theorem checked13049 : checkPrefixCuts (2^48) 1714290689 9 Manual.Count131072.C013049.packed 128 cuts13049 = true := by
 decide +kernel
def pointBounds13049 : List (Nat × Nat × Nat) := [(1714294784,94434260934690,94434637695727),(1714349056,94434680768925,94435057530266),(1714403328,94435101082574,94435477844220)]
theorem point_links_checked13049 : (cuts13049.take 3).map (fun c => (1714290689-1+2*2^9*c.k,94434227439317+c.lower,94434604200330+c.upper)) = pointBounds13049 := by
 decide +kernel
def cuts13050 : List PrefixCut := [⟨35,271551993,271552193⟩,
⟨88,690033122,690033624⟩,
⟨128,1013448149,1013448883⟩]
theorem checked13050 : checkPrefixCuts (2^48) 1714421761 9 Manual.Count131072.C013050.packed 128 cuts13050 = true := by
 decide +kernel
def pointBounds13050 : List (Nat × Nat × Nat) := [(1714457600,94435509233612,94435885995557),(1714511872,94435927714741,94436304476988)]
theorem point_links_checked13050 : (cuts13050.take 2).map (fun c => (1714421761-1+2*2^9*c.k,94435237681619+c.lower,94435614443364+c.upper)) = pointBounds13050 := by
 decide +kernel
def cuts13051 : List PrefixCut := [⟨13,97843803,97843873⟩,
⟨66,516298458,516298830⟩,
⟨119,932769880,932770553⟩,
⟨128,1001879549,1001880272⟩]
theorem checked13051 : checkPrefixCuts (2^48) 1714552833 9 Manual.Count131072.C013051.packed 128 cuts13051 = true := by
 decide +kernel
def pointBounds13051 : List (Nat × Nat × Nat) := [(1714566144,94436348973571,94436725736120),(1714620416,94436767428226,94437144191077),(1714674688,94437183899648,94437560662800)]
theorem point_links_checked13051 : (cuts13051.take 3).map (fun c => (1714552833-1+2*2^9*c.k,94436251129768+c.lower,94436627892247+c.upper)) = pointBounds13051 := by
 decide +kernel
def cuts13052 : List PrefixCut := [⟨44,348825961,348826212⟩,
⟨97,772165211,772165775⟩,
⟨128,1019859279,1019860023⟩]
theorem checked13052 : checkPrefixCuts (2^48) 1714683905 9 Manual.Count131072.C013052.packed 128 cuts13052 = true := by
 decide +kernel
def pointBounds13052 : List (Nat × Nat × Nat) := [(1714728960,94437601835278,94437978598731),(1714783232,94438025174528,94438401938294)]
theorem point_links_checked13052 : (cuts13052.take 2).map (fun c => (1714683905-1+2*2^9*c.k,94437253009317+c.lower,94437629772519+c.upper)) = pointBounds13052 := by
 decide +kernel
def cuts13053 : List PrefixCut := [⟨22,171364171,171364296⟩,
⟨75,596810409,596810842⟩,
⟨128,1019945395,1019946132⟩]
theorem checked13053 : checkPrefixCuts (2^48) 1714814977 9 Manual.Count131072.C013053.packed 128 cuts13053 = true := by
 decide +kernel
def pointBounds13053 : List (Nat × Nat × Nat) := [(1714837504,94438444232767,94438820996838),(1714891776,94438869679005,94439246443384),(1714946048,94439292813991,94439669578674)]
theorem point_links_checked13053 : (cuts13053.take 3).map (fun c => (1714814977-1+2*2^9*c.k,94438272868596+c.lower,94438649632542+c.upper)) = pointBounds13053 := by
 decide +kernel
def cuts13054 : List PrefixCut := [⟨53,414094630,414094933⟩,
⟨106,832607358,832607964⟩,
⟨128,1009855853,1009856591⟩]
theorem checked13054 : checkPrefixCuts (2^48) 1714946049 9 Manual.Count131072.C013054.packed 128 cuts13054 = true := by
 decide +kernel
def pointBounds13054 : List (Nat × Nat × Nat) := [(1715000320,94439706908621,94440083673607),(1715054592,94440125421349,94440502186638)]
theorem point_links_checked13054 : (cuts13054.take 2).map (fun c => (1714946049-1+2*2^9*c.k,94439292813991+c.lower,94439669578674+c.upper)) = pointBounds13054 := by
 decide +kernel
def cuts13055 : List PrefixCut := [⟨31,248144017,248144197⟩,
⟨84,665481471,665481952⟩,
⟨128,1011256063,1011256800⟩]
theorem checked13055 : checkPrefixCuts (2^48) 1715077121 9 Manual.Count131072.C013055.packed 128 cuts13055 = true := by
 decide +kernel
def pointBounds13055 : List (Nat × Nat × Nat) := [(1715108864,94440550813861,94440927579462),(1715163136,94440968151315,94441344917217)]
theorem point_links_checked13055 : (cuts13055.take 2).map (fun c => (1715077121-1+2*2^9*c.k,94440302669844+c.lower,94440679435265+c.upper)) = pointBounds13055 := by
 decide +kernel
def cuts13056 : List PrefixCut := [⟨9,72042064,72042114⟩,
⟨62,484594256,484594607⟩,
⟨115,908948396,908949053⟩,
⟨128,1016265527,1016266260⟩]
theorem checked13056 : checkPrefixCuts (2^48) 1715208193 9 Manual.Count131072.C013056.packed 128 cuts13056 = true := by
 decide +kernel
def pointBounds13056 : List (Nat × Nat × Nat) := [(1715217408,94441385967971,94441762734179),(1715271680,94441798520163,94442175286672),(1715325952,94442222874303,94442599641118)]
theorem point_links_checked13056 : (cuts13056.take 3).map (fun c => (1715208193-1+2*2^9*c.k,94441313925907+c.lower,94441690692065+c.upper)) = pointBounds13056 := by
 decide +kernel
def cuts13057 : List PrefixCut := [⟨40,311772631,311772855⟩,
⟨93,731833621,731834144⟩,
⟨128,1007655516,1007656240⟩]
theorem checked13057 : checkPrefixCuts (2^48) 1715339265 9 Manual.Count131072.C013057.packed 128 cuts13057 = true := by
 decide +kernel
def pointBounds13057 : List (Nat × Nat × Nat) := [(1715380224,94442641964065,94443018731180),(1715434496,94443062025055,94443438792469)]
theorem point_links_checked13057 : (cuts13057.take 2).map (fun c => (1715339265-1+2*2^9*c.k,94442330191434+c.lower,94442706958325+c.upper)) = pointBounds13057 := by
 decide +kernel
def cuts13058 : List PrefixCut := [⟨18,142256872,142256972⟩,
⟨71,556056394,556056794⟩,
⟨124,978702692,978703398⟩,
⟨128,1011352214,1011352944⟩]
theorem checked13058 : checkPrefixCuts (2^48) 1715470337 9 Manual.Count131072.C013058.packed 128 cuts13058 = true := by
 decide +kernel
def pointBounds13058 : List (Nat × Nat × Nat) := [(1715488768,94443480103822,94443856871537),(1715543040,94443893903344,94444270671359),(1715597312,94444316549642,94444693317963)]
theorem point_links_checked13058 : (cuts13058.take 3).map (fun c => (1715470337-1+2*2^9*c.k,94443337846950+c.lower,94443714614565+c.upper)) = pointBounds13058 := by
 decide +kernel
def cuts13059 : List PrefixCut := [⟨49,387850558,387850839⟩,
⟨102,801446717,801447294⟩,
⟨128,1011767123,1011767852⟩]
theorem checked13059 : checkPrefixCuts (2^48) 1715601409 9 Manual.Count131072.C013059.packed 128 cuts13059 = true := by
 decide +kernel
def pointBounds13059 : List (Nat × Nat × Nat) := [(1715651584,94444737049722,94445113818348),(1715705856,94445150645881,94445527414803)]
theorem point_links_checked13059 : (cuts13059.take 2).map (fun c => (1715601409-1+2*2^9*c.k,94444349199164+c.lower,94444725967509+c.upper)) = pointBounds13059 := by
 decide +kernel
def cuts13060 : List PrefixCut := [⟨27,213434109,213434264⟩,
⟨80,629464896,629465352⟩,
⟨128,1016119064,1016119800⟩]
theorem checked13060 : checkPrefixCuts (2^48) 1715732481 9 Manual.Count131072.C013060.packed 128 cuts13060 = true := by
 decide +kernel
def pointBounds13060 : List (Nat × Nat × Nat) := [(1715760128,94445574400396,94445951169625),(1715814400,94445990431183,94446367200713)]
theorem point_links_checked13060 : (cuts13060.take 2).map (fun c => (1715732481-1+2*2^9*c.k,94445360966287+c.lower,94445737735361+c.upper)) = pointBounds13060 := by
 decide +kernel
def cuts13061 : List PrefixCut := [⟨5,39534230,39534259⟩,
⟨58,462920429,462920765⟩,
⟨111,878255498,878256136⟩,
⟨128,1006691757,1006692489⟩]
theorem checked13061 : checkPrefixCuts (2^48) 1715863553 9 Manual.Count131072.C013061.packed 128 cuts13061 = true := by
 decide +kernel
def pointBounds13061 : List (Nat × Nat × Nat) := [(1715868672,94446416619581,94446793389420),(1715922944,94446840005780,94447216775926),(1715977216,94447255340849,94447632111297)]
theorem point_links_checked13061 : (cuts13061.take 3).map (fun c => (1715863553-1+2*2^9*c.k,94446377085351+c.lower,94446753855161+c.upper)) = pointBounds13061 := by
 decide +kernel
def cuts13062 : List PrefixCut := [⟨36,285573430,285573637⟩,
⟨89,707279225,707279734⟩,
⟨128,1016784071,1016784801⟩]
theorem checked13062 : checkPrefixCuts (2^48) 1715994625 9 Manual.Count131072.C013062.packed 128 cuts13062 = true := by
 decide +kernel
def pointBounds13062 : List (Nat × Nat × Nat) := [(1716031488,94447669350538,94448046121287),(1716085760,94448091056333,94448467827384)]
theorem point_links_checked13062 : (cuts13062.take 2).map (fun c => (1715994625-1+2*2^9*c.k,94447383777108+c.lower,94447760547650+c.upper)) = pointBounds13062 := by
 decide +kernel
def cuts13063 : List PrefixCut := [⟨14,110547421,110547502⟩,
⟨67,532062589,532062977⟩,
⟨120,965865028,965865727⟩,
⟨128,1031959244,1031959991⟩]
theorem checked13063 : checkPrefixCuts (2^48) 1716125697 9 Manual.Count131072.C013063.packed 128 cuts13063 = true := by
 decide +kernel
def pointBounds13063 : List (Nat × Nat × Nat) := [(1716140032,94448511108600,94448887879953),(1716194304,94448932623768,94449309395428),(1716248576,94449366426207,94449743198178)]
theorem point_links_checked13063 : (cuts13063.take 3).map (fun c => (1716125697-1+2*2^9*c.k,94448400561179+c.lower,94448777332451+c.upper)) = pointBounds13063 := by
 decide +kernel
def cuts13064 : List PrefixCut := [⟨45,353426160,353426418⟩,
⟨98,768177360,768177918⟩,
⟨128,1004000786,1004001515⟩]
theorem checked13064 : checkPrefixCuts (2^48) 1716256769 9 Manual.Count131072.C013064.packed 128 cuts13064 = true := by
 decide +kernel
def pointBounds13064 : List (Nat × Nat × Nat) := [(1716302848,94449785946583,94450162718860),(1716357120,94450200697783,94450577470360)]
theorem point_links_checked13064 : (cuts13064.take 2).map (fun c => (1716256769-1+2*2^9*c.k,94449432520423+c.lower,94449809292442+c.upper)) = pointBounds13064 := by
 decide +kernel
def cuts13065 : List PrefixCut := [⟨23,179898595,179898727⟩,
⟨76,613154167,613154617⟩,
⟨128,1030653906,1030654658⟩]
theorem checked13065 : checkPrefixCuts (2^48) 1716387841 9 Manual.Count131072.C013065.packed 128 cuts13065 = true := by
 decide +kernel
def pointBounds13065 : List (Nat × Nat × Nat) := [(1716411392,94450616419804,94450993192684),(1716465664,94451049675376,94451426448574)]
theorem point_links_checked13065 : (cuts13065.take 2).map (fun c => (1716387841-1+2*2^9*c.k,94450436521209+c.lower,94450813293957+c.upper)) = pointBounds13065 := by
 decide +kernel
def cuts13066 : List PrefixCut := [⟨1,8035021,8035026⟩,
⟨54,425849342,425849646⟩,
⟨107,846601977,846602583⟩,
⟨128,1009914674,1009915400⟩]
theorem checked13066 : checkPrefixCuts (2^48) 1716518913 9 Manual.Count131072.C013066.packed 128 cuts13066 = true := by
 decide +kernel
def pointBounds13066 : List (Nat × Nat × Nat) := [(1716519936,94451475210136,94451851983641),(1716574208,94451893024457,94452269798261),(1716628480,94452313777092,94452690551198)]
theorem point_links_checked13066 : (cuts13066.take 3).map (fun c => (1716518913-1+2*2^9*c.k,94451467175115+c.lower,94451843948615+c.upper)) = pointBounds13066 := by
 decide +kernel
def cuts13067 : List PrefixCut := [⟨32,252999510,252999696⟩,
⟨85,671594105,671594593⟩,
⟨128,1020986742,1020987482⟩]
theorem checked13067 : checkPrefixCuts (2^48) 1716649985 9 Manual.Count131072.C013067.packed 128 cuts13067 = true := by
 decide +kernel
def pointBounds13067 : List (Nat × Nat × Nat) := [(1716682752,94452730089299,94453106863711),(1716737024,94453148683894,94453525458608)]
theorem point_links_checked13067 : (cuts13067.take 2).map (fun c => (1716649985-1+2*2^9*c.k,94452477089789+c.lower,94452853864015+c.upper)) = pointBounds13067 := by
 decide +kernel
def cuts13068 : List PrefixCut := [⟨10,77714454,77714510⟩,
⟨63,490544217,490544573⟩,
⟨116,905164262,905164917⟩,
⟨128,1000087314,1000088037⟩]
theorem checked13068 : checkPrefixCuts (2^48) 1716781057 9 Manual.Count131072.C013068.packed 128 cuts13068 = true := by
 decide +kernel
def pointBounds13068 : List (Nat × Nat × Nat) := [(1716791296,94453575790985,94453952566007),(1716845568,94453988620748,94454365396070),(1716899840,94454403240793,94454780016414)]
theorem point_links_checked13068 : (cuts13068.take 3).map (fun c => (1716781057-1+2*2^9*c.k,94453498076531+c.lower,94453874851497+c.upper)) = pointBounds13068 := by
 decide +kernel
def cuts13069 : List PrefixCut := [⟨41,320667667,320667899⟩,
⟨94,739523849,739524386⟩,
⟨128,1011158611,1011159345⟩]
theorem checked13069 : checkPrefixCuts (2^48) 1716912129 9 Manual.Count131072.C013069.packed 128 cuts13069 = true := by
 decide +kernel
def pointBounds13069 : List (Nat × Nat × Nat) := [(1716954112,94454818831512,94455195607433),(1717008384,94455237687694,94455614463920)]
theorem point_links_checked13069 : (cuts13069.take 2).map (fun c => (1716912129-1+2*2^9*c.k,94454498163845+c.lower,94454874939534+c.upper)) = pointBounds13069 := by
 decide +kernel
def cuts13070 : List PrefixCut := [⟨19,150159020,150159128⟩,
⟨72,563415231,563415637⟩,
⟨125,981576018,981576729⟩,
⟨128,1008130673,1008131403⟩]
theorem checked13070 : checkPrefixCuts (2^48) 1717043201 9 Manual.Count131072.C013070.packed 128 cuts13070 = true := by
 decide +kernel
def pointBounds13070 : List (Nat × Nat × Nat) := [(1717062656,94455659481476,94456036258007),(1717116928,94456072737687,94456449514516),(1717171200,94456490898474,94456867675608)]
theorem point_links_checked13070 : (cuts13070.take 3).map (fun c => (1717043201-1+2*2^9*c.k,94455509322456+c.lower,94455886098879+c.upper)) = pointBounds13070 := by
 decide +kernel
def cuts13071 : List PrefixCut := [⟨50,392248633,392248915⟩,
⟨103,812349906,812350496⟩,
⟨128,1007726079,1007726811⟩]
theorem checked13071 : checkPrefixCuts (2^48) 1717174273 9 Manual.Count131072.C013071.packed 128 cuts13071 = true := by
 decide +kernel
def pointBounds13071 : List (Nat × Nat × Nat) := [(1717225472,94456909701762,94457286479197),(1717279744,94457329803035,94457706580778)]
theorem point_links_checked13071 : (cuts13071.take 2).map (fun c => (1717174273-1+2*2^9*c.k,94456517453129+c.lower,94456894230282+c.upper)) = pointBounds13071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000095
