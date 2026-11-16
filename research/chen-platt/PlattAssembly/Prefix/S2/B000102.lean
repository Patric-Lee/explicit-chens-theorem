import PlattAssemblyKernel
import PlattCertificates.Count131072.C013264
import PlattCertificates.Count131072.C013265
import PlattCertificates.Count131072.C013266
import PlattCertificates.Count131072.C013267
import PlattCertificates.Count131072.C013268
import PlattCertificates.Count131072.C013269
import PlattCertificates.Count131072.C013270
import PlattCertificates.Count131072.C013271
import PlattCertificates.Count131072.C013272
import PlattCertificates.Count131072.C013273
import PlattCertificates.Count131072.C013274
import PlattCertificates.Count131072.C013275
import PlattCertificates.Count131072.C013276
import PlattCertificates.Count131072.C013277
import PlattCertificates.Count131072.C013278
import PlattCertificates.Count131072.C013279
import PlattCertificates.Count131072.C013280
import PlattCertificates.Count131072.C013281
import PlattCertificates.Count131072.C013282
import PlattCertificates.Count131072.C013283
import PlattCertificates.Count131072.C013284
import PlattCertificates.Count131072.C013285
import PlattCertificates.Count131072.C013286
import PlattCertificates.Count131072.C013287
import PlattCertificates.Count131072.C013288
import PlattCertificates.Count131072.C013289
import PlattCertificates.Count131072.C013290
import PlattCertificates.Count131072.C013291
import PlattCertificates.Count131072.C013292
import PlattCertificates.Count131072.C013293
import PlattCertificates.Count131072.C013294
import PlattCertificates.Count131072.C013295
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000102
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13264 : List PrefixCut := [⟨42,330825247,330825480⟩,
⟨96,749675598,749676130⟩,
⟨128,995519901,995520608⟩]
theorem checked13264 : checkPrefixCuts (2^48) 1742471169 9 Manual.Count131072.C013264.packed 128 cuts13264 = true := by
 decide +kernel
def pointBounds13264 : List (Nat × Nat × Nat) := [(1742514176,94650303122420,94650680039058),(1742569472,94650721972771,94651098889708)]
theorem point_links_checked13264 : (cuts13264.take 2).map (fun c => (1742471169-1+2*2^9*c.k,94649972297173+c.lower,94650349213578+c.upper)) = pointBounds13264 := by
 decide +kernel
def cuts13265 : List PrefixCut := [⟨22,173638884,173639008⟩,
⟨76,590039957,590040383⟩,
⟨128,994798859,994799577⟩]
theorem checked13265 : checkPrefixCuts (2^48) 1742602241 9 Manual.Count131072.C013265.packed 128 cuts13265 = true := by
 decide +kernel
def pointBounds13265 : List (Nat × Nat × Nat) := [(1742624768,94651141455958,94651518373194),(1742680064,94651557857031,94651934774569)]
theorem point_links_checked13265 : (cuts13265.take 2).map (fun c => (1742602241-1+2*2^9*c.k,94650967817074+c.lower,94651344734186+c.upper)) = pointBounds13265 := by
 decide +kernel
def cuts13266 : List PrefixCut := [⟨2,15182256,15182267⟩,
⟨56,430426284,430426594⟩,
⟨110,847918248,847918855⟩,
⟨128,989555640,989556351⟩]
theorem checked13266 : checkPrefixCuts (2^48) 1742733313 9 Manual.Count131072.C013266.packed 128 cuts13266 = true := by
 decide +kernel
def pointBounds13266 : List (Nat × Nat × Nat) := [(1742735360,94651977798189,94652354716030),(1742790656,94652393042217,94652769960357),(1742845952,94652810534181,94653187452618)]
theorem point_links_checked13266 : (cuts13266.take 3).map (fun c => (1742733313-1+2*2^9*c.k,94651962615933+c.lower,94652339533763+c.upper)) = pointBounds13266 := by
 decide +kernel
def cuts13267 : List PrefixCut := [⟨36,280524839,280525040⟩,
⟨90,699282157,699282654⟩,
⟨128,992226756,992227465⟩]
theorem checked13267 : checkPrefixCuts (2^48) 1742864385 9 Manual.Count131072.C013267.packed 128 cuts13267 = true := by
 decide +kernel
def pointBounds13267 : List (Nat × Nat × Nat) := [(1742901248,94653232696412,94653609615154),(1742956544,94653651453730,94654028372768)]
theorem point_links_checked13267 : (cuts13267.take 2).map (fun c => (1742864385-1+2*2^9*c.k,94652952171573+c.lower,94653329090114+c.upper)) = pointBounds13267 := by
 decide +kernel
def cuts13268 : List PrefixCut := [⟨16,131290075,131290171⟩,
⟨70,557287735,557288137⟩,
⟨124,978427538,978428240⟩,
⟨128,1012176276,1012177002⟩]
theorem checked13268 : checkPrefixCuts (2^48) 1742995457 9 Manual.Count131072.C013268.packed 128 cuts13268 = true := by
 decide +kernel
def pointBounds13268 : List (Nat × Nat × Nat) := [(1743011840,94654075688404,94654452607750),(1743067136,94654501686064,94654878605716),(1743122432,94654922825867,94655299745819)]
theorem point_links_checked13268 : (cuts13268.take 3).map (fun c => (1742995457-1+2*2^9*c.k,94653944398329+c.lower,94654321317579+c.upper)) = pointBounds13268 := by
 decide +kernel
def cuts13269 : List PrefixCut := [⟨50,383825254,383825528⟩,
⟨104,800094133,800094707⟩,
⟨128,996436795,996437509⟩]
theorem checked13269 : checkPrefixCuts (2^48) 1743126529 9 Manual.Count131072.C013269.packed 128 cuts13269 = true := by
 decide +kernel
def pointBounds13269 : List (Nat × Nat × Nat) := [(1743177728,94655340399859,94655717320109),(1743233024,94655756668738,94656133589288)]
theorem point_links_checked13269 : (cuts13269.take 2).map (fun c => (1743126529-1+2*2^9*c.k,94654956574605+c.lower,94655333494581+c.upper)) = pointBounds13269 := by
 decide +kernel
def cuts13270 : List PrefixCut := [⟨30,228632242,228632402⟩,
⟨84,645359034,645359493⟩,
⟨128,985382926,985383629⟩]
theorem checked13270 : checkPrefixCuts (2^48) 1743257601 9 Manual.Count131072.C013270.packed 128 cuts13270 = true := by
 decide +kernel
def pointBounds13270 : List (Nat × Nat × Nat) := [(1743288320,94656181643642,94656558564492),(1743343616,94656598370434,94656975291583)]
theorem point_links_checked13270 : (cuts13270.take 2).map (fun c => (1743257601-1+2*2^9*c.k,94655953011400+c.lower,94656329932090+c.upper)) = pointBounds13270 := by
 decide +kernel
def cuts13271 : List PrefixCut := [⟨10,76366918,76366973⟩,
⟨64,491614363,491614711⟩,
⟨118,910561785,910562439⟩,
⟨128,989667908,989668618⟩]
theorem checked13271 : checkPrefixCuts (2^48) 1743388673 9 Manual.Count131072.C013271.packed 128 cuts13271 = true := by
 decide +kernel
def pointBounds13271 : List (Nat × Nat × Nat) := [(1743398912,94657014761244,94657391682692),(1743454208,94657430008689,94657806930430),(1743509504,94657848956111,94658225878158)]
theorem point_links_checked13271 : (cuts13271.take 3).map (fun c => (1743388673-1+2*2^9*c.k,94656938394326+c.lower,94657315315719+c.upper)) = pointBounds13271 := by
 decide +kernel
def cuts13272 : List PrefixCut := [⟨44,339989547,339989790⟩,
⟨98,762139109,762139650⟩,
⟨128,992983827,992984536⟩]
theorem checked13272 : checkPrefixCuts (2^48) 1743519745 9 Manual.Count131072.C013272.packed 128 cuts13272 = true := by
 decide +kernel
def pointBounds13272 : List (Nat × Nat × Nat) := [(1743564800,94658268051781,94658644974127),(1743620096,94658690201343,94659067123987)]
theorem point_links_checked13272 : (cuts13272.take 2).map (fun c => (1743519745-1+2*2^9*c.k,94657928062234+c.lower,94658304984337+c.upper)) = pointBounds13272 := by
 decide +kernel
def cuts13273 : List PrefixCut := [⟨24,187255705,187255841⟩,
⟨78,601145869,601146307⟩,
⟨128,989680692,989681412⟩]
theorem checked13273 : checkPrefixCuts (2^48) 1743650817 9 Manual.Count131072.C013273.packed 128 cuts13273 = true := by
 decide +kernel
def pointBounds13273 : List (Nat × Nat × Nat) := [(1743675392,94659108301766,94659485224714),(1743730688,94659522191930,94659899115180)]
theorem point_links_checked13273 : (cuts13273.take 2).map (fun c => (1743650817-1+2*2^9*c.k,94658921046061+c.lower,94659297968873+c.upper)) = pointBounds13273 := by
 decide +kernel
def cuts13274 : List PrefixCut := [⟨4,34543056,34543081⟩,
⟨58,459544447,459544778⟩,
⟨112,884048247,884048880⟩,
⟨128,1013656422,1013657148⟩]
theorem checked13274 : checkPrefixCuts (2^48) 1743781889 9 Manual.Count131072.C013274.packed 128 cuts13274 = true := by
 decide +kernel
def pointBounds13274 : List (Nat × Nat × Nat) := [(1743785984,94659945269809,94660322193366),(1743841280,94660370271200,94660747195063),(1743896576,94660794775000,94661171699165)]
theorem point_links_checked13274 : (cuts13274.take 3).map (fun c => (1743781889-1+2*2^9*c.k,94659910726753+c.lower,94660287650285+c.upper)) = pointBounds13274 := by
 decide +kernel
def cuts13275 : List PrefixCut := [⟨38,291976955,291977162⟩,
⟨92,712096087,712096592⟩,
⟨128,991791487,991792190⟩]
theorem checked13275 : checkPrefixCuts (2^48) 1743912961 9 Manual.Count131072.C013275.packed 128 cuts13275 = true := by
 decide +kernel
def pointBounds13275 : List (Nat × Nat × Nat) := [(1743951872,94661216360130,94661593284595),(1744007168,94661636479262,94662013404025)]
theorem point_links_checked13275 : (cuts13275.take 2).map (fun c => (1743912961-1+2*2^9*c.k,94660924383175+c.lower,94661301307433+c.upper)) = pointBounds13275 := by
 decide +kernel
def cuts13276 : List PrefixCut := [⟨18,141862894,141862995⟩,
⟨72,562278140,562278545⟩,
⟨126,978161194,978161892⟩,
⟨128,993008157,993008866⟩]
theorem checked13276 : checkPrefixCuts (2^48) 1744044033 9 Manual.Count131072.C013276.packed 128 cuts13276 = true := by
 decide +kernel
def pointBounds13276 : List (Nat × Nat × Nat) := [(1744062464,94662058037556,94662434962618),(1744117760,94662478452802,94662855378168),(1744173056,94662894335856,94663271261515)]
theorem point_links_checked13276 : (cuts13276.take 3).map (fun c => (1744044033-1+2*2^9*c.k,94661916174662+c.lower,94662293099623+c.upper)) = pointBounds13276 := by
 decide +kernel
def cuts13277 : List PrefixCut := [⟨52,410060146,410060437⟩,
⟨106,828821599,828822194⟩,
⟨128,986640360,986641069⟩]
theorem checked13277 : checkPrefixCuts (2^48) 1744175105 9 Manual.Count131072.C013277.packed 128 cuts13277 = true := by
 decide +kernel
def pointBounds13277 : List (Nat × Nat × Nat) := [(1744228352,94663319242965,94663696168926),(1744283648,94663738004418,94664114930683)]
theorem point_links_checked13277 : (cuts13277.take 2).map (fun c => (1744175105-1+2*2^9*c.k,94662909182819+c.lower,94663286108489+c.upper)) = pointBounds13277 := by
 decide +kernel
def cuts13278 : List PrefixCut := [⟨32,249794993,249795175⟩,
⟨86,670466345,670466826⟩,
⟨128,1000442859,1000443577⟩]
theorem checked13278 : checkPrefixCuts (2^48) 1744306177 9 Manual.Count131072.C013278.packed 128 cuts13278 = true := by
 decide +kernel
def pointBounds13278 : List (Nat × Nat × Nat) := [(1744338944,94664145618172,94664522544733),(1744394240,94664566289524,94664943216384)]
theorem point_links_checked13278 : (cuts13278.take 2).map (fun c => (1744306177-1+2*2^9*c.k,94663895823179+c.lower,94664272749558+c.upper)) = pointBounds13278 := by
 decide +kernel
def cuts13279 : List PrefixCut := [⟨12,86324981,86325045⟩,
⟨66,521491277,521491648⟩,
⟨120,927601345,927602005⟩,
⟨128,987621288,987621992⟩]
theorem checked13279 : checkPrefixCuts (2^48) 1744437249 9 Manual.Count131072.C013279.packed 128 cuts13279 = true := by
 decide +kernel
def pointBounds13279 : List (Nat × Nat × Nat) := [(1744449536,94664982591019,94665359518180),(1744504832,94665417757315,94665794684783),(1744560128,94665823867383,94666200795140)]
theorem point_links_checked13279 : (cuts13279.take 3).map (fun c => (1744437249-1+2*2^9*c.k,94664896266038+c.lower,94665273193135+c.upper)) = pointBounds13279 := by
 decide +kernel
def cuts13280 : List PrefixCut := [⟨46,363824783,363825044⟩,
⟨100,780234666,780235227⟩,
⟨128,994807285,994808001⟩]
theorem checked13280 : checkPrefixCuts (2^48) 1744568321 9 Manual.Count131072.C013280.packed 128 cuts13280 = true := by
 decide +kernel
def pointBounds13280 : List (Nat × Nat × Nat) := [(1744615424,94666247712109,94666624640171),(1744670720,94666664121992,94667041050354)]
theorem point_links_checked13280 : (cuts13280.take 2).map (fun c => (1744568321-1+2*2^9*c.k,94665883887326+c.lower,94666260815127+c.upper)) = pointBounds13280 := by
 decide +kernel
def cuts13281 : List PrefixCut := [⟨26,200210804,200210946⟩,
⟨80,622886041,622886480⟩,
⟨128,999733322,999734030⟩]
theorem checked13281 : checkPrefixCuts (2^48) 1744699393 9 Manual.Count131072.C013281.packed 128 cuts13281 = true := by
 decide +kernel
def pointBounds13281 : List (Nat × Nat × Nat) := [(1744726016,94667078905415,94667455834074),(1744781312,94667501580652,94667878509608)]
theorem point_links_checked13281 : (cuts13281.take 2).map (fun c => (1744699393-1+2*2^9*c.k,94666878694611+c.lower,94667255623128+c.upper)) = pointBounds13281 := by
 decide +kernel
def cuts13282 : List PrefixCut := [⟨6,44201420,44201453⟩,
⟨60,452976630,452976954⟩,
⟨114,871901530,871902155⟩,
⟨128,980945645,980946349⟩]
theorem checked13282 : checkPrefixCuts (2^48) 1744830465 9 Manual.Count131072.C013282.packed 128 cuts13282 = true := by
 decide +kernel
def pointBounds13282 : List (Nat × Nat × Nat) := [(1744836608,94667922629353,94668299558611),(1744891904,94668331404563,94668708334112),(1744947200,94668750329463,94669127259313)]
theorem point_links_checked13282 : (cuts13282.take 3).map (fun c => (1744830465-1+2*2^9*c.k,94667878427933+c.lower,94668255357158+c.upper)) = pointBounds13282 := by
 decide +kernel
def cuts13283 : List PrefixCut := [⟨40,312770991,312771220⟩,
⟨94,729249912,729250441⟩,
⟨128,998938054,998938780⟩]
theorem checked13283 : checkPrefixCuts (2^48) 1744961537 9 Manual.Count131072.C013283.packed 128 cuts13283 = true := by
 decide +kernel
def pointBounds13283 : List (Nat × Nat × Nat) := [(1745002496,94669172144569,94669549074727),(1745057792,94669588623490,94669965553948)]
theorem point_links_checked13283 : (cuts13283.take 2).map (fun c => (1744961537-1+2*2^9*c.k,94668859373578+c.lower,94669236303507+c.upper)) = pointBounds13283 := by
 decide +kernel
def cuts13284 : List PrefixCut := [⟨20,160810259,160810372⟩,
⟨74,581456198,581456614⟩,
⟨128,1002411364,1002412082⟩]
theorem checked13284 : checkPrefixCuts (2^48) 1745092609 9 Manual.Count131072.C013284.packed 128 cuts13284 = true := by
 decide +kernel
def pointBounds13284 : List (Nat × Nat × Nat) := [(1745113088,94670019121891,94670396052659),(1745168384,94670439767830,94670816698901),(1745223680,94670860722996,94671237654369)]
theorem point_links_checked13284 : (cuts13284.take 3).map (fun c => (1745092609-1+2*2^9*c.k,94669858311632+c.lower,94670235242287+c.upper)) = pointBounds13284 := by
 decide +kernel
def cuts13285 : List PrefixCut := [⟨54,405459081,405459377⟩,
⟨108,829613210,829613809⟩,
⟨128,985885603,985886314⟩]
theorem checked13285 : checkPrefixCuts (2^48) 1745223681 9 Manual.Count131072.C013285.packed 128 cuts13285 = true := by
 decide +kernel
def pointBounds13285 : List (Nat × Nat × Nat) := [(1745278976,94671266182077,94671643113746),(1745334272,94671690336206,94672067268178)]
theorem point_links_checked13285 : (cuts13285.take 2).map (fun c => (1745223681-1+2*2^9*c.k,94670860722996+c.lower,94671237654369+c.upper)) = pointBounds13285 := by
 decide +kernel
def cuts13286 : List PrefixCut := [⟨34,272222500,272222692⟩,
⟨88,698768663,698769157⟩,
⟨128,1008389105,1008389820⟩]
theorem checked13286 : checkPrefixCuts (2^48) 1745354753 9 Manual.Count131072.C013286.packed 128 cuts13286 = true := by
 decide +kernel
def pointBounds13286 : List (Nat × Nat × Nat) := [(1745389568,94672118831099,94672495763375),(1745444864,94672545377262,94672922309840)]
theorem point_links_checked13286 : (cuts13286.take 2).map (fun c => (1745354753-1+2*2^9*c.k,94671846608599+c.lower,94672223540683+c.upper)) = pointBounds13286 := by
 decide +kernel
def cuts13287 : List PrefixCut := [⟨14,105624066,105624145⟩,
⟨68,528595655,528596031⟩,
⟨122,947845095,947845770⟩,
⟨128,994606705,994607413⟩]
theorem checked13287 : checkPrefixCuts (2^48) 1745485825 9 Manual.Count131072.C013287.packed 128 cuts13287 = true := by
 decide +kernel
def pointBounds13287 : List (Nat × Nat × Nat) := [(1745500160,94672960621770,94673337554648),(1745555456,94673383593359,94673760526534),(1745610752,94673802842799,94674179776273)]
theorem point_links_checked13287 : (cuts13287.take 3).map (fun c => (1745485825-1+2*2^9*c.k,94672854997704+c.lower,94673231930503+c.upper)) = pointBounds13287 := by
 decide +kernel
def cuts13288 : List PrefixCut := [⟨48,376989343,376989615⟩,
⟨102,799436945,799437518⟩,
⟨128,1005979964,1005980680⟩]
theorem checked13288 : checkPrefixCuts (2^48) 1745616897 9 Manual.Count131072.C013288.packed 128 cuts13288 = true := by
 decide +kernel
def pointBounds13288 : List (Nat × Nat × Nat) := [(1745666048,94674226593752,94674603527531),(1745721344,94674649041354,94675025975434)]
theorem point_links_checked13288 : (cuts13288.take 2).map (fun c => (1745616897-1+2*2^9*c.k,94673849604409+c.lower,94674226537916+c.upper)) = pointBounds13288 := by
 decide +kernel
def cuts13289 : List PrefixCut := [⟨28,205411083,205411235⟩,
⟨82,629283048,629283508⟩,
⟨128,983171007,983171721⟩]
theorem checked13289 : checkPrefixCuts (2^48) 1745747969 9 Manual.Count131072.C013289.packed 128 cuts13289 = true := by
 decide +kernel
def pointBounds13289 : List (Nat × Nat × Nat) := [(1745776640,94675060995456,94675437929831),(1745831936,94675484867421,94675861802104)]
theorem point_links_checked13289 : (cuts13289.take 2).map (fun c => (1745747969-1+2*2^9*c.k,94674855584373+c.lower,94675232518596+c.upper)) = pointBounds13289 := by
 decide +kernel
def cuts13290 : List PrefixCut := [⟨8,59329718,59329761⟩,
⟨62,473340402,473340739⟩,
⟨116,892335678,892336316⟩,
⟨128,981485306,981486007⟩]
theorem checked13290 : checkPrefixCuts (2^48) 1745879041 9 Manual.Count131072.C013290.packed 128 cuts13290 = true := by
 decide +kernel
def pointBounds13290 : List (Nat × Nat × Nat) := [(1745887232,94675898085098,94676275020078),(1745942528,94676312095782,94676689031056),(1745997824,94676731091058,94677108026633)]
theorem point_links_checked13290 : (cuts13290.take 3).map (fun c => (1745879041-1+2*2^9*c.k,94675838755380+c.lower,94676215690317+c.upper)) = pointBounds13290 := by
 decide +kernel
def cuts13291 : List PrefixCut := [⟨42,325963378,325963609⟩,
⟨96,750574305,750574836⟩,
⟨128,1002690727,1002691437⟩]
theorem checked13291 : checkPrefixCuts (2^48) 1746010113 9 Manual.Count131072.C013291.packed 128 cuts13291 = true := by
 decide +kernel
def pointBounds13291 : List (Nat × Nat × Nat) := [(1746053120,94677146204064,94677523139933),(1746108416,94677570814991,94677947751160)]
theorem point_links_checked13291 : (cuts13291.take 2).map (fun c => (1746010113-1+2*2^9*c.k,94676820240686+c.lower,94677197176324+c.upper)) = pointBounds13291 := by
 decide +kernel
def cuts13292 : List PrefixCut := [⟨22,174415382,174415507⟩,
⟨76,598676877,598677307⟩,
⟨128,985851794,985852502⟩]
theorem checked13292 : checkPrefixCuts (2^48) 1746141185 9 Manual.Count131072.C013292.packed 128 cuts13292 = true := by
 decide +kernel
def pointBounds13292 : List (Nat × Nat × Nat) := [(1746163712,94677997346795,94678374283268),(1746219008,94678421608290,94678798545068)]
theorem point_links_checked13292 : (cuts13292.take 2).map (fun c => (1746141185-1+2*2^9*c.k,94677822931413+c.lower,94678199867761+c.upper)) = pointBounds13292 := by
 decide +kernel
def cuts13293 : List PrefixCut := [⟨2,14023185,14023195⟩,
⟨56,428264478,428264788⟩,
⟨110,851035140,851035751⟩,
⟨128,994158441,994159152⟩]
theorem checked13293 : checkPrefixCuts (2^48) 1746272257 9 Manual.Count131072.C013293.packed 128 cuts13293 = true := by
 decide +kernel
def pointBounds13293 : List (Nat × Nat × Nat) := [(1746274304,94678822806392,94679199743458),(1746329600,94679237047685,94679613985051),(1746384896,94679659818347,94680036756014)]
theorem point_links_checked13293 : (cuts13293.take 3).map (fun c => (1746272257-1+2*2^9*c.k,94678808783207+c.lower,94679185720263+c.upper)) = pointBounds13293 := by
 decide +kernel
def cuts13294 : List PrefixCut := [⟨36,280923384,280923586⟩,
⟨90,707535316,707535821⟩,
⟨128,1001336821,1001337538⟩]
theorem checked13294 : checkPrefixCuts (2^48) 1746403329 9 Manual.Count131072.C013294.packed 128 cuts13294 = true := by
 decide +kernel
def pointBounds13294 : List (Nat × Nat × Nat) := [(1746440192,94680083865032,94680460803001),(1746495488,94680510476964,94680887415236)]
theorem point_links_checked13294 : (cuts13294.take 2).map (fun c => (1746403329-1+2*2^9*c.k,94679802941648+c.lower,94680179879415+c.upper)) = pointBounds13294 := by
 decide +kernel
def cuts13295 : List PrefixCut := [⟨16,121837849,121837937⟩,
⟨70,536013404,536013789⟩,
⟨124,956944486,956945177⟩,
⟨128,988852194,988852907⟩]
theorem checked13295 : checkPrefixCuts (2^48) 1746534401 9 Manual.Count131072.C013295.packed 128 cuts13295 = true := by
 decide +kernel
def pointBounds13295 : List (Nat × Nat × Nat) := [(1746550784,94680926116318,94681303054890),(1746606080,94681340291873,94681717230742),(1746661376,94681761222955,94682138162130)]
theorem point_links_checked13295 : (cuts13295.take 3).map (fun c => (1746534401-1+2*2^9*c.k,94680804278469+c.lower,94681181216953+c.upper)) = pointBounds13295 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000102
