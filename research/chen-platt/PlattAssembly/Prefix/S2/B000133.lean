import PlattAssemblyKernel
import PlattCertificates.Count131072.C014256
import PlattCertificates.Count131072.C014257
import PlattCertificates.Count131072.C014258
import PlattCertificates.Count131072.C014259
import PlattCertificates.Count131072.C014260
import PlattCertificates.Count131072.C014261
import PlattCertificates.Count131072.C014262
import PlattCertificates.Count131072.C014263
import PlattCertificates.Count131072.C014264
import PlattCertificates.Count131072.C014265
import PlattCertificates.Count131072.C014266
import PlattCertificates.Count131072.C014267
import PlattCertificates.Count131072.C014268
import PlattCertificates.Count131072.C014269
import PlattCertificates.Count131072.C014270
import PlattCertificates.Count131072.C014271
import PlattCertificates.Count131072.C014272
import PlattCertificates.Count131072.C014273
import PlattCertificates.Count131072.C014274
import PlattCertificates.Count131072.C014275
import PlattCertificates.Count131072.C014276
import PlattCertificates.Count131072.C014277
import PlattCertificates.Count131072.C014278
import PlattCertificates.Count131072.C014279
import PlattCertificates.Count131072.C014280
import PlattCertificates.Count131072.C014281
import PlattCertificates.Count131072.C014282
import PlattCertificates.Count131072.C014283
import PlattCertificates.Count131072.C014284
import PlattCertificates.Count131072.C014285
import PlattCertificates.Count131072.C014286
import PlattCertificates.Count131072.C014287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000133
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14256 : List PrefixCut := [⟨18,127772053,127772139⟩,
⟨76,543097762,543098135⟩,
⟨128,917075025,917075653⟩]
theorem checked14256 : checkPrefixCuts (2^48) 1872494593 9 Manual.Count131072.C014256.packed 128 cuts14256 = true := by
 decide +kernel
def pointBounds14256 : List (Nat × Nat × Nat) := [(1872513024,95600404612784,95600782195369),(1872572416,95600819938493,95601197521365)]
theorem point_links_checked14256 : (cuts14256.take 2).map (fun c => (1872494593-1+2*2^9*c.k,95600276840731+c.lower,95600654423230+c.upper)) = pointBounds14256 := by
 decide +kernel
def cuts14257 : List PrefixCut := [⟨6,41936497,41936527⟩,
⟨64,470011876,470012198⟩,
⟨122,887402202,887402811⟩,
⟨128,930989200,930989839⟩]
theorem checked14257 : checkPrefixCuts (2^48) 1872625665 9 Manual.Count131072.C014257.packed 128 cuts14257 = true := by
 decide +kernel
def pointBounds14257 : List (Nat × Nat × Nat) := [(1872631808,95601235852253,95601613435410),(1872691200,95601663927632,95602041511081),(1872750592,95602081317958,95602458901694)]
theorem point_links_checked14257 : (cuts14257.take 3).map (fun c => (1872625665-1+2*2^9*c.k,95601193915756+c.lower,95601571498883+c.upper)) = pointBounds14257 := by
 decide +kernel
def cuts14258 : List PrefixCut := [⟨52,379501420,379501675⟩,
⟨110,801975349,801975891⟩,
⟨128,930022410,930023042⟩]
theorem checked14258 : checkPrefixCuts (2^48) 1872756737 9 Manual.Count131072.C014258.packed 128 cuts14258 = true := by
 decide +kernel
def pointBounds14258 : List (Nat × Nat × Nat) := [(1872809984,95602504406376,95602881990397),(1872869376,95602926880305,95603304464613)]
theorem point_links_checked14258 : (cuts14258.take 2).map (fun c => (1872756737-1+2*2^9*c.k,95602124904956+c.lower,95602502488722+c.upper)) = pointBounds14258 := by
 decide +kernel
def cuts14259 : List PrefixCut := [⟨40,294112826,294113025⟩,
⟨98,710849211,710849695⟩,
⟨128,929205972,929206605⟩]
theorem checked14259 : checkPrefixCuts (2^48) 1872887809 9 Manual.Count131072.C014259.packed 128 cuts14259 = true := by
 decide +kernel
def pointBounds14259 : List (Nat × Nat × Nat) := [(1872928768,95603349040192,95603726624789),(1872988160,95603765776577,95604143361459)]
theorem point_links_checked14259 : (cuts14259.take 2).map (fun c => (1872887809-1+2*2^9*c.k,95603054927366+c.lower,95603432511764+c.upper)) = pointBounds14259 := by
 decide +kernel
def cuts14260 : List PrefixCut := [⟨28,198817226,198817364⟩,
⟨86,610417809,610418233⟩,
⟨128,916667895,916668530⟩]
theorem checked14260 : checkPrefixCuts (2^48) 1873018881 9 Manual.Count131072.C014260.packed 128 cuts14260 = true := by
 decide +kernel
def pointBounds14260 : List (Nat × Nat × Nat) := [(1873047552,95604182950564,95604560535733),(1873106944,95604594551147,95604972136602)]
theorem point_links_checked14260 : (cuts14260.take 2).map (fun c => (1873018881-1+2*2^9*c.k,95603984133338+c.lower,95604361718369+c.upper)) = pointBounds14260 := by
 decide +kernel
def cuts14261 : List PrefixCut := [⟨16,112850938,112851017⟩,
⟨74,525326988,525327353⟩,
⟨128,926220453,926221089⟩]
theorem checked14261 : checkPrefixCuts (2^48) 1873149953 9 Manual.Count131072.C014261.packed 128 cuts14261 = true := by
 decide +kernel
def pointBounds14261 : List (Nat × Nat × Nat) := [(1873166336,95605013652171,95605391237916),(1873225728,95605426128221,95605803714252)]
theorem point_links_checked14261 : (cuts14261.take 2).map (fun c => (1873149953-1+2*2^9*c.k,95604900801233+c.lower,95605278386899+c.upper)) = pointBounds14261 := by
 decide +kernel
def cuts14262 : List PrefixCut := [⟨4,27647385,27647404⟩,
⟨62,443553132,443553434⟩,
⟨120,867409019,867409612⟩,
⟨128,925254307,925254940⟩]
theorem checked14262 : checkPrefixCuts (2^48) 1873281025 9 Manual.Count131072.C014262.packed 128 cuts14262 = true := by
 decide +kernel
def pointBounds14262 : List (Nat × Nat × Nat) := [(1873285120,95605854669071,95606232255392),(1873344512,95606270574818,95606648161422),(1873403904,95606694430705,95607072017600)]
theorem point_links_checked14262 : (cuts14262.take 3).map (fun c => (1873281025-1+2*2^9*c.k,95605827021686+c.lower,95606204607988+c.upper)) = pointBounds14262 := by
 decide +kernel
def cuts14263 : List PrefixCut := [⟨50,358034141,358034387⟩,
⟨108,777806587,777807119⟩,
⟨128,918729352,918729984⟩]
theorem checked14263 : checkPrefixCuts (2^48) 1873412097 9 Manual.Count131072.C014263.packed 128 cuts14263 = true := by
 decide +kernel
def pointBounds14263 : List (Nat × Nat × Nat) := [(1873463296,95607110310134,95607487897315),(1873522688,95607530082580,95607907670047)]
theorem point_links_checked14263 : (cuts14263.take 2).map (fun c => (1873412097-1+2*2^9*c.k,95606752275993+c.lower,95607129862928+c.upper)) = pointBounds14263 := by
 decide +kernel
def cuts14264 : List PrefixCut := [⟨38,275681388,275681574⟩,
⟨96,686112951,686113416⟩,
⟨128,916411679,916412300⟩]
theorem checked14264 : checkPrefixCuts (2^48) 1873543169 9 Manual.Count131072.C014264.packed 128 cuts14264 = true := by
 decide +kernel
def pointBounds14264 : List (Nat × Nat × Nat) := [(1873582080,95607946686733,95608324274486),(1873641472,95608357118296,95608734706328)]
theorem point_links_checked14264 : (cuts14264.take 2).map (fun c => (1873543169-1+2*2^9*c.k,95607671005345+c.lower,95608048592912+c.upper)) = pointBounds14264 := by
 decide +kernel
def cuts14265 : List PrefixCut := [⟨26,194391256,194391390⟩,
⟨84,614561233,614561653⟩,
⟨128,931219659,931220300⟩]
theorem checked14265 : checkPrefixCuts (2^48) 1873674241 9 Manual.Count131072.C014265.packed 128 cuts14265 = true := by
 decide +kernel
def pointBounds14265 : List (Nat × Nat × Nat) := [(1873700864,95608781808280,95609159396602),(1873760256,95609201978257,95609579566865)]
theorem point_links_checked14265 : (cuts14265.take 2).map (fun c => (1873674241-1+2*2^9*c.k,95608587417024+c.lower,95608965005212+c.upper)) = pointBounds14265 := by
 decide +kernel
def cuts14266 : List PrefixCut := [⟨14,106652701,106652773⟩,
⟨72,528448344,528448704⟩,
⟨128,923193563,923194192⟩]
theorem checked14266 : checkPrefixCuts (2^48) 1873805313 9 Manual.Count131072.C014266.packed 128 cuts14266 = true := by
 decide +kernel
def pointBounds14266 : List (Nat × Nat × Nat) := [(1873819648,95609625289384,95610002878285),(1873879040,95610047085027,95610424674216)]
theorem point_links_checked14266 : (cuts14266.take 2).map (fun c => (1873805313-1+2*2^9*c.k,95609518636683+c.lower,95609896225512+c.upper)) = pointBounds14266 := by
 decide +kernel
def cuts14267 : List PrefixCut := [⟨2,17874402,17874414⟩,
⟨60,441295496,441295796⟩,
⟨118,857343449,857344042⟩,
⟨128,930488440,930489083⟩]
theorem checked14267 : checkPrefixCuts (2^48) 1873936385 9 Manual.Count131072.C014267.packed 128 cuts14267 = true := by
 decide +kernel
def pointBounds14267 : List (Nat × Nat × Nat) := [(1873938432,95610459704648,95610837294118),(1873997824,95610883125742,95611260715500),(1874057216,95611299173695,95611676763746)]
theorem point_links_checked14267 : (cuts14267.take 3).map (fun c => (1873936385-1+2*2^9*c.k,95610441830246+c.lower,95610819419704+c.upper)) = pointBounds14267 := by
 decide +kernel
def cuts14268 : List PrefixCut := [⟨48,344842389,344842628⟩,
⟨106,768073045,768073575⟩,
⟨128,932075095,932075735⟩]
theorem checked14268 : checkPrefixCuts (2^48) 1874067457 9 Manual.Count131072.C014268.packed 128 cuts14268 = true := by
 decide +kernel
def pointBounds14268 : List (Nat × Nat × Nat) := [(1874116608,95611717161075,95612094751415),(1874176000,95612140391731,95612517982362)]
theorem point_links_checked14268 : (cuts14268.take 2).map (fun c => (1874067457-1+2*2^9*c.k,95611372318686+c.lower,95611749908787+c.upper)) = pointBounds14268 := by
 decide +kernel
def cuts14269 : List PrefixCut := [⟨36,264171303,264171486⟩,
⟨94,672357204,672357670⟩,
⟨128,918944598,918945237⟩]
theorem checked14269 : checkPrefixCuts (2^48) 1874198529 9 Manual.Count131072.C014269.packed 128 cuts14269 = true := by
 decide +kernel
def pointBounds14269 : List (Nat × Nat × Nat) := [(1874235392,95612568565084,95612946156008),(1874294784,95612976750985,95613354342192)]
theorem point_links_checked14269 : (cuts14269.take 2).map (fun c => (1874198529-1+2*2^9*c.k,95612304393781+c.lower,95612681984522+c.upper)) = pointBounds14269 := by
 decide +kernel
def cuts14270 : List PrefixCut := [⟨24,170596130,170596247⟩,
⟨82,584612931,584613333⟩,
⟨128,903713586,903714206⟩]
theorem checked14270 : checkPrefixCuts (2^48) 1874329601 9 Manual.Count131072.C014270.packed 128 cuts14270 = true := by
 decide +kernel
def pointBounds14270 : List (Nat × Nat × Nat) := [(1874354176,95613393934509,95613771526006),(1874413568,95613807951310,95614185543092)]
theorem point_links_checked14270 : (cuts14270.take 2).map (fun c => (1874329601-1+2*2^9*c.k,95613223338379+c.lower,95613600929759+c.upper)) = pointBounds14270 := by
 decide +kernel
def cuts14271 : List PrefixCut := [⟨12,84992050,84992108⟩,
⟨70,508893079,508893429⟩,
⟨128,929026835,929027470⟩]
theorem checked14271 : checkPrefixCuts (2^48) 1874460673 9 Manual.Count131072.C014271.packed 128 cuts14271 = true := by
 decide +kernel
def pointBounds14271 : List (Nat × Nat × Nat) := [(1874472960,95614212044015,95614589636073),(1874532352,95614635945044,95615013537394),(1874591744,95615056078800,95615433671435)]
theorem point_links_checked14271 : (cuts14271.take 3).map (fun c => (1874460673-1+2*2^9*c.k,95614127051965+c.lower,95614504643965+c.upper)) = pointBounds14271 := by
 decide +kernel
def cuts14272 : List PrefixCut := [⟨58,416366666,416366949⟩,
⟨116,837975208,837975780⟩,
⟨128,924006941,924007571⟩]
theorem checked14272 : checkPrefixCuts (2^48) 1874591745 9 Manual.Count131072.C014272.packed 128 cuts14272 = true := by
 decide +kernel
def pointBounds14272 : List (Nat × Nat × Nat) := [(1874651136,95615472445466,95615850038384),(1874710528,95615894054008,95616271647215)]
theorem point_links_checked14272 : (cuts14272.take 2).map (fun c => (1874591745-1+2*2^9*c.k,95615056078800+c.lower,95615433671435+c.upper)) = pointBounds14272 := by
 decide +kernel
def cuts14273 : List PrefixCut := [⟨46,327005495,327005715⟩,
⟨104,750989547,750990059⟩,
⟨128,921390071,921390700⟩]
theorem checked14273 : checkPrefixCuts (2^48) 1874722817 9 Manual.Count131072.C014273.packed 128 cuts14273 = true := by
 decide +kernel
def pointBounds14273 : List (Nat × Nat × Nat) := [(1874769920,95616307091236,95616684684721),(1874829312,95616731075288,95617108669065)]
theorem point_links_checked14273 : (cuts14273.take 2).map (fun c => (1874722817-1+2*2^9*c.k,95615980085741+c.lower,95616357679006+c.upper)) = pointBounds14273 := by
 decide +kernel
def cuts14274 : List PrefixCut := [⟨34,254020430,254020603⟩,
⟨92,666868210,666868663⟩,
⟨128,935437586,935438223⟩]
theorem checked14274 : checkPrefixCuts (2^48) 1874853889 9 Manual.Count131072.C014274.packed 128 cuts14274 = true := by
 decide +kernel
def pointBounds14274 : List (Nat × Nat × Nat) := [(1874888704,95617155496242,95617533090309),(1874948096,95617568344022,95617945938369)]
theorem point_links_checked14274 : (cuts14274.take 2).map (fun c => (1874853889-1+2*2^9*c.k,95616901475812+c.lower,95617279069706+c.upper)) = pointBounds14274 := by
 decide +kernel
def cuts14275 : List PrefixCut := [⟨22,157476123,157476232⟩,
⟨80,571798897,571799291⟩,
⟨128,914956337,914956963⟩]
theorem checked14275 : checkPrefixCuts (2^48) 1874984961 9 Manual.Count131072.C014275.packed 128 cuts14275 = true := by
 decide +kernel
def pointBounds14275 : List (Nat × Nat × Nat) := [(1875007488,95617994389521,95618371984161),(1875066880,95618408712295,95618786307220)]
theorem point_links_checked14275 : (cuts14275.take 2).map (fun c => (1874984961-1+2*2^9*c.k,95617836913398+c.lower,95618214507929+c.upper)) = pointBounds14275 := by
 decide +kernel
def cuts14276 : List PrefixCut := [⟨10,73554019,73554067⟩,
⟨68,480045023,480045357⟩,
⟨126,899431948,899432570⟩,
⟨128,911890267,911890898⟩]
theorem checked14276 : checkPrefixCuts (2^48) 1875116033 9 Manual.Count131072.C014276.packed 128 cuts14276 = true := by
 decide +kernel
def pointBounds14276 : List (Nat × Nat × Nat) := [(1875126272,95618825423754,95619203018959),(1875185664,95619231914758,95619609510249),(1875245056,95619651301683,95620028897462)]
theorem point_links_checked14276 : (cuts14276.take 3).map (fun c => (1875116033-1+2*2^9*c.k,95618751869735+c.lower,95619129464892+c.upper)) = pointBounds14276 := by
 decide +kernel
def cuts14277 : List PrefixCut := [⟨56,402562417,402562687⟩,
⟨114,819821464,819822011⟩,
⟨128,924284269,924284886⟩]
theorem checked14277 : checkPrefixCuts (2^48) 1875247105 9 Manual.Count131072.C014277.packed 128 cuts14277 = true := by
 decide +kernel
def pointBounds14277 : List (Nat × Nat × Nat) := [(1875304448,95620066322419,95620443918477),(1875363840,95620483581466,95620861177801)]
theorem point_links_checked14277 : (cuts14277.take 2).map (fun c => (1875247105-1+2*2^9*c.k,95619663760002+c.lower,95620041355790+c.upper)) = pointBounds14277 := by
 decide +kernel
def cuts14278 : List PrefixCut := [⟨44,317585891,317586109⟩,
⟨102,733767852,733768358⟩,
⟨128,918516641,918517277⟩]
theorem checked14278 : checkPrefixCuts (2^48) 1875378177 9 Manual.Count131072.C014278.packed 128 cuts14278 = true := by
 decide +kernel
def pointBounds14278 : List (Nat × Nat × Nat) := [(1875423232,95620905630162,95621283226785),(1875482624,95621321812123,95621699409034)]
theorem point_links_checked14278 : (cuts14278.take 2).map (fun c => (1875378177-1+2*2^9*c.k,95620588044271+c.lower,95620965640676+c.upper)) = pointBounds14278 := by
 decide +kernel
def cuts14279 : List PrefixCut := [⟨32,232320525,232320680⟩,
⟨90,640372275,640372715⟩,
⟨128,917251889,917252514⟩]
theorem checked14279 : checkPrefixCuts (2^48) 1875509249 9 Manual.Count131072.C014279.packed 128 cuts14279 = true := by
 decide +kernel
def pointBounds14279 : List (Nat × Nat × Nat) := [(1875542016,95621738881437,95622116478633),(1875601408,95622146933187,95622524530668)]
theorem point_links_checked14279 : (cuts14279.take 2).map (fun c => (1875509249-1+2*2^9*c.k,95621506560912+c.lower,95621884157953+c.upper)) = pointBounds14279 := by
 decide +kernel
def cuts14280 : List PrefixCut := [⟨20,138962845,138962939⟩,
⟨78,554641991,554642372⟩,
⟨128,914486470,914487095⟩]
theorem checked14280 : checkPrefixCuts (2^48) 1875640321 9 Manual.Count131072.C014280.packed 128 cuts14280 = true := by
 decide +kernel
def pointBounds14280 : List (Nat × Nat × Nat) := [(1875660800,95622562775646,95622940373406),(1875720192,95622978454792,95623356052839)]
theorem point_links_checked14280 : (cuts14280.take 2).map (fun c => (1875640321-1+2*2^9*c.k,95622423812801+c.lower,95622801410467+c.upper)) = pointBounds14280 := by
 decide +kernel
def cuts14281 : List PrefixCut := [⟨8,55221294,55221333⟩,
⟨66,469523748,469524072⟩,
⟨124,887414236,887414848⟩,
⟨128,916973668,916974300⟩]
theorem checked14281 : checkPrefixCuts (2^48) 1875771393 9 Manual.Count131072.C014281.packed 128 cuts14281 = true := by
 decide +kernel
def pointBounds14281 : List (Nat × Nat × Nat) := [(1875779584,95623393520565,95623771118895),(1875838976,95623807823019,95624185421634),(1875898368,95624225713507,95624603312410)]
theorem point_links_checked14281 : (cuts14281.take 3).map (fun c => (1875771393-1+2*2^9*c.k,95623338299271+c.lower,95623715897562+c.upper)) = pointBounds14281 := by
 decide +kernel
def cuts14282 : List PrefixCut := [⟨54,382165850,382166110⟩,
⟨112,797179042,797179581⟩,
⟨128,914058550,914059170⟩]
theorem checked14282 : checkPrefixCuts (2^48) 1875902465 9 Manual.Count131072.C014282.packed 128 cuts14282 = true := by
 decide +kernel
def pointBounds14282 : List (Nat × Nat × Nat) := [(1875957760,95624637438789,95625015037972),(1876017152,95625052451981,95625430051443)]
theorem point_links_checked14282 : (cuts14282.take 2).map (fun c => (1875902465-1+2*2^9*c.k,95624255272939+c.lower,95624632871862+c.upper)) = pointBounds14282 := by
 decide +kernel
def cuts14283 : List PrefixCut := [⟨42,311173664,311173879⟩,
⟨100,724660319,724660811⟩,
⟨128,928848280,928848911⟩]
theorem checked14283 : checkPrefixCuts (2^48) 1876033537 9 Manual.Count131072.C014283.packed 128 cuts14283 = true := by
 decide +kernel
def pointBounds14283 : List (Nat × Nat × Nat) := [(1876076544,95625480505153,95625858104911),(1876135936,95625893991808,95626271591843)]
theorem point_links_checked14283 : (cuts14283.take 2).map (fun c => (1876033537-1+2*2^9*c.k,95625169331489+c.lower,95625546931032+c.upper)) = pointBounds14283 := by
 decide +kernel
def cuts14284 : List PrefixCut := [⟨30,215286648,215286797⟩,
⟨88,632497622,632498058⟩,
⟨128,916631557,916632190⟩]
theorem checked14284 : checkPrefixCuts (2^48) 1876164609 9 Manual.Count131072.C014284.packed 128 cuts14284 = true := by
 decide +kernel
def pointBounds14284 : List (Nat × Nat × Nat) := [(1876195328,95626313466417,95626691066740),(1876254720,95626730677391,95627108278001)]
theorem point_links_checked14284 : (cuts14284.take 2).map (fun c => (1876164609-1+2*2^9*c.k,95626098179769+c.lower,95626475779943+c.upper)) = pointBounds14284 := by
 decide +kernel
def cuts14285 : List PrefixCut := [⟨18,129313400,129313488⟩,
⟨76,550248336,550248708⟩,
⟨128,927818196,927818828⟩]
theorem checked14285 : checkPrefixCuts (2^48) 1876295681 9 Manual.Count131072.C014285.packed 128 cuts14285 = true := by
 decide +kernel
def pointBounds14285 : List (Nat × Nat × Nat) := [(1876314112,95627144124726,95627521725621),(1876373504,95627565059662,95627942660841)]
theorem point_links_checked14285 : (cuts14285.take 2).map (fun c => (1876295681-1+2*2^9*c.k,95627014811326+c.lower,95627392412133+c.upper)) = pointBounds14285 := by
 decide +kernel
def cuts14286 : List PrefixCut := [⟨6,44551650,44551679⟩,
⟨64,469660019,469660335⟩,
⟨122,889054904,889055508⟩,
⟨128,932853609,932854242⟩]
theorem checked14286 : checkPrefixCuts (2^48) 1876426753 9 Manual.Count131072.C014286.packed 128 cuts14286 = true := by
 decide +kernel
def pointBounds14286 : List (Nat × Nat × Nat) := [(1876432896,95627987181172,95628364782640),(1876492288,95628412289541,95628789891296),(1876551680,95628831684426,95629209286469)]
theorem point_links_checked14286 : (cuts14286.take 3).map (fun c => (1876426753-1+2*2^9*c.k,95627942629522+c.lower,95628320230961+c.upper)) = pointBounds14286 := by
 decide +kernel
def cuts14287 : List PrefixCut := [⟨52,381282758,381283016⟩,
⟨110,794951547,794952090⟩,
⟨128,920189512,920190141⟩]
theorem checked14287 : checkPrefixCuts (2^48) 1876557825 9 Manual.Count131072.C014287.packed 128 cuts14287 = true := by
 decide +kernel
def pointBounds14287 : List (Nat × Nat × Nat) := [(1876611072,95629256765889,95629634368219),(1876670464,95629670434678,95630048037293)]
theorem point_links_checked14287 : (cuts14287.take 2).map (fun c => (1876557825-1+2*2^9*c.k,95628875483131+c.lower,95629253085203+c.upper)) = pointBounds14287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000133
