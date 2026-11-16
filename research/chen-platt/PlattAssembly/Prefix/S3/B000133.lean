import PlattAssemblyKernel
import PlattCertificates.Count131072.C024256
import PlattCertificates.Count131072.C024257
import PlattCertificates.Count131072.C024258
import PlattCertificates.Count131072.C024259
import PlattCertificates.Count131072.C024260
import PlattCertificates.Count131072.C024261
import PlattCertificates.Count131072.C024262
import PlattCertificates.Count131072.C024263
import PlattCertificates.Count131072.C024264
import PlattCertificates.Count131072.C024265
import PlattCertificates.Count131072.C024266
import PlattCertificates.Count131072.C024267
import PlattCertificates.Count131072.C024268
import PlattCertificates.Count131072.C024269
import PlattCertificates.Count131072.C024270
import PlattCertificates.Count131072.C024271
import PlattCertificates.Count131072.C024272
import PlattCertificates.Count131072.C024273
import PlattCertificates.Count131072.C024274
import PlattCertificates.Count131072.C024275
import PlattCertificates.Count131072.C024276
import PlattCertificates.Count131072.C024277
import PlattCertificates.Count131072.C024278
import PlattCertificates.Count131072.C024279
import PlattCertificates.Count131072.C024280
import PlattCertificates.Count131072.C024281
import PlattCertificates.Count131072.C024282
import PlattCertificates.Count131072.C024283
import PlattCertificates.Count131072.C024284
import PlattCertificates.Count131072.C024285
import PlattCertificates.Count131072.C024286
import PlattCertificates.Count131072.C024287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000133
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24256 : List PrefixCut := [⟨38,161197303,161197393⟩,
⟨128,527796442,527796737⟩]
theorem checked24256 : checkPrefixCuts (2^48) 3183214593 9 Manual.Count131072.C024256.packed 128 cuts24256 = true := by
 decide +kernel
def pointBounds24256 : List (Nat × Nat × Nat) := [(3183253504,102510308713681,102510690511898)]
theorem point_links_checked24256 : (cuts24256.take 1).map (fun c => (3183214593-1+2*2^9*c.k,102510147516378+c.lower,102510529314505+c.upper)) = pointBounds24256 := by
 decide +kernel
def cuts24257 : List PrefixCut := [⟨8,35103127,35103146⟩,
⟨106,438207451,438207694⟩,
⟨128,526006286,526006579⟩]
theorem checked24257 : checkPrefixCuts (2^48) 3183345665 9 Manual.Count131072.C024257.packed 128 cuts24257 = true := by
 decide +kernel
def pointBounds24257 : List (Nat × Nat × Nat) := [(3183353856,102510710415947,102511092214388),(3183454208,102511113520271,102511495318936)]
theorem point_links_checked24257 : (cuts24257.take 2).map (fun c => (3183345665-1+2*2^9*c.k,102510675312820+c.lower,102511057111242+c.upper)) = pointBounds24257 := by
 decide +kernel
def cuts24258 : List PrefixCut := [⟨76,314673871,314674062⟩,
⟨128,533323039,533323348⟩]
theorem checked24258 : checkPrefixCuts (2^48) 3183476737 9 Manual.Count131072.C024258.packed 128 cuts24258 = true := by
 decide +kernel
def pointBounds24258 : List (Nat × Nat × Nat) := [(3183554560,102511515992977,102511897791883)]
theorem point_links_checked24258 : (cuts24258.take 1).map (fun c => (3183476737-1+2*2^9*c.k,102511201319106+c.lower,102511583117821+c.upper)) = pointBounds24258 := by
 decide +kernel
def cuts24259 : List PrefixCut := [⟨46,187877952,187878060⟩,
⟨128,527289081,527289379⟩]
theorem checked24259 : checkPrefixCuts (2^48) 3183607809 9 Manual.Count131072.C024259.packed 128 cuts24259 = true := by
 decide +kernel
def pointBounds24259 : List (Nat × Nat × Nat) := [(3183654912,102511922520097,102512304319229)]
theorem point_links_checked24259 : (cuts24259.take 1).map (fun c => (3183607809-1+2*2^9*c.k,102511734642145+c.lower,102512116441169+c.upper)) = pointBounds24259 := by
 decide +kernel
def cuts24260 : List PrefixCut := [⟨16,68164071,68164108⟩,
⟨114,471748096,471748358⟩,
⟨128,528682032,528682327⟩]
theorem checked24260 : checkPrefixCuts (2^48) 3183738881 9 Manual.Count131072.C024260.packed 128 cuts24260 = true := by
 decide +kernel
def pointBounds24260 : List (Nat × Nat × Nat) := [(3183755264,102512330095297,102512711894656),(3183855616,102512733679322,102513115478906)]
theorem point_links_checked24260 : (cuts24260.take 2).map (fun c => (3183738881-1+2*2^9*c.k,102512261931226+c.lower,102512643730548+c.upper)) = pointBounds24260 := by
 decide +kernel
def cuts24261 : List PrefixCut := [⟨84,347167828,347168024⟩,
⟨128,531931189,531931486⟩]
theorem checked24261 : checkPrefixCuts (2^48) 3183869953 9 Manual.Count131072.C024261.packed 128 cuts24261 = true := by
 decide +kernel
def pointBounds24261 : List (Nat × Nat × Nat) := [(3183955968,102513137781086,102513519580899)]
theorem point_links_checked24261 : (cuts24261.take 1).map (fun c => (3183869953-1+2*2^9*c.k,102512790613258+c.lower,102513172412875+c.upper)) = pointBounds24261 := by
 decide +kernel
def cuts24262 : List PrefixCut := [⟨54,221889327,221889454⟩,
⟨128,529257175,529257471⟩]
theorem checked24262 : checkPrefixCuts (2^48) 3184001025 9 Manual.Count131072.C024262.packed 128 cuts24262 = true := by
 decide +kernel
def pointBounds24262 : List (Nat × Nat × Nat) := [(3184056320,102513544433774,102513926233815)]
theorem point_links_checked24262 : (cuts24262.take 1).map (fun c => (3184001025-1+2*2^9*c.k,102513322544447+c.lower,102513704344361+c.upper)) = pointBounds24262 := by
 decide +kernel
def cuts24263 : List PrefixCut := [⟨24,99979171,99979225⟩,
⟨122,502274695,502274973⟩,
⟨128,527909448,527909740⟩]
theorem checked24263 : checkPrefixCuts (2^48) 3184132097 9 Manual.Count131072.C024263.packed 128 cuts24263 = true := by
 decide +kernel
def pointBounds24263 : List (Nat × Nat × Nat) := [(3184156672,102513951780793,102514333581057),(3184257024,102514354076317,102514735876805)]
theorem point_links_checked24263 : (cuts24263.take 2).map (fun c => (3184132097-1+2*2^9*c.k,102513851801622+c.lower,102514233601832+c.upper)) = pointBounds24263 := by
 decide +kernel
def cuts24264 : List PrefixCut := [⟨92,382835710,382835922⟩,
⟨128,527710988,527711283⟩]
theorem checked24264 : checkPrefixCuts (2^48) 3184263169 9 Manual.Count131072.C024264.packed 128 cuts24264 = true := by
 decide +kernel
def pointBounds24264 : List (Nat × Nat × Nat) := [(3184357376,102514762546780,102515144347494)]
theorem point_links_checked24264 : (cuts24264.take 1).map (fun c => (3184263169-1+2*2^9*c.k,102514379711070+c.lower,102514761511572+c.upper)) = pointBounds24264 := by
 decide +kernel
def cuts24265 : List PrefixCut := [⟨62,256687707,256687848⟩,
⟨128,528926671,528926962⟩]
theorem checked24265 : checkPrefixCuts (2^48) 3184394241 9 Manual.Count131072.C024265.packed 128 cuts24265 = true := by
 decide +kernel
def pointBounds24265 : List (Nat × Nat × Nat) := [(3184457728,102515164109765,102515545910703)]
theorem point_links_checked24265 : (cuts24265.take 1).map (fun c => (3184394241-1+2*2^9*c.k,102514907422058+c.lower,102515289222855+c.upper)) = pointBounds24265 := by
 decide +kernel
def cuts24266 : List PrefixCut := [⟨32,134261186,134261260⟩,
⟨128,529170072,529170370⟩]
theorem checked24266 : checkPrefixCuts (2^48) 3184525313 9 Manual.Count131072.C024266.packed 128 cuts24266 = true := by
 decide +kernel
def pointBounds24266 : List (Nat × Nat × Nat) := [(3184558080,102515570609915,102515952411077)]
theorem point_links_checked24266 : (cuts24266.take 1).map (fun c => (3184525313-1+2*2^9*c.k,102515436348729+c.lower,102515818149817+c.upper)) = pointBounds24266 := by
 decide +kernel
def cuts24267 : List PrefixCut := [⟨2,8838467,8838472⟩,
⟨100,422560462,422560695⟩,
⟨128,538163409,538163707⟩]
theorem checked24267 : checkPrefixCuts (2^48) 3184656385 9 Manual.Count131072.C024267.packed 128 cuts24267 = true := by
 decide +kernel
def pointBounds24267 : List (Nat × Nat × Nat) := [(3184658432,102515974357268,102516356158659),(3184758784,102516388079263,102516769880882)]
theorem point_links_checked24267 : (cuts24267.take 2).map (fun c => (3184656385-1+2*2^9*c.k,102515965518801+c.lower,102516347320187+c.upper)) = pointBounds24267 := by
 decide +kernel
def cuts24268 : List PrefixCut := [⟨70,287853852,287854018⟩,
⟨128,530540517,530540818⟩]
theorem checked24268 : checkPrefixCuts (2^48) 3184787457 9 Manual.Count131072.C024268.packed 128 cuts24268 = true := by
 decide +kernel
def pointBounds24268 : List (Nat × Nat × Nat) := [(3184859136,102516791536062,102517173337912)]
theorem point_links_checked24268 : (cuts24268.take 1).map (fun c => (3184787457-1+2*2^9*c.k,102516503682210+c.lower,102516885483894+c.upper)) = pointBounds24268 := by
 decide +kernel
def cuts24269 : List PrefixCut := [⟨40,164557709,164557805⟩,
⟨128,528397752,528398053⟩]
theorem checked24269 : checkPrefixCuts (2^48) 3184918529 9 Manual.Count131072.C024269.packed 128 cuts24269 = true := by
 decide +kernel
def pointBounds24269 : List (Nat × Nat × Nat) := [(3184959488,102517198780436,102517580582517)]
theorem point_links_checked24269 : (cuts24269.take 1).map (fun c => (3184918529-1+2*2^9*c.k,102517034222727+c.lower,102517416024712+c.upper)) = pointBounds24269 := by
 decide +kernel
def cuts24270 : List PrefixCut := [⟨10,41712362,41712384⟩,
⟨108,447605487,447605740⟩,
⟨128,529524879,529525179⟩]
theorem checked24270 : checkPrefixCuts (2^48) 3185049601 9 Manual.Count131072.C024270.packed 128 cuts24270 = true := by
 decide +kernel
def pointBounds24270 : List (Nat × Nat × Nat) := [(3185059840,102517604332841,102517986135149),(3185160192,102518010225966,102518392028505)]
theorem point_links_checked24270 : (cuts24270.take 2).map (fun c => (3185049601-1+2*2^9*c.k,102517562620479+c.lower,102517944422765+c.upper)) = pointBounds24270 := by
 decide +kernel
def cuts24271 : List PrefixCut := [⟨78,323430738,323430923⟩,
⟨128,527559034,527559330⟩]
theorem checked24271 : checkPrefixCuts (2^48) 3185180673 9 Manual.Count131072.C024271.packed 128 cuts24271 = true := by
 decide +kernel
def pointBounds24271 : List (Nat × Nat × Nat) := [(3185260544,102518415576096,102518797378867)]
theorem point_links_checked24271 : (cuts24271.take 1).map (fun c => (3185180673-1+2*2^9*c.k,102518092145358+c.lower,102518473947944+c.upper)) = pointBounds24271 := by
 decide +kernel
def cuts24272 : List PrefixCut := [⟨48,201032292,201032404⟩,
⟨128,535401736,535402039⟩]
theorem checked24272 : checkPrefixCuts (2^48) 3185311745 9 Manual.Count131072.C024272.packed 128 cuts24272 = true := by
 decide +kernel
def pointBounds24272 : List (Nat × Nat × Nat) := [(3185360896,102518820736684,102519202539678)]
theorem point_links_checked24272 : (cuts24272.take 1).map (fun c => (3185311745-1+2*2^9*c.k,102518619704392+c.lower,102519001507274+c.upper)) = pointBounds24272 := by
 decide +kernel
def cuts24273 : List PrefixCut := [⟨18,76522033,76522076⟩,
⟨116,483424251,483424518⟩,
⟨128,534142558,534142851⟩]
theorem checked24273 : checkPrefixCuts (2^48) 3185442817 9 Manual.Count131072.C024273.packed 128 cuts24273 = true := by
 decide +kernel
def pointBounds24273 : List (Nat × Nat × Nat) := [(3185461248,102519231628161,102519613431389),(3185561600,102519638530379,102520020333831)]
theorem point_links_checked24273 : (cuts24273.take 2).map (fun c => (3185442817-1+2*2^9*c.k,102519155106128+c.lower,102519536909313+c.upper)) = pointBounds24273 := by
 decide +kernel
def cuts24274 : List PrefixCut := [⟨86,350427922,350428116⟩,
⟨128,520867034,520867327⟩]
theorem checked24274 : checkPrefixCuts (2^48) 3185573889 9 Manual.Count131072.C024274.packed 128 cuts24274 = true := by
 decide +kernel
def pointBounds24274 : List (Nat × Nat × Nat) := [(3185661952,102520039676608,102520421480280)]
theorem point_links_checked24274 : (cuts24274.take 1).map (fun c => (3185573889-1+2*2^9*c.k,102519689248686+c.lower,102520071052164+c.upper)) = pointBounds24274 := by
 decide +kernel
def cuts24275 : List PrefixCut := [⟨56,238027870,238028003⟩,
⟨128,536307609,536307909⟩]
theorem checked24275 : checkPrefixCuts (2^48) 3185704961 9 Manual.Count131072.C024275.packed 128 cuts24275 = true := by
 decide +kernel
def pointBounds24275 : List (Nat × Nat × Nat) := [(3185762304,102520448143590,102520829947494)]
theorem point_links_checked24275 : (cuts24275.take 1).map (fun c => (3185704961-1+2*2^9*c.k,102520210115720+c.lower,102520591919491+c.upper)) = pointBounds24275 := by
 decide +kernel
def cuts24276 : List PrefixCut := [⟨26,109114226,109114287⟩,
⟨124,516141910,516142197⟩,
⟨128,532574711,532575007⟩]
theorem checked24276 : checkPrefixCuts (2^48) 3185836033 9 Manual.Count131072.C024276.packed 128 cuts24276 = true := by
 decide +kernel
def pointBounds24276 : List (Nat × Nat × Nat) := [(3185862656,102520855537555,102521237341687),(3185963008,102521262565239,102521644369597)]
theorem point_links_checked24276 : (cuts24276.take 2).map (fun c => (3185836033-1+2*2^9*c.k,102520746423329+c.lower,102521128227400+c.upper)) = pointBounds24276 := by
 decide +kernel
def cuts24277 : List PrefixCut := [⟨94,388726871,388727093⟩,
⟨128,530167514,530167815⟩]
theorem checked24277 : checkPrefixCuts (2^48) 3185967105 9 Manual.Count131072.C024277.packed 128 cuts24277 = true := by
 decide +kernel
def pointBounds24277 : List (Nat × Nat × Nat) := [(3186063360,102521667724911,102522049529500)]
theorem point_links_checked24277 : (cuts24277.take 1).map (fun c => (3185967105-1+2*2^9*c.k,102521278998040+c.lower,102521660802407+c.upper)) = pointBounds24277 := by
 decide +kernel
def cuts24278 : List PrefixCut := [⟨64,261939362,261939514⟩,
⟨128,523166607,523166908⟩]
theorem checked24278 : checkPrefixCuts (2^48) 3186098177 9 Manual.Count131072.C024278.packed 128 cuts24278 = true := by
 decide +kernel
def pointBounds24278 : List (Nat × Nat × Nat) := [(3186163712,102522071104916,102522452909736)]
theorem point_links_checked24278 : (cuts24278.take 1).map (fun c => (3186098177-1+2*2^9*c.k,102521809165554+c.lower,102522190970222+c.upper)) = pointBounds24278 := by
 decide +kernel
def cuts24279 : List PrefixCut := [⟨34,143641792,143641870⟩,
⟨128,535247513,535247813⟩]
theorem checked24279 : checkPrefixCuts (2^48) 3186229249 9 Manual.Count131072.C024279.packed 128 cuts24279 = true := by
 decide +kernel
def pointBounds24279 : List (Nat × Nat × Nat) := [(3186264064,102522475973953,102522857779000)]
theorem point_links_checked24279 : (cuts24279.take 1).map (fun c => (3186229249-1+2*2^9*c.k,102522332332161+c.lower,102522714137130+c.upper)) = pointBounds24279 := by
 decide +kernel
def cuts24280 : List PrefixCut := [⟨4,16342414,16342424⟩,
⟨102,420920933,420921180⟩,
⟨128,523476904,523477209⟩]
theorem checked24280 : checkPrefixCuts (2^48) 3186360321 9 Manual.Count131072.C024280.packed 128 cuts24280 = true := by
 decide +kernel
def pointBounds24280 : List (Nat × Nat × Nat) := [(3186364416,102522883922088,102523265727367),(3186464768,102523288500607,102523670306123)]
theorem point_links_checked24280 : (cuts24280.take 2).map (fun c => (3186360321-1+2*2^9*c.k,102522867579674+c.lower,102523249384943+c.upper)) = pointBounds24280 := by
 decide +kernel
def cuts24281 : List PrefixCut := [⟨72,301038115,301038273⟩,
⟨128,527430391,527430676⟩]
theorem checked24281 : checkPrefixCuts (2^48) 3186491393 9 Manual.Count131072.C024281.packed 128 cuts24281 = true := by
 decide +kernel
def pointBounds24281 : List (Nat × Nat × Nat) := [(3186565120,102523692094693,102524073900425)]
theorem point_links_checked24281 : (cuts24281.take 1).map (fun c => (3186491393-1+2*2^9*c.k,102523391056578+c.lower,102523772862152+c.upper)) = pointBounds24281 := by
 decide +kernel
def cuts24282 : List PrefixCut := [⟨42,171447714,171447816⟩,
⟨128,522903785,522904087⟩]
theorem checked24282 : checkPrefixCuts (2^48) 3186622465 9 Manual.Count131072.C024282.packed 128 cuts24282 = true := by
 decide +kernel
def pointBounds24282 : List (Nat × Nat × Nat) := [(3186665472,102524089934683,102524471740644)]
theorem point_links_checked24282 : (cuts24282.take 1).map (fun c => (3186622465-1+2*2^9*c.k,102523918486969+c.lower,102524300292828+c.upper)) = pointBounds24282 := by
 decide +kernel
def cuts24283 : List PrefixCut := [⟨12,49904392,49904419⟩,
⟨110,452400508,452400760⟩,
⟨128,527916804,527917098⟩]
theorem checked24283 : checkPrefixCuts (2^48) 3186753537 9 Manual.Count131072.C024283.packed 128 cuts24283 = true := by
 decide +kernel
def pointBounds24283 : List (Nat × Nat × Nat) := [(3186765824,102524491295146,102524873101334),(3186866176,102524893791262,102525275597675)]
theorem point_links_checked24283 : (cuts24283.take 2).map (fun c => (3186753537-1+2*2^9*c.k,102524441390754+c.lower,102524823196915+c.upper)) = pointBounds24283 := by
 decide +kernel
def cuts24284 : List PrefixCut := [⟨80,331029955,331030142⟩,
⟨128,532929378,532929679⟩]
theorem checked24284 : checkPrefixCuts (2^48) 3186884609 9 Manual.Count131072.C024284.packed 128 cuts24284 = true := by
 decide +kernel
def pointBounds24284 : List (Nat × Nat × Nat) := [(3186966528,102525300337513,102525682144155)]
theorem point_links_checked24284 : (cuts24284.take 1).map (fun c => (3186884609-1+2*2^9*c.k,102524969307558+c.lower,102525351114013+c.upper)) = pointBounds24284 := by
 decide +kernel
def cuts24285 : List PrefixCut := [⟨50,205605609,205605724⟩,
⟨128,528844878,528845178⟩]
theorem checked24285 : checkPrefixCuts (2^48) 3187015681 9 Manual.Count131072.C024285.packed 128 cuts24285 = true := by
 decide +kernel
def pointBounds24285 : List (Nat × Nat × Nat) := [(3187066880,102525707842545,102526089649416)]
theorem point_links_checked24285 : (cuts24285.take 1).map (fun c => (3187015681-1+2*2^9*c.k,102525502236936+c.lower,102525884043692+c.upper)) = pointBounds24285 := by
 decide +kernel
def cuts24286 : List PrefixCut := [⟨20,86372420,86372467⟩,
⟨118,493233454,493233726⟩,
⟨128,533238855,533239152⟩]
theorem checked24286 : checkPrefixCuts (2^48) 3187146753 9 Manual.Count131072.C024286.packed 128 cuts24286 = true := by
 decide +kernel
def pointBounds24286 : List (Nat × Nat × Nat) := [(3187167232,102526117454234,102526499261337),(3187267584,102526524315268,102526906122596)]
theorem point_links_checked24286 : (cuts24286.take 2).map (fun c => (3187146753-1+2*2^9*c.k,102526031081814+c.lower,102526412888870+c.upper)) = pointBounds24286 := by
 decide +kernel
def cuts24287 : List PrefixCut := [⟨88,361190977,361191179⟩,
⟨128,531362297,531362593⟩]
theorem checked24287 : checkPrefixCuts (2^48) 3187277825 9 Manual.Count131072.C024287.packed 128 cuts24287 = true := by
 decide +kernel
def pointBounds24287 : List (Nat × Nat × Nat) := [(3187367936,102526925511646,102527307319201)]
theorem point_links_checked24287 : (cuts24287.take 1).map (fun c => (3187277825-1+2*2^9*c.k,102526564320669+c.lower,102526946128022+c.upper)) = pointBounds24287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000133
