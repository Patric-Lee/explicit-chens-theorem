import PlattAssemblyKernel
import PlattCertificates.Count131072.C015248
import PlattCertificates.Count131072.C015249
import PlattCertificates.Count131072.C015250
import PlattCertificates.Count131072.C015251
import PlattCertificates.Count131072.C015252
import PlattCertificates.Count131072.C015253
import PlattCertificates.Count131072.C015254
import PlattCertificates.Count131072.C015255
import PlattCertificates.Count131072.C015256
import PlattCertificates.Count131072.C015257
import PlattCertificates.Count131072.C015258
import PlattCertificates.Count131072.C015259
import PlattCertificates.Count131072.C015260
import PlattCertificates.Count131072.C015261
import PlattCertificates.Count131072.C015262
import PlattCertificates.Count131072.C015263
import PlattCertificates.Count131072.C015264
import PlattCertificates.Count131072.C015265
import PlattCertificates.Count131072.C015266
import PlattCertificates.Count131072.C015267
import PlattCertificates.Count131072.C015268
import PlattCertificates.Count131072.C015269
import PlattCertificates.Count131072.C015270
import PlattCertificates.Count131072.C015271
import PlattCertificates.Count131072.C015272
import PlattCertificates.Count131072.C015273
import PlattCertificates.Count131072.C015274
import PlattCertificates.Count131072.C015275
import PlattCertificates.Count131072.C015276
import PlattCertificates.Count131072.C015277
import PlattCertificates.Count131072.C015278
import PlattCertificates.Count131072.C015279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000164
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15248 : List PrefixCut := [⟨54,364468290,364468533⟩,
⟨116,775730419,775730933⟩,
⟨128,856547634,856548200⟩]
theorem checked15248 : checkPrefixCuts (2^48) 2002518017 9 Manual.Count131072.C015248.packed 128 cuts15248 = true := by
 decide +kernel
def pointBounds15248 : List (Nat × Nat × Nat) := [(2002573312,96484346751417,96484724928304),(2002636800,96484758013546,96485136190704)]
theorem point_links_checked15248 : (cuts15248.take 2).map (fun c => (2002518017-1+2*2^9*c.k,96483982283127+c.lower,96484360459771+c.upper)) = pointBounds15248 := by
 decide +kernel
def cuts15249 : List PrefixCut := [⟨50,337037627,337037851⟩,
⟨112,751225076,751225571⟩,
⟨128,860145624,860146189⟩]
theorem checked15249 : checkPrefixCuts (2^48) 2002649089 9 Manual.Count131072.C015249.packed 128 cuts15249 = true := by
 decide +kernel
def pointBounds15249 : List (Nat × Nat × Nat) := [(2002700288,96485175868388,96485554045822),(2002763776,96485590055837,96485968233542)]
theorem point_links_checked15249 : (cuts15249.take 2).map (fun c => (2002649089-1+2*2^9*c.k,96484838830761+c.lower,96485217007971+c.upper)) = pointBounds15249 := by
 decide +kernel
def cuts15250 : List PrefixCut := [⟨46,303988902,303989103⟩,
⟨108,725176974,725177451⟩,
⟨128,857840688,857841255⟩]
theorem checked15250 : checkPrefixCuts (2^48) 2002780161 9 Manual.Count131072.C015250.packed 128 cuts15250 = true := by
 decide +kernel
def pointBounds15250 : List (Nat × Nat × Nat) := [(2002827264,96486002965287,96486381143263),(2002890752,96486424153359,96486802331611)]
theorem point_links_checked15250 : (cuts15250.take 2).map (fun c => (2002780161-1+2*2^9*c.k,96485698976385+c.lower,96486077154160+c.upper)) = pointBounds15250 := by
 decide +kernel
def cuts15251 : List PrefixCut := [⟨42,281343779,281343968⟩,
⟨104,697727162,697727625⟩,
⟨128,857925147,857925714⟩]
theorem checked15251 : checkPrefixCuts (2^48) 2002911233 9 Manual.Count131072.C015251.packed 128 cuts15251 = true := by
 decide +kernel
def pointBounds15251 : List (Nat × Nat × Nat) := [(2002954240,96486838160852,96487216339383),(2003017728,96487254544235,96487632723040)]
theorem point_links_checked15251 : (cuts15251.take 2).map (fun c => (2002911233-1+2*2^9*c.k,96486556817073+c.lower,96486934995415+c.upper)) = pointBounds15251 := by
 decide +kernel
def cuts15252 : List PrefixCut := [⟨38,251394401,251394570⟩,
⟨100,672669552,672669998⟩,
⟨128,865316288,865316864⟩]
theorem checked15252 : checkPrefixCuts (2^48) 2003042305 9 Manual.Count131072.C015252.packed 128 cuts15252 = true := by
 decide +kernel
def pointBounds15252 : List (Nat × Nat × Nat) := [(2003081216,96487666136621,96488044315699),(2003144704,96488087411772,96488465591127)]
theorem point_links_checked15252 : (cuts15252.take 2).map (fun c => (2003042305-1+2*2^9*c.k,96487414742220+c.lower,96487792921129+c.upper)) = pointBounds15252 := by
 decide +kernel
def cuts15253 : List PrefixCut := [⟨34,227490977,227491126⟩,
⟨96,636936634,636937055⟩,
⟨128,853457072,853457643⟩]
theorem checked15253 : checkPrefixCuts (2^48) 2003173377 9 Manual.Count131072.C015253.packed 128 cuts15253 = true := by
 decide +kernel
def pointBounds15253 : List (Nat × Nat × Nat) := [(2003208192,96488507549485,96488885729119),(2003271680,96488916995142,96489295175048)]
theorem point_links_checked15253 : (cuts15253.take 2).map (fun c => (2003173377-1+2*2^9*c.k,96488280058508+c.lower,96488658237993+c.upper)) = pointBounds15253 := by
 decide +kernel
def cuts15254 : List PrefixCut := [⟨30,203169090,203169220⟩,
⟨92,616241861,616242262⟩,
⟨128,857616370,857616928⟩]
theorem checked15254 : checkPrefixCuts (2^48) 2003304449 9 Manual.Count131072.C015254.packed 128 cuts15254 = true := by
 decide +kernel
def pointBounds15254 : List (Nat × Nat × Nat) := [(2003335168,96489336684670,96489714864856),(2003398656,96489749757441,96490127937898)]
theorem point_links_checked15254 : (cuts15254.take 2).map (fun c => (2003304449-1+2*2^9*c.k,96489133515580+c.lower,96489511695636+c.upper)) = pointBounds15254 := by
 decide +kernel
def cuts15255 : List PrefixCut := [⟨26,180395772,180395888⟩,
⟨88,599061969,599062362⟩,
⟨128,870485454,870486027⟩]
theorem checked15255 : checkPrefixCuts (2^48) 2003435521 9 Manual.Count131072.C015255.packed 128 cuts15255 = true := by
 decide +kernel
def pointBounds15255 : List (Nat × Nat × Nat) := [(2003462144,96490171527722,96490549708452),(2003525632,96490590193919,96490968374926)]
theorem point_links_checked15255 : (cuts15255.take 2).map (fun c => (2003435521-1+2*2^9*c.k,96489991131950+c.lower,96490369312564+c.upper)) = pointBounds15255 := by
 decide +kernel
def cuts15256 : List PrefixCut := [⟨22,151163073,151163174⟩,
⟨84,579636556,579636940⟩,
⟨128,872395408,872395990⟩]
theorem checked15256 : checkPrefixCuts (2^48) 2003566593 9 Manual.Count131072.C015256.packed 128 cuts15256 = true := by
 decide +kernel
def pointBounds15256 : List (Nat × Nat × Nat) := [(2003589120,96491012780477,96491390961765),(2003652608,96491441253960,96491819435531)]
theorem point_links_checked15256 : (cuts15256.take 2).map (fun c => (2003566593-1+2*2^9*c.k,96490861617404+c.lower,96491239798591+c.upper)) = pointBounds15256 := by
 decide +kernel
def cuts15257 : List PrefixCut := [⟨18,123619838,123619917⟩,
⟨80,537175825,537176180⟩,
⟨128,865595247,865595816⟩]
theorem checked15257 : checkPrefixCuts (2^48) 2003697665 9 Manual.Count131072.C015257.packed 128 cuts15257 = true := by
 decide +kernel
def pointBounds15257 : List (Nat × Nat × Nat) := [(2003716096,96491857632650,96492235814498),(2003779584,96492271188637,96492649370761)]
theorem point_links_checked15257 : (cuts15257.take 2).map (fun c => (2003697665-1+2*2^9*c.k,96491734012812+c.lower,96492112194581+c.upper)) = pointBounds15257 := by
 decide +kernel
def cuts15258 : List PrefixCut := [⟨14,93551703,93551766⟩,
⟨76,517335532,517335872⟩,
⟨128,858656305,858656870⟩]
theorem checked15258 : checkPrefixCuts (2^48) 2003828737 9 Manual.Count131072.C015258.packed 128 cuts15258 = true := by
 decide +kernel
def pointBounds15258 : List (Nat × Nat × Nat) := [(2003843072,96492693159762,96493071342163),(2003906560,96493116943591,96493495126269)]
theorem point_links_checked15258 : (cuts15258.take 2).map (fun c => (2003828737-1+2*2^9*c.k,96492599608059+c.lower,96492977790397+c.upper)) = pointBounds15258 := by
 decide +kernel
def cuts15259 : List PrefixCut := [⟨10,68824908,68824953⟩,
⟨72,483733103,483733417⟩,
⟨128,861970751,861971313⟩]
theorem checked15259 : checkPrefixCuts (2^48) 2003959809 9 Manual.Count131072.C015259.packed 128 cuts15259 = true := by
 decide +kernel
def pointBounds15259 : List (Nat × Nat × Nat) := [(2003970048,96493527089272,96493905272220),(2004033536,96493941997467,96494320180684)]
theorem point_links_checked15259 : (cuts15259.take 2).map (fun c => (2003959809-1+2*2^9*c.k,96493458264364+c.lower,96493836447267+c.upper)) = pointBounds15259 := by
 decide +kernel
def cuts15260 : List PrefixCut := [⟨6,40168685,40168712⟩,
⟨68,458280936,458281237⟩,
⟨128,861633527,861634089⟩]
theorem checked15260 : checkPrefixCuts (2^48) 2004090881 9 Manual.Count131072.C015260.packed 128 cuts15260 = true := by
 decide +kernel
def pointBounds15260 : List (Nat × Nat × Nat) := [(2004097024,96494360403800,96494738587292),(2004160512,96494778516051,96495156699817)]
theorem point_links_checked15260 : (cuts15260.take 2).map (fun c => (2004090881-1+2*2^9*c.k,96494320235115+c.lower,96494698418580+c.upper)) = pointBounds15260 := by
 decide +kernel
def cuts15261 : List PrefixCut := [⟨2,12358799,12358807⟩,
⟨64,426652657,426652937⟩,
⟨126,835596932,835597484⟩,
⟨128,850061413,850061975⟩]
theorem checked15261 : checkPrefixCuts (2^48) 2004221953 9 Manual.Count131072.C015261.packed 128 cuts15261 = true := by
 decide +kernel
def pointBounds15261 : List (Nat × Nat × Nat) := [(2004224000,96495194227441,96495572411476),(2004287488,96495608521299,96495986705606),(2004350976,96496017465574,96496395650153)]
theorem point_links_checked15261 : (cuts15261.take 3).map (fun c => (2004221953-1+2*2^9*c.k,96495181868642+c.lower,96495560052669+c.upper)) = pointBounds15261 := by
 decide +kernel
def cuts15262 : List PrefixCut := [⟨60,404296914,404297185⟩,
⟨122,828240756,828241311⟩,
⟨128,867278300,867278880⟩]
theorem checked15262 : checkPrefixCuts (2^48) 2004353025 9 Manual.Count131072.C015262.packed 128 cuts15262 = true := by
 decide +kernel
def pointBounds15262 : List (Nat × Nat × Nat) := [(2004414464,96496436226969,96496814411829),(2004477952,96496860170811,96497238355955)]
theorem point_links_checked15262 : (cuts15262.take 2).map (fun c => (2004353025-1+2*2^9*c.k,96496031930055+c.lower,96496410114644+c.upper)) = pointBounds15262 := by
 decide +kernel
def cuts15263 : List PrefixCut := [⟨56,382224869,382225121⟩,
⟨118,793364006,793364527⟩,
⟨128,860903035,860903600⟩]
theorem checked15263 : checkPrefixCuts (2^48) 2004484097 9 Manual.Count131072.C015263.packed 128 cuts15263 = true := by
 decide +kernel
def pointBounds15263 : List (Nat × Nat × Nat) := [(2004541440,96497281433224,96497659618645),(2004604928,96497692572361,96498070758051)]
theorem point_links_checked15263 : (cuts15263.take 2).map (fun c => (2004484097-1+2*2^9*c.k,96496899208355+c.lower,96497277393524+c.upper)) = pointBounds15263 := by
 decide +kernel
def cuts15264 : List PrefixCut := [⟨52,351028873,351029107⟩,
⟨114,755823586,755824086⟩,
⟨128,848069501,848070060⟩]
theorem checked15264 : checkPrefixCuts (2^48) 2004615169 9 Manual.Count131072.C015264.packed 128 cuts15264 = true := by
 decide +kernel
def pointBounds15264 : List (Nat × Nat × Nat) := [(2004668416,96498111140263,96498489326231),(2004731904,96498515934976,96498894121210)]
theorem point_links_checked15264 : (cuts15264.take 2).map (fun c => (2004615169-1+2*2^9*c.k,96497760111390+c.lower,96498138297124+c.upper)) = pointBounds15264 := by
 decide +kernel
def cuts15265 : List PrefixCut := [⟨48,319275390,319275600⟩,
⟨110,732047221,732047702⟩,
⟨128,851804751,851805312⟩]
theorem checked15265 : checkPrefixCuts (2^48) 2004746241 9 Manual.Count131072.C015265.packed 128 cuts15265 = true := by
 decide +kernel
def pointBounds15265 : List (Nat × Nat × Nat) := [(2004795392,96498927456281,96499305642784),(2004858880,96499340228112,96499718414886)]
theorem point_links_checked15265 : (cuts15265.take 2).map (fun c => (2004746241-1+2*2^9*c.k,96498608180891+c.lower,96498986367184+c.upper)) = pointBounds15265 := by
 decide +kernel
def cuts15266 : List PrefixCut := [⟨44,303671163,303671361⟩,
⟨106,721751711,721752179⟩,
⟨128,868034612,868035180⟩]
theorem checked15266 : checkPrefixCuts (2^48) 2004877313 9 Manual.Count131072.C015266.packed 128 cuts15266 = true := by
 decide +kernel
def pointBounds15266 : List (Nat × Nat × Nat) := [(2004922368,96499763656805,96500141843857),(2004985856,96500181737353,96500559924675)]
theorem point_links_checked15266 : (cuts15266.take 2).map (fun c => (2004877313-1+2*2^9*c.k,96499459985642+c.lower,96499838172496+c.upper)) = pointBounds15266 := by
 decide +kernel
def cuts15267 : List PrefixCut := [⟨40,268555459,268555638⟩,
⟨102,677625123,677625577⟩,
⟨128,849728117,849728686⟩]
theorem checked15267 : checkPrefixCuts (2^48) 2005008385 9 Manual.Count131072.C015267.packed 128 cuts15267 = true := by
 decide +kernel
def pointBounds15267 : List (Nat × Nat × Nat) := [(2005049344,96500596575713,96500974763314),(2005112832,96501005645377,96501383833253)]
theorem point_links_checked15267 : (cuts15267.take 2).map (fun c => (2005008385-1+2*2^9*c.k,96500328020254+c.lower,96500706207676+c.upper)) = pointBounds15267 := by
 decide +kernel
def cuts15268 : List PrefixCut := [⟨36,244112876,244113033⟩,
⟨98,664386410,664386843⟩,
⟨128,876904467,876905034⟩]
theorem checked15268 : checkPrefixCuts (2^48) 2005139457 9 Manual.Count131072.C015268.packed 128 cuts15268 = true := by
 decide +kernel
def pointBounds15268 : List (Nat × Nat × Nat) := [(2005176320,96501421861247,96501800049395),(2005239808,96501842134781,96502220323205)]
theorem point_links_checked15268 : (cuts15268.take 2).map (fun c => (2005139457-1+2*2^9*c.k,96501177748371+c.lower,96501555936362+c.upper)) = pointBounds15268 := by
 decide +kernel
def cuts15269 : List PrefixCut := [⟨32,215602763,215602905⟩,
⟨94,621532696,621533110⟩,
⟨128,861828300,861828869⟩]
theorem checked15269 : checkPrefixCuts (2^48) 2005270529 9 Manual.Count131072.C015269.packed 128 cuts15269 = true := by
 decide +kernel
def pointBounds15269 : List (Nat × Nat × Nat) := [(2005303296,96502270255601,96502648444301),(2005366784,96502676185534,96503054374506)]
theorem point_links_checked15269 : (cuts15269.take 2).map (fun c => (2005270529-1+2*2^9*c.k,96502054652838+c.lower,96502432841396+c.upper)) = pointBounds15269 := by
 decide +kernel
def cuts15270 : List PrefixCut := [⟨28,189342081,189342203⟩,
⟨90,601702558,601702951⟩,
⟨128,859807248,859807808⟩]
theorem checked15270 : checkPrefixCuts (2^48) 2005401601 9 Manual.Count131072.C015270.packed 128 cuts15270 = true := by
 decide +kernel
def pointBounds15270 : List (Nat × Nat × Nat) := [(2005430272,96503105823219,96503484012468),(2005493760,96503518183696,96503896373216)]
theorem point_links_checked15270 : (cuts15270.take 2).map (fun c => (2005401601-1+2*2^9*c.k,96502916481138+c.lower,96503294670265+c.upper)) = pointBounds15270 := by
 decide +kernel
def cuts15271 : List PrefixCut := [⟨24,163365420,163365529⟩,
⟨86,585102960,585103344⟩,
⟨128,866908768,866909341⟩]
theorem checked15271 : checkPrefixCuts (2^48) 2005532673 9 Manual.Count131072.C015271.packed 128 cuts15271 = true := by
 decide +kernel
def pointBounds15271 : List (Nat × Nat × Nat) := [(2005557248,96503939653806,96504317843602),(2005620736,96504361391346,96504739581417)]
theorem point_links_checked15271 : (cuts15271.take 2).map (fun c => (2005532673-1+2*2^9*c.k,96503776288386+c.lower,96504154478073+c.upper)) = pointBounds15271 := by
 decide +kernel
def cuts15272 : List PrefixCut := [⟨20,135146739,135146829⟩,
⟨82,551384402,551384766⟩,
⟨128,856186520,856187087⟩]
theorem checked15272 : checkPrefixCuts (2^48) 2005663745 9 Manual.Count131072.C015272.packed 128 cuts15272 = true := by
 decide +kernel
def pointBounds15272 : List (Nat × Nat × Nat) := [(2005684224,96504778343893,96505156534243),(2005747712,96505194581556,96505572772180)]
theorem point_links_checked15272 : (cuts15272.take 2).map (fun c => (2005663745-1+2*2^9*c.k,96504643197154+c.lower,96505021387414+c.upper)) = pointBounds15272 := by
 decide +kernel
def cuts15273 : List PrefixCut := [⟨16,104826708,104826781⟩,
⟨78,518792778,518793131⟩,
⟨128,856972407,856972986⟩]
theorem checked15273 : checkPrefixCuts (2^48) 2005794817 9 Manual.Count131072.C015273.packed 128 cuts15273 = true := by
 decide +kernel
def pointBounds15273 : List (Nat × Nat × Nat) := [(2005811200,96505604210382,96505982401282),(2005874688,96506018176452,96506396367632)]
theorem point_links_checked15273 : (cuts15273.take 2).map (fun c => (2005794817-1+2*2^9*c.k,96505499383674+c.lower,96505877574501+c.upper)) = pointBounds15273 := by
 decide +kernel
def cuts15274 : List PrefixCut := [⟨12,82649212,82649265⟩,
⟨74,501219591,501219921⟩,
⟨128,862809906,862810477⟩]
theorem checked15274 : checkPrefixCuts (2^48) 2005925889 9 Manual.Count131072.C015274.packed 128 cuts15274 = true := by
 decide +kernel
def pointBounds15274 : List (Nat × Nat × Nat) := [(2005938176,96506439005293,96506817196752),(2006001664,96506857575672,96507235767408)]
theorem point_links_checked15274 : (cuts15274.take 2).map (fun c => (2005925889-1+2*2^9*c.k,96506356356081+c.lower,96506734547487+c.upper)) = pointBounds15274 := by
 decide +kernel
def cuts15275 : List PrefixCut := [⟨8,53599263,53599299⟩,
⟨70,472564056,472564369⟩,
⟨128,858684585,858685154⟩]
theorem checked15275 : checkPrefixCuts (2^48) 2006056961 9 Manual.Count131072.C015275.packed 128 cuts15275 = true := by
 decide +kernel
def pointBounds15275 : List (Nat × Nat × Nat) := [(2006065152,96507272765250,96507650957263),(2006128640,96507691730043,96508069922333)]
theorem point_links_checked15275 : (cuts15275.take 2).map (fun c => (2006056961-1+2*2^9*c.k,96507219165987+c.lower,96507597357964+c.upper)) = pointBounds15275 := by
 decide +kernel
def cuts15276 : List PrefixCut := [⟨4,27639731,27639748⟩,
⟨66,438580888,438581178⟩,
⟨128,867887837,867888408⟩]
theorem checked15276 : checkPrefixCuts (2^48) 2006188033 9 Manual.Count131072.C015276.packed 128 cuts15276 = true := by
 decide +kernel
def pointBounds15276 : List (Nat × Nat × Nat) := [(2006192128,96508105490303,96508483682866),(2006255616,96508516431460,96508894624296),(2006319104,96508945738409,96509323931526)]
theorem point_links_checked15276 : (cuts15276.take 3).map (fun c => (2006188033-1+2*2^9*c.k,96508077850572+c.lower,96508456043118+c.upper)) = pointBounds15276 := by
 decide +kernel
def cuts15277 : List PrefixCut := [⟨62,411616629,411616896⟩,
⟨124,834162606,834163151⟩,
⟨128,860957071,860957634⟩]
theorem checked15277 : checkPrefixCuts (2^48) 2006319105 9 Manual.Count131072.C015277.packed 128 cuts15277 = true := by
 decide +kernel
def pointBounds15277 : List (Nat × Nat × Nat) := [(2006382592,96509357355038,96509735548422),(2006446080,96509779901015,96510158094677)]
theorem point_links_checked15277 : (cuts15277.take 2).map (fun c => (2006319105-1+2*2^9*c.k,96508945738409+c.lower,96509323931526+c.upper)) = pointBounds15277 := by
 decide +kernel
def cuts15278 : List PrefixCut := [⟨58,389144848,389145105⟩,
⟨120,806193267,806193793⟩,
⟨128,861041231,861041794⟩]
theorem checked15278 : checkPrefixCuts (2^48) 2006450177 9 Manual.Count131072.C015278.packed 128 cuts15278 = true := by
 decide +kernel
def pointBounds15278 : List (Nat × Nat × Nat) := [(2006509568,96510195840328,96510574034265),(2006573056,96510612888747,96510991082953)]
theorem point_links_checked15278 : (cuts15278.take 2).map (fun c => (2006450177-1+2*2^9*c.k,96509806695480+c.lower,96510184889160+c.upper)) = pointBounds15278 := by
 decide +kernel
def cuts15279 : List PrefixCut := [⟨54,361345645,361345886⟩,
⟨116,771634730,771635243⟩,
⟨128,852288327,852288892⟩]
theorem checked15279 : checkPrefixCuts (2^48) 2006581249 9 Manual.Count131072.C015279.packed 128 cuts15279 = true := by
 decide +kernel
def pointBounds15279 : List (Nat × Nat × Nat) := [(2006636544,96511029082356,96511407276840),(2006700032,96511439371441,96511817566197)]
theorem point_links_checked15279 : (cuts15279.take 2).map (fun c => (2006581249-1+2*2^9*c.k,96510667736711+c.lower,96511045930954+c.upper)) = pointBounds15279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000164
