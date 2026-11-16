import PlattAssemblyKernel
import PlattCertificates.Count131072.C050256
import PlattCertificates.Count131072.C050257
import PlattCertificates.Count131072.C050258
import PlattCertificates.Count131072.C050259
import PlattCertificates.Count131072.C050260
import PlattCertificates.Count131072.C050261
import PlattCertificates.Count131072.C050262
import PlattCertificates.Count131072.C050263
import PlattCertificates.Count131072.C050264
import PlattCertificates.Count131072.C050265
import PlattCertificates.Count131072.C050266
import PlattCertificates.Count131072.C050267
import PlattCertificates.Count131072.C050268
import PlattCertificates.Count131072.C050269
import PlattCertificates.Count131072.C050270
import PlattCertificates.Count131072.C050271
import PlattCertificates.Count131072.C050272
import PlattCertificates.Count131072.C050273
import PlattCertificates.Count131072.C050274
import PlattCertificates.Count131072.C050275
import PlattCertificates.Count131072.C050276
import PlattCertificates.Count131072.C050277
import PlattCertificates.Count131072.C050278
import PlattCertificates.Count131072.C050279
import PlattCertificates.Count131072.C050280
import PlattCertificates.Count131072.C050281
import PlattCertificates.Count131072.C050282
import PlattCertificates.Count131072.C050283
import PlattCertificates.Count131072.C050284
import PlattCertificates.Count131072.C050285
import PlattCertificates.Count131072.C050286
import PlattCertificates.Count131072.C050287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50256 : List PrefixCut := [⟨64,248884513,248884654⟩]
theorem checked50256 : checkPrefixCuts (2^48) 6591086593 10 Manual.Count131072.C050256.packed 64 cuts50256 = true := by
 decide +kernel
def cuts50257 : List PrefixCut := [⟨27,105138128,105138188⟩,
⟨64,246274622,246274764⟩]
theorem checked50257 : checkPrefixCuts (2^48) 6591217665 10 Manual.Count131072.C050257.packed 64 cuts50257 = true := by
 decide +kernel
def pointBounds50257 : List (Nat × Nat × Nat) := [(6591272960,111720757703365,111721144861796)]
theorem point_links_checked50257 : (cuts50257.take 1).map (fun c => (6591217665-1+2*2^10*c.k,111720652565237+c.lower,111721039723608+c.upper)) = pointBounds50257 := by
 decide +kernel
def cuts50258 : List PrefixCut := [⟨64,250283817,250283957⟩]
theorem checked50258 : checkPrefixCuts (2^48) 6591348737 10 Manual.Count131072.C050258.packed 64 cuts50258 = true := by
 decide +kernel
def pointBounds50258 : List (Nat × Nat × Nat) := [(6591479808,111721149123676,111721536282329)]
theorem point_links_checked50258 : (cuts50258.take 1).map (fun c => (6591348737-1+2*2^10*c.k,111720898839859+c.lower,111721285998372+c.upper)) = pointBounds50258 := by
 decide +kernel
def cuts50259 : List PrefixCut := [⟨64,248186424,248186565⟩]
theorem checked50259 : checkPrefixCuts (2^48) 6591479809 10 Manual.Count131072.C050259.packed 64 cuts50259 = true := by
 decide +kernel
def cuts50260 : List PrefixCut := [⟨37,141513567,141513650⟩,
⟨64,245021569,245021710⟩]
theorem checked50260 : checkPrefixCuts (2^48) 6591610881 10 Manual.Count131072.C050260.packed 64 cuts50260 = true := by
 decide +kernel
def pointBounds50260 : List (Nat × Nat × Nat) := [(6591686656,111721538823667,111721925982544)]
theorem point_links_checked50260 : (cuts50260.take 1).map (fun c => (6591610881-1+2*2^10*c.k,111721397310100+c.lower,111721784468894+c.upper)) = pointBounds50260 := by
 decide +kernel
def cuts50261 : List PrefixCut := [⟨64,246852852,246852994⟩]
theorem checked50261 : checkPrefixCuts (2^48) 6591741953 10 Manual.Count131072.C050261.packed 64 cuts50261 = true := by
 decide +kernel
def cuts50262 : List PrefixCut := [⟨10,38985305,38985327⟩,
⟨64,249836934,249837070⟩]
theorem checked50262 : checkPrefixCuts (2^48) 6591873025 10 Manual.Count131072.C050262.packed 64 cuts50262 = true := by
 decide +kernel
def pointBounds50262 : List (Nat × Nat × Nat) := [(6591893504,111721928169826,111722315328925)]
theorem point_links_checked50262 : (cuts50262.take 1).map (fun c => (6591873025-1+2*2^10*c.k,111721889184521+c.lower,111722276343598+c.upper)) = pointBounds50262 := by
 decide +kernel
def cuts50263 : List PrefixCut := [⟨47,180275724,180275826⟩,
⟨64,248465560,248465700⟩]
theorem checked50263 : checkPrefixCuts (2^48) 6592004097 10 Manual.Count131072.C050263.packed 64 cuts50263 = true := by
 decide +kernel
def pointBounds50263 : List (Nat × Nat × Nat) := [(6592100352,111722319297179,111722706456494)]
theorem point_links_checked50263 : (cuts50263.take 1).map (fun c => (6592004097-1+2*2^10*c.k,111722139021455+c.lower,111722526180668+c.upper)) = pointBounds50263 := by
 decide +kernel
def cuts50264 : List PrefixCut := [⟨64,246795422,246795559⟩]
theorem checked50264 : checkPrefixCuts (2^48) 6592135169 10 Manual.Count131072.C050264.packed 64 cuts50264 = true := by
 decide +kernel
def cuts50265 : List PrefixCut := [⟨20,76684911,76684953⟩,
⟨64,246448920,246449066⟩]
theorem checked50265 : checkPrefixCuts (2^48) 6592266241 10 Manual.Count131072.C050265.packed 64 cuts50265 = true := by
 decide +kernel
def pointBounds50265 : List (Nat × Nat × Nat) := [(6592307200,111722710967348,111723098126880)]
theorem point_links_checked50265 : (cuts50265.take 1).map (fun c => (6592266241-1+2*2^10*c.k,111722634282437+c.lower,111723021441927+c.upper)) = pointBounds50265 := by
 decide +kernel
def cuts50266 : List PrefixCut := [⟨57,222918518,222918645⟩,
⟨64,248621565,248621708⟩]
theorem checked50266 : checkPrefixCuts (2^48) 6592397313 10 Manual.Count131072.C050266.packed 64 cuts50266 = true := by
 decide +kernel
def pointBounds50266 : List (Nat × Nat × Nat) := [(6592514048,111723103649875,111723490809638)]
theorem point_links_checked50266 : (cuts50266.take 1).map (fun c => (6592397313-1+2*2^10*c.k,111722880731357+c.lower,111723267890993+c.upper)) = pointBounds50266 := by
 decide +kernel
def cuts50267 : List PrefixCut := [⟨64,249086265,249086407⟩]
theorem checked50267 : checkPrefixCuts (2^48) 6592528385 10 Manual.Count131072.C050267.packed 64 cuts50267 = true := by
 decide +kernel
def cuts50268 : List PrefixCut := [⟨30,115361885,115361949⟩,
⟨64,245964580,245964717⟩]
theorem checked50268 : checkPrefixCuts (2^48) 6592659457 10 Manual.Count131072.C050268.packed 64 cuts50268 = true := by
 decide +kernel
def pointBounds50268 : List (Nat × Nat × Nat) := [(6592720896,111723493801072,111723880961057)]
theorem point_links_checked50268 : (cuts50268.take 1).map (fun c => (6592659457-1+2*2^10*c.k,111723378439187+c.lower,111723765599108+c.upper)) = pointBounds50268 := by
 decide +kernel
def cuts50269 : List PrefixCut := [⟨64,244508103,244508242⟩]
theorem checked50269 : checkPrefixCuts (2^48) 6592790529 10 Manual.Count131072.C050269.packed 64 cuts50269 = true := by
 decide +kernel
def cuts50270 : List PrefixCut := [⟨3,11441852,11441859⟩,
⟨64,245399798,245399936⟩]
theorem checked50270 : checkPrefixCuts (2^48) 6592921601 10 Manual.Count131072.C050270.packed 64 cuts50270 = true := by
 decide +kernel
def pointBounds50270 : List (Nat × Nat × Nat) := [(6592927744,111723880353722,111724267513926)]
theorem point_links_checked50270 : (cuts50270.take 1).map (fun c => (6592921601-1+2*2^10*c.k,111723868911870+c.lower,111724256072067+c.upper)) = pointBounds50270 := by
 decide +kernel
def cuts50271 : List PrefixCut := [⟨40,155144129,155144219⟩,
⟨64,248767606,248767747⟩]
theorem checked50271 : checkPrefixCuts (2^48) 6593052673 10 Manual.Count131072.C050271.packed 64 cuts50271 = true := by
 decide +kernel
def pointBounds50271 : List (Nat × Nat × Nat) := [(6593134592,111724269455797,111724656616222)]
theorem point_links_checked50271 : (cuts50271.take 1).map (fun c => (6593052673-1+2*2^10*c.k,111724114311668+c.lower,111724501472003+c.upper)) = pointBounds50271 := by
 decide +kernel
def cuts50272 : List PrefixCut := [⟨64,251751048,251751194⟩]
theorem checked50272 : checkPrefixCuts (2^48) 6593183745 10 Manual.Count131072.C050272.packed 64 cuts50272 = true := by
 decide +kernel
def cuts50273 : List PrefixCut := [⟨13,49734860,49734886⟩,
⟨64,247861202,247861343⟩]
theorem checked50273 : checkPrefixCuts (2^48) 6593314817 10 Manual.Count131072.C050273.packed 64 cuts50273 = true := by
 decide +kernel
def pointBounds50273 : List (Nat × Nat × Nat) := [(6593341440,111724664565182,111725051725830)]
theorem point_links_checked50273 : (cuts50273.take 1).map (fun c => (6593314817-1+2*2^10*c.k,111724614830322+c.lower,111725001990944+c.upper)) = pointBounds50273 := by
 decide +kernel
def cuts50274 : List PrefixCut := [⟨50,193555431,193555541⟩,
⟨64,248582004,248582145⟩]
theorem checked50274 : checkPrefixCuts (2^48) 6593445889 10 Manual.Count131072.C050274.packed 64 cuts50274 = true := by
 decide +kernel
def pointBounds50274 : List (Nat × Nat × Nat) := [(6593548288,111725056246955,111725443407828)]
theorem point_links_checked50274 : (cuts50274.take 1).map (fun c => (6593445889-1+2*2^10*c.k,111724862691524+c.lower,111725249852287+c.upper)) = pointBounds50274 := by
 decide +kernel
def cuts50275 : List PrefixCut := [⟨64,243966676,243966812⟩]
theorem checked50275 : checkPrefixCuts (2^48) 6593576961 10 Manual.Count131072.C050275.packed 64 cuts50275 = true := by
 decide +kernel
def cuts50276 : List PrefixCut := [⟨23,90840603,90840654⟩,
⟨64,248059880,248060022⟩]
theorem checked50276 : checkPrefixCuts (2^48) 6593708033 10 Manual.Count131072.C050276.packed 64 cuts50276 = true := by
 decide +kernel
def pointBounds50276 : List (Nat × Nat × Nat) := [(6593755136,111725446080807,111725833241898)]
theorem point_links_checked50276 : (cuts50276.take 1).map (fun c => (6593708033-1+2*2^10*c.k,111725355240204+c.lower,111725742401244+c.upper)) = pointBounds50276 := by
 decide +kernel
def cuts50277 : List PrefixCut := [⟨60,230382621,230382752⟩,
⟨64,245066858,245066997⟩]
theorem checked50277 : checkPrefixCuts (2^48) 6593839105 10 Manual.Count131072.C050277.packed 64 cuts50277 = true := by
 decide +kernel
def pointBounds50277 : List (Nat × Nat × Nat) := [(6593961984,111725833682705,111726220844018)]
theorem point_links_checked50277 : (cuts50277.take 1).map (fun c => (6593839105-1+2*2^10*c.k,111725603300084+c.lower,111725990461266+c.upper)) = pointBounds50277 := by
 decide +kernel
def cuts50278 : List PrefixCut := [⟨64,249159843,249159987⟩]
theorem checked50278 : checkPrefixCuts (2^48) 6593970177 10 Manual.Count131072.C050278.packed 64 cuts50278 = true := by
 decide +kernel
def cuts50279 : List PrefixCut := [⟨33,128355733,128355805⟩,
⟨64,249709814,249709955⟩]
theorem checked50279 : checkPrefixCuts (2^48) 6594101249 10 Manual.Count131072.C050279.packed 64 cuts50279 = true := by
 decide +kernel
def pointBounds50279 : List (Nat × Nat × Nat) := [(6594168832,111726225882518,111726613044055)]
theorem point_links_checked50279 : (cuts50279.take 1).map (fun c => (6594101249-1+2*2^10*c.k,111726097526785+c.lower,111726484688250+c.upper)) = pointBounds50279 := by
 decide +kernel
def cuts50280 : List PrefixCut := [⟨64,248168209,248168348⟩]
theorem checked50280 : checkPrefixCuts (2^48) 6594232321 10 Manual.Count131072.C050280.packed 64 cuts50280 = true := by
 decide +kernel
def cuts50281 : List PrefixCut := [⟨6,23305532,23305545⟩,
⟨64,248675471,248675611⟩]
theorem checked50281 : checkPrefixCuts (2^48) 6594363393 10 Manual.Count131072.C050281.packed 64 cuts50281 = true := by
 decide +kernel
def pointBounds50281 : List (Nat × Nat × Nat) := [(6594375680,111726618710340,111727005872098)]
theorem point_links_checked50281 : (cuts50281.take 1).map (fun c => (6594363393-1+2*2^10*c.k,111726595404808+c.lower,111726982566553+c.upper)) = pointBounds50281 := by
 decide +kernel
def cuts50282 : List PrefixCut := [⟨43,166890662,166890755⟩,
⟨64,248542488,248542626⟩]
theorem checked50282 : checkPrefixCuts (2^48) 6594494465 10 Manual.Count131072.C050282.packed 64 cuts50282 = true := by
 decide +kernel
def pointBounds50282 : List (Nat × Nat × Nat) := [(6594582528,111727010970941,111727398132919)]
theorem point_links_checked50282 : (cuts50282.take 1).map (fun c => (6594494465-1+2*2^10*c.k,111726844080279+c.lower,111727231242164+c.upper)) = pointBounds50282 := by
 decide +kernel
def cuts50283 : List PrefixCut := [⟨64,248452170,248452309⟩]
theorem checked50283 : checkPrefixCuts (2^48) 6594625537 10 Manual.Count131072.C050283.packed 64 cuts50283 = true := by
 decide +kernel
def cuts50284 : List PrefixCut := [⟨16,60991882,60991918⟩,
⟨64,244520550,244520695⟩]
theorem checked50284 : checkPrefixCuts (2^48) 6594756609 10 Manual.Count131072.C050284.packed 64 cuts50284 = true := by
 decide +kernel
def pointBounds50284 : List (Nat × Nat × Nat) := [(6594789376,111727402066819,111727789229017)]
theorem point_links_checked50284 : (cuts50284.take 1).map (fun c => (6594756609-1+2*2^10*c.k,111727341074937+c.lower,111727728237099+c.upper)) = pointBounds50284 := by
 decide +kernel
def cuts50285 : List PrefixCut := [⟨53,204994044,204994162⟩,
⟨64,246905800,246905944⟩]
theorem checked50285 : checkPrefixCuts (2^48) 6594887681 10 Manual.Count131072.C050285.packed 64 cuts50285 = true := by
 decide +kernel
def pointBounds50285 : List (Nat × Nat × Nat) := [(6594996224,111727790589531,111728177751956)]
theorem point_links_checked50285 : (cuts50285.take 1).map (fun c => (6594887681-1+2*2^10*c.k,111727585595487+c.lower,111727972757794+c.upper)) = pointBounds50285 := by
 decide +kernel
def cuts50286 : List PrefixCut := [⟨64,249333640,249333780⟩]
theorem checked50286 : checkPrefixCuts (2^48) 6595018753 10 Manual.Count131072.C050286.packed 64 cuts50286 = true := by
 decide +kernel
def cuts50287 : List PrefixCut := [⟨26,97521299,97521354⟩,
⟨64,244207230,244207368⟩]
theorem checked50287 : checkPrefixCuts (2^48) 6595149825 10 Manual.Count131072.C050287.packed 64 cuts50287 = true := by
 decide +kernel
def pointBounds50287 : List (Nat × Nat × Nat) := [(6595203072,111728179356226,111728566518872)]
theorem point_links_checked50287 : (cuts50287.take 1).map (fun c => (6595149825-1+2*2^10*c.k,111728081834927+c.lower,111728468997518+c.upper)) = pointBounds50287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000008
