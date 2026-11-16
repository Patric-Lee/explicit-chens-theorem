import PlattAssemblyKernel
import PlattCertificates.Count131072.C053232
import PlattCertificates.Count131072.C053233
import PlattCertificates.Count131072.C053234
import PlattCertificates.Count131072.C053235
import PlattCertificates.Count131072.C053236
import PlattCertificates.Count131072.C053237
import PlattCertificates.Count131072.C053238
import PlattCertificates.Count131072.C053239
import PlattCertificates.Count131072.C053240
import PlattCertificates.Count131072.C053241
import PlattCertificates.Count131072.C053242
import PlattCertificates.Count131072.C053243
import PlattCertificates.Count131072.C053244
import PlattCertificates.Count131072.C053245
import PlattCertificates.Count131072.C053246
import PlattCertificates.Count131072.C053247
import PlattCertificates.Count131072.C053248
import PlattCertificates.Count131072.C053249
import PlattCertificates.Count131072.C053250
import PlattCertificates.Count131072.C053251
import PlattCertificates.Count131072.C053252
import PlattCertificates.Count131072.C053253
import PlattCertificates.Count131072.C053254
import PlattCertificates.Count131072.C053255
import PlattCertificates.Count131072.C053256
import PlattCertificates.Count131072.C053257
import PlattCertificates.Count131072.C053258
import PlattCertificates.Count131072.C053259
import PlattCertificates.Count131072.C053260
import PlattCertificates.Count131072.C053261
import PlattCertificates.Count131072.C053262
import PlattCertificates.Count131072.C053263
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53232 : List PrefixCut := [⟨64,232155975,232156107⟩]
theorem checked53232 : checkPrefixCuts (2^48) 6981156865 10 Manual.Count131072.C053232.packed 64 cuts53232 = true := by
 decide +kernel
def cuts53233 : List PrefixCut := [⟨23,84426607,84426656⟩,
⟨64,234731972,234732107⟩]
theorem checked53233 : checkPrefixCuts (2^48) 6981287937 10 Manual.Count131072.C053233.packed 64 cuts53233 = true := by
 decide +kernel
def pointBounds53233 : List (Nat × Nat × Nat) := [(6981335040,112435602478927,112435990043631)]
theorem point_links_checked53233 : (cuts53233.take 1).map (fun c => (6981287937-1+2*2^10*c.k,112435518052320+c.lower,112435905616975+c.upper)) = pointBounds53233 := by
 decide +kernel
def cuts53234 : List PrefixCut := [⟨64,234929155,234929288⟩]
theorem checked53234 : checkPrefixCuts (2^48) 6981419009 10 Manual.Count131072.C053234.packed 64 cuts53234 = true := by
 decide +kernel
def cuts53235 : List PrefixCut := [⟨2,7378002,7378006⟩,
⟨64,232142905,232143040⟩]
theorem checked53235 : checkPrefixCuts (2^48) 6981550081 10 Manual.Count131072.C053235.packed 64 cuts53235 = true := by
 decide +kernel
def pointBounds53235 : List (Nat × Nat × Nat) := [(6981554176,112435995091449,112436382656376)]
theorem point_links_checked53235 : (cuts53235.take 1).map (fun c => (6981550081-1+2*2^10*c.k,112435987713447+c.lower,112436375278370+c.upper)) = pointBounds53235 := by
 decide +kernel
def cuts53236 : List PrefixCut := [⟨45,162311977,162312071⟩,
⟨64,231412851,231412984⟩]
theorem checked53236 : checkPrefixCuts (2^48) 6981681153 10 Manual.Count131072.C053236.packed 64 cuts53236 = true := by
 decide +kernel
def pointBounds53236 : List (Nat × Nat × Nat) := [(6981773312,112436382168329,112436769733481)]
theorem point_links_checked53236 : (cuts53236.take 1).map (fun c => (6981681153-1+2*2^10*c.k,112436219856352+c.lower,112436607421410+c.upper)) = pointBounds53236 := by
 decide +kernel
def cuts53237 : List PrefixCut := [⟨64,233263009,233263141⟩]
theorem checked53237 : checkPrefixCuts (2^48) 6981812225 10 Manual.Count131072.C053237.packed 64 cuts53237 = true := by
 decide +kernel
def cuts53238 : List PrefixCut := [⟨24,87966355,87966404⟩,
⟨64,235758112,235758243⟩]
theorem checked53238 : checkPrefixCuts (2^48) 6981943297 10 Manual.Count131072.C053238.packed 64 cuts53238 = true := by
 decide +kernel
def pointBounds53238 : List (Nat × Nat × Nat) := [(6981992448,112436772498567,112437160063939)]
theorem point_links_checked53238 : (cuts53238.take 1).map (fun c => (6981943297-1+2*2^10*c.k,112436684532212+c.lower,112437072097535+c.upper)) = pointBounds53238 := by
 decide +kernel
def cuts53239 : List PrefixCut := [⟨64,233294560,233294693⟩]
theorem checked53239 : checkPrefixCuts (2^48) 6982074369 10 Manual.Count131072.C053239.packed 64 cuts53239 = true := by
 decide +kernel
def cuts53240 : List PrefixCut := [⟨3,11005493,11005499⟩,
⟨64,233249868,233249999⟩]
theorem checked53240 : checkPrefixCuts (2^48) 6982205441 10 Manual.Count131072.C053240.packed 64 cuts53240 = true := by
 decide +kernel
def pointBounds53240 : List (Nat × Nat × Nat) := [(6982211584,112437164590377,112437552155970)]
theorem point_links_checked53240 : (cuts53240.take 1).map (fun c => (6982205441-1+2*2^10*c.k,112437153584884+c.lower,112437541150471+c.upper)) = pointBounds53240 := by
 decide +kernel
def cuts53241 : List PrefixCut := [⟨46,170076965,170077061⟩,
⟨64,235019230,235019364⟩]
theorem checked53241 : checkPrefixCuts (2^48) 6982336513 10 Manual.Count131072.C053241.packed 64 cuts53241 = true := by
 decide +kernel
def pointBounds53241 : List (Nat × Nat × Nat) := [(6982430720,112437556911717,112437944477531)]
theorem point_links_checked53241 : (cuts53241.take 1).map (fun c => (6982336513-1+2*2^10*c.k,112437386834752+c.lower,112437774400470+c.upper)) = pointBounds53241 := by
 decide +kernel
def cuts53242 : List PrefixCut := [⟨64,228806851,228806985⟩]
theorem checked53242 : checkPrefixCuts (2^48) 6982467585 10 Manual.Count131072.C053242.packed 64 cuts53242 = true := by
 decide +kernel
def cuts53243 : List PrefixCut := [⟨25,91062012,91062062⟩,
⟨64,231059962,231060091⟩]
theorem checked53243 : checkPrefixCuts (2^48) 6982598657 10 Manual.Count131072.C053243.packed 64 cuts53243 = true := by
 decide +kernel
def pointBounds53243 : List (Nat × Nat × Nat) := [(6982649856,112437941722845,112438329288881)]
theorem point_links_checked53243 : (cuts53243.take 1).map (fun c => (6982598657-1+2*2^10*c.k,112437850660833+c.lower,112438238226819+c.upper)) = pointBounds53243 := by
 decide +kernel
def cuts53244 : List PrefixCut := [⟨64,236497414,236497548⟩]
theorem checked53244 : checkPrefixCuts (2^48) 6982729729 10 Manual.Count131072.C053244.packed 64 cuts53244 = true := by
 decide +kernel
def cuts53245 : List PrefixCut := [⟨4,14672611,14672619⟩,
⟨64,232099337,232099470⟩]
theorem checked53245 : checkPrefixCuts (2^48) 6982860801 10 Manual.Count131072.C053245.packed 64 cuts53245 = true := by
 decide +kernel
def pointBounds53245 : List (Nat × Nat × Nat) := [(6982868992,112438332890820,112438720457077)]
theorem point_links_checked53245 : (cuts53245.take 1).map (fun c => (6982860801-1+2*2^10*c.k,112438318218209+c.lower,112438705784458+c.upper)) = pointBounds53245 := by
 decide +kernel
def cuts53246 : List PrefixCut := [⟨47,171189604,171189703⟩,
⟨64,232498049,232498183⟩]
theorem checked53246 : checkPrefixCuts (2^48) 6982991873 10 Manual.Count131072.C053246.packed 64 cuts53246 = true := by
 decide +kernel
def pointBounds53246 : List (Nat × Nat × Nat) := [(6983088128,112438721507150,112439109073631)]
theorem point_links_checked53246 : (cuts53246.take 1).map (fun c => (6982991873-1+2*2^10*c.k,112438550317546+c.lower,112438937883928+c.upper)) = pointBounds53246 := by
 decide +kernel
def cuts53247 : List PrefixCut := [⟨64,231365087,231365214⟩]
theorem checked53247 : checkPrefixCuts (2^48) 6983122945 10 Manual.Count131072.C053247.packed 64 cuts53247 = true := by
 decide +kernel
def cuts53248 : List PrefixCut := [⟨26,95849981,95850034⟩,
⟨64,232932704,232932835⟩]
theorem checked53248 : checkPrefixCuts (2^48) 6983254017 10 Manual.Count131072.C053248.packed 64 cuts53248 = true := by
 decide +kernel
def pointBounds53248 : List (Nat × Nat × Nat) := [(6983307264,112439110030663,112439497597359)]
theorem point_links_checked53248 : (cuts53248.take 1).map (fun c => (6983254017-1+2*2^10*c.k,112439014180682+c.lower,112439401747325+c.upper)) = pointBounds53248 := by
 decide +kernel
def cuts53249 : List PrefixCut := [⟨64,236515557,236515690⟩]
theorem checked53249 : checkPrefixCuts (2^48) 6983385089 10 Manual.Count131072.C053249.packed 64 cuts53249 = true := by
 decide +kernel
def cuts53250 : List PrefixCut := [⟨5,18863013,18863023⟩,
⟨64,230304101,230304232⟩]
theorem checked53250 : checkPrefixCuts (2^48) 6983516161 10 Manual.Count131072.C053250.packed 64 cuts53250 = true := by
 decide +kernel
def pointBounds53250 : List (Nat × Nat × Nat) := [(6983526400,112439502491956,112439890058873)]
theorem point_links_checked53250 : (cuts53250.take 1).map (fun c => (6983516161-1+2*2^10*c.k,112439483628943+c.lower,112439871195850+c.upper)) = pointBounds53250 := by
 decide +kernel
def cuts53251 : List PrefixCut := [⟨48,176130969,176131069⟩,
⟨64,234854182,234854317⟩]
theorem checked53251 : checkPrefixCuts (2^48) 6983647233 10 Manual.Count131072.C053251.packed 64 cuts53251 = true := by
 decide +kernel
def pointBounds53251 : List (Nat × Nat × Nat) := [(6983745536,112439890064013,112440277631151)]
theorem point_links_checked53251 : (cuts53251.take 1).map (fun c => (6983647233-1+2*2^10*c.k,112439713933044+c.lower,112440101500082+c.upper)) = pointBounds53251 := by
 decide +kernel
def cuts53252 : List PrefixCut := [⟨64,230577588,230577722⟩]
theorem checked53252 : checkPrefixCuts (2^48) 6983778305 10 Manual.Count131072.C053252.packed 64 cuts53252 = true := by
 decide +kernel
def cuts53253 : List PrefixCut := [⟨27,96364910,96364965⟩,
⟨64,230170230,230170363⟩]
theorem checked53253 : checkPrefixCuts (2^48) 6983909377 10 Manual.Count131072.C053253.packed 64 cuts53253 = true := by
 decide +kernel
def pointBounds53253 : List (Nat × Nat × Nat) := [(6983964672,112440275729724,112440663297086)]
theorem point_links_checked53253 : (cuts53253.take 1).map (fun c => (6983909377-1+2*2^10*c.k,112440179364814+c.lower,112440566932121+c.upper)) = pointBounds53253 := by
 decide +kernel
def cuts53254 : List PrefixCut := [⟨64,233188583,233188714⟩]
theorem checked53254 : checkPrefixCuts (2^48) 6984040449 10 Manual.Count131072.C053254.packed 64 cuts53254 = true := by
 decide +kernel
def cuts53255 : List PrefixCut := [⟨6,22165988,22166001⟩,
⟨64,229839209,229839340⟩]
theorem checked53255 : checkPrefixCuts (2^48) 6984171521 10 Manual.Count131072.C053255.packed 64 cuts53255 = true := by
 decide +kernel
def pointBounds53255 : List (Nat × Nat × Nat) := [(6984183808,112440664889615,112441052457199)]
theorem point_links_checked53255 : (cuts53255.take 1).map (fun c => (6984171521-1+2*2^10*c.k,112440642723627+c.lower,112441030291198+c.upper)) = pointBounds53255 := by
 decide +kernel
def cuts53256 : List PrefixCut := [⟨49,179056383,179056485⟩,
⟨64,233945537,233945669⟩]
theorem checked53256 : checkPrefixCuts (2^48) 6984302593 10 Manual.Count131072.C053256.packed 64 cuts53256 = true := by
 decide +kernel
def pointBounds53256 : List (Nat × Nat × Nat) := [(6984402944,112441051619219,112441439187023)]
theorem point_links_checked53256 : (cuts53256.take 1).map (fun c => (6984302593-1+2*2^10*c.k,112440872562836+c.lower,112441260130538+c.upper)) = pointBounds53256 := by
 decide +kernel
def cuts53257 : List PrefixCut := [⟨64,230555950,230556083⟩]
theorem checked53257 : checkPrefixCuts (2^48) 6984433665 10 Manual.Count131072.C053257.packed 64 cuts53257 = true := by
 decide +kernel
def cuts53258 : List PrefixCut := [⟨28,101111186,101111244⟩,
⟨64,232123291,232123424⟩]
theorem checked53258 : checkPrefixCuts (2^48) 6984564737 10 Manual.Count131072.C053258.packed 64 cuts53258 = true := by
 decide +kernel
def pointBounds53258 : List (Nat × Nat × Nat) := [(6984622080,112441438175509,112441825743534)]
theorem point_links_checked53258 : (cuts53258.take 1).map (fun c => (6984564737-1+2*2^10*c.k,112441337064323+c.lower,112441724632290+c.upper)) = pointBounds53258 := by
 decide +kernel
def cuts53259 : List PrefixCut := [⟨64,229781632,229781762⟩]
theorem checked53259 : checkPrefixCuts (2^48) 6984695809 10 Manual.Count131072.C053259.packed 64 cuts53259 = true := by
 decide +kernel
def cuts53260 : List PrefixCut := [⟨7,25145959,25145973⟩,
⟨64,234048858,234048991⟩]
theorem checked53260 : checkPrefixCuts (2^48) 6984826881 10 Manual.Count131072.C053260.packed 64 cuts53260 = true := by
 decide +kernel
def pointBounds53260 : List (Nat × Nat × Nat) := [(6984841216,112441824115205,112442211683449)]
theorem point_links_checked53260 : (cuts53260.take 1).map (fun c => (6984826881-1+2*2^10*c.k,112441798969246+c.lower,112442186537476+c.upper)) = pointBounds53260 := by
 decide +kernel
def cuts53261 : List PrefixCut := [⟨50,183472215,183472321⟩,
⟨64,233037057,233037193⟩]
theorem checked53261 : checkPrefixCuts (2^48) 6984957953 10 Manual.Count131072.C053261.packed 64 cuts53261 = true := by
 decide +kernel
def pointBounds53261 : List (Nat × Nat × Nat) := [(6985060352,112442216490319,112442604058788)]
theorem point_links_checked53261 : (cuts53261.take 1).map (fun c => (6984957953-1+2*2^10*c.k,112442033018104+c.lower,112442420586467+c.upper)) = pointBounds53261 := by
 decide +kernel
def cuts53262 : List PrefixCut := [⟨64,234362460,234362593⟩]
theorem checked53262 : checkPrefixCuts (2^48) 6985089025 10 Manual.Count131072.C053262.packed 64 cuts53262 = true := by
 decide +kernel
def cuts53263 : List PrefixCut := [⟨29,106420710,106420773⟩,
⟨64,235204257,235204391⟩]
theorem checked53263 : checkPrefixCuts (2^48) 6985220097 10 Manual.Count131072.C053263.packed 64 cuts53263 = true := by
 decide +kernel
def pointBounds53263 : List (Nat × Nat × Nat) := [(6985279488,112442606838331,112442994407026)]
theorem point_links_checked53263 : (cuts53263.take 1).map (fun c => (6985220097-1+2*2^10*c.k,112442500417621+c.lower,112442887986253+c.upper)) = pointBounds53263 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000101
