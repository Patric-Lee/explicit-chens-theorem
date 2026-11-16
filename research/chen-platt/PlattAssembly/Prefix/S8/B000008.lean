import PlattAssemblyKernel
import PlattCertificates.Count131072.C070256
import PlattCertificates.Count131072.C070257
import PlattCertificates.Count131072.C070258
import PlattCertificates.Count131072.C070259
import PlattCertificates.Count131072.C070260
import PlattCertificates.Count131072.C070261
import PlattCertificates.Count131072.C070262
import PlattCertificates.Count131072.C070263
import PlattCertificates.Count131072.C070264
import PlattCertificates.Count131072.C070265
import PlattCertificates.Count131072.C070266
import PlattCertificates.Count131072.C070267
import PlattCertificates.Count131072.C070268
import PlattCertificates.Count131072.C070269
import PlattCertificates.Count131072.C070270
import PlattCertificates.Count131072.C070271
import PlattCertificates.Count131072.C070272
import PlattCertificates.Count131072.C070273
import PlattCertificates.Count131072.C070274
import PlattCertificates.Count131072.C070275
import PlattCertificates.Count131072.C070276
import PlattCertificates.Count131072.C070277
import PlattCertificates.Count131072.C070278
import PlattCertificates.Count131072.C070279
import PlattCertificates.Count131072.C070280
import PlattCertificates.Count131072.C070281
import PlattCertificates.Count131072.C070282
import PlattCertificates.Count131072.C070283
import PlattCertificates.Count131072.C070284
import PlattCertificates.Count131072.C070285
import PlattCertificates.Count131072.C070286
import PlattCertificates.Count131072.C070287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70256 : List PrefixCut := [⟨64,173206537,173206641⟩]
theorem checked70256 : checkPrefixCuts (2^48) 9212526593 10 Manual.Count131072.C070256.packed 64 cuts70256 = true := by
 decide +kernel
def cuts70257 : List PrefixCut := [⟨20,53681608,53681641⟩,
⟨64,175434420,175434523⟩]
theorem checked70257 : checkPrefixCuts (2^48) 9212657665 10 Manual.Count131072.C070257.packed 64 cuts70257 = true := by
 decide +kernel
def pointBounds70257 : List (Nat × Nat × Nat) := [(9212698624,115858716769213,115859106300854)]
theorem point_links_checked70257 : (cuts70257.take 1).map (fun c => (9212657665-1+2*2^10*c.k,115858663087605+c.lower,115859052619213+c.upper)) = pointBounds70257 := by
 decide +kernel
def cuts70258 : List PrefixCut := [⟨64,175859662,175859766⟩]
theorem checked70258 : checkPrefixCuts (2^48) 9212788737 10 Manual.Count131072.C070258.packed 64 cuts70258 = true := by
 decide +kernel
def cuts70259 : List PrefixCut := [⟨33,89456490,89456542⟩,
⟨64,174268460,174268563⟩]
theorem checked70259 : checkPrefixCuts (2^48) 9212919809 10 Manual.Count131072.C070259.packed 64 cuts70259 = true := by
 decide +kernel
def pointBounds70259 : List (Nat × Nat × Nat) := [(9212987392,115859103838177,115859493370044)]
theorem point_links_checked70259 : (cuts70259.take 1).map (fun c => (9212919809-1+2*2^10*c.k,115859014381687+c.lower,115859403913502+c.upper)) = pointBounds70259 := by
 decide +kernel
def cuts70260 : List PrefixCut := [⟨64,175121426,175121524⟩]
theorem checked70260 : checkPrefixCuts (2^48) 9213050881 10 Manual.Count131072.C070260.packed 64 cuts70260 = true := by
 decide +kernel
def cuts70261 : List PrefixCut := [⟨46,123854436,123854503⟩,
⟨64,173285871,173285968⟩]
theorem checked70261 : checkPrefixCuts (2^48) 9213181953 10 Manual.Count131072.C070261.packed 64 cuts70261 = true := by
 decide +kernel
def pointBounds70261 : List (Nat × Nat × Nat) := [(9213276160,115859487626009,115859877158092)]
theorem point_links_checked70261 : (cuts70261.take 1).map (fun c => (9213181953-1+2*2^10*c.k,115859363771573+c.lower,115859753303589+c.upper)) = pointBounds70261 := by
 decide +kernel
def cuts70262 : List PrefixCut := [⟨64,175574703,175574806⟩]
theorem checked70262 : checkPrefixCuts (2^48) 9213313025 10 Manual.Count131072.C070262.packed 64 cuts70262 = true := by
 decide +kernel
def cuts70263 : List PrefixCut := [⟨59,160358275,160358367⟩,
⟨64,174227991,174228092⟩]
theorem checked70263 : checkPrefixCuts (2^48) 9213444097 10 Manual.Count131072.C070263.packed 64 cuts70263 = true := by
 decide +kernel
def pointBounds70263 : List (Nat × Nat × Nat) := [(9213564928,115859872990422,115860262522730)]
theorem point_links_checked70263 : (cuts70263.take 1).map (fun c => (9213444097-1+2*2^10*c.k,115859712632147+c.lower,115860102164363+c.upper)) = pointBounds70263 := by
 decide +kernel
def cuts70264 : List PrefixCut := [⟨64,174347720,174347824⟩]
theorem checked70264 : checkPrefixCuts (2^48) 9213575169 10 Manual.Count131072.C070264.packed 64 cuts70264 = true := by
 decide +kernel
def cuts70265 : List PrefixCut := [⟨64,175506106,175506207⟩]
theorem checked70265 : checkPrefixCuts (2^48) 9213706241 10 Manual.Count131072.C070265.packed 64 cuts70265 = true := by
 decide +kernel
def cuts70266 : List PrefixCut := [⟨8,20956697,20956712⟩,
⟨64,174190011,174190113⟩]
theorem checked70266 : checkPrefixCuts (2^48) 9213837313 10 Manual.Count131072.C070266.packed 64 cuts70266 = true := by
 decide +kernel
def pointBounds70266 : List (Nat × Nat × Nat) := [(9213853696,115860257670661,115860647203198)]
theorem point_links_checked70266 : (cuts70266.take 1).map (fun c => (9213837313-1+2*2^10*c.k,115860236713964+c.lower,115860626246486+c.upper)) = pointBounds70266 := by
 decide +kernel
def cuts70267 : List PrefixCut := [⟨64,174981791,174981898⟩]
theorem checked70267 : checkPrefixCuts (2^48) 9213968385 10 Manual.Count131072.C070267.packed 64 cuts70267 = true := by
 decide +kernel
def cuts70268 : List PrefixCut := [⟨21,57216792,57216829⟩,
⟨64,172352174,172352282⟩]
theorem checked70268 : checkPrefixCuts (2^48) 9214099457 10 Manual.Count131072.C070268.packed 64 cuts70268 = true := by
 decide +kernel
def pointBounds70268 : List (Nat × Nat × Nat) := [(9214142464,115860643102558,115861032635326)]
theorem point_links_checked70268 : (cuts70268.take 1).map (fun c => (9214099457-1+2*2^10*c.k,115860585885766+c.lower,115860975418497+c.upper)) = pointBounds70268 := by
 decide +kernel
def cuts70269 : List PrefixCut := [⟨64,171952608,171952716⟩]
theorem checked70269 : checkPrefixCuts (2^48) 9214230529 10 Manual.Count131072.C070269.packed 64 cuts70269 = true := by
 decide +kernel
def cuts70270 : List PrefixCut := [⟨34,91397511,91397565⟩,
⟨64,174607750,174607857⟩]
theorem checked70270 : checkPrefixCuts (2^48) 9214361601 10 Manual.Count131072.C070270.packed 64 cuts70270 = true := by
 decide +kernel
def pointBounds70270 : List (Nat × Nat × Nat) := [(9214431232,115861021588059,115861411121060)]
theorem point_links_checked70270 : (cuts70270.take 1).map (fun c => (9214361601-1+2*2^10*c.k,115860930190548+c.lower,115861319723495+c.upper)) = pointBounds70270 := by
 decide +kernel
def cuts70271 : List PrefixCut := [⟨64,174819100,174819202⟩]
theorem checked70271 : checkPrefixCuts (2^48) 9214492673 10 Manual.Count131072.C070271.packed 64 cuts70271 = true := by
 decide +kernel
def cuts70272 : List PrefixCut := [⟨47,129455574,129455650⟩,
⟨64,175122089,175122193⟩]
theorem checked70272 : checkPrefixCuts (2^48) 9214623745 10 Manual.Count131072.C070272.packed 64 cuts70272 = true := by
 decide +kernel
def pointBounds70272 : List (Nat × Nat × Nat) := [(9214720000,115861409072972,115861798606204)]
theorem point_links_checked70272 : (cuts70272.take 1).map (fun c => (9214623745-1+2*2^10*c.k,115861279617398+c.lower,115861669150554+c.upper)) = pointBounds70272 := by
 decide +kernel
def cuts70273 : List PrefixCut := [⟨64,174233755,174233855⟩]
theorem checked70273 : checkPrefixCuts (2^48) 9214754817 10 Manual.Count131072.C070273.packed 64 cuts70273 = true := by
 decide +kernel
def cuts70274 : List PrefixCut := [⟨60,160608077,160608178⟩,
⟨64,171360006,171360114⟩]
theorem checked70274 : checkPrefixCuts (2^48) 9214885889 10 Manual.Count131072.C070274.packed 64 cuts70274 = true := by
 decide +kernel
def pointBounds70274 : List (Nat × Nat × Nat) := [(9215008768,115861789581319,115862179114780)]
theorem point_links_checked70274 : (cuts70274.take 1).map (fun c => (9214885889-1+2*2^10*c.k,115861628973242+c.lower,115862018506602+c.upper)) = pointBounds70274 := by
 decide +kernel
def cuts70275 : List PrefixCut := [⟨64,175175702,175175803⟩]
theorem checked70275 : checkPrefixCuts (2^48) 9215016961 10 Manual.Count131072.C070275.packed 64 cuts70275 = true := by
 decide +kernel
def cuts70276 : List PrefixCut := [⟨64,174653955,174654057⟩]
theorem checked70276 : checkPrefixCuts (2^48) 9215148033 10 Manual.Count131072.C070276.packed 64 cuts70276 = true := by
 decide +kernel
def cuts70277 : List PrefixCut := [⟨9,23610774,23610787⟩,
⟨64,172788265,172788370⟩]
theorem checked70277 : checkPrefixCuts (2^48) 9215279105 10 Manual.Count131072.C070277.packed 64 cuts70277 = true := by
 decide +kernel
def pointBounds70277 : List (Nat × Nat × Nat) := [(9215297536,115862173773679,115862563307363)]
theorem point_links_checked70277 : (cuts70277.take 1).map (fun c => (9215279105-1+2*2^10*c.k,115862150162905+c.lower,115862539696576+c.upper)) = pointBounds70277 := by
 decide +kernel
def cuts70278 : List PrefixCut := [⟨64,176725950,176726057⟩]
theorem checked70278 : checkPrefixCuts (2^48) 9215410177 10 Manual.Count131072.C070278.packed 64 cuts70278 = true := by
 decide +kernel
def cuts70279 : List PrefixCut := [⟨22,60445440,60445480⟩,
⟨64,174157809,174157918⟩]
theorem checked70279 : checkPrefixCuts (2^48) 9215541249 10 Manual.Count131072.C070279.packed 64 cuts70279 = true := by
 decide +kernel
def pointBounds70279 : List (Nat × Nat × Nat) := [(9215586304,115862560122560,115862949656483)]
theorem point_links_checked70279 : (cuts70279.take 1).map (fun c => (9215541249-1+2*2^10*c.k,115862499677120+c.lower,115862889211003+c.upper)) = pointBounds70279 := by
 decide +kernel
def cuts70280 : List PrefixCut := [⟨64,175590841,175590939⟩]
theorem checked70280 : checkPrefixCuts (2^48) 9215672321 10 Manual.Count131072.C070280.packed 64 cuts70280 = true := by
 decide +kernel
def cuts70281 : List PrefixCut := [⟨35,93765524,93765573⟩,
⟨64,173633629,173633728⟩]
theorem checked70281 : checkPrefixCuts (2^48) 9215803393 10 Manual.Count131072.C070281.packed 64 cuts70281 = true := by
 decide +kernel
def pointBounds70281 : List (Nat × Nat × Nat) := [(9215875072,115862943191294,115863332725433)]
theorem point_links_checked70281 : (cuts70281.take 1).map (fun c => (9215803393-1+2*2^10*c.k,115862849425770+c.lower,115863238959860+c.upper)) = pointBounds70281 := by
 decide +kernel
def cuts70282 : List PrefixCut := [⟨64,176654817,176654920⟩]
theorem checked70282 : checkPrefixCuts (2^48) 9215934465 10 Manual.Count131072.C070282.packed 64 cuts70282 = true := by
 decide +kernel
def cuts70283 : List PrefixCut := [⟨48,129465852,129465924⟩,
⟨64,173414901,173415001⟩]
theorem checked70283 : checkPrefixCuts (2^48) 9216065537 10 Manual.Count131072.C070283.packed 64 cuts70283 = true := by
 decide +kernel
def pointBounds70283 : List (Nat × Nat × Nat) := [(9216163840,115863329180068,115863718714432)]
theorem point_links_checked70283 : (cuts70283.take 1).map (fun c => (9216065537-1+2*2^10*c.k,115863199714216+c.lower,115863589248508+c.upper)) = pointBounds70283 := by
 decide +kernel
def cuts70284 : List PrefixCut := [⟨64,178054692,178054794⟩]
theorem checked70284 : checkPrefixCuts (2^48) 9216196609 10 Manual.Count131072.C070284.packed 64 cuts70284 = true := by
 decide +kernel
def cuts70285 : List PrefixCut := [⟨61,166049713,166049813⟩,
⟨64,174509423,174509528⟩]
theorem checked70285 : checkPrefixCuts (2^48) 9216327681 10 Manual.Count131072.C070285.packed 64 cuts70285 = true := by
 decide +kernel
def pointBounds70285 : List (Nat × Nat × Nat) := [(9216452608,115863717233522,115864106768116)]
theorem point_links_checked70285 : (cuts70285.take 1).map (fun c => (9216327681-1+2*2^10*c.k,115863551183809+c.lower,115863940718303+c.upper)) = pointBounds70285 := by
 decide +kernel
def cuts70286 : List PrefixCut := [⟨64,174476408,174476519⟩]
theorem checked70286 : checkPrefixCuts (2^48) 9216458753 10 Manual.Count131072.C070286.packed 64 cuts70286 = true := by
 decide +kernel
def cuts70287 : List PrefixCut := [⟨64,176245236,176245340⟩]
theorem checked70287 : checkPrefixCuts (2^48) 9216589825 10 Manual.Count131072.C070287.packed 64 cuts70287 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000008
