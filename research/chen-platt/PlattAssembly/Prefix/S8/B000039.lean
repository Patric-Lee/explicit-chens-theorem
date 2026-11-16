import PlattAssemblyKernel
import PlattCertificates.Count131072.C071248
import PlattCertificates.Count131072.C071249
import PlattCertificates.Count131072.C071250
import PlattCertificates.Count131072.C071251
import PlattCertificates.Count131072.C071252
import PlattCertificates.Count131072.C071253
import PlattCertificates.Count131072.C071254
import PlattCertificates.Count131072.C071255
import PlattCertificates.Count131072.C071256
import PlattCertificates.Count131072.C071257
import PlattCertificates.Count131072.C071258
import PlattCertificates.Count131072.C071259
import PlattCertificates.Count131072.C071260
import PlattCertificates.Count131072.C071261
import PlattCertificates.Count131072.C071262
import PlattCertificates.Count131072.C071263
import PlattCertificates.Count131072.C071264
import PlattCertificates.Count131072.C071265
import PlattCertificates.Count131072.C071266
import PlattCertificates.Count131072.C071267
import PlattCertificates.Count131072.C071268
import PlattCertificates.Count131072.C071269
import PlattCertificates.Count131072.C071270
import PlattCertificates.Count131072.C071271
import PlattCertificates.Count131072.C071272
import PlattCertificates.Count131072.C071273
import PlattCertificates.Count131072.C071274
import PlattCertificates.Count131072.C071275
import PlattCertificates.Count131072.C071276
import PlattCertificates.Count131072.C071277
import PlattCertificates.Count131072.C071278
import PlattCertificates.Count131072.C071279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71248 : List PrefixCut := [⟨64,174561986,174562091⟩]
theorem checked71248 : checkPrefixCuts (2^48) 9342550017 10 Manual.Count131072.C071248.packed 64 cuts71248 = true := by
 decide +kernel
def cuts71249 : List PrefixCut := [⟨33,89328753,89328801⟩,
⟨64,171667287,171667386⟩]
theorem checked71249 : checkPrefixCuts (2^48) 9342681089 10 Manual.Count131072.C071249.packed 64 cuts71249 = true := by
 decide +kernel
def pointBounds71249 : List (Nat × Nat × Nat) := [(9342748672,116030679925465,116031069558675)]
theorem point_links_checked71249 : (cuts71249.take 1).map (fun c => (9342681089-1+2*2^10*c.k,116030590596712+c.lower,116030980229874+c.upper)) = pointBounds71249 := by
 decide +kernel
def cuts71250 : List PrefixCut := [⟨64,173321883,173321988⟩]
theorem checked71250 : checkPrefixCuts (2^48) 9342812161 10 Manual.Count131072.C071250.packed 64 cuts71250 = true := by
 decide +kernel
def cuts71251 : List PrefixCut := [⟨48,126231487,126231562⟩,
⟨64,168951055,168951155⟩]
theorem checked71251 : checkPrefixCuts (2^48) 9342943233 10 Manual.Count131072.C071251.packed 64 cuts71251 = true := by
 decide +kernel
def pointBounds71251 : List (Nat × Nat × Nat) := [(9343041536,116031061817369,116031451450810)]
theorem point_links_checked71251 : (cuts71251.take 1).map (fun c => (9342943233-1+2*2^10*c.k,116030935585882+c.lower,116031325219248+c.upper)) = pointBounds71251 := by
 decide +kernel
def cuts71252 : List PrefixCut := [⟨64,173196506,173196606⟩]
theorem checked71252 : checkPrefixCuts (2^48) 9343074305 10 Manual.Count131072.C071252.packed 64 cuts71252 = true := by
 decide +kernel
def cuts71253 : List PrefixCut := [⟨63,167530422,167530527⟩,
⟨64,170271864,170271971⟩]
theorem checked71253 : checkPrefixCuts (2^48) 9343205377 10 Manual.Count131072.C071253.packed 64 cuts71253 = true := by
 decide +kernel
def pointBounds71253 : List (Nat × Nat × Nat) := [(9343334400,116031445263865,116031834897536)]
theorem point_links_checked71253 : (cuts71253.take 1).map (fun c => (9343205377-1+2*2^10*c.k,116031277733443+c.lower,116031667367009+c.upper)) = pointBounds71253 := by
 decide +kernel
def cuts71254 : List PrefixCut := [⟨64,172257751,172257849⟩]
theorem checked71254 : checkPrefixCuts (2^48) 9343336449 10 Manual.Count131072.C071254.packed 64 cuts71254 = true := by
 decide +kernel
def cuts71255 : List PrefixCut := [⟨64,171080455,171080557⟩]
theorem checked71255 : checkPrefixCuts (2^48) 9343467521 10 Manual.Count131072.C071255.packed 64 cuts71255 = true := by
 decide +kernel
def cuts71256 : List PrefixCut := [⟨14,37927180,37927200⟩,
⟨64,173608528,173608627⟩]
theorem checked71256 : checkPrefixCuts (2^48) 9343598593 10 Manual.Count131072.C071256.packed 64 cuts71256 = true := by
 decide +kernel
def pointBounds71256 : List (Nat × Nat × Nat) := [(9343627264,116031829270693,116032218904586)]
theorem point_links_checked71256 : (cuts71256.take 1).map (fun c => (9343598593-1+2*2^10*c.k,116031791343513+c.lower,116032180977386+c.upper)) = pointBounds71256 := by
 decide +kernel
def cuts71257 : List PrefixCut := [⟨64,169961052,169961159⟩]
theorem checked71257 : checkPrefixCuts (2^48) 9343729665 10 Manual.Count131072.C071257.packed 64 cuts71257 = true := by
 decide +kernel
def cuts71258 : List PrefixCut := [⟨29,78864505,78864550⟩,
⟨64,173935020,173935123⟩]
theorem checked71258 : checkPrefixCuts (2^48) 9343860737 10 Manual.Count131072.C071258.packed 64 cuts71258 = true := by
 decide +kernel
def pointBounds71258 : List (Nat × Nat × Nat) := [(9343920128,116032213777598,116032603411722)]
theorem point_links_checked71258 : (cuts71258.take 1).map (fun c => (9343860737-1+2*2^10*c.k,116032134913093+c.lower,116032524547172+c.upper)) = pointBounds71258 := by
 decide +kernel
def cuts71259 : List PrefixCut := [⟨64,172727640,172727741⟩]
theorem checked71259 : checkPrefixCuts (2^48) 9343991809 10 Manual.Count131072.C071259.packed 64 cuts71259 = true := by
 decide +kernel
def cuts71260 : List PrefixCut := [⟨44,119166807,119166879⟩,
⟨64,173026455,173026557⟩]
theorem checked71260 : checkPrefixCuts (2^48) 9344122881 10 Manual.Count131072.C071260.packed 64 cuts71260 = true := by
 decide +kernel
def pointBounds71260 : List (Nat × Nat × Nat) := [(9344212992,116032600742560,116032990376915)]
theorem point_links_checked71260 : (cuts71260.take 1).map (fun c => (9344122881-1+2*2^10*c.k,116032481575753+c.lower,116032871210036+c.upper)) = pointBounds71260 := by
 decide +kernel
def cuts71261 : List PrefixCut := [⟨64,169620172,169620274⟩]
theorem checked71261 : checkPrefixCuts (2^48) 9344253953 10 Manual.Count131072.C071261.packed 64 cuts71261 = true := by
 decide +kernel
def cuts71262 : List PrefixCut := [⟨59,157147320,157147411⟩,
⟨64,169828661,169828760⟩]
theorem checked71262 : checkPrefixCuts (2^48) 9344385025 10 Manual.Count131072.C071262.packed 64 cuts71262 = true := by
 decide +kernel
def pointBounds71262 : List (Nat × Nat × Nat) := [(9344505856,116032981369700,116033371004278)]
theorem point_links_checked71262 : (cuts71262.take 1).map (fun c => (9344385025-1+2*2^10*c.k,116032824222380+c.lower,116033213856867+c.upper)) = pointBounds71262 := by
 decide +kernel
def cuts71263 : List PrefixCut := [⟨64,173591487,173591593⟩]
theorem checked71263 : checkPrefixCuts (2^48) 9344516097 10 Manual.Count131072.C071263.packed 64 cuts71263 = true := by
 decide +kernel
def cuts71264 : List PrefixCut := [⟨64,170245592,170245695⟩]
theorem checked71264 : checkPrefixCuts (2^48) 9344647169 10 Manual.Count131072.C071264.packed 64 cuts71264 = true := by
 decide +kernel
def cuts71265 : List PrefixCut := [⟨10,26747498,26747511⟩,
⟨64,174761337,174761435⟩]
theorem checked71265 : checkPrefixCuts (2^48) 9344778241 10 Manual.Count131072.C071265.packed 64 cuts71265 = true := by
 decide +kernel
def pointBounds71265 : List (Nat × Nat × Nat) := [(9344798720,116033364635618,116033754270426)]
theorem point_links_checked71265 : (cuts71265.take 1).map (fun c => (9344778241-1+2*2^10*c.k,116033337888120+c.lower,116033727522915+c.upper)) = pointBounds71265 := by
 decide +kernel
def cuts71266 : List PrefixCut := [⟨64,168885380,168885478⟩]
theorem checked71266 : checkPrefixCuts (2^48) 9344909313 10 Manual.Count131072.C071266.packed 64 cuts71266 = true := by
 decide +kernel
def cuts71267 : List PrefixCut := [⟨25,67981205,67981248⟩,
⟨64,173099830,173099939⟩]
theorem checked71267 : checkPrefixCuts (2^48) 9345040385 10 Manual.Count131072.C071267.packed 64 cuts71267 = true := by
 decide +kernel
def pointBounds71267 : List (Nat × Nat × Nat) := [(9345091584,116033749516042,116034139151076)]
theorem point_links_checked71267 : (cuts71267.take 1).map (fun c => (9345040385-1+2*2^10*c.k,116033681534837+c.lower,116034071169828+c.upper)) = pointBounds71267 := by
 decide +kernel
def cuts71268 : List PrefixCut := [⟨64,173278112,173278217⟩]
theorem checked71268 : checkPrefixCuts (2^48) 9345171457 10 Manual.Count131072.C071268.packed 64 cuts71268 = true := by
 decide +kernel
def cuts71269 : List PrefixCut := [⟨40,105146365,105146427⟩,
⟨64,169661383,169661482⟩]
theorem checked71269 : checkPrefixCuts (2^48) 9345302529 10 Manual.Count131072.C071269.packed 64 cuts71269 = true := by
 decide +kernel
def pointBounds71269 : List (Nat × Nat × Nat) := [(9345384448,116034133059144,116034522694411)]
theorem point_links_checked71269 : (cuts71269.take 1).map (fun c => (9345302529-1+2*2^10*c.k,116034027912779+c.lower,116034417547984+c.upper)) = pointBounds71269 := by
 decide +kernel
def cuts71270 : List PrefixCut := [⟨64,173032303,173032405⟩]
theorem checked71270 : checkPrefixCuts (2^48) 9345433601 10 Manual.Count131072.C071270.packed 64 cuts71270 = true := by
 decide +kernel
def cuts71271 : List PrefixCut := [⟨55,148664286,148664374⟩,
⟨64,173421415,173421515⟩]
theorem checked71271 : checkPrefixCuts (2^48) 9345564673 10 Manual.Count131072.C071271.packed 64 cuts71271 = true := by
 decide +kernel
def pointBounds71271 : List (Nat × Nat × Nat) := [(9345677312,116034519270751,116034908906245)]
theorem point_links_checked71271 : (cuts71271.take 1).map (fun c => (9345564673-1+2*2^10*c.k,116034370606465+c.lower,116034760241871+c.upper)) = pointBounds71271 := by
 decide +kernel
def cuts71272 : List PrefixCut := [⟨64,170738493,170738593⟩]
theorem checked71272 : checkPrefixCuts (2^48) 9345695745 10 Manual.Count131072.C071272.packed 64 cuts71272 = true := by
 decide +kernel
def cuts71273 : List PrefixCut := [⟨64,172753962,172754064⟩]
theorem checked71273 : checkPrefixCuts (2^48) 9345826817 10 Manual.Count131072.C071273.packed 64 cuts71273 = true := by
 decide +kernel
def cuts71274 : List PrefixCut := [⟨6,15239336,15239347⟩,
⟨64,171667323,171667429⟩]
theorem checked71274 : checkPrefixCuts (2^48) 9345957889 10 Manual.Count131072.C071274.packed 64 cuts71274 = true := by
 decide +kernel
def pointBounds71274 : List (Nat × Nat × Nat) := [(9345970176,116034902759671,116035292395390)]
theorem point_links_checked71274 : (cuts71274.take 1).map (fun c => (9345957889-1+2*2^10*c.k,116034887520335+c.lower,116035277156043+c.upper)) = pointBounds71274 := by
 decide +kernel
def cuts71275 : List PrefixCut := [⟨64,171393878,171393980⟩]
theorem checked71275 : checkPrefixCuts (2^48) 9346088961 10 Manual.Count131072.C071275.packed 64 cuts71275 = true := by
 decide +kernel
def cuts71276 : List PrefixCut := [⟨21,57251224,57251259⟩,
⟨64,173228566,173228673⟩]
theorem checked71276 : checkPrefixCuts (2^48) 9346220033 10 Manual.Count131072.C071276.packed 64 cuts71276 = true := by
 decide +kernel
def pointBounds71276 : List (Nat × Nat × Nat) := [(9346263040,116035287832760,116035677468711)]
theorem point_links_checked71276 : (cuts71276.take 1).map (fun c => (9346220033-1+2*2^10*c.k,116035230581536+c.lower,116035620217452+c.upper)) = pointBounds71276 := by
 decide +kernel
def cuts71277 : List PrefixCut := [⟨64,173045439,173045537⟩]
theorem checked71277 : checkPrefixCuts (2^48) 9346351105 10 Manual.Count131072.C071277.packed 64 cuts71277 = true := by
 decide +kernel
def cuts71278 : List PrefixCut := [⟨36,96429763,96429820⟩,
⟨64,171868507,171868607⟩]
theorem checked71278 : checkPrefixCuts (2^48) 9346482177 10 Manual.Count131072.C071278.packed 64 cuts71278 = true := by
 decide +kernel
def pointBounds71278 : List (Nat × Nat × Nat) := [(9346555904,116035673285304,116036062921482)]
theorem point_links_checked71278 : (cuts71278.take 1).map (fun c => (9346482177-1+2*2^10*c.k,116035576855541+c.lower,116035966491662+c.upper)) = pointBounds71278 := by
 decide +kernel
def cuts71279 : List PrefixCut := [⟨64,172829787,172829883⟩]
theorem checked71279 : checkPrefixCuts (2^48) 9346613249 10 Manual.Count131072.C071279.packed 64 cuts71279 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000039
