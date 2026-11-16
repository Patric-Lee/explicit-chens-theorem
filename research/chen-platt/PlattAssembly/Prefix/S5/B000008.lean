import PlattAssemblyKernel
import PlattCertificates.Count131072.C040256
import PlattCertificates.Count131072.C040257
import PlattCertificates.Count131072.C040258
import PlattCertificates.Count131072.C040259
import PlattCertificates.Count131072.C040260
import PlattCertificates.Count131072.C040261
import PlattCertificates.Count131072.C040262
import PlattCertificates.Count131072.C040263
import PlattCertificates.Count131072.C040264
import PlattCertificates.Count131072.C040265
import PlattCertificates.Count131072.C040266
import PlattCertificates.Count131072.C040267
import PlattCertificates.Count131072.C040268
import PlattCertificates.Count131072.C040269
import PlattCertificates.Count131072.C040270
import PlattCertificates.Count131072.C040271
import PlattCertificates.Count131072.C040272
import PlattCertificates.Count131072.C040273
import PlattCertificates.Count131072.C040274
import PlattCertificates.Count131072.C040275
import PlattCertificates.Count131072.C040276
import PlattCertificates.Count131072.C040277
import PlattCertificates.Count131072.C040278
import PlattCertificates.Count131072.C040279
import PlattCertificates.Count131072.C040280
import PlattCertificates.Count131072.C040281
import PlattCertificates.Count131072.C040282
import PlattCertificates.Count131072.C040283
import PlattCertificates.Count131072.C040284
import PlattCertificates.Count131072.C040285
import PlattCertificates.Count131072.C040286
import PlattCertificates.Count131072.C040287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40256 : List PrefixCut := [⟨5,25480214,25480229⟩,
⟨64,314714357,314714543⟩]
theorem checked40256 : checkPrefixCuts (2^48) 5280366593 10 Manual.Count131072.C040256.packed 64 cuts40256 = true := by
 decide +kernel
def pointBounds40256 : List (Nat × Nat × Nat) := [(5280376832,108946400264335,108946785817578)]
theorem point_links_checked40256 : (cuts40256.take 1).map (fun c => (5280366593-1+2*2^10*c.k,108946374784121+c.lower,108946760337349+c.upper)) = pointBounds40256 := by
 decide +kernel
def cuts40257 : List PrefixCut := [⟨22,109433912,109433975⟩,
⟨64,314866463,314866647⟩]
theorem checked40257 : checkPrefixCuts (2^48) 5280497665 10 Manual.Count131072.C040257.packed 64 cuts40257 = true := by
 decide +kernel
def pointBounds40257 : List (Nat × Nat × Nat) := [(5280542720,108946798932390,108947184485867)]
theorem point_links_checked40257 : (cuts40257.take 1).map (fun c => (5280497665-1+2*2^10*c.k,108946689498478+c.lower,108947075051892+c.upper)) = pointBounds40257 := by
 decide +kernel
def cuts40258 : List PrefixCut := [⟨39,190184704,190184818⟩,
⟨64,310647741,310647921⟩]
theorem checked40258 : checkPrefixCuts (2^48) 5280628737 10 Manual.Count131072.C040258.packed 64 cuts40258 = true := by
 decide +kernel
def pointBounds40258 : List (Nat × Nat × Nat) := [(5280708608,108947194549645,108947580103357)]
theorem point_links_checked40258 : (cuts40258.take 1).map (fun c => (5280628737-1+2*2^10*c.k,108947004364941+c.lower,108947389918539+c.upper)) = pointBounds40258 := by
 decide +kernel
def cuts40259 : List PrefixCut := [⟨56,274502165,274502328⟩,
⟨64,313091891,313092077⟩]
theorem checked40259 : checkPrefixCuts (2^48) 5280759809 10 Manual.Count131072.C040259.packed 64 cuts40259 = true := by
 decide +kernel
def pointBounds40259 : List (Nat × Nat × Nat) := [(5280874496,108947589514847,108947975068788)]
theorem point_links_checked40259 : (cuts40259.take 1).map (fun c => (5280759809-1+2*2^10*c.k,108947315012682+c.lower,108947700566460+c.upper)) = pointBounds40259 := by
 decide +kernel
def cuts40260 : List PrefixCut := [⟨64,313830320,313830504⟩]
theorem checked40260 : checkPrefixCuts (2^48) 5280890881 10 Manual.Count131072.C040260.packed 64 cuts40260 = true := by
 decide +kernel
def cuts40261 : List PrefixCut := [⟨9,45464242,45464269⟩,
⟨64,314568701,314568889⟩]
theorem checked40261 : checkPrefixCuts (2^48) 5281021953 10 Manual.Count131072.C040261.packed 64 cuts40261 = true := by
 decide +kernel
def pointBounds40261 : List (Nat × Nat × Nat) := [(5281040384,108947987399135,108948372953310)]
theorem point_links_checked40261 : (cuts40261.take 1).map (fun c => (5281021953-1+2*2^10*c.k,108947941934893+c.lower,108948327489041+c.upper)) = pointBounds40261 := by
 decide +kernel
def cuts40262 : List PrefixCut := [⟨26,127754664,127754738⟩,
⟨64,315733429,315733611⟩]
theorem checked40262 : checkPrefixCuts (2^48) 5281153025 10 Manual.Count131072.C040262.packed 64 cuts40262 = true := by
 decide +kernel
def pointBounds40262 : List (Nat × Nat × Nat) := [(5281206272,108948384258258,108948769812668)]
theorem point_links_checked40262 : (cuts40262.take 1).map (fun c => (5281153025-1+2*2^10*c.k,108948256503594+c.lower,108948642057930+c.upper)) = pointBounds40262 := by
 decide +kernel
def cuts40263 : List PrefixCut := [⟨43,213184935,213185060⟩,
⟨64,318763459,318763647⟩]
theorem checked40263 : checkPrefixCuts (2^48) 5281284097 10 Manual.Count131072.C040263.packed 64 cuts40263 = true := by
 decide +kernel
def pointBounds40263 : List (Nat × Nat × Nat) := [(5281372160,108948785421958,108949170976601)]
theorem point_links_checked40263 : (cuts40263.take 1).map (fun c => (5281284097-1+2*2^10*c.k,108948572237023+c.lower,108948957791541+c.upper)) = pointBounds40263 := by
 decide +kernel
def cuts40264 : List PrefixCut := [⟨60,294773203,294773379⟩,
⟨64,315344716,315344903⟩]
theorem checked40264 : checkPrefixCuts (2^48) 5281415169 10 Manual.Count131072.C040264.packed 64 cuts40264 = true := by
 decide +kernel
def pointBounds40264 : List (Nat × Nat × Nat) := [(5281538048,108949185773685,108949571328567)]
theorem point_links_checked40264 : (cuts40264.take 1).map (fun c => (5281415169-1+2*2^10*c.k,108948891000482+c.lower,108949276555188+c.upper)) = pointBounds40264 := by
 decide +kernel
def cuts40265 : List PrefixCut := [⟨64,307289562,307289747⟩]
theorem checked40265 : checkPrefixCuts (2^48) 5281546241 10 Manual.Count131072.C040265.packed 64 cuts40265 = true := by
 decide +kernel
def cuts40266 : List PrefixCut := [⟨13,61872682,61872720⟩,
⟨64,310159715,310159900⟩]
theorem checked40266 : checkPrefixCuts (2^48) 5281677313 10 Manual.Count131072.C040266.packed 64 cuts40266 = true := by
 decide +kernel
def pointBounds40266 : List (Nat × Nat × Nat) := [(5281703936,108949575507442,108949961062558)]
theorem point_links_checked40266 : (cuts40266.take 1).map (fun c => (5281677313-1+2*2^10*c.k,108949513634760+c.lower,108949899189838+c.upper)) = pointBounds40266 := by
 decide +kernel
def cuts40267 : List PrefixCut := [⟨30,147509710,147509797⟩,
⟨64,313349483,313349668⟩]
theorem checked40267 : checkPrefixCuts (2^48) 5281808385 10 Manual.Count131072.C040267.packed 64 cuts40267 = true := by
 decide +kernel
def pointBounds40267 : List (Nat × Nat × Nat) := [(5281869824,108949971304185,108950356859535)]
theorem point_links_checked40267 : (cuts40267.take 1).map (fun c => (5281808385-1+2*2^10*c.k,108949823794475+c.lower,108950209349738+c.upper)) = pointBounds40267 := by
 decide +kernel
def cuts40268 : List PrefixCut := [⟨47,229145215,229145354⟩,
⟨64,313554861,313555051⟩]
theorem checked40268 : checkPrefixCuts (2^48) 5281939457 10 Manual.Count131072.C040268.packed 64 cuts40268 = true := by
 decide +kernel
def pointBounds40268 : List (Nat × Nat × Nat) := [(5282035712,108950366289173,108950751844760)]
theorem point_links_checked40268 : (cuts40268.take 1).map (fun c => (5281939457-1+2*2^10*c.k,108950137143958+c.lower,108950522699406+c.upper)) = pointBounds40268 := by
 decide +kernel
def cuts40269 : List PrefixCut := [⟨64,310403036,310403218⟩]
theorem checked40269 : checkPrefixCuts (2^48) 5282070529 10 Manual.Count131072.C040269.packed 64 cuts40269 = true := by
 decide +kernel
def pointBounds40269 : List (Nat × Nat × Nat) := [(5282201600,108950761101855,108951146657675)]
theorem point_links_checked40269 : (cuts40269.take 1).map (fun c => (5282070529-1+2*2^10*c.k,108950450698819+c.lower,108950836254457+c.upper)) = pointBounds40269 := by
 decide +kernel
def cuts40270 : List PrefixCut := [⟨64,312420256,312420438⟩]
theorem checked40270 : checkPrefixCuts (2^48) 5282201601 10 Manual.Count131072.C040270.packed 64 cuts40270 = true := by
 decide +kernel
def cuts40271 : List PrefixCut := [⟨17,82486606,82486655⟩,
⟨64,310334391,310334577⟩]
theorem checked40271 : checkPrefixCuts (2^48) 5282332673 10 Manual.Count131072.C040271.packed 64 cuts40271 = true := by
 decide +kernel
def pointBounds40271 : List (Nat × Nat × Nat) := [(5282367488,108951156008717,108951541564768)]
theorem point_links_checked40271 : (cuts40271.take 1).map (fun c => (5282332673-1+2*2^10*c.k,108951073522111+c.lower,108951459078113+c.upper)) = pointBounds40271 := by
 decide +kernel
def cuts40272 : List PrefixCut := [⟨34,163956174,163956270⟩,
⟨64,309101139,309101323⟩]
theorem checked40272 : checkPrefixCuts (2^48) 5282463745 10 Manual.Count131072.C040272.packed 64 cuts40272 = true := by
 decide +kernel
def pointBounds40272 : List (Nat × Nat × Nat) := [(5282533376,108951547812676,108951933368960)]
theorem point_links_checked40272 : (cuts40272.take 1).map (fun c => (5282463745-1+2*2^10*c.k,108951383856502+c.lower,108951769412690+c.upper)) = pointBounds40272 := by
 decide +kernel
def cuts40273 : List PrefixCut := [⟨51,247818910,247819057⟩,
⟨64,313196250,313196435⟩]
theorem checked40273 : checkPrefixCuts (2^48) 5282594817 10 Manual.Count131072.C040273.packed 64 cuts40273 = true := by
 decide +kernel
def pointBounds40273 : List (Nat × Nat × Nat) := [(5282699264,108951940776551,108952326333070)]
theorem point_links_checked40273 : (cuts40273.take 1).map (fun c => (5282594817-1+2*2^10*c.k,108951692957641+c.lower,108952078514013+c.upper)) = pointBounds40273 := by
 decide +kernel
def cuts40274 : List PrefixCut := [⟨64,316705045,316705231⟩]
theorem checked40274 : checkPrefixCuts (2^48) 5282725889 10 Manual.Count131072.C040274.packed 64 cuts40274 = true := by
 decide +kernel
def cuts40275 : List PrefixCut := [⟨4,18754831,18754842⟩,
⟨64,313553669,313553852⟩]
theorem checked40275 : checkPrefixCuts (2^48) 5282856961 10 Manual.Count131072.C040275.packed 64 cuts40275 = true := by
 decide +kernel
def pointBounds40275 : List (Nat × Nat × Nat) := [(5282865152,108952341613767,108952727170521)]
theorem point_links_checked40275 : (cuts40275.take 1).map (fun c => (5282856961-1+2*2^10*c.k,108952322858936+c.lower,108952708415679+c.upper)) = pointBounds40275 := by
 decide +kernel
def cuts40276 : List PrefixCut := [⟨21,105652788,105652852⟩,
⟨64,310775433,310775619⟩]
theorem checked40276 : checkPrefixCuts (2^48) 5282988033 10 Manual.Count131072.C040276.packed 64 cuts40276 = true := by
 decide +kernel
def pointBounds40276 : List (Nat × Nat × Nat) := [(5283031040,108952742065393,108953127622383)]
theorem point_links_checked40276 : (cuts40276.take 1).map (fun c => (5282988033-1+2*2^10*c.k,108952636412605+c.lower,108953021969531+c.upper)) = pointBounds40276 := by
 decide +kernel
def cuts40277 : List PrefixCut := [⟨38,188390202,188390315⟩,
⟨64,311140662,311140848⟩]
theorem checked40277 : checkPrefixCuts (2^48) 5283119105 10 Manual.Count131072.C040277.packed 64 cuts40277 = true := by
 decide +kernel
def pointBounds40277 : List (Nat × Nat × Nat) := [(5283196928,108953135578240,108953521135465)]
theorem point_links_checked40277 : (cuts40277.take 1).map (fun c => (5283119105-1+2*2^10*c.k,108952947188038+c.lower,108953332745150+c.upper)) = pointBounds40277 := by
 decide +kernel
def cuts40278 : List PrefixCut := [⟨55,267873134,267873295⟩,
⟨64,313796716,313796903⟩]
theorem checked40278 : checkPrefixCuts (2^48) 5283250177 10 Manual.Count131072.C040278.packed 64 cuts40278 = true := by
 decide +kernel
def pointBounds40278 : List (Nat × Nat × Nat) := [(5283362816,108953526201834,108953911759293)]
theorem point_links_checked40278 : (cuts40278.take 1).map (fun c => (5283250177-1+2*2^10*c.k,108953258328700+c.lower,108953643885998+c.upper)) = pointBounds40278 := by
 decide +kernel
def cuts40279 : List PrefixCut := [⟨64,315866663,315866848⟩]
theorem checked40279 : checkPrefixCuts (2^48) 5283381249 10 Manual.Count131072.C040279.packed 64 cuts40279 = true := by
 decide +kernel
def cuts40280 : List PrefixCut := [⟨8,37931170,37931194⟩,
⟨64,317297198,317297387⟩]
theorem checked40280 : checkPrefixCuts (2^48) 5283512321 10 Manual.Count131072.C040280.packed 64 cuts40280 = true := by
 decide +kernel
def pointBounds40280 : List (Nat × Nat × Nat) := [(5283528704,108953925923249,108954311480943)]
theorem point_links_checked40280 : (cuts40280.take 1).map (fun c => (5283512321-1+2*2^10*c.k,108953887992079+c.lower,108954273549749+c.upper)) = pointBounds40280 := by
 decide +kernel
def cuts40281 : List PrefixCut := [⟨25,121621387,121621460⟩,
⟨64,317662189,317662377⟩]
theorem checked40281 : checkPrefixCuts (2^48) 5283643393 10 Manual.Count131072.C040281.packed 64 cuts40281 = true := by
 decide +kernel
def pointBounds40281 : List (Nat × Nat × Nat) := [(5283694592,108954326910664,108954712468596)]
theorem point_links_checked40281 : (cuts40281.take 1).map (fun c => (5283643393-1+2*2^10*c.k,108954205289277+c.lower,108954590847136+c.upper)) = pointBounds40281 := by
 decide +kernel
def cuts40282 : List PrefixCut := [⟨42,200405969,200406089⟩,
⟨64,308385203,308385386⟩]
theorem checked40282 : checkPrefixCuts (2^48) 5283774465 10 Manual.Count131072.C040282.packed 64 cuts40282 = true := by
 decide +kernel
def pointBounds40282 : List (Nat × Nat × Nat) := [(5283860480,108954723357435,108955108915602)]
theorem point_links_checked40282 : (cuts40282.take 1).map (fun c => (5283774465-1+2*2^10*c.k,108954522951466+c.lower,108954908509513+c.upper)) = pointBounds40282 := by
 decide +kernel
def cuts40283 : List PrefixCut := [⟨59,289840040,289840217⟩,
⟨64,314503571,314503763⟩]
theorem checked40283 : checkPrefixCuts (2^48) 5283905537 10 Manual.Count131072.C040283.packed 64 cuts40283 = true := by
 decide +kernel
def pointBounds40283 : List (Nat × Nat × Nat) := [(5284026368,108955121176709,108955506735116)]
theorem point_links_checked40283 : (cuts40283.take 1).map (fun c => (5283905537-1+2*2^10*c.k,108954831336669+c.lower,108955216894899+c.upper)) = pointBounds40283 := by
 decide +kernel
def cuts40284 : List PrefixCut := [⟨64,309381998,309382182⟩]
theorem checked40284 : checkPrefixCuts (2^48) 5284036609 10 Manual.Count131072.C040284.packed 64 cuts40284 = true := by
 decide +kernel
def cuts40285 : List PrefixCut := [⟨12,59233427,59233463⟩,
⟨64,311132145,311132330⟩]
theorem checked40285 : checkPrefixCuts (2^48) 5284167681 10 Manual.Count131072.C040285.packed 64 cuts40285 = true := by
 decide +kernel
def pointBounds40285 : List (Nat × Nat × Nat) := [(5284192256,108955514455665,108955900014307)]
theorem point_links_checked40285 : (cuts40285.take 1).map (fun c => (5284167681-1+2*2^10*c.k,108955455222238+c.lower,108955840780844+c.upper)) = pointBounds40285 := by
 decide +kernel
def cuts40286 : List PrefixCut := [⟨29,140036240,140036322⟩,
⟨64,312189734,312189920⟩]
theorem checked40286 : checkPrefixCuts (2^48) 5284298753 10 Manual.Count131072.C040286.packed 64 cuts40286 = true := by
 decide +kernel
def pointBounds40286 : List (Nat × Nat × Nat) := [(5284358144,108955906390623,108956291949496)]
theorem point_links_checked40286 : (cuts40286.take 1).map (fun c => (5284298753-1+2*2^10*c.k,108955766354383+c.lower,108956151913174+c.upper)) = pointBounds40286 := by
 decide +kernel
def cuts40287 : List PrefixCut := [⟨46,225415253,225415386⟩,
⟨64,313939710,313939894⟩]
theorem checked40287 : checkPrefixCuts (2^48) 5284429825 10 Manual.Count131072.C040287.packed 64 cuts40287 = true := by
 decide +kernel
def pointBounds40287 : List (Nat × Nat × Nat) := [(5284524032,108956303959370,108956689518480)]
theorem point_links_checked40287 : (cuts40287.take 1).map (fun c => (5284429825-1+2*2^10*c.k,108956078544117+c.lower,108956464103094+c.upper)) = pointBounds40287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000008
