import PlattAssemblyKernel
import PlattCertificates.Count131072.C059312
import PlattCertificates.Count131072.C059313
import PlattCertificates.Count131072.C059314
import PlattCertificates.Count131072.C059315
import PlattCertificates.Count131072.C059316
import PlattCertificates.Count131072.C059317
import PlattCertificates.Count131072.C059318
import PlattCertificates.Count131072.C059319
import PlattCertificates.Count131072.C059320
import PlattCertificates.Count131072.C059321
import PlattCertificates.Count131072.C059322
import PlattCertificates.Count131072.C059323
import PlattCertificates.Count131072.C059324
import PlattCertificates.Count131072.C059325
import PlattCertificates.Count131072.C059326
import PlattCertificates.Count131072.C059327
import PlattCertificates.Count131072.C059328
import PlattCertificates.Count131072.C059329
import PlattCertificates.Count131072.C059330
import PlattCertificates.Count131072.C059331
import PlattCertificates.Count131072.C059332
import PlattCertificates.Count131072.C059333
import PlattCertificates.Count131072.C059334
import PlattCertificates.Count131072.C059335
import PlattCertificates.Count131072.C059336
import PlattCertificates.Count131072.C059337
import PlattCertificates.Count131072.C059338
import PlattCertificates.Count131072.C059339
import PlattCertificates.Count131072.C059340
import PlattCertificates.Count131072.C059341
import PlattCertificates.Count131072.C059342
import PlattCertificates.Count131072.C059343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000291
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59312 : List PrefixCut := [⟨64,207537856,207537977⟩]
theorem checked59312 : checkPrefixCuts (2^48) 7778074625 10 Manual.Count131072.C059312.packed 64 cuts59312 = true := by
 decide +kernel
def cuts59313 : List PrefixCut := [⟨52,168814180,168814279⟩,
⟨64,208113355,208113475⟩]
theorem checked59313 : checkPrefixCuts (2^48) 7778205697 10 Manual.Count131072.C059313.packed 64 cuts59313 = true := by
 decide +kernel
def pointBounds59313 : List (Nat × Nat × Nat) := [(7778312192,113774728497477,113775116823661)]
theorem point_links_checked59313 : (cuts59313.take 1).map (fun c => (7778205697-1+2*2^10*c.k,113774559683297+c.lower,113774948009382+c.upper)) = pointBounds59313 := by
 decide +kernel
def cuts59314 : List PrefixCut := [⟨64,207386123,207386239⟩]
theorem checked59314 : checkPrefixCuts (2^48) 7778336769 10 Manual.Count131072.C059314.packed 64 cuts59314 = true := by
 decide +kernel
def cuts59315 : List PrefixCut := [⟨43,140076836,140076915⟩,
⟨64,207165510,207165628⟩]
theorem checked59315 : checkPrefixCuts (2^48) 7778467841 10 Manual.Count131072.C059315.packed 64 cuts59315 = true := by
 decide +kernel
def pointBounds59315 : List (Nat × Nat × Nat) := [(7778555904,113775115259611,113775503586011)]
theorem point_links_checked59315 : (cuts59315.take 1).map (fun c => (7778467841-1+2*2^10*c.k,113774975182775+c.lower,113775363509096+c.upper)) = pointBounds59315 := by
 decide +kernel
def cuts59316 : List PrefixCut := [⟨64,209984484,209984610⟩]
theorem checked59316 : checkPrefixCuts (2^48) 7778598913 10 Manual.Count131072.C059316.packed 64 cuts59316 = true := by
 decide +kernel
def cuts59317 : List PrefixCut := [⟨34,109134070,109134132⟩,
⟨64,206072973,206073092⟩]
theorem checked59317 : checkPrefixCuts (2^48) 7778729985 10 Manual.Count131072.C059317.packed 64 cuts59317 = true := by
 decide +kernel
def pointBounds59317 : List (Nat × Nat × Nat) := [(7778799616,113775501466839,113775889793466)]
theorem point_links_checked59317 : (cuts59317.take 1).map (fun c => (7778729985-1+2*2^10*c.k,113775392332769+c.lower,113775780659334+c.upper)) = pointBounds59317 := by
 decide +kernel
def cuts59318 : List PrefixCut := [⟨64,209181359,209181476⟩]
theorem checked59318 : checkPrefixCuts (2^48) 7778861057 10 Manual.Count131072.C059318.packed 64 cuts59318 = true := by
 decide +kernel
def cuts59319 : List PrefixCut := [⟨25,80762376,80762422⟩,
⟨64,206464049,206464169⟩]
theorem checked59319 : checkPrefixCuts (2^48) 7778992129 10 Manual.Count131072.C059319.packed 64 cuts59319 = true := by
 decide +kernel
def pointBounds59319 : List (Nat × Nat × Nat) := [(7779043328,113775888349477,113776276676324)]
theorem point_links_checked59319 : (cuts59319.take 1).map (fun c => (7778992129-1+2*2^10*c.k,113775807587101+c.lower,113776195913902+c.upper)) = pointBounds59319 := by
 decide +kernel
def cuts59320 : List PrefixCut := [⟨64,209753221,209753343⟩]
theorem checked59320 : checkPrefixCuts (2^48) 7779123201 10 Manual.Count131072.C059320.packed 64 cuts59320 = true := by
 decide +kernel
def cuts59321 : List PrefixCut := [⟨16,51126132,51126159⟩,
⟨64,206674185,206674300⟩]
theorem checked59321 : checkPrefixCuts (2^48) 7779254273 10 Manual.Count131072.C059321.packed 64 cuts59321 = true := by
 decide +kernel
def pointBounds59321 : List (Nat × Nat × Nat) := [(7779287040,113776274930503,113776663257573)]
theorem point_links_checked59321 : (cuts59321.take 1).map (fun c => (7779254273-1+2*2^10*c.k,113776223804371+c.lower,113776612131414+c.upper)) = pointBounds59321 := by
 decide +kernel
def cuts59322 : List PrefixCut := [⟨64,209601427,209601549⟩]
theorem checked59322 : checkPrefixCuts (2^48) 7779385345 10 Manual.Count131072.C059322.packed 64 cuts59322 = true := by
 decide +kernel
def cuts59323 : List PrefixCut := [⟨7,22577260,22577273⟩,
⟨64,207137587,207137705⟩]
theorem checked59323 : checkPrefixCuts (2^48) 7779516417 10 Manual.Count131072.C059323.packed 64 cuts59323 = true := by
 decide +kernel
def pointBounds59323 : List (Nat × Nat × Nat) := [(7779530752,113776662657243,113777050984536)]
theorem point_links_checked59323 : (cuts59323.take 1).map (fun c => (7779516417-1+2*2^10*c.k,113776640079983+c.lower,113777028407263+c.upper)) = pointBounds59323 := by
 decide +kernel
def cuts59324 : List PrefixCut := [⟨62,202105034,202105153⟩,
⟨64,208798396,208798518⟩]
theorem checked59324 : checkPrefixCuts (2^48) 7779647489 10 Manual.Count131072.C059324.packed 64 cuts59324 = true := by
 decide +kernel
def pointBounds59324 : List (Nat × Nat × Nat) := [(7779774464,113777049322604,113777437650121)]
theorem point_links_checked59324 : (cuts59324.take 1).map (fun c => (7779647489-1+2*2^10*c.k,113776847217570+c.lower,113777235544968+c.upper)) = pointBounds59324 := by
 decide +kernel
def cuts59325 : List PrefixCut := [⟨64,206696435,206696557⟩]
theorem checked59325 : checkPrefixCuts (2^48) 7779778561 10 Manual.Count131072.C059325.packed 64 cuts59325 = true := by
 decide +kernel
def cuts59326 : List PrefixCut := [⟨53,172358956,172359053⟩,
⟨64,207597454,207597572⟩]
theorem checked59326 : checkPrefixCuts (2^48) 7779909633 10 Manual.Count131072.C059326.packed 64 cuts59326 = true := by
 decide +kernel
def pointBounds59326 : List (Nat × Nat × Nat) := [(7780018176,113777435071357,113777823399096)]
theorem point_links_checked59326 : (cuts59326.take 1).map (fun c => (7779909633-1+2*2^10*c.k,113777262712401+c.lower,113777651040043+c.upper)) = pointBounds59326 := by
 decide +kernel
def cuts59327 : List PrefixCut := [⟨64,210777672,210777792⟩]
theorem checked59327 : checkPrefixCuts (2^48) 7780040705 10 Manual.Count131072.C059327.packed 64 cuts59327 = true := by
 decide +kernel
def cuts59328 : List PrefixCut := [⟨44,142904225,142904309⟩,
⟨64,206179509,206179629⟩]
theorem checked59328 : checkPrefixCuts (2^48) 7780171777 10 Manual.Count131072.C059328.packed 64 cuts59328 = true := by
 decide +kernel
def pointBounds59328 : List (Nat × Nat × Nat) := [(7780261888,113777823991752,113778212319716)]
theorem point_links_checked59328 : (cuts59328.take 1).map (fun c => (7780171777-1+2*2^10*c.k,113777681087527+c.lower,113778069415407+c.upper)) = pointBounds59328 := by
 decide +kernel
def cuts59329 : List PrefixCut := [⟨64,209142587,209142703⟩]
theorem checked59329 : checkPrefixCuts (2^48) 7780302849 10 Manual.Count131072.C059329.packed 64 cuts59329 = true := by
 decide +kernel
def cuts59330 : List PrefixCut := [⟨35,114102604,114102665⟩,
⟨64,210224371,210224487⟩]
theorem checked59330 : checkPrefixCuts (2^48) 7780433921 10 Manual.Count131072.C059330.packed 64 cuts59330 = true := by
 decide +kernel
def pointBounds59330 : List (Nat × Nat × Nat) := [(7780505600,113778210512227,113778598840404)]
theorem point_links_checked59330 : (cuts59330.take 1).map (fun c => (7780433921-1+2*2^10*c.k,113778096409623+c.lower,113778484737739+c.upper)) = pointBounds59330 := by
 decide +kernel
def cuts59331 : List PrefixCut := [⟨64,208520543,208520662⟩]
theorem checked59331 : checkPrefixCuts (2^48) 7780564993 10 Manual.Count131072.C059331.packed 64 cuts59331 = true := by
 decide +kernel
def cuts59332 : List PrefixCut := [⟨26,86171070,86171118⟩,
⟨64,211411097,211411214⟩]
theorem checked59332 : checkPrefixCuts (2^48) 7780696065 10 Manual.Count131072.C059332.packed 64 cuts59332 = true := by
 decide +kernel
def pointBounds59332 : List (Nat × Nat × Nat) := [(7780749312,113778601325607,113778989654006)]
theorem point_links_checked59332 : (cuts59332.take 1).map (fun c => (7780696065-1+2*2^10*c.k,113778515154537+c.lower,113778903482888+c.upper)) = pointBounds59332 := by
 decide +kernel
def cuts59333 : List PrefixCut := [⟨64,211262811,211262930⟩]
theorem checked59333 : checkPrefixCuts (2^48) 7780827137 10 Manual.Count131072.C059333.packed 64 cuts59333 = true := by
 decide +kernel
def cuts59334 : List PrefixCut := [⟨17,55057979,55058010⟩,
⟨64,207858868,207858983⟩]
theorem checked59334 : checkPrefixCuts (2^48) 7780958209 10 Manual.Count131072.C059334.packed 64 cuts59334 = true := by
 decide +kernel
def pointBounds59334 : List (Nat × Nat × Nat) := [(7780993024,113778992886424,113779381215042)]
theorem point_links_checked59334 : (cuts59334.take 1).map (fun c => (7780958209-1+2*2^10*c.k,113778937828445+c.lower,113779326157032+c.upper)) = pointBounds59334 := by
 decide +kernel
def cuts59335 : List PrefixCut := [⟨64,208542661,208542786⟩]
theorem checked59335 : checkPrefixCuts (2^48) 7781089281 10 Manual.Count131072.C059335.packed 64 cuts59335 = true := by
 decide +kernel
def cuts59336 : List PrefixCut := [⟨8,25755589,25755604⟩,
⟨64,207490122,207490237⟩]
theorem checked59336 : checkPrefixCuts (2^48) 7781220353 10 Manual.Count131072.C059336.packed 64 cuts59336 = true := by
 decide +kernel
def pointBounds59336 : List (Nat × Nat × Nat) := [(7781236736,113779379985563,113779768314405)]
theorem point_links_checked59336 : (cuts59336.take 1).map (fun c => (7781220353-1+2*2^10*c.k,113779354229974+c.lower,113779742558801+c.upper)) = pointBounds59336 := by
 decide +kernel
def cuts59337 : List PrefixCut := [⟨63,204918389,204918507⟩,
⟨64,207450457,207450577⟩]
theorem checked59337 : checkPrefixCuts (2^48) 7781351425 10 Manual.Count131072.C059337.packed 64 cuts59337 = true := by
 decide +kernel
def pointBounds59337 : List (Nat × Nat × Nat) := [(7781480448,113779766638485,113780154967545)]
theorem point_links_checked59337 : (cuts59337.take 1).map (fun c => (7781351425-1+2*2^10*c.k,113779561720096+c.lower,113779950049038+c.upper)) = pointBounds59337 := by
 decide +kernel
def cuts59338 : List PrefixCut := [⟨64,208532126,208532252⟩]
theorem checked59338 : checkPrefixCuts (2^48) 7781482497 10 Manual.Count131072.C059338.packed 64 cuts59338 = true := by
 decide +kernel
def cuts59339 : List PrefixCut := [⟨54,176372397,176372497⟩,
⟨64,208094564,208094684⟩]
theorem checked59339 : checkPrefixCuts (2^48) 7781613569 10 Manual.Count131072.C059339.packed 64 cuts59339 = true := by
 decide +kernel
def pointBounds59339 : List (Nat × Nat × Nat) := [(7781724160,113780154075076,113780542404364)]
theorem point_links_checked59339 : (cuts59339.take 1).map (fun c => (7781613569-1+2*2^10*c.k,113779977702679+c.lower,113780366031867+c.upper)) = pointBounds59339 := by
 decide +kernel
def cuts59340 : List PrefixCut := [⟨64,208850635,208850754⟩]
theorem checked59340 : checkPrefixCuts (2^48) 7781744641 10 Manual.Count131072.C059340.packed 64 cuts59340 = true := by
 decide +kernel
def cuts59341 : List PrefixCut := [⟨45,146779311,146779393⟩,
⟨64,209968395,209968512⟩]
theorem checked59341 : checkPrefixCuts (2^48) 7781875713 10 Manual.Count131072.C059341.packed 64 cuts59341 = true := by
 decide +kernel
def pointBounds59341 : List (Nat × Nat × Nat) := [(7781967872,113780541427189,113780929756698)]
theorem point_links_checked59341 : (cuts59341.take 1).map (fun c => (7781875713-1+2*2^10*c.k,113780394647878+c.lower,113780782977305+c.upper)) = pointBounds59341 := by
 decide +kernel
def cuts59342 : List PrefixCut := [⟨64,209277658,209277774⟩]
theorem checked59342 : checkPrefixCuts (2^48) 7782006785 10 Manual.Count131072.C059342.packed 64 cuts59342 = true := by
 decide +kernel
def cuts59343 : List PrefixCut := [⟨36,116790290,116790358⟩,
⟨64,208152870,208152991⟩]
theorem checked59343 : checkPrefixCuts (2^48) 7782137857 10 Manual.Count131072.C059343.packed 64 cuts59343 = true := by
 decide +kernel
def pointBounds59343 : List (Nat × Nat × Nat) := [(7782211584,113780930684221,113781319013949)]
theorem point_links_checked59343 : (cuts59343.take 1).map (fun c => (7782137857-1+2*2^10*c.k,113780813893931+c.lower,113781202223591+c.upper)) = pointBounds59343 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000291
