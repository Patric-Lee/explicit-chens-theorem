import PlattAssemblyKernel
import PlattCertificates.Count131072.C040288
import PlattCertificates.Count131072.C040289
import PlattCertificates.Count131072.C040290
import PlattCertificates.Count131072.C040291
import PlattCertificates.Count131072.C040292
import PlattCertificates.Count131072.C040293
import PlattCertificates.Count131072.C040294
import PlattCertificates.Count131072.C040295
import PlattCertificates.Count131072.C040296
import PlattCertificates.Count131072.C040297
import PlattCertificates.Count131072.C040298
import PlattCertificates.Count131072.C040299
import PlattCertificates.Count131072.C040300
import PlattCertificates.Count131072.C040301
import PlattCertificates.Count131072.C040302
import PlattCertificates.Count131072.C040303
import PlattCertificates.Count131072.C040304
import PlattCertificates.Count131072.C040305
import PlattCertificates.Count131072.C040306
import PlattCertificates.Count131072.C040307
import PlattCertificates.Count131072.C040308
import PlattCertificates.Count131072.C040309
import PlattCertificates.Count131072.C040310
import PlattCertificates.Count131072.C040311
import PlattCertificates.Count131072.C040312
import PlattCertificates.Count131072.C040313
import PlattCertificates.Count131072.C040314
import PlattCertificates.Count131072.C040315
import PlattCertificates.Count131072.C040316
import PlattCertificates.Count131072.C040317
import PlattCertificates.Count131072.C040318
import PlattCertificates.Count131072.C040319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40288 : List PrefixCut := [⟨63,308658970,308659155⟩,
⟨64,314144989,314145177⟩]
theorem checked40288 : checkPrefixCuts (2^48) 5284560897 10 Manual.Count131072.C040288.packed 64 cuts40288 = true := by
 decide +kernel
def pointBounds40288 : List (Nat × Nat × Nat) := [(5284689920,108956701142797,108957086702143)]
theorem point_links_checked40288 : (cuts40288.take 1).map (fun c => (5284560897-1+2*2^10*c.k,108956392483827+c.lower,108956778042988+c.upper)) = pointBounds40288 := by
 decide +kernel
def cuts40289 : List PrefixCut := [⟨64,312379549,312379730⟩]
theorem checked40289 : checkPrefixCuts (2^48) 5284691969 10 Manual.Count131072.C040289.packed 64 cuts40289 = true := by
 decide +kernel
def cuts40290 : List PrefixCut := [⟨16,79624927,79624974⟩,
⟨64,310614240,310614422⟩]
theorem checked40290 : checkPrefixCuts (2^48) 5284823041 10 Manual.Count131072.C040290.packed 64 cuts40290 = true := by
 decide +kernel
def pointBounds40290 : List (Nat × Nat × Nat) := [(5284855808,108957098633292,108957484192869)]
theorem point_links_checked40290 : (cuts40290.take 1).map (fun c => (5284823041-1+2*2^10*c.k,108957019008365+c.lower,108957404567895+c.upper)) = pointBounds40290 := by
 decide +kernel
def cuts40291 : List PrefixCut := [⟨33,161695308,161695403⟩,
⟨64,311192376,311192559⟩]
theorem checked40291 : checkPrefixCuts (2^48) 5284954113 10 Manual.Count131072.C040291.packed 64 cuts40291 = true := by
 decide +kernel
def pointBounds40291 : List (Nat × Nat × Nat) := [(5285021696,108957491317913,108957876877720)]
theorem point_links_checked40291 : (cuts40291.take 1).map (fun c => (5284954113-1+2*2^10*c.k,108957329622605+c.lower,108957715182317+c.upper)) = pointBounds40291 := by
 decide +kernel
def cuts40292 : List PrefixCut := [⟨50,240991694,240991842⟩,
⟨64,308841331,308841518⟩]
theorem checked40292 : checkPrefixCuts (2^48) 5285085185 10 Manual.Count131072.C040292.packed 64 cuts40292 = true := by
 decide +kernel
def pointBounds40292 : List (Nat × Nat × Nat) := [(5285187584,108957881806675,108958267366718)]
theorem point_links_checked40292 : (cuts40292.take 1).map (fun c => (5285085185-1+2*2^10*c.k,108957640814981+c.lower,108958026374876+c.upper)) = pointBounds40292 := by
 decide +kernel
def cuts40293 : List PrefixCut := [⟨64,316715598,316715785⟩]
theorem checked40293 : checkPrefixCuts (2^48) 5285216257 10 Manual.Count131072.C040293.packed 64 cuts40293 = true := by
 decide +kernel
def cuts40294 : List PrefixCut := [⟨3,14432288,14432296⟩,
⟨64,313778746,313778932⟩]
theorem checked40294 : checkPrefixCuts (2^48) 5285347329 10 Manual.Count131072.C040294.packed 64 cuts40294 = true := by
 decide +kernel
def pointBounds40294 : List (Nat × Nat × Nat) := [(5285353472,108958280804198,108958666364475)]
theorem point_links_checked40294 : (cuts40294.take 1).map (fun c => (5285347329-1+2*2^10*c.k,108958266371910+c.lower,108958651932179+c.upper)) = pointBounds40294 := by
 decide +kernel
def cuts40295 : List PrefixCut := [⟨20,98786502,98786560⟩,
⟨64,311321298,311321482⟩]
theorem checked40295 : checkPrefixCuts (2^48) 5285478401 10 Manual.Count131072.C040295.packed 64 cuts40295 = true := by
 decide +kernel
def pointBounds40295 : List (Nat × Nat × Nat) := [(5285519360,108958678937158,108959064497671)]
theorem point_links_checked40295 : (cuts40295.take 1).map (fun c => (5285478401-1+2*2^10*c.k,108958580150656+c.lower,108958965711111+c.upper)) = pointBounds40295 := by
 decide +kernel
def cuts40296 : List PrefixCut := [⟨37,178023722,178023830⟩,
⟨64,313230604,313230792⟩]
theorem checked40296 : checkPrefixCuts (2^48) 5285609473 10 Manual.Count131072.C040296.packed 64 cuts40296 = true := by
 decide +kernel
def pointBounds40296 : List (Nat × Nat × Nat) := [(5285685248,108959069495676,108959455056423)]
theorem point_links_checked40296 : (cuts40296.take 1).map (fun c => (5285609473-1+2*2^10*c.k,108958891471954+c.lower,108959277032593+c.upper)) = pointBounds40296 := by
 decide +kernel
def cuts40297 : List PrefixCut := [⟨54,266628691,266628846⟩,
⟨64,316258177,316258362⟩]
theorem checked40297 : checkPrefixCuts (2^48) 5285740545 10 Manual.Count131072.C040297.packed 64 cuts40297 = true := by
 decide +kernel
def pointBounds40297 : List (Nat × Nat × Nat) := [(5285851136,108959471331249,108959856892231)]
theorem point_links_checked40297 : (cuts40297.take 1).map (fun c => (5285740545-1+2*2^10*c.k,108959204702558+c.lower,108959590263385+c.upper)) = pointBounds40297 := by
 decide +kernel
def cuts40298 : List PrefixCut := [⟨64,308582363,308582547⟩]
theorem checked40298 : checkPrefixCuts (2^48) 5285871617 10 Manual.Count131072.C040298.packed 64 cuts40298 = true := by
 decide +kernel
def cuts40299 : List PrefixCut := [⟨7,35144360,35144381⟩,
⟨64,316295741,316295926⟩]
theorem checked40299 : checkPrefixCuts (2^48) 5286002689 10 Manual.Count131072.C040299.packed 64 cuts40299 = true := by
 decide +kernel
def pointBounds40299 : List (Nat × Nat × Nat) := [(5286017024,108959864687458,108960250248675)]
theorem point_links_checked40299 : (cuts40299.take 1).map (fun c => (5286002689-1+2*2^10*c.k,108959829543098+c.lower,108960215104294+c.upper)) = pointBounds40299 := by
 decide +kernel
def cuts40300 : List PrefixCut := [⟨24,117304320,117304390⟩,
⟨64,313785272,313785455⟩]
theorem checked40300 : checkPrefixCuts (2^48) 5286133761 10 Manual.Count131072.C040300.packed 64 cuts40300 = true := by
 decide +kernel
def pointBounds40300 : List (Nat × Nat × Nat) := [(5286182912,108960263143159,108960648704610)]
theorem point_links_checked40300 : (cuts40300.take 1).map (fun c => (5286133761-1+2*2^10*c.k,108960145838839+c.lower,108960531400220+c.upper)) = pointBounds40300 := by
 decide +kernel
def cuts40301 : List PrefixCut := [⟨41,199193407,199193525⟩,
⟨64,310689230,310689412⟩]
theorem checked40301 : checkPrefixCuts (2^48) 5286264833 10 Manual.Count131072.C040301.packed 64 cuts40301 = true := by
 decide +kernel
def pointBounds40301 : List (Nat × Nat × Nat) := [(5286348800,108960658817518,108961044379200)]
theorem point_links_checked40301 : (cuts40301.take 1).map (fun c => (5286264833-1+2*2^10*c.k,108960459624111+c.lower,108960845185675+c.upper)) = pointBounds40301 := by
 decide +kernel
def cuts40302 : List PrefixCut := [⟨58,282622068,282622234⟩,
⟨64,311746471,311746655⟩]
theorem checked40302 : checkPrefixCuts (2^48) 5286395905 10 Manual.Count131072.C040302.packed 64 cuts40302 = true := by
 decide +kernel
def pointBounds40302 : List (Nat × Nat × Nat) := [(5286514688,108961052935409,108961438497321)]
theorem point_links_checked40302 : (cuts40302.take 1).map (fun c => (5286395905-1+2*2^10*c.k,108960770313341+c.lower,108961155875087+c.upper)) = pointBounds40302 := by
 decide +kernel
def cuts40303 : List PrefixCut := [⟨64,309182987,309183171⟩]
theorem checked40303 : checkPrefixCuts (2^48) 5286526977 10 Manual.Count131072.C040303.packed 64 cuts40303 = true := by
 decide +kernel
def cuts40304 : List PrefixCut := [⟨11,52550237,52550268⟩,
⟨64,308589714,308589894⟩]
theorem checked40304 : checkPrefixCuts (2^48) 5286658049 10 Manual.Count131072.C040304.packed 64 cuts40304 = true := by
 decide +kernel
def pointBounds40304 : List (Nat × Nat × Nat) := [(5286680576,108961443793036,108961829355181)]
theorem point_links_checked40304 : (cuts40304.take 1).map (fun c => (5286658049-1+2*2^10*c.k,108961391242799+c.lower,108961776804913+c.upper)) = pointBounds40304 := by
 decide +kernel
def cuts40305 : List PrefixCut := [⟨28,134433251,134433334⟩,
⟨64,311084344,311084532⟩]
theorem checked40305 : checkPrefixCuts (2^48) 5286789121 10 Manual.Count131072.C040305.packed 64 cuts40305 = true := by
 decide +kernel
def pointBounds40305 : List (Nat × Nat × Nat) := [(5286846464,108961834265764,108962219828141)]
theorem point_links_checked40305 : (cuts40305.take 1).map (fun c => (5286789121-1+2*2^10*c.k,108961699832513+c.lower,108962085394807+c.upper)) = pointBounds40305 := by
 decide +kernel
def cuts40306 : List PrefixCut := [⟨45,218175055,218175180⟩,
⟨64,311183130,311183310⟩]
theorem checked40306 : checkPrefixCuts (2^48) 5286920193 10 Manual.Count131072.C040306.packed 64 cuts40306 = true := by
 decide +kernel
def pointBounds40306 : List (Nat × Nat × Nat) := [(5287012352,108962229091912,108962614654519)]
theorem point_links_checked40306 : (cuts40306.take 1).map (fun c => (5286920193-1+2*2^10*c.k,108962010916857+c.lower,108962396479339+c.upper)) = pointBounds40306 := by
 decide +kernel
def cuts40307 : List PrefixCut := [⟨62,301113564,301113744⟩,
⟨64,311441589,311441775⟩]
theorem checked40307 : checkPrefixCuts (2^48) 5287051265 10 Manual.Count131072.C040307.packed 64 cuts40307 = true := by
 decide +kernel
def pointBounds40307 : List (Nat × Nat × Nat) := [(5287178240,108962623213551,108963008776393)]
theorem point_links_checked40307 : (cuts40307.take 1).map (fun c => (5287051265-1+2*2^10*c.k,108962322099987+c.lower,108962707662649+c.upper)) = pointBounds40307 := by
 decide +kernel
def cuts40308 : List PrefixCut := [⟨64,314681273,314681455⟩]
theorem checked40308 : checkPrefixCuts (2^48) 5287182337 10 Manual.Count131072.C040308.packed 64 cuts40308 = true := by
 decide +kernel
def cuts40309 : List PrefixCut := [⟨15,71815023,71815068⟩,
⟨64,306209096,306209282⟩]
theorem checked40309 : checkPrefixCuts (2^48) 5287313409 10 Manual.Count131072.C040309.packed 64 cuts40309 = true := by
 decide +kernel
def pointBounds40309 : List (Nat × Nat × Nat) := [(5287344128,108963020037872,108963405600947)]
theorem point_links_checked40309 : (cuts40309.take 1).map (fun c => (5287313409-1+2*2^10*c.k,108962948222849+c.lower,108963333785879+c.upper)) = pointBounds40309 := by
 decide +kernel
def cuts40310 : List PrefixCut := [⟨32,156455464,156455559⟩,
⟨64,310460238,310460421⟩]
theorem checked40310 : checkPrefixCuts (2^48) 5287444481 10 Manual.Count131072.C040310.packed 64 cuts40310 = true := by
 decide +kernel
def pointBounds40310 : List (Nat × Nat × Nat) := [(5287510016,108963410887409,108963796450720)]
theorem point_links_checked40310 : (cuts40310.take 1).map (fun c => (5287444481-1+2*2^10*c.k,108963254431945+c.lower,108963639995161+c.upper)) = pointBounds40310 := by
 decide +kernel
def cuts40311 : List PrefixCut := [⟨49,241623475,241623619⟩,
⟨64,316095178,316095365⟩]
theorem checked40311 : checkPrefixCuts (2^48) 5287575553 10 Manual.Count131072.C040311.packed 64 cuts40311 = true := by
 decide +kernel
def pointBounds40311 : List (Nat × Nat × Nat) := [(5287675904,108963806515658,108964192079201)]
theorem point_links_checked40311 : (cuts40311.take 1).map (fun c => (5287575553-1+2*2^10*c.k,108963564892183+c.lower,108963950455582+c.upper)) = pointBounds40311 := by
 decide +kernel
def cuts40312 : List PrefixCut := [⟨64,314117786,314117969⟩]
theorem checked40312 : checkPrefixCuts (2^48) 5287706625 10 Manual.Count131072.C040312.packed 64 cuts40312 = true := by
 decide +kernel
def cuts40313 : List PrefixCut := [⟨2,9528277,9528283⟩,
⟨64,312726044,312726231⟩]
theorem checked40313 : checkPrefixCuts (2^48) 5287837697 10 Manual.Count131072.C040313.packed 64 cuts40313 = true := by
 decide +kernel
def pointBounds40313 : List (Nat × Nat × Nat) := [(5287841792,108964204633424,108964590197199)]
theorem point_links_checked40313 : (cuts40313.take 1).map (fun c => (5287837697-1+2*2^10*c.k,108964195105147+c.lower,108964580668916+c.upper)) = pointBounds40313 := by
 decide +kernel
def cuts40314 : List PrefixCut := [⟨19,89691048,89691101⟩,
⟨64,306117932,306118110⟩]
theorem checked40314 : checkPrefixCuts (2^48) 5287968769 10 Manual.Count131072.C040314.packed 64 cuts40314 = true := by
 decide +kernel
def pointBounds40314 : List (Nat × Nat × Nat) := [(5288007680,108964597522239,108964983086248)]
theorem point_links_checked40314 : (cuts40314.take 1).map (fun c => (5287968769-1+2*2^10*c.k,108964507831191+c.lower,108964893395147+c.upper)) = pointBounds40314 := by
 decide +kernel
def cuts40315 : List PrefixCut := [⟨36,176130180,176130283⟩,
⟨64,314254122,314254306⟩]
theorem checked40315 : checkPrefixCuts (2^48) 5288099841 10 Manual.Count131072.C040315.packed 64 cuts40315 = true := by
 decide +kernel
def pointBounds40315 : List (Nat × Nat × Nat) := [(5288173568,108964990079303,108965375643540)]
theorem point_links_checked40315 : (cuts40315.take 1).map (fun c => (5288099841-1+2*2^10*c.k,108964813949123+c.lower,108965199513257+c.upper)) = pointBounds40315 := by
 decide +kernel
def cuts40316 : List PrefixCut := [⟨53,253782136,253782286⟩,
⟨64,307859202,307859384⟩]
theorem checked40316 : checkPrefixCuts (2^48) 5288230913 10 Manual.Count131072.C040316.packed 64 cuts40316 = true := by
 decide +kernel
def pointBounds40316 : List (Nat × Nat × Nat) := [(5288339456,108965381985381,108965767549849)]
theorem point_links_checked40316 : (cuts40316.take 1).map (fun c => (5288230913-1+2*2^10*c.k,108965128203245+c.lower,108965513767563+c.upper)) = pointBounds40316 := by
 decide +kernel
def cuts40317 : List PrefixCut := [⟨64,315835289,315835474⟩]
theorem checked40317 : checkPrefixCuts (2^48) 5288361985 10 Manual.Count131072.C040317.packed 64 cuts40317 = true := by
 decide +kernel
def cuts40318 : List PrefixCut := [⟨6,29486078,29486095⟩,
⟨64,311409931,311410113⟩]
theorem checked40318 : checkPrefixCuts (2^48) 5288493057 10 Manual.Count131072.C040318.packed 64 cuts40318 = true := by
 decide +kernel
def pointBounds40318 : List (Nat × Nat × Nat) := [(5288505344,108965781383814,108966166948516)]
theorem point_links_checked40318 : (cuts40318.take 1).map (fun c => (5288493057-1+2*2^10*c.k,108965751897736+c.lower,108966137462421+c.upper)) = pointBounds40318 := by
 decide +kernel
def cuts40319 : List PrefixCut := [⟨23,107722274,107722337⟩,
⟨64,308262051,308262238⟩]
theorem checked40319 : checkPrefixCuts (2^48) 5288624129 10 Manual.Count131072.C040319.packed 64 cuts40319 = true := by
 decide +kernel
def pointBounds40319 : List (Nat × Nat × Nat) := [(5288671232,108966171029941,108966556594871)]
theorem point_links_checked40319 : (cuts40319.take 1).map (fun c => (5288624129-1+2*2^10*c.k,108966063307667+c.lower,108966448872534+c.upper)) = pointBounds40319 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000009
