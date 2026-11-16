import PlattAssemblyKernel
import PlattCertificates.Count131072.C039280
import PlattCertificates.Count131072.C039281
import PlattCertificates.Count131072.C039282
import PlattCertificates.Count131072.C039283
import PlattCertificates.Count131072.C039284
import PlattCertificates.Count131072.C039285
import PlattCertificates.Count131072.C039286
import PlattCertificates.Count131072.C039287
import PlattCertificates.Count131072.C039288
import PlattCertificates.Count131072.C039289
import PlattCertificates.Count131072.C039290
import PlattCertificates.Count131072.C039291
import PlattCertificates.Count131072.C039292
import PlattCertificates.Count131072.C039293
import PlattCertificates.Count131072.C039294
import PlattCertificates.Count131072.C039295
import PlattCertificates.Count131072.C039296
import PlattCertificates.Count131072.C039297
import PlattCertificates.Count131072.C039298
import PlattCertificates.Count131072.C039299
import PlattCertificates.Count131072.C039300
import PlattCertificates.Count131072.C039301
import PlattCertificates.Count131072.C039302
import PlattCertificates.Count131072.C039303
import PlattCertificates.Count131072.C039304
import PlattCertificates.Count131072.C039305
import PlattCertificates.Count131072.C039306
import PlattCertificates.Count131072.C039307
import PlattCertificates.Count131072.C039308
import PlattCertificates.Count131072.C039309
import PlattCertificates.Count131072.C039310
import PlattCertificates.Count131072.C039311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000290
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39280 : List PrefixCut := [⟨64,320889205,320889392⟩]
theorem checked39280 : checkPrefixCuts (2^48) 5152440321 10 Manual.Count131072.C039280.packed 64 cuts39280 = true := by
 decide +kernel
def cuts39281 : List PrefixCut := [⟨14,69377423,69377465⟩,
⟨64,318477447,318477640⟩]
theorem checked39281 : checkPrefixCuts (2^48) 5152571393 10 Manual.Count131072.C039281.packed 64 cuts39281 = true := by
 decide +kernel
def pointBounds39281 : List (Nat × Nat × Nat) := [(5152600064,108638261105958,108638646475801)]
theorem point_links_checked39281 : (cuts39281.take 1).map (fun c => (5152571393-1+2*2^10*c.k,108638191728535+c.lower,108638577098336+c.upper)) = pointBounds39281 := by
 decide +kernel
def cuts39282 : List PrefixCut := [⟨29,143995024,143995110⟩,
⟨64,317759199,317759392⟩]
theorem checked39282 : checkPrefixCuts (2^48) 5152702465 10 Manual.Count131072.C039282.packed 64 cuts39282 = true := by
 decide +kernel
def pointBounds39282 : List (Nat × Nat × Nat) := [(5152761856,108638654201006,108639039571086)]
theorem point_links_checked39282 : (cuts39282.take 1).map (fun c => (5152702465-1+2*2^10*c.k,108638510205982+c.lower,108638895575976+c.upper)) = pointBounds39282 := by
 decide +kernel
def cuts39283 : List PrefixCut := [⟨44,221940492,221940624⟩,
⟨64,321793328,321793519⟩]
theorem checked39283 : checkPrefixCuts (2^48) 5152833537 10 Manual.Count131072.C039283.packed 64 cuts39283 = true := by
 decide +kernel
def pointBounds39283 : List (Nat × Nat × Nat) := [(5152923648,108639049905673,108639435275992)]
theorem point_links_checked39283 : (cuts39283.take 1).map (fun c => (5152833537-1+2*2^10*c.k,108638827965181+c.lower,108639213335368+c.upper)) = pointBounds39283 := by
 decide +kernel
def cuts39284 : List PrefixCut := [⟨59,296768019,296768193⟩,
⟨64,322331367,322331556⟩]
theorem checked39284 : checkPrefixCuts (2^48) 5152964609 10 Manual.Count131072.C039284.packed 64 cuts39284 = true := by
 decide +kernel
def pointBounds39284 : List (Nat × Nat × Nat) := [(5153085440,108639446526528,108639831897080)]
theorem point_links_checked39284 : (cuts39284.take 1).map (fun c => (5152964609-1+2*2^10*c.k,108639149758509+c.lower,108639535128887+c.upper)) = pointBounds39284 := by
 decide +kernel
def cuts39285 : List PrefixCut := [⟨64,320302196,320302388⟩]
theorem checked39285 : checkPrefixCuts (2^48) 5153095681 10 Manual.Count131072.C039285.packed 64 cuts39285 = true := by
 decide +kernel
def cuts39286 : List PrefixCut := [⟨10,49923585,49923615⟩,
⟨64,321987284,321987473⟩]
theorem checked39286 : checkPrefixCuts (2^48) 5153226753 10 Manual.Count131072.C039286.packed 64 cuts39286 = true := by
 decide +kernel
def pointBounds39286 : List (Nat × Nat × Nat) := [(5153247232,108639842315657,108640227686446)]
theorem point_links_checked39286 : (cuts39286.take 1).map (fun c => (5153226753-1+2*2^10*c.k,108639792392072+c.lower,108640177762831+c.upper)) = pointBounds39286 := by
 decide +kernel
def cuts39287 : List PrefixCut := [⟨25,126443986,126444063⟩,
⟨64,318264992,318265187⟩]
theorem checked39287 : checkPrefixCuts (2^48) 5153357825 10 Manual.Count131072.C039287.packed 64 cuts39287 = true := by
 decide +kernel
def pointBounds39287 : List (Nat × Nat × Nat) := [(5153409024,108640240823342,108640626194367)]
theorem point_links_checked39287 : (cuts39287.take 1).map (fun c => (5153357825-1+2*2^10*c.k,108640114379356+c.lower,108640499750304+c.upper)) = pointBounds39287 := by
 decide +kernel
def cuts39288 : List PrefixCut := [⟨40,203779337,203779455⟩,
⟨64,322954039,322954228⟩]
theorem checked39288 : checkPrefixCuts (2^48) 5153488897 10 Manual.Count131072.C039288.packed 64 cuts39288 = true := by
 decide +kernel
def pointBounds39288 : List (Nat × Nat × Nat) := [(5153570816,108640636423685,108641021794946)]
theorem point_links_checked39288 : (cuts39288.take 1).map (fun c => (5153488897-1+2*2^10*c.k,108640432644348+c.lower,108640818015491+c.upper)) = pointBounds39288 := by
 decide +kernel
def cuts39289 : List PrefixCut := [⟨55,267565418,267565578⟩,
⟨64,313442555,313442741⟩]
theorem checked39289 : checkPrefixCuts (2^48) 5153619969 10 Manual.Count131072.C039289.packed 64 cuts39289 = true := by
 decide +kernel
def pointBounds39289 : List (Nat × Nat × Nat) := [(5153732608,108641023163805,108641408535297)]
theorem point_links_checked39289 : (cuts39289.take 1).map (fun c => (5153619969-1+2*2^10*c.k,108640755598387+c.lower,108641140969719+c.upper)) = pointBounds39289 := by
 decide +kernel
def cuts39290 : List PrefixCut := [⟨64,321299134,321299324⟩]
theorem checked39290 : checkPrefixCuts (2^48) 5153751041 10 Manual.Count131072.C039290.packed 64 cuts39290 = true := by
 decide +kernel
def cuts39291 : List PrefixCut := [⟨6,29327765,29327782⟩,
⟨64,321017885,321018073⟩]
theorem checked39291 : checkPrefixCuts (2^48) 5153882113 10 Manual.Count131072.C039291.packed 64 cuts39291 = true := by
 decide +kernel
def pointBounds39291 : List (Nat × Nat × Nat) := [(5153894400,108641419667841,108641805039566)]
theorem point_links_checked39291 : (cuts39291.take 1).map (fun c => (5153882113-1+2*2^10*c.k,108641390340076+c.lower,108641775711784+c.upper)) = pointBounds39291 := by
 decide +kernel
def cuts39292 : List PrefixCut := [⟨21,105129131,105129194⟩,
⟨64,317842248,317842437⟩]
theorem checked39292 : checkPrefixCuts (2^48) 5154013185 10 Manual.Count131072.C039292.packed 64 cuts39292 = true := by
 decide +kernel
def pointBounds39292 : List (Nat × Nat × Nat) := [(5154056192,108641816487092,108642201859051)]
theorem point_links_checked39292 : (cuts39292.take 1).map (fun c => (5154013185-1+2*2^10*c.k,108641711357961+c.lower,108642096729857+c.upper)) = pointBounds39292 := by
 decide +kernel
def cuts39293 : List PrefixCut := [⟨36,178468689,178468797⟩,
⟨64,320236989,320237182⟩]
theorem checked39293 : checkPrefixCuts (2^48) 5154144257 10 Manual.Count131072.C039293.packed 64 cuts39293 = true := by
 decide +kernel
def pointBounds39293 : List (Nat × Nat × Nat) := [(5154217984,108642207668898,108642593041091)]
theorem point_links_checked39293 : (cuts39293.take 1).map (fun c => (5154144257-1+2*2^10*c.k,108642029200209+c.lower,108642414572294+c.upper)) = pointBounds39293 := by
 decide +kernel
def cuts39294 : List PrefixCut := [⟨51,254152268,254152424⟩,
⟨64,320501887,320502084⟩]
theorem checked39294 : checkPrefixCuts (2^48) 5154275329 10 Manual.Count131072.C039294.packed 64 cuts39294 = true := by
 decide +kernel
def pointBounds39294 : List (Nat × Nat × Nat) := [(5154379776,108642603589466,108642988961900)]
theorem point_links_checked39294 : (cuts39294.take 1).map (fun c => (5154275329-1+2*2^10*c.k,108642349437198+c.lower,108642734809476+c.upper)) = pointBounds39294 := by
 decide +kernel
def cuts39295 : List PrefixCut := [⟨64,321804366,321804554⟩]
theorem checked39295 : checkPrefixCuts (2^48) 5154406401 10 Manual.Count131072.C039295.packed 64 cuts39295 = true := by
 decide +kernel
def cuts39296 : List PrefixCut := [⟨2,10266151,10266157⟩,
⟨64,319393495,319393686⟩]
theorem checked39296 : checkPrefixCuts (2^48) 5154537473 10 Manual.Count131072.C039296.packed 64 cuts39296 = true := by
 decide +kernel
def pointBounds39296 : List (Nat × Nat × Nat) := [(5154541568,108643002009602,108643387382271)]
theorem point_links_checked39296 : (cuts39296.take 1).map (fun c => (5154537473-1+2*2^10*c.k,108642991743451+c.lower,108643377116114+c.upper)) = pointBounds39296 := by
 decide +kernel
def cuts39297 : List PrefixCut := [⟨17,88133493,88133544⟩,
⟨64,325992606,325992798⟩]
theorem checked39297 : checkPrefixCuts (2^48) 5154668545 10 Manual.Count131072.C039297.packed 64 cuts39297 = true := by
 decide +kernel
def pointBounds39297 : List (Nat × Nat × Nat) := [(5154703360,108643399270439,108643784643344)]
theorem point_links_checked39297 : (cuts39297.take 1).map (fun c => (5154668545-1+2*2^10*c.k,108643311136946+c.lower,108643696509800+c.upper)) = pointBounds39297 := by
 decide +kernel
def cuts39298 : List PrefixCut := [⟨32,160535993,160536093⟩,
⟨64,319541062,319541255⟩]
theorem checked39298 : checkPrefixCuts (2^48) 5154799617 10 Manual.Count131072.C039298.packed 64 cuts39298 = true := by
 decide +kernel
def pointBounds39298 : List (Nat × Nat × Nat) := [(5154865152,108643797665545,108644183038691)]
theorem point_links_checked39298 : (cuts39298.take 1).map (fun c => (5154799617-1+2*2^10*c.k,108643637129552+c.lower,108644022502598+c.upper)) = pointBounds39298 := by
 decide +kernel
def cuts39299 : List PrefixCut := [⟨47,234681679,234681819⟩,
⟨64,321007183,321007374⟩]
theorem checked39299 : checkPrefixCuts (2^48) 5154930689 10 Manual.Count131072.C039299.packed 64 cuts39299 = true := by
 decide +kernel
def pointBounds39299 : List (Nat × Nat × Nat) := [(5155026944,108644191352293,108644576725672)]
theorem point_links_checked39299 : (cuts39299.take 1).map (fun c => (5154930689-1+2*2^10*c.k,108643956670614+c.lower,108644342043853+c.upper)) = pointBounds39299 := by
 decide +kernel
def cuts39300 : List PrefixCut := [⟨62,309696746,309696929⟩,
⟨64,320125401,320125590⟩]
theorem checked39300 : checkPrefixCuts (2^48) 5155061761 10 Manual.Count131072.C039300.packed 64 cuts39300 = true := by
 decide +kernel
def pointBounds39300 : List (Nat × Nat × Nat) := [(5155188736,108644587374543,108644972748156)]
theorem point_links_checked39300 : (cuts39300.take 1).map (fun c => (5155061761-1+2*2^10*c.k,108644277677797+c.lower,108644663051227+c.upper)) = pointBounds39300 := by
 decide +kernel
def cuts39301 : List PrefixCut := [⟨64,317551169,317551361⟩]
theorem checked39301 : checkPrefixCuts (2^48) 5155192833 10 Manual.Count131072.C039301.packed 64 cuts39301 = true := by
 decide +kernel
def cuts39302 : List PrefixCut := [⟨13,65627684,65627720⟩,
⟨64,320709765,320709954⟩]
theorem checked39302 : checkPrefixCuts (2^48) 5155323905 10 Manual.Count131072.C039302.packed 64 cuts39302 = true := by
 decide +kernel
def pointBounds39302 : List (Nat × Nat × Nat) := [(5155350528,108644980982051,108645366355898)]
theorem point_links_checked39302 : (cuts39302.take 1).map (fun c => (5155323905-1+2*2^10*c.k,108644915354367+c.lower,108645300728178+c.upper)) = pointBounds39302 := by
 decide +kernel
def cuts39303 : List PrefixCut := [⟨28,139823391,139823473⟩,
⟨64,317098185,317098375⟩]
theorem checked39303 : checkPrefixCuts (2^48) 5155454977 10 Manual.Count131072.C039303.packed 64 cuts39303 = true := by
 decide +kernel
def pointBounds39303 : List (Nat × Nat × Nat) := [(5155512320,108645375887523,108645761261605)]
theorem point_links_checked39303 : (cuts39303.take 1).map (fun c => (5155454977-1+2*2^10*c.k,108645236064132+c.lower,108645621438132+c.upper)) = pointBounds39303 := by
 decide +kernel
def cuts39304 : List PrefixCut := [⟨43,216963034,216963162⟩,
⟨64,321676122,321676312⟩]
theorem checked39304 : checkPrefixCuts (2^48) 5155586049 10 Manual.Count131072.C039304.packed 64 cuts39304 = true := by
 decide +kernel
def pointBounds39304 : List (Nat × Nat × Nat) := [(5155674112,108645770125351,108646155499669)]
theorem point_links_checked39304 : (cuts39304.take 1).map (fun c => (5155586049-1+2*2^10*c.k,108645553162317+c.lower,108645938536507+c.upper)) = pointBounds39304 := by
 decide +kernel
def cuts39305 : List PrefixCut := [⟨58,288911915,288912085⟩,
⟨64,317518852,317519037⟩]
theorem checked39305 : checkPrefixCuts (2^48) 5155717121 10 Manual.Count131072.C039305.packed 64 cuts39305 = true := by
 decide +kernel
def pointBounds39305 : List (Nat × Nat × Nat) := [(5155835904,108646163750354,108646549124904)]
theorem point_links_checked39305 : (cuts39305.take 1).map (fun c => (5155717121-1+2*2^10*c.k,108645874838439+c.lower,108646260212819+c.upper)) = pointBounds39305 := by
 decide +kernel
def cuts39306 : List PrefixCut := [⟨64,323952698,323952890⟩]
theorem checked39306 : checkPrefixCuts (2^48) 5155848193 10 Manual.Count131072.C039306.packed 64 cuts39306 = true := by
 decide +kernel
def cuts39307 : List PrefixCut := [⟨9,46239287,46239315⟩,
⟨64,323343920,323344118⟩]
theorem checked39307 : checkPrefixCuts (2^48) 5155979265 10 Manual.Count131072.C039307.packed 64 cuts39307 = true := by
 decide +kernel
def pointBounds39307 : List (Nat × Nat × Nat) := [(5155997696,108646562549276,108646947924061)]
theorem point_links_checked39307 : (cuts39307.take 1).map (fun c => (5155979265-1+2*2^10*c.k,108646516309989+c.lower,108646901684746+c.upper)) = pointBounds39307 := by
 decide +kernel
def cuts39308 : List PrefixCut := [⟨24,114475842,114475912⟩,
⟨64,316730290,316730482⟩]
theorem checked39308 : checkPrefixCuts (2^48) 5156110337 10 Manual.Count131072.C039308.packed 64 cuts39308 = true := by
 decide +kernel
def pointBounds39308 : List (Nat × Nat × Nat) := [(5156159488,108646954129751,108647339504776)]
theorem point_links_checked39308 : (cuts39308.take 1).map (fun c => (5156110337-1+2*2^10*c.k,108646839653909+c.lower,108647225028864+c.upper)) = pointBounds39308 := by
 decide +kernel
def cuts39309 : List PrefixCut := [⟨39,190787643,190787756⟩,
⟨64,315139210,315139398⟩]
theorem checked39309 : checkPrefixCuts (2^48) 5156241409 10 Manual.Count131072.C039309.packed 64 cuts39309 = true := by
 decide +kernel
def pointBounds39309 : List (Nat × Nat × Nat) := [(5156321280,108647347171842,108647732547102)]
theorem point_links_checked39309 : (cuts39309.take 1).map (fun c => (5156241409-1+2*2^10*c.k,108647156384199+c.lower,108647541759346+c.upper)) = pointBounds39309 := by
 decide +kernel
def cuts39310 : List PrefixCut := [⟨54,273099741,273099900⟩,
⟨64,322009239,322009428⟩]
theorem checked39310 : checkPrefixCuts (2^48) 5156372481 10 Manual.Count131072.C039310.packed 64 cuts39310 = true := by
 decide +kernel
def pointBounds39310 : List (Nat × Nat × Nat) := [(5156483072,108647744623150,108648129998644)]
theorem point_links_checked39310 : (cuts39310.take 1).map (fun c => (5156372481-1+2*2^10*c.k,108647471523409+c.lower,108647856898744+c.upper)) = pointBounds39310 := by
 decide +kernel
def cuts39311 : List PrefixCut := [⟨64,322219370,322219561⟩]
theorem checked39311 : checkPrefixCuts (2^48) 5156503553 10 Manual.Count131072.C039311.packed 64 cuts39311 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000290
