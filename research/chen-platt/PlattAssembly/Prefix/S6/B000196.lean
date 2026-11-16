import PlattAssemblyKernel
import PlattCertificates.Count131072.C056272
import PlattCertificates.Count131072.C056273
import PlattCertificates.Count131072.C056274
import PlattCertificates.Count131072.C056275
import PlattCertificates.Count131072.C056276
import PlattCertificates.Count131072.C056277
import PlattCertificates.Count131072.C056278
import PlattCertificates.Count131072.C056279
import PlattCertificates.Count131072.C056280
import PlattCertificates.Count131072.C056281
import PlattCertificates.Count131072.C056282
import PlattCertificates.Count131072.C056283
import PlattCertificates.Count131072.C056284
import PlattCertificates.Count131072.C056285
import PlattCertificates.Count131072.C056286
import PlattCertificates.Count131072.C056287
import PlattCertificates.Count131072.C056288
import PlattCertificates.Count131072.C056289
import PlattCertificates.Count131072.C056290
import PlattCertificates.Count131072.C056291
import PlattCertificates.Count131072.C056292
import PlattCertificates.Count131072.C056293
import PlattCertificates.Count131072.C056294
import PlattCertificates.Count131072.C056295
import PlattCertificates.Count131072.C056296
import PlattCertificates.Count131072.C056297
import PlattCertificates.Count131072.C056298
import PlattCertificates.Count131072.C056299
import PlattCertificates.Count131072.C056300
import PlattCertificates.Count131072.C056301
import PlattCertificates.Count131072.C056302
import PlattCertificates.Count131072.C056303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000196
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56272 : List PrefixCut := [⟨64,218057107,218057232⟩]
theorem checked56272 : checkPrefixCuts (2^48) 7379615745 10 Manual.Count131072.C056272.packed 64 cuts56272 = true := by
 decide +kernel
def cuts56273 : List PrefixCut := [⟨4,13807230,13807237⟩,
⟨64,217633696,217633822⟩]
theorem checked56273 : checkPrefixCuts (2^48) 7379746817 10 Manual.Count131072.C056273.packed 64 cuts56273 = true := by
 decide +kernel
def pointBounds56273 : List (Nat × Nat × Nat) := [(7379755008,113123928078189,113124316033746)]
theorem point_links_checked56273 : (cuts56273.take 1).map (fun c => (7379746817-1+2*2^10*c.k,113123914270959+c.lower,113124302226509+c.upper)) = pointBounds56273 := by
 decide +kernel
def cuts56274 : List PrefixCut := [⟨53,181549172,181549272⟩,
⟨64,219880116,219880237⟩]
theorem checked56274 : checkPrefixCuts (2^48) 7379877889 10 Manual.Count131072.C056274.packed 64 cuts56274 = true := by
 decide +kernel
def pointBounds56274 : List (Nat × Nat × Nat) := [(7379986432,113124313453827,113124701409603)]
theorem point_links_checked56274 : (cuts56274.take 1).map (fun c => (7379877889-1+2*2^10*c.k,113124131904655+c.lower,113124519860331+c.upper)) = pointBounds56274 := by
 decide +kernel
def cuts56275 : List PrefixCut := [⟨64,221897641,221897767⟩]
theorem checked56275 : checkPrefixCuts (2^48) 7380008961 10 Manual.Count131072.C056275.packed 64 cuts56275 = true := by
 decide +kernel
def cuts56276 : List PrefixCut := [⟨38,131695018,131695094⟩,
⟨64,219185808,219185936⟩]
theorem checked56276 : checkPrefixCuts (2^48) 7380140033 10 Manual.Count131072.C056276.packed 64 cuts56276 = true := by
 decide +kernel
def pointBounds56276 : List (Nat × Nat × Nat) := [(7380217856,113124705377430,113125093333429)]
theorem point_links_checked56276 : (cuts56276.take 1).map (fun c => (7380140033-1+2*2^10*c.k,113124573682412+c.lower,113124961638335+c.upper)) = pointBounds56276 := by
 decide +kernel
def cuts56277 : List PrefixCut := [⟨64,221203235,221203360⟩]
theorem checked56277 : checkPrefixCuts (2^48) 7380271105 10 Manual.Count131072.C056277.packed 64 cuts56277 = true := by
 decide +kernel
def cuts56278 : List PrefixCut := [⟨23,78221099,78221143⟩,
⟨64,220894197,220894320⟩]
theorem checked56278 : checkPrefixCuts (2^48) 7380402177 10 Manual.Count131072.C056278.packed 64 cuts56278 = true := by
 decide +kernel
def pointBounds56278 : List (Nat × Nat × Nat) := [(7380449280,113125092292554,113125480248774)]
theorem point_links_checked56278 : (cuts56278.take 1).map (fun c => (7380402177-1+2*2^10*c.k,113125014071455+c.lower,113125402027631+c.upper)) = pointBounds56278 := by
 decide +kernel
def cuts56279 : List PrefixCut := [⟨64,220356369,220356492⟩]
theorem checked56279 : checkPrefixCuts (2^48) 7380533249 10 Manual.Count131072.C056279.packed 64 cuts56279 = true := by
 decide +kernel
def cuts56280 : List PrefixCut := [⟨8,28106790,28106806⟩,
⟨64,222373689,222373814⟩]
theorem checked56280 : checkPrefixCuts (2^48) 7380664321 10 Manual.Count131072.C056280.packed 64 cuts56280 = true := by
 decide +kernel
def pointBounds56280 : List (Nat × Nat × Nat) := [(7380680704,113125483428811,113125871385249)]
theorem point_links_checked56280 : (cuts56280.take 1).map (fun c => (7380664321-1+2*2^10*c.k,113125455322021+c.lower,113125843278443+c.upper)) = pointBounds56280 := by
 decide +kernel
def cuts56281 : List PrefixCut := [⟨57,194340128,194340237⟩,
⟨64,219433273,219433397⟩]
theorem checked56281 : checkPrefixCuts (2^48) 7380795393 10 Manual.Count131072.C056281.packed 64 cuts56281 = true := by
 decide +kernel
def pointBounds56281 : List (Nat × Nat × Nat) := [(7380912128,113125872035838,113126259992494)]
theorem point_links_checked56281 : (cuts56281.take 1).map (fun c => (7380795393-1+2*2^10*c.k,113125677695710+c.lower,113126065652257+c.upper)) = pointBounds56281 := by
 decide +kernel
def cuts56282 : List PrefixCut := [⟨64,219391247,219391374⟩]
theorem checked56282 : checkPrefixCuts (2^48) 7380926465 10 Manual.Count131072.C056282.packed 64 cuts56282 = true := by
 decide +kernel
def cuts56283 : List PrefixCut := [⟨42,143157074,143157154⟩,
⟨64,220073763,220073886⟩]
theorem checked56283 : checkPrefixCuts (2^48) 7381057537 10 Manual.Count131072.C056283.packed 64 cuts56283 = true := by
 decide +kernel
def pointBounds56283 : List (Nat × Nat × Nat) := [(7381143552,113126259677304,113126647634182)]
theorem point_links_checked56283 : (cuts56283.take 1).map (fun c => (7381057537-1+2*2^10*c.k,113126116520230+c.lower,113126504477028+c.upper)) = pointBounds56283 := by
 decide +kernel
def cuts56284 : List PrefixCut := [⟨64,222396034,222396160⟩]
theorem checked56284 : checkPrefixCuts (2^48) 7381188609 10 Manual.Count131072.C056284.packed 64 cuts56284 = true := by
 decide +kernel
def cuts56285 : List PrefixCut := [⟨27,90452108,90452159⟩,
⟨64,216100117,216100236⟩]
theorem checked56285 : checkPrefixCuts (2^48) 7381319681 10 Manual.Count131072.C056285.packed 64 cuts56285 = true := by
 decide +kernel
def pointBounds56285 : List (Nat × Nat × Nat) := [(7381374976,113126649442135,113127037399233)]
theorem point_links_checked56285 : (cuts56285.take 1).map (fun c => (7381319681-1+2*2^10*c.k,113126558990027+c.lower,113126946947074+c.upper)) = pointBounds56285 := by
 decide +kernel
def cuts56286 : List PrefixCut := [⟨64,221701722,221701848⟩]
theorem checked56286 : checkPrefixCuts (2^48) 7381450753 10 Manual.Count131072.C056286.packed 64 cuts56286 = true := by
 decide +kernel
def cuts56287 : List PrefixCut := [⟨12,41563873,41563897⟩,
⟨64,221125823,221125951⟩]
theorem checked56287 : checkPrefixCuts (2^48) 7381581825 10 Manual.Count131072.C056287.packed 64 cuts56287 = true := by
 decide +kernel
def pointBounds56287 : List (Nat × Nat × Nat) := [(7381606400,113127038355739,113127426313055)]
theorem point_links_checked56287 : (cuts56287.take 1).map (fun c => (7381581825-1+2*2^10*c.k,113126996791866+c.lower,113127384749158+c.upper)) = pointBounds56287 := by
 decide +kernel
def cuts56288 : List PrefixCut := [⟨61,212161194,212161313⟩,
⟨64,222189572,222189697⟩]
theorem checked56288 : checkPrefixCuts (2^48) 7381712897 10 Manual.Count131072.C056288.packed 64 cuts56288 = true := by
 decide +kernel
def pointBounds56288 : List (Nat × Nat × Nat) := [(7381837824,113127430078883,113127818036422)]
theorem point_links_checked56288 : (cuts56288.take 1).map (fun c => (7381712897-1+2*2^10*c.k,113127217917689+c.lower,113127605875109+c.upper)) = pointBounds56288 := by
 decide +kernel
def cuts56289 : List PrefixCut := [⟨64,219554632,219554757⟩]
theorem checked56289 : checkPrefixCuts (2^48) 7381843969 10 Manual.Count131072.C056289.packed 64 cuts56289 = true := by
 decide +kernel
def cuts56290 : List PrefixCut := [⟨46,156751538,156751629⟩,
⟨64,218559366,218559492⟩]
theorem checked56290 : checkPrefixCuts (2^48) 7381975041 10 Manual.Count131072.C056290.packed 64 cuts56290 = true := by
 decide +kernel
def pointBounds56290 : List (Nat × Nat × Nat) := [(7382069248,113127816413431,113128204371192)]
theorem point_links_checked56290 : (cuts56290.take 1).map (fun c => (7381975041-1+2*2^10*c.k,113127659661893+c.lower,113128047619563+c.upper)) = pointBounds56290 := by
 decide +kernel
def cuts56291 : List PrefixCut := [⟨64,220919492,220919618⟩]
theorem checked56291 : checkPrefixCuts (2^48) 7382106113 10 Manual.Count131072.C056291.packed 64 cuts56291 = true := by
 decide +kernel
def cuts56292 : List PrefixCut := [⟨31,104929651,104929713⟩,
⟨64,218132193,218132321⟩]
theorem checked56292 : checkPrefixCuts (2^48) 7382237185 10 Manual.Count131072.C056292.packed 64 cuts56292 = true := by
 decide +kernel
def pointBounds56292 : List (Nat × Nat × Nat) := [(7382300672,113128204070402,113128592028386)]
theorem point_links_checked56292 : (cuts56292.take 1).map (fun c => (7382237185-1+2*2^10*c.k,113128099140751+c.lower,113128487098673+c.upper)) = pointBounds56292 := by
 decide +kernel
def cuts56293 : List PrefixCut := [⟨64,224343130,224343257⟩]
theorem checked56293 : checkPrefixCuts (2^48) 7382368257 10 Manual.Count131072.C056293.packed 64 cuts56293 = true := by
 decide +kernel
def cuts56294 : List PrefixCut := [⟨16,55742014,55742046⟩,
⟨64,219573281,219573404⟩]
theorem checked56294 : checkPrefixCuts (2^48) 7382499329 10 Manual.Count131072.C056294.packed 64 cuts56294 = true := by
 decide +kernel
def pointBounds56294 : List (Nat × Nat × Nat) := [(7382532096,113128597358088,113128985316297)]
theorem point_links_checked56294 : (cuts56294.take 1).map (fun c => (7382499329-1+2*2^10*c.k,113128541616074+c.lower,113128929574251+c.upper)) = pointBounds56294 := by
 decide +kernel
def cuts56295 : List PrefixCut := [⟨64,219493126,219493247⟩]
theorem checked56295 : checkPrefixCuts (2^48) 7382630401 10 Manual.Count131072.C056295.packed 64 cuts56295 = true := by
 decide +kernel
def cuts56296 : List PrefixCut := [⟨1,3660092,3660094⟩,
⟨64,218955469,218955590⟩]
theorem checked56296 : checkPrefixCuts (2^48) 7382761473 10 Manual.Count131072.C056296.packed 64 cuts56296 = true := by
 decide +kernel
def pointBounds56296 : List (Nat × Nat × Nat) := [(7382763520,113128984342573,113129372300996)]
theorem point_links_checked56296 : (cuts56296.take 1).map (fun c => (7382761473-1+2*2^10*c.k,113128980682481+c.lower,113129368640902+c.upper)) = pointBounds56296 := by
 decide +kernel
def cuts56297 : List PrefixCut := [⟨50,170113853,170113951⟩,
⟨64,217121591,217121717⟩]
theorem checked56297 : checkPrefixCuts (2^48) 7382892545 10 Manual.Count131072.C056297.packed 64 cuts56297 = true := by
 decide +kernel
def pointBounds56297 : List (Nat × Nat × Nat) := [(7382994944,113129369751803,113129757710443)]
theorem point_links_checked56297 : (cuts56297.take 1).map (fun c => (7382892545-1+2*2^10*c.k,113129199637950+c.lower,113129587596492+c.upper)) = pointBounds56297 := by
 decide +kernel
def cuts56298 : List PrefixCut := [⟨64,214944642,214944766⟩]
theorem checked56298 : checkPrefixCuts (2^48) 7383023617 10 Manual.Count131072.C056298.packed 64 cuts56298 = true := by
 decide +kernel
def cuts56299 : List PrefixCut := [⟨35,119594195,119594264⟩,
⟨64,220506858,220506983⟩]
theorem checked56299 : checkPrefixCuts (2^48) 7383154689 10 Manual.Count131072.C056299.packed 64 cuts56299 = true := by
 decide +kernel
def pointBounds56299 : List (Nat × Nat × Nat) := [(7383226368,113129751298378,113130139257239)]
theorem point_links_checked56299 : (cuts56299.take 1).map (fun c => (7383154689-1+2*2^10*c.k,113129631704183+c.lower,113130019662975+c.upper)) = pointBounds56299 := by
 decide +kernel
def cuts56300 : List PrefixCut := [⟨64,218939925,218940054⟩]
theorem checked56300 : checkPrefixCuts (2^48) 7383285761 10 Manual.Count131072.C056300.packed 64 cuts56300 = true := by
 decide +kernel
def cuts56301 : List PrefixCut := [⟨20,69573515,69573553⟩,
⟨64,220041580,220041705⟩]
theorem checked56301 : checkPrefixCuts (2^48) 7383416833 10 Manual.Count131072.C056301.packed 64 cuts56301 = true := by
 decide +kernel
def pointBounds56301 : List (Nat × Nat × Nat) := [(7383457792,113130140724481,113130528683565)]
theorem point_links_checked56301 : (cuts56301.take 1).map (fun c => (7383416833-1+2*2^10*c.k,113130071150966+c.lower,113130459110012+c.upper)) = pointBounds56301 := by
 decide +kernel
def cuts56302 : List PrefixCut := [⟨64,223392388,223392514⟩]
theorem checked56302 : checkPrefixCuts (2^48) 7383547905 10 Manual.Count131072.C056302.packed 64 cuts56302 = true := by
 decide +kernel
def cuts56303 : List PrefixCut := [⟨5,17573873,17573883⟩,
⟨64,220110004,220110131⟩]
theorem checked56303 : checkPrefixCuts (2^48) 7383678977 10 Manual.Count131072.C056303.packed 64 cuts56303 = true := by
 decide +kernel
def pointBounds56303 : List (Nat × Nat × Nat) := [(7383689216,113130532158807,113130920118114)]
theorem point_links_checked56303 : (cuts56303.take 1).map (fun c => (7383678977-1+2*2^10*c.k,113130514584934+c.lower,113130902544231+c.upper)) = pointBounds56303 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000196
