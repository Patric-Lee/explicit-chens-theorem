import PlattAssemblyKernel
import PlattCertificates.Count131072.C058352
import PlattCertificates.Count131072.C058353
import PlattCertificates.Count131072.C058354
import PlattCertificates.Count131072.C058355
import PlattCertificates.Count131072.C058356
import PlattCertificates.Count131072.C058357
import PlattCertificates.Count131072.C058358
import PlattCertificates.Count131072.C058359
import PlattCertificates.Count131072.C058360
import PlattCertificates.Count131072.C058361
import PlattCertificates.Count131072.C058362
import PlattCertificates.Count131072.C058363
import PlattCertificates.Count131072.C058364
import PlattCertificates.Count131072.C058365
import PlattCertificates.Count131072.C058366
import PlattCertificates.Count131072.C058367
import PlattCertificates.Count131072.C058368
import PlattCertificates.Count131072.C058369
import PlattCertificates.Count131072.C058370
import PlattCertificates.Count131072.C058371
import PlattCertificates.Count131072.C058372
import PlattCertificates.Count131072.C058373
import PlattCertificates.Count131072.C058374
import PlattCertificates.Count131072.C058375
import PlattCertificates.Count131072.C058376
import PlattCertificates.Count131072.C058377
import PlattCertificates.Count131072.C058378
import PlattCertificates.Count131072.C058379
import PlattCertificates.Count131072.C058380
import PlattCertificates.Count131072.C058381
import PlattCertificates.Count131072.C058382
import PlattCertificates.Count131072.C058383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000261
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58352 : List PrefixCut := [⟨64,211575793,211575913⟩]
theorem checked58352 : checkPrefixCuts (2^48) 7652245505 10 Manual.Count131072.C058352.packed 64 cuts58352 = true := by
 decide +kernel
def cuts58353 : List PrefixCut := [⟨13,44617311,44617335⟩,
⟨64,213963018,213963136⟩]
theorem checked58353 : checkPrefixCuts (2^48) 7652376577 10 Manual.Count131072.C058353.packed 64 cuts58353 = true := by
 decide +kernel
def pointBounds58353 : List (Nat × Nat × Nat) := [(7652403200,113572969579044,113573357790067)]
theorem point_links_checked58353 : (cuts58353.take 1).map (fun c => (7652376577-1+2*2^10*c.k,113572924961733+c.lower,113573313172732+c.upper)) = pointBounds58353 := by
 decide +kernel
def cuts58354 : List PrefixCut := [⟨64,209692648,209692764⟩]
theorem checked58354 : checkPrefixCuts (2^48) 7652507649 10 Manual.Count131072.C058354.packed 64 cuts58354 = true := by
 decide +kernel
def cuts58355 : List PrefixCut := [⟨2,6547090,6547094⟩,
⟨64,212447655,212447776⟩]
theorem checked58355 : checkPrefixCuts (2^48) 7652638721 10 Manual.Count131072.C058355.packed 64 cuts58355 = true := by
 decide +kernel
def pointBounds58355 : List (Nat × Nat × Nat) := [(7652642816,113573355164489,113573743375726)]
theorem point_links_checked58355 : (cuts58355.take 1).map (fun c => (7652638721-1+2*2^10*c.k,113573348617399+c.lower,113573736828632+c.upper)) = pointBounds58355 := by
 decide +kernel
def cuts58356 : List PrefixCut := [⟨55,181180822,181180925⟩,
⟨64,211524487,211524607⟩]
theorem checked58356 : checkPrefixCuts (2^48) 7652769793 10 Manual.Count131072.C058356.packed 64 cuts58356 = true := by
 decide +kernel
def pointBounds58356 : List (Nat × Nat × Nat) := [(7652882432,113573742245876,113574130457333)]
theorem point_links_checked58356 : (cuts58356.take 1).map (fun c => (7652769793-1+2*2^10*c.k,113573561065054+c.lower,113573949276408+c.upper)) = pointBounds58356 := by
 decide +kernel
def cuts58357 : List PrefixCut := [⟨64,212587505,212587626⟩]
theorem checked58357 : checkPrefixCuts (2^48) 7652900865 10 Manual.Count131072.C058357.packed 64 cuts58357 = true := by
 decide +kernel
def cuts58358 : List PrefixCut := [⟨44,145498953,145499038⟩,
⟨64,212105712,212105836⟩]
theorem checked58358 : checkPrefixCuts (2^48) 7653031937 10 Manual.Count131072.C058358.packed 64 cuts58358 = true := by
 decide +kernel
def pointBounds58358 : List (Nat × Nat × Nat) := [(7653122048,113574130675999,113574518887679)]
theorem point_links_checked58358 : (cuts58358.take 1).map (fun c => (7653031937-1+2*2^10*c.k,113573985177046+c.lower,113574373388641+c.upper)) = pointBounds58358 := by
 decide +kernel
def cuts58359 : List PrefixCut := [⟨64,213940996,213941115⟩]
theorem checked58359 : checkPrefixCuts (2^48) 7653163009 10 Manual.Count131072.C058359.packed 64 cuts58359 = true := by
 decide +kernel
def cuts58360 : List PrefixCut := [⟨33,110150422,110150485⟩,
⟨64,212797233,212797357⟩]
theorem checked58360 : checkPrefixCuts (2^48) 7653294081 10 Manual.Count131072.C058360.packed 64 cuts58360 = true := by
 decide +kernel
def pointBounds58360 : List (Nat × Nat × Nat) := [(7653361664,113574521374176,113574909586077)]
theorem point_links_checked58360 : (cuts58360.take 1).map (fun c => (7653294081-1+2*2^10*c.k,113574411223754+c.lower,113574799435592+c.upper)) = pointBounds58360 := by
 decide +kernel
def cuts58361 : List PrefixCut := [⟨64,210954703,210954826⟩]
theorem checked58361 : checkPrefixCuts (2^48) 7653425153 10 Manual.Count131072.C058361.packed 64 cuts58361 = true := by
 decide +kernel
def cuts58362 : List PrefixCut := [⟨22,72965367,72965410⟩,
⟨64,213819688,213819809⟩]
theorem checked58362 : checkPrefixCuts (2^48) 7653556225 10 Manual.Count131072.C058362.packed 64 cuts58362 = true := by
 decide +kernel
def pointBounds58362 : List (Nat × Nat × Nat) := [(7653601280,113574907941057,113575296153185)]
theorem point_links_checked58362 : (cuts58362.take 1).map (fun c => (7653556225-1+2*2^10*c.k,113574834975690+c.lower,113575223187775+c.upper)) = pointBounds58362 := by
 decide +kernel
def cuts58363 : List PrefixCut := [⟨64,210653289,210653409⟩]
theorem checked58363 : checkPrefixCuts (2^48) 7653687297 10 Manual.Count131072.C058363.packed 64 cuts58363 = true := by
 decide +kernel
def cuts58364 : List PrefixCut := [⟨11,36812473,36812493⟩,
⟨64,214216899,214217020⟩]
theorem checked58364 : checkPrefixCuts (2^48) 7653818369 10 Manual.Count131072.C058364.packed 64 cuts58364 = true := by
 decide +kernel
def pointBounds58364 : List (Nat × Nat × Nat) := [(7653840896,113575296261140,113575684473486)]
theorem point_links_checked58364 : (cuts58364.take 1).map (fun c => (7653818369-1+2*2^10*c.k,113575259448667+c.lower,113575647660993+c.upper)) = pointBounds58364 := by
 decide +kernel
def cuts58365 : List PrefixCut := [⟨64,211234464,211234585⟩]
theorem checked58365 : checkPrefixCuts (2^48) 7653949441 10 Manual.Count131072.C058365.packed 64 cuts58365 = true := by
 decide +kernel
def pointBounds58365 : List (Nat × Nat × Nat) := [(7654080512,113575684900030,113576073112598)]
theorem point_links_checked58365 : (cuts58365.take 1).map (fun c => (7653949441-1+2*2^10*c.k,113575473665566+c.lower,113575861878013+c.upper)) = pointBounds58365 := by
 decide +kernel
def cuts58366 : List PrefixCut := [⟨64,211414707,211414827⟩]
theorem checked58366 : checkPrefixCuts (2^48) 7654080513 10 Manual.Count131072.C058366.packed 64 cuts58366 = true := by
 decide +kernel
def cuts58367 : List PrefixCut := [⟨53,173056540,173056636⟩,
⟨64,209572410,209572528⟩]
theorem checked58367 : checkPrefixCuts (2^48) 7654211585 10 Manual.Count131072.C058367.packed 64 cuts58367 = true := by
 decide +kernel
def pointBounds58367 : List (Nat × Nat × Nat) := [(7654320128,113576069371277,113576457584061)]
theorem point_links_checked58367 : (cuts58367.take 1).map (fun c => (7654211585-1+2*2^10*c.k,113575896314737+c.lower,113576284527425+c.upper)) = pointBounds58367 := by
 decide +kernel
def cuts58368 : List PrefixCut := [⟨64,211811984,211812106⟩]
theorem checked58368 : checkPrefixCuts (2^48) 7654342657 10 Manual.Count131072.C058368.packed 64 cuts58368 = true := by
 decide +kernel
def cuts58369 : List PrefixCut := [⟨42,138852570,138852651⟩,
⟨64,211330340,211330462⟩]
theorem checked58369 : checkPrefixCuts (2^48) 7654473729 10 Manual.Count131072.C058369.packed 64 cuts58369 = true := by
 decide +kernel
def pointBounds58369 : List (Nat × Nat × Nat) := [(7654559744,113576456551701,113576844764710)]
theorem point_links_checked58369 : (cuts58369.take 1).map (fun c => (7654473729-1+2*2^10*c.k,113576317699131+c.lower,113576705912059+c.upper)) = pointBounds58369 := by
 decide +kernel
def cuts58370 : List PrefixCut := [⟨64,214305209,214305331⟩]
theorem checked58370 : checkPrefixCuts (2^48) 7654604801 10 Manual.Count131072.C058370.packed 64 cuts58370 = true := by
 decide +kernel
def cuts58371 : List PrefixCut := [⟨31,102260671,102260731⟩,
⟨64,211065680,211065801⟩]
theorem checked58371 : checkPrefixCuts (2^48) 7654735873 10 Manual.Count131072.C058371.packed 64 cuts58371 = true := by
 decide +kernel
def pointBounds58371 : List (Nat × Nat × Nat) := [(7654799360,113576845595351,113577233808583)]
theorem point_links_checked58371 : (cuts58371.take 1).map (fun c => (7654735873-1+2*2^10*c.k,113576743334680+c.lower,113577131547852+c.upper)) = pointBounds58371 := by
 decide +kernel
def cuts58372 : List PrefixCut := [⟨64,210106050,210106169⟩]
theorem checked58372 : checkPrefixCuts (2^48) 7654866945 10 Manual.Count131072.C058372.packed 64 cuts58372 = true := by
 decide +kernel
def cuts58373 : List PrefixCut := [⟨20,65707961,65707998⟩,
⟨64,212014474,212014595⟩]
theorem checked58373 : checkPrefixCuts (2^48) 7654998017 10 Manual.Count131072.C058373.packed 64 cuts58373 = true := by
 decide +kernel
def pointBounds58373 : List (Nat × Nat × Nat) := [(7655038976,113577230214371,113577618427820)]
theorem point_links_checked58373 : (cuts58373.take 1).map (fun c => (7654998017-1+2*2^10*c.k,113577164506410+c.lower,113577552719822+c.upper)) = pointBounds58373 := by
 decide +kernel
def cuts58374 : List PrefixCut := [⟨64,207010236,207010355⟩]
theorem checked58374 : checkPrefixCuts (2^48) 7655129089 10 Manual.Count131072.C058374.packed 64 cuts58374 = true := by
 decide +kernel
def cuts58375 : List PrefixCut := [⟨9,28863491,28863507⟩,
⟨64,212080744,212080866⟩]
theorem checked58375 : checkPrefixCuts (2^48) 7655260161 10 Manual.Count131072.C058375.packed 64 cuts58375 = true := by
 decide +kernel
def pointBounds58375 : List (Nat × Nat × Nat) := [(7655278592,113577612394611,113578000608279)]
theorem point_links_checked58375 : (cuts58375.take 1).map (fun c => (7655260161-1+2*2^10*c.k,113577583531120+c.lower,113577971744772+c.upper)) = pointBounds58375 := by
 decide +kernel
def cuts58376 : List PrefixCut := [⟨62,202333687,202333803⟩,
⟨64,209393061,209393181⟩]
theorem checked58376 : checkPrefixCuts (2^48) 7655391233 10 Manual.Count131072.C058376.packed 64 cuts58376 = true := by
 decide +kernel
def pointBounds58376 : List (Nat × Nat × Nat) := [(7655518208,113577997945551,113578386159441)]
theorem point_links_checked58376 : (cuts58376.take 1).map (fun c => (7655391233-1+2*2^10*c.k,113577795611864+c.lower,113578183825638+c.upper)) = pointBounds58376 := by
 decide +kernel
def cuts58377 : List PrefixCut := [⟨64,212110253,212110371⟩]
theorem checked58377 : checkPrefixCuts (2^48) 7655522305 10 Manual.Count131072.C058377.packed 64 cuts58377 = true := by
 decide +kernel
def cuts58378 : List PrefixCut := [⟨51,171001844,171001942⟩,
⟨64,215342085,215342208⟩]
theorem checked58378 : checkPrefixCuts (2^48) 7655653377 10 Manual.Count131072.C058378.packed 64 cuts58378 = true := by
 decide +kernel
def pointBounds58378 : List (Nat × Nat × Nat) := [(7655757824,113578388117022,113578776331132)]
theorem point_links_checked58378 : (cuts58378.take 1).map (fun c => (7655653377-1+2*2^10*c.k,113578217115178+c.lower,113578605329190+c.upper)) = pointBounds58378 := by
 decide +kernel
def cuts58379 : List PrefixCut := [⟨64,212580953,212581070⟩]
theorem checked58379 : checkPrefixCuts (2^48) 7655784449 10 Manual.Count131072.C058379.packed 64 cuts58379 = true := by
 decide +kernel
def cuts58380 : List PrefixCut := [⟨40,133973400,133973475⟩,
⟨64,212540550,212540672⟩]
theorem checked58380 : checkPrefixCuts (2^48) 7655915521 10 Manual.Count131072.C058380.packed 64 cuts58380 = true := by
 decide +kernel
def pointBounds58380 : List (Nat × Nat × Nat) := [(7655997440,113578779011616,113579167225943)]
theorem point_links_checked58380 : (cuts58380.take 1).map (fun c => (7655915521-1+2*2^10*c.k,113578645038216+c.lower,113579033252468+c.upper)) = pointBounds58380 := by
 decide +kernel
def cuts58381 : List PrefixCut := [⟨64,209706017,209706136⟩]
theorem checked58381 : checkPrefixCuts (2^48) 7656046593 10 Manual.Count131072.C058381.packed 64 cuts58381 = true := by
 decide +kernel
def cuts58382 : List PrefixCut := [⟨29,97167974,97168030⟩,
⟨64,211467116,211467238⟩]
theorem checked58382 : checkPrefixCuts (2^48) 7656177665 10 Manual.Count131072.C058382.packed 64 cuts58382 = true := by
 decide +kernel
def pointBounds58382 : List (Nat × Nat × Nat) := [(7656237056,113579164452757,113579552667306)]
theorem point_links_checked58382 : (cuts58382.take 1).map (fun c => (7656177665-1+2*2^10*c.k,113579067284783+c.lower,113579455499276+c.upper)) = pointBounds58382 := by
 decide +kernel
def cuts58383 : List PrefixCut := [⟨64,210029707,210029826⟩]
theorem checked58383 : checkPrefixCuts (2^48) 7656308737 10 Manual.Count131072.C058383.packed 64 cuts58383 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000261
