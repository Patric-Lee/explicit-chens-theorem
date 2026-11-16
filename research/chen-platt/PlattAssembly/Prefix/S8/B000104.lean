import PlattAssemblyKernel
import PlattCertificates.Count131072.C073328
import PlattCertificates.Count131072.C073329
import PlattCertificates.Count131072.C073330
import PlattCertificates.Count131072.C073331
import PlattCertificates.Count131072.C073332
import PlattCertificates.Count131072.C073333
import PlattCertificates.Count131072.C073334
import PlattCertificates.Count131072.C073335
import PlattCertificates.Count131072.C073336
import PlattCertificates.Count131072.C073337
import PlattCertificates.Count131072.C073338
import PlattCertificates.Count131072.C073339
import PlattCertificates.Count131072.C073340
import PlattCertificates.Count131072.C073341
import PlattCertificates.Count131072.C073342
import PlattCertificates.Count131072.C073343
import PlattCertificates.Count131072.C073344
import PlattCertificates.Count131072.C073345
import PlattCertificates.Count131072.C073346
import PlattCertificates.Count131072.C073347
import PlattCertificates.Count131072.C073348
import PlattCertificates.Count131072.C073349
import PlattCertificates.Count131072.C073350
import PlattCertificates.Count131072.C073351
import PlattCertificates.Count131072.C073352
import PlattCertificates.Count131072.C073353
import PlattCertificates.Count131072.C073354
import PlattCertificates.Count131072.C073355
import PlattCertificates.Count131072.C073356
import PlattCertificates.Count131072.C073357
import PlattCertificates.Count131072.C073358
import PlattCertificates.Count131072.C073359
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73328 : List PrefixCut := [⟨52,135098821,135098901⟩,
⟨64,165953249,165953348⟩]
theorem checked73328 : checkPrefixCuts (2^48) 9615179777 10 Manual.Count131072.C073328.packed 64 cuts73328 = true := by
 decide +kernel
def pointBounds73328 : List (Nat × Nat × Nat) := [(9615286272,116382987946928,116383377789448)]
theorem point_links_checked73328 : (cuts73328.take 1).map (fun c => (9615179777-1+2*2^10*c.k,116382852848107+c.lower,116383242690547+c.upper)) = pointBounds73328 := by
 decide +kernel
def cuts73329 : List PrefixCut := [⟨64,167121941,167122034⟩]
theorem checked73329 : checkPrefixCuts (2^48) 9615310849 10 Manual.Count131072.C073329.packed 64 cuts73329 = true := by
 decide +kernel
def cuts73330 : List PrefixCut := [⟨64,168524753,168524845⟩]
theorem checked73330 : checkPrefixCuts (2^48) 9615441921 10 Manual.Count131072.C073330.packed 64 cuts73330 = true := by
 decide +kernel
def cuts73331 : List PrefixCut := [⟨7,18617497,18617508⟩,
⟨64,167117364,167117468⟩]
theorem checked73331 : checkPrefixCuts (2^48) 9615572993 10 Manual.Count131072.C073331.packed 64 cuts73331 = true := by
 decide +kernel
def pointBounds73331 : List (Nat × Nat × Nat) := [(9615587328,116383373065547,116383762908282)]
theorem point_links_checked73331 : (cuts73331.take 1).map (fun c => (9615572993-1+2*2^10*c.k,116383354448050+c.lower,116383744290774+c.upper)) = pointBounds73331 := by
 decide +kernel
def cuts73332 : List PrefixCut := [⟨64,165651477,165651577⟩]
theorem checked73332 : checkPrefixCuts (2^48) 9615704065 10 Manual.Count131072.C073332.packed 64 cuts73332 = true := by
 decide +kernel
def cuts73333 : List PrefixCut := [⟨26,67647441,67647482⟩,
⟨64,167464069,167464168⟩]
theorem checked73333 : checkPrefixCuts (2^48) 9615835137 10 Manual.Count131072.C073333.packed 64 cuts73333 = true := by
 decide +kernel
def pointBounds73333 : List (Nat × Nat × Nat) := [(9615888384,116383754864332,116384144707301)]
theorem point_links_checked73333 : (cuts73333.take 1).map (fun c => (9615835137-1+2*2^10*c.k,116383687216891+c.lower,116384077059819+c.upper)) = pointBounds73333 := by
 decide +kernel
def cuts73334 : List PrefixCut := [⟨64,168808272,168808367⟩]
theorem checked73334 : checkPrefixCuts (2^48) 9615966209 10 Manual.Count131072.C073334.packed 64 cuts73334 = true := by
 decide +kernel
def cuts73335 : List PrefixCut := [⟨45,116323264,116323332⟩,
⟨64,167225325,167225424⟩]
theorem checked73335 : checkPrefixCuts (2^48) 9616097281 10 Manual.Count131072.C073335.packed 64 cuts73335 = true := by
 decide +kernel
def pointBounds73335 : List (Nat × Nat × Nat) := [(9616189440,116384139812496,116384529655686)]
theorem point_links_checked73335 : (cuts73335.take 1).map (fun c => (9616097281-1+2*2^10*c.k,116384023489232+c.lower,116384413332354+c.upper)) = pointBounds73335 := by
 decide +kernel
def cuts73336 : List PrefixCut := [⟨64,167193776,167193882⟩]
theorem checked73336 : checkPrefixCuts (2^48) 9616228353 10 Manual.Count131072.C073336.packed 64 cuts73336 = true := by
 decide +kernel
def cuts73337 : List PrefixCut := [⟨64,166049969,166050076⟩]
theorem checked73337 : checkPrefixCuts (2^48) 9616359425 10 Manual.Count131072.C073337.packed 64 cuts73337 = true := by
 decide +kernel
def pointBounds73337 : List (Nat × Nat × Nat) := [(9616490496,116384523958302,116384913801736)]
theorem point_links_checked73337 : (cuts73337.take 1).map (fun c => (9616359425-1+2*2^10*c.k,116384357908333+c.lower,116384747751660+c.upper)) = pointBounds73337 := by
 decide +kernel
def cuts73338 : List PrefixCut := [⟨64,168008773,168008876⟩]
theorem checked73338 : checkPrefixCuts (2^48) 9616490497 10 Manual.Count131072.C073338.packed 64 cuts73338 = true := by
 decide +kernel
def cuts73339 : List PrefixCut := [⟨64,164581974,164582071⟩]
theorem checked73339 : checkPrefixCuts (2^48) 9616621569 10 Manual.Count131072.C073339.packed 64 cuts73339 = true := by
 decide +kernel
def cuts73340 : List PrefixCut := [⟨19,48089239,48089267⟩,
⟨64,165955370,165955468⟩]
theorem checked73340 : checkPrefixCuts (2^48) 9616752641 10 Manual.Count131072.C073340.packed 64 cuts73340 = true := by
 decide +kernel
def pointBounds73340 : List (Nat × Nat × Nat) := [(9616791552,116384904638288,116385294481950)]
theorem point_links_checked73340 : (cuts73340.take 1).map (fun c => (9616752641-1+2*2^10*c.k,116384856549049+c.lower,116385246392683+c.upper)) = pointBounds73340 := by
 decide +kernel
def cuts73341 : List PrefixCut := [⟨64,168733632,168733733⟩]
theorem checked73341 : checkPrefixCuts (2^48) 9616883713 10 Manual.Count131072.C073341.packed 64 cuts73341 = true := by
 decide +kernel
def cuts73342 : List PrefixCut := [⟨38,98165904,98165964⟩,
⟨64,164984995,164985098⟩]
theorem checked73342 : checkPrefixCuts (2^48) 9617014785 10 Manual.Count131072.C073342.packed 64 cuts73342 = true := by
 decide +kernel
def pointBounds73342 : List (Nat × Nat × Nat) := [(9617092608,116385289403955,116385679247848)]
theorem point_links_checked73342 : (cuts73342.take 1).map (fun c => (9617014785-1+2*2^10*c.k,116385191238051+c.lower,116385581081884+c.upper)) = pointBounds73342 := by
 decide +kernel
def cuts73343 : List PrefixCut := [⟨64,165655909,165656013⟩]
theorem checked73343 : checkPrefixCuts (2^48) 9617145857 10 Manual.Count131072.C073343.packed 64 cuts73343 = true := by
 decide +kernel
def cuts73344 : List PrefixCut := [⟨57,147449417,147449506⟩,
⟨64,166092656,166092757⟩]
theorem checked73344 : checkPrefixCuts (2^48) 9617276929 10 Manual.Count131072.C073344.packed 64 cuts73344 = true := by
 decide +kernel
def pointBounds73344 : List (Nat × Nat × Nat) := [(9617393664,116385669328372,116386059172501)]
theorem point_links_checked73344 : (cuts73344.take 1).map (fun c => (9617276929-1+2*2^10*c.k,116385521878955+c.lower,116385911722995+c.upper)) = pointBounds73344 := by
 decide +kernel
def cuts73345 : List PrefixCut := [⟨64,165680663,165680761⟩]
theorem checked73345 : checkPrefixCuts (2^48) 9617408001 10 Manual.Count131072.C073345.packed 64 cuts73345 = true := by
 decide +kernel
def cuts73346 : List PrefixCut := [⟨64,165590599,165590700⟩]
theorem checked73346 : checkPrefixCuts (2^48) 9617539073 10 Manual.Count131072.C073346.packed 64 cuts73346 = true := by
 decide +kernel
def cuts73347 : List PrefixCut := [⟨12,31900371,31900389⟩,
⟨64,165763951,165764049⟩]
theorem checked73347 : checkPrefixCuts (2^48) 9617670145 10 Manual.Count131072.C073347.packed 64 cuts73347 = true := by
 decide +kernel
def pointBounds73347 : List (Nat × Nat × Nat) := [(9617694720,116386051143244,116386440987602)]
theorem point_links_checked73347 : (cuts73347.take 1).map (fun c => (9617670145-1+2*2^10*c.k,116386019242873+c.lower,116386409087213+c.upper)) = pointBounds73347 := by
 decide +kernel
def cuts73348 : List PrefixCut := [⟨64,167166445,167166547⟩]
theorem checked73348 : checkPrefixCuts (2^48) 9617801217 10 Manual.Count131072.C073348.packed 64 cuts73348 = true := by
 decide +kernel
def cuts73349 : List PrefixCut := [⟨31,81065541,81065589⟩,
⟨64,165583840,165583937⟩]
theorem checked73349 : checkPrefixCuts (2^48) 9617932289 10 Manual.Count131072.C073349.packed 64 cuts73349 = true := by
 decide +kernel
def pointBounds73349 : List (Nat × Nat × Nat) := [(9617995776,116386433238810,116386823083398)]
theorem point_links_checked73349 : (cuts73349.take 1).map (fun c => (9617932289-1+2*2^10*c.k,116386352173269+c.lower,116386742017809+c.upper)) = pointBounds73349 := by
 decide +kernel
def cuts73350 : List PrefixCut := [⟨64,169825008,169825107⟩]
theorem checked73350 : checkPrefixCuts (2^48) 9618063361 10 Manual.Count131072.C073350.packed 64 cuts73350 = true := by
 decide +kernel
def cuts73351 : List PrefixCut := [⟨50,130403415,130403491⟩,
⟨64,167101074,167101173⟩]
theorem checked73351 : checkPrefixCuts (2^48) 9618194433 10 Manual.Count131072.C073351.packed 64 cuts73351 = true := by
 decide +kernel
def pointBounds73351 : List (Nat × Nat × Nat) := [(9618296832,116386817985532,116387207830344)]
theorem point_links_checked73351 : (cuts73351.take 1).map (fun c => (9618194433-1+2*2^10*c.k,116386687582117+c.lower,116387077426853+c.upper)) = pointBounds73351 := by
 decide +kernel
def cuts73352 : List PrefixCut := [⟨64,167830414,167830521⟩]
theorem checked73352 : checkPrefixCuts (2^48) 9618325505 10 Manual.Count131072.C073352.packed 64 cuts73352 = true := by
 decide +kernel
def cuts73353 : List PrefixCut := [⟨64,164140870,164140972⟩]
theorem checked73353 : checkPrefixCuts (2^48) 9618456577 10 Manual.Count131072.C073353.packed 64 cuts73353 = true := by
 decide +kernel
def cuts73354 : List PrefixCut := [⟨5,13256421,13256430⟩,
⟨64,164197163,164197263⟩]
theorem checked73354 : checkPrefixCuts (2^48) 9618587649 10 Manual.Count131072.C073354.packed 64 cuts73354 = true := by
 decide +kernel
def pointBounds73354 : List (Nat × Nat × Nat) := [(9618597888,116387199910896,116387589755949)]
theorem point_links_checked73354 : (cuts73354.take 1).map (fun c => (9618587649-1+2*2^10*c.k,116387186654475+c.lower,116387576499519+c.upper)) = pointBounds73354 := by
 decide +kernel
def cuts73355 : List PrefixCut := [⟨64,168233247,168233343⟩]
theorem checked73355 : checkPrefixCuts (2^48) 9618718721 10 Manual.Count131072.C073355.packed 64 cuts73355 = true := by
 decide +kernel
def cuts73356 : List PrefixCut := [⟨24,64524404,64524442⟩,
⟨64,168786936,168787034⟩]
theorem checked73356 : checkPrefixCuts (2^48) 9618849793 10 Manual.Count131072.C073356.packed 64 cuts73356 = true := by
 decide +kernel
def pointBounds73356 : List (Nat × Nat × Nat) := [(9618898944,116387583609289,116387973454567)]
theorem point_links_checked73356 : (cuts73356.take 1).map (fun c => (9618849793-1+2*2^10*c.k,116387519084885+c.lower,116387908930125+c.upper)) = pointBounds73356 := by
 decide +kernel
def cuts73357 : List PrefixCut := [⟨64,169340602,169340703⟩]
theorem checked73357 : checkPrefixCuts (2^48) 9618980865 10 Manual.Count131072.C073357.packed 64 cuts73357 = true := by
 decide +kernel
def cuts73358 : List PrefixCut := [⟨43,113038765,113038834⟩,
⟨64,166880315,166880418⟩]
theorem checked73358 : checkPrefixCuts (2^48) 9619111937 10 Manual.Count131072.C073358.packed 64 cuts73358 = true := by
 decide +kernel
def pointBounds73358 : List (Nat × Nat × Nat) := [(9619200000,116387970251188,116388360096696)]
theorem point_links_checked73358 : (cuts73358.take 1).map (fun c => (9619111937-1+2*2^10*c.k,116387857212423+c.lower,116388247057862+c.upper)) = pointBounds73358 := by
 decide +kernel
def cuts73359 : List PrefixCut := [⟨64,167697365,167697462⟩]
theorem checked73359 : checkPrefixCuts (2^48) 9619243009 10 Manual.Count131072.C073359.packed 64 cuts73359 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000104
