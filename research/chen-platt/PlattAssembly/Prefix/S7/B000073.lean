import PlattAssemblyKernel
import PlattCertificates.Count131072.C062336
import PlattCertificates.Count131072.C062337
import PlattCertificates.Count131072.C062338
import PlattCertificates.Count131072.C062339
import PlattCertificates.Count131072.C062340
import PlattCertificates.Count131072.C062341
import PlattCertificates.Count131072.C062342
import PlattCertificates.Count131072.C062343
import PlattCertificates.Count131072.C062344
import PlattCertificates.Count131072.C062345
import PlattCertificates.Count131072.C062346
import PlattCertificates.Count131072.C062347
import PlattCertificates.Count131072.C062348
import PlattCertificates.Count131072.C062349
import PlattCertificates.Count131072.C062350
import PlattCertificates.Count131072.C062351
import PlattCertificates.Count131072.C062352
import PlattCertificates.Count131072.C062353
import PlattCertificates.Count131072.C062354
import PlattCertificates.Count131072.C062355
import PlattCertificates.Count131072.C062356
import PlattCertificates.Count131072.C062357
import PlattCertificates.Count131072.C062358
import PlattCertificates.Count131072.C062359
import PlattCertificates.Count131072.C062360
import PlattCertificates.Count131072.C062361
import PlattCertificates.Count131072.C062362
import PlattCertificates.Count131072.C062363
import PlattCertificates.Count131072.C062364
import PlattCertificates.Count131072.C062365
import PlattCertificates.Count131072.C062366
import PlattCertificates.Count131072.C062367
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62336 : List PrefixCut := [⟨64,197612579,197612695⟩]
theorem checked62336 : checkPrefixCuts (2^48) 8174436353 10 Manual.Count131072.C062336.packed 64 cuts62336 = true := by
 decide +kernel
def cuts62337 : List PrefixCut := [⟨52,159664786,159664880⟩,
⟨64,196438697,196438812⟩]
theorem checked62337 : checkPrefixCuts (2^48) 8174567425 10 Manual.Count131072.C062337.packed 64 cuts62337 = true := by
 decide +kernel
def pointBounds62337 : List (Nat × Nat × Nat) := [(8174673920,114388363322094,114388751999375)]
theorem point_links_checked62337 : (cuts62337.take 1).map (fun c => (8174567425-1+2*2^10*c.k,114388203657308+c.lower,114388592334495+c.upper)) = pointBounds62337 := by
 decide +kernel
def cuts62338 : List PrefixCut := [⟨64,195884630,195884742⟩]
theorem checked62338 : checkPrefixCuts (2^48) 8174698497 10 Manual.Count131072.C062338.packed 64 cuts62338 = true := by
 decide +kernel
def cuts62339 : List PrefixCut := [⟨49,150569753,150569840⟩,
⟨64,195984783,195984898⟩]
theorem checked62339 : checkPrefixCuts (2^48) 8174829569 10 Manual.Count131072.C062339.packed 64 cuts62339 = true := by
 decide +kernel
def pointBounds62339 : List (Nat × Nat × Nat) := [(8174929920,114388746550388,114389135227889)]
theorem point_links_checked62339 : (cuts62339.take 1).map (fun c => (8174829569-1+2*2^10*c.k,114388595980635+c.lower,114388984658049+c.upper)) = pointBounds62339 := by
 decide +kernel
def cuts62340 : List PrefixCut := [⟨64,199183739,199183854⟩]
theorem checked62340 : checkPrefixCuts (2^48) 8174960641 10 Manual.Count131072.C062340.packed 64 cuts62340 = true := by
 decide +kernel
def cuts62341 : List PrefixCut := [⟨46,141681903,141681983⟩,
⟨64,197665601,197665714⟩]
theorem checked62341 : checkPrefixCuts (2^48) 8175091713 10 Manual.Count131072.C062341.packed 64 cuts62341 = true := by
 decide +kernel
def pointBounds62341 : List (Nat × Nat × Nat) := [(8175185920,114389132831060,114389521508784)]
theorem point_links_checked62341 : (cuts62341.take 1).map (fun c => (8175091713-1+2*2^10*c.k,114388991149157+c.lower,114389379826801+c.upper)) = pointBounds62341 := by
 decide +kernel
def cuts62342 : List PrefixCut := [⟨64,196354081,196354195⟩]
theorem checked62342 : checkPrefixCuts (2^48) 8175222785 10 Manual.Count131072.C062342.packed 64 cuts62342 = true := by
 decide +kernel
def cuts62343 : List PrefixCut := [⟨43,133724195,133724273⟩,
⟨64,201308772,201308889⟩]
theorem checked62343 : checkPrefixCuts (2^48) 8175353857 10 Manual.Count131072.C062343.packed 64 cuts62343 = true := by
 decide +kernel
def pointBounds62343 : List (Nat × Nat × Nat) := [(8175441920,114389518893034,114389907570983)]
theorem point_links_checked62343 : (cuts62343.take 1).map (fun c => (8175353857-1+2*2^10*c.k,114389385168839+c.lower,114389773846710+c.upper)) = pointBounds62343 := by
 decide +kernel
def cuts62344 : List PrefixCut := [⟨64,197311803,197311911⟩]
theorem checked62344 : checkPrefixCuts (2^48) 8175484929 10 Manual.Count131072.C062344.packed 64 cuts62344 = true := by
 decide +kernel
def cuts62345 : List PrefixCut := [⟨40,123322581,123322650⟩,
⟨64,197515220,197515327⟩]
theorem checked62345 : checkPrefixCuts (2^48) 8175616001 10 Manual.Count131072.C062345.packed 64 cuts62345 = true := by
 decide +kernel
def pointBounds62345 : List (Nat × Nat × Nat) := [(8175697920,114389907111995,114390295790160)]
theorem point_links_checked62345 : (cuts62345.take 1).map (fun c => (8175616001-1+2*2^10*c.k,114389783789414+c.lower,114390172467510+c.upper)) = pointBounds62345 := by
 decide +kernel
def cuts62346 : List PrefixCut := [⟨64,197684174,197684289⟩]
theorem checked62346 : checkPrefixCuts (2^48) 8175747073 10 Manual.Count131072.C062346.packed 64 cuts62346 = true := by
 decide +kernel
def cuts62347 : List PrefixCut := [⟨37,114746266,114746329⟩,
⟨64,199815493,199815604⟩]
theorem checked62347 : checkPrefixCuts (2^48) 8175878145 10 Manual.Count131072.C062347.packed 64 cuts62347 = true := by
 decide +kernel
def pointBounds62347 : List (Nat × Nat × Nat) := [(8175953920,114390293735074,114390682413455)]
theorem point_links_checked62347 : (cuts62347.take 1).map (fun c => (8175878145-1+2*2^10*c.k,114390178988808+c.lower,114390567667126+c.upper)) = pointBounds62347 := by
 decide +kernel
def cuts62348 : List PrefixCut := [⟨64,193649938,193650047⟩]
theorem checked62348 : checkPrefixCuts (2^48) 8176009217 10 Manual.Count131072.C062348.packed 64 cuts62348 = true := by
 decide +kernel
def cuts62349 : List PrefixCut := [⟨34,105757379,105757439⟩,
⟨64,196917310,196917425⟩]
theorem checked62349 : checkPrefixCuts (2^48) 8176140289 10 Manual.Count131072.C062349.packed 64 cuts62349 = true := by
 decide +kernel
def pointBounds62349 : List (Nat × Nat × Nat) := [(8176209920,114390678211618,114391066890216)]
theorem point_links_checked62349 : (cuts62349.take 1).map (fun c => (8176140289-1+2*2^10*c.k,114390572454239+c.lower,114390961132777+c.upper)) = pointBounds62349 := by
 decide +kernel
def cuts62350 : List PrefixCut := [⟨64,197499372,197499487⟩]
theorem checked62350 : checkPrefixCuts (2^48) 8176271361 10 Manual.Count131072.C062350.packed 64 cuts62350 = true := by
 decide +kernel
def cuts62351 : List PrefixCut := [⟨31,95082243,95082299⟩,
⟨64,194811069,194811184⟩]
theorem checked62351 : checkPrefixCuts (2^48) 8176402433 10 Manual.Count131072.C062351.packed 64 cuts62351 = true := by
 decide +kernel
def pointBounds62351 : List (Nat × Nat × Nat) := [(8176465920,114391061953164,114391450631988)]
theorem point_links_checked62351 : (cuts62351.take 1).map (fun c => (8176402433-1+2*2^10*c.k,114390966870921+c.lower,114391355549689+c.upper)) = pointBounds62351 := by
 decide +kernel
def cuts62352 : List PrefixCut := [⟨64,196047231,196047341⟩]
theorem checked62352 : checkPrefixCuts (2^48) 8176533505 10 Manual.Count131072.C062352.packed 64 cuts62352 = true := by
 decide +kernel
def cuts62353 : List PrefixCut := [⟨28,84786433,84786484⟩,
⟨64,195011354,195011464⟩]
theorem checked62353 : checkPrefixCuts (2^48) 8176664577 10 Manual.Count131072.C062353.packed 64 cuts62353 = true := by
 decide +kernel
def pointBounds62353 : List (Nat × Nat × Nat) := [(8176721920,114391442515654,114391831194698)]
theorem point_links_checked62353 : (cuts62353.take 1).map (fun c => (8176664577-1+2*2^10*c.k,114391357729221+c.lower,114391746408214+c.upper)) = pointBounds62353 := by
 decide +kernel
def cuts62354 : List PrefixCut := [⟨64,198691530,198691645⟩]
theorem checked62354 : checkPrefixCuts (2^48) 8176795649 10 Manual.Count131072.C062354.packed 64 cuts62354 = true := by
 decide +kernel
def cuts62355 : List PrefixCut := [⟨25,76900887,76900932⟩,
⟨64,194867424,194867538⟩]
theorem checked62355 : checkPrefixCuts (2^48) 8176926721 10 Manual.Count131072.C062355.packed 64 cuts62355 = true := by
 decide +kernel
def pointBounds62355 : List (Nat × Nat × Nat) := [(8176977920,114391828332992,114392217012255)]
theorem point_links_checked62355 : (cuts62355.take 1).map (fun c => (8176926721-1+2*2^10*c.k,114391751432105+c.lower,114392140111323+c.upper)) = pointBounds62355 := by
 decide +kernel
def cuts62356 : List PrefixCut := [⟨64,198409794,198409910⟩]
theorem checked62356 : checkPrefixCuts (2^48) 8177057793 10 Manual.Count131072.C062356.packed 64 cuts62356 = true := by
 decide +kernel
def cuts62357 : List PrefixCut := [⟨22,70117343,70117385⟩,
⟨64,199508110,199508223⟩]
theorem checked62357 : checkPrefixCuts (2^48) 8177188865 10 Manual.Count131072.C062357.packed 64 cuts62357 = true := by
 decide +kernel
def pointBounds62357 : List (Nat × Nat × Nat) := [(8177233920,114392214826666,114392603506156)]
theorem point_links_checked62357 : (cuts62357.take 1).map (fun c => (8177188865-1+2*2^10*c.k,114392144709323+c.lower,114392533388771+c.upper)) = pointBounds62357 := by
 decide +kernel
def cuts62358 : List PrefixCut := [⟨64,194995739,194995852⟩]
theorem checked62358 : checkPrefixCuts (2^48) 8177319937 10 Manual.Count131072.C062358.packed 64 cuts62358 = true := by
 decide +kernel
def cuts62359 : List PrefixCut := [⟨19,58446482,58446515⟩,
⟨64,198847714,198847826⟩]
theorem checked62359 : checkPrefixCuts (2^48) 8177451009 10 Manual.Count131072.C062359.packed 64 cuts62359 = true := by
 decide +kernel
def pointBounds62359 : List (Nat × Nat × Nat) := [(8177489920,114392597659654,114392986339361)]
theorem point_links_checked62359 : (cuts62359.take 1).map (fun c => (8177451009-1+2*2^10*c.k,114392539213172+c.lower,114392927892846+c.upper)) = pointBounds62359 := by
 decide +kernel
def cuts62360 : List PrefixCut := [⟨64,200290165,200290286⟩]
theorem checked62360 : checkPrefixCuts (2^48) 8177582081 10 Manual.Count131072.C062360.packed 64 cuts62360 = true := by
 decide +kernel
def cuts62361 : List PrefixCut := [⟨16,49357832,49357858⟩,
⟨64,195433804,195433919⟩]
theorem checked62361 : checkPrefixCuts (2^48) 8177713153 10 Manual.Count131072.C062361.packed 64 cuts62361 = true := by
 decide +kernel
def pointBounds62361 : List (Nat × Nat × Nat) := [(8177745920,114392987708883,114393376388816)]
theorem point_links_checked62361 : (cuts62361.take 1).map (fun c => (8177713153-1+2*2^10*c.k,114392938351051+c.lower,114393327030958+c.upper)) = pointBounds62361 := by
 decide +kernel
def cuts62362 : List PrefixCut := [⟨64,198906969,198907080⟩]
theorem checked62362 : checkPrefixCuts (2^48) 8177844225 10 Manual.Count131072.C062362.packed 64 cuts62362 = true := by
 decide +kernel
def cuts62363 : List PrefixCut := [⟨13,39133946,39133966⟩,
⟨64,194739180,194739289⟩]
theorem checked62363 : checkPrefixCuts (2^48) 8177975297 10 Manual.Count131072.C062363.packed 64 cuts62363 = true := by
 decide +kernel
def pointBounds62363 : List (Nat × Nat × Nat) := [(8178001920,114393371825770,114393760505923)]
theorem point_links_checked62363 : (cuts62363.take 1).map (fun c => (8177975297-1+2*2^10*c.k,114393332691824+c.lower,114393721371957+c.upper)) = pointBounds62363 := by
 decide +kernel
def cuts62364 : List PrefixCut := [⟨64,196732284,196732395⟩]
theorem checked62364 : checkPrefixCuts (2^48) 8178106369 10 Manual.Count131072.C062364.packed 64 cuts62364 = true := by
 decide +kernel
def cuts62365 : List PrefixCut := [⟨10,31698524,31698541⟩,
⟨64,199344858,199344969⟩]
theorem checked62365 : checkPrefixCuts (2^48) 8178237441 10 Manual.Count131072.C062365.packed 64 cuts62365 = true := by
 decide +kernel
def pointBounds62365 : List (Nat × Nat × Nat) := [(8178257920,114393755861812,114394144542182)]
theorem point_links_checked62365 : (cuts62365.take 1).map (fun c => (8178237441-1+2*2^10*c.k,114393724163288+c.lower,114394112843641+c.upper)) = pointBounds62365 := by
 decide +kernel
def cuts62366 : List PrefixCut := [⟨64,197138982,197139096⟩]
theorem checked62366 : checkPrefixCuts (2^48) 8178368513 10 Manual.Count131072.C062366.packed 64 cuts62366 = true := by
 decide +kernel
def cuts62367 : List PrefixCut := [⟨7,22026507,22026520⟩,
⟨64,196894936,196895040⟩]
theorem checked62367 : checkPrefixCuts (2^48) 8178499585 10 Manual.Count131072.C062367.packed 64 cuts62367 = true := by
 decide +kernel
def pointBounds62367 : List (Nat × Nat × Nat) := [(8178513920,114394142673635,114394531354226)]
theorem point_links_checked62367 : (cuts62367.take 1).map (fun c => (8178499585-1+2*2^10*c.k,114394120647128+c.lower,114394509327706+c.upper)) = pointBounds62367 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000073
