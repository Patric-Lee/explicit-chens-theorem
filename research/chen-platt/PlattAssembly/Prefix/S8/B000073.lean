import PlattAssemblyKernel
import PlattCertificates.Count131072.C072336
import PlattCertificates.Count131072.C072337
import PlattCertificates.Count131072.C072338
import PlattCertificates.Count131072.C072339
import PlattCertificates.Count131072.C072340
import PlattCertificates.Count131072.C072341
import PlattCertificates.Count131072.C072342
import PlattCertificates.Count131072.C072343
import PlattCertificates.Count131072.C072344
import PlattCertificates.Count131072.C072345
import PlattCertificates.Count131072.C072346
import PlattCertificates.Count131072.C072347
import PlattCertificates.Count131072.C072348
import PlattCertificates.Count131072.C072349
import PlattCertificates.Count131072.C072350
import PlattCertificates.Count131072.C072351
import PlattCertificates.Count131072.C072352
import PlattCertificates.Count131072.C072353
import PlattCertificates.Count131072.C072354
import PlattCertificates.Count131072.C072355
import PlattCertificates.Count131072.C072356
import PlattCertificates.Count131072.C072357
import PlattCertificates.Count131072.C072358
import PlattCertificates.Count131072.C072359
import PlattCertificates.Count131072.C072360
import PlattCertificates.Count131072.C072361
import PlattCertificates.Count131072.C072362
import PlattCertificates.Count131072.C072363
import PlattCertificates.Count131072.C072364
import PlattCertificates.Count131072.C072365
import PlattCertificates.Count131072.C072366
import PlattCertificates.Count131072.C072367
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72336 : List PrefixCut := [⟨64,168050087,168050186⟩]
theorem checked72336 : checkPrefixCuts (2^48) 9485156353 10 Manual.Count131072.C072336.packed 64 cuts72336 = true := by
 decide +kernel
def cuts72337 : List PrefixCut := [⟨15,40150067,40150091⟩,
⟨64,167572969,167573075⟩]
theorem checked72337 : checkPrefixCuts (2^48) 9485287425 10 Manual.Count131072.C072337.packed 64 cuts72337 = true := by
 decide +kernel
def pointBounds72337 : List (Nat × Nat × Nat) := [(9485318144,116216286385449,116216676128619)]
theorem point_links_checked72337 : (cuts72337.take 1).map (fun c => (9485287425-1+2*2^10*c.k,116216246235382+c.lower,116216635978528+c.upper)) = pointBounds72337 := by
 decide +kernel
def cuts72338 : List PrefixCut := [⟨64,169113704,169113805⟩]
theorem checked72338 : checkPrefixCuts (2^48) 9485418497 10 Manual.Count131072.C072338.packed 64 cuts72338 = true := by
 decide +kernel
def cuts72339 : List PrefixCut := [⟨32,84303751,84303797⟩,
⟨64,169942241,169942341⟩]
theorem checked72339 : checkPrefixCuts (2^48) 9485549569 10 Manual.Count131072.C072339.packed 64 cuts72339 = true := by
 decide +kernel
def pointBounds72339 : List (Nat × Nat × Nat) := [(9485615104,116216667225806,116217056969205)]
theorem point_links_checked72339 : (cuts72339.take 1).map (fun c => (9485549569-1+2*2^10*c.k,116216582922055+c.lower,116216972665408+c.upper)) = pointBounds72339 := by
 decide +kernel
def cuts72340 : List PrefixCut := [⟨64,166942881,166942983⟩]
theorem checked72340 : checkPrefixCuts (2^48) 9485680641 10 Manual.Count131072.C072340.packed 64 cuts72340 = true := by
 decide +kernel
def cuts72341 : List PrefixCut := [⟨49,132431024,132431097⟩,
⟨64,171747605,171747701⟩]
theorem checked72341 : checkPrefixCuts (2^48) 9485811713 10 Manual.Count131072.C072341.packed 64 cuts72341 = true := by
 decide +kernel
def pointBounds72341 : List (Nat × Nat × Nat) := [(9485912064,116217052238201,116217441981829)]
theorem point_links_checked72341 : (cuts72341.take 1).map (fun c => (9485811713-1+2*2^10*c.k,116216919807177+c.lower,116217309550732+c.upper)) = pointBounds72341 := by
 decide +kernel
def cuts72342 : List PrefixCut := [⟨64,171359481,171359586⟩]
theorem checked72342 : checkPrefixCuts (2^48) 9485942785 10 Manual.Count131072.C072342.packed 64 cuts72342 = true := by
 decide +kernel
def cuts72343 : List PrefixCut := [⟨64,169458107,169458203⟩]
theorem checked72343 : checkPrefixCuts (2^48) 9486073857 10 Manual.Count131072.C072343.packed 64 cuts72343 = true := by
 decide +kernel
def cuts72344 : List PrefixCut := [⟨2,5251947,5251950⟩,
⟨64,169604113,169604214⟩]
theorem checked72344 : checkPrefixCuts (2^48) 9486204929 10 Manual.Count131072.C072344.packed 64 cuts72344 = true := by
 decide +kernel
def pointBounds72344 : List (Nat × Nat × Nat) := [(9486209024,116217437624317,116217827368172)]
theorem point_links_checked72344 : (cuts72344.take 1).map (fun c => (9486204929-1+2*2^10*c.k,116217432372370+c.lower,116217822116222+c.upper)) = pointBounds72344 := by
 decide +kernel
def cuts72345 : List PrefixCut := [⟨64,169216040,169216146⟩]
theorem checked72345 : checkPrefixCuts (2^48) 9486336001 10 Manual.Count131072.C072345.packed 64 cuts72345 = true := by
 decide +kernel
def cuts72346 : List PrefixCut := [⟨19,50262914,50262945⟩,
⟨64,168560942,168561041⟩]
theorem checked72346 : checkPrefixCuts (2^48) 9486467073 10 Manual.Count131072.C072346.packed 64 cuts72346 = true := by
 decide +kernel
def pointBounds72346 : List (Nat × Nat × Nat) := [(9486505984,116217821455437,116218211199527)]
theorem point_links_checked72346 : (cuts72346.take 1).map (fun c => (9486467073-1+2*2^10*c.k,116217771192523+c.lower,116218160936582+c.upper)) = pointBounds72346 := by
 decide +kernel
def cuts72347 : List PrefixCut := [⟨64,171495999,171496103⟩]
theorem checked72347 : checkPrefixCuts (2^48) 9486598145 10 Manual.Count131072.C072347.packed 64 cuts72347 = true := by
 decide +kernel
def cuts72348 : List PrefixCut := [⟨36,94529476,94529535⟩,
⟨64,167844203,167844304⟩]
theorem checked72348 : checkPrefixCuts (2^48) 9486729217 10 Manual.Count131072.C072348.packed 64 cuts72348 = true := by
 decide +kernel
def pointBounds72348 : List (Nat × Nat × Nat) := [(9486802944,116218205778940,116218595523261)]
theorem point_links_checked72348 : (cuts72348.take 1).map (fun c => (9486729217-1+2*2^10*c.k,116218111249464+c.lower,116218500993726+c.upper)) = pointBounds72348 := by
 decide +kernel
def cuts72349 : List PrefixCut := [⟨64,169058344,169058440⟩]
theorem checked72349 : checkPrefixCuts (2^48) 9486860289 10 Manual.Count131072.C072349.packed 64 cuts72349 = true := by
 decide +kernel
def cuts72350 : List PrefixCut := [⟨53,140781274,140781363⟩,
⟨64,170153769,170153880⟩]
theorem checked72350 : checkPrefixCuts (2^48) 9486991361 10 Manual.Count131072.C072350.packed 64 cuts72350 = true := by
 decide +kernel
def pointBounds72350 : List (Nat × Nat × Nat) := [(9487099904,116218588933285,116218978677833)]
theorem point_links_checked72350 : (cuts72350.take 1).map (fun c => (9486991361-1+2*2^10*c.k,116218448152011+c.lower,116218837896470+c.upper)) = pointBounds72350 := by
 decide +kernel
def cuts72351 : List PrefixCut := [⟨64,168282288,168282390⟩]
theorem checked72351 : checkPrefixCuts (2^48) 9487122433 10 Manual.Count131072.C072351.packed 64 cuts72351 = true := by
 decide +kernel
def cuts72352 : List PrefixCut := [⟨64,167686576,167686674⟩]
theorem checked72352 : checkPrefixCuts (2^48) 9487253505 10 Manual.Count131072.C072352.packed 64 cuts72352 = true := by
 decide +kernel
def cuts72353 : List PrefixCut := [⟨6,15516529,15516540⟩,
⟨64,170562076,170562183⟩]
theorem checked72353 : checkPrefixCuts (2^48) 9487384577 10 Manual.Count131072.C072353.packed 64 cuts72353 = true := by
 decide +kernel
def pointBounds72353 : List (Nat × Nat × Nat) := [(9487396864,116218969791173,116219359535954)]
theorem point_links_checked72353 : (cuts72353.take 1).map (fun c => (9487384577-1+2*2^10*c.k,116218954274644+c.lower,116219344019414+c.upper)) = pointBounds72353 := by
 decide +kernel
def cuts72354 : List PrefixCut := [⟨64,170085027,170085127⟩]
theorem checked72354 : checkPrefixCuts (2^48) 9487515649 10 Manual.Count131072.C072354.packed 64 cuts72354 = true := by
 decide +kernel
def cuts72355 : List PrefixCut := [⟨23,61114929,61114966⟩,
⟨64,168955331,168955427⟩]
theorem checked72355 : checkPrefixCuts (2^48) 9487646721 10 Manual.Count131072.C072355.packed 64 cuts72355 = true := by
 decide +kernel
def pointBounds72355 : List (Nat × Nat × Nat) := [(9487693824,116219356036676,116219745781690)]
theorem point_links_checked72355 : (cuts72355.take 1).map (fun c => (9487646721-1+2*2^10*c.k,116219294921747+c.lower,116219684666724+c.upper)) = pointBounds72355 := by
 decide +kernel
def cuts72356 : List PrefixCut := [⟨64,167706977,167707082⟩]
theorem checked72356 : checkPrefixCuts (2^48) 9487777793 10 Manual.Count131072.C072356.packed 64 cuts72356 = true := by
 decide +kernel
def cuts72357 : List PrefixCut := [⟨40,106829310,106829377⟩,
⟨64,169277002,169277105⟩]
theorem checked72357 : checkPrefixCuts (2^48) 9487908865 10 Manual.Count131072.C072357.packed 64 cuts72357 = true := by
 decide +kernel
def pointBounds72357 : List (Nat × Nat × Nat) := [(9487990784,116219738413365,116220128158610)]
theorem point_links_checked72357 : (cuts72357.take 1).map (fun c => (9487908865-1+2*2^10*c.k,116219631584055+c.lower,116220021329233+c.upper)) = pointBounds72357 := by
 decide +kernel
def cuts72358 : List PrefixCut := [⟨64,167376016,167376119⟩]
theorem checked72358 : checkPrefixCuts (2^48) 9488039937 10 Manual.Count131072.C072358.packed 64 cuts72358 = true := by
 decide +kernel
def cuts72359 : List PrefixCut := [⟨57,148209796,148209882⟩,
⟨64,167255039,167255136⟩]
theorem checked72359 : checkPrefixCuts (2^48) 9488171009 10 Manual.Count131072.C072359.packed 64 cuts72359 = true := by
 decide +kernel
def pointBounds72359 : List (Nat × Nat × Nat) := [(9488287744,116220116446869,116220506192339)]
theorem point_links_checked72359 : (cuts72359.take 1).map (fun c => (9488171009-1+2*2^10*c.k,116219968237073+c.lower,116220357982457+c.upper)) = pointBounds72359 := by
 decide +kernel
def cuts72360 : List PrefixCut := [⟨64,165947468,165947572⟩]
theorem checked72360 : checkPrefixCuts (2^48) 9488302081 10 Manual.Count131072.C072360.packed 64 cuts72360 = true := by
 decide +kernel
def cuts72361 : List PrefixCut := [⟨64,168288697,168288792⟩]
theorem checked72361 : checkPrefixCuts (2^48) 9488433153 10 Manual.Count131072.C072361.packed 64 cuts72361 = true := by
 decide +kernel
def cuts72362 : List PrefixCut := [⟨10,27558426,27558444⟩,
⟨64,167752416,167752520⟩]
theorem checked72362 : checkPrefixCuts (2^48) 9488564225 10 Manual.Count131072.C072362.packed 64 cuts72362 = true := by
 decide +kernel
def pointBounds72362 : List (Nat × Nat × Nat) := [(9488584704,116220497286703,116220887032401)]
theorem point_links_checked72362 : (cuts72362.take 1).map (fun c => (9488564225-1+2*2^10*c.k,116220469728277+c.lower,116220859473957+c.upper)) = pointBounds72362 := by
 decide +kernel
def cuts72363 : List PrefixCut := [⟨64,170152890,170152993⟩]
theorem checked72363 : checkPrefixCuts (2^48) 9488695297 10 Manual.Count131072.C072363.packed 64 cuts72363 = true := by
 decide +kernel
def cuts72364 : List PrefixCut := [⟨27,70421718,70421755⟩,
⟨64,169112302,169112396⟩]
theorem checked72364 : checkPrefixCuts (2^48) 9488826369 10 Manual.Count131072.C072364.packed 64 cuts72364 = true := by
 decide +kernel
def pointBounds72364 : List (Nat × Nat × Nat) := [(9488881664,116220878055301,116221267801225)]
theorem point_links_checked72364 : (cuts72364.take 1).map (fun c => (9488826369-1+2*2^10*c.k,116220807633583+c.lower,116221197379470+c.upper)) = pointBounds72364 := by
 decide +kernel
def cuts72365 : List PrefixCut := [⟨64,170800771,170800875⟩]
theorem checked72365 : checkPrefixCuts (2^48) 9488957441 10 Manual.Count131072.C072365.packed 64 cuts72365 = true := by
 decide +kernel
def cuts72366 : List PrefixCut := [⟨44,116189447,116189516⟩,
⟨64,169789875,169789975⟩]
theorem checked72366 : checkPrefixCuts (2^48) 9489088513 10 Manual.Count131072.C072366.packed 64 cuts72366 = true := by
 decide +kernel
def pointBounds72366 : List (Nat × Nat × Nat) := [(9489178624,116221263736103,116221653482257)]
theorem point_links_checked72366 : (cuts72366.take 1).map (fun c => (9489088513-1+2*2^10*c.k,116221147546656+c.lower,116221537292741+c.upper)) = pointBounds72366 := by
 decide +kernel
def cuts72367 : List PrefixCut := [⟨64,168541704,168541801⟩]
theorem checked72367 : checkPrefixCuts (2^48) 9489219585 10 Manual.Count131072.C072367.packed 64 cuts72367 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000073
