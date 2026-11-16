import PlattAssemblyKernel
import PlattCertificates.Count131072.C074320
import PlattCertificates.Count131072.C074321
import PlattCertificates.Count131072.C074322
import PlattCertificates.Count131072.C074323
import PlattCertificates.Count131072.C074324
import PlattCertificates.Count131072.C074325
import PlattCertificates.Count131072.C074326
import PlattCertificates.Count131072.C074327
import PlattCertificates.Count131072.C074328
import PlattCertificates.Count131072.C074329
import PlattCertificates.Count131072.C074330
import PlattCertificates.Count131072.C074331
import PlattCertificates.Count131072.C074332
import PlattCertificates.Count131072.C074333
import PlattCertificates.Count131072.C074334
import PlattCertificates.Count131072.C074335
import PlattCertificates.Count131072.C074336
import PlattCertificates.Count131072.C074337
import PlattCertificates.Count131072.C074338
import PlattCertificates.Count131072.C074339
import PlattCertificates.Count131072.C074340
import PlattCertificates.Count131072.C074341
import PlattCertificates.Count131072.C074342
import PlattCertificates.Count131072.C074343
import PlattCertificates.Count131072.C074344
import PlattCertificates.Count131072.C074345
import PlattCertificates.Count131072.C074346
import PlattCertificates.Count131072.C074347
import PlattCertificates.Count131072.C074348
import PlattCertificates.Count131072.C074349
import PlattCertificates.Count131072.C074350
import PlattCertificates.Count131072.C074351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000135
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74320 : List PrefixCut := [⟨64,164114539,164114632⟩]
theorem checked74320 : checkPrefixCuts (2^48) 9745203201 10 Manual.Count131072.C074320.packed 64 cuts74320 = true := by
 decide +kernel
def cuts74321 : List PrefixCut := [⟨64,167058381,167058481⟩]
theorem checked74321 : checkPrefixCuts (2^48) 9745334273 10 Manual.Count131072.C074321.packed 64 cuts74321 = true := by
 decide +kernel
def cuts74322 : List PrefixCut := [⟨17,42197480,42197506⟩,
⟨64,163041464,163041555⟩]
theorem checked74322 : checkPrefixCuts (2^48) 9745465345 10 Manual.Count131072.C074322.packed 64 cuts74322 = true := by
 decide +kernel
def pointBounds74322 : List (Nat × Nat × Nat) := [(9745500160,116547711110798,116548101051622)]
theorem point_links_checked74322 : (cuts74322.take 1).map (fun c => (9745465345-1+2*2^10*c.k,116547668913318+c.lower,116548058854116+c.upper)) = pointBounds74322 := by
 decide +kernel
def cuts74323 : List PrefixCut := [⟨64,164136798,164136896⟩]
theorem checked74323 : checkPrefixCuts (2^48) 9745596417 10 Manual.Count131072.C074323.packed 64 cuts74323 = true := by
 decide +kernel
def cuts74324 : List PrefixCut := [⟨38,96725017,96725073⟩,
⟨64,163990188,163990279⟩]
theorem checked74324 : checkPrefixCuts (2^48) 9745727489 10 Manual.Count131072.C074324.packed 64 cuts74324 = true := by
 decide +kernel
def pointBounds74324 : List (Nat × Nat × Nat) := [(9745805312,116548092816597,116548482757640)]
theorem point_links_checked74324 : (cuts74324.take 1).map (fun c => (9745727489-1+2*2^10*c.k,116547996091580+c.lower,116548386032567+c.upper)) = pointBounds74324 := by
 decide +kernel
def cuts74325 : List PrefixCut := [⟨64,162283992,162284089⟩]
theorem checked74325 : checkPrefixCuts (2^48) 9745858561 10 Manual.Count131072.C074325.packed 64 cuts74325 = true := by
 decide +kernel
def cuts74326 : List PrefixCut := [⟨59,151336024,151336121⟩,
⟨64,164823323,164823428⟩]
theorem checked74326 : checkPrefixCuts (2^48) 9745989633 10 Manual.Count131072.C074326.packed 64 cuts74326 = true := by
 decide +kernel
def pointBounds74326 : List (Nat × Nat × Nat) := [(9746110464,116548473701784,116548863643056)]
theorem point_links_checked74326 : (cuts74326.take 1).map (fun c => (9745989633-1+2*2^10*c.k,116548322365760+c.lower,116548712306935+c.upper)) = pointBounds74326 := by
 decide +kernel
def cuts74327 : List PrefixCut := [⟨64,164676705,164676805⟩]
theorem checked74327 : checkPrefixCuts (2^48) 9746120705 10 Manual.Count131072.C074327.packed 64 cuts74327 = true := by
 decide +kernel
def cuts74328 : List PrefixCut := [⟨64,163721450,163721549⟩]
theorem checked74328 : checkPrefixCuts (2^48) 9746251777 10 Manual.Count131072.C074328.packed 64 cuts74328 = true := by
 decide +kernel
def cuts74329 : List PrefixCut := [⟨16,40345198,40345225⟩,
⟨64,163834754,163834847⟩]
theorem checked74329 : checkPrefixCuts (2^48) 9746382849 10 Manual.Count131072.C074329.packed 64 cuts74329 = true := by
 decide +kernel
def pointBounds74329 : List (Nat × Nat × Nat) := [(9746415616,116548855932436,116549245873942)]
theorem point_links_checked74329 : (cuts74329.take 1).map (fun c => (9746382849-1+2*2^10*c.k,116548815587238+c.lower,116549205528717+c.upper)) = pointBounds74329 := by
 decide +kernel
def cuts74330 : List PrefixCut := [⟨64,166489462,166489557⟩]
theorem checked74330 : checkPrefixCuts (2^48) 9746513921 10 Manual.Count131072.C074330.packed 64 cuts74330 = true := by
 decide +kernel
def cuts74331 : List PrefixCut := [⟨37,92557343,92557395⟩,
⟨64,162732950,162733045⟩]
theorem checked74331 : checkPrefixCuts (2^48) 9746644993 10 Manual.Count131072.C074331.packed 64 cuts74331 = true := by
 decide +kernel
def pointBounds74331 : List (Nat × Nat × Nat) := [(9746720768,116549238468797,116549628410516)]
theorem point_links_checked74331 : (cuts74331.take 1).map (fun c => (9746644993-1+2*2^10*c.k,116549145911454+c.lower,116549535853121+c.upper)) = pointBounds74331 := by
 decide +kernel
def cuts74332 : List PrefixCut := [⟨64,164983300,164983401⟩]
theorem checked74332 : checkPrefixCuts (2^48) 9746776065 10 Manual.Count131072.C074332.packed 64 cuts74332 = true := by
 decide +kernel
def cuts74333 : List PrefixCut := [⟨58,148289585,148289667⟩,
⟨64,163768199,163768290⟩]
theorem checked74333 : checkPrefixCuts (2^48) 9746907137 10 Manual.Count131072.C074333.packed 64 cuts74333 = true := by
 decide +kernel
def pointBounds74333 : List (Nat × Nat × Nat) := [(9747025920,116549621917289,116550011859234)]
theorem point_links_checked74333 : (cuts74333.take 1).map (fun c => (9746907137-1+2*2^10*c.k,116549473627704+c.lower,116549863569567+c.upper)) = pointBounds74333 := by
 decide +kernel
def cuts74334 : List PrefixCut := [⟨64,162610878,162610976⟩]
theorem checked74334 : checkPrefixCuts (2^48) 9747038209 10 Manual.Count131072.C074334.packed 64 cuts74334 = true := by
 decide +kernel
def cuts74335 : List PrefixCut := [⟨64,163272873,163272969⟩]
theorem checked74335 : checkPrefixCuts (2^48) 9747169281 10 Manual.Count131072.C074335.packed 64 cuts74335 = true := by
 decide +kernel
def cuts74336 : List PrefixCut := [⟨15,38031234,38031257⟩,
⟨64,163703833,163703928⟩]
theorem checked74336 : checkPrefixCuts (2^48) 9747300353 10 Manual.Count131072.C074336.packed 64 cuts74336 = true := by
 decide +kernel
def pointBounds74336 : List (Nat × Nat × Nat) := [(9747331072,116550001310888,116550391253059)]
theorem point_links_checked74336 : (cuts74336.take 1).map (fun c => (9747300353-1+2*2^10*c.k,116549963279654+c.lower,116550353221802+c.upper)) = pointBounds74336 := by
 decide +kernel
def cuts74337 : List PrefixCut := [⟨64,165087712,165087806⟩]
theorem checked74337 : checkPrefixCuts (2^48) 9747431425 10 Manual.Count131072.C074337.packed 64 cuts74337 = true := by
 decide +kernel
def cuts74338 : List PrefixCut := [⟨36,92924028,92924082⟩,
⟨64,164190331,164190428⟩]
theorem checked74338 : checkPrefixCuts (2^48) 9747562497 10 Manual.Count131072.C074338.packed 64 cuts74338 = true := by
 decide +kernel
def pointBounds74338 : List (Nat × Nat × Nat) := [(9747636224,116550384995227,116550774937618)]
theorem point_links_checked74338 : (cuts74338.take 1).map (fun c => (9747562497-1+2*2^10*c.k,116550292071199+c.lower,116550682013536+c.upper)) = pointBounds74338 := by
 decide +kernel
def cuts74339 : List PrefixCut := [⟨64,165834046,165834142⟩]
theorem checked74339 : checkPrefixCuts (2^48) 9747693569 10 Manual.Count131072.C074339.packed 64 cuts74339 = true := by
 decide +kernel
def cuts74340 : List PrefixCut := [⟨57,147813627,147813714⟩,
⟨64,166611444,166611543⟩]
theorem checked74340 : checkPrefixCuts (2^48) 9747824641 10 Manual.Count131072.C074340.packed 64 cuts74340 = true := by
 decide +kernel
def pointBounds74340 : List (Nat × Nat × Nat) := [(9747941376,116550769909203,116551159851820)]
theorem point_links_checked74340 : (cuts74340.take 1).map (fun c => (9747824641-1+2*2^10*c.k,116550622095576+c.lower,116551012038106+c.upper)) = pointBounds74340 := by
 decide +kernel
def cuts74341 : List PrefixCut := [⟨64,163808336,163808432⟩]
theorem checked74341 : checkPrefixCuts (2^48) 9747955713 10 Manual.Count131072.C074341.packed 64 cuts74341 = true := by
 decide +kernel
def cuts74342 : List PrefixCut := [⟨64,165654106,165654204⟩]
theorem checked74342 : checkPrefixCuts (2^48) 9748086785 10 Manual.Count131072.C074342.packed 64 cuts74342 = true := by
 decide +kernel
def cuts74343 : List PrefixCut := [⟨14,35804323,35804346⟩,
⟨64,164612403,164612510⟩]
theorem checked74343 : checkPrefixCuts (2^48) 9748217857 10 Manual.Count131072.C074343.packed 64 cuts74343 = true := by
 decide +kernel
def pointBounds74343 : List (Nat × Nat × Nat) := [(9748246528,116551153973785,116551543916631)]
theorem point_links_checked74343 : (cuts74343.take 1).map (fun c => (9748217857-1+2*2^10*c.k,116551118169462+c.lower,116551508112285+c.upper)) = pointBounds74343 := by
 decide +kernel
def cuts74344 : List PrefixCut := [⟨64,162848880,162848979⟩]
theorem checked74344 : checkPrefixCuts (2^48) 9748348929 10 Manual.Count131072.C074344.packed 64 cuts74344 = true := by
 decide +kernel
def cuts74345 : List PrefixCut := [⟨35,89479329,89479387⟩,
⟨64,164290358,164290470⟩]
theorem checked74345 : checkPrefixCuts (2^48) 9748480001 10 Manual.Count131072.C074345.packed 64 cuts74345 = true := by
 decide +kernel
def pointBounds74345 : List (Nat × Nat × Nat) := [(9748551680,116551535110074,116551925053161)]
theorem point_links_checked74345 : (cuts74345.take 1).map (fun c => (9748480001-1+2*2^10*c.k,116551445630745+c.lower,116551835573774+c.upper)) = pointBounds74345 := by
 decide +kernel
def cuts74346 : List PrefixCut := [⟨64,164605765,164605870⟩]
theorem checked74346 : checkPrefixCuts (2^48) 9748611073 10 Manual.Count131072.C074346.packed 64 cuts74346 = true := by
 decide +kernel
def cuts74347 : List PrefixCut := [⟨56,144565982,144566064⟩,
⟨64,164574679,164574774⟩]
theorem checked74347 : checkPrefixCuts (2^48) 9748742145 10 Manual.Count131072.C074347.packed 64 cuts74347 = true := by
 decide +kernel
def pointBounds74347 : List (Nat × Nat × Nat) := [(9748856832,116551919092850,116552309036178)]
theorem point_links_checked74347 : (cuts74347.take 1).map (fun c => (9748742145-1+2*2^10*c.k,116551774526868+c.lower,116552164470114+c.upper)) = pointBounds74347 := by
 decide +kernel
def cuts74348 : List PrefixCut := [⟨64,165871716,165871816⟩]
theorem checked74348 : checkPrefixCuts (2^48) 9748873217 10 Manual.Count131072.C074348.packed 64 cuts74348 = true := by
 decide +kernel
def cuts74349 : List PrefixCut := [⟨64,165407545,165407644⟩]
theorem checked74349 : checkPrefixCuts (2^48) 9749004289 10 Manual.Count131072.C074349.packed 64 cuts74349 = true := by
 decide +kernel
def cuts74350 : List PrefixCut := [⟨13,33000398,33000419⟩,
⟨64,162431541,162431638⟩]
theorem checked74350 : checkPrefixCuts (2^48) 9749135361 10 Manual.Count131072.C074350.packed 64 cuts74350 = true := by
 decide +kernel
def pointBounds74350 : List (Nat × Nat × Nat) := [(9749161984,116552303381206,116552693324767)]
theorem point_links_checked74350 : (cuts74350.take 1).map (fun c => (9749135361-1+2*2^10*c.k,116552270380808+c.lower,116552660324348+c.upper)) = pointBounds74350 := by
 decide +kernel
def cuts74351 : List PrefixCut := [⟨64,162775824,162775919⟩]
theorem checked74351 : checkPrefixCuts (2^48) 9749266433 10 Manual.Count131072.C074351.packed 64 cuts74351 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000135
