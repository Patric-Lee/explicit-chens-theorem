import PlattAssemblyKernel
import PlattCertificates.Count131072.C070320
import PlattCertificates.Count131072.C070321
import PlattCertificates.Count131072.C070322
import PlattCertificates.Count131072.C070323
import PlattCertificates.Count131072.C070324
import PlattCertificates.Count131072.C070325
import PlattCertificates.Count131072.C070326
import PlattCertificates.Count131072.C070327
import PlattCertificates.Count131072.C070328
import PlattCertificates.Count131072.C070329
import PlattCertificates.Count131072.C070330
import PlattCertificates.Count131072.C070331
import PlattCertificates.Count131072.C070332
import PlattCertificates.Count131072.C070333
import PlattCertificates.Count131072.C070334
import PlattCertificates.Count131072.C070335
import PlattCertificates.Count131072.C070336
import PlattCertificates.Count131072.C070337
import PlattCertificates.Count131072.C070338
import PlattCertificates.Count131072.C070339
import PlattCertificates.Count131072.C070340
import PlattCertificates.Count131072.C070341
import PlattCertificates.Count131072.C070342
import PlattCertificates.Count131072.C070343
import PlattCertificates.Count131072.C070344
import PlattCertificates.Count131072.C070345
import PlattCertificates.Count131072.C070346
import PlattCertificates.Count131072.C070347
import PlattCertificates.Count131072.C070348
import PlattCertificates.Count131072.C070349
import PlattCertificates.Count131072.C070350
import PlattCertificates.Count131072.C070351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70320 : List PrefixCut := [⟨64,176650972,176651070⟩]
theorem checked70320 : checkPrefixCuts (2^48) 9220915201 10 Manual.Count131072.C070320.packed 64 cuts70320 = true := by
 decide +kernel
def cuts70321 : List PrefixCut := [⟨13,35592409,35592428⟩,
⟨64,172436003,172436101⟩]
theorem checked70321 : checkPrefixCuts (2^48) 9221046273 10 Manual.Count131072.C070321.packed 64 cuts70321 = true := by
 decide +kernel
def pointBounds70321 : List (Nat × Nat × Nat) := [(9221072896,115869864192850,115870253731043)]
theorem point_links_checked70321 : (cuts70321.take 1).map (fun c => (9221046273-1+2*2^10*c.k,115869828600441+c.lower,115870218138615+c.upper)) = pointBounds70321 := by
 decide +kernel
def cuts70322 : List PrefixCut := [⟨64,174539761,174539862⟩]
theorem checked70322 : checkPrefixCuts (2^48) 9221177345 10 Manual.Count131072.C070322.packed 64 cuts70322 = true := by
 decide +kernel
def cuts70323 : List PrefixCut := [⟨26,70511156,70511196⟩,
⟨64,173194210,173194312⟩]
theorem checked70323 : checkPrefixCuts (2^48) 9221308417 10 Manual.Count131072.C070323.packed 64 cuts70323 = true := by
 decide +kernel
def pointBounds70323 : List (Nat × Nat × Nat) := [(9221361664,115870246087361,115870635625774)]
theorem point_links_checked70323 : (cuts70323.take 1).map (fun c => (9221308417-1+2*2^10*c.k,115870175576205+c.lower,115870565114578+c.upper)) = pointBounds70323 := by
 decide +kernel
def cuts70324 : List PrefixCut := [⟨64,172917038,172917135⟩]
theorem checked70324 : checkPrefixCuts (2^48) 9221439489 10 Manual.Count131072.C070324.packed 64 cuts70324 = true := by
 decide +kernel
def cuts70325 : List PrefixCut := [⟨39,105794104,105794167⟩,
⟨64,174959633,174959740⟩]
theorem checked70325 : checkPrefixCuts (2^48) 9221570561 10 Manual.Count131072.C070325.packed 64 cuts70325 = true := by
 decide +kernel
def pointBounds70325 : List (Nat × Nat × Nat) := [(9221650432,115870627481557,115871017020192)]
theorem point_links_checked70325 : (cuts70325.take 1).map (fun c => (9221570561-1+2*2^10*c.k,115870521687453+c.lower,115870911226025+c.upper)) = pointBounds70325 := by
 decide +kernel
def cuts70326 : List PrefixCut := [⟨64,174316175,174316278⟩]
theorem checked70326 : checkPrefixCuts (2^48) 9221701633 10 Manual.Count131072.C070326.packed 64 cuts70326 = true := by
 decide +kernel
def cuts70327 : List PrefixCut := [⟨52,141013887,141013977⟩,
⟨64,173550628,173550736⟩]
theorem checked70327 : checkPrefixCuts (2^48) 9221832705 10 Manual.Count131072.C070327.packed 64 cuts70327 = true := by
 decide +kernel
def pointBounds70327 : List (Nat × Nat × Nat) := [(9221939200,115871011977148,115871401516020)]
theorem point_links_checked70327 : (cuts70327.take 1).map (fun c => (9221832705-1+2*2^10*c.k,115870870963261+c.lower,115871260502043+c.upper)) = pointBounds70327 := by
 decide +kernel
def cuts70328 : List PrefixCut := [⟨64,173242943,173243045⟩]
theorem checked70328 : checkPrefixCuts (2^48) 9221963777 10 Manual.Count131072.C070328.packed 64 cuts70328 = true := by
 decide +kernel
def cuts70329 : List PrefixCut := [⟨64,171805972,171806070⟩]
theorem checked70329 : checkPrefixCuts (2^48) 9222094849 10 Manual.Count131072.C070329.packed 64 cuts70329 = true := by
 decide +kernel
def cuts70330 : List PrefixCut := [⟨1,2655358,2655360⟩,
⟨64,176015441,176015548⟩]
theorem checked70330 : checkPrefixCuts (2^48) 9222225921 10 Manual.Count131072.C070330.packed 64 cuts70330 = true := by
 decide +kernel
def pointBounds70330 : List (Nat × Nat × Nat) := [(9222227968,115871392218162,115871781757254)]
theorem point_links_checked70330 : (cuts70330.take 1).map (fun c => (9222225921-1+2*2^10*c.k,115871389562804+c.lower,115871779101894+c.upper)) = pointBounds70330 := by
 decide +kernel
def cuts70331 : List PrefixCut := [⟨64,175310965,175311065⟩]
theorem checked70331 : checkPrefixCuts (2^48) 9222356993 10 Manual.Count131072.C070331.packed 64 cuts70331 = true := by
 decide +kernel
def cuts70332 : List PrefixCut := [⟨14,36807659,36807682⟩,
⟨64,172622683,172622786⟩]
theorem checked70332 : checkPrefixCuts (2^48) 9222488065 10 Manual.Count131072.C070332.packed 64 cuts70332 = true := by
 decide +kernel
def pointBounds70332 : List (Nat × Nat × Nat) := [(9222516736,115871777696869,115872167236189)]
theorem point_links_checked70332 : (cuts70332.take 1).map (fun c => (9222488065-1+2*2^10*c.k,115871740889210+c.lower,115872130428507+c.upper)) = pointBounds70332 := by
 decide +kernel
def cuts70333 : List PrefixCut := [⟨64,176954047,176954150⟩]
theorem checked70333 : checkPrefixCuts (2^48) 9222619137 10 Manual.Count131072.C070333.packed 64 cuts70333 = true := by
 decide +kernel
def cuts70334 : List PrefixCut := [⟨27,73979352,73979396⟩,
⟨64,174174270,174174379⟩]
theorem checked70334 : checkPrefixCuts (2^48) 9222750209 10 Manual.Count131072.C070334.packed 64 cuts70334 = true := by
 decide +kernel
def pointBounds70334 : List (Nat × Nat × Nat) := [(9222805504,115872164445292,115872553984839)]
theorem point_links_checked70334 : (cuts70334.take 1).map (fun c => (9222750209-1+2*2^10*c.k,115872090465940+c.lower,115872480005443+c.upper)) = pointBounds70334 := by
 decide +kernel
def cuts70335 : List PrefixCut := [⟨64,174446460,174446565⟩]
theorem checked70335 : checkPrefixCuts (2^48) 9222881281 10 Manual.Count131072.C070335.packed 64 cuts70335 = true := by
 decide +kernel
def cuts70336 : List PrefixCut := [⟨40,108646307,108646368⟩,
⟨64,174749177,174749275⟩]
theorem checked70336 : checkPrefixCuts (2^48) 9223012353 10 Manual.Count131072.C070336.packed 64 cuts70336 = true := by
 decide +kernel
def pointBounds70336 : List (Nat × Nat × Nat) := [(9223094272,115872547732977,115872937272755)]
theorem point_links_checked70336 : (cuts70336.take 1).map (fun c => (9223012353-1+2*2^10*c.k,115872439086670+c.lower,115872828626387+c.upper)) = pointBounds70336 := by
 decide +kernel
def cuts70337 : List PrefixCut := [⟨64,173159742,173159845⟩]
theorem checked70337 : checkPrefixCuts (2^48) 9223143425 10 Manual.Count131072.C070337.packed 64 cuts70337 = true := by
 decide +kernel
def cuts70338 : List PrefixCut := [⟨53,145233792,145233875⟩,
⟨64,174713692,174713795⟩]
theorem checked70338 : checkPrefixCuts (2^48) 9223274497 10 Manual.Count131072.C070338.packed 64 cuts70338 = true := by
 decide +kernel
def pointBounds70338 : List (Nat × Nat × Nat) := [(9223383040,115872932229381,115873321769382)]
theorem point_links_checked70338 : (cuts70338.take 1).map (fun c => (9223274497-1+2*2^10*c.k,115872786995589+c.lower,115873176535507+c.upper)) = pointBounds70338 := by
 decide +kernel
def cuts70339 : List PrefixCut := [⟨64,174772247,174772346⟩]
theorem checked70339 : checkPrefixCuts (2^48) 9223405569 10 Manual.Count131072.C070339.packed 64 cuts70339 = true := by
 decide +kernel
def cuts70340 : List PrefixCut := [⟨64,174617168,174617270⟩]
theorem checked70340 : checkPrefixCuts (2^48) 9223536641 10 Manual.Count131072.C070340.packed 64 cuts70340 = true := by
 decide +kernel
def cuts70341 : List PrefixCut := [⟨2,5706601,5706605⟩,
⟨64,174492623,174492728⟩]
theorem checked70341 : checkPrefixCuts (2^48) 9223667713 10 Manual.Count131072.C070341.packed 64 cuts70341 = true := by
 decide +kernel
def pointBounds70341 : List (Nat × Nat × Nat) := [(9223671808,115873316805297,115873706345523)]
theorem point_links_checked70341 : (cuts70341.take 1).map (fun c => (9223667713-1+2*2^10*c.k,115873311098696+c.lower,115873700638918+c.upper)) = pointBounds70341 := by
 decide +kernel
def cuts70342 : List PrefixCut := [⟨64,177206058,177206157⟩]
theorem checked70342 : checkPrefixCuts (2^48) 9223798785 10 Manual.Count131072.C070342.packed 64 cuts70342 = true := by
 decide +kernel
def cuts70343 : List PrefixCut := [⟨15,39426250,39426271⟩,
⟨64,172412599,172412700⟩]
theorem checked70343 : checkPrefixCuts (2^48) 9223929857 10 Manual.Count131072.C070343.packed 64 cuts70343 = true := by
 decide +kernel
def pointBounds70343 : List (Nat × Nat × Nat) := [(9223960576,115873702223627,115874091764074)]
theorem point_links_checked70343 : (cuts70343.take 1).map (fun c => (9223929857-1+2*2^10*c.k,115873662797377+c.lower,115874052337803+c.upper)) = pointBounds70343 := by
 decide +kernel
def cuts70344 : List PrefixCut := [⟨64,175339612,175339711⟩]
theorem checked70344 : checkPrefixCuts (2^48) 9224060929 10 Manual.Count131072.C070344.packed 64 cuts70344 = true := by
 decide +kernel
def cuts70345 : List PrefixCut := [⟨28,75615580,75615621⟩,
⟨64,173475728,173475827⟩]
theorem checked70345 : checkPrefixCuts (2^48) 9224192001 10 Manual.Count131072.C070345.packed 64 cuts70345 = true := by
 decide +kernel
def pointBounds70345 : List (Nat × Nat × Nat) := [(9224249344,115874086165168,115874475705835)]
theorem point_links_checked70345 : (cuts70345.take 1).map (fun c => (9224192001-1+2*2^10*c.k,115874010549588+c.lower,115874400090214+c.upper)) = pointBounds70345 := by
 decide +kernel
def cuts70346 : List PrefixCut := [⟨64,172862971,172863083⟩]
theorem checked70346 : checkPrefixCuts (2^48) 9224323073 10 Manual.Count131072.C070346.packed 64 cuts70346 = true := by
 decide +kernel
def cuts70347 : List PrefixCut := [⟨41,110643217,110643282⟩,
⟨64,173104624,173104730⟩]
theorem checked70347 : checkPrefixCuts (2^48) 9224454145 10 Manual.Count131072.C070347.packed 64 cuts70347 = true := by
 decide +kernel
def pointBounds70347 : List (Nat × Nat × Nat) := [(9224538112,115874467531504,115874857072406)]
theorem point_links_checked70347 : (cuts70347.take 1).map (fun c => (9224454145-1+2*2^10*c.k,115874356888287+c.lower,115874746429124+c.upper)) = pointBounds70347 := by
 decide +kernel
def cuts70348 : List PrefixCut := [⟨64,175848375,175848484⟩]
theorem checked70348 : checkPrefixCuts (2^48) 9224585217 10 Manual.Count131072.C070348.packed 64 cuts70348 = true := by
 decide +kernel
def cuts70349 : List PrefixCut := [⟨54,145302612,145302704⟩,
⟨64,171665606,171665711⟩]
theorem checked70349 : checkPrefixCuts (2^48) 9224716289 10 Manual.Count131072.C070349.packed 64 cuts70349 = true := by
 decide +kernel
def pointBounds70349 : List (Nat × Nat × Nat) := [(9224826880,115874851143898,115875240685042)]
theorem point_links_checked70349 : (cuts70349.take 1).map (fun c => (9224716289-1+2*2^10*c.k,115874705841286+c.lower,115875095382338+c.upper)) = pointBounds70349 := by
 decide +kernel
def cuts70350 : List PrefixCut := [⟨64,175995928,175996034⟩]
theorem checked70350 : checkPrefixCuts (2^48) 9224847361 10 Manual.Count131072.C070350.packed 64 cuts70350 = true := by
 decide +kernel
def cuts70351 : List PrefixCut := [⟨64,174681419,174681517⟩]
theorem checked70351 : checkPrefixCuts (2^48) 9224978433 10 Manual.Count131072.C070351.packed 64 cuts70351 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000010
