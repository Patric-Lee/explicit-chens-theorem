import PlattAssemblyKernel
import PlattCertificates.Count131072.C064320
import PlattCertificates.Count131072.C064321
import PlattCertificates.Count131072.C064322
import PlattCertificates.Count131072.C064323
import PlattCertificates.Count131072.C064324
import PlattCertificates.Count131072.C064325
import PlattCertificates.Count131072.C064326
import PlattCertificates.Count131072.C064327
import PlattCertificates.Count131072.C064328
import PlattCertificates.Count131072.C064329
import PlattCertificates.Count131072.C064330
import PlattCertificates.Count131072.C064331
import PlattCertificates.Count131072.C064332
import PlattCertificates.Count131072.C064333
import PlattCertificates.Count131072.C064334
import PlattCertificates.Count131072.C064335
import PlattCertificates.Count131072.C064336
import PlattCertificates.Count131072.C064337
import PlattCertificates.Count131072.C064338
import PlattCertificates.Count131072.C064339
import PlattCertificates.Count131072.C064340
import PlattCertificates.Count131072.C064341
import PlattCertificates.Count131072.C064342
import PlattCertificates.Count131072.C064343
import PlattCertificates.Count131072.C064344
import PlattCertificates.Count131072.C064345
import PlattCertificates.Count131072.C064346
import PlattCertificates.Count131072.C064347
import PlattCertificates.Count131072.C064348
import PlattCertificates.Count131072.C064349
import PlattCertificates.Count131072.C064350
import PlattCertificates.Count131072.C064351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000135
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64320 : List PrefixCut := [⟨64,192888193,192888309⟩]
theorem checked64320 : checkPrefixCuts (2^48) 8434483201 10 Manual.Count131072.C064320.packed 64 cuts64320 = true := by
 decide +kernel
def cuts64321 : List PrefixCut := [⟨30,89067945,89067994⟩,
⟨64,190916304,190916410⟩]
theorem checked64321 : checkPrefixCuts (2^48) 8434614273 10 Manual.Count131072.C064321.packed 64 cuts64321 = true := by
 decide +kernel
def pointBounds64321 : List (Nat × Nat × Nat) := [(8434675712,114774285216985,114774674116380)]
theorem point_links_checked64321 : (cuts64321.take 1).map (fun c => (8434614273-1+2*2^10*c.k,114774196149040+c.lower,114774585048386+c.upper)) = pointBounds64321 := by
 decide +kernel
def cuts64322 : List PrefixCut := [⟨64,189845483,189845598⟩]
theorem checked64322 : checkPrefixCuts (2^48) 8434745345 10 Manual.Count131072.C064322.packed 64 cuts64322 = true := by
 decide +kernel
def cuts64323 : List PrefixCut := [⟨31,93236444,93236499⟩,
⟨64,189775793,189775903⟩]
theorem checked64323 : checkPrefixCuts (2^48) 8434876417 10 Manual.Count131072.C064323.packed 64 cuts64323 = true := by
 decide +kernel
def pointBounds64323 : List (Nat × Nat × Nat) := [(8434939904,114774670147271,114775059046893)]
theorem point_links_checked64323 : (cuts64323.take 1).map (fun c => (8434876417-1+2*2^10*c.k,114774576910827+c.lower,114774965810394+c.upper)) = pointBounds64323 := by
 decide +kernel
def cuts64324 : List PrefixCut := [⟨64,192041972,192042084⟩]
theorem checked64324 : checkPrefixCuts (2^48) 8435007489 10 Manual.Count131072.C064324.packed 64 cuts64324 = true := by
 decide +kernel
def cuts64325 : List PrefixCut := [⟨32,96103290,96103340⟩,
⟨64,192439417,192439519⟩]
theorem checked64325 : checkPrefixCuts (2^48) 8435138561 10 Manual.Count131072.C064325.packed 64 cuts64325 = true := by
 decide +kernel
def pointBounds64325 : List (Nat × Nat × Nat) := [(8435204096,114775054831882,114775443731721)]
theorem point_links_checked64325 : (cuts64325.take 1).map (fun c => (8435138561-1+2*2^10*c.k,114774958728592+c.lower,114775347628381+c.upper)) = pointBounds64325 := by
 decide +kernel
def cuts64326 : List PrefixCut := [⟨64,192669991,192670108⟩]
theorem checked64326 : checkPrefixCuts (2^48) 8435269633 10 Manual.Count131072.C064326.packed 64 cuts64326 = true := by
 decide +kernel
def cuts64327 : List PrefixCut := [⟨33,100638357,100638415⟩,
⟨64,194835929,194836041⟩]
theorem checked64327 : checkPrefixCuts (2^48) 8435400705 10 Manual.Count131072.C064327.packed 64 cuts64327 = true := by
 decide +kernel
def pointBounds64327 : List (Nat × Nat × Nat) := [(8435468288,114775444476357,114775833376423)]
theorem point_links_checked64327 : (cuts64327.take 1).map (fun c => (8435400705-1+2*2^10*c.k,114775343838000+c.lower,114775732738008+c.upper)) = pointBounds64327 := by
 decide +kernel
def cuts64328 : List PrefixCut := [⟨64,190428384,190428495⟩]
theorem checked64328 : checkPrefixCuts (2^48) 8435531777 10 Manual.Count131072.C064328.packed 64 cuts64328 = true := by
 decide +kernel
def cuts64329 : List PrefixCut := [⟨34,103871824,103871888⟩,
⟨64,192093788,192093906⟩]
theorem checked64329 : checkPrefixCuts (2^48) 8435662849 10 Manual.Count131072.C064329.packed 64 cuts64329 = true := by
 decide +kernel
def pointBounds64329 : List (Nat × Nat × Nat) := [(8435732480,114775832974137,114776221874432)]
theorem point_links_checked64329 : (cuts64329.take 1).map (fun c => (8435662849-1+2*2^10*c.k,114775729102313+c.lower,114776118002544+c.upper)) = pointBounds64329 := by
 decide +kernel
def cuts64330 : List PrefixCut := [⟨64,194159515,194159629⟩]
theorem checked64330 : checkPrefixCuts (2^48) 8435793921 10 Manual.Count131072.C064330.packed 64 cuts64330 = true := by
 decide +kernel
def cuts64331 : List PrefixCut := [⟨35,103301359,103301423⟩,
⟨64,191186915,191187030⟩]
theorem checked64331 : checkPrefixCuts (2^48) 8435924993 10 Manual.Count131072.C064331.packed 64 cuts64331 = true := by
 decide +kernel
def pointBounds64331 : List (Nat × Nat × Nat) := [(8435996672,114776218656975,114776607557502)]
theorem point_links_checked64331 : (cuts64331.take 1).map (fun c => (8435924993-1+2*2^10*c.k,114776115355616+c.lower,114776504256079+c.upper)) = pointBounds64331 := by
 decide +kernel
def cuts64332 : List PrefixCut := [⟨64,189115299,189115408⟩]
theorem checked64332 : checkPrefixCuts (2^48) 8436056065 10 Manual.Count131072.C064332.packed 64 cuts64332 = true := by
 decide +kernel
def cuts64333 : List PrefixCut := [⟨36,108102713,108102772⟩,
⟨64,191648102,191648211⟩]
theorem checked64333 : checkPrefixCuts (2^48) 8436187137 10 Manual.Count131072.C064333.packed 64 cuts64333 = true := by
 decide +kernel
def pointBounds64333 : List (Nat × Nat × Nat) := [(8436260864,114776603760543,114776992661289)]
theorem point_links_checked64333 : (cuts64333.take 1).map (fun c => (8436187137-1+2*2^10*c.k,114776495657830+c.lower,114776884558517+c.upper)) = pointBounds64333 := by
 decide +kernel
def cuts64334 : List PrefixCut := [⟨64,190777641,190777748⟩]
theorem checked64334 : checkPrefixCuts (2^48) 8436318209 10 Manual.Count131072.C064334.packed 64 cuts64334 = true := by
 decide +kernel
def cuts64335 : List PrefixCut := [⟨37,112136372,112136436⟩,
⟨64,191975785,191975897⟩]
theorem checked64335 : checkPrefixCuts (2^48) 8436449281 10 Manual.Count131072.C064335.packed 64 cuts64335 = true := by
 decide +kernel
def pointBounds64335 : List (Nat × Nat × Nat) := [(8436525056,114776990219945,114777379120912)]
theorem point_links_checked64335 : (cuts64335.take 1).map (fun c => (8436449281-1+2*2^10*c.k,114776878083573+c.lower,114777266984476+c.upper)) = pointBounds64335 := by
 decide +kernel
def cuts64336 : List PrefixCut := [⟨64,189870908,189871018⟩]
theorem checked64336 : checkPrefixCuts (2^48) 8436580353 10 Manual.Count131072.C064336.packed 64 cuts64336 = true := by
 decide +kernel
def cuts64337 : List PrefixCut := [⟨38,115302366,115302433⟩,
⟨64,194138406,194138518⟩]
theorem checked64337 : checkPrefixCuts (2^48) 8436711425 10 Manual.Count131072.C064337.packed 64 cuts64337 = true := by
 decide +kernel
def pointBounds64337 : List (Nat × Nat × Nat) := [(8436789248,114777375232632,114777764133824)]
theorem point_links_checked64337 : (cuts64337.take 1).map (fun c => (8436711425-1+2*2^10*c.k,114777259930266+c.lower,114777648831391+c.upper)) = pointBounds64337 := by
 decide +kernel
def cuts64338 : List PrefixCut := [⟨64,193201231,193201341⟩]
theorem checked64338 : checkPrefixCuts (2^48) 8436842497 10 Manual.Count131072.C064338.packed 64 cuts64338 = true := by
 decide +kernel
def cuts64339 : List PrefixCut := [⟨39,114464723,114464794⟩,
⟨64,188427508,188427620⟩]
theorem checked64339 : checkPrefixCuts (2^48) 8436973569 10 Manual.Count131072.C064339.packed 64 cuts64339 = true := by
 decide +kernel
def pointBounds64339 : List (Nat × Nat × Nat) := [(8437053440,114777761734626,114778150636044)]
theorem point_links_checked64339 : (cuts64339.take 1).map (fun c => (8436973569-1+2*2^10*c.k,114777647269903+c.lower,114778036171250+c.upper)) = pointBounds64339 := by
 decide +kernel
def cuts64340 : List PrefixCut := [⟨64,189658953,189659061⟩]
theorem checked64340 : checkPrefixCuts (2^48) 8437104641 10 Manual.Count131072.C064340.packed 64 cuts64340 = true := by
 decide +kernel
def cuts64341 : List PrefixCut := [⟨40,121166683,121166754⟩,
⟨64,194226419,194226536⟩]
theorem checked64341 : checkPrefixCuts (2^48) 8437235713 10 Manual.Count131072.C064341.packed 64 cuts64341 = true := by
 decide +kernel
def pointBounds64341 : List (Nat × Nat × Nat) := [(8437317632,114778146523047,114778535424685)]
theorem point_links_checked64341 : (cuts64341.take 1).map (fun c => (8437235713-1+2*2^10*c.k,114778025356364+c.lower,114778414257931+c.upper)) = pointBounds64341 := by
 decide +kernel
def cuts64342 : List PrefixCut := [⟨64,190253524,190253633⟩]
theorem checked64342 : checkPrefixCuts (2^48) 8437366785 10 Manual.Count131072.C064342.packed 64 cuts64342 = true := by
 decide +kernel
def cuts64343 : List PrefixCut := [⟨41,122930967,122931041⟩,
⟨64,191885198,191885315⟩]
theorem checked64343 : checkPrefixCuts (2^48) 8437497857 10 Manual.Count131072.C064343.packed 64 cuts64343 = true := by
 decide +kernel
def pointBounds64343 : List (Nat × Nat × Nat) := [(8437581824,114778532767274,114778921669141)]
theorem point_links_checked64343 : (cuts64343.take 1).map (fun c => (8437497857-1+2*2^10*c.k,114778409836307+c.lower,114778798738100+c.upper)) = pointBounds64343 := by
 decide +kernel
def cuts64344 : List PrefixCut := [⟨64,188679738,188679844⟩]
theorem checked64344 : checkPrefixCuts (2^48) 8437628929 10 Manual.Count131072.C064344.packed 64 cuts64344 = true := by
 decide +kernel
def cuts64345 : List PrefixCut := [⟨42,126563259,126563325⟩,
⟨64,192279564,192279668⟩]
theorem checked64345 : checkPrefixCuts (2^48) 8437760001 10 Manual.Count131072.C064345.packed 64 cuts64345 = true := by
 decide +kernel
def pointBounds64345 : List (Nat × Nat × Nat) := [(8437846016,114778916964502,114779305866584)]
theorem point_links_checked64345 : (cuts64345.take 1).map (fun c => (8437760001-1+2*2^10*c.k,114778790401243+c.lower,114779179303259+c.upper)) = pointBounds64345 := by
 decide +kernel
def cuts64346 : List PrefixCut := [⟨64,190975589,190975697⟩]
theorem checked64346 : checkPrefixCuts (2^48) 8437891073 10 Manual.Count131072.C064346.packed 64 cuts64346 = true := by
 decide +kernel
def cuts64347 : List PrefixCut := [⟨43,128694199,128694271⟩,
⟨64,192540435,192540544⟩]
theorem checked64347 : checkPrefixCuts (2^48) 8438022145 10 Manual.Count131072.C064347.packed 64 cuts64347 = true := by
 decide +kernel
def pointBounds64347 : List (Nat × Nat × Nat) := [(8438110208,114779302350595,114779691252895)]
theorem point_links_checked64347 : (cuts64347.take 1).map (fun c => (8438022145-1+2*2^10*c.k,114779173656396+c.lower,114779562558624+c.upper)) = pointBounds64347 := by
 decide +kernel
def cuts64348 : List PrefixCut := [⟨64,192904368,192904479⟩]
theorem checked64348 : checkPrefixCuts (2^48) 8438153217 10 Manual.Count131072.C064348.packed 64 cuts64348 = true := by
 decide +kernel
def cuts64349 : List PrefixCut := [⟨44,130858370,130858445⟩,
⟨64,189699146,189699255⟩]
theorem checked64349 : checkPrefixCuts (2^48) 8438284289 10 Manual.Count131072.C064349.packed 64 cuts64349 = true := by
 decide +kernel
def pointBounds64349 : List (Nat × Nat × Nat) := [(8438374400,114779689959569,114780078862092)]
theorem point_links_checked64349 : (cuts64349.take 1).map (fun c => (8438284289-1+2*2^10*c.k,114779559101199+c.lower,114779948003647+c.upper)) = pointBounds64349 := by
 decide +kernel
def cuts64350 : List PrefixCut := [⟨64,191497437,191497542⟩]
theorem checked64350 : checkPrefixCuts (2^48) 8438415361 10 Manual.Count131072.C064350.packed 64 cuts64350 = true := by
 decide +kernel
def cuts64351 : List PrefixCut := [⟨45,134389990,134390068⟩,
⟨64,190693921,190694031⟩]
theorem checked64351 : checkPrefixCuts (2^48) 8438546433 10 Manual.Count131072.C064351.packed 64 cuts64351 = true := by
 decide +kernel
def pointBounds64351 : List (Nat × Nat × Nat) := [(8438638592,114780074687772,114780463590512)]
theorem point_links_checked64351 : (cuts64351.take 1).map (fun c => (8438546433-1+2*2^10*c.k,114779940297782+c.lower,114780329200444+c.upper)) = pointBounds64351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000135
