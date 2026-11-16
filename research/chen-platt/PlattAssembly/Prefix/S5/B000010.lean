import PlattAssemblyKernel
import PlattCertificates.Count131072.C040320
import PlattCertificates.Count131072.C040321
import PlattCertificates.Count131072.C040322
import PlattCertificates.Count131072.C040323
import PlattCertificates.Count131072.C040324
import PlattCertificates.Count131072.C040325
import PlattCertificates.Count131072.C040326
import PlattCertificates.Count131072.C040327
import PlattCertificates.Count131072.C040328
import PlattCertificates.Count131072.C040329
import PlattCertificates.Count131072.C040330
import PlattCertificates.Count131072.C040331
import PlattCertificates.Count131072.C040332
import PlattCertificates.Count131072.C040333
import PlattCertificates.Count131072.C040334
import PlattCertificates.Count131072.C040335
import PlattCertificates.Count131072.C040336
import PlattCertificates.Count131072.C040337
import PlattCertificates.Count131072.C040338
import PlattCertificates.Count131072.C040339
import PlattCertificates.Count131072.C040340
import PlattCertificates.Count131072.C040341
import PlattCertificates.Count131072.C040342
import PlattCertificates.Count131072.C040343
import PlattCertificates.Count131072.C040344
import PlattCertificates.Count131072.C040345
import PlattCertificates.Count131072.C040346
import PlattCertificates.Count131072.C040347
import PlattCertificates.Count131072.C040348
import PlattCertificates.Count131072.C040349
import PlattCertificates.Count131072.C040350
import PlattCertificates.Count131072.C040351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40320 : List PrefixCut := [⟨40,195320980,195321099⟩,
⟨64,309744656,309744844⟩]
theorem checked40320 : checkPrefixCuts (2^48) 5288755201 10 Manual.Count131072.C040320.packed 64 cuts40320 = true := by
 decide +kernel
def pointBounds40320 : List (Nat × Nat × Nat) := [(5288837120,108966566890698,108966952455871)]
theorem point_links_checked40320 : (cuts40320.take 1).map (fun c => (5288755201-1+2*2^10*c.k,108966371569718+c.lower,108966757134772+c.upper)) = pointBounds40320 := by
 decide +kernel
def cuts40321 : List PrefixCut := [⟨57,277060595,277060762⟩,
⟨64,309843390,309843578⟩]
theorem checked40321 : checkPrefixCuts (2^48) 5288886273 10 Manual.Count131072.C040321.packed 64 cuts40321 = true := by
 decide +kernel
def pointBounds40321 : List (Nat × Nat × Nat) := [(5289003008,108966958374969,108967343940378)]
theorem point_links_checked40321 : (cuts40321.take 1).map (fun c => (5288886273-1+2*2^10*c.k,108966681314374+c.lower,108967066879616+c.upper)) = pointBounds40321 := by
 decide +kernel
def cuts40322 : List PrefixCut := [⟨64,311857979,311858165⟩]
theorem checked40322 : checkPrefixCuts (2^48) 5289017345 10 Manual.Count131072.C040322.packed 64 cuts40322 = true := by
 decide +kernel
def cuts40323 : List PrefixCut := [⟨10,47735946,47735973⟩,
⟨64,312169573,312169759⟩]
theorem checked40323 : checkPrefixCuts (2^48) 5289148417 10 Manual.Count131072.C040323.packed 64 cuts40323 = true := by
 decide +kernel
def pointBounds40323 : List (Nat × Nat × Nat) := [(5289168896,108967350751689,108967736317332)]
theorem point_links_checked40323 : (cuts40323.take 1).map (fun c => (5289148417-1+2*2^10*c.k,108967303015743+c.lower,108967688581359+c.upper)) = pointBounds40323 := by
 decide +kernel
def cuts40324 : List PrefixCut := [⟨27,131177034,131177112⟩,
⟨64,313226139,313226325⟩]
theorem checked40324 : checkPrefixCuts (2^48) 5289279489 10 Manual.Count131072.C040324.packed 64 cuts40324 = true := by
 decide +kernel
def pointBounds40324 : List (Nat × Nat × Nat) := [(5289334784,108967746362350,108968131928230)]
theorem point_links_checked40324 : (cuts40324.take 1).map (fun c => (5289279489-1+2*2^10*c.k,108967615185316+c.lower,108968000751118+c.upper)) = pointBounds40324 := by
 decide +kernel
def cuts40325 : List PrefixCut := [⟨44,215518071,215518199⟩,
⟨64,313271605,313271790⟩]
theorem checked40325 : checkPrefixCuts (2^48) 5289410561 10 Manual.Count131072.C040325.packed 64 cuts40325 = true := by
 decide +kernel
def pointBounds40325 : List (Nat × Nat × Nat) := [(5289500672,108968143929526,108968529495642)]
theorem point_links_checked40325 : (cuts40325.take 1).map (fun c => (5289410561-1+2*2^10*c.k,108967928411455+c.lower,108968313977443+c.upper)) = pointBounds40325 := by
 decide +kernel
def cuts40326 : List PrefixCut := [⟨61,294745959,294746138⟩,
⟨64,310177493,310177681⟩]
theorem checked40326 : checkPrefixCuts (2^48) 5289541633 10 Manual.Count131072.C040326.packed 64 cuts40326 = true := by
 decide +kernel
def pointBounds40326 : List (Nat × Nat × Nat) := [(5289666560,108968536429019,108968921995371)]
theorem point_links_checked40326 : (cuts40326.take 1).map (fun c => (5289541633-1+2*2^10*c.k,108968241683060+c.lower,108968627249233+c.upper)) = pointBounds40326 := by
 decide +kernel
def cuts40327 : List PrefixCut := [⟨64,314054257,314054444⟩]
theorem checked40327 : checkPrefixCuts (2^48) 5289672705 10 Manual.Count131072.C040327.packed 64 cuts40327 = true := by
 decide +kernel
def cuts40328 : List PrefixCut := [⟨14,67684004,67684042⟩,
⟨64,311119935,311120121⟩]
theorem checked40328 : checkPrefixCuts (2^48) 5289803777 10 Manual.Count131072.C040328.packed 64 cuts40328 = true := by
 decide +kernel
def pointBounds40328 : List (Nat × Nat × Nat) := [(5289832448,108968933598814,108969319165400)]
theorem point_links_checked40328 : (cuts40328.take 1).map (fun c => (5289803777-1+2*2^10*c.k,108968865914810+c.lower,108969251481358+c.upper)) = pointBounds40328 := by
 decide +kernel
def cuts40329 : List PrefixCut := [⟨31,151486588,151486680⟩,
⟨64,312548835,312549022⟩]
theorem checked40329 : checkPrefixCuts (2^48) 5289934849 10 Manual.Count131072.C040329.packed 64 cuts40329 = true := by
 decide +kernel
def pointBounds40329 : List (Nat × Nat × Nat) := [(5289998336,108969328521333,108969714088159)]
theorem point_links_checked40329 : (cuts40329.take 1).map (fun c => (5289934849-1+2*2^10*c.k,108969177034745+c.lower,108969562601479+c.upper)) = pointBounds40329 := by
 decide +kernel
def cuts40330 : List PrefixCut := [⟨48,234167121,234167260⟩,
⟨64,312860343,312860528⟩]
theorem checked40330 : checkPrefixCuts (2^48) 5290065921 10 Manual.Count131072.C040330.packed 64 cuts40330 = true := by
 decide +kernel
def pointBounds40330 : List (Nat × Nat × Nat) := [(5290164224,108969723750701,108970109317761)]
theorem point_links_checked40330 : (cuts40330.take 1).map (fun c => (5290065921-1+2*2^10*c.k,108969489583580+c.lower,108969875150501+c.upper)) = pointBounds40330 := by
 decide +kernel
def cuts40331 : List PrefixCut := [⟨64,312586523,312586712⟩]
theorem checked40331 : checkPrefixCuts (2^48) 5290196993 10 Manual.Count131072.C040331.packed 64 cuts40331 = true := by
 decide +kernel
def cuts40332 : List PrefixCut := [⟨1,4469267,4469269⟩,
⟨64,308748089,308748272⟩]
theorem checked40332 : checkPrefixCuts (2^48) 5290328065 10 Manual.Count131072.C040332.packed 64 cuts40332 = true := by
 decide +kernel
def pointBounds40332 : List (Nat × Nat × Nat) := [(5290330112,108970119499713,108970505067010)]
theorem point_links_checked40332 : (cuts40332.take 1).map (fun c => (5290328065-1+2*2^10*c.k,108970115030446+c.lower,108970500597741+c.upper)) = pointBounds40332 := by
 decide +kernel
def cuts40333 : List PrefixCut := [⟨18,89223210,89223262⟩,
⟨64,314912037,314912219⟩]
theorem checked40333 : checkPrefixCuts (2^48) 5290459137 10 Manual.Count131072.C040333.packed 64 cuts40333 = true := by
 decide +kernel
def pointBounds40333 : List (Nat × Nat × Nat) := [(5290496000,108970513001745,108970898569275)]
theorem point_links_checked40333 : (cuts40333.take 1).map (fun c => (5290459137-1+2*2^10*c.k,108970423778535+c.lower,108970809346013+c.upper)) = pointBounds40333 := by
 decide +kernel
def cuts40334 : List PrefixCut := [⟨35,168226518,168226620⟩,
⟨64,306285464,306285650⟩]
theorem checked40334 : checkPrefixCuts (2^48) 5290590209 10 Manual.Count131072.C040334.packed 64 cuts40334 = true := by
 decide +kernel
def pointBounds40334 : List (Nat × Nat × Nat) := [(5290661888,108970906917090,108971292484852)]
theorem point_links_checked40334 : (cuts40334.take 1).map (fun c => (5290590209-1+2*2^10*c.k,108970738690572+c.lower,108971124258232+c.upper)) = pointBounds40334 := by
 decide +kernel
def cuts40335 : List PrefixCut := [⟨52,252173114,252173265⟩,
⟨64,309310360,309310543⟩]
theorem checked40335 : checkPrefixCuts (2^48) 5290721281 10 Manual.Count131072.C040335.packed 64 cuts40335 = true := by
 decide +kernel
def pointBounds40335 : List (Nat × Nat × Nat) := [(5290827776,108971297149150,108971682717147)]
theorem point_links_checked40335 : (cuts40335.take 1).map (fun c => (5290721281-1+2*2^10*c.k,108971044976036+c.lower,108971430543882+c.upper)) = pointBounds40335 := by
 decide +kernel
def cuts40336 : List PrefixCut := [⟨64,307866283,307866468⟩]
theorem checked40336 : checkPrefixCuts (2^48) 5290852353 10 Manual.Count131072.C040336.packed 64 cuts40336 = true := by
 decide +kernel
def cuts40337 : List PrefixCut := [⟨5,24205509,24205523⟩,
⟨64,312061316,312061500⟩]
theorem checked40337 : checkPrefixCuts (2^48) 5290983425 10 Manual.Count131072.C040337.packed 64 cuts40337 = true := by
 decide +kernel
def pointBounds40337 : List (Nat × Nat × Nat) := [(5290993664,108971686358188,108972071926416)]
theorem point_links_checked40337 : (cuts40337.take 1).map (fun c => (5290983425-1+2*2^10*c.k,108971662152679+c.lower,108972047720893+c.upper)) = pointBounds40337 := by
 decide +kernel
def cuts40338 : List PrefixCut := [⟨22,109373909,109373974⟩,
⟨64,314766646,314766831⟩]
theorem checked40338 : checkPrefixCuts (2^48) 5291114497 10 Manual.Count131072.C040338.packed 64 cuts40338 = true := by
 decide +kernel
def pointBounds40338 : List (Nat × Nat × Nat) := [(5291159552,108972083587904,108972469156367)]
theorem point_links_checked40338 : (cuts40338.take 1).map (fun c => (5291114497-1+2*2^10*c.k,108971974213995+c.lower,108972359782393+c.upper)) = pointBounds40338 := by
 decide +kernel
def cuts40339 : List PrefixCut := [⟨39,190069078,190069190⟩,
⟨64,310503188,310503372⟩]
theorem checked40339 : checkPrefixCuts (2^48) 5291245569 10 Manual.Count131072.C040339.packed 64 cuts40339 = true := by
 decide +kernel
def pointBounds40339 : List (Nat × Nat × Nat) := [(5291325440,108972479049719,108972864618414)]
theorem point_links_checked40339 : (cuts40339.take 1).map (fun c => (5291245569-1+2*2^10*c.k,108972288980641+c.lower,108972674549224+c.upper)) = pointBounds40339 := by
 decide +kernel
def cuts40340 : List PrefixCut := [⟨56,267355281,267355441⟩,
⟨64,306027163,306027346⟩]
theorem checked40340 : checkPrefixCuts (2^48) 5291376641 10 Manual.Count131072.C040340.packed 64 cuts40340 = true := by
 decide +kernel
def pointBounds40340 : List (Nat × Nat × Nat) := [(5291491328,108972866839110,108973252408037)]
theorem point_links_checked40340 : (cuts40340.take 1).map (fun c => (5291376641-1+2*2^10*c.k,108972599483829+c.lower,108972985052596+c.upper)) = pointBounds40340 := by
 decide +kernel
def cuts40341 : List PrefixCut := [⟨64,315807083,315807272⟩]
theorem checked40341 : checkPrefixCuts (2^48) 5291507713 10 Manual.Count131072.C040341.packed 64 cuts40341 = true := by
 decide +kernel
def cuts40342 : List PrefixCut := [⟨9,41649564,41649591⟩,
⟨64,309256672,309256857⟩]
theorem checked40342 : checkPrefixCuts (2^48) 5291638785 10 Manual.Count131072.C040342.packed 64 cuts40342 = true := by
 decide +kernel
def pointBounds40342 : List (Nat × Nat × Nat) := [(5291657216,108973262967639,108973648536805)]
theorem point_links_checked40342 : (cuts40342.take 1).map (fun c => (5291638785-1+2*2^10*c.k,108973221318075+c.lower,108973606887214+c.upper)) = pointBounds40342 := by
 decide +kernel
def cuts40343 : List PrefixCut := [⟨26,124679233,124679304⟩,
⟨64,310153239,310153421⟩]
theorem checked40343 : checkPrefixCuts (2^48) 5291769857 10 Manual.Count131072.C040343.packed 64 cuts40343 = true := by
 decide +kernel
def pointBounds40343 : List (Nat × Nat × Nat) := [(5291823104,108973655253980,108974040823375)]
theorem point_links_checked40343 : (cuts40343.take 1).map (fun c => (5291769857-1+2*2^10*c.k,108973530574747+c.lower,108973916144071+c.upper)) = pointBounds40343 := by
 decide +kernel
def cuts40344 : List PrefixCut := [⟨43,209619061,209619185⟩,
⟨64,308709510,308709695⟩]
theorem checked40344 : checkPrefixCuts (2^48) 5291900929 10 Manual.Count131072.C040344.packed 64 cuts40344 = true := by
 decide +kernel
def pointBounds40344 : List (Nat × Nat × Nat) := [(5291988992,108974050347047,108974435916677)]
theorem point_links_checked40344 : (cuts40344.take 1).map (fun c => (5291900929-1+2*2^10*c.k,108973840727986+c.lower,108974226297492+c.upper)) = pointBounds40344 := by
 decide +kernel
def cuts40345 : List PrefixCut := [⟨60,293756335,293756508⟩,
⟨64,313435584,313435769⟩]
theorem checked40345 : checkPrefixCuts (2^48) 5292032001 10 Manual.Count131072.C040345.packed 64 cuts40345 = true := by
 decide +kernel
def pointBounds40345 : List (Nat × Nat × Nat) := [(5292154880,108974443193831,108974828763695)]
theorem point_links_checked40345 : (cuts40345.take 1).map (fun c => (5292032001-1+2*2^10*c.k,108974149437496+c.lower,108974535007187+c.upper)) = pointBounds40345 := by
 decide +kernel
def cuts40346 : List PrefixCut := [⟨64,312204517,312204701⟩]
theorem checked40346 : checkPrefixCuts (2^48) 5292163073 10 Manual.Count131072.C040346.packed 64 cuts40346 = true := by
 decide +kernel
def cuts40347 : List PrefixCut := [⟨13,62120857,62120896⟩,
⟨64,310069359,310069546⟩]
theorem checked40347 : checkPrefixCuts (2^48) 5292294145 10 Manual.Count131072.C040347.packed 64 cuts40347 = true := by
 decide +kernel
def pointBounds40347 : List (Nat × Nat × Nat) := [(5292320768,108974837198454,108975222768553)]
theorem point_links_checked40347 : (cuts40347.take 1).map (fun c => (5292294145-1+2*2^10*c.k,108974775077597+c.lower,108975160647657+c.upper)) = pointBounds40347 := by
 decide +kernel
def cuts40348 : List PrefixCut := [⟨30,145352350,145352434⟩,
⟨64,310433989,310434170⟩]
theorem checked40348 : checkPrefixCuts (2^48) 5292425217 10 Manual.Count131072.C040348.packed 64 cuts40348 = true := by
 decide +kernel
def pointBounds40348 : List (Nat × Nat × Nat) := [(5292486656,108975230499306,108975616069637)]
theorem point_links_checked40348 : (cuts40348.take 1).map (fun c => (5292425217-1+2*2^10*c.k,108975085146956+c.lower,108975470717203+c.upper)) = pointBounds40348 := by
 decide +kernel
def cuts40349 : List PrefixCut := [⟨47,228685523,228685658⟩,
⟨64,310798564,310798747⟩]
theorem checked40349 : checkPrefixCuts (2^48) 5292556289 10 Manual.Count131072.C040349.packed 64 cuts40349 = true := by
 decide +kernel
def pointBounds40349 : List (Nat × Nat × Nat) := [(5292652544,108975624266468,108976009837031)]
theorem point_links_checked40349 : (cuts40349.take 1).map (fun c => (5292556289-1+2*2^10*c.k,108975395580945+c.lower,108975781151373+c.upper)) = pointBounds40349 := by
 decide +kernel
def cuts40350 : List PrefixCut := [⟨64,311109950,311110130⟩]
theorem checked40350 : checkPrefixCuts (2^48) 5292687361 10 Manual.Count131072.C040350.packed 64 cuts40350 = true := by
 decide +kernel
def pointBounds40350 : List (Nat × Nat × Nat) := [(5292818432,108976017489459,108976403060250)]
theorem point_links_checked40350 : (cuts40350.take 1).map (fun c => (5292687361-1+2*2^10*c.k,108975706379509+c.lower,108976091950120+c.upper)) = pointBounds40350 := by
 decide +kernel
def cuts40351 : List PrefixCut := [⟨64,311368149,311368332⟩]
theorem checked40351 : checkPrefixCuts (2^48) 5292818433 10 Manual.Count131072.C040351.packed 64 cuts40351 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000010
