import PlattAssemblyKernel
import PlattCertificates.Count131072.C057360
import PlattCertificates.Count131072.C057361
import PlattCertificates.Count131072.C057362
import PlattCertificates.Count131072.C057363
import PlattCertificates.Count131072.C057364
import PlattCertificates.Count131072.C057365
import PlattCertificates.Count131072.C057366
import PlattCertificates.Count131072.C057367
import PlattCertificates.Count131072.C057368
import PlattCertificates.Count131072.C057369
import PlattCertificates.Count131072.C057370
import PlattCertificates.Count131072.C057371
import PlattCertificates.Count131072.C057372
import PlattCertificates.Count131072.C057373
import PlattCertificates.Count131072.C057374
import PlattCertificates.Count131072.C057375
import PlattCertificates.Count131072.C057376
import PlattCertificates.Count131072.C057377
import PlattCertificates.Count131072.C057378
import PlattCertificates.Count131072.C057379
import PlattCertificates.Count131072.C057380
import PlattCertificates.Count131072.C057381
import PlattCertificates.Count131072.C057382
import PlattCertificates.Count131072.C057383
import PlattCertificates.Count131072.C057384
import PlattCertificates.Count131072.C057385
import PlattCertificates.Count131072.C057386
import PlattCertificates.Count131072.C057387
import PlattCertificates.Count131072.C057388
import PlattCertificates.Count131072.C057389
import PlattCertificates.Count131072.C057390
import PlattCertificates.Count131072.C057391
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000230
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57360 : List PrefixCut := [⟨64,214896113,214896236⟩]
theorem checked57360 : checkPrefixCuts (2^48) 7522222081 10 Manual.Count131072.C057360.packed 64 cuts57360 = true := by
 decide +kernel
def cuts57361 : List PrefixCut := [⟨17,55828217,55828249⟩,
⟨64,212235676,212235796⟩]
theorem checked57361 : checkPrefixCuts (2^48) 7522353153 10 Manual.Count131072.C057361.packed 64 cuts57361 = true := by
 decide +kernel
def pointBounds57361 : List (Nat × Nat × Nat) := [(7522387968,113361017962399,113361406052676)]
theorem point_links_checked57361 : (cuts57361.take 1).map (fun c => (7522353153-1+2*2^10*c.k,113360962134182+c.lower,113361350224427+c.upper)) = pointBounds57361 := by
 decide +kernel
def cuts57362 : List PrefixCut := [⟨64,216273046,216273168⟩]
theorem checked57362 : checkPrefixCuts (2^48) 7522484225 10 Manual.Count131072.C057362.packed 64 cuts57362 = true := by
 decide +kernel
def cuts57363 : List PrefixCut := [⟨4,14181096,14181103⟩,
⟨64,216418965,216419082⟩]
theorem checked57363 : checkPrefixCuts (2^48) 7522615297 10 Manual.Count131072.C057363.packed 64 cuts57363 = true := by
 decide +kernel
def pointBounds57363 : List (Nat × Nat × Nat) := [(7522623488,113361404824000,113361792914494)]
theorem point_links_checked57363 : (cuts57363.take 1).map (fun c => (7522615297-1+2*2^10*c.k,113361390642904+c.lower,113361778733391+c.upper)) = pointBounds57363 := by
 decide +kernel
def cuts57364 : List PrefixCut := [⟨55,184424591,184424696⟩,
⟨64,214357313,214357435⟩]
theorem checked57364 : checkPrefixCuts (2^48) 7522746369 10 Manual.Count131072.C057364.packed 64 cuts57364 = true := by
 decide +kernel
def pointBounds57364 : List (Nat × Nat × Nat) := [(7522859008,113361791486460,113362179577169)]
theorem point_links_checked57364 : (cuts57364.take 1).map (fun c => (7522746369-1+2*2^10*c.k,113361607061869+c.lower,113361995152473+c.upper)) = pointBounds57364 := by
 decide +kernel
def cuts57365 : List PrefixCut := [⟨64,213792339,213792461⟩]
theorem checked57365 : checkPrefixCuts (2^48) 7522877441 10 Manual.Count131072.C057365.packed 64 cuts57365 = true := by
 decide +kernel
def cuts57366 : List PrefixCut := [⟨42,141316412,141316494⟩,
⟨64,214649152,214649274⟩]
theorem checked57366 : checkPrefixCuts (2^48) 7523008513 10 Manual.Count131072.C057366.packed 64 cuts57366 = true := by
 decide +kernel
def pointBounds57366 : List (Nat × Nat × Nat) := [(7523094528,113362176527933,113362564618863)]
theorem point_links_checked57366 : (cuts57366.take 1).map (fun c => (7523008513-1+2*2^10*c.k,113362035211521+c.lower,113362423302369+c.upper)) = pointBounds57366 := by
 decide +kernel
def cuts57367 : List PrefixCut := [⟨64,213485561,213485681⟩]
theorem checked57367 : checkPrefixCuts (2^48) 7523139585 10 Manual.Count131072.C057367.packed 64 cuts57367 = true := by
 decide +kernel
def cuts57368 : List PrefixCut := [⟨29,96078517,96078574⟩,
⟨64,215015800,215015924⟩]
theorem checked57368 : checkPrefixCuts (2^48) 7523270657 10 Manual.Count131072.C057368.packed 64 cuts57368 = true := by
 decide +kernel
def pointBounds57368 : List (Nat × Nat × Nat) := [(7523330048,113362559424751,113362947515898)]
theorem point_links_checked57368 : (cuts57368.take 1).map (fun c => (7523270657-1+2*2^10*c.k,113362463346234+c.lower,113362851437324+c.upper)) = pointBounds57368 := by
 decide +kernel
def cuts57369 : List PrefixCut := [⟨64,216284098,216284220⟩]
theorem checked57369 : checkPrefixCuts (2^48) 7523401729 10 Manual.Count131072.C057369.packed 64 cuts57369 = true := by
 decide +kernel
def cuts57370 : List PrefixCut := [⟨16,54098498,54098529⟩,
⟨64,214372321,214372443⟩]
theorem checked57370 : checkPrefixCuts (2^48) 7523532801 10 Manual.Count131072.C057370.packed 64 cuts57370 = true := by
 decide +kernel
def pointBounds57370 : List (Nat × Nat × Nat) := [(7523565568,113362948744630,113363336835997)]
theorem point_links_checked57370 : (cuts57370.take 1).map (fun c => (7523532801-1+2*2^10*c.k,113362894646132+c.lower,113363282737468+c.upper)) = pointBounds57370 := by
 decide +kernel
def cuts57371 : List PrefixCut := [⟨64,214593053,214593175⟩]
theorem checked57371 : checkPrefixCuts (2^48) 7523663873 10 Manual.Count131072.C057371.packed 64 cuts57371 = true := by
 decide +kernel
def cuts57372 : List PrefixCut := [⟨3,9427642,9427648⟩,
⟨64,215000833,215000956⟩]
theorem checked57372 : checkPrefixCuts (2^48) 7523794945 10 Manual.Count131072.C057372.packed 64 cuts57372 = true := by
 decide +kernel
def pointBounds57372 : List (Nat × Nat × Nat) := [(7523801088,113363333039148,113363721130734)]
theorem point_links_checked57372 : (cuts57372.take 1).map (fun c => (7523794945-1+2*2^10*c.k,113363323611506+c.lower,113363711703086+c.upper)) = pointBounds57372 := by
 decide +kernel
def cuts57373 : List PrefixCut := [⟨54,181552505,181552608⟩,
⟨64,215857512,215857634⟩]
theorem checked57373 : checkPrefixCuts (2^48) 7523926017 10 Manual.Count131072.C057373.packed 64 cuts57373 = true := by
 decide +kernel
def pointBounds57373 : List (Nat × Nat × Nat) := [(7524036608,113363720164844,113364108256650)]
theorem point_links_checked57373 : (cuts57373.take 1).map (fun c => (7523926017-1+2*2^10*c.k,113363538612339+c.lower,113363926704042+c.upper)) = pointBounds57373 := by
 decide +kernel
def cuts57374 : List PrefixCut := [⟨64,215217785,215217909⟩]
theorem checked57374 : checkPrefixCuts (2^48) 7524057089 10 Manual.Count131072.C057374.packed 64 cuts57374 = true := by
 decide +kernel
def cuts57375 : List PrefixCut := [⟨41,134859903,134859982⟩,
⟨64,210986825,210986947⟩]
theorem checked57375 : checkPrefixCuts (2^48) 7524188161 10 Manual.Count131072.C057375.packed 64 cuts57375 = true := by
 decide +kernel
def pointBounds57375 : List (Nat × Nat × Nat) := [(7524272128,113364104547539,113364492639567)]
theorem point_links_checked57375 : (cuts57375.take 1).map (fun c => (7524188161-1+2*2^10*c.k,113363969687636+c.lower,113364357779585+c.upper)) = pointBounds57375 := by
 decide +kernel
def cuts57376 : List PrefixCut := [⟨64,219100754,219100878⟩]
theorem checked57376 : checkPrefixCuts (2^48) 7524319233 10 Manual.Count131072.C057376.packed 64 cuts57376 = true := by
 decide +kernel
def cuts57377 : List PrefixCut := [⟨28,93220465,93220519⟩,
⟨64,214533201,214533323⟩]
theorem checked57377 : checkPrefixCuts (2^48) 7524450305 10 Manual.Count131072.C057377.packed 64 cuts57377 = true := by
 decide +kernel
def pointBounds57377 : List (Nat × Nat × Nat) := [(7524507648,113364492995680,113364881087929)]
theorem point_links_checked57377 : (cuts57377.take 1).map (fun c => (7524450305-1+2*2^10*c.k,113364399775215+c.lower,113364787867410+c.upper)) = pointBounds57377 := by
 decide +kernel
def cuts57378 : List PrefixCut := [⟨64,217709086,217709206⟩]
theorem checked57378 : checkPrefixCuts (2^48) 7524581377 10 Manual.Count131072.C057378.packed 64 cuts57378 = true := by
 decide +kernel
def cuts57379 : List PrefixCut := [⟨15,48965314,48965342⟩,
⟨64,211121738,211121863⟩]
theorem checked57379 : checkPrefixCuts (2^48) 7524712449 10 Manual.Count131072.C057379.packed 64 cuts57379 = true := by
 decide +kernel
def pointBounds57379 : List (Nat × Nat × Nat) := [(7524743168,113364880982816,113365269075281)]
theorem point_links_checked57379 : (cuts57379.take 1).map (fun c => (7524712449-1+2*2^10*c.k,113364832017502+c.lower,113365220109939+c.upper)) = pointBounds57379 := by
 decide +kernel
def cuts57380 : List PrefixCut := [⟨64,217290028,217290150⟩]
theorem checked57380 : checkPrefixCuts (2^48) 7524843521 10 Manual.Count131072.C057380.packed 64 cuts57380 = true := by
 decide +kernel
def cuts57381 : List PrefixCut := [⟨2,7481084,7481088⟩,
⟨64,220241250,220241370⟩]
theorem checked57381 : checkPrefixCuts (2^48) 7524974593 10 Manual.Count131072.C057381.packed 64 cuts57381 = true := by
 decide +kernel
def pointBounds57381 : List (Nat × Nat × Nat) := [(7524978688,113365267910352,113365656003040)]
theorem point_links_checked57381 : (cuts57381.take 1).map (fun c => (7524974593-1+2*2^10*c.k,113365260429268+c.lower,113365648521952+c.upper)) = pointBounds57381 := by
 decide +kernel
def cuts57382 : List PrefixCut := [⟨53,178531708,178531811⟩,
⟨64,215487040,215487163⟩]
theorem checked57382 : checkPrefixCuts (2^48) 7525105665 10 Manual.Count131072.C057382.packed 64 cuts57382 = true := by
 decide +kernel
def pointBounds57382 : List (Nat × Nat × Nat) := [(7525214208,113365659202226,113366047295133)]
theorem point_links_checked57382 : (cuts57382.take 1).map (fun c => (7525105665-1+2*2^10*c.k,113365480670518+c.lower,113365868763322+c.upper)) = pointBounds57382 := by
 decide +kernel
def cuts57383 : List PrefixCut := [⟨64,215071858,215071982⟩]
theorem checked57383 : checkPrefixCuts (2^48) 7525236737 10 Manual.Count131072.C057383.packed 64 cuts57383 = true := by
 decide +kernel
def cuts57384 : List PrefixCut := [⟨40,133529679,133529756⟩,
⟨64,214469651,214469774⟩]
theorem checked57384 : checkPrefixCuts (2^48) 7525367809 10 Manual.Count131072.C057384.packed 64 cuts57384 = true := by
 decide +kernel
def pointBounds57384 : List (Nat × Nat × Nat) := [(7525449728,113366044759095,113366432852223)]
theorem point_links_checked57384 : (cuts57384.take 1).map (fun c => (7525367809-1+2*2^10*c.k,113365911229416+c.lower,113366299322467+c.upper)) = pointBounds57384 := by
 decide +kernel
def cuts57385 : List PrefixCut := [⟨64,216934476,216934601⟩]
theorem checked57385 : checkPrefixCuts (2^48) 7525498881 10 Manual.Count131072.C057385.packed 64 cuts57385 = true := by
 decide +kernel
def cuts57386 : List PrefixCut := [⟨27,91971598,91971651⟩,
⟨64,216631487,216631609⟩]
theorem checked57386 : checkPrefixCuts (2^48) 7525629953 10 Manual.Count131072.C057386.packed 64 cuts57386 = true := by
 decide +kernel
def pointBounds57386 : List (Nat × Nat × Nat) := [(7525685248,113366434605141,113366822698493)]
theorem point_links_checked57386 : (cuts57386.take 1).map (fun c => (7525629953-1+2*2^10*c.k,113366342633543+c.lower,113366730726842+c.upper)) = pointBounds57386 := by
 decide +kernel
def cuts57387 : List PrefixCut := [⟨64,213299006,213299128⟩]
theorem checked57387 : checkPrefixCuts (2^48) 7525761025 10 Manual.Count131072.C057387.packed 64 cuts57387 = true := by
 decide +kernel
def cuts57388 : List PrefixCut := [⟨14,48658436,48658464⟩,
⟨64,217708560,217708683⟩]
theorem checked57388 : checkPrefixCuts (2^48) 7525892097 10 Manual.Count131072.C057388.packed 64 cuts57388 = true := by
 decide +kernel
def pointBounds57388 : List (Nat × Nat × Nat) := [(7525920768,113366821222472,113367209316043)]
theorem point_links_checked57388 : (cuts57388.take 1).map (fun c => (7525892097-1+2*2^10*c.k,113366772564036+c.lower,113367160657579+c.upper)) = pointBounds57388 := by
 decide +kernel
def cuts57389 : List PrefixCut := [⟨64,216433180,216433300⟩]
theorem checked57389 : checkPrefixCuts (2^48) 7526023169 10 Manual.Count131072.C057389.packed 64 cuts57389 = true := by
 decide +kernel
def cuts57390 : List PrefixCut := [⟨1,3104163,3104165⟩,
⟨64,216990405,216990528⟩]
theorem checked57390 : checkPrefixCuts (2^48) 7526154241 10 Manual.Count131072.C057390.packed 64 cuts57390 = true := by
 decide +kernel
def pointBounds57390 : List (Nat × Nat × Nat) := [(7526156288,113367209809939,113367597903727)]
theorem point_links_checked57390 : (cuts57390.take 1).map (fun c => (7526154241-1+2*2^10*c.k,113367206705776+c.lower,113367594799562+c.upper)) = pointBounds57390 := by
 decide +kernel
def cuts57391 : List PrefixCut := [⟨52,177793173,177793274⟩,
⟨64,218482549,218482673⟩]
theorem checked57391 : checkPrefixCuts (2^48) 7526285313 10 Manual.Count131072.C057391.packed 64 cuts57391 = true := by
 decide +kernel
def pointBounds57391 : List (Nat × Nat × Nat) := [(7526391808,113367601489354,113367989583364)]
theorem point_links_checked57391 : (cuts57391.take 1).map (fun c => (7526285313-1+2*2^10*c.k,113367423696181+c.lower,113367811790090+c.upper)) = pointBounds57391 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000230
