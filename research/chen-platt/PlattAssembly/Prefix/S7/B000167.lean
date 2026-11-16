import PlattAssemblyKernel
import PlattCertificates.Count131072.C065344
import PlattCertificates.Count131072.C065345
import PlattCertificates.Count131072.C065346
import PlattCertificates.Count131072.C065347
import PlattCertificates.Count131072.C065348
import PlattCertificates.Count131072.C065349
import PlattCertificates.Count131072.C065350
import PlattCertificates.Count131072.C065351
import PlattCertificates.Count131072.C065352
import PlattCertificates.Count131072.C065353
import PlattCertificates.Count131072.C065354
import PlattCertificates.Count131072.C065355
import PlattCertificates.Count131072.C065356
import PlattCertificates.Count131072.C065357
import PlattCertificates.Count131072.C065358
import PlattCertificates.Count131072.C065359
import PlattCertificates.Count131072.C065360
import PlattCertificates.Count131072.C065361
import PlattCertificates.Count131072.C065362
import PlattCertificates.Count131072.C065363
import PlattCertificates.Count131072.C065364
import PlattCertificates.Count131072.C065365
import PlattCertificates.Count131072.C065366
import PlattCertificates.Count131072.C065367
import PlattCertificates.Count131072.C065368
import PlattCertificates.Count131072.C065369
import PlattCertificates.Count131072.C065370
import PlattCertificates.Count131072.C065371
import PlattCertificates.Count131072.C065372
import PlattCertificates.Count131072.C065373
import PlattCertificates.Count131072.C065374
import PlattCertificates.Count131072.C065375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000167
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65344 : List PrefixCut := [⟨57,167201246,167201349⟩,
⟨64,186746233,186746347⟩]
theorem checked65344 : checkPrefixCuts (2^48) 8568700929 10 Manual.Count131072.C065344.packed 64 cuts65344 = true := by
 decide +kernel
def pointBounds65344 : List (Nat × Nat × Nat) := [(8568817664,114968542751253,114968931763079)]
theorem point_links_checked65344 : (cuts65344.take 1).map (fun c => (8568700929-1+2*2^10*c.k,114968375550007+c.lower,114968764561730+c.upper)) = pointBounds65344 := by
 decide +kernel
def cuts65345 : List PrefixCut := [⟨64,184509675,184509786⟩]
theorem checked65345 : checkPrefixCuts (2^48) 8568832001 10 Manual.Count131072.C065345.packed 64 cuts65345 = true := by
 decide +kernel
def cuts65346 : List PrefixCut := [⟨60,178068749,178068849⟩,
⟨64,190813657,190813763⟩]
theorem checked65346 : checkPrefixCuts (2^48) 8568963073 10 Manual.Count131072.C065346.packed 64 cuts65346 = true := by
 decide +kernel
def pointBounds65346 : List (Nat × Nat × Nat) := [(8569085952,114968924874664,114969313886712)]
theorem point_links_checked65346 : (cuts65346.take 1).map (fun c => (8568963073-1+2*2^10*c.k,114968746805915+c.lower,114969135817863+c.upper)) = pointBounds65346 := by
 decide +kernel
def cuts65347 : List PrefixCut := [⟨64,189923864,189923970⟩]
theorem checked65347 : checkPrefixCuts (2^48) 8569094145 10 Manual.Count131072.C065347.packed 64 cuts65347 = true := by
 decide +kernel
def cuts65348 : List PrefixCut := [⟨63,186340669,186340780⟩,
⟨64,189592491,189592603⟩]
theorem checked65348 : checkPrefixCuts (2^48) 8569225217 10 Manual.Count131072.C065348.packed 64 cuts65348 = true := by
 decide +kernel
def pointBounds65348 : List (Nat × Nat × Nat) := [(8569354240,114969313884105,114969702896376)]
theorem point_links_checked65348 : (cuts65348.take 1).map (fun c => (8569225217-1+2*2^10*c.k,114969127543436+c.lower,114969516555596+c.upper)) = pointBounds65348 := by
 decide +kernel
def cuts65349 : List PrefixCut := [⟨64,188045790,188045900⟩]
theorem checked65349 : checkPrefixCuts (2^48) 8569356289 10 Manual.Count131072.C065349.packed 64 cuts65349 = true := by
 decide +kernel
def cuts65350 : List PrefixCut := [⟨64,185316719,185316827⟩]
theorem checked65350 : checkPrefixCuts (2^48) 8569487361 10 Manual.Count131072.C065350.packed 64 cuts65350 = true := by
 decide +kernel
def cuts65351 : List PrefixCut := [⟨2,5583764,5583766⟩,
⟨64,186529161,186529268⟩]
theorem checked65351 : checkPrefixCuts (2^48) 8569618433 10 Manual.Count131072.C065351.packed 64 cuts65351 = true := by
 decide +kernel
def pointBounds65351 : List (Nat × Nat × Nat) := [(8569622528,114969696082200,114970085094692)]
theorem point_links_checked65351 : (cuts65351.take 1).map (fun c => (8569618433-1+2*2^10*c.k,114969690498436+c.lower,114970079510926+c.upper)) = pointBounds65351 := by
 decide +kernel
def cuts65352 : List PrefixCut := [⟨64,188004322,188004437⟩]
theorem checked65352 : checkPrefixCuts (2^48) 8569749505 10 Manual.Count131072.C065352.packed 64 cuts65352 = true := by
 decide +kernel
def cuts65353 : List PrefixCut := [⟨5,14550180,14550187⟩,
⟨64,188526957,188527059⟩]
theorem checked65353 : checkPrefixCuts (2^48) 8569880577 10 Manual.Count131072.C065353.packed 64 cuts65353 = true := by
 decide +kernel
def pointBounds65353 : List (Nat × Nat × Nat) := [(8569890816,114970079582099,114970468594818)]
theorem point_links_checked65353 : (cuts65353.take 1).map (fun c => (8569880577-1+2*2^10*c.k,114970065031919+c.lower,114970454044631+c.upper)) = pointBounds65353 := by
 decide +kernel
def cuts65354 : List PrefixCut := [⟨64,188129942,188130052⟩]
theorem checked65354 : checkPrefixCuts (2^48) 8570011649 10 Manual.Count131072.C065354.packed 64 cuts65354 = true := by
 decide +kernel
def cuts65355 : List PrefixCut := [⟨8,22892013,22892025⟩,
⟨64,188028536,188028645⟩]
theorem checked65355 : checkPrefixCuts (2^48) 8570142721 10 Manual.Count131072.C065355.packed 64 cuts65355 = true := by
 decide +kernel
def pointBounds65355 : List (Nat × Nat × Nat) := [(8570159104,114970464580831,114970853593767)]
theorem point_links_checked65355 : (cuts65355.take 1).map (fun c => (8570142721-1+2*2^10*c.k,114970441688818+c.lower,114970830701742+c.upper)) = pointBounds65355 := by
 decide +kernel
def cuts65356 : List PrefixCut := [⟨64,190521749,190521854⟩]
theorem checked65356 : checkPrefixCuts (2^48) 8570273793 10 Manual.Count131072.C065356.packed 64 cuts65356 = true := by
 decide +kernel
def cuts65357 : List PrefixCut := [⟨11,32021551,32021571⟩,
⟨64,189500695,189500807⟩]
theorem checked65357 : checkPrefixCuts (2^48) 8570404865 10 Manual.Count131072.C065357.packed 64 cuts65357 = true := by
 decide +kernel
def pointBounds65357 : List (Nat × Nat × Nat) := [(8570427392,114970852260654,114971241273812)]
theorem point_links_checked65357 : (cuts65357.take 1).map (fun c => (8570404865-1+2*2^10*c.k,114970820239103+c.lower,114971209252241+c.upper)) = pointBounds65357 := by
 decide +kernel
def cuts65358 : List PrefixCut := [⟨64,189859060,189859164⟩]
theorem checked65358 : checkPrefixCuts (2^48) 8570535937 10 Manual.Count131072.C065358.packed 64 cuts65358 = true := by
 decide +kernel
def cuts65359 : List PrefixCut := [⟨14,40854949,40854975⟩,
⟨64,187163164,187163280⟩]
theorem checked65359 : checkPrefixCuts (2^48) 8570667009 10 Manual.Count131072.C065359.packed 64 cuts65359 = true := by
 decide +kernel
def pointBounds65359 : List (Nat × Nat × Nat) := [(8570695680,114971240453807,114971629467187)]
theorem point_links_checked65359 : (cuts65359.take 1).map (fun c => (8570667009-1+2*2^10*c.k,114971199598858+c.lower,114971588612212+c.upper)) = pointBounds65359 := by
 decide +kernel
def cuts65360 : List PrefixCut := [⟨64,186372129,186372234⟩]
theorem checked65360 : checkPrefixCuts (2^48) 8570798081 10 Manual.Count131072.C065360.packed 64 cuts65360 = true := by
 decide +kernel
def cuts65361 : List PrefixCut := [⟨17,49983366,49983396⟩,
⟨64,187978445,187978552⟩]
theorem checked65361 : checkPrefixCuts (2^48) 8570929153 10 Manual.Count131072.C065361.packed 64 cuts65361 = true := by
 decide +kernel
def pointBounds65361 : List (Nat × Nat × Nat) := [(8570963968,114971623117517,114972012131122)]
theorem point_links_checked65361 : (cuts65361.take 1).map (fun c => (8570929153-1+2*2^10*c.k,114971573134151+c.lower,114971962147726+c.upper)) = pointBounds65361 := by
 decide +kernel
def cuts65362 : List PrefixCut := [⟨64,187056084,187056187⟩]
theorem checked65362 : checkPrefixCuts (2^48) 8571060225 10 Manual.Count131072.C065362.packed 64 cuts65362 = true := by
 decide +kernel
def cuts65363 : List PrefixCut := [⟨20,59866531,59866565⟩,
⟨64,187972708,187972816⟩]
theorem checked65363 : checkPrefixCuts (2^48) 8571191297 10 Manual.Count131072.C065363.packed 64 cuts65363 = true := by
 decide +kernel
def pointBounds65363 : List (Nat × Nat × Nat) := [(8571232256,114972008035211,114972397049030)]
theorem point_links_checked65363 : (cuts65363.take 1).map (fun c => (8571191297-1+2*2^10*c.k,114971948168680+c.lower,114972337182465+c.upper)) = pointBounds65363 := by
 decide +kernel
def cuts65364 : List PrefixCut := [⟨64,190531255,190531365⟩]
theorem checked65364 : checkPrefixCuts (2^48) 8571322369 10 Manual.Count131072.C065364.packed 64 cuts65364 = true := by
 decide +kernel
def cuts65365 : List PrefixCut := [⟨23,68632574,68632611⟩,
⟨64,189608877,189608985⟩]
theorem checked65365 : checkPrefixCuts (2^48) 8571453441 10 Manual.Count131072.C065365.packed 64 cuts65365 = true := by
 decide +kernel
def pointBounds65365 : List (Nat × Nat × Nat) := [(8571500544,114972395305217,114972784319257)]
theorem point_links_checked65365 : (cuts65365.take 1).map (fun c => (8571453441-1+2*2^10*c.k,114972326672643+c.lower,114972715686646+c.upper)) = pointBounds65365 := by
 decide +kernel
def cuts65366 : List PrefixCut := [⟨64,189770171,189770283⟩]
theorem checked65366 : checkPrefixCuts (2^48) 8571584513 10 Manual.Count131072.C065366.packed 64 cuts65366 = true := by
 decide +kernel
def cuts65367 : List PrefixCut := [⟨26,75887546,75887589⟩,
⟨64,187862693,187862792⟩]
theorem checked65367 : checkPrefixCuts (2^48) 8571715585 10 Manual.Count131072.C065367.packed 64 cuts65367 = true := by
 decide +kernel
def pointBounds65367 : List (Nat × Nat × Nat) := [(8571768832,114972781939237,114973170953503)]
theorem point_links_checked65367 : (cuts65367.take 1).map (fun c => (8571715585-1+2*2^10*c.k,114972706051691+c.lower,114973095065914+c.upper)) = pointBounds65367 := by
 decide +kernel
def cuts65368 : List PrefixCut := [⟨64,186940390,186940497⟩]
theorem checked65368 : checkPrefixCuts (2^48) 8571846657 10 Manual.Count131072.C065368.packed 64 cuts65368 = true := by
 decide +kernel
def cuts65369 : List PrefixCut := [⟨29,85867500,85867545⟩,
⟨64,191042073,191042182⟩]
theorem checked65369 : checkPrefixCuts (2^48) 8571977729 10 Manual.Count131072.C065369.packed 64 cuts65369 = true := by
 decide +kernel
def pointBounds65369 : List (Nat × Nat × Nat) := [(8572037120,114973166722274,114973555736748)]
theorem point_links_checked65369 : (cuts65369.take 1).map (fun c => (8571977729-1+2*2^10*c.k,114973080854774+c.lower,114973469869203+c.upper)) = pointBounds65369 := by
 decide +kernel
def cuts65370 : List PrefixCut := [⟨64,189364530,189364638⟩]
theorem checked65370 : checkPrefixCuts (2^48) 8572108801 10 Manual.Count131072.C065370.packed 64 cuts65370 = true := by
 decide +kernel
def cuts65371 : List PrefixCut := [⟨32,93778196,93778251⟩,
⟨64,186734800,186734912⟩]
theorem checked65371 : checkPrefixCuts (2^48) 8572239873 10 Manual.Count131072.C065371.packed 64 cuts65371 = true := by
 decide +kernel
def pointBounds65371 : List (Nat × Nat × Nat) := [(8572305408,114973555039573,114973944054274)]
theorem point_links_checked65371 : (cuts65371.take 1).map (fun c => (8572239873-1+2*2^10*c.k,114973461261377+c.lower,114973850276023+c.upper)) = pointBounds65371 := by
 decide +kernel
def cuts65372 : List PrefixCut := [⟨64,189457231,189457341⟩]
theorem checked65372 : checkPrefixCuts (2^48) 8572370945 10 Manual.Count131072.C065372.packed 64 cuts65372 = true := by
 decide +kernel
def cuts65373 : List PrefixCut := [⟨35,102443608,102443669⟩,
⟨64,186663427,186663541⟩]
theorem checked65373 : checkPrefixCuts (2^48) 8572502017 10 Manual.Count131072.C065373.packed 64 cuts65373 = true := by
 decide +kernel
def pointBounds65373 : List (Nat × Nat × Nat) := [(8572573696,114973939897016,114974328911945)]
theorem point_links_checked65373 : (cuts65373.take 1).map (fun c => (8572502017-1+2*2^10*c.k,114973837453408+c.lower,114974226468276+c.upper)) = pointBounds65373 := by
 decide +kernel
def cuts65374 : List PrefixCut := [⟨64,186069539,186069647⟩]
theorem checked65374 : checkPrefixCuts (2^48) 8572633089 10 Manual.Count131072.C065374.packed 64 cuts65374 = true := by
 decide +kernel
def cuts65375 : List PrefixCut := [⟨38,112257647,112257711⟩,
⟨64,187872549,187872658⟩]
theorem checked65375 : checkPrefixCuts (2^48) 8572764161 10 Manual.Count131072.C065375.packed 64 cuts65375 = true := by
 decide +kernel
def pointBounds65375 : List (Nat × Nat × Nat) := [(8572841984,114974322444021,114974711459175)]
theorem point_links_checked65375 : (cuts65375.take 1).map (fun c => (8572764161-1+2*2^10*c.k,114974210186374+c.lower,114974599201464+c.upper)) = pointBounds65375 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000167
