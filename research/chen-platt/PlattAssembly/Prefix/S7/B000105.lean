import PlattAssemblyKernel
import PlattCertificates.Count131072.C063360
import PlattCertificates.Count131072.C063361
import PlattCertificates.Count131072.C063362
import PlattCertificates.Count131072.C063363
import PlattCertificates.Count131072.C063364
import PlattCertificates.Count131072.C063365
import PlattCertificates.Count131072.C063366
import PlattCertificates.Count131072.C063367
import PlattCertificates.Count131072.C063368
import PlattCertificates.Count131072.C063369
import PlattCertificates.Count131072.C063370
import PlattCertificates.Count131072.C063371
import PlattCertificates.Count131072.C063372
import PlattCertificates.Count131072.C063373
import PlattCertificates.Count131072.C063374
import PlattCertificates.Count131072.C063375
import PlattCertificates.Count131072.C063376
import PlattCertificates.Count131072.C063377
import PlattCertificates.Count131072.C063378
import PlattCertificates.Count131072.C063379
import PlattCertificates.Count131072.C063380
import PlattCertificates.Count131072.C063381
import PlattCertificates.Count131072.C063382
import PlattCertificates.Count131072.C063383
import PlattCertificates.Count131072.C063384
import PlattCertificates.Count131072.C063385
import PlattCertificates.Count131072.C063386
import PlattCertificates.Count131072.C063387
import PlattCertificates.Count131072.C063388
import PlattCertificates.Count131072.C063389
import PlattCertificates.Count131072.C063390
import PlattCertificates.Count131072.C063391
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000105
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63360 : List PrefixCut := [⟨64,194793004,194793118⟩]
theorem checked63360 : checkPrefixCuts (2^48) 8308654081 10 Manual.Count131072.C063360.packed 64 cuts63360 = true := by
 decide +kernel
def cuts63361 : List PrefixCut := [⟨39,118364901,118364971⟩,
⟨64,195772362,195772473⟩]
theorem checked63361 : checkPrefixCuts (2^48) 8308785153 10 Manual.Count131072.C063361.packed 64 cuts63361 = true := by
 decide +kernel
def pointBounds63361 : List (Nat × Nat × Nat) := [(8308865024,114589149099540,114589537892260)]
theorem point_links_checked63361 : (cuts63361.take 1).map (fun c => (8308785153-1+2*2^10*c.k,114589030734639+c.lower,114589419527289+c.upper)) = pointBounds63361 := by
 decide +kernel
def cuts63362 : List PrefixCut := [⟨64,193465718,193465829⟩]
theorem checked63362 : checkPrefixCuts (2^48) 8308916225 10 Manual.Count131072.C063362.packed 64 cuts63362 = true := by
 decide +kernel
def cuts63363 : List PrefixCut := [⟨38,115414010,115414077⟩,
⟨64,194140177,194140290⟩]
theorem checked63363 : checkPrefixCuts (2^48) 8309047297 10 Manual.Count131072.C063363.packed 64 cuts63363 = true := by
 decide +kernel
def pointBounds63363 : List (Nat × Nat × Nat) := [(8309125120,114589535386729,114589924179668)]
theorem point_links_checked63363 : (cuts63363.take 1).map (fun c => (8309047297-1+2*2^10*c.k,114589419972719+c.lower,114589808765591+c.upper)) = pointBounds63363 := by
 decide +kernel
def cuts63364 : List PrefixCut := [⟨64,193595111,193595226⟩]
theorem checked63364 : checkPrefixCuts (2^48) 8309178369 10 Manual.Count131072.C063364.packed 64 cuts63364 = true := by
 decide +kernel
def cuts63365 : List PrefixCut := [⟨37,110634085,110634149⟩,
⟨64,192474209,192474316⟩]
theorem checked63365 : checkPrefixCuts (2^48) 8309309441 10 Manual.Count131072.C063365.packed 64 cuts63365 = true := by
 decide +kernel
def pointBounds63365 : List (Nat × Nat × Nat) := [(8309385216,114589918342092,114590307135256)]
theorem point_links_checked63365 : (cuts63365.take 1).map (fun c => (8309309441-1+2*2^10*c.k,114589807708007+c.lower,114590196501107+c.upper)) = pointBounds63365 := by
 decide +kernel
def cuts63366 : List PrefixCut := [⟨64,195147215,195147326⟩]
theorem checked63366 : checkPrefixCuts (2^48) 8309440513 10 Manual.Count131072.C063366.packed 64 cuts63366 = true := by
 decide +kernel
def cuts63367 : List PrefixCut := [⟨36,110325748,110325814⟩,
⟨64,192773012,192773125⟩]
theorem checked63367 : checkPrefixCuts (2^48) 8309571585 10 Manual.Count131072.C063367.packed 64 cuts63367 = true := by
 decide +kernel
def pointBounds63367 : List (Nat × Nat × Nat) := [(8309645312,114590305655179,114590694448563)]
theorem point_links_checked63367 : (cuts63367.take 1).map (fun c => (8309571585-1+2*2^10*c.k,114590195329431+c.lower,114590584122749+c.upper)) = pointBounds63367 := by
 decide +kernel
def cuts63368 : List PrefixCut := [⟨64,195683020,195683130⟩]
theorem checked63368 : checkPrefixCuts (2^48) 8309702657 10 Manual.Count131072.C063368.packed 64 cuts63368 = true := by
 decide +kernel
def cuts63369 : List PrefixCut := [⟨35,106799556,106799611⟩,
⟨64,194155681,194155788⟩]
theorem checked63369 : checkPrefixCuts (2^48) 8309833729 10 Manual.Count131072.C063369.packed 64 cuts63369 = true := by
 decide +kernel
def pointBounds63369 : List (Nat × Nat × Nat) := [(8309905408,114590690585019,114591079378615)]
theorem point_links_checked63369 : (cuts63369.take 1).map (fun c => (8309833729-1+2*2^10*c.k,114590583785463+c.lower,114590972579004+c.upper)) = pointBounds63369 := by
 decide +kernel
def cuts63370 : List PrefixCut := [⟨64,193915508,193915616⟩]
theorem checked63370 : checkPrefixCuts (2^48) 8309964801 10 Manual.Count131072.C063370.packed 64 cuts63370 = true := by
 decide +kernel
def cuts63371 : List PrefixCut := [⟨34,102528420,102528480⟩,
⟨64,193743102,193743213⟩]
theorem checked63371 : checkPrefixCuts (2^48) 8310095873 10 Manual.Count131072.C063371.packed 64 cuts63371 = true := by
 decide +kernel
def pointBounds63371 : List (Nat × Nat × Nat) := [(8310165504,114591074385072,114591463178888)]
theorem point_links_checked63371 : (cuts63371.take 1).map (fun c => (8310095873-1+2*2^10*c.k,114590971856652+c.lower,114591360650408+c.upper)) = pointBounds63371 := by
 decide +kernel
def cuts63372 : List PrefixCut := [⟨64,192859411,192859522⟩]
theorem checked63372 : checkPrefixCuts (2^48) 8310226945 10 Manual.Count131072.C063372.packed 64 cuts63372 = true := by
 decide +kernel
def cuts63373 : List PrefixCut := [⟨33,101847788,101847841⟩,
⟨64,197394958,197395066⟩]
theorem checked63373 : checkPrefixCuts (2^48) 8310358017 10 Manual.Count131072.C063373.packed 64 cuts63373 = true := by
 decide +kernel
def pointBounds63373 : List (Nat × Nat × Nat) := [(8310425600,114591460306953,114591849100984)]
theorem point_links_checked63373 : (cuts63373.take 1).map (fun c => (8310358017-1+2*2^10*c.k,114591358459165+c.lower,114591747253143+c.upper)) = pointBounds63373 := by
 decide +kernel
def cuts63374 : List PrefixCut := [⟨64,192074307,192074424⟩]
theorem checked63374 : checkPrefixCuts (2^48) 8310489089 10 Manual.Count131072.C063374.packed 64 cuts63374 = true := by
 decide +kernel
def cuts63375 : List PrefixCut := [⟨32,97475457,97475514⟩,
⟨64,194205034,194205151⟩]
theorem checked63375 : checkPrefixCuts (2^48) 8310620161 10 Manual.Count131072.C063375.packed 64 cuts63375 = true := by
 decide +kernel
def pointBounds63375 : List (Nat × Nat × Nat) := [(8310685696,114591845403887,114592234198147)]
theorem point_links_checked63375 : (cuts63375.take 1).map (fun c => (8310620161-1+2*2^10*c.k,114591747928430+c.lower,114592136722633+c.upper)) = pointBounds63375 := by
 decide +kernel
def cuts63376 : List PrefixCut := [⟨64,193524618,193524734⟩]
theorem checked63376 : checkPrefixCuts (2^48) 8310751233 10 Manual.Count131072.C063376.packed 64 cuts63376 = true := by
 decide +kernel
def cuts63377 : List PrefixCut := [⟨31,94017848,94017903⟩,
⟨64,195655229,195655337⟩]
theorem checked63377 : checkPrefixCuts (2^48) 8310882305 10 Manual.Count131072.C063377.packed 64 cuts63377 = true := by
 decide +kernel
def pointBounds63377 : List (Nat × Nat × Nat) := [(8310945792,114592229675930,114592618470421)]
theorem point_links_checked63377 : (cuts63377.take 1).map (fun c => (8310882305-1+2*2^10*c.k,114592135658082+c.lower,114592524452518+c.upper)) = pointBounds63377 := by
 decide +kernel
def cuts63378 : List PrefixCut := [⟨64,194907072,194907182⟩]
theorem checked63378 : checkPrefixCuts (2^48) 8311013377 10 Manual.Count131072.C063378.packed 64 cuts63378 = true := by
 decide +kernel
def cuts63379 : List PrefixCut := [⟨30,92761823,92761876⟩,
⟨64,197782682,197782797⟩]
theorem checked63379 : checkPrefixCuts (2^48) 8311144449 10 Manual.Count131072.C063379.packed 64 cuts63379 = true := by
 decide +kernel
def pointBounds63379 : List (Nat × Nat × Nat) := [(8311205888,114592618982206,114593007776913)]
theorem point_links_checked63379 : (cuts63379.take 1).map (fun c => (8311144449-1+2*2^10*c.k,114592526220383+c.lower,114592915015037+c.upper)) = pointBounds63379 := by
 decide +kernel
def cuts63380 : List PrefixCut := [⟨64,192394812,192394923⟩]
theorem checked63380 : checkPrefixCuts (2^48) 8311275521 10 Manual.Count131072.C063380.packed 64 cuts63380 = true := by
 decide +kernel
def cuts63381 : List PrefixCut := [⟨29,88153130,88153185⟩,
⟨64,194525319,194525439⟩]
theorem checked63381 : checkPrefixCuts (2^48) 8311406593 10 Manual.Count131072.C063381.packed 64 cuts63381 = true := by
 decide +kernel
def pointBounds63381 : List (Nat × Nat × Nat) := [(8311465984,114593004551007,114593393345942)]
theorem point_links_checked63381 : (cuts63381.take 1).map (fun c => (8311406593-1+2*2^10*c.k,114592916397877+c.lower,114593305192757+c.upper)) = pointBounds63381 := by
 decide +kernel
def cuts63382 : List PrefixCut := [⟨64,194759320,194759435⟩]
theorem checked63382 : checkPrefixCuts (2^48) 8311537665 10 Manual.Count131072.C063382.packed 64 cuts63382 = true := by
 decide +kernel
def cuts63383 : List PrefixCut := [⟨28,84560686,84560736⟩,
⟨64,193537109,193537221⟩]
theorem checked63383 : checkPrefixCuts (2^48) 8311668737 10 Manual.Count131072.C063383.packed 64 cuts63383 = true := by
 decide +kernel
def pointBounds63383 : List (Nat × Nat × Nat) := [(8311726080,114593390243202,114593779038367)]
theorem point_links_checked63383 : (cuts63383.take 1).map (fun c => (8311668737-1+2*2^10*c.k,114593305682516+c.lower,114593694477631+c.upper)) = pointBounds63383 := by
 decide +kernel
def cuts63384 : List PrefixCut := [⟨64,195227275,195227389⟩]
theorem checked63384 : checkPrefixCuts (2^48) 8311799809 10 Manual.Count131072.C063384.packed 64 cuts63384 = true := by
 decide +kernel
def cuts63385 : List PrefixCut := [⟨27,81510281,81510327⟩,
⟨64,193023055,193023163⟩]
theorem checked63385 : checkPrefixCuts (2^48) 8311930881 10 Manual.Count131072.C063385.packed 64 cuts63385 = true := by
 decide +kernel
def pointBounds63385 : List (Nat × Nat × Nat) := [(8311986176,114593775957181,114594164752568)]
theorem point_links_checked63385 : (cuts63385.take 1).map (fun c => (8311930881-1+2*2^10*c.k,114593694446900+c.lower,114594083242241+c.upper)) = pointBounds63385 := by
 decide +kernel
def cuts63386 : List PrefixCut := [⟨64,192308866,192308976⟩]
theorem checked63386 : checkPrefixCuts (2^48) 8312061953 10 Manual.Count131072.C063386.packed 64 cuts63386 = true := by
 decide +kernel
def cuts63387 : List PrefixCut := [⟨26,79103464,79103510⟩,
⟨64,193084690,193084804⟩]
theorem checked63387 : checkPrefixCuts (2^48) 8312193025 10 Manual.Count131072.C063387.packed 64 cuts63387 = true := by
 decide +kernel
def pointBounds63387 : List (Nat × Nat × Nat) := [(8312246272,114594158882285,114594547677890)]
theorem point_links_checked63387 : (cuts63387.take 1).map (fun c => (8312193025-1+2*2^10*c.k,114594079778821+c.lower,114594468574380+c.upper)) = pointBounds63387 := by
 decide +kernel
def cuts63388 : List PrefixCut := [⟨64,195384269,195384387⟩]
theorem checked63388 : checkPrefixCuts (2^48) 8312324097 10 Manual.Count131072.C063388.packed 64 cuts63388 = true := by
 decide +kernel
def cuts63389 : List PrefixCut := [⟨25,76933830,76933875⟩,
⟨64,197988528,197988639⟩]
theorem checked63389 : checkPrefixCuts (2^48) 8312455169 10 Manual.Count131072.C063389.packed 64 cuts63389 = true := by
 decide +kernel
def pointBounds63389 : List (Nat × Nat × Nat) := [(8312506368,114594545181610,114594933977446)]
theorem point_links_checked63389 : (cuts63389.take 1).map (fun c => (8312455169-1+2*2^10*c.k,114594468247780+c.lower,114594857043571+c.upper)) = pointBounds63389 := by
 decide +kernel
def cuts63390 : List PrefixCut := [⟨64,195276531,195276643⟩]
theorem checked63390 : checkPrefixCuts (2^48) 8312586241 10 Manual.Count131072.C063390.packed 64 cuts63390 = true := by
 decide +kernel
def cuts63391 : List PrefixCut := [⟨24,72935857,72935898⟩,
⟨64,193174102,193174214⟩]
theorem checked63391 : checkPrefixCuts (2^48) 8312717313 10 Manual.Count131072.C063391.packed 64 cuts63391 = true := by
 decide +kernel
def pointBounds63391 : List (Nat × Nat × Nat) := [(8312766464,114594934448696,114595323244751)]
theorem point_links_checked63391 : (cuts63391.take 1).map (fun c => (8312717313-1+2*2^10*c.k,114594861512839+c.lower,114595250308853+c.upper)) = pointBounds63391 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000105
