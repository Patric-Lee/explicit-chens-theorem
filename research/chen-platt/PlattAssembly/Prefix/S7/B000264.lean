import PlattAssemblyKernel
import PlattCertificates.Count131072.C068448
import PlattCertificates.Count131072.C068449
import PlattCertificates.Count131072.C068450
import PlattCertificates.Count131072.C068451
import PlattCertificates.Count131072.C068452
import PlattCertificates.Count131072.C068453
import PlattCertificates.Count131072.C068454
import PlattCertificates.Count131072.C068455
import PlattCertificates.Count131072.C068456
import PlattCertificates.Count131072.C068457
import PlattCertificates.Count131072.C068458
import PlattCertificates.Count131072.C068459
import PlattCertificates.Count131072.C068460
import PlattCertificates.Count131072.C068461
import PlattCertificates.Count131072.C068462
import PlattCertificates.Count131072.C068463
import PlattCertificates.Count131072.C068464
import PlattCertificates.Count131072.C068465
import PlattCertificates.Count131072.C068466
import PlattCertificates.Count131072.C068467
import PlattCertificates.Count131072.C068468
import PlattCertificates.Count131072.C068469
import PlattCertificates.Count131072.C068470
import PlattCertificates.Count131072.C068471
import PlattCertificates.Count131072.C068472
import PlattCertificates.Count131072.C068473
import PlattCertificates.Count131072.C068474
import PlattCertificates.Count131072.C068475
import PlattCertificates.Count131072.C068476
import PlattCertificates.Count131072.C068477
import PlattCertificates.Count131072.C068478
import PlattCertificates.Count131072.C068479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000264
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68448 : List PrefixCut := [⟨52,145479049,145479131⟩,
⟨64,177528736,177528839⟩]
theorem checked68448 : checkPrefixCuts (2^48) 8975548417 10 Manual.Count131072.C068448.packed 64 cuts68448 = true := by
 decide +kernel
def pointBounds68448 : List (Nat × Nat × Nat) := [(8975654912,115538773386250,115539162729972)]
theorem point_links_checked68448 : (cuts68448.take 1).map (fun c => (8975548417-1+2*2^10*c.k,115538627907201+c.lower,115539017250841+c.upper)) = pointBounds68448 := by
 decide +kernel
def cuts68449 : List PrefixCut := [⟨64,179470430,179470532⟩]
theorem checked68449 : checkPrefixCuts (2^48) 8975679489 10 Manual.Count131072.C068449.packed 64 cuts68449 = true := by
 decide +kernel
def cuts68450 : List PrefixCut := [⟨61,169809265,169809365⟩,
⟨64,178652454,178652559⟩]
theorem checked68450 : checkPrefixCuts (2^48) 8975810561 10 Manual.Count131072.C068450.packed 64 cuts68450 = true := by
 decide +kernel
def pointBounds68450 : List (Nat × Nat × Nat) := [(8975935488,115539154715632,115539544059577)]
theorem point_links_checked68450 : (cuts68450.take 1).map (fun c => (8975810561-1+2*2^10*c.k,115538984906367+c.lower,115539374250212+c.upper)) = pointBounds68450 := by
 decide +kernel
def cuts68451 : List PrefixCut := [⟨64,177803185,177803291⟩]
theorem checked68451 : checkPrefixCuts (2^48) 8975941633 10 Manual.Count131072.C068451.packed 64 cuts68451 = true := by
 decide +kernel
def cuts68452 : List PrefixCut := [⟨64,178835396,178835503⟩]
theorem checked68452 : checkPrefixCuts (2^48) 8976072705 10 Manual.Count131072.C068452.packed 64 cuts68452 = true := by
 decide +kernel
def cuts68453 : List PrefixCut := [⟨6,16745107,16745116⟩,
⟨64,180776972,180777078⟩]
theorem checked68453 : checkPrefixCuts (2^48) 8976203777 10 Manual.Count131072.C068453.packed 64 cuts68453 = true := by
 decide +kernel
def pointBounds68453 : List (Nat × Nat × Nat) := [(8976216064,115539536942509,115539926286681)]
theorem point_links_checked68453 : (cuts68453.take 1).map (fun c => (8976203777-1+2*2^10*c.k,115539520197402+c.lower,115539909541565+c.upper)) = pointBounds68453 := by
 decide +kernel
def cuts68454 : List PrefixCut := [⟨64,180711623,180711723⟩]
theorem checked68454 : checkPrefixCuts (2^48) 8976334849 10 Manual.Count131072.C068454.packed 64 cuts68454 = true := by
 decide +kernel
def cuts68455 : List PrefixCut := [⟨15,42394572,42394598⟩,
⟨64,181963246,181963355⟩]
theorem checked68455 : checkPrefixCuts (2^48) 8976465921 10 Manual.Count131072.C068455.packed 64 cuts68455 = true := by
 decide +kernel
def pointBounds68455 : List (Nat × Nat × Nat) := [(8976496640,115539924080569,115540313424964)]
theorem point_links_checked68455 : (cuts68455.take 1).map (fun c => (8976465921-1+2*2^10*c.k,115539881685997+c.lower,115540271030366+c.upper)) = pointBounds68455 := by
 decide +kernel
def cuts68456 : List PrefixCut := [⟨64,176065614,176065722⟩]
theorem checked68456 : checkPrefixCuts (2^48) 8976596993 10 Manual.Count131072.C068456.packed 64 cuts68456 = true := by
 decide +kernel
def cuts68457 : List PrefixCut := [⟨24,67728920,67728959⟩,
⟨64,180107939,180108040⟩]
theorem checked68457 : checkPrefixCuts (2^48) 8976728065 10 Manual.Count131072.C068457.packed 64 cuts68457 = true := by
 decide +kernel
def pointBounds68457 : List (Nat × Nat × Nat) := [(8976777216,115540307443777,115540696788402)]
theorem point_links_checked68457 : (cuts68457.take 1).map (fun c => (8976728065-1+2*2^10*c.k,115540239714857+c.lower,115540629059443+c.upper)) = pointBounds68457 := by
 decide +kernel
def cuts68458 : List PrefixCut := [⟨64,179791762,179791864⟩]
theorem checked68458 : checkPrefixCuts (2^48) 8976859137 10 Manual.Count131072.C068458.packed 64 cuts68458 = true := by
 decide +kernel
def cuts68459 : List PrefixCut := [⟨33,91180439,91180491⟩,
⟨64,178095956,178096056⟩]
theorem checked68459 : checkPrefixCuts (2^48) 8976990209 10 Manual.Count131072.C068459.packed 64 cuts68459 = true := by
 decide +kernel
def pointBounds68459 : List (Nat × Nat × Nat) := [(8977057792,115540690794997,115541080139838)]
theorem point_links_checked68459 : (cuts68459.take 1).map (fun c => (8976990209-1+2*2^10*c.k,115540599614558+c.lower,115540988959347+c.upper)) = pointBounds68459 := by
 decide +kernel
def cuts68460 : List PrefixCut := [⟨64,178720454,178720556⟩]
theorem checked68460 : checkPrefixCuts (2^48) 8977121281 10 Manual.Count131072.C068460.packed 64 cuts68460 = true := by
 decide +kernel
def cuts68461 : List PrefixCut := [⟨42,117891371,117891442⟩,
⟨64,179564410,179564516⟩]
theorem checked68461 : checkPrefixCuts (2^48) 8977252353 10 Manual.Count131072.C068461.packed 64 cuts68461 = true := by
 decide +kernel
def pointBounds68461 : List (Nat × Nat × Nat) := [(8977338368,115541074322339,115541463667401)]
theorem point_links_checked68461 : (cuts68461.take 1).map (fun c => (8977252353-1+2*2^10*c.k,115540956430968+c.lower,115541345775959+c.upper)) = pointBounds68461 := by
 decide +kernel
def cuts68462 : List PrefixCut := [⟨64,179248243,179248352⟩]
theorem checked68462 : checkPrefixCuts (2^48) 8977383425 10 Manual.Count131072.C068462.packed 64 cuts68462 = true := by
 decide +kernel
def cuts68463 : List PrefixCut := [⟨51,146011569,146011657⟩,
⟨64,180844649,180844762⟩]
theorem checked68463 : checkPrefixCuts (2^48) 8977514497 10 Manual.Count131072.C068463.packed 64 cuts68463 = true := by
 decide +kernel
def pointBounds68463 : List (Nat × Nat × Nat) := [(8977618944,115541461255190,115541850600484)]
theorem point_links_checked68463 : (cuts68463.take 1).map (fun c => (8977514497-1+2*2^10*c.k,115541315243621+c.lower,115541704588827+c.upper)) = pointBounds68463 := by
 decide +kernel
def cuts68464 : List PrefixCut := [⟨64,181312291,181312393⟩]
theorem checked68464 : checkPrefixCuts (2^48) 8977645569 10 Manual.Count131072.C068464.packed 64 cuts68464 = true := by
 decide +kernel
def cuts68465 : List PrefixCut := [⟨60,167483393,167483494⟩,
⟨64,178958210,178958319⟩]
theorem checked68465 : checkPrefixCuts (2^48) 8977776641 10 Manual.Count131072.C068465.packed 64 cuts68465 = true := by
 decide +kernel
def pointBounds68465 : List (Nat × Nat × Nat) := [(8977899520,115541844883954,115542234229476)]
theorem point_links_checked68465 : (cuts68465.take 1).map (fun c => (8977776641-1+2*2^10*c.k,115541677400561+c.lower,115542066745982+c.upper)) = pointBounds68465 := by
 decide +kernel
def cuts68466 : List PrefixCut := [⟨64,177576149,177576244⟩]
theorem checked68466 : checkPrefixCuts (2^48) 8977907713 10 Manual.Count131072.C068466.packed 64 cuts68466 = true := by
 decide +kernel
def cuts68467 : List PrefixCut := [⟨64,181461093,181461196⟩]
theorem checked68467 : checkPrefixCuts (2^48) 8978038785 10 Manual.Count131072.C068467.packed 64 cuts68467 = true := by
 decide +kernel
def cuts68468 : List PrefixCut := [⟨5,14013904,14013912⟩,
⟨64,177163392,177163496⟩]
theorem checked68468 : checkPrefixCuts (2^48) 8978169857 10 Manual.Count131072.C068468.packed 64 cuts68468 = true := by
 decide +kernel
def pointBounds68468 : List (Nat × Nat × Nat) := [(8978180096,115542229409917,115542618755653)]
theorem point_links_checked68468 : (cuts68468.take 1).map (fun c => (8978169857-1+2*2^10*c.k,115542215396013+c.lower,115542604741741+c.upper)) = pointBounds68468 := by
 decide +kernel
def cuts68469 : List PrefixCut := [⟨64,178195372,178195480⟩]
theorem checked68469 : checkPrefixCuts (2^48) 8978300929 10 Manual.Count131072.C068469.packed 64 cuts68469 = true := by
 decide +kernel
def cuts68470 : List PrefixCut := [⟨14,38247081,38247100⟩,
⟨64,177910617,177910711⟩]
theorem checked68470 : checkPrefixCuts (2^48) 8978432001 10 Manual.Count131072.C068470.packed 64 cuts68470 = true := by
 decide +kernel
def pointBounds68470 : List (Nat × Nat × Nat) := [(8978460672,115542609001858,115542998347817)]
theorem point_links_checked68470 : (cuts68470.take 1).map (fun c => (8978432001-1+2*2^10*c.k,115542570754777+c.lower,115542960100717+c.upper)) = pointBounds68470 := by
 decide +kernel
def cuts68471 : List PrefixCut := [⟨64,181356464,181356568⟩]
theorem checked68471 : checkPrefixCuts (2^48) 8978563073 10 Manual.Count131072.C068471.packed 64 cuts68471 = true := by
 decide +kernel
def cuts68472 : List PrefixCut := [⟨23,62980382,62980419⟩,
⟨64,178218905,178219006⟩]
theorem checked68472 : checkPrefixCuts (2^48) 8978694145 10 Manual.Count131072.C068472.packed 64 cuts68472 = true := by
 decide +kernel
def pointBounds68472 : List (Nat × Nat × Nat) := [(8978741248,115542993002240,115543382348415)]
theorem point_links_checked68472 : (cuts68472.take 1).map (fun c => (8978694145-1+2*2^10*c.k,115542930021858+c.lower,115543319367996+c.upper)) = pointBounds68472 := by
 decide +kernel
def cuts68473 : List PrefixCut := [⟨64,180786886,180786994⟩]
theorem checked68473 : checkPrefixCuts (2^48) 8978825217 10 Manual.Count131072.C068473.packed 64 cuts68473 = true := by
 decide +kernel
def cuts68474 : List PrefixCut := [⟨33,94295288,94295342⟩,
⟨64,180564816,180564920⟩]
theorem checked68474 : checkPrefixCuts (2^48) 8978956289 10 Manual.Count131072.C068474.packed 64 cuts68474 = true := by
 decide +kernel
def pointBounds68474 : List (Nat × Nat × Nat) := [(8979023872,115543383322937,115543772669338)]
theorem point_links_checked68474 : (cuts68474.take 1).map (fun c => (8978956289-1+2*2^10*c.k,115543289027649+c.lower,115543678373996+c.upper)) = pointBounds68474 := by
 decide +kernel
def cuts68475 : List PrefixCut := [⟨64,178712655,178712766⟩]
theorem checked68475 : checkPrefixCuts (2^48) 8979087361 10 Manual.Count131072.C068475.packed 64 cuts68475 = true := by
 decide +kernel
def cuts68476 : List PrefixCut := [⟨43,121846637,121846705⟩,
⟨64,179117585,179117688⟩]
theorem checked68476 : checkPrefixCuts (2^48) 8979218433 10 Manual.Count131072.C068476.packed 64 cuts68476 = true := by
 decide +kernel
def pointBounds68476 : List (Nat × Nat × Nat) := [(8979306496,115543770151757,115544159498387)]
theorem point_links_checked68476 : (cuts68476.take 1).map (fun c => (8979218433-1+2*2^10*c.k,115543648305120+c.lower,115544037651682+c.upper)) = pointBounds68476 := by
 decide +kernel
def cuts68477 : List PrefixCut := [⟨64,180368810,180368919⟩]
theorem checked68477 : checkPrefixCuts (2^48) 8979349505 10 Manual.Count131072.C068477.packed 64 cuts68477 = true := by
 decide +kernel
def cuts68478 : List PrefixCut := [⟨53,149020152,149020236⟩,
⟨64,180084075,180084178⟩]
theorem checked68478 : checkPrefixCuts (2^48) 8979480577 10 Manual.Count131072.C068478.packed 64 cuts68478 = true := by
 decide +kernel
def pointBounds68478 : List (Nat × Nat × Nat) := [(8979589120,115544156811667,115544546158525)]
theorem point_links_checked68478 : (cuts68478.take 1).map (fun c => (8979480577-1+2*2^10*c.k,115544007791515+c.lower,115544397138289+c.upper)) = pointBounds68478 := by
 decide +kernel
def cuts68479 : List PrefixCut := [⟨64,181241244,181241342⟩]
theorem checked68479 : checkPrefixCuts (2^48) 8979611649 10 Manual.Count131072.C068479.packed 64 cuts68479 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000264
