import PlattAssemblyKernel
import PlattCertificates.Count131072.C066464
import PlattCertificates.Count131072.C066465
import PlattCertificates.Count131072.C066466
import PlattCertificates.Count131072.C066467
import PlattCertificates.Count131072.C066468
import PlattCertificates.Count131072.C066469
import PlattCertificates.Count131072.C066470
import PlattCertificates.Count131072.C066471
import PlattCertificates.Count131072.C066472
import PlattCertificates.Count131072.C066473
import PlattCertificates.Count131072.C066474
import PlattCertificates.Count131072.C066475
import PlattCertificates.Count131072.C066476
import PlattCertificates.Count131072.C066477
import PlattCertificates.Count131072.C066478
import PlattCertificates.Count131072.C066479
import PlattCertificates.Count131072.C066480
import PlattCertificates.Count131072.C066481
import PlattCertificates.Count131072.C066482
import PlattCertificates.Count131072.C066483
import PlattCertificates.Count131072.C066484
import PlattCertificates.Count131072.C066485
import PlattCertificates.Count131072.C066486
import PlattCertificates.Count131072.C066487
import PlattCertificates.Count131072.C066488
import PlattCertificates.Count131072.C066489
import PlattCertificates.Count131072.C066490
import PlattCertificates.Count131072.C066491
import PlattCertificates.Count131072.C066492
import PlattCertificates.Count131072.C066493
import PlattCertificates.Count131072.C066494
import PlattCertificates.Count131072.C066495
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000202
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66464 : List PrefixCut := [⟨64,184731116,184731220⟩]
theorem checked66464 : checkPrefixCuts (2^48) 8715501569 10 Manual.Count131072.C066464.packed 64 cuts66464 = true := by
 decide +kernel
def cuts66465 : List PrefixCut := [⟨33,95238782,95238838⟩,
⟨64,187376523,187376633⟩]
theorem checked66465 : checkPrefixCuts (2^48) 8715632641 10 Manual.Count131072.C066465.packed 64 cuts66465 = true := by
 decide +kernel
def pointBounds66465 : List (Nat × Nat × Nat) := [(8715700224,115177598445961,115177987578972)]
theorem point_links_checked66465 : (cuts66465.take 1).map (fun c => (8715632641-1+2*2^10*c.k,115177503207179+c.lower,115177892340134+c.upper)) = pointBounds66465 := by
 decide +kernel
def cuts66466 : List PrefixCut := [⟨64,185823570,185823681⟩]
theorem checked66466 : checkPrefixCuts (2^48) 8715763713 10 Manual.Count131072.C066466.packed 64 cuts66466 = true := by
 decide +kernel
def cuts66467 : List PrefixCut := [⟨38,109445355,109445419⟩,
⟨64,183140376,183140482⟩]
theorem checked66467 : checkPrefixCuts (2^48) 8715894785 10 Manual.Count131072.C066467.packed 64 cuts66467 = true := by
 decide +kernel
def pointBounds66467 : List (Nat × Nat × Nat) := [(8715972608,115177985852627,115178374985867)]
theorem point_links_checked66467 : (cuts66467.take 1).map (fun c => (8715894785-1+2*2^10*c.k,115177876407272+c.lower,115178265540448+c.upper)) = pointBounds66467 := by
 decide +kernel
def cuts66468 : List PrefixCut := [⟨64,186302396,186302506⟩]
theorem checked66468 : checkPrefixCuts (2^48) 8716025857 10 Manual.Count131072.C066468.packed 64 cuts66468 = true := by
 decide +kernel
def cuts66469 : List PrefixCut := [⟨43,123457287,123457360⟩,
⟨64,183231735,183231842⟩]
theorem checked66469 : checkPrefixCuts (2^48) 8716156929 10 Manual.Count131072.C066469.packed 64 cuts66469 = true := by
 decide +kernel
def pointBounds66469 : List (Nat × Nat × Nat) := [(8716244992,115178369307331,115178758440796)]
theorem point_links_checked66469 : (cuts66469.take 1).map (fun c => (8716156929-1+2*2^10*c.k,115178245850044+c.lower,115178634983436+c.upper)) = pointBounds66469 := by
 decide +kernel
def cuts66470 : List PrefixCut := [⟨64,187427030,187427144⟩]
theorem checked66470 : checkPrefixCuts (2^48) 8716288001 10 Manual.Count131072.C066470.packed 64 cuts66470 = true := by
 decide +kernel
def cuts66471 : List PrefixCut := [⟨48,140891354,140891431⟩,
⟨64,187456515,187456619⟩]
theorem checked66471 : checkPrefixCuts (2^48) 8716419073 10 Manual.Count131072.C066471.packed 64 cuts66471 = true := by
 decide +kernel
def pointBounds66471 : List (Nat × Nat × Nat) := [(8716517376,115178757400163,115179146533853)]
theorem point_links_checked66471 : (cuts66471.take 1).map (fun c => (8716419073-1+2*2^10*c.k,115178616508809+c.lower,115179005642422+c.upper)) = pointBounds66471 := by
 decide +kernel
def cuts66472 : List PrefixCut := [⟨64,187292221,187292334⟩]
theorem checked66472 : checkPrefixCuts (2^48) 8716550145 10 Manual.Count131072.C066472.packed 64 cuts66472 = true := by
 decide +kernel
def cuts66473 : List PrefixCut := [⟨54,154578536,154578631⟩,
⟨64,184157159,184157272⟩]
theorem checked66473 : checkPrefixCuts (2^48) 8716681217 10 Manual.Count131072.C066473.packed 64 cuts66473 = true := by
 decide +kernel
def pointBounds66473 : List (Nat × Nat × Nat) := [(8716791808,115179145836081,115179534970006)]
theorem point_links_checked66473 : (cuts66473.take 1).map (fun c => (8716681217-1+2*2^10*c.k,115178991257545+c.lower,115179380391375+c.upper)) = pointBounds66473 := by
 decide +kernel
def cuts66474 : List PrefixCut := [⟨64,182636712,182636822⟩]
theorem checked66474 : checkPrefixCuts (2^48) 8716812289 10 Manual.Count131072.C066474.packed 64 cuts66474 = true := by
 decide +kernel
def cuts66475 : List PrefixCut := [⟨60,171978249,171978350⟩,
⟨64,183505807,183505915⟩]
theorem checked66475 : checkPrefixCuts (2^48) 8716943361 10 Manual.Count131072.C066475.packed 64 cuts66475 = true := by
 decide +kernel
def pointBounds66475 : List (Nat × Nat × Nat) := [(8717066240,115179530029665,115179919163819)]
theorem point_links_checked66475 : (cuts66475.take 1).map (fun c => (8716943361-1+2*2^10*c.k,115179358051416+c.lower,115179747185469+c.upper)) = pointBounds66475 := by
 decide +kernel
def cuts66476 : List PrefixCut := [⟨64,183309315,183309426⟩]
theorem checked66476 : checkPrefixCuts (2^48) 8717074433 10 Manual.Count131072.C066476.packed 64 cuts66476 = true := by
 decide +kernel
def cuts66477 : List PrefixCut := [⟨64,185469963,185470069⟩]
theorem checked66477 : checkPrefixCuts (2^48) 8717205505 10 Manual.Count131072.C066477.packed 64 cuts66477 = true := by
 decide +kernel
def cuts66478 : List PrefixCut := [⟨2,5650591,5650593⟩,
⟨64,185725473,185725584⟩]
theorem checked66478 : checkPrefixCuts (2^48) 8717336577 10 Manual.Count131072.C066478.packed 64 cuts66478 = true := by
 decide +kernel
def pointBounds66478 : List (Nat × Nat × Nat) := [(8717340672,115179915987092,115180305121472)]
theorem point_links_checked66478 : (cuts66478.take 1).map (fun c => (8717336577-1+2*2^10*c.k,115179910336501+c.lower,115180299470879+c.upper)) = pointBounds66478 := by
 decide +kernel
def cuts66479 : List PrefixCut := [⟨64,185464379,185464488⟩]
theorem checked66479 : checkPrefixCuts (2^48) 8717467649 10 Manual.Count131072.C066479.packed 64 cuts66479 = true := by
 decide +kernel
def cuts66480 : List PrefixCut := [⟨8,23021411,23021422⟩,
⟨64,186397929,186398039⟩]
theorem checked66480 : checkPrefixCuts (2^48) 8717598721 10 Manual.Count131072.C066480.packed 64 cuts66480 = true := by
 decide +kernel
def pointBounds66480 : List (Nat × Nat × Nat) := [(8717615104,115180304547764,115180693682373)]
theorem point_links_checked66480 : (cuts66480.take 1).map (fun c => (8717598721-1+2*2^10*c.k,115180281526353+c.lower,115180670660951+c.upper)) = pointBounds66480 := by
 decide +kernel
def cuts66481 : List PrefixCut := [⟨64,186362838,186362944⟩]
theorem checked66481 : checkPrefixCuts (2^48) 8717729793 10 Manual.Count131072.C066481.packed 64 cuts66481 = true := by
 decide +kernel
def cuts66482 : List PrefixCut := [⟨14,41327487,41327511⟩,
⟨64,186424612,186424723⟩]
theorem checked66482 : checkPrefixCuts (2^48) 8717860865 10 Manual.Count131072.C066482.packed 64 cuts66482 = true := by
 decide +kernel
def pointBounds66482 : List (Nat × Nat × Nat) := [(8717889536,115180695614607,115181084749445)]
theorem point_links_checked66482 : (cuts66482.take 1).map (fun c => (8717860865-1+2*2^10*c.k,115180654287120+c.lower,115181043421934+c.upper)) = pointBounds66482 := by
 decide +kernel
def cuts66483 : List PrefixCut := [⟨64,181966281,181966390⟩]
theorem checked66483 : checkPrefixCuts (2^48) 8717991937 10 Manual.Count131072.C066483.packed 64 cuts66483 = true := by
 decide +kernel
def cuts66484 : List PrefixCut := [⟨20,58986716,58986750⟩,
⟨64,187258443,187258552⟩]
theorem checked66484 : checkPrefixCuts (2^48) 8718123009 10 Manual.Count131072.C066484.packed 64 cuts66484 = true := by
 decide +kernel
def pointBounds66484 : List (Nat × Nat × Nat) := [(8718163968,115181081664729,115181470799797)]
theorem point_links_checked66484 : (cuts66484.take 1).map (fun c => (8718123009-1+2*2^10*c.k,115181022678013+c.lower,115181411813047+c.upper)) = pointBounds66484 := by
 decide +kernel
def cuts66485 : List PrefixCut := [⟨64,186222494,186222600⟩]
theorem checked66485 : checkPrefixCuts (2^48) 8718254081 10 Manual.Count131072.C066485.packed 64 cuts66485 = true := by
 decide +kernel
def cuts66486 : List PrefixCut := [⟨26,76096004,76096046⟩,
⟨64,186542545,186542652⟩]
theorem checked66486 : checkPrefixCuts (2^48) 8718385153 10 Manual.Count131072.C066486.packed 64 cuts66486 = true := by
 decide +kernel
def pointBounds66486 : List (Nat × Nat × Nat) := [(8718438400,115181472254954,115181861390245)]
theorem point_links_checked66486 : (cuts66486.take 1).map (fun c => (8718385153-1+2*2^10*c.k,115181396158950+c.lower,115181785294199+c.upper)) = pointBounds66486 := by
 decide +kernel
def cuts66487 : List PrefixCut := [⟨64,184828653,184828755⟩]
theorem checked66487 : checkPrefixCuts (2^48) 8718516225 10 Manual.Count131072.C066487.packed 64 cuts66487 = true := by
 decide +kernel
def cuts66488 : List PrefixCut := [⟨32,90847505,90847558⟩,
⟨64,183308528,183308636⟩]
theorem checked66488 : checkPrefixCuts (2^48) 8718647297 10 Manual.Count131072.C066488.packed 64 cuts66488 = true := by
 decide +kernel
def pointBounds66488 : List (Nat × Nat × Nat) := [(8718712832,115181858377653,115182247513164)]
theorem point_links_checked66488 : (cuts66488.take 1).map (fun c => (8718647297-1+2*2^10*c.k,115181767530148+c.lower,115182156665606+c.upper)) = pointBounds66488 := by
 decide +kernel
def cuts66489 : List PrefixCut := [⟨64,185823906,185824009⟩]
theorem checked66489 : checkPrefixCuts (2^48) 8718778369 10 Manual.Count131072.C066489.packed 64 cuts66489 = true := by
 decide +kernel
def cuts66490 : List PrefixCut := [⟨38,110182305,110182367⟩,
⟨64,185110868,185110978⟩]
theorem checked66490 : checkPrefixCuts (2^48) 8718909441 10 Manual.Count131072.C066490.packed 64 cuts66490 = true := by
 decide +kernel
def pointBounds66490 : List (Nat × Nat × Nat) := [(8718987264,115182246844887,115182635980618)]
theorem point_links_checked66490 : (cuts66490.take 1).map (fun c => (8718909441-1+2*2^10*c.k,115182136662582+c.lower,115182525798251+c.upper)) = pointBounds66490 := by
 decide +kernel
def cuts66491 : List PrefixCut := [⟨64,185334075,185334177⟩]
theorem checked66491 : checkPrefixCuts (2^48) 8719040513 10 Manual.Count131072.C066491.packed 64 cuts66491 = true := by
 decide +kernel
def cuts66492 : List PrefixCut := [⟨44,124867281,124867361⟩,
⟨64,184265956,184266071⟩]
theorem checked66492 : checkPrefixCuts (2^48) 8719171585 10 Manual.Count131072.C066492.packed 64 cuts66492 = true := by
 decide +kernel
def pointBounds66492 : List (Nat × Nat × Nat) := [(8719261696,115182631974806,115183021110767)]
theorem point_links_checked66492 : (cuts66492.take 1).map (fun c => (8719171585-1+2*2^10*c.k,115182507107525+c.lower,115182896243406+c.upper)) = pointBounds66492 := by
 decide +kernel
def cuts66493 : List PrefixCut := [⟨64,185812710,185812816⟩]
theorem checked66493 : checkPrefixCuts (2^48) 8719302657 10 Manual.Count131072.C066493.packed 64 cuts66493 = true := by
 decide +kernel
def cuts66494 : List PrefixCut := [⟨50,146039872,146039956⟩,
⟨64,184486421,184486528⟩]
theorem checked66494 : checkPrefixCuts (2^48) 8719433729 10 Manual.Count131072.C066494.packed 64 cuts66494 = true := by
 decide +kernel
def pointBounds66494 : List (Nat × Nat × Nat) := [(8719536128,115183023226063,115183412362249)]
theorem point_links_checked66494 : (cuts66494.take 1).map (fun c => (8719433729-1+2*2^10*c.k,115182877186191+c.lower,115183266322293+c.upper)) = pointBounds66494 := by
 decide +kernel
def cuts66495 : List PrefixCut := [⟨64,182805050,182805156⟩]
theorem checked66495 : checkPrefixCuts (2^48) 8719564801 10 Manual.Count131072.C066495.packed 64 cuts66495 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000202
