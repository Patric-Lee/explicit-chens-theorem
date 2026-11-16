import PlattAssemblyKernel
import PlattCertificates.Count131072.C070448
import PlattCertificates.Count131072.C070449
import PlattCertificates.Count131072.C070450
import PlattCertificates.Count131072.C070451
import PlattCertificates.Count131072.C070452
import PlattCertificates.Count131072.C070453
import PlattCertificates.Count131072.C070454
import PlattCertificates.Count131072.C070455
import PlattCertificates.Count131072.C070456
import PlattCertificates.Count131072.C070457
import PlattCertificates.Count131072.C070458
import PlattCertificates.Count131072.C070459
import PlattCertificates.Count131072.C070460
import PlattCertificates.Count131072.C070461
import PlattCertificates.Count131072.C070462
import PlattCertificates.Count131072.C070463
import PlattCertificates.Count131072.C070464
import PlattCertificates.Count131072.C070465
import PlattCertificates.Count131072.C070466
import PlattCertificates.Count131072.C070467
import PlattCertificates.Count131072.C070468
import PlattCertificates.Count131072.C070469
import PlattCertificates.Count131072.C070470
import PlattCertificates.Count131072.C070471
import PlattCertificates.Count131072.C070472
import PlattCertificates.Count131072.C070473
import PlattCertificates.Count131072.C070474
import PlattCertificates.Count131072.C070475
import PlattCertificates.Count131072.C070476
import PlattCertificates.Count131072.C070477
import PlattCertificates.Count131072.C070478
import PlattCertificates.Count131072.C070479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70448 : List PrefixCut := [⟨63,174532423,174532522⟩,
⟨64,177609876,177609977⟩]
theorem checked70448 : checkPrefixCuts (2^48) 9237692417 10 Manual.Count131072.C070448.packed 64 cuts70448 = true := by
 decide +kernel
def pointBounds70448 : List (Nat × Nat × Nat) := [(9237821440,115892146656163,115892536207502)]
theorem point_links_checked70448 : (cuts70448.take 1).map (fun c => (9237692417-1+2*2^10*c.k,115891972123740+c.lower,115892361674980+c.upper)) = pointBounds70448 := by
 decide +kernel
def cuts70449 : List PrefixCut := [⟨64,171147807,171147914⟩]
theorem checked70449 : checkPrefixCuts (2^48) 9237823489 10 Manual.Count131072.C070449.packed 64 cuts70449 = true := by
 decide +kernel
def cuts70450 : List PrefixCut := [⟨64,174405583,174405680⟩]
theorem checked70450 : checkPrefixCuts (2^48) 9237954561 10 Manual.Count131072.C070450.packed 64 cuts70450 = true := by
 decide +kernel
def cuts70451 : List PrefixCut := [⟨12,31504866,31504886⟩,
⟨64,171996070,171996177⟩]
theorem checked70451 : checkPrefixCuts (2^48) 9238085633 10 Manual.Count131072.C070451.packed 64 cuts70451 = true := by
 decide +kernel
def pointBounds70451 : List (Nat × Nat × Nat) := [(9238110208,115892526791872,115892916343437)]
theorem point_links_checked70451 : (cuts70451.take 1).map (fun c => (9238085633-1+2*2^10*c.k,115892495287006+c.lower,115892884838551+c.upper)) = pointBounds70451 := by
 decide +kernel
def cuts70452 : List PrefixCut := [⟨64,175497491,175497594⟩]
theorem checked70452 : checkPrefixCuts (2^48) 9238216705 10 Manual.Count131072.C070452.packed 64 cuts70452 = true := by
 decide +kernel
def cuts70453 : List PrefixCut := [⟨25,66907760,66907797⟩,
⟨64,171808393,171808493⟩]
theorem checked70453 : checkPrefixCuts (2^48) 9238347777 10 Manual.Count131072.C070453.packed 64 cuts70453 = true := by
 decide +kernel
def pointBounds70453 : List (Nat × Nat × Nat) := [(9238398976,115892909688327,115893299240119)]
theorem point_links_checked70453 : (cuts70453.take 1).map (fun c => (9238347777-1+2*2^10*c.k,115892842780567+c.lower,115893232332322+c.upper)) = pointBounds70453 := by
 decide +kernel
def cuts70454 : List PrefixCut := [⟨64,176040922,176041025⟩]
theorem checked70454 : checkPrefixCuts (2^48) 9238478849 10 Manual.Count131072.C070454.packed 64 cuts70454 = true := by
 decide +kernel
def cuts70455 : List PrefixCut := [⟨38,104075642,104075700⟩,
⟨64,175337700,175337798⟩]
theorem checked70455 : checkPrefixCuts (2^48) 9238609921 10 Manual.Count131072.C070455.packed 64 cuts70455 = true := by
 decide +kernel
def pointBounds70455 : List (Nat × Nat × Nat) := [(9238687744,115893294705524,115893684257540)]
theorem point_links_checked70455 : (cuts70455.take 1).map (fun c => (9238609921-1+2*2^10*c.k,115893190629882+c.lower,115893580181840+c.upper)) = pointBounds70455 := by
 decide +kernel
def cuts70456 : List PrefixCut := [⟨64,171465944,171466039⟩]
theorem checked70456 : checkPrefixCuts (2^48) 9238740993 10 Manual.Count131072.C070456.packed 64 cuts70456 = true := by
 decide +kernel
def cuts70457 : List PrefixCut := [⟨51,137646274,137646360⟩,
⟨64,173900791,173900899⟩]
theorem checked70457 : checkPrefixCuts (2^48) 9238872065 10 Manual.Count131072.C070457.packed 64 cuts70457 = true := by
 decide +kernel
def pointBounds70457 : List (Nat × Nat × Nat) := [(9238976512,115893675079800,115894064632037)]
theorem point_links_checked70457 : (cuts70457.take 1).map (fun c => (9238872065-1+2*2^10*c.k,115893537433526+c.lower,115893926985677+c.upper)) = pointBounds70457 := by
 decide +kernel
def cuts70458 : List PrefixCut := [⟨64,174324851,174324952⟩]
theorem checked70458 : checkPrefixCuts (2^48) 9239003137 10 Manual.Count131072.C070458.packed 64 cuts70458 = true := by
 decide +kernel
def cuts70459 : List PrefixCut := [⟨64,175236337,175236440⟩]
theorem checked70459 : checkPrefixCuts (2^48) 9239134209 10 Manual.Count131072.C070459.packed 64 cuts70459 = true := by
 decide +kernel
def pointBounds70459 : List (Nat × Nat × Nat) := [(9239265280,115894060895505,115894450447968)]
theorem point_links_checked70459 : (cuts70459.take 1).map (fun c => (9239134209-1+2*2^10*c.k,115893885659168+c.lower,115894275211528+c.upper)) = pointBounds70459 := by
 decide +kernel
def cuts70460 : List PrefixCut := [⟨64,173040394,173040492⟩]
theorem checked70460 : checkPrefixCuts (2^48) 9239265281 10 Manual.Count131072.C070460.packed 64 cuts70460 = true := by
 decide +kernel
def cuts70461 : List PrefixCut := [⟨64,174469754,174469854⟩]
theorem checked70461 : checkPrefixCuts (2^48) 9239396353 10 Manual.Count131072.C070461.packed 64 cuts70461 = true := by
 decide +kernel
def cuts70462 : List PrefixCut := [⟨13,36130503,36130519⟩,
⟨64,174497746,174497845⟩]
theorem checked70462 : checkPrefixCuts (2^48) 9239527425 10 Manual.Count131072.C070462.packed 64 cuts70462 = true := by
 decide +kernel
def pointBounds70462 : List (Nat × Nat × Nat) := [(9239554048,115894444536156,115894834088833)]
theorem point_links_checked70462 : (cuts70462.take 1).map (fun c => (9239527425-1+2*2^10*c.k,115894408405653+c.lower,115894797958314+c.upper)) = pointBounds70462 := by
 decide +kernel
def cuts70463 : List PrefixCut := [⟨64,172789328,172789432⟩]
theorem checked70463 : checkPrefixCuts (2^48) 9239658497 10 Manual.Count131072.C070463.packed 64 cuts70463 = true := by
 decide +kernel
def cuts70464 : List PrefixCut := [⟨26,71192636,71192678⟩,
⟨64,173792158,173792258⟩]
theorem checked70464 : checkPrefixCuts (2^48) 9239789569 10 Manual.Count131072.C070464.packed 64 cuts70464 = true := by
 decide +kernel
def pointBounds70464 : List (Nat × Nat × Nat) := [(9239842816,115894826885363,115895216438269)]
theorem point_links_checked70464 : (cuts70464.take 1).map (fun c => (9239789569-1+2*2^10*c.k,115894755692727+c.lower,115895145245591+c.upper)) = pointBounds70464 := by
 decide +kernel
def cuts70465 : List PrefixCut := [⟨64,175069121,175069225⟩]
theorem checked70465 : checkPrefixCuts (2^48) 9239920641 10 Manual.Count131072.C070465.packed 64 cuts70465 = true := by
 decide +kernel
def cuts70466 : List PrefixCut := [⟨39,104729549,104729612⟩,
⟨64,175066614,175066716⟩]
theorem checked70466 : checkPrefixCuts (2^48) 9240051713 10 Manual.Count131072.C070466.packed 64 cuts70466 = true := by
 decide +kernel
def pointBounds70466 : List (Nat × Nat × Nat) := [(9240131584,115895209283555,115895598836686)]
theorem point_links_checked70466 : (cuts70466.take 1).map (fun c => (9240051713-1+2*2^10*c.k,115895104554006+c.lower,115895494107074+c.upper)) = pointBounds70466 := by
 decide +kernel
def cuts70467 : List PrefixCut := [⟨64,171104101,171104203⟩]
theorem checked70467 : checkPrefixCuts (2^48) 9240182785 10 Manual.Count131072.C070467.packed 64 cuts70467 = true := by
 decide +kernel
def cuts70468 : List PrefixCut := [⟨52,138690931,138691021⟩,
⟨64,172716119,172716227⟩]
theorem checked70468 : checkPrefixCuts (2^48) 9240313857 10 Manual.Count131072.C070468.packed 64 cuts70468 = true := by
 decide +kernel
def pointBounds70468 : List (Nat × Nat × Nat) := [(9240420352,115895589415652,115895978969014)]
theorem point_links_checked70468 : (cuts70468.take 1).map (fun c => (9240313857-1+2*2^10*c.k,115895450724721+c.lower,115895840277993+c.upper)) = pointBounds70468 := by
 decide +kernel
def cuts70469 : List PrefixCut := [⟨64,173140132,173140232⟩]
theorem checked70469 : checkPrefixCuts (2^48) 9240444929 10 Manual.Count131072.C070469.packed 64 cuts70469 = true := by
 decide +kernel
def cuts70470 : List PrefixCut := [⟨64,174660726,174660823⟩]
theorem checked70470 : checkPrefixCuts (2^48) 9240576001 10 Manual.Count131072.C070470.packed 64 cuts70470 = true := by
 decide +kernel
def cuts70471 : List PrefixCut := [⟨1,2558667,2558668⟩,
⟨64,173013380,173013485⟩]
theorem checked70471 : checkPrefixCuts (2^48) 9240707073 10 Manual.Count131072.C070471.packed 64 cuts70471 = true := by
 decide +kernel
def pointBounds70471 : List (Nat × Nat × Nat) := [(9240709120,115895973800365,115896363353943)]
theorem point_links_checked70471 : (cuts70471.take 1).map (fun c => (9240707073-1+2*2^10*c.k,115895971241698+c.lower,115896360795275+c.upper)) = pointBounds70471 := by
 decide +kernel
def cuts70472 : List PrefixCut := [⟨64,173681042,173681145⟩]
theorem checked70472 : checkPrefixCuts (2^48) 9240838145 10 Manual.Count131072.C070472.packed 64 cuts70472 = true := by
 decide +kernel
def cuts70473 : List PrefixCut := [⟨15,40937440,40937464⟩,
⟨64,173769962,173770065⟩]
theorem checked70473 : checkPrefixCuts (2^48) 9240969217 10 Manual.Count131072.C070473.packed 64 cuts70473 = true := by
 decide +kernel
def pointBounds70473 : List (Nat × Nat × Nat) := [(9240999936,115896358873560,115896748427369)]
theorem point_links_checked70473 : (cuts70473.take 1).map (fun c => (9240969217-1+2*2^10*c.k,115896317936120+c.lower,115896707489905+c.upper)) = pointBounds70473 := by
 decide +kernel
def cuts70474 : List PrefixCut := [⟨64,174285286,174285393⟩]
theorem checked70474 : checkPrefixCuts (2^48) 9241100289 10 Manual.Count131072.C070474.packed 64 cuts70474 = true := by
 decide +kernel
def cuts70475 : List PrefixCut := [⟨29,78552460,78552503⟩,
⟨64,173308166,173308260⟩]
theorem checked70475 : checkPrefixCuts (2^48) 9241231361 10 Manual.Count131072.C070475.packed 64 cuts70475 = true := by
 decide +kernel
def pointBounds70475 : List (Nat × Nat × Nat) := [(9241290752,115896744543828,115897134097866)]
theorem point_links_checked70475 : (cuts70475.take 1).map (fun c => (9241231361-1+2*2^10*c.k,115896665991368+c.lower,115897055545363+c.upper)) = pointBounds70475 := by
 decide +kernel
def cuts70476 : List PrefixCut := [⟨64,176838832,176838933⟩]
theorem checked70476 : checkPrefixCuts (2^48) 9241362433 10 Manual.Count131072.C070476.packed 64 cuts70476 = true := by
 decide +kernel
def cuts70477 : List PrefixCut := [⟨43,115830188,115830259⟩,
⟨64,173394614,173394718⟩]
theorem checked70477 : checkPrefixCuts (2^48) 9241493505 10 Manual.Count131072.C070477.packed 64 cuts70477 = true := by
 decide +kernel
def pointBounds70477 : List (Nat × Nat × Nat) := [(9241581568,115897131968554,115897521522815)]
theorem point_links_checked70477 : (cuts70477.take 1).map (fun c => (9241493505-1+2*2^10*c.k,115897016138366+c.lower,115897405692556+c.upper)) = pointBounds70477 := by
 decide +kernel
def cuts70478 : List PrefixCut := [⟨64,176011463,176011570⟩]
theorem checked70478 : checkPrefixCuts (2^48) 9241624577 10 Manual.Count131072.C070478.packed 64 cuts70478 = true := by
 decide +kernel
def cuts70479 : List PrefixCut := [⟨57,155298563,155298653⟩,
⟨64,173846544,173846647⟩]
theorem checked70479 : checkPrefixCuts (2^48) 9241755649 10 Manual.Count131072.C070479.packed 64 cuts70479 = true := by
 decide +kernel
def pointBounds70479 : List (Nat × Nat × Nat) := [(9241872384,115897520843006,115897910397497)]
theorem point_links_checked70479 : (cuts70479.take 1).map (fun c => (9241755649-1+2*2^10*c.k,115897365544443+c.lower,115897755098844+c.upper)) = pointBounds70479 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000014
