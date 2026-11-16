import PlattAssemblyKernel
import PlattCertificates.Count131072.C055440
import PlattCertificates.Count131072.C055441
import PlattCertificates.Count131072.C055442
import PlattCertificates.Count131072.C055443
import PlattCertificates.Count131072.C055444
import PlattCertificates.Count131072.C055445
import PlattCertificates.Count131072.C055446
import PlattCertificates.Count131072.C055447
import PlattCertificates.Count131072.C055448
import PlattCertificates.Count131072.C055449
import PlattCertificates.Count131072.C055450
import PlattCertificates.Count131072.C055451
import PlattCertificates.Count131072.C055452
import PlattCertificates.Count131072.C055453
import PlattCertificates.Count131072.C055454
import PlattCertificates.Count131072.C055455
import PlattCertificates.Count131072.C055456
import PlattCertificates.Count131072.C055457
import PlattCertificates.Count131072.C055458
import PlattCertificates.Count131072.C055459
import PlattCertificates.Count131072.C055460
import PlattCertificates.Count131072.C055461
import PlattCertificates.Count131072.C055462
import PlattCertificates.Count131072.C055463
import PlattCertificates.Count131072.C055464
import PlattCertificates.Count131072.C055465
import PlattCertificates.Count131072.C055466
import PlattCertificates.Count131072.C055467
import PlattCertificates.Count131072.C055468
import PlattCertificates.Count131072.C055469
import PlattCertificates.Count131072.C055470
import PlattCertificates.Count131072.C055471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000170
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55440 : List PrefixCut := [⟨64,221018036,221018159⟩]
theorem checked55440 : checkPrefixCuts (2^48) 7270563841 10 Manual.Count131072.C055440.packed 64 cuts55440 = true := by
 decide +kernel
def cuts55441 : List PrefixCut := [⟨10,34377642,34377662⟩,
⟨64,222369003,222369132⟩]
theorem checked55441 : checkPrefixCuts (2^48) 7270694913 10 Manual.Count131072.C055441.packed 64 cuts55441 = true := by
 decide +kernel
def pointBounds55441 : List (Nat × Nat × Nat) := [(7270715392,112939507527204,112939895378008)]
theorem point_links_checked55441 : (cuts55441.take 1).map (fun c => (7270694913-1+2*2^10*c.k,112939473149562+c.lower,112939861000346+c.upper)) = pointBounds55441 := by
 decide +kernel
def cuts55442 : List PrefixCut := [⟨57,200376462,200376577⟩,
⟨64,225732993,225733122⟩]
theorem checked55442 : checkPrefixCuts (2^48) 7270825985 10 Manual.Count131072.C055442.packed 64 cuts55442 = true := by
 decide +kernel
def pointBounds55442 : List (Nat × Nat × Nat) := [(7270942720,112939895895027,112940283746055)]
theorem point_links_checked55442 : (cuts55442.take 1).map (fun c => (7270825985-1+2*2^10*c.k,112939695518565+c.lower,112940083369478+c.upper)) = pointBounds55442 := by
 decide +kernel
def cuts55443 : List PrefixCut := [⟨64,221973861,221973987⟩]
theorem checked55443 : checkPrefixCuts (2^48) 7270957057 10 Manual.Count131072.C055443.packed 64 cuts55443 = true := by
 decide +kernel
def cuts55444 : List PrefixCut := [⟨40,139554262,139554342⟩,
⟨64,225144183,225144310⟩]
theorem checked55444 : checkPrefixCuts (2^48) 7271088129 10 Manual.Count131072.C055444.packed 64 cuts55444 = true := by
 decide +kernel
def pointBounds55444 : List (Nat × Nat × Nat) := [(7271170048,112940282779681,112940670630929)]
theorem point_links_checked55444 : (cuts55444.take 1).map (fun c => (7271088129-1+2*2^10*c.k,112940143225419+c.lower,112940531076587+c.upper)) = pointBounds55444 := by
 decide +kernel
def cuts55445 : List PrefixCut := [⟨64,222894935,222895063⟩]
theorem checked55445 : checkPrefixCuts (2^48) 7271219201 10 Manual.Count131072.C055445.packed 64 cuts55445 = true := by
 decide +kernel
def cuts55446 : List PrefixCut := [⟨23,79510344,79510390⟩,
⟨64,222736064,222736191⟩]
theorem checked55446 : checkPrefixCuts (2^48) 7271350273 10 Manual.Count131072.C055446.packed 64 cuts55446 = true := by
 decide +kernel
def pointBounds55446 : List (Nat × Nat × Nat) := [(7271397376,112940670774881,112941058626350)]
theorem point_links_checked55446 : (cuts55446.take 1).map (fun c => (7271350273-1+2*2^10*c.k,112940591264537+c.lower,112940979115960+c.upper)) = pointBounds55446 := by
 decide +kernel
def cuts55447 : List PrefixCut := [⟨64,224706221,224706348⟩]
theorem checked55447 : checkPrefixCuts (2^48) 7271481345 10 Manual.Count131072.C055447.packed 64 cuts55447 = true := by
 decide +kernel
def cuts55448 : List PrefixCut := [⟨6,21134951,21134963⟩,
⟨64,219321700,219321825⟩]
theorem checked55448 : checkPrefixCuts (2^48) 7271612417 10 Manual.Count131072.C055448.packed 64 cuts55448 = true := by
 decide +kernel
def pointBounds55448 : List (Nat × Nat × Nat) := [(7271624704,112941059841773,112941447693462)]
theorem point_links_checked55448 : (cuts55448.take 1).map (fun c => (7271612417-1+2*2^10*c.k,112941038706822+c.lower,112941426558499+c.upper)) = pointBounds55448 := by
 decide +kernel
def cuts55449 : List PrefixCut := [⟨53,188506712,188506816⟩,
⟨64,225936765,225936890⟩]
theorem checked55449 : checkPrefixCuts (2^48) 7271743489 10 Manual.Count131072.C055449.packed 64 cuts55449 = true := by
 decide +kernel
def pointBounds55449 : List (Nat × Nat × Nat) := [(7271852032,112941446535234,112941834387140)]
theorem point_links_checked55449 : (cuts55449.take 1).map (fun c => (7271743489-1+2*2^10*c.k,112941258028522+c.lower,112941645880324+c.upper)) = pointBounds55449 := by
 decide +kernel
def cuts55450 : List PrefixCut := [⟨64,220862079,220862206⟩]
theorem checked55450 : checkPrefixCuts (2^48) 7271874561 10 Manual.Count131072.C055450.packed 64 cuts55450 = true := by
 decide +kernel
def cuts55451 : List PrefixCut := [⟨36,125099224,125099296⟩,
⟨64,224844832,224844961⟩]
theorem checked55451 : checkPrefixCuts (2^48) 7272005633 10 Manual.Count131072.C055451.packed 64 cuts55451 = true := by
 decide +kernel
def pointBounds55451 : List (Nat × Nat × Nat) := [(7272079360,112941829926590,112942217778716)]
theorem point_links_checked55451 : (cuts55451.take 1).map (fun c => (7272005633-1+2*2^10*c.k,112941704827366+c.lower,112942092679420+c.upper)) = pointBounds55451 := by
 decide +kernel
def cuts55452 : List PrefixCut := [⟨64,218493068,218493194⟩]
theorem checked55452 : checkPrefixCuts (2^48) 7272136705 10 Manual.Count131072.C055452.packed 64 cuts55452 = true := by
 decide +kernel
def cuts55453 : List PrefixCut := [⟨19,66263200,66263239⟩,
⟨64,225262478,225262607⟩]
theorem checked55453 : checkPrefixCuts (2^48) 7272267777 10 Manual.Count131072.C055453.packed 64 cuts55453 = true := by
 decide +kernel
def pointBounds55453 : List (Nat × Nat × Nat) := [(7272306688,112942214428466,112942602280814)]
theorem point_links_checked55453 : (cuts55453.take 1).map (fun c => (7272267777-1+2*2^10*c.k,112942148165266+c.lower,112942536017575+c.upper)) = pointBounds55453 := by
 decide +kernel
def cuts55454 : List PrefixCut := [⟨64,220381683,220381810⟩]
theorem checked55454 : checkPrefixCuts (2^48) 7272398849 10 Manual.Count131072.C055454.packed 64 cuts55454 = true := by
 decide +kernel
def cuts55455 : List PrefixCut := [⟨2,7508544,7508549⟩,
⟨64,227537872,227538000⟩]
theorem checked55455 : checkPrefixCuts (2^48) 7272529921 10 Manual.Count131072.C055455.packed 64 cuts55455 = true := by
 decide +kernel
def pointBounds55455 : List (Nat × Nat × Nat) := [(7272534016,112942601317971,112942989170541)]
theorem point_links_checked55455 : (cuts55455.take 1).map (fun c => (7272529921-1+2*2^10*c.k,112942593809427+c.lower,112942981661992+c.upper)) = pointBounds55455 := by
 decide +kernel
def cuts55456 : List PrefixCut := [⟨49,172111720,172111818⟩,
⟨64,224050522,224050650⟩]
theorem checked55456 : checkPrefixCuts (2^48) 7272660993 10 Manual.Count131072.C055456.packed 64 cuts55456 = true := by
 decide +kernel
def pointBounds55456 : List (Nat × Nat × Nat) := [(7272761344,112942993459019,112943381311810)]
theorem point_links_checked55456 : (cuts55456.take 1).map (fun c => (7272660993-1+2*2^10*c.k,112942821347299+c.lower,112943209199992+c.upper)) = pointBounds55456 := by
 decide +kernel
def cuts55457 : List PrefixCut := [⟨64,223465940,223466064⟩]
theorem checked55457 : checkPrefixCuts (2^48) 7272792065 10 Manual.Count131072.C055457.packed 64 cuts55457 = true := by
 decide +kernel
def cuts55458 : List PrefixCut := [⟨32,111537959,111538022⟩,
⟨64,223578034,223578159⟩]
theorem checked55458 : checkPrefixCuts (2^48) 7272923137 10 Manual.Count131072.C055458.packed 64 cuts55458 = true := by
 decide +kernel
def pointBounds55458 : List (Nat × Nat × Nat) := [(7272988672,112943380401720,112943768254728)]
theorem point_links_checked55458 : (cuts55458.take 1).map (fun c => (7272923137-1+2*2^10*c.k,112943268863761+c.lower,112943656716706+c.upper)) = pointBounds55458 := by
 decide +kernel
def cuts55459 : List PrefixCut := [⟨64,223380479,223380605⟩]
theorem checked55459 : checkPrefixCuts (2^48) 7273054209 10 Manual.Count131072.C055459.packed 64 cuts55459 = true := by
 decide +kernel
def cuts55460 : List PrefixCut := [⟨15,52206676,52206705⟩,
⟨64,225466260,225466388⟩]
theorem checked55460 : checkPrefixCuts (2^48) 7273185281 10 Manual.Count131072.C055460.packed 64 cuts55460 = true := by
 decide +kernel
def pointBounds55460 : List (Nat × Nat × Nat) := [(7273216000,112943768028950,112944155882175)]
theorem point_links_checked55460 : (cuts55460.take 1).map (fun c => (7273185281-1+2*2^10*c.k,112943715822274+c.lower,112944103675470+c.upper)) = pointBounds55460 := by
 decide +kernel
def cuts55461 : List PrefixCut := [⟨62,217180603,217180727⟩,
⟨64,224765602,224765730⟩]
theorem checked55461 : checkPrefixCuts (2^48) 7273316353 10 Manual.Count131072.C055461.packed 64 cuts55461 = true := by
 decide +kernel
def pointBounds55461 : List (Nat × Nat × Nat) := [(7273443328,112944158469137,112944546322585)]
theorem point_links_checked55461 : (cuts55461.take 1).map (fun c => (7273316353-1+2*2^10*c.k,112943941288534+c.lower,112944329141858+c.upper)) = pointBounds55461 := by
 decide +kernel
def cuts55462 : List PrefixCut := [⟨64,222362257,222362385⟩]
theorem checked55462 : checkPrefixCuts (2^48) 7273447425 10 Manual.Count131072.C055462.packed 64 cuts55462 = true := by
 decide +kernel
def cuts55463 : List PrefixCut := [⟨45,154676000,154676090⟩,
⟨64,219378510,219378637⟩]
theorem checked55463 : checkPrefixCuts (2^48) 7273578497 10 Manual.Count131072.C055463.packed 64 cuts55463 = true := by
 decide +kernel
def pointBounds55463 : List (Nat × Nat × Nat) := [(7273670656,112944543092393,112944930946063)]
theorem point_links_checked55463 : (cuts55463.take 1).map (fun c => (7273578497-1+2*2^10*c.k,112944388416393+c.lower,112944776269973+c.upper)) = pointBounds55463 := by
 decide +kernel
def cuts55464 : List PrefixCut := [⟨64,224211707,224211834⟩]
theorem checked55464 : checkPrefixCuts (2^48) 7273709569 10 Manual.Count131072.C055464.packed 64 cuts55464 = true := by
 decide +kernel
def cuts55465 : List PrefixCut := [⟨28,97477038,97477094⟩,
⟨64,222234147,222234276⟩]
theorem checked55465 : checkPrefixCuts (2^48) 7273840641 10 Manual.Count131072.C055465.packed 64 cuts55465 = true := by
 decide +kernel
def pointBounds55465 : List (Nat × Nat × Nat) := [(7273897984,112944929483648,112945317337538)]
theorem point_links_checked55465 : (cuts55465.take 1).map (fun c => (7273840641-1+2*2^10*c.k,112944832006610+c.lower,112945219860444+c.upper)) = pointBounds55465 := by
 decide +kernel
def cuts55466 : List PrefixCut := [⟨64,225016245,225016374⟩]
theorem checked55466 : checkPrefixCuts (2^48) 7273971713 10 Manual.Count131072.C055466.packed 64 cuts55466 = true := by
 decide +kernel
def cuts55467 : List PrefixCut := [⟨11,38579333,38579354⟩,
⟨64,226598685,226598809⟩]
theorem checked55467 : checkPrefixCuts (2^48) 7274102785 10 Manual.Count131072.C055467.packed 64 cuts55467 = true := by
 decide +kernel
def pointBounds55467 : List (Nat × Nat × Nat) := [(7274125312,112945317836335,112945705690448)]
theorem point_links_checked55467 : (cuts55467.take 1).map (fun c => (7274102785-1+2*2^10*c.k,112945279257002+c.lower,112945667111094+c.upper)) = pointBounds55467 := by
 decide +kernel
def cuts55468 : List PrefixCut := [⟨58,206434983,206435097⟩,
⟨64,226710701,226710826⟩]
theorem checked55468 : checkPrefixCuts (2^48) 7274233857 10 Manual.Count131072.C055468.packed 64 cuts55468 = true := by
 decide +kernel
def pointBounds55468 : List (Nat × Nat × Nat) := [(7274352640,112945712290670,112946100145000)]
theorem point_links_checked55468 : (cuts55468.take 1).map (fun c => (7274233857-1+2*2^10*c.k,112945505855687+c.lower,112945893709903+c.upper)) = pointBounds55468 := by
 decide +kernel
def cuts55469 : List PrefixCut := [⟨64,223881957,223882083⟩]
theorem checked55469 : checkPrefixCuts (2^48) 7274364929 10 Manual.Count131072.C055469.packed 64 cuts55469 = true := by
 decide +kernel
def cuts55470 : List PrefixCut := [⟨41,142584302,142584381⟩,
⟨64,222523661,222523786⟩]
theorem checked55470 : checkPrefixCuts (2^48) 7274496001 10 Manual.Count131072.C055470.packed 64 cuts55470 = true := by
 decide +kernel
def pointBounds55470 : List (Nat × Nat × Nat) := [(7274579968,112946099032647,112946486887193)]
theorem point_links_checked55470 : (cuts55470.take 1).map (fun c => (7274496001-1+2*2^10*c.k,112945956448345+c.lower,112946344302812+c.upper)) = pointBounds55470 := by
 decide +kernel
def cuts55471 : List PrefixCut := [⟨64,220546354,220546482⟩]
theorem checked55471 : checkPrefixCuts (2^48) 7274627073 10 Manual.Count131072.C055471.packed 64 cuts55471 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000170
