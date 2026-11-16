import PlattAssemblyKernel
import PlattCertificates.Count131072.C069504
import PlattCertificates.Count131072.C069505
import PlattCertificates.Count131072.C069506
import PlattCertificates.Count131072.C069507
import PlattCertificates.Count131072.C069508
import PlattCertificates.Count131072.C069509
import PlattCertificates.Count131072.C069510
import PlattCertificates.Count131072.C069511
import PlattCertificates.Count131072.C069512
import PlattCertificates.Count131072.C069513
import PlattCertificates.Count131072.C069514
import PlattCertificates.Count131072.C069515
import PlattCertificates.Count131072.C069516
import PlattCertificates.Count131072.C069517
import PlattCertificates.Count131072.C069518
import PlattCertificates.Count131072.C069519
import PlattCertificates.Count131072.C069520
import PlattCertificates.Count131072.C069521
import PlattCertificates.Count131072.C069522
import PlattCertificates.Count131072.C069523
import PlattCertificates.Count131072.C069524
import PlattCertificates.Count131072.C069525
import PlattCertificates.Count131072.C069526
import PlattCertificates.Count131072.C069527
import PlattCertificates.Count131072.C069528
import PlattCertificates.Count131072.C069529
import PlattCertificates.Count131072.C069530
import PlattCertificates.Count131072.C069531
import PlattCertificates.Count131072.C069532
import PlattCertificates.Count131072.C069533
import PlattCertificates.Count131072.C069534
import PlattCertificates.Count131072.C069535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000297
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69504 : List PrefixCut := [⟨62,171867858,171867953⟩,
⟨64,177148935,177149033⟩]
theorem checked69504 : checkPrefixCuts (2^48) 9113960449 10 Manual.Count131072.C069504.packed 64 cuts69504 = true := by
 decide +kernel
def pointBounds69504 : List (Nat × Nat × Nat) := [(9114087424,115726705138305,115727094592346)]
theorem point_links_checked69504 : (cuts69504.take 1).map (fun c => (9113960449-1+2*2^10*c.k,115726533270447+c.lower,115726922724393+c.upper)) = pointBounds69504 := by
 decide +kernel
def cuts69505 : List PrefixCut := [⟨64,179709698,179709804⟩]
theorem checked69505 : checkPrefixCuts (2^48) 9114091521 10 Manual.Count131072.C069505.packed 64 cuts69505 = true := by
 decide +kernel
def cuts69506 : List PrefixCut := [⟨64,174333505,174333610⟩]
theorem checked69506 : checkPrefixCuts (2^48) 9114222593 10 Manual.Count131072.C069506.packed 64 cuts69506 = true := by
 decide +kernel
def cuts69507 : List PrefixCut := [⟨10,27207534,27207553⟩,
⟨64,175010393,175010503⟩]
theorem checked69507 : checkPrefixCuts (2^48) 9114353665 10 Manual.Count131072.C069507.packed 64 cuts69507 = true := by
 decide +kernel
def pointBounds69507 : List (Nat × Nat × Nat) := [(9114374144,115727091670119,115727481124393)]
theorem point_links_checked69507 : (cuts69507.take 1).map (fun c => (9114353665-1+2*2^10*c.k,115727064462585+c.lower,115727453916840+c.upper)) = pointBounds69507 := by
 decide +kernel
def cuts69508 : List PrefixCut := [⟨64,177787275,177787373⟩]
theorem checked69508 : checkPrefixCuts (2^48) 9114484737 10 Manual.Count131072.C069508.packed 64 cuts69508 = true := by
 decide +kernel
def cuts69509 : List PrefixCut := [⟨22,60775045,60775085⟩,
⟨64,175499476,175499586⟩]
theorem checked69509 : checkPrefixCuts (2^48) 9114615809 10 Manual.Count131072.C069509.packed 64 cuts69509 = true := by
 decide +kernel
def pointBounds69509 : List (Nat × Nat × Nat) := [(9114660864,115727478035298,115727867489801)]
theorem point_links_checked69509 : (cuts69509.take 1).map (fun c => (9114615809-1+2*2^10*c.k,115727417260253+c.lower,115727806714716+c.upper)) = pointBounds69509 := by
 decide +kernel
def cuts69510 : List PrefixCut := [⟨64,176763068,176763175⟩]
theorem checked69510 : checkPrefixCuts (2^48) 9114746881 10 Manual.Count131072.C069510.packed 64 cuts69510 = true := by
 decide +kernel
def cuts69511 : List PrefixCut := [⟨34,92703866,92703917⟩,
⟨64,177779586,177779681⟩]
theorem checked69511 : checkPrefixCuts (2^48) 9114877953 10 Manual.Count131072.C069511.packed 64 cuts69511 = true := by
 decide +kernel
def pointBounds69511 : List (Nat × Nat × Nat) := [(9114947584,115727862226663,115728251681394)]
theorem point_links_checked69511 : (cuts69511.take 1).map (fun c => (9114877953-1+2*2^10*c.k,115727769522797+c.lower,115728158977477+c.upper)) = pointBounds69511 := by
 decide +kernel
def cuts69512 : List PrefixCut := [⟨64,176572687,176572795⟩]
theorem checked69512 : checkPrefixCuts (2^48) 9115009025 10 Manual.Count131072.C069512.packed 64 cuts69512 = true := by
 decide +kernel
def cuts69513 : List PrefixCut := [⟨46,127502573,127502641⟩,
⟨64,177033370,177033466⟩]
theorem checked69513 : checkPrefixCuts (2^48) 9115140097 10 Manual.Count131072.C069513.packed 64 cuts69513 = true := by
 decide +kernel
def pointBounds69513 : List (Nat × Nat × Nat) := [(9115234304,115728251377643,115728640832594)]
theorem point_links_checked69513 : (cuts69513.take 1).map (fun c => (9115140097-1+2*2^10*c.k,115728123875070+c.lower,115728513329953+c.upper)) = pointBounds69513 := by
 decide +kernel
def cuts69514 : List PrefixCut := [⟨64,176907300,176907404⟩]
theorem checked69514 : checkPrefixCuts (2^48) 9115271169 10 Manual.Count131072.C069514.packed 64 cuts69514 = true := by
 decide +kernel
def cuts69515 : List PrefixCut := [⟨58,159828872,159828968⟩,
⟨64,176379812,176379917⟩]
theorem checked69515 : checkPrefixCuts (2^48) 9115402241 10 Manual.Count131072.C069515.packed 64 cuts69515 = true := by
 decide +kernel
def pointBounds69515 : List (Nat × Nat × Nat) := [(9115521024,115728637644612,115729027099791)]
theorem point_links_checked69515 : (cuts69515.take 1).map (fun c => (9115402241-1+2*2^10*c.k,115728477815740+c.lower,115728867270823+c.upper)) = pointBounds69515 := by
 decide +kernel
def cuts69516 : List PrefixCut := [⟨64,179557762,179557865⟩]
theorem checked69516 : checkPrefixCuts (2^48) 9115533313 10 Manual.Count131072.C069516.packed 64 cuts69516 = true := by
 decide +kernel
def cuts69517 : List PrefixCut := [⟨64,176405634,176405730⟩]
theorem checked69517 : checkPrefixCuts (2^48) 9115664385 10 Manual.Count131072.C069517.packed 64 cuts69517 = true := by
 decide +kernel
def cuts69518 : List PrefixCut := [⟨6,17538528,17538537⟩,
⟨64,179676120,179676219⟩]
theorem checked69518 : checkPrefixCuts (2^48) 9115795457 10 Manual.Count131072.C069518.packed 64 cuts69518 = true := by
 decide +kernel
def pointBounds69518 : List (Nat × Nat × Nat) := [(9115807744,115729027697476,115729417152872)]
theorem point_links_checked69518 : (cuts69518.take 1).map (fun c => (9115795457-1+2*2^10*c.k,115729010158948+c.lower,115729399614335+c.upper)) = pointBounds69518 := by
 decide +kernel
def cuts69519 : List PrefixCut := [⟨64,176307910,176308023⟩]
theorem checked69519 : checkPrefixCuts (2^48) 9115926529 10 Manual.Count131072.C069519.packed 64 cuts69519 = true := by
 decide +kernel
def cuts69520 : List PrefixCut := [⟨18,51193665,51193697⟩,
⟨64,179331296,179331402⟩]
theorem checked69520 : checkPrefixCuts (2^48) 9116057601 10 Manual.Count131072.C069520.packed 64 cuts69520 = true := by
 decide +kernel
def pointBounds69520 : List (Nat × Nat × Nat) := [(9116094464,115729417336643,115729806792274)]
theorem point_links_checked69520 : (cuts69520.take 1).map (fun c => (9116057601-1+2*2^10*c.k,115729366142978+c.lower,115729755598577+c.upper)) = pointBounds69520 := by
 decide +kernel
def cuts69521 : List PrefixCut := [⟨64,176179355,176179454⟩]
theorem checked69521 : checkPrefixCuts (2^48) 9116188673 10 Manual.Count131072.C069521.packed 64 cuts69521 = true := by
 decide +kernel
def cuts69522 : List PrefixCut := [⟨30,82098834,82098887⟩,
⟨64,176578196,176578307⟩]
theorem checked69522 : checkPrefixCuts (2^48) 9116319745 10 Manual.Count131072.C069522.packed 64 cuts69522 = true := by
 decide +kernel
def pointBounds69522 : List (Nat × Nat × Nat) := [(9116381184,115729803752463,115730193208320)]
theorem point_links_checked69522 : (cuts69522.take 1).map (fun c => (9116319745-1+2*2^10*c.k,115729721653629+c.lower,115730111109433+c.upper)) = pointBounds69522 := by
 decide +kernel
def cuts69523 : List PrefixCut := [⟨64,178891312,178891415⟩]
theorem checked69523 : checkPrefixCuts (2^48) 9116450817 10 Manual.Count131072.C069523.packed 64 cuts69523 = true := by
 decide +kernel
def cuts69524 : List PrefixCut := [⟨42,115595634,115595701⟩,
⟨64,176542252,176542355⟩]
theorem checked69524 : checkPrefixCuts (2^48) 9116581889 10 Manual.Count131072.C069524.packed 64 cuts69524 = true := by
 decide +kernel
def pointBounds69524 : List (Nat × Nat × Nat) := [(9116667904,115730192718771,115730582174856)]
theorem point_links_checked69524 : (cuts69524.take 1).map (fun c => (9116581889-1+2*2^10*c.k,115730077123137+c.lower,115730466579155+c.upper)) = pointBounds69524 := by
 decide +kernel
def cuts69525 : List PrefixCut := [⟨64,175675223,175675329⟩]
theorem checked69525 : checkPrefixCuts (2^48) 9116712961 10 Manual.Count131072.C069525.packed 64 cuts69525 = true := by
 decide +kernel
def cuts69526 : List PrefixCut := [⟨54,149862272,149862358⟩,
⟨64,177062046,177062147⟩]
theorem checked69526 : checkPrefixCuts (2^48) 9116844033 10 Manual.Count131072.C069526.packed 64 cuts69526 = true := by
 decide +kernel
def pointBounds69526 : List (Nat × Nat × Nat) := [(9116954624,115730579202884,115730968659197)]
theorem point_links_checked69526 : (cuts69526.take 1).map (fun c => (9116844033-1+2*2^10*c.k,115730429340612+c.lower,115730818796839+c.upper)) = pointBounds69526 := by
 decide +kernel
def cuts69527 : List PrefixCut := [⟨64,176071531,176071643⟩]
theorem checked69527 : checkPrefixCuts (2^48) 9116975105 10 Manual.Count131072.C069527.packed 64 cuts69527 = true := by
 decide +kernel
def cuts69528 : List PrefixCut := [⟨64,173259551,173259657⟩]
theorem checked69528 : checkPrefixCuts (2^48) 9117106177 10 Manual.Count131072.C069528.packed 64 cuts69528 = true := by
 decide +kernel
def cuts69529 : List PrefixCut := [⟨2,6514166,6514168⟩,
⟨64,178443667,178443771⟩]
theorem checked69529 : checkPrefixCuts (2^48) 9117237249 10 Manual.Count131072.C069529.packed 64 cuts69529 = true := by
 decide +kernel
def pointBounds69529 : List (Nat × Nat × Nat) := [(9117241344,115730962247906,115731351704454)]
theorem point_links_checked69529 : (cuts69529.take 1).map (fun c => (9117237249-1+2*2^10*c.k,115730955733740+c.lower,115731345190286+c.upper)) = pointBounds69529 := by
 decide +kernel
def cuts69530 : List PrefixCut := [⟨64,177020969,177021074⟩]
theorem checked69530 : checkPrefixCuts (2^48) 9117368321 10 Manual.Count131072.C069530.packed 64 cuts69530 = true := by
 decide +kernel
def cuts69531 : List PrefixCut := [⟨14,38836839,38836863⟩,
⟨64,175907054,175907160⟩]
theorem checked69531 : checkPrefixCuts (2^48) 9117499393 10 Manual.Count131072.C069531.packed 64 cuts69531 = true := by
 decide +kernel
def pointBounds69531 : List (Nat × Nat × Nat) := [(9117528064,115731350035215,115731739491994)]
theorem point_links_checked69531 : (cuts69531.take 1).map (fun c => (9117499393-1+2*2^10*c.k,115731311198376+c.lower,115731700655131+c.upper)) = pointBounds69531 := by
 decide +kernel
def cuts69532 : List PrefixCut := [⟨64,172910014,172910123⟩]
theorem checked69532 : checkPrefixCuts (2^48) 9117630465 10 Manual.Count131072.C069532.packed 64 cuts69532 = true := by
 decide +kernel
def cuts69533 : List PrefixCut := [⟨26,70725374,70725415⟩,
⟨64,174389317,174389418⟩]
theorem checked69533 : checkPrefixCuts (2^48) 9117761537 10 Manual.Count131072.C069533.packed 64 cuts69533 = true := by
 decide +kernel
def pointBounds69533 : List (Nat × Nat × Nat) := [(9117814784,115731730740818,115732120197829)]
theorem point_links_checked69533 : (cuts69533.take 1).map (fun c => (9117761537-1+2*2^10*c.k,115731660015444+c.lower,115732049472414+c.upper)) = pointBounds69533 := by
 decide +kernel
def cuts69534 : List PrefixCut := [⟨64,178739540,178739644⟩]
theorem checked69534 : checkPrefixCuts (2^48) 9117892609 10 Manual.Count131072.C069534.packed 64 cuts69534 = true := by
 decide +kernel
def cuts69535 : List PrefixCut := [⟨38,105637251,105637317⟩,
⟨64,177131735,177131842⟩]
theorem checked69535 : checkPrefixCuts (2^48) 9118023681 10 Manual.Count131072.C069535.packed 64 cuts69535 = true := by
 decide +kernel
def pointBounds69535 : List (Nat × Nat × Nat) := [(9118101504,115732118781552,115732508238793)]
theorem point_links_checked69535 : (cuts69535.take 1).map (fun c => (9118023681-1+2*2^10*c.k,115732013144301+c.lower,115732402601476+c.upper)) = pointBounds69535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000297
