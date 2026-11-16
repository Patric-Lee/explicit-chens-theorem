import PlattAssemblyKernel
import PlattCertificates.Count131072.C056464
import PlattCertificates.Count131072.C056465
import PlattCertificates.Count131072.C056466
import PlattCertificates.Count131072.C056467
import PlattCertificates.Count131072.C056468
import PlattCertificates.Count131072.C056469
import PlattCertificates.Count131072.C056470
import PlattCertificates.Count131072.C056471
import PlattCertificates.Count131072.C056472
import PlattCertificates.Count131072.C056473
import PlattCertificates.Count131072.C056474
import PlattCertificates.Count131072.C056475
import PlattCertificates.Count131072.C056476
import PlattCertificates.Count131072.C056477
import PlattCertificates.Count131072.C056478
import PlattCertificates.Count131072.C056479
import PlattCertificates.Count131072.C056480
import PlattCertificates.Count131072.C056481
import PlattCertificates.Count131072.C056482
import PlattCertificates.Count131072.C056483
import PlattCertificates.Count131072.C056484
import PlattCertificates.Count131072.C056485
import PlattCertificates.Count131072.C056486
import PlattCertificates.Count131072.C056487
import PlattCertificates.Count131072.C056488
import PlattCertificates.Count131072.C056489
import PlattCertificates.Count131072.C056490
import PlattCertificates.Count131072.C056491
import PlattCertificates.Count131072.C056492
import PlattCertificates.Count131072.C056493
import PlattCertificates.Count131072.C056494
import PlattCertificates.Count131072.C056495
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000202
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56464 : List PrefixCut := [⟨64,219292670,219292794⟩]
theorem checked56464 : checkPrefixCuts (2^48) 7404781569 10 Manual.Count131072.C056464.packed 64 cuts56464 = true := by
 decide +kernel
def cuts56465 : List PrefixCut := [⟨33,113046917,113046981⟩,
⟨64,219706914,219707039⟩]
theorem checked56465 : checkPrefixCuts (2^48) 7404912641 10 Manual.Count131072.C056465.packed 64 cuts56465 = true := by
 decide +kernel
def pointBounds56465 : List (Nat × Nat × Nat) := [(7404980224,113166220670506,113166608650085)]
theorem point_links_checked56465 : (cuts56465.take 1).map (fun c => (7404912641-1+2*2^10*c.k,113166107623589+c.lower,113166495603104+c.upper)) = pointBounds56465 := by
 decide +kernel
def cuts56466 : List PrefixCut := [⟨64,221375510,221375633⟩]
theorem checked56466 : checkPrefixCuts (2^48) 7405043713 10 Manual.Count131072.C056466.packed 64 cuts56466 = true := by
 decide +kernel
def cuts56467 : List PrefixCut := [⟨18,61919060,61919095⟩,
⟨64,219167000,219167121⟩]
theorem checked56467 : checkPrefixCuts (2^48) 7405174785 10 Manual.Count131072.C056467.packed 64 cuts56467 = true := by
 decide +kernel
def pointBounds56467 : List (Nat × Nat × Nat) := [(7405211648,113166610625073,113166998604871)]
theorem point_links_checked56467 : (cuts56467.take 1).map (fun c => (7405174785-1+2*2^10*c.k,113166548706013+c.lower,113166936685776+c.upper)) = pointBounds56467 := by
 decide +kernel
def cuts56468 : List PrefixCut := [⟨64,216996552,216996677⟩]
theorem checked56468 : checkPrefixCuts (2^48) 7405305857 10 Manual.Count131072.C056468.packed 64 cuts56468 = true := by
 decide +kernel
def cuts56469 : List PrefixCut := [⟨3,10832624,10832630⟩,
⟨64,221173702,221173827⟩]
theorem checked56469 : checkPrefixCuts (2^48) 7405436929 10 Manual.Count131072.C056469.packed 64 cuts56469 = true := by
 decide +kernel
def pointBounds56469 : List (Nat × Nat × Nat) := [(7405443072,113166995702189,113167383682204)]
theorem point_links_checked56469 : (cuts56469.take 1).map (fun c => (7405436929-1+2*2^10*c.k,113166984869565+c.lower,113167372849574+c.upper)) = pointBounds56469 := by
 decide +kernel
def cuts56470 : List PrefixCut := [⟨52,176396416,176396514⟩,
⟨64,217178935,217179056⟩]
theorem checked56470 : checkPrefixCuts (2^48) 7405568001 10 Manual.Count131072.C056470.packed 64 cuts56470 = true := by
 decide +kernel
def pointBounds56470 : List (Nat × Nat × Nat) := [(7405674496,113167382439683,113167770419915)]
theorem point_links_checked56470 : (cuts56470.take 1).map (fun c => (7405568001-1+2*2^10*c.k,113167206043267+c.lower,113167594023401+c.upper)) = pointBounds56470 := by
 decide +kernel
def cuts56471 : List PrefixCut := [⟨64,218657381,218657505⟩]
theorem checked56471 : checkPrefixCuts (2^48) 7405699073 10 Manual.Count131072.C056471.packed 64 cuts56471 = true := by
 decide +kernel
def cuts56472 : List PrefixCut := [⟨38,130211996,130212068⟩,
⟨64,218767532,218767655⟩]
theorem checked56472 : checkPrefixCuts (2^48) 7405830145 10 Manual.Count131072.C056472.packed 64 cuts56472 = true := by
 decide +kernel
def pointBounds56472 : List (Nat × Nat × Nat) := [(7405907968,113167772091579,113168160072030)]
theorem point_links_checked56472 : (cuts56472.take 1).map (fun c => (7405830145-1+2*2^10*c.k,113167641879583+c.lower,113168029859962+c.upper)) = pointBounds56472 := by
 decide +kernel
def cuts56473 : List PrefixCut := [⟨64,217433457,217433583⟩]
theorem checked56473 : checkPrefixCuts (2^48) 7405961217 10 Manual.Count131072.C056473.packed 64 cuts56473 = true := by
 decide +kernel
def cuts56474 : List PrefixCut := [⟨24,81940355,81940404⟩,
⟨64,218797783,218797910⟩]
theorem checked56474 : checkPrefixCuts (2^48) 7406092289 10 Manual.Count131072.C056474.packed 64 cuts56474 = true := by
 decide +kernel
def pointBounds56474 : List (Nat × Nat × Nat) := [(7406141440,113168160020927,113168548001604)]
theorem point_links_checked56474 : (cuts56474.take 1).map (fun c => (7406092289-1+2*2^10*c.k,113168078080572+c.lower,113168466061200+c.upper)) = pointBounds56474 := by
 decide +kernel
def cuts56475 : List PrefixCut := [⟨64,222290335,222290462⟩]
theorem checked56475 : checkPrefixCuts (2^48) 7406223361 10 Manual.Count131072.C056475.packed 64 cuts56475 = true := by
 decide +kernel
def cuts56476 : List PrefixCut := [⟨10,32987872,32987892⟩,
⟨64,219968161,219968287⟩]
theorem checked56476 : checkPrefixCuts (2^48) 7406354433 10 Manual.Count131072.C056476.packed 64 cuts56476 = true := by
 decide +kernel
def pointBounds56476 : List (Nat × Nat × Nat) := [(7406374912,113168552156562,113168940137464)]
theorem point_links_checked56476 : (cuts56476.take 1).map (fun c => (7406354433-1+2*2^10*c.k,113168519168690+c.lower,113168907149572+c.upper)) = pointBounds56476 := by
 decide +kernel
def cuts56477 : List PrefixCut := [⟨60,204801001,204801119⟩,
⟨64,218710168,218710294⟩]
theorem checked56477 : checkPrefixCuts (2^48) 7406485505 10 Manual.Count131072.C056477.packed 64 cuts56477 = true := by
 decide +kernel
def pointBounds56477 : List (Nat × Nat × Nat) := [(7406608384,113168943937852,113169331918978)]
theorem point_links_checked56477 : (cuts56477.take 1).map (fun c => (7406485505-1+2*2^10*c.k,113168739136851+c.lower,113169127117859+c.upper)) = pointBounds56477 := by
 decide +kernel
def cuts56478 : List PrefixCut := [⟨64,218098252,218098374⟩]
theorem checked56478 : checkPrefixCuts (2^48) 7406616577 10 Manual.Count131072.C056478.packed 64 cuts56478 = true := by
 decide +kernel
def cuts56479 : List PrefixCut := [⟨46,158963427,158963515⟩,
⟨64,219918505,219918629⟩]
theorem checked56479 : checkPrefixCuts (2^48) 7406747649 10 Manual.Count131072.C056479.packed 64 cuts56479 = true := by
 decide +kernel
def pointBounds56479 : List (Nat × Nat × Nat) := [(7406841856,113169334908698,113169722890042)]
theorem point_links_checked56479 : (cuts56479.take 1).map (fun c => (7406747649-1+2*2^10*c.k,113169175945271+c.lower,113169563926527+c.upper)) = pointBounds56479 := by
 decide +kernel
def cuts56480 : List PrefixCut := [⟨64,218356559,218356684⟩]
theorem checked56480 : checkPrefixCuts (2^48) 7406878721 10 Manual.Count131072.C056480.packed 64 cuts56480 = true := by
 decide +kernel
def cuts56481 : List PrefixCut := [⟨32,110810870,110810934⟩,
⟨64,218428705,218428830⟩]
theorem checked56481 : checkPrefixCuts (2^48) 7407009793 10 Manual.Count131072.C056481.packed 64 cuts56481 = true := by
 decide +kernel
def pointBounds56481 : List (Nat × Nat × Nat) := [(7407075328,113169725031205,113170113012774)]
theorem point_links_checked56481 : (cuts56481.take 1).map (fun c => (7407009793-1+2*2^10*c.k,113169614220335+c.lower,113170002201840+c.upper)) = pointBounds56481 := by
 decide +kernel
def cuts56482 : List PrefixCut := [⟨64,219070812,219070936⟩]
theorem checked56482 : checkPrefixCuts (2^48) 7407140865 10 Manual.Count131072.C056482.packed 64 cuts56482 = true := by
 decide +kernel
def cuts56483 : List PrefixCut := [⟨18,61445534,61445567⟩,
⟨64,217774966,217775088⟩]
theorem checked56483 : checkPrefixCuts (2^48) 7407271937 10 Manual.Count131072.C056483.packed 64 cuts56483 = true := by
 decide +kernel
def pointBounds56483 : List (Nat × Nat × Nat) := [(7407308800,113170113165386,113170501147173)]
theorem point_links_checked56483 : (cuts56483.take 1).map (fun c => (7407271937-1+2*2^10*c.k,113170051719852+c.lower,113170439701606+c.upper)) = pointBounds56483 := by
 decide +kernel
def cuts56484 : List PrefixCut := [⟨64,221228998,221229124⟩]
theorem checked56484 : checkPrefixCuts (2^48) 7407403009 10 Manual.Count131072.C056484.packed 64 cuts56484 = true := by
 decide +kernel
def cuts56485 : List PrefixCut := [⟨4,13147461,13147468⟩,
⟨64,219021200,219021322⟩]
theorem checked56485 : checkPrefixCuts (2^48) 7407534081 10 Manual.Count131072.C056485.packed 64 cuts56485 = true := by
 decide +kernel
def pointBounds56485 : List (Nat × Nat × Nat) := [(7407542272,113170503871277,113170891853286)]
theorem point_links_checked56485 : (cuts56485.take 1).map (fun c => (7407534081-1+2*2^10*c.k,113170490723816+c.lower,113170878705818+c.upper)) = pointBounds56485 := by
 decide +kernel
def cuts56486 : List PrefixCut := [⟨54,188619613,188619721⟩,
⟨64,222551084,222551212⟩]
theorem checked56486 : checkPrefixCuts (2^48) 7407665153 10 Manual.Count131072.C056486.packed 64 cuts56486 = true := by
 decide +kernel
def pointBounds56486 : List (Nat × Nat × Nat) := [(7407775744,113170898364629,113171286346861)]
theorem point_links_checked56486 : (cuts56486.take 1).map (fun c => (7407665153-1+2*2^10*c.k,113170709745016+c.lower,113171097727140+c.upper)) = pointBounds56486 := by
 decide +kernel
def cuts56487 : List PrefixCut := [⟨64,219089438,219089561⟩]
theorem checked56487 : checkPrefixCuts (2^48) 7407796225 10 Manual.Count131072.C056487.packed 64 cuts56487 = true := by
 decide +kernel
def cuts56488 : List PrefixCut := [⟨40,136520466,136520545⟩,
⟨64,220529392,220529517⟩]
theorem checked56488 : checkPrefixCuts (2^48) 7407927297 10 Manual.Count131072.C056488.packed 64 cuts56488 = true := by
 decide +kernel
def pointBounds56488 : List (Nat × Nat × Nat) := [(7408009216,113171287906004,113171675888458)]
theorem point_links_checked56488 : (cuts56488.take 1).map (fun c => (7407927297-1+2*2^10*c.k,113171151385538+c.lower,113171539367913+c.upper)) = pointBounds56488 := by
 decide +kernel
def cuts56489 : List PrefixCut := [⟨64,221057443,221057568⟩]
theorem checked56489 : checkPrefixCuts (2^48) 7408058369 10 Manual.Count131072.C056489.packed 64 cuts56489 = true := by
 decide +kernel
def cuts56490 : List PrefixCut := [⟨26,90504002,90504051⟩,
⟨64,220521614,220521735⟩]
theorem checked56490 : checkPrefixCuts (2^48) 7408189441 10 Manual.Count131072.C056490.packed 64 cuts56490 = true := by
 decide +kernel
def pointBounds56490 : List (Nat × Nat × Nat) := [(7408242688,113171683476375,113172071459049)]
theorem point_links_checked56490 : (cuts56490.take 1).map (fun c => (7408189441-1+2*2^10*c.k,113171592972373+c.lower,113171980954998+c.upper)) = pointBounds56490 := by
 decide +kernel
def cuts56491 : List PrefixCut := [⟨64,218997948,218998072⟩]
theorem checked56491 : checkPrefixCuts (2^48) 7408320513 10 Manual.Count131072.C056491.packed 64 cuts56491 = true := by
 decide +kernel
def cuts56492 : List PrefixCut := [⟨12,42628923,42628947⟩,
⟨64,221463639,221463765⟩]
theorem checked56492 : checkPrefixCuts (2^48) 7408451585 10 Manual.Count131072.C056492.packed 64 cuts56492 = true := by
 decide +kernel
def pointBounds56492 : List (Nat × Nat × Nat) := [(7408476160,113172075120858,113172463103752)]
theorem point_links_checked56492 : (cuts56492.take 1).map (fun c => (7408451585-1+2*2^10*c.k,113172032491935+c.lower,113172420474805+c.upper)) = pointBounds56492 := by
 decide +kernel
def cuts56493 : List PrefixCut := [⟨62,211771629,211771747⟩,
⟨64,218534280,218534402⟩]
theorem checked56493 : checkPrefixCuts (2^48) 7408582657 10 Manual.Count131072.C056493.packed 64 cuts56493 = true := by
 decide +kernel
def pointBounds56493 : List (Nat × Nat × Nat) := [(7408709632,113172465727203,113172853710317)]
theorem point_links_checked56493 : (cuts56493.take 1).map (fun c => (7408582657-1+2*2^10*c.k,113172253955574+c.lower,113172641938570+c.upper)) = pointBounds56493 := by
 decide +kernel
def cuts56494 : List PrefixCut := [⟨64,219822135,219822260⟩]
theorem checked56494 : checkPrefixCuts (2^48) 7408713729 10 Manual.Count131072.C056494.packed 64 cuts56494 = true := by
 decide +kernel
def cuts56495 : List PrefixCut := [⟨48,163135452,163135544⟩,
⟨64,217880703,217880825⟩]
theorem checked56495 : checkPrefixCuts (2^48) 7408844801 10 Manual.Count131072.C056495.packed 64 cuts56495 = true := by
 decide +kernel
def pointBounds56495 : List (Nat × Nat × Nat) := [(7408943104,113172855447441,113173243430776)]
theorem point_links_checked56495 : (cuts56495.take 1).map (fun c => (7408844801-1+2*2^10*c.k,113172692311989+c.lower,113173080295232+c.upper)) = pointBounds56495 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000202
