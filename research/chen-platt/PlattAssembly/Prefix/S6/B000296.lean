import PlattAssemblyKernel
import PlattCertificates.Count131072.C059472
import PlattCertificates.Count131072.C059473
import PlattCertificates.Count131072.C059474
import PlattCertificates.Count131072.C059475
import PlattCertificates.Count131072.C059476
import PlattCertificates.Count131072.C059477
import PlattCertificates.Count131072.C059478
import PlattCertificates.Count131072.C059479
import PlattCertificates.Count131072.C059480
import PlattCertificates.Count131072.C059481
import PlattCertificates.Count131072.C059482
import PlattCertificates.Count131072.C059483
import PlattCertificates.Count131072.C059484
import PlattCertificates.Count131072.C059485
import PlattCertificates.Count131072.C059486
import PlattCertificates.Count131072.C059487
import PlattCertificates.Count131072.C059488
import PlattCertificates.Count131072.C059489
import PlattCertificates.Count131072.C059490
import PlattCertificates.Count131072.C059491
import PlattCertificates.Count131072.C059492
import PlattCertificates.Count131072.C059493
import PlattCertificates.Count131072.C059494
import PlattCertificates.Count131072.C059495
import PlattCertificates.Count131072.C059496
import PlattCertificates.Count131072.C059497
import PlattCertificates.Count131072.C059498
import PlattCertificates.Count131072.C059499
import PlattCertificates.Count131072.C059500
import PlattCertificates.Count131072.C059501
import PlattCertificates.Count131072.C059502
import PlattCertificates.Count131072.C059503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000296
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59472 : List PrefixCut := [⟨64,207809877,207809994⟩]
theorem checked59472 : checkPrefixCuts (2^48) 7799046145 10 Manual.Count131072.C059472.packed 64 cuts59472 = true := by
 decide +kernel
def cuts59473 : List PrefixCut := [⟨47,149665677,149665762⟩,
⟨64,204125192,204125309⟩]
theorem checked59473 : checkPrefixCuts (2^48) 7799177217 10 Manual.Count131072.C059473.packed 64 cuts59473 = true := by
 decide +kernel
def pointBounds59473 : List (Nat × Nat × Nat) := [(7799273472,113807975581121,113808363926254)]
theorem point_links_checked59473 : (cuts59473.take 1).map (fun c => (7799177217-1+2*2^10*c.k,113807825915444+c.lower,113808214260492+c.upper)) = pointBounds59473 := by
 decide +kernel
def cuts59474 : List PrefixCut := [⟨64,207875091,207875209⟩]
theorem checked59474 : checkPrefixCuts (2^48) 7799308289 10 Manual.Count131072.C059474.packed 64 cuts59474 = true := by
 decide +kernel
def cuts59475 : List PrefixCut := [⟨39,124903806,124903878⟩,
⟨64,207258062,207258179⟩]
theorem checked59475 : checkPrefixCuts (2^48) 7799439361 10 Manual.Count131072.C059475.packed 64 cuts59475 = true := by
 decide +kernel
def pointBounds59475 : List (Nat × Nat × Nat) := [(7799519232,113808362819533,113808751164888)]
theorem point_links_checked59475 : (cuts59475.take 1).map (fun c => (7799439361-1+2*2^10*c.k,113808237915727+c.lower,113808626261010+c.upper)) = pointBounds59475 := by
 decide +kernel
def cuts59476 : List PrefixCut := [⟨64,208409411,208409527⟩]
theorem checked59476 : checkPrefixCuts (2^48) 7799570433 10 Manual.Count131072.C059476.packed 64 cuts59476 = true := by
 decide +kernel
def cuts59477 : List PrefixCut := [⟨31,102922284,102922340⟩,
⟨64,207467639,207467756⟩]
theorem checked59477 : checkPrefixCuts (2^48) 7799701505 10 Manual.Count131072.C059477.packed 64 cuts59477 = true := by
 decide +kernel
def pointBounds59477 : List (Nat × Nat × Nat) := [(7799764992,113808756505484,113809144851056)]
theorem point_links_checked59477 : (cuts59477.take 1).map (fun c => (7799701505-1+2*2^10*c.k,113808653583200+c.lower,113809041928716+c.upper)) = pointBounds59477 := by
 decide +kernel
def cuts59478 : List PrefixCut := [⟨64,206525875,206525998⟩]
theorem checked59478 : checkPrefixCuts (2^48) 7799832577 10 Manual.Count131072.C059478.packed 64 cuts59478 = true := by
 decide +kernel
def cuts59479 : List PrefixCut := [⟨23,73869236,73869275⟩,
⟨64,206630659,206630777⟩]
theorem checked59479 : checkPrefixCuts (2^48) 7799963649 10 Manual.Count131072.C059479.packed 64 cuts59479 = true := by
 decide +kernel
def pointBounds59479 : List (Nat × Nat × Nat) := [(7800010752,113809141445950,113809529791745)]
theorem point_links_checked59479 : (cuts59479.take 1).map (fun c => (7799963649-1+2*2^10*c.k,113809067576714+c.lower,113809455922470+c.upper)) = pointBounds59479 := by
 decide +kernel
def cuts59480 : List PrefixCut := [⟨64,207276745,207276866⟩]
theorem checked59480 : checkPrefixCuts (2^48) 7800094721 10 Manual.Count131072.C059480.packed 64 cuts59480 = true := by
 decide +kernel
def cuts59481 : List PrefixCut := [⟨15,49437011,49437040⟩,
⟨64,208355824,208355946⟩]
theorem checked59481 : checkPrefixCuts (2^48) 7800225793 10 Manual.Count131072.C059481.packed 64 cuts59481 = true := by
 decide +kernel
def pointBounds59481 : List (Nat × Nat × Nat) := [(7800256512,113809530921129,113809919267153)]
theorem point_links_checked59481 : (cuts59481.take 1).map (fun c => (7800225793-1+2*2^10*c.k,113809481484118+c.lower,113809869830113+c.upper)) = pointBounds59481 := by
 decide +kernel
def cuts59482 : List PrefixCut := [⟨64,208604911,208605032⟩]
theorem checked59482 : checkPrefixCuts (2^48) 7800356865 10 Manual.Count131072.C059482.packed 64 cuts59482 = true := by
 decide +kernel
def cuts59483 : List PrefixCut := [⟨7,22877405,22877417⟩,
⟨64,211019036,211019154⟩]
theorem checked59483 : checkPrefixCuts (2^48) 7800487937 10 Manual.Count131072.C059483.packed 64 cuts59483 = true := by
 decide +kernel
def pointBounds59483 : List (Nat × Nat × Nat) := [(7800502272,113809921322258,113810309668508)]
theorem point_links_checked59483 : (cuts59483.take 1).map (fun c => (7800487937-1+2*2^10*c.k,113809898444853+c.lower,113810286791091+c.upper)) = pointBounds59483 := by
 decide +kernel
def cuts59484 : List PrefixCut := [⟨63,202752423,202752534⟩,
⟨64,205711234,205711347⟩]
theorem checked59484 : checkPrefixCuts (2^48) 7800619009 10 Manual.Count131072.C059484.packed 64 cuts59484 = true := by
 decide +kernel
def pointBounds59484 : List (Nat × Nat × Nat) := [(7800748032,113810312216312,113810700562779)]
theorem point_links_checked59484 : (cuts59484.take 1).map (fun c => (7800619009-1+2*2^10*c.k,113810109463889+c.lower,113810497810245+c.upper)) = pointBounds59484 := by
 decide +kernel
def cuts59485 : List PrefixCut := [⟨64,205888176,205888296⟩]
theorem checked59485 : checkPrefixCuts (2^48) 7800750081 10 Manual.Count131072.C059485.packed 64 cuts59485 = true := by
 decide +kernel
def cuts59486 : List PrefixCut := [⟨55,177235707,177235807⟩,
⟨64,206137298,206137416⟩]
theorem checked59486 : checkPrefixCuts (2^48) 7800881153 10 Manual.Count131072.C059486.packed 64 cuts59486 = true := by
 decide +kernel
def pointBounds59486 : List (Nat × Nat × Nat) := [(7800993792,113810698299006,113811086645695)]
theorem point_links_checked59486 : (cuts59486.take 1).map (fun c => (7800881153-1+2*2^10*c.k,113810521063299+c.lower,113810909409888+c.upper)) = pointBounds59486 := by
 decide +kernel
def cuts59487 : List PrefixCut := [⟨64,207757504,207757622⟩]
theorem checked59487 : checkPrefixCuts (2^48) 7801012225 10 Manual.Count131072.C059487.packed 64 cuts59487 = true := by
 decide +kernel
def cuts59488 : List PrefixCut := [⟨47,152839179,152839269⟩,
⟨64,207645778,207645900⟩]
theorem checked59488 : checkPrefixCuts (2^48) 7801143297 10 Manual.Count131072.C059488.packed 64 cuts59488 = true := by
 decide +kernel
def pointBounds59488 : List (Nat × Nat × Nat) := [(7801239552,113811087797280,113811476144195)]
theorem point_links_checked59488 : (cuts59488.take 1).map (fun c => (7801143297-1+2*2^10*c.k,113810934958101+c.lower,113811323304926+c.upper)) = pointBounds59488 := by
 decide +kernel
def cuts59489 : List PrefixCut := [⟨64,208796844,208796961⟩]
theorem checked59489 : checkPrefixCuts (2^48) 7801274369 10 Manual.Count131072.C059489.packed 64 cuts59489 = true := by
 decide +kernel
def cuts59490 : List PrefixCut := [⟨39,127614389,127614462⟩,
⟨64,209334540,209334658⟩]
theorem checked59490 : checkPrefixCuts (2^48) 7801405441 10 Manual.Count131072.C059490.packed 64 cuts59490 = true := by
 decide +kernel
def pointBounds59490 : List (Nat × Nat × Nat) := [(7801485312,113811479015112,113811867362249)]
theorem point_links_checked59490 : (cuts59490.take 1).map (fun c => (7801405441-1+2*2^10*c.k,113811351400723+c.lower,113811739747787+c.upper)) = pointBounds59490 := by
 decide +kernel
def cuts59491 : List PrefixCut := [⟨64,207021963,207022080⟩]
theorem checked59491 : checkPrefixCuts (2^48) 7801536513 10 Manual.Count131072.C059491.packed 64 cuts59491 = true := by
 decide +kernel
def cuts59492 : List PrefixCut := [⟨31,99035941,99036002⟩,
⟨64,207234949,207235075⟩]
theorem checked59492 : checkPrefixCuts (2^48) 7801667585 10 Manual.Count131072.C059492.packed 64 cuts59492 = true := by
 decide +kernel
def pointBounds59492 : List (Nat × Nat × Nat) := [(7801731072,113811866793167,113812255140527)]
theorem point_links_checked59492 : (cuts59492.take 1).map (fun c => (7801667585-1+2*2^10*c.k,113811767757226+c.lower,113812156104525+c.upper)) = pointBounds59492 := by
 decide +kernel
def cuts59493 : List PrefixCut := [⟨64,210983573,210983693⟩]
theorem checked59493 : checkPrefixCuts (2^48) 7801798657 10 Manual.Count131072.C059493.packed 64 cuts59493 = true := by
 decide +kernel
def cuts59494 : List PrefixCut := [⟨23,72876530,72876572⟩,
⟨64,204089263,204089384⟩]
theorem checked59494 : checkPrefixCuts (2^48) 7801929729 10 Manual.Count131072.C059494.packed 64 cuts59494 = true := by
 decide +kernel
def pointBounds59494 : List (Nat × Nat × Nat) := [(7801976832,113812258852278,113812647199865)]
theorem point_links_checked59494 : (cuts59494.take 1).map (fun c => (7801929729-1+2*2^10*c.k,113812185975748+c.lower,113812574323293+c.upper)) = pointBounds59494 := by
 decide +kernel
def cuts59495 : List PrefixCut := [⟨64,208234666,208234784⟩]
theorem checked59495 : checkPrefixCuts (2^48) 7802060801 10 Manual.Count131072.C059495.packed 64 cuts59495 = true := by
 decide +kernel
def cuts59496 : List PrefixCut := [⟨15,49893546,49893573⟩,
⟨64,208483696,208483813⟩]
theorem checked59496 : checkPrefixCuts (2^48) 7802191873 10 Manual.Count131072.C059496.packed 64 cuts59496 = true := by
 decide +kernel
def pointBounds59496 : List (Nat × Nat × Nat) := [(7802222592,113812648193223,113813036541034)]
theorem point_links_checked59496 : (cuts59496.take 1).map (fun c => (7802191873-1+2*2^10*c.k,113812598299677+c.lower,113812986647461+c.upper)) = pointBounds59496 := by
 decide +kernel
def cuts59497 : List PrefixCut := [⟨64,208299827,208299941⟩]
theorem checked59497 : checkPrefixCuts (2^48) 7802322945 10 Manual.Count131072.C059497.packed 64 cuts59497 = true := by
 decide +kernel
def cuts59498 : List PrefixCut := [⟨7,22799490,22799503⟩,
⟨64,207141912,207142029⟩]
theorem checked59498 : checkPrefixCuts (2^48) 7802454017 10 Manual.Count131072.C059498.packed 64 cuts59498 = true := by
 decide +kernel
def pointBounds59498 : List (Nat × Nat × Nat) := [(7802468352,113813037882690,113813426230718)]
theorem point_links_checked59498 : (cuts59498.take 1).map (fun c => (7802454017-1+2*2^10*c.k,113813015083200+c.lower,113813403431215+c.upper)) = pointBounds59498 := by
 decide +kernel
def cuts59499 : List PrefixCut := [⟨63,205803714,205803834⟩,
⟨64,209411111,209411233⟩]
theorem checked59499 : checkPrefixCuts (2^48) 7802585089 10 Manual.Count131072.C059499.packed 64 cuts59499 = true := by
 decide +kernel
def pointBounds59499 : List (Nat × Nat × Nat) := [(7802714112,113813428028826,113813816377078)]
theorem point_links_checked59499 : (cuts59499.take 1).map (fun c => (7802585089-1+2*2^10*c.k,113813222225112+c.lower,113813610573244+c.upper)) = pointBounds59499 := by
 decide +kernel
def cuts59500 : List PrefixCut := [⟨64,203780098,203780215⟩]
theorem checked59500 : checkPrefixCuts (2^48) 7802716161 10 Manual.Count131072.C059500.packed 64 cuts59500 = true := by
 decide +kernel
def cuts59501 : List PrefixCut := [⟨55,180545844,180545946⟩,
⟨64,209331934,209332054⟩]
theorem checked59501 : checkPrefixCuts (2^48) 7802847233 10 Manual.Count131072.C059501.packed 64 cuts59501 = true := by
 decide +kernel
def pointBounds59501 : List (Nat × Nat × Nat) := [(7802959872,113813815962165,113814204310638)]
theorem point_links_checked59501 : (cuts59501.take 1).map (fun c => (7802847233-1+2*2^10*c.k,113813635416321+c.lower,113814023764692+c.upper)) = pointBounds59501 := by
 decide +kernel
def cuts59502 : List PrefixCut := [⟨64,206875495,206875614⟩]
theorem checked59502 : checkPrefixCuts (2^48) 7802978305 10 Manual.Count131072.C059502.packed 64 cuts59502 = true := by
 decide +kernel
def cuts59503 : List PrefixCut := [⟨47,152764594,152764681⟩,
⟨64,206944167,206944286⟩]
theorem checked59503 : checkPrefixCuts (2^48) 7803109377 10 Manual.Count131072.C059503.packed 64 cuts59503 = true := by
 decide +kernel
def pointBounds59503 : List (Nat × Nat × Nat) := [(7803205632,113814204388344,113814592737041)]
theorem point_links_checked59503 : (cuts59503.take 1).map (fun c => (7803109377-1+2*2^10*c.k,113814051623750+c.lower,113814439972360+c.upper)) = pointBounds59503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000296
