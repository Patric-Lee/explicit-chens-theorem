import PlattAssemblyKernel
import PlattCertificates.Count131072.C035472
import PlattCertificates.Count131072.C035473
import PlattCertificates.Count131072.C035474
import PlattCertificates.Count131072.C035475
import PlattCertificates.Count131072.C035476
import PlattCertificates.Count131072.C035477
import PlattCertificates.Count131072.C035478
import PlattCertificates.Count131072.C035479
import PlattCertificates.Count131072.C035480
import PlattCertificates.Count131072.C035481
import PlattCertificates.Count131072.C035482
import PlattCertificates.Count131072.C035483
import PlattCertificates.Count131072.C035484
import PlattCertificates.Count131072.C035485
import PlattCertificates.Count131072.C035486
import PlattCertificates.Count131072.C035487
import PlattCertificates.Count131072.C035488
import PlattCertificates.Count131072.C035489
import PlattCertificates.Count131072.C035490
import PlattCertificates.Count131072.C035491
import PlattCertificates.Count131072.C035492
import PlattCertificates.Count131072.C035493
import PlattCertificates.Count131072.C035494
import PlattCertificates.Count131072.C035495
import PlattCertificates.Count131072.C035496
import PlattCertificates.Count131072.C035497
import PlattCertificates.Count131072.C035498
import PlattCertificates.Count131072.C035499
import PlattCertificates.Count131072.C035500
import PlattCertificates.Count131072.C035501
import PlattCertificates.Count131072.C035502
import PlattCertificates.Count131072.C035503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000171
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts35472 : List PrefixCut := [⟨16,87587866,87587921⟩,
⟨64,355126311,355126532⟩]
theorem checked35472 : checkPrefixCuts (2^48) 4653318145 10 Manual.Count131072.C035472.packed 64 cuts35472 = true := by
 decide +kernel
def pointBounds35472 : List (Nat × Nat × Nat) := [(4653350912,107352569970928,107352954558676)]
theorem point_links_checked35472 : (cuts35472.take 1).map (fun c => (4653318145-1+2*2^10*c.k,107352482383062+c.lower,107352866970755+c.upper)) = pointBounds35472 := by
 decide +kernel
def cuts35473 : List PrefixCut := [⟨24,133676375,133676457⟩,
⟨64,353120308,353120531⟩]
theorem checked35473 : checkPrefixCuts (2^48) 4653449217 10 Manual.Count131072.C035473.packed 64 cuts35473 = true := by
 decide +kernel
def pointBounds35473 : List (Nat × Nat × Nat) := [(4653498368,107352971185748,107353355773744)]
theorem point_links_checked35473 : (cuts35473.take 1).map (fun c => (4653449217-1+2*2^10*c.k,107352837509373+c.lower,107353222097287+c.upper)) = pointBounds35473 := by
 decide +kernel
def cuts35474 : List PrefixCut := [⟨32,173774107,173774214⟩,
⟨64,350569970,350570188⟩]
theorem checked35474 : checkPrefixCuts (2^48) 4653580289 10 Manual.Count131072.C035474.packed 64 cuts35474 = true := by
 decide +kernel
def pointBounds35474 : List (Nat × Nat × Nat) := [(4653645824,107353364403788,107353748992032)]
theorem point_links_checked35474 : (cuts35474.take 1).map (fun c => (4653580289-1+2*2^10*c.k,107353190629681+c.lower,107353575217818+c.upper)) = pointBounds35474 := by
 decide +kernel
def cuts35475 : List PrefixCut := [⟨40,227296704,227296847⟩,
⟨64,358483395,358483616⟩]
theorem checked35475 : checkPrefixCuts (2^48) 4653711361 10 Manual.Count131072.C035475.packed 64 cuts35475 = true := by
 decide +kernel
def pointBounds35475 : List (Nat × Nat × Nat) := [(4653793280,107353768496355,107354153084853)]
theorem point_links_checked35475 : (cuts35475.take 1).map (fun c => (4653711361-1+2*2^10*c.k,107353541199651+c.lower,107353925788006+c.upper)) = pointBounds35475 := by
 decide +kernel
def cuts35476 : List PrefixCut := [⟨48,264123249,264123414⟩,
⟨64,355509687,355509909⟩]
theorem checked35476 : checkPrefixCuts (2^48) 4653842433 10 Manual.Count131072.C035476.packed 64 cuts35476 = true := by
 decide +kernel
def pointBounds35476 : List (Nat × Nat × Nat) := [(4653940736,107354163806295,107354548395036)]
theorem point_links_checked35476 : (cuts35476.take 1).map (fun c => (4653842433-1+2*2^10*c.k,107353899683046+c.lower,107354284271622+c.upper)) = pointBounds35476 := by
 decide +kernel
def cuts35477 : List PrefixCut := [⟨56,310200944,310201139⟩,
⟨64,354773935,354774157⟩]
theorem checked35477 : checkPrefixCuts (2^48) 4653973505 10 Manual.Count131072.C035477.packed 64 cuts35477 = true := by
 decide +kernel
def pointBounds35477 : List (Nat × Nat × Nat) := [(4654088192,107354565393677,107354949982670)]
theorem point_links_checked35477 : (cuts35477.take 1).map (fun c => (4653973505-1+2*2^10*c.k,107354255192733+c.lower,107354639781531+c.upper)) = pointBounds35477 := by
 decide +kernel
def cuts35478 : List PrefixCut := [⟨64,349986147,349986372⟩]
theorem checked35478 : checkPrefixCuts (2^48) 4654104577 10 Manual.Count131072.C035478.packed 64 cuts35478 = true := by
 decide +kernel
def pointBounds35478 : List (Nat × Nat × Nat) := [(4654235648,107354959952815,107355344542060)]
theorem point_links_checked35478 : (cuts35478.take 1).map (fun c => (4654104577-1+2*2^10*c.k,107354609966668+c.lower,107354994555688+c.upper)) = pointBounds35478 := by
 decide +kernel
def cuts35479 : List PrefixCut := [⟨64,354391131,354391347⟩]
theorem checked35479 : checkPrefixCuts (2^48) 4654235649 10 Manual.Count131072.C035479.packed 64 cuts35479 = true := by
 decide +kernel
def cuts35480 : List PrefixCut := [⟨8,45598404,45598431⟩,
⟨64,357223416,357223637⟩]
theorem checked35480 : checkPrefixCuts (2^48) 4654366721 10 Manual.Count131072.C035480.packed 64 cuts35480 = true := by
 decide +kernel
def pointBounds35480 : List (Nat × Nat × Nat) := [(4654383104,107355359942350,107355744531838)]
theorem point_links_checked35480 : (cuts35480.take 1).map (fun c => (4654366721-1+2*2^10*c.k,107355314343946+c.lower,107355698933407+c.upper)) = pointBounds35480 := by
 decide +kernel
def cuts35481 : List PrefixCut := [⟨16,88835612,88835667⟩,
⟨64,355882943,355883159⟩]
theorem checked35481 : checkPrefixCuts (2^48) 4654497793 10 Manual.Count131072.C035481.packed 64 cuts35481 = true := by
 decide +kernel
def pointBounds35481 : List (Nat × Nat × Nat) := [(4654530560,107355760402974,107356144992711)]
theorem point_links_checked35481 : (cuts35481.take 1).map (fun c => (4654497793-1+2*2^10*c.k,107355671567362+c.lower,107356056157044+c.upper)) = pointBounds35481 := by
 decide +kernel
def cuts35482 : List PrefixCut := [⟨24,130921276,130921358⟩,
⟨64,352426071,352426295⟩]
theorem checked35482 : checkPrefixCuts (2^48) 4654628865 10 Manual.Count131072.C035482.packed 64 cuts35482 = true := by
 decide +kernel
def pointBounds35482 : List (Nat × Nat × Nat) := [(4654678016,107356158371581,107356542961561)]
theorem point_links_checked35482 : (cuts35482.take 1).map (fun c => (4654628865-1+2*2^10*c.k,107356027450305+c.lower,107356412040203+c.upper)) = pointBounds35482 := by
 decide +kernel
def cuts35483 : List PrefixCut := [⟨32,174395221,174395329⟩,
⟨64,353202226,353202447⟩]
theorem checked35483 : checkPrefixCuts (2^48) 4654759937 10 Manual.Count131072.C035483.packed 64 cuts35483 = true := by
 decide +kernel
def pointBounds35483 : List (Nat × Nat × Nat) := [(4654825472,107356554271597,107356938861827)]
theorem point_links_checked35483 : (cuts35483.take 1).map (fun c => (4654759937-1+2*2^10*c.k,107356379876376+c.lower,107356764466498+c.upper)) = pointBounds35483 := by
 decide +kernel
def cuts35484 : List PrefixCut := [⟨40,222764476,222764619⟩,
⟨64,356699425,356699650⟩]
theorem checked35484 : checkPrefixCuts (2^48) 4654891009 10 Manual.Count131072.C035484.packed 64 cuts35484 = true := by
 decide +kernel
def pointBounds35484 : List (Nat × Nat × Nat) := [(4654972928,107356955843078,107357340433564)]
theorem point_links_checked35484 : (cuts35484.take 1).map (fun c => (4654891009-1+2*2^10*c.k,107356733078602+c.lower,107357117668945+c.upper)) = pointBounds35484 := by
 decide +kernel
def cuts35485 : List PrefixCut := [⟨48,273186687,273186856⟩,
⟨64,361405760,361405982⟩]
theorem checked35485 : checkPrefixCuts (2^48) 4655022081 10 Manual.Count131072.C035485.packed 64 cuts35485 = true := by
 decide +kernel
def pointBounds35485 : List (Nat × Nat × Nat) := [(4655120384,107357362964714,107357747555451)]
theorem point_links_checked35485 : (cuts35485.take 1).map (fun c => (4655022081-1+2*2^10*c.k,107357089778027+c.lower,107357474368595+c.upper)) = pointBounds35485 := by
 decide +kernel
def cuts35486 : List PrefixCut := [⟨56,309457217,309457407⟩,
⟨64,354502619,354502836⟩]
theorem checked35486 : checkPrefixCuts (2^48) 4655153153 10 Manual.Count131072.C035486.packed 64 cuts35486 = true := by
 decide +kernel
def pointBounds35486 : List (Nat × Nat × Nat) := [(4655267840,107357760641004,107358145231984)]
theorem point_links_checked35486 : (cuts35486.take 1).map (fun c => (4655153153-1+2*2^10*c.k,107357451183787+c.lower,107357835774577+c.upper)) = pointBounds35486 := by
 decide +kernel
def cuts35487 : List PrefixCut := [⟨64,359390151,359390369⟩]
theorem checked35487 : checkPrefixCuts (2^48) 4655284225 10 Manual.Count131072.C035487.packed 64 cuts35487 = true := by
 decide +kernel
def pointBounds35487 : List (Nat × Nat × Nat) := [(4655415296,107358165076557,107358549667782)]
theorem point_links_checked35487 : (cuts35487.take 1).map (fun c => (4655284225-1+2*2^10*c.k,107357805686406+c.lower,107358190277413+c.upper)) = pointBounds35487 := by
 decide +kernel
def cuts35488 : List PrefixCut := [⟨64,349827180,349827392⟩]
theorem checked35488 : checkPrefixCuts (2^48) 4655415297 10 Manual.Count131072.C035488.packed 64 cuts35488 = true := by
 decide +kernel
def cuts35489 : List PrefixCut := [⟨8,44679948,44679976⟩,
⟨64,357374731,357374954⟩]
theorem checked35489 : checkPrefixCuts (2^48) 4655546369 10 Manual.Count131072.C035489.packed 64 cuts35489 = true := by
 decide +kernel
def pointBounds35489 : List (Nat × Nat × Nat) := [(4655562752,107358559583685,107358944175150)]
theorem point_links_checked35489 : (cuts35489.take 1).map (fun c => (4655546369-1+2*2^10*c.k,107358514903737+c.lower,107358899495174+c.upper)) = pointBounds35489 := by
 decide +kernel
def cuts35490 : List PrefixCut := [⟨16,88692192,88692247⟩,
⟨64,355309145,355309362⟩]
theorem checked35490 : checkPrefixCuts (2^48) 4655677441 10 Manual.Count131072.C035490.packed 64 cuts35490 = true := by
 decide +kernel
def pointBounds35490 : List (Nat × Nat × Nat) := [(4655710208,107358960970660,107359345562375)]
theorem point_links_checked35490 : (cuts35490.take 1).map (fun c => (4655677441-1+2*2^10*c.k,107358872278468+c.lower,107359256870128+c.upper)) = pointBounds35490 := by
 decide +kernel
def cuts35491 : List PrefixCut := [⟨24,133548177,133548261⟩,
⟨64,355117704,355117925⟩]
theorem checked35491 : checkPrefixCuts (2^48) 4655808513 10 Manual.Count131072.C035491.packed 64 cuts35491 = true := by
 decide +kernel
def pointBounds35491 : List (Nat × Nat × Nat) := [(4655857664,107359361135790,107359745727751)]
theorem point_links_checked35491 : (cuts35491.take 1).map (fun c => (4655808513-1+2*2^10*c.k,107359227587613+c.lower,107359612179490+c.upper)) = pointBounds35491 := by
 decide +kernel
def cuts35492 : List PrefixCut := [⟨32,174895132,174895243⟩,
⟨64,352387297,352387524⟩]
theorem checked35492 : checkPrefixCuts (2^48) 4655939585 10 Manual.Count131072.C035492.packed 64 cuts35492 = true := by
 decide +kernel
def pointBounds35492 : List (Nat × Nat × Nat) := [(4656005120,107359757600449,107360142192658)]
theorem point_links_checked35492 : (cuts35492.take 1).map (fun c => (4655939585-1+2*2^10*c.k,107359582705317+c.lower,107359967297415+c.upper)) = pointBounds35492 := by
 decide +kernel
def cuts35493 : List PrefixCut := [⟨40,222163955,222164095⟩,
⟨64,356125431,356125656⟩]
theorem checked35493 : checkPrefixCuts (2^48) 4656070657 10 Manual.Count131072.C035493.packed 64 cuts35493 = true := by
 decide +kernel
def pointBounds35493 : List (Nat × Nat × Nat) := [(4656152576,107360157256569,107360541849034)]
theorem point_links_checked35493 : (cuts35493.take 1).map (fun c => (4656070657-1+2*2^10*c.k,107359935092614+c.lower,107360319684939+c.upper)) = pointBounds35493 := by
 decide +kernel
def cuts35494 : List PrefixCut := [⟨48,268825461,268825625⟩,
⟨64,359681994,359682216⟩]
theorem checked35494 : checkPrefixCuts (2^48) 4656201729 10 Manual.Count131072.C035494.packed 64 cuts35494 = true := by
 decide +kernel
def pointBounds35494 : List (Nat × Nat × Nat) := [(4656300032,107360560043506,107360944636220)]
theorem point_links_checked35494 : (cuts35494.take 1).map (fun c => (4656201729-1+2*2^10*c.k,107360291218045+c.lower,107360675810595+c.upper)) = pointBounds35494 := by
 decide +kernel
def cuts35495 : List PrefixCut := [⟨56,316149085,316149286⟩,
⟨64,361606218,361606447⟩]
theorem checked35495 : checkPrefixCuts (2^48) 4656332801 10 Manual.Count131072.C035495.packed 64 cuts35495 = true := by
 decide +kernel
def pointBounds35495 : List (Nat × Nat × Nat) := [(4656447488,107360967049124,107361351642097)]
theorem point_links_checked35495 : (cuts35495.take 1).map (fun c => (4656332801-1+2*2^10*c.k,107360650900039+c.lower,107361035492811+c.upper)) = pointBounds35495 := by
 decide +kernel
def cuts35496 : List PrefixCut := [⟨64,357243887,357244109⟩]
theorem checked35496 : checkPrefixCuts (2^48) 4656463873 10 Manual.Count131072.C035496.packed 64 cuts35496 = true := by
 decide +kernel
def pointBounds35496 : List (Nat × Nat × Nat) := [(4656594944,107361369750144,107361754343367)]
theorem point_links_checked35496 : (cuts35496.take 1).map (fun c => (4656463873-1+2*2^10*c.k,107361012506257+c.lower,107361397099258+c.upper)) = pointBounds35496 := by
 decide +kernel
def cuts35497 : List PrefixCut := [⟨64,357536023,357536248⟩]
theorem checked35497 : checkPrefixCuts (2^48) 4656594945 10 Manual.Count131072.C035497.packed 64 cuts35497 = true := by
 decide +kernel
def cuts35498 : List PrefixCut := [⟨8,45514856,45514884⟩,
⟨64,362542827,362543054⟩]
theorem checked35498 : checkPrefixCuts (2^48) 4656726017 10 Manual.Count131072.C035498.packed 64 cuts35498 = true := by
 decide +kernel
def pointBounds35498 : List (Nat × Nat × Nat) := [(4656742400,107361772801023,107362157394499)]
theorem point_links_checked35498 : (cuts35498.take 1).map (fun c => (4656726017-1+2*2^10*c.k,107361727286167+c.lower,107362111879615+c.upper)) = pointBounds35498 := by
 decide +kernel
def cuts35499 : List PrefixCut := [⟨16,87702635,87702688⟩,
⟨64,353224492,353224714⟩]
theorem checked35499 : checkPrefixCuts (2^48) 4656857089 10 Manual.Count131072.C035499.packed 64 cuts35499 = true := by
 decide +kernel
def pointBounds35499 : List (Nat × Nat × Nat) := [(4656889856,107362177531629,107362562125357)]
theorem point_links_checked35499 : (cuts35499.take 1).map (fun c => (4656857089-1+2*2^10*c.k,107362089828994+c.lower,107362474422669+c.upper)) = pointBounds35499 := by
 decide +kernel
def cuts35500 : List PrefixCut := [⟨24,131821999,131822079⟩,
⟨64,356176139,356176357⟩]
theorem checked35500 : checkPrefixCuts (2^48) 4656988161 10 Manual.Count131072.C035500.packed 64 cuts35500 = true := by
 decide +kernel
def pointBounds35500 : List (Nat × Nat × Nat) := [(4657037312,107362574875485,107362959469462)]
theorem point_links_checked35500 : (cuts35500.take 1).map (fun c => (4656988161-1+2*2^10*c.k,107362443053486+c.lower,107362827647383+c.upper)) = pointBounds35500 := by
 decide +kernel
def cuts35501 : List PrefixCut := [⟨32,180834318,180834430⟩,
⟨64,359188096,359188323⟩]
theorem checked35501 : checkPrefixCuts (2^48) 4657119233 10 Manual.Count131072.C035501.packed 64 cuts35501 = true := by
 decide +kernel
def pointBounds35501 : List (Nat × Nat × Nat) := [(4657184768,107362980063943,107363364658170)]
theorem point_links_checked35501 : (cuts35501.take 1).map (fun c => (4657119233-1+2*2^10*c.k,107362799229625+c.lower,107363183823740+c.upper)) = pointBounds35501 := by
 decide +kernel
def cuts35502 : List PrefixCut := [⟨40,223679090,223679225⟩,
⟨64,356035284,356035505⟩]
theorem checked35502 : checkPrefixCuts (2^48) 4657250305 10 Manual.Count131072.C035502.packed 64 cuts35502 = true := by
 decide +kernel
def pointBounds35502 : List (Nat × Nat × Nat) := [(4657332224,107363382096811,107363766691288)]
theorem point_links_checked35502 : (cuts35502.take 1).map (fun c => (4657250305-1+2*2^10*c.k,107363158417721+c.lower,107363543012063+c.upper)) = pointBounds35502 := by
 decide +kernel
def cuts35503 : List PrefixCut := [⟨48,263680785,263680946⟩,
⟨64,353970395,353970613⟩]
theorem checked35503 : checkPrefixCuts (2^48) 4657381377 10 Manual.Count131072.C035503.packed 64 cuts35503 = true := by
 decide +kernel
def pointBounds35503 : List (Nat × Nat × Nat) := [(4657479680,107363778133790,107364162728514)]
theorem point_links_checked35503 : (cuts35503.take 1).map (fun c => (4657381377-1+2*2^10*c.k,107363514453005+c.lower,107363899047568+c.upper)) = pointBounds35503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000171
