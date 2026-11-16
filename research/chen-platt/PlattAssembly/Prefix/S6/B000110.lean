import PlattAssemblyKernel
import PlattCertificates.Count131072.C053520
import PlattCertificates.Count131072.C053521
import PlattCertificates.Count131072.C053522
import PlattCertificates.Count131072.C053523
import PlattCertificates.Count131072.C053524
import PlattCertificates.Count131072.C053525
import PlattCertificates.Count131072.C053526
import PlattCertificates.Count131072.C053527
import PlattCertificates.Count131072.C053528
import PlattCertificates.Count131072.C053529
import PlattCertificates.Count131072.C053530
import PlattCertificates.Count131072.C053531
import PlattCertificates.Count131072.C053532
import PlattCertificates.Count131072.C053533
import PlattCertificates.Count131072.C053534
import PlattCertificates.Count131072.C053535
import PlattCertificates.Count131072.C053536
import PlattCertificates.Count131072.C053537
import PlattCertificates.Count131072.C053538
import PlattCertificates.Count131072.C053539
import PlattCertificates.Count131072.C053540
import PlattCertificates.Count131072.C053541
import PlattCertificates.Count131072.C053542
import PlattCertificates.Count131072.C053543
import PlattCertificates.Count131072.C053544
import PlattCertificates.Count131072.C053545
import PlattCertificates.Count131072.C053546
import PlattCertificates.Count131072.C053547
import PlattCertificates.Count131072.C053548
import PlattCertificates.Count131072.C053549
import PlattCertificates.Count131072.C053550
import PlattCertificates.Count131072.C053551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53520 : List PrefixCut := [⟨64,227177926,227178058⟩]
theorem checked53520 : checkPrefixCuts (2^48) 7018905601 10 Manual.Count131072.C053520.packed 64 cuts53520 = true := by
 decide +kernel
def cuts53521 : List PrefixCut := [⟨25,90829885,90829937⟩,
⟨64,235033519,235033651⟩]
theorem checked53521 : checkPrefixCuts (2^48) 7019036673 10 Manual.Count131072.C053521.packed 64 cuts53521 = true := by
 decide +kernel
def pointBounds53521 : List (Nat × Nat × Nat) := [(7019087872,112502572668455,112502960271161)]
theorem point_links_checked53521 : (cuts53521.take 1).map (fun c => (7019036673-1+2*2^10*c.k,112502481838570+c.lower,112502869441224+c.upper)) = pointBounds53521 := by
 decide +kernel
def cuts53522 : List PrefixCut := [⟨64,230056679,230056809⟩]
theorem checked53522 : checkPrefixCuts (2^48) 7019167745 10 Manual.Count131072.C053522.packed 64 cuts53522 = true := by
 decide +kernel
def cuts53523 : List PrefixCut := [⟨5,18045052,18045064⟩,
⟨64,231175175,231175306⟩]
theorem checked53523 : checkPrefixCuts (2^48) 7019298817 10 Manual.Count131072.C053523.packed 64 cuts53523 = true := by
 decide +kernel
def pointBounds53523 : List (Nat × Nat × Nat) := [(7019309056,112502964973820,112503352576748)]
theorem point_links_checked53523 : (cuts53523.take 1).map (fun c => (7019298817-1+2*2^10*c.k,112502946928768+c.lower,112503334531684+c.upper)) = pointBounds53523 := by
 decide +kernel
def cuts53524 : List PrefixCut := [⟨49,178721727,178721828⟩,
⟨64,233175808,233175939⟩]
theorem checked53524 : checkPrefixCuts (2^48) 7019429889 10 Manual.Count131072.C053524.packed 64 cuts53524 = true := by
 decide +kernel
def pointBounds53524 : List (Nat × Nat × Nat) := [(7019530240,112503356825670,112503744428818)]
theorem point_links_checked53524 : (cuts53524.take 1).map (fun c => (7019429889-1+2*2^10*c.k,112503178103943+c.lower,112503565706990+c.upper)) = pointBounds53524 := by
 decide +kernel
def cuts53525 : List PrefixCut := [⟨64,232008606,232008736⟩]
theorem checked53525 : checkPrefixCuts (2^48) 7019560961 10 Manual.Count131072.C053525.packed 64 cuts53525 = true := by
 decide +kernel
def cuts53526 : List PrefixCut := [⟨29,103291750,103291809⟩,
⟨64,228154913,228155044⟩]
theorem checked53526 : checkPrefixCuts (2^48) 7019692033 10 Manual.Count131072.C053526.packed 64 cuts53526 = true := by
 decide +kernel
def pointBounds53526 : List (Nat × Nat × Nat) := [(7019751424,112503746580107,112504134183474)]
theorem point_links_checked53526 : (cuts53526.take 1).map (fun c => (7019692033-1+2*2^10*c.k,112503643288357+c.lower,112504030891665+c.upper)) = pointBounds53526 := by
 decide +kernel
def cuts53527 : List PrefixCut := [⟨64,230275787,230275919⟩]
theorem checked53527 : checkPrefixCuts (2^48) 7019823105 10 Manual.Count131072.C053527.packed 64 cuts53527 = true := by
 decide +kernel
def cuts53528 : List PrefixCut := [⟨9,32437945,32437963⟩,
⟨64,235203265,235203398⟩]
theorem checked53528 : checkPrefixCuts (2^48) 7019954177 10 Manual.Count131072.C053528.packed 64 cuts53528 = true := by
 decide +kernel
def pointBounds53528 : List (Nat × Nat × Nat) := [(7019972608,112504134157002,112504521760591)]
theorem point_links_checked53528 : (cuts53528.take 1).map (fun c => (7019954177-1+2*2^10*c.k,112504101719057+c.lower,112504489322628+c.upper)) = pointBounds53528 := by
 decide +kernel
def cuts53529 : List PrefixCut := [⟨53,191094398,191094505⟩,
⟨64,231550221,231550351⟩]
theorem checked53529 : checkPrefixCuts (2^48) 7020085249 10 Manual.Count131072.C053529.packed 64 cuts53529 = true := by
 decide +kernel
def pointBounds53529 : List (Nat × Nat × Nat) := [(7020193792,112504528016720,112504915620531)]
theorem point_links_checked53529 : (cuts53529.take 1).map (fun c => (7020085249-1+2*2^10*c.k,112504336922322+c.lower,112504724526026+c.upper)) = pointBounds53529 := by
 decide +kernel
def cuts53530 : List PrefixCut := [⟨64,232307713,232307845⟩]
theorem checked53530 : checkPrefixCuts (2^48) 7020216321 10 Manual.Count131072.C053530.packed 64 cuts53530 = true := by
 decide +kernel
def cuts53531 : List PrefixCut := [⟨33,119279541,119279607⟩,
⟨64,233826923,233827054⟩]
theorem checked53531 : checkPrefixCuts (2^48) 7020347393 10 Manual.Count131072.C053531.packed 64 cuts53531 = true := by
 decide +kernel
def pointBounds53531 : List (Nat × Nat × Nat) := [(7020414976,112504920059797,112505307663829)]
theorem point_links_checked53531 : (cuts53531.take 1).map (fun c => (7020347393-1+2*2^10*c.k,112504800780256+c.lower,112505188384222+c.upper)) = pointBounds53531 := by
 decide +kernel
def cuts53532 : List PrefixCut := [⟨64,229933536,229933670⟩]
theorem checked53532 : checkPrefixCuts (2^48) 7020478465 10 Manual.Count131072.C053532.packed 64 cuts53532 = true := by
 decide +kernel
def cuts53533 : List PrefixCut := [⟨13,48271469,48271497⟩,
⟨64,233016347,233016476⟩]
theorem checked53533 : checkPrefixCuts (2^48) 7020609537 10 Manual.Count131072.C053533.packed 64 cuts53533 = true := by
 decide +kernel
def pointBounds53533 : List (Nat × Nat × Nat) := [(7020636160,112505312812184,112505700416443)]
theorem point_links_checked53533 : (cuts53533.take 1).map (fun c => (7020609537-1+2*2^10*c.k,112505264540715+c.lower,112505652144946+c.upper)) = pointBounds53533 := by
 decide +kernel
def cuts53534 : List PrefixCut := [⟨57,204667485,204667604⟩,
⟨64,230365946,230366079⟩]
theorem checked53534 : checkPrefixCuts (2^48) 7020740609 10 Manual.Count131072.C053534.packed 64 cuts53534 = true := by
 decide +kernel
def pointBounds53534 : List (Nat × Nat × Nat) := [(7020857344,112505702224547,112506089829026)]
theorem point_links_checked53534 : (cuts53534.take 1).map (fun c => (7020740609-1+2*2^10*c.k,112505497557062+c.lower,112505885161422+c.upper)) = pointBounds53534 := by
 decide +kernel
def cuts53535 : List PrefixCut := [⟨64,233328394,233328523⟩]
theorem checked53535 : checkPrefixCuts (2^48) 7020871681 10 Manual.Count131072.C053535.packed 64 cuts53535 = true := by
 decide +kernel
def cuts53536 : List PrefixCut := [⟨37,134943604,134943681⟩,
⟨64,231600169,231600302⟩]
theorem checked53536 : checkPrefixCuts (2^48) 7021002753 10 Manual.Count131072.C053536.packed 64 cuts53536 = true := by
 decide +kernel
def pointBounds53536 : List (Nat × Nat × Nat) := [(7021078528,112506096195006,112506483799705)]
theorem point_links_checked53536 : (cuts53536.take 1).map (fun c => (7021002753-1+2*2^10*c.k,112505961251402+c.lower,112506348856024+c.upper)) = pointBounds53536 := by
 decide +kernel
def cuts53537 : List PrefixCut := [⟨64,228348589,228348719⟩]
theorem checked53537 : checkPrefixCuts (2^48) 7021133825 10 Manual.Count131072.C053537.packed 64 cuts53537 = true := by
 decide +kernel
def cuts53538 : List PrefixCut := [⟨17,62257931,62257965⟩,
⟨64,230749653,230749784⟩]
theorem checked53538 : checkPrefixCuts (2^48) 7021264897 10 Manual.Count131072.C053538.packed 64 cuts53538 = true := by
 decide +kernel
def pointBounds53538 : List (Nat × Nat × Nat) := [(7021299712,112506483458091,112506871063010)]
theorem point_links_checked53538 : (cuts53538.take 1).map (fun c => (7021264897-1+2*2^10*c.k,112506421200160+c.lower,112506808805045+c.upper)) = pointBounds53538 := by
 decide +kernel
def cuts53539 : List PrefixCut := [⟨61,222126557,222126681⟩,
⟨64,233551477,233551607⟩]
theorem checked53539 : checkPrefixCuts (2^48) 7021395969 10 Manual.Count131072.C053539.packed 64 cuts53539 = true := by
 decide +kernel
def pointBounds53539 : List (Nat × Nat × Nat) := [(7021520896,112506874076370,112507261681510)]
theorem point_links_checked53539 : (cuts53539.take 1).map (fun c => (7021395969-1+2*2^10*c.k,112506651949813+c.lower,112507039554829+c.upper)) = pointBounds53539 := by
 decide +kernel
def cuts53540 : List PrefixCut := [⟨64,233667392,233667521⟩]
theorem checked53540 : checkPrefixCuts (2^48) 7021527041 10 Manual.Count131072.C053540.packed 64 cuts53540 = true := by
 decide +kernel
def cuts53541 : List PrefixCut := [⟨41,146515893,146515977⟩,
⟨64,230776784,230776915⟩]
theorem checked53541 : checkPrefixCuts (2^48) 7021658113 10 Manual.Count131072.C053541.packed 64 cuts53541 = true := by
 decide +kernel
def pointBounds53541 : List (Nat × Nat × Nat) := [(7021742080,112507265684575,112507653289934)]
theorem point_links_checked53541 : (cuts53541.take 1).map (fun c => (7021658113-1+2*2^10*c.k,112507119168682+c.lower,112507506773957+c.upper)) = pointBounds53541 := by
 decide +kernel
def cuts53542 : List PrefixCut := [⟨64,231694469,231694601⟩]
theorem checked53542 : checkPrefixCuts (2^48) 7021789185 10 Manual.Count131072.C053542.packed 64 cuts53542 = true := by
 decide +kernel
def cuts53543 : List PrefixCut := [⟨21,78165848,78165891⟩,
⟨64,233012963,233013093⟩]
theorem checked53543 : checkPrefixCuts (2^48) 7021920257 10 Manual.Count131072.C053543.packed 64 cuts53543 = true := by
 decide +kernel
def pointBounds53543 : List (Nat × Nat × Nat) := [(7021963264,112507659805783,112508047411364)]
theorem point_links_checked53543 : (cuts53543.take 1).map (fun c => (7021920257-1+2*2^10*c.k,112507581639935+c.lower,112507969245473+c.upper)) = pointBounds53543 := by
 decide +kernel
def cuts53544 : List PrefixCut := [⟨64,231445325,231445457⟩]
theorem checked53544 : checkPrefixCuts (2^48) 7022051329 10 Manual.Count131072.C053544.packed 64 cuts53544 = true := by
 decide +kernel
def cuts53545 : List PrefixCut := [⟨1,3046359,3046361⟩,
⟨64,231240557,231240691⟩]
theorem checked53545 : checkPrefixCuts (2^48) 7022182401 10 Manual.Count131072.C053545.packed 64 cuts53545 = true := by
 decide +kernel
def pointBounds53545 : List (Nat × Nat × Nat) := [(7022184448,112508049144582,112508436750384)]
theorem point_links_checked53545 : (cuts53545.take 1).map (fun c => (7022182401-1+2*2^10*c.k,112508046098223+c.lower,112508433704023+c.upper)) = pointBounds53545 := by
 decide +kernel
def cuts53546 : List PrefixCut := [⟨45,161372820,161372910⟩,
⟨64,230234201,230234328⟩]
theorem checked53546 : checkPrefixCuts (2^48) 7022313473 10 Manual.Count131072.C053546.packed 64 cuts53546 = true := by
 decide +kernel
def pointBounds53546 : List (Nat × Nat × Nat) := [(7022405632,112508438711600,112508826317624)]
theorem point_links_checked53546 : (cuts53546.take 1).map (fun c => (7022313473-1+2*2^10*c.k,112508277338780+c.lower,112508664944714+c.upper)) = pointBounds53546 := by
 decide +kernel
def cuts53547 : List PrefixCut := [⟨64,233556664,233556798⟩]
theorem checked53547 : checkPrefixCuts (2^48) 7022444545 10 Manual.Count131072.C053547.packed 64 cuts53547 = true := by
 decide +kernel
def cuts53548 : List PrefixCut := [⟨25,89461433,89461486⟩,
⟨64,232710625,232710760⟩]
theorem checked53548 : checkPrefixCuts (2^48) 7022575617 10 Manual.Count131072.C053548.packed 64 cuts53548 = true := by
 decide +kernel
def pointBounds53548 : List (Nat × Nat × Nat) := [(7022626816,112508830591078,112509218197326)]
theorem point_links_checked53548 : (cuts53548.take 1).map (fun c => (7022575617-1+2*2^10*c.k,112508741129645+c.lower,112509128735840+c.upper)) = pointBounds53548 := by
 decide +kernel
def cuts53549 : List PrefixCut := [⟨64,230020905,230021034⟩]
theorem checked53549 : checkPrefixCuts (2^48) 7022706689 10 Manual.Count131072.C053549.packed 64 cuts53549 = true := by
 decide +kernel
def cuts53550 : List PrefixCut := [⟨5,17955798,17955808⟩,
⟨64,231740040,231740169⟩]
theorem checked53550 : checkPrefixCuts (2^48) 7022837761 10 Manual.Count131072.C053550.packed 64 cuts53550 = true := by
 decide +kernel
def pointBounds53550 : List (Nat × Nat × Nat) := [(7022848000,112509221816973,112509609423442)]
theorem point_links_checked53550 : (cuts53550.take 1).map (fun c => (7022837761-1+2*2^10*c.k,112509203861175+c.lower,112509591467634+c.upper)) = pointBounds53550 := by
 decide +kernel
def cuts53551 : List PrefixCut := [⟨49,178912215,178912318⟩,
⟨64,232336893,232337028⟩]
theorem checked53551 : checkPrefixCuts (2^48) 7022968833 10 Manual.Count131072.C053551.packed 64 cuts53551 = true := by
 decide +kernel
def pointBounds53551 : List (Nat × Nat × Nat) := [(7023069184,112509614513430,112510002120121)]
theorem point_links_checked53551 : (cuts53551.take 1).map (fun c => (7022968833-1+2*2^10*c.k,112509435601215+c.lower,112509823207803+c.upper)) = pointBounds53551 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000110
