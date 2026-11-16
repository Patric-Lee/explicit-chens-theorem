import PlattAssemblyKernel
import PlattCertificates.Count131072.C019472
import PlattCertificates.Count131072.C019473
import PlattCertificates.Count131072.C019474
import PlattCertificates.Count131072.C019475
import PlattCertificates.Count131072.C019476
import PlattCertificates.Count131072.C019477
import PlattCertificates.Count131072.C019478
import PlattCertificates.Count131072.C019479
import PlattCertificates.Count131072.C019480
import PlattCertificates.Count131072.C019481
import PlattCertificates.Count131072.C019482
import PlattCertificates.Count131072.C019483
import PlattCertificates.Count131072.C019484
import PlattCertificates.Count131072.C019485
import PlattCertificates.Count131072.C019486
import PlattCertificates.Count131072.C019487
import PlattCertificates.Count131072.C019488
import PlattCertificates.Count131072.C019489
import PlattCertificates.Count131072.C019490
import PlattCertificates.Count131072.C019491
import PlattCertificates.Count131072.C019492
import PlattCertificates.Count131072.C019493
import PlattCertificates.Count131072.C019494
import PlattCertificates.Count131072.C019495
import PlattCertificates.Count131072.C019496
import PlattCertificates.Count131072.C019497
import PlattCertificates.Count131072.C019498
import PlattCertificates.Count131072.C019499
import PlattCertificates.Count131072.C019500
import PlattCertificates.Count131072.C019501
import PlattCertificates.Count131072.C019502
import PlattCertificates.Count131072.C019503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000296
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19472 : List PrefixCut := [⟨31,160658307,160658403⟩,
⟨110,573471749,573472093⟩,
⟨128,665194041,665194439⟩]
theorem checked19472 : checkPrefixCuts (2^48) 2556166145 9 Manual.Count131072.C019472.packed 128 cuts19472 = true := by
 decide +kernel
def pointBounds19472 : List (Nat × Nat × Nat) := [(2556197888,99674080120365,99674460285296),(2556278784,99674492933807,99674873098986)]
theorem point_links_checked19472 : (cuts19472.take 2).map (fun c => (2556166145-1+2*2^9*c.k,99673919462058+c.lower,99674299626893+c.upper)) = pointBounds19472 := by
 decide +kernel
def cuts19473 : List PrefixCut := [⟨61,320637525,320637715⟩,
⟨128,670114683,670115083⟩]
theorem checked19473 : checkPrefixCuts (2^48) 2556297217 9 Manual.Count131072.C019473.packed 128 cuts19473 = true := by
 decide +kernel
def pointBounds19473 : List (Nat × Nat × Nat) := [(2556359680,99674905293624,99675285459047)]
theorem point_links_checked19473 : (cuts19473.take 1).map (fun c => (2556297217-1+2*2^9*c.k,99674584656099+c.lower,99674964821332+c.upper)) = pointBounds19473 := by
 decide +kernel
def cuts19474 : List PrefixCut := [⟨12,61878721,61878757⟩,
⟨91,470799356,470799637⟩,
⟨128,667107509,667107909⟩]
theorem checked19474 : checkPrefixCuts (2^48) 2556428289 9 Manual.Count131072.C019474.packed 128 cuts19474 = true := by
 decide +kernel
def pointBounds19474 : List (Nat × Nat × Nat) := [(2556440576,99675316649503,99675696815172),(2556521472,99675725570138,99676105736052)]
theorem point_links_checked19474 : (cuts19474.take 2).map (fun c => (2556428289-1+2*2^9*c.k,99675254770782+c.lower,99675634936415+c.upper)) = pointBounds19474 := by
 decide +kernel
def cuts19475 : List PrefixCut := [⟨42,217333821,217333952⟩,
⟨121,629421245,629421624⟩,
⟨128,664320921,664321321⟩]
theorem checked19475 : checkPrefixCuts (2^48) 2556559361 9 Manual.Count131072.C019475.packed 128 cuts19475 = true := by
 decide +kernel
def pointBounds19475 : List (Nat × Nat × Nat) := [(2556602368,99676139212112,99676519378276),(2556683264,99676551299536,99676931465948)]
theorem point_links_checked19475 : (cuts19475.take 2).map (fun c => (2556559361-1+2*2^9*c.k,99675921878291+c.lower,99676302044324+c.upper)) = pointBounds19475 := by
 decide +kernel
def cuts19476 : List PrefixCut := [⟨72,371229860,371230082⟩,
⟨128,664396975,664397372⟩]
theorem checked19476 : checkPrefixCuts (2^48) 2556690433 9 Manual.Count131072.C019476.packed 128 cuts19476 = true := by
 decide +kernel
def pointBounds19476 : List (Nat × Nat × Nat) := [(2556764160,99676957429072,99677337595727)]
theorem point_links_checked19476 : (cuts19476.take 1).map (fun c => (2556690433-1+2*2^9*c.k,99676586199212+c.lower,99676966365645+c.upper)) = pointBounds19476 := by
 decide +kernel
def cuts19477 : List PrefixCut := [⟨23,117903510,117903581⟩,
⟨102,520374452,520374762⟩,
⟨128,651483004,651483391⟩]
theorem checked19477 : checkPrefixCuts (2^48) 2556821505 9 Manual.Count131072.C019477.packed 128 cuts19477 = true := by
 decide +kernel
def pointBounds19477 : List (Nat × Nat × Nat) := [(2556845056,99677368499697,99677748666598),(2556925952,99677770970639,99678151137779)]
theorem point_links_checked19477 : (cuts19477.take 2).map (fun c => (2556821505-1+2*2^9*c.k,99677250596187+c.lower,99677630763017+c.upper)) = pointBounds19477 := by
 decide +kernel
def cuts19478 : List PrefixCut := [⟨53,282137683,282137848⟩,
⟨128,681941691,681942094⟩]
theorem checked19478 : checkPrefixCuts (2^48) 2556952577 9 Manual.Count131072.C019478.packed 128 cuts19478 = true := by
 decide +kernel
def pointBounds19478 : List (Nat × Nat × Nat) := [(2557006848,99678184216874,99678564384256)]
theorem point_links_checked19478 : (cuts19478.take 1).map (fun c => (2556952577-1+2*2^9*c.k,99677902079191+c.lower,99678282246408+c.upper)) = pointBounds19478 := by
 decide +kernel
def cuts19479 : List PrefixCut := [⟨4,20804447,20804460⟩,
⟨83,434354738,434354997⟩,
⟨128,670348863,670349261⟩]
theorem checked19479 : checkPrefixCuts (2^48) 2557083649 9 Manual.Count131072.C019479.packed 128 cuts19479 = true := by
 decide +kernel
def pointBounds19479 : List (Nat × Nat × Nat) := [(2557087744,99678604825329,99678984992962),(2557168640,99679018375620,99679398543499)]
theorem point_links_checked19479 : (cuts19479.take 2).map (fun c => (2557083649-1+2*2^9*c.k,99678584020882+c.lower,99678964188502+c.upper)) = pointBounds19479 := by
 decide +kernel
def cuts19480 : List PrefixCut := [⟨34,178643826,178643930⟩,
⟨113,587875229,587875582⟩,
⟨128,667452644,667453046⟩]
theorem checked19480 : checkPrefixCuts (2^48) 2557214721 9 Manual.Count131072.C019480.packed 128 cuts19480 = true := by
 decide +kernel
def pointBounds19480 : List (Nat × Nat × Nat) := [(2557249536,99679433013571,99679813181693),(2557330432,99679842244974,99680222413345)]
theorem point_links_checked19480 : (cuts19480.take 2).map (fun c => (2557214721-1+2*2^9*c.k,99679254369745+c.lower,99679634537763+c.upper)) = pointBounds19480 := by
 decide +kernel
def cuts19481 : List PrefixCut := [⟨64,328870743,328870944⟩,
⟨128,658063204,658063601⟩]
theorem checked19481 : checkPrefixCuts (2^48) 2557345793 9 Manual.Count131072.C019481.packed 128 cuts19481 = true := by
 decide +kernel
def pointBounds19481 : List (Nat × Nat × Nat) := [(2557411328,99680250693132,99680630861753)]
theorem point_links_checked19481 : (cuts19481.take 1).map (fun c => (2557345793-1+2*2^9*c.k,99679921822389+c.lower,99680301990809+c.upper)) = pointBounds19481 := by
 decide +kernel
def cuts19482 : List PrefixCut := [⟨15,76161015,76161060⟩,
⟨94,489315740,489316030⟩,
⟨128,668925034,668925431⟩]
theorem checked19482 : checkPrefixCuts (2^48) 2557476865 9 Manual.Count131072.C019482.packed 128 cuts19482 = true := by
 decide +kernel
def pointBounds19482 : List (Nat × Nat × Nat) := [(2557492224,99680656046608,99681036215470),(2557573120,99681069201333,99681449370440)]
theorem point_links_checked19482 : (cuts19482.take 2).map (fun c => (2557476865-1+2*2^9*c.k,99680579885593+c.lower,99680960054410+c.upper)) = pointBounds19482 := by
 decide +kernel
def cuts19483 : List PrefixCut := [⟨45,229570493,229570636⟩,
⟨124,638627237,638627621⟩,
⟨128,658545999,658546397⟩]
theorem checked19483 : checkPrefixCuts (2^48) 2557607937 9 Manual.Count131072.C019483.packed 128 cuts19483 = true := by
 decide +kernel
def pointBounds19483 : List (Nat × Nat × Nat) := [(2557654016,99681478381120,99681858550477),(2557734912,99681887437864,99682267607462)]
theorem point_links_checked19483 : (cuts19483.take 2).map (fun c => (2557607937-1+2*2^9*c.k,99681248810627+c.lower,99681628979841+c.upper)) = pointBounds19483 := by
 decide +kernel
def cuts19484 : List PrefixCut := [⟨75,387804503,387804739⟩,
⟨128,659392733,659393135⟩]
theorem checked19484 : checkPrefixCuts (2^48) 2557739009 9 Manual.Count131072.C019484.packed 128 cuts19484 = true := by
 decide +kernel
def pointBounds19484 : List (Nat × Nat × Nat) := [(2557815808,99682295161129,99682675330977)]
theorem point_links_checked19484 : (cuts19484.take 1).map (fun c => (2557739009-1+2*2^9*c.k,99681907356626+c.lower,99682287526238+c.upper)) = pointBounds19484 := by
 decide +kernel
def cuts19485 : List PrefixCut := [⟨26,134251373,134251453⟩,
⟨105,548441220,548441548⟩,
⟨128,667831968,667832367⟩]
theorem checked19485 : checkPrefixCuts (2^48) 2557870081 9 Manual.Count131072.C019485.packed 128 cuts19485 = true := by
 decide +kernel
def pointBounds19485 : List (Nat × Nat × Nat) := [(2557896704,99682701000732,99683081170826),(2557977600,99683115190579,99683495360921)]
theorem point_links_checked19485 : (cuts19485.take 2).map (fun c => (2557870081-1+2*2^9*c.k,99682566749359+c.lower,99682946919373+c.upper)) = pointBounds19485 := by
 decide +kernel
def cuts19486 : List PrefixCut := [⟨56,292695292,292695464⟩,
⟨128,663726520,663726906⟩]
theorem checked19486 : checkPrefixCuts (2^48) 2558001153 9 Manual.Count131072.C019486.packed 128 cuts19486 = true := by
 decide +kernel
def pointBounds19486 : List (Nat × Nat × Nat) := [(2558058496,99683527276619,99683907447204)]
theorem point_links_checked19486 : (cuts19486.take 1).map (fun c => (2558001153-1+2*2^9*c.k,99683234581327+c.lower,99683614751740+c.upper)) = pointBounds19486 := by
 decide +kernel
def cuts19487 : List PrefixCut := [⟨7,36860473,36860495⟩,
⟨86,454091887,454092154⟩,
⟨128,675795678,675796076⟩]
theorem checked19487 : checkPrefixCuts (2^48) 2558132225 9 Manual.Count131072.C019487.packed 128 cuts19487 = true := by
 decide +kernel
def pointBounds19487 : List (Nat × Nat × Nat) := [(2558139392,99683935168320,99684315339141),(2558220288,99684352399734,99684732570800)]
theorem point_links_checked19487 : (cuts19487.take 2).map (fun c => (2558132225-1+2*2^9*c.k,99683898307847+c.lower,99684278478646+c.upper)) = pointBounds19487 := by
 decide +kernel
def cuts19488 : List PrefixCut := [⟨37,196614602,196614718⟩,
⟨116,610738929,610739293⟩,
⟨128,673340536,673340936⟩]
theorem checked19488 : checkPrefixCuts (2^48) 2558263297 9 Manual.Count131072.C019488.packed 128 cuts19488 = true := by
 decide +kernel
def pointBounds19488 : List (Nat × Nat × Nat) := [(2558301184,99684770718127,99685150889440),(2558382080,99685184842454,99685565014015)]
theorem point_links_checked19488 : (cuts19488.take 2).map (fun c => (2558263297-1+2*2^9*c.k,99684574103525+c.lower,99684954274722+c.upper)) = pointBounds19488 := by
 decide +kernel
def cuts19489 : List PrefixCut := [⟨67,350739469,350739674⟩,
⟨128,666814954,666815351⟩]
theorem checked19489 : checkPrefixCuts (2^48) 2558394369 9 Manual.Count131072.C019489.packed 128 cuts19489 = true := by
 decide +kernel
def pointBounds19489 : List (Nat × Nat × Nat) := [(2558462976,99685598183530,99685978355332)]
theorem point_links_checked19489 : (cuts19489.take 1).map (fun c => (2558394369-1+2*2^9*c.k,99685247444061+c.lower,99685627615658+c.upper)) = pointBounds19489 := by
 decide +kernel
def cuts19490 : List PrefixCut := [⟨18,95382221,95382277⟩,
⟨97,502756603,502756901⟩,
⟨128,662270453,662270845⟩]
theorem checked19490 : checkPrefixCuts (2^48) 2558525441 9 Manual.Count131072.C019490.packed 128 cuts19490 = true := by
 decide +kernel
def pointBounds19490 : List (Nat × Nat × Nat) := [(2558543872,99686009641236,99686389813286),(2558624768,99686417015618,99686797187910)]
theorem point_links_checked19490 : (cuts19490.take 2).map (fun c => (2558525441-1+2*2^9*c.k,99685914259015+c.lower,99686294431009+c.upper)) = pointBounds19490 := by
 decide +kernel
def cuts19491 : List PrefixCut := [⟨48,248617655,248617806⟩,
⟨127,656186293,656186683⟩,
⟨128,661026436,661026829⟩]
theorem checked19491 : checkPrefixCuts (2^48) 2558656513 9 Manual.Count131072.C019491.packed 128 cuts19491 = true := by
 decide +kernel
def pointBounds19491 : List (Nat × Nat × Nat) := [(2558705664,99686825147123,99687205319660),(2558786560,99687232715761,99687612888537)]
theorem point_links_checked19491 : (cuts19491.take 2).map (fun c => (2558656513-1+2*2^9*c.k,99686576529468+c.lower,99686956701854+c.upper)) = pointBounds19491 := by
 decide +kernel
def cuts19492 : List PrefixCut := [⟨78,411515639,411515891⟩,
⟨128,673092548,673092953⟩]
theorem checked19492 : checkPrefixCuts (2^48) 2558787585 9 Manual.Count131072.C019492.packed 128 cuts19492 = true := by
 decide +kernel
def pointBounds19492 : List (Nat × Nat × Nat) := [(2558867456,99687649071543,99688029244574)]
theorem point_links_checked19492 : (cuts19492.take 1).map (fun c => (2558787585-1+2*2^9*c.k,99687237555904+c.lower,99687617728683+c.upper)) = pointBounds19492 := by
 decide +kernel
def cuts19493 : List PrefixCut := [⟨29,149925847,149925935⟩,
⟨108,557675779,557676110⟩,
⟨128,661508610,661509000⟩]
theorem checked19493 : checkPrefixCuts (2^48) 2558918657 9 Manual.Count131072.C019493.packed 128 cuts19493 = true := by
 decide +kernel
def pointBounds19493 : List (Nat × Nat × Nat) := [(2558948352,99688060574299,99688440747571),(2559029248,99688468324231,99688848497746)]
theorem point_links_checked19493 : (cuts19493.take 2).map (fun c => (2558918657-1+2*2^9*c.k,99687910648452+c.lower,99688290821636+c.upper)) = pointBounds19493 := by
 decide +kernel
def cuts19494 : List PrefixCut := [⟨59,306103994,306104175⟩,
⟨128,668513949,668514349⟩]
theorem checked19494 : checkPrefixCuts (2^48) 2559049729 9 Manual.Count131072.C019494.packed 128 cuts19494 = true := by
 decide +kernel
def pointBounds19494 : List (Nat × Nat × Nat) := [(2559110144,99688878261056,99689258434811)]
theorem point_links_checked19494 : (cuts19494.take 1).map (fun c => (2559049729-1+2*2^9*c.k,99688572157062+c.lower,99688952330636+c.upper)) = pointBounds19494 := by
 decide +kernel
def cuts19495 : List PrefixCut := [⟨10,52463374,52463404⟩,
⟨89,465013860,465014137⟩,
⟨128,672109121,672109523⟩]
theorem checked19495 : checkPrefixCuts (2^48) 2559180801 9 Manual.Count131072.C019495.packed 128 cuts19495 = true := by
 decide +kernel
def pointBounds19495 : List (Nat × Nat × Nat) := [(2559191040,99689293134385,99689673308389),(2559271936,99689705684871,99690085859122)]
theorem point_links_checked19495 : (cuts19495.take 2).map (fun c => (2559180801-1+2*2^9*c.k,99689240671011+c.lower,99689620844985+c.upper)) = pointBounds19495 := by
 decide +kernel
def cuts19496 : List PrefixCut := [⟨40,212041059,212041188⟩,
⟨119,623025829,623026203⟩,
⟨128,668995486,668995888⟩]
theorem checked19496 : checkPrefixCuts (2^48) 2559311873 9 Manual.Count131072.C019496.packed 128 cuts19496 = true := by
 decide +kernel
def pointBounds19496 : List (Nat × Nat × Nat) := [(2559352832,99690124821191,99690504995696),(2559433728,99690535805961,99690915980711)]
theorem point_links_checked19496 : (cuts19496.take 2).map (fun c => (2559311873-1+2*2^9*c.k,99689912780132+c.lower,99690292954508+c.upper)) = pointBounds19496 := by
 decide +kernel
def cuts19497 : List PrefixCut := [⟨70,357413926,357414139⟩,
⟨128,658183866,658184254⟩]
theorem checked19497 : checkPrefixCuts (2^48) 2559442945 9 Manual.Count131072.C019497.packed 128 cuts19497 = true := by
 decide +kernel
def pointBounds19497 : List (Nat × Nat × Nat) := [(2559514624,99690939189544,99691319364535)]
theorem point_links_checked19497 : (cuts19497.take 1).map (fun c => (2559442945-1+2*2^9*c.k,99690581775618+c.lower,99690961950396+c.upper)) = pointBounds19497 := by
 decide +kernel
def cuts19498 : List PrefixCut := [⟨21,112828152,112828221⟩,
⟨100,519265328,519265643⟩,
⟨128,665737930,665738333⟩]
theorem checked19498 : checkPrefixCuts (2^48) 2559574017 9 Manual.Count131072.C019498.packed 128 cuts19498 = true := by
 decide +kernel
def pointBounds19498 : List (Nat × Nat × Nat) := [(2559595520,99691352787636,99691732962871),(2559676416,99691759224812,99692139400293)]
theorem point_links_checked19498 : (cuts19498.take 2).map (fun c => (2559574017-1+2*2^9*c.k,99691239959484+c.lower,99691620134650+c.upper)) = pointBounds19498 := by
 decide +kernel
def cuts19499 : List PrefixCut := [⟨51,269738434,269738595⟩,
⟨128,669992349,669992749⟩]
theorem checked19499 : checkPrefixCuts (2^48) 2559705089 9 Manual.Count131072.C019499.packed 128 cuts19499 = true := by
 decide +kernel
def pointBounds19499 : List (Nat × Nat × Nat) := [(2559757312,99692175435848,99692555611578)]
theorem point_links_checked19499 : (cuts19499.take 1).map (fun c => (2559705089-1+2*2^9*c.k,99691905697414+c.lower,99692285872983+c.upper)) = pointBounds19499 := by
 decide +kernel
def cuts19500 : List PrefixCut := [⟨2,10995812,10995819⟩,
⟨81,424651575,424651822⟩,
⟨128,668418659,668419047⟩]
theorem checked19500 : checkPrefixCuts (2^48) 2559836161 9 Manual.Count131072.C019500.packed 128 cuts19500 = true := by
 decide +kernel
def pointBounds19500 : List (Nat × Nat × Nat) := [(2559838208,99692586685575,99692966861551),(2559919104,99693000341338,99693380517554)]
theorem point_links_checked19500 : (cuts19500.take 2).map (fun c => (2559836161-1+2*2^9*c.k,99692575689763+c.lower,99692955865732+c.upper)) = pointBounds19500 := by
 decide +kernel
def cuts19501 : List PrefixCut := [⟨32,166796939,166797038⟩,
⟨111,574049405,574049746⟩,
⟨128,662886808,662887204⟩]
theorem checked19501 : checkPrefixCuts (2^48) 2559967233 9 Manual.Count131072.C019501.packed 128 cuts19501 = true := by
 decide +kernel
def pointBounds19501 : List (Nat × Nat × Nat) := [(2560000000,99693410905361,99693791081817),(2560080896,99693818157827,99694198334525)]
theorem point_links_checked19501 : (cuts19501.take 2).map (fun c => (2559967233-1+2*2^9*c.k,99693244108422+c.lower,99693624284779+c.upper)) = pointBounds19501 := by
 decide +kernel
def cuts19502 : List PrefixCut := [⟨62,324779121,324779314⟩,
⟨128,662193428,662193821⟩]
theorem checked19502 : checkPrefixCuts (2^48) 2560098305 9 Manual.Count131072.C019502.packed 128 cuts19502 = true := by
 decide +kernel
def pointBounds19502 : List (Nat × Nat × Nat) := [(2560161792,99694231774351,99694611951297)]
theorem point_links_checked19502 : (cuts19502.take 1).map (fun c => (2560098305-1+2*2^9*c.k,99693906995230+c.lower,99694287171983+c.upper)) = pointBounds19502 := by
 decide +kernel
def cuts19503 : List PrefixCut := [⟨13,65744716,65744758⟩,
⟨92,478785451,478785735⟩,
⟨128,660840165,660840562⟩]
theorem checked19503 : checkPrefixCuts (2^48) 2560229377 9 Manual.Count131072.C019503.packed 128 cuts19503 = true := by
 decide +kernel
def pointBounds19503 : List (Nat × Nat × Nat) := [(2560242688,99694634933374,99695015110562),(2560323584,99695047974109,99695428151539)]
theorem point_links_checked19503 : (cuts19503.take 2).map (fun c => (2560229377-1+2*2^9*c.k,99694569188658+c.lower,99694949365804+c.upper)) = pointBounds19503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000296
