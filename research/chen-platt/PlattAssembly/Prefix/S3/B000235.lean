import PlattAssemblyKernel
import PlattCertificates.Count131072.C027520
import PlattCertificates.Count131072.C027521
import PlattCertificates.Count131072.C027522
import PlattCertificates.Count131072.C027523
import PlattCertificates.Count131072.C027524
import PlattCertificates.Count131072.C027525
import PlattCertificates.Count131072.C027526
import PlattCertificates.Count131072.C027527
import PlattCertificates.Count131072.C027528
import PlattCertificates.Count131072.C027529
import PlattCertificates.Count131072.C027530
import PlattCertificates.Count131072.C027531
import PlattCertificates.Count131072.C027532
import PlattCertificates.Count131072.C027533
import PlattCertificates.Count131072.C027534
import PlattCertificates.Count131072.C027535
import PlattCertificates.Count131072.C027536
import PlattCertificates.Count131072.C027537
import PlattCertificates.Count131072.C027538
import PlattCertificates.Count131072.C027539
import PlattCertificates.Count131072.C027540
import PlattCertificates.Count131072.C027541
import PlattCertificates.Count131072.C027542
import PlattCertificates.Count131072.C027543
import PlattCertificates.Count131072.C027544
import PlattCertificates.Count131072.C027545
import PlattCertificates.Count131072.C027546
import PlattCertificates.Count131072.C027547
import PlattCertificates.Count131072.C027548
import PlattCertificates.Count131072.C027549
import PlattCertificates.Count131072.C027550
import PlattCertificates.Count131072.C027551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000235
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27520 : List PrefixCut := [⟨51,182632181,182632283⟩,
⟨128,462850228,462850488⟩]
theorem checked27520 : checkPrefixCuts (2^48) 3611033601 9 Manual.Count131072.C027520.packed 128 cuts27520 = true := by
 decide +kernel
def pointBounds27520 : List (Nat × Nat × Nat) := [(3611085824,104127831899690,104128214604721)]
theorem point_links_checked27520 : (cuts27520.take 1).map (fun c => (3611033601-1+2*2^9*c.k,104127649267509+c.lower,104128031972438+c.upper)) = pointBounds27520 := by
 decide +kernel
def cuts27521 : List PrefixCut := [⟨34,122140385,122140455⟩,
⟨128,461742206,461742463⟩]
theorem checked27521 : checkPrefixCuts (2^48) 3611164673 9 Manual.Count131072.C027521.packed 128 cuts27521 = true := by
 decide +kernel
def pointBounds27521 : List (Nat × Nat × Nat) := [(3611199488,104128234258122,104128616963381)]
theorem point_links_checked27521 : (cuts27521.take 1).map (fun c => (3611164673-1+2*2^9*c.k,104128112117737+c.lower,104128494822926+c.upper)) = pointBounds27521 := by
 decide +kernel
def cuts27522 : List PrefixCut := [⟨17,63289492,63289527⟩,
⟨128,472013749,472014010⟩]
theorem checked27522 : checkPrefixCuts (2^48) 3611295745 9 Manual.Count131072.C027522.packed 128 cuts27522 = true := by
 decide +kernel
def pointBounds27522 : List (Nat × Nat × Nat) := [(3611313152,104128637149435,104129019854916),(3611426816,104129045873692,104129428579399)]
theorem point_links_checked27522 : (cuts27522.take 2).map (fun c => (3611295745-1+2*2^9*c.k,104128573859943+c.lower,104128956565389+c.upper)) = pointBounds27522 := by
 decide +kernel
def cuts27523 : List PrefixCut := [⟨111,402787998,402788219⟩,
⟨128,465371760,465372016⟩]
theorem checked27523 : checkPrefixCuts (2^48) 3611426817 9 Manual.Count131072.C027523.packed 128 cuts27523 = true := by
 decide +kernel
def pointBounds27523 : List (Nat × Nat × Nat) := [(3611540480,104129448661690,104129831367618)]
theorem point_links_checked27523 : (cuts27523.take 1).map (fun c => (3611426817-1+2*2^9*c.k,104129045873692+c.lower,104129428579399+c.upper)) = pointBounds27523 := by
 decide +kernel
def cuts27524 : List PrefixCut := [⟨94,346270646,346270835⟩,
⟨128,468238601,468238858⟩]
theorem checked27524 : checkPrefixCuts (2^48) 3611557889 9 Manual.Count131072.C027524.packed 128 cuts27524 = true := by
 decide +kernel
def pointBounds27524 : List (Nat × Nat × Nat) := [(3611654144,104129857516098,104130240222250)]
theorem point_links_checked27524 : (cuts27524.take 1).map (fun c => (3611557889-1+2*2^9*c.k,104129511245452+c.lower,104129893951415+c.upper)) = pointBounds27524 := by
 decide +kernel
def cuts27525 : List PrefixCut := [⟨77,281028464,281028622⟩,
⟨128,465493883,465494146⟩]
theorem checked27525 : checkPrefixCuts (2^48) 3611688961 9 Manual.Count131072.C027525.packed 128 cuts27525 = true := by
 decide +kernel
def pointBounds27525 : List (Nat × Nat × Nat) := [(3611767808,104130260512517,104130643218895)]
theorem point_links_checked27525 : (cuts27525.take 1).map (fun c => (3611688961-1+2*2^9*c.k,104129979484053+c.lower,104130362190273+c.upper)) = pointBounds27525 := by
 decide +kernel
def cuts27526 : List PrefixCut := [⟨60,216959723,216959845⟩,
⟨128,462048092,462048354⟩]
theorem checked27526 : checkPrefixCuts (2^48) 3611820033 9 Manual.Count131072.C027526.packed 128 cuts27526 = true := by
 decide +kernel
def pointBounds27526 : List (Nat × Nat × Nat) := [(3611881472,104130661937659,104131044644264)]
theorem point_links_checked27526 : (cuts27526.take 1).map (fun c => (3611820033-1+2*2^9*c.k,104130444977936+c.lower,104130827684419+c.upper)) = pointBounds27526 := by
 decide +kernel
def cuts27527 : List PrefixCut := [⟨43,156402080,156402165⟩,
⟨128,464758713,464758972⟩]
theorem checked27527 : checkPrefixCuts (2^48) 3611951105 9 Manual.Count131072.C027527.packed 128 cuts27527 = true := by
 decide +kernel
def pointBounds27527 : List (Nat × Nat × Nat) := [(3611995136,104131063428108,104131446134938)]
theorem point_links_checked27527 : (cuts27527.take 1).map (fun c => (3611951105-1+2*2^9*c.k,104130907026028+c.lower,104131289732773+c.upper)) = pointBounds27527 := by
 decide +kernel
def cuts27528 : List PrefixCut := [⟨26,97329137,97329191⟩,
⟨128,460533945,460534201⟩]
theorem checked27528 : checkPrefixCuts (2^48) 3612082177 9 Manual.Count131072.C027528.packed 128 cuts27528 = true := by
 decide +kernel
def pointBounds27528 : List (Nat × Nat × Nat) := [(3612108800,104131469113878,104131851820936)]
theorem point_links_checked27528 : (cuts27528.take 1).map (fun c => (3612082177-1+2*2^9*c.k,104131371784741+c.lower,104131754491745+c.upper)) = pointBounds27528 := by
 decide +kernel
def cuts27529 : List PrefixCut := [⟨9,34364051,34364071⟩,
⟨120,440102316,440102561⟩,
⟨128,470023740,470024001⟩]
theorem checked27529 : checkPrefixCuts (2^48) 3612213249 9 Manual.Count131072.C027529.packed 128 cuts27529 = true := by
 decide +kernel
def pointBounds27529 : List (Nat × Nat × Nat) := [(3612222464,104131866682737,104132249390017),(3612336128,104132272421002,104132655128507)]
theorem point_links_checked27529 : (cuts27529.take 2).map (fun c => (3612213249-1+2*2^9*c.k,104131832318686+c.lower,104132215025946+c.upper)) = pointBounds27529 := by
 decide +kernel
def cuts27530 : List PrefixCut := [⟨103,370739264,370739469⟩,
⟨128,461123839,461124093⟩]
theorem checked27530 : checkPrefixCuts (2^48) 3612344321 9 Manual.Count131072.C027530.packed 128 cuts27530 = true := by
 decide +kernel
def pointBounds27530 : List (Nat × Nat × Nat) := [(3612449792,104132673081690,104133055789416)]
theorem point_links_checked27530 : (cuts27530.take 1).map (fun c => (3612344321-1+2*2^9*c.k,104132302342426+c.lower,104132685049947+c.upper)) = pointBounds27530 := by
 decide +kernel
def cuts27531 : List PrefixCut := [⟨86,307692273,307692444⟩,
⟨128,457912570,457912832⟩]
theorem checked27531 : checkPrefixCuts (2^48) 3612475393 9 Manual.Count131072.C027531.packed 128 cuts27531 = true := by
 decide +kernel
def pointBounds27531 : List (Nat × Nat × Nat) := [(3612563456,104133071158538,104133453866484)]
theorem point_links_checked27531 : (cuts27531.take 1).map (fun c => (3612475393-1+2*2^9*c.k,104132763466265+c.lower,104133146174040+c.upper)) = pointBounds27531 := by
 decide +kernel
def cuts27532 : List PrefixCut := [⟨69,247376518,247376658⟩,
⟨128,462570723,462570983⟩]
theorem checked27532 : checkPrefixCuts (2^48) 3612606465 9 Manual.Count131072.C027532.packed 128 cuts27532 = true := by
 decide +kernel
def pointBounds27532 : List (Nat × Nat × Nat) := [(3612677120,104133468755353,104133851463530)]
theorem point_links_checked27532 : (cuts27532.take 1).map (fun c => (3612606465-1+2*2^9*c.k,104133221378835+c.lower,104133604086872+c.upper)) = pointBounds27532 := by
 decide +kernel
def cuts27533 : List PrefixCut := [⟨52,189713836,189713939⟩,
⟨128,469955411,469955669⟩]
theorem checked27533 : checkPrefixCuts (2^48) 3612737537 9 Manual.Count131072.C027533.packed 128 cuts27533 = true := by
 decide +kernel
def pointBounds27533 : List (Nat × Nat × Nat) := [(3612790784,104133873663394,104134256371794)]
theorem point_links_checked27533 : (cuts27533.take 1).map (fun c => (3612737537-1+2*2^9*c.k,104133683949558+c.lower,104134066657855+c.upper)) = pointBounds27533 := by
 decide +kernel
def cuts27534 : List PrefixCut := [⟨35,121771134,121771202⟩,
⟨128,458485948,458486210⟩]
theorem checked27534 : checkPrefixCuts (2^48) 3612868609 9 Manual.Count131072.C027534.packed 128 cuts27534 = true := by
 decide +kernel
def pointBounds27534 : List (Nat × Nat × Nat) := [(3612904448,104134275676103,104134658384726)]
theorem point_links_checked27534 : (cuts27534.take 1).map (fun c => (3612868609-1+2*2^9*c.k,104134153904969+c.lower,104134536613524+c.upper)) = pointBounds27534 := by
 decide +kernel
def cuts27535 : List PrefixCut := [⟨18,65129373,65129410⟩,
⟨128,464312218,464312472⟩]
theorem checked27535 : checkPrefixCuts (2^48) 3612999681 9 Manual.Count131072.C027535.packed 128 cuts27535 = true := by
 decide +kernel
def pointBounds27535 : List (Nat × Nat × Nat) := [(3613018112,104134677520290,104135060229144)]
theorem point_links_checked27535 : (cuts27535.take 1).map (fun c => (3612999681-1+2*2^9*c.k,104134612390917+c.lower,104134995099734+c.upper)) = pointBounds27535 := by
 decide +kernel
def cuts27536 : List PrefixCut := [⟨1,4440489,4440491⟩,
⟨112,404389711,404389938⟩,
⟨128,462347809,462348069⟩]
theorem checked27536 : checkPrefixCuts (2^48) 3613130753 9 Manual.Count131072.C027536.packed 128 cuts27536 = true := by
 decide +kernel
def pointBounds27536 : List (Nat × Nat × Nat) := [(3613131776,104135081143624,104135463852697),(3613245440,104135481092846,104135863802144)]
theorem point_links_checked27536 : (cuts27536.take 2).map (fun c => (3613130753-1+2*2^9*c.k,104135076703135+c.lower,104135459412206+c.upper)) = pointBounds27536 := by
 decide +kernel
def cuts27537 : List PrefixCut := [⟨95,336993026,336993214⟩,
⟨128,457734990,457735243⟩]
theorem checked27537 : checkPrefixCuts (2^48) 3613261825 9 Manual.Count131072.C027537.packed 128 cuts27537 = true := by
 decide +kernel
def pointBounds27537 : List (Nat × Nat × Nat) := [(3613359104,104135876043970,104136258753489)]
theorem point_links_checked27537 : (cuts27537.take 1).map (fun c => (3613261825-1+2*2^9*c.k,104135539050944+c.lower,104135921760275+c.upper)) = pointBounds27537 := by
 decide +kernel
def cuts27538 : List PrefixCut := [⟨78,280428602,280428760⟩,
⟨128,462470132,462470393⟩]
theorem checked27538 : checkPrefixCuts (2^48) 3613392897 9 Manual.Count131072.C027538.packed 128 cuts27538 = true := by
 decide +kernel
def pointBounds27538 : List (Nat × Nat × Nat) := [(3613472768,104136277214536,104136659924278)]
theorem point_links_checked27538 : (cuts27538.take 1).map (fun c => (3613392897-1+2*2^9*c.k,104135996785934+c.lower,104136379495518+c.upper)) = pointBounds27538 := by
 decide +kernel
def cuts27539 : List PrefixCut := [⟨61,219505796,219505918⟩,
⟨128,458169243,458169503⟩]
theorem checked27539 : checkPrefixCuts (2^48) 3613523969 9 Manual.Count131072.C027539.packed 128 cuts27539 = true := by
 decide +kernel
def pointBounds27539 : List (Nat × Nat × Nat) := [(3613586432,104136678761862,104137061471829)]
theorem point_links_checked27539 : (cuts27539.take 1).map (fun c => (3613523969-1+2*2^9*c.k,104136459256066+c.lower,104136841965911+c.upper)) = pointBounds27539 := by
 decide +kernel
def cuts27540 : List PrefixCut := [⟨44,158898744,158898836⟩,
⟨128,470692910,470693174⟩]
theorem checked27540 : checkPrefixCuts (2^48) 3613655041 9 Manual.Count131072.C027540.packed 128 cuts27540 = true := by
 decide +kernel
def pointBounds27540 : List (Nat × Nat × Nat) := [(3613700096,104137076324053,104137459034250)]
theorem point_links_checked27540 : (cuts27540.take 1).map (fun c => (3613655041-1+2*2^9*c.k,104136917425309+c.lower,104137300135414+c.upper)) = pointBounds27540 := by
 decide +kernel
def cuts27541 : List PrefixCut := [⟨27,96582223,96582281⟩,
⟨128,465379510,465379769⟩]
theorem checked27541 : checkPrefixCuts (2^48) 3613786113 9 Manual.Count131072.C027541.packed 128 cuts27541 = true := by
 decide +kernel
def pointBounds27541 : List (Nat × Nat × Nat) := [(3613813760,104137484700442,104137867410869)]
theorem point_links_checked27541 : (cuts27541.take 1).map (fun c => (3613786113-1+2*2^9*c.k,104137388118219+c.lower,104137770828588+c.upper)) = pointBounds27541 := by
 decide +kernel
def cuts27542 : List PrefixCut := [⟨10,36684430,36684450⟩,
⟨121,435143729,435143975⟩,
⟨128,460767442,460767701⟩]
theorem checked27542 : checkPrefixCuts (2^48) 3613917185 9 Manual.Count131072.C027542.packed 128 cuts27542 = true := by
 decide +kernel
def pointBounds27542 : List (Nat × Nat × Nat) := [(3613927424,104137890182159,104138272892807),(3614041088,104138288641458,104138671352332)]
theorem point_links_checked27542 : (cuts27542.take 2).map (fun c => (3613917185-1+2*2^9*c.k,104137853497729+c.lower,104138236208357+c.upper)) = pointBounds27542 := by
 decide +kernel
def cuts27543 : List PrefixCut := [⟨104,372199946,372200152⟩,
⟨128,455298955,455299210⟩]
theorem checked27543 : checkPrefixCuts (2^48) 3614048257 9 Manual.Count131072.C027543.packed 128 cuts27543 = true := by
 decide +kernel
def pointBounds27543 : List (Nat × Nat × Nat) := [(3614154752,104138686465117,104139069176210)]
theorem point_links_checked27543 : (cuts27543.take 1).map (fun c => (3614048257-1+2*2^9*c.k,104138314265171+c.lower,104138696976058+c.upper)) = pointBounds27543 := by
 decide +kernel
def cuts27544 : List PrefixCut := [⟨87,311752707,311752879⟩,
⟨128,462369438,462369694⟩]
theorem checked27544 : checkPrefixCuts (2^48) 3614179329 9 Manual.Count131072.C027544.packed 128 cuts27544 = true := by
 decide +kernel
def pointBounds27544 : List (Nat × Nat × Nat) := [(3614268416,104139081316833,104139464028147)]
theorem point_links_checked27544 : (cuts27544.take 1).map (fun c => (3614179329-1+2*2^9*c.k,104138769564126+c.lower,104139152275268+c.upper)) = pointBounds27544 := by
 decide +kernel
def cuts27545 : List PrefixCut := [⟨70,250842207,250842348⟩,
⟨128,461262408,461262665⟩]
theorem checked27545 : checkPrefixCuts (2^48) 3614310401 9 Manual.Count131072.C027545.packed 128 cuts27545 = true := by
 decide +kernel
def pointBounds27545 : List (Nat × Nat × Nat) := [(3614382080,104139482775771,104139865487310)]
theorem point_links_checked27545 : (cuts27545.take 1).map (fun c => (3614310401-1+2*2^9*c.k,104139231933564+c.lower,104139614644962+c.upper)) = pointBounds27545 := by
 decide +kernel
def cuts27546 : List PrefixCut := [⟨53,187989034,187989140⟩,
⟨128,458675865,458676125⟩]
theorem checked27546 : checkPrefixCuts (2^48) 3614441473 9 Manual.Count131072.C027546.packed 128 cuts27546 = true := by
 decide +kernel
def pointBounds27546 : List (Nat × Nat × Nat) := [(3614495744,104139881185006,104140263896767)]
theorem point_links_checked27546 : (cuts27546.take 1).map (fun c => (3614441473-1+2*2^9*c.k,104139693195972+c.lower,104140075907627+c.upper)) = pointBounds27546 := by
 decide +kernel
def cuts27547 : List PrefixCut := [⟨36,130045999,130046071⟩,
⟨128,461151078,461151336⟩]
theorem checked27547 : checkPrefixCuts (2^48) 3614572545 9 Manual.Count131072.C027547.packed 128 cuts27547 = true := by
 decide +kernel
def pointBounds27547 : List (Nat × Nat × Nat) := [(3614609408,104140281917836,104140664629823)]
theorem point_links_checked27547 : (cuts27547.take 1).map (fun c => (3614572545-1+2*2^9*c.k,104140151871837+c.lower,104140534583752+c.upper)) = pointBounds27547 := by
 decide +kernel
def cuts27548 : List PrefixCut := [⟨19,69848691,69848729⟩,
⟨128,462224579,462224836⟩]
theorem checked27548 : checkPrefixCuts (2^48) 3614703617 9 Manual.Count131072.C027548.packed 128 cuts27548 = true := by
 decide +kernel
def pointBounds27548 : List (Nat × Nat × Nat) := [(3614723072,104140682871606,104141065583817)]
theorem point_links_checked27548 : (cuts27548.take 1).map (fun c => (3614703617-1+2*2^9*c.k,104140613022915+c.lower,104140995735088+c.upper)) = pointBounds27548 := by
 decide +kernel
def cuts27549 : List PrefixCut := [⟨2,7553058,7553062⟩,
⟨113,405055607,405055836⟩,
⟨128,459171049,459171310⟩]
theorem checked27549 : checkPrefixCuts (2^48) 3614834689 9 Manual.Count131072.C027549.packed 128 cuts27549 = true := by
 decide +kernel
def pointBounds27549 : List (Nat × Nat × Nat) := [(3614836736,104141082800552,104141465512986),(3614950400,104141480303101,104141863015760)]
theorem point_links_checked27549 : (cuts27549.take 2).map (fun c => (3614834689-1+2*2^9*c.k,104141075247494+c.lower,104141457959924+c.upper)) = pointBounds27549 := by
 decide +kernel
def cuts27550 : List PrefixCut := [⟨96,349136421,349136619⟩,
⟨128,465616939,465617201⟩]
theorem checked27550 : checkPrefixCuts (2^48) 3614965761 9 Manual.Count131072.C027550.packed 128 cuts27550 = true := by
 decide +kernel
def pointBounds27550 : List (Nat × Nat × Nat) := [(3615064064,104141883554964,104142266267853)]
theorem point_links_checked27550 : (cuts27550.take 1).map (fun c => (3614965761-1+2*2^9*c.k,104141534418543+c.lower,104141917131234+c.upper)) = pointBounds27550 := by
 decide +kernel
def cuts27551 : List PrefixCut := [⟨79,288004473,288004632⟩,
⟨128,467313009,467313269⟩]
theorem checked27551 : checkPrefixCuts (2^48) 3615096833 9 Manual.Count131072.C027551.packed 128 cuts27551 = true := by
 decide +kernel
def pointBounds27551 : List (Nat × Nat × Nat) := [(3615177728,104142288039955,104142670753067)]
theorem point_links_checked27551 : (cuts27551.take 1).map (fun c => (3615096833-1+2*2^9*c.k,104142000035482+c.lower,104142382748435+c.upper)) = pointBounds27551 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000235
