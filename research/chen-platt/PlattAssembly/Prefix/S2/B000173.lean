import PlattAssemblyKernel
import PlattCertificates.Count131072.C015536
import PlattCertificates.Count131072.C015537
import PlattCertificates.Count131072.C015538
import PlattCertificates.Count131072.C015539
import PlattCertificates.Count131072.C015540
import PlattCertificates.Count131072.C015541
import PlattCertificates.Count131072.C015542
import PlattCertificates.Count131072.C015543
import PlattCertificates.Count131072.C015544
import PlattCertificates.Count131072.C015545
import PlattCertificates.Count131072.C015546
import PlattCertificates.Count131072.C015547
import PlattCertificates.Count131072.C015548
import PlattCertificates.Count131072.C015549
import PlattCertificates.Count131072.C015550
import PlattCertificates.Count131072.C015551
import PlattCertificates.Count131072.C015552
import PlattCertificates.Count131072.C015553
import PlattCertificates.Count131072.C015554
import PlattCertificates.Count131072.C015555
import PlattCertificates.Count131072.C015556
import PlattCertificates.Count131072.C015557
import PlattCertificates.Count131072.C015558
import PlattCertificates.Count131072.C015559
import PlattCertificates.Count131072.C015560
import PlattCertificates.Count131072.C015561
import PlattCertificates.Count131072.C015562
import PlattCertificates.Count131072.C015563
import PlattCertificates.Count131072.C015564
import PlattCertificates.Count131072.C015565
import PlattCertificates.Count131072.C015566
import PlattCertificates.Count131072.C015567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000173
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15536 : List PrefixCut := [⟨28,180450196,180450317⟩,
⟨91,590730539,590730926⟩,
⟨128,837113278,837113823⟩]
theorem checked15536 : checkPrefixCuts (2^48) 2040266753 9 Manual.Count131072.C015536.packed 128 cuts15536 = true := by
 decide +kernel
def pointBounds15536 : List (Nat × Nat × Nat) := [(2040295424,96729516797814,96729895135853),(2040359936,96729927078157,96730305416462)]
theorem point_links_checked15536 : (cuts15536.take 2).map (fun c => (2040266753-1+2*2^9*c.k,96729336347618+c.lower,96729714685536+c.upper)) = pointBounds15536 := by
 decide +kernel
def cuts15537 : List PrefixCut := [⟨26,171609905,171610016⟩,
⟨89,585588875,585589256⟩,
⟨128,844784672,844785221⟩]
theorem checked15537 : checkPrefixCuts (2^48) 2040397825 9 Manual.Count131072.C015537.packed 128 cuts15537 = true := by
 decide +kernel
def pointBounds15537 : List (Nat × Nat × Nat) := [(2040424448,96730345070801,96730723409375),(2040488960,96730759049771,96731137388615)]
theorem point_links_checked15537 : (cuts15537.take 2).map (fun c => (2040397825-1+2*2^9*c.k,96730173460896+c.lower,96730551799359+c.upper)) = pointBounds15537 := by
 decide +kernel
def cuts15538 : List PrefixCut := [⟨24,163460439,163460544⟩,
⟨87,575344100,575344471⟩,
⟨128,846109890,846110438⟩]
theorem checked15538 : checkPrefixCuts (2^48) 2040528897 9 Manual.Count131072.C015538.packed 128 cuts15538 = true := by
 decide +kernel
def pointBounds15538 : List (Nat × Nat × Nat) := [(2040553472,96731181706007,96731560045124),(2040617984,96731593589668,96731971929051)]
theorem point_links_checked15538 : (cuts15538.take 2).map (fun c => (2040528897-1+2*2^9*c.k,96731018245568+c.lower,96731396584580+c.upper)) = pointBounds15538 := by
 decide +kernel
def cuts15539 : List PrefixCut := [⟨22,141656695,141656787⟩,
⟨85,555445401,555445766⟩,
⟨128,844400145,844400700⟩]
theorem checked15539 : checkPrefixCuts (2^48) 2040659969 9 Manual.Count131072.C015539.packed 128 cuts15539 = true := by
 decide +kernel
def pointBounds15539 : List (Nat × Nat × Nat) := [(2040682496,96732006012153,96732384351805),(2040747008,96732419800859,96732798140784)]
theorem point_links_checked15539 : (cuts15539.take 2).map (fun c => (2040659969-1+2*2^9*c.k,96731864355458+c.lower,96732242695018+c.upper)) = pointBounds15539 := by
 decide +kernel
def cuts15540 : List PrefixCut := [⟨20,129786211,129786298⟩,
⟨83,538169843,538170196⟩,
⟨128,831795386,831795926⟩]
theorem checked15540 : checkPrefixCuts (2^48) 2040791041 9 Manual.Count131072.C015540.packed 128 cuts15540 = true := by
 decide +kernel
def pointBounds15540 : List (Nat × Nat × Nat) := [(2040811520,96732838541814,96733216882016),(2040876032,96733246925446,96733625265914)]
theorem point_links_checked15540 : (cuts15540.take 2).map (fun c => (2040791041-1+2*2^9*c.k,96732708755603+c.lower,96733087095718+c.upper)) = pointBounds15540 := by
 decide +kernel
def cuts15541 : List PrefixCut := [⟨18,120123883,120123960⟩,
⟨81,533446553,533446902⟩,
⟨128,848429209,848429761⟩]
theorem checked15541 : checkPrefixCuts (2^48) 2040922113 9 Manual.Count131072.C015541.packed 128 cuts15541 = true := by
 decide +kernel
def pointBounds15541 : List (Nat × Nat × Nat) := [(2040940544,96733660674872,96734039015604),(2041005056,96734073997542,96734452338546)]
theorem point_links_checked15541 : (cuts15541.take 2).map (fun c => (2040922113-1+2*2^9*c.k,96733540550989+c.lower,96733918891644+c.upper)) = pointBounds15541 := by
 decide +kernel
def cuts15542 : List PrefixCut := [⟨16,103567506,103567573⟩,
⟨79,517829348,517829689⟩,
⟨128,836515203,836515756⟩]
theorem checked15542 : checkPrefixCuts (2^48) 2041053185 9 Manual.Count131072.C015542.packed 128 cuts15542 = true := by
 decide +kernel
def pointBounds15542 : List (Nat × Nat × Nat) := [(2041069568,96734492547704,96734870888978),(2041134080,96734906809546,96735285151094)]
theorem point_links_checked15542 : (cuts15542.take 2).map (fun c => (2041053185-1+2*2^9*c.k,96734388980198+c.lower,96734767321405+c.upper)) = pointBounds15542 := by
 decide +kernel
def cuts15543 : List PrefixCut := [⟨14,92667017,92667078⟩,
⟨77,509108866,509109201⟩,
⟨128,844045508,844046066⟩]
theorem checked15543 : checkPrefixCuts (2^48) 2041184257 9 Manual.Count131072.C015543.packed 128 cuts15543 = true := by
 decide +kernel
def pointBounds15543 : List (Nat × Nat × Nat) := [(2041198592,96735318162418,96735696504239),(2041263104,96735734604267,96736112946362)]
theorem point_links_checked15543 : (cuts15543.take 2).map (fun c => (2041184257-1+2*2^9*c.k,96735225495401+c.lower,96735603837161+c.upper)) = pointBounds15543 := by
 decide +kernel
def cuts15544 : List PrefixCut := [⟨12,79010150,79010202⟩,
⟨75,491013390,491013712⟩,
⟨128,841095653,841096201⟩]
theorem checked15544 : checkPrefixCuts (2^48) 2041315329 9 Manual.Count131072.C015544.packed 128 cuts15544 = true := by
 decide +kernel
def pointBounds15544 : List (Nat × Nat × Nat) := [(2041327616,96736148551059,96736526893429),(2041392128,96736560554299,96736938896939)]
theorem point_links_checked15544 : (cuts15544.take 2).map (fun c => (2041315329-1+2*2^9*c.k,96736069540909+c.lower,96736447883227+c.upper)) = pointBounds15544 := by
 decide +kernel
def cuts15545 : List PrefixCut := [⟨10,63700461,63700502⟩,
⟨73,473885300,473885613⟩,
⟨128,831390390,831390933⟩]
theorem checked15545 : checkPrefixCuts (2^48) 2041446401 9 Manual.Count131072.C015545.packed 128 cuts15545 = true := by
 decide +kernel
def pointBounds15545 : List (Nat × Nat × Nat) := [(2041456640,96736974337023,96737352679930),(2041521152,96737384521862,96737762865041)]
theorem point_links_checked15545 : (cuts15545.take 2).map (fun c => (2041446401-1+2*2^9*c.k,96736910636562+c.lower,96737288979428+c.upper)) = pointBounds15545 := by
 decide +kernel
def cuts15546 : List PrefixCut := [⟨8,52942459,52942494⟩,
⟨71,466823839,466824145⟩,
⟨128,848708175,848708730⟩]
theorem checked15546 : checkPrefixCuts (2^48) 2041577473 9 Manual.Count131072.C015546.packed 128 cuts15546 = true := by
 decide +kernel
def pointBounds15546 : List (Nat × Nat × Nat) := [(2041585664,96737794969411,96738173312855),(2041650176,96738208850791,96738587194506)]
theorem point_links_checked15546 : (cuts15546.take 2).map (fun c => (2041577473-1+2*2^9*c.k,96737742026952+c.lower,96738120370361+c.upper)) = pointBounds15546 := by
 decide +kernel
def cuts15547 : List PrefixCut := [⟨6,42599424,42599451⟩,
⟨69,459487463,459487760⟩,
⟨128,845069591,845070140⟩]
theorem checked15547 : checkPrefixCuts (2^48) 2041708545 9 Manual.Count131072.C015547.packed 128 cuts15547 = true := by
 decide +kernel
def pointBounds15547 : List (Nat × Nat × Nat) := [(2041714688,96738633334551,96739011678542),(2041779200,96739050222590,96739428566851)]
theorem point_links_checked15547 : (cuts15547.take 2).map (fun c => (2041708545-1+2*2^9*c.k,96738590735127+c.lower,96738969079091+c.upper)) = pointBounds15547 := by
 decide +kernel
def cuts15548 : List PrefixCut := [⟨4,27294980,27294999⟩,
⟨67,436437068,436437358⟩,
⟨128,830127552,830128097⟩]
theorem checked15548 : checkPrefixCuts (2^48) 2041839617 9 Manual.Count131072.C015548.packed 128 cuts15548 = true := by
 decide +kernel
def pointBounds15548 : List (Nat × Nat × Nat) := [(2041843712,96739463099698,96739841444230),(2041908224,96739872241786,96740250586589)]
theorem point_links_checked15548 : (cuts15548.take 2).map (fun c => (2041839617-1+2*2^9*c.k,96739435804718+c.lower,96739814149231+c.upper)) = pointBounds15548 := by
 decide +kernel
def cuts15549 : List PrefixCut := [⟨2,12957397,12957406⟩,
⟨65,425244009,425244292⟩,
⟨128,832831107,832831658⟩]
theorem checked15549 : checkPrefixCuts (2^48) 2041970689 9 Manual.Count131072.C015549.packed 128 cuts15549 = true := by
 decide +kernel
def pointBounds15549 : List (Nat × Nat × Nat) := [(2041972736,96740278889667,96740657234734),(2042037248,96740691176279,96741069521620),(2042101760,96741098763377,96741477108986)]
theorem point_links_checked15549 : (cuts15549.take 3).map (fun c => (2041970689-1+2*2^9*c.k,96740265932270+c.lower,96740644277328+c.upper)) = pointBounds15549 := by
 decide +kernel
def cuts15550 : List PrefixCut := [⟨63,420530629,420530906⟩,
⟨126,826989349,826989894⟩,
⟨128,840772059,840772613⟩]
theorem checked15550 : checkPrefixCuts (2^48) 2042101761 9 Manual.Count131072.C015550.packed 128 cuts15550 = true := by
 decide +kernel
def pointBounds15550 : List (Nat × Nat × Nat) := [(2042166272,96741519294006,96741897639892),(2042230784,96741925752726,96742304098880)]
theorem point_links_checked15550 : (cuts15550.take 2).map (fun c => (2042101761-1+2*2^9*c.k,96741098763377+c.lower,96741477108986+c.upper)) = pointBounds15550 := by
 decide +kernel
def cuts15551 : List PrefixCut := [⟨61,402311004,402311264⟩,
⟨124,815359356,815359890⟩,
⟨128,843749932,843750484⟩]
theorem checked15551 : checkPrefixCuts (2^48) 2042232833 9 Manual.Count131072.C015551.packed 128 cuts15551 = true := by
 decide +kernel
def pointBounds15551 : List (Nat × Nat × Nat) := [(2042295296,96742341846440,96742720192863),(2042359808,96742754894792,96743133241489)]
theorem point_links_checked15551 : (cuts15551.take 2).map (fun c => (2042232833-1+2*2^9*c.k,96741939535436+c.lower,96742317881599+c.upper)) = pointBounds15551 := by
 decide +kernel
def cuts15552 : List PrefixCut := [⟨59,390019653,390019905⟩,
⟨122,806349590,806350113⟩,
⟨128,849346170,849346721⟩]
theorem checked15552 : checkPrefixCuts (2^48) 2042363905 9 Manual.Count131072.C015552.packed 128 cuts15552 = true := by
 decide +kernel
def pointBounds15552 : List (Nat × Nat × Nat) := [(2042424320,96743173305021,96743551651988),(2042488832,96743589634958,96743967982196)]
theorem point_links_checked15552 : (cuts15552.take 2).map (fun c => (2042363905-1+2*2^9*c.k,96742783285368+c.lower,96743161632083+c.upper)) = pointBounds15552 := by
 decide +kernel
def cuts15553 : List PrefixCut := [⟨57,375387302,375387550⟩,
⟨120,785903167,785903686⟩,
⟨128,839232068,839232620⟩]
theorem checked15553 : checkPrefixCuts (2^48) 2042494977 9 Manual.Count131072.C015553.packed 128 cuts15553 = true := by
 decide +kernel
def pointBounds15553 : List (Nat × Nat × Nat) := [(2042553344,96744008018840,96744386366354),(2042617856,96744418534705,96744796882490)]
theorem point_links_checked15553 : (cuts15553.take 2).map (fun c => (2042494977-1+2*2^9*c.k,96743632631538+c.lower,96744010978804+c.upper)) = pointBounds15553 := by
 decide +kernel
def cuts15554 : List PrefixCut := [⟨55,358965395,358965630⟩,
⟨118,771797757,771798262⟩,
⟨128,839729214,839729765⟩]
theorem checked15554 : checkPrefixCuts (2^48) 2042626049 9 Manual.Count131072.C015554.packed 128 cuts15554 = true := by
 decide +kernel
def pointBounds15554 : List (Nat × Nat × Nat) := [(2042682368,96744830829001,96745209177054),(2042746880,96745243661363,96745622009686)]
theorem point_links_checked15554 : (cuts15554.take 2).map (fun c => (2042626049-1+2*2^9*c.k,96744471863606+c.lower,96744850211424+c.upper)) = pointBounds15554 := by
 decide +kernel
def cuts15555 : List PrefixCut := [⟨53,347643720,347643945⟩,
⟨116,775606431,775606932⟩,
⟨128,858827505,858828059⟩]
theorem checked15555 : checkPrefixCuts (2^48) 2042757121 9 Manual.Count131072.C015555.packed 128 cuts15555 = true := by
 decide +kernel
def pointBounds15555 : List (Nat × Nat × Nat) := [(2042811392,96745659236540,96746037585134),(2042875904,96746087199251,96746465548121)]
theorem point_links_checked15555 : (cuts15555.take 2).map (fun c => (2042757121-1+2*2^9*c.k,96745311592820+c.lower,96745689941189+c.upper)) = pointBounds15555 := by
 decide +kernel
def cuts15556 : List PrefixCut := [⟨51,340043651,340043875⟩,
⟨114,751721696,751722192⟩,
⟨128,847750494,847751055⟩]
theorem checked15556 : checkPrefixCuts (2^48) 2042888193 9 Manual.Count131072.C015556.packed 128 cuts15556 = true := by
 decide +kernel
def pointBounds15556 : List (Nat × Nat × Nat) := [(2042940416,96746510463976,96746888813123),(2043004928,96746922142021,96747300491440)]
theorem point_links_checked15556 : (cuts15556.take 2).map (fun c => (2042888193-1+2*2^9*c.k,96746170420325+c.lower,96746548769248+c.upper)) = pointBounds15556 := by
 decide +kernel
def cuts15557 : List PrefixCut := [⟨49,326382518,326382729⟩,
⟨112,740376567,740377048⟩,
⟨128,844665191,844665740⟩]
theorem checked15557 : checkPrefixCuts (2^48) 2043019265 9 Manual.Count131072.C015557.packed 128 cuts15557 = true := by
 decide +kernel
def pointBounds15557 : List (Nat × Nat × Nat) := [(2043069440,96747344553337,96747722903032),(2043133952,96747758547386,96748136897351)]
theorem point_links_checked15557 : (cuts15557.take 2).map (fun c => (2043019265-1+2*2^9*c.k,96747018170819+c.lower,96747396520303+c.upper)) = pointBounds15557 := by
 decide +kernel
def cuts15558 : List PrefixCut := [⟨47,306110540,306110747⟩,
⟨110,729997174,729997658⟩,
⟨128,844059902,844060461⟩]
theorem checked15558 : checkPrefixCuts (2^48) 2043150337 9 Manual.Count131072.C015558.packed 128 cuts15558 = true := by
 decide +kernel
def pointBounds15558 : List (Nat × Nat × Nat) := [(2043198464,96748168946550,96748547296790),(2043262976,96748592833184,96748971183701)]
theorem point_links_checked15558 : (cuts15558.take 2).map (fun c => (2043150337-1+2*2^9*c.k,96747862836010+c.lower,96748241186043+c.upper)) = pointBounds15558 := by
 decide +kernel
def cuts15559 : List PrefixCut := [⟨45,297688032,297688225⟩,
⟨108,717139893,717140358⟩,
⟨128,848551630,848552181⟩]
theorem checked15559 : checkPrefixCuts (2^48) 2043281409 9 Manual.Count131072.C015559.packed 128 cuts15559 = true := by
 decide +kernel
def pointBounds15559 : List (Nat × Nat × Nat) := [(2043327488,96749004583944,96749382934729),(2043392000,96749424035805,96749802386862)]
theorem point_links_checked15559 : (cuts15559.take 2).map (fun c => (2043281409-1+2*2^9*c.k,96748706895912+c.lower,96749085246504+c.upper)) = pointBounds15559 := by
 decide +kernel
def cuts15560 : List PrefixCut := [⟨43,283894456,283894639⟩,
⟨106,702906705,702907161⟩,
⟨128,851665235,851665790⟩]
theorem checked15560 : checkPrefixCuts (2^48) 2043412481 9 Manual.Count131072.C015560.packed 128 cuts15560 = true := by
 decide +kernel
def pointBounds15560 : List (Nat × Nat × Nat) := [(2043456512,96749839341998,96750217693324),(2043521024,96750258354247,96750636705846)]
theorem point_links_checked15560 : (cuts15560.take 2).map (fun c => (2043412481-1+2*2^9*c.k,96749555447542+c.lower,96749933798685+c.upper)) = pointBounds15560 := by
 decide +kernel
def cuts15561 : List PrefixCut := [⟨41,266521516,266521693⟩,
⟨104,676003532,676003977⟩,
⟨128,833705105,833705650⟩]
theorem checked15561 : checkPrefixCuts (2^48) 2043543553 9 Manual.Count131072.C015561.packed 128 cuts15561 = true := by
 decide +kernel
def pointBounds15561 : List (Nat × Nat × Nat) := [(2043585536,96750673634293,96751051986168),(2043650048,96751083116309,96751461468452)]
theorem point_links_checked15561 : (cuts15561.take 2).map (fun c => (2043543553-1+2*2^9*c.k,96750407112777+c.lower,96750785464475+c.upper)) = pointBounds15561 := by
 decide +kernel
def cuts15562 : List PrefixCut := [⟨39,252731710,252731878⟩,
⟨102,660535256,660535691⟩,
⟨128,831310349,831310896⟩]
theorem checked15562 : checkPrefixCuts (2^48) 2043674625 9 Manual.Count131072.C015562.packed 128 cuts15562 = true := by
 decide +kernel
def pointBounds15562 : List (Nat × Nat × Nat) := [(2043714560,96751493549592,96751871902003),(2043779072,96751901353138,96752279705816)]
theorem point_links_checked15562 : (cuts15562.take 2).map (fun c => (2043674625-1+2*2^9*c.k,96751240817882+c.lower,96751619170125+c.upper)) = pointBounds15562 := by
 decide +kernel
def cuts15563 : List PrefixCut := [⟨37,249548047,249548212⟩,
⟨100,664349349,664349786⟩,
⟨128,842825517,842826068⟩]
theorem checked15563 : checkPrefixCuts (2^48) 2043805697 9 Manual.Count131072.C015563.packed 128 cuts15563 = true := by
 decide +kernel
def pointBounds15563 : List (Nat × Nat × Nat) := [(2043843584,96752321676278,96752700029233),(2043908096,96752736477580,96753114830807)]
theorem point_links_checked15563 : (cuts15563.take 2).map (fun c => (2043805697-1+2*2^9*c.k,96752072128231+c.lower,96752450481021+c.upper)) = pointBounds15563 := by
 decide +kernel
def cuts15564 : List PrefixCut := [⟨35,234108545,234108697⟩,
⟨98,648608244,648608665⟩,
⟨128,847866398,847866948⟩]
theorem checked15564 : checkPrefixCuts (2^48) 2043936769 9 Manual.Count131072.C015564.packed 128 cuts15564 = true := by
 decide +kernel
def pointBounds15564 : List (Nat × Nat × Nat) := [(2043972608,96753149062293,96753527415786),(2044037120,96753563561992,96753941915754)]
theorem point_links_checked15564 : (cuts15564.take 2).map (fun c => (2043936769-1+2*2^9*c.k,96752914953748+c.lower,96753293307089+c.upper)) = pointBounds15564 := by
 decide +kernel
def cuts15565 : List PrefixCut := [⟨33,217431695,217431842⟩,
⟨96,635485421,635485841⟩,
⟨128,850015140,850015702⟩]
theorem checked15565 : checkPrefixCuts (2^48) 2044067841 9 Manual.Count131072.C015565.packed 128 cuts15565 = true := by
 decide +kernel
def pointBounds15565 : List (Nat × Nat × Nat) := [(2044101632,96753980251841,96754358605879),(2044166144,96754398305567,96754776659878)]
theorem point_links_checked15565 : (cuts15565.take 2).map (fun c => (2044067841-1+2*2^9*c.k,96753762820146+c.lower,96754141174037+c.upper)) = pointBounds15565 := by
 decide +kernel
def cuts15566 : List PrefixCut := [⟨31,206402376,206402512⟩,
⟨94,613552200,613552602⟩,
⟨128,839220922,839221469⟩]
theorem checked15566 : checkPrefixCuts (2^48) 2044198913 9 Manual.Count131072.C015566.packed 128 cuts15566 = true := by
 decide +kernel
def pointBounds15566 : List (Nat × Nat × Nat) := [(2044230656,96754819237662,96755197592251),(2044295168,96755226387486,96755604742341)]
theorem point_links_checked15566 : (cuts15566.take 2).map (fun c => (2044198913-1+2*2^9*c.k,96754612835286+c.lower,96754991189739+c.upper)) = pointBounds15566 := by
 decide +kernel
def cuts15567 : List PrefixCut := [⟨29,189729441,189729566⟩,
⟨92,605389744,605390138⟩,
⟨128,841645282,841645832⟩]
theorem checked15567 : checkPrefixCuts (2^48) 2044329985 9 Manual.Count131072.C015567.packed 128 cuts15567 = true := by
 decide +kernel
def pointBounds15567 : List (Nat × Nat × Nat) := [(2044359680,96755641785649,96756020140774),(2044424192,96756057445952,96756435801346)]
theorem point_links_checked15567 : (cuts15567.take 2).map (fun c => (2044329985-1+2*2^9*c.k,96755452056208+c.lower,96755830411208+c.upper)) = pointBounds15567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000173
