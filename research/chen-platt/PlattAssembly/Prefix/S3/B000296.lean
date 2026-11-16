import PlattAssemblyKernel
import PlattCertificates.Count131072.C029472
import PlattCertificates.Count131072.C029473
import PlattCertificates.Count131072.C029474
import PlattCertificates.Count131072.C029475
import PlattCertificates.Count131072.C029476
import PlattCertificates.Count131072.C029477
import PlattCertificates.Count131072.C029478
import PlattCertificates.Count131072.C029479
import PlattCertificates.Count131072.C029480
import PlattCertificates.Count131072.C029481
import PlattCertificates.Count131072.C029482
import PlattCertificates.Count131072.C029483
import PlattCertificates.Count131072.C029484
import PlattCertificates.Count131072.C029485
import PlattCertificates.Count131072.C029486
import PlattCertificates.Count131072.C029487
import PlattCertificates.Count131072.C029488
import PlattCertificates.Count131072.C029489
import PlattCertificates.Count131072.C029490
import PlattCertificates.Count131072.C029491
import PlattCertificates.Count131072.C029492
import PlattCertificates.Count131072.C029493
import PlattCertificates.Count131072.C029494
import PlattCertificates.Count131072.C029495
import PlattCertificates.Count131072.C029496
import PlattCertificates.Count131072.C029497
import PlattCertificates.Count131072.C029498
import PlattCertificates.Count131072.C029499
import PlattCertificates.Count131072.C029500
import PlattCertificates.Count131072.C029501
import PlattCertificates.Count131072.C029502
import PlattCertificates.Count131072.C029503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000296
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29472 : List PrefixCut := [⟨24,81307406,81307453⟩,
⟨128,429096300,429096542⟩]
theorem checked29472 : checkPrefixCuts (2^48) 3866886145 9 Manual.Count131072.C029472.packed 128 cuts29472 = true := by
 decide +kernel
def pointBounds29472 : List (Nat × Nat × Nat) := [(3866910720,105002005919914,105002389114369)]
theorem point_links_checked29472 : (cuts29472.take 1).map (fun c => (3866886145-1+2*2^9*c.k,105001924612508+c.lower,105002307806916+c.upper)) = pointBounds29472 := by
 decide +kernel
def cuts29473 : List PrefixCut := [⟨15,49568959,49568989⟩,
⟨128,431629305,431629547⟩]
theorem checked29473 : checkPrefixCuts (2^48) 3867017217 9 Manual.Count131072.C029473.packed 128 cuts29473 = true := by
 decide +kernel
def pointBounds29473 : List (Nat × Nat × Nat) := [(3867032576,105002403277767,105002786472447)]
theorem point_links_checked29473 : (cuts29473.take 1).map (fun c => (3867017217-1+2*2^9*c.k,105002353708808+c.lower,105002736903458+c.upper)) = pointBounds29473 := by
 decide +kernel
def cuts29474 : List PrefixCut := [⟨6,20088966,20088978⟩,
⟨125,424700283,424700520⟩,
⟨128,434234952,434235194⟩]
theorem checked29474 : checkPrefixCuts (2^48) 3867148289 9 Manual.Count131072.C029474.packed 128 cuts29474 = true := by
 decide +kernel
def pointBounds29474 : List (Nat × Nat × Nat) := [(3867154432,105002805427079,105003188621983),(3867276288,105003210038396,105003593233525)]
theorem point_links_checked29474 : (cuts29474.take 2).map (fun c => (3867148289-1+2*2^9*c.k,105002785338113+c.lower,105003168533005+c.upper)) = pointBounds29474 := by
 decide +kernel
def cuts29475 : List PrefixCut := [⟨116,389168449,389168662⟩,
⟨128,431527197,431527432⟩]
theorem checked29475 : checkPrefixCuts (2^48) 3867279361 9 Manual.Count131072.C029475.packed 128 cuts29475 = true := by
 decide +kernel
def pointBounds29475 : List (Nat × Nat × Nat) := [(3867398144,105003608741514,105003991936861)]
theorem point_links_checked29475 : (cuts29475.take 1).map (fun c => (3867279361-1+2*2^9*c.k,105003219573065+c.lower,105003602768199+c.upper)) = pointBounds29475 := by
 decide +kernel
def cuts29476 : List PrefixCut := [⟨107,357787502,357787707⟩,
⟨128,433113734,433113982⟩]
theorem checked29476 : checkPrefixCuts (2^48) 3867410433 9 Manual.Count131072.C029476.packed 128 cuts29476 = true := by
 decide +kernel
def pointBounds29476 : List (Nat × Nat × Nat) := [(3867520000,105004008887764,105004392083338)]
theorem point_links_checked29476 : (cuts29476.take 1).map (fun c => (3867410433-1+2*2^9*c.k,105003651100262+c.lower,105004034295631+c.upper)) = pointBounds29476 := by
 decide +kernel
def cuts29477 : List PrefixCut := [⟨98,332376335,332376522⟩,
⟨128,435500766,435501010⟩]
theorem checked29477 : checkPrefixCuts (2^48) 3867541505 9 Manual.Count131072.C029477.packed 128 cuts29477 = true := by
 decide +kernel
def pointBounds29477 : List (Nat × Nat × Nat) := [(3867641856,105004416590331,105004799786135)]
theorem point_links_checked29477 : (cuts29477.take 1).map (fun c => (3867541505-1+2*2^9*c.k,105004084213996+c.lower,105004467409613+c.upper)) = pointBounds29477 := by
 decide +kernel
def cuts29478 : List PrefixCut := [⟨89,298670393,298670561⟩,
⟨128,430828347,430828588⟩]
theorem checked29478 : checkPrefixCuts (2^48) 3867672577 9 Manual.Count131072.C029478.packed 128 cuts29478 = true := by
 decide +kernel
def pointBounds29478 : List (Nat × Nat × Nat) := [(3867763712,105004818385155,105005201581184)]
theorem point_links_checked29478 : (cuts29478.take 1).map (fun c => (3867672577-1+2*2^9*c.k,105004519714762+c.lower,105004902910623+c.upper)) = pointBounds29478 := by
 decide +kernel
def cuts29479 : List PrefixCut := [⟨80,266131067,266131220⟩,
⟨128,429285499,429285742⟩]
theorem checked29479 : checkPrefixCuts (2^48) 3867803649 9 Manual.Count131072.C029479.packed 128 cuts29479 = true := by
 decide +kernel
def pointBounds29479 : List (Nat × Nat × Nat) := [(3867885568,105005216674176,105005599870431)]
theorem point_links_checked29479 : (cuts29479.take 1).map (fun c => (3867803649-1+2*2^9*c.k,105004950543109+c.lower,105005333739211+c.upper)) = pointBounds29479 := by
 decide +kernel
def cuts29480 : List PrefixCut := [⟨71,242544678,242544813⟩,
⟨128,434437718,434437966⟩]
theorem checked29480 : checkPrefixCuts (2^48) 3867934721 9 Manual.Count131072.C029480.packed 128 cuts29480 = true := by
 decide +kernel
def pointBounds29480 : List (Nat × Nat × Nat) := [(3868007424,105005622373286,105006005569766)]
theorem point_links_checked29480 : (cuts29480.take 1).map (fun c => (3867934721-1+2*2^9*c.k,105005379828608+c.lower,105005763024953+c.upper)) = pointBounds29480 := by
 decide +kernel
def cuts29481 : List PrefixCut := [⟨62,207607952,207608064⟩,
⟨128,427873891,427874129⟩]
theorem checked29481 : checkPrefixCuts (2^48) 3868065793 9 Manual.Count131072.C029481.packed 128 cuts29481 = true := by
 decide +kernel
def pointBounds29481 : List (Nat × Nat × Nat) := [(3868129280,105006021874278,105006405070983)]
theorem point_links_checked29481 : (cuts29481.take 1).map (fun c => (3868065793-1+2*2^9*c.k,105005814266326+c.lower,105006197462919+c.upper)) = pointBounds29481 := by
 decide +kernel
def cuts29482 : List PrefixCut := [⟨53,177039500,177039600⟩,
⟨128,433098443,433098689⟩]
theorem checked29482 : checkPrefixCuts (2^48) 3868196865 9 Manual.Count131072.C029482.packed 128 cuts29482 = true := by
 decide +kernel
def pointBounds29482 : List (Nat × Nat × Nat) := [(3868251136,105006419179717,105006802376648)]
theorem point_links_checked29482 : (cuts29482.take 1).map (fun c => (3868196865-1+2*2^9*c.k,105006242140217+c.lower,105006625337048+c.upper)) = pointBounds29482 := by
 decide +kernel
def cuts29483 : List PrefixCut := [⟨44,147709998,147710081⟩,
⟨128,436285355,436285601⟩]
theorem checked29483 : checkPrefixCuts (2^48) 3868327937 9 Manual.Count131072.C029483.packed 128 cuts29483 = true := by
 decide +kernel
def pointBounds29483 : List (Nat × Nat × Nat) := [(3868372992,105006822948658,105007206145818)]
theorem point_links_checked29483 : (cuts29483.take 1).map (fun c => (3868327937-1+2*2^9*c.k,105006675238660+c.lower,105007058435737+c.upper)) = pointBounds29483 := by
 decide +kernel
def cuts29484 : List PrefixCut := [⟨35,120710787,120710854⟩,
⟨128,434597138,434597377⟩]
theorem checked29484 : checkPrefixCuts (2^48) 3868459009 9 Manual.Count131072.C029484.packed 128 cuts29484 = true := by
 decide +kernel
def pointBounds29484 : List (Nat × Nat × Nat) := [(3868494848,105007232234802,105007615432192)]
theorem point_links_checked29484 : (cuts29484.take 1).map (fun c => (3868459009-1+2*2^9*c.k,105007111524015+c.lower,105007494721338+c.upper)) = pointBounds29484 := by
 decide +kernel
def cuts29485 : List PrefixCut := [⟨26,87674353,87674399⟩,
⟨128,437347194,437347431⟩]
theorem checked29485 : checkPrefixCuts (2^48) 3868590081 9 Manual.Count131072.C029485.packed 128 cuts29485 = true := by
 decide +kernel
def pointBounds29485 : List (Nat × Nat × Nat) := [(3868616704,105007633795506,105008016993114)]
theorem point_links_checked29485 : (cuts29485.take 1).map (fun c => (3868590081-1+2*2^9*c.k,105007546121153+c.lower,105007929318715+c.upper)) = pointBounds29485 := by
 decide +kernel
def cuts29486 : List PrefixCut := [⟨17,55440382,55440415⟩,
⟨128,430493393,430493636⟩]
theorem checked29486 : checkPrefixCuts (2^48) 3868721153 9 Manual.Count131072.C029486.packed 128 cuts29486 = true := by
 decide +kernel
def pointBounds29486 : List (Nat × Nat × Nat) := [(3868738560,105008038908729,105008422106561)]
theorem point_links_checked29486 : (cuts29486.take 1).map (fun c => (3868721153-1+2*2^9*c.k,105007983468347+c.lower,105008366666146+c.upper)) = pointBounds29486 := by
 decide +kernel
def cuts29487 : List PrefixCut := [⟨8,26191452,26191466⟩,
⟨127,427714209,427714447⟩,
⟨128,430842530,430842770⟩]
theorem checked29487 : checkPrefixCuts (2^48) 3868852225 9 Manual.Count131072.C029487.packed 128 cuts29487 = true := by
 decide +kernel
def pointBounds29487 : List (Nat × Nat × Nat) := [(3868860416,105008440153192,105008823351248),(3868982272,105008841675949,105009224874229)]
theorem point_links_checked29487 : (cuts29487.take 2).map (fun c => (3868852225-1+2*2^9*c.k,105008413961740+c.lower,105008797159782+c.upper)) = pointBounds29487 := by
 decide +kernel
def cuts29488 : List PrefixCut := [⟨118,401146338,401146568⟩,
⟨128,437229982,437230232⟩]
theorem checked29488 : checkPrefixCuts (2^48) 3868983297 9 Manual.Count131072.C029488.packed 128 cuts29488 = true := by
 decide +kernel
def pointBounds29488 : List (Nat × Nat × Nat) := [(3869104128,105009245950608,105009629149120)]
theorem point_links_checked29488 : (cuts29488.take 1).map (fun c => (3868983297-1+2*2^9*c.k,105008844804270+c.lower,105009228002552+c.upper)) = pointBounds29488 := by
 decide +kernel
def cuts29489 : List PrefixCut := [⟨109,370142478,370142689⟩,
⟨128,435178204,435178451⟩]
theorem checked29489 : checkPrefixCuts (2^48) 3869114369 9 Manual.Count131072.C029489.packed 128 cuts29489 = true := by
 decide +kernel
def pointBounds29489 : List (Nat × Nat × Nat) := [(3869225984,105009652176730,105010035375473)]
theorem point_links_checked29489 : (cuts29489.take 1).map (fun c => (3869114369-1+2*2^9*c.k,105009282034252+c.lower,105009665232784+c.upper)) = pointBounds29489 := by
 decide +kernel
def cuts29490 : List PrefixCut := [⟨100,332739057,332739244⟩,
⟨128,423596966,423597205⟩]
theorem checked29490 : checkPrefixCuts (2^48) 3869245441 9 Manual.Count131072.C029490.packed 128 cuts29490 = true := by
 decide +kernel
def pointBounds29490 : List (Nat × Nat × Nat) := [(3869347840,105010049951513,105010433150479)]
theorem point_links_checked29490 : (cuts29490.take 1).map (fun c => (3869245441-1+2*2^9*c.k,105009717212456+c.lower,105010100411235+c.upper)) = pointBounds29490 := by
 decide +kernel
def cuts29491 : List PrefixCut := [⟨91,306322348,306322520⟩,
⟨128,427583518,427583758⟩]
theorem checked29491 : checkPrefixCuts (2^48) 3869376513 9 Manual.Count131072.C029491.packed 128 cuts29491 = true := by
 decide +kernel
def pointBounds29491 : List (Nat × Nat × Nat) := [(3869469696,105010447131770,105010830330960)]
theorem point_links_checked29491 : (cuts29491.take 1).map (fun c => (3869376513-1+2*2^9*c.k,105010140809422+c.lower,105010524008440+c.upper)) = pointBounds29491 := by
 decide +kernel
def cuts29492 : List PrefixCut := [⟨82,280198349,280198500⟩,
⟨128,437170767,437171007⟩]
theorem checked29492 : checkPrefixCuts (2^48) 3869507585 9 Manual.Count131072.C029492.packed 128 cuts29492 = true := by
 decide +kernel
def pointBounds29492 : List (Nat × Nat × Nat) := [(3869591552,105010848591289,105011231790698)]
theorem point_links_checked29492 : (cuts29492.take 1).map (fun c => (3869507585-1+2*2^9*c.k,105010568392940+c.lower,105010951592198+c.upper)) = pointBounds29492 := by
 decide +kernel
def cuts29493 : List PrefixCut := [⟨73,246002045,246002184⟩,
⟨128,432209775,432210018⟩]
theorem checked29493 : checkPrefixCuts (2^48) 3869638657 9 Manual.Count131072.C029493.packed 128 cuts29493 = true := by
 decide +kernel
def pointBounds29493 : List (Nat × Nat × Nat) := [(3869713408,105011251565752,105011634765389)]
theorem point_links_checked29493 : (cuts29493.take 1).map (fun c => (3869638657-1+2*2^9*c.k,105011005563707+c.lower,105011388763205+c.upper)) = pointBounds29493 := by
 decide +kernel
def cuts29494 : List PrefixCut := [⟨64,217917792,217917910⟩,
⟨128,431540517,431540756⟩]
theorem checked29494 : checkPrefixCuts (2^48) 3869769729 9 Manual.Count131072.C029494.packed 128 cuts29494 = true := by
 decide +kernel
def pointBounds29494 : List (Nat × Nat × Nat) := [(3869835264,105011655691274,105012038891133)]
theorem point_links_checked29494 : (cuts29494.take 1).map (fun c => (3869769729-1+2*2^9*c.k,105011437773482+c.lower,105011820973223+c.upper)) = pointBounds29494 := by
 decide +kernel
def cuts29495 : List PrefixCut := [⟨55,186489650,186489754⟩,
⟨128,432980571,432980813⟩]
theorem checked29495 : checkPrefixCuts (2^48) 3869900801 9 Manual.Count131072.C029495.packed 128 cuts29495 = true := by
 decide +kernel
def pointBounds29495 : List (Nat × Nat × Nat) := [(3869957120,105012055803649,105012439003733)]
theorem point_links_checked29495 : (cuts29495.take 1).map (fun c => (3869900801-1+2*2^9*c.k,105011869313999+c.lower,105012252513979+c.upper)) = pointBounds29495 := by
 decide +kernel
def cuts29496 : List PrefixCut := [⟨46,156590910,156590995⟩,
⟨128,429547557,429547801⟩]
theorem checked29496 : checkPrefixCuts (2^48) 3870031873 9 Manual.Count131072.C029496.packed 128 cuts29496 = true := by
 decide +kernel
def pointBounds29496 : List (Nat × Nat × Nat) := [(3870078976,105012458885480,105012842085787)]
theorem point_links_checked29496 : (cuts29496.take 1).map (fun c => (3870031873-1+2*2^9*c.k,105012302294570+c.lower,105012685494792+c.upper)) = pointBounds29496 := by
 decide +kernel
def cuts29497 : List PrefixCut := [⟨37,123057654,123057721⟩,
⟨128,429969303,429969539⟩]
theorem checked29497 : checkPrefixCuts (2^48) 3870162945 9 Manual.Count131072.C029497.packed 128 cuts29497 = true := by
 decide +kernel
def pointBounds29497 : List (Nat × Nat × Nat) := [(3870200832,105012854899781,105013238100314)]
theorem point_links_checked29497 : (cuts29497.take 1).map (fun c => (3870162945-1+2*2^9*c.k,105012731842127+c.lower,105013115042593+c.upper)) = pointBounds29497 := by
 decide +kernel
def cuts29498 : List PrefixCut := [⟨28,96435650,96435705⟩,
⟨128,439118249,439118490⟩]
theorem checked29498 : checkPrefixCuts (2^48) 3870294017 9 Manual.Count131072.C029498.packed 128 cuts29498 = true := by
 decide +kernel
def pointBounds29498 : List (Nat × Nat × Nat) := [(3870322688,105013258247080,105013641447837)]
theorem point_links_checked29498 : (cuts29498.take 1).map (fun c => (3870294017-1+2*2^9*c.k,105013161811430+c.lower,105013545012132+c.upper)) = pointBounds29498 := by
 decide +kernel
def cuts29499 : List PrefixCut := [⟨19,63924713,63924749⟩,
⟨128,431903715,431903951⟩]
theorem checked29499 : checkPrefixCuts (2^48) 3870425089 9 Manual.Count131072.C029499.packed 128 cuts29499 = true := by
 decide +kernel
def pointBounds29499 : List (Nat × Nat × Nat) := [(3870444544,105013664854392,105014048055371)]
theorem point_links_checked29499 : (cuts29499.take 1).map (fun c => (3870425089-1+2*2^9*c.k,105013600929679+c.lower,105013984130622+c.upper)) = pointBounds29499 := by
 decide +kernel
def cuts29500 : List PrefixCut := [⟨10,33379391,33379410⟩,
⟨128,435816021,435816269⟩]
theorem checked29500 : checkPrefixCuts (2^48) 3870556161 9 Manual.Count131072.C029500.packed 128 cuts29500 = true := by
 decide +kernel
def pointBounds29500 : List (Nat × Nat × Nat) := [(3870566400,105014066212785,105014449413983)]
theorem point_links_checked29500 : (cuts29500.take 1).map (fun c => (3870556161-1+2*2^9*c.k,105014032833394+c.lower,105014416034573+c.upper)) = pointBounds29500 := by
 decide +kernel
def cuts29501 : List PrefixCut := [⟨1,3563261,3563263⟩,
⟨120,397406380,397406599⟩,
⟨128,423148282,423148514⟩]
theorem checked29501 : checkPrefixCuts (2^48) 3870687233 9 Manual.Count131072.C029501.packed 128 cuts29501 = true := by
 decide +kernel
def pointBounds29501 : List (Nat × Nat × Nat) := [(3870688256,105014472212676,105014855414105),(3870810112,105014866055795,105015249257441)]
theorem point_links_checked29501 : (cuts29501.take 2).map (fun c => (3870687233-1+2*2^9*c.k,105014468649415+c.lower,105014851850842+c.upper)) = pointBounds29501 := by
 decide +kernel
def cuts29502 : List PrefixCut := [⟨111,372015549,372015752⟩,
⟨128,431569023,431569259⟩]
theorem checked29502 : checkPrefixCuts (2^48) 3870818305 9 Manual.Count131072.C029502.packed 128 cuts29502 = true := by
 decide +kernel
def pointBounds29502 : List (Nat × Nat × Nat) := [(3870931968,105015263813246,105015647015108)]
theorem point_links_checked29502 : (cuts29502.take 1).map (fun c => (3870818305-1+2*2^9*c.k,105014891797697+c.lower,105015274999356+c.upper)) = pointBounds29502 := by
 decide +kernel
def cuts29503 : List PrefixCut := [⟨102,342118043,342118232⟩,
⟨128,429154872,429155111⟩]
theorem checked29503 : checkPrefixCuts (2^48) 3870949377 9 Manual.Count131072.C029503.packed 128 cuts29503 = true := by
 decide +kernel
def pointBounds29503 : List (Nat × Nat × Nat) := [(3871053824,105015665484763,105016048686847)]
theorem point_links_checked29503 : (cuts29503.take 1).map (fun c => (3870949377-1+2*2^9*c.k,105015323366720+c.lower,105015706568615+c.upper)) = pointBounds29503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000296
