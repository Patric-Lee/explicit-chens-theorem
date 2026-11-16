import PlattAssemblyKernel
import PlattCertificates.Count131072.C025344
import PlattCertificates.Count131072.C025345
import PlattCertificates.Count131072.C025346
import PlattCertificates.Count131072.C025347
import PlattCertificates.Count131072.C025348
import PlattCertificates.Count131072.C025349
import PlattCertificates.Count131072.C025350
import PlattCertificates.Count131072.C025351
import PlattCertificates.Count131072.C025352
import PlattCertificates.Count131072.C025353
import PlattCertificates.Count131072.C025354
import PlattCertificates.Count131072.C025355
import PlattCertificates.Count131072.C025356
import PlattCertificates.Count131072.C025357
import PlattCertificates.Count131072.C025358
import PlattCertificates.Count131072.C025359
import PlattCertificates.Count131072.C025360
import PlattCertificates.Count131072.C025361
import PlattCertificates.Count131072.C025362
import PlattCertificates.Count131072.C025363
import PlattCertificates.Count131072.C025364
import PlattCertificates.Count131072.C025365
import PlattCertificates.Count131072.C025366
import PlattCertificates.Count131072.C025367
import PlattCertificates.Count131072.C025368
import PlattCertificates.Count131072.C025369
import PlattCertificates.Count131072.C025370
import PlattCertificates.Count131072.C025371
import PlattCertificates.Count131072.C025372
import PlattCertificates.Count131072.C025373
import PlattCertificates.Count131072.C025374
import PlattCertificates.Count131072.C025375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000167
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25344 : List PrefixCut := [⟨18,73715322,73715363⟩,
⟨120,478845863,478846127⟩,
⟨128,510666735,510667017⟩]
theorem checked25344 : checkPrefixCuts (2^48) 3325820929 9 Manual.Count131072.C025344.packed 128 cuts25344 = true := by
 decide +kernel
def pointBounds25344 : List (Nat × Nat × Nat) := [(3325839360,103073404570297,103073786685237),(3325943808,103073809700838,103074191816001)]
theorem point_links_checked25344 : (cuts25344.take 2).map (fun c => (3325820929-1+2*2^9*c.k,103073330854975+c.lower,103073712969874+c.upper)) = pointBounds25344 := by
 decide +kernel
def cuts25345 : List PrefixCut := [⟨94,367203733,367203941⟩,
⟨128,499475708,499475991⟩]
theorem checked25345 : checkPrefixCuts (2^48) 3325952001 9 Manual.Count131072.C025345.packed 128 cuts25345 = true := by
 decide +kernel
def pointBounds25345 : List (Nat × Nat × Nat) := [(3326048256,103074208725443,103074590840832)]
theorem point_links_checked25345 : (cuts25345.take 1).map (fun c => (3325952001-1+2*2^9*c.k,103073841521710+c.lower,103074223636891+c.upper)) = pointBounds25345 := by
 decide +kernel
def cuts25346 : List PrefixCut := [⟨68,268094077,268094220⟩,
⟨128,504448880,504449158⟩]
theorem checked25346 : checkPrefixCuts (2^48) 3326083073 9 Manual.Count131072.C025346.packed 128 cuts25346 = true := by
 decide +kernel
def pointBounds25346 : List (Nat × Nat × Nat) := [(3326152704,103074609091495,103074991207102)]
theorem point_links_checked25346 : (cuts25346.take 1).map (fun c => (3326083073-1+2*2^9*c.k,103074340997418+c.lower,103074723112882+c.upper)) = pointBounds25346 := by
 decide +kernel
def cuts25347 : List PrefixCut := [⟨42,167891346,167891440⟩,
⟨128,504090481,504090755⟩]
theorem checked25347 : checkPrefixCuts (2^48) 3326214145 9 Manual.Count131072.C025347.packed 128 cuts25347 = true := by
 decide +kernel
def pointBounds25347 : List (Nat × Nat × Nat) := [(3326257152,103075013337644,103075395453480)]
theorem point_links_checked25347 : (cuts25347.take 1).map (fun c => (3326214145-1+2*2^9*c.k,103074845446298+c.lower,103075227562040+c.upper)) = pointBounds25347 := by
 decide +kernel
def cuts25348 : List PrefixCut := [⟨16,63887843,63887877⟩,
⟨118,465485493,465485752⟩,
⟨128,503224527,503224806⟩]
theorem checked25348 : checkPrefixCuts (2^48) 3326345217 9 Manual.Count131072.C025348.packed 128 cuts25348 = true := by
 decide +kernel
def pointBounds25348 : List (Nat × Nat × Nat) := [(3326361600,103075413424622,103075795540672),(3326466048,103075815022272,103076197138547)]
theorem point_links_checked25348 : (cuts25348.take 2).map (fun c => (3326345217-1+2*2^9*c.k,103075349536779+c.lower,103075731652795+c.upper)) = pointBounds25348 := by
 decide +kernel
def cuts25349 : List PrefixCut := [⟨92,360545977,360546180⟩,
⟨128,503289248,503289528⟩]
theorem checked25349 : checkPrefixCuts (2^48) 3326476289 9 Manual.Count131072.C025349.packed 128 cuts25349 = true := by
 decide +kernel
def pointBounds25349 : List (Nat × Nat × Nat) := [(3326570496,103076213307283,103076595423781)]
theorem point_links_checked25349 : (cuts25349.take 1).map (fun c => (3326476289-1+2*2^9*c.k,103075852761306+c.lower,103076234877601+c.upper)) = pointBounds25349 := by
 decide +kernel
def cuts25350 : List PrefixCut := [⟨66,263736644,263736792⟩,
⟨128,512830465,512830751⟩]
theorem checked25350 : checkPrefixCuts (2^48) 3326607361 9 Manual.Count131072.C025350.packed 128 cuts25350 = true := by
 decide +kernel
def pointBounds25350 : List (Nat × Nat × Nat) := [(3326674944,103076619787198,103077001903921)]
theorem point_links_checked25350 : (cuts25350.take 1).map (fun c => (3326607361-1+2*2^9*c.k,103076356050554+c.lower,103076738167129+c.upper)) = pointBounds25350 := by
 decide +kernel
def cuts25351 : List PrefixCut := [⟨40,159404019,159404107⟩,
⟨128,510102869,510103149⟩]
theorem checked25351 : checkPrefixCuts (2^48) 3326738433 9 Manual.Count131072.C025351.packed 128 cuts25351 = true := by
 decide +kernel
def pointBounds25351 : List (Nat × Nat × Nat) := [(3326779392,103077028285038,103077410401987)]
theorem point_links_checked25351 : (cuts25351.take 1).map (fun c => (3326738433-1+2*2^9*c.k,103076868881019+c.lower,103077250997880+c.upper)) = pointBounds25351 := by
 decide +kernel
def cuts25352 : List PrefixCut := [⟨14,54909526,54909556⟩,
⟨116,454159745,454159996⟩,
⟨128,501030003,501030281⟩]
theorem checked25352 : checkPrefixCuts (2^48) 3326869505 9 Manual.Count131072.C025352.packed 128 cuts25352 = true := by
 decide +kernel
def pointBounds25352 : List (Nat × Nat × Nat) := [(3326883840,103077433893414,103077816010585),(3326988288,103077833143633,103078215261025)]
theorem point_links_checked25352 : (cuts25352.take 2).map (fun c => (3326869505-1+2*2^9*c.k,103077378983888+c.lower,103077761101029+c.upper)) = pointBounds25352 := by
 decide +kernel
def cuts25353 : List PrefixCut := [⟨90,357612808,357613006⟩,
⟨128,507693853,507694130⟩]
theorem checked25353 : checkPrefixCuts (2^48) 3327000577 9 Manual.Count131072.C025353.packed 128 cuts25353 = true := by
 decide +kernel
def pointBounds25353 : List (Nat × Nat × Nat) := [(3327092736,103078237626699,103078619744316)]
theorem point_links_checked25353 : (cuts25353.take 1).map (fun c => (3327000577-1+2*2^9*c.k,103077880013891+c.lower,103078262131310+c.upper)) = pointBounds25353 := by
 decide +kernel
def cuts25354 : List PrefixCut := [⟨64,257604022,257604167⟩,
⟨128,509619606,509619890⟩]
theorem checked25354 : checkPrefixCuts (2^48) 3327131649 9 Manual.Count131072.C025354.packed 128 cuts25354 = true := by
 decide +kernel
def pointBounds25354 : List (Nat × Nat × Nat) := [(3327197184,103078645311766,103079027429607)]
theorem point_links_checked25354 : (cuts25354.take 1).map (fun c => (3327131649-1+2*2^9*c.k,103078387707744+c.lower,103078769825440+c.upper)) = pointBounds25354 := by
 decide +kernel
def cuts25355 : List PrefixCut := [⟨38,154726159,154726249⟩,
⟨128,508076911,508077197⟩]
theorem checked25355 : checkPrefixCuts (2^48) 3327262721 9 Manual.Count131072.C025355.packed 128 cuts25355 = true := by
 decide +kernel
def pointBounds25355 : List (Nat × Nat × Nat) := [(3327301632,103079052053509,103079434171579)]
theorem point_links_checked25355 : (cuts25355.take 1).map (fun c => (3327262721-1+2*2^9*c.k,103078897327350+c.lower,103079279445330+c.upper)) = pointBounds25355 := by
 decide +kernel
def cuts25356 : List PrefixCut := [⟨12,46949139,46949166⟩,
⟨114,450704653,450704904⟩,
⟨128,506957039,506957321⟩]
theorem checked25356 : checkPrefixCuts (2^48) 3327393793 9 Manual.Count131072.C025356.packed 128 cuts25356 = true := by
 decide +kernel
def pointBounds25356 : List (Nat × Nat × Nat) := [(3327406080,103079452353400,103079834471693),(3327510528,103079856108914,103080238227431)]
theorem point_links_checked25356 : (cuts25356.take 2).map (fun c => (3327393793-1+2*2^9*c.k,103079405404261+c.lower,103079787522527+c.upper)) = pointBounds25356 := by
 decide +kernel
def cuts25357 : List PrefixCut := [⟨88,354426774,354426972⟩,
⟨128,511251193,511251477⟩]
theorem checked25357 : checkPrefixCuts (2^48) 3327524865 9 Manual.Count131072.C025357.packed 128 cuts25357 = true := by
 decide +kernel
def pointBounds25357 : List (Nat × Nat × Nat) := [(3327614976,103080266788074,103080648906820)]
theorem point_links_checked25357 : (cuts25357.take 1).map (fun c => (3327524865-1+2*2^9*c.k,103079912361300+c.lower,103080294479848+c.upper)) = pointBounds25357 := by
 decide +kernel
def cuts25358 : List PrefixCut := [⟨62,234133312,234133444⟩,
⟨128,494736804,494737086⟩]
theorem checked25358 : checkPrefixCuts (2^48) 3327655937 9 Manual.Count131072.C025358.packed 128 cuts25358 = true := by
 decide +kernel
def pointBounds25358 : List (Nat × Nat × Nat) := [(3327719424,103080657745805,103081039864769)]
theorem point_links_checked25358 : (cuts25358.take 1).map (fun c => (3327655937-1+2*2^9*c.k,103080423612493+c.lower,103080805731325+c.upper)) = pointBounds25358 := by
 decide +kernel
def cuts25359 : List PrefixCut := [⟨36,145566878,145566957⟩,
⟨128,502583565,502583841⟩]
theorem checked25359 : checkPrefixCuts (2^48) 3327787009 9 Manual.Count131072.C025359.packed 128 cuts25359 = true := by
 decide +kernel
def pointBounds25359 : List (Nat × Nat × Nat) := [(3327823872,103081063916175,103081446035368)]
theorem point_links_checked25359 : (cuts25359.take 1).map (fun c => (3327787009-1+2*2^9*c.k,103080918349297+c.lower,103081300468411+c.upper)) = pointBounds25359 := by
 decide +kernel
def cuts25360 : List PrefixCut := [⟨10,41697817,41697837⟩,
⟨112,442175989,442176236⟩,
⟨128,507384665,507384950⟩]
theorem checked25360 : checkPrefixCuts (2^48) 3327918081 9 Manual.Count131072.C025360.packed 128 cuts25360 = true := by
 decide +kernel
def pointBounds25360 : List (Nat × Nat × Nat) := [(3327928320,103081462630679,103081844750089),(3328032768,103081863108851,103082245228488)]
theorem point_links_checked25360 : (cuts25360.take 2).map (fun c => (3327918081-1+2*2^9*c.k,103081420932862+c.lower,103081803052252+c.upper)) = pointBounds25360 := by
 decide +kernel
def cuts25361 : List PrefixCut := [⟨86,335933589,335933780⟩,
⟨128,498484374,498484660⟩]
theorem checked25361 : checkPrefixCuts (2^48) 3328049153 9 Manual.Count131072.C025361.packed 128 cuts25361 = true := by
 decide +kernel
def pointBounds25361 : List (Nat × Nat × Nat) := [(3328137216,103082264251116,103082646370982)]
theorem point_links_checked25361 : (cuts25361.take 1).map (fun c => (3328049153-1+2*2^9*c.k,103081928317527+c.lower,103082310437202+c.upper)) = pointBounds25361 := by
 decide +kernel
def cuts25362 : List PrefixCut := [⟨60,243822339,243822476⟩,
⟨128,517324216,517324505⟩]
theorem checked25362 : checkPrefixCuts (2^48) 3328180225 9 Manual.Count131072.C025362.packed 128 cuts25362 = true := by
 decide +kernel
def pointBounds25362 : List (Nat × Nat × Nat) := [(3328241664,103082670624240,103083052744338)]
theorem point_links_checked25362 : (cuts25362.take 1).map (fun c => (3328180225-1+2*2^9*c.k,103082426801901+c.lower,103082808921862+c.upper)) = pointBounds25362 := by
 decide +kernel
def cuts25363 : List PrefixCut := [⟨34,135564804,135564881⟩,
⟨128,509692701,509692991⟩]
theorem checked25363 : checkPrefixCuts (2^48) 3328311297 9 Manual.Count131072.C025363.packed 128 cuts25363 = true := by
 decide +kernel
def pointBounds25363 : List (Nat × Nat × Nat) := [(3328346112,103083079690921,103083461811248)]
theorem point_links_checked25363 : (cuts25363.take 1).map (fun c => (3328311297-1+2*2^9*c.k,103082944126117+c.lower,103083326246367+c.upper)) = pointBounds25363 := by
 decide +kernel
def cuts25364 : List PrefixCut := [⟨8,30951320,30951337⟩,
⟨110,430774723,430774965⟩,
⟨128,500624140,500624420⟩]
theorem checked25364 : checkPrefixCuts (2^48) 3328442369 9 Manual.Count131072.C025364.packed 128 cuts25364 = true := by
 decide +kernel
def pointBounds25364 : List (Nat × Nat × Nat) := [(3328450560,103083484770138,103083866890695),(3328555008,103083884593541,103084266714323)]
theorem point_links_checked25364 : (cuts25364.take 2).map (fun c => (3328442369-1+2*2^9*c.k,103083453818818+c.lower,103083835939358+c.upper)) = pointBounds25364 := by
 decide +kernel
def cuts25365 : List PrefixCut := [⟨84,330468766,330468947⟩,
⟨128,502633879,502634157⟩]
theorem checked25365 : checkPrefixCuts (2^48) 3328573441 9 Manual.Count131072.C025365.packed 128 cuts25365 = true := by
 decide +kernel
def pointBounds25365 : List (Nat × Nat × Nat) := [(3328659456,103084284911724,103084667032725)]
theorem point_links_checked25365 : (cuts25365.take 1).map (fun c => (3328573441-1+2*2^9*c.k,103083954442958+c.lower,103084336563778+c.upper)) = pointBounds25365 := by
 decide +kernel
def cuts25366 : List PrefixCut := [⟨58,229916319,229916440⟩,
⟨128,506588360,506588636⟩]
theorem checked25366 : checkPrefixCuts (2^48) 3328704513 9 Manual.Count131072.C025366.packed 128 cuts25366 = true := by
 decide +kernel
def pointBounds25366 : List (Nat × Nat × Nat) := [(3328763904,103084686993156,103085069114375)]
theorem point_links_checked25366 : (cuts25366.take 1).map (fun c => (3328704513-1+2*2^9*c.k,103084457076837+c.lower,103084839197935+c.upper)) = pointBounds25366 := by
 decide +kernel
def cuts25367 : List PrefixCut := [⟨32,128271676,128271750⟩,
⟨128,506230213,506230498⟩]
theorem checked25367 : checkPrefixCuts (2^48) 3328835585 9 Manual.Count131072.C025367.packed 128 cuts25367 = true := by
 decide +kernel
def pointBounds25367 : List (Nat × Nat × Nat) := [(3328868352,103085091936873,103085474058321)]
theorem point_links_checked25367 : (cuts25367.take 1).map (fun c => (3328835585-1+2*2^9*c.k,103084963665197+c.lower,103085345786571+c.upper)) = pointBounds25367 := by
 decide +kernel
def cuts25368 : List PrefixCut := [⟨6,24182203,24182217⟩,
⟨108,431890737,431890968⟩,
⟨128,512805248,512805523⟩]
theorem checked25368 : checkPrefixCuts (2^48) 3328966657 9 Manual.Count131072.C025368.packed 128 cuts25368 = true := by
 decide +kernel
def pointBounds25368 : List (Nat × Nat × Nat) := [(3328972800,103085494077613,103085876199286),(3329077248,103085901786147,103086283908037)]
theorem point_links_checked25368 : (cuts25368.take 2).map (fun c => (3328966657-1+2*2^9*c.k,103085469895410+c.lower,103085852017069+c.upper)) = pointBounds25368 := by
 decide +kernel
def cuts25369 : List PrefixCut := [⟨82,315367145,315367322⟩,
⟨128,492493476,492493749⟩]
theorem checked25369 : checkPrefixCuts (2^48) 3329097729 9 Manual.Count131072.C025369.packed 128 cuts25369 = true := by
 decide +kernel
def pointBounds25369 : List (Nat × Nat × Nat) := [(3329181696,103086298067803,103086680189914)]
theorem point_links_checked25369 : (cuts25369.take 1).map (fun c => (3329097729-1+2*2^9*c.k,103085982700658+c.lower,103086364822592+c.upper)) = pointBounds25369 := by
 decide +kernel
def cuts25370 : List PrefixCut := [⟨56,223370136,223370254⟩,
⟨128,504225919,504226189⟩]
theorem checked25370 : checkPrefixCuts (2^48) 3329228801 9 Manual.Count131072.C025370.packed 128 cuts25370 = true := by
 decide +kernel
def pointBounds25370 : List (Nat × Nat × Nat) := [(3329286144,103086698564270,103087080686595)]
theorem point_links_checked25370 : (cuts25370.take 1).map (fun c => (3329228801-1+2*2^9*c.k,103086475194134+c.lower,103086857316341+c.upper)) = pointBounds25370 := by
 decide +kernel
def cuts25371 : List PrefixCut := [⟨30,118190929,118190995⟩,
⟨128,501331579,501331858⟩]
theorem checked25371 : checkPrefixCuts (2^48) 3329359873 9 Manual.Count131072.C025371.packed 128 cuts25371 = true := by
 decide +kernel
def pointBounds25371 : List (Nat × Nat × Nat) := [(3329390592,103087097610982,103087479733525)]
theorem point_links_checked25371 : (cuts25371.take 1).map (fun c => (3329359873-1+2*2^9*c.k,103086979420053+c.lower,103087361542530+c.upper)) = pointBounds25371 := by
 decide +kernel
def cuts25372 : List PrefixCut := [⟨4,15555335,15555345⟩,
⟨106,418381248,418381487⟩,
⟨128,505876923,505877208⟩]
theorem checked25372 : checkPrefixCuts (2^48) 3329490945 9 Manual.Count131072.C025372.packed 128 cuts25372 = true := by
 decide +kernel
def pointBounds25372 : List (Nat × Nat × Nat) := [(3329495040,103087496306967,103087878429733),(3329599488,103087899132880,103088281255875)]
theorem point_links_checked25372 : (cuts25372.take 2).map (fun c => (3329490945-1+2*2^9*c.k,103087480751632+c.lower,103087862874388+c.upper)) = pointBounds25372 := by
 decide +kernel
def cuts25373 : List PrefixCut := [⟨80,311851615,311851786⟩,
⟨128,504081676,504081953⟩]
theorem checked25373 : checkPrefixCuts (2^48) 3329622017 9 Manual.Count131072.C025373.packed 128 cuts25373 = true := by
 decide +kernel
def pointBounds25373 : List (Nat × Nat × Nat) := [(3329703936,103088298480170,103088680603382)]
theorem point_links_checked25373 : (cuts25373.take 1).map (fun c => (3329622017-1+2*2^9*c.k,103087986628555+c.lower,103088368751596+c.upper)) = pointBounds25373 := by
 decide +kernel
def cuts25374 : List PrefixCut := [⟨54,216234299,216234421⟩,
⟨128,504062009,504062291⟩]
theorem checked25374 : checkPrefixCuts (2^48) 3329753089 9 Manual.Count131072.C025374.packed 128 cuts25374 = true := by
 decide +kernel
def pointBounds25374 : List (Nat × Nat × Nat) := [(3329808384,103088706944530,103089089067970)]
theorem point_links_checked25374 : (cuts25374.take 1).map (fun c => (3329753089-1+2*2^9*c.k,103088490710231+c.lower,103088872833549+c.upper)) = pointBounds25374 := by
 decide +kernel
def cuts25375 : List PrefixCut := [⟨28,109212211,109212272⟩,
⟨128,503703921,503704204⟩]
theorem checked25375 : checkPrefixCuts (2^48) 3329884161 9 Manual.Count131072.C025375.packed 128 cuts25375 = true := by
 decide +kernel
def pointBounds25375 : List (Nat × Nat × Nat) := [(3329912832,103089103984451,103089486108112)]
theorem point_links_checked25375 : (cuts25375.take 1).map (fun c => (3329884161-1+2*2^9*c.k,103088994772240+c.lower,103089376895840+c.upper)) = pointBounds25375 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000167
