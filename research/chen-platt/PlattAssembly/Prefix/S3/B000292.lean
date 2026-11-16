import PlattAssemblyKernel
import PlattCertificates.Count131072.C029344
import PlattCertificates.Count131072.C029345
import PlattCertificates.Count131072.C029346
import PlattCertificates.Count131072.C029347
import PlattCertificates.Count131072.C029348
import PlattCertificates.Count131072.C029349
import PlattCertificates.Count131072.C029350
import PlattCertificates.Count131072.C029351
import PlattCertificates.Count131072.C029352
import PlattCertificates.Count131072.C029353
import PlattCertificates.Count131072.C029354
import PlattCertificates.Count131072.C029355
import PlattCertificates.Count131072.C029356
import PlattCertificates.Count131072.C029357
import PlattCertificates.Count131072.C029358
import PlattCertificates.Count131072.C029359
import PlattCertificates.Count131072.C029360
import PlattCertificates.Count131072.C029361
import PlattCertificates.Count131072.C029362
import PlattCertificates.Count131072.C029363
import PlattCertificates.Count131072.C029364
import PlattCertificates.Count131072.C029365
import PlattCertificates.Count131072.C029366
import PlattCertificates.Count131072.C029367
import PlattCertificates.Count131072.C029368
import PlattCertificates.Count131072.C029369
import PlattCertificates.Count131072.C029370
import PlattCertificates.Count131072.C029371
import PlattCertificates.Count131072.C029372
import PlattCertificates.Count131072.C029373
import PlattCertificates.Count131072.C029374
import PlattCertificates.Count131072.C029375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000292
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29344 : List PrefixCut := [⟨4,14256110,14256118⟩,
⟨122,414444233,414444463⟩,
⟨128,434621452,434621694⟩]
theorem checked29344 : checkPrefixCuts (2^48) 3850108929 9 Manual.Count131072.C029344.packed 128 cuts29344 = true := by
 decide +kernel
def pointBounds29344 : List (Nat × Nat × Nat) := [(3850113024,104946487306066,104946870469413),(3850233856,104946887494189,104947270657758)]
theorem point_links_checked29344 : (cuts29344.take 2).map (fun c => (3850108929-1+2*2^9*c.k,104946473049956+c.lower,104946856213295+c.upper)) = pointBounds29344 := by
 decide +kernel
def cuts29345 : List PrefixCut := [⟨112,379194138,379194342⟩,
⟨128,432194157,432194389⟩]
theorem checked29345 : checkPrefixCuts (2^48) 3850240001 9 Manual.Count131072.C029345.packed 128 cuts29345 = true := by
 decide +kernel
def pointBounds29345 : List (Nat × Nat × Nat) := [(3850354688,104947286865546,104947670029331)]
theorem point_links_checked29345 : (cuts29345.take 1).map (fun c => (3850240001-1+2*2^9*c.k,104946907671408+c.lower,104947290834989+c.upper)) = pointBounds29345 := by
 decide +kernel
def cuts29346 : List PrefixCut := [⟨102,348990508,348990706⟩,
⟨128,439708945,439709191⟩]
theorem checked29346 : checkPrefixCuts (2^48) 3850371073 9 Manual.Count131072.C029346.packed 128 cuts29346 = true := by
 decide +kernel
def pointBounds29346 : List (Nat × Nat × Nat) := [(3850475520,104947688856073,104948072020084)]
theorem point_links_checked29346 : (cuts29346.take 1).map (fun c => (3850371073-1+2*2^9*c.k,104947339865565+c.lower,104947723029378+c.upper)) = pointBounds29346 := by
 decide +kernel
def cuts29347 : List PrefixCut := [⟨92,313306315,313306494⟩,
⟨128,435015642,435015887⟩]
theorem checked29347 : checkPrefixCuts (2^48) 3850502145 9 Manual.Count131072.C029347.packed 128 cuts29347 = true := by
 decide +kernel
def pointBounds29347 : List (Nat × Nat × Nat) := [(3850596352,104948092880825,104948476045063)]
theorem point_links_checked29347 : (cuts29347.take 1).map (fun c => (3850502145-1+2*2^9*c.k,104947779574510+c.lower,104948162738569+c.upper)) = pointBounds29347 := by
 decide +kernel
def cuts29348 : List PrefixCut := [⟨82,277258983,277259140⟩,
⟨128,437412983,437413231⟩]
theorem checked29348 : checkPrefixCuts (2^48) 3850633217 9 Manual.Count131072.C029348.packed 128 cuts29348 = true := by
 decide +kernel
def pointBounds29348 : List (Nat × Nat × Nat) := [(3850717184,104948491849135,104948875013596)]
theorem point_links_checked29348 : (cuts29348.take 1).map (fun c => (3850633217-1+2*2^9*c.k,104948214590152+c.lower,104948597754456+c.upper)) = pointBounds29348 := by
 decide +kernel
def cuts29349 : List PrefixCut := [⟨72,239532791,239532928⟩,
⟨128,428480557,428480801⟩]
theorem checked29349 : checkPrefixCuts (2^48) 3850764289 9 Manual.Count131072.C029349.packed 128 cuts29349 = true := by
 decide +kernel
def pointBounds29349 : List (Nat × Nat × Nat) := [(3850838016,104948891535926,104949274700615)]
theorem point_links_checked29349 : (cuts29349.take 1).map (fun c => (3850764289-1+2*2^9*c.k,104948652003135+c.lower,104949035167687+c.upper)) = pointBounds29349 := by
 decide +kernel
def cuts29350 : List PrefixCut := [⟨62,211603545,211603662⟩,
⟨128,432339940,432340184⟩]
theorem checked29350 : checkPrefixCuts (2^48) 3850895361 9 Manual.Count131072.C029350.packed 128 cuts29350 = true := by
 decide +kernel
def pointBounds29350 : List (Nat × Nat × Nat) := [(3850958848,104949292087237,104949675252150)]
theorem point_links_checked29350 : (cuts29350.take 1).map (fun c => (3850895361-1+2*2^9*c.k,104949080483692+c.lower,104949463648488+c.upper)) = pointBounds29350 := by
 decide +kernel
def cuts29351 : List PrefixCut := [⟨52,179656146,179656246⟩,
⟨128,441461397,441461643⟩]
theorem checked29351 : checkPrefixCuts (2^48) 3851026433 9 Manual.Count131072.C029351.packed 128 cuts29351 = true := by
 decide +kernel
def pointBounds29351 : List (Nat × Nat × Nat) := [(3851079680,104949692479778,104950075644918)]
theorem point_links_checked29351 : (cuts29351.take 1).map (fun c => (3851026433-1+2*2^9*c.k,104949512823632+c.lower,104949895988672+c.upper)) = pointBounds29351 := by
 decide +kernel
def cuts29352 : List PrefixCut := [⟨42,142521567,142521652⟩,
⟨128,432091250,432091501⟩]
theorem checked29352 : checkPrefixCuts (2^48) 3851157505 9 Manual.Count131072.C029352.packed 128 cuts29352 = true := by
 decide +kernel
def pointBounds29352 : List (Nat × Nat × Nat) := [(3851200512,104950096806596,104950479971967)]
theorem point_links_checked29352 : (cuts29352.take 1).map (fun c => (3851157505-1+2*2^9*c.k,104949954285029+c.lower,104950337450315+c.upper)) = pointBounds29352 := by
 decide +kernel
def cuts29353 : List PrefixCut := [⟨32,111674781,111674842⟩,
⟨128,438946510,438946750⟩]
theorem checked29353 : checkPrefixCuts (2^48) 3851288577 9 Manual.Count131072.C029353.packed 128 cuts29353 = true := by
 decide +kernel
def pointBounds29353 : List (Nat × Nat × Nat) := [(3851321344,104950498051060,104950881216658)]
theorem point_links_checked29353 : (cuts29353.take 1).map (fun c => (3851288577-1+2*2^9*c.k,104950386376279+c.lower,104950769541816+c.upper)) = pointBounds29353 := by
 decide +kernel
def cuts29354 : List PrefixCut := [⟨22,73375532,73375574⟩,
⟨128,431696315,431696561⟩]
theorem checked29354 : checkPrefixCuts (2^48) 3851419649 9 Manual.Count131072.C029354.packed 128 cuts29354 = true := by
 decide +kernel
def pointBounds29354 : List (Nat × Nat × Nat) := [(3851442176,104950898698321,104951281864140)]
theorem point_links_checked29354 : (cuts29354.take 1).map (fun c => (3851419649-1+2*2^9*c.k,104950825322789+c.lower,104951208488566+c.upper)) = pointBounds29354 := by
 decide +kernel
def cuts29355 : List PrefixCut := [⟨12,39025152,39025175⟩,
⟨128,433362489,433362731⟩]
theorem checked29355 : checkPrefixCuts (2^48) 3851550721 9 Manual.Count131072.C029355.packed 128 cuts29355 = true := by
 decide +kernel
def pointBounds29355 : List (Nat × Nat × Nat) := [(3851563008,104951296044256,104951679210302)]
theorem point_links_checked29355 : (cuts29355.take 1).map (fun c => (3851550721-1+2*2^9*c.k,104951257019104+c.lower,104951640185127+c.upper)) = pointBounds29355 := by
 decide +kernel
def cuts29356 : List PrefixCut := [⟨2,6723215,6723218⟩,
⟨120,408501970,408502197⟩,
⟨128,435686254,435686496⟩]
theorem checked29356 : checkPrefixCuts (2^48) 3851681793 9 Manual.Count131072.C029356.packed 128 cuts29356 = true := by
 decide +kernel
def pointBounds29356 : List (Nat × Nat × Nat) := [(3851683840,104951697104808,104952080271076),(3851804672,104952098883563,104952482050055)]
theorem point_links_checked29356 : (cuts29356.take 2).map (fun c => (3851681793-1+2*2^9*c.k,104951690381593+c.lower,104952073547858+c.upper)) = pointBounds29356 := by
 decide +kernel
def cuts29357 : List PrefixCut := [⟨110,374362631,374362843⟩,
⟨128,435671417,435671663⟩]
theorem checked29357 : checkPrefixCuts (2^48) 3851812865 9 Manual.Count131072.C029357.packed 128 cuts29357 = true := by
 decide +kernel
def pointBounds29357 : List (Nat × Nat × Nat) := [(3851925504,104952500430478,104952883597197)]
theorem point_links_checked29357 : (cuts29357.take 1).map (fun c => (3851812865-1+2*2^9*c.k,104952126067847+c.lower,104952509234354+c.upper)) = pointBounds29357 := by
 decide +kernel
def cuts29358 : List PrefixCut := [⟨100,334379726,334379910⟩,
⟨128,432660565,432660801⟩]
theorem checked29358 : checkPrefixCuts (2^48) 3851943937 9 Manual.Count131072.C029358.packed 128 cuts29358 = true := by
 decide +kernel
def pointBounds29358 : List (Nat × Nat × Nat) := [(3852046336,104952896118990,104953279285927)]
theorem point_links_checked29358 : (cuts29358.take 1).map (fun c => (3851943937-1+2*2^9*c.k,104952561739264+c.lower,104952944906017+c.upper)) = pointBounds29358 := by
 decide +kernel
def cuts29359 : List PrefixCut := [⟨90,300610406,300610578⟩,
⟨128,431403678,431403925⟩]
theorem checked29359 : checkPrefixCuts (2^48) 3852075009 9 Manual.Count131072.C029359.packed 128 cuts29359 = true := by
 decide +kernel
def pointBounds29359 : List (Nat × Nat × Nat) := [(3852167168,104953295010235,104953678177396)]
theorem point_links_checked29359 : (cuts29359.take 1).map (fun c => (3852075009-1+2*2^9*c.k,104952994399829+c.lower,104953377566818+c.upper)) = pointBounds29359 := by
 decide +kernel
def cuts29360 : List PrefixCut := [⟨80,274369249,274369402⟩,
⟨128,434457905,434458147⟩]
theorem checked29360 : checkPrefixCuts (2^48) 3852206081 9 Manual.Count131072.C029360.packed 128 cuts29360 = true := by
 decide +kernel
def pointBounds29360 : List (Nat × Nat × Nat) := [(3852288000,104953700172756,104954083340145)]
theorem point_links_checked29360 : (cuts29360.take 1).map (fun c => (3852206081-1+2*2^9*c.k,104953425803507+c.lower,104953808970743+c.upper)) = pointBounds29360 := by
 decide +kernel
def cuts29361 : List PrefixCut := [⟨70,234831947,234832083⟩,
⟨128,427794212,427794458⟩]
theorem checked29361 : checkPrefixCuts (2^48) 3852337153 9 Manual.Count131072.C029361.packed 128 cuts29361 = true := by
 decide +kernel
def pointBounds29361 : List (Nat × Nat × Nat) := [(3852408832,104954095093359,104954478260973)]
theorem point_links_checked29361 : (cuts29361.take 1).map (fun c => (3852337153-1+2*2^9*c.k,104953860261412+c.lower,104954243428890+c.upper)) = pointBounds29361 := by
 decide +kernel
def cuts29362 : List PrefixCut := [⟨60,202822730,202822846⟩,
⟨128,433478518,433478765⟩]
theorem checked29362 : checkPrefixCuts (2^48) 3852468225 9 Manual.Count131072.C029362.packed 128 cuts29362 = true := by
 decide +kernel
def pointBounds29362 : List (Nat × Nat × Nat) := [(3852529664,104954490878354,104954874046194)]
theorem point_links_checked29362 : (cuts29362.take 1).map (fun c => (3852468225-1+2*2^9*c.k,104954288055624+c.lower,104954671223348+c.upper)) = pointBounds29362 := by
 decide +kernel
def cuts29363 : List PrefixCut := [⟨50,169573547,169573643⟩,
⟨128,432294824,432295069⟩]
theorem checked29363 : checkPrefixCuts (2^48) 3852599297 9 Manual.Count131072.C029363.packed 128 cuts29363 = true := by
 decide +kernel
def pointBounds29363 : List (Nat × Nat × Nat) := [(3852650496,104954891107689,104955274275756)]
theorem point_links_checked29363 : (cuts29363.take 1).map (fun c => (3852599297-1+2*2^9*c.k,104954721534142+c.lower,104955104702113+c.upper)) = pointBounds29363 := by
 decide +kernel
def cuts29364 : List PrefixCut := [⟨40,133038922,133038995⟩,
⟨128,433741232,433741471⟩]
theorem checked29364 : checkPrefixCuts (2^48) 3852730369 9 Manual.Count131072.C029364.packed 128 cuts29364 = true := by
 decide +kernel
def pointBounds29364 : List (Nat × Nat × Nat) := [(3852771328,104955286867888,104955670036177)]
theorem point_links_checked29364 : (cuts29364.take 1).map (fun c => (3852730369-1+2*2^9*c.k,104955153828966+c.lower,104955536997182+c.upper)) = pointBounds29364 := by
 decide +kernel
def cuts29365 : List PrefixCut := [⟨30,98479188,98479241⟩,
⟨128,432338401,432338644⟩]
theorem checked29365 : checkPrefixCuts (2^48) 3852861441 9 Manual.Count131072.C029365.packed 128 cuts29365 = true := by
 decide +kernel
def pointBounds29365 : List (Nat × Nat × Nat) := [(3852892160,104955686049386,104956069217894)]
theorem point_links_checked29365 : (cuts29365.take 1).map (fun c => (3852861441-1+2*2^9*c.k,104955587570198+c.lower,104955970738653+c.upper)) = pointBounds29365 := by
 decide +kernel
def cuts29366 : List PrefixCut := [⟨20,66405529,66405567⟩,
⟨128,426917884,426918124⟩]
theorem checked29366 : checkPrefixCuts (2^48) 3852992513 9 Manual.Count131072.C029366.packed 128 cuts29366 = true := by
 decide +kernel
def pointBounds29366 : List (Nat × Nat × Nat) := [(3853012992,104956086314128,104956469482864)]
theorem point_links_checked29366 : (cuts29366.take 1).map (fun c => (3852992513-1+2*2^9*c.k,104956019908599+c.lower,104956403077297+c.upper)) = pointBounds29366 := by
 decide +kernel
def cuts29367 : List PrefixCut := [⟨10,34845323,34845343⟩,
⟨128,438518257,438518501⟩]
theorem checked29367 : checkPrefixCuts (2^48) 3853123585 9 Manual.Count131072.C029367.packed 128 cuts29367 = true := by
 decide +kernel
def pointBounds29367 : List (Nat × Nat × Nat) := [(3853133824,104956481671806,104956864840764),(3853254656,104956885344740,104957268513922)]
theorem point_links_checked29367 : (cuts29367.take 2).map (fun c => (3853123585-1+2*2^9*c.k,104956446826483+c.lower,104956829995421+c.upper)) = pointBounds29367 := by
 decide +kernel
def cuts29368 : List PrefixCut := [⟨118,403002897,403003124⟩,
⟨128,436458065,436458311⟩]
theorem checked29368 : checkPrefixCuts (2^48) 3853254657 9 Manual.Count131072.C029368.packed 128 cuts29368 = true := by
 decide +kernel
def pointBounds29368 : List (Nat × Nat × Nat) := [(3853375488,104957288347637,104957671517046)]
theorem point_links_checked29368 : (cuts29368.take 1).map (fun c => (3853254657-1+2*2^9*c.k,104956885344740+c.lower,104957268513922+c.upper)) = pointBounds29368 := by
 decide +kernel
def cuts29369 : List PrefixCut := [⟨108,365590616,365590825⟩,
⟨128,431183977,431184225⟩]
theorem checked29369 : checkPrefixCuts (2^48) 3853385729 9 Manual.Count131072.C029369.packed 128 cuts29369 = true := by
 decide +kernel
def pointBounds29369 : List (Nat × Nat × Nat) := [(3853496320,104957687393421,104958070563058)]
theorem point_links_checked29369 : (cuts29369.take 1).map (fun c => (3853385729-1+2*2^9*c.k,104957321802805+c.lower,104957704972233+c.upper)) = pointBounds29369 := by
 decide +kernel
def cuts29370 : List PrefixCut := [⟨98,335046824,335047014⟩,
⟨128,438181347,438181595⟩]
theorem checked29370 : checkPrefixCuts (2^48) 3853516801 9 Manual.Count131072.C029370.packed 128 cuts29370 = true := by
 decide +kernel
def pointBounds29370 : List (Nat × Nat × Nat) := [(3853617152,104958088033606,104958471203472)]
theorem point_links_checked29370 : (cuts29370.take 1).map (fun c => (3853516801-1+2*2^9*c.k,104957752986782+c.lower,104958136156458+c.upper)) = pointBounds29370 := by
 decide +kernel
def cuts29371 : List PrefixCut := [⟨88,295009760,295009922⟩,
⟨128,432104082,432104317⟩]
theorem checked29371 : checkPrefixCuts (2^48) 3853647873 9 Manual.Count131072.C029371.packed 128 cuts29371 = true := by
 decide +kernel
def pointBounds29371 : List (Nat × Nat × Nat) := [(3853737984,104958486177889,104958869347975)]
theorem point_links_checked29371 : (cuts29371.take 1).map (fun c => (3853647873-1+2*2^9*c.k,104958191168129+c.lower,104958574338053+c.upper)) = pointBounds29371 := by
 decide +kernel
def cuts29372 : List PrefixCut := [⟨78,261329674,261329822⟩,
⟨128,428656684,428656928⟩]
theorem checked29372 : checkPrefixCuts (2^48) 3853778945 9 Manual.Count131072.C029372.packed 128 cuts29372 = true := by
 decide +kernel
def pointBounds29372 : List (Nat × Nat × Nat) := [(3853858816,104958884601885,104959267772192)]
theorem point_links_checked29372 : (cuts29372.take 1).map (fun c => (3853778945-1+2*2^9*c.k,104958623272211+c.lower,104959006442370+c.upper)) = pointBounds29372 := by
 decide +kernel
def cuts29373 : List PrefixCut := [⟨68,230500110,230500244⟩,
⟨128,429518544,429518788⟩]
theorem checked29373 : checkPrefixCuts (2^48) 3853910017 9 Manual.Count131072.C029373.packed 128 cuts29373 = true := by
 decide +kernel
def pointBounds29373 : List (Nat × Nat × Nat) := [(3853979648,104959282429005,104959665599542)]
theorem point_links_checked29373 : (cuts29373.take 1).map (fun c => (3853910017-1+2*2^9*c.k,104959051928895+c.lower,104959435099298+c.upper)) = pointBounds29373 := by
 decide +kernel
def cuts29374 : List PrefixCut := [⟨58,195363651,195363761⟩,
⟨128,438925034,438925282⟩]
theorem checked29374 : checkPrefixCuts (2^48) 3854041089 9 Manual.Count131072.C029374.packed 128 cuts29374 = true := by
 decide +kernel
def pointBounds29374 : List (Nat × Nat × Nat) := [(3854100480,104959676811090,104960059981847)]
theorem point_links_checked29374 : (cuts29374.take 1).map (fun c => (3854041089-1+2*2^9*c.k,104959481447439+c.lower,104959864618086+c.upper)) = pointBounds29374 := by
 decide +kernel
def cuts29375 : List PrefixCut := [⟨48,164757369,164757462⟩,
⟨128,438106840,438107089⟩]
theorem checked29375 : checkPrefixCuts (2^48) 3854172161 9 Manual.Count131072.C029375.packed 128 cuts29375 = true := by
 decide +kernel
def pointBounds29375 : List (Nat × Nat × Nat) := [(3854221312,104960085129842,104960468300830)]
theorem point_links_checked29375 : (cuts29375.take 1).map (fun c => (3854172161-1+2*2^9*c.k,104959920372473+c.lower,104960303543368+c.upper)) = pointBounds29375 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000292
