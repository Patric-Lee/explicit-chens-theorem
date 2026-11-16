import PlattAssemblyKernel
import PlattCertificates.Count131072.C026368
import PlattCertificates.Count131072.C026369
import PlattCertificates.Count131072.C026370
import PlattCertificates.Count131072.C026371
import PlattCertificates.Count131072.C026372
import PlattCertificates.Count131072.C026373
import PlattCertificates.Count131072.C026374
import PlattCertificates.Count131072.C026375
import PlattCertificates.Count131072.C026376
import PlattCertificates.Count131072.C026377
import PlattCertificates.Count131072.C026378
import PlattCertificates.Count131072.C026379
import PlattCertificates.Count131072.C026380
import PlattCertificates.Count131072.C026381
import PlattCertificates.Count131072.C026382
import PlattCertificates.Count131072.C026383
import PlattCertificates.Count131072.C026384
import PlattCertificates.Count131072.C026385
import PlattCertificates.Count131072.C026386
import PlattCertificates.Count131072.C026387
import PlattCertificates.Count131072.C026388
import PlattCertificates.Count131072.C026389
import PlattCertificates.Count131072.C026390
import PlattCertificates.Count131072.C026391
import PlattCertificates.Count131072.C026392
import PlattCertificates.Count131072.C026393
import PlattCertificates.Count131072.C026394
import PlattCertificates.Count131072.C026395
import PlattCertificates.Count131072.C026396
import PlattCertificates.Count131072.C026397
import PlattCertificates.Count131072.C026398
import PlattCertificates.Count131072.C026399
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000199
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26368 : List PrefixCut := [⟨19,73865785,73865825⟩,
⟨125,477516994,477517260⟩,
⟨128,489475029,489475301⟩]
theorem checked26368 : checkPrefixCuts (2^48) 3460038657 9 Manual.Count131072.C026368.packed 128 cuts26368 = true := by
 decide +kernel
def pointBounds26368 : List (Nat × Nat × Nat) := [(3460058112,103580829669148,103581212068184),(3460166656,103581233320357,103581615719619)]
theorem point_links_checked26368 : (cuts26368.take 2).map (fun c => (3460038657-1+2*2^9*c.k,103580755803363+c.lower,103581138202359+c.upper)) = pointBounds26368 := by
 decide +kernel
def cuts26369 : List PrefixCut := [⟨103,388589356,388589578⟩,
⟨128,482786113,482786389⟩]
theorem checked26369 : checkPrefixCuts (2^48) 3460169729 9 Manual.Count131072.C026369.packed 128 cuts26369 = true := by
 decide +kernel
def pointBounds26369 : List (Nat × Nat × Nat) := [(3460275200,103581633867748,103582016267238)]
theorem point_links_checked26369 : (cuts26369.take 1).map (fun c => (3460169729-1+2*2^9*c.k,103581245278392+c.lower,103581627677660+c.upper)) = pointBounds26369 := by
 decide +kernel
def cuts26370 : List PrefixCut := [⟨81,311869390,311869563⟩,
⟨128,486591023,486591294⟩]
theorem checked26370 : checkPrefixCuts (2^48) 3460300801 9 Manual.Count131072.C026370.packed 128 cuts26370 = true := by
 decide +kernel
def pointBounds26370 : List (Nat × Nat × Nat) := [(3460383744,103582039933895,103582422333612)]
theorem point_links_checked26370 : (cuts26370.take 1).map (fun c => (3460300801-1+2*2^9*c.k,103581728064505+c.lower,103582110464049+c.upper)) = pointBounds26370 := by
 decide +kernel
def cuts26371 : List PrefixCut := [⟨59,225149865,225149994⟩,
⟨128,488768641,488768914⟩]
theorem checked26371 : checkPrefixCuts (2^48) 3460431873 9 Manual.Count131072.C026371.packed 128 cuts26371 = true := by
 decide +kernel
def pointBounds26371 : List (Nat × Nat × Nat) := [(3460492288,103582439805393,103582822205337)]
theorem point_links_checked26371 : (cuts26371.take 1).map (fun c => (3460431873-1+2*2^9*c.k,103582214655528+c.lower,103582597055343+c.upper)) = pointBounds26371 := by
 decide +kernel
def cuts26372 : List PrefixCut := [⟨37,140225756,140225834⟩,
⟨128,485659349,485659624⟩]
theorem checked26372 : checkPrefixCuts (2^48) 3460562945 9 Manual.Count131072.C026372.packed 128 cuts26372 = true := by
 decide +kernel
def pointBounds26372 : List (Nat × Nat × Nat) := [(3460600832,103582843649925,103583226050091)]
theorem point_links_checked26372 : (cuts26372.take 1).map (fun c => (3460562945-1+2*2^9*c.k,103582703424169+c.lower,103583085824257+c.upper)) = pointBounds26372 := by
 decide +kernel
def cuts26373 : List PrefixCut := [⟨15,58154260,58154292⟩,
⟨121,465470813,465471070⟩,
⟨128,491334330,491334603⟩]
theorem checked26373 : checkPrefixCuts (2^48) 3460694017 9 Manual.Count131072.C026373.packed 128 cuts26373 = true := by
 decide +kernel
def pointBounds26373 : List (Nat × Nat × Nat) := [(3460709376,103583247237778,103583629638173),(3460817920,103583654554331,103584036954951)]
theorem point_links_checked26373 : (cuts26373.take 2).map (fun c => (3460694017-1+2*2^9*c.k,103583189083518+c.lower,103583571483881+c.upper)) = pointBounds26373 := by
 decide +kernel
def cuts26374 : List PrefixCut := [⟨99,376397725,376397934⟩,
⟨128,484402634,484402902⟩]
theorem checked26374 : checkPrefixCuts (2^48) 3460825089 9 Manual.Count131072.C026374.packed 128 cuts26374 = true := by
 decide +kernel
def pointBounds26374 : List (Nat × Nat × Nat) := [(3460926464,103584056815573,103584439216418)]
theorem point_links_checked26374 : (cuts26374.take 1).map (fun c => (3460825089-1+2*2^9*c.k,103583680417848+c.lower,103584062818484+c.upper)) = pointBounds26374 := by
 decide +kernel
def cuts26375 : List PrefixCut := [⟨77,292291832,292291993⟩,
⟨128,483245729,483245998⟩]
theorem checked26375 : checkPrefixCuts (2^48) 3460956161 9 Manual.Count131072.C026375.packed 128 cuts26375 = true := by
 decide +kernel
def pointBounds26375 : List (Nat × Nat × Nat) := [(3461035008,103584457112314,103584839513379)]
theorem point_links_checked26375 : (cuts26375.take 1).map (fun c => (3460956161-1+2*2^9*c.k,103584164820482+c.lower,103584547221386+c.upper)) = pointBounds26375 := by
 decide +kernel
def cuts26376 : List PrefixCut := [⟨55,206727928,206728043⟩,
⟨128,480625020,480625291⟩]
theorem checked26376 : checkPrefixCuts (2^48) 3461087233 9 Manual.Count131072.C026376.packed 128 cuts26376 = true := by
 decide +kernel
def pointBounds26376 : List (Nat × Nat × Nat) := [(3461143552,103584854794139,103585237195427)]
theorem point_links_checked26376 : (cuts26376.take 1).map (fun c => (3461087233-1+2*2^9*c.k,103584648066211+c.lower,103585030467384+c.upper)) = pointBounds26376 := by
 decide +kernel
def cuts26377 : List PrefixCut := [⟨33,124016180,124016249⟩,
⟨128,488006962,488007238⟩]
theorem checked26377 : checkPrefixCuts (2^48) 3461218305 9 Manual.Count131072.C026377.packed 128 cuts26377 = true := by
 decide +kernel
def pointBounds26377 : List (Nat × Nat × Nat) := [(3461252096,103585252707411,103585635108924)]
theorem point_links_checked26377 : (cuts26377.take 1).map (fun c => (3461218305-1+2*2^9*c.k,103585128691231+c.lower,103585511092675+c.upper)) = pointBounds26377 := by
 decide +kernel
def cuts26378 : List PrefixCut := [⟨11,40171725,40171749⟩,
⟨117,437165557,437165801⟩,
⟨128,478799590,478799856⟩]
theorem checked26378 : checkPrefixCuts (2^48) 3461349377 9 Manual.Count131072.C026378.packed 128 cuts26378 = true := by
 decide +kernel
def pointBounds26378 : List (Nat × Nat × Nat) := [(3461360640,103585656869918,103586039271662),(3461469184,103586053863750,103586436265714)]
theorem point_links_checked26378 : (cuts26378.take 2).map (fun c => (3461349377-1+2*2^9*c.k,103585616698193+c.lower,103585999099913+c.upper)) = pointBounds26378 := by
 decide +kernel
def cuts26379 : List PrefixCut := [⟨95,364617350,364617551⟩,
⟨128,487238341,487238613⟩]
theorem checked26379 : checkPrefixCuts (2^48) 3461480449 9 Manual.Count131072.C026379.packed 128 cuts26379 = true := by
 decide +kernel
def pointBounds26379 : List (Nat × Nat × Nat) := [(3461577728,103586460115133,103586842517320)]
theorem point_links_checked26379 : (cuts26379.take 1).map (fun c => (3461480449-1+2*2^9*c.k,103586095497783+c.lower,103586477899769+c.upper)) = pointBounds26379 := by
 decide +kernel
def cuts26380 : List PrefixCut := [⟨73,277519133,277519286⟩,
⟨128,486813234,486813507⟩]
theorem checked26380 : checkPrefixCuts (2^48) 3461611521 9 Manual.Count131072.C026380.packed 128 cuts26380 = true := by
 decide +kernel
def pointBounds26380 : List (Nat × Nat × Nat) := [(3461686272,103586860255257,103587242657668)]
theorem point_links_checked26380 : (cuts26380.take 1).map (fun c => (3461611521-1+2*2^9*c.k,103586582736124+c.lower,103586965138382+c.upper)) = pointBounds26380 := by
 decide +kernel
def cuts26381 : List PrefixCut := [⟨51,193760689,193760796⟩,
⟨128,489396686,489396959⟩]
theorem checked26381 : checkPrefixCuts (2^48) 3461742593 9 Manual.Count131072.C026381.packed 128 cuts26381 = true := by
 decide +kernel
def pointBounds26381 : List (Nat × Nat × Nat) := [(3461794816,103587263310047,103587645712685)]
theorem point_links_checked26381 : (cuts26381.take 1).map (fun c => (3461742593-1+2*2^9*c.k,103587069549358+c.lower,103587451951889+c.upper)) = pointBounds26381 := by
 decide +kernel
def cuts26382 : List PrefixCut := [⟨29,107568832,107568891⟩,
⟨128,487752007,487752274⟩]
theorem checked26382 : checkPrefixCuts (2^48) 3461873665 9 Manual.Count131072.C026382.packed 128 cuts26382 = true := by
 decide +kernel
def pointBounds26382 : List (Nat × Nat × Nat) := [(3461903360,103587666514876,103588048917739)]
theorem point_links_checked26382 : (cuts26382.take 1).map (fun c => (3461873665-1+2*2^9*c.k,103587558946044+c.lower,103587941348848+c.upper)) = pointBounds26382 := by
 decide +kernel
def cuts26383 : List PrefixCut := [⟨7,27562034,27562048⟩,
⟨113,433912315,433912549⟩,
⟨128,489522284,489522549⟩]
theorem checked26383 : checkPrefixCuts (2^48) 3462004737 9 Manual.Count131072.C026383.packed 128 cuts26383 = true := by
 decide +kernel
def pointBounds26383 : List (Nat × Nat × Nat) := [(3462011904,103588074260085,103588456663170),(3462120448,103588480610366,103588863013671)]
theorem point_links_checked26383 : (cuts26383.take 2).map (fun c => (3462004737-1+2*2^9*c.k,103588046698051+c.lower,103588429101122+c.upper)) = pointBounds26383 := by
 decide +kernel
def cuts26384 : List PrefixCut := [⟨91,345686933,345687123⟩,
⟨128,485276133,485276401⟩]
theorem checked26384 : checkPrefixCuts (2^48) 3462135809 9 Manual.Count131072.C026384.packed 128 cuts26384 = true := by
 decide +kernel
def pointBounds26384 : List (Nat × Nat × Nat) := [(3462228992,103588881907268,103589264310794)]
theorem point_links_checked26384 : (cuts26384.take 1).map (fun c => (3462135809-1+2*2^9*c.k,103588536220335+c.lower,103588918623671+c.upper)) = pointBounds26384 := by
 decide +kernel
def cuts26385 : List PrefixCut := [⟨69,261695149,261695297⟩,
⟨128,482087233,482087504⟩]
theorem checked26385 : checkPrefixCuts (2^48) 3462266881 9 Manual.Count131072.C026385.packed 128 cuts26385 = true := by
 decide +kernel
def pointBounds26385 : List (Nat × Nat × Nat) := [(3462337536,103589283191617,103589665595369)]
theorem point_links_checked26385 : (cuts26385.take 1).map (fun c => (3462266881-1+2*2^9*c.k,103589021496468+c.lower,103589403900072+c.upper)) = pointBounds26385 := by
 decide +kernel
def cuts26386 : List PrefixCut := [⟨47,177709154,177709257⟩,
⟨128,484426435,484426712⟩]
theorem checked26386 : checkPrefixCuts (2^48) 3462397953 9 Manual.Count131072.C026386.packed 128 cuts26386 = true := by
 decide +kernel
def pointBounds26386 : List (Nat × Nat × Nat) := [(3462446080,103589681292855,103590063696833)]
theorem point_links_checked26386 : (cuts26386.take 1).map (fun c => (3462397953-1+2*2^9*c.k,103589503583701+c.lower,103589885987576+c.upper)) = pointBounds26386 := by
 decide +kernel
def cuts26387 : List PrefixCut := [⟨25,94541914,94541965⟩,
⟨128,491317681,491317955⟩]
theorem checked26387 : checkPrefixCuts (2^48) 3462529025 9 Manual.Count131072.C026387.packed 128 cuts26387 = true := by
 decide +kernel
def pointBounds26387 : List (Nat × Nat × Nat) := [(3462554624,103590082552050,103590464956253)]
theorem point_links_checked26387 : (cuts26387.take 1).map (fun c => (3462529025-1+2*2^9*c.k,103589988010136+c.lower,103590370414288+c.upper)) = pointBounds26387 := by
 decide +kernel
def cuts26388 : List PrefixCut := [⟨3,12112001,12112008⟩,
⟨109,409769476,409769702⟩,
⟨128,482438965,482439234⟩]
theorem checked26388 : checkPrefixCuts (2^48) 3462660097 9 Manual.Count131072.C026388.packed 128 cuts26388 = true := by
 decide +kernel
def pointBounds26388 : List (Nat × Nat × Nat) := [(3462663168,103590491439818,103590873844251),(3462771712,103590889097293,103591271501945)]
theorem point_links_checked26388 : (cuts26388.take 2).map (fun c => (3462660097-1+2*2^9*c.k,103590479327817+c.lower,103590861732243+c.upper)) = pointBounds26388 := by
 decide +kernel
def cuts26389 : List PrefixCut := [⟨87,333672951,333673142⟩,
⟨128,490223971,490224250⟩]
theorem checked26389 : checkPrefixCuts (2^48) 3462791169 9 Manual.Count131072.C026389.packed 128 cuts26389 = true := by
 decide +kernel
def pointBounds26389 : List (Nat × Nat × Nat) := [(3462880256,103591295439733,103591677844619)]
theorem point_links_checked26389 : (cuts26389.take 1).map (fun c => (3462791169-1+2*2^9*c.k,103590961766782+c.lower,103591344171477+c.upper)) = pointBounds26389 := by
 decide +kernel
def cuts26390 : List PrefixCut := [⟨65,249616062,249616200⟩,
⟨128,487035394,487035670⟩]
theorem checked26390 : checkPrefixCuts (2^48) 3462922241 9 Manual.Count131072.C026390.packed 128 cuts26390 = true := by
 decide +kernel
def pointBounds26390 : List (Nat × Nat × Nat) := [(3462988800,103591701606815,103592084011927)]
theorem point_links_checked26390 : (cuts26390.take 1).map (fun c => (3462922241-1+2*2^9*c.k,103591451990753+c.lower,103591834395727+c.upper)) = pointBounds26390 := by
 decide +kernel
def cuts26391 : List PrefixCut := [⟨43,165565088,165565177⟩,
⟨128,486691886,486692149⟩]
theorem checked26391 : checkPrefixCuts (2^48) 3463053313 9 Manual.Count131072.C026391.packed 128 cuts26391 = true := by
 decide +kernel
def pointBounds26391 : List (Nat × Nat × Nat) := [(3463097344,103592104591235,103592486996574)]
theorem point_links_checked26391 : (cuts26391.take 1).map (fun c => (3463053313-1+2*2^9*c.k,103591939026147+c.lower,103592321431397+c.upper)) = pointBounds26391 := by
 decide +kernel
def cuts26392 : List PrefixCut := [⟨21,80869690,80869735⟩,
⟨127,489518140,489518408⟩,
⟨128,493337983,493338253⟩]
theorem checked26392 : checkPrefixCuts (2^48) 3463184385 9 Manual.Count131072.C026392.packed 128 cuts26392 = true := by
 decide +kernel
def pointBounds26392 : List (Nat × Nat × Nat) := [(3463205888,103592506587723,103592888993281),(3463314432,103592915236173,103593297641954)]
theorem point_links_checked26392 : (cuts26392.take 2).map (fun c => (3463184385-1+2*2^9*c.k,103592425718033+c.lower,103592808123546+c.upper)) = pointBounds26392 := by
 decide +kernel
def cuts26393 : List PrefixCut := [⟨105,397663803,397664024⟩,
⟨128,485760969,485761239⟩]
theorem checked26393 : checkPrefixCuts (2^48) 3463315457 9 Manual.Count131072.C026393.packed 128 cuts26393 = true := by
 decide +kernel
def pointBounds26393 : List (Nat × Nat × Nat) := [(3463422976,103593316719819,103593699125823)]
theorem point_links_checked26393 : (cuts26393.take 1).map (fun c => (3463315457-1+2*2^9*c.k,103592919056016+c.lower,103593301461799+c.upper)) = pointBounds26393 := by
 decide +kernel
def cuts26394 : List PrefixCut := [⟨83,313536486,313536663⟩,
⟨128,482329366,482329638⟩]
theorem checked26394 : checkPrefixCuts (2^48) 3463446529 9 Manual.Count131072.C026394.packed 128 cuts26394 = true := by
 decide +kernel
def pointBounds26394 : List (Nat × Nat × Nat) := [(3463531520,103593718353471,103594100759701)]
theorem point_links_checked26394 : (cuts26394.take 1).map (fun c => (3463446529-1+2*2^9*c.k,103593404816985+c.lower,103593787223038+c.upper)) = pointBounds26394 := by
 decide +kernel
def cuts26395 : List PrefixCut := [⟨61,233722061,233722188⟩,
⟨128,488974894,488975164⟩]
theorem checked26395 : checkPrefixCuts (2^48) 3463577601 9 Manual.Count131072.C026395.packed 128 cuts26395 = true := by
 decide +kernel
def pointBounds26395 : List (Nat × Nat × Nat) := [(3463640064,103594120868412,103594503274864)]
theorem point_links_checked26395 : (cuts26395.take 1).map (fun c => (3463577601-1+2*2^9*c.k,103593887146351+c.lower,103594269552676+c.upper)) = pointBounds26395 := by
 decide +kernel
def cuts26396 : List PrefixCut := [⟨39,146680719,146680801⟩,
⟨128,484811978,484812255⟩]
theorem checked26396 : checkPrefixCuts (2^48) 3463708673 9 Manual.Count131072.C026396.packed 128 cuts26396 = true := by
 decide +kernel
def pointBounds26396 : List (Nat × Nat × Nat) := [(3463748608,103594522801964,103594905208641)]
theorem point_links_checked26396 : (cuts26396.take 1).map (fun c => (3463708673-1+2*2^9*c.k,103594376121245+c.lower,103594758527840+c.upper)) = pointBounds26396 := by
 decide +kernel
def cuts26397 : List PrefixCut := [⟨17,60051692,60051725⟩,
⟨123,461716263,461716521⟩,
⟨128,480730619,480730888⟩]
theorem checked26397 : checkPrefixCuts (2^48) 3463839745 9 Manual.Count131072.C026397.packed 128 cuts26397 = true := by
 decide +kernel
def pointBounds26397 : List (Nat × Nat × Nat) := [(3463857152,103594920984915,103595303391820),(3463965696,103595322649486,103595705056616)]
theorem point_links_checked26397 : (cuts26397.take 2).map (fun c => (3463839745-1+2*2^9*c.k,103594860933223+c.lower,103595243340095+c.upper)) = pointBounds26397 := by
 decide +kernel
def cuts26398 : List PrefixCut := [⟨101,384912803,384913019⟩,
⟨128,486887984,486888260⟩]
theorem checked26398 : checkPrefixCuts (2^48) 3463970817 9 Manual.Count131072.C026398.packed 128 cuts26398 = true := by
 decide +kernel
def pointBounds26398 : List (Nat × Nat × Nat) := [(3464074240,103595726576645,103596108984002)]
theorem point_links_checked26398 : (cuts26398.take 1).map (fun c => (3463970817-1+2*2^9*c.k,103595341663842+c.lower,103595724070983+c.upper)) = pointBounds26398 := by
 decide +kernel
def cuts26399 : List PrefixCut := [⟨79,305027013,305027182⟩,
⟨128,488901006,488901275⟩]
theorem checked26399 : checkPrefixCuts (2^48) 3464101889 9 Manual.Count131072.C026399.packed 128 cuts26399 = true := by
 decide +kernel
def pointBounds26399 : List (Nat × Nat × Nat) := [(3464182784,103596133578839,103596515986425)]
theorem point_links_checked26399 : (cuts26399.take 1).map (fun c => (3464101889-1+2*2^9*c.k,103595828551826+c.lower,103596210959243+c.upper)) = pointBounds26399 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000199
