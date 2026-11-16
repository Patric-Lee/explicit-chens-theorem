import PlattAssemblyKernel
import PlattCertificates.Count131072.C015344
import PlattCertificates.Count131072.C015345
import PlattCertificates.Count131072.C015346
import PlattCertificates.Count131072.C015347
import PlattCertificates.Count131072.C015348
import PlattCertificates.Count131072.C015349
import PlattCertificates.Count131072.C015350
import PlattCertificates.Count131072.C015351
import PlattCertificates.Count131072.C015352
import PlattCertificates.Count131072.C015353
import PlattCertificates.Count131072.C015354
import PlattCertificates.Count131072.C015355
import PlattCertificates.Count131072.C015356
import PlattCertificates.Count131072.C015357
import PlattCertificates.Count131072.C015358
import PlattCertificates.Count131072.C015359
import PlattCertificates.Count131072.C015360
import PlattCertificates.Count131072.C015361
import PlattCertificates.Count131072.C015362
import PlattCertificates.Count131072.C015363
import PlattCertificates.Count131072.C015364
import PlattCertificates.Count131072.C015365
import PlattCertificates.Count131072.C015366
import PlattCertificates.Count131072.C015367
import PlattCertificates.Count131072.C015368
import PlattCertificates.Count131072.C015369
import PlattCertificates.Count131072.C015370
import PlattCertificates.Count131072.C015371
import PlattCertificates.Count131072.C015372
import PlattCertificates.Count131072.C015373
import PlattCertificates.Count131072.C015374
import PlattCertificates.Count131072.C015375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000167
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15344 : List PrefixCut := [⟨42,279222867,279223054⟩,
⟨104,690433767,690434228⟩,
⟨128,852456233,852456800⟩]
theorem checked15344 : checkPrefixCuts (2^48) 2015100929 9 Manual.Count131072.C015344.packed 128 cuts15344 = true := by
 decide +kernel
def pointBounds15344 : List (Nat × Nat × Nat) := [(2015143936,96566646267451,96567024498563),(2015207424,96567057478351,96567435709737)]
theorem point_links_checked15344 : (cuts15344.take 2).map (fun c => (2015100929-1+2*2^9*c.k,96566367044584+c.lower,96566745275509+c.upper)) = pointBounds15344 := by
 decide +kernel
def cuts15345 : List PrefixCut := [⟨38,256438460,256438630⟩,
⟨100,667064781,667065224⟩,
⟨128,854496041,854496609⟩]
theorem checked15345 : checkPrefixCuts (2^48) 2015232001 9 Manual.Count131072.C015345.packed 128 cuts15345 = true := by
 decide +kernel
def pointBounds15345 : List (Nat × Nat × Nat) := [(2015270912,96567475939277,96567854170939),(2015334400,96567886565598,96568264797533)]
theorem point_links_checked15345 : (cuts15345.take 2).map (fun c => (2015232001-1+2*2^9*c.k,96567219500817+c.lower,96567597732309+c.upper)) = pointBounds15345 := by
 decide +kernel
def cuts15346 : List PrefixCut := [⟨34,232679209,232679364⟩,
⟨96,640626168,640626596⟩,
⟨128,844385221,844385787⟩]
theorem checked15346 : checkPrefixCuts (2^48) 2015363073 9 Manual.Count131072.C015346.packed 128 cuts15346 = true := by
 decide +kernel
def pointBounds15346 : List (Nat × Nat × Nat) := [(2015397888,96568306676067,96568684908282),(2015461376,96568714623026,96569092855514)]
theorem point_links_checked15346 : (cuts15346.take 2).map (fun c => (2015363073-1+2*2^9*c.k,96568073996858+c.lower,96568452228918+c.upper)) = pointBounds15346 := by
 decide +kernel
def cuts15347 : List PrefixCut := [⟨30,200823109,200823241⟩,
⟨92,616285412,616285824⟩,
⟨128,863461896,863462464⟩]
theorem checked15347 : checkPrefixCuts (2^48) 2015494145 9 Manual.Count131072.C015347.packed 128 cuts15347 = true := by
 decide +kernel
def pointBounds15347 : List (Nat × Nat × Nat) := [(2015524864,96569119205188,96569497437946),(2015588352,96569534667491,96569912900529)]
theorem point_links_checked15347 : (cuts15347.take 2).map (fun c => (2015494145-1+2*2^9*c.k,96568918382079+c.lower,96569296614705+c.upper)) = pointBounds15347 := by
 decide +kernel
def cuts15348 : List PrefixCut := [⟨26,176791235,176791348⟩,
⟨88,595439055,595439441⟩,
⟨128,869270707,869271274⟩]
theorem checked15348 : checkPrefixCuts (2^48) 2015625217 9 Manual.Count131072.C015348.packed 128 cuts15348 = true := by
 decide +kernel
def pointBounds15348 : List (Nat × Nat × Nat) := [(2015651840,96569958635210,96570336868517),(2015715328,96570377283030,96570755516610)]
theorem point_links_checked15348 : (cuts15348.take 2).map (fun c => (2015625217-1+2*2^9*c.k,96569781843975+c.lower,96570160077169+c.upper)) = pointBounds15348 := by
 decide +kernel
def cuts15349 : List PrefixCut := [⟨22,144523857,144523954⟩,
⟨84,552533225,552533582⟩,
⟨128,848269191,848269741⟩]
theorem checked15349 : checkPrefixCuts (2^48) 2015756289 9 Manual.Count131072.C015349.packed 128 cuts15349 = true := by
 decide +kernel
def pointBounds15349 : List (Nat × Nat × Nat) := [(2015778816,96570795638539,96571173872397),(2015842304,96571203647907,96571581882025)]
theorem point_links_checked15349 : (cuts15349.take 2).map (fun c => (2015756289-1+2*2^9*c.k,96570651114682+c.lower,96571029348443+c.upper)) = pointBounds15349 := by
 decide +kernel
def cuts15350 : List PrefixCut := [⟨18,123011948,123012032⟩,
⟨80,531414495,531414846⟩,
⟨128,857987753,857988323⟩]
theorem checked15350 : checkPrefixCuts (2^48) 2015887361 9 Manual.Count131072.C015350.packed 128 cuts15350 = true := by
 decide +kernel
def pointBounds15350 : List (Nat × Nat × Nat) := [(2015905792,96571622395821,96572000630216),(2015969280,96572030798368,96572409033030)]
theorem point_links_checked15350 : (cuts15350.take 2).map (fun c => (2015887361-1+2*2^9*c.k,96571499383873+c.lower,96571877618184+c.upper)) = pointBounds15350 := by
 decide +kernel
def cuts15351 : List PrefixCut := [⟨14,91589868,91589929⟩,
⟨76,509879514,509879851⟩,
⟨128,855419182,855419746⟩]
theorem checked15351 : checkPrefixCuts (2^48) 2016018433 9 Manual.Count131072.C015351.packed 128 cuts15351 = true := by
 decide +kernel
def pointBounds15351 : List (Nat × Nat × Nat) := [(2016032768,96572448961494,96572827196436),(2016096256,96572867251140,96573245486358)]
theorem point_links_checked15351 : (cuts15351.take 2).map (fun c => (2016018433-1+2*2^9*c.k,96572357371626+c.lower,96572735606507+c.upper)) = pointBounds15351 := by
 decide +kernel
def cuts15352 : List PrefixCut := [⟨10,67291914,67291958⟩,
⟨72,477876652,477876964⟩,
⟨128,857317733,857318296⟩]
theorem checked15352 : checkPrefixCuts (2^48) 2016149505 9 Manual.Count131072.C015352.packed 128 cuts15352 = true := by
 decide +kernel
def pointBounds15352 : List (Nat × Nat × Nat) := [(2016159744,96573280082722,96573658318211),(2016223232,96573690667460,96574068903217)]
theorem point_links_checked15352 : (cuts15352.take 2).map (fun c => (2016149505-1+2*2^9*c.k,96573212790808+c.lower,96573591026253+c.upper)) = pointBounds15352 := by
 decide +kernel
def cuts15353 : List PrefixCut := [⟨6,38809035,38809061⟩,
⟨68,446715581,446715878⟩,
⟨128,854609620,854610181⟩]
theorem checked15353 : checkPrefixCuts (2^48) 2016280577 9 Manual.Count131072.C015353.packed 128 cuts15353 = true := by
 decide +kernel
def pointBounds15353 : List (Nat × Nat × Nat) := [(2016286720,96574108917576,96574487153610),(2016350208,96574516824122,96574895060427)]
theorem point_links_checked15353 : (cuts15353.take 2).map (fun c => (2016280577-1+2*2^9*c.k,96574070108541+c.lower,96574448344549+c.upper)) = pointBounds15353 := by
 decide +kernel
def cuts15354 : List PrefixCut := [⟨2,13819598,13819607⟩,
⟨64,430355160,430355444⟩,
⟨126,851065078,851065640⟩,
⟨128,866000457,866001028⟩]
theorem checked15354 : checkPrefixCuts (2^48) 2016411649 9 Manual.Count131072.C015354.packed 128 cuts15354 = true := by
 decide +kernel
def pointBounds15354 : List (Nat × Nat × Nat) := [(2016413696,96574938537759,96575316774337),(2016477184,96575355073321,96575733310174),(2016540672,96575775783239,96576154020370)]
theorem point_links_checked15354 : (cuts15354.take 3).map (fun c => (2016411649-1+2*2^9*c.k,96574924718161+c.lower,96575302954730+c.upper)) = pointBounds15354 := by
 decide +kernel
def cuts15355 : List PrefixCut := [⟨60,398921803,398922069⟩,
⟨122,808020376,808020909⟩,
⟨128,847798979,847799538⟩]
theorem checked15355 : checkPrefixCuts (2^48) 2016542721 9 Manual.Count131072.C015355.packed 128 cuts15355 = true := by
 decide +kernel
def pointBounds15355 : List (Nat × Nat × Nat) := [(2016604160,96576189640421,96576567877827),(2016667648,96576598738994,96576976976667)]
theorem point_links_checked15355 : (cuts15355.take 2).map (fun c => (2016542721-1+2*2^9*c.k,96575790718618+c.lower,96576168955758+c.upper)) = pointBounds15355 := by
 decide +kernel
def cuts15356 : List PrefixCut := [⟨56,371400654,371400901⟩,
⟨118,790103727,790104250⟩,
⟨128,852489332,852489895⟩]
theorem checked15356 : checkPrefixCuts (2^48) 2016673793 9 Manual.Count131072.C015356.packed 128 cuts15356 = true := by
 decide +kernel
def pointBounds15356 : List (Nat × Nat × Nat) := [(2016731136,96577009918251,96577388156197),(2016794624,96577428621324,96577806859546)]
theorem point_links_checked15356 : (cuts15356.take 2).map (fun c => (2016673793-1+2*2^9*c.k,96576638517597+c.lower,96577016755296+c.upper)) = pointBounds15356 := by
 decide +kernel
def cuts15357 : List PrefixCut := [⟨52,345278671,345278896⟩,
⟨114,757814732,757815231⟩,
⟨128,850340490,850341050⟩]
theorem checked15357 : checkPrefixCuts (2^48) 2016804865 9 Manual.Count131072.C015357.packed 128 cuts15357 = true := by
 decide +kernel
def pointBounds15357 : List (Nat × Nat × Nat) := [(2016858112,96577836285600,96578214524087),(2016921600,96578248821661,96578627060422)]
theorem point_links_checked15357 : (cuts15357.take 2).map (fun c => (2016804865-1+2*2^9*c.k,96577491006929+c.lower,96577869245191+c.upper)) = pointBounds15357 := by
 decide +kernel
def cuts15358 : List PrefixCut := [⟨48,318462248,318462467⟩,
⟨110,730553656,730554151⟩,
⟨128,852238869,852239441⟩]
theorem checked15358 : checkPrefixCuts (2^48) 2016935937 9 Manual.Count131072.C015358.packed 128 cuts15358 = true := by
 decide +kernel
def pointBounds15358 : List (Nat × Nat × Nat) := [(2016985088,96578659809667,96579038048708),(2017048576,96579071901075,96579450140392)]
theorem point_links_checked15358 : (cuts15358.take 2).map (fun c => (2016935937-1+2*2^9*c.k,96578341347419+c.lower,96578719586241+c.upper)) = pointBounds15358 := by
 decide +kernel
def cuts15359 : List PrefixCut := [⟨44,290672369,290672561⟩,
⟨106,708040426,708040893⟩,
⟨128,852881212,852881778⟩]
theorem checked15359 : checkPrefixCuts (2^48) 2017067009 9 Manual.Count131072.C015359.packed 128 cuts15359 = true := by
 decide +kernel
def pointBounds15359 : List (Nat × Nat × Nat) := [(2017112064,96579484258657,96579862498243),(2017175552,96579901626714,96580279866575)]
theorem point_links_checked15359 : (cuts15359.take 2).map (fun c => (2017067009-1+2*2^9*c.k,96579193586288+c.lower,96579571825682+c.upper)) = pointBounds15359 := by
 decide +kernel
def cuts15360 : List PrefixCut := [⟨40,270839680,270839861⟩,
⟨102,690832664,690833116⟩,
⟨128,861477120,861477685⟩]
theorem checked15360 : checkPrefixCuts (2^48) 2017198081 9 Manual.Count131072.C015360.packed 128 cuts15360 = true := by
 decide +kernel
def pointBounds15360 : List (Nat × Nat × Nat) := [(2017239040,96580317307180,96580695547321),(2017302528,96580737300164,96581115540576)]
theorem point_links_checked15360 : (cuts15360.take 2).map (fun c => (2017198081-1+2*2^9*c.k,96580046467500+c.lower,96580424707460+c.upper)) = pointBounds15360 := by
 decide +kernel
def cuts15361 : List PrefixCut := [⟨36,231336126,231336280⟩,
⟨98,648930696,648931125⟩,
⟨128,841747963,841748520⟩]
theorem checked15361 : checkPrefixCuts (2^48) 2017329153 9 Manual.Count131072.C015361.packed 128 cuts15361 = true := by
 decide +kernel
def pointBounds15361 : List (Nat × Nat × Nat) := [(2017366016,96581139280746,96581517521425),(2017429504,96581556875316,96581935116270)]
theorem point_links_checked15361 : (cuts15361.take 2).map (fun c => (2017329153-1+2*2^9*c.k,96580907944620+c.lower,96581286185145+c.upper)) = pointBounds15361 := by
 decide +kernel
def cuts15362 : List PrefixCut := [⟨32,215137204,215137344⟩,
⟨94,632984504,632984924⟩,
⟨128,863039056,863039628⟩]
theorem checked15362 : checkPrefixCuts (2^48) 2017460225 9 Manual.Count131072.C015362.packed 128 cuts15362 = true := by
 decide +kernel
def pointBounds15362 : List (Nat × Nat × Nat) := [(2017492992,96581964829787,96582343071009),(2017556480,96582382677087,96582760918589)]
theorem point_links_checked15362 : (cuts15362.take 2).map (fun c => (2017460225-1+2*2^9*c.k,96581749692583+c.lower,96582127933665+c.upper)) = pointBounds15362 := by
 decide +kernel
def cuts15363 : List PrefixCut := [⟨28,187640089,187640214⟩,
⟨90,592626657,592627047⟩,
⟨128,846800466,846801026⟩]
theorem checked15363 : checkPrefixCuts (2^48) 2017591297 9 Manual.Count131072.C015363.packed 128 cuts15363 = true := by
 decide +kernel
def pointBounds15363 : List (Nat × Nat × Nat) := [(2017619968,96582800371728,96583178613507),(2017683456,96583205358296,96583583600340)]
theorem point_links_checked15363 : (cuts15363.take 2).map (fun c => (2017591297-1+2*2^9*c.k,96582612731639+c.lower,96582990973293+c.upper)) = pointBounds15363 := by
 decide +kernel
def cuts15364 : List PrefixCut := [⟨24,160844012,160844116⟩,
⟨86,565386445,565386822⟩,
⟨128,847861225,847861786⟩]
theorem checked15364 : checkPrefixCuts (2^48) 2017722369 9 Manual.Count131072.C015364.packed 128 cuts15364 = true := by
 decide +kernel
def pointBounds15364 : List (Nat × Nat × Nat) := [(2017746944,96583620376117,96583998618435),(2017810432,96584024918550,96584403161141)]
theorem point_links_checked15364 : (cuts15364.take 2).map (fun c => (2017722369-1+2*2^9*c.k,96583459532105+c.lower,96583837774319+c.upper)) = pointBounds15364 := by
 decide +kernel
def cuts15365 : List PrefixCut := [⟨20,128750672,128750758⟩,
⟨82,543589855,543590217⟩,
⟨128,852269774,852270337⟩]
theorem checked15365 : checkPrefixCuts (2^48) 2017853441 9 Manual.Count131072.C015365.packed 128 cuts15365 = true := by
 decide +kernel
def pointBounds15365 : List (Nat × Nat × Nat) := [(2017873920,96584436144002,96584814386863),(2017937408,96584850983185,96585229226322)]
theorem point_links_checked15365 : (cuts15365.take 2).map (fun c => (2017853441-1+2*2^9*c.k,96584307393330+c.lower,96584685636105+c.upper)) = pointBounds15365 := by
 decide +kernel
def cuts15366 : List PrefixCut := [⟨16,105867300,105867371⟩,
⟨78,519006590,519006929⟩,
⟨128,843845892,843846448⟩]
theorem checked15366 : checkPrefixCuts (2^48) 2017984513 9 Manual.Count131072.C015366.packed 128 cuts15366 = true := by
 decide +kernel
def pointBounds15366 : List (Nat × Nat × Nat) := [(2018000896,96585265530404,96585643773813),(2018064384,96585678669694,96586056913371)]
theorem point_links_checked15366 : (cuts15366.take 2).map (fun c => (2017984513-1+2*2^9*c.k,96585159663104+c.lower,96585537906442+c.upper)) = pointBounds15366 := by
 decide +kernel
def cuts15367 : List PrefixCut := [⟨12,82707905,82707958⟩,
⟨74,495821189,495821512⟩,
⟨128,851182994,851183552⟩]
theorem checked15367 : checkPrefixCuts (2^48) 2018115585 9 Manual.Count131072.C015367.packed 128 cuts15367 = true := by
 decide +kernel
def pointBounds15367 : List (Nat × Nat × Nat) := [(2018127872,96586086216901,96586464460848),(2018191360,96586499330185,96586877574402)]
theorem point_links_checked15367 : (cuts15367.take 2).map (fun c => (2018115585-1+2*2^9*c.k,96586003508996+c.lower,96586381752890+c.upper)) = pointBounds15367 := by
 decide +kernel
def cuts15368 : List PrefixCut := [⟨8,52159823,52159857⟩,
⟨70,469570532,469570837⟩,
⟨128,844991602,844992152⟩]
theorem checked15368 : checkPrefixCuts (2^48) 2018246657 9 Manual.Count131072.C015368.packed 128 cuts15368 = true := by
 decide +kernel
def pointBounds15368 : List (Nat × Nat × Nat) := [(2018254848,96586906851813,96587285096299),(2018318336,96587324262522,96587702507279)]
theorem point_links_checked15368 : (cuts15368.take 2).map (fun c => (2018246657-1+2*2^9*c.k,96586854691990+c.lower,96587232936442+c.upper)) = pointBounds15368 := by
 decide +kernel
def cuts15369 : List PrefixCut := [⟨4,27891171,27891190⟩,
⟨66,445414874,445415170⟩,
⟨128,853443082,853443652⟩]
theorem checked15369 : checkPrefixCuts (2^48) 2018377729 9 Manual.Count131072.C015369.packed 128 cuts15369 = true := by
 decide +kernel
def pointBounds15369 : List (Nat × Nat × Nat) := [(2018381824,96587727574763,96588105819784),(2018445312,96588145098466,96588523343764),(2018508800,96588553126674,96588931372246)]
theorem point_links_checked15369 : (cuts15369.take 3).map (fun c => (2018377729-1+2*2^9*c.k,96587699683592+c.lower,96588077928594+c.upper)) = pointBounds15369 := by
 decide +kernel
def cuts15370 : List PrefixCut := [⟨62,415963649,415963922⟩,
⟨124,824245007,824245550⟩,
⟨128,849622728,849623289⟩]
theorem checked15370 : checkPrefixCuts (2^48) 2018508801 9 Manual.Count131072.C015370.packed 128 cuts15370 = true := by
 decide +kernel
def pointBounds15370 : List (Nat × Nat × Nat) := [(2018572288,96588969090323,96589347336168),(2018635776,96589377371681,96589755617796)]
theorem point_links_checked15370 : (cuts15370.take 2).map (fun c => (2018508801-1+2*2^9*c.k,96588553126674+c.lower,96588931372246+c.upper)) = pointBounds15370 := by
 decide +kernel
def cuts15371 : List PrefixCut := [⟨58,389862612,389862867⟩,
⟨120,801046349,801046877⟩,
⟨128,854865986,854866549⟩]
theorem checked15371 : checkPrefixCuts (2^48) 2018639873 9 Manual.Count131072.C015371.packed 128 cuts15371 = true := by
 decide +kernel
def pointBounds15371 : List (Nat × Nat × Nat) := [(2018699264,96589792612014,96590170858402),(2018762752,96590203795751,96590582042412)]
theorem point_links_checked15371 : (cuts15371.take 2).map (fun c => (2018639873-1+2*2^9*c.k,96589402749402+c.lower,96589780995535+c.upper)) = pointBounds15371 := by
 decide +kernel
def cuts15372 : List PrefixCut := [⟨54,367389958,367390202⟩,
⟨116,790538268,790538784⟩,
⟨128,869450103,869450673⟩]
theorem checked15372 : checkPrefixCuts (2^48) 2018770945 9 Manual.Count131072.C015372.packed 128 cuts15372 = true := by
 decide +kernel
def pointBounds15372 : List (Nat × Nat × Nat) := [(2018826240,96590625005346,96591003252286),(2018889728,96591048153656,96591426400868)]
theorem point_links_checked15372 : (cuts15372.take 2).map (fun c => (2018770945-1+2*2^9*c.k,96590257615388+c.lower,96590635862084+c.upper)) = pointBounds15372 := by
 decide +kernel
def cuts15373 : List PrefixCut := [⟨50,331954274,331954495⟩,
⟨112,748105145,748105640⟩,
⟨128,851966571,851967136⟩]
theorem checked15373 : checkPrefixCuts (2^48) 2018902017 9 Manual.Count131072.C015373.packed 128 cuts15373 = true := by
 decide +kernel
def pointBounds15373 : List (Nat × Nat × Nat) := [(2018953216,96591459019765,96591837267252),(2019016704,96591875170636,96592253418397)]
theorem point_links_checked15373 : (cuts15373.take 2).map (fun c => (2018902017-1+2*2^9*c.k,96591127065491+c.lower,96591505312757+c.upper)) = pointBounds15373 := by
 decide +kernel
def cuts15374 : List PrefixCut := [⟨46,307257684,307257881⟩,
⟨108,726309956,726310431⟩,
⟨128,861112064,861112628⟩]
theorem checked15374 : checkPrefixCuts (2^48) 2019033089 9 Manual.Count131072.C015374.packed 128 cuts15374 = true := by
 decide +kernel
def pointBounds15374 : List (Nat × Nat × Nat) := [(2019080192,96592286289746,96592664537774),(2019143680,96592705342018,96593083590324)]
theorem point_links_checked15374 : (cuts15374.take 2).map (fun c => (2019033089-1+2*2^9*c.k,96591979032062+c.lower,96592357279893+c.upper)) = pointBounds15374 := by
 decide +kernel
def cuts15375 : List PrefixCut := [⟨42,274339638,274339818⟩,
⟨104,694480688,694481147⟩,
⟨128,855061974,855062539⟩]
theorem checked15375 : checkPrefixCuts (2^48) 2019164161 9 Manual.Count131072.C015375.packed 128 cuts15375 = true := by
 decide +kernel
def pointBounds15375 : List (Nat × Nat × Nat) := [(2019207168,96593114483764,96593492732339),(2019270656,96593534624814,96593912873668)]
theorem point_links_checked15375 : (cuts15375.take 2).map (fun c => (2019164161-1+2*2^9*c.k,96592840144126+c.lower,96593218392521+c.upper)) = pointBounds15375 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000167
