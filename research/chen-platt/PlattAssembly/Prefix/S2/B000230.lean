import PlattAssemblyKernel
import PlattCertificates.Count131072.C017360
import PlattCertificates.Count131072.C017361
import PlattCertificates.Count131072.C017362
import PlattCertificates.Count131072.C017363
import PlattCertificates.Count131072.C017364
import PlattCertificates.Count131072.C017365
import PlattCertificates.Count131072.C017366
import PlattCertificates.Count131072.C017367
import PlattCertificates.Count131072.C017368
import PlattCertificates.Count131072.C017369
import PlattCertificates.Count131072.C017370
import PlattCertificates.Count131072.C017371
import PlattCertificates.Count131072.C017372
import PlattCertificates.Count131072.C017373
import PlattCertificates.Count131072.C017374
import PlattCertificates.Count131072.C017375
import PlattCertificates.Count131072.C017376
import PlattCertificates.Count131072.C017377
import PlattCertificates.Count131072.C017378
import PlattCertificates.Count131072.C017379
import PlattCertificates.Count131072.C017380
import PlattCertificates.Count131072.C017381
import PlattCertificates.Count131072.C017382
import PlattCertificates.Count131072.C017383
import PlattCertificates.Count131072.C017384
import PlattCertificates.Count131072.C017385
import PlattCertificates.Count131072.C017386
import PlattCertificates.Count131072.C017387
import PlattCertificates.Count131072.C017388
import PlattCertificates.Count131072.C017389
import PlattCertificates.Count131072.C017390
import PlattCertificates.Count131072.C017391
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000230
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17360 : List PrefixCut := [⟨26,152014720,152014814⟩,
⟨96,564211394,564211743⟩,
⟨128,746596225,746596691⟩]
theorem checked17360 : checkPrefixCuts (2^48) 2279342081 9 Manual.Count131072.C017360.packed 128 cuts17360 = true := by
 decide +kernel
def pointBounds17360 : List (Nat × Nat × Nat) := [(2279368704,98180765648735,98181144909271),(2279440384,98181177845409,98181557106200)]
theorem point_links_checked17360 : (cuts17360.take 2).map (fun c => (2279342081-1+2*2^9*c.k,98180613634015+c.lower,98180992894457+c.upper)) = pointBounds17360 := by
 decide +kernel
def cuts17361 : List PrefixCut := [⟨38,219302900,219303041⟩,
⟨108,626411155,626411552⟩,
⟨128,744577574,744578042⟩]
theorem checked17361 : checkPrefixCuts (2^48) 2279473153 9 Manual.Count131072.C017361.packed 128 cuts17361 = true := by
 decide +kernel
def pointBounds17361 : List (Nat × Nat × Nat) := [(2279512064,98181579533140,98181958794189),(2279583744,98181986641395,98182365902700)]
theorem point_links_checked17361 : (cuts17361.take 2).map (fun c => (2279473153-1+2*2^9*c.k,98181360230240+c.lower,98181739491148+c.upper)) = pointBounds17361 := by
 decide +kernel
def cuts17362 : List PrefixCut := [⟨50,291398492,291398673⟩,
⟨120,696258612,696259041⟩,
⟨128,741941939,741942396⟩]
theorem checked17362 : checkPrefixCuts (2^48) 2279604225 9 Manual.Count131072.C017362.packed 128 cuts17362 = true := by
 decide +kernel
def pointBounds17362 : List (Nat × Nat × Nat) := [(2279655424,98182396206306,98182775467863),(2279727104,98182801066426,98183180328231)]
theorem point_links_checked17362 : (cuts17362.take 2).map (fun c => (2279604225-1+2*2^9*c.k,98182104807814+c.lower,98182484069190+c.upper)) = pointBounds17362 := by
 decide +kernel
def cuts17363 : List PrefixCut := [⟨62,359534502,359534726⟩,
⟨128,751529467,751529931⟩]
theorem checked17363 : checkPrefixCuts (2^48) 2279735297 9 Manual.Count131072.C017363.packed 128 cuts17363 = true := by
 decide +kernel
def pointBounds17363 : List (Nat × Nat × Nat) := [(2279798784,98183206284255,98183585546312)]
theorem point_links_checked17363 : (cuts17363.take 1).map (fun c => (2279735297-1+2*2^9*c.k,98182846749753+c.lower,98183226011586+c.upper)) = pointBounds17363 := by
 decide +kernel
def cuts17364 : List PrefixCut := [⟨4,23087213,23087228⟩,
⟨74,432847544,432847813⟩,
⟨128,746424617,746425075⟩]
theorem checked17364 : checkPrefixCuts (2^48) 2279866369 9 Manual.Count131072.C017364.packed 128 cuts17364 = true := by
 decide +kernel
def pointBounds17364 : List (Nat × Nat × Nat) := [(2279870464,98183621366433,98184000628745),(2279942144,98184031126764,98184410389330)]
theorem point_links_checked17364 : (cuts17364.take 2).map (fun c => (2279866369-1+2*2^9*c.k,98183598279220+c.lower,98183977541517+c.upper)) = pointBounds17364 := by
 decide +kernel
def cuts17365 : List PrefixCut := [⟨16,92590192,92590250⟩,
⟨86,508867699,508868010⟩,
⟨128,758232887,758233354⟩]
theorem checked17365 : checkPrefixCuts (2^48) 2279997441 9 Manual.Count131072.C017365.packed 128 cuts17365 = true := by
 decide +kernel
def pointBounds17365 : List (Nat × Nat × Nat) := [(2280013824,98184437294029,98184816556842),(2280085504,98184853571536,98185232834602)]
theorem point_links_checked17365 : (cuts17365.take 2).map (fun c => (2279997441-1+2*2^9*c.k,98184344703837+c.lower,98184723966592+c.upper)) = pointBounds17365 := by
 decide +kernel
def cuts17366 : List PrefixCut := [⟨28,162825492,162825591⟩,
⟨98,570188897,570189250⟩,
⟨128,743746488,743746953⟩]
theorem checked17366 : checkPrefixCuts (2^48) 2280128513 9 Manual.Count131072.C017366.packed 128 cuts17366 = true := by
 decide +kernel
def pointBounds17366 : List (Nat × Nat × Nat) := [(2280157184,98185265762216,98185645025537),(2280228864,98185673125621,98186052389196)]
theorem point_links_checked17366 : (cuts17366.take 2).map (fun c => (2280128513-1+2*2^9*c.k,98185102936724+c.lower,98185482199946+c.upper)) = pointBounds17366 := by
 decide +kernel
def cuts17367 : List PrefixCut := [⟨40,229719481,229719622⟩,
⟨110,641624417,641624807⟩,
⟨128,749381635,749382095⟩]
theorem checked17367 : checkPrefixCuts (2^48) 2280259585 9 Manual.Count131072.C017367.packed 128 cuts17367 = true := by
 decide +kernel
def pointBounds17367 : List (Nat × Nat × Nat) := [(2280300544,98186076402693,98186455666521),(2280372224,98186488307629,98186867571706)]
theorem point_links_checked17367 : (cuts17367.take 2).map (fun c => (2280259585-1+2*2^9*c.k,98185846683212+c.lower,98186225946899+c.upper)) = pointBounds17367 := by
 decide +kernel
def cuts17368 : List PrefixCut := [⟨52,311046930,311047124⟩,
⟨122,724900880,724901334⟩,
⟨128,760817792,760818268⟩]
theorem checked17368 : checkPrefixCuts (2^48) 2280390657 9 Manual.Count131072.C017368.packed 128 cuts17368 = true := by
 decide +kernel
def pointBounds17368 : List (Nat × Nat × Nat) := [(2280443904,98186907111777,98187286376118),(2280515584,98187320965727,98187700230328)]
theorem point_links_checked17368 : (cuts17368.take 2).map (fun c => (2280390657-1+2*2^9*c.k,98186596064847+c.lower,98186975328994+c.upper)) = pointBounds17368 := by
 decide +kernel
def cuts17369 : List PrefixCut := [⟨64,367309522,367309751⟩,
⟨128,738064209,738064664⟩]
theorem checked17369 : checkPrefixCuts (2^48) 2280521729 9 Manual.Count131072.C017369.packed 128 cuts17369 = true := by
 decide +kernel
def pointBounds17369 : List (Nat × Nat × Nat) := [(2280587264,98187724192161,98188103457013)]
theorem point_links_checked17369 : (cuts17369.take 1).map (fun c => (2280521729-1+2*2^9*c.k,98187356882639+c.lower,98187736147262+c.upper)) = pointBounds17369 := by
 decide +kernel
def cuts17370 : List PrefixCut := [⟨6,36778683,36778706⟩,
⟨76,451827622,451827906⟩,
⟨128,756904327,756904803⟩]
theorem checked17370 : checkPrefixCuts (2^48) 2280652801 9 Manual.Count131072.C017370.packed 128 cuts17370 = true := by
 decide +kernel
def pointBounds17370 : List (Nat × Nat × Nat) := [(2280658944,98188131725531,98188510990632),(2280730624,98188546774470,98188926039832)]
theorem point_links_checked17370 : (cuts17370.take 2).map (fun c => (2280652801-1+2*2^9*c.k,98188094946848+c.lower,98188474211926+c.upper)) = pointBounds17370 := by
 decide +kernel
def cuts17371 : List PrefixCut := [⟨18,106256851,106256919⟩,
⟨88,512764555,512764878⟩,
⟨128,747975399,747975867⟩]
theorem checked17371 : checkPrefixCuts (2^48) 2280783873 9 Manual.Count131072.C017371.packed 128 cuts17371 = true := by
 decide +kernel
def pointBounds17371 : List (Nat × Nat × Nat) := [(2280802304,98188958108026,98189337373648),(2280873984,98189364615730,98189743881607)]
theorem point_links_checked17371 : (cuts17371.take 2).map (fun c => (2280783873-1+2*2^9*c.k,98188851851175+c.lower,98189231116729+c.upper)) = pointBounds17371 := by
 decide +kernel
def cuts17372 : List PrefixCut := [⟨30,176467089,176467198⟩,
⟨100,589489556,589489916⟩,
⟨128,753979172,753979635⟩]
theorem checked17372 : checkPrefixCuts (2^48) 2280914945 9 Manual.Count131072.C017372.packed 128 cuts17372 = true := by
 decide +kernel
def pointBounds17372 : List (Nat × Nat × Nat) := [(2280945664,98189776293663,98190155559794),(2281017344,98190189316130,98190568582512)]
theorem point_links_checked17372 : (cuts17372.take 2).map (fun c => (2280914945-1+2*2^9*c.k,98189599826574+c.lower,98189979092596+c.upper)) = pointBounds17372 := by
 decide +kernel
def cuts17373 : List PrefixCut := [⟨42,248149576,248149727⟩,
⟨112,655593420,655593825⟩,
⟨128,749740484,749740947⟩]
theorem checked17373 : checkPrefixCuts (2^48) 2281046017 9 Manual.Count131072.C017373.packed 128 cuts17373 = true := by
 decide +kernel
def pointBounds17373 : List (Nat × Nat × Nat) := [(2281089024,98190601955322,98190981221958),(2281160704,98191009399166,98191388666056)]
theorem point_links_checked17373 : (cuts17373.take 2).map (fun c => (2281046017-1+2*2^9*c.k,98190353805746+c.lower,98190733072231+c.upper)) = pointBounds17373 := by
 decide +kernel
def cuts17374 : List PrefixCut := [⟨54,309582213,309582410⟩,
⟨124,719961636,719962091⟩,
⟨128,741677082,741677551⟩]
theorem checked17374 : checkPrefixCuts (2^48) 2281177089 9 Manual.Count131072.C017374.packed 128 cuts17374 = true := by
 decide +kernel
def pointBounds17374 : List (Nat × Nat × Nat) := [(2281232384,98191413128443,98191792395588),(2281304064,98191823507866,98192202775269)]
theorem point_links_checked17374 : (cuts17374.take 2).map (fun c => (2281177089-1+2*2^9*c.k,98191103546230+c.lower,98191482813178+c.upper)) = pointBounds17374 := by
 decide +kernel
def cuts17375 : List PrefixCut := [⟨66,391365373,391365619⟩,
⟨128,752738753,752739232⟩]
theorem checked17375 : checkPrefixCuts (2^48) 2281308161 9 Manual.Count131072.C017375.packed 128 cuts17375 = true := by
 decide +kernel
def pointBounds17375 : List (Nat × Nat × Nat) := [(2281375744,98192236588685,98192615856348)]
theorem point_links_checked17375 : (cuts17375.take 1).map (fun c => (2281308161-1+2*2^9*c.k,98191845223312+c.lower,98192224490729+c.upper)) = pointBounds17375 := by
 decide +kernel
def cuts17376 : List PrefixCut := [⟨8,45278912,45278941⟩,
⟨78,451918366,451918647⟩,
⟨128,743689168,743689633⟩]
theorem checked17376 : checkPrefixCuts (2^48) 2281439233 9 Manual.Count131072.C017376.packed 128 cuts17376 = true := by
 decide +kernel
def pointBounds17376 : List (Nat × Nat × Nat) := [(2281447424,98192643240977,98193022508902),(2281519104,98193049880431,98193429148608)]
theorem point_links_checked17376 : (cuts17376.take 2).map (fun c => (2281439233-1+2*2^9*c.k,98192597962065+c.lower,98192977229961+c.upper)) = pointBounds17376 := by
 decide +kernel
def cuts17377 : List PrefixCut := [⟨20,118927106,118927181⟩,
⟨90,521593273,521593594⟩,
⟨128,744263286,744263747⟩]
theorem checked17377 : checkPrefixCuts (2^48) 2281570305 9 Manual.Count131072.C017377.packed 128 cuts17377 = true := by
 decide +kernel
def pointBounds17377 : List (Nat × Nat × Nat) := [(2281590784,98193460578339,98193839846775),(2281662464,98193863244506,98194242513188)]
theorem point_links_checked17377 : (cuts17377.take 2).map (fun c => (2281570305-1+2*2^9*c.k,98193341651233+c.lower,98193720919594+c.upper)) = pointBounds17377 := by
 decide +kernel
def cuts17378 : List PrefixCut := [⟨32,189975872,189975985⟩,
⟨102,598291349,598291714⟩,
⟨128,749648518,749648980⟩]
theorem checked17378 : checkPrefixCuts (2^48) 2281701377 9 Manual.Count131072.C017378.packed 128 cuts17378 = true := by
 decide +kernel
def pointBounds17378 : List (Nat × Nat × Nat) := [(2281734144,98194275890391,98194655159326),(2281805824,98194684205868,98195063475055)]
theorem point_links_checked17378 : (cuts17378.take 2).map (fun c => (2281701377-1+2*2^9*c.k,98194085914519+c.lower,98194465183341+c.upper)) = pointBounds17378 := by
 decide +kernel
def cuts17379 : List PrefixCut := [⟨44,257685569,257685725⟩,
⟨114,663014997,663015405⟩,
⟨128,747385077,747385536⟩]
theorem checked17379 : checkPrefixCuts (2^48) 2281832449 9 Manual.Count131072.C017379.packed 128 cuts17379 = true := by
 decide +kernel
def pointBounds17379 : List (Nat × Nat × Nat) := [(2281877504,98195093248606,98195472518046),(2281949184,98195498578034,98195877847726)]
theorem point_links_checked17379 : (cuts17379.take 2).map (fun c => (2281832449-1+2*2^9*c.k,98194835563037+c.lower,98195214832321+c.upper)) = pointBounds17379 := by
 decide +kernel
def cuts17380 : List PrefixCut := [⟨56,331431048,331431255⟩,
⟨126,745492312,745492770⟩,
⟨128,757703036,757703501⟩]
theorem checked17380 : checkPrefixCuts (2^48) 2281963521 9 Manual.Count131072.C017380.packed 128 cuts17380 = true := by
 decide +kernel
def pointBounds17380 : List (Nat × Nat × Nat) := [(2282020864,98195914379162,98196293649112),(2282092544,98196328440426,98196707710627)]
theorem point_links_checked17380 : (cuts17380.take 2).map (fun c => (2281963521-1+2*2^9*c.k,98195582948114+c.lower,98195962217857+c.upper)) = pointBounds17380 := by
 decide +kernel
def cuts17381 : List PrefixCut := [⟨68,396903973,396904223⟩,
⟨128,746065802,746066270⟩]
theorem checked17381 : checkPrefixCuts (2^48) 2282094593 9 Manual.Count131072.C017381.packed 128 cuts17381 = true := by
 decide +kernel
def pointBounds17381 : List (Nat × Nat × Nat) := [(2282164224,98196737555123,98197116825581)]
theorem point_links_checked17381 : (cuts17381.take 1).map (fun c => (2282094593-1+2*2^9*c.k,98196340651150+c.lower,98196719921358+c.upper)) = pointBounds17381 := by
 decide +kernel
def cuts17382 : List PrefixCut := [⟨10,53279956,53279990⟩,
⟨80,465945545,465945838⟩,
⟨128,752065916,752066383⟩]
theorem checked17382 : checkPrefixCuts (2^48) 2282225665 9 Manual.Count131072.C017382.packed 128 cuts17382 = true := by
 decide +kernel
def pointBounds17382 : List (Nat × Nat × Nat) := [(2282235904,98197139996908,98197519267618),(2282307584,98197552662497,98197931933466)]
theorem point_links_checked17382 : (cuts17382.take 2).map (fun c => (2282225665-1+2*2^9*c.k,98197086716952+c.lower,98197465987628+c.upper)) = pointBounds17382 := by
 decide +kernel
def cuts17383 : List PrefixCut := [⟨22,125299031,125299109⟩,
⟨92,532389106,532389434⟩,
⟨128,740307230,740307689⟩]
theorem checked17383 : checkPrefixCuts (2^48) 2282356737 9 Manual.Count131072.C017383.packed 128 cuts17383 = true := by
 decide +kernel
def pointBounds17383 : List (Nat × Nat × Nat) := [(2282379264,98197964081899,98198343353120),(2282450944,98198371171974,98198750443445)]
theorem point_links_checked17383 : (cuts17383.take 2).map (fun c => (2282356737-1+2*2^9*c.k,98197838782868+c.lower,98198218054011+c.upper)) = pointBounds17383 := by
 decide +kernel
def cuts17384 : List PrefixCut := [⟨34,197926039,197926161⟩,
⟨104,609923189,609923564⟩,
⟨128,750499925,750500387⟩]
theorem checked17384 : checkPrefixCuts (2^48) 2282487809 9 Manual.Count131072.C017384.packed 128 cuts17384 = true := by
 decide +kernel
def pointBounds17384 : List (Nat × Nat × Nat) := [(2282522624,98198777016137,98199156287861),(2282594304,98199189013287,98199568285264)]
theorem point_links_checked17384 : (cuts17384.take 2).map (fun c => (2282487809-1+2*2^9*c.k,98198579090098+c.lower,98198958361700+c.upper)) = pointBounds17384 := by
 decide +kernel
def cuts17385 : List PrefixCut := [⟨46,275230118,275230286⟩,
⟨116,695093138,695093562⟩,
⟨128,766980249,766980717⟩]
theorem checked17385 : checkPrefixCuts (2^48) 2282618881 9 Manual.Count131072.C017385.packed 128 cuts17385 = true := by
 decide +kernel
def pointBounds17385 : List (Nat × Nat × Nat) := [(2282665984,98199604820141,98199984092373),(2282737664,98200024683161,98200403955649)]
theorem point_links_checked17385 : (cuts17385.take 2).map (fun c => (2282618881-1+2*2^9*c.k,98199329590023+c.lower,98199708862087+c.upper)) = pointBounds17385 := by
 decide +kernel
def cuts17386 : List PrefixCut := [⟨58,347716053,347716269⟩,
⟨128,757811911,757812380⟩]
theorem checked17386 : checkPrefixCuts (2^48) 2282749953 9 Manual.Count131072.C017386.packed 128 cuts17386 = true := by
 decide +kernel
def pointBounds17386 : List (Nat × Nat × Nat) := [(2282809344,98200444286325,98200823559073),(2282881024,98200854382183,98201233655184)]
theorem point_links_checked17386 : (cuts17386.take 2).map (fun c => (2282749953-1+2*2^9*c.k,98200096570272+c.lower,98200475842804+c.upper)) = pointBounds17386 := by
 decide +kernel
def cuts17387 : List PrefixCut := [⟨70,401822143,401822393⟩,
⟨128,733602571,733603026⟩]
theorem checked17387 : checkPrefixCuts (2^48) 2282881025 9 Manual.Count131072.C017387.packed 128 cuts17387 = true := by
 decide +kernel
def pointBounds17387 : List (Nat × Nat × Nat) := [(2282952704,98201256204326,98201635477577)]
theorem point_links_checked17387 : (cuts17387.take 1).map (fun c => (2282881025-1+2*2^9*c.k,98200854382183+c.lower,98201233655184+c.upper)) = pointBounds17387 := by
 decide +kernel
def cuts17388 : List PrefixCut := [⟨12,70522277,70522318⟩,
⟨82,486743973,486744268⟩,
⟨128,761546687,761547149⟩]
theorem checked17388 : checkPrefixCuts (2^48) 2283012097 9 Manual.Count131072.C017388.packed 128 cuts17388 = true := by
 decide +kernel
def pointBounds17388 : List (Nat × Nat × Nat) := [(2283024384,98201658507031,98202037780528),(2283096064,98202074728727,98202454002478)]
theorem point_links_checked17388 : (cuts17388.take 2).map (fun c => (2283012097-1+2*2^9*c.k,98201587984754+c.lower,98201967258210+c.upper)) = pointBounds17388 := by
 decide +kernel
def cuts17389 : List PrefixCut := [⟨24,142515461,142515545⟩,
⟨94,546382961,546383300⟩,
⟨128,744490375,744490837⟩]
theorem checked17389 : checkPrefixCuts (2^48) 2283143169 9 Manual.Count131072.C017389.packed 128 cuts17389 = true := by
 decide +kernel
def pointBounds17389 : List (Nat × Nat × Nat) := [(2283167744,98202492046902,98202871320904),(2283239424,98202895914402,98203275188659)]
theorem point_links_checked17389 : (cuts17389.take 2).map (fun c => (2283143169-1+2*2^9*c.k,98202349531441+c.lower,98202728805359+c.upper)) = pointBounds17389 := by
 decide +kernel
def cuts17390 : List PrefixCut := [⟨36,203775027,203775156⟩,
⟨106,605274992,605275367⟩,
⟨128,731257336,731257785⟩]
theorem checked17390 : checkPrefixCuts (2^48) 2283274241 9 Manual.Count131072.C017390.packed 128 cuts17390 = true := by
 decide +kernel
def pointBounds17390 : List (Nat × Nat × Nat) := [(2283311104,98203297796843,98203677071352),(2283382784,98203699296808,98204078571563)]
theorem point_links_checked17390 : (cuts17390.take 2).map (fun c => (2283274241-1+2*2^9*c.k,98203094021816+c.lower,98203473296196+c.upper)) = pointBounds17390 := by
 decide +kernel
def cuts17391 : List PrefixCut := [⟨48,282408032,282408204⟩,
⟨118,696948892,696949318⟩,
⟨128,753773130,753773592⟩]
theorem checked17391 : checkPrefixCuts (2^48) 2283405313 9 Manual.Count131072.C017391.packed 128 cuts17391 = true := by
 decide +kernel
def pointBounds17391 : List (Nat × Nat × Nat) := [(2283454464,98204107687184,98204486962185),(2283526144,98204522228044,98204901503299)]
theorem point_links_checked17391 : (cuts17391.take 2).map (fun c => (2283405313-1+2*2^9*c.k,98203825279152+c.lower,98204204553981+c.upper)) = pointBounds17391 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000230
