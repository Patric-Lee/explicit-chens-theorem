import PlattAssemblyKernel
import PlattCertificates.Count131072.C018352
import PlattCertificates.Count131072.C018353
import PlattCertificates.Count131072.C018354
import PlattCertificates.Count131072.C018355
import PlattCertificates.Count131072.C018356
import PlattCertificates.Count131072.C018357
import PlattCertificates.Count131072.C018358
import PlattCertificates.Count131072.C018359
import PlattCertificates.Count131072.C018360
import PlattCertificates.Count131072.C018361
import PlattCertificates.Count131072.C018362
import PlattCertificates.Count131072.C018363
import PlattCertificates.Count131072.C018364
import PlattCertificates.Count131072.C018365
import PlattCertificates.Count131072.C018366
import PlattCertificates.Count131072.C018367
import PlattCertificates.Count131072.C018368
import PlattCertificates.Count131072.C018369
import PlattCertificates.Count131072.C018370
import PlattCertificates.Count131072.C018371
import PlattCertificates.Count131072.C018372
import PlattCertificates.Count131072.C018373
import PlattCertificates.Count131072.C018374
import PlattCertificates.Count131072.C018375
import PlattCertificates.Count131072.C018376
import PlattCertificates.Count131072.C018377
import PlattCertificates.Count131072.C018378
import PlattCertificates.Count131072.C018379
import PlattCertificates.Count131072.C018380
import PlattCertificates.Count131072.C018381
import PlattCertificates.Count131072.C018382
import PlattCertificates.Count131072.C018383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000261
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18352 : List PrefixCut := [⟨26,144979418,144979505⟩,
⟨100,558530021,558530355⟩,
⟨128,712731964,712732388⟩]
theorem checked18352 : checkPrefixCuts (2^48) 2409365505 9 Manual.Count131072.C018352.packed 128 cuts18352 = true := by
 decide +kernel
def pointBounds18352 : List (Nat × Nat × Nat) := [(2409392128,98904381087378,98904760791261),(2409467904,98904794637981,98905174342111)]
theorem point_links_checked18352 : (cuts18352.take 2).map (fun c => (2409365505-1+2*2^9*c.k,98904236107960+c.lower,98904615811756+c.upper)) = pointBounds18352 := by
 decide +kernel
def cuts18353 : List PrefixCut := [⟨46,248354733,248354885⟩,
⟨120,662112964,662113366⟩,
⟨128,708487649,708488080⟩]
theorem checked18353 : checkPrefixCuts (2^48) 2409496577 9 Manual.Count131072.C018353.packed 128 cuts18353 = true := by
 decide +kernel
def pointBounds18353 : List (Nat × Nat × Nat) := [(2409543680,98905197194657,98905576899029),(2409619456,98905610952888,98905990657510)]
theorem point_links_checked18353 : (cuts18353.take 2).map (fun c => (2409496577-1+2*2^9*c.k,98904948839924+c.lower,98905328544144+c.upper)) = pointBounds18353 := by
 decide +kernel
def cuts18354 : List PrefixCut := [⟨66,369940375,369940600⟩,
⟨128,717560382,717560816⟩]
theorem checked18354 : checkPrefixCuts (2^48) 2409627649 9 Manual.Count131072.C018354.packed 128 cuts18354 = true := by
 decide +kernel
def pointBounds18354 : List (Nat × Nat × Nat) := [(2409695232,98906027267948,98906406972824)]
theorem point_links_checked18354 : (cuts18354.take 1).map (fun c => (2409627649-1+2*2^9*c.k,98905657327573+c.lower,98906037032224+c.upper)) = pointBounds18354 := by
 decide +kernel
def cuts18355 : List PrefixCut := [⟨12,68331487,68331530⟩,
⟨86,474808752,474809039⟩,
⟨128,704088979,704089406⟩]
theorem checked18355 : checkPrefixCuts (2^48) 2409758721 9 Manual.Count131072.C018355.packed 128 cuts18355 = true := by
 decide +kernel
def pointBounds18355 : List (Nat × Nat × Nat) := [(2409771008,98906443219442,98906822924570),(2409846784,98906849696707,98907229402079)]
theorem point_links_checked18355 : (cuts18355.take 2).map (fun c => (2409758721-1+2*2^9*c.k,98906374887955+c.lower,98906754593040+c.upper)) = pointBounds18355 := by
 decide +kernel
def cuts18356 : List PrefixCut := [⟨32,174965052,174965160⟩,
⟨106,585271111,585271470⟩,
⟨128,710824756,710825190⟩]
theorem checked18356 : checkPrefixCuts (2^48) 2409889793 9 Manual.Count131072.C018356.packed 128 cuts18356 = true := by
 decide +kernel
def pointBounds18356 : List (Nat × Nat × Nat) := [(2409922560,98907253941986,98907633647606),(2409998336,98907664248045,98908043953916)]
theorem point_links_checked18356 : (cuts18356.take 2).map (fun c => (2409889793-1+2*2^9*c.k,98907078976934+c.lower,98907458682446+c.upper)) = pointBounds18356 := by
 decide +kernel
def cuts18357 : List PrefixCut := [⟨52,286024220,286024392⟩,
⟨126,694085391,694085812⟩,
⟨128,705764116,705764544⟩]
theorem checked18357 : checkPrefixCuts (2^48) 2410020865 9 Manual.Count131072.C018357.packed 128 cuts18357 = true := by
 decide +kernel
def pointBounds18357 : List (Nat × Nat × Nat) := [(2410074112,98908075825910,98908455532028),(2410149888,98908483887081,98908863593448)]
theorem point_links_checked18357 : (cuts18357.take 2).map (fun c => (2410020865-1+2*2^9*c.k,98907789801690+c.lower,98908169507636+c.upper)) = pointBounds18357 := by
 decide +kernel
def cuts18358 : List PrefixCut := [⟨72,396136069,396136310⟩,
⟨128,706309645,706310076⟩]
theorem checked18358 : checkPrefixCuts (2^48) 2410151937 9 Manual.Count131072.C018358.packed 128 cuts18358 = true := by
 decide +kernel
def pointBounds18358 : List (Nat × Nat × Nat) := [(2410225664,98908891701875,98909271408490)]
theorem point_links_checked18358 : (cuts18358.take 1).map (fun c => (2410151937-1+2*2^9*c.k,98908495565806+c.lower,98908875272180+c.upper)) = pointBounds18358 := by
 decide +kernel
def cuts18359 : List PrefixCut := [⟨18,102066070,102066129⟩,
⟨92,510439160,510439466⟩,
⟨128,708256678,708257101⟩]
theorem checked18359 : checkPrefixCuts (2^48) 2410283009 9 Manual.Count131072.C018359.packed 128 cuts18359 = true := by
 decide +kernel
def pointBounds18359 : List (Nat × Nat × Nat) := [(2410301440,98909303941521,98909683648385),(2410377216,98909712314611,98910092021722)]
theorem point_links_checked18359 : (cuts18359.take 2).map (fun c => (2410283009-1+2*2^9*c.k,98909201875451+c.lower,98909581582256+c.upper)) = pointBounds18359 := by
 decide +kernel
def cuts18360 : List PrefixCut := [⟨38,212644672,212644799⟩,
⟨112,615270300,615270673⟩,
⟨128,703547315,703547741⟩]
theorem checked18360 : checkPrefixCuts (2^48) 2410414081 9 Manual.Count131072.C018360.packed 128 cuts18360 = true := by
 decide +kernel
def pointBounds18360 : List (Nat × Nat × Nat) := [(2410452992,98910122776801,98910502484156),(2410528768,98910525402429,98910905110030)]
theorem point_links_checked18360 : (cuts18360.take 2).map (fun c => (2410414081-1+2*2^9*c.k,98909910132129+c.lower,98910289839357+c.upper)) = pointBounds18360 := by
 decide +kernel
def cuts18361 : List PrefixCut := [⟨58,322859965,322860162⟩,
⟨128,702808494,702808924⟩]
theorem checked18361 : checkPrefixCuts (2^48) 2410545153 9 Manual.Count131072.C018361.packed 128 cuts18361 = true := by
 decide +kernel
def pointBounds18361 : List (Nat × Nat × Nat) := [(2410604544,98910936539409,98911316247260)]
theorem point_links_checked18361 : (cuts18361.take 1).map (fun c => (2410545153-1+2*2^9*c.k,98910613679444+c.lower,98910993387098+c.upper)) = pointBounds18361 := by
 decide +kernel
def cuts18362 : List PrefixCut := [⟨4,21951200,21951214⟩,
⟨78,440651726,440651992⟩,
⟨128,714679717,714680149⟩]
theorem checked18362 : checkPrefixCuts (2^48) 2410676225 9 Manual.Count131072.C018362.packed 128 cuts18362 = true := by
 decide +kernel
def pointBounds18362 : List (Nat × Nat × Nat) := [(2410680320,98911338439138,98911718147236),(2410756096,98911757139664,98912136848014)]
theorem point_links_checked18362 : (cuts18362.take 2).map (fun c => (2410676225-1+2*2^9*c.k,98911316487938+c.lower,98911696196022+c.upper)) = pointBounds18362 := by
 decide +kernel
def cuts18363 : List PrefixCut := [⟨24,133217278,133217357⟩,
⟨98,540916776,540917099⟩,
⟨128,704950308,704950730⟩]
theorem checked18363 : checkPrefixCuts (2^48) 2410807297 9 Manual.Count131072.C018363.packed 128 cuts18363 = true := by
 decide +kernel
def pointBounds18363 : List (Nat × Nat × Nat) := [(2410831872,98912164384933,98912544093528),(2410907648,98912572084431,98912951793270)]
theorem point_links_checked18363 : (cuts18363.take 2).map (fun c => (2410807297-1+2*2^9*c.k,98912031167655+c.lower,98912410876171+c.upper)) = pointBounds18363 := by
 decide +kernel
def cuts18364 : List PrefixCut := [⟨44,245637835,245637981⟩,
⟨118,656463768,656464160⟩,
⟨128,711099493,711099917⟩]
theorem checked18364 : checkPrefixCuts (2^48) 2410938369 9 Manual.Count131072.C018364.packed 128 cuts18364 = true := by
 decide +kernel
def pointBounds18364 : List (Nat × Nat × Nat) := [(2410983424,98912981755798,98913361464882),(2411059200,98913392581731,98913772291061)]
theorem point_links_checked18364 : (cuts18364.take 2).map (fun c => (2410938369-1+2*2^9*c.k,98912736117963+c.lower,98913115826901+c.upper)) = pointBounds18364 := by
 decide +kernel
def cuts18365 : List PrefixCut := [⟨64,355126681,355126895⟩,
⟨128,704640213,704640638⟩]
theorem checked18365 : checkPrefixCuts (2^48) 2411069441 9 Manual.Count131072.C018365.packed 128 cuts18365 = true := by
 decide +kernel
def pointBounds18365 : List (Nat × Nat × Nat) := [(2411134976,98913802344137,98914182053713)]
theorem point_links_checked18365 : (cuts18365.take 1).map (fun c => (2411069441-1+2*2^9*c.k,98913447217456+c.lower,98913826926818+c.upper)) = pointBounds18365 := by
 decide +kernel
def cuts18366 : List PrefixCut := [⟨10,55216208,55216241⟩,
⟨84,472073605,472073892⟩,
⟨128,718493061,718493496⟩]
theorem checked18366 : checkPrefixCuts (2^48) 2411200513 9 Manual.Count131072.C018366.packed 128 cuts18366 = true := by
 decide +kernel
def pointBounds18366 : List (Nat × Nat × Nat) := [(2411210752,98914207073877,98914586783697),(2411286528,98914623931274,98915003641348)]
theorem point_links_checked18366 : (cuts18366.take 2).map (fun c => (2411200513-1+2*2^9*c.k,98914151857669+c.lower,98914531567456+c.upper)) = pointBounds18366 := by
 decide +kernel
def cuts18367 : List PrefixCut := [⟨30,163537782,163537879⟩,
⟨104,572314881,572315223⟩,
⟨128,702462488,702462908⟩]
theorem checked18367 : checkPrefixCuts (2^48) 2411331585 9 Manual.Count131072.C018367.packed 128 cuts18367 = true := by
 decide +kernel
def pointBounds18367 : List (Nat × Nat × Nat) := [(2411362304,98915033888512,98915413598831),(2411438080,98915442665611,98915822376175)]
theorem point_links_checked18367 : (cuts18367.take 2).map (fun c => (2411331585-1+2*2^9*c.k,98914870350730+c.lower,98915250060952+c.upper)) = pointBounds18367 := by
 decide +kernel
def cuts18368 : List PrefixCut := [⟨50,278266436,278266607⟩,
⟨124,687951517,687951937⟩,
⟨128,710477989,710478423⟩]
theorem checked18368 : checkPrefixCuts (2^48) 2411462657 9 Manual.Count131072.C018368.packed 128 cuts18368 = true := by
 decide +kernel
def pointBounds18368 : List (Nat × Nat × Nat) := [(2411513856,98915851079654,98916230790467),(2411589632,98916260764735,98916640475797)]
theorem point_links_checked18368 : (cuts18368.take 2).map (fun c => (2411462657-1+2*2^9*c.k,98915572813218+c.lower,98915952523860+c.upper)) = pointBounds18368 := by
 decide +kernel
def cuts18369 : List PrefixCut := [⟨70,396132927,396133164⟩,
⟨128,717325596,717326022⟩]
theorem checked18369 : checkPrefixCuts (2^48) 2411593729 9 Manual.Count131072.C018369.packed 128 cuts18369 = true := by
 decide +kernel
def pointBounds18369 : List (Nat × Nat × Nat) := [(2411665408,98916679424134,98917059135447)]
theorem point_links_checked18369 : (cuts18369.take 1).map (fun c => (2411593729-1+2*2^9*c.k,98916283291207+c.lower,98916663002283+c.upper)) = pointBounds18369 := by
 decide +kernel
def cuts18370 : List PrefixCut := [⟨16,87999814,87999868⟩,
⟨90,499747021,499747328⟩,
⟨128,708416673,708417109⟩]
theorem checked18370 : checkPrefixCuts (2^48) 2411724801 9 Manual.Count131072.C018370.packed 128 cuts18370 = true := by
 decide +kernel
def pointBounds18370 : List (Nat × Nat × Nat) := [(2411741184,98917088616617,98917468328173),(2411816960,98917500363824,98917880075633)]
theorem point_links_checked18370 : (cuts18370.take 2).map (fun c => (2411724801-1+2*2^9*c.k,98917000616803+c.lower,98917380328305+c.upper)) = pointBounds18370 := by
 decide +kernel
def cuts18371 : List PrefixCut := [⟨36,199330064,199330181⟩,
⟨110,601015104,601015461⟩,
⟨128,698341894,698342311⟩]
theorem checked18371 : checkPrefixCuts (2^48) 2411855873 9 Manual.Count131072.C018371.packed 128 cuts18371 = true := by
 decide +kernel
def pointBounds18371 : List (Nat × Nat × Nat) := [(2411892736,98917908363540,98918288075595),(2411968512,98918310048580,98918689760875)]
theorem point_links_checked18371 : (cuts18371.take 2).map (fun c => (2411855873-1+2*2^9*c.k,98917709033476+c.lower,98918088745414+c.upper)) = pointBounds18371 := by
 decide +kernel
def cuts18372 : List PrefixCut := [⟨56,308546812,308546992⟩,
⟨128,709740008,709740425⟩]
theorem checked18372 : checkPrefixCuts (2^48) 2411986945 9 Manual.Count131072.C018372.packed 128 cuts18372 = true := by
 decide +kernel
def pointBounds18372 : List (Nat × Nat × Nat) := [(2412044288,98918715922182,98919095634717)]
theorem point_links_checked18372 : (cuts18372.take 1).map (fun c => (2411986945-1+2*2^9*c.k,98918407375370+c.lower,98918787087725+c.upper)) = pointBounds18372 := by
 decide +kernel
def cuts18373 : List PrefixCut := [⟨2,12135964,12135971⟩,
⟨76,414950034,414950282⟩,
⟨128,700132925,700133346⟩]
theorem checked18373 : checkPrefixCuts (2^48) 2412118017 9 Manual.Count131072.C018373.packed 128 cuts18373 = true := by
 decide +kernel
def pointBounds18373 : List (Nat × Nat × Nat) := [(2412120064,98919129251342,98919508964121),(2412195840,98919532065412,98919911778432)]
theorem point_links_checked18373 : (cuts18373.take 2).map (fun c => (2412118017-1+2*2^9*c.k,98919117115378+c.lower,98919496828150+c.upper)) = pointBounds18373 := by
 decide +kernel
def cuts18374 : List PrefixCut := [⟨22,125669876,125669946⟩,
⟨96,533242679,533242999⟩,
⟨128,713863490,713863919⟩]
theorem checked18374 : checkPrefixCuts (2^48) 2412249089 9 Manual.Count131072.C018374.packed 128 cuts18374 = true := by
 decide +kernel
def pointBounds18374 : List (Nat × Nat × Nat) := [(2412271616,98919942918179,98920322631442),(2412347392,98920350490982,98920730204495)]
theorem point_links_checked18374 : (cuts18374.take 2).map (fun c => (2412249089-1+2*2^9*c.k,98919817248303+c.lower,98920196961496+c.upper)) = pointBounds18374 := by
 decide +kernel
def cuts18375 : List PrefixCut := [⟨42,228806112,228806256⟩,
⟨116,636353303,636353689⟩,
⟨128,704140476,704140905⟩]
theorem checked18375 : checkPrefixCuts (2^48) 2412380161 9 Manual.Count131072.C018375.packed 128 cuts18375 = true := by
 decide +kernel
def pointBounds18375 : List (Nat × Nat × Nat) := [(2412423168,98920759917905,98921139631671),(2412498944,98921167465096,98921547179104)]
theorem point_links_checked18375 : (cuts18375.take 2).map (fun c => (2412380161-1+2*2^9*c.k,98920531111793+c.lower,98920910825415+c.upper)) = pointBounds18375 := by
 decide +kernel
def cuts18376 : List PrefixCut := [⟨62,346980932,346981140⟩,
⟨128,707252578,707253009⟩]
theorem checked18376 : checkPrefixCuts (2^48) 2412511233 9 Manual.Count131072.C018376.packed 128 cuts18376 = true := by
 decide +kernel
def pointBounds18376 : List (Nat × Nat × Nat) := [(2412574720,98921582233201,98921961947460)]
theorem point_links_checked18376 : (cuts18376.take 1).map (fun c => (2412511233-1+2*2^9*c.k,98921235252269+c.lower,98921614966320+c.upper)) = pointBounds18376 := by
 decide +kernel
def cuts18377 : List PrefixCut := [⟨8,44916580,44916607⟩,
⟨82,458958594,458958875⟩,
⟨128,712113920,712114355⟩]
theorem checked18377 : checkPrefixCuts (2^48) 2412642305 9 Manual.Count131072.C018377.packed 128 cuts18377 = true := by
 decide +kernel
def pointBounds18377 : List (Nat × Nat × Nat) := [(2412650496,98921987421427,98922367135936),(2412726272,98922401463441,98922781178204)]
theorem point_links_checked18377 : (cuts18377.take 2).map (fun c => (2412642305-1+2*2^9*c.k,98921942504847+c.lower,98922322219329+c.upper)) = pointBounds18377 := by
 decide +kernel
def cuts18378 : List PrefixCut := [⟨28,158307127,158307222⟩,
⟨102,566956895,566957236⟩,
⟨128,707059092,707059521⟩]
theorem checked18378 : checkPrefixCuts (2^48) 2412773377 9 Manual.Count131072.C018378.packed 128 cuts18378 = true := by
 decide +kernel
def pointBounds18378 : List (Nat × Nat × Nat) := [(2412802048,98922812925894,98923192640906),(2412877824,98923221575662,98923601290920)]
theorem point_links_checked18378 : (cuts18378.take 2).map (fun c => (2412773377-1+2*2^9*c.k,98922654618767+c.lower,98923034333684+c.upper)) = pointBounds18378 := by
 decide +kernel
def cuts18379 : List PrefixCut := [⟨48,267484833,267484993⟩,
⟨122,678442002,678442409⟩,
⟨128,712269859,712270286⟩]
theorem checked18379 : checkPrefixCuts (2^48) 2412904449 9 Manual.Count131072.C018379.packed 128 cuts18379 = true := by
 decide +kernel
def pointBounds18379 : List (Nat × Nat × Nat) := [(2412953600,98923629162692,98924008878198),(2413029376,98924040119861,98924419835614)]
theorem point_links_checked18379 : (cuts18379.take 2).map (fun c => (2412904449-1+2*2^9*c.k,98923361677859+c.lower,98923741393205+c.upper)) = pointBounds18379 := by
 decide +kernel
def cuts18380 : List PrefixCut := [⟨68,371517417,371517647⟩,
⟨128,703132871,703133297⟩]
theorem checked18380 : checkPrefixCuts (2^48) 2413035521 9 Manual.Count131072.C018380.packed 128 cuts18380 = true := by
 decide +kernel
def pointBounds18380 : List (Nat × Nat × Nat) := [(2413105152,98924445465135,98924825181138)]
theorem point_links_checked18380 : (cuts18380.take 1).map (fun c => (2413035521-1+2*2^9*c.k,98924073947718+c.lower,98924453663491+c.upper)) = pointBounds18380 := by
 decide +kernel
def cuts18381 : List PrefixCut := [⟨14,76049903,76049949⟩,
⟨88,485102117,485102406⟩,
⟨128,708343340,708343762⟩]
theorem checked18381 : checkPrefixCuts (2^48) 2413166593 9 Manual.Count131072.C018381.packed 128 cuts18381 = true := by
 decide +kernel
def pointBounds18381 : List (Nat × Nat × Nat) := [(2413180928,98924853130492,98925232846737),(2413256704,98925262182706,98925641899194)]
theorem point_links_checked18381 : (cuts18381.take 2).map (fun c => (2413166593-1+2*2^9*c.k,98924777080589+c.lower,98925156796788+c.upper)) = pointBounds18381 := by
 decide +kernel
def cuts18382 : List PrefixCut := [⟨34,193729297,193729414⟩,
⟨108,604505317,604505677⟩,
⟨128,714486586,714487015⟩]
theorem checked18382 : checkPrefixCuts (2^48) 2413297665 9 Manual.Count131072.C018382.packed 128 cuts18382 = true := by
 decide +kernel
def pointBounds18382 : List (Nat × Nat × Nat) := [(2413332480,98925679153226,98926058869964),(2413408256,98926089929246,98926469646227)]
theorem point_links_checked18382 : (cuts18382.take 2).map (fun c => (2413297665-1+2*2^9*c.k,98925485423929+c.lower,98925865140550+c.upper)) = pointBounds18382 := by
 decide +kernel
def cuts18383 : List PrefixCut := [⟨54,289818836,289819015⟩,
⟨128,703951159,703951596⟩]
theorem checked18383 : checkPrefixCuts (2^48) 2413428737 9 Manual.Count131072.C018383.packed 128 cuts18383 = true := by
 decide +kernel
def pointBounds18383 : List (Nat × Nat × Nat) := [(2413484032,98926489729351,98926869446580),(2413559808,98926903861674,98927283579161)]
theorem point_links_checked18383 : (cuts18383.take 2).map (fun c => (2413428737-1+2*2^9*c.k,98926199910515+c.lower,98926579627565+c.upper)) = pointBounds18383 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000261
