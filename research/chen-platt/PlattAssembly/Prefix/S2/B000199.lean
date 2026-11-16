import PlattAssemblyKernel
import PlattCertificates.Count131072.C016368
import PlattCertificates.Count131072.C016369
import PlattCertificates.Count131072.C016370
import PlattCertificates.Count131072.C016371
import PlattCertificates.Count131072.C016372
import PlattCertificates.Count131072.C016373
import PlattCertificates.Count131072.C016374
import PlattCertificates.Count131072.C016375
import PlattCertificates.Count131072.C016376
import PlattCertificates.Count131072.C016377
import PlattCertificates.Count131072.C016378
import PlattCertificates.Count131072.C016379
import PlattCertificates.Count131072.C016380
import PlattCertificates.Count131072.C016381
import PlattCertificates.Count131072.C016382
import PlattCertificates.Count131072.C016383
import PlattCertificates.Count131072.C016384
import PlattCertificates.Count131072.C016385
import PlattCertificates.Count131072.C016386
import PlattCertificates.Count131072.C016387
import PlattCertificates.Count131072.C016388
import PlattCertificates.Count131072.C016389
import PlattCertificates.Count131072.C016390
import PlattCertificates.Count131072.C016391
import PlattCertificates.Count131072.C016392
import PlattCertificates.Count131072.C016393
import PlattCertificates.Count131072.C016394
import PlattCertificates.Count131072.C016395
import PlattCertificates.Count131072.C016396
import PlattCertificates.Count131072.C016397
import PlattCertificates.Count131072.C016398
import PlattCertificates.Count131072.C016399
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000199
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16368 : List PrefixCut := [⟨15,93636111,93636168⟩,
⟨81,497114727,497115037⟩,
⟨128,791629254,791629753⟩]
theorem checked16368 : checkPrefixCuts (2^48) 2149318657 9 Manual.Count131072.C016368.packed 128 cuts16368 = true := by
 decide +kernel
def pointBounds16368 : List (Nat × Nat × Nat) := [(2149334016,97412268325707,97412647103882),(2149401600,97412671804323,97413050582751)]
theorem point_links_checked16368 : (cuts16368.take 2).map (fun c => (2149318657-1+2*2^9*c.k,97412174689596+c.lower,97412553467714+c.upper)) = pointBounds16368 := by
 decide +kernel
def cuts16369 : List PrefixCut := [⟨19,116415873,116415944⟩,
⟨85,533487880,533488218⟩,
⟨128,806378089,806378597⟩]
theorem checked16369 : checkPrefixCuts (2^48) 2149449729 9 Manual.Count131072.C016369.packed 128 cuts16369 = true := by
 decide +kernel
def pointBounds16369 : List (Nat × Nat × Nat) := [(2149469184,97413082734723,97413461513411),(2149536768,97413499806730,97413878585685)]
theorem point_links_checked16369 : (cuts16369.take 2).map (fun c => (2149449729-1+2*2^9*c.k,97412966318850+c.lower,97413345097467+c.upper)) = pointBounds16369 := by
 decide +kernel
def cuts16370 : List PrefixCut := [⟨23,142073572,142073661⟩,
⟨89,560952495,560952849⟩,
⟨128,802139003,802139511⟩]
theorem checked16370 : checkPrefixCuts (2^48) 2149580801 9 Manual.Count131072.C016370.packed 128 cuts16370 = true := by
 decide +kernel
def pointBounds16370 : List (Nat × Nat × Nat) := [(2149604352,97413914770511,97414293549725),(2149671936,97414333649434,97414712428913)]
theorem point_links_checked16370 : (cuts16370.take 2).map (fun c => (2149580801-1+2*2^9*c.k,97413772696939+c.lower,97414151476064+c.upper)) = pointBounds16370 := by
 decide +kernel
def cuts16371 : List PrefixCut := [⟨27,169168356,169168464⟩,
⟨93,582128926,582129297⟩,
⟨128,799078628,799079133⟩]
theorem checked16371 : checkPrefixCuts (2^48) 2149711873 9 Manual.Count131072.C016371.packed 128 cuts16371 = true := by
 decide +kernel
def pointBounds16371 : List (Nat × Nat × Nat) := [(2149739520,97414744004298,97415122784039),(2149807104,97415156964868,97415535744872)]
theorem point_links_checked16371 : (cuts16371.take 2).map (fun c => (2149711873-1+2*2^9*c.k,97414574835942+c.lower,97414953615575+c.upper)) = pointBounds16371 := by
 decide +kernel
def cuts16372 : List PrefixCut := [⟨31,189975298,189975421⟩,
⟨97,597411073,597411454⟩,
⟨128,793530854,793531361⟩]
theorem checked16372 : checkPrefixCuts (2^48) 2149842945 9 Manual.Count131072.C016372.packed 128 cuts16372 = true := by
 decide +kernel
def pointBounds16372 : List (Nat × Nat × Nat) := [(2149874688,97415563889868,97415942670129),(2149942272,97415971325643,97416350106162)]
theorem point_links_checked16372 : (cuts16372.take 2).map (fun c => (2149842945-1+2*2^9*c.k,97415373914570+c.lower,97415752694708+c.upper)) = pointBounds16372 := by
 decide +kernel
def cuts16373 : List PrefixCut := [⟨35,219289417,219289554⟩,
⟨101,628401628,628402021⟩,
⟨128,799374017,799374517⟩]
theorem checked16373 : checkPrefixCuts (2^48) 2149974017 9 Manual.Count131072.C016373.packed 128 cuts16373 = true := by
 decide +kernel
def pointBounds16373 : List (Nat × Nat × Nat) := [(2150009856,97416386734841,97416765515623),(2150077440,97416795847052,97417174628090)]
theorem point_links_checked16373 : (cuts16373.take 2).map (fun c => (2149974017-1+2*2^9*c.k,97416167445424+c.lower,97416546226069+c.upper)) = pointBounds16373 := by
 decide +kernel
def cuts16374 : List PrefixCut := [⟨39,243232523,243232678⟩,
⟨105,662267949,662268370⟩,
⟨128,808096002,808096516⟩]
theorem checked16374 : checkPrefixCuts (2^48) 2150105089 9 Manual.Count131072.C016374.packed 128 cuts16374 = true := by
 decide +kernel
def pointBounds16374 : List (Nat × Nat × Nat) := [(2150145024,97417210051964,97417588833264),(2150212608,97417629087390,97418007868956)]
theorem point_links_checked16374 : (cuts16374.take 2).map (fun c => (2150105089-1+2*2^9*c.k,97416966819441+c.lower,97417345600586+c.upper)) = pointBounds16374 := by
 decide +kernel
def cuts16375 : List PrefixCut := [⟨43,275288668,275288845⟩,
⟨109,684873011,684873458⟩,
⟨128,805036251,805036773⟩]
theorem checked16375 : checkPrefixCuts (2^48) 2150236161 9 Manual.Count131072.C016375.packed 128 cuts16375 = true := by
 decide +kernel
def pointBounds16375 : List (Nat × Nat × Nat) := [(2150280192,97418050204111,97418428985947),(2150347776,97418459788454,97418838570560)]
theorem point_links_checked16375 : (cuts16375.take 2).map (fun c => (2150236161-1+2*2^9*c.k,97417774915443+c.lower,97418153697102+c.upper)) = pointBounds16375 := by
 decide +kernel
def cuts16376 : List PrefixCut := [⟨47,293073254,293073442⟩,
⟨113,704464382,704464834⟩,
⟨128,802500005,802500519⟩]
theorem checked16376 : checkPrefixCuts (2^48) 2150367233 9 Manual.Count131072.C016376.packed 128 cuts16376 = true := by
 decide +kernel
def pointBounds16376 : List (Nat × Nat × Nat) := [(2150415360,97418873024948,97419251807317),(2150482944,97419284416076,97419663198709)]
theorem point_links_checked16376 : (cuts16376.take 2).map (fun c => (2150367233-1+2*2^9*c.k,97418579951694+c.lower,97418958733875+c.upper)) = pointBounds16376 := by
 decide +kernel
def cuts16377 : List PrefixCut := [⟨51,313473474,313473674⟩,
⟨117,723529761,723530223⟩,
⟨128,789362696,789363200⟩]
theorem checked16377 : checkPrefixCuts (2^48) 2150498305 9 Manual.Count131072.C016377.packed 128 cuts16377 = true := by
 decide +kernel
def pointBounds16377 : List (Nat × Nat × Nat) := [(2150550528,97419695925173,97420074708068),(2150618112,97420105981460,97420484764617)]
theorem point_links_checked16377 : (cuts16377.take 2).map (fun c => (2150498305-1+2*2^9*c.k,97419382451699+c.lower,97419761234394+c.upper)) = pointBounds16377 := by
 decide +kernel
def cuts16378 : List PrefixCut := [⟨55,340153299,340153518⟩,
⟨121,757643686,757644168⟩,
⟨128,802532944,802533453⟩]
theorem checked16378 : checkPrefixCuts (2^48) 2150629377 9 Manual.Count131072.C016378.packed 128 cuts16378 = true := by
 decide +kernel
def pointBounds16378 : List (Nat × Nat × Nat) := [(2150685696,97420511967694,97420890751112),(2150753280,97420929458081,97421308241762)]
theorem point_links_checked16378 : (cuts16378.take 2).map (fun c => (2150629377-1+2*2^9*c.k,97420171814395+c.lower,97420550597594+c.upper)) = pointBounds16378 := by
 decide +kernel
def cuts16379 : List PrefixCut := [⟨59,365390219,365390452⟩,
⟨125,765710863,765711351⟩,
⟨128,784293605,784294105⟩]
theorem checked16379 : checkPrefixCuts (2^48) 2150760449 9 Manual.Count131072.C016379.packed 128 cuts16379 = true := by
 decide +kernel
def pointBounds16379 : List (Nat × Nat × Nat) := [(2150820864,97421339737558,97421718521499),(2150888448,97421740058202,97422118842398)]
theorem point_links_checked16379 : (cuts16379.take 2).map (fun c => (2150760449-1+2*2^9*c.k,97420974347339+c.lower,97421353131047+c.upper)) = pointBounds16379 := by
 decide +kernel
def cuts16380 : List PrefixCut := [⟨63,392194413,392194670⟩,
⟨128,803351325,803351844⟩]
theorem checked16380 : checkPrefixCuts (2^48) 2150891521 9 Manual.Count131072.C016380.packed 128 cuts16380 = true := by
 decide +kernel
def pointBounds16380 : List (Nat × Nat × Nat) := [(2150956032,97422150835357,97422529619822)]
theorem point_links_checked16380 : (cuts16380.take 1).map (fun c => (2150891521-1+2*2^9*c.k,97421758640944+c.lower,97422137425152+c.upper)) = pointBounds16380 := by
 decide +kernel
def cuts16381 : List PrefixCut := [⟨1,5888533,5888536⟩,
⟨67,409966393,409966658⟩,
⟨128,792441634,792442140⟩]
theorem checked16381 : checkPrefixCuts (2^48) 2151022593 9 Manual.Count131072.C016381.packed 128 cuts16381 = true := by
 decide +kernel
def pointBounds16381 : List (Nat × Nat × Nat) := [(2151023616,97422567880802,97422946665532),(2151091200,97422971958662,97423350743654)]
theorem point_links_checked16381 : (cuts16381.take 2).map (fun c => (2151022593-1+2*2^9*c.k,97422561992269+c.lower,97422940776996+c.upper)) = pointBounds16381 := by
 decide +kernel
def cuts16382 : List PrefixCut := [⟨5,32057806,32057825⟩,
⟨71,442390755,442391037⟩,
⟨128,794225297,794225804⟩]
theorem checked16382 : checkPrefixCuts (2^48) 2151153665 9 Manual.Count131072.C016382.packed 128 cuts16382 = true := by
 decide +kernel
def pointBounds16382 : List (Nat × Nat × Nat) := [(2151158784,97423386491709,97423765276961),(2151226368,97423796824658,97424175610173)]
theorem point_links_checked16382 : (cuts16382.take 2).map (fun c => (2151153665-1+2*2^9*c.k,97423354433903+c.lower,97423733219136+c.upper)) = pointBounds16382 := by
 decide +kernel
def cuts16383 : List PrefixCut := [⟨9,58747199,58747235⟩,
⟨75,470101156,470101454⟩,
⟨128,806998851,806999365⟩]
theorem checked16383 : checkPrefixCuts (2^48) 2151284737 9 Manual.Count131072.C016383.packed 128 cuts16383 = true := by
 decide +kernel
def pointBounds16383 : List (Nat × Nat × Nat) := [(2151293952,97424207406399,97424586192175),(2151361536,97424618760356,97424997546394)]
theorem point_links_checked16383 : (cuts16383.take 2).map (fun c => (2151284737-1+2*2^9*c.k,97424148659200+c.lower,97424527444940+c.upper)) = pointBounds16383 := by
 decide +kernel
def cuts16384 : List PrefixCut := [⟨13,80069181,80069233⟩,
⟨79,490350645,490350957⟩,
⟨128,796614209,796614718⟩]
theorem checked16384 : checkPrefixCuts (2^48) 2151415809 9 Manual.Count131072.C016384.packed 128 cuts16384 = true := by
 decide +kernel
def pointBounds16384 : List (Nat × Nat × Nat) := [(2151429120,97425035727232,97425414513538),(2151496704,97425446008696,97425824795262)]
theorem point_links_checked16384 : (cuts16384.take 2).map (fun c => (2151415809-1+2*2^9*c.k,97424955658051+c.lower,97425334444305+c.upper)) = pointBounds16384 := by
 decide +kernel
def cuts16385 : List PrefixCut := [⟨17,105967359,105967426⟩,
⟨83,522240852,522241181⟩,
⟨128,800490438,800490949⟩]
theorem checked16385 : checkPrefixCuts (2^48) 2151546881 9 Manual.Count131072.C016385.packed 128 cuts16385 = true := by
 decide +kernel
def pointBounds16385 : List (Nat × Nat × Nat) := [(2151564288,97425858239619,97426237026449),(2151631872,97426274513112,97426653300204)]
theorem point_links_checked16385 : (cuts16385.take 2).map (fun c => (2151546881-1+2*2^9*c.k,97425752272260+c.lower,97426131059023+c.upper)) = pointBounds16385 := by
 decide +kernel
def cuts16386 : List PrefixCut := [⟨21,126891329,126891411⟩,
⟨87,547193798,547194146⟩,
⟨128,795601583,795602093⟩]
theorem checked16386 : checkPrefixCuts (2^48) 2151677953 9 Manual.Count131072.C016386.packed 128 cuts16386 = true := by
 decide +kernel
def pointBounds16386 : List (Nat × Nat × Nat) := [(2151699456,97426679654027,97427058441383),(2151767040,97427099956496,97427478744118)]
theorem point_links_checked16386 : (cuts16386.take 2).map (fun c => (2151677953-1+2*2^9*c.k,97426552762698+c.lower,97426931549972+c.upper)) = pointBounds16386 := by
 decide +kernel
def cuts16387 : List PrefixCut := [⟨25,160762695,160762794⟩,
⟨91,567565837,567566191⟩,
⟨128,800131235,800131734⟩]
theorem checked16387 : checkPrefixCuts (2^48) 2151809025 9 Manual.Count131072.C016387.packed 128 cuts16387 = true := by
 decide +kernel
def pointBounds16387 : List (Nat × Nat × Nat) := [(2151834624,97427509126976,97427887914859),(2151902208,97427915930118,97428294718256)]
theorem point_links_checked16387 : (cuts16387.take 2).map (fun c => (2151809025-1+2*2^9*c.k,97427348364281+c.lower,97427727152065+c.upper)) = pointBounds16387 := by
 decide +kernel
def cuts16388 : List PrefixCut := [⟨29,182596256,182596370⟩,
⟨95,593690211,593690586⟩,
⟨128,796027897,796028401⟩]
theorem checked16388 : checkPrefixCuts (2^48) 2151940097 9 Manual.Count131072.C016388.packed 128 cuts16388 = true := by
 decide +kernel
def pointBounds16388 : List (Nat × Nat × Nat) := [(2151969792,97428331091772,97428709880169),(2152037376,97428742185727,97429120974385)]
theorem point_links_checked16388 : (cuts16388.take 2).map (fun c => (2151940097-1+2*2^9*c.k,97428148495516+c.lower,97428527283799+c.upper)) = pointBounds16388 := by
 decide +kernel
def cuts16389 : List PrefixCut := [⟨33,202072894,202073024⟩,
⟨99,614841312,614841702⟩,
⟨128,802649289,802649797⟩]
theorem checked16389 : checkPrefixCuts (2^48) 2152071169 9 Manual.Count131072.C016389.packed 128 cuts16389 = true := by
 decide +kernel
def pointBounds16389 : List (Nat × Nat × Nat) := [(2152104960,97429146596307,97429525385224),(2152172544,97429559364725,97429938153902)]
theorem point_links_checked16389 : (cuts16389.take 2).map (fun c => (2152071169-1+2*2^9*c.k,97428944523413+c.lower,97429323312200+c.upper)) = pointBounds16389 := by
 decide +kernel
def cuts16390 : List PrefixCut := [⟨37,235148599,235148746⟩,
⟨103,643444491,643444900⟩,
⟨128,799200382,799200890⟩]
theorem checked16390 : checkPrefixCuts (2^48) 2152202241 9 Manual.Count131072.C016390.packed 128 cuts16390 = true := by
 decide +kernel
def pointBounds16390 : List (Nat × Nat × Nat) := [(2152240128,97429982321301,97430361110743),(2152307712,97430390617193,97430769406897)]
theorem point_links_checked16390 : (cuts16390.take 2).map (fun c => (2152202241-1+2*2^9*c.k,97429747172702+c.lower,97430125961997+c.upper)) = pointBounds16390 := by
 decide +kernel
def cuts16391 : List PrefixCut := [⟨41,249780937,249781100⟩,
⟨107,669820681,669821106⟩,
⟨128,796928443,796928949⟩]
theorem checked16391 : checkPrefixCuts (2^48) 2152333313 9 Manual.Count131072.C016391.packed 128 cuts16391 = true := by
 decide +kernel
def pointBounds16391 : List (Nat × Nat × Nat) := [(2152375296,97430796154021,97431174943987),(2152442880,97431216193765,97431594983993)]
theorem point_links_checked16391 : (cuts16391.take 2).map (fun c => (2152333313-1+2*2^9*c.k,97430546373084+c.lower,97430925162887+c.upper)) = pointBounds16391 := by
 decide +kernel
def cuts16392 : List PrefixCut := [⟨45,277226608,277226782⟩,
⟨111,695932287,695932722⟩,
⟨128,804202577,804203084⟩]
theorem checked16392 : checkPrefixCuts (2^48) 2152464385 9 Manual.Count131072.C016392.packed 128 cuts16392 = true := by
 decide +kernel
def pointBounds16392 : List (Nat × Nat × Nat) := [(2152510464,97431620528135,97431999318618),(2152578048,97432039233814,97432418024558)]
theorem point_links_checked16392 : (cuts16392.take 2).map (fun c => (2152464385-1+2*2^9*c.k,97431343301527+c.lower,97431722091836+c.upper)) = pointBounds16392 := by
 decide +kernel
def cuts16393 : List PrefixCut := [⟨49,309245440,309245639⟩,
⟨115,724525303,724525765⟩,
⟨128,805199988,805200500⟩]
theorem checked16393 : checkPrefixCuts (2^48) 2152595457 9 Manual.Count131072.C016393.packed 128 cuts16393 = true := by
 decide +kernel
def pointBounds16393 : List (Nat × Nat × Nat) := [(2152645632,97432456749544,97432835540559),(2152713216,97432872029407,97433250820685)]
theorem point_links_checked16393 : (cuts16393.take 2).map (fun c => (2152595457-1+2*2^9*c.k,97432147504104+c.lower,97432526294920+c.upper)) = pointBounds16393 := by
 decide +kernel
def cuts16394 : List PrefixCut := [⟨53,331192503,331192715⟩,
⟨119,740039638,740040108⟩,
⟨128,795475541,795476047⟩]
theorem checked16394 : checkPrefixCuts (2^48) 2152726529 9 Manual.Count131072.C016394.packed 128 cuts16394 = true := by
 decide +kernel
def pointBounds16394 : List (Nat × Nat × Nat) := [(2152780800,97433283896595,97433662688135),(2152848384,97433692743730,97434071535528)]
theorem point_links_checked16394 : (cuts16394.take 2).map (fun c => (2152726529-1+2*2^9*c.k,97432952704092+c.lower,97433331495420+c.upper)) = pointBounds16394 := by
 decide +kernel
def cuts16395 : List PrefixCut := [⟨57,356013232,356013456⟩,
⟨123,765096068,765096548⟩,
⟨128,795557783,795558282⟩]
theorem checked16395 : checkPrefixCuts (2^48) 2152857601 9 Manual.Count131072.C016395.packed 128 cuts16395 = true := by
 decide +kernel
def pointBounds16395 : List (Nat × Nat × Nat) := [(2152915968,97434104192865,97434482984923),(2152983552,97434513275701,97434892068015)]
theorem point_links_checked16395 : (cuts16395.take 2).map (fun c => (2152857601-1+2*2^9*c.k,97433748179633+c.lower,97434126971467+c.upper)) = pointBounds16395 := by
 decide +kernel
def cuts16396 : List PrefixCut := [⟨61,377693080,377693318⟩,
⟨127,792763861,792764365⟩,
⟨128,798515932,798516440⟩]
theorem checked16396 : checkPrefixCuts (2^48) 2152988673 9 Manual.Count131072.C016396.packed 128 cuts16396 = true := by
 decide +kernel
def pointBounds16396 : List (Nat × Nat × Nat) := [(2153051136,97434921430496,97435300223067),(2153118720,97435336501277,97435715294114)]
theorem point_links_checked16396 : (cuts16396.take 2).map (fun c => (2152988673-1+2*2^9*c.k,97434543737416+c.lower,97434922529749+c.upper)) = pointBounds16396 := by
 decide +kernel
def cuts16397 : List PrefixCut := [⟨65,394664262,394664515⟩,
⟨128,784349068,784349571⟩]
theorem checked16397 : checkPrefixCuts (2^48) 2153119745 9 Manual.Count131072.C016397.packed 128 cuts16397 = true := by
 decide +kernel
def pointBounds16397 : List (Nat × Nat × Nat) := [(2153186304,97435736917610,97436115710704)]
theorem point_links_checked16397 : (cuts16397.take 1).map (fun c => (2153119745-1+2*2^9*c.k,97435342253348+c.lower,97435721046189+c.upper)) = pointBounds16397 := by
 decide +kernel
def cuts16398 : List PrefixCut := [⟨3,18562356,18562368⟩,
⟨69,429411145,429411421⟩,
⟨128,791752486,791752993⟩]
theorem checked16398 : checkPrefixCuts (2^48) 2153250817 9 Manual.Count131072.C016398.packed 128 cuts16398 = true := by
 decide +kernel
def pointBounds16398 : List (Nat × Nat × Nat) := [(2153253888,97436145164772,97436523958128),(2153321472,97436556013561,97436934807181)]
theorem point_links_checked16398 : (cuts16398.take 2).map (fun c => (2153250817-1+2*2^9*c.k,97436126602416+c.lower,97436505395760+c.upper)) = pointBounds16398 := by
 decide +kernel
def cuts16399 : List PrefixCut := [⟨7,43527339,43527366⟩,
⟨73,454873198,454873485⟩,
⟨128,803990834,803991342⟩]
theorem checked16399 : checkPrefixCuts (2^48) 2153381889 9 Manual.Count131072.C016399.packed 128 cuts16399 = true := by
 decide +kernel
def pointBounds16399 : List (Nat × Nat × Nat) := [(2153389056,97436961882241,97437340676119),(2153456640,97437373228100,97437752022238)]
theorem point_links_checked16399 : (cuts16399.take 2).map (fun c => (2153381889-1+2*2^9*c.k,97436918354902+c.lower,97437297148753+c.upper)) = pointBounds16399 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000199
