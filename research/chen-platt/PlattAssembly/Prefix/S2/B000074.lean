import PlattAssemblyKernel
import PlattCertificates.Count131072.C012368
import PlattCertificates.Count131072.C012369
import PlattCertificates.Count131072.C012370
import PlattCertificates.Count131072.C012371
import PlattCertificates.Count131072.C012372
import PlattCertificates.Count131072.C012373
import PlattCertificates.Count131072.C012374
import PlattCertificates.Count131072.C012375
import PlattCertificates.Count131072.C012376
import PlattCertificates.Count131072.C012377
import PlattCertificates.Count131072.C012378
import PlattCertificates.Count131072.C012379
import PlattCertificates.Count131072.C012380
import PlattCertificates.Count131072.C012381
import PlattCertificates.Count131072.C012382
import PlattCertificates.Count131072.C012383
import PlattCertificates.Count131072.C012384
import PlattCertificates.Count131072.C012385
import PlattCertificates.Count131072.C012386
import PlattCertificates.Count131072.C012387
import PlattCertificates.Count131072.C012388
import PlattCertificates.Count131072.C012389
import PlattCertificates.Count131072.C012390
import PlattCertificates.Count131072.C012391
import PlattCertificates.Count131072.C012392
import PlattCertificates.Count131072.C012393
import PlattCertificates.Count131072.C012394
import PlattCertificates.Count131072.C012395
import PlattCertificates.Count131072.C012396
import PlattCertificates.Count131072.C012397
import PlattCertificates.Count131072.C012398
import PlattCertificates.Count131072.C012399
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000074
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12368 : List PrefixCut := [⟨44,366857983,366858262⟩,
⟨94,785146868,785147456⟩,
⟨128,1066077205,1066078004⟩]
theorem checked12368 : checkPrefixCuts (2^48) 1625030657 9 Manual.Count131072.C012368.packed 128 cuts12368 = true := by
 decide +kernel
def pointBounds12368 : List (Nat × Nat × Nat) := [(1625075712,93725820583394,93726196822691),(1625126912,93726238872279,93726615111885)]
theorem point_links_checked12368 : (cuts12368.take 2).map (fun c => (1625030657-1+2*2^9*c.k,93725453725411+c.lower,93725829964429+c.upper)) = pointBounds12368 := by
 decide +kernel
def cuts12369 : List PrefixCut := [⟨16,135267003,135267106⟩,
⟨66,553183183,553183599⟩,
⟨116,969354315,969355042⟩,
⟨128,1071533315,1071534119⟩]
theorem checked12369 : checkPrefixCuts (2^48) 1625161729 9 Manual.Count131072.C012369.packed 128 cuts12369 = true := by
 decide +kernel
def pointBounds12369 : List (Nat × Nat × Nat) := [(1625178112,93726655069619,93727031309539),(1625229312,93727072985799,93727449226032),(1625280512,93727489156931,93727865397475)]
theorem point_links_checked12369 : (cuts12369.take 3).map (fun c => (1625161729-1+2*2^9*c.k,93726519802616+c.lower,93726896042433+c.upper)) = pointBounds12369 := by
 decide +kernel
def cuts12370 : List PrefixCut := [⟨38,323504010,323504251⟩,
⟨88,738782943,738783498⟩,
⟨128,1080971455,1080972268⟩]
theorem checked12370 : checkPrefixCuts (2^48) 1625292801 9 Manual.Count131072.C012370.packed 128 cuts12370 = true := by
 decide +kernel
def pointBounds12370 : List (Nat × Nat × Nat) := [(1625331712,93727914839941,93728291080803),(1625382912,93728330118874,93728706360050)]
theorem point_links_checked12370 : (cuts12370.take 2).map (fun c => (1625292801-1+2*2^9*c.k,93727591335931+c.lower,93727967576552+c.upper)) = pointBounds12370 := by
 decide +kernel
def cuts12371 : List PrefixCut := [⟨10,81389706,81389766⟩,
⟨60,493005943,493006312⟩,
⟨110,909457873,909458553⟩,
⟨128,1057507236,1057508026⟩]
theorem checked12371 : checkPrefixCuts (2^48) 1625423873 9 Manual.Count131072.C012371.packed 128 cuts12371 = true := by
 decide +kernel
def pointBounds12371 : List (Nat × Nat × Nat) := [(1625434112,93728753697092,93729129938586),(1625485312,93729165313329,93729541555132),(1625536512,93729581765259,93729958007373)]
theorem point_links_checked12371 : (cuts12371.take 3).map (fun c => (1625423873-1+2*2^9*c.k,93728672307386+c.lower,93729048548820+c.upper)) = pointBounds12371 := by
 decide +kernel
def cuts12372 : List PrefixCut := [⟨32,266484654,266484854⟩,
⟨82,680139930,680140442⟩,
⟨128,1066425755,1066426560⟩]
theorem checked12372 : checkPrefixCuts (2^48) 1625554945 9 Manual.Count131072.C012372.packed 128 cuts12372 = true := by
 decide +kernel
def pointBounds12372 : List (Nat × Nat × Nat) := [(1625587712,93729996299276,93730372541700),(1625638912,93730409954552,93730786197288)]
theorem point_links_checked12372 : (cuts12372.take 2).map (fun c => (1625554945-1+2*2^9*c.k,93729729814622+c.lower,93730106056846+c.upper)) = pointBounds12372 := by
 decide +kernel
def cuts12373 : List PrefixCut := [⟨4,32550694,32550719⟩,
⟨54,447218793,447219128⟩,
⟨104,852870860,852871498⟩,
⟨128,1056644352,1056645145⟩]
theorem checked12373 : checkPrefixCuts (2^48) 1625686017 9 Manual.Count131072.C012373.packed 128 cuts12373 = true := by
 decide +kernel
def pointBounds12373 : List (Nat × Nat × Nat) := [(1625690112,93730828791071,93731205034125),(1625741312,93731243459170,93731619702534),(1625792512,93731649111237,93732025354904)]
theorem point_links_checked12373 : (cuts12373.take 3).map (fun c => (1625686017-1+2*2^9*c.k,93730796240377+c.lower,93731172483406+c.upper)) = pointBounds12373 := by
 decide +kernel
def cuts12374 : List PrefixCut := [⟨26,219697932,219698098⟩,
⟨76,641597866,641598352⟩,
⟨126,1061234096,1061234898⟩,
⟨128,1077333736,1077334550⟩]
theorem checked12374 : checkPrefixCuts (2^48) 1625817089 9 Manual.Count131072.C012374.packed 128 cuts12374 = true := by
 decide +kernel
def pointBounds12374 : List (Nat × Nat × Nat) := [(1625843712,93732072582661,93732448826649),(1625894912,93732494482595,93732870726903),(1625946112,93732914118825,93733290363449)]
theorem point_links_checked12374 : (cuts12374.take 3).map (fun c => (1625817089-1+2*2^9*c.k,93731852884729+c.lower,93732229128551+c.upper)) = pointBounds12374 := by
 decide +kernel
def cuts12375 : List PrefixCut := [⟨48,401445965,401446266⟩,
⟨98,829884283,829884905⟩,
⟨128,1088844861,1088845680⟩]
theorem checked12375 : checkPrefixCuts (2^48) 1625948161 9 Manual.Count131072.C012375.packed 128 cuts12375 = true := by
 decide +kernel
def pointBounds12375 : List (Nat × Nat × Nat) := [(1625997312,93733331664430,93733707909367),(1626048512,93733760102748,93734136348006)]
theorem point_links_checked12375 : (cuts12375.take 2).map (fun c => (1625948161-1+2*2^9*c.k,93732930218465+c.lower,93733306463101+c.upper)) = pointBounds12375 := by
 decide +kernel
def cuts12376 : List PrefixCut := [⟨20,166002188,166002314⟩,
⟨70,587662558,587663003⟩,
⟨120,998058915,998059669⟩,
⟨128,1071101560,1071102369⟩]
theorem checked12376 : checkPrefixCuts (2^48) 1626079233 9 Manual.Count131072.C012376.packed 128 cuts12376 = true := by
 decide +kernel
def pointBounds12376 : List (Nat × Nat × Nat) := [(1626099712,93734185065514,93734561311095),(1626150912,93734606725884,93734982971784),(1626202112,93735017122241,93735393368450)]
theorem point_links_checked12376 : (cuts12376.take 3).map (fun c => (1626079233-1+2*2^9*c.k,93734019063326+c.lower,93734395308781+c.upper)) = pointBounds12376 := by
 decide +kernel
def cuts12377 : List PrefixCut := [⟨42,351360747,351361012⟩,
⟨92,761038983,761039556⟩,
⟨128,1065476806,1065477607⟩]
theorem checked12377 : checkPrefixCuts (2^48) 1626210305 9 Manual.Count131072.C012377.packed 128 cuts12377 = true := by
 decide +kernel
def pointBounds12377 : List (Nat × Nat × Nat) := [(1626253312,93735441525633,93735817772162),(1626304512,93735851203869,93736227450706)]
theorem point_links_checked12377 : (cuts12377.take 2).map (fun c => (1626210305-1+2*2^9*c.k,93735090164886+c.lower,93735466411150+c.upper)) = pointBounds12377 := by
 decide +kernel
def cuts12378 : List PrefixCut := [⟨14,120977102,120977191⟩,
⟨64,532879374,532879772⟩,
⟨114,953075680,953076393⟩,
⟨128,1059507119,1059507912⟩]
theorem checked12378 : checkPrefixCuts (2^48) 1626341377 9 Manual.Count131072.C012378.packed 128 cuts12378 = true := by
 decide +kernel
def pointBounds12378 : List (Nat × Nat × Nat) := [(1626355712,93736276618794,93736652865948),(1626406912,93736688521066,93737064768529),(1626458112,93737108717372,93737484965150)]
theorem point_links_checked12378 : (cuts12378.take 3).map (fun c => (1626341377-1+2*2^9*c.k,93736155641692+c.lower,93736531888757+c.upper)) = pointBounds12378 := by
 decide +kernel
def cuts12379 : List PrefixCut := [⟨36,307348424,307348649⟩,
⟨86,721634491,721635025⟩,
⟨128,1066862902,1066863697⟩]
theorem checked12379 : checkPrefixCuts (2^48) 1626472449 9 Manual.Count131072.C012379.packed 128 cuts12379 = true := by
 decide +kernel
def pointBounds12379 : List (Nat × Nat × Nat) := [(1626509312,93737522497235,93737898745318),(1626560512,93737936783302,93738313031694)]
theorem point_links_checked12379 : (cuts12379.take 2).map (fun c => (1626472449-1+2*2^9*c.k,93737215148811+c.lower,93737591396669+c.upper)) = pointBounds12379 := by
 decide +kernel
def cuts12380 : List PrefixCut := [⟨8,63680232,63680281⟩,
⟨58,496455678,496456048⟩,
⟨108,907934182,907934858⟩,
⟨128,1071968219,1071969019⟩]
theorem checked12380 : checkPrefixCuts (2^48) 1626603521 9 Manual.Count131072.C012380.packed 128 cuts12380 = true := by
 decide +kernel
def pointBounds12380 : List (Nat × Nat × Nat) := [(1626611712,93738345691945,93738721940647),(1626662912,93738778467391,93739154716414),(1626714112,93739189945895,93739566195224)]
theorem point_links_checked12380 : (cuts12380.take 3).map (fun c => (1626603521-1+2*2^9*c.k,93738282011713+c.lower,93738658260366+c.upper)) = pointBounds12380 := by
 decide +kernel
def cuts12381 : List PrefixCut := [⟨30,251930144,251930332⟩,
⟨80,663728719,663729218⟩,
⟨128,1070151007,1070151807⟩]
theorem checked12381 : checkPrefixCuts (2^48) 1626734593 9 Manual.Count131072.C012381.packed 128 cuts12381 = true := by
 decide +kernel
def pointBounds12381 : List (Nat × Nat × Nat) := [(1626765312,93739605910076,93739982159717),(1626816512,93740017708651,93740393958603)]
theorem point_links_checked12381 : (cuts12381.take 2).map (fun c => (1626734593-1+2*2^9*c.k,93739353979932+c.lower,93739730229385+c.upper)) = pointBounds12381 := by
 decide +kernel
def cuts12382 : List PrefixCut := [⟨2,17128638,17128651⟩,
⟨52,436859922,436860249⟩,
⟨102,855540039,855540678⟩,
⟨128,1066432101,1066432900⟩]
theorem checked12382 : checkPrefixCuts (2^48) 1626865665 9 Manual.Count131072.C012382.packed 128 cuts12382 = true := by
 decide +kernel
def pointBounds12382 : List (Nat × Nat × Nat) := [(1626867712,93740441259577,93740817509843),(1626918912,93740860990861,93741237241441),(1626970112,93741279670978,93741655921870)]
theorem point_links_checked12382 : (cuts12382.take 3).map (fun c => (1626865665-1+2*2^9*c.k,93740424130939+c.lower,93740800381192+c.upper)) = pointBounds12382 := by
 decide +kernel
def cuts12383 : List PrefixCut := [⟨24,206044702,206044854⟩,
⟨74,626255390,626255859⟩,
⟨124,1038149247,1038150026⟩,
⟨128,1068422326,1068423128⟩]
theorem checked12383 : checkPrefixCuts (2^48) 1626996737 9 Manual.Count131072.C012383.packed 128 cuts12383 = true := by
 decide +kernel
def pointBounds12383 : List (Nat × Nat × Nat) := [(1627021312,93741696607742,93742072858946),(1627072512,93742116818430,93742493069951),(1627123712,93742528712287,93742904964118)]
theorem point_links_checked12383 : (cuts12383.take 3).map (fun c => (1626996737-1+2*2^9*c.k,93741490563040+c.lower,93741866814092+c.upper)) = pointBounds12383 := by
 decide +kernel
def cuts12384 : List PrefixCut := [⟨46,375034203,375034486⟩,
⟨96,782058652,782059240⟩,
⟨128,1052248111,1052248902⟩]
theorem checked12384 : checkPrefixCuts (2^48) 1627127809 9 Manual.Count131072.C012384.packed 128 cuts12384 = true := by
 decide +kernel
def pointBounds12384 : List (Nat × Nat × Nat) := [(1627174912,93742934019569,93743310271706),(1627226112,93743341044018,93743717296460)]
theorem point_links_checked12384 : (cuts12384.take 2).map (fun c => (1627127809-1+2*2^9*c.k,93742558985366+c.lower,93742935237220+c.upper)) = pointBounds12384 := by
 decide +kernel
def cuts12385 : List PrefixCut := [⟨18,153946753,153946866⟩,
⟨68,569767029,569767455⟩,
⟨118,993011682,993012429⟩,
⟨128,1074476535,1074477343⟩]
theorem checked12385 : checkPrefixCuts (2^48) 1627258881 9 Manual.Count131072.C012385.packed 128 cuts12385 = true := by
 decide +kernel
def pointBounds12385 : List (Nat × Nat × Nat) := [(1627277312,93743765180230,93744141432988),(1627328512,93744181000506,93744557253577),(1627379712,93744604245159,93744980498551)]
theorem point_links_checked12385 : (cuts12385.take 3).map (fun c => (1627258881-1+2*2^9*c.k,93743611233477+c.lower,93743987486122+c.upper)) = pointBounds12385 := by
 decide +kernel
def cuts12386 : List PrefixCut := [⟨40,341939466,341939723⟩,
⟨90,759276980,759277546⟩,
⟨128,1079924548,1079925356⟩]
theorem checked12386 : checkPrefixCuts (2^48) 1627389953 9 Manual.Count131072.C012386.packed 128 cuts12386 = true := by
 decide +kernel
def pointBounds12386 : List (Nat × Nat × Nat) := [(1627430912,93745027649478,93745403903188),(1627482112,93745444986992,93745821241011)]
theorem point_links_checked12386 : (cuts12386.take 2).map (fun c => (1627389953-1+2*2^9*c.k,93744685710012+c.lower,93745061963465+c.upper)) = pointBounds12386 := by
 decide +kernel
def cuts12387 : List PrefixCut := [⟨12,103594860,103594937⟩,
⟨62,518830888,518831279⟩,
⟨112,932497444,932498146⟩,
⟨128,1063408454,1063409252⟩]
theorem checked12387 : checkPrefixCuts (2^48) 1627521025 9 Manual.Count131072.C012387.packed 128 cuts12387 = true := by
 decide +kernel
def pointBounds12387 : List (Nat × Nat × Nat) := [(1627533312,93745869229420,93746245483758),(1627584512,93746284465448,93746660720100),(1627635712,93746698132004,93747074386967)]
theorem point_links_checked12387 : (cuts12387.take 3).map (fun c => (1627521025-1+2*2^9*c.k,93745765634560+c.lower,93746141888821+c.upper)) = pointBounds12387 := by
 decide +kernel
def cuts12388 : List PrefixCut := [⟨34,289832779,289832996⟩,
⟨84,709179861,709180391⟩,
⟨128,1072314999,1072315801⟩]
theorem checked12388 : checkPrefixCuts (2^48) 1627652097 9 Manual.Count131072.C012388.packed 128 cuts12388 = true := by
 decide +kernel
def pointBounds12388 : List (Nat × Nat × Nat) := [(1627686912,93747118875793,93747495131069),(1627738112,93747538222875,93747914478464)]
theorem point_links_checked12388 : (cuts12388.take 2).map (fun c => (1627652097-1+2*2^9*c.k,93746829043014+c.lower,93747205298073+c.upper)) = pointBounds12388 := by
 decide +kernel
def cuts12389 : List PrefixCut := [⟨6,53086075,53086114⟩,
⟨56,470677672,470678021⟩,
⟨106,887910261,887910922⟩,
⟨128,1069807832,1069808630⟩]
theorem checked12389 : checkPrefixCuts (2^48) 1627783169 9 Manual.Count131072.C012389.packed 128 cuts12389 = true := by
 decide +kernel
def pointBounds12389 : List (Nat × Nat × Nat) := [(1627789312,93747954444088,93748330699988),(1627840512,93748372035685,93748748291895),(1627891712,93748789268274,93749165524796)]
theorem point_links_checked12389 : (cuts12389.take 3).map (fun c => (1627783169-1+2*2^9*c.k,93747901358013+c.lower,93748277613874+c.upper)) = pointBounds12389 := by
 decide +kernel
def cuts12390 : List PrefixCut := [⟨28,235494824,235495001⟩,
⟨78,658579745,658580237⟩,
⟨128,1074216972,1074217779⟩]
theorem checked12390 : checkPrefixCuts (2^48) 1627914241 9 Manual.Count131072.C012390.packed 128 cuts12390 = true := by
 decide +kernel
def pointBounds12390 : List (Nat × Nat × Nat) := [(1627942912,93749206660669,93749582917505),(1627994112,93749629745590,93750006002741),(1628045312,93750045382817,93750421640283)]
theorem point_links_checked12390 : (cuts12390.take 3).map (fun c => (1627914241-1+2*2^9*c.k,93748971165845+c.lower,93749347422504+c.upper)) = pointBounds12390 := by
 decide +kernel
def cuts12391 : List PrefixCut := [⟨50,424268642,424268963⟩,
⟨100,837632116,837632748⟩,
⟨128,1072747437,1072748246⟩]
theorem checked12391 : checkPrefixCuts (2^48) 1628045313 9 Manual.Count131072.C012391.packed 128 cuts12391 = true := by
 decide +kernel
def pointBounds12391 : List (Nat × Nat × Nat) := [(1628096512,93750469651459,93750845909246),(1628147712,93750883014933,93751259273031)]
theorem point_links_checked12391 : (cuts12391.take 2).map (fun c => (1628045313-1+2*2^9*c.k,93750045382817+c.lower,93750421640283+c.upper)) = pointBounds12391 := by
 decide +kernel
def cuts12392 : List PrefixCut := [⟨22,181174260,181174394⟩,
⟨72,585695351,585695789⟩,
⟨122,1002304365,1002305114⟩,
⟨128,1052607729,1052608516⟩]
theorem checked12392 : checkPrefixCuts (2^48) 1628176385 9 Manual.Count131072.C012392.packed 128 cuts12392 = true := by
 decide +kernel
def pointBounds12392 : List (Nat × Nat × Nat) := [(1628198912,93751299304514,93751675562923),(1628250112,93751703825605,93752080084318),(1628301312,93752120434619,93752496693643)]
theorem point_links_checked12392 : (cuts12392.take 3).map (fun c => (1628176385-1+2*2^9*c.k,93751118130254+c.lower,93751494388529+c.upper)) = pointBounds12392 := by
 decide +kernel
def cuts12393 : List PrefixCut := [⟨44,364218318,364218594⟩,
⟨94,793765477,793766072⟩,
⟨128,1077587448,1077588258⟩]
theorem checked12393 : checkPrefixCuts (2^48) 1628307457 9 Manual.Count131072.C012393.packed 128 cuts12393 = true := by
 decide +kernel
def pointBounds12393 : List (Nat × Nat × Nat) := [(1628352512,93752534956301,93752911215639),(1628403712,93752964503460,93753340763117)]
theorem point_links_checked12393 : (cuts12393.take 2).map (fun c => (1628307457-1+2*2^9*c.k,93752170737983+c.lower,93752546997045+c.upper)) = pointBounds12393 := by
 decide +kernel
def cuts12394 : List PrefixCut := [⟨16,133266340,133266442⟩,
⟨66,562440723,562441146⟩,
⟨116,968441180,968441911⟩,
⟨128,1062809785,1062810590⟩]
theorem checked12394 : checkPrefixCuts (2^48) 1628438529 9 Manual.Count131072.C012394.packed 128 cuts12394 = true := by
 decide +kernel
def pointBounds12394 : List (Nat × Nat × Nat) := [(1628454912,93753381591771,93753757851745),(1628506112,93753810766154,93754187026449),(1628557312,93754216766611,93754593027214)]
theorem point_links_checked12394 : (cuts12394.take 3).map (fun c => (1628438529-1+2*2^9*c.k,93753248325431+c.lower,93753624585303+c.upper)) = pointBounds12394 := by
 decide +kernel
def cuts12395 : List PrefixCut := [⟨38,312483082,312483317⟩,
⟨88,741271334,741271882⟩,
⟨128,1078969245,1078970046⟩]
theorem checked12395 : checkPrefixCuts (2^48) 1628569601 9 Manual.Count131072.C012395.packed 128 cuts12395 = true := by
 decide +kernel
def pointBounds12395 : List (Nat × Nat × Nat) := [(1628608512,93754623618298,93754999879210),(1628659712,93755052406550,93755428667775)]
theorem point_links_checked12395 : (cuts12395.take 2).map (fun c => (1628569601-1+2*2^9*c.k,93754311135216+c.lower,93754687395893+c.upper)) = pointBounds12395 := by
 decide +kernel
def cuts12396 : List PrefixCut := [⟨10,89348550,89348614⟩,
⟨60,506531032,506531412⟩,
⟨110,925428549,925429238⟩,
⟨128,1076290634,1076291436⟩]
theorem checked12396 : checkPrefixCuts (2^48) 1628700673 9 Manual.Count131072.C012396.packed 128 cuts12396 = true := by
 decide +kernel
def pointBounds12396 : List (Nat × Nat × Nat) := [(1628710912,93755479453011,93755855714553),(1628762112,93755896635493,93756272897351),(1628813312,93756315533010,93756691795177)]
theorem point_links_checked12396 : (cuts12396.take 3).map (fun c => (1628700673-1+2*2^9*c.k,93755390104461+c.lower,93755766365939+c.upper)) = pointBounds12396 := by
 decide +kernel
def cuts12397 : List PrefixCut := [⟨32,264047694,264047890⟩,
⟨82,680154022,680154529⟩,
⟨128,1068254782,1068255580⟩]
theorem checked12397 : checkPrefixCuts (2^48) 1628831745 9 Manual.Count131072.C012397.packed 128 cuts12397 = true := by
 decide +kernel
def pointBounds12397 : List (Nat × Nat × Nat) := [(1628864512,93756730442789,93757106705265),(1628915712,93757146549117,93757522811904)]
theorem point_links_checked12397 : (cuts12397.take 2).map (fun c => (1628831745-1+2*2^9*c.k,93756466395095+c.lower,93756842657375+c.upper)) = pointBounds12397 := by
 decide +kernel
def cuts12398 : List PrefixCut := [⟨4,32830806,32830831⟩,
⟨54,449429383,449429719⟩,
⟨104,867397174,867397824⟩,
⟨128,1066441268,1066442067⟩]
theorem checked12398 : checkPrefixCuts (2^48) 1628962817 9 Manual.Count131072.C012398.packed 128 cuts12398 = true := by
 decide +kernel
def pointBounds12398 : List (Nat × Nat × Nat) := [(1628966912,93757567480683,93757943743786),(1629018112,93757984079260,93758360342674),(1629069312,93758402047051,93758778310779)]
theorem point_links_checked12398 : (cuts12398.take 3).map (fun c => (1628962817-1+2*2^9*c.k,93757534649877+c.lower,93757910912955+c.upper)) = pointBounds12398 := by
 decide +kernel
def cuts12399 : List PrefixCut := [⟨26,218219401,218219564⟩,
⟨76,627349262,627349730⟩,
⟨126,1047696403,1047697186⟩,
⟨128,1067046221,1067047018⟩]
theorem checked12399 : checkPrefixCuts (2^48) 1629093889 9 Manual.Count131072.C012399.packed 128 cuts12399 = true := by
 decide +kernel
def pointBounds12399 : List (Nat × Nat × Nat) := [(1629120512,93758819310546,93759195574586),(1629171712,93759228440407,93759604704752),(1629222912,93759648787548,93760025052208)]
theorem point_links_checked12399 : (cuts12399.take 3).map (fun c => (1629093889-1+2*2^9*c.k,93758601091145+c.lower,93758977355022+c.upper)) = pointBounds12399 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000074
