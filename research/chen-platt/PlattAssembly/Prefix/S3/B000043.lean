import PlattAssemblyKernel
import PlattCertificates.Count131072.C021376
import PlattCertificates.Count131072.C021377
import PlattCertificates.Count131072.C021378
import PlattCertificates.Count131072.C021379
import PlattCertificates.Count131072.C021380
import PlattCertificates.Count131072.C021381
import PlattCertificates.Count131072.C021382
import PlattCertificates.Count131072.C021383
import PlattCertificates.Count131072.C021384
import PlattCertificates.Count131072.C021385
import PlattCertificates.Count131072.C021386
import PlattCertificates.Count131072.C021387
import PlattCertificates.Count131072.C021388
import PlattCertificates.Count131072.C021389
import PlattCertificates.Count131072.C021390
import PlattCertificates.Count131072.C021391
import PlattCertificates.Count131072.C021392
import PlattCertificates.Count131072.C021393
import PlattCertificates.Count131072.C021394
import PlattCertificates.Count131072.C021395
import PlattCertificates.Count131072.C021396
import PlattCertificates.Count131072.C021397
import PlattCertificates.Count131072.C021398
import PlattCertificates.Count131072.C021399
import PlattCertificates.Count131072.C021400
import PlattCertificates.Count131072.C021401
import PlattCertificates.Count131072.C021402
import PlattCertificates.Count131072.C021403
import PlattCertificates.Count131072.C021404
import PlattCertificates.Count131072.C021405
import PlattCertificates.Count131072.C021406
import PlattCertificates.Count131072.C021407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21376 : List PrefixCut := [⟨4,19462366,19462377⟩,
⟨90,428967920,428968165⟩,
⟨128,614354764,614355111⟩]
theorem checked21376 : checkPrefixCuts (2^48) 2805727233 9 Manual.Count131072.C021376.packed 128 cuts21376 = true := by
 decide +kernel
def pointBounds21376 : List (Nat × Nat × Nat) := [(2805731328,100881747779570,100882128650348),(2805819392,100882157285124,100882538156136)]
theorem point_links_checked21376 : (cuts21376.take 2).map (fun c => (2805727233-1+2*2^9*c.k,100881728317204+c.lower,100882109187971+c.upper)) = pointBounds21376 := by
 decide +kernel
def cuts21377 : List PrefixCut := [⟨48,226714117,226714250⟩,
⟨128,601184938,601185284⟩]
theorem checked21377 : checkPrefixCuts (2^48) 2805858305 9 Manual.Count131072.C021377.packed 128 cuts21377 = true := by
 decide +kernel
def pointBounds21377 : List (Nat × Nat × Nat) := [(2805907456,100882569386085,100882950257332)]
theorem point_links_checked21377 : (cuts21377.take 1).map (fun c => (2805858305-1+2*2^9*c.k,100882342671968+c.lower,100882723543082+c.upper)) = pointBounds21377 := by
 decide +kernel
def cuts21378 : List PrefixCut := [⟨6,28388316,28388330⟩,
⟨92,440563643,440563892⟩,
⟨128,608178546,608178894⟩]
theorem checked21378 : checkPrefixCuts (2^48) 2805989377 9 Manual.Count131072.C021378.packed 128 cuts21378 = true := by
 decide +kernel
def pointBounds21378 : List (Nat × Nat × Nat) := [(2805995520,100882972245222,100883353116696),(2806083584,100883384420549,100883765292258)]
theorem point_links_checked21378 : (cuts21378.take 2).map (fun c => (2805989377-1+2*2^9*c.k,100882943856906+c.lower,100883324728366+c.upper)) = pointBounds21378 := by
 decide +kernel
def cuts21379 : List PrefixCut := [⟨50,239933310,239933448⟩,
⟨128,606846140,606846487⟩]
theorem checked21379 : checkPrefixCuts (2^48) 2806120449 9 Manual.Count131072.C021379.packed 128 cuts21379 = true := by
 decide +kernel
def pointBounds21379 : List (Nat × Nat × Nat) := [(2806171648,100883791968762,100884172840708)]
theorem point_links_checked21379 : (cuts21379.take 1).map (fun c => (2806120449-1+2*2^9*c.k,100883552035452+c.lower,100883932907260+c.upper)) = pointBounds21379 := by
 decide +kernel
def cuts21380 : List PrefixCut := [⟨8,37312590,37312612⟩,
⟨94,443431084,443431338⟩,
⟨128,605614172,605614518⟩]
theorem checked21380 : checkPrefixCuts (2^48) 2806251521 9 Manual.Count131072.C021380.packed 128 cuts21380 = true := by
 decide +kernel
def pointBounds21380 : List (Nat × Nat × Nat) := [(2806259712,100884196194182,100884577066359),(2806347776,100884602312676,100884983185085)]
theorem point_links_checked21380 : (cuts21380.take 2).map (fun c => (2806251521-1+2*2^9*c.k,100884158881592+c.lower,100884539753747+c.upper)) = pointBounds21380 := by
 decide +kernel
def cuts21381 : List PrefixCut := [⟨52,248636673,248636812⟩,
⟨128,609898620,609898971⟩]
theorem checked21381 : checkPrefixCuts (2^48) 2806382593 9 Manual.Count131072.C021381.packed 128 cuts21381 = true := by
 decide +kernel
def pointBounds21381 : List (Nat × Nat × Nat) := [(2806435840,100885013132437,100885394005077)]
theorem point_links_checked21381 : (cuts21381.take 1).map (fun c => (2806382593-1+2*2^9*c.k,100884764495764+c.lower,100885145368265+c.upper)) = pointBounds21381 := by
 decide +kernel
def cuts21382 : List PrefixCut := [⟨10,46937241,46937268⟩,
⟨96,452014594,452014855⟩,
⟨128,600242216,600242560⟩]
theorem checked21382 : checkPrefixCuts (2^48) 2806513665 9 Manual.Count131072.C021382.packed 128 cuts21382 = true := by
 decide +kernel
def pointBounds21382 : List (Nat × Nat × Nat) := [(2806523904,100885421331625,100885802204504),(2806611968,100885826408978,100886207282091)]
theorem point_links_checked21382 : (cuts21382.take 2).map (fun c => (2806513665-1+2*2^9*c.k,100885374394384+c.lower,100885755267236+c.upper)) = pointBounds21382 := by
 decide +kernel
def cuts21383 : List PrefixCut := [⟨54,256536058,256536211⟩,
⟨128,599913303,599913658⟩]
theorem checked21383 : checkPrefixCuts (2^48) 2806644737 9 Manual.Count131072.C021383.packed 128 cuts21383 = true := by
 decide +kernel
def pointBounds21383 : List (Nat × Nat × Nat) := [(2806700032,100886231172658,100886612046007)]
theorem point_links_checked21383 : (cuts21383.take 1).map (fun c => (2806644737-1+2*2^9*c.k,100885974636600+c.lower,100886355509796+c.upper)) = pointBounds21383 := by
 decide +kernel
def cuts21384 : List PrefixCut := [⟨12,55858103,55858138⟩,
⟨98,459593612,459593883⟩,
⟨128,599784950,599785306⟩]
theorem checked21384 : checkPrefixCuts (2^48) 2806775809 9 Manual.Count131072.C021384.packed 128 cuts21384 = true := by
 decide +kernel
def pointBounds21384 : List (Nat × Nat × Nat) := [(2806788096,100886630408006,100887011281592),(2806876160,100887034143515,100887415017337)]
theorem point_links_checked21384 : (cuts21384.take 2).map (fun c => (2806775809-1+2*2^9*c.k,100886574549903+c.lower,100886955423454+c.upper)) = pointBounds21384 := by
 decide +kernel
def cuts21385 : List PrefixCut := [⟨56,261525959,261526110⟩,
⟨128,596848975,596849309⟩]
theorem checked21385 : checkPrefixCuts (2^48) 2806906881 9 Manual.Count131072.C021385.packed 128 cuts21385 = true := by
 decide +kernel
def pointBounds21385 : List (Nat × Nat × Nat) := [(2806964224,100887435860812,100887816734870)]
theorem point_links_checked21385 : (cuts21385.take 1).map (fun c => (2806906881-1+2*2^9*c.k,100887174334853+c.lower,100887555208760+c.upper)) = pointBounds21385 := by
 decide +kernel
def cuts21386 : List PrefixCut := [⟨14,66682510,66682549⟩,
⟨100,469176800,469177072⟩,
⟨128,598224979,598225327⟩]
theorem checked21386 : checkPrefixCuts (2^48) 2807037953 9 Manual.Count131072.C021386.packed 128 cuts21386 = true := by
 decide +kernel
def pointBounds21386 : List (Nat × Nat × Nat) := [(2807052288,100887837866338,100888218740618),(2807140352,100888240360628,100888621235141)]
theorem point_links_checked21386 : (cuts21386.take 2).map (fun c => (2807037953-1+2*2^9*c.k,100887771183828+c.lower,100888152058069+c.upper)) = pointBounds21386 := by
 decide +kernel
def cuts21387 : List PrefixCut := [⟨58,278446893,278447048⟩,
⟨128,611031237,611031581⟩]
theorem checked21387 : checkPrefixCuts (2^48) 2807169025 9 Manual.Count131072.C021387.packed 128 cuts21387 = true := by
 decide +kernel
def pointBounds21387 : List (Nat × Nat × Nat) := [(2807228416,100888647855700,100889028730444)]
theorem point_links_checked21387 : (cuts21387.take 1).map (fun c => (2807169025-1+2*2^9*c.k,100888369408807+c.lower,100888750283396+c.upper)) = pointBounds21387 := by
 decide +kernel
def cuts21388 : List PrefixCut := [⟨16,75299050,75299091⟩,
⟨102,484072034,484072312⟩,
⟨128,606490878,606491231⟩]
theorem checked21388 : checkPrefixCuts (2^48) 2807300097 9 Manual.Count131072.C021388.packed 128 cuts21388 = true := by
 decide +kernel
def pointBounds21388 : List (Nat × Nat × Nat) := [(2807316480,100889055739094,100889436614068),(2807404544,100889464512078,100889845387289)]
theorem point_links_checked21388 : (cuts21388.take 2).map (fun c => (2807300097-1+2*2^9*c.k,100888980440044+c.lower,100889361314977+c.upper)) = pointBounds21388 := by
 decide +kernel
def cuts21389 : List PrefixCut := [⟨60,282130414,282130577⟩,
⟨128,597439374,597439726⟩]
theorem checked21389 : checkPrefixCuts (2^48) 2807431169 9 Manual.Count131072.C021389.packed 128 cuts21389 = true := by
 decide +kernel
def pointBounds21389 : List (Nat × Nat × Nat) := [(2807492608,100889869061336,100890249936785)]
theorem point_links_checked21389 : (cuts21389.take 1).map (fun c => (2807431169-1+2*2^9*c.k,100889586930922+c.lower,100889967806208+c.upper)) = pointBounds21389 := by
 decide +kernel
def cuts21390 : List PrefixCut := [⟨18,85718581,85718628⟩,
⟨104,497059748,497060030⟩,
⟨128,607837922,607838268⟩]
theorem checked21390 : checkPrefixCuts (2^48) 2807562241 9 Manual.Count131072.C021390.packed 128 cuts21390 = true := by
 decide +kernel
def pointBounds21390 : List (Nat × Nat × Nat) := [(2807580672,100890270088877,100890650964562),(2807668736,100890681430044,100891062305964)]
theorem point_links_checked21390 : (cuts21390.take 2).map (fun c => (2807562241-1+2*2^9*c.k,100890184370296+c.lower,100890565245934+c.upper)) = pointBounds21390 := by
 decide +kernel
def cuts21391 : List PrefixCut := [⟨62,293131535,293131708⟩,
⟨128,596982701,596983058⟩]
theorem checked21391 : checkPrefixCuts (2^48) 2807693313 9 Manual.Count131072.C021391.packed 128 cuts21391 = true := by
 decide +kernel
def pointBounds21391 : List (Nat × Nat × Nat) := [(2807756800,100891085339753,100891466215910)]
theorem point_links_checked21391 : (cuts21391.take 1).map (fun c => (2807693313-1+2*2^9*c.k,100890792208218+c.lower,100891173084202+c.upper)) = pointBounds21391 := by
 decide +kernel
def cuts21392 : List PrefixCut := [⟨20,93128774,93128827⟩,
⟨106,502927573,502927860⟩,
⟨128,606177198,606177540⟩]
theorem checked21392 : checkPrefixCuts (2^48) 2807824385 9 Manual.Count131072.C021392.packed 128 cuts21392 = true := by
 decide +kernel
def pointBounds21392 : List (Nat × Nat × Nat) := [(2807844864,100891482319693,100891863196087),(2807932928,100891892118492,100892272995120)]
theorem point_links_checked21392 : (cuts21392.take 2).map (fun c => (2807824385-1+2*2^9*c.k,100891389190919+c.lower,100891770067260+c.upper)) = pointBounds21392 := by
 decide +kernel
def cuts21393 : List PrefixCut := [⟨64,300221060,300221233⟩,
⟨128,605046174,605046527⟩]
theorem checked21393 : checkPrefixCuts (2^48) 2807955457 9 Manual.Count131072.C021393.packed 128 cuts21393 = true := by
 decide +kernel
def pointBounds21393 : List (Nat × Nat × Nat) := [(2808020992,100892295589177,100892676466033)]
theorem point_links_checked21393 : (cuts21393.take 1).map (fun c => (2807955457-1+2*2^9*c.k,100891995368117+c.lower,100892376244800+c.upper)) = pointBounds21393 := by
 decide +kernel
def cuts21394 : List PrefixCut := [⟨22,103143716,103143773⟩,
⟨108,510197557,510197854⟩,
⟨128,604817460,604817811⟩]
theorem checked21394 : checkPrefixCuts (2^48) 2808086529 9 Manual.Count131072.C021394.packed 128 cuts21394 = true := by
 decide +kernel
def pointBounds21394 : List (Nat × Nat × Nat) := [(2808109056,100892703558007,100893084435100),(2808197120,100893110611848,100893491489181)]
theorem point_links_checked21394 : (cuts21394.take 2).map (fun c => (2808086529-1+2*2^9*c.k,100892600414291+c.lower,100892981291327+c.upper)) = pointBounds21394 := by
 decide +kernel
def cuts21395 : List PrefixCut := [⟨66,309815165,309815341⟩,
⟨128,599176401,599176747⟩]
theorem checked21395 : checkPrefixCuts (2^48) 2808217601 9 Manual.Count131072.C021395.packed 128 cuts21395 = true := by
 decide +kernel
def pointBounds21395 : List (Nat × Nat × Nat) := [(2808285184,100893515046916,100893895924479)]
theorem point_links_checked21395 : (cuts21395.take 1).map (fun c => (2808217601-1+2*2^9*c.k,100893205231751+c.lower,100893586109138+c.upper)) = pointBounds21395 := by
 decide +kernel
def cuts21396 : List PrefixCut := [⟨24,112455208,112455273⟩,
⟨110,523379593,523379891⟩,
⟨128,604560675,604561023⟩]
theorem checked21396 : checkPrefixCuts (2^48) 2808348673 9 Manual.Count131072.C021396.packed 128 cuts21396 = true := by
 decide +kernel
def pointBounds21396 : List (Nat × Nat × Nat) := [(2808373248,100893916863360,100894297741158),(2808461312,100894327787745,100894708665776)]
theorem point_links_checked21396 : (cuts21396.take 2).map (fun c => (2808348673-1+2*2^9*c.k,100893804408152+c.lower,100894185285885+c.upper)) = pointBounds21396 := by
 decide +kernel
def cuts21397 : List PrefixCut := [⟨68,318906300,318906488⟩,
⟨128,605734928,605735278⟩]
theorem checked21397 : checkPrefixCuts (2^48) 2808479745 9 Manual.Count131072.C021397.packed 128 cuts21397 = true := by
 decide +kernel
def pointBounds21397 : List (Nat × Nat × Nat) := [(2808549376,100894727875127,100895108753396)]
theorem point_links_checked21397 : (cuts21397.take 1).map (fun c => (2808479745-1+2*2^9*c.k,100894408968827+c.lower,100894789846908+c.upper)) = pointBounds21397 := by
 decide +kernel
def cuts21398 : List PrefixCut := [⟨26,123568872,123568943⟩,
⟨112,529543965,529544278⟩,
⟨128,604403940,604404296⟩]
theorem checked21398 : checkPrefixCuts (2^48) 2808610817 9 Manual.Count131072.C021398.packed 128 cuts21398 = true := by
 decide +kernel
def pointBounds21398 : List (Nat × Nat × Nat) := [(2808637440,100895138272627,100895519151129),(2808725504,100895544247720,100895925126464)]
theorem point_links_checked21398 : (cuts21398.take 2).map (fun c => (2808610817-1+2*2^9*c.k,100895014703755+c.lower,100895395582186+c.upper)) = pointBounds21398 := by
 decide +kernel
def cuts21399 : List PrefixCut := [⟨70,330200531,330200726⟩,
⟨128,602171117,602171469⟩]
theorem checked21399 : checkPrefixCuts (2^48) 2808741889 9 Manual.Count131072.C021399.packed 128 cuts21399 = true := by
 decide +kernel
def pointBounds21399 : List (Nat × Nat × Nat) := [(2808813568,100895949308226,100896330187208)]
theorem point_links_checked21399 : (cuts21399.take 1).map (fun c => (2808741889-1+2*2^9*c.k,100895619107695+c.lower,100895999986482+c.upper)) = pointBounds21399 := by
 decide +kernel
def cuts21400 : List PrefixCut := [⟨28,130772326,130772402⟩,
⟨114,535807396,535807701⟩,
⟨128,602042752,602043095⟩]
theorem checked21400 : checkPrefixCuts (2^48) 2808872961 9 Manual.Count131072.C021400.packed 128 cuts21400 = true := by
 decide +kernel
def pointBounds21400 : List (Nat × Nat × Nat) := [(2808901632,100896352051138,100896732930353),(2808989696,100896757086208,100897137965652)]
theorem point_links_checked21400 : (cuts21400.take 2).map (fun c => (2808872961-1+2*2^9*c.k,100896221278812+c.lower,100896602157951+c.upper)) = pointBounds21400 := by
 decide +kernel
def cuts21401 : List PrefixCut := [⟨72,338586596,338586791⟩,
⟨128,602014643,602014989⟩]
theorem checked21401 : checkPrefixCuts (2^48) 2809004033 9 Manual.Count131072.C021401.packed 128 cuts21401 = true := by
 decide +kernel
def pointBounds21401 : List (Nat × Nat × Nat) := [(2809077760,100897161908160,100897542787837)]
theorem point_links_checked21401 : (cuts21401.take 1).map (fun c => (2809004033-1+2*2^9*c.k,100896823321564+c.lower,100897204201046+c.upper)) = pointBounds21401 := by
 decide +kernel
def cuts21402 : List PrefixCut := [⟨30,144186794,144186875⟩,
⟨116,544274124,544274437⟩,
⟨128,603189009,603189355⟩]
theorem checked21402 : checkPrefixCuts (2^48) 2809135105 9 Manual.Count131072.C021402.packed 128 cuts21402 = true := by
 decide +kernel
def pointBounds21402 : List (Nat × Nat × Nat) := [(2809165824,100897569523001,100897950402910),(2809253888,100897969610331,100898350490472)]
theorem point_links_checked21402 : (cuts21402.take 2).map (fun c => (2809135105-1+2*2^9*c.k,100897425336207+c.lower,100897806216035+c.upper)) = pointBounds21402 := by
 decide +kernel
def cuts21403 : List PrefixCut := [⟨74,347472154,347472355⟩,
⟨128,598151243,598151593⟩]
theorem checked21403 : checkPrefixCuts (2^48) 2809266177 9 Manual.Count131072.C021403.packed 128 cuts21403 = true := by
 decide +kernel
def pointBounds21403 : List (Nat × Nat × Nat) := [(2809341952,100898375997370,100898756877745)]
theorem point_links_checked21403 : (cuts21403.take 1).map (fun c => (2809266177-1+2*2^9*c.k,100898028525216+c.lower,100898409405390+c.upper)) = pointBounds21403 := by
 decide +kernel
def cuts21404 : List PrefixCut := [⟨32,156496643,156496729⟩,
⟨118,567266410,567266735⟩,
⟨128,615756436,615756790⟩]
theorem checked21404 : checkPrefixCuts (2^48) 2809397249 9 Manual.Count131072.C021404.packed 128 cuts21404 = true := by
 decide +kernel
def pointBounds21404 : List (Nat × Nat × Nat) := [(2809430016,100898783173102,100899164053712),(2809518080,100899193942869,100899574823718)]
theorem point_links_checked21404 : (cuts21404.take 2).map (fun c => (2809397249-1+2*2^9*c.k,100898626676459+c.lower,100899007556983+c.upper)) = pointBounds21404 := by
 decide +kernel
def cuts21405 : List PrefixCut := [⟨76,355254007,355254204⟩,
⟨128,602102719,602103056⟩]
theorem checked21405 : checkPrefixCuts (2^48) 2809528321 9 Manual.Count131072.C021405.packed 128 cuts21405 = true := by
 decide +kernel
def pointBounds21405 : List (Nat × Nat × Nat) := [(2809606144,100899597686902,100899978567977)]
theorem point_links_checked21405 : (cuts21405.take 1).map (fun c => (2809528321-1+2*2^9*c.k,100899242432895+c.lower,100899623313773+c.upper)) = pointBounds21405 := by
 decide +kernel
def cuts21406 : List PrefixCut := [⟨34,162993715,162993810⟩,
⟨120,568114838,568115164⟩,
⟨128,604879654,604880003⟩]
theorem checked21406 : checkPrefixCuts (2^48) 2809659393 9 Manual.Count131072.C021406.packed 128 cuts21406 = true := by
 decide +kernel
def pointBounds21406 : List (Nat × Nat × Nat) := [(2809694208,100900007529329,100900388410639),(2809782272,100900412650452,100900793531993)]
theorem point_links_checked21406 : (cuts21406.take 2).map (fun c => (2809659393-1+2*2^9*c.k,100899844535614+c.lower,100900225416829+c.upper)) = pointBounds21406 := by
 decide +kernel
def cuts21407 : List PrefixCut := [⟨78,364537038,364537242⟩,
⟨128,604250297,604250638⟩]
theorem checked21407 : checkPrefixCuts (2^48) 2809790465 9 Manual.Count131072.C021407.packed 128 cuts21407 = true := by
 decide +kernel
def pointBounds21407 : List (Nat × Nat × Nat) := [(2809870336,100900813952306,100901194834074)]
theorem point_links_checked21407 : (cuts21407.take 1).map (fun c => (2809790465-1+2*2^9*c.k,100900449415268+c.lower,100900830296832+c.upper)) = pointBounds21407 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000043
