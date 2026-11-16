import PlattAssemblyKernel
import PlattCertificates.Count131072.C014512
import PlattCertificates.Count131072.C014513
import PlattCertificates.Count131072.C014514
import PlattCertificates.Count131072.C014515
import PlattCertificates.Count131072.C014516
import PlattCertificates.Count131072.C014517
import PlattCertificates.Count131072.C014518
import PlattCertificates.Count131072.C014519
import PlattCertificates.Count131072.C014520
import PlattCertificates.Count131072.C014521
import PlattCertificates.Count131072.C014522
import PlattCertificates.Count131072.C014523
import PlattCertificates.Count131072.C014524
import PlattCertificates.Count131072.C014525
import PlattCertificates.Count131072.C014526
import PlattCertificates.Count131072.C014527
import PlattCertificates.Count131072.C014528
import PlattCertificates.Count131072.C014529
import PlattCertificates.Count131072.C014530
import PlattCertificates.Count131072.C014531
import PlattCertificates.Count131072.C014532
import PlattCertificates.Count131072.C014533
import PlattCertificates.Count131072.C014534
import PlattCertificates.Count131072.C014535
import PlattCertificates.Count131072.C014536
import PlattCertificates.Count131072.C014537
import PlattCertificates.Count131072.C014538
import PlattCertificates.Count131072.C014539
import PlattCertificates.Count131072.C014540
import PlattCertificates.Count131072.C014541
import PlattCertificates.Count131072.C014542
import PlattCertificates.Count131072.C014543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14512 : List PrefixCut := [⟨53,384538968,384539225⟩,
⟨112,793283943,793284482⟩,
⟨128,904771020,904771633⟩]
theorem checked14512 : checkPrefixCuts (2^48) 1906049025 9 Manual.Count131072.C014512.packed 128 cuts14512 = true := by
 decide +kernel
def pointBounds14512 : List (Nat × Nat × Nat) := [(1906103296,95834756977227,95835134719505),(1906163712,95835165722202,95835543464762)]
theorem point_links_checked14512 : (cuts14512.take 2).map (fun c => (1906049025-1+2*2^9*c.k,95834372438259+c.lower,95834750180280+c.upper)) = pointBounds14512 := by
 decide +kernel
def cuts14513 : List PrefixCut := [⟨43,300198179,300198378⟩,
⟨102,727079176,727079662⟩,
⟨128,911205283,911205895⟩]
theorem checked14513 : checkPrefixCuts (2^48) 1906180097 9 Manual.Count131072.C014513.packed 128 cuts14513 = true := by
 decide +kernel
def pointBounds14513 : List (Nat × Nat × Nat) := [(1906224128,95835577407458,95835955150291),(1906284544,95836004288455,95836382031575)]
theorem point_links_checked14513 : (cuts14513.take 2).map (fun c => (1906180097-1+2*2^9*c.k,95835277209279+c.lower,95835654951913+c.upper)) = pointBounds14513 := by
 decide +kernel
def cuts14514 : List PrefixCut := [⟨33,232110332,232110490⟩,
⟨92,642575320,642575755⟩,
⟨128,897854388,897854998⟩]
theorem checked14514 : checkPrefixCuts (2^48) 1906311169 9 Manual.Count131072.C014514.packed 128 cuts14514 = true := by
 decide +kernel
def pointBounds14514 : List (Nat × Nat × Nat) := [(1906344960,95836420524894,95836798268298),(1906405376,95836830989882,95837208733563)]
theorem point_links_checked14514 : (cuts14514.take 2).map (fun c => (1906311169-1+2*2^9*c.k,95836188414562+c.lower,95836566157808+c.upper)) = pointBounds14514 := by
 decide +kernel
def cuts14515 : List PrefixCut := [⟨23,166098547,166098660⟩,
⟨82,583181290,583181684⟩,
⟨128,901926814,901927423⟩]
theorem checked14515 : checkPrefixCuts (2^48) 1906442241 9 Manual.Count131072.C014515.packed 128 cuts14515 = true := by
 decide +kernel
def pointBounds14515 : List (Nat × Nat × Nat) := [(1906465792,95837252367497,95837630111466),(1906526208,95837669450240,95838047194490)]
theorem point_links_checked14515 : (cuts14515.take 2).map (fun c => (1906442241-1+2*2^9*c.k,95837086268950+c.lower,95837464012806+c.upper)) = pointBounds14515 := by
 decide +kernel
def cuts14516 : List PrefixCut := [⟨13,93156673,93156735⟩,
⟨72,506522205,506522545⟩,
⟨128,903340849,903341452⟩]
theorem checked14516 : checkPrefixCuts (2^48) 1906573313 9 Manual.Count131072.C014516.packed 128 cuts14516 = true := by
 decide +kernel
def pointBounds14516 : List (Nat × Nat × Nat) := [(1906586624,95838081352437,95838459096964),(1906647040,95838494717969,95838872462774)]
theorem point_links_checked14516 : (cuts14516.take 2).map (fun c => (1906573313-1+2*2^9*c.k,95837988195764+c.lower,95838365940229+c.upper)) = pointBounds14516 := by
 decide +kernel
def cuts14517 : List PrefixCut := [⟨3,22291170,22291184⟩,
⟨62,449211676,449211975⟩,
⟨121,872871036,872871617⟩,
⟨128,923059767,923060382⟩]
theorem checked14517 : checkPrefixCuts (2^48) 1906704385 9 Manual.Count131072.C014517.packed 128 cuts14517 = true := by
 decide +kernel
def pointBounds14517 : List (Nat × Nat × Nat) := [(1906707456,95838913827783,95839291572865),(1906767872,95839340748289,95839718493656),(1906828288,95839764407649,95840142153298)]
theorem point_links_checked14517 : (cuts14517.take 3).map (fun c => (1906704385-1+2*2^9*c.k,95838891536613+c.lower,95839269281681+c.upper)) = pointBounds14517 := by
 decide +kernel
def cuts14518 : List PrefixCut := [⟨52,362238829,362239075⟩,
⟨111,772882026,772882550⟩,
⟨128,886684827,886685429⟩]
theorem checked14518 : checkPrefixCuts (2^48) 1906835457 9 Manual.Count131072.C014518.packed 128 cuts14518 = true := by
 decide +kernel
def pointBounds14518 : List (Nat × Nat × Nat) := [(1906888704,95840176835209,95840554581138),(1906949120,95840587478406,95840965224613)]
theorem point_links_checked14518 : (cuts14518.take 2).map (fun c => (1906835457-1+2*2^9*c.k,95839814596380+c.lower,95840192342063+c.upper)) = pointBounds14518 := by
 decide +kernel
def cuts14519 : List PrefixCut := [⟨42,297417591,297417795⟩,
⟨101,713643393,713643878⟩,
⟨128,898874354,898874967⟩]
theorem checked14519 : checkPrefixCuts (2^48) 1906966529 9 Manual.Count131072.C014519.packed 128 cuts14519 = true := by
 decide +kernel
def pointBounds14519 : List (Nat × Nat × Nat) := [(1907009536,95840998698798,95841376445287),(1907069952,95841414924600,95841792671370)]
theorem point_links_checked14519 : (cuts14519.take 2).map (fun c => (1906966529-1+2*2^9*c.k,95840701281207+c.lower,95841079027492+c.upper)) = pointBounds14519 := by
 decide +kernel
def cuts14520 : List PrefixCut := [⟨32,222716411,222716563⟩,
⟨91,640539337,640539773⟩,
⟨128,899697978,899698590⟩]
theorem checked14520 : checkPrefixCuts (2^48) 1907097601 9 Manual.Count131072.C014520.packed 128 cuts14520 = true := by
 decide +kernel
def pointBounds14520 : List (Nat × Nat × Nat) := [(1907130368,95841822871972,95842200619022),(1907190784,95842240694898,95842618442232)]
theorem point_links_checked14520 : (cuts14520.take 2).map (fun c => (1907097601-1+2*2^9*c.k,95841600155561+c.lower,95841977902459+c.upper)) = pointBounds14520 := by
 decide +kernel
def cuts14521 : List PrefixCut := [⟨22,157617915,157618020⟩,
⟨81,568330493,568330879⟩,
⟨128,896537005,896537617⟩]
theorem checked14521 : checkPrefixCuts (2^48) 1907228673 9 Manual.Count131072.C014521.packed 128 cuts14521 = true := by
 decide +kernel
def pointBounds14521 : List (Nat × Nat × Nat) := [(1907251200,95842657471454,95843035219069),(1907311616,95843068184032,95843445931928)]
theorem point_links_checked14521 : (cuts14521.take 2).map (fun c => (1907228673-1+2*2^9*c.k,95842499853539+c.lower,95842877601049+c.upper)) = pointBounds14521 := by
 decide +kernel
def cuts14522 : List PrefixCut := [⟨12,88986259,88986318⟩,
⟨71,499230137,499230471⟩,
⟨128,908575874,908576484⟩]
theorem checked14522 : checkPrefixCuts (2^48) 1907359745 9 Manual.Count131072.C014522.packed 128 cuts14522 = true := by
 decide +kernel
def pointBounds14522 : List (Nat × Nat × Nat) := [(1907372032,95843485376803,95843863124984),(1907432448,95843895620681,95844273369137)]
theorem point_links_checked14522 : (cuts14522.take 2).map (fun c => (1907359745-1+2*2^9*c.k,95843396390544+c.lower,95843774138666+c.upper)) = pointBounds14522 := by
 decide +kernel
def cuts14523 : List PrefixCut := [⟨2,12542841,12542849⟩,
⟨61,424826592,424826878⟩,
⟨120,846245762,846246328⟩,
⟨128,904086570,904087176⟩]
theorem checked14523 : checkPrefixCuts (2^48) 1907490817 9 Manual.Count131072.C014523.packed 128 cuts14523 = true := by
 decide +kernel
def pointBounds14523 : List (Nat × Nat × Nat) := [(1907492864,95844317509259,95844695257999),(1907553280,95844729793010,95845107542028),(1907613696,95845151212180,95845528961478)]
theorem point_links_checked14523 : (cuts14523.take 3).map (fun c => (1907490817-1+2*2^9*c.k,95844304966418+c.lower,95844682715150+c.upper)) = pointBounds14523 := by
 decide +kernel
def cuts14524 : List PrefixCut := [⟨51,356335053,356335293⟩,
⟨110,774038888,774039409⟩,
⟨128,904614749,904615358⟩]
theorem checked14524 : checkPrefixCuts (2^48) 1907621889 9 Manual.Count131072.C014524.packed 128 cuts14524 = true := by
 decide +kernel
def pointBounds14524 : List (Nat × Nat × Nat) := [(1907674112,95845565388041,95845943137619),(1907734528,95845983091876,95846360841735)]
theorem point_links_checked14524 : (cuts14524.take 2).map (fun c => (1907621889-1+2*2^9*c.k,95845209052988+c.lower,95845586802326+c.upper)) = pointBounds14524 := by
 decide +kernel
def cuts14525 : List PrefixCut := [⟨41,295229569,295229770⟩,
⟨100,712611851,712612337⟩,
⟨128,913110048,913110671⟩]
theorem checked14525 : checkPrefixCuts (2^48) 1907752961 9 Manual.Count131072.C014525.packed 128 cuts14525 = true := by
 decide +kernel
def pointBounds14525 : List (Nat × Nat × Nat) := [(1907794944,95846408897306,95846786647454),(1907855360,95846826279588,95847204030021)]
theorem point_links_checked14525 : (cuts14525.take 2).map (fun c => (1907752961-1+2*2^9*c.k,95846113667737+c.lower,95846491417684+c.upper)) = pointBounds14525 := by
 decide +kernel
def cuts14526 : List PrefixCut := [⟨31,218346243,218346396⟩,
⟨90,638062528,638062963⟩,
⟨128,914817307,914817927⟩]
theorem checked14526 : checkPrefixCuts (2^48) 1907884033 9 Manual.Count131072.C014526.packed 128 cuts14526 = true := by
 decide +kernel
def pointBounds14526 : List (Nat × Nat × Nat) := [(1907915776,95847245124028,95847622874751),(1907976192,95847664840313,95848042591318)]
theorem point_links_checked14526 : (cuts14526.take 2).map (fun c => (1907884033-1+2*2^9*c.k,95847026777785+c.lower,95847404528355+c.upper)) = pointBounds14526 := by
 decide +kernel
def cuts14527 : List PrefixCut := [⟨21,150914513,150914616⟩,
⟨80,569129103,569129494⟩,
⟨128,905756321,905756938⟩]
theorem checked14527 : checkPrefixCuts (2^48) 1908015105 9 Manual.Count131072.C014527.packed 128 cuts14527 = true := by
 decide +kernel
def pointBounds14527 : List (Nat × Nat × Nat) := [(1908036608,95848092509605,95848470260898),(1908097024,95848510724195,95848888475776)]
theorem point_links_checked14527 : (cuts14527.take 2).map (fun c => (1908015105-1+2*2^9*c.k,95847941595092+c.lower,95848319346282+c.upper)) = pointBounds14527 := by
 decide +kernel
def cuts14528 : List PrefixCut := [⟨11,75526039,75526089⟩,
⟨70,491796540,491796870⟩,
⟨128,902301215,902301825⟩]
theorem checked14528 : checkPrefixCuts (2^48) 1908146177 9 Manual.Count131072.C014528.packed 128 cuts14528 = true := by
 decide +kernel
def pointBounds14528 : List (Nat × Nat × Nat) := [(1908157440,95848922877452,95849300629309),(1908217856,95849339147953,95849716900090)]
theorem point_links_checked14528 : (cuts14528.take 2).map (fun c => (1908146177-1+2*2^9*c.k,95848847351413+c.lower,95849225103220+c.upper)) = pointBounds14528 := by
 decide +kernel
def cuts14529 : List PrefixCut := [⟨1,7817609,7817614⟩,
⟨60,424946722,424947012⟩,
⟨119,842210066,842210638⟩,
⟨128,904451825,904452438⟩]
theorem checked14529 : checkPrefixCuts (2^48) 1908277249 9 Manual.Count131072.C014529.packed 128 cuts14529 = true := by
 decide +kernel
def pointBounds14529 : List (Nat × Nat × Nat) := [(1908278272,95849757470237,95850135222659),(1908338688,95850174599350,95850552352057),(1908399104,95850591862694,95850969615683)]
theorem point_links_checked14529 : (cuts14529.take 3).map (fun c => (1908277249-1+2*2^9*c.k,95849749652628+c.lower,95850127405045+c.upper)) = pointBounds14529 := by
 decide +kernel
def cuts14530 : List PrefixCut := [⟨50,357515668,357515914⟩,
⟨109,771507947,771508474⟩,
⟨128,907191915,907192531⟩]
theorem checked14530 : checkPrefixCuts (2^48) 1908408321 9 Manual.Count131072.C014530.packed 128 cuts14530 = true := by
 decide +kernel
def pointBounds14530 : List (Nat × Nat × Nat) := [(1908459520,95851011620121,95851389373397),(1908519936,95851425612400,95851803365957)]
theorem point_links_checked14530 : (cuts14530.take 2).map (fun c => (1908408321-1+2*2^9*c.k,95850654104453+c.lower,95851031857483+c.upper)) = pointBounds14530 := by
 decide +kernel
def cuts14531 : List PrefixCut := [⟨40,286111725,286111917⟩,
⟨99,698603012,698603483⟩,
⟨128,901230709,901231317⟩]
theorem checked14531 : checkPrefixCuts (2^48) 1908539393 9 Manual.Count131072.C014531.packed 128 cuts14531 = true := by
 decide +kernel
def pointBounds14531 : List (Nat × Nat × Nat) := [(1908580352,95851847408093,95852225161931),(1908640768,95852259899380,95852637653497)]
theorem point_links_checked14531 : (cuts14531.take 2).map (fun c => (1908539393-1+2*2^9*c.k,95851561296368+c.lower,95851939050014+c.upper)) = pointBounds14531 := by
 decide +kernel
def cuts14532 : List PrefixCut := [⟨30,212357534,212357682⟩,
⟨89,618039188,618039611⟩,
⟨128,897039411,897040026⟩]
theorem checked14532 : checkPrefixCuts (2^48) 1908670465 9 Manual.Count131072.C014532.packed 128 cuts14532 = true := by
 decide +kernel
def pointBounds14532 : List (Nat × Nat × Nat) := [(1908701184,95852674884611,95853052639013),(1908761600,95853080566265,95853458320942)]
theorem point_links_checked14532 : (cuts14532.take 2).map (fun c => (1908670465-1+2*2^9*c.k,95852462527077+c.lower,95852840281331+c.upper)) = pointBounds14532 := by
 decide +kernel
def cuts14533 : List PrefixCut := [⟨20,135811386,135811479⟩,
⟨79,550757207,550757584⟩,
⟨128,897715042,897715654⟩]
theorem checked14533 : checkPrefixCuts (2^48) 1908801537 9 Manual.Count131072.C014533.packed 128 cuts14533 = true := by
 decide +kernel
def pointBounds14533 : List (Nat × Nat × Nat) := [(1908822016,95853495377874,95853873132836),(1908882432,95853910323695,95854288078941)]
theorem point_links_checked14533 : (cuts14533.take 2).map (fun c => (1908801537-1+2*2^9*c.k,95853359566488+c.lower,95853737321357+c.upper)) = pointBounds14533 := by
 decide +kernel
def cuts14534 : List PrefixCut := [⟨10,72251019,72251068⟩,
⟨69,487023247,487023577⟩,
⟨128,903404167,903404775⟩]
theorem checked14534 : checkPrefixCuts (2^48) 1908932609 9 Manual.Count131072.C014534.packed 128 cuts14534 = true := by
 decide +kernel
def pointBounds14534 : List (Nat × Nat × Nat) := [(1908942848,95854329532549,95854707288079),(1909003264,95854744304777,95855122060588),(1909063680,95855160685697,95855538441786)]
theorem point_links_checked14534 : (cuts14534.take 3).map (fun c => (1908932609-1+2*2^9*c.k,95854257281530+c.lower,95854635037011+c.upper)) = pointBounds14534 := by
 decide +kernel
def cuts14535 : List PrefixCut := [⟨59,417399799,417400081⟩,
⟨118,836408070,836408637⟩,
⟨128,909829005,909829622⟩]
theorem checked14535 : checkPrefixCuts (2^48) 1909063681 9 Manual.Count131072.C014535.packed 128 cuts14535 = true := by
 decide +kernel
def pointBounds14535 : List (Nat × Nat × Nat) := [(1909124096,95855578085496,95855955841867),(1909184512,95855997093767,95856374850423)]
theorem point_links_checked14535 : (cuts14535.take 2).map (fun c => (1909063681-1+2*2^9*c.k,95855160685697+c.lower,95855538441786+c.upper)) = pointBounds14535 := by
 decide +kernel
def cuts14536 : List PrefixCut := [⟨49,341888437,341888672⟩,
⟨108,757626893,757627412⟩,
⟨128,898119944,898120556⟩]
theorem checked14536 : checkPrefixCuts (2^48) 1909194753 9 Manual.Count131072.C014536.packed 128 cuts14536 = true := by
 decide +kernel
def pointBounds14536 : List (Nat × Nat × Nat) := [(1909244928,95856412403139,95856790160080),(1909305344,95856828141595,95857205898820)]
theorem point_links_checked14536 : (cuts14536.take 2).map (fun c => (1909194753-1+2*2^9*c.k,95856070514702+c.lower,95856448271408+c.upper)) = pointBounds14536 := by
 decide +kernel
def cuts14537 : List PrefixCut := [⟨39,271841630,271841817⟩,
⟨98,689470182,689470648⟩,
⟨128,911178027,911178642⟩]
theorem checked14537 : checkPrefixCuts (2^48) 1909325825 9 Manual.Count131072.C014537.packed 128 cuts14537 = true := by
 decide +kernel
def pointBounds14537 : List (Nat × Nat × Nat) := [(1909365760,95857240476276,95857618233781),(1909426176,95857658104828,95858035862612)]
theorem point_links_checked14537 : (cuts14537.take 2).map (fun c => (1909325825-1+2*2^9*c.k,95856968634646+c.lower,95857346391964+c.upper)) = pointBounds14537 := by
 decide +kernel
def cuts14538 : List PrefixCut := [⟨29,199592881,199593015⟩,
⟨88,623533523,623533943⟩,
⟨128,905956616,905957232⟩]
theorem checked14538 : checkPrefixCuts (2^48) 1909456897 9 Manual.Count131072.C014538.packed 128 cuts14538 = true := by
 decide +kernel
def pointBounds14538 : List (Nat × Nat × Nat) := [(1909486592,95858079405554,95858457163621),(1909547008,95858503346196,95858881104549)]
theorem point_links_checked14538 : (cuts14538.take 2).map (fun c => (1909456897-1+2*2^9*c.k,95857879812673+c.lower,95858257570606+c.upper)) = pointBounds14538 := by
 decide +kernel
def cuts14539 : List PrefixCut := [⟨19,137376892,137376983⟩,
⟨78,546845815,546846184⟩,
⟨128,903536171,903536785⟩]
theorem checked14539 : checkPrefixCuts (2^48) 1909587969 9 Manual.Count131072.C014539.packed 128 cuts14539 = true := by
 decide +kernel
def pointBounds14539 : List (Nat × Nat × Nat) := [(1909607424,95858923146181,95859300904821),(1909667840,95859332615104,95859710374022)]
theorem point_links_checked14539 : (cuts14539.take 2).map (fun c => (1909587969-1+2*2^9*c.k,95858785769289+c.lower,95859163527838+c.upper)) = pointBounds14539 := by
 decide +kernel
def cuts14540 : List PrefixCut := [⟨9,65883490,65883534⟩,
⟨68,476800352,476800676⟩,
⟨127,892862661,892863266⟩,
⟨128,899642171,899642781⟩]
theorem checked14540 : checkPrefixCuts (2^48) 1909719041 9 Manual.Count131072.C014540.packed 128 cuts14540 = true := by
 decide +kernel
def pointBounds14540 : List (Nat × Nat × Nat) := [(1909728256,95859755188950,95860132948157),(1909788672,95860166105812,95860543865299),(1909849088,95860582168121,95860959927889)]
theorem point_links_checked14540 : (cuts14540.take 3).map (fun c => (1909719041-1+2*2^9*c.k,95859689305460+c.lower,95860067064623+c.upper)) = pointBounds14540 := by
 decide +kernel
def cuts14541 : List PrefixCut := [⟨58,399395228,399395496⟩,
⟨117,826631632,826632185⟩,
⟨128,905622456,905623063⟩]
theorem checked14541 : checkPrefixCuts (2^48) 1909850113 9 Manual.Count131072.C014541.packed 128 cuts14541 = true := by
 decide +kernel
def pointBounds14541 : List (Nat × Nat × Nat) := [(1909909504,95860988342859,95861366102900),(1909969920,95861415579263,95861793339589)]
theorem point_links_checked14541 : (cuts14541.take 2).map (fun c => (1909850113-1+2*2^9*c.k,95860588947631+c.lower,95860966707404+c.upper)) = pointBounds14541 := by
 decide +kernel
def cuts14542 : List PrefixCut := [⟨48,332758304,332758534⟩,
⟨107,750831038,750831553⟩,
⟨128,901728904,901729520⟩]
theorem checked14542 : checkPrefixCuts (2^48) 1909981185 9 Manual.Count131072.C014542.packed 128 cuts14542 = true := by
 decide +kernel
def pointBounds14542 : List (Nat × Nat × Nat) := [(1910030336,95861827328391,95862205089001),(1910090752,95862245401125,95862623162020)]
theorem point_links_checked14542 : (cuts14542.take 2).map (fun c => (1909981185-1+2*2^9*c.k,95861494570087+c.lower,95861872330467+c.upper)) = pointBounds14542 := by
 decide +kernel
def cuts14543 : List PrefixCut := [⟨38,265540719,265540902⟩,
⟨97,690217940,690218411⟩,
⟨128,906529938,906530559⟩]
theorem checked14543 : checkPrefixCuts (2^48) 1910112257 9 Manual.Count131072.C014543.packed 128 cuts14543 = true := by
 decide +kernel
def pointBounds14543 : List (Nat × Nat × Nat) := [(1910151168,95862661839710,95863039600889),(1910211584,95863086516931,95863464278398)]
theorem point_links_checked14543 : (cuts14543.take 2).map (fun c => (1910112257-1+2*2^9*c.k,95862396298991+c.lower,95862774059987+c.upper)) = pointBounds14543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000141
