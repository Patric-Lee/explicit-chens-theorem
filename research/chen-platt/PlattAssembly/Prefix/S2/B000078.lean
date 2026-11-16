import PlattAssemblyKernel
import PlattCertificates.Count131072.C012496
import PlattCertificates.Count131072.C012497
import PlattCertificates.Count131072.C012498
import PlattCertificates.Count131072.C012499
import PlattCertificates.Count131072.C012500
import PlattCertificates.Count131072.C012501
import PlattCertificates.Count131072.C012502
import PlattCertificates.Count131072.C012503
import PlattCertificates.Count131072.C012504
import PlattCertificates.Count131072.C012505
import PlattCertificates.Count131072.C012506
import PlattCertificates.Count131072.C012507
import PlattCertificates.Count131072.C012508
import PlattCertificates.Count131072.C012509
import PlattCertificates.Count131072.C012510
import PlattCertificates.Count131072.C012511
import PlattCertificates.Count131072.C012512
import PlattCertificates.Count131072.C012513
import PlattCertificates.Count131072.C012514
import PlattCertificates.Count131072.C012515
import PlattCertificates.Count131072.C012516
import PlattCertificates.Count131072.C012517
import PlattCertificates.Count131072.C012518
import PlattCertificates.Count131072.C012519
import PlattCertificates.Count131072.C012520
import PlattCertificates.Count131072.C012521
import PlattCertificates.Count131072.C012522
import PlattCertificates.Count131072.C012523
import PlattCertificates.Count131072.C012524
import PlattCertificates.Count131072.C012525
import PlattCertificates.Count131072.C012526
import PlattCertificates.Count131072.C012527
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000078
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12496 : List PrefixCut := [⟨25,207100358,207100511⟩,
⟨76,630205860,630206329⟩,
⟨127,1055355100,1055355886⟩,
⟨128,1063926520,1063927312⟩]
theorem checked12496 : checkPrefixCuts (2^48) 1641807873 9 Manual.Count131072.C012496.packed 128 cuts12496 = true := by
 decide +kernel
def pointBounds12496 : List (Nat × Nat × Nat) := [(1641833472,93862035137977,93862411479028),(1641885696,93862458243479,93862834584846),(1641937920,93862883392719,93863259734403)]
theorem point_links_checked12496 : (cuts12496.take 3).map (fun c => (1641807873-1+2*2^9*c.k,93861828037619+c.lower,93862204378517+c.upper)) = pointBounds12496 := by
 decide +kernel
def cuts12497 : List PrefixCut := [⟨50,415021547,415021856⟩,
⟨101,835001250,835001869⟩,
⟨128,1053042525,1053043304⟩]
theorem checked12497 : checkPrefixCuts (2^48) 1641938945 9 Manual.Count131072.C012497.packed 128 cuts12497 = true := by
 decide +kernel
def pointBounds12497 : List (Nat × Nat × Nat) := [(1641990144,93863306985686,93863683327685),(1642042368,93863726965389,93864103307698)]
theorem point_links_checked12497 : (cuts12497.take 2).map (fun c => (1641938945-1+2*2^9*c.k,93862891964139+c.lower,93863268305829+c.upper)) = pointBounds12497 := by
 decide +kernel
def cuts12498 : List PrefixCut := [⟨24,207924388,207924541⟩,
⟨75,627534434,627534903⟩,
⟨126,1045074293,1045075073⟩,
⟨128,1060157588,1060158379⟩]
theorem checked12498 : checkPrefixCuts (2^48) 1642070017 9 Manual.Count131072.C012498.packed 128 cuts12498 = true := by
 decide +kernel
def pointBounds12498 : List (Nat × Nat × Nat) := [(1642094592,93864152931052,93864529273674),(1642146816,93864572541098,93864948884036),(1642199040,93864990080957,93865366424206)]
theorem point_links_checked12498 : (cuts12498.take 3).map (fun c => (1642070017-1+2*2^9*c.k,93863945006664+c.lower,93864321349133+c.upper)) = pointBounds12498 := by
 decide +kernel
def cuts12499 : List PrefixCut := [⟨49,402272052,402272353⟩,
⟨100,824927218,824927833⟩,
⟨128,1062129294,1062130087⟩]
theorem checked12499 : checkPrefixCuts (2^48) 1642201089 9 Manual.Count131072.C012499.packed 128 cuts12499 = true := by
 decide +kernel
def pointBounds12499 : List (Nat × Nat × Nat) := [(1642251264,93865407436304,93865783779865),(1642303488,93865830091470,93866206435345)]
theorem point_links_checked12499 : (cuts12499.take 2).map (fun c => (1642201089-1+2*2^9*c.k,93865005164252+c.lower,93865381507512+c.upper)) = pointBounds12499 := by
 decide +kernel
def cuts12500 : List PrefixCut := [⟨23,189895763,189895906⟩,
⟨74,609781946,609782403⟩,
⟨125,1035652906,1035653683⟩,
⟨128,1058788367,1058789161⟩]
theorem checked12500 : checkPrefixCuts (2^48) 1642332161 9 Manual.Count131072.C012500.packed 128 cuts12500 = true := by
 decide +kernel
def pointBounds12500 : List (Nat × Nat × Nat) := [(1642355712,93866257189309,93866633533505),(1642407936,93866677075492,93867053420002),(1642460160,93867102946452,93867479291282)]
theorem point_links_checked12500 : (cuts12500.take 3).map (fun c => (1642332161-1+2*2^9*c.k,93866067293546+c.lower,93866443637599+c.upper)) = pointBounds12500 := by
 decide +kernel
def cuts12501 : List PrefixCut := [⟨48,401008311,401008612⟩,
⟨99,817427021,817427640⟩,
⟨128,1059389436,1059390233⟩]
theorem checked12501 : checkPrefixCuts (2^48) 1642463233 9 Manual.Count131072.C012501.packed 128 cuts12501 = true := by
 decide +kernel
def pointBounds12501 : List (Nat × Nat × Nat) := [(1642512384,93867527090224,93867903435372),(1642564608,93867943508934,93868319854400)]
theorem point_links_checked12501 : (cuts12501.take 2).map (fun c => (1642463233-1+2*2^9*c.k,93867126081913+c.lower,93867502426760+c.upper)) = pointBounds12501 := by
 decide +kernel
def cuts12502 : List PrefixCut := [⟨22,184724740,184724878⟩,
⟨73,610370250,610370705⟩,
⟨124,1026235231,1026236000⟩,
⟨128,1059476448,1059477243⟩]
theorem checked12502 : checkPrefixCuts (2^48) 1642594305 9 Manual.Count131072.C012502.packed 128 cuts12502 = true := by
 decide +kernel
def pointBounds12502 : List (Nat × Nat × Nat) := [(1642616832,93868370196089,93868746541871),(1642669056,93868795841599,93869172187698),(1642721280,93869211706580,93869588052993)]
theorem point_links_checked12502 : (cuts12502.take 3).map (fun c => (1642594305-1+2*2^9*c.k,93868185471349+c.lower,93868561816993+c.upper)) = pointBounds12502 := by
 decide +kernel
def cuts12503 : List PrefixCut := [⟨47,395461406,395461702⟩,
⟨98,817125545,817126155⟩,
⟨128,1067444784,1067445580⟩]
theorem checked12503 : checkPrefixCuts (2^48) 1642725377 9 Manual.Count131072.C012503.packed 128 cuts12503 = true := by
 decide +kernel
def pointBounds12503 : List (Nat × Nat × Nat) := [(1642773504,93869640409203,93870016755938),(1642825728,93870062073342,93870438420391)]
theorem point_links_checked12503 : (cuts12503.take 2).map (fun c => (1642725377-1+2*2^9*c.k,93869244947797+c.lower,93869621294236+c.upper)) = pointBounds12503 := by
 decide +kernel
def cuts12504 : List PrefixCut := [⟨21,169960868,169960996⟩,
⟨72,592454740,592455184⟩,
⟨123,1004313152,1004313899⟩,
⟨128,1044744484,1044745262⟩]
theorem checked12504 : checkPrefixCuts (2^48) 1642856449 9 Manual.Count131072.C012504.packed 128 cuts12504 = true := by
 decide +kernel
def pointBounds12504 : List (Nat × Nat × Nat) := [(1642877952,93870482353449,93870858700812),(1642930176,93870904847321,93871281195000),(1642982400,93871316705733,93871693053715)]
theorem point_links_checked12504 : (cuts12504.take 3).map (fun c => (1642856449-1+2*2^9*c.k,93870312392581+c.lower,93870688739816+c.upper)) = pointBounds12504 := by
 decide +kernel
def cuts12505 : List PrefixCut := [⟨46,377581539,377581820⟩,
⟨97,790441762,790442354⟩,
⟨128,1049457813,1049458593⟩]
theorem checked12505 : checkPrefixCuts (2^48) 1642987521 9 Manual.Count131072.C012505.packed 128 cuts12505 = true := by
 decide +kernel
def pointBounds12505 : List (Nat × Nat × Nat) := [(1643034624,93871734718604,93872111066898),(1643086848,93872147578827,93872523927432)]
theorem point_links_checked12505 : (cuts12505.take 2).map (fun c => (1642987521-1+2*2^9*c.k,93871357137065+c.lower,93871733485078+c.upper)) = pointBounds12505 := by
 decide +kernel
def cuts12506 : List PrefixCut := [⟨20,161025939,161026062⟩,
⟨71,578313735,578314170⟩,
⟨122,1001926196,1001926945⟩,
⟨128,1052628610,1052629396⟩]
theorem checked12506 : checkPrefixCuts (2^48) 1643118593 9 Manual.Count131072.C012506.packed 128 cuts12506 = true := by
 decide +kernel
def pointBounds12506 : List (Nat × Nat × Nat) := [(1643139072,93872567620817,93872943969733),(1643191296,93872984908613,93873361257841),(1643243520,93873408521074,93873784870616)]
theorem point_links_checked12506 : (cuts12506.take 3).map (fun c => (1643118593-1+2*2^9*c.k,93872406594878+c.lower,93872782943671+c.upper)) = pointBounds12506 := by
 decide +kernel
def cuts12507 : List PrefixCut := [⟨45,375465903,375466185⟩,
⟨96,797509893,797510493⟩,
⟨128,1064192325,1064193126⟩]
theorem checked12507 : checkPrefixCuts (2^48) 1643249665 9 Manual.Count131072.C012507.packed 128 cuts12507 = true := by
 decide +kernel
def pointBounds12507 : List (Nat × Nat × Nat) := [(1643295744,93873834689391,93874211039252),(1643347968,93874256733381,93874633083560)]
theorem point_links_checked12507 : (cuts12507.take 2).map (fun c => (1643249665-1+2*2^9*c.k,93873459223488+c.lower,93873835573067+c.upper)) = pointBounds12507 := by
 decide +kernel
def cuts12508 : List PrefixCut := [⟨19,155176921,155177038⟩,
⟨70,579078061,579078491⟩,
⟨121,1005706048,1005706793⟩,
⟨128,1063250972,1063251760⟩]
theorem checked12508 : checkPrefixCuts (2^48) 1643380737 9 Manual.Count131072.C012508.packed 128 cuts12508 = true := by
 decide +kernel
def pointBounds12508 : List (Nat × Nat × Nat) := [(1643400192,93874678592734,93875054943231),(1643452416,93875102493874,93875478844684),(1643504640,93875529121861,93875905472986)]
theorem point_links_checked12508 : (cuts12508.take 3).map (fun c => (1643380737-1+2*2^9*c.k,93874523415813+c.lower,93874899766193+c.upper)) = pointBounds12508 := by
 decide +kernel
def cuts12509 : List PrefixCut := [⟨44,358793717,358793984⟩,
⟨95,775119048,775119625⟩,
⟨128,1047067827,1047068600⟩]
theorem checked12509 : checkPrefixCuts (2^48) 1643511809 9 Manual.Count131072.C012509.packed 128 cuts12509 = true := by
 decide +kernel
def pointBounds12509 : List (Nat × Nat × Nat) := [(1643556864,93875945460502,93876321811937),(1643609088,93876361785833,93876738137578)]
theorem point_links_checked12509 : (cuts12509.take 2).map (fun c => (1643511809-1+2*2^9*c.k,93875586666785+c.lower,93875963017953+c.upper)) = pointBounds12509 := by
 decide +kernel
def cuts12510 : List PrefixCut := [⟨18,146247224,146247335⟩,
⟨69,565457324,565457748⟩,
⟨120,986537824,986538564⟩,
⟨128,1054347834,1054348624⟩]
theorem checked12510 : checkPrefixCuts (2^48) 1643642881 9 Manual.Count131072.C012510.packed 128 cuts12510 = true := by
 decide +kernel
def pointBounds12510 : List (Nat × Nat × Nat) := [(1643661312,93876779981836,93877156333888),(1643713536,93877199191936,93877575544301),(1643765760,93877620272436,93877996625117)]
theorem point_links_checked12510 : (cuts12510.take 3).map (fun c => (1643642881-1+2*2^9*c.k,93876633734612+c.lower,93877010086553+c.upper)) = pointBounds12510 := by
 decide +kernel
def cuts12511 : List PrefixCut := [⟨43,356168126,356168391⟩,
⟨94,784584758,784585340⟩,
⟨128,1070017038,1070017833⟩]
theorem checked12511 : checkPrefixCuts (2^48) 1643773953 9 Manual.Count131072.C012511.packed 128 cuts12511 = true := by
 decide +kernel
def pointBounds12511 : List (Nat × Nat × Nat) := [(1643817984,93878044250572,93878420603568),(1643870208,93878472667204,93878849020517)]
theorem point_links_checked12511 : (cuts12511.take 2).map (fun c => (1643773953-1+2*2^9*c.k,93877688082446+c.lower,93878064435177+c.upper)) = pointBounds12511 := by
 decide +kernel
def cuts12512 : List PrefixCut := [⟨17,136635467,136635569⟩,
⟨68,553895675,553896084⟩,
⟨119,975080548,975081268⟩,
⟨128,1044934292,1044935065⟩]
theorem checked12512 : checkPrefixCuts (2^48) 1643905025 9 Manual.Count131072.C012512.packed 128 cuts12512 = true := by
 decide +kernel
def pointBounds12512 : List (Nat × Nat × Nat) := [(1643922432,93878894734951,93879271088579),(1643974656,93879311995159,93879688349094),(1644026880,93879733180032,93880109534278)]
theorem point_links_checked12512 : (cuts12512.take 3).map (fun c => (1643905025-1+2*2^9*c.k,93878758099484+c.lower,93879134453010+c.upper)) = pointBounds12512 := by
 decide +kernel
def cuts12513 : List PrefixCut := [⟨42,339333141,339333398⟩,
⟨93,756895931,756896502⟩,
⟨128,1041940405,1041941183⟩]
theorem checked12513 : checkPrefixCuts (2^48) 1644036097 9 Manual.Count131072.C012513.packed 128 cuts12513 = true := by
 decide +kernel
def pointBounds12513 : List (Nat × Nat × Nat) := [(1644079104,93880142366917,93880518721473),(1644131328,93880559929707,93880936284577)]
theorem point_links_checked12513 : (cuts12513.take 2).map (fun c => (1644036097-1+2*2^9*c.k,93879803033776+c.lower,93880179388075+c.upper)) = pointBounds12513 := by
 decide +kernel
def cuts12514 : List PrefixCut := [⟨16,129081169,129081263⟩,
⟨67,559285608,559286021⟩,
⟨118,982115357,982116083⟩,
⟨128,1062571319,1062572106⟩]
theorem checked12514 : checkPrefixCuts (2^48) 1644167169 9 Manual.Count131072.C012514.packed 128 cuts12514 = true := by
 decide +kernel
def pointBounds12514 : List (Nat × Nat × Nat) := [(1644183552,93880974055350,93881350410521),(1644235776,93881404259789,93881780615279),(1644288000,93881827089538,93882203445341)]
theorem point_links_checked12514 : (cuts12514.take 3).map (fun c => (1644167169-1+2*2^9*c.k,93880844974181+c.lower,93881221329258+c.upper)) = pointBounds12514 := by
 decide +kernel
def cuts12515 : List PrefixCut := [⟨41,336026734,336026981⟩,
⟨92,754379106,754379665⟩,
⟨128,1046738575,1046739356⟩]
theorem checked12515 : checkPrefixCuts (2^48) 1644298241 9 Manual.Count131072.C012515.packed 128 cuts12515 = true := by
 decide +kernel
def pointBounds12515 : List (Nat × Nat × Nat) := [(1644340224,93882243572234,93882619928345),(1644392448,93882661924606,93883038281029)]
theorem point_links_checked12515 : (cuts12515.take 2).map (fun c => (1644298241-1+2*2^9*c.k,93881907545500+c.lower,93882283901364+c.upper)) = pointBounds12515 := by
 decide +kernel
def cuts12516 : List PrefixCut := [⟨15,129402959,129403053⟩,
⟨66,550296223,550296631⟩,
⟨117,983499446,983500175⟩,
⟨128,1067365716,1067366507⟩]
theorem checked12516 : checkPrefixCuts (2^48) 1644429313 9 Manual.Count131072.C012516.packed 128 cuts12516 = true := by
 decide +kernel
def pointBounds12516 : List (Nat × Nat × Nat) := [(1644444672,93883083687034,93883460043773),(1644496896,93883504580298,93883880937351),(1644549120,93883937783521,93884314140895)]
theorem point_links_checked12516 : (cuts12516.take 3).map (fun c => (1644429313-1+2*2^9*c.k,93882954284075+c.lower,93883330640720+c.upper)) = pointBounds12516 := by
 decide +kernel
def cuts12517 : List PrefixCut := [⟨40,325875233,325875470⟩,
⟨91,736459520,736460065⟩,
⟨128,1043833166,1043833940⟩]
theorem checked12517 : checkPrefixCuts (2^48) 1644560385 9 Manual.Count131072.C012517.packed 128 cuts12517 = true := by
 decide +kernel
def pointBounds12517 : List (Nat × Nat × Nat) := [(1644601344,93884347525024,93884723882697),(1644653568,93884758109311,93885134467292)]
theorem point_links_checked12517 : (cuts12517.take 2).map (fun c => (1644560385-1+2*2^9*c.k,93884021649791+c.lower,93884398007227+c.upper)) = pointBounds12517 := by
 decide +kernel
def cuts12518 : List PrefixCut := [⟨14,120654203,120654293⟩,
⟨65,546957102,546957509⟩,
⟨116,955277586,955278296⟩,
⟨128,1051109518,1051110299⟩]
theorem checked12518 : checkPrefixCuts (2^48) 1644691457 9 Manual.Count131072.C012518.packed 128 cuts12518 = true := by
 decide +kernel
def pointBounds12518 : List (Nat × Nat × Nat) := [(1644705792,93885186137160,93885562495460),(1644758016,93885612440059,93885988798676),(1644810240,93886020760543,93886397119463)]
theorem point_links_checked12518 : (cuts12518.take 3).map (fun c => (1644691457-1+2*2^9*c.k,93885065482957+c.lower,93885441841167+c.upper)) = pointBounds12518 := by
 decide +kernel
def cuts12519 : List PrefixCut := [⟨39,317780473,317780709⟩,
⟨90,723850552,723851089⟩,
⟨128,1030490720,1030491488⟩]
theorem checked12519 : checkPrefixCuts (2^48) 1644822529 9 Manual.Count131072.C012519.packed 128 cuts12519 = true := by
 decide +kernel
def pointBounds12519 : List (Nat × Nat × Nat) := [(1644862464,93886434372948,93886810732175),(1644914688,93886840443027,93887216802555)]
theorem point_links_checked12519 : (cuts12519.take 2).map (fun c => (1644822529-1+2*2^9*c.k,93886116592475+c.lower,93886492951466+c.upper)) = pointBounds12519 := by
 decide +kernel
def cuts12520 : List PrefixCut := [⟨13,104379225,104379303⟩,
⟨64,535747668,535748069⟩,
⟨115,959060584,959061296⟩,
⟨128,1066341062,1066341855⟩]
theorem checked12520 : checkPrefixCuts (2^48) 1644953601 9 Manual.Count131072.C012520.packed 128 cuts12520 = true := by
 decide +kernel
def pointBounds12520 : List (Nat × Nat × Nat) := [(1644966912,93887251462420,93887627822257),(1645019136,93887682830863,93888059191023),(1645071360,93888106143779,93888482504250)]
theorem point_links_checked12520 : (cuts12520.take 3).map (fun c => (1644953601-1+2*2^9*c.k,93887147083195+c.lower,93887523442954+c.upper)) = pointBounds12520 := by
 decide +kernel
def cuts12521 : List PrefixCut := [⟨38,313965791,313966023⟩,
⟨89,739647000,739647551⟩,
⟨128,1061123237,1061124026⟩]
theorem checked12521 : checkPrefixCuts (2^48) 1645084673 9 Manual.Count131072.C012521.packed 128 cuts12521 = true := by
 decide +kernel
def pointBounds12521 : List (Nat × Nat × Nat) := [(1645123584,93888527390048,93888903750832),(1645175808,93888953071257,93889329432360)]
theorem point_links_checked12521 : (cuts12521.take 2).map (fun c => (1645084673-1+2*2^9*c.k,93888213424257+c.lower,93888589784809+c.upper)) = pointBounds12521 := by
 decide +kernel
def cuts12522 : List PrefixCut := [⟨12,102480675,102480751⟩,
⟨63,521975966,521976351⟩,
⟨114,945221629,945222329⟩,
⟨128,1059328003,1059328792⟩]
theorem checked12522 : checkPrefixCuts (2^48) 1645215745 9 Manual.Count131072.C012522.packed 128 cuts12522 = true := by
 decide +kernel
def pointBounds12522 : List (Nat × Nat × Nat) := [(1645228032,93889377028169,93889753389586),(1645280256,93889796523460,93890172885186),(1645332480,93890219769123,93890596131164)]
theorem point_links_checked12522 : (cuts12522.take 3).map (fun c => (1645215745-1+2*2^9*c.k,93889274547494+c.lower,93889650908835+c.upper)) = pointBounds12522 := by
 decide +kernel
def cuts12523 : List PrefixCut := [⟨37,308270478,308270711⟩,
⟨88,727041506,727042050⟩,
⟨128,1044018995,1044019774⟩]
theorem checked12523 : checkPrefixCuts (2^48) 1645346817 9 Manual.Count131072.C012523.packed 128 cuts12523 = true := by
 decide +kernel
def pointBounds12523 : List (Nat × Nat × Nat) := [(1645384704,93890642145975,93891018508338),(1645436928,93891060917003,93891437279677)]
theorem point_links_checked12523 : (cuts12523.take 2).map (fun c => (1645346817-1+2*2^9*c.k,93890333875497+c.lower,93890710237627+c.upper)) = pointBounds12523 := by
 decide +kernel
def cuts12524 : List PrefixCut := [⟨11,92371899,92371964⟩,
⟨62,522235088,522235467⟩,
⟨113,946439957,946440653⟩,
⟨128,1067199013,1067199800⟩]
theorem checked12524 : checkPrefixCuts (2^48) 1645477889 9 Manual.Count131072.C012524.packed 128 cuts12524 = true := by
 decide +kernel
def pointBounds12524 : List (Nat × Nat × Nat) := [(1645489152,93891470266391,93891846629365),(1645541376,93891900129580,93892276492868),(1645593600,93892324334449,93892700698054)]
theorem point_links_checked12524 : (cuts12524.take 3).map (fun c => (1645477889-1+2*2^9*c.k,93891377894492+c.lower,93891754257401+c.upper)) = pointBounds12524 := by
 decide +kernel
def cuts12525 : List PrefixCut := [⟨36,295906336,295906554⟩,
⟨87,728807281,728807821⟩,
⟨128,1061298539,1061299324⟩]
theorem checked12525 : checkPrefixCuts (2^48) 1645608961 9 Manual.Count131072.C012525.packed 128 cuts12525 = true := by
 decide +kernel
def pointBounds12525 : List (Nat × Nat × Nat) := [(1645645824,93892740999841,93893117363755),(1645698048,93893173900786,93893550265022)]
theorem point_links_checked12525 : (cuts12525.take 2).map (fun c => (1645608961-1+2*2^9*c.k,93892445093505+c.lower,93892821457201+c.upper)) = pointBounds12525 := by
 decide +kernel
def cuts12526 : List PrefixCut := [⟨10,79529822,79529882⟩,
⟨61,506246247,506246624⟩,
⟨112,927647478,927648163⟩,
⟨128,1056254237,1056255019⟩]
theorem checked12526 : checkPrefixCuts (2^48) 1645740033 9 Manual.Count131072.C012526.packed 128 cuts12526 = true := by
 decide +kernel
def pointBounds12526 : List (Nat × Nat × Nat) := [(1645750272,93893585921866,93893962286407),(1645802496,93894012638291,93894389003149),(1645854720,93894434039522,93894810404688)]
theorem point_links_checked12526 : (cuts12526.take 3).map (fun c => (1645740033-1+2*2^9*c.k,93893506392044+c.lower,93893882756525+c.upper)) = pointBounds12526 := by
 decide +kernel
def cuts12527 : List PrefixCut := [⟨35,287650415,287650626⟩,
⟨86,707656751,707657277⟩,
⟨128,1059932010,1059932796⟩]
theorem checked12527 : checkPrefixCuts (2^48) 1645871105 9 Manual.Count131072.C012527.packed 128 cuts12527 = true := by
 decide +kernel
def pointBounds12527 : List (Nat × Nat × Nat) := [(1645906944,93894850296696,93895226662170),(1645959168,93895270303032,93895646668821)]
theorem point_links_checked12527 : (cuts12527.take 2).map (fun c => (1645871105-1+2*2^9*c.k,93894562646281+c.lower,93894939011544+c.upper)) = pointBounds12527 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000078
