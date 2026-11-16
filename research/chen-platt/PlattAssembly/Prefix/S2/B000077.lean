import PlattAssemblyKernel
import PlattCertificates.Count131072.C012464
import PlattCertificates.Count131072.C012465
import PlattCertificates.Count131072.C012466
import PlattCertificates.Count131072.C012467
import PlattCertificates.Count131072.C012468
import PlattCertificates.Count131072.C012469
import PlattCertificates.Count131072.C012470
import PlattCertificates.Count131072.C012471
import PlattCertificates.Count131072.C012472
import PlattCertificates.Count131072.C012473
import PlattCertificates.Count131072.C012474
import PlattCertificates.Count131072.C012475
import PlattCertificates.Count131072.C012476
import PlattCertificates.Count131072.C012477
import PlattCertificates.Count131072.C012478
import PlattCertificates.Count131072.C012479
import PlattCertificates.Count131072.C012480
import PlattCertificates.Count131072.C012481
import PlattCertificates.Count131072.C012482
import PlattCertificates.Count131072.C012483
import PlattCertificates.Count131072.C012484
import PlattCertificates.Count131072.C012485
import PlattCertificates.Count131072.C012486
import PlattCertificates.Count131072.C012487
import PlattCertificates.Count131072.C012488
import PlattCertificates.Count131072.C012489
import PlattCertificates.Count131072.C012490
import PlattCertificates.Count131072.C012491
import PlattCertificates.Count131072.C012492
import PlattCertificates.Count131072.C012493
import PlattCertificates.Count131072.C012494
import PlattCertificates.Count131072.C012495
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12464 : List PrefixCut := [⟨6,49673549,49673588⟩,
⟨56,479883668,479884028⟩,
⟨106,899424288,899424961⟩,
⟨128,1076620782,1076621586⟩]
theorem checked12464 : checkPrefixCuts (2^48) 1637613569 9 Manual.Count131072.C012464.packed 128 cuts12464 = true := by
 decide +kernel
def pointBounds12464 : List (Nat × Nat × Nat) := [(1637619712,93827933902307,93828310217952),(1637670912,93828364112426,93828740428392),(1637722112,93828783653046,93829159969325)]
theorem point_links_checked12464 : (cuts12464.take 3).map (fun c => (1637613569-1+2*2^9*c.k,93827884228758+c.lower,93828260544364+c.upper)) = pointBounds12464 := by
 decide +kernel
def cuts12465 : List PrefixCut := [⟨28,235112518,235112692⟩,
⟨78,649127182,649127663⟩,
⟨128,1070690712,1070691506⟩]
theorem checked12465 : checkPrefixCuts (2^48) 1637744641 9 Manual.Count131072.C012465.packed 128 cuts12465 = true := by
 decide +kernel
def pointBounds12465 : List (Nat × Nat × Nat) := [(1637773312,93829195962058,93829572278642),(1637824512,93829609976722,93829986293613),(1637875712,93830031540252,93830407857456)]
theorem point_links_checked12465 : (cuts12465.take 3).map (fun c => (1637744641-1+2*2^9*c.k,93828960849540+c.lower,93829337165950+c.upper)) = pointBounds12465 := by
 decide +kernel
def cuts12466 : List PrefixCut := [⟨50,412270395,412270701⟩,
⟨100,828824034,828824651⟩,
⟨128,1055482842,1055483629⟩]
theorem checked12466 : checkPrefixCuts (2^48) 1637875713 9 Manual.Count131072.C012466.packed 128 cuts12466 = true := by
 decide +kernel
def pointBounds12466 : List (Nat × Nat × Nat) := [(1637926912,93830443810647,93830820128157),(1637978112,93830860364286,93831236682107)]
theorem point_links_checked12466 : (cuts12466.take 2).map (fun c => (1637875713-1+2*2^9*c.k,93830031540252+c.lower,93830407857456+c.upper)) = pointBounds12466 := by
 decide +kernel
def cuts12467 : List PrefixCut := [⟨22,184554749,184554887⟩,
⟨72,596271005,596271455⟩,
⟨122,1007287022,1007287778⟩,
⟨128,1054023813,1054024604⟩]
theorem checked12467 : checkPrefixCuts (2^48) 1638006785 9 Manual.Count131072.C012467.packed 128 cuts12467 = true := by
 decide +kernel
def pointBounds12467 : List (Nat × Nat × Nat) := [(1638029312,93831271577843,93831647895972),(1638080512,93831683294099,93832059612540),(1638131712,93832094310116,93832470628863)]
theorem point_links_checked12467 : (cuts12467.take 3).map (fun c => (1638006785-1+2*2^9*c.k,93831087023094+c.lower,93831463341085+c.upper)) = pointBounds12467 := by
 decide +kernel
def cuts12468 : List PrefixCut := [⟨44,365640914,365641186⟩,
⟨94,778864876,778865456⟩,
⟨128,1062186471,1062187262⟩]
theorem checked12468 : checkPrefixCuts (2^48) 1638137857 9 Manual.Count131072.C012468.packed 128 cuts12468 = true := by
 decide +kernel
def pointBounds12468 : List (Nat × Nat × Nat) := [(1638182912,93832506687821,93832883006875),(1638234112,93832919911783,93833296231145)]
theorem point_links_checked12468 : (cuts12468.take 2).map (fun c => (1638137857-1+2*2^9*c.k,93832141046907+c.lower,93832517365689+c.upper)) = pointBounds12468 := by
 decide +kernel
def cuts12469 : List PrefixCut := [⟨16,133841167,133841266⟩,
⟨66,547554672,547555082⟩,
⟨116,963660557,963661276⟩,
⟨128,1061414338,1061415130⟩]
theorem checked12469 : checkPrefixCuts (2^48) 1638268929 9 Manual.Count131072.C012469.packed 128 cuts12469 = true := by
 decide +kernel
def pointBounds12469 : List (Nat × Nat × Nat) := [(1638285312,93833337074545,93833713394217),(1638336512,93833750788050,93834127108033),(1638387712,93834166893935,93834543214227)]
theorem point_links_checked12469 : (cuts12469.take 3).map (fun c => (1638268929-1+2*2^9*c.k,93833203233378+c.lower,93833579552951+c.upper)) = pointBounds12469 := by
 decide +kernel
def cuts12470 : List PrefixCut := [⟨38,312154353,312154586⟩,
⟨89,730467440,730467985⟩,
⟨128,1057034495,1057035283⟩]
theorem checked12470 : checkPrefixCuts (2^48) 1638400001 9 Manual.Count131072.C012470.packed 128 cuts12470 = true := by
 decide +kernel
def pointBounds12470 : List (Nat × Nat × Nat) := [(1638438912,93834576802069,93834953122667),(1638491136,93834995115156,93835371436066)]
theorem point_links_checked12470 : (cuts12470.take 2).map (fun c => (1638400001-1+2*2^9*c.k,93834264647716+c.lower,93834640968081+c.upper)) = pointBounds12470 := by
 decide +kernel
def cuts12471 : List PrefixCut := [⟨12,99119501,99119576⟩,
⟨63,517921233,517921615⟩,
⟨114,938427441,938428136⟩,
⟨128,1051625117,1051625898⟩]
theorem checked12471 : checkPrefixCuts (2^48) 1638531073 9 Manual.Count131072.C012471.packed 128 cuts12471 = true := by
 decide +kernel
def pointBounds12471 : List (Nat × Nat × Nat) := [(1638543360,93835420801712,93835797122940),(1638595584,93835839603444,93836215924979),(1638647808,93836260109652,93836636431500)]
theorem point_links_checked12471 : (cuts12471.take 3).map (fun c => (1638531073-1+2*2^9*c.k,93835321682211+c.lower,93835698003364+c.upper)) = pointBounds12471 := by
 decide +kernel
def cuts12472 : List PrefixCut := [⟨37,305233867,305234095⟩,
⟨88,726572009,726572554⟩,
⟨128,1052915171,1052915959⟩]
theorem checked12472 : checkPrefixCuts (2^48) 1638662145 9 Manual.Count131072.C012472.packed 128 cuts12472 = true := by
 decide +kernel
def pointBounds12472 : List (Nat × Nat × Nat) := [(1638700032,93836678541195,93837054863357),(1638752256,93837099879337,93837476201816)]
theorem point_links_checked12472 : (cuts12472.take 2).map (fun c => (1638662145-1+2*2^9*c.k,93836373307328+c.lower,93836749629262+c.upper)) = pointBounds12472 := by
 decide +kernel
def cuts12473 : List PrefixCut := [⟨11,95153285,95153354⟩,
⟨62,514747054,514747436⟩,
⟨113,932438268,932438961⟩,
⟨128,1055579054,1055579842⟩]
theorem checked12473 : checkPrefixCuts (2^48) 1638793217 9 Manual.Count131072.C012473.packed 128 cuts12473 = true := by
 decide +kernel
def pointBounds12473 : List (Nat × Nat × Nat) := [(1638804480,93837521375784,93837897698575),(1638856704,93837940969553,93838317292657),(1638908928,93838358660767,93838734984182)]
theorem point_links_checked12473 : (cuts12473.take 3).map (fun c => (1638793217-1+2*2^9*c.k,93837426222499+c.lower,93837802545221+c.upper)) = pointBounds12473 := by
 decide +kernel
def cuts12474 : List PrefixCut := [⟨36,306043798,306044025⟩,
⟨87,730234394,730234935⟩,
⟨128,1072839986,1072840790⟩]
theorem checked12474 : checkPrefixCuts (2^48) 1638924289 9 Manual.Count131072.C012474.packed 128 cuts12474 = true := by
 decide +kernel
def pointBounds12474 : List (Nat × Nat × Nat) := [(1638961152,93838787845351,93839164169088),(1639013376,93839212035947,93839588359998)]
theorem point_links_checked12474 : (cuts12474.take 2).map (fun c => (1638924289-1+2*2^9*c.k,93838481801553+c.lower,93838858125063+c.upper)) = pointBounds12474 := by
 decide +kernel
def cuts12475 : List PrefixCut := [⟨10,80541082,80541141⟩,
⟨61,512432391,512432774⟩,
⟨112,929713600,929714293⟩,
⟨128,1058157973,1058158760⟩]
theorem checked12475 : checkPrefixCuts (2^48) 1639055361 9 Manual.Count131072.C012475.packed 128 cuts12475 = true := by
 decide +kernel
def pointBounds12475 : List (Nat × Nat × Nat) := [(1639065600,93839635182621,93840011506994),(1639117824,93840067073930,93840443398627),(1639170048,93840484355139,93840860680146)]
theorem point_links_checked12475 : (cuts12475.take 3).map (fun c => (1639055361-1+2*2^9*c.k,93839554641539+c.lower,93839930965853+c.upper)) = pointBounds12475 := by
 decide +kernel
def cuts12476 : List PrefixCut := [⟨35,288308350,288308565⟩,
⟨86,715865586,715866120⟩,
⟨128,1067345116,1067345910⟩]
theorem checked12476 : checkPrefixCuts (2^48) 1639186433 9 Manual.Count131072.C012476.packed 128 cuts12476 = true := by
 decide +kernel
def pointBounds12476 : List (Nat × Nat × Nat) := [(1639222272,93840901107862,93841277433178),(1639274496,93841328665098,93841704990733)]
theorem point_links_checked12476 : (cuts12476.take 2).map (fun c => (1639186433-1+2*2^9*c.k,93840612799512+c.lower,93840989124613+c.upper)) = pointBounds12476 := by
 decide +kernel
def cuts12477 : List PrefixCut := [⟨9,75892288,75892344⟩,
⟨60,486424052,486424418⟩,
⟨111,904497266,904497945⟩,
⟨128,1045797862,1045798645⟩]
theorem checked12477 : checkPrefixCuts (2^48) 1639317505 9 Manual.Count131072.C012477.packed 128 cuts12477 = true := by
 decide +kernel
def pointBounds12477 : List (Nat × Nat × Nat) := [(1639326720,93841756036916,93842132362867),(1639378944,93842166568680,93842542894941),(1639431168,93842584641894,93842960968468)]
theorem point_links_checked12477 : (cuts12477.take 3).map (fun c => (1639317505-1+2*2^9*c.k,93841680144628+c.lower,93842056470523+c.upper)) = pointBounds12477 := by
 decide +kernel
def cuts12478 : List PrefixCut := [⟨34,281909947,281910158⟩,
⟨85,709742382,709742911⟩,
⟨128,1068376350,1068377148⟩]
theorem checked12478 : checkPrefixCuts (2^48) 1639448577 9 Manual.Count131072.C012478.packed 128 cuts12478 = true := by
 decide +kernel
def pointBounds12478 : List (Nat × Nat × Nat) := [(1639483392,93843007852437,93843384179326),(1639535616,93843435684872,93843812012079)]
theorem point_links_checked12478 : (cuts12478.take 2).map (fun c => (1639448577-1+2*2^9*c.k,93842725942490+c.lower,93843102269168+c.upper)) = pointBounds12478 := by
 decide +kernel
def cuts12479 : List PrefixCut := [⟨8,67983137,67983186⟩,
⟨59,494929979,494930348⟩,
⟨110,914996679,914997361⟩,
⟨128,1057648027,1057648812⟩]
theorem checked12479 : checkPrefixCuts (2^48) 1639579649 9 Manual.Count131072.C012479.packed 128 cuts12479 = true := by
 decide +kernel
def pointBounds12479 : List (Nat × Nat × Nat) := [(1639587840,93843862301977,93844238629502),(1639640064,93844289248819,93844665576664),(1639692288,93844709315519,93845085643677)]
theorem point_links_checked12479 : (cuts12479.take 3).map (fun c => (1639579649-1+2*2^9*c.k,93843794318840+c.lower,93844170646316+c.upper)) = pointBounds12479 := by
 decide +kernel
def cuts12480 : List PrefixCut := [⟨33,271050417,271050618⟩,
⟨84,691605188,691605705⟩,
⟨128,1057734452,1057735243⟩]
theorem checked12480 : checkPrefixCuts (2^48) 1639710721 9 Manual.Count131072.C012480.packed 128 cuts12480 = true := by
 decide +kernel
def pointBounds12480 : List (Nat × Nat × Nat) := [(1639744512,93845123017284,93845499345746),(1639796736,93845543572055,93845919900833)]
theorem point_links_checked12480 : (cuts12480.take 2).map (fun c => (1639710721-1+2*2^9*c.k,93844851966867+c.lower,93845228295128+c.upper)) = pointBounds12480 := by
 decide +kernel
def cuts12481 : List PrefixCut := [⟨7,57330170,57330211⟩,
⟨58,486268666,486269029⟩,
⟨109,915193628,915194306⟩,
⟨128,1071896249,1071897042⟩]
theorem checked12481 : checkPrefixCuts (2^48) 1639841793 9 Manual.Count131072.C012481.packed 128 cuts12481 = true := by
 decide +kernel
def pointBounds12481 : List (Nat × Nat × Nat) := [(1639848960,93845967031489,93846343360582),(1639901184,93846395969985,93846772299400),(1639953408,93846824894947,93847201224677)]
theorem point_links_checked12481 : (cuts12481.take 3).map (fun c => (1639841793-1+2*2^9*c.k,93845909701319+c.lower,93846286030371+c.upper)) = pointBounds12481 := by
 decide +kernel
def cuts12482 : List PrefixCut := [⟨32,260709262,260709455⟩,
⟨83,687890647,687891155⟩,
⟨128,1053789909,1053790688⟩]
theorem checked12482 : checkPrefixCuts (2^48) 1639972865 9 Manual.Count131072.C012482.packed 128 cuts12482 = true := by
 decide +kernel
def pointBounds12482 : List (Nat × Nat × Nat) := [(1640005632,93847242306830,93847618636868),(1640057856,93847669488215,93848045818568)]
theorem point_links_checked12482 : (cuts12482.take 2).map (fun c => (1639972865-1+2*2^9*c.k,93846981597568+c.lower,93847357927413+c.upper)) = pointBounds12482 := by
 decide +kernel
def cuts12483 : List PrefixCut := [⟨6,48396790,48396828⟩,
⟨57,468857824,468858182⟩,
⟨108,894453955,894454634⟩,
⟨128,1062457693,1062458495⟩]
theorem checked12483 : checkPrefixCuts (2^48) 1640103937 9 Manual.Count131072.C012483.packed 128 cuts12483 = true := by
 decide +kernel
def pointBounds12483 : List (Nat × Nat × Nat) := [(1640110080,93848083784267,93848460114929),(1640162304,93848504245301,93848880576283),(1640214528,93848929841432,93849306172735)]
theorem point_links_checked12483 : (cuts12483.take 3).map (fun c => (1640103937-1+2*2^9*c.k,93848035387477+c.lower,93848411718101+c.upper)) = pointBounds12483 := by
 decide +kernel
def cuts12484 : List PrefixCut := [⟨31,244708394,244708578⟩,
⟨82,674395768,674396277⟩,
⟨128,1068378378,1068379175⟩]
theorem checked12484 : checkPrefixCuts (2^48) 1640235009 9 Manual.Count131072.C012484.packed 128 cuts12484 = true := by
 decide +kernel
def pointBounds12484 : List (Nat × Nat × Nat) := [(1640266752,93849342553564,93849718885174),(1640318976,93849772240938,93850148572873)]
theorem point_links_checked12484 : (cuts12484.take 2).map (fun c => (1640235009-1+2*2^9*c.k,93849097845170+c.lower,93849474176596+c.upper)) = pointBounds12484 := by
 decide +kernel
def cuts12485 : List PrefixCut := [⟨5,42040153,42040183⟩,
⟨56,467753593,467753937⟩,
⟨107,882128821,882129482⟩,
⟨128,1062287976,1062288769⟩]
theorem checked12485 : checkPrefixCuts (2^48) 1640366081 9 Manual.Count131072.C012485.packed 128 cuts12485 = true := by
 decide +kernel
def pointBounds12485 : List (Nat × Nat × Nat) := [(1640371200,93850208263701,93850584595954),(1640423424,93850633977141,93851010309708),(1640475648,93851048352369,93851424685253)]
theorem point_links_checked12485 : (cuts12485.take 3).map (fun c => (1640366081-1+2*2^9*c.k,93850166223548+c.lower,93850542555771+c.upper)) = pointBounds12485 := by
 decide +kernel
def cuts12486 : List PrefixCut := [⟨30,246385142,246385324⟩,
⟨81,680121838,680122342⟩,
⟨128,1061860284,1061861075⟩]
theorem checked12486 : checkPrefixCuts (2^48) 1640497153 9 Manual.Count131072.C012486.packed 128 cuts12486 = true := by
 decide +kernel
def pointBounds12486 : List (Nat × Nat × Nat) := [(1640527872,93851474896666,93851851229864),(1640580096,93851908633362,93852284966882)]
theorem point_links_checked12486 : (cuts12486.take 2).map (fun c => (1640497153-1+2*2^9*c.k,93851228511524+c.lower,93851604844540+c.upper)) = pointBounds12486 := by
 decide +kernel
def cuts12487 : List PrefixCut := [⟨4,31053283,31053305⟩,
⟨55,450008017,450008352⟩,
⟨106,874610854,874611508⟩,
⟨128,1057314549,1057315341⟩]
theorem checked12487 : checkPrefixCuts (2^48) 1640628225 9 Manual.Count131072.C012487.packed 128 cuts12487 = true := by
 decide +kernel
def pointBounds12487 : List (Nat × Nat × Nat) := [(1640632320,93852321425091,93852697758920),(1640684544,93852740379825,93853116713967),(1640736768,93853164982662,93853541317123)]
theorem point_links_checked12487 : (cuts12487.take 3).map (fun c => (1640628225-1+2*2^9*c.k,93852290371808+c.lower,93852666705615+c.upper)) = pointBounds12487 := by
 decide +kernel
def cuts12488 : List PrefixCut := [⟨29,242228670,242228850⟩,
⟨80,669034439,669034938⟩,
⟨128,1064092104,1064092894⟩]
theorem checked12488 : checkPrefixCuts (2^48) 1640759297 9 Manual.Count131072.C012488.packed 128 cuts12488 = true := by
 decide +kernel
def pointBounds12488 : List (Nat × Nat × Nat) := [(1640788992,93853589915027,93853966249806),(1640841216,93854016720796,93854393055894)]
theorem point_links_checked12488 : (cuts12488.take 2).map (fun c => (1640759297-1+2*2^9*c.k,93853347686357+c.lower,93853724020956+c.upper)) = pointBounds12488 := by
 decide +kernel
def cuts12489 : List PrefixCut := [⟨3,24015280,24015299⟩,
⟨54,449250178,449250514⟩,
⟨105,875157643,875158294⟩,
⟨128,1069667488,1069668284⟩]
theorem checked12489 : checkPrefixCuts (2^48) 1640890369 9 Manual.Count131072.C012489.packed 128 cuts12489 = true := by
 decide +kernel
def pointBounds12489 : List (Nat × Nat × Nat) := [(1640893440,93854435793741,93854812129149),(1640945664,93854861028639,93855237364364),(1640997888,93855286936104,93855663272144)]
theorem point_links_checked12489 : (cuts12489.take 3).map (fun c => (1640890369-1+2*2^9*c.k,93854411778461+c.lower,93854788113850+c.upper)) = pointBounds12489 := by
 decide +kernel
def cuts12490 : List PrefixCut := [⟨28,242876109,242876290⟩,
⟨79,659322900,659323386⟩,
⟨128,1068038663,1068039451⟩]
theorem checked12490 : checkPrefixCuts (2^48) 1641021441 9 Manual.Count131072.C012490.packed 128 cuts12490 = true := by
 decide +kernel
def pointBounds12490 : List (Nat × Nat × Nat) := [(1641050112,93855724322058,93856100658424),(1641102336,93856140768849,93856517105520)]
theorem point_links_checked12490 : (cuts12490.take 2).map (fun c => (1641021441-1+2*2^9*c.k,93855481445949+c.lower,93855857782134+c.upper)) = pointBounds12490 := by
 decide +kernel
def cuts12491 : List PrefixCut := [⟨2,16293487,16293499⟩,
⟨53,444376381,444376712⟩,
⟨104,860097471,860098109⟩,
⟨128,1055433784,1055434567⟩]
theorem checked12491 : checkPrefixCuts (2^48) 1641152513 9 Manual.Count131072.C012491.packed 128 cuts12491 = true := by
 decide +kernel
def pointBounds12491 : List (Nat × Nat × Nat) := [(1641154560,93856565778099,93856942115084),(1641206784,93856993860993,93857370198297),(1641259008,93857409582083,93857785919694)]
theorem point_links_checked12491 : (cuts12491.take 3).map (fun c => (1641152513-1+2*2^9*c.k,93856549484612+c.lower,93856925821585+c.upper)) = pointBounds12491 := by
 decide +kernel
def cuts12492 : List PrefixCut := [⟨27,217113091,217113258⟩,
⟨78,637437941,637438425⟩,
⟨128,1055691775,1055692569⟩]
theorem checked12492 : checkPrefixCuts (2^48) 1641283585 9 Manual.Count131072.C012492.packed 128 cuts12492 = true := by
 decide +kernel
def pointBounds12492 : List (Nat × Nat × Nat) := [(1641311232,93857822031487,93858198369410),(1641363456,93858242356337,93858618694577)]
theorem point_links_checked12492 : (cuts12492.take 2).map (fun c => (1641283585-1+2*2^9*c.k,93857604918396+c.lower,93857981256152+c.upper)) = pointBounds12492 := by
 decide +kernel
def cuts12493 : List PrefixCut := [⟨1,8574152,8574159⟩,
⟨52,422699010,422699328⟩,
⟨103,850871529,850872164⟩,
⟨128,1056979357,1056980143⟩]
theorem checked12493 : checkPrefixCuts (2^48) 1641414657 9 Manual.Count131072.C012493.packed 128 cuts12493 = true := by
 decide +kernel
def pointBounds12493 : List (Nat × Nat × Nat) := [(1641415680,93858669184323,93859045522880),(1641467904,93859083309181,93859459648049),(1641520128,93859511481700,93859887820885)]
theorem point_links_checked12493 : (cuts12493.take 3).map (fun c => (1641414657-1+2*2^9*c.k,93858660610171+c.lower,93859036948721+c.upper)) = pointBounds12493 := by
 decide +kernel
def cuts12494 : List PrefixCut := [⟨26,209533888,209534041⟩,
⟨77,623962114,623962573⟩,
⟨128,1054665730,1054666510⟩]
theorem checked12494 : checkPrefixCuts (2^48) 1641545729 9 Manual.Count131072.C012494.packed 128 cuts12494 = true := by
 decide +kernel
def pointBounds12494 : List (Nat × Nat × Nat) := [(1641572352,93859927123416,93860303462905),(1641624576,93860341551642,93860717891437),(1641676800,93860772255258,93861148595374)]
theorem point_links_checked12494 : (cuts12494.take 3).map (fun c => (1641545729-1+2*2^9*c.k,93859717589528+c.lower,93860093928864+c.upper)) = pointBounds12494 := by
 decide +kernel
def cuts12495 : List PrefixCut := [⟨51,422974575,422974888⟩,
⟨102,841135195,841135818⟩,
⟨128,1055782361,1055783143⟩]
theorem checked12495 : checkPrefixCuts (2^48) 1641676801 9 Manual.Count131072.C012495.packed 128 cuts12495 = true := by
 decide +kernel
def pointBounds12495 : List (Nat × Nat × Nat) := [(1641729024,93861195229833,93861571570262),(1641781248,93861613390453,93861989731192)]
theorem point_links_checked12495 : (cuts12495.take 2).map (fun c => (1641676801-1+2*2^9*c.k,93860772255258+c.lower,93861148595374+c.upper)) = pointBounds12495 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000077
