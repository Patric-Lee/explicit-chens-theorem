import PlattAssemblyKernel
import PlattCertificates.Count131072.C013616
import PlattCertificates.Count131072.C013617
import PlattCertificates.Count131072.C013618
import PlattCertificates.Count131072.C013619
import PlattCertificates.Count131072.C013620
import PlattCertificates.Count131072.C013621
import PlattCertificates.Count131072.C013622
import PlattCertificates.Count131072.C013623
import PlattCertificates.Count131072.C013624
import PlattCertificates.Count131072.C013625
import PlattCertificates.Count131072.C013626
import PlattCertificates.Count131072.C013627
import PlattCertificates.Count131072.C013628
import PlattCertificates.Count131072.C013629
import PlattCertificates.Count131072.C013630
import PlattCertificates.Count131072.C013631
import PlattCertificates.Count131072.C013632
import PlattCertificates.Count131072.C013633
import PlattCertificates.Count131072.C013634
import PlattCertificates.Count131072.C013635
import PlattCertificates.Count131072.C013636
import PlattCertificates.Count131072.C013637
import PlattCertificates.Count131072.C013638
import PlattCertificates.Count131072.C013639
import PlattCertificates.Count131072.C013640
import PlattCertificates.Count131072.C013641
import PlattCertificates.Count131072.C013642
import PlattCertificates.Count131072.C013643
import PlattCertificates.Count131072.C013644
import PlattCertificates.Count131072.C013645
import PlattCertificates.Count131072.C013646
import PlattCertificates.Count131072.C013647
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000113
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13616 : List PrefixCut := [⟨37,283736665,283736860⟩,
⟨92,694616825,694617313⟩,
⟨128,956622836,956623513⟩]
theorem checked13616 : checkPrefixCuts (2^48) 1788608513 9 Manual.Count131072.C013616.packed 128 cuts13616 = true := by
 decide +kernel
def pointBounds13616 : List (Nat × Nat × Nat) := [(1788646400,94995747235766,94996124397848),(1788702720,94996158115926,94996535278301)]
theorem point_links_checked13616 : (cuts13616.take 2).map (fun c => (1788608513-1+2*2^9*c.k,94995463499101+c.lower,94995840660988+c.upper)) = pointBounds13616 := by
 decide +kernel
def cuts13617 : List PrefixCut := [⟨19,145084534,145084633⟩,
⟨74,560502152,560502545⟩,
⟨128,968826041,968826720⟩]
theorem checked13617 : checkPrefixCuts (2^48) 1788739585 9 Manual.Count131072.C013617.packed 128 cuts13617 = true := by
 decide +kernel
def pointBounds13617 : List (Nat × Nat × Nat) := [(1788759040,94996565206471,94996942369134),(1788815360,94996980624089,94997357787046)]
theorem point_links_checked13617 : (cuts13617.take 2).map (fun c => (1788739585-1+2*2^9*c.k,94996420121937+c.lower,94996797284501+c.upper)) = pointBounds13617 := by
 decide +kernel
def cuts13618 : List PrefixCut := [⟨1,8182084,8182089⟩,
⟨56,422786798,422787096⟩,
⟨111,830770162,830770745⟩,
⟨128,957426488,957427161⟩]
theorem checked13618 : checkPrefixCuts (2^48) 1788870657 9 Manual.Count131072.C013618.packed 128 cuts13618 = true := by
 decide +kernel
def pointBounds13618 : List (Nat × Nat × Nat) := [(1788871680,94997397130062,94997774293310),(1788928000,94997811734776,94998188898317),(1788984320,94998219718140,94998596881966)]
theorem point_links_checked13618 : (cuts13618.take 3).map (fun c => (1788870657-1+2*2^9*c.k,94997388947978+c.lower,94997766111221+c.upper)) = pointBounds13618 := by
 decide +kernel
def cuts13619 : List PrefixCut := [⟨38,288866289,288866492⟩,
⟨93,711141024,711141527⟩,
⟨128,986462082,986462775⟩]
theorem checked13619 : checkPrefixCuts (2^48) 1789001729 9 Manual.Count131072.C013619.packed 128 cuts13619 = true := by
 decide +kernel
def pointBounds13619 : List (Nat × Nat × Nat) := [(1789040640,94998635240755,94999012404874),(1789096960,94999057515490,94999434679909)]
theorem point_links_checked13619 : (cuts13619.take 2).map (fun c => (1789001729-1+2*2^9*c.k,94998346374466+c.lower,94998723538382+c.upper)) = pointBounds13619 := by
 decide +kernel
def cuts13620 : List PrefixCut := [⟨20,151502884,151502989⟩,
⟨75,563053378,563053771⟩,
⟨128,966095991,966096670⟩]
theorem checked13620 : checkPrefixCuts (2^48) 1789132801 9 Manual.Count131072.C013620.packed 128 cuts13620 = true := by
 decide +kernel
def pointBounds13620 : List (Nat × Nat × Nat) := [(1789153280,94999484339432,94999861504146),(1789209600,94999895889926,95000273054928)]
theorem point_links_checked13620 : (cuts13620.take 2).map (fun c => (1789132801-1+2*2^9*c.k,94999332836548+c.lower,94999710001157+c.upper)) = pointBounds13620 := by
 decide +kernel
def cuts13621 : List PrefixCut := [⟨2,15731315,15731326⟩,
⟨57,436851692,436851996⟩,
⟨112,842542946,842543541⟩,
⟨128,961778190,961778871⟩]
theorem checked13621 : checkPrefixCuts (2^48) 1789263873 9 Manual.Count131072.C013621.packed 128 cuts13621 = true := by
 decide +kernel
def pointBounds13621 : List (Nat × Nat × Nat) := [(1789265920,95000314663854,95000691829153),(1789322240,95000735784231,95001112949823),(1789378560,95001141475485,95001518641368)]
theorem point_links_checked13621 : (cuts13621.take 3).map (fun c => (1789263873-1+2*2^9*c.k,95000298932539+c.lower,95000676097827+c.upper)) = pointBounds13621 := by
 decide +kernel
def cuts13622 : List PrefixCut := [⟨39,297926153,297926360⟩,
⟨94,710355513,710356008⟩,
⟨128,966426400,966427079⟩]
theorem checked13622 : checkPrefixCuts (2^48) 1789394945 9 Manual.Count131072.C013622.packed 128 cuts13622 = true := by
 decide +kernel
def pointBounds13622 : List (Nat × Nat × Nat) := [(1789434880,95001558636882,95001935803058),(1789491200,95001971066242,95002348232706)]
theorem point_links_checked13622 : (cuts13622.take 2).map (fun c => (1789394945-1+2*2^9*c.k,95001260710729+c.lower,95001637876698+c.upper)) = pointBounds13622 := by
 decide +kernel
def cuts13623 : List PrefixCut := [⟨21,159805867,159805977⟩,
⟨76,569220829,569221231⟩,
⟨128,962108814,962109496⟩]
theorem checked13623 : checkPrefixCuts (2^48) 1789526017 9 Manual.Count131072.C013623.packed 128 cuts13623 = true := by
 decide +kernel
def pointBounds13623 : List (Nat × Nat × Nat) := [(1789547520,95002386942996,95002764109754),(1789603840,95002796357958,95003173525008)]
theorem point_links_checked13623 : (cuts13623.take 2).map (fun c => (1789526017-1+2*2^9*c.k,95002227137129+c.lower,95002604303777+c.upper)) = pointBounds13623 := by
 decide +kernel
def cuts13624 : List PrefixCut := [⟨3,22648107,22648125⟩,
⟨58,452797631,452797947⟩,
⟨113,870981087,870981701⟩,
⟨128,986415683,986416376⟩]
theorem checked13624 : checkPrefixCuts (2^48) 1789657089 9 Manual.Count131072.C013624.packed 128 cuts13624 = true := by
 decide +kernel
def pointBounds13624 : List (Nat × Nat × Nat) := [(1789660160,95003211894050,95003589061398),(1789716480,95003642043574,95004019211220),(1789772800,95004060227030,95004437394974)]
theorem point_links_checked13624 : (cuts13624.take 3).map (fun c => (1789657089-1+2*2^9*c.k,95003189245943+c.lower,95003566413273+c.upper)) = pointBounds13624 := by
 decide +kernel
def cuts13625 : List PrefixCut := [⟨40,298332310,298332522⟩,
⟨95,718691111,718691618⟩,
⟨128,972346834,972347522⟩]
theorem checked13625 : checkPrefixCuts (2^48) 1789788161 9 Manual.Count131072.C013625.packed 128 cuts13625 = true := by
 decide +kernel
def pointBounds13625 : List (Nat × Nat × Nat) := [(1789829120,95004473993936,95004851162171),(1789885440,95004894352737,95005271521267)]
theorem point_links_checked13625 : (cuts13625.take 2).map (fun c => (1789788161-1+2*2^9*c.k,95004175661626+c.lower,95004552829649+c.upper)) = pointBounds13625 := by
 decide +kernel
def cuts13626 : List PrefixCut := [⟨22,162915795,162915909⟩,
⟨77,578058943,578059348⟩,
⟨128,964098887,964099561⟩]
theorem checked13626 : checkPrefixCuts (2^48) 1789919233 9 Manual.Count131072.C013626.packed 128 cuts13626 = true := by
 decide +kernel
def pointBounds13626 : List (Nat × Nat × Nat) := [(1789941760,95005310924255,95005688093080),(1789998080,95005726067403,95006103236519)]
theorem point_links_checked13626 : (cuts13626.take 2).map (fun c => (1789919233-1+2*2^9*c.k,95005148008460+c.lower,95005525177171+c.upper)) = pointBounds13626 := by
 decide +kernel
def cuts13627 : List PrefixCut := [⟨4,27045957,27045976⟩,
⟨59,442320200,442320509⟩,
⟨114,860254420,860255026⟩,
⟨128,969374292,969374975⟩]
theorem checked13627 : checkPrefixCuts (2^48) 1790050305 9 Manual.Count131072.C013627.packed 128 cuts13627 = true := by
 decide +kernel
def pointBounds13627 : List (Nat × Nat × Nat) := [(1790054400,95006139153304,95006516322708),(1790110720,95006554427547,95006931597241),(1790167040,95006972361767,95007349531758)]
theorem point_links_checked13627 : (cuts13627.take 3).map (fun c => (1790050305-1+2*2^9*c.k,95006112107347+c.lower,95006489276732+c.upper)) = pointBounds13627 := by
 decide +kernel
def cuts13628 : List PrefixCut := [⟨41,303455366,303455583⟩,
⟨96,721205973,721206487⟩,
⟨128,964586450,964587137⟩]
theorem checked13628 : checkPrefixCuts (2^48) 1790181377 9 Manual.Count131072.C013628.packed 128 cuts13628 = true := by
 decide +kernel
def pointBounds13628 : List (Nat × Nat × Nat) := [(1790223360,95007384937005,95007762107290),(1790279680,95007802687612,95008179858194)]
theorem point_links_checked13628 : (cuts13628.take 2).map (fun c => (1790181377-1+2*2^9*c.k,95007081481639+c.lower,95007458651707+c.upper)) = pointBounds13628 := by
 decide +kernel
def cuts13629 : List PrefixCut := [⟨23,173570931,173571052⟩,
⟨78,586264435,586264845⟩,
⟨128,964358947,964359627⟩]
theorem checked13629 : checkPrefixCuts (2^48) 1790312449 9 Manual.Count131072.C013629.packed 128 cuts13629 = true := by
 decide +kernel
def pointBounds13629 : List (Nat × Nat × Nat) := [(1790336000,95008219639020,95008596809896),(1790392320,95008632332524,95009009503689)]
theorem point_links_checked13629 : (cuts13629.take 2).map (fun c => (1790312449-1+2*2^9*c.k,95008046068089+c.lower,95008423238844+c.upper)) = pointBounds13629 := by
 decide +kernel
def cuts13630 : List PrefixCut := [⟨5,37887454,37887480⟩,
⟨60,450397692,450398010⟩,
⟨115,870440640,870441255⟩,
⟨128,967746616,967747302⟩]
theorem checked13630 : checkPrefixCuts (2^48) 1790443521 9 Manual.Count131072.C013630.packed 128 cuts13630 = true := by
 decide +kernel
def pointBounds13630 : List (Nat × Nat × Nat) := [(1790448640,95009048314490,95009425485951),(1790504960,95009460824728,95009837996481),(1790561280,95009880867676,95010258039726)]
theorem point_links_checked13630 : (cuts13630.take 3).map (fun c => (1790443521-1+2*2^9*c.k,95009010427036+c.lower,95009387598471+c.upper)) = pointBounds13630 := by
 decide +kernel
def cuts13631 : List PrefixCut := [⟨42,319422648,319422869⟩,
⟨97,736766951,736767464⟩,
⟨128,974120748,974121432⟩]
theorem checked13631 : checkPrefixCuts (2^48) 1790574593 9 Manual.Count131072.C013631.packed 128 cuts13631 = true := by
 decide +kernel
def pointBounds13631 : List (Nat × Nat × Nat) := [(1790617600,95010297596300,95010674768642),(1790673920,95010714940603,95011092113237)]
theorem point_links_checked13631 : (cuts13631.take 2).map (fun c => (1790574593-1+2*2^9*c.k,95009978173652+c.lower,95010355345773+c.upper)) = pointBounds13631 := by
 decide +kernel
def cuts13632 : List PrefixCut := [⟨24,177933988,177934111⟩,
⟨79,589750790,589751204⟩,
⟨128,964304277,964304953⟩]
theorem checked13632 : checkPrefixCuts (2^48) 1790705665 9 Manual.Count131072.C013632.packed 128 cuts13632 = true := by
 decide +kernel
def pointBounds13632 : List (Nat × Nat × Nat) := [(1790730240,95011130228388,95011507401316),(1790786560,95011542045190,95011919218409)]
theorem point_links_checked13632 : (cuts13632.take 2).map (fun c => (1790705665-1+2*2^9*c.k,95010952294400+c.lower,95011329467205+c.upper)) = pointBounds13632 := by
 decide +kernel
def cuts13633 : List PrefixCut := [⟨6,45580690,45580722⟩,
⟨61,465858755,465859088⟩,
⟨116,882508800,882509426⟩,
⟨128,973035327,973036015⟩]
theorem checked13633 : checkPrefixCuts (2^48) 1790836737 9 Manual.Count131072.C013633.packed 128 cuts13633 = true := by
 decide +kernel
def pointBounds13633 : List (Nat × Nat × Nat) := [(1790842880,95011962179367,95012339352880),(1790899200,95012382457432,95012759631246),(1790955520,95012799107477,95013176281584)]
theorem point_links_checked13633 : (cuts13633.take 3).map (fun c => (1790836737-1+2*2^9*c.k,95011916598677+c.lower,95012293772158+c.upper)) = pointBounds13633 := by
 decide +kernel
def cuts13634 : List PrefixCut := [⟨43,322338532,322338757⟩,
⟨98,734561946,734562462⟩,
⟨128,955833925,955834600⟩]
theorem checked13634 : checkPrefixCuts (2^48) 1790967809 9 Manual.Count131072.C013634.packed 128 cuts13634 = true := by
 decide +kernel
def pointBounds13634 : List (Nat × Nat × Nat) := [(1791011840,95013211972536,95013589146930),(1791068160,95013624195950,95014001370635)]
theorem point_links_checked13634 : (cuts13634.take 2).map (fun c => (1790967809-1+2*2^9*c.k,95012889634004+c.lower,95013266808173+c.upper)) = pointBounds13634 := by
 decide +kernel
def cuts13635 : List PrefixCut := [⟨25,184495204,184495339⟩,
⟨80,596849796,596850224⟩,
⟨128,966292316,966293003⟩]
theorem checked13635 : checkPrefixCuts (2^48) 1791098881 9 Manual.Count131072.C013635.packed 128 cuts13635 = true := by
 decide +kernel
def pointBounds13635 : List (Nat × Nat × Nat) := [(1791124480,95014029963133,95014407138112),(1791180800,95014442317725,95014819492997)]
theorem point_links_checked13635 : (cuts13635.take 2).map (fun c => (1791098881-1+2*2^9*c.k,95013845467929+c.lower,95014222642773+c.upper)) = pointBounds13635 := by
 decide +kernel
def cuts13636 : List PrefixCut := [⟨7,50442023,50442059⟩,
⟨62,473456035,473456366⟩,
⟨117,882786229,882786847⟩,
⟨128,961351007,961351681⟩]
theorem checked13636 : checkPrefixCuts (2^48) 1791229953 9 Manual.Count131072.C013636.packed 128 cuts13636 = true := by
 decide +kernel
def pointBounds13636 : List (Nat × Nat × Nat) := [(1791237120,95014862202268,95015239377835),(1791293440,95015285216280,95015662392142),(1791349760,95015694546474,95016071722623)]
theorem point_links_checked13636 : (cuts13636.take 3).map (fun c => (1791229953-1+2*2^9*c.k,95014811760245+c.lower,95015188935776+c.upper)) = pointBounds13636 := by
 decide +kernel
def cuts13637 : List PrefixCut := [⟨44,331381023,331381258⟩,
⟨99,745713537,745714062⟩,
⟨128,969293719,969294399⟩]
theorem checked13637 : checkPrefixCuts (2^48) 1791361025 9 Manual.Count131072.C013637.packed 128 cuts13637 = true := by
 decide +kernel
def pointBounds13637 : List (Nat × Nat × Nat) := [(1791406080,95016104492275,95016481668715),(1791462400,95016518824789,95016896001519)]
theorem point_links_checked13637 : (cuts13637.take 2).map (fun c => (1791361025-1+2*2^9*c.k,95015773111252+c.lower,95016150287457+c.upper)) = pointBounds13637 := by
 decide +kernel
def cuts13638 : List PrefixCut := [⟨26,202680119,202680263⟩,
⟨81,619971594,619972030⟩,
⟨128,970165714,970166401⟩]
theorem checked13638 : checkPrefixCuts (2^48) 1791492097 9 Manual.Count131072.C013638.packed 128 cuts13638 = true := by
 decide +kernel
def pointBounds13638 : List (Nat × Nat × Nat) := [(1791518720,95016945085090,95017322262119),(1791575040,95017362376565,95017739553886)]
theorem point_links_checked13638 : (cuts13638.take 2).map (fun c => (1791492097-1+2*2^9*c.k,95016742404971+c.lower,95017119581856+c.upper)) = pointBounds13638 := by
 decide +kernel
def cuts13639 : List PrefixCut := [⟨8,60642805,60642849⟩,
⟨63,464711307,464711638⟩,
⟨118,882906056,882906681⟩,
⟨128,958154582,958155260⟩]
theorem checked13639 : checkPrefixCuts (2^48) 1791623169 9 Manual.Count131072.C013639.packed 128 cuts13639 = true := by
 decide +kernel
def pointBounds13639 : List (Nat × Nat × Nat) := [(1791631360,95017773213490,95018150391106),(1791687680,95018177281992,95018554459895),(1791744000,95018595476741,95018972654938)]
theorem point_links_checked13639 : (cuts13639.take 3).map (fun c => (1791623169-1+2*2^9*c.k,95017712570685+c.lower,95018089748257+c.upper)) = pointBounds13639 := by
 decide +kernel
def cuts13640 : List PrefixCut := [⟨45,344975229,344975475⟩,
⟨100,760787340,760787876⟩,
⟨128,973322479,973323159⟩]
theorem checked13640 : checkPrefixCuts (2^48) 1791754241 9 Manual.Count131072.C013640.packed 128 cuts13640 = true := by
 decide +kernel
def pointBounds13640 : List (Nat × Nat × Nat) := [(1791800320,95019015700496,95019392878992),(1791856640,95019431512607,95019808691393)]
theorem point_links_checked13640 : (cuts13640.take 2).map (fun c => (1791754241-1+2*2^9*c.k,95018670725267+c.lower,95019047903517+c.upper)) = pointBounds13640 := by
 decide +kernel
def cuts13641 : List PrefixCut := [⟨27,207505167,207505314⟩,
⟨82,628474739,628475183⟩,
⟨128,973565588,973566275⟩]
theorem checked13641 : checkPrefixCuts (2^48) 1791885313 9 Manual.Count131072.C013641.packed 128 cuts13641 = true := by
 decide +kernel
def pointBounds13641 : List (Nat × Nat × Nat) := [(1791912960,95019851552913,95020228731990),(1791969280,95020272522485,95020649701859)]
theorem point_links_checked13641 : (cuts13641.take 2).map (fun c => (1791885313-1+2*2^9*c.k,95019644047746+c.lower,95020021226676+c.upper)) = pointBounds13641 := by
 decide +kernel
def cuts13642 : List PrefixCut := [⟨9,67854759,67854806⟩,
⟨64,487541333,487541676⟩,
⟨119,903288059,903288691⟩,
⟨128,975064715,975065398⟩]
theorem checked13642 : checkPrefixCuts (2^48) 1792016385 9 Manual.Count131072.C013642.packed 128 cuts13642 = true := by
 decide +kernel
def pointBounds13642 : List (Nat × Nat × Nat) := [(1792025600,95020685468093,95021062647757),(1792081920,95021105154667,95021482334627),(1792138240,95021520901393,95021898081642)]
theorem point_links_checked13642 : (cuts13642.take 3).map (fun c => (1792016385-1+2*2^9*c.k,95020617613334+c.lower,95020994792951+c.upper)) = pointBounds13642 := by
 decide +kernel
def cuts13643 : List PrefixCut := [⟨46,337517754,337517990⟩,
⟨101,762347508,762348047⟩,
⟨128,971851991,971852677⟩]
theorem checked13643 : checkPrefixCuts (2^48) 1792147457 9 Manual.Count131072.C013643.packed 128 cuts13643 = true := by
 decide +kernel
def pointBounds13643 : List (Nat × Nat × Nat) := [(1792194560,95021930195803,95022307376339),(1792250880,95022355025557,95022732206396)]
theorem point_links_checked13643 : (cuts13643.take 2).map (fun c => (1792147457-1+2*2^9*c.k,95021592678049+c.lower,95021969858349+c.upper)) = pointBounds13643 := by
 decide +kernel
def cuts13644 : List PrefixCut := [⟨28,212799188,212799340⟩,
⟨83,627394327,627394769⟩,
⟨128,971467143,971467826⟩]
theorem checked13644 : checkPrefixCuts (2^48) 1792278529 9 Manual.Count131072.C013644.packed 128 cuts13644 = true := by
 decide +kernel
def pointBounds13644 : List (Nat × Nat × Nat) := [(1792307200,95022777329228,95023154510366),(1792363520,95023191924367,95023569105795)]
theorem point_links_checked13644 : (cuts13644.take 2).map (fun c => (1792278529-1+2*2^9*c.k,95022564530040+c.lower,95022941711026+c.upper)) = pointBounds13644 := by
 decide +kernel
def cuts13645 : List PrefixCut := [⟨10,76790944,76790997⟩,
⟨65,492145261,492145605⟩,
⟨120,902304603,902305236⟩,
⟨128,964643931,964644608⟩]
theorem checked13645 : checkPrefixCuts (2^48) 1792409601 9 Manual.Count131072.C013645.packed 128 cuts13645 = true := by
 decide +kernel
def pointBounds13645 : List (Nat × Nat × Nat) := [(1792419840,95023612788127,95023989969849),(1792476160,95024028142444,95024405324457),(1792532480,95024438301786,95024815484088)]
theorem point_links_checked13645 : (cuts13645.take 3).map (fun c => (1792409601-1+2*2^9*c.k,95023535997183+c.lower,95023913178852+c.upper)) = pointBounds13645 := by
 decide +kernel
def cuts13646 : List PrefixCut := [⟨47,352988960,352989211⟩,
⟨102,772229663,772230209⟩,
⟨128,966143593,966144273⟩]
theorem checked13646 : checkPrefixCuts (2^48) 1792540673 9 Manual.Count131072.C013646.packed 128 cuts13646 = true := by
 decide +kernel
def pointBounds13646 : List (Nat × Nat × Nat) := [(1792588800,95024853630074,95025230812671),(1792645120,95025272870777,95025650053669)]
theorem point_links_checked13646 : (cuts13646.take 2).map (fun c => (1792540673-1+2*2^9*c.k,95024500641114+c.lower,95024877823460+c.upper)) = pointBounds13646 := by
 decide +kernel
def cuts13647 : List PrefixCut := [⟨29,216677746,216677896⟩,
⟨84,632123932,632124373⟩,
⟨128,958693654,958694329⟩]
theorem checked13647 : checkPrefixCuts (2^48) 1792671745 9 Manual.Count131072.C013647.packed 128 cuts13647 = true := by
 decide +kernel
def pointBounds13647 : List (Nat × Nat × Nat) := [(1792701440,95025683462453,95026060645629),(1792757760,95026098908639,95026476092106)]
theorem point_links_checked13647 : (cuts13647.take 2).map (fun c => (1792671745-1+2*2^9*c.k,95025466784707+c.lower,95025843967733+c.upper)) = pointBounds13647 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000113
