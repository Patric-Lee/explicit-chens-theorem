import PlattAssemblyKernel
import PlattCertificates.Count131072.C012624
import PlattCertificates.Count131072.C012625
import PlattCertificates.Count131072.C012626
import PlattCertificates.Count131072.C012627
import PlattCertificates.Count131072.C012628
import PlattCertificates.Count131072.C012629
import PlattCertificates.Count131072.C012630
import PlattCertificates.Count131072.C012631
import PlattCertificates.Count131072.C012632
import PlattCertificates.Count131072.C012633
import PlattCertificates.Count131072.C012634
import PlattCertificates.Count131072.C012635
import PlattCertificates.Count131072.C012636
import PlattCertificates.Count131072.C012637
import PlattCertificates.Count131072.C012638
import PlattCertificates.Count131072.C012639
import PlattCertificates.Count131072.C012640
import PlattCertificates.Count131072.C012641
import PlattCertificates.Count131072.C012642
import PlattCertificates.Count131072.C012643
import PlattCertificates.Count131072.C012644
import PlattCertificates.Count131072.C012645
import PlattCertificates.Count131072.C012646
import PlattCertificates.Count131072.C012647
import PlattCertificates.Count131072.C012648
import PlattCertificates.Count131072.C012649
import PlattCertificates.Count131072.C012650
import PlattCertificates.Count131072.C012651
import PlattCertificates.Count131072.C012652
import PlattCertificates.Count131072.C012653
import PlattCertificates.Count131072.C012654
import PlattCertificates.Count131072.C012655
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000082
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12624 : List PrefixCut := [⟨12,98769589,98769663⟩,
⟨63,510641063,510641445⟩,
⟨114,936414712,936415407⟩,
⟨128,1045019605,1045020382⟩]
theorem checked12624 : checkPrefixCuts (2^48) 1658585089 9 Manual.Count131072.C012624.packed 128 cuts12624 = true := by
 decide +kernel
def pointBounds12624 : List (Nat × Nat × Nat) := [(1658597376,93996652119871,93997028560816),(1658649600,93997063991345,93997440432598),(1658701824,93997489764994,93997866206560)]
theorem point_links_checked12624 : (cuts12624.take 3).map (fun c => (1658585089-1+2*2^9*c.k,93996553350282+c.lower,93996929791153+c.upper)) = pointBounds12624 := by
 decide +kernel
def cuts12625 : List PrefixCut := [⟨37,300016346,300016565⟩,
⟨88,721690686,721691213⟩,
⟨128,1050197210,1050197978⟩]
theorem checked12625 : checkPrefixCuts (2^48) 1658716161 9 Manual.Count131072.C012625.packed 128 cuts12625 = true := by
 decide +kernel
def pointBounds12625 : List (Nat × Nat × Nat) := [(1658754048,93997898386233,93998274828100),(1658806272,93998320060573,93998696502748)]
theorem point_links_checked12625 : (cuts12625.take 2).map (fun c => (1658716161-1+2*2^9*c.k,93997598369887+c.lower,93997974811535+c.upper)) = pointBounds12625 := by
 decide +kernel
def cuts12626 : List PrefixCut := [⟨11,93324235,93324303⟩,
⟨62,509711998,509712373⟩,
⟨113,932025266,932025952⟩,
⟨128,1058597903,1058598682⟩]
theorem checked12626 : checkPrefixCuts (2^48) 1658847233 9 Manual.Count131072.C012626.packed 128 cuts12626 = true := by
 decide +kernel
def pointBounds12626 : List (Nat × Nat × Nat) := [(1658858496,93998741891332,93999118333816),(1658910720,93999158279095,93999534721886),(1658962944,93999580592363,93999957035465)]
theorem point_links_checked12626 : (cuts12626.take 3).map (fun c => (1658847233-1+2*2^9*c.k,93998648567097+c.lower,93999025009513+c.upper)) = pointBounds12626 := by
 decide +kernel
def cuts12627 : List PrefixCut := [⟨36,301665598,301665822⟩,
⟨87,719032073,719032608⟩,
⟨128,1046638472,1046639250⟩]
theorem checked12627 : checkPrefixCuts (2^48) 1658978305 9 Manual.Count131072.C012627.packed 128 cuts12627 = true := by
 decide +kernel
def pointBounds12627 : List (Nat × Nat × Nat) := [(1659015168,94000008830598,94000385274017),(1659067392,94000426197073,94000802640803)]
theorem point_links_checked12627 : (cuts12627.take 2).map (fun c => (1658978305-1+2*2^9*c.k,93999707165000+c.lower,94000083608195+c.upper)) = pointBounds12627 := by
 decide +kernel
def cuts12628 : List PrefixCut := [⟨10,81264109,81264167⟩,
⟨61,501318617,501318986⟩,
⟨112,925770715,925771398⟩,
⟨128,1054019776,1054020554⟩]
theorem checked12628 : checkPrefixCuts (2^48) 1659109377 9 Manual.Count131072.C012628.packed 128 cuts12628 = true := by
 decide +kernel
def pointBounds12628 : List (Nat × Nat × Nat) := [(1659119616,94000835067581,94001211511612),(1659171840,94001255122089,94001631566431),(1659224064,94001679574187,94002056018843)]
theorem point_links_checked12628 : (cuts12628.take 3).map (fun c => (1659109377-1+2*2^9*c.k,94000753803472+c.lower,94001130247445+c.upper)) = pointBounds12628 := by
 decide +kernel
def cuts12629 : List PrefixCut := [⟨35,276681137,276681344⟩,
⟨86,695169213,695169722⟩,
⟨128,1040365438,1040366200⟩]
theorem checked12629 : checkPrefixCuts (2^48) 1659240449 9 Manual.Count131072.C012629.packed 128 cuts12629 = true := by
 decide +kernel
def pointBounds12629 : List (Nat × Nat × Nat) := [(1659276288,94002084504385,94002460949343),(1659328512,94002502992461,94002879437721)]
theorem point_links_checked12629 : (cuts12629.take 2).map (fun c => (1659240449-1+2*2^9*c.k,94001807823248+c.lower,94002184267999+c.upper)) = pointBounds12629 := by
 decide +kernel
def cuts12630 : List PrefixCut := [⟨9,71921820,71921873⟩,
⟨60,476304869,476305217⟩,
⟨111,888986586,888987239⟩,
⟨128,1031123851,1031124606⟩]
theorem checked12630 : checkPrefixCuts (2^48) 1659371521 9 Manual.Count131072.C012630.packed 128 cuts12630 = true := by
 decide +kernel
def pointBounds12630 : List (Nat × Nat × Nat) := [(1659380736,94002920110506,94003296556072),(1659432960,94003324493555,94003700939416),(1659485184,94003737175272,94004113621438)]
theorem point_links_checked12630 : (cuts12630.take 3).map (fun c => (1659371521-1+2*2^9*c.k,94002848188686+c.lower,94003224634199+c.upper)) = pointBounds12630 := by
 decide +kernel
def cuts12631 : List PrefixCut := [⟨34,270022635,270022834⟩,
⟨85,689801915,689802423⟩,
⟨128,1040540619,1040541383⟩]
theorem checked12631 : checkPrefixCuts (2^48) 1659502593 9 Manual.Count131072.C012631.packed 128 cuts12631 = true := by
 decide +kernel
def pointBounds12631 : List (Nat × Nat × Nat) := [(1659537408,94004149335172,94004525781639),(1659589632,94004569114452,94004945561228)]
theorem point_links_checked12631 : (cuts12631.take 2).map (fun c => (1659502593-1+2*2^9*c.k,94003879312537+c.lower,94004255758805+c.upper)) = pointBounds12631 := by
 decide +kernel
def cuts12632 : List PrefixCut := [⟨8,65465675,65465724⟩,
⟨59,476060193,476060550⟩,
⟨110,895291048,895291716⟩,
⟨128,1035370873,1035371645⟩]
theorem checked12632 : checkPrefixCuts (2^48) 1659633665 9 Manual.Count131072.C012632.packed 128 cuts12632 = true := by
 decide +kernel
def pointBounds12632 : List (Nat × Nat × Nat) := [(1659641856,94004985318831,94005361765912),(1659694080,94005395913349,94005772360738),(1659746304,94005815144204,94006191591904)]
theorem point_links_checked12632 : (cuts12632.take 3).map (fun c => (1659633665-1+2*2^9*c.k,94004919853156+c.lower,94005296300188+c.upper)) = pointBounds12632 := by
 decide +kernel
def cuts12633 : List PrefixCut := [⟨33,266588337,266588536⟩,
⟨84,681892420,681892923⟩,
⟨128,1047328857,1047329625⟩]
theorem checked12633 : checkPrefixCuts (2^48) 1659764737 9 Manual.Count131072.C012633.packed 128 cuts12633 = true := by
 decide +kernel
def pointBounds12633 : List (Nat × Nat × Nat) := [(1659798528,94006221812366,94006598260369),(1659850752,94006637116449,94007013564756)]
theorem point_links_checked12633 : (cuts12633.take 2).map (fun c => (1659764737-1+2*2^9*c.k,94005955224029+c.lower,94006331671833+c.upper)) = pointBounds12633 := by
 decide +kernel
def cuts12634 : List PrefixCut := [⟨7,53585213,53585253⟩,
⟨58,457162799,457163135⟩,
⟨109,871410276,871410916⟩,
⟨128,1027237242,1027237996⟩]
theorem checked12634 : checkPrefixCuts (2^48) 1659895809 9 Manual.Count131072.C012634.packed 128 cuts12634 = true := by
 decide +kernel
def pointBounds12634 : List (Nat × Nat × Nat) := [(1659902976,94007056138099,94007432586711),(1659955200,94007459715685,94007836164593),(1660007424,94007873963162,94008250412374)]
theorem point_links_checked12634 : (cuts12634.take 3).map (fun c => (1659895809-1+2*2^9*c.k,94007002552886+c.lower,94007379001458+c.upper)) = pointBounds12634 := by
 decide +kernel
def cuts12635 : List PrefixCut := [⟨32,266885513,266885712⟩,
⟨83,682632922,682633429⟩,
⟨128,1047672731,1047673500⟩]
theorem checked12635 : checkPrefixCuts (2^48) 1660026881 9 Manual.Count131072.C012635.packed 128 cuts12635 = true := by
 decide +kernel
def pointBounds12635 : List (Nat × Nat × Nat) := [(1660059648,94008296675641,94008673125166),(1660111872,94008712423050,94009088872883)]
theorem point_links_checked12635 : (cuts12635.take 2).map (fun c => (1660026881-1+2*2^9*c.k,94008029790128+c.lower,94008406239454+c.upper)) = pointBounds12635 := by
 decide +kernel
def cuts12636 : List PrefixCut := [⟨6,49677194,49677231⟩,
⟨57,471332590,471332939⟩,
⟨108,889075265,889075927⟩,
⟨128,1051150429,1051151209⟩]
theorem checked12636 : checkPrefixCuts (2^48) 1660157953 9 Manual.Count131072.C012636.packed 128 cuts12636 = true := by
 decide +kernel
def pointBounds12636 : List (Nat × Nat × Nat) := [(1660164096,94009127140053,94009503590185),(1660216320,94009548795449,94009925245893),(1660268544,94009966538124,94010342988881)]
theorem point_links_checked12636 : (cuts12636.take 3).map (fun c => (1660157953-1+2*2^9*c.k,94009077462859+c.lower,94009453912954+c.upper)) = pointBounds12636 := by
 decide +kernel
def cuts12637 : List PrefixCut := [⟨31,253619923,253620116⟩,
⟨82,665911348,665911850⟩,
⟨128,1050049800,1050050579⟩]
theorem checked12637 : checkPrefixCuts (2^48) 1660289025 9 Manual.Count131072.C012637.packed 128 cuts12637 = true := by
 decide +kernel
def pointBounds12637 : List (Nat × Nat × Nat) := [(1660320768,94010382233211,94010758684279),(1660372992,94010794524636,94011170976013)]
theorem point_links_checked12637 : (cuts12637.take 2).map (fun c => (1660289025-1+2*2^9*c.k,94010128613288+c.lower,94010505064163+c.upper)) = pointBounds12637 := by
 decide +kernel
def cuts12638 : List PrefixCut := [⟨5,41023844,41023874⟩,
⟨56,459052993,459053332⟩,
⟨107,867067694,867068338⟩,
⟨128,1037084189,1037084957⟩]
theorem checked12638 : checkPrefixCuts (2^48) 1660420097 9 Manual.Count131072.C012638.packed 128 cuts12638 = true := by
 decide +kernel
def pointBounds12638 : List (Nat × Nat × Nat) := [(1660425216,94011219686932,94011596138616),(1660477440,94011637716081,94012014168074),(1660529664,94012045730782,94012422183080)]
theorem point_links_checked12638 : (cuts12638.take 3).map (fun c => (1660420097-1+2*2^9*c.k,94011178663088+c.lower,94011555114742+c.upper)) = pointBounds12638 := by
 decide +kernel
def cuts12639 : List PrefixCut := [⟨30,241375609,241375786⟩,
⟨81,655975197,655975678⟩,
⟨128,1050222905,1050223673⟩]
theorem checked12639 : checkPrefixCuts (2^48) 1660551169 9 Manual.Count131072.C012639.packed 128 cuts12639 = true := by
 decide +kernel
def pointBounds12639 : List (Nat × Nat × Nat) := [(1660581888,94012457122886,94012833575485),(1660634112,94012871722474,94013248175377)]
theorem point_links_checked12639 : (cuts12639.take 2).map (fun c => (1660551169-1+2*2^9*c.k,94012215747277+c.lower,94012592199699+c.upper)) = pointBounds12639 := by
 decide +kernel
def cuts12640 : List PrefixCut := [⟨4,30169809,30169832⟩,
⟨55,449150155,449150488⟩,
⟨106,869473234,869473876⟩,
⟨128,1045055833,1045056605⟩]
theorem checked12640 : checkPrefixCuts (2^48) 1660682241 9 Manual.Count131072.C012640.packed 128 cuts12640 = true := by
 decide +kernel
def pointBounds12640 : List (Nat × Nat × Nat) := [(1660686336,94013296139991,94013672593204),(1660738560,94013715120337,94014091573860),(1660790784,94014135443416,94014511897248)]
theorem point_links_checked12640 : (cuts12640.take 3).map (fun c => (1660682241-1+2*2^9*c.k,94013265970182+c.lower,94013642423372+c.upper)) = pointBounds12640 := by
 decide +kernel
def cuts12641 : List PrefixCut := [⟨29,239473278,239473454⟩,
⟨80,662820446,662820936⟩,
⟨128,1053955535,1053956310⟩]
theorem checked12641 : checkPrefixCuts (2^48) 1660813313 9 Manual.Count131072.C012641.packed 128 cuts12641 = true := by
 decide +kernel
def pointBounds12641 : List (Nat × Nat × Nat) := [(1660843008,94014550499293,94014926953431),(1660895232,94014973846461,94015350300913)]
theorem point_links_checked12641 : (cuts12641.take 2).map (fun c => (1660813313-1+2*2^9*c.k,94014311026015+c.lower,94014687479977+c.upper)) = pointBounds12641 := by
 decide +kernel
def cuts12642 : List PrefixCut := [⟨3,24911591,24911609⟩,
⟨54,448740567,448740899⟩,
⟨105,862388686,862389325⟩,
⟨128,1053025088,1053025868⟩]
theorem checked12642 : checkPrefixCuts (2^48) 1660944385 9 Manual.Count131072.C012642.packed 128 cuts12642 = true := by
 decide +kernel
def pointBounds12642 : List (Nat × Nat × Nat) := [(1660947456,94015389893141,94015766347896),(1660999680,94015813722117,94016190177186),(1661051904,94016227370236,94016603825612)]
theorem point_links_checked12642 : (cuts12642.take 3).map (fun c => (1660944385-1+2*2^9*c.k,94015364981550+c.lower,94015741436287+c.upper)) = pointBounds12642 := by
 decide +kernel
def cuts12643 : List PrefixCut := [⟨28,227743462,227743632⟩,
⟨79,633570939,633571412⟩,
⟨128,1032777630,1032778400⟩]
theorem checked12643 : checkPrefixCuts (2^48) 1661075457 9 Manual.Count131072.C012643.packed 128 cuts12643 = true := by
 decide +kernel
def pointBounds12643 : List (Nat × Nat × Nat) := [(1661104128,94016645750100,94017022205787),(1661156352,94017051577577,94017428033567)]
theorem point_links_checked12643 : (cuts12643.take 2).map (fun c => (1661075457-1+2*2^9*c.k,94016418006638+c.lower,94016794462155+c.upper)) = pointBounds12643 := by
 decide +kernel
def cuts12644 : List PrefixCut := [⟨2,14910713,14910724⟩,
⟨53,440197979,440198302⟩,
⟨104,850561862,850562487⟩,
⟨128,1047437111,1047437881⟩]
theorem checked12644 : checkPrefixCuts (2^48) 1661206529 9 Manual.Count131072.C012644.packed 128 cuts12644 = true := by
 decide +kernel
def pointBounds12644 : List (Nat × Nat × Nat) := [(1661208576,94017465694981,94017842151279),(1661260800,94017890982247,94018267438857),(1661313024,94018301346130,94018677803042)]
theorem point_links_checked12644 : (cuts12644.take 3).map (fun c => (1661206529-1+2*2^9*c.k,94017450784268+c.lower,94017827240555+c.upper)) = pointBounds12644 := by
 decide +kernel
def cuts12645 : List PrefixCut := [⟨27,219236266,219236427⟩,
⟨78,637198340,637198805⟩,
⟨128,1044643530,1044644295⟩]
theorem checked12645 : checkPrefixCuts (2^48) 1661337601 9 Manual.Count131072.C012645.packed 128 cuts12645 = true := by
 decide +kernel
def pointBounds12645 : List (Nat × Nat × Nat) := [(1661365248,94018717457645,94019093914863),(1661417472,94019135419719,94019511877241)]
theorem point_links_checked12645 : (cuts12645.take 2).map (fun c => (1661337601-1+2*2^9*c.k,94018498221379+c.lower,94018874678436+c.upper)) = pointBounds12645 := by
 decide +kernel
def cuts12646 : List PrefixCut := [⟨1,8301249,8301255⟩,
⟨52,420477023,420477334⟩,
⟨103,843990013,843990636⟩,
⟨128,1050828921,1050829700⟩]
theorem checked12646 : checkPrefixCuts (2^48) 1661468673 9 Manual.Count131072.C012646.packed 128 cuts12646 = true := by
 decide +kernel
def pointBounds12646 : List (Nat × Nat × Nat) := [(1661469696,94019551166158,94019927623986),(1661521920,94019963341932,94020339800065),(1661574144,94020386854922,94020763313367)]
theorem point_links_checked12646 : (cuts12646.take 3).map (fun c => (1661468673-1+2*2^9*c.k,94019542864909+c.lower,94019919322731+c.upper)) = pointBounds12646 := by
 decide +kernel
def cuts12647 : List PrefixCut := [⟨26,206835655,206835807⟩,
⟨77,619480748,619481209⟩,
⟨128,1031435320,1031436092⟩]
theorem checked12647 : checkPrefixCuts (2^48) 1661599745 9 Manual.Count131072.C012647.packed 128 cuts12647 = true := by
 decide +kernel
def pointBounds12647 : List (Nat × Nat × Nat) := [(1661626368,94020800529485,94021176988238),(1661678592,94021213174578,94021589633640),(1661730816,94021625129150,94022001588523)]
theorem point_links_checked12647 : (cuts12647.take 3).map (fun c => (1661599745-1+2*2^9*c.k,94020593693830+c.lower,94020970152431+c.upper)) = pointBounds12647 := by
 decide +kernel
def cuts12648 : List PrefixCut := [⟨51,429557506,429557822⟩,
⟨102,835557951,835558563⟩,
⟨128,1048123059,1048123825⟩]
theorem checked12648 : checkPrefixCuts (2^48) 1661730817 9 Manual.Count131072.C012648.packed 128 cuts12648 = true := by
 decide +kernel
def pointBounds12648 : List (Nat × Nat × Nat) := [(1661783040,94022054686656,94022431146345),(1661835264,94022460687101,94022837147086)]
theorem point_links_checked12648 : (cuts12648.take 2).map (fun c => (1661730817-1+2*2^9*c.k,94021625129150+c.lower,94022001588523+c.upper)) = pointBounds12648 := by
 decide +kernel
def cuts12649 : List PrefixCut := [⟨25,205617467,205617619⟩,
⟨76,628021018,628021483⟩,
⟨127,1040080214,1040080982⟩,
⟨128,1048548209,1048548983⟩]
theorem checked12649 : checkPrefixCuts (2^48) 1661861889 9 Manual.Count131072.C012649.packed 128 cuts12649 = true := by
 decide +kernel
def pointBounds12649 : List (Nat × Nat × Nat) := [(1661887488,94022878869676,94023255329967),(1661939712,94023301273227,94023677733831),(1661991936,94023713332423,94024089793330)]
theorem point_links_checked12649 : (cuts12649.take 3).map (fun c => (1661861889-1+2*2^9*c.k,94022673252209+c.lower,94023049712348+c.upper)) = pointBounds12649 := by
 decide +kernel
def cuts12650 : List PrefixCut := [⟨50,401038007,401038299⟩,
⟨101,820861508,820862112⟩,
⟨128,1048126412,1048127183⟩]
theorem checked12650 : checkPrefixCuts (2^48) 1661992961 9 Manual.Count131072.C012650.packed 128 cuts12650 = true := by
 decide +kernel
def pointBounds12650 : List (Nat × Nat × Nat) := [(1662044160,94024122838425,94024499299630),(1662096384,94024542661926,94024919123443)]
theorem point_links_checked12650 : (cuts12650.take 2).map (fun c => (1661992961-1+2*2^9*c.k,94023721800418+c.lower,94024098261331+c.upper)) = pointBounds12650 := by
 decide +kernel
def cuts12651 : List PrefixCut := [⟨24,199319334,199319478⟩,
⟨75,619285837,619286295⟩,
⟨126,1040593814,1040594579⟩,
⟨128,1056849806,1056850583⟩]
theorem checked12651 : checkPrefixCuts (2^48) 1662124033 9 Manual.Count131072.C012651.packed 128 cuts12651 = true := by
 decide +kernel
def pointBounds12651 : List (Nat × Nat × Nat) := [(1662148608,94024969246164,94025345707992),(1662200832,94025389212667,94025765674809),(1662253056,94025810520644,94026186983093)]
theorem point_links_checked12651 : (cuts12651.take 3).map (fun c => (1662124033-1+2*2^9*c.k,94024769926830+c.lower,94025146388514+c.upper)) = pointBounds12651 := by
 decide +kernel
def cuts12652 : List PrefixCut := [⟨49,401821525,401821818⟩,
⟨100,825812225,825812832⟩,
⟨128,1058120992,1058121772⟩]
theorem checked12652 : checkPrefixCuts (2^48) 1662255105 9 Manual.Count131072.C012652.packed 128 cuts12652 = true := by
 decide +kernel
def pointBounds12652 : List (Nat × Nat × Nat) := [(1662305280,94026228598161,94026605060915),(1662357504,94026652588861,94027029051929)]
theorem point_links_checked12652 : (cuts12652.take 2).map (fun c => (1662255105-1+2*2^9*c.k,94025826776636+c.lower,94026203239097+c.upper)) = pointBounds12652 := by
 decide +kernel
def cuts12653 : List PrefixCut := [⟨23,184726594,184726730⟩,
⟨74,602087402,602087842⟩,
⟨125,1019773715,1019774461⟩,
⟨128,1044492478,1044493243⟩]
theorem checked12653 : checkPrefixCuts (2^48) 1662386177 9 Manual.Count131072.C012653.packed 128 cuts12653 = true := by
 decide +kernel
def pointBounds12653 : List (Nat × Nat × Nat) := [(1662409728,94027069624222,94027446087599),(1662461952,94027486985030,94027863448711),(1662514176,94027904671343,94028281135330)]
theorem point_links_checked12653 : (cuts12653.take 3).map (fun c => (1662386177-1+2*2^9*c.k,94026884897628+c.lower,94027261360869+c.upper)) = pointBounds12653 := by
 decide +kernel
def cuts12654 : List PrefixCut := [⟨48,385674404,385674692⟩,
⟨99,806720462,806721066⟩,
⟨128,1049658230,1049659009⟩]
theorem checked12654 : checkPrefixCuts (2^48) 1662517249 9 Manual.Count131072.C012654.packed 128 cuts12654 = true := by
 decide +kernel
def pointBounds12654 : List (Nat × Nat × Nat) := [(1662566400,94028315064510,94028691528804),(1662618624,94028736110568,94029112575178)]
theorem point_links_checked12654 : (cuts12654.take 2).map (fun c => (1662517249-1+2*2^9*c.k,94027929390106+c.lower,94028305854112+c.upper)) = pointBounds12654 := by
 decide +kernel
def cuts12655 : List PrefixCut := [⟨22,179788043,179788176⟩,
⟨73,595390438,595390883⟩,
⟨124,1014026924,1014027681⟩,
⟨128,1048898594,1048899377⟩]
theorem checked12655 : checkPrefixCuts (2^48) 1662648321 9 Manual.Count131072.C012655.packed 128 cuts12655 = true := by
 decide +kernel
def pointBounds12655 : List (Nat × Nat × Nat) := [(1662670848,94029158836379,94029535301297),(1662723072,94029574438774,94029950904004),(1662775296,94029993075260,94030369540802)]
theorem point_links_checked12655 : (cuts12655.take 3).map (fun c => (1662648321-1+2*2^9*c.k,94028979048336+c.lower,94029355513121+c.upper)) = pointBounds12655 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000082
