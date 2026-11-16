import PlattAssemblyKernel
import PlattCertificates.Count131072.C012592
import PlattCertificates.Count131072.C012593
import PlattCertificates.Count131072.C012594
import PlattCertificates.Count131072.C012595
import PlattCertificates.Count131072.C012596
import PlattCertificates.Count131072.C012597
import PlattCertificates.Count131072.C012598
import PlattCertificates.Count131072.C012599
import PlattCertificates.Count131072.C012600
import PlattCertificates.Count131072.C012601
import PlattCertificates.Count131072.C012602
import PlattCertificates.Count131072.C012603
import PlattCertificates.Count131072.C012604
import PlattCertificates.Count131072.C012605
import PlattCertificates.Count131072.C012606
import PlattCertificates.Count131072.C012607
import PlattCertificates.Count131072.C012608
import PlattCertificates.Count131072.C012609
import PlattCertificates.Count131072.C012610
import PlattCertificates.Count131072.C012611
import PlattCertificates.Count131072.C012612
import PlattCertificates.Count131072.C012613
import PlattCertificates.Count131072.C012614
import PlattCertificates.Count131072.C012615
import PlattCertificates.Count131072.C012616
import PlattCertificates.Count131072.C012617
import PlattCertificates.Count131072.C012618
import PlattCertificates.Count131072.C012619
import PlattCertificates.Count131072.C012620
import PlattCertificates.Count131072.C012621
import PlattCertificates.Count131072.C012622
import PlattCertificates.Count131072.C012623
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12592 : List PrefixCut := [⟨28,238361396,238361566⟩,
⟨79,654845648,654846125⟩,
⟨128,1055325008,1055325780⟩]
theorem checked12592 : checkPrefixCuts (2^48) 1654390785 9 Manual.Count131072.C012592.packed 128 cuts12592 = true := by
 decide +kernel
def pointBounds12592 : List (Nat × Nat × Nat) := [(1654419456,93963199188724,93963575604895),(1654471680,93963615672976,93963992089454)]
theorem point_links_checked12592 : (cuts12592.take 2).map (fun c => (1654390785-1+2*2^9*c.k,93962960827328+c.lower,93963337243329+c.upper)) = pointBounds12592 := by
 decide +kernel
def cuts12593 : List PrefixCut := [⟨2,17352698,17352712⟩,
⟨53,433300374,433300698⟩,
⟨104,848214210,848214842⟩,
⟨128,1052519238,1052520018⟩]
theorem checked12593 : checkPrefixCuts (2^48) 1654521857 9 Manual.Count131072.C012593.packed 128 cuts12593 = true := by
 decide +kernel
def pointBounds12593 : List (Nat × Nat × Nat) := [(1654523904,93964033505034,93964409921821),(1654576128,93964449452710,93964825869807),(1654628352,93964864366546,93965240783951)]
theorem point_links_checked12593 : (cuts12593.take 3).map (fun c => (1654521857-1+2*2^9*c.k,93964016152336+c.lower,93964392569109+c.upper)) = pointBounds12593 := by
 decide +kernel
def cuts12594 : List PrefixCut := [⟨27,222673603,222673770⟩,
⟨78,633138488,633138962⟩,
⟨128,1038317305,1038318080⟩]
theorem checked12594 : checkPrefixCuts (2^48) 1654652929 9 Manual.Count131072.C012594.packed 128 cuts12594 = true := by
 decide +kernel
def pointBounds12594 : List (Nat × Nat × Nat) := [(1654680576,93965291345177,93965667762897),(1654732800,93965701810062,93966078228089)]
theorem point_links_checked12594 : (cuts12594.take 2).map (fun c => (1654652929-1+2*2^9*c.k,93965068671574+c.lower,93965445089127+c.upper)) = pointBounds12594 := by
 decide +kernel
def cuts12595 : List PrefixCut := [⟨1,7654392,7654398⟩,
⟨52,424726961,424727279⟩,
⟨103,836173380,836174007⟩,
⟨128,1046228989,1046229771⟩]
theorem checked12595 : checkPrefixCuts (2^48) 1654784001 9 Manual.Count131072.C012595.packed 128 cuts12595 = true := by
 decide +kernel
def pointBounds12595 : List (Nat × Nat × Nat) := [(1654785024,93966114643271,93966491061605),(1654837248,93966531715840,93966908134486),(1654889472,93966943162259,93967319581214)]
theorem point_links_checked12595 : (cuts12595.take 3).map (fun c => (1654784001-1+2*2^9*c.k,93966106988879+c.lower,93966483407207+c.upper)) = pointBounds12595 := by
 decide +kernel
def cuts12596 : List PrefixCut := [⟨26,217706014,217706176⟩,
⟨77,636609862,636610332⟩,
⟨128,1064344450,1064345234⟩]
theorem checked12596 : checkPrefixCuts (2^48) 1654915073 9 Manual.Count131072.C012596.packed 128 cuts12596 = true := by
 decide +kernel
def pointBounds12596 : List (Nat × Nat × Nat) := [(1654941696,93967370923882,93967747343154),(1654993920,93967789827730,93968166247310),(1655046144,93968217562318,93968593982212)]
theorem point_links_checked12596 : (cuts12596.take 3).map (fun c => (1654915073-1+2*2^9*c.k,93967153217868+c.lower,93967529636978+c.upper)) = pointBounds12596 := by
 decide +kernel
def cuts12597 : List PrefixCut := [⟨51,420748299,420748610⟩,
⟨102,840973175,840973794⟩,
⟨128,1051335668,1051336443⟩]
theorem checked12597 : checkPrefixCuts (2^48) 1655046145 9 Manual.Count131072.C012597.packed 128 cuts12597 = true := by
 decide +kernel
def pointBounds12597 : List (Nat × Nat × Nat) := [(1655098368,93968638310617,93969014730822),(1655150592,93969058535493,93969434956006)]
theorem point_links_checked12597 : (cuts12597.take 2).map (fun c => (1655046145-1+2*2^9*c.k,93968217562318+c.lower,93968593982212+c.upper)) = pointBounds12597 := by
 decide +kernel
def cuts12598 : List PrefixCut := [⟨25,203386881,203387034⟩,
⟨76,629537035,629537499⟩,
⟨127,1055163645,1055164422⟩,
⟨128,1064686100,1064686883⟩]
theorem checked12598 : checkPrefixCuts (2^48) 1655177217 9 Manual.Count131072.C012598.packed 128 cuts12598 = true := by
 decide +kernel
def pointBounds12598 : List (Nat × Nat × Nat) := [(1655202816,93969472284867,93969848705689),(1655255040,93969898435021,93970274856154),(1655307264,93970324061631,93970700483077)]
theorem point_links_checked12598 : (cuts12598.take 3).map (fun c => (1655177217-1+2*2^9*c.k,93969268897986+c.lower,93969645318655+c.upper)) = pointBounds12598 := by
 decide +kernel
def cuts12599 : List PrefixCut := [⟨50,409459060,409459360⟩,
⟨101,818565288,818565895⟩,
⟨128,1036886032,1036886802⟩]
theorem checked12599 : checkPrefixCuts (2^48) 1655308289 9 Manual.Count131072.C012599.packed 128 cuts12599 = true := by
 decide +kernel
def pointBounds12599 : List (Nat × Nat × Nat) := [(1655359488,93970743043146,93971119464898),(1655411712,93971152149374,93971528571433)]
theorem point_links_checked12599 : (cuts12599.take 2).map (fun c => (1655308289-1+2*2^9*c.k,93970333584086+c.lower,93970710005538+c.upper)) = pointBounds12599 := by
 decide +kernel
def cuts12600 : List PrefixCut := [⟨24,188562261,188562403⟩,
⟨75,607164086,607164542⟩,
⟨126,1022522315,1022523080⟩,
⟨128,1040034061,1040034839⟩]
theorem checked12600 : checkPrefixCuts (2^48) 1655439361 9 Manual.Count131072.C012600.packed 128 cuts12600 = true := by
 decide +kernel
def pointBounds12600 : List (Nat × Nat × Nat) := [(1655463936,93971559032379,93971935454743),(1655516160,93971977634204,93972354056882),(1655568384,93972392992433,93972769415420)]
theorem point_links_checked12600 : (cuts12600.take 3).map (fun c => (1655439361-1+2*2^9*c.k,93971370470118+c.lower,93971746892340+c.upper)) = pointBounds12600 := by
 decide +kernel
def cuts12601 : List PrefixCut := [⟨49,399873538,399873833⟩,
⟨100,826936160,826936769⟩,
⟨128,1055762741,1055763520⟩]
theorem checked12601 : checkPrefixCuts (2^48) 1655570433 9 Manual.Count131072.C012601.packed 128 cuts12601 = true := by
 decide +kernel
def pointBounds12601 : List (Nat × Nat × Nat) := [(1655620608,93972810377717,93973186801012),(1655672832,93973237440339,93973613863948)]
theorem point_links_checked12601 : (cuts12601.take 2).map (fun c => (1655570433-1+2*2^9*c.k,93972410504179+c.lower,93972786927179+c.upper)) = pointBounds12601 := by
 decide +kernel
def cuts12602 : List PrefixCut := [⟨23,185302368,185302507⟩,
⟨74,597718167,597718610⟩,
⟨125,1021850554,1021851306⟩,
⟨128,1044969205,1044969976⟩]
theorem checked12602 : checkPrefixCuts (2^48) 1655701505 9 Manual.Count131072.C012602.packed 128 cuts12602 = true := by
 decide +kernel
def pointBounds12602 : List (Nat × Nat × Nat) := [(1655725056,93973651569288,93974027993206),(1655777280,93974063985087,93974440409309),(1655829504,93974488117474,93974864542005)]
theorem point_links_checked12602 : (cuts12602.take 3).map (fun c => (1655701505-1+2*2^9*c.k,93973466266920+c.lower,93973842690699+c.upper)) = pointBounds12602 := by
 decide +kernel
def cuts12603 : List PrefixCut := [⟨48,385021453,385021743⟩,
⟨99,795528453,795529047⟩,
⟨128,1032647748,1032648517⟩]
theorem checked12603 : checkPrefixCuts (2^48) 1655832577 9 Manual.Count131072.C012603.packed 128 cuts12603 = true := by
 decide +kernel
def pointBounds12603 : List (Nat × Nat × Nat) := [(1655881728,93974896257578,93975272682418),(1655933952,93975306764578,93975683189722)]
theorem point_links_checked12603 : (cuts12603.take 2).map (fun c => (1655832577-1+2*2^9*c.k,93974511236125+c.lower,93974887660675+c.upper)) = pointBounds12603 := by
 decide +kernel
def cuts12604 : List PrefixCut := [⟨22,180003840,180003975⟩,
⟨73,607652034,607652486⟩,
⟨124,1022369396,1022370153⟩,
⟨128,1056701971,1056702752⟩]
theorem checked12604 : checkPrefixCuts (2^48) 1655963649 9 Manual.Count131072.C012604.packed 128 cuts12604 = true := by
 decide +kernel
def pointBounds12604 : List (Nat × Nat × Nat) := [(1655986176,93975723887713,93976100313167),(1656038400,93976151535907,93976527961678),(1656090624,93976566253269,93976942679345)]
theorem point_links_checked12604 : (cuts12604.take 3).map (fun c => (1655963649-1+2*2^9*c.k,93975543883873+c.lower,93975920309192+c.upper)) = pointBounds12604 := by
 decide +kernel
def cuts12605 : List PrefixCut := [⟨47,382581154,382581440⟩,
⟨98,798122133,798122724⟩,
⟨128,1052369074,1052369851⟩]
theorem checked12605 : checkPrefixCuts (2^48) 1656094721 9 Manual.Count131072.C012605.packed 128 cuts12605 = true := by
 decide +kernel
def pointBounds12605 : List (Nat × Nat × Nat) := [(1656142848,93976983166998,93977359593384),(1656195072,93977398707977,93977775134668)]
theorem point_links_checked12605 : (cuts12605.take 2).map (fun c => (1656094721-1+2*2^9*c.k,93976600585844+c.lower,93976977011944+c.upper)) = pointBounds12605 := by
 decide +kernel
def cuts12606 : List PrefixCut := [⟨21,166549524,166549652⟩,
⟨72,592091029,592091474⟩,
⟨123,1006912908,1006913658⟩,
⟨128,1048717259,1048718043⟩]
theorem checked12606 : checkPrefixCuts (2^48) 1656225793 9 Manual.Count131072.C012606.packed 128 cuts12606 = true := by
 decide +kernel
def pointBounds12606 : List (Nat × Nat × Nat) := [(1656247296,93977819504442,93978195931447),(1656299520,93978245045947,93978621473269),(1656351744,93978659867826,93979036295453)]
theorem point_links_checked12606 : (cuts12606.take 3).map (fun c => (1656225793-1+2*2^9*c.k,93977652954918+c.lower,93978029381795+c.upper)) = pointBounds12606 := by
 decide +kernel
def cuts12607 : List PrefixCut := [⟨46,371984869,371985146⟩,
⟨97,788479952,788480540⟩,
⟨128,1048804026,1048804809⟩]
theorem checked12607 : checkPrefixCuts (2^48) 1656356865 9 Manual.Count131072.C012607.packed 128 cuts12607 = true := by
 decide +kernel
def pointBounds12607 : List (Nat × Nat × Nat) := [(1656403968,93979073657046,93979450084984),(1656456192,93979490152129,93979866580378)]
theorem point_links_checked12607 : (cuts12607.take 2).map (fun c => (1656356865-1+2*2^9*c.k,93978701672177+c.lower,93979078099838+c.upper)) = pointBounds12607 := by
 decide +kernel
def cuts12608 : List PrefixCut := [⟨20,163974384,163974506⟩,
⟨71,575685486,575685916⟩,
⟨122,997408360,997409108⟩,
⟨128,1047701588,1047702374⟩]
theorem checked12608 : checkPrefixCuts (2^48) 1656487937 9 Manual.Count131072.C012608.packed 128 cuts12608 = true := by
 decide +kernel
def pointBounds12608 : List (Nat × Nat × Nat) := [(1656508416,93979914450587,93980290879153),(1656560640,93980326161689,93980702590563),(1656612864,93980747884563,93981124313755)]
theorem point_links_checked12608 : (cuts12608.take 3).map (fun c => (1656487937-1+2*2^9*c.k,93979750476203+c.lower,93980126904647+c.upper)) = pointBounds12608 := by
 decide +kernel
def cuts12609 : List PrefixCut := [⟨45,376173830,376174110⟩,
⟨96,792603257,792603849⟩,
⟨128,1057473421,1057474213⟩]
theorem checked12609 : checkPrefixCuts (2^48) 1656619009 9 Manual.Count131072.C012609.packed 128 cuts12609 = true := by
 decide +kernel
def pointBounds12609 : List (Nat × Nat × Nat) := [(1656665088,93981174351621,93981550781131),(1656717312,93981590781048,93981967210870)]
theorem point_links_checked12609 : (cuts12609.take 2).map (fun c => (1656619009-1+2*2^9*c.k,93980798177791+c.lower,93981174607021+c.upper)) = pointBounds12609 := by
 decide +kernel
def cuts12610 : List PrefixCut := [⟨19,157322597,157322713⟩,
⟨70,574235435,574235860⟩,
⟨121,995891912,995892647⟩,
⟨128,1054331568,1054332346⟩]
theorem checked12610 : checkPrefixCuts (2^48) 1656750081 9 Manual.Count131072.C012610.packed 128 cuts12610 = true := by
 decide +kernel
def pointBounds12610 : List (Nat × Nat × Nat) := [(1656769536,93982012973809,93982389403947),(1656821760,93982429886647,93982806317094),(1656873984,93982851543124,93983227973881)]
theorem point_links_checked12610 : (cuts12610.take 3).map (fun c => (1656750081-1+2*2^9*c.k,93981855651212+c.lower,93982232081234+c.upper)) = pointBounds12610 := by
 decide +kernel
def cuts12611 : List PrefixCut := [⟨44,362014318,362014584⟩,
⟨95,784323701,784324274⟩,
⟨128,1055946860,1055947635⟩]
theorem checked12611 : checkPrefixCuts (2^48) 1656881153 9 Manual.Count131072.C012611.packed 128 cuts12611 = true := by
 decide +kernel
def pointBounds12611 : List (Nat × Nat × Nat) := [(1656926208,93983271997098,93983648428164),(1656978432,93983694306481,93984070737854)]
theorem point_links_checked12611 : (cuts12611.take 2).map (fun c => (1656881153-1+2*2^9*c.k,93982909982780+c.lower,93983286413580+c.upper)) = pointBounds12611 := by
 decide +kernel
def cuts12612 : List PrefixCut := [⟨18,145067254,145067362⟩,
⟨69,560895154,560895568⟩,
⟨120,976879937,976880658⟩,
⟨128,1045162008,1045162778⟩]
theorem checked12612 : checkPrefixCuts (2^48) 1657012225 9 Manual.Count131072.C012612.packed 128 cuts12612 = true := by
 decide +kernel
def pointBounds12612 : List (Nat × Nat × Nat) := [(1657030656,93984110996894,93984487428577),(1657082880,93984526824794,93984903256783),(1657135104,93984942809577,93985319241873)]
theorem point_links_checked12612 : (cuts12612.take 3).map (fun c => (1657012225-1+2*2^9*c.k,93983965929640+c.lower,93984342361215+c.upper)) = pointBounds12612 := by
 decide +kernel
def cuts12613 : List PrefixCut := [⟨43,356352031,356352296⟩,
⟨94,774348631,774349206⟩,
⟨128,1046948006,1046948783⟩]
theorem checked12613 : checkPrefixCuts (2^48) 1657143297 9 Manual.Count131072.C012613.packed 128 cuts12613 = true := by
 decide +kernel
def pointBounds12613 : List (Nat × Nat × Nat) := [(1657187328,93985367443679,93985743876289),(1657239552,93985785440279,93986161873199)]
theorem point_links_checked12613 : (cuts12613.take 2).map (fun c => (1657143297-1+2*2^9*c.k,93985011091648+c.lower,93985387523993+c.upper)) = pointBounds12613 := by
 decide +kernel
def cuts12614 : List PrefixCut := [⟨17,140118941,140119045⟩,
⟨68,550786295,550786707⟩,
⟨119,970441860,970442580⟩,
⟨128,1047544271,1047545049⟩]
theorem checked12614 : checkPrefixCuts (2^48) 1657274369 9 Manual.Count131072.C012614.packed 128 cuts12614 = true := by
 decide +kernel
def pointBounds12614 : List (Nat × Nat × Nat) := [(1657291776,93986198158595,93986574591821),(1657344000,93986608825949,93986985259483),(1657396224,93987028481514,93987404915356)]
theorem point_links_checked12614 : (cuts12614.take 3).map (fun c => (1657274369-1+2*2^9*c.k,93986058039654+c.lower,93986434472776+c.upper)) = pointBounds12614 := by
 decide +kernel
def cuts12615 : List PrefixCut := [⟨42,349672510,349672769⟩,
⟨93,766754156,766754723⟩,
⟨128,1056461943,1056462725⟩]
theorem checked12615 : checkPrefixCuts (2^48) 1657405441 9 Manual.Count131072.C012615.packed 128 cuts12615 = true := by
 decide +kernel
def pointBounds12615 : List (Nat × Nat × Nat) := [(1657448448,93987455256435,93987831690594),(1657500672,93987872338081,93988248772548)]
theorem point_links_checked12615 : (cuts12615.take 2).map (fun c => (1657405441-1+2*2^9*c.k,93987105583925+c.lower,93987482017825+c.upper)) = pointBounds12615 := by
 decide +kernel
def cuts12616 : List PrefixCut := [⟨16,129058903,129058996⟩,
⟨67,542378595,542378991⟩,
⟨118,958062375,958063080⟩,
⟨128,1036680829,1036681592⟩]
theorem checked12616 : checkPrefixCuts (2^48) 1657536513 9 Manual.Count131072.C012616.packed 128 cuts12616 = true := by
 decide +kernel
def pointBounds12616 : List (Nat × Nat × Nat) := [(1657552896,93988291104771,93988667539546),(1657605120,93988704424463,93989080859541),(1657657344,93989120108243,93989496543630)]
theorem point_links_checked12616 : (cuts12616.take 3).map (fun c => (1657536513-1+2*2^9*c.k,93988162045868+c.lower,93988538480550+c.upper)) = pointBounds12616 := by
 decide +kernel
def cuts12617 : List PrefixCut := [⟨41,340448259,340448509⟩,
⟨92,758313200,758313758⟩,
⟨128,1051031557,1051032332⟩]
theorem checked12617 : checkPrefixCuts (2^48) 1657667585 9 Manual.Count131072.C012617.packed 128 cuts12617 = true := by
 decide +kernel
def pointBounds12617 : List (Nat × Nat × Nat) := [(1657709568,93989539174956,93989915610651),(1657761792,93989957039897,93990333475900)]
theorem point_links_checked12617 : (cuts12617.take 2).map (fun c => (1657667585-1+2*2^9*c.k,93989198726697+c.lower,93989575162142+c.upper)) = pointBounds12617 := by
 decide +kernel
def cuts12618 : List PrefixCut := [⟨15,123605340,123605432⟩,
⟨66,546197919,546198324⟩,
⟨117,962325595,962326306⟩,
⟨128,1053664814,1053665591⟩]
theorem checked12618 : checkPrefixCuts (2^48) 1657798657 9 Manual.Count131072.C012618.packed 128 cuts12618 = true := by
 decide +kernel
def pointBounds12618 : List (Nat × Nat × Nat) := [(1657814016,93990373363594,93990749799906),(1657866240,93990795956173,93991172392798),(1657918464,93991212083849,93991588520780)]
theorem point_links_checked12618 : (cuts12618.take 3).map (fun c => (1657798657-1+2*2^9*c.k,93990249758254+c.lower,93990626194474+c.upper)) = pointBounds12618 := by
 decide +kernel
def cuts12619 : List PrefixCut := [⟨40,330717424,330717669⟩,
⟨91,743253802,743254348⟩,
⟨128,1034567851,1034568615⟩]
theorem checked12619 : checkPrefixCuts (2^48) 1657929729 9 Manual.Count131072.C012619.packed 128 cuts12619 = true := by
 decide +kernel
def pointBounds12619 : List (Nat × Nat × Nat) := [(1657970688,93991634140492,93992010577734),(1658022912,93992046676870,93992423114413)]
theorem point_links_checked12619 : (cuts12619.take 2).map (fun c => (1657929729-1+2*2^9*c.k,93991303423068+c.lower,93991679860065+c.upper)) = pointBounds12619 := by
 decide +kernel
def cuts12620 : List PrefixCut := [⟨14,114758280,114758363⟩,
⟨65,534059023,534059415⟩,
⟨116,958948297,958949001⟩,
⟨128,1051461348,1051462121⟩]
theorem checked12620 : checkPrefixCuts (2^48) 1658060801 9 Manual.Count131072.C012620.packed 128 cuts12620 = true := by
 decide +kernel
def pointBounds12620 : List (Nat × Nat × Nat) := [(1658075136,93992452749199,93992829187043),(1658127360,93992872049942,93993248488095),(1658179584,93993296939216,93993673377681)]
theorem point_links_checked12620 : (cuts12620.take 3).map (fun c => (1658060801-1+2*2^9*c.k,93992337990919+c.lower,93992714428680+c.upper)) = pointBounds12620 := by
 decide +kernel
def cuts12621 : List PrefixCut := [⟨39,323026667,323026907⟩,
⟨90,736686251,736686798⟩,
⟨128,1040005611,1040006384⟩]
theorem checked12621 : checkPrefixCuts (2^48) 1658191873 9 Manual.Count131072.C012621.packed 128 cuts12621 = true := by
 decide +kernel
def pointBounds12621 : List (Nat × Nat × Nat) := [(1658231808,93993712478934,93994088917708),(1658284032,93994126138518,93994502577599)]
theorem point_links_checked12621 : (cuts12621.take 2).map (fun c => (1658191873-1+2*2^9*c.k,93993389452267+c.lower,93993765890801+c.upper)) = pointBounds12621 := by
 decide +kernel
def cuts12622 : List PrefixCut := [⟨13,108290274,108290354⟩,
⟨64,530410375,530410768⟩,
⟨115,963040147,963040859⟩,
⟨128,1070474115,1070474906⟩]
theorem checked12622 : checkPrefixCuts (2^48) 1658322945 9 Manual.Count131072.C012622.packed 128 cuts12622 = true := by
 decide +kernel
def pointBounds12622 : List (Nat × Nat × Nat) := [(1658336256,93994537748152,93994914187539),(1658388480,93994959868253,93995336307953),(1658440704,93995392498025,93995768938044)]
theorem point_links_checked12622 : (cuts12622.take 3).map (fun c => (1658322945-1+2*2^9*c.k,93994429457878+c.lower,93994805897185+c.upper)) = pointBounds12622 := by
 decide +kernel
def cuts12623 : List PrefixCut := [⟨38,316696088,316696317⟩,
⟨89,734872833,734873371⟩,
⟨128,1053418289,1053419062⟩]
theorem checked12623 : checkPrefixCuts (2^48) 1658454017 9 Manual.Count131072.C012623.packed 128 cuts12623 = true := by
 decide +kernel
def pointBounds12623 : List (Nat × Nat × Nat) := [(1658492928,93995816628081,93996193068408),(1658545152,93996234804826,93996611245462)]
theorem point_links_checked12623 : (cuts12623.take 2).map (fun c => (1658454017-1+2*2^9*c.k,93995499931993+c.lower,93995876372091+c.upper)) = pointBounds12623 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000081
