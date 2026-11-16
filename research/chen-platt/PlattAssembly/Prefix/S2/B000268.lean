import PlattAssemblyKernel
import PlattCertificates.Count131072.C018576
import PlattCertificates.Count131072.C018577
import PlattCertificates.Count131072.C018578
import PlattCertificates.Count131072.C018579
import PlattCertificates.Count131072.C018580
import PlattCertificates.Count131072.C018581
import PlattCertificates.Count131072.C018582
import PlattCertificates.Count131072.C018583
import PlattCertificates.Count131072.C018584
import PlattCertificates.Count131072.C018585
import PlattCertificates.Count131072.C018586
import PlattCertificates.Count131072.C018587
import PlattCertificates.Count131072.C018588
import PlattCertificates.Count131072.C018589
import PlattCertificates.Count131072.C018590
import PlattCertificates.Count131072.C018591
import PlattCertificates.Count131072.C018592
import PlattCertificates.Count131072.C018593
import PlattCertificates.Count131072.C018594
import PlattCertificates.Count131072.C018595
import PlattCertificates.Count131072.C018596
import PlattCertificates.Count131072.C018597
import PlattCertificates.Count131072.C018598
import PlattCertificates.Count131072.C018599
import PlattCertificates.Count131072.C018600
import PlattCertificates.Count131072.C018601
import PlattCertificates.Count131072.C018602
import PlattCertificates.Count131072.C018603
import PlattCertificates.Count131072.C018604
import PlattCertificates.Count131072.C018605
import PlattCertificates.Count131072.C018606
import PlattCertificates.Count131072.C018607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000268
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18576 : List PrefixCut := [⟨24,132269342,132269420⟩,
⟨99,534147392,534147714⟩,
⟨128,693764062,693764478⟩]
theorem checked18576 : checkPrefixCuts (2^48) 2438725633 9 Manual.Count131072.C018576.packed 128 cuts18576 = true := by
 decide +kernel
def pointBounds18576 : List (Nat × Nat × Nat) := [(2438750208,99062157772073,99062537571185),(2438827008,99062559650123,99062939449479)]
theorem point_links_checked18576 : (cuts18576.take 2).map (fun c => (2438725633-1+2*2^9*c.k,99062025502731+c.lower,99062405301765+c.upper)) = pointBounds18576 := by
 decide +kernel
def cuts18577 : List PrefixCut := [⟨46,254482388,254482547⟩,
⟨121,661759315,661759719⟩,
⟨128,702613255,702613683⟩]
theorem checked18577 : checkPrefixCuts (2^48) 2438856705 9 Manual.Count131072.C018577.packed 128 cuts18577 = true := by
 decide +kernel
def pointBounds18577 : List (Nat × Nat × Nat) := [(2438903808,99062973749181,99063353548790),(2438980608,99063381026108,99063760825962)]
theorem point_links_checked18577 : (cuts18577.take 2).map (fun c => (2438856705-1+2*2^9*c.k,99062719266793+c.lower,99063099066243+c.upper)) = pointBounds18577 := by
 decide +kernel
def cuts18578 : List PrefixCut := [⟨68,370564751,370564977⟩,
⟨128,702575433,702575859⟩]
theorem checked18578 : checkPrefixCuts (2^48) 2438987777 9 Manual.Count131072.C018578.packed 128 cuts18578 = true := by
 decide +kernel
def pointBounds18578 : List (Nat × Nat × Nat) := [(2439057408,99063792444799,99064172244903)]
theorem point_links_checked18578 : (cuts18578.take 1).map (fun c => (2438987777-1+2*2^9*c.k,99063421880048+c.lower,99063801679926+c.upper)) = pointBounds18578 := by
 decide +kernel
def cuts18579 : List PrefixCut := [⟨15,80779911,80779959⟩,
⟨90,499442801,499443096⟩,
⟨128,702307156,702307572⟩]
theorem checked18579 : checkPrefixCuts (2^48) 2439118849 9 Manual.Count131072.C018579.packed 128 cuts18579 = true := by
 decide +kernel
def pointBounds18579 : List (Nat × Nat × Nat) := [(2439134208,99064205235392,99064585035744),(2439211008,99064623898282,99065003698881)]
theorem point_links_checked18579 : (cuts18579.take 2).map (fun c => (2439118849-1+2*2^9*c.k,99064124455481+c.lower,99064504255785+c.upper)) = pointBounds18579 := by
 decide +kernel
def cuts18580 : List PrefixCut := [⟨37,201707192,201707313⟩,
⟨112,622766831,622767201⟩,
⟨128,707577177,707577599⟩]
theorem checked18580 : checkPrefixCuts (2^48) 2439249921 9 Manual.Count131072.C018580.packed 128 cuts18580 = true := by
 decide +kernel
def pointBounds18580 : List (Nat × Nat × Nat) := [(2439287808,99065028469829,99065408270670),(2439364608,99065449529468,99065829330558)]
theorem point_links_checked18580 : (cuts18580.take 2).map (fun c => (2439249921-1+2*2^9*c.k,99064826762637+c.lower,99065206563357+c.upper)) = pointBounds18580 := by
 decide +kernel
def cuts18581 : List PrefixCut := [⟨59,323081939,323082130⟩,
⟨128,702577689,702578111⟩]
theorem checked18581 : checkPrefixCuts (2^48) 2439380993 9 Manual.Count131072.C018581.packed 128 cuts18581 = true := by
 decide +kernel
def pointBounds18581 : List (Nat × Nat × Nat) := [(2439441408,99065857421753,99066237223086)]
theorem point_links_checked18581 : (cuts18581.take 1).map (fun c => (2439380993-1+2*2^9*c.k,99065534339814+c.lower,99065914140956+c.upper)) = pointBounds18581 := by
 decide +kernel
def cuts18582 : List PrefixCut := [⟨6,32537581,32537599⟩,
⟨81,435673651,435673909⟩,
⟨128,687656097,687656508⟩]
theorem checked18582 : checkPrefixCuts (2^48) 2439512065 9 Manual.Count131072.C018582.packed 128 cuts18582 = true := by
 decide +kernel
def pointBounds18582 : List (Nat × Nat × Nat) := [(2439518208,99066269455084,99066649256666),(2439595008,99066672591154,99067052392976)]
theorem point_links_checked18582 : (cuts18582.take 2).map (fun c => (2439512065-1+2*2^9*c.k,99066236917503+c.lower,99066616719067+c.upper)) = pointBounds18582 := by
 decide +kernel
def cuts18583 : List PrefixCut := [⟨28,155640548,155640642⟩,
⟨103,564173786,564174121⟩,
⟨128,699271864,699272281⟩]
theorem checked18583 : checkPrefixCuts (2^48) 2439643137 9 Manual.Count131072.C018583.packed 128 cuts18583 = true := by
 decide +kernel
def pointBounds18583 : List (Nat × Nat × Nat) := [(2439671808,99067080214148,99067460016217),(2439748608,99067488747386,99067868549696)]
theorem point_links_checked18583 : (cuts18583.take 2).map (fun c => (2439643137-1+2*2^9*c.k,99066924573600+c.lower,99067304375575+c.upper)) = pointBounds18583 := by
 decide +kernel
def cuts18584 : List PrefixCut := [⟨50,279305965,279306133⟩,
⟨125,695312159,695312576⟩,
⟨128,710078638,710079064⟩]
theorem checked18584 : checkPrefixCuts (2^48) 2439774209 9 Manual.Count131072.C018584.packed 128 cuts18584 = true := by
 decide +kernel
def pointBounds18584 : List (Nat × Nat × Nat) := [(2439825408,99067903151429,99068282953989),(2439902208,99068319157623,99068698960432)]
theorem point_links_checked18584 : (cuts18584.take 2).map (fun c => (2439774209-1+2*2^9*c.k,99067623845464+c.lower,99068003647856+c.upper)) = pointBounds18584 := by
 decide +kernel
def cuts18585 : List PrefixCut := [⟨72,396266070,396266313⟩,
⟨128,712347606,712348042⟩]
theorem checked18585 : checkPrefixCuts (2^48) 2439905281 9 Manual.Count131072.C018585.packed 128 cuts18585 = true := by
 decide +kernel
def pointBounds18585 : List (Nat × Nat × Nat) := [(2439979008,99068730190172,99069109993233)]
theorem point_links_checked18585 : (cuts18585.take 1).map (fun c => (2439905281-1+2*2^9*c.k,99068333924102+c.lower,99068713726920+c.upper)) = pointBounds18585 := by
 decide +kernel
def cuts18586 : List PrefixCut := [⟨19,103936103,103936165⟩,
⟨94,511366787,511367085⟩,
⟨128,702273457,702273868⟩]
theorem checked18586 : checkPrefixCuts (2^48) 2440036353 9 Manual.Count131072.C018586.packed 128 cuts18586 = true := by
 decide +kernel
def pointBounds18586 : List (Nat × Nat × Nat) := [(2440055808,99069150207811,99069530011127),(2440132608,99069557638495,99069937442047)]
theorem point_links_checked18586 : (cuts18586.take 2).map (fun c => (2440036353-1+2*2^9*c.k,99069046271708+c.lower,99069426074962+c.upper)) = pointBounds18586 := by
 decide +kernel
def cuts18587 : List PrefixCut := [⟨41,223201596,223201737⟩,
⟨116,635681914,635682301⟩,
⟨128,701659105,701659533⟩]
theorem checked18587 : checkPrefixCuts (2^48) 2440167425 9 Manual.Count131072.C018587.packed 128 cuts18587 = true := by
 decide +kernel
def pointBounds18587 : List (Nat × Nat × Nat) := [(2440209408,99069971746761,99070351550567),(2440286208,99070384227079,99070764031131)]
theorem point_links_checked18587 : (cuts18587.take 2).map (fun c => (2440167425-1+2*2^9*c.k,99069748545165+c.lower,99070128348830+c.upper)) = pointBounds18587 := by
 decide +kernel
def cuts18588 : List PrefixCut := [⟨63,348681645,348681850⟩,
⟨128,701275472,701275890⟩]
theorem checked18588 : checkPrefixCuts (2^48) 2440298497 9 Manual.Count131072.C018588.packed 128 cuts18588 = true := by
 decide +kernel
def pointBounds18588 : List (Nat × Nat × Nat) := [(2440363008,99070798885915,99071178690213)]
theorem point_links_checked18588 : (cuts18588.take 1).map (fun c => (2440298497-1+2*2^9*c.k,99070450204270+c.lower,99070830008363+c.upper)) = pointBounds18588 := by
 decide +kernel
def cuts18589 : List PrefixCut := [⟨10,53401500,53401533⟩,
⟨85,461114063,461114348⟩,
⟨128,698238943,698239371⟩]
theorem checked18589 : checkPrefixCuts (2^48) 2440429569 9 Manual.Count131072.C018589.packed 128 cuts18589 = true := by
 decide +kernel
def pointBounds18589 : List (Nat × Nat × Nat) := [(2440439808,99071204881242,99071584685786),(2440516608,99071612593805,99071992398601)]
theorem point_links_checked18589 : (cuts18589.take 2).map (fun c => (2440429569-1+2*2^9*c.k,99071151479742+c.lower,99071531284253+c.upper)) = pointBounds18589 := by
 decide +kernel
def cuts18590 : List PrefixCut := [⟨32,173342922,173343025⟩,
⟨107,576647346,576647693⟩,
⟨128,687014690,687015105⟩]
theorem checked18590 : checkPrefixCuts (2^48) 2440560641 9 Manual.Count131072.C018590.packed 128 cuts18590 = true := by
 decide +kernel
def pointBounds18590 : List (Nat × Nat × Nat) := [(2440593408,99072023061607,99072402866649),(2440670208,99072426366031,99072806171317)]
theorem point_links_checked18590 : (cuts18590.take 2).map (fun c => (2440560641-1+2*2^9*c.k,99071849718685+c.lower,99072229523624+c.upper)) = pointBounds18590 := by
 decide +kernel
def cuts18591 : List PrefixCut := [⟨54,297306762,297306940⟩,
⟨128,697818150,697818570⟩]
theorem checked18591 : checkPrefixCuts (2^48) 2440691713 9 Manual.Count131072.C018591.packed 128 cuts18591 = true := by
 decide +kernel
def pointBounds18591 : List (Nat × Nat × Nat) := [(2440747008,99072834040137,99073213845669)]
theorem point_links_checked18591 : (cuts18591.take 1).map (fun c => (2440691713-1+2*2^9*c.k,99072536733375+c.lower,99072916538729+c.upper)) = pointBounds18591 := by
 decide +kernel
def cuts18592 : List PrefixCut := [⟨1,6573220,6573224⟩,
⟨76,411684699,411684949⟩,
⟨128,696512123,696512546⟩]
theorem checked18592 : checkPrefixCuts (2^48) 2440822785 9 Manual.Count131072.C018592.packed 128 cuts18592 = true := by
 decide +kernel
def pointBounds18592 : List (Nat × Nat × Nat) := [(2440823808,99073241124745,99073620930523),(2440900608,99073646236224,99074026042248)]
theorem point_links_checked18592 : (cuts18592.take 2).map (fun c => (2440822785-1+2*2^9*c.k,99073234551525+c.lower,99073614357299+c.upper)) = pointBounds18592 := by
 decide +kernel
def cuts18593 : List PrefixCut := [⟨23,127190160,127190238⟩,
⟨98,543807269,543807597⟩,
⟨128,707890577,707891003⟩]
theorem checked18593 : checkPrefixCuts (2^48) 2440953857 9 Manual.Count131072.C018593.packed 128 cuts18593 = true := by
 decide +kernel
def pointBounds18593 : List (Nat × Nat × Nat) := [(2440977408,99074058253808,99074438060083),(2441054208,99074474870917,99074854677442)]
theorem point_links_checked18593 : (cuts18593.take 2).map (fun c => (2440953857-1+2*2^9*c.k,99073931063648+c.lower,99074310869845+c.upper)) = pointBounds18593 := by
 decide +kernel
def cuts18594 : List PrefixCut := [⟨45,244679765,244679919⟩,
⟨120,654237085,654237492⟩,
⟨128,695745552,695745983⟩]
theorem checked18594 : checkPrefixCuts (2^48) 2441084929 9 Manual.Count131072.C018594.packed 128 cuts18594 = true := by
 decide +kernel
def pointBounds18594 : List (Nat × Nat × Nat) := [(2441131008,99074883633990,99075263440767),(2441207808,99075293191310,99075672998340)]
theorem point_links_checked18594 : (cuts18594.take 2).map (fun c => (2441084929-1+2*2^9*c.k,99074638954225+c.lower,99075018760848+c.upper)) = pointBounds18594 := by
 decide +kernel
def cuts18595 : List PrefixCut := [⟨67,369419531,369419753⟩,
⟨128,699397774,699398198⟩]
theorem checked18595 : checkPrefixCuts (2^48) 2441216001 9 Manual.Count131072.C018595.packed 128 cuts18595 = true := by
 decide +kernel
def pointBounds18595 : List (Nat × Nat × Nat) := [(2441284608,99075704119308,99076083926584)]
theorem point_links_checked18595 : (cuts18595.take 1).map (fun c => (2441216001-1+2*2^9*c.k,99075334699777+c.lower,99075714506831+c.upper)) = pointBounds18595 := by
 decide +kernel
def cuts18596 : List PrefixCut := [⟨14,75979131,75979177⟩,
⟨89,493568308,493568602⟩,
⟨128,701320315,701320734⟩]
theorem checked18596 : checkPrefixCuts (2^48) 2441347073 9 Manual.Count131072.C018596.packed 128 cuts18596 = true := by
 decide +kernel
def pointBounds18596 : List (Nat × Nat × Nat) := [(2441361408,99076110076682,99076489884206),(2441438208,99076527665859,99076907473631)]
theorem point_links_checked18596 : (cuts18596.take 2).map (fun c => (2441347073-1+2*2^9*c.k,99076034097551+c.lower,99076413905029+c.upper)) = pointBounds18596 := by
 decide +kernel
def cuts18597 : List PrefixCut := [⟨36,197142224,197142344⟩,
⟨111,599026291,599026657⟩,
⟨128,692405473,692405894⟩]
theorem checked18597 : checkPrefixCuts (2^48) 2441478145 9 Manual.Count131072.C018597.packed 128 cuts18597 = true := by
 decide +kernel
def pointBounds18597 : List (Nat × Nat × Nat) := [(2441515008,99076932560090,99077312368107),(2441591808,99077334444157,99077714252420)]
theorem point_links_checked18597 : (cuts18597.take 2).map (fun c => (2441478145-1+2*2^9*c.k,99076735417866+c.lower,99077115225763+c.upper)) = pointBounds18597 := by
 decide +kernel
def cuts18598 : List PrefixCut := [⟨58,318521774,318521968⟩,
⟨128,707700429,707700864⟩]
theorem checked18598 : checkPrefixCuts (2^48) 2441609217 9 Manual.Count131072.C018598.packed 128 cuts18598 = true := by
 decide +kernel
def pointBounds18598 : List (Nat × Nat × Nat) := [(2441668608,99077746345113,99078126153625)]
theorem point_links_checked18598 : (cuts18598.take 1).map (fun c => (2441609217-1+2*2^9*c.k,99077427823339+c.lower,99077807631657+c.upper)) = pointBounds18598 := by
 decide +kernel
def cuts18599 : List PrefixCut := [⟨5,26974636,26974653⟩,
⟨80,440348239,440348503⟩,
⟨128,700746113,700746531⟩]
theorem checked18599 : checkPrefixCuts (2^48) 2441740289 9 Manual.Count131072.C018599.packed 128 cuts18599 = true := by
 decide +kernel
def pointBounds18599 : List (Nat × Nat × Nat) := [(2441745408,99078162498404,99078542307174),(2441822208,99078575872007,99078955681024)]
theorem point_links_checked18599 : (cuts18599.take 2).map (fun c => (2441740289-1+2*2^9*c.k,99078135523768+c.lower,99078515332521+c.upper)) = pointBounds18599 := by
 decide +kernel
def cuts18600 : List PrefixCut := [⟨27,146853337,146853427⟩,
⟨102,555013876,555014221⟩,
⟨128,696789347,696789777⟩]
theorem checked18600 : checkPrefixCuts (2^48) 2441871361 9 Manual.Count131072.C018600.packed 128 cuts18600 = true := by
 decide +kernel
def pointBounds18600 : List (Nat × Nat × Nat) := [(2441899008,99078983123218,99079362932479),(2441975808,99079391283757,99079771093273)]
theorem point_links_checked18600 : (cuts18600.take 2).map (fun c => (2441871361-1+2*2^9*c.k,99078836269881+c.lower,99079216079052+c.upper)) = pointBounds18600 := by
 decide +kernel
def cuts18601 : List PrefixCut := [⟨49,268792797,268792958⟩,
⟨124,677734459,677734866⟩,
⟨128,698480877,698481297⟩]
theorem checked18601 : checkPrefixCuts (2^48) 2442002433 9 Manual.Count131072.C018601.packed 128 cuts18601 = true := by
 decide +kernel
def pointBounds18601 : List (Nat × Nat × Nat) := [(2442052608,99079801852025,99080181661787),(2442129408,99080210793687,99080590603695)]
theorem point_links_checked18601 : (cuts18601.take 2).map (fun c => (2442002433-1+2*2^9*c.k,99079533059228+c.lower,99079912868829+c.upper)) = pointBounds18601 := by
 decide +kernel
def cuts18602 : List PrefixCut := [⟨71,386453570,386453802⟩,
⟨128,702016181,702016599⟩]
theorem checked18602 : checkPrefixCuts (2^48) 2442133505 9 Manual.Count131072.C018602.packed 128 cuts18602 = true := by
 decide +kernel
def pointBounds18602 : List (Nat × Nat × Nat) := [(2442206208,99080617993675,99080997803928)]
theorem point_links_checked18602 : (cuts18602.take 1).map (fun c => (2442133505-1+2*2^9*c.k,99080231540105+c.lower,99080611350126+c.upper)) = pointBounds18602 := by
 decide +kernel
def cuts18603 : List PrefixCut := [⟨18,93583947,93584002⟩,
⟨93,504446318,504446616⟩,
⟨128,697829558,697829971⟩]
theorem checked18603 : checkPrefixCuts (2^48) 2442264577 9 Manual.Count131072.C018603.packed 128 cuts18603 = true := by
 decide +kernel
def pointBounds18603 : List (Nat × Nat × Nat) := [(2442283008,99081027140233,99081406950727),(2442359808,99081438002604,99081817813341)]
theorem point_links_checked18603 : (cuts18603.take 2).map (fun c => (2442264577-1+2*2^9*c.k,99080933556286+c.lower,99081313366725+c.upper)) = pointBounds18603 := by
 decide +kernel
def cuts18604 : List PrefixCut := [⟨40,219540660,219540792⟩,
⟨115,631760124,631760496⟩,
⟨128,705052474,705052891⟩]
theorem checked18604 : checkPrefixCuts (2^48) 2442395649 9 Manual.Count131072.C018604.packed 128 cuts18604 = true := by
 decide +kernel
def pointBounds18604 : List (Nat × Nat × Nat) := [(2442436608,99081850926504,99082230737488),(2442513408,99082263145968,99082642957192)]
theorem point_links_checked18604 : (cuts18604.take 2).map (fun c => (2442395649-1+2*2^9*c.k,99081631385844+c.lower,99082011196696+c.upper)) = pointBounds18604 := by
 decide +kernel
def cuts18605 : List PrefixCut := [⟨62,338568491,338568698⟩,
⟨128,691647392,691647811⟩]
theorem checked18605 : checkPrefixCuts (2^48) 2442526721 9 Manual.Count131072.C018605.packed 128 cuts18605 = true := by
 decide +kernel
def pointBounds18605 : List (Nat × Nat × Nat) := [(2442590208,99082675006809,99083054818285)]
theorem point_links_checked18605 : (cuts18605.take 1).map (fun c => (2442526721-1+2*2^9*c.k,99082336438318+c.lower,99082716249587+c.upper)) = pointBounds18605 := by
 decide +kernel
def cuts18606 : List PrefixCut := [⟨9,49434884,49434914⟩,
⟨84,457351875,457352152⟩,
⟨128,693799574,693799990⟩]
theorem checked18606 : checkPrefixCuts (2^48) 2442657793 9 Manual.Count131072.C018606.packed 128 cuts18606 = true := by
 decide +kernel
def pointBounds18606 : List (Nat × Nat × Nat) := [(2442667008,99083077520594,99083457332312),(2442743808,99083485437585,99083865249550)]
theorem point_links_checked18606 : (cuts18606.take 2).map (fun c => (2442657793-1+2*2^9*c.k,99083028085710+c.lower,99083407897398+c.upper)) = pointBounds18606 := by
 decide +kernel
def cuts18607 : List PrefixCut := [⟨31,172608710,172608815⟩,
⟨106,580269609,580269964⟩,
⟨128,705860729,705861159⟩]
theorem checked18607 : checkPrefixCuts (2^48) 2442788865 9 Manual.Count131072.C018607.packed 128 cuts18607 = true := by
 decide +kernel
def pointBounds18607 : List (Nat × Nat × Nat) := [(2442820608,99083894493994,99084274306203),(2442897408,99084302154893,99084681967352)]
theorem point_links_checked18607 : (cuts18607.take 2).map (fun c => (2442788865-1+2*2^9*c.k,99083721885284+c.lower,99084101697388+c.upper)) = pointBounds18607 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000268
