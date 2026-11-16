import PlattAssemblyKernel
import PlattCertificates.Count131072.C017552
import PlattCertificates.Count131072.C017553
import PlattCertificates.Count131072.C017554
import PlattCertificates.Count131072.C017555
import PlattCertificates.Count131072.C017556
import PlattCertificates.Count131072.C017557
import PlattCertificates.Count131072.C017558
import PlattCertificates.Count131072.C017559
import PlattCertificates.Count131072.C017560
import PlattCertificates.Count131072.C017561
import PlattCertificates.Count131072.C017562
import PlattCertificates.Count131072.C017563
import PlattCertificates.Count131072.C017564
import PlattCertificates.Count131072.C017565
import PlattCertificates.Count131072.C017566
import PlattCertificates.Count131072.C017567
import PlattCertificates.Count131072.C017568
import PlattCertificates.Count131072.C017569
import PlattCertificates.Count131072.C017570
import PlattCertificates.Count131072.C017571
import PlattCertificates.Count131072.C017572
import PlattCertificates.Count131072.C017573
import PlattCertificates.Count131072.C017574
import PlattCertificates.Count131072.C017575
import PlattCertificates.Count131072.C017576
import PlattCertificates.Count131072.C017577
import PlattCertificates.Count131072.C017578
import PlattCertificates.Count131072.C017579
import PlattCertificates.Count131072.C017580
import PlattCertificates.Count131072.C017581
import PlattCertificates.Count131072.C017582
import PlattCertificates.Count131072.C017583
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000236
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17552 : List PrefixCut := [⟨27,155362426,155362518⟩,
⟨98,565500611,565500952⟩,
⟨128,740153471,740153922⟩]
theorem checked17552 : checkPrefixCuts (2^48) 2304507905 9 Manual.Count131072.C017552.packed 128 cuts17552 = true := by
 decide +kernel
def pointBounds17552 : List (Nat × Nat × Nat) := [(2304535552,98324164185412,98324543534638),(2304608256,98324574323597,98324953673072)]
theorem point_links_checked17552 : (cuts17552.take 2).map (fun c => (2304507905-1+2*2^9*c.k,98324008822986+c.lower,98324388172120+c.upper)) = pointBounds17552 := by
 decide +kernel
def cuts17553 : List PrefixCut := [⟨41,238403499,238403643⟩,
⟨112,650347685,650348087⟩,
⟨128,745851414,745851875⟩]
theorem checked17553 : checkPrefixCuts (2^48) 2304638977 9 Manual.Count131072.C017553.packed 128 cuts17553 = true := by
 decide +kernel
def pointBounds17553 : List (Nat × Nat × Nat) := [(2304680960,98324987379956,98325366729685),(2304753664,98325399324142,98325778674129)]
theorem point_links_checked17553 : (cuts17553.take 2).map (fun c => (2304638977-1+2*2^9*c.k,98324748976457+c.lower,98325128326042+c.upper)) = pointBounds17553 := by
 decide +kernel
def cuts17554 : List PrefixCut := [⟨55,322167327,322167523⟩,
⟨126,738115544,738115995⟩,
⟨128,748862122,748862580⟩]
theorem checked17554 : checkPrefixCuts (2^48) 2304770049 9 Manual.Count131072.C017554.packed 128 cuts17554 = true := by
 decide +kernel
def pointBounds17554 : List (Nat × Nat × Nat) := [(2304826368,98325816995198,98326196345440),(2304899072,98326232943415,98326612293912)]
theorem point_links_checked17554 : (cuts17554.take 2).map (fun c => (2304770049-1+2*2^9*c.k,98325494827871+c.lower,98325874177917+c.upper)) = pointBounds17554 := by
 decide +kernel
def cuts17555 : List PrefixCut := [⟨69,394564123,394564372⟩,
⟨128,739416394,739416851⟩]
theorem checked17555 : checkPrefixCuts (2^48) 2304901121 9 Manual.Count131072.C017555.packed 128 cuts17555 = true := by
 decide +kernel
def pointBounds17555 : List (Nat × Nat × Nat) := [(2304971776,98326638254116,98327017604869)]
theorem point_links_checked17555 : (cuts17555.take 1).map (fun c => (2304901121-1+2*2^9*c.k,98326243689993+c.lower,98326623040497+c.upper)) = pointBounds17555 := by
 decide +kernel
def cuts17556 : List PrefixCut := [⟨12,72535054,72535096⟩,
⟨83,476232905,476233193⟩,
⟨128,741328250,741328700⟩]
theorem checked17556 : checkPrefixCuts (2^48) 2305032193 9 Manual.Count131072.C017556.packed 128 cuts17556 = true := by
 decide +kernel
def pointBounds17556 : List (Nat × Nat × Nat) := [(2305044480,98327055641441,98327434992444),(2305117184,98327459339292,98327838690541)]
theorem point_links_checked17556 : (cuts17556.take 2).map (fun c => (2305032193-1+2*2^9*c.k,98326983106387+c.lower,98327362457348+c.upper)) = pointBounds17556 := by
 decide +kernel
def cuts17557 : List PrefixCut := [⟨26,149701427,149701520⟩,
⟨97,555693664,555694015⟩,
⟨128,736768208,736768671⟩]
theorem checked17557 : checkPrefixCuts (2^48) 2305163265 9 Manual.Count131072.C017557.packed 128 cuts17557 = true := by
 decide +kernel
def pointBounds17557 : List (Nat × Nat × Nat) := [(2305189888,98327874136064,98328253487568),(2305262592,98328280128301,98328659480063)]
theorem point_links_checked17557 : (cuts17557.take 2).map (fun c => (2305163265-1+2*2^9*c.k,98327724434637+c.lower,98328103786048+c.upper)) = pointBounds17557 := by
 decide +kernel
def cuts17558 : List PrefixCut := [⟨40,230277276,230277421⟩,
⟨111,636488094,636488494⟩,
⟨128,735749582,735750041⟩]
theorem checked17558 : checkPrefixCuts (2^48) 2305294337 9 Manual.Count131072.C017558.packed 128 cuts17558 = true := by
 decide +kernel
def pointBounds17558 : List (Nat × Nat × Nat) := [(2305335296,98328691480121,98329070832140),(2305408000,98329097690939,98329477043213)]
theorem point_links_checked17558 : (cuts17558.take 2).map (fun c => (2305294337-1+2*2^9*c.k,98328461202845+c.lower,98328840554719+c.upper)) = pointBounds17558 := by
 decide +kernel
def cuts17559 : List PrefixCut := [⟨54,317070105,317070299⟩,
⟨125,725697117,725697567⟩,
⟨128,743155348,743155809⟩]
theorem checked17559 : checkPrefixCuts (2^48) 2305425409 9 Manual.Count131072.C017559.packed 128 cuts17559 = true := by
 decide +kernel
def pointBounds17559 : List (Nat × Nat × Nat) := [(2305480704,98329514022532,98329893375059),(2305553408,98329922649544,98330302002327)]
theorem point_links_checked17559 : (cuts17559.take 2).map (fun c => (2305425409-1+2*2^9*c.k,98329196952427+c.lower,98329576304760+c.upper)) = pointBounds17559 := by
 decide +kernel
def cuts17560 : List PrefixCut := [⟨68,392132547,392132791⟩,
⟨128,734567253,734567707⟩]
theorem checked17560 : checkPrefixCuts (2^48) 2305556481 9 Manual.Count131072.C017560.packed 128 cuts17560 = true := by
 decide +kernel
def pointBounds17560 : List (Nat × Nat × Nat) := [(2305626112,98330332240322,98330711593360)]
theorem point_links_checked17560 : (cuts17560.take 1).map (fun c => (2305556481-1+2*2^9*c.k,98329940107775+c.lower,98330319460569+c.upper)) = pointBounds17560 := by
 decide +kernel
def cuts17561 : List PrefixCut := [⟨11,60917029,60917067⟩,
⟨82,473778039,473778340⟩,
⟨128,740751255,740751720⟩]
theorem checked17561 : checkPrefixCuts (2^48) 2305687553 9 Manual.Count131072.C017561.packed 128 cuts17561 = true := by
 decide +kernel
def pointBounds17561 : List (Nat × Nat × Nat) := [(2305698816,98330735592057,98331114945343),(2305771520,98331148453067,98331527806616)]
theorem point_links_checked17561 : (cuts17561.take 2).map (fun c => (2305687553-1+2*2^9*c.k,98330674675028+c.lower,98331054028276+c.upper)) = pointBounds17561 := by
 decide +kernel
def cuts17562 : List PrefixCut := [⟨25,141602246,141602332⟩,
⟨96,556512290,556512638⟩,
⟨128,742173872,742174335⟩]
theorem checked17562 : checkPrefixCuts (2^48) 2305818625 9 Manual.Count131072.C017562.packed 128 cuts17562 = true := by
 decide +kernel
def pointBounds17562 : List (Nat × Nat × Nat) := [(2305844224,98331557028529,98331936382328),(2305916928,98331971938573,98332351292634)]
theorem point_links_checked17562 : (cuts17562.take 2).map (fun c => (2305818625-1+2*2^9*c.k,98331415426283+c.lower,98331794779996+c.upper)) = pointBounds17562 := by
 decide +kernel
def cuts17563 : List PrefixCut := [⟨39,223010104,223010247⟩,
⟨110,636673426,636673824⟩,
⟨128,742009635,742010100⟩]
theorem checked17563 : checkPrefixCuts (2^48) 2305949697 9 Manual.Count131072.C017563.packed 128 cuts17563 = true := by
 decide +kernel
def pointBounds17563 : List (Nat × Nat × Nat) := [(2305989632,98332380610259,98332759964578),(2306062336,98332794273581,98333173628155)]
theorem point_links_checked17563 : (cuts17563.take 2).map (fun c => (2305949697-1+2*2^9*c.k,98332157600155+c.lower,98332536954331+c.upper)) = pointBounds17563 := by
 decide +kernel
def cuts17564 : List PrefixCut := [⟨53,307825835,307826026⟩,
⟨124,716702995,716703435⟩,
⟨128,739770608,739771061⟩]
theorem checked17564 : checkPrefixCuts (2^48) 2306080769 9 Manual.Count131072.C017564.packed 128 cuts17564 = true := by
 decide +kernel
def pointBounds17564 : List (Nat × Nat × Nat) := [(2306135040,98333207435625,98333586790457),(2306207744,98333616312785,98333995667866)]
theorem point_links_checked17564 : (cuts17564.take 2).map (fun c => (2306080769-1+2*2^9*c.k,98332899609790+c.lower,98333278964431+c.upper)) = pointBounds17564 := by
 decide +kernel
def cuts17565 : List PrefixCut := [⟨67,391410911,391411158⟩,
⟨128,754008010,754008479⟩]
theorem checked17565 : checkPrefixCuts (2^48) 2306211841 9 Manual.Count131072.C017565.packed 128 cuts17565 = true := by
 decide +kernel
def pointBounds17565 : List (Nat × Nat × Nat) := [(2306280448,98334030791309,98334410146650)]
theorem point_links_checked17565 : (cuts17565.take 1).map (fun c => (2306211841-1+2*2^9*c.k,98333639380398+c.lower,98334018735492+c.upper)) = pointBounds17565 := by
 decide +kernel
def cuts17566 : List PrefixCut := [⟨10,59679292,59679328⟩,
⟨81,468883936,468884228⟩,
⟨128,737733994,737734456⟩]
theorem checked17566 : checkPrefixCuts (2^48) 2306342913 9 Manual.Count131072.C017566.packed 128 cuts17566 = true := by
 decide +kernel
def pointBounds17566 : List (Nat × Nat × Nat) := [(2306353152,98334453067700,98334832423299),(2306425856,98334862272344,98335241628199)]
theorem point_links_checked17566 : (cuts17566.take 2).map (fun c => (2306342913-1+2*2^9*c.k,98334393388408+c.lower,98334772743971+c.upper)) = pointBounds17566 := by
 decide +kernel
def cuts17567 : List PrefixCut := [⟨24,142050171,142050260⟩,
⟨95,557208648,557208997⟩,
⟨128,751847840,751848309⟩]
theorem checked17567 : checkPrefixCuts (2^48) 2306473985 9 Manual.Count131072.C017567.packed 128 cuts17567 = true := by
 decide +kernel
def pointBounds17567 : List (Nat × Nat × Nat) := [(2306498560,98335273172573,98335652528687),(2306571264,98335688331050,98336067687424)]
theorem point_links_checked17567 : (cuts17567.take 2).map (fun c => (2306473985-1+2*2^9*c.k,98335131122402+c.lower,98335510478427+c.upper)) = pointBounds17567 := by
 decide +kernel
def cuts17568 : List PrefixCut := [⟨38,217943645,217943781⟩,
⟨109,625876470,625876855⟩,
⟨128,734355393,734355845⟩]
theorem checked17568 : checkPrefixCuts (2^48) 2306605057 9 Manual.Count131072.C017568.packed 128 cuts17568 = true := by
 decide +kernel
def pointBounds17568 : List (Nat × Nat × Nat) := [(2306643968,98336100913887,98336480270517),(2306716672,98336508846712,98336888203591)]
theorem point_links_checked17568 : (cuts17568.take 2).map (fun c => (2306605057-1+2*2^9*c.k,98335882970242+c.lower,98336262326736+c.upper)) = pointBounds17568 := by
 decide +kernel
def cuts17569 : List PrefixCut := [⟨52,296878571,296878754⟩,
⟨123,713448988,713449429⟩,
⟨128,741268684,741269143⟩]
theorem checked17569 : checkPrefixCuts (2^48) 2306736129 9 Manual.Count131072.C017569.packed 128 cuts17569 = true := by
 decide +kernel
def pointBounds17569 : List (Nat × Nat × Nat) := [(2306789376,98336914204206,98337293561335),(2306862080,98337330774623,98337710132010)]
theorem point_links_checked17569 : (cuts17569.take 2).map (fun c => (2306736129-1+2*2^9*c.k,98336617325635+c.lower,98336996682581+c.upper)) = pointBounds17569 := by
 decide +kernel
def cuts17570 : List PrefixCut := [⟨66,379830380,379830617⟩,
⟨128,742202552,742203007⟩]
theorem checked17570 : checkPrefixCuts (2^48) 2306867201 9 Manual.Count131072.C017570.packed 128 cuts17570 = true := by
 decide +kernel
def pointBounds17570 : List (Nat × Nat × Nat) := [(2306934784,98337738424699,98338117782341)]
theorem point_links_checked17570 : (cuts17570.take 1).map (fun c => (2306867201-1+2*2^9*c.k,98337358594319+c.lower,98337737951724+c.upper)) = pointBounds17570 := by
 decide +kernel
def cuts17571 : List PrefixCut := [⟨9,52341821,52341854⟩,
⟨80,467042717,467043001⟩,
⟨128,738622504,738622953⟩]
theorem checked17571 : checkPrefixCuts (2^48) 2306998273 9 Manual.Count131072.C017571.packed 128 cuts17571 = true := by
 decide +kernel
def pointBounds17571 : List (Nat × Nat × Nat) := [(2307007488,98338153138692,98338532496585),(2307080192,98338567839588,98338947197732)]
theorem point_links_checked17571 : (cuts17571.take 2).map (fun c => (2306998273-1+2*2^9*c.k,98338100796871+c.lower,98338480154731+c.upper)) = pointBounds17571 := by
 decide +kernel
def cuts17572 : List PrefixCut := [⟨23,134323747,134323831⟩,
⟨94,547900500,547900841⟩,
⟨128,739678514,739678976⟩]
theorem checked17572 : checkPrefixCuts (2^48) 2307129345 9 Manual.Count131072.C017572.packed 128 cuts17572 = true := by
 decide +kernel
def pointBounds17572 : List (Nat × Nat × Nat) := [(2307152896,98338973743122,98339353101515),(2307225600,98339387319875,98339766678525)]
theorem point_links_checked17572 : (cuts17572.take 2).map (fun c => (2307129345-1+2*2^9*c.k,98338839419375+c.lower,98339218777684+c.upper)) = pointBounds17572 := by
 decide +kernel
def cuts17573 : List PrefixCut := [⟨37,220321681,220321813⟩,
⟨108,633018453,633018842⟩,
⟨128,745614193,745614653⟩]
theorem checked17573 : checkPrefixCuts (2^48) 2307260417 9 Manual.Count131072.C017573.packed 128 cuts17573 = true := by
 decide +kernel
def pointBounds17573 : List (Nat × Nat × Nat) := [(2307298304,98339799419570,98340178778473),(2307371008,98340212116342,98340591475502)]
theorem point_links_checked17573 : (cuts17573.take 2).map (fun c => (2307260417-1+2*2^9*c.k,98339579097889+c.lower,98339958456660+c.upper)) = pointBounds17573 := by
 decide +kernel
def cuts17574 : List PrefixCut := [⟨51,296184389,296184574⟩,
⟨122,711660699,711661136⟩,
⟨128,744107801,744108259⟩]
theorem checked17574 : checkPrefixCuts (2^48) 2307391489 9 Manual.Count131072.C017574.packed 128 cuts17574 = true := by
 decide +kernel
def pointBounds17574 : List (Nat × Nat × Nat) := [(2307443712,98340620896471,98341000255887),(2307516416,98341036372781,98341415732449)]
theorem point_links_checked17574 : (cuts17574.take 2).map (fun c => (2307391489-1+2*2^9*c.k,98340324712082+c.lower,98340704071313+c.upper)) = pointBounds17574 := by
 decide +kernel
def cuts17575 : List PrefixCut := [⟨65,366061034,366061260⟩,
⟨128,730891876,730892327⟩]
theorem checked17575 : checkPrefixCuts (2^48) 2307522561 9 Manual.Count131072.C017575.packed 128 cuts17575 = true := by
 decide +kernel
def pointBounds17575 : List (Nat × Nat × Nat) := [(2307589120,98341434880917,98341814240832)]
theorem point_links_checked17575 : (cuts17575.take 1).map (fun c => (2307522561-1+2*2^9*c.k,98341068819883+c.lower,98341448179572+c.upper)) = pointBounds17575 := by
 decide +kernel
def cuts17576 : List PrefixCut := [⟨8,45130489,45130518⟩,
⟨79,451053654,451053940⟩,
⟨128,729020749,729021206⟩]
theorem checked17576 : checkPrefixCuts (2^48) 2307653633 9 Manual.Count131072.C017576.packed 128 cuts17576 = true := by
 decide +kernel
def pointBounds17576 : List (Nat × Nat × Nat) := [(2307661824,98341844842248,98342224202417),(2307734528,98342250765413,98342630125839)]
theorem point_links_checked17576 : (cuts17576.take 2).map (fun c => (2307653633-1+2*2^9*c.k,98341799711759+c.lower,98342179071899+c.upper)) = pointBounds17576 := by
 decide +kernel
def cuts17577 : List PrefixCut := [⟨22,129284992,129285069⟩,
⟨93,541890782,541891109⟩,
⟨128,746054477,746054931⟩]
theorem checked17577 : checkPrefixCuts (2^48) 2307784705 9 Manual.Count131072.C017577.packed 128 cuts17577 = true := by
 decide +kernel
def pointBounds17577 : List (Nat × Nat × Nat) := [(2307807232,98342658017500,98343037378174),(2307879936,98343070623290,98343449984214)]
theorem point_links_checked17577 : (cuts17577.take 2).map (fun c => (2307784705-1+2*2^9*c.k,98342528732508+c.lower,98342908093105+c.upper)) = pointBounds17577 := by
 decide +kernel
def cuts17578 : List PrefixCut := [⟨36,204404429,204404556⟩,
⟨107,624911411,624911793⟩,
⟨128,744548563,744549018⟩]
theorem checked17578 : checkPrefixCuts (2^48) 2307915777 9 Manual.Count131072.C017578.packed 128 cuts17578 = true := by
 decide +kernel
def pointBounds17578 : List (Nat × Nat × Nat) := [(2307952640,98343479191414,98343858552592),(2308025344,98343899698396,98344279059829)]
theorem point_links_checked17578 : (cuts17578.take 2).map (fun c => (2307915777-1+2*2^9*c.k,98343274786985+c.lower,98343654148036+c.upper)) = pointBounds17578 := by
 decide +kernel
def cuts17579 : List PrefixCut := [⟨50,292319803,292319984⟩,
⟨121,701215138,701215573⟩,
⟨128,742433216,742433677⟩]
theorem checked17579 : checkPrefixCuts (2^48) 2308046849 9 Manual.Count131072.C017579.packed 128 cuts17579 = true := by
 decide +kernel
def pointBounds17579 : List (Nat × Nat × Nat) := [(2308098048,98344311655351,98344691017038),(2308170752,98344720550686,98345099912627)]
theorem point_links_checked17579 : (cuts17579.take 2).map (fun c => (2308046849-1+2*2^9*c.k,98344019335548+c.lower,98344398697054+c.upper)) = pointBounds17579 := by
 decide +kernel
def cuts17580 : List PrefixCut := [⟨64,370834946,370835173⟩,
⟨128,741049561,741050015⟩]
theorem checked17580 : checkPrefixCuts (2^48) 2308177921 9 Manual.Count131072.C017580.packed 128 cuts17580 = true := by
 decide +kernel
def pointBounds17580 : List (Nat × Nat × Nat) := [(2308243456,98345132603710,98345511965904)]
theorem point_links_checked17580 : (cuts17580.take 1).map (fun c => (2308177921-1+2*2^9*c.k,98344761768764+c.lower,98345141130731+c.upper)) = pointBounds17580 := by
 decide +kernel
def cuts17581 : List PrefixCut := [⟨7,39264577,39264600⟩,
⟨78,455681364,455681645⟩,
⟨128,738203109,738203567⟩]
theorem checked17581 : checkPrefixCuts (2^48) 2308308993 9 Manual.Count131072.C017581.packed 128 cuts17581 = true := by
 decide +kernel
def pointBounds17581 : List (Nat × Nat × Nat) := [(2308316160,98345542082902,98345921445346),(2308388864,98345958499689,98346337862391)]
theorem point_links_checked17581 : (cuts17581.take 2).map (fun c => (2308308993-1+2*2^9*c.k,98345502818325+c.lower,98345882180746+c.upper)) = pointBounds17581 := by
 decide +kernel
def cuts17582 : List PrefixCut := [⟨21,121444641,121444721⟩,
⟨92,532226462,532226796⟩,
⟨128,742428588,742429053⟩]
theorem checked17582 : checkPrefixCuts (2^48) 2308440065 9 Manual.Count131072.C017582.packed 128 cuts17582 = true := by
 decide +kernel
def pointBounds17582 : List (Nat × Nat × Nat) := [(2308461568,98346362466075,98346741829034),(2308534272,98346773247896,98347152611109)]
theorem point_links_checked17582 : (cuts17582.take 2).map (fun c => (2308440065-1+2*2^9*c.k,98346241021434+c.lower,98346620384313+c.upper)) = pointBounds17582 := by
 decide +kernel
def cuts17583 : List PrefixCut := [⟨35,204468365,204468490⟩,
⟨106,610835102,610835481⟩,
⟨128,734705510,734705964⟩]
theorem checked17583 : checkPrefixCuts (2^48) 2308571137 9 Manual.Count131072.C017583.packed 128 cuts17583 = true := by
 decide +kernel
def pointBounds17583 : List (Nat × Nat × Nat) := [(2308606976,98347187918387,98347567281856),(2308679680,98347594285124,98347973648847)]
theorem point_links_checked17583 : (cuts17583.take 2).map (fun c => (2308571137-1+2*2^9*c.k,98346983450022+c.lower,98347362813366+c.upper)) = pointBounds17583 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000236
