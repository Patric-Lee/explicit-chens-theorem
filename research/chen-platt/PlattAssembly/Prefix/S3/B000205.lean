import PlattAssemblyKernel
import PlattCertificates.Count131072.C026560
import PlattCertificates.Count131072.C026561
import PlattCertificates.Count131072.C026562
import PlattCertificates.Count131072.C026563
import PlattCertificates.Count131072.C026564
import PlattCertificates.Count131072.C026565
import PlattCertificates.Count131072.C026566
import PlattCertificates.Count131072.C026567
import PlattCertificates.Count131072.C026568
import PlattCertificates.Count131072.C026569
import PlattCertificates.Count131072.C026570
import PlattCertificates.Count131072.C026571
import PlattCertificates.Count131072.C026572
import PlattCertificates.Count131072.C026573
import PlattCertificates.Count131072.C026574
import PlattCertificates.Count131072.C026575
import PlattCertificates.Count131072.C026576
import PlattCertificates.Count131072.C026577
import PlattCertificates.Count131072.C026578
import PlattCertificates.Count131072.C026579
import PlattCertificates.Count131072.C026580
import PlattCertificates.Count131072.C026581
import PlattCertificates.Count131072.C026582
import PlattCertificates.Count131072.C026583
import PlattCertificates.Count131072.C026584
import PlattCertificates.Count131072.C026585
import PlattCertificates.Count131072.C026586
import PlattCertificates.Count131072.C026587
import PlattCertificates.Count131072.C026588
import PlattCertificates.Count131072.C026589
import PlattCertificates.Count131072.C026590
import PlattCertificates.Count131072.C026591
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000205
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26560 : List PrefixCut := [⟨36,139799694,139799772⟩,
⟨128,485617728,485617998⟩]
theorem checked26560 : checkPrefixCuts (2^48) 3485204481 9 Manual.Count131072.C026560.packed 128 cuts26560 = true := by
 decide +kernel
def pointBounds26560 : List (Nat × Nat × Nat) := [(3485241344,103673783261114,103674165712062)]
theorem point_links_checked26560 : (cuts26560.take 1).map (fun c => (3485204481-1+2*2^9*c.k,103673643461420+c.lower,103674025912290+c.upper)) = pointBounds26560 := by
 decide +kernel
def cuts26561 : List PrefixCut := [⟨15,56047160,56047191⟩,
⟨122,449177823,449178080⟩,
⟨128,471870486,471870755⟩]
theorem checked26561 : checkPrefixCuts (2^48) 3485335553 9 Manual.Count131072.C026561.packed 128 cuts26561 = true := by
 decide +kernel
def pointBounds26561 : List (Nat × Nat × Nat) := [(3485350912,103674185126308,103674567577479),(3485460480,103674578256971,103674960708368)]
theorem point_links_checked26561 : (cuts26561.take 2).map (fun c => (3485335553-1+2*2^9*c.k,103674129079148+c.lower,103674511530288+c.upper)) = pointBounds26561 := by
 decide +kernel
def cuts26562 : List PrefixCut := [⟨101,376240026,376240231⟩,
⟨128,476940288,476940552⟩]
theorem checked26562 : checkPrefixCuts (2^48) 3485466625 9 Manual.Count131072.C026562.packed 128 cuts26562 = true := by
 decide +kernel
def pointBounds26562 : List (Nat × Nat × Nat) := [(3485570048,103674977189660,103675359641274)]
theorem point_links_checked26562 : (cuts26562.take 1).map (fun c => (3485466625-1+2*2^9*c.k,103674600949634+c.lower,103674983401043+c.upper)) = pointBounds26562 := by
 decide +kernel
def cuts26563 : List PrefixCut := [⟨80,303711079,303711247⟩,
⟨128,484432344,484432613⟩]
theorem checked26563 : checkPrefixCuts (2^48) 3485597697 9 Manual.Count131072.C026563.packed 128 cuts26563 = true := by
 decide +kernel
def pointBounds26563 : List (Nat × Nat × Nat) := [(3485679616,103675381601001,103675764052842)]
theorem point_links_checked26563 : (cuts26563.take 1).map (fun c => (3485597697-1+2*2^9*c.k,103675077889922+c.lower,103675460341595+c.upper)) = pointBounds26563 := by
 decide +kernel
def cuts26564 : List PrefixCut := [⟨59,222385372,222385496⟩,
⟨128,484333322,484333589⟩]
theorem checked26564 : checkPrefixCuts (2^48) 3485728769 9 Manual.Count131072.C026564.packed 128 cuts26564 = true := by
 decide +kernel
def pointBounds26564 : List (Nat × Nat × Nat) := [(3485789184,103675784707638,103676167159704)]
theorem point_links_checked26564 : (cuts26564.take 1).map (fun c => (3485728769-1+2*2^9*c.k,103675562322266+c.lower,103675944774208+c.upper)) = pointBounds26564 := by
 decide +kernel
def cuts26565 : List PrefixCut := [⟨38,143729985,143730065⟩,
⟨128,487706464,487706741⟩]
theorem checked26565 : checkPrefixCuts (2^48) 3485859841 9 Manual.Count131072.C026565.packed 128 cuts26565 = true := by
 decide +kernel
def pointBounds26565 : List (Nat × Nat × Nat) := [(3485898752,103676190385573,103676572837862)]
theorem point_links_checked26565 : (cuts26565.take 1).map (fun c => (3485859841-1+2*2^9*c.k,103676046655588+c.lower,103676429107797+c.upper)) = pointBounds26565 := by
 decide +kernel
def cuts26566 : List PrefixCut := [⟨17,62738390,62738425⟩,
⟨124,463707705,463707970⟩,
⟨128,479533059,479533332⟩]
theorem checked26566 : checkPrefixCuts (2^48) 3485990913 9 Manual.Count131072.C026566.packed 128 cuts26566 = true := by
 decide +kernel
def pointBounds26566 : List (Nat × Nat × Nat) := [(3486008320,103676597100442,103676979552963),(3486117888,103676998069757,103677380522508)]
theorem point_links_checked26566 : (cuts26566.take 2).map (fun c => (3485990913-1+2*2^9*c.k,103676534362052+c.lower,103676916814538+c.upper)) = pointBounds26566 := by
 decide +kernel
def cuts26567 : List PrefixCut := [⟨103,388845398,388845613⟩,
⟨128,481129857,481130125⟩]
theorem checked26567 : checkPrefixCuts (2^48) 3486121985 9 Manual.Count131072.C026567.packed 128 cuts26567 = true := by
 decide +kernel
def pointBounds26567 : List (Nat × Nat × Nat) := [(3486227456,103677402740509,103677785193483)]
theorem point_links_checked26567 : (cuts26567.take 1).map (fun c => (3486121985-1+2*2^9*c.k,103677013895111+c.lower,103677396347870+c.upper)) = pointBounds26567 := by
 decide +kernel
def cuts26568 : List PrefixCut := [⟨82,307771493,307771666⟩,
⟨128,484018235,484018506⟩]
theorem checked26568 : checkPrefixCuts (2^48) 3486253057 9 Manual.Count131072.C026568.packed 128 cuts26568 = true := by
 decide +kernel
def pointBounds26568 : List (Nat × Nat × Nat) := [(3486337024,103677802796461,103678185249661)]
theorem point_links_checked26568 : (cuts26568.take 1).map (fun c => (3486253057-1+2*2^9*c.k,103677495024968+c.lower,103677877477995+c.upper)) = pointBounds26568 := by
 decide +kernel
def cuts26569 : List PrefixCut := [⟨61,227349086,227349211⟩,
⟨128,483515675,483515944⟩]
theorem checked26569 : checkPrefixCuts (2^48) 3486384129 9 Manual.Count131072.C026569.packed 128 cuts26569 = true := by
 decide +kernel
def pointBounds26569 : List (Nat × Nat × Nat) := [(3486446592,103678206392289,103678588845712)]
theorem point_links_checked26569 : (cuts26569.take 1).map (fun c => (3486384129-1+2*2^9*c.k,103677979043203+c.lower,103678361496501+c.upper)) = pointBounds26569 := by
 decide +kernel
def cuts26570 : List PrefixCut := [⟨40,151776096,151776179⟩,
⟨128,483336067,483336335⟩]
theorem checked26570 : checkPrefixCuts (2^48) 3486515201 9 Manual.Count131072.C026570.packed 128 cuts26570 = true := by
 decide +kernel
def pointBounds26570 : List (Nat × Nat × Nat) := [(3486556160,103678614334974,103678996788624)]
theorem point_links_checked26570 : (cuts26570.take 1).map (fun c => (3486515201-1+2*2^9*c.k,103678462558878+c.lower,103678845012445+c.upper)) = pointBounds26570 := by
 decide +kernel
def cuts26571 : List PrefixCut := [⟨19,69184914,69184954⟩,
⟨126,468221951,468222214⟩,
⟨128,475890959,475891226⟩]
theorem checked26571 : checkPrefixCuts (2^48) 3486646273 9 Manual.Count131072.C026571.packed 128 cuts26571 = true := by
 decide +kernel
def pointBounds26571 : List (Nat × Nat × Nat) := [(3486665728,103679015079859,103679397533734),(3486775296,103679414116896,103679796570994)]
theorem point_links_checked26571 : (cuts26571.take 2).map (fun c => (3486646273-1+2*2^9*c.k,103678945894945+c.lower,103679328348780+c.upper)) = pointBounds26571 := by
 decide +kernel
def cuts26572 : List PrefixCut := [⟨105,399670147,399670371⟩,
⟨128,487820331,487820605⟩]
theorem checked26572 : checkPrefixCuts (2^48) 3486777345 9 Manual.Count131072.C026572.packed 128 cuts26572 = true := by
 decide +kernel
def pointBounds26572 : List (Nat × Nat × Nat) := [(3486884864,103679821456051,103680203910377)]
theorem point_links_checked26572 : (cuts26572.take 1).map (fun c => (3486777345-1+2*2^9*c.k,103679421785904+c.lower,103679804240006+c.upper)) = pointBounds26572 := by
 decide +kernel
def cuts26573 : List PrefixCut := [⟨84,316915923,316916102⟩,
⟨128,477792532,477792798⟩]
theorem checked26573 : checkPrefixCuts (2^48) 3486908417 9 Manual.Count131072.C026573.packed 128 cuts26573 = true := by
 decide +kernel
def pointBounds26573 : List (Nat × Nat × Nat) := [(3486994432,103680226522158,103680608976713)]
theorem point_links_checked26573 : (cuts26573.take 1).map (fun c => (3486908417-1+2*2^9*c.k,103679909606235+c.lower,103680292060611+c.upper)) = pointBounds26573 := by
 decide +kernel
def cuts26574 : List PrefixCut := [⟨63,240059955,240060088⟩,
⟨128,485765670,485765935⟩]
theorem checked26574 : checkPrefixCuts (2^48) 3487039489 9 Manual.Count131072.C026574.packed 128 cuts26574 = true := by
 decide +kernel
def pointBounds26574 : List (Nat × Nat × Nat) := [(3487104000,103680627458722,103681009913497)]
theorem point_links_checked26574 : (cuts26574.take 1).map (fun c => (3487039489-1+2*2^9*c.k,103680387398767+c.lower,103680769853409+c.upper)) = pointBounds26574 := by
 decide +kernel
def cuts26575 : List PrefixCut := [⟨42,159899948,159900036⟩,
⟨128,483648862,483649132⟩]
theorem checked26575 : checkPrefixCuts (2^48) 3487170561 9 Manual.Count131072.C026575.packed 128 cuts26575 = true := by
 decide +kernel
def pointBounds26575 : List (Nat × Nat × Nat) := [(3487213568,103681033064385,103681415519380)]
theorem point_links_checked26575 : (cuts26575.take 1).map (fun c => (3487170561-1+2*2^9*c.k,103680873164437+c.lower,103681255619344+c.upper)) = pointBounds26575 := by
 decide +kernel
def cuts26576 : List PrefixCut := [⟨21,81036843,81036886⟩,
⟨128,478303640,478303906⟩]
theorem checked26576 : checkPrefixCuts (2^48) 3487301633 9 Manual.Count131072.C026576.packed 128 cuts26576 = true := by
 decide +kernel
def pointBounds26576 : List (Nat × Nat × Nat) := [(3487323136,103681437850142,103681820305362),(3487432704,103681835116939,103682217572382)]
theorem point_links_checked26576 : (cuts26576.take 2).map (fun c => (3487301633-1+2*2^9*c.k,103681356813299+c.lower,103681739268476+c.upper)) = pointBounds26576 := by
 decide +kernel
def cuts26577 : List PrefixCut := [⟨107,404841013,404841238⟩,
⟨128,481998260,481998528⟩]
theorem checked26577 : checkPrefixCuts (2^48) 3487432705 9 Manual.Count131072.C026577.packed 128 cuts26577 = true := by
 decide +kernel
def pointBounds26577 : List (Nat × Nat × Nat) := [(3487542272,103682239957952,103682622413620)]
theorem point_links_checked26577 : (cuts26577.take 1).map (fun c => (3487432705-1+2*2^9*c.k,103681835116939+c.lower,103682217572382+c.upper)) = pointBounds26577 := by
 decide +kernel
def cuts26578 : List PrefixCut := [⟨86,325976205,325976383⟩,
⟨128,484966300,484966569⟩]
theorem checked26578 : checkPrefixCuts (2^48) 3487563777 9 Manual.Count131072.C026578.packed 128 cuts26578 = true := by
 decide +kernel
def pointBounds26578 : List (Nat × Nat × Nat) := [(3487651840,103682643091404,103683025547293)]
theorem point_links_checked26578 : (cuts26578.take 1).map (fun c => (3487563777-1+2*2^9*c.k,103682317115199+c.lower,103682699570910+c.upper)) = pointBounds26578 := by
 decide +kernel
def cuts26579 : List PrefixCut := [⟨65,240902540,240902676⟩,
⟨128,476877719,476877987⟩]
theorem checked26579 : checkPrefixCuts (2^48) 3487694849 9 Manual.Count131072.C026579.packed 128 cuts26579 = true := by
 decide +kernel
def pointBounds26579 : List (Nat × Nat × Nat) := [(3487761408,103683042984039,103683425440155)]
theorem point_links_checked26579 : (cuts26579.take 1).map (fun c => (3487694849-1+2*2^9*c.k,103682802081499+c.lower,103683184537479+c.upper)) = pointBounds26579 := by
 decide +kernel
def cuts26580 : List PrefixCut := [⟨44,163582117,163582214⟩,
⟨128,480652698,480652969⟩]
theorem checked26580 : checkPrefixCuts (2^48) 3487825921 9 Manual.Count131072.C026580.packed 128 cuts26580 = true := by
 decide +kernel
def pointBounds26580 : List (Nat × Nat × Nat) := [(3487870976,103683442541335,103683824997680)]
theorem point_links_checked26580 : (cuts26580.take 1).map (fun c => (3487825921-1+2*2^9*c.k,103683278959218+c.lower,103683661415466+c.upper)) = pointBounds26580 := by
 decide +kernel
def cuts26581 : List PrefixCut := [⟨23,84249553,84249600⟩,
⟨128,485234363,485234632⟩]
theorem checked26581 : checkPrefixCuts (2^48) 3487956993 9 Manual.Count131072.C026581.packed 128 cuts26581 = true := by
 decide +kernel
def pointBounds26581 : List (Nat × Nat × Nat) := [(3487980544,103683843861469,103684226318035)]
theorem point_links_checked26581 : (cuts26581.take 1).map (fun c => (3487956993-1+2*2^9*c.k,103683759611916+c.lower,103684142068435+c.upper)) = pointBounds26581 := by
 decide +kernel
def cuts26582 : List PrefixCut := [⟨2,6939857,6939861⟩,
⟨109,412027382,412027609⟩,
⟨128,481100791,481101057⟩]
theorem checked26582 : checkPrefixCuts (2^48) 3488088065 9 Manual.Count131072.C026582.packed 128 cuts26582 = true := by
 decide +kernel
def pointBounds26582 : List (Nat × Nat × Nat) := [(3488090112,103684251786136,103684634242928),(3488199680,103684656873661,103685039330676)]
theorem point_links_checked26582 : (cuts26582.take 2).map (fun c => (3488088065-1+2*2^9*c.k,103684244846279+c.lower,103684627303067+c.upper)) = pointBounds26582 := by
 decide +kernel
def cuts26583 : List PrefixCut := [⟨88,333015744,333015931⟩,
⟨128,485117251,485117523⟩]
theorem checked26583 : checkPrefixCuts (2^48) 3488219137 9 Manual.Count131072.C026583.packed 128 cuts26583 = true := by
 decide +kernel
def pointBounds26583 : List (Nat × Nat × Nat) := [(3488309248,103685058962814,103685441420055)]
theorem point_links_checked26583 : (cuts26583.take 1).map (fun c => (3488219137-1+2*2^9*c.k,103684725947070+c.lower,103685108404124+c.upper)) = pointBounds26583 := by
 decide +kernel
def cuts26584 : List PrefixCut := [⟨67,252153682,252153822⟩,
⟨128,479773577,479773845⟩]
theorem checked26584 : checkPrefixCuts (2^48) 3488350209 9 Manual.Count131072.C026584.packed 128 cuts26584 = true := by
 decide +kernel
def pointBounds26584 : List (Nat × Nat × Nat) := [(3488418816,103685463218003,103685845675469)]
theorem point_links_checked26584 : (cuts26584.take 1).map (fun c => (3488350209-1+2*2^9*c.k,103685211064321+c.lower,103685593521647+c.upper)) = pointBounds26584 := by
 decide +kernel
def cuts26585 : List PrefixCut := [⟨46,169360768,169360862⟩,
⟨128,476043998,476044264⟩]
theorem checked26585 : checkPrefixCuts (2^48) 3488481281 9 Manual.Count131072.C026585.packed 128 cuts26585 = true := by
 decide +kernel
def pointBounds26585 : List (Nat × Nat × Nat) := [(3488528384,103685860198666,103686242656354)]
theorem point_links_checked26585 : (cuts26585.take 1).map (fun c => (3488481281-1+2*2^9*c.k,103685690837898+c.lower,103686073295492+c.upper)) = pointBounds26585 := by
 decide +kernel
def cuts26586 : List PrefixCut := [⟨25,97304443,97304499⟩,
⟨128,485385326,485385595⟩]
theorem checked26586 : checkPrefixCuts (2^48) 3488612353 9 Manual.Count131072.C026586.packed 128 cuts26586 = true := by
 decide +kernel
def pointBounds26586 : List (Nat × Nat × Nat) := [(3488637952,103686264186339,103686646644255)]
theorem point_links_checked26586 : (cuts26586.take 1).map (fun c => (3488612353-1+2*2^9*c.k,103686166881896+c.lower,103686549339756+c.upper)) = pointBounds26586 := by
 decide +kernel
def cuts26587 : List PrefixCut := [⟨4,17346380,17346390⟩,
⟨111,419856480,419856713⟩,
⟨128,482381966,482382236⟩]
theorem checked26587 : checkPrefixCuts (2^48) 3488743425 9 Manual.Count131072.C026587.packed 128 cuts26587 = true := by
 decide +kernel
def pointBounds26587 : List (Nat × Nat × Nat) := [(3488747520,103686669613602,103687052071741),(3488857088,103687072123702,103687454582064)]
theorem point_links_checked26587 : (cuts26587.take 2).map (fun c => (3488743425-1+2*2^9*c.k,103686652267222+c.lower,103687034725351+c.upper)) = pointBounds26587 := by
 decide +kernel
def cuts26588 : List PrefixCut := [⟨90,339729941,339730128⟩,
⟨128,480185590,480185856⟩]
theorem checked26588 : checkPrefixCuts (2^48) 3488874497 9 Manual.Count131072.C026588.packed 128 cuts26588 = true := by
 decide +kernel
def pointBounds26588 : List (Nat × Nat × Nat) := [(3488966656,103687474379129,103687856837715)]
theorem point_links_checked26588 : (cuts26588.take 1).map (fun c => (3488874497-1+2*2^9*c.k,103687134649188+c.lower,103687517107587+c.upper)) = pointBounds26588 := by
 decide +kernel
def cuts26589 : List PrefixCut := [⟨69,262190491,262190636⟩,
⟨128,482265032,482265300⟩]
theorem checked26589 : checkPrefixCuts (2^48) 3489005569 9 Manual.Count131072.C026589.packed 128 cuts26589 = true := by
 decide +kernel
def pointBounds26589 : List (Nat × Nat × Nat) := [(3489076224,103687877025269,103688259484079)]
theorem point_links_checked26589 : (cuts26589.take 1).map (fun c => (3489005569-1+2*2^9*c.k,103687614834778+c.lower,103687997293443+c.upper)) = pointBounds26589 := by
 decide +kernel
def cuts26590 : List PrefixCut := [⟨48,184172394,184172493⟩,
⟨128,484425047,484425314⟩]
theorem checked26590 : checkPrefixCuts (2^48) 3489136641 9 Manual.Count131072.C026590.packed 128 cuts26590 = true := by
 decide +kernel
def pointBounds26590 : List (Nat × Nat × Nat) := [(3489185792,103688281272204,103688663731236)]
theorem point_links_checked26590 : (cuts26590.take 1).map (fun c => (3489136641-1+2*2^9*c.k,103688097099810+c.lower,103688479558743+c.upper)) = pointBounds26590 := by
 decide +kernel
def cuts26591 : List PrefixCut := [⟨27,103658937,103658996⟩,
⟨128,474404123,474404389⟩]
theorem checked26591 : checkPrefixCuts (2^48) 3489267713 9 Manual.Count131072.C026591.packed 128 cuts26591 = true := by
 decide +kernel
def pointBounds26591 : List (Nat × Nat × Nat) := [(3489295360,103688685183794,103689067643053)]
theorem point_links_checked26591 : (cuts26591.take 1).map (fun c => (3489267713-1+2*2^9*c.k,103688581524857+c.lower,103688963984057+c.upper)) = pointBounds26591 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000205
