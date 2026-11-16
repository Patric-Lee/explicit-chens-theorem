import PlattAssemblyKernel
import PlattCertificates.Count131072.C012752
import PlattCertificates.Count131072.C012753
import PlattCertificates.Count131072.C012754
import PlattCertificates.Count131072.C012755
import PlattCertificates.Count131072.C012756
import PlattCertificates.Count131072.C012757
import PlattCertificates.Count131072.C012758
import PlattCertificates.Count131072.C012759
import PlattCertificates.Count131072.C012760
import PlattCertificates.Count131072.C012761
import PlattCertificates.Count131072.C012762
import PlattCertificates.Count131072.C012763
import PlattCertificates.Count131072.C012764
import PlattCertificates.Count131072.C012765
import PlattCertificates.Count131072.C012766
import PlattCertificates.Count131072.C012767
import PlattCertificates.Count131072.C012768
import PlattCertificates.Count131072.C012769
import PlattCertificates.Count131072.C012770
import PlattCertificates.Count131072.C012771
import PlattCertificates.Count131072.C012772
import PlattCertificates.Count131072.C012773
import PlattCertificates.Count131072.C012774
import PlattCertificates.Count131072.C012775
import PlattCertificates.Count131072.C012776
import PlattCertificates.Count131072.C012777
import PlattCertificates.Count131072.C012778
import PlattCertificates.Count131072.C012779
import PlattCertificates.Count131072.C012780
import PlattCertificates.Count131072.C012781
import PlattCertificates.Count131072.C012782
import PlattCertificates.Count131072.C012783
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000086
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12752 : List PrefixCut := [⟨26,218241121,218241282⟩,
⟨78,631864598,631865067⟩,
⟨128,1036067324,1036068095⟩]
theorem checked12752 : checkPrefixCuts (2^48) 1675362305 9 Manual.Count131072.C012752.packed 128 cuts12752 = true := by
 decide +kernel
def pointBounds12752 : List (Nat × Nat × Nat) := [(1675388928,94130133016046,94130509555343),(1675442176,94130546639523,94130923179128)]
theorem point_links_checked12752 : (cuts12752.take 2).map (fun c => (1675362305-1+2*2^9*c.k,94129914774925+c.lower,94130291314061+c.upper)) = pointBounds12752 := by
 decide +kernel
def cuts12753 : List PrefixCut := [⟨2,19487434,19487448⟩,
⟨54,438292328,438292649⟩,
⟨106,861115566,861116200⟩,
⟨128,1037665872,1037666638⟩]
theorem checked12753 : checkPrefixCuts (2^48) 1675493377 9 Manual.Count131072.C012753.packed 128 cuts12753 = true := by
 decide +kernel
def pointBounds12753 : List (Nat × Nat × Nat) := [(1675495424,94130970329683,94131346869604),(1675548672,94131389134577,94131765674805),(1675601920,94131811957815,94132188498356)]
theorem point_links_checked12753 : (cuts12753.take 3).map (fun c => (1675493377-1+2*2^9*c.k,94130950842249+c.lower,94131327382156+c.upper)) = pointBounds12753 := by
 decide +kernel
def cuts12754 : List PrefixCut := [⟨30,243067848,243068026⟩,
⟨82,669223739,669224222⟩,
⟨128,1038592630,1038593383⟩]
theorem checked12754 : checkPrefixCuts (2^48) 1675624449 9 Manual.Count131072.C012754.packed 128 cuts12754 = true := by
 decide +kernel
def pointBounds12754 : List (Nat × Nat × Nat) := [(1675655168,94132231575969,94132608116820),(1675708416,94132657731860,94133034273016)]
theorem point_links_checked12754 : (cuts12754.take 2).map (fun c => (1675624449-1+2*2^9*c.k,94131988508121+c.lower,94132365048794+c.upper)) = pointBounds12754 := by
 decide +kernel
def cuts12755 : List PrefixCut := [⟨6,46695277,46695312⟩,
⟨58,478031162,478031510⟩,
⟨110,888358155,888358807⟩,
⟨128,1036999837,1037000597⟩]
theorem checked12755 : checkPrefixCuts (2^48) 1675755521 9 Manual.Count131072.C012755.packed 128 cuts12755 = true := by
 decide +kernel
def pointBounds12755 : List (Nat × Nat × Nat) := [(1675761664,94133073796028,94133450337489),(1675814912,94133505131913,94133881673687),(1675868160,94133915458906,94134292000984)]
theorem point_links_checked12755 : (cuts12755.take 3).map (fun c => (1675755521-1+2*2^9*c.k,94133027100751+c.lower,94133403642177+c.upper)) = pointBounds12755 := by
 decide +kernel
def cuts12756 : List PrefixCut := [⟨34,277124239,277124442⟩,
⟨86,691624089,691624595⟩,
⟨128,1033559797,1033560555⟩]
theorem checked12756 : checkPrefixCuts (2^48) 1675886593 9 Manual.Count131072.C012756.packed 128 cuts12756 = true := by
 decide +kernel
def pointBounds12756 : List (Nat × Nat × Nat) := [(1675921408,94134341224827,94134717767216),(1675974656,94134755724677,94135132267369)]
theorem point_links_checked12756 : (cuts12756.take 2).map (fun c => (1675886593-1+2*2^9*c.k,94134064100588+c.lower,94134440642774+c.upper)) = pointBounds12756 := by
 decide +kernel
def cuts12757 : List PrefixCut := [⟨10,84474909,84474970⟩,
⟨62,507849160,507849529⟩,
⟨114,933393004,933393690⟩,
⟨128,1045234547,1045235316⟩]
theorem checked12757 : checkPrefixCuts (2^48) 1676017665 9 Manual.Count131072.C012757.packed 128 cuts12757 = true := by
 decide +kernel
def pointBounds12757 : List (Nat × Nat × Nat) := [(1676027904,94135182135294,94135558678299),(1676081152,94135605509545,94135982052858),(1676134400,94136031053389,94136407597019)]
theorem point_links_checked12757 : (cuts12757.take 3).map (fun c => (1676017665-1+2*2^9*c.k,94135097660385+c.lower,94135474203329+c.upper)) = pointBounds12757 := by
 decide +kernel
def cuts12758 : List PrefixCut := [⟨38,307139537,307139762⟩,
⟨90,737862006,737862550⟩,
⟨128,1044145030,1044145798⟩]
theorem checked12758 : checkPrefixCuts (2^48) 1676148737 9 Manual.Count131072.C012758.packed 128 cuts12758 = true := by
 decide +kernel
def pointBounds12758 : List (Nat × Nat × Nat) := [(1676187648,94136450034469,94136826578407),(1676240896,94136880756938,94137257301195)]
theorem point_links_checked12758 : (cuts12758.take 2).map (fun c => (1676148737-1+2*2^9*c.k,94136142894932+c.lower,94136519438645+c.upper)) = pointBounds12758 := by
 decide +kernel
def cuts12759 : List PrefixCut := [⟨14,108473538,108473618⟩,
⟨66,537657370,537657765⟩,
⟨118,953562956,953563657⟩,
⟨128,1031806120,1031806878⟩]
theorem checked12759 : checkPrefixCuts (2^48) 1676279809 9 Manual.Count131072.C012759.packed 128 cuts12759 = true := by
 decide +kernel
def pointBounds12759 : List (Nat × Nat × Nat) := [(1676294144,94137295513500,94137672058061),(1676347392,94137724697332,94138101242208),(1676400640,94138140602918,94138517148100)]
theorem point_links_checked12759 : (cuts12759.take 3).map (fun c => (1676279809-1+2*2^9*c.k,94137187039962+c.lower,94137563584443+c.upper)) = pointBounds12759 := by
 decide +kernel
def cuts12760 : List PrefixCut := [⟨42,330093571,330093816⟩,
⟨94,740935795,740936345⟩,
⟨128,1021147352,1021148105⟩]
theorem checked12760 : checkPrefixCuts (2^48) 1676410881 9 Manual.Count131072.C012760.packed 128 cuts12760 = true := by
 decide +kernel
def pointBounds12760 : List (Nat × Nat × Nat) := [(1676453888,94138548939653,94138925485137),(1676507136,94138959781877,94139336327666)]
theorem point_links_checked12760 : (cuts12760.take 2).map (fun c => (1676410881-1+2*2^9*c.k,94138218846082+c.lower,94138595391321+c.upper)) = pointBounds12760 := by
 decide +kernel
def cuts12761 : List PrefixCut := [⟨18,149253519,149253627⟩,
⟨70,571318071,571318489⟩,
⟨122,994880115,994880838⟩,
⟨128,1043060909,1043061668⟩]
theorem checked12761 : checkPrefixCuts (2^48) 1676541953 9 Manual.Count131072.C012761.packed 128 cuts12761 = true := by
 decide +kernel
def pointBounds12761 : List (Nat × Nat × Nat) := [(1676560384,94139389246953,94139765793053),(1676613632,94139811311505,94140187857915),(1676666880,94140234873549,94140611420264)]
theorem point_links_checked12761 : (cuts12761.take 3).map (fun c => (1676541953-1+2*2^9*c.k,94139239993434+c.lower,94139616539426+c.upper)) = pointBounds12761 := by
 decide +kernel
def cuts12762 : List PrefixCut := [⟨46,375199838,375200115⟩,
⟨98,782955147,782955726⟩,
⟨128,1028710161,1028710918⟩]
theorem checked12762 : checkPrefixCuts (2^48) 1676673025 9 Manual.Count131072.C012762.packed 128 cuts12762 = true := by
 decide +kernel
def pointBounds12762 : List (Nat × Nat × Nat) := [(1676720128,94140658254181,94141034801209),(1676773376,94141066009490,94141442556820)]
theorem point_links_checked12762 : (cuts12762.take 2).map (fun c => (1676673025-1+2*2^9*c.k,94140283054343+c.lower,94140659601094+c.upper)) = pointBounds12762 := by
 decide +kernel
def cuts12763 : List PrefixCut := [⟨22,179277440,179277568⟩,
⟨74,603624909,603625344⟩,
⟨126,1031819412,1031820158⟩,
⟨128,1046758141,1046758898⟩]
theorem checked12763 : checkPrefixCuts (2^48) 1676804097 9 Manual.Count131072.C012763.packed 128 cuts12763 = true := by
 decide +kernel
def pointBounds12763 : List (Nat × Nat × Nat) := [(1676826624,94141491041944,94141867589580),(1676879872,94141915389413,94142291937356),(1676933120,94142343583916,94142720132170)]
theorem point_links_checked12763 : (cuts12763.take 3).map (fun c => (1676804097-1+2*2^9*c.k,94141311764504+c.lower,94141688312012+c.upper)) = pointBounds12763 := by
 decide +kernel
def cuts12764 : List PrefixCut := [⟨50,400989363,400989655⟩,
⟨102,830331816,830332417⟩,
⟨128,1043823022,1043823777⟩]
theorem checked12764 : checkPrefixCuts (2^48) 1676935169 9 Manual.Count131072.C012764.packed 128 cuts12764 = true := by
 decide +kernel
def pointBounds12764 : List (Nat × Nat × Nat) := [(1676986368,94142759512008,94143136060565),(1677039616,94143188854461,94143565403327)]
theorem point_links_checked12764 : (cuts12764.take 2).map (fun c => (1676935169-1+2*2^9*c.k,94142358522645+c.lower,94142735070910+c.upper)) = pointBounds12764 := by
 decide +kernel
def cuts12765 : List PrefixCut := [⟨26,212984310,212984462⟩,
⟨78,631390426,631390883⟩,
⟨128,1030483319,1030484073⟩]
theorem checked12765 : checkPrefixCuts (2^48) 1677066241 9 Manual.Count131072.C012765.packed 128 cuts12765 = true := by
 decide +kernel
def pointBounds12765 : List (Nat × Nat × Nat) := [(1677092864,94143615329977,94143991879149),(1677146112,94144033736093,94144410285570)]
theorem point_links_checked12765 : (cuts12765.take 2).map (fun c => (1677066241-1+2*2^9*c.k,94143402345667+c.lower,94143778894687+c.upper)) = pointBounds12765 := by
 decide +kernel
def cuts12766 : List PrefixCut := [⟨2,13929428,13929439⟩,
⟨54,431637597,431637914⟩,
⟨106,854366905,854367535⟩,
⟨128,1028388521,1028389279⟩]
theorem checked12766 : checkPrefixCuts (2^48) 1677197313 9 Manual.Count131072.C012766.packed 128 cuts12766 = true := by
 decide +kernel
def pointBounds12766 : List (Nat × Nat × Nat) := [(1677199360,94144446758414,94144823308199),(1677252608,94144864466583,94145241016674),(1677305856,94145287195891,94145663746295)]
theorem point_links_checked12766 : (cuts12766.take 3).map (fun c => (1677197313-1+2*2^9*c.k,94144432828986+c.lower,94144809378760+c.upper)) = pointBounds12766 := by
 decide +kernel
def cuts12767 : List PrefixCut := [⟨30,246009351,246009531⟩,
⟨82,670725534,670726025⟩,
⟨128,1043746361,1043747126⟩]
theorem checked12767 : checkPrefixCuts (2^48) 1677328385 9 Manual.Count131072.C012767.packed 128 cuts12767 = true := by
 decide +kernel
def pointBounds12767 : List (Nat × Nat × Nat) := [(1677359104,94145707226858,94146083777570),(1677412352,94146131943041,94146508494064)]
theorem point_links_checked12767 : (cuts12767.take 2).map (fun c => (1677328385-1+2*2^9*c.k,94145461217507+c.lower,94145837768039+c.upper)) = pointBounds12767 := by
 decide +kernel
def cuts12768 : List PrefixCut := [⟨6,51681788,51681825⟩,
⟨58,471840559,471840904⟩,
⟨110,884435470,884436123⟩,
⟨128,1026046955,1026047713⟩]
theorem checked12768 : checkPrefixCuts (2^48) 1677459457 9 Manual.Count131072.C012768.packed 128 cuts12768 = true := by
 decide +kernel
def pointBounds12768 : List (Nat × Nat × Nat) := [(1677465600,94146556645656,94146933196990),(1677518848,94146976804427,94147353356069),(1677572096,94147389399338,94147765951288)]
theorem point_links_checked12768 : (cuts12768.take 3).map (fun c => (1677459457-1+2*2^9*c.k,94146504963868+c.lower,94146881515165+c.upper)) = pointBounds12768 := by
 decide +kernel
def cuts12769 : List PrefixCut := [⟨34,280533969,280534174⟩,
⟨86,702498252,702498768⟩,
⟨128,1050294307,1050295077⟩]
theorem checked12769 : checkPrefixCuts (2^48) 1677590529 9 Manual.Count131072.C012769.packed 128 cuts12769 = true := by
 decide +kernel
def pointBounds12769 : List (Nat × Nat × Nat) := [(1677625344,94147811544792,94148188097052),(1677678592,94148233509075,94148610061646)]
theorem point_links_checked12769 : (cuts12769.take 2).map (fun c => (1677590529-1+2*2^9*c.k,94147531010823+c.lower,94147907562878+c.upper)) = pointBounds12769 := by
 decide +kernel
def cuts12770 : List PrefixCut := [⟨10,82711401,82711461⟩,
⟨62,499951390,499951754⟩,
⟨114,921875550,921876225⟩,
⟨128,1036119919,1036120675⟩]
theorem checked12770 : checkPrefixCuts (2^48) 1677721601 9 Manual.Count131072.C012770.packed 128 cuts12770 = true := by
 decide +kernel
def pointBounds12770 : List (Nat × Nat × Nat) := [(1677731840,94148664016531,94149040569416),(1677785088,94149081256520,94149457809709),(1677838336,94149503180680,94149879734180)]
theorem point_links_checked12770 : (cuts12770.take 3).map (fun c => (1677721601-1+2*2^9*c.k,94148581305130+c.lower,94148957857955+c.upper)) = pointBounds12770 := by
 decide +kernel
def cuts12771 : List PrefixCut := [⟨38,300788338,300788558⟩,
⟨90,716646646,716647177⟩,
⟨128,1024967180,1024967942⟩]
theorem checked12771 : checkPrefixCuts (2^48) 1677852673 9 Manual.Count131072.C012771.packed 128 cuts12771 = true := by
 decide +kernel
def pointBounds12771 : List (Nat × Nat × Nat) := [(1677891584,94149918213387,94150294767188),(1677944832,94150334071695,94150710625807)]
theorem point_links_checked12771 : (cuts12771.take 2).map (fun c => (1677852673-1+2*2^9*c.k,94149617425049+c.lower,94149993978630+c.upper)) = pointBounds12771 := by
 decide +kernel
def cuts12772 : List PrefixCut := [⟨14,115408686,115408771⟩,
⟨66,540466406,540466804⟩,
⟨118,962155843,962156548⟩,
⟨128,1047196619,1047197388⟩]
theorem checked12772 : checkPrefixCuts (2^48) 1677983745 9 Manual.Count131072.C012772.packed 128 cuts12772 = true := by
 decide +kernel
def pointBounds12772 : List (Nat × Nat × Nat) := [(1677998080,94150757800915,94151134355343),(1678051328,94151182858635,94151559413376),(1678104576,94151604548072,94151981103120)]
theorem point_links_checked12772 : (cuts12772.take 3).map (fun c => (1677983745-1+2*2^9*c.k,94150642392229+c.lower,94151018946572+c.upper)) = pointBounds12772 := by
 decide +kernel
def cuts12773 : List PrefixCut := [⟨42,338480395,338480645⟩,
⟨94,763329993,763330554⟩,
⟨128,1048456434,1048457200⟩]
theorem checked12773 : checkPrefixCuts (2^48) 1678114817 9 Manual.Count131072.C012773.packed 128 cuts12773 = true := by
 decide +kernel
def pointBounds12773 : List (Nat × Nat × Nat) := [(1678157824,94152028069243,94152404624605),(1678211072,94152452918841,94152829474514)]
theorem point_links_checked12773 : (cuts12773.take 2).map (fun c => (1678114817-1+2*2^9*c.k,94151689588848+c.lower,94152066143960+c.upper)) = pointBounds12773 := by
 decide +kernel
def cuts12774 : List PrefixCut := [⟨18,144238153,144238260⟩,
⟨70,564196947,564197363⟩,
⟨122,993701935,993702667⟩,
⟨128,1040156743,1040157509⟩]
theorem checked12774 : checkPrefixCuts (2^48) 1678245889 9 Manual.Count131072.C012774.packed 128 cuts12774 = true := by
 decide +kernel
def pointBounds12774 : List (Nat × Nat × Nat) := [(1678264320,94152882283435,94153258839420),(1678317568,94153302242229,94153678798523),(1678370816,94153731747217,94154108303827)]
theorem point_links_checked12774 : (cuts12774.take 3).map (fun c => (1678245889-1+2*2^9*c.k,94152738045282+c.lower,94153114601160+c.upper)) = pointBounds12774 := by
 decide +kernel
def cuts12775 : List PrefixCut := [⟨46,371967881,371968152⟩,
⟨98,793899147,793899728⟩,
⟨128,1042087793,1042088551⟩]
theorem checked12775 : checkPrefixCuts (2^48) 1678376961 9 Manual.Count131072.C012775.packed 128 cuts12775 = true := by
 decide +kernel
def pointBounds12775 : List (Nat × Nat × Nat) := [(1678424064,94154150169906,94154526726821),(1678477312,94154572101172,94154948658397)]
theorem point_links_checked12775 : (cuts12775.take 2).map (fun c => (1678376961-1+2*2^9*c.k,94153778202025+c.lower,94154154758669+c.upper)) = pointBounds12775 := by
 decide +kernel
def cuts12776 : List PrefixCut := [⟨22,182616984,182617117⟩,
⟨74,596807713,596808146⟩,
⟨126,1004277959,1004278692⟩,
⟨128,1020039926,1020040671⟩]
theorem checked12776 : checkPrefixCuts (2^48) 1678508033 9 Manual.Count131072.C012776.packed 128 cuts12776 = true := by
 decide +kernel
def pointBounds12776 : List (Nat × Nat × Nat) := [(1678530560,94155002906802,94155379464337),(1678583808,94155417097531,94155793655366),(1678637056,94155824567777,94156201125912)]
theorem point_links_checked12776 : (cuts12776.take 3).map (fun c => (1678508033-1+2*2^9*c.k,94154820289818+c.lower,94155196847220+c.upper)) = pointBounds12776 := by
 decide +kernel
def cuts12777 : List PrefixCut := [⟨50,411313677,411313979⟩,
⟨102,838040431,838041043⟩,
⟨128,1049805918,1049806684⟩]
theorem checked12777 : checkPrefixCuts (2^48) 1678639105 9 Manual.Count131072.C012777.packed 128 cuts12777 = true := by
 decide +kernel
def pointBounds12777 : List (Nat × Nat × Nat) := [(1678690304,94156251643421,94156628201870),(1678743552,94156678370175,94157054928934)]
theorem point_links_checked12777 : (cuts12777.take 2).map (fun c => (1678639105-1+2*2^9*c.k,94155840329744+c.lower,94156216887891+c.upper)) = pointBounds12777 := by
 decide +kernel
def cuts12778 : List PrefixCut := [⟨26,210253191,210253342⟩,
⟨78,637623594,637624057⟩,
⟨128,1044861827,1044862588⟩]
theorem checked12778 : checkPrefixCuts (2^48) 1678770177 9 Manual.Count131072.C012778.packed 128 cuts12778 = true := by
 decide +kernel
def pointBounds12778 : List (Nat × Nat × Nat) := [(1678796800,94157100388853,94157476947917),(1678850048,94157527759256,94157904318632)]
theorem point_links_checked12778 : (cuts12778.take 2).map (fun c => (1678770177-1+2*2^9*c.k,94156890135662+c.lower,94157266694575+c.upper)) = pointBounds12778 := by
 decide +kernel
def cuts12779 : List PrefixCut := [⟨2,15256525,15256536⟩,
⟨54,431870195,431870514⟩,
⟨106,847464712,847465340⟩,
⟨128,1023321426,1023322187⟩]
theorem checked12779 : checkPrefixCuts (2^48) 1678901249 9 Manual.Count131072.C012779.packed 128 cuts12779 = true := by
 decide +kernel
def pointBounds12779 : List (Nat × Nat × Nat) := [(1678903296,94157950254014,94158326813699),(1678956544,94158366867684,94158743427677),(1679009792,94158782462201,94159159022503)]
theorem point_links_checked12779 : (cuts12779.take 3).map (fun c => (1678901249-1+2*2^9*c.k,94157934997489+c.lower,94158311557163+c.upper)) = pointBounds12779 := by
 decide +kernel
def cuts12780 : List PrefixCut := [⟨30,241401003,241401180⟩,
⟨82,667195024,667195515⟩,
⟨128,1035311333,1035312099⟩]
theorem checked12780 : checkPrefixCuts (2^48) 1679032321 9 Manual.Count131072.C012780.packed 128 cuts12780 = true := by
 decide +kernel
def pointBounds12780 : List (Nat × Nat × Nat) := [(1679063040,94159199719918,94159576280530),(1679116288,94159625513939,94160002074865)]
theorem point_links_checked12780 : (cuts12780.take 2).map (fun c => (1679032321-1+2*2^9*c.k,94158958318915+c.lower,94159334879350+c.upper)) = pointBounds12780 := by
 decide +kernel
def cuts12781 : List PrefixCut := [⟨6,50288323,50288359⟩,
⟨58,472535053,472535401⟩,
⟨110,890410274,890410930⟩,
⟨128,1032548552,1032549314⟩]
theorem checked12781 : checkPrefixCuts (2^48) 1679163393 9 Manual.Count131072.C012781.packed 128 cuts12781 = true := by
 decide +kernel
def pointBounds12781 : List (Nat × Nat × Nat) := [(1679169536,94160043918571,94160420479808),(1679222784,94160466165301,94160842726850),(1679276032,94160884040522,94161260602379)]
theorem point_links_checked12781 : (cuts12781.take 3).map (fun c => (1679163393-1+2*2^9*c.k,94159993630248+c.lower,94160370191449+c.upper)) = pointBounds12781 := by
 decide +kernel
def cuts12782 : List PrefixCut := [⟨34,280919751,280919955⟩,
⟨86,703294042,703294555⟩,
⟨128,1028613513,1028614264⟩]
theorem checked12782 : checkPrefixCuts (2^48) 1679294465 9 Manual.Count131072.C012782.packed 128 cuts12782 = true := by
 decide +kernel
def pointBounds12782 : List (Nat × Nat × Nat) := [(1679329280,94161307098551,94161683660718),(1679382528,94161729472842,94162106035318)]
theorem point_links_checked12782 : (cuts12782.take 2).map (fun c => (1679294465-1+2*2^9*c.k,94161026178800+c.lower,94161402740763+c.upper)) = pointBounds12782 := by
 decide +kernel
def cuts12783 : List PrefixCut := [⟨10,81957065,81957125⟩,
⟨62,507824093,507824472⟩,
⟨114,926135900,926136588⟩,
⟨128,1040264361,1040265131⟩]
theorem checked12783 : checkPrefixCuts (2^48) 1679425537 9 Manual.Count131072.C012783.packed 128 cuts12783 = true := by
 decide +kernel
def pointBounds12783 : List (Nat × Nat × Nat) := [(1679435776,94162136749378,94162513312152),(1679489024,94162562616406,94162939179499),(1679542272,94162980928213,94163357491615)]
theorem point_links_checked12783 : (cuts12783.take 3).map (fun c => (1679425537-1+2*2^9*c.k,94162054792313+c.lower,94162431355027+c.upper)) = pointBounds12783 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000086
