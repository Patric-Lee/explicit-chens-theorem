import PlattAssemblyKernel
import PlattCertificates.Count131072.C011792
import PlattCertificates.Count131072.C011793
import PlattCertificates.Count131072.C011794
import PlattCertificates.Count131072.C011795
import PlattCertificates.Count131072.C011796
import PlattCertificates.Count131072.C011797
import PlattCertificates.Count131072.C011798
import PlattCertificates.Count131072.C011799
import PlattCertificates.Count131072.C011800
import PlattCertificates.Count131072.C011801
import PlattCertificates.Count131072.C011802
import PlattCertificates.Count131072.C011803
import PlattCertificates.Count131072.C011804
import PlattCertificates.Count131072.C011805
import PlattCertificates.Count131072.C011806
import PlattCertificates.Count131072.C011807
import PlattCertificates.Count131072.C011808
import PlattCertificates.Count131072.C011809
import PlattCertificates.Count131072.C011810
import PlattCertificates.Count131072.C011811
import PlattCertificates.Count131072.C011812
import PlattCertificates.Count131072.C011813
import PlattCertificates.Count131072.C011814
import PlattCertificates.Count131072.C011815
import PlattCertificates.Count131072.C011816
import PlattCertificates.Count131072.C011817
import PlattCertificates.Count131072.C011818
import PlattCertificates.Count131072.C011819
import PlattCertificates.Count131072.C011820
import PlattCertificates.Count131072.C011821
import PlattCertificates.Count131072.C011822
import PlattCertificates.Count131072.C011823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11792 : List PrefixCut := [⟨25,223974293,223974464⟩,
⟨73,643212135,643212628⟩,
⟨121,1056987469,1056988285⟩,
⟨128,1115837681,1115838543⟩]
theorem checked11792 : checkPrefixCuts (2^48) 1549533185 9 Manual.Count131072.C011792.packed 128 cuts11792 = true := by
 decide +kernel
def pointBounds11792 : List (Nat × Nat × Nat) := [(1549558784,93093668557055,93094044314569),(1549607936,93094087794897,93094463552733),(1549657088,93094501570231,93094877328390)]
theorem point_links_checked11792 : (cuts11792.take 3).map (fun c => (1549533185-1+2*2^9*c.k,93093444582762+c.lower,93093820340105+c.upper)) = pointBounds11792 := by
 decide +kernel
def cuts11793 : List PrefixCut := [⟨41,363267194,363267478⟩,
⟨89,789548744,789549356⟩,
⟨128,1140444426,1140445310⟩]
theorem checked11793 : checkPrefixCuts (2^48) 1549664257 9 Manual.Count131072.C011793.packed 128 cuts11793 = true := by
 decide +kernel
def pointBounds11793 : List (Nat × Nat × Nat) := [(1549706240,93094923687637,93095299446126),(1549755392,93095349969187,93095725728004)]
theorem point_links_checked11793 : (cuts11793.take 2).map (fun c => (1549664257-1+2*2^9*c.k,93094560420443+c.lower,93094936178648+c.upper)) = pointBounds11793 := by
 decide +kernel
def cuts11794 : List PrefixCut := [⟨9,81365820,81365884⟩,
⟨57,502716549,502716945⟩,
⟨105,937311569,937312300⟩,
⟨128,1144888001,1144888895⟩]
theorem checked11794 : checkPrefixCuts (2^48) 1549795329 9 Manual.Count131072.C011794.packed 128 cuts11794 = true := by
 decide +kernel
def pointBounds11794 : List (Nat × Nat × Nat) := [(1549804544,93095782230689,93096157989842),(1549853696,93096203581418,93096579340903),(1549902848,93096638176438,93097013936258)]
theorem point_links_checked11794 : (cuts11794.take 3).map (fun c => (1549795329-1+2*2^9*c.k,93095700864869+c.lower,93096076623958+c.upper)) = pointBounds11794 := by
 decide +kernel
def cuts11795 : List PrefixCut := [⟨25,209389199,209389362⟩,
⟨73,630336682,630337178⟩,
⟨121,1041828004,1041828817⟩,
⟨128,1103568730,1103569590⟩]
theorem checked11795 : checkPrefixCuts (2^48) 1549926401 9 Manual.Count131072.C011795.packed 128 cuts11795 = true := by
 decide +kernel
def pointBounds11795 : List (Nat × Nat × Nat) := [(1549952000,93097055142069,93097430902215),(1550001152,93097476089552,93097851850031),(1550050304,93097887580874,93098263341670)]
theorem point_links_checked11795 : (cuts11795.take 3).map (fun c => (1549926401-1+2*2^9*c.k,93096845752870+c.lower,93097221512853+c.upper)) = pointBounds11795 := by
 decide +kernel
def cuts11796 : List PrefixCut := [⟨41,367714694,367714977⟩,
⟨89,790619573,790620185⟩,
⟨128,1137431613,1137432497⟩]
theorem checked11796 : checkPrefixCuts (2^48) 1550057473 9 Manual.Count131072.C011796.packed 128 cuts11796 = true := by
 decide +kernel
def pointBounds11796 : List (Nat × Nat × Nat) := [(1550099456,93098317036294,93098692797420),(1550148608,93098739941173,93099115702628)]
theorem point_links_checked11796 : (cuts11796.take 2).map (fun c => (1550057473-1+2*2^9*c.k,93097949321600+c.lower,93098325082443+c.upper)) = pointBounds11796 := by
 decide +kernel
def cuts11797 : List PrefixCut := [⟨9,80982027,80982091⟩,
⟨57,507672958,507673351⟩,
⟨105,926179979,926180699⟩,
⟨128,1124807289,1124808164⟩]
theorem checked11797 : checkPrefixCuts (2^48) 1550188545 9 Manual.Count131072.C011797.packed 128 cuts11797 = true := by
 decide +kernel
def pointBounds11797 : List (Nat × Nat × Nat) := [(1550197760,93099167735240,93099543497031),(1550246912,93099594426171,93099970188291),(1550296064,93100012933192,93100388695639)]
theorem point_links_checked11797 : (cuts11797.take 3).map (fun c => (1550188545-1+2*2^9*c.k,93099086753213+c.lower,93099462514940+c.upper)) = pointBounds11797 := by
 decide +kernel
def cuts11798 : List PrefixCut := [⟨25,218595572,218595737⟩,
⟨73,636531432,636531923⟩,
⟨121,1064983797,1064984615⟩,
⟨128,1127616590,1127617458⟩]
theorem checked11798 : checkPrefixCuts (2^48) 1550319617 9 Manual.Count131072.C011798.packed 128 cuts11798 = true := by
 decide +kernel
def pointBounds11798 : List (Nat × Nat × Nat) := [(1550345216,93100430156074,93100805918841),(1550394368,93100848091934,93101223855027),(1550443520,93101276544299,93101652307719)]
theorem point_links_checked11798 : (cuts11798.take 3).map (fun c => (1550319617-1+2*2^9*c.k,93100211560502+c.lower,93100587323104+c.upper)) = pointBounds11798 := by
 decide +kernel
def cuts11799 : List PrefixCut := [⟨41,355276674,355276954⟩,
⟨89,782794173,782794780⟩,
⟨128,1125524519,1125525394⟩]
theorem checked11799 : checkPrefixCuts (2^48) 1550450689 9 Manual.Count131072.C011799.packed 128 cuts11799 = true := by
 decide +kernel
def pointBounds11799 : List (Nat × Nat × Nat) := [(1550492672,93101694453766,93102070217516),(1550541824,93102121971265,93102497735342)]
theorem point_links_checked11799 : (cuts11799.take 2).map (fun c => (1550450689-1+2*2^9*c.k,93101339177092+c.lower,93101714940562+c.upper)) = pointBounds11799 := by
 decide +kernel
def cuts11800 : List PrefixCut := [⟨9,76060241,76060301⟩,
⟨57,508270274,508270667⟩,
⟨105,935020999,935021724⟩,
⟨128,1141403119,1141404002⟩]
theorem checked11800 : checkPrefixCuts (2^48) 1550581761 9 Manual.Count131072.C011800.packed 128 cuts11800 = true := by
 decide +kernel
def pointBounds11800 : List (Nat × Nat × Nat) := [(1550590976,93102540761852,93102916526257),(1550640128,93102972971885,93103348736623),(1550689280,93103399722610,93103775487680)]
theorem point_links_checked11800 : (cuts11800.take 3).map (fun c => (1550581761-1+2*2^9*c.k,93102464701611+c.lower,93102840465956+c.upper)) = pointBounds11800 := by
 decide +kernel
def cuts11801 : List PrefixCut := [⟨25,217269507,217269676⟩,
⟨73,647804858,647805362⟩,
⟨121,1069432975,1069433800⟩,
⟨128,1128056925,1128057798⟩]
theorem checked11801 : checkPrefixCuts (2^48) 1550712833 9 Manual.Count131072.C011801.packed 128 cuts11801 = true := by
 decide +kernel
def pointBounds11801 : List (Nat × Nat × Nat) := [(1550738432,93103823374237,93104199139634),(1550787584,93104253909588,93104629675320),(1550836736,93104675537705,93105051303758)]
theorem point_links_checked11801 : (cuts11801.take 3).map (fun c => (1550712833-1+2*2^9*c.k,93103606104730+c.lower,93103981869958+c.upper)) = pointBounds11801 := by
 decide +kernel
def cuts11802 : List PrefixCut := [⟨41,366257747,366258025⟩,
⟨89,787677674,787678278⟩,
⟨128,1134495201,1134496077⟩]
theorem checked11802 : checkPrefixCuts (2^48) 1550843905 9 Manual.Count131072.C011802.packed 128 cuts11802 = true := by
 decide +kernel
def pointBounds11802 : List (Nat × Nat × Nat) := [(1550885888,93105100419402,93105476185781),(1550935040,93105521839329,93105897606034)]
theorem point_links_checked11802 : (cuts11802.take 2).map (fun c => (1550843905-1+2*2^9*c.k,93104734161655+c.lower,93105109927756+c.upper)) = pointBounds11802 := by
 decide +kernel
def cuts11803 : List PrefixCut := [⟨9,79307628,79307689⟩,
⟨57,496163868,496164256⟩,
⟨105,911918130,911918841⟩,
⟨128,1117340581,1117341452⟩]
theorem checked11803 : checkPrefixCuts (2^48) 1550974977 9 Manual.Count131072.C011803.packed 128 cuts11803 = true := by
 decide +kernel
def pointBounds11803 : List (Nat × Nat × Nat) := [(1550984192,93105947964484,93106323731522),(1551033344,93106364820724,93106740588089),(1551082496,93106780574986,93107156342674)]
theorem point_links_checked11803 : (cuts11803.take 3).map (fun c => (1550974977-1+2*2^9*c.k,93105868656856+c.lower,93106244423833+c.upper)) = pointBounds11803 := by
 decide +kernel
def cuts11804 : List PrefixCut := [⟨25,221751086,221751257⟩,
⟨73,647459380,647459882⟩,
⟨121,1073154098,1073154927⟩,
⟨128,1132307540,1132308417⟩]
theorem checked11804 : checkPrefixCuts (2^48) 1551106049 9 Manual.Count131072.C011804.packed 128 cuts11804 = true := by
 decide +kernel
def pointBounds11804 : List (Nat × Nat × Nat) := [(1551131648,93107207748523,93107583516542),(1551180800,93107633456817,93108009225167),(1551229952,93108059151535,93108434920212)]
theorem point_links_checked11804 : (cuts11804.take 3).map (fun c => (1551106049-1+2*2^9*c.k,93106985997437+c.lower,93107361765285+c.upper)) = pointBounds11804 := by
 decide +kernel
def cuts11805 : List PrefixCut := [⟨41,356366613,356366884⟩,
⟨89,779857090,779857686⟩,
⟨128,1122050824,1122051684⟩]
theorem checked11805 : checkPrefixCuts (2^48) 1551237121 9 Manual.Count131072.C011805.packed 128 cuts11805 = true := by
 decide +kernel
def pointBounds11805 : List (Nat × Nat × Nat) := [(1551279104,93108474671590,93108850440586),(1551328256,93108898162067,93109273931388)]
theorem point_links_checked11805 : (cuts11805.take 2).map (fun c => (1551237121-1+2*2^9*c.k,93108118304977+c.lower,93108494073702+c.upper)) = pointBounds11805 := by
 decide +kernel
def cuts11806 : List PrefixCut := [⟨9,83279126,83279192⟩,
⟨57,500392681,500393067⟩,
⟨105,929648563,929649282⟩,
⟨128,1128124863,1128125735⟩]
theorem checked11806 : checkPrefixCuts (2^48) 1551368193 9 Manual.Count131072.C011806.packed 128 cuts11806 = true := by
 decide +kernel
def pointBounds11806 : List (Nat × Nat × Nat) := [(1551377408,93109323634927,93109699404578),(1551426560,93109740748482,93110116518453),(1551475712,93110170004364,93110545774668)]
theorem point_links_checked11806 : (cuts11806.take 3).map (fun c => (1551368193-1+2*2^9*c.k,93109240355801+c.lower,93109616125386+c.upper)) = pointBounds11806 := by
 decide +kernel
def cuts11807 : List PrefixCut := [⟨25,213893829,213893996⟩,
⟨73,631330532,631331020⟩,
⟨121,1051656659,1051657474⟩,
⟨128,1113516201,1113517064⟩]
theorem checked11807 : checkPrefixCuts (2^48) 1551499265 9 Manual.Count131072.C011807.packed 128 cuts11807 = true := by
 decide +kernel
def pointBounds11807 : List (Nat × Nat × Nat) := [(1551524864,93110582374493,93110958145117),(1551574016,93110999811196,93111375582141),(1551623168,93111420137323,93111795908595)]
theorem point_links_checked11807 : (cuts11807.take 3).map (fun c => (1551499265-1+2*2^9*c.k,93110368480664+c.lower,93110744251121+c.upper)) = pointBounds11807 := by
 decide +kernel
def cuts11808 : List PrefixCut := [⟨41,362444106,362444387⟩,
⟨89,782924974,782925580⟩,
⟨128,1127390051,1127390921⟩]
theorem checked11808 : checkPrefixCuts (2^48) 1551630337 9 Manual.Count131072.C011808.packed 128 cuts11808 = true := by
 decide +kernel
def pointBounds11808 : List (Nat × Nat × Nat) := [(1551672320,93111844440971,93112220212572),(1551721472,93112264921839,93112640693765)]
theorem point_links_checked11808 : (cuts11808.take 2).map (fun c => (1551630337-1+2*2^9*c.k,93111481996865+c.lower,93111857768185+c.upper)) = pointBounds11808 := by
 decide +kernel
def cuts11809 : List PrefixCut := [⟨9,78541884,78541944⟩,
⟨57,498995990,498996375⟩,
⟨105,927598921,927599640⟩,
⟨128,1127475971,1127476842⟩]
theorem checked11809 : checkPrefixCuts (2^48) 1551761409 9 Manual.Count131072.C011809.packed 128 cuts11809 = true := by
 decide +kernel
def pointBounds11809 : List (Nat × Nat × Nat) := [(1551770624,93112687928800,93113063701050),(1551819776,93113108382906,93113484155481),(1551868928,93113536985837,93113912758746)]
theorem point_links_checked11809 : (cuts11809.take 3).map (fun c => (1551761409-1+2*2^9*c.k,93112609386916+c.lower,93112985159106+c.upper)) = pointBounds11809 := by
 decide +kernel
def cuts11810 : List PrefixCut := [⟨25,223633829,223634001⟩,
⟨73,640601953,640602452⟩,
⟨121,1057738225,1057739049⟩,
⟨128,1119763462,1119764336⟩]
theorem checked11810 : checkPrefixCuts (2^48) 1551892481 9 Manual.Count131072.C011810.packed 128 cuts11810 = true := by
 decide +kernel
def pointBounds11810 : List (Nat × Nat × Nat) := [(1551918080,93113960496716,93114336269949),(1551967232,93114377464840,93114753238400),(1552016384,93114794601112,93115170374997)]
theorem point_links_checked11810 : (cuts11810.take 3).map (fun c => (1551892481-1+2*2^9*c.k,93113736862887+c.lower,93114112635948+c.upper)) = pointBounds11810 := by
 decide +kernel
def cuts11811 : List PrefixCut := [⟨41,362352239,362352521⟩,
⟨89,767674210,767674807⟩,
⟨128,1114228156,1114229018⟩]
theorem checked11811 : checkPrefixCuts (2^48) 1552023553 9 Manual.Count131072.C011811.packed 128 cuts11811 = true := by
 decide +kernel
def pointBounds11811 : List (Nat × Nat × Nat) := [(1552065536,93115218978588,93115594752805),(1552114688,93115624300559,93116000075091)]
theorem point_links_checked11811 : (cuts11811.take 2).map (fun c => (1552023553-1+2*2^9*c.k,93114856626349+c.lower,93115232400284+c.upper)) = pointBounds11811 := by
 decide +kernel
def cuts11812 : List PrefixCut := [⟨9,78159291,78159351⟩,
⟨57,493066690,493067072⟩,
⟨105,915939713,915940428⟩,
⟨128,1115766125,1115766993⟩]
theorem checked11812 : checkPrefixCuts (2^48) 1552154625 9 Manual.Count131072.C011812.packed 128 cuts11812 = true := by
 decide +kernel
def pointBounds11812 : List (Nat × Nat × Nat) := [(1552163840,93116049013796,93116424788653),(1552212992,93116463921195,93116839696374),(1552262144,93116886794218,93117262569730)]
theorem point_links_checked11812 : (cuts11812.take 3).map (fun c => (1552154625-1+2*2^9*c.k,93115970854505+c.lower,93116346629302+c.upper)) = pointBounds11812 := by
 decide +kernel
def cuts11813 : List PrefixCut := [⟨25,217774694,217774862⟩,
⟨73,636994480,636994968⟩,
⟨121,1060915262,1060916078⟩,
⟨128,1120930328,1120931191⟩]
theorem checked11813 : checkPrefixCuts (2^48) 1552285697 9 Manual.Count131072.C011813.packed 128 cuts11813 = true := by
 decide +kernel
def pointBounds11813 : List (Nat × Nat × Nat) := [(1552311296,93117304395324,93117680171157),(1552360448,93117723615110,93118099391263),(1552409600,93118147535892,93118523312373)]
theorem point_links_checked11813 : (cuts11813.take 3).map (fun c => (1552285697-1+2*2^9*c.k,93117086620630+c.lower,93117462396295+c.upper)) = pointBounds11813 := by
 decide +kernel
def cuts11814 : List PrefixCut := [⟨41,364798758,364799041⟩,
⟨89,782890822,782891435⟩,
⟨128,1124462000,1124462876⟩]
theorem checked11814 : checkPrefixCuts (2^48) 1552416769 9 Manual.Count131072.C011814.packed 128 cuts11814 = true := by
 decide +kernel
def pointBounds11814 : List (Nat × Nat × Nat) := [(1552458752,93118572349716,93118948126527),(1552507904,93118990441780,93119366218921)]
theorem point_links_checked11814 : (cuts11814.take 2).map (fun c => (1552416769-1+2*2^9*c.k,93118207550958+c.lower,93118583327486+c.upper)) = pointBounds11814 := by
 decide +kernel
def cuts11815 : List PrefixCut := [⟨9,83215847,83215911⟩,
⟨57,504182191,504182578⟩,
⟨105,920784325,920785037⟩,
⟨128,1124729662,1124730534⟩]
theorem checked11815 : checkPrefixCuts (2^48) 1552547841 9 Manual.Count131072.C011815.packed 128 cuts11815 = true := by
 decide +kernel
def pointBounds11815 : List (Nat × Nat × Nat) := [(1552557056,93119415228805,93119791006273),(1552606208,93119836195149,93120211972940),(1552655360,93120252797283,93120628575399)]
theorem point_links_checked11815 : (cuts11815.take 3).map (fun c => (1552547841-1+2*2^9*c.k,93119332012958+c.lower,93119707790362+c.upper)) = pointBounds11815 := by
 decide +kernel
def cuts11816 : List PrefixCut := [⟨25,214275218,214275384⟩,
⟨73,632845014,632845506⟩,
⟨121,1055752068,1055752886⟩,
⟨128,1117383349,1117384215⟩]
theorem checked11816 : checkPrefixCuts (2^48) 1552678913 9 Manual.Count131072.C011816.packed 128 cuts11816 = true := by
 decide +kernel
def pointBounds11816 : List (Nat × Nat × Nat) := [(1552704512,93120671017838,93121046796280),(1552753664,93121089587634,93121465366402),(1552802816,93121512494688,93121888273782)]
theorem point_links_checked11816 : (cuts11816.take 3).map (fun c => (1552678913-1+2*2^9*c.k,93120456742620+c.lower,93120832520896+c.upper)) = pointBounds11816 := by
 decide +kernel
def cuts11817 : List PrefixCut := [⟨41,368331708,368331990⟩,
⟨89,797737309,797737923⟩,
⟨128,1141759416,1141760295⟩]
theorem checked11817 : checkPrefixCuts (2^48) 1552809985 9 Manual.Count131072.C011817.packed 128 cuts11817 = true := by
 decide +kernel
def pointBounds11817 : List (Nat × Nat × Nat) := [(1552851968,93121942457677,93122318237101),(1552901120,93122371863278,93122747643034)]
theorem point_links_checked11817 : (cuts11817.take 2).map (fun c => (1552809985-1+2*2^9*c.k,93121574125969+c.lower,93121949905111+c.upper)) = pointBounds11817 := by
 decide +kernel
def cuts11818 : List PrefixCut := [⟨9,76307186,76307245⟩,
⟨57,489735852,489736227⟩,
⟨105,905326163,905326860⟩,
⟨128,1107045008,1107045861⟩]
theorem checked11818 : checkPrefixCuts (2^48) 1552941057 9 Manual.Count131072.C011818.packed 128 cuts11818 = true := by
 decide +kernel
def pointBounds11818 : List (Nat × Nat × Nat) := [(1552950272,93122792192571,93123167972651),(1552999424,93123205621237,93123581401633),(1553048576,93123621211548,93123996992266)]
theorem point_links_checked11818 : (cuts11818.take 3).map (fun c => (1552941057-1+2*2^9*c.k,93122715885385+c.lower,93123091665406+c.upper)) = pointBounds11818 := by
 decide +kernel
def cuts11819 : List PrefixCut := [⟨25,220926646,220926818⟩,
⟨73,641927780,641928275⟩,
⟨121,1060559553,1060560370⟩,
⟨128,1122900129,1122900994⟩]
theorem checked11819 : checkPrefixCuts (2^48) 1553072129 9 Manual.Count131072.C011819.packed 128 cuts11819 = true := by
 decide +kernel
def pointBounds11819 : List (Nat × Nat × Nat) := [(1553097728,93124043857039,93124419638085),(1553146880,93124464858173,93124840639542),(1553196032,93124883489946,93125259271637)]
theorem point_links_checked11819 : (cuts11819.take 3).map (fun c => (1553072129-1+2*2^9*c.k,93123822930393+c.lower,93124198711267+c.upper)) = pointBounds11819 := by
 decide +kernel
def cuts11820 : List PrefixCut := [⟨41,362801858,362802143⟩,
⟨89,776514380,776514989⟩,
⟨128,1118274966,1118275838⟩]
theorem checked11820 : checkPrefixCuts (2^48) 1553203201 9 Manual.Count131072.C011820.packed 128 cuts11820 = true := by
 decide +kernel
def pointBounds11820 : List (Nat × Nat × Nat) := [(1553245184,93125308632380,93125684414404),(1553294336,93125722344902,93126098127250)]
theorem point_links_checked11820 : (cuts11820.take 2).map (fun c => (1553203201-1+2*2^9*c.k,93124945830522+c.lower,93125321612261+c.upper)) = pointBounds11820 := by
 decide +kernel
def cuts11821 : List PrefixCut := [⟨9,79549586,79549647⟩,
⟨57,505195233,505195623⟩,
⟨105,928653178,928653893⟩,
⟨128,1132676458,1132677332⟩]
theorem checked11821 : checkPrefixCuts (2^48) 1553334273 9 Manual.Count131072.C011821.packed 128 cuts11821 = true := by
 decide +kernel
def pointBounds11821 : List (Nat × Nat × Nat) := [(1553343488,93126143655074,93126519437746),(1553392640,93126569300721,93126945083722),(1553441792,93126992758666,93127368541992)]
theorem point_links_checked11821 : (cuts11821.take 3).map (fun c => (1553334273-1+2*2^9*c.k,93126064105488+c.lower,93126439888099+c.upper)) = pointBounds11821 := by
 decide +kernel
def cuts11822 : List PrefixCut := [⟨25,215978613,215978781⟩,
⟨73,638866186,638866677⟩,
⟨121,1056848479,1056849292⟩,
⟨128,1120079162,1120080023⟩]
theorem checked11822 : checkPrefixCuts (2^48) 1553465345 9 Manual.Count131072.C011822.packed 128 cuts11822 = true := by
 decide +kernel
def pointBounds11822 : List (Nat × Nat × Nat) := [(1553490944,93127412760559,93127788544212),(1553540096,93127835648132,93128211432108),(1553589248,93128253630425,93128629414723)]
theorem point_links_checked11822 : (cuts11822.take 3).map (fun c => (1553465345-1+2*2^9*c.k,93127196781946+c.lower,93127572565431+c.upper)) = pointBounds11822 := by
 decide +kernel
def cuts11823 : List PrefixCut := [⟨41,352201995,352202268⟩,
⟨89,775592954,775593553⟩,
⟨128,1115274310,1115275171⟩]
theorem checked11823 : checkPrefixCuts (2^48) 1553596417 9 Manual.Count131072.C011823.packed 128 cuts11823 = true := by
 decide +kernel
def pointBounds11823 : List (Nat × Nat × Nat) := [(1553638400,93128669063103,93129044847722),(1553687552,93129092454062,93129468239007)]
theorem point_links_checked11823 : (cuts11823.take 2).map (fun c => (1553596417-1+2*2^9*c.k,93128316861108+c.lower,93128692645454+c.upper)) = pointBounds11823 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000056
