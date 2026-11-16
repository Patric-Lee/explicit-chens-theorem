import PlattAssemblyKernel
import PlattCertificates.Count131072.C014672
import PlattCertificates.Count131072.C014673
import PlattCertificates.Count131072.C014674
import PlattCertificates.Count131072.C014675
import PlattCertificates.Count131072.C014676
import PlattCertificates.Count131072.C014677
import PlattCertificates.Count131072.C014678
import PlattCertificates.Count131072.C014679
import PlattCertificates.Count131072.C014680
import PlattCertificates.Count131072.C014681
import PlattCertificates.Count131072.C014682
import PlattCertificates.Count131072.C014683
import PlattCertificates.Count131072.C014684
import PlattCertificates.Count131072.C014685
import PlattCertificates.Count131072.C014686
import PlattCertificates.Count131072.C014687
import PlattCertificates.Count131072.C014688
import PlattCertificates.Count131072.C014689
import PlattCertificates.Count131072.C014690
import PlattCertificates.Count131072.C014691
import PlattCertificates.Count131072.C014692
import PlattCertificates.Count131072.C014693
import PlattCertificates.Count131072.C014694
import PlattCertificates.Count131072.C014695
import PlattCertificates.Count131072.C014696
import PlattCertificates.Count131072.C014697
import PlattCertificates.Count131072.C014698
import PlattCertificates.Count131072.C014699
import PlattCertificates.Count131072.C014700
import PlattCertificates.Count131072.C014701
import PlattCertificates.Count131072.C014702
import PlattCertificates.Count131072.C014703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000146
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14672 : List PrefixCut := [⟨46,324411691,324411909⟩,
⟨105,736889482,736889977⟩,
⟨128,901351196,901351800⟩]
theorem checked14672 : checkPrefixCuts (2^48) 1927020545 9 Manual.Count131072.C014672.packed 128 cuts14672 = true := by
 decide +kernel
def pointBounds14672 : List (Nat × Nat × Nat) := [(1927067648,95978689920225,95979067759822),(1927128064,95979102398016,95979480237890)]
theorem point_links_checked14672 : (cuts14672.take 2).map (fun c => (1927020545-1+2*2^9*c.k,95978365508534+c.lower,95978743347913+c.upper)) = pointBounds14672 := by
 decide +kernel
def cuts14673 : List PrefixCut := [⟨36,252530983,252531153⟩,
⟨95,671409268,671409719⟩,
⟨128,899099359,899099962⟩]
theorem checked14673 : checkPrefixCuts (2^48) 1927151617 9 Manual.Count131072.C014673.packed 128 cuts14673 = true := by
 decide +kernel
def pointBounds14673 : List (Nat × Nat × Nat) := [(1927188480,95979519390713,95979897230866),(1927248896,95979938268998,95980316109432)]
theorem point_links_checked14673 : (cuts14673.take 2).map (fun c => (1927151617-1+2*2^9*c.k,95979266859730+c.lower,95979644699713+c.upper)) = pointBounds14673 := by
 decide +kernel
def cuts14674 : List PrefixCut := [⟨26,177884647,177884766⟩,
⟨85,590748914,590749305⟩,
⟨128,894656678,894657272⟩]
theorem checked14674 : checkPrefixCuts (2^48) 1927282689 9 Manual.Count131072.C014674.packed 128 cuts14674 = true := by
 decide +kernel
def pointBounds14674 : List (Nat × Nat × Nat) := [(1927309312,95980343843736,95980721684441),(1927369728,95980756708003,95981134548980)]
theorem point_links_checked14674 : (cuts14674.take 2).map (fun c => (1927282689-1+2*2^9*c.k,95980165959089+c.lower,95980543799675+c.upper)) = pointBounds14674 := by
 decide +kernel
def cuts14675 : List PrefixCut := [⟨16,114785064,114785140⟩,
⟨75,517401006,517401353⟩,
⟨128,888170598,888171189⟩]
theorem checked14675 : checkPrefixCuts (2^48) 1927413761 9 Manual.Count131072.C014675.packed 128 cuts14675 = true := by
 decide +kernel
def pointBounds14675 : List (Nat × Nat × Nat) := [(1927430144,95981175400831,95981553242087),(1927490560,95981578016773,95981955858300)]
theorem point_links_checked14675 : (cuts14675.take 2).map (fun c => (1927413761-1+2*2^9*c.k,95981060615767+c.lower,95981438456947+c.upper)) = pointBounds14675 := by
 decide +kernel
def cuts14676 : List PrefixCut := [⟨6,44976450,44976480⟩,
⟨65,459833281,459833589⟩,
⟨124,870296424,870297007⟩,
⟨128,897601769,897602372⟩]
theorem checked14676 : checkPrefixCuts (2^48) 1927544833 9 Manual.Count131072.C014676.packed 128 cuts14676 = true := by
 decide +kernel
def pointBounds14676 : List (Nat × Nat × Nat) := [(1927550976,95981993762815,95982371604616),(1927611392,95982408619646,95982786461725),(1927671808,95982819082789,95983196925143)]
theorem point_links_checked14676 : (cuts14676.take 3).map (fun c => (1927544833-1+2*2^9*c.k,95981948786365+c.lower,95982326628136+c.upper)) = pointBounds14676 := by
 decide +kernel
def cuts14677 : List PrefixCut := [⟨55,394972167,394972433⟩,
⟨114,824245004,824245557⟩,
⟨128,915938253,915938869⟩]
theorem checked14677 : checkPrefixCuts (2^48) 1927675905 9 Manual.Count131072.C014677.packed 128 cuts14677 = true := by
 decide +kernel
def pointBounds14677 : List (Nat × Nat × Nat) := [(1927732224,95983241360301,95983619202941),(1927792640,95983670633138,95984048476065)]
theorem point_links_checked14677 : (cuts14677.take 2).map (fun c => (1927675905-1+2*2^9*c.k,95982846388134+c.lower,95983224230508+c.upper)) = pointBounds14677 := by
 decide +kernel
def cuts14678 : List PrefixCut := [⟨45,315519158,315519371⟩,
⟨104,731186985,731187479⟩,
⟨128,899669597,899670203⟩]
theorem checked14678 : checkPrefixCuts (2^48) 1927806977 9 Manual.Count131072.C014678.packed 128 cuts14678 = true := by
 decide +kernel
def pointBounds14678 : List (Nat × Nat × Nat) := [(1927853056,95984077845545,95984455688748),(1927913472,95984493513372,95984871356856)]
theorem point_links_checked14678 : (cuts14678.take 2).map (fun c => (1927806977-1+2*2^9*c.k,95983762326387+c.lower,95984140169377+c.upper)) = pointBounds14678 := by
 decide +kernel
def cuts14679 : List PrefixCut := [⟨35,245420154,245420320⟩,
⟨94,651718421,651718859⟩,
⟨128,891432806,891433406⟩]
theorem checked14679 : checkPrefixCuts (2^48) 1927938049 9 Manual.Count131072.C014679.packed 128 cuts14679 = true := by
 decide +kernel
def pointBounds14679 : List (Nat × Nat × Nat) := [(1927973888,95984907416138,95985285259900),(1928034304,95985313714405,95985691558439)]
theorem point_links_checked14679 : (cuts14679.take 2).map (fun c => (1927938049-1+2*2^9*c.k,95984661995984+c.lower,95985039839580+c.upper)) = pointBounds14679 := by
 decide +kernel
def cuts14680 : List PrefixCut := [⟨25,171680713,171680831⟩,
⟨84,576785544,576785935⟩,
⟨128,888890250,888890847⟩]
theorem checked14680 : checkPrefixCuts (2^48) 1928069121 9 Manual.Count131072.C014680.packed 128 cuts14680 = true := by
 decide +kernel
def pointBounds14680 : List (Nat × Nat × Nat) := [(1928094720,95985725109503,95986102953817),(1928155136,95986130214334,95986508058921)]
theorem point_links_checked14680 : (cuts14680.take 2).map (fun c => (1928069121-1+2*2^9*c.k,95985553428790+c.lower,95985931272986+c.upper)) = pointBounds14680 := by
 decide +kernel
def cuts14681 : List PrefixCut := [⟨15,101308344,101308412⟩,
⟨74,513540515,513540858⟩,
⟨128,894230831,894231432⟩]
theorem checked14681 : checkPrefixCuts (2^48) 1928200193 9 Manual.Count131072.C014681.packed 128 cuts14681 = true := by
 decide +kernel
def pointBounds14681 : List (Nat × Nat × Nat) := [(1928215552,95986543627384,95986921472245),(1928275968,95986955859555,95987333704691)]
theorem point_links_checked14681 : (cuts14681.take 2).map (fun c => (1928200193-1+2*2^9*c.k,95986442319040+c.lower,95986820163833+c.upper)) = pointBounds14681 := by
 decide +kernel
def cuts14682 : List PrefixCut := [⟨5,34156494,34156518⟩,
⟨64,451033795,451034104⟩,
⟨123,863665115,863665702⟩,
⟨128,898257252,898257863⟩]
theorem checked14682 : checkPrefixCuts (2^48) 1928331265 9 Manual.Count131072.C014682.packed 128 cuts14682 = true := by
 decide +kernel
def pointBounds14682 : List (Nat × Nat × Nat) := [(1928336384,95987370706365,95987748551783),(1928396800,95987787583666,95988165429369),(1928457216,95988200214986,95988578060967)]
theorem point_links_checked14682 : (cuts14682.take 3).map (fun c => (1928331265-1+2*2^9*c.k,95987336549871+c.lower,95987714395265+c.upper)) = pointBounds14682 := by
 decide +kernel
def cuts14683 : List PrefixCut := [⟨54,385762019,385762279⟩,
⟨113,791653806,791654340⟩,
⟨128,896153186,896153792⟩]
theorem checked14683 : checkPrefixCuts (2^48) 1928462337 9 Manual.Count131072.C014683.packed 128 cuts14683 = true := by
 decide +kernel
def pointBounds14683 : List (Nat × Nat × Nat) := [(1928517632,95988620569142,95988998415407),(1928578048,95989026460929,95989404307468)]
theorem point_links_checked14683 : (cuts14683.take 2).map (fun c => (1928462337-1+2*2^9*c.k,95988234807123+c.lower,95988612653128+c.upper)) = pointBounds14683 := by
 decide +kernel
def cuts14684 : List PrefixCut := [⟨44,309260752,309260959⟩,
⟨103,718775641,718776121⟩,
⟨128,889086826,889087419⟩]
theorem checked14684 : checkPrefixCuts (2^48) 1928593409 9 Manual.Count131072.C014684.packed 128 cuts14684 = true := by
 decide +kernel
def pointBounds14684 : List (Nat × Nat × Nat) := [(1928638464,95989440221061,95989818067879),(1928698880,95989849735950,95990227583041)]
theorem point_links_checked14684 : (cuts14684.take 2).map (fun c => (1928593409-1+2*2^9*c.k,95989130960309+c.lower,95989508806920+c.upper)) = pointBounds14684 := by
 decide +kernel
def cuts14685 : List PrefixCut := [⟨34,238752982,238753142⟩,
⟨93,653641838,653642281⟩,
⟨128,902014361,902014971⟩]
theorem checked14685 : checkPrefixCuts (2^48) 1928724481 9 Manual.Count131072.C014685.packed 128 cuts14685 = true := by
 decide +kernel
def pointBounds14685 : List (Nat × Nat × Nat) := [(1928759296,95990258800117,95990636647481),(1928819712,95990673688973,95991051536620)]
theorem point_links_checked14685 : (cuts14685.take 2).map (fun c => (1928724481-1+2*2^9*c.k,95990020047135+c.lower,95990397894339+c.upper)) = pointBounds14685 := by
 decide +kernel
def cuts14686 : List PrefixCut := [⟨24,170881104,170881221⟩,
⟨83,573486249,573486643⟩,
⟨128,889111745,889112351⟩]
theorem checked14686 : checkPrefixCuts (2^48) 1928855553 9 Manual.Count131072.C014686.packed 128 cuts14686 = true := by
 decide +kernel
def pointBounds14686 : List (Nat × Nat × Nat) := [(1928880128,95991092942600,95991470790531),(1928940544,95991495547745,95991873395953)]
theorem point_links_checked14686 : (cuts14686.take 2).map (fun c => (1928855553-1+2*2^9*c.k,95990922061496+c.lower,95991299909310+c.upper)) = pointBounds14686 := by
 decide +kernel
def cuts14687 : List PrefixCut := [⟨14,96014027,96014089⟩,
⟨73,500198987,500199325⟩,
⟨128,885403353,885403947⟩]
theorem checked14687 : checkPrefixCuts (2^48) 1928986625 9 Manual.Count131072.C014687.packed 128 cuts14687 = true := by
 decide +kernel
def pointBounds14687 : List (Nat × Nat × Nat) := [(1929000960,95991907187268,95992285035750),(1929061376,95992311372228,95992689220986)]
theorem point_links_checked14687 : (cuts14687.take 2).map (fun c => (1928986625-1+2*2^9*c.k,95991811173241+c.lower,95992189021661+c.upper)) = pointBounds14687 := by
 decide +kernel
def cuts14688 : List PrefixCut := [⟨4,26847157,26847174⟩,
⟨63,438156302,438156597⟩,
⟨122,846680354,846680924⟩,
⟨128,884322277,884322873⟩]
theorem checked14688 : checkPrefixCuts (2^48) 1929117697 9 Manual.Count131072.C014688.packed 128 cuts14688 = true := by
 decide +kernel
def pointBounds14688 : List (Nat × Nat × Nat) := [(1929121792,95992723423751,95993101272782),(1929182208,95993134732896,95993512582205),(1929242624,95993543256948,95993921106532)]
theorem point_links_checked14688 : (cuts14688.take 3).map (fun c => (1929117697-1+2*2^9*c.k,95992696576594+c.lower,95993074425608+c.upper)) = pointBounds14688 := by
 decide +kernel
def cuts14689 : List PrefixCut := [⟨53,378455881,378456136⟩,
⟨112,793519470,793520011⟩,
⟨128,904249532,904250145⟩]
theorem checked14689 : checkPrefixCuts (2^48) 1929248769 9 Manual.Count131072.C014689.packed 128 cuts14689 = true := by
 decide +kernel
def pointBounds14689 : List (Nat × Nat × Nat) := [(1929303040,95993959354752,95994337204617),(1929363456,95994374418341,95994752268492)]
theorem point_links_checked14689 : (cuts14689.take 2).map (fun c => (1929248769-1+2*2^9*c.k,95993580898871+c.lower,95993958748481+c.upper)) = pointBounds14689 := by
 decide +kernel
def cuts14690 : List PrefixCut := [⟨43,301548706,301548910⟩,
⟨102,716878120,716878603⟩,
⟨128,903020829,903021433⟩]
theorem checked14690 : checkPrefixCuts (2^48) 1929379841 9 Manual.Count131072.C014690.packed 128 cuts14690 = true := by
 decide +kernel
def pointBounds14690 : List (Nat × Nat × Nat) := [(1929423872,95994786697109,95995164547536),(1929484288,95995202026523,95995579877229)]
theorem point_links_checked14690 : (cuts14690.take 2).map (fun c => (1929379841-1+2*2^9*c.k,95994485148403+c.lower,95994862998626+c.upper)) = pointBounds14690 := by
 decide +kernel
def cuts14691 : List PrefixCut := [⟨33,230048990,230049142⟩,
⟨92,644331255,644331681⟩,
⟨128,894353054,894353651⟩]
theorem checked14691 : checkPrefixCuts (2^48) 1929510913 9 Manual.Count131072.C014691.packed 128 cuts14691 = true := by
 decide +kernel
def pointBounds14691 : List (Nat × Nat × Nat) := [(1929544704,95995618218222,95995996069201),(1929605120,95996032500487,95996410351740)]
theorem point_links_checked14691 : (cuts14691.take 2).map (fun c => (1929510913-1+2*2^9*c.k,95995388169232+c.lower,95995766020059+c.upper)) = pointBounds14691 := by
 decide +kernel
def cuts14692 : List PrefixCut := [⟨23,159725526,159725634⟩,
⟨82,577774343,577774741⟩,
⟨128,897647200,897647808⟩]
theorem checked14692 : checkPrefixCuts (2^48) 1929641985 9 Manual.Count131072.C014692.packed 128 cuts14692 = true := by
 decide +kernel
def pointBounds14692 : List (Nat × Nat × Nat) := [(1929665536,95996442247812,95996820099344),(1929725952,95996860296629,95997238148451)]
theorem point_links_checked14692 : (cuts14692.take 2).map (fun c => (1929641985-1+2*2^9*c.k,95996282522286+c.lower,95996660373710+c.upper)) = pointBounds14692 := by
 decide +kernel
def cuts14693 : List PrefixCut := [⟨13,93057759,93057823⟩,
⟨72,506267162,506267502⟩,
⟨128,898169631,898170234⟩]
theorem checked14693 : checkPrefixCuts (2^48) 1929773057 9 Manual.Count131072.C014693.packed 128 cuts14693 = true := by
 decide +kernel
def pointBounds14693 : List (Nat × Nat × Nat) := [(1929786368,95997273227245,95997651079341),(1929846784,95997686436648,95998064289020)]
theorem point_links_checked14693 : (cuts14693.take 2).map (fun c => (1929773057-1+2*2^9*c.k,95997180169486+c.lower,95997558021518+c.upper)) = pointBounds14693 := by
 decide +kernel
def cuts14694 : List PrefixCut := [⟨3,18231129,18231142⟩,
⟨62,432727268,432727563⟩,
⟨121,837584920,837585486⟩,
⟨128,889066271,889066871⟩]
theorem checked14694 : checkPrefixCuts (2^48) 1929904129 9 Manual.Count131072.C014694.packed 128 cuts14694 = true := by
 decide +kernel
def pointBounds14694 : List (Nat × Nat × Nat) := [(1929907200,95998096570246,95998474422894),(1929967616,95998511066385,95998888919315),(1930028032,95998915924037,95999293777238)]
theorem point_links_checked14694 : (cuts14694.take 3).map (fun c => (1929904129-1+2*2^9*c.k,95998078339117+c.lower,95998456191752+c.upper)) = pointBounds14694 := by
 decide +kernel
def cuts14695 : List PrefixCut := [⟨52,370134922,370135166⟩,
⟨111,787362981,787363502⟩,
⟨128,904901962,904902562⟩]
theorem checked14695 : checkPrefixCuts (2^48) 1930035201 9 Manual.Count131072.C014695.packed 128 cuts14695 = true := by
 decide +kernel
def pointBounds14695 : List (Nat × Nat × Nat) := [(1930088448,95999337540310,95999715393789),(1930148864,95999754768369,96000132622125)]
theorem point_links_checked14695 : (cuts14695.take 2).map (fun c => (1930035201-1+2*2^9*c.k,95998967405388+c.lower,95999345258623+c.upper)) = pointBounds14695 := by
 decide +kernel
def cuts14696 : List PrefixCut := [⟨42,298509294,298509492⟩,
⟨101,705066100,705066569⟩,
⟨128,890258117,890258711⟩]
theorem checked14696 : checkPrefixCuts (2^48) 1930166273 9 Manual.Count131072.C014696.packed 128 cuts14696 = true := by
 decide +kernel
def pointBounds14696 : List (Nat × Nat × Nat) := [(1930209280,96000170816644,96000548670677),(1930269696,96000577373450,96000955227754)]
theorem point_links_checked14696 : (cuts14696.take 2).map (fun c => (1930166273-1+2*2^9*c.k,95999872307350+c.lower,96000250161185+c.upper)) = pointBounds14696 := by
 decide +kernel
def cuts14697 : List PrefixCut := [⟨32,223830981,223831131⟩,
⟨91,633861917,633862340⟩,
⟨128,891509927,891510521⟩]
theorem checked14697 : checkPrefixCuts (2^48) 1930297345 9 Manual.Count131072.C014697.packed 128 cuts14697 = true := by
 decide +kernel
def pointBounds14697 : List (Nat × Nat × Nat) := [(1930330112,96000986396448,96001364251027),(1930390528,96001396427384,96001774282236)]
theorem point_links_checked14697 : (cuts14697.take 2).map (fun c => (1930297345-1+2*2^9*c.k,96000762565467+c.lower,96001140419896+c.upper)) = pointBounds14697 := by
 decide +kernel
def cuts14698 : List PrefixCut := [⟨22,154119791,154119894⟩,
⟨81,566895251,566895635⟩,
⟨128,897427195,897427801⟩]
theorem checked14698 : checkPrefixCuts (2^48) 1930428417 9 Manual.Count131072.C014698.packed 128 cuts14698 = true := by
 decide +kernel
def pointBounds14698 : List (Nat × Nat × Nat) := [(1930450944,96001808195185,96002186050311),(1930511360,96002220970645,96002598826052)]
theorem point_links_checked14698 : (cuts14698.take 2).map (fun c => (1930428417-1+2*2^9*c.k,96001654075394+c.lower,96002031930417+c.upper)) = pointBounds14698 := by
 decide +kernel
def cuts14699 : List PrefixCut := [⟨12,84563526,84563583⟩,
⟨71,497458996,497459331⟩,
⟨128,896491583,896492186⟩]
theorem checked14699 : checkPrefixCuts (2^48) 1930559489 9 Manual.Count131072.C014699.packed 128 cuts14699 = true := by
 decide +kernel
def pointBounds14699 : List (Nat × Nat × Nat) := [(1930571776,96002636066115,96003013921801),(1930632192,96003048961585,96003426817549)]
theorem point_links_checked14699 : (cuts14699.take 2).map (fun c => (1930559489-1+2*2^9*c.k,96002551502589+c.lower,96002929358218+c.upper)) = pointBounds14699 := by
 decide +kernel
def cuts14700 : List PrefixCut := [⟨2,15016336,15016346⟩,
⟨61,425844972,425845262⟩,
⟨120,843949919,843950491⟩,
⟨128,898471698,898472308⟩]
theorem checked14700 : checkPrefixCuts (2^48) 1930690561 9 Manual.Count131072.C014700.packed 128 cuts14700 = true := by
 decide +kernel
def pointBounds14700 : List (Nat × Nat × Nat) := [(1930692608,96003463010508,96003840866750),(1930753024,96003873839144,96004251695666),(1930813440,96004291944091,96004669800895)]
theorem point_links_checked14700 : (cuts14700.take 3).map (fun c => (1930690561-1+2*2^9*c.k,96003447994172+c.lower,96003825850404+c.upper)) = pointBounds14700 := by
 decide +kernel
def cuts14701 : List PrefixCut := [⟨51,364444732,364444979⟩,
⟨110,775380538,775381059⟩,
⟨128,897682122,897682722⟩]
theorem checked14701 : checkPrefixCuts (2^48) 1930821633 9 Manual.Count131072.C014701.packed 128 cuts14701 = true := by
 decide +kernel
def pointBounds14701 : List (Nat × Nat × Nat) := [(1930873856,96004710910602,96005088767691),(1930934272,96005121846408,96005499703771)]
theorem point_links_checked14701 : (cuts14701.take 2).map (fun c => (1930821633-1+2*2^9*c.k,96004346465870+c.lower,96004724322712+c.upper)) = pointBounds14701 := by
 decide +kernel
def cuts14702 : List PrefixCut := [⟨41,288475577,288475773⟩,
⟨100,700114498,700114973⟩,
⟨128,890624315,890624922⟩]
theorem checked14702 : checkPrefixCuts (2^48) 1930952705 9 Manual.Count131072.C014702.packed 128 cuts14702 = true := by
 decide +kernel
def pointBounds14702 : List (Nat × Nat × Nat) := [(1930994688,96005532623569,96005910481207),(1931055104,96005944262490,96006322120407)]
theorem point_links_checked14702 : (cuts14702.take 2).map (fun c => (1930952705-1+2*2^9*c.k,96005244147992+c.lower,96005622005434+c.upper)) = pointBounds14702 := by
 decide +kernel
def cuts14703 : List PrefixCut := [⟨31,216889187,216889331⟩,
⟨90,627044739,627045158⟩,
⟨128,891292432,891293027⟩]
theorem checked14703 : checkPrefixCuts (2^48) 1931083777 9 Manual.Count131072.C014703.packed 128 cuts14703 = true := by
 decide +kernel
def pointBounds14703 : List (Nat × Nat × Nat) := [(1931115520,96006351661494,96006729519687),(1931175936,96006761817046,96007139675514)]
theorem point_links_checked14703 : (cuts14703.take 2).map (fun c => (1931083777-1+2*2^9*c.k,96006134772307+c.lower,96006512630356+c.upper)) = pointBounds14703 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000146
