import PlattAssemblyKernel
import PlattCertificates.Count131072.C013904
import PlattCertificates.Count131072.C013905
import PlattCertificates.Count131072.C013906
import PlattCertificates.Count131072.C013907
import PlattCertificates.Count131072.C013908
import PlattCertificates.Count131072.C013909
import PlattCertificates.Count131072.C013910
import PlattCertificates.Count131072.C013911
import PlattCertificates.Count131072.C013912
import PlattCertificates.Count131072.C013913
import PlattCertificates.Count131072.C013914
import PlattCertificates.Count131072.C013915
import PlattCertificates.Count131072.C013916
import PlattCertificates.Count131072.C013917
import PlattCertificates.Count131072.C013918
import PlattCertificates.Count131072.C013919
import PlattCertificates.Count131072.C013920
import PlattCertificates.Count131072.C013921
import PlattCertificates.Count131072.C013922
import PlattCertificates.Count131072.C013923
import PlattCertificates.Count131072.C013924
import PlattCertificates.Count131072.C013925
import PlattCertificates.Count131072.C013926
import PlattCertificates.Count131072.C013927
import PlattCertificates.Count131072.C013928
import PlattCertificates.Count131072.C013929
import PlattCertificates.Count131072.C013930
import PlattCertificates.Count131072.C013931
import PlattCertificates.Count131072.C013932
import PlattCertificates.Count131072.C013933
import PlattCertificates.Count131072.C013934
import PlattCertificates.Count131072.C013935
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13904 : List PrefixCut := [⟨3,21268294,21268309⟩,
⟨59,429828507,429828805⟩,
⟨115,849934183,849934772⟩,
⟨128,950258290,950258947⟩]
theorem checked13904 : checkPrefixCuts (2^48) 1826357249 9 Manual.Count131072.C013904.packed 128 cuts13904 = true := by
 decide +kernel
def pointBounds13904 : List (Nat × Nat × Nat) := [(1826360320,95271284060547,95271661415627),(1826417664,95271692620760,95272069976123),(1826475008,95272112726436,95272490082090)]
theorem point_links_checked13904 : (cuts13904.take 3).map (fun c => (1826357249-1+2*2^9*c.k,95271262792253+c.lower,95271640147318+c.upper)) = pointBounds13904 := by
 decide +kernel
def cuts13905 : List PrefixCut := [⟨43,307285948,307286163⟩,
⟨99,719351939,719352443⟩,
⟨128,937707837,937708492⟩]
theorem checked13905 : checkPrefixCuts (2^48) 1826488321 9 Manual.Count131072.C013905.packed 128 cuts13905 = true := by
 decide +kernel
def pointBounds13905 : List (Nat × Nat × Nat) := [(1826532352,95272520336491,95272897692428),(1826589696,95272932402482,95273309758708)]
theorem point_links_checked13905 : (cuts13905.take 2).map (fun c => (1826488321-1+2*2^9*c.k,95272213050543+c.lower,95272590406265+c.upper)) = pointBounds13905 := by
 decide +kernel
def cuts13906 : List PrefixCut := [⟨27,197395579,197395715⟩,
⟨83,616524027,616524453⟩,
⟨128,959521595,959522263⟩]
theorem checked13906 : checkPrefixCuts (2^48) 1826619393 9 Manual.Count131072.C013906.packed 128 cuts13906 = true := by
 decide +kernel
def pointBounds13906 : List (Nat × Nat × Nat) := [(1826647040,95273348153959,95273725510472),(1826704384,95273767282407,95274144639210)]
theorem point_links_checked13906 : (cuts13906.take 2).map (fun c => (1826619393-1+2*2^9*c.k,95273150758380+c.lower,95273528114757+c.upper)) = pointBounds13906 := by
 decide +kernel
def cuts13907 : List PrefixCut := [⟨11,79507635,79507690⟩,
⟨67,498609707,498610053⟩,
⟨123,920163909,920164545⟩,
⟨128,955600970,955601631⟩]
theorem checked13907 : checkPrefixCuts (2^48) 1826750465 9 Manual.Count131072.C013907.packed 128 cuts13907 = true := by
 decide +kernel
def pointBounds13907 : List (Nat × Nat × Nat) := [(1826761728,95274189787610,95274567144710),(1826819072,95274608889682,95274986247073),(1826876416,95275030443884,95275407801565)]
theorem point_links_checked13907 : (cuts13907.take 3).map (fun c => (1826750465-1+2*2^9*c.k,95274110279975+c.lower,95274487637020+c.upper)) = pointBounds13907 := by
 decide +kernel
def cuts13908 : List PrefixCut := [⟨51,377321829,377322089⟩,
⟨107,791146203,791146750⟩,
⟨128,947520980,947521634⟩]
theorem checked13908 : checkPrefixCuts (2^48) 1826881537 9 Manual.Count131072.C013908.packed 128 cuts13908 = true := by
 decide +kernel
def pointBounds13908 : List (Nat × Nat × Nat) := [(1826933760,95275443202774,95275820560740),(1826991104,95275857027148,95276234385401)]
theorem point_links_checked13908 : (cuts13908.take 2).map (fun c => (1826881537-1+2*2^9*c.k,95275065880945+c.lower,95275443238651+c.upper)) = pointBounds13908 := by
 decide +kernel
def cuts13909 : List PrefixCut := [⟨35,249117314,249117488⟩,
⟨91,665226570,665227034⟩,
⟨128,947760644,947761301⟩]
theorem checked13909 : checkPrefixCuts (2^48) 1827012609 9 Manual.Count131072.C013909.packed 128 cuts13909 = true := by
 decide +kernel
def pointBounds13909 : List (Nat × Nat × Nat) := [(1827048448,95276262519239,95276639877773),(1827105792,95276678628495,95277055987319)]
theorem point_links_checked13909 : (cuts13909.take 2).map (fun c => (1827012609-1+2*2^9*c.k,95276013401925+c.lower,95276390760285+c.upper)) = pointBounds13909 := by
 decide +kernel
def cuts13910 : List PrefixCut := [⟨19,138337836,138337933⟩,
⟨75,552418386,552418772⟩,
⟨128,944304046,944304700⟩]
theorem checked13910 : checkPrefixCuts (2^48) 1827143681 9 Manual.Count131072.C013910.packed 128 cuts13910 = true := by
 decide +kernel
def pointBounds13910 : List (Nat × Nat × Nat) := [(1827163136,95277099500405,95277476859519),(1827220480,95277513580955,95277890940358)]
theorem point_links_checked13910 : (cuts13910.take 2).map (fun c => (1827143681-1+2*2^9*c.k,95276961162569+c.lower,95277338521586+c.upper)) = pointBounds13910 := by
 decide +kernel
def cuts13911 : List PrefixCut := [⟨3,23568223,23568240⟩,
⟨59,440087366,440087668⟩,
⟨115,851664335,851664922⟩,
⟨128,946392985,946393641⟩]
theorem checked13911 : checkPrefixCuts (2^48) 1827274753 9 Manual.Count131072.C013911.packed 128 cuts13911 = true := by
 decide +kernel
def pointBounds13911 : List (Nat × Nat × Nat) := [(1827277824,95277929034838,95278306394526),(1827335168,95278345553981,95278722913954),(1827392512,95278757130950,95279134491208)]
theorem point_links_checked13911 : (cuts13911.take 3).map (fun c => (1827274753-1+2*2^9*c.k,95277905466615+c.lower,95278282826286+c.upper)) = pointBounds13911 := by
 decide +kernel
def cuts13912 : List PrefixCut := [⟨43,316835454,316835677⟩,
⟨99,728848656,728849166⟩,
⟨128,940626092,940626752⟩]
theorem checked13912 : checkPrefixCuts (2^48) 1827405825 9 Manual.Count131072.C013912.packed 128 cuts13912 = true := by
 decide +kernel
def pointBounds13912 : List (Nat × Nat × Nat) := [(1827449856,95279168695054,95279546055604),(1827507200,95279580708256,95279958069093)]
theorem point_links_checked13912 : (cuts13912.take 2).map (fun c => (1827405825-1+2*2^9*c.k,95278851859600+c.lower,95279229219927+c.upper)) = pointBounds13912 := by
 decide +kernel
def cuts13913 : List PrefixCut := [⟨27,203149162,203149303⟩,
⟨83,619294899,619295332⟩,
⟨128,947027300,947027963⟩]
theorem checked13913 : checkPrefixCuts (2^48) 1827536897 9 Manual.Count131072.C013913.packed 128 cuts13913 = true := by
 decide +kernel
def pointBounds13913 : List (Nat × Nat × Nat) := [(1827564544,95279995634854,95280372995982),(1827621888,95280411780591,95280789142011)]
theorem point_links_checked13913 : (cuts13913.take 2).map (fun c => (1827536897-1+2*2^9*c.k,95279792485692+c.lower,95280169846679+c.upper)) = pointBounds13913 := by
 decide +kernel
def cuts13914 : List PrefixCut := [⟨11,81007772,81007829⟩,
⟨67,491121137,491121478⟩,
⟨123,902607668,902608299⟩,
⟨128,943570829,943571488⟩]
theorem checked13914 : checkPrefixCuts (2^48) 1827667969 9 Manual.Count131072.C013914.packed 128 cuts13914 = true := by
 decide +kernel
def pointBounds13914 : List (Nat × Nat × Nat) := [(1827679232,95280820520764,95281197882471),(1827736576,95281230634129,95281607996120),(1827793920,95281642120660,95282019482941)]
theorem point_links_checked13914 : (cuts13914.take 3).map (fun c => (1827667969-1+2*2^9*c.k,95280739512992+c.lower,95281116874642+c.upper)) = pointBounds13914 := by
 decide +kernel
def cuts13915 : List PrefixCut := [⟨51,375284358,375284622⟩,
⟨107,790748808,790749363⟩,
⟨128,948276981,948277645⟩]
theorem checked13915 : checkPrefixCuts (2^48) 1827799041 9 Manual.Count131072.C013915.packed 128 cuts13915 = true := by
 decide +kernel
def pointBounds13915 : List (Nat × Nat × Nat) := [(1827851264,95282058368179,95282435730752),(1827908608,95282473832629,95282851195493)]
theorem point_links_checked13915 : (cuts13915.take 2).map (fun c => (1827799041-1+2*2^9*c.k,95281683083821+c.lower,95282060446130+c.upper)) = pointBounds13915 := by
 decide +kernel
def cuts13916 : List PrefixCut := [⟨35,259463157,259463337⟩,
⟨91,683524579,683525056⟩,
⟨128,954984538,954985207⟩]
theorem checked13916 : checkPrefixCuts (2^48) 1827930113 9 Manual.Count131072.C013916.packed 128 cuts13916 = true := by
 decide +kernel
def pointBounds13916 : List (Nat × Nat × Nat) := [(1827965952,95282890823959,95283268187112),(1828023296,95283314885381,95283692248831)]
theorem point_links_checked13916 : (cuts13916.take 2).map (fun c => (1827930113-1+2*2^9*c.k,95282631360802+c.lower,95283008723775+c.upper)) = pointBounds13916 := by
 decide +kernel
def cuts13917 : List PrefixCut := [⟨19,139654170,139654268⟩,
⟨75,559839668,559840059⟩,
⟨128,958611032,958611703⟩]
theorem checked13917 : checkPrefixCuts (2^48) 1828061185 9 Manual.Count131072.C013917.packed 128 cuts13917 = true := by
 decide +kernel
def pointBounds13917 : List (Nat × Nat × Nat) := [(1828080640,95283725999510,95284103363250),(1828137984,95284146185008,95284523549041)]
theorem point_links_checked13917 : (cuts13917.take 2).map (fun c => (1828061185-1+2*2^9*c.k,95283586345340+c.lower,95283963708982+c.upper)) = pointBounds13917 := by
 decide +kernel
def cuts13918 : List PrefixCut := [⟨3,22940542,22940557⟩,
⟨59,440482189,440482492⟩,
⟨115,856317309,856317902⟩,
⟨128,949304938,949305594⟩]
theorem checked13918 : checkPrefixCuts (2^48) 1828192257 9 Manual.Count131072.C013918.packed 128 cuts13918 = true := by
 decide +kernel
def pointBounds13918 : List (Nat × Nat × Nat) := [(1828195328,95284567896914,95284945261242),(1828252672,95284985438561,95285362803177),(1828310016,95285401273681,95285778638587)]
theorem point_links_checked13918 : (cuts13918.take 3).map (fun c => (1828192257-1+2*2^9*c.k,95284544956372+c.lower,95284922320685+c.upper)) = pointBounds13918 := by
 decide +kernel
def cuts13919 : List PrefixCut := [⟨43,321140946,321141170⟩,
⟨99,730176373,730176885⟩,
⟨128,947543420,947544081⟩]
theorem checked13919 : checkPrefixCuts (2^48) 1828323329 9 Manual.Count131072.C013919.packed 128 cuts13919 = true := by
 decide +kernel
def pointBounds13919 : List (Nat × Nat × Nat) := [(1828367360,95285815402256,95286192767449),(1828424704,95286224437683,95286601803164)]
theorem point_links_checked13919 : (cuts13919.take 2).map (fun c => (1828323329-1+2*2^9*c.k,95285494261310+c.lower,95285871626279+c.upper)) = pointBounds13919 := by
 decide +kernel
def cuts13920 : List PrefixCut := [⟨27,194272574,194272706⟩,
⟨83,605129582,605129996⟩,
⟨128,942087502,942088149⟩]
theorem checked13920 : checkPrefixCuts (2^48) 1828454401 9 Manual.Count131072.C013920.packed 128 cuts13920 = true := by
 decide +kernel
def pointBounds13920 : List (Nat × Nat × Nat) := [(1828482048,95286636077304,95287013443066),(1828539392,95287046934312,95287424300356)]
theorem point_links_checked13920 : (cuts13920.take 2).map (fun c => (1828454401-1+2*2^9*c.k,95286441804730+c.lower,95286819170360+c.upper)) = pointBounds13920 := by
 decide +kernel
def cuts13921 : List PrefixCut := [⟨11,81582862,81582918⟩,
⟨67,485333384,485333721⟩,
⟨123,897998884,897999506⟩,
⟨128,935863101,935863750⟩]
theorem checked13921 : checkPrefixCuts (2^48) 1828585473 9 Manual.Count131072.C013921.packed 128 cuts13921 = true := by
 decide +kernel
def pointBounds13921 : List (Nat × Nat × Nat) := [(1828596736,95287465475094,95287842841427),(1828654080,95287869225616,95288246592230),(1828711424,95288281891116,95288659258015)]
theorem point_links_checked13921 : (cuts13921.take 3).map (fun c => (1828585473-1+2*2^9*c.k,95287383892232+c.lower,95287761258509+c.upper)) = pointBounds13921 := by
 decide +kernel
def cuts13922 : List PrefixCut := [⟨51,380483202,380483466⟩,
⟨107,793738405,793738953⟩,
⟨128,951033612,951034267⟩]
theorem checked13922 : checkPrefixCuts (2^48) 1828716545 9 Manual.Count131072.C013922.packed 128 cuts13922 = true := by
 decide +kernel
def pointBounds13922 : List (Nat × Nat × Nat) := [(1828768768,95288700238535,95289077605725),(1828826112,95289113493738,95289490861212)]
theorem point_links_checked13922 : (cuts13922.take 2).map (fun c => (1828716545-1+2*2^9*c.k,95288319755333+c.lower,95288697122259+c.upper)) = pointBounds13922 := by
 decide +kernel
def cuts13923 : List PrefixCut := [⟨35,257947799,257947979⟩,
⟨91,668252911,668253376⟩,
⟨128,941423469,941424124⟩]
theorem checked13923 : checkPrefixCuts (2^48) 1828847617 9 Manual.Count131072.C013923.packed 128 cuts13923 = true := by
 decide +kernel
def pointBounds13923 : List (Nat × Nat × Nat) := [(1828883456,95289528736744,95289906104505),(1828940800,95289939041856,95290316409902)]
theorem point_links_checked13923 : (cuts13923.take 2).map (fun c => (1828847617-1+2*2^9*c.k,95289270788945+c.lower,95289648156526+c.upper)) = pointBounds13923 := by
 decide +kernel
def cuts13924 : List PrefixCut := [⟨19,142969822,142969923⟩,
⟨75,553710824,553711208⟩,
⟨128,947203920,947204582⟩]
theorem checked13924 : checkPrefixCuts (2^48) 1828978689 9 Manual.Count131072.C013924.packed 128 cuts13924 = true := by
 decide +kernel
def pointBounds13924 : List (Nat × Nat × Nat) := [(1828998144,95290355182236,95290732550573),(1829055488,95290765923238,95291143291858)]
theorem point_links_checked13924 : (cuts13924.take 2).map (fun c => (1828978689-1+2*2^9*c.k,95290212212414+c.lower,95290589580650+c.upper)) = pointBounds13924 := by
 decide +kernel
def cuts13925 : List PrefixCut := [⟨3,23698466,23698482⟩,
⟨59,448109423,448109728⟩,
⟨115,852502846,852503437⟩,
⟨128,948059721,948060381⟩]
theorem checked13925 : checkPrefixCuts (2^48) 1829109761 9 Manual.Count131072.C013925.packed 128 cuts13925 = true := by
 decide +kernel
def pointBounds13925 : List (Nat × Nat × Nat) := [(1829112832,95291183114800,95291560483714),(1829170176,95291607525757,95291984894960),(1829227520,95292011919180,95292389288669)]
theorem point_links_checked13925 : (cuts13925.take 3).map (fun c => (1829109761-1+2*2^9*c.k,95291159416334+c.lower,95291536785232+c.upper)) = pointBounds13925 := by
 decide +kernel
def cuts13926 : List PrefixCut := [⟨43,317594680,317594900⟩,
⟨99,737503572,737504086⟩,
⟨128,945529742,945530401⟩]
theorem checked13926 : checkPrefixCuts (2^48) 1829240833 9 Manual.Count131072.C013926.packed 128 cuts13926 = true := by
 decide +kernel
def pointBounds13926 : List (Nat × Nat × Nat) := [(1829284864,95292425070735,95292802440513),(1829342208,95292844979627,95293222349699)]
theorem point_links_checked13926 : (cuts13926.take 2).map (fun c => (1829240833-1+2*2^9*c.k,95292107476055+c.lower,95292484845613+c.upper)) = pointBounds13926 := by
 decide +kernel
def cuts13927 : List PrefixCut := [⟨27,197714016,197714152⟩,
⟨83,615288709,615289134⟩,
⟨128,949769794,949770449⟩]
theorem checked13927 : checkPrefixCuts (2^48) 1829371905 9 Manual.Count131072.C013927.packed 128 cuts13927 = true := by
 decide +kernel
def pointBounds13927 : List (Nat × Nat × Nat) := [(1829399552,95293250719813,95293628090166),(1829456896,95293668294506,95294045665148)]
theorem point_links_checked13927 : (cuts13927.take 2).map (fun c => (1829371905-1+2*2^9*c.k,95293053005797+c.lower,95293430376014+c.upper)) = pointBounds13927 := by
 decide +kernel
def cuts13928 : List PrefixCut := [⟨11,82772766,82772823⟩,
⟨67,494936435,494936780⟩,
⟨123,908933366,908934003⟩,
⟨128,945701696,945702358⟩]
theorem checked13928 : checkPrefixCuts (2^48) 1829502977 9 Manual.Count131072.C013928.packed 128 cuts13928 = true := by
 decide +kernel
def pointBounds13928 : List (Nat × Nat × Nat) := [(1829514240,95294085548357,95294462919286),(1829571584,95294497712026,95294875083243),(1829628928,95294911708957,95295289080466)]
theorem point_links_checked13928 : (cuts13928.take 3).map (fun c => (1829502977-1+2*2^9*c.k,95294002775591+c.lower,95294380146463+c.upper)) = pointBounds13928 := by
 decide +kernel
def cuts13929 : List PrefixCut := [⟨51,382600031,382600295⟩,
⟨107,794571114,794571663⟩,
⟨128,949787663,949788320⟩]
theorem checked13929 : checkPrefixCuts (2^48) 1829634049 9 Manual.Count131072.C013929.packed 128 cuts13929 = true := by
 decide +kernel
def pointBounds13929 : List (Nat × Nat × Nat) := [(1829686272,95295331077318,95295708449116),(1829743616,95295743048401,95296120420484)]
theorem point_links_checked13929 : (cuts13929.take 2).map (fun c => (1829634049-1+2*2^9*c.k,95294948477287+c.lower,95295325848821+c.upper)) = pointBounds13929 := by
 decide +kernel
def cuts13930 : List PrefixCut := [⟨35,252895961,252896136⟩,
⟨91,667917742,667918205⟩,
⟨128,939566895,939567552⟩]
theorem checked13930 : checkPrefixCuts (2^48) 1829765121 9 Manual.Count131072.C013930.packed 128 cuts13930 = true := by
 decide +kernel
def pointBounds13930 : List (Nat × Nat × Nat) := [(1829800960,95296151160911,95296528533277),(1829858304,95296566182692,95296943555346)]
theorem point_links_checked13930 : (cuts13930.take 2).map (fun c => (1829765121-1+2*2^9*c.k,95295898264950+c.lower,95296275637141+c.upper)) = pointBounds13930 := by
 decide +kernel
def cuts13931 : List PrefixCut := [⟨19,132592230,132592323⟩,
⟨75,549587679,549588063⟩,
⟨128,929655626,929656276⟩]
theorem checked13931 : checkPrefixCuts (2^48) 1829896193 9 Manual.Count131072.C013931.packed 128 cuts13931 = true := by
 decide +kernel
def pointBounds13931 : List (Nat × Nat × Nat) := [(1829915648,95296970424075,95297347797016),(1829972992,95297387419524,95297764792756)]
theorem point_links_checked13931 : (cuts13931.take 2).map (fun c => (1829896193-1+2*2^9*c.k,95296837831845+c.lower,95297215204693+c.upper)) = pointBounds13931 := by
 decide +kernel
def cuts13932 : List PrefixCut := [⟨3,21225639,21225654⟩,
⟨59,433273166,433273469⟩,
⟨115,845461580,845462171⟩,
⟨128,944969313,944969973⟩]
theorem checked13932 : checkPrefixCuts (2^48) 1830027265 9 Manual.Count131072.C013932.packed 128 cuts13932 = true := by
 decide +kernel
def pointBounds13932 : List (Nat × Nat × Nat) := [(1830030336,95297788713110,95298166086623),(1830087680,95298200760637,95298578134438),(1830145024,95298612949051,95298990323140)]
theorem point_links_checked13932 : (cuts13932.take 3).map (fun c => (1830027265-1+2*2^9*c.k,95297767487471+c.lower,95298144860969+c.upper)) = pointBounds13932 := by
 decide +kernel
def cuts13933 : List PrefixCut := [⟨43,314051916,314052139⟩,
⟨99,732827481,732827995⟩,
⟨128,942594782,942595447⟩]
theorem checked13933 : checkPrefixCuts (2^48) 1830158337 9 Manual.Count131072.C013933.packed 128 cuts13933 = true := by
 decide +kernel
def pointBounds13933 : List (Nat × Nat × Nat) := [(1830202368,95299026508700,95299403883081),(1830259712,95299445284265,95299822658937)]
theorem point_links_checked13933 : (cuts13933.take 2).map (fun c => (1830158337-1+2*2^9*c.k,95298712456784+c.lower,95299089830942+c.upper)) = pointBounds13933 := by
 decide +kernel
def cuts13934 : List PrefixCut := [⟨27,198537640,198537779⟩,
⟨83,616825647,616826075⟩,
⟨128,950831481,950832143⟩]
theorem checked13934 : checkPrefixCuts (2^48) 1830289409 9 Manual.Count131072.C013934.packed 128 cuts13934 = true := by
 decide +kernel
def pointBounds13934 : List (Nat × Nat × Nat) := [(1830317056,95299853589206,95300230964168),(1830374400,95300271877213,95300649252464)]
theorem point_links_checked13934 : (cuts13934.take 2).map (fun c => (1830289409-1+2*2^9*c.k,95299655051566+c.lower,95300032426389+c.upper)) = pointBounds13934 := by
 decide +kernel
def cuts13935 : List PrefixCut := [⟨11,78271779,78271836⟩,
⟨67,494842025,494842368⟩,
⟨123,909092796,909093424⟩,
⟨128,947380354,947381008⟩]
theorem checked13935 : checkPrefixCuts (2^48) 1830420481 9 Manual.Count131072.C013935.packed 128 cuts13935 = true := by
 decide +kernel
def pointBounds13935 : List (Nat × Nat × Nat) := [(1830431744,95300684154826,95301061530368),(1830489088,95301100725072,95301478100900),(1830546432,95301514975843,95301892351956)]
theorem point_links_checked13935 : (cuts13935.take 3).map (fun c => (1830420481-1+2*2^9*c.k,95300605883047+c.lower,95300983258532+c.upper)) = pointBounds13935 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000122
