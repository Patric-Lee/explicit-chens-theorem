import PlattAssemblyKernel
import PlattCertificates.Count131072.C023904
import PlattCertificates.Count131072.C023905
import PlattCertificates.Count131072.C023906
import PlattCertificates.Count131072.C023907
import PlattCertificates.Count131072.C023908
import PlattCertificates.Count131072.C023909
import PlattCertificates.Count131072.C023910
import PlattCertificates.Count131072.C023911
import PlattCertificates.Count131072.C023912
import PlattCertificates.Count131072.C023913
import PlattCertificates.Count131072.C023914
import PlattCertificates.Count131072.C023915
import PlattCertificates.Count131072.C023916
import PlattCertificates.Count131072.C023917
import PlattCertificates.Count131072.C023918
import PlattCertificates.Count131072.C023919
import PlattCertificates.Count131072.C023920
import PlattCertificates.Count131072.C023921
import PlattCertificates.Count131072.C023922
import PlattCertificates.Count131072.C023923
import PlattCertificates.Count131072.C023924
import PlattCertificates.Count131072.C023925
import PlattCertificates.Count131072.C023926
import PlattCertificates.Count131072.C023927
import PlattCertificates.Count131072.C023928
import PlattCertificates.Count131072.C023929
import PlattCertificates.Count131072.C023930
import PlattCertificates.Count131072.C023931
import PlattCertificates.Count131072.C023932
import PlattCertificates.Count131072.C023933
import PlattCertificates.Count131072.C023934
import PlattCertificates.Count131072.C023935
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23904 : List PrefixCut := [⟨31,129293363,129293435⟩,
⟨127,533046410,533046706⟩,
⟨128,536994155,536994453⟩]
theorem checked23904 : checkPrefixCuts (2^48) 3137077249 9 Manual.Count131072.C023904.packed 128 cuts23904 = true := by
 decide +kernel
def pointBounds23904 : List (Nat × Nat × Nat) := [(3137108992,102322391772054,102322773464339),(3137207296,102322795525101,102323177217610)]
theorem point_links_checked23904 : (cuts23904.take 2).map (fun c => (3137077249-1+2*2^9*c.k,102322262478691+c.lower,102322644170904+c.upper)) = pointBounds23904 := by
 decide +kernel
def cuts23905 : List PrefixCut := [⟨95,397549546,397549766⟩,
⟨128,542444436,542444735⟩]
theorem checked23905 : checkPrefixCuts (2^48) 3137208321 9 Manual.Count131072.C023905.packed 128 cuts23905 = true := by
 decide +kernel
def pointBounds23905 : List (Nat × Nat × Nat) := [(3137305600,102323197022392,102323578715123)]
theorem point_links_checked23905 : (cuts23905.take 1).map (fun c => (3137208321-1+2*2^9*c.k,102322799472846+c.lower,102323181165357+c.upper)) = pointBounds23905 := by
 decide +kernel
def cuts23906 : List PrefixCut := [⟨63,260537556,260537702⟩,
⟨128,531207435,531207730⟩]
theorem checked23906 : checkPrefixCuts (2^48) 3137339393 9 Manual.Count131072.C023906.packed 128 cuts23906 = true := by
 decide +kernel
def pointBounds23906 : List (Nat × Nat × Nat) := [(3137403904,102323602454838,102323984147794)]
theorem point_links_checked23906 : (cuts23906.take 1).map (fun c => (3137339393-1+2*2^9*c.k,102323341917282+c.lower,102323723610092+c.upper)) = pointBounds23906 := by
 decide +kernel
def cuts23907 : List PrefixCut := [⟨31,131071427,131071500⟩,
⟨127,536657813,536658107⟩,
⟨128,540335932,540336228⟩]
theorem checked23907 : checkPrefixCuts (2^48) 3137470465 9 Manual.Count131072.C023907.packed 128 cuts23907 = true := by
 decide +kernel
def pointBounds23907 : List (Nat × Nat × Nat) := [(3137502208,102324004196144,102324385889322),(3137600512,102324409782530,102324791475929)]
theorem point_links_checked23907 : (cuts23907.take 2).map (fun c => (3137470465-1+2*2^9*c.k,102323873124717+c.lower,102324254817822+c.upper)) = pointBounds23907 := by
 decide +kernel
def cuts23908 : List PrefixCut := [⟨95,405304498,405304728⟩,
⟨128,546862066,546862382⟩]
theorem checked23908 : checkPrefixCuts (2^48) 3137601537 9 Manual.Count131072.C023908.packed 128 cuts23908 = true := by
 decide +kernel
def pointBounds23908 : List (Nat × Nat × Nat) := [(3137698816,102324818765147,102325200458778)]
theorem point_links_checked23908 : (cuts23908.take 1).map (fun c => (3137601537-1+2*2^9*c.k,102324413460649+c.lower,102324795154050+c.upper)) = pointBounds23908 := by
 decide +kernel
def cuts23909 : List PrefixCut := [⟨63,260594586,260594736⟩,
⟨128,533204055,533204357⟩]
theorem checked23909 : checkPrefixCuts (2^48) 3137732609 9 Manual.Count131072.C023909.packed 128 cuts23909 = true := by
 decide +kernel
def pointBounds23909 : List (Nat × Nat × Nat) := [(3137797120,102325220917301,102325602611168)]
theorem point_links_checked23909 : (cuts23909.take 1).map (fun c => (3137732609-1+2*2^9*c.k,102324960322715+c.lower,102325342016432+c.upper)) = pointBounds23909 := by
 decide +kernel
def cuts23910 : List PrefixCut := [⟨31,132310838,132310917⟩,
⟨127,535514168,535514474⟩,
⟨128,539460923,539461232⟩]
theorem checked23910 : checkPrefixCuts (2^48) 3137863681 9 Manual.Count131072.C023910.packed 128 cuts23910 = true := by
 decide +kernel
def pointBounds23910 : List (Nat × Nat × Nat) := [(3137895424,102325625837608,102326007531706),(3137993728,102326029040938,102326410735263)]
theorem point_links_checked23910 : (cuts23910.take 2).map (fun c => (3137863681-1+2*2^9*c.k,102325493526770+c.lower,102325875220789+c.upper)) = pointBounds23910 := by
 decide +kernel
def cuts23911 : List PrefixCut := [⟨95,403459721,403459944⟩,
⟨128,541052932,541053235⟩]
theorem checked23911 : checkPrefixCuts (2^48) 3137994753 9 Manual.Count131072.C023911.packed 128 cuts23911 = true := by
 decide +kernel
def pointBounds23911 : List (Nat × Nat × Nat) := [(3138092032,102326436447414,102326818141965)]
theorem point_links_checked23911 : (cuts23911.take 1).map (fun c => (3137994753-1+2*2^9*c.k,102326032987693+c.lower,102326414682021+c.upper)) = pointBounds23911 := by
 decide +kernel
def cuts23912 : List PrefixCut := [⟨63,269441691,269441842⟩,
⟨128,542375749,542376048⟩]
theorem checked23912 : checkPrefixCuts (2^48) 3138125825 9 Manual.Count131072.C023912.packed 128 cuts23912 = true := by
 decide +kernel
def pointBounds23912 : List (Nat × Nat × Nat) := [(3138190336,102326843482316,102327225177098)]
theorem point_links_checked23912 : (cuts23912.take 1).map (fun c => (3138125825-1+2*2^9*c.k,102326574040625+c.lower,102326955735256+c.upper)) = pointBounds23912 := by
 decide +kernel
def cuts23913 : List PrefixCut := [⟨31,131666426,131666500⟩,
⟨127,531141921,531142221⟩,
⟨128,535536621,535536923⟩]
theorem checked23913 : checkPrefixCuts (2^48) 3138256897 9 Manual.Count131072.C023913.packed 128 cuts23913 = true := by
 decide +kernel
def pointBounds23913 : List (Nat × Nat × Nat) := [(3138288640,102327248082800,102327629777804),(3138386944,102327647558295,102328029253525)]
theorem point_links_checked23913 : (cuts23913.take 2).map (fun c => (3138256897-1+2*2^9*c.k,102327116416374+c.lower,102327498111304+c.upper)) = pointBounds23913 := by
 decide +kernel
def cuts23914 : List PrefixCut := [⟨95,391749909,391750131⟩,
⟨128,531657688,531657987⟩]
theorem checked23914 : checkPrefixCuts (2^48) 3138387969 9 Manual.Count131072.C023914.packed 128 cuts23914 = true := by
 decide +kernel
def pointBounds23914 : List (Nat × Nat × Nat) := [(3138485248,102328043702904,102328425398358)]
theorem point_links_checked23914 : (cuts23914.take 1).map (fun c => (3138387969-1+2*2^9*c.k,102327651952995+c.lower,102328033648227+c.upper)) = pointBounds23914 := by
 decide +kernel
def cuts23915 : List PrefixCut := [⟨63,262950813,262950963⟩,
⟨128,537016575,537016881⟩]
theorem checked23915 : checkPrefixCuts (2^48) 3138519041 9 Manual.Count131072.C023915.packed 128 cuts23915 = true := by
 decide +kernel
def pointBounds23915 : List (Nat × Nat × Nat) := [(3138583552,102328446561496,102328828257177)]
theorem point_links_checked23915 : (cuts23915.take 1).map (fun c => (3138519041-1+2*2^9*c.k,102328183610683+c.lower,102328565306214+c.upper)) = pointBounds23915 := by
 decide +kernel
def cuts23916 : List PrefixCut := [⟨31,128152427,128152503⟩,
⟨127,527308936,527309237⟩,
⟨128,531523732,531524035⟩]
theorem checked23916 : checkPrefixCuts (2^48) 3138650113 9 Manual.Count131072.C023916.packed 128 cuts23916 = true := by
 decide +kernel
def pointBounds23916 : List (Nat × Nat × Nat) := [(3138681856,102328848779685,102329230475598),(3138780160,102329247936194,102329629632332)]
theorem point_links_checked23916 : (cuts23916.take 2).map (fun c => (3138650113-1+2*2^9*c.k,102328720627258+c.lower,102329102323095+c.upper)) = pointBounds23916 := by
 decide +kernel
def cuts23917 : List PrefixCut := [⟨95,397978090,397978319⟩,
⟨128,537240616,537240921⟩]
theorem checked23917 : checkPrefixCuts (2^48) 3138781185 9 Manual.Count131072.C023917.packed 128 cuts23917 = true := by
 decide +kernel
def pointBounds23917 : List (Nat × Nat × Nat) := [(3138878464,102329650129080,102330031825449)]
theorem point_links_checked23917 : (cuts23917.take 1).map (fun c => (3138781185-1+2*2^9*c.k,102329252150990+c.lower,102329633847130+c.upper)) = pointBounds23917 := by
 decide +kernel
def cuts23918 : List PrefixCut := [⟨63,259689627,259689781⟩,
⟨128,535604096,535604401⟩]
theorem checked23918 : checkPrefixCuts (2^48) 3138912257 9 Manual.Count131072.C023918.packed 128 cuts23918 = true := by
 decide +kernel
def pointBounds23918 : List (Nat × Nat × Nat) := [(3138976768,102330049081233,102330430777832)]
theorem point_links_checked23918 : (cuts23918.take 1).map (fun c => (3138912257-1+2*2^9*c.k,102329789391606+c.lower,102330171088051+c.upper)) = pointBounds23918 := by
 decide +kernel
def cuts23919 : List PrefixCut := [⟨31,129481389,129481462⟩,
⟨127,529932847,529933148⟩,
⟨128,534416111,534416414⟩]
theorem checked23919 : checkPrefixCuts (2^48) 3139043329 9 Manual.Count131072.C023919.packed 128 cuts23919 = true := by
 decide +kernel
def pointBounds23919 : List (Nat × Nat × Nat) := [(3139075072,102330454477091,102330836173914),(3139173376,102330854928549,102331236625600)]
theorem point_links_checked23919 : (cuts23919.take 2).map (fun c => (3139043329-1+2*2^9*c.k,102330324995702+c.lower,102330706692452+c.upper)) = pointBounds23919 := by
 decide +kernel
def cuts23920 : List PrefixCut := [⟨95,397748987,397749215⟩,
⟨128,538697638,538697943⟩]
theorem checked23920 : checkPrefixCuts (2^48) 3139174401 9 Manual.Count131072.C023920.packed 128 cuts23920 = true := by
 decide +kernel
def pointBounds23920 : List (Nat × Nat × Nat) := [(3139271680,102331257160800,102331638858081)]
theorem point_links_checked23920 : (cuts23920.take 1).map (fun c => (3139174401-1+2*2^9*c.k,102330859411813+c.lower,102331241108866+c.upper)) = pointBounds23920 := by
 decide +kernel
def cuts23921 : List PrefixCut := [⟨63,262167575,262167719⟩,
⟨128,534281812,534282113⟩]
theorem checked23921 : checkPrefixCuts (2^48) 3139305473 9 Manual.Count131072.C023921.packed 128 cuts23921 = true := by
 decide +kernel
def pointBounds23921 : List (Nat × Nat × Nat) := [(3139369984,102331660277026,102332041974528)]
theorem point_links_checked23921 : (cuts23921.take 1).map (fun c => (3139305473-1+2*2^9*c.k,102331398109451+c.lower,102331779806809+c.upper)) = pointBounds23921 := by
 decide +kernel
def cuts23922 : List PrefixCut := [⟨31,130541070,130541148⟩,
⟨127,528163076,528163378⟩,
⟨128,532376816,532377121⟩]
theorem checked23922 : checkPrefixCuts (2^48) 3139436545 9 Manual.Count131072.C023922.packed 128 cuts23922 = true := by
 decide +kernel
def pointBounds23922 : List (Nat × Nat × Nat) := [(3139468288,102332062932333,102332444630070),(3139566592,102332460554339,102332842252300)]
theorem point_links_checked23922 : (cuts23922.take 2).map (fun c => (3139436545-1+2*2^9*c.k,102331932391263+c.lower,102332314088922+c.upper)) = pointBounds23922 := by
 decide +kernel
def cuts23923 : List PrefixCut := [⟨95,405140365,405140594⟩,
⟨128,545623126,545623431⟩]
theorem checked23923 : checkPrefixCuts (2^48) 3139567617 9 Manual.Count131072.C023923.packed 128 cuts23923 = true := by
 decide +kernel
def pointBounds23923 : List (Nat × Nat × Nat) := [(3139664896,102332869908444,102333251606637)]
theorem point_links_checked23923 : (cuts23923.take 1).map (fun c => (3139567617-1+2*2^9*c.k,102332464768079+c.lower,102332846466043+c.upper)) = pointBounds23923 := by
 decide +kernel
def cuts23924 : List PrefixCut := [⟨63,262851917,262852066⟩,
⟨128,531884044,531884342⟩]
theorem checked23924 : checkPrefixCuts (2^48) 3139698689 9 Manual.Count131072.C023924.packed 128 cuts23924 = true := by
 decide +kernel
def pointBounds23924 : List (Nat × Nat × Nat) := [(3139763200,102333273243122,102333654941540)]
theorem point_links_checked23924 : (cuts23924.take 1).map (fun c => (3139698689-1+2*2^9*c.k,102333010391205+c.lower,102333392089474+c.upper)) = pointBounds23924 := by
 decide +kernel
def cuts23925 : List PrefixCut := [⟨31,129180022,129180095⟩,
⟨127,536075181,536075474⟩,
⟨128,541095179,541095475⟩]
theorem checked23925 : checkPrefixCuts (2^48) 3139829761 9 Manual.Count131072.C023925.packed 128 cuts23925 = true := by
 decide +kernel
def pointBounds23925 : List (Nat × Nat × Nat) := [(3139861504,102333671455271,102334053153911),(3139959808,102334078350430,102334460049290)]
theorem point_links_checked23925 : (cuts23925.take 2).map (fun c => (3139829761-1+2*2^9*c.k,102333542275249+c.lower,102333923973816+c.upper)) = pointBounds23925 := by
 decide +kernel
def cuts23926 : List PrefixCut := [⟨95,396125445,396125668⟩,
⟨128,534259988,534260288⟩]
theorem checked23926 : checkPrefixCuts (2^48) 3139960833 9 Manual.Count131072.C023926.packed 128 cuts23926 = true := by
 decide +kernel
def pointBounds23926 : List (Nat × Nat × Nat) := [(3140058112,102334479495873,102334861194959)]
theorem point_links_checked23926 : (cuts23926.take 1).map (fun c => (3139960833-1+2*2^9*c.k,102334083370428+c.lower,102334465069291+c.upper)) = pointBounds23926 := by
 decide +kernel
def cuts23927 : List PrefixCut := [⟨63,270617531,270617676⟩,
⟨128,542394749,542395046⟩]
theorem checked23927 : checkPrefixCuts (2^48) 3140091905 9 Manual.Count131072.C023927.packed 128 cuts23927 = true := by
 decide +kernel
def pointBounds23927 : List (Nat × Nat × Nat) := [(3140156416,102334888247947,102335269947255)]
theorem point_links_checked23927 : (cuts23927.take 1).map (fun c => (3140091905-1+2*2^9*c.k,102334617630416+c.lower,102334999329579+c.upper)) = pointBounds23927 := by
 decide +kernel
def cuts23928 : List PrefixCut := [⟨31,131225443,131225520⟩,
⟨127,528210037,528210344⟩,
⟨128,532870880,532871190⟩]
theorem checked23928 : checkPrefixCuts (2^48) 3140222977 9 Manual.Count131072.C023928.packed 128 cuts23928 = true := by
 decide +kernel
def pointBounds23928 : List (Nat × Nat × Nat) := [(3140254720,102335291250608,102335672950145),(3140353024,102335688235202,102336069934969)]
theorem point_links_checked23928 : (cuts23928.take 2).map (fun c => (3140222977-1+2*2^9*c.k,102335160025165+c.lower,102335541724625+c.upper)) = pointBounds23928 := by
 decide +kernel
def cuts23929 : List PrefixCut := [⟨95,400826248,400826467⟩,
⟨128,536702775,536703070⟩]
theorem checked23929 : checkPrefixCuts (2^48) 3140354049 9 Manual.Count131072.C023929.packed 128 cuts23929 = true := by
 decide +kernel
def pointBounds23929 : List (Nat × Nat × Nat) := [(3140451328,102336093722293,102336475422282)]
theorem point_links_checked23929 : (cuts23929.take 1).map (fun c => (3140354049-1+2*2^9*c.k,102335692896045+c.lower,102336074595815+c.upper)) = pointBounds23929 := by
 decide +kernel
def cuts23930 : List PrefixCut := [⟨63,269060028,269060178⟩,
⟨128,540444681,540444987⟩]
theorem checked23930 : checkPrefixCuts (2^48) 3140485121 9 Manual.Count131072.C023930.packed 128 cuts23930 = true := by
 decide +kernel
def pointBounds23930 : List (Nat × Nat × Nat) := [(3140549632,102336498658848,102336880359063)]
theorem point_links_checked23930 : (cuts23930.take 1).map (fun c => (3140485121-1+2*2^9*c.k,102336229598820+c.lower,102336611298885+c.upper)) = pointBounds23930 := by
 decide +kernel
def cuts23931 : List PrefixCut := [⟨31,127355206,127355279⟩,
⟨127,538271114,538271428⟩,
⟨128,541855929,541856245⟩]
theorem checked23931 : checkPrefixCuts (2^48) 3140616193 9 Manual.Count131072.C023931.packed 128 cuts23931 = true := by
 decide +kernel
def pointBounds23931 : List (Nat × Nat × Nat) := [(3140647936,102336897398707,102337279099151),(3140746240,102337308314615,102337690015300)]
theorem point_links_checked23931 : (cuts23931.take 2).map (fun c => (3140616193-1+2*2^9*c.k,102336770043501+c.lower,102337151743872+c.upper)) = pointBounds23931 := by
 decide +kernel
def cuts23932 : List PrefixCut := [⟨95,404181637,404181863⟩,
⟨128,541295807,541296110⟩]
theorem checked23932 : checkPrefixCuts (2^48) 3140747265 9 Manual.Count131072.C023932.packed 128 cuts23932 = true := by
 decide +kernel
def pointBounds23932 : List (Nat × Nat × Nat) := [(3140844544,102337716081067,102338097781980)]
theorem point_links_checked23932 : (cuts23932.take 1).map (fun c => (3140747265-1+2*2^9*c.k,102337311899430+c.lower,102337693600117+c.upper)) = pointBounds23932 := by
 decide +kernel
def cuts23933 : List PrefixCut := [⟨63,262125945,262126093⟩,
⟨128,534462405,534462705⟩]
theorem checked23933 : checkPrefixCuts (2^48) 3140878337 9 Manual.Count131072.C023933.packed 128 cuts23933 = true := by
 decide +kernel
def pointBounds23933 : List (Nat × Nat × Nat) := [(3140942848,102338115321182,102338497022320)]
theorem point_links_checked23933 : (cuts23933.take 1).map (fun c => (3140878337-1+2*2^9*c.k,102337853195237+c.lower,102338234896227+c.upper)) = pointBounds23933 := by
 decide +kernel
def cuts23934 : List PrefixCut := [⟨31,126174298,126174375⟩,
⟨127,532468578,532468882⟩,
⟨128,536142553,536142859⟩]
theorem checked23934 : checkPrefixCuts (2^48) 3141009409 9 Manual.Count131072.C023934.packed 128 cuts23934 = true := by
 decide +kernel
def pointBounds23934 : List (Nat × Nat × Nat) := [(3141041152,102338513831940,102338895533307),(3141139456,102338920126220,102339301827814)]
theorem point_links_checked23934 : (cuts23934.take 2).map (fun c => (3141009409-1+2*2^9*c.k,102338387657642+c.lower,102338769358932+c.upper)) = pointBounds23934 := by
 decide +kernel
def cuts23935 : List PrefixCut := [⟨95,398216825,398217053⟩,
⟨128,536478703,536479009⟩]
theorem checked23935 : checkPrefixCuts (2^48) 3141140481 9 Manual.Count131072.C023935.packed 128 cuts23935 = true := by
 decide +kernel
def pointBounds23935 : List (Nat × Nat × Nat) := [(3141237760,102339322017020,102339703718844)]
theorem point_links_checked23935 : (cuts23935.take 1).map (fun c => (3141140481-1+2*2^9*c.k,102338923800195+c.lower,102339305501791+c.upper)) = pointBounds23935 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000122
