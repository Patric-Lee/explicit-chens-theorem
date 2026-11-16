import PlattAssemblyKernel
import PlattCertificates.Count131072.C023808
import PlattCertificates.Count131072.C023809
import PlattCertificates.Count131072.C023810
import PlattCertificates.Count131072.C023811
import PlattCertificates.Count131072.C023812
import PlattCertificates.Count131072.C023813
import PlattCertificates.Count131072.C023814
import PlattCertificates.Count131072.C023815
import PlattCertificates.Count131072.C023816
import PlattCertificates.Count131072.C023817
import PlattCertificates.Count131072.C023818
import PlattCertificates.Count131072.C023819
import PlattCertificates.Count131072.C023820
import PlattCertificates.Count131072.C023821
import PlattCertificates.Count131072.C023822
import PlattCertificates.Count131072.C023823
import PlattCertificates.Count131072.C023824
import PlattCertificates.Count131072.C023825
import PlattCertificates.Count131072.C023826
import PlattCertificates.Count131072.C023827
import PlattCertificates.Count131072.C023828
import PlattCertificates.Count131072.C023829
import PlattCertificates.Count131072.C023830
import PlattCertificates.Count131072.C023831
import PlattCertificates.Count131072.C023832
import PlattCertificates.Count131072.C023833
import PlattCertificates.Count131072.C023834
import PlattCertificates.Count131072.C023835
import PlattCertificates.Count131072.C023836
import PlattCertificates.Count131072.C023837
import PlattCertificates.Count131072.C023838
import PlattCertificates.Count131072.C023839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000119
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23808 : List PrefixCut := [⟨31,132246381,132246454⟩,
⟨127,537445173,537445480⟩,
⟨128,541588981,541589290⟩]
theorem checked23808 : checkPrefixCuts (2^48) 3124494337 9 Manual.Count131072.C023808.packed 128 cuts23808 = true := by
 decide +kernel
def pointBounds23808 : List (Nat × Nat × Nat) := [(3124526080,102270676659283,102271058322366),(3124624384,102271081858075,102271463521392)]
theorem point_links_checked23808 : (cuts23808.take 2).map (fun c => (3124494337-1+2*2^9*c.k,102270544412902+c.lower,102270926075912+c.upper)) = pointBounds23808 := by
 decide +kernel
def cuts23809 : List PrefixCut := [⟨95,402123190,402123416⟩,
⟨128,543638025,543638331⟩]
theorem checked23809 : checkPrefixCuts (2^48) 3124625409 9 Manual.Count131072.C023809.packed 128 cuts23809 = true := by
 decide +kernel
def pointBounds23809 : List (Nat × Nat × Nat) := [(3124722688,102271488125073,102271869788618)]
theorem point_links_checked23809 : (cuts23809.take 1).map (fun c => (3124625409-1+2*2^9*c.k,102271086001883+c.lower,102271467665202+c.upper)) = pointBounds23809 := by
 decide +kernel
def cuts23810 : List PrefixCut := [⟨63,267441749,267441895⟩,
⟨128,542714532,542714833⟩]
theorem checked23810 : checkPrefixCuts (2^48) 3124756481 9 Manual.Count131072.C023810.packed 128 cuts23810 = true := by
 decide +kernel
def pointBounds23810 : List (Nat × Nat × Nat) := [(3124820992,102271897081657,102272278745428)]
theorem point_links_checked23810 : (cuts23810.take 1).map (fun c => (3124756481-1+2*2^9*c.k,102271629639908+c.lower,102272011303533+c.upper)) = pointBounds23810 := by
 decide +kernel
def cuts23811 : List PrefixCut := [⟨31,130338161,130338232⟩,
⟨127,535936280,535936578⟩,
⟨128,540800138,540800439⟩]
theorem checked23811 : checkPrefixCuts (2^48) 3124887553 9 Manual.Count131072.C023811.packed 128 cuts23811 = true := by
 decide +kernel
def pointBounds23811 : List (Nat × Nat × Nat) := [(3124919296,102272302692601,102272684356598),(3125017600,102272708290720,102273089954944)]
theorem point_links_checked23811 : (cuts23811.take 2).map (fun c => (3124887553-1+2*2^9*c.k,102272172354440+c.lower,102272554018366+c.upper)) = pointBounds23811 := by
 decide +kernel
def cuts23812 : List PrefixCut := [⟨95,395317383,395317611⟩,
⟨128,534022321,534022630⟩]
theorem checked23812 : checkPrefixCuts (2^48) 3125018625 9 Manual.Count131072.C023812.packed 128 cuts23812 = true := by
 decide +kernel
def pointBounds23812 : List (Nat × Nat × Nat) := [(3125115904,102273108471961,102273490136416)]
theorem point_links_checked23812 : (cuts23812.take 1).map (fun c => (3125018625-1+2*2^9*c.k,102272713154578+c.lower,102273094818805+c.upper)) = pointBounds23812 := by
 decide +kernel
def cuts23813 : List PrefixCut := [⟨63,267137876,267138027⟩,
⟨128,541205164,541205472⟩]
theorem checked23813 : checkPrefixCuts (2^48) 3125149697 9 Manual.Count131072.C023813.packed 128 cuts23813 = true := by
 decide +kernel
def pointBounds23813 : List (Nat × Nat × Nat) := [(3125214208,102273514314775,102273895979462)]
theorem point_links_checked23813 : (cuts23813.take 1).map (fun c => (3125149697-1+2*2^9*c.k,102273247176899+c.lower,102273628841435+c.upper)) = pointBounds23813 := by
 decide +kernel
def cuts23814 : List PrefixCut := [⟨31,135275235,135275313⟩,
⟨127,536499422,536499730⟩,
⟨128,540822307,540822618⟩]
theorem checked23814 : checkPrefixCuts (2^48) 3125280769 9 Manual.Count131072.C023814.packed 128 cuts23814 = true := by
 decide +kernel
def pointBounds23814 : List (Nat × Nat × Nat) := [(3125312512,102273923657298,102274305322220),(3125410816,102274324881485,102274706546637)]
theorem point_links_checked23814 : (cuts23814.take 2).map (fun c => (3125280769-1+2*2^9*c.k,102273788382063+c.lower,102274170046907+c.upper)) = pointBounds23814 := by
 decide +kernel
def cuts23815 : List PrefixCut := [⟨95,397879336,397879566⟩,
⟨128,535666248,535666554⟩]
theorem checked23815 : checkPrefixCuts (2^48) 3125411841 9 Manual.Count131072.C023815.packed 128 cuts23815 = true := by
 decide +kernel
def pointBounds23815 : List (Nat × Nat × Nat) := [(3125509120,102274727083706,102275108749091)]
theorem point_links_checked23815 : (cuts23815.take 1).map (fun c => (3125411841-1+2*2^9*c.k,102274329204370+c.lower,102274710869525+c.upper)) = pointBounds23815 := by
 decide +kernel
def cuts23816 : List PrefixCut := [⟨63,263321941,263322090⟩,
⟨128,541317084,541317392⟩]
theorem checked23816 : checkPrefixCuts (2^48) 3125542913 9 Manual.Count131072.C023816.packed 128 cuts23816 = true := by
 decide +kernel
def pointBounds23816 : List (Nat × Nat × Nat) := [(3125607424,102275128192559,102275509858169)]
theorem point_links_checked23816 : (cuts23816.take 1).map (fun c => (3125542913-1+2*2^9*c.k,102274864870618+c.lower,102275246536079+c.upper)) = pointBounds23816 := by
 decide +kernel
def cuts23817 : List PrefixCut := [⟨31,129224756,129224832⟩,
⟨127,539493530,539493841⟩,
⟨128,543995969,543996283⟩]
theorem checked23817 : checkPrefixCuts (2^48) 3125673985 9 Manual.Count131072.C023817.packed 128 cuts23817 = true := by
 decide +kernel
def pointBounds23817 : List (Nat × Nat × Nat) := [(3125705728,102275535412458,102275917078303),(3125804032,102275945681232,102276327347312)]
theorem point_links_checked23817 : (cuts23817.take 2).map (fun c => (3125673985-1+2*2^9*c.k,102275406187702+c.lower,102275787853471+c.upper)) = pointBounds23817 := by
 decide +kernel
def cuts23818 : List PrefixCut := [⟨95,401791355,401791579⟩,
⟨128,542712525,542712826⟩]
theorem checked23818 : checkPrefixCuts (2^48) 3125805057 9 Manual.Count131072.C023818.packed 128 cuts23818 = true := by
 decide +kernel
def pointBounds23818 : List (Nat × Nat × Nat) := [(3125902336,102276351975026,102276733641333)]
theorem point_links_checked23818 : (cuts23818.take 1).map (fun c => (3125805057-1+2*2^9*c.k,102275950183671+c.lower,102276331849754+c.upper)) = pointBounds23818 := by
 decide +kernel
def cuts23819 : List PrefixCut := [⟨63,265449909,265450064⟩,
⟨128,538367747,538368058⟩]
theorem checked23819 : checkPrefixCuts (2^48) 3125936129 9 Manual.Count131072.C023819.packed 128 cuts23819 = true := by
 decide +kernel
def pointBounds23819 : List (Nat × Nat × Nat) := [(3126000640,102276758346105,102277140012644)]
theorem point_links_checked23819 : (cuts23819.take 1).map (fun c => (3125936129-1+2*2^9*c.k,102276492896196+c.lower,102276874562580+c.upper)) = pointBounds23819 := by
 decide +kernel
def cuts23820 : List PrefixCut := [⟨31,128308083,128308155⟩,
⟨127,532492703,532493005⟩,
⟨128,537264688,537264993⟩]
theorem checked23820 : checkPrefixCuts (2^48) 3126067201 9 Manual.Count131072.C023820.packed 128 cuts23820 = true := by
 decide +kernel
def pointBounds23820 : List (Nat × Nat × Nat) := [(3126098944,102277159572026,102277541238793),(3126197248,102277563756646,102277945423643)]
theorem point_links_checked23820 : (cuts23820.take 2).map (fun c => (3126067201-1+2*2^9*c.k,102277031263943+c.lower,102277412930638+c.upper)) = pointBounds23820 := by
 decide +kernel
def cuts23821 : List PrefixCut := [⟨95,401920929,401921164⟩,
⟨128,541834001,541834315⟩]
theorem checked23821 : checkPrefixCuts (2^48) 3126198273 9 Manual.Count131072.C023821.packed 128 cuts23821 = true := by
 decide +kernel
def pointBounds23821 : List (Nat × Nat × Nat) := [(3126295552,102277970449560,102278352116795)]
theorem point_links_checked23821 : (cuts23821.take 1).map (fun c => (3126198273-1+2*2^9*c.k,102277568528631+c.lower,102277950195631+c.upper)) = pointBounds23821 := by
 decide +kernel
def cuts23822 : List PrefixCut := [⟨63,263795936,263796085⟩,
⟨128,536409329,536409635⟩]
theorem checked23822 : checkPrefixCuts (2^48) 3126329345 9 Manual.Count131072.C023822.packed 128 cuts23822 = true := by
 decide +kernel
def pointBounds23822 : List (Nat × Nat × Nat) := [(3126393856,102278374158568,102278755826031)]
theorem point_links_checked23822 : (cuts23822.take 1).map (fun c => (3126329345-1+2*2^9*c.k,102278110362632+c.lower,102278492029946+c.upper)) = pointBounds23822 := by
 decide +kernel
def cuts23823 : List PrefixCut := [⟨31,133063518,133063593⟩,
⟨127,538817730,538818032⟩,
⟨128,542328749,542329053⟩]
theorem checked23823 : checkPrefixCuts (2^48) 3126460417 9 Manual.Count131072.C023823.packed 128 cuts23823 = true := by
 decide +kernel
def pointBounds23823 : List (Nat × Nat × Nat) := [(3126492160,102278779835479,102279161503174),(3126590464,102279185589691,102279567257613)]
theorem point_links_checked23823 : (cuts23823.take 2).map (fun c => (3126460417-1+2*2^9*c.k,102278646771961+c.lower,102279028439581+c.upper)) = pointBounds23823 := by
 decide +kernel
def cuts23824 : List PrefixCut := [⟨95,393858126,393858360⟩,
⟨128,533033411,533033722⟩]
theorem checked23824 : checkPrefixCuts (2^48) 3126591489 9 Manual.Count131072.C023824.packed 128 cuts23824 = true := by
 decide +kernel
def pointBounds23824 : List (Nat × Nat × Nat) := [(3126688768,102279582958836,102279964626994)]
theorem point_links_checked23824 : (cuts23824.take 1).map (fun c => (3126591489-1+2*2^9*c.k,102279189100710+c.lower,102279570768634+c.upper)) = pointBounds23824 := by
 decide +kernel
def cuts23825 : List PrefixCut := [⟨63,263582715,263582861⟩,
⟨128,537062048,537062346⟩]
theorem checked23825 : checkPrefixCuts (2^48) 3126722561 9 Manual.Count131072.C023825.packed 128 cuts23825 = true := by
 decide +kernel
def pointBounds23825 : List (Nat × Nat × Nat) := [(3126787072,102279985716836,102280367385217)]
theorem point_links_checked23825 : (cuts23825.take 1).map (fun c => (3126722561-1+2*2^9*c.k,102279722134121+c.lower,102280103802356+c.upper)) = pointBounds23825 := by
 decide +kernel
def cuts23826 : List PrefixCut := [⟨31,130256219,130256291⟩,
⟨127,545681094,545681396⟩,
⟨128,550001805,550002109⟩]
theorem checked23826 : checkPrefixCuts (2^48) 3126853633 9 Manual.Count131072.C023826.packed 128 cuts23826 = true := by
 decide +kernel
def pointBounds23826 : List (Nat × Nat × Nat) := [(3126885376,102280389452388,102280771120993),(3126983680,102280804877263,102281186546098)]
theorem point_links_checked23826 : (cuts23826.take 2).map (fun c => (3126853633-1+2*2^9*c.k,102280259196169+c.lower,102280640864702+c.upper)) = pointBounds23826 := by
 decide +kernel
def cuts23827 : List PrefixCut := [⟨95,401369717,401369939⟩,
⟨128,535936923,535937225⟩]
theorem checked23827 : checkPrefixCuts (2^48) 3126984705 9 Manual.Count131072.C023827.packed 128 cuts23827 = true := by
 decide +kernel
def pointBounds23827 : List (Nat × Nat × Nat) := [(3127081984,102281210567691,102281592236750)]
theorem point_links_checked23827 : (cuts23827.take 1).map (fun c => (3126984705-1+2*2^9*c.k,102280809197974+c.lower,102281190866811+c.upper)) = pointBounds23827 := by
 decide +kernel
def cuts23828 : List PrefixCut := [⟨63,264989732,264989883⟩,
⟨128,538434707,538435011⟩]
theorem checked23828 : checkPrefixCuts (2^48) 3127115777 9 Manual.Count131072.C023828.packed 128 cuts23828 = true := by
 decide +kernel
def pointBounds23828 : List (Nat × Nat × Nat) := [(3127180288,102281610124629,102281991793919)]
theorem point_links_checked23828 : (cuts23828.take 1).map (fun c => (3127115777-1+2*2^9*c.k,102281345134897+c.lower,102281726804036+c.upper)) = pointBounds23828 := by
 decide +kernel
def cuts23829 : List PrefixCut := [⟨31,134110128,134110207⟩,
⟨127,536972202,536972509⟩,
⟨128,541652384,541652693⟩]
theorem checked23829 : checkPrefixCuts (2^48) 3127246849 9 Manual.Count131072.C023829.packed 128 cuts23829 = true := by
 decide +kernel
def pointBounds23829 : List (Nat × Nat × Nat) := [(3127278592,102282017679732,102282399349254),(3127376896,102282420541806,102282802211556)]
theorem point_links_checked23829 : (cuts23829.take 2).map (fun c => (3127246849-1+2*2^9*c.k,102281883569604+c.lower,102282265239047+c.upper)) = pointBounds23829 := by
 decide +kernel
def cuts23830 : List PrefixCut := [⟨95,402309356,402309583⟩,
⟨128,537849639,537849944⟩]
theorem checked23830 : checkPrefixCuts (2^48) 3127377921 9 Manual.Count131072.C023830.packed 128 cuts23830 = true := by
 decide +kernel
def pointBounds23830 : List (Nat × Nat × Nat) := [(3127475200,102282827531344,102283209201323)]
theorem point_links_checked23830 : (cuts23830.take 1).map (fun c => (3127377921-1+2*2^9*c.k,102282425221988+c.lower,102282806891740+c.upper)) = pointBounds23830 := by
 decide +kernel
def cuts23831 : List PrefixCut := [⟨63,266576389,266576541⟩,
⟨128,538996960,538997267⟩]
theorem checked23831 : checkPrefixCuts (2^48) 3127508993 9 Manual.Count131072.C023831.packed 128 cuts23831 = true := by
 decide +kernel
def pointBounds23831 : List (Nat × Nat × Nat) := [(3127573504,102283229648016,102283611318225)]
theorem point_links_checked23831 : (cuts23831.take 1).map (fun c => (3127508993-1+2*2^9*c.k,102282963071627+c.lower,102283344741684+c.upper)) = pointBounds23831 := by
 decide +kernel
def cuts23832 : List PrefixCut := [⟨31,129953491,129953566⟩,
⟨127,529345196,529345488⟩,
⟨128,532854891,532855185⟩]
theorem checked23832 : checkPrefixCuts (2^48) 3127640065 9 Manual.Count131072.C023832.packed 128 cuts23832 = true := by
 decide +kernel
def pointBounds23832 : List (Nat × Nat × Nat) := [(3127671808,102283632022078,102284013692517),(3127770112,102284031413783,102284413084439)]
theorem point_links_checked23832 : (cuts23832.take 2).map (fun c => (3127640065-1+2*2^9*c.k,102283502068587+c.lower,102283883738951+c.upper)) = pointBounds23832 := by
 decide +kernel
def cuts23833 : List PrefixCut := [⟨95,407298261,407298481⟩,
⟨128,549480680,549480981⟩]
theorem checked23833 : checkPrefixCuts (2^48) 3127771137 9 Manual.Count131072.C023833.packed 128 cuts23833 = true := by
 decide +kernel
def pointBounds23833 : List (Nat × Nat × Nat) := [(3127868416,102284442221739,102284823892617)]
theorem point_links_checked23833 : (cuts23833.take 1).map (fun c => (3127771137-1+2*2^9*c.k,102284034923478+c.lower,102284416594136+c.upper)) = pointBounds23833 := by
 decide +kernel
def cuts23834 : List PrefixCut := [⟨63,265553021,265553170⟩,
⟨128,538209315,538209618⟩]
theorem checked23834 : checkPrefixCuts (2^48) 3127902209 9 Manual.Count131072.C023834.packed 128 cuts23834 = true := by
 decide +kernel
def pointBounds23834 : List (Nat × Nat × Nat) := [(3127966720,102284849957179,102285231628287)]
theorem point_links_checked23834 : (cuts23834.take 1).map (fun c => (3127902209-1+2*2^9*c.k,102284584404158+c.lower,102284966075117+c.upper)) = pointBounds23834 := by
 decide +kernel
def cuts23835 : List PrefixCut := [⟨31,125977822,125977895⟩,
⟨127,525409210,525409510⟩,
⟨128,529818273,529818575⟩]
theorem checked23835 : checkPrefixCuts (2^48) 3128033281 9 Manual.Count131072.C023835.packed 128 cuts23835 = true := by
 decide +kernel
def pointBounds23835 : List (Nat × Nat × Nat) := [(3128065024,102285248591295,102285630262630),(3128163328,102285648022683,102286029694245)]
theorem point_links_checked23835 : (cuts23835.take 2).map (fun c => (3128033281-1+2*2^9*c.k,102285122613473+c.lower,102285504284735+c.upper)) = pointBounds23835 := by
 decide +kernel
def cuts23836 : List PrefixCut := [⟨95,395639635,395639857⟩,
⟨128,532045630,532045929⟩]
theorem checked23836 : checkPrefixCuts (2^48) 3128164353 9 Manual.Count131072.C023836.packed 128 cuts23836 = true := by
 decide +kernel
def pointBounds23836 : List (Nat × Nat × Nat) := [(3128261632,102286048071381,102286429743167)]
theorem point_links_checked23836 : (cuts23836.take 1).map (fun c => (3128164353-1+2*2^9*c.k,102285652431746+c.lower,102286034103310+c.upper)) = pointBounds23836 := by
 decide +kernel
def cuts23837 : List PrefixCut := [⟨63,267589079,267589235⟩,
⟨128,541290798,541291106⟩]
theorem checked23837 : checkPrefixCuts (2^48) 3128295425 9 Manual.Count131072.C023837.packed 128 cuts23837 = true := by
 decide +kernel
def pointBounds23837 : List (Nat × Nat × Nat) := [(3128359936,102286452066455,102286833738474)]
theorem point_links_checked23837 : (cuts23837.take 1).map (fun c => (3128295425-1+2*2^9*c.k,102286184477376+c.lower,102286566149239+c.upper)) = pointBounds23837 := by
 decide +kernel
def cuts23838 : List PrefixCut := [⟨31,130190721,130190793⟩,
⟨127,537939255,537939556⟩,
⟨128,542257794,542258097⟩]
theorem checked23838 : checkPrefixCuts (2^48) 3128426497 9 Manual.Count131072.C023838.packed 128 cuts23838 = true := by
 decide +kernel
def pointBounds23838 : List (Nat × Nat × Nat) := [(3128458240,102286855958895,102287237631138),(3128556544,102287263707429,102287645379901)]
theorem point_links_checked23838 : (cuts23838.take 2).map (fun c => (3128426497-1+2*2^9*c.k,102286725768174+c.lower,102287107440345+c.upper)) = pointBounds23838 := by
 decide +kernel
def cuts23839 : List PrefixCut := [⟨95,394960102,394960321⟩,
⟨128,532518493,532518792⟩]
theorem checked23839 : checkPrefixCuts (2^48) 3128557569 9 Manual.Count131072.C023839.packed 128 cuts23839 = true := by
 decide +kernel
def pointBounds23839 : List (Nat × Nat × Nat) := [(3128654848,102287662986070,102288044658763)]
theorem point_links_checked23839 : (cuts23839.take 1).map (fun c => (3128557569-1+2*2^9*c.k,102287268025968+c.lower,102287649698442+c.upper)) = pointBounds23839 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000119
