import PlattAssemblyKernel
import PlattCertificates.Count131072.C015728
import PlattCertificates.Count131072.C015729
import PlattCertificates.Count131072.C015730
import PlattCertificates.Count131072.C015731
import PlattCertificates.Count131072.C015732
import PlattCertificates.Count131072.C015733
import PlattCertificates.Count131072.C015734
import PlattCertificates.Count131072.C015735
import PlattCertificates.Count131072.C015736
import PlattCertificates.Count131072.C015737
import PlattCertificates.Count131072.C015738
import PlattCertificates.Count131072.C015739
import PlattCertificates.Count131072.C015740
import PlattCertificates.Count131072.C015741
import PlattCertificates.Count131072.C015742
import PlattCertificates.Count131072.C015743
import PlattCertificates.Count131072.C015744
import PlattCertificates.Count131072.C015745
import PlattCertificates.Count131072.C015746
import PlattCertificates.Count131072.C015747
import PlattCertificates.Count131072.C015748
import PlattCertificates.Count131072.C015749
import PlattCertificates.Count131072.C015750
import PlattCertificates.Count131072.C015751
import PlattCertificates.Count131072.C015752
import PlattCertificates.Count131072.C015753
import PlattCertificates.Count131072.C015754
import PlattCertificates.Count131072.C015755
import PlattCertificates.Count131072.C015756
import PlattCertificates.Count131072.C015757
import PlattCertificates.Count131072.C015758
import PlattCertificates.Count131072.C015759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15728 : List PrefixCut := [⟨38,243664357,243664513⟩,
⟨102,666386912,666387343⟩,
⟨128,834818028,834818566⟩]
theorem checked15728 : checkPrefixCuts (2^48) 2065432577 9 Manual.Count131072.C015728.packed 128 cuts15728 = true := by
 decide +kernel
def pointBounds15728 : List (Nat × Nat × Nat) := [(2065471488,96890481972301,96890860415193),(2065537024,96890904694856,96891283138023)]
theorem point_links_checked15728 : (cuts15728.take 2).map (fun c => (2065432577-1+2*2^9*c.k,96890238307944+c.lower,96890616750680+c.upper)) = pointBounds15728 := by
 decide +kernel
def cuts15729 : List PrefixCut := [⟨38,249644741,249644907⟩,
⟨102,655307224,655307656⟩,
⟨128,826044134,826044677⟩]
theorem checked15729 : checkPrefixCuts (2^48) 2065563649 9 Manual.Count131072.C015729.packed 128 cuts15729 = true := by
 decide +kernel
def pointBounds15729 : List (Nat × Nat × Nat) := [(2065602560,96891322770713,96891701214153),(2065668096,96891728433196,96892106876902)]
theorem point_links_checked15729 : (cuts15729.take 2).map (fun c => (2065563649-1+2*2^9*c.k,96891073125972+c.lower,96891451569246+c.upper)) = pointBounds15729 := by
 decide +kernel
def cuts15730 : List PrefixCut := [⟨38,238728048,238728208⟩,
⟨102,651450128,651450556⟩,
⟨128,821358657,821359194⟩]
theorem checked15730 : checkPrefixCuts (2^48) 2065694721 9 Manual.Count131072.C015730.packed 128 cuts15730 = true := by
 decide +kernel
def pointBounds15730 : List (Nat × Nat × Nat) := [(2065733632,96892137898154,96892516342131),(2065799168,96892550620234,96892929064479)]
theorem point_links_checked15730 : (cuts15730.take 2).map (fun c => (2065694721-1+2*2^9*c.k,96891899170106+c.lower,96892277613923+c.upper)) = pointBounds15730 := by
 decide +kernel
def cuts15731 : List PrefixCut := [⟨38,248523026,248523184⟩,
⟨102,654270196,654270616⟩,
⟨128,825394146,825394676⟩]
theorem checked15731 : checkPrefixCuts (2^48) 2065825793 9 Manual.Count131072.C015731.packed 128 cuts15731 = true := by
 decide +kernel
def pointBounds15731 : List (Nat × Nat × Nat) := [(2065864704,96892969051789,96893347496301),(2065930240,96893374798959,96893753243733)]
theorem point_links_checked15731 : (cuts15731.take 2).map (fun c => (2065825793-1+2*2^9*c.k,96892720528763+c.lower,96893098973117+c.upper)) = pointBounds15731 := by
 decide +kernel
def cuts15732 : List PrefixCut := [⟨38,244556255,244556413⟩,
⟨102,668670197,668670629⟩,
⟨128,840736958,840737504⟩]
theorem checked15732 : checkPrefixCuts (2^48) 2065956865 9 Manual.Count131072.C015732.packed 128 cuts15732 = true := by
 decide +kernel
def pointBounds15732 : List (Nat × Nat × Nat) := [(2065995776,96893790479164,96894168924206),(2066061312,96894214593106,96894593038422)]
theorem point_links_checked15732 : (cuts15732.take 2).map (fun c => (2065956865-1+2*2^9*c.k,96893545922909+c.lower,96893924367793+c.upper)) = pointBounds15732 := by
 decide +kernel
def cuts15733 : List PrefixCut := [⟨38,252578571,252578735⟩,
⟨102,674622065,674622502⟩,
⟨128,844906957,844907506⟩]
theorem checked15733 : checkPrefixCuts (2^48) 2066087937 9 Manual.Count131072.C015733.packed 128 cuts15733 = true := by
 decide +kernel
def pointBounds15733 : List (Nat × Nat × Nat) := [(2066126848,96894639238438,96895017684032),(2066192384,96895061281932,96895439727799)]
theorem point_links_checked15733 : (cuts15733.take 2).map (fun c => (2066087937-1+2*2^9*c.k,96894386659867+c.lower,96894765105297+c.upper)) = pointBounds15733 := by
 decide +kernel
def cuts15734 : List PrefixCut := [⟨38,250246686,250246846⟩,
⟨102,662455373,662455806⟩,
⟨128,831094834,831095378⟩]
theorem checked15734 : checkPrefixCuts (2^48) 2066219009 9 Manual.Count131072.C015734.packed 128 cuts15734 = true := by
 decide +kernel
def pointBounds15734 : List (Nat × Nat × Nat) := [(2066257920,96895481813510,96895860259649),(2066323456,96895894022197,96896272468609)]
theorem point_links_checked15734 : (cuts15734.take 2).map (fun c => (2066219009-1+2*2^9*c.k,96895231566824+c.lower,96895610012803+c.upper)) = pointBounds15734 := by
 decide +kernel
def cuts15735 : List PrefixCut := [⟨38,250911935,250912098⟩,
⟨102,667998214,667998647⟩,
⟨128,838533910,838534451⟩]
theorem checked15735 : checkPrefixCuts (2^48) 2066350081 9 Manual.Count131072.C015735.packed 128 cuts15735 = true := by
 decide +kernel
def pointBounds15735 : List (Nat × Nat × Nat) := [(2066388992,96896313573593,96896692020279),(2066454528,96896730659872,96897109106828)]
theorem point_links_checked15735 : (cuts15735.take 2).map (fun c => (2066350081-1+2*2^9*c.k,96896062661658+c.lower,96896441108181+c.upper)) = pointBounds15735 := by
 decide +kernel
def cuts15736 : List PrefixCut := [⟨38,247899438,247899598⟩,
⟨102,664550629,664551060⟩,
⟨128,832623861,832624404⟩]
theorem checked15736 : checkPrefixCuts (2^48) 2066481153 9 Manual.Count131072.C015736.packed 128 cuts15736 = true := by
 decide +kernel
def pointBounds15736 : List (Nat × Nat × Nat) := [(2066520064,96897149095006,96897527542230),(2066585600,96897565746197,96897944193692)]
theorem point_links_checked15736 : (cuts15736.take 2).map (fun c => (2066481153-1+2*2^9*c.k,96896901195568+c.lower,96897279642632+c.upper)) = pointBounds15736 := by
 decide +kernel
def cuts15737 : List PrefixCut := [⟨38,251969682,251969846⟩,
⟨102,660014000,660014429⟩,
⟨128,829847112,829847654⟩]
theorem checked15737 : checkPrefixCuts (2^48) 2066612225 9 Manual.Count131072.C015737.packed 128 cuts15737 = true := by
 decide +kernel
def pointBounds15737 : List (Nat × Nat × Nat) := [(2066651136,96897985789111,96898364236882),(2066716672,96898393833429,96898772281465)]
theorem point_links_checked15737 : (cuts15737.take 2).map (fun c => (2066612225-1+2*2^9*c.k,96897733819429+c.lower,96898112267036+c.upper)) = pointBounds15737 := by
 decide +kernel
def cuts15738 : List PrefixCut := [⟨38,253588023,253588189⟩,
⟨102,668960733,668961166⟩,
⟨128,835787022,835787565⟩]
theorem checked15738 : checkPrefixCuts (2^48) 2066743297 9 Manual.Count131072.C015738.packed 128 cuts15738 = true := by
 decide +kernel
def pointBounds15738 : List (Nat × Nat × Nat) := [(2066782208,96898817254564,96899195702879),(2066847744,96899232627274,96899611075856)]
theorem point_links_checked15738 : (cuts15738.take 2).map (fun c => (2066743297-1+2*2^9*c.k,96898563666541+c.lower,96898942114690+c.upper)) = pointBounds15738 := by
 decide +kernel
def cuts15739 : List PrefixCut := [⟨38,251256811,251256975⟩,
⟨102,648218880,648219305⟩,
⟨128,816532530,816533064⟩]
theorem checked15739 : checkPrefixCuts (2^48) 2066874369 9 Manual.Count131072.C015739.packed 128 cuts15739 = true := by
 decide +kernel
def pointBounds15739 : List (Nat × Nat × Nat) := [(2066913280,96899650710374,96900029159230),(2066978816,96900047672443,96900426121560)]
theorem point_links_checked15739 : (cuts15739.take 2).map (fun c => (2066874369-1+2*2^9*c.k,96899399453563+c.lower,96899777902255+c.upper)) = pointBounds15739 := by
 decide +kernel
def cuts15740 : List PrefixCut := [⟨38,250015289,250015453⟩,
⟨102,666969343,666969776⟩,
⟨128,834863808,834864346⟩]
theorem checked15740 : checkPrefixCuts (2^48) 2067005441 9 Manual.Count131072.C015740.packed 128 cuts15740 = true := by
 decide +kernel
def pointBounds15740 : List (Nat × Nat × Nat) := [(2067044352,96900466001382,96900844450772),(2067109888,96900882955436,96901261405095)]
theorem point_links_checked15740 : (cuts15740.take 2).map (fun c => (2067005441-1+2*2^9*c.k,96900215986093+c.lower,96900594435319+c.upper)) = pointBounds15740 := by
 decide +kernel
def cuts15741 : List PrefixCut := [⟨38,247139990,247140154⟩,
⟨102,656714853,656715283⟩,
⟨128,829772686,829773226⟩]
theorem checked15741 : checkPrefixCuts (2^48) 2067136513 9 Manual.Count131072.C015741.packed 128 cuts15741 = true := by
 decide +kernel
def pointBounds15741 : List (Nat × Nat × Nat) := [(2067175424,96901297989891,96901676439819),(2067240960,96901707564754,96902086014948)]
theorem point_links_checked15741 : (cuts15741.take 2).map (fun c => (2067136513-1+2*2^9*c.k,96901050849901+c.lower,96901429299665+c.upper)) = pointBounds15741 := by
 decide +kernel
def cuts15742 : List PrefixCut := [⟨38,240452643,240452799⟩,
⟨102,657489991,657490419⟩,
⟨128,824682411,824682945⟩]
theorem checked15742 : checkPrefixCuts (2^48) 2067267585 9 Manual.Count131072.C015742.packed 128 cuts15742 = true := by
 decide +kernel
def pointBounds15742 : List (Nat × Nat × Nat) := [(2067306496,96902121075230,96902499525690),(2067372032,96902538112578,96902916563310)]
theorem point_links_checked15742 : (cuts15742.take 2).map (fun c => (2067267585-1+2*2^9*c.k,96901880622587+c.lower,96902259072891+c.upper)) = pointBounds15742 := by
 decide +kernel
def cuts15743 : List PrefixCut := [⟨38,241390421,241390578⟩,
⟨102,657584434,657584864⟩,
⟨128,824766226,824766765⟩]
theorem checked15743 : checkPrefixCuts (2^48) 2067398657 9 Manual.Count131072.C015743.packed 128 cuts15743 = true := by
 decide +kernel
def pointBounds15743 : List (Nat × Nat × Nat) := [(2067437568,96902946695419,96903325146414),(2067503104,96903362889432,96903741340700)]
theorem point_links_checked15743 : (cuts15743.take 2).map (fun c => (2067398657-1+2*2^9*c.k,96902705304998+c.lower,96903083755836+c.upper)) = pointBounds15743 := by
 decide +kernel
def cuts15744 : List PrefixCut := [⟨38,245731627,245731784⟩,
⟨102,662443875,662444301⟩,
⟨128,837102432,837102968⟩]
theorem checked15744 : checkPrefixCuts (2^48) 2067529729 9 Manual.Count131072.C015744.packed 128 cuts15744 = true := by
 decide +kernel
def pointBounds15744 : List (Nat × Nat × Nat) := [(2067568640,96903775802851,96904154254385),(2067634176,96904192515099,96904570966902)]
theorem point_links_checked15744 : (cuts15744.take 2).map (fun c => (2067529729-1+2*2^9*c.k,96903530071224+c.lower,96903908522601+c.upper)) = pointBounds15744 := by
 decide +kernel
def cuts15745 : List PrefixCut := [⟨38,245579907,245580065⟩,
⟨102,656820591,656821009⟩,
⟨128,824525737,824526265⟩]
theorem checked15745 : checkPrefixCuts (2^48) 2067660801 9 Manual.Count131072.C015745.packed 128 cuts15745 = true := by
 decide +kernel
def pointBounds15745 : List (Nat × Nat × Nat) := [(2067699712,96904612753563,96904991205634),(2067765248,96905023994247,96905402446578)]
theorem point_links_checked15745 : (cuts15745.take 2).map (fun c => (2067660801-1+2*2^9*c.k,96904367173656+c.lower,96904745625569+c.upper)) = pointBounds15745 := by
 decide +kernel
def cuts15746 : List PrefixCut := [⟨38,245292082,245292240⟩,
⟨102,655281592,655282012⟩,
⟨128,828284596,828285129⟩]
theorem checked15746 : checkPrefixCuts (2^48) 2067791873 9 Manual.Count131072.C015746.packed 128 cuts15746 = true := by
 decide +kernel
def pointBounds15746 : List (Nat × Nat × Nat) := [(2067830784,96905436991475,96905815444074),(2067896320,96905846980985,96906225433846)]
theorem point_links_checked15746 : (cuts15746.take 2).map (fun c => (2067791873-1+2*2^9*c.k,96905191699393+c.lower,96905570151834+c.upper)) = pointBounds15746 := by
 decide +kernel
def cuts15747 : List PrefixCut := [⟨38,251401679,251401844⟩,
⟨102,671573485,671573925⟩,
⟨128,835854655,835855201⟩]
theorem checked15747 : checkPrefixCuts (2^48) 2067922945 9 Manual.Count131072.C015747.packed 128 cuts15747 = true := by
 decide +kernel
def pointBounds15747 : List (Nat × Nat × Nat) := [(2067961856,96906271385668,96906649838807),(2068027392,96906691557474,96907070010888)]
theorem point_links_checked15747 : (cuts15747.take 2).map (fun c => (2067922945-1+2*2^9*c.k,96906019983989+c.lower,96906398436963+c.upper)) = pointBounds15747 := by
 decide +kernel
def cuts15748 : List PrefixCut := [⟨38,254924441,254924605⟩,
⟨102,664998077,664998511⟩,
⟨128,833624009,833624555⟩]
theorem checked15748 : checkPrefixCuts (2^48) 2068054017 9 Manual.Count131072.C015748.packed 128 cuts15748 = true := by
 decide +kernel
def pointBounds15748 : List (Nat × Nat × Nat) := [(2068092928,96907110763085,96907489216769),(2068158464,96907520836721,96907899290675)]
theorem point_links_checked15748 : (cuts15748.take 2).map (fun c => (2068054017-1+2*2^9*c.k,96906855838644+c.lower,96907234292164+c.upper)) = pointBounds15748 := by
 decide +kernel
def cuts15749 : List PrefixCut := [⟨38,240345988,240346145⟩,
⟨102,659920116,659920543⟩,
⟨128,826766195,826766730⟩]
theorem checked15749 : checkPrefixCuts (2^48) 2068185089 9 Manual.Count131072.C015749.packed 128 cuts15749 = true := by
 decide +kernel
def pointBounds15749 : List (Nat × Nat × Nat) := [(2068224000,96907929808641,96908308262864),(2068289536,96908349382769,96908727837262)]
theorem point_links_checked15749 : (cuts15749.take 2).map (fun c => (2068185089-1+2*2^9*c.k,96907689462653+c.lower,96908067916719+c.upper)) = pointBounds15749 := by
 decide +kernel
def cuts15750 : List PrefixCut := [⟨38,246590749,246590908⟩,
⟨102,666682654,666683084⟩,
⟨128,830524373,830524910⟩]
theorem checked15750 : checkPrefixCuts (2^48) 2068316161 9 Manual.Count131072.C015750.packed 128 cuts15750 = true := by
 decide +kernel
def pointBounds15750 : List (Nat × Nat × Nat) := [(2068355072,96908762819597,96909141274357),(2068420608,96909182911502,96909561366533)]
theorem point_links_checked15750 : (cuts15750.take 2).map (fun c => (2068316161-1+2*2^9*c.k,96908516228848+c.lower,96908894683449+c.upper)) = pointBounds15750 := by
 decide +kernel
def cuts15751 : List PrefixCut := [⟨38,241404115,241404272⟩,
⟨102,664871328,664871761⟩,
⟨128,835098091,835098632⟩]
theorem checked15751 : checkPrefixCuts (2^48) 2068447233 9 Manual.Count131072.C015751.packed 128 cuts15751 = true := by
 decide +kernel
def pointBounds15751 : List (Nat × Nat × Nat) := [(2068486144,96909588157336,96909966612631),(2068551680,96910011624549,96910390080120)]
theorem point_links_checked15751 : (cuts15751.take 2).map (fun c => (2068447233-1+2*2^9*c.k,96909346753221+c.lower,96909725208359+c.upper)) = pointBounds15751 := by
 decide +kernel
def cuts15752 : List PrefixCut := [⟨38,245062753,245062912⟩,
⟨102,653671775,653672198⟩,
⟨128,824295929,824296463⟩]
theorem checked15752 : checkPrefixCuts (2^48) 2068578305 9 Manual.Count131072.C015752.packed 128 cuts15752 = true := by
 decide +kernel
def pointBounds15752 : List (Nat × Nat × Nat) := [(2068617216,96910426914065,96910805369903),(2068682752,96910835523087,96911213979189)]
theorem point_links_checked15752 : (cuts15752.take 2).map (fun c => (2068578305-1+2*2^9*c.k,96910181851312+c.lower,96910560306991+c.upper)) = pointBounds15752 := by
 decide +kernel
def cuts15753 : List PrefixCut := [⟨38,250625755,250625915⟩,
⟨102,667236346,667236781⟩,
⟨128,828870014,828870556⟩]
theorem checked15753 : checkPrefixCuts (2^48) 2068709377 9 Manual.Count131072.C015753.packed 128 cuts15753 = true := by
 decide +kernel
def pointBounds15753 : List (Nat × Nat × Nat) := [(2068748288,96911256772996,96911635229369),(2068813824,96911673383587,96912051840235)]
theorem point_links_checked15753 : (cuts15753.take 2).map (fun c => (2068709377-1+2*2^9*c.k,96911006147241+c.lower,96911384603454+c.upper)) = pointBounds15753 := by
 decide +kernel
def cuts15754 : List PrefixCut := [⟨38,249521442,249521604⟩,
⟨102,664609079,664609511⟩,
⟨128,838612770,838613314⟩]
theorem checked15754 : checkPrefixCuts (2^48) 2068840449 9 Manual.Count131072.C015754.packed 128 cuts15754 = true := by
 decide +kernel
def pointBounds15754 : List (Nat × Nat × Nat) := [(2068879360,96912084538697,96912462995614),(2068944896,96912499626334,96912878083521)]
theorem point_links_checked15754 : (cuts15754.take 2).map (fun c => (2068840449-1+2*2^9*c.k,96911835017255+c.lower,96912213474010+c.upper)) = pointBounds15754 := by
 decide +kernel
def cuts15755 : List PrefixCut := [⟨38,251274212,251274378⟩,
⟨102,667423941,667424374⟩,
⟨128,839648104,839648650⟩]
theorem checked15755 : checkPrefixCuts (2^48) 2068971521 9 Manual.Count131072.C015755.packed 128 cuts15755 = true := by
 decide +kernel
def pointBounds15755 : List (Nat × Nat × Nat) := [(2069010432,96912924904237,96913303361702),(2069075968,96913341053966,96913719511698)]
theorem point_links_checked15755 : (cuts15755.take 2).map (fun c => (2068971521-1+2*2^9*c.k,96912673630025+c.lower,96913052087324+c.upper)) = pointBounds15755 := by
 decide +kernel
def cuts15756 : List PrefixCut := [⟨38,242960105,242960267⟩,
⟨102,664660821,664661257⟩,
⟨128,833337340,833337886⟩]
theorem checked15756 : checkPrefixCuts (2^48) 2069102593 9 Manual.Count131072.C015756.packed 128 cuts15756 = true := by
 decide +kernel
def pointBounds15756 : List (Nat × Nat × Nat) := [(2069141504,96913756238234,96914134696241),(2069207040,96914177938950,96914556397231)]
theorem point_links_checked15756 : (cuts15756.take 2).map (fun c => (2069102593-1+2*2^9*c.k,96913513278129+c.lower,96913891735974+c.upper)) = pointBounds15756 := by
 decide +kernel
def cuts15757 : List PrefixCut := [⟨38,249065958,249066122⟩,
⟨102,667203297,667203728⟩,
⟨128,836413193,836413736⟩]
theorem checked15757 : checkPrefixCuts (2^48) 2069233665 9 Manual.Count131072.C015757.packed 128 cuts15757 = true := by
 decide +kernel
def pointBounds15757 : List (Nat × Nat × Nat) := [(2069272576,96914595681427,96914974139982),(2069338112,96915013818766,96915392277588)]
theorem point_links_checked15757 : (cuts15757.take 2).map (fun c => (2069233665-1+2*2^9*c.k,96914346615469+c.lower,96914725073860+c.upper)) = pointBounds15757 := by
 decide +kernel
def cuts15758 : List PrefixCut := [⟨38,246465839,246466000⟩,
⟨102,658455997,658456415⟩,
⟨128,827519193,827519718⟩]
theorem checked15758 : checkPrefixCuts (2^48) 2069364737 9 Manual.Count131072.C015758.packed 128 cuts15758 = true := by
 decide +kernel
def pointBounds15758 : List (Nat × Nat × Nat) := [(2069403648,96915429494501,96915807953596),(2069469184,96915841484659,96916219944011)]
theorem point_links_checked15758 : (cuts15758.take 2).map (fun c => (2069364737-1+2*2^9*c.k,96915183028662+c.lower,96915561487596+c.upper)) = pointBounds15758 := by
 decide +kernel
def cuts15759 : List PrefixCut := [⟨38,250938547,250938706⟩,
⟨102,660318438,660318865⟩,
⟨128,824474760,824475298⟩]
theorem checked15759 : checkPrefixCuts (2^48) 2069495809 9 Manual.Count131072.C015759.packed 128 cuts15759 = true := by
 decide +kernel
def pointBounds15759 : List (Nat × Nat × Nat) := [(2069534720,96916261486402,96916639946020),(2069600256,96916670866293,96917049326179)]
theorem point_links_checked15759 : (cuts15759.take 2).map (fun c => (2069495809-1+2*2^9*c.k,96916010547855+c.lower,96916389007314+c.upper)) = pointBounds15759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000179
