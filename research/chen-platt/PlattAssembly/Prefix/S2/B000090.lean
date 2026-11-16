import PlattAssemblyKernel
import PlattCertificates.Count131072.C012880
import PlattCertificates.Count131072.C012881
import PlattCertificates.Count131072.C012882
import PlattCertificates.Count131072.C012883
import PlattCertificates.Count131072.C012884
import PlattCertificates.Count131072.C012885
import PlattCertificates.Count131072.C012886
import PlattCertificates.Count131072.C012887
import PlattCertificates.Count131072.C012888
import PlattCertificates.Count131072.C012889
import PlattCertificates.Count131072.C012890
import PlattCertificates.Count131072.C012891
import PlattCertificates.Count131072.C012892
import PlattCertificates.Count131072.C012893
import PlattCertificates.Count131072.C012894
import PlattCertificates.Count131072.C012895
import PlattCertificates.Count131072.C012896
import PlattCertificates.Count131072.C012897
import PlattCertificates.Count131072.C012898
import PlattCertificates.Count131072.C012899
import PlattCertificates.Count131072.C012900
import PlattCertificates.Count131072.C012901
import PlattCertificates.Count131072.C012902
import PlattCertificates.Count131072.C012903
import PlattCertificates.Count131072.C012904
import PlattCertificates.Count131072.C012905
import PlattCertificates.Count131072.C012906
import PlattCertificates.Count131072.C012907
import PlattCertificates.Count131072.C012908
import PlattCertificates.Count131072.C012909
import PlattCertificates.Count131072.C012910
import PlattCertificates.Count131072.C012911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12880 : List PrefixCut := [⟨22,168171247,168171370⟩,
⟨74,586843416,586843844⟩,
⟨126,993526485,993527212⟩,
⟨128,1009494147,1009494886⟩]
theorem checked12880 : checkPrefixCuts (2^48) 1692139521 9 Manual.Count131072.C012880.packed 128 cuts12880 = true := by
 decide +kernel
def pointBounds12880 : List (Nat × Nat × Nat) := [(1692162048,94262184212508,94262560848481),(1692215296,94262602884677,94262979520955),(1692268544,94263009567746,94263386204323)]
theorem point_links_checked12880 : (cuts12880.take 3).map (fun c => (1692139521-1+2*2^9*c.k,94262016041261+c.lower,94262392677111+c.upper)) = pointBounds12880 := by
 decide +kernel
def cuts12881 : List PrefixCut := [⟨50,403676030,403676320⟩,
⟨102,831290175,831290779⟩,
⟨128,1036360436,1036361194⟩]
theorem checked12881 : checkPrefixCuts (2^48) 1692270593 9 Manual.Count131072.C012881.packed 128 cuts12881 = true := by
 decide +kernel
def pointBounds12881 : List (Nat × Nat × Nat) := [(1692321792,94263429211438,94263805848317),(1692375040,94263856825583,94264233462776)]
theorem point_links_checked12881 : (cuts12881.take 2).map (fun c => (1692270593-1+2*2^9*c.k,94263025535408+c.lower,94263402171997+c.upper)) = pointBounds12881 := by
 decide +kernel
def cuts12882 : List PrefixCut := [⟨26,204900754,204900903⟩,
⟨78,628330143,628330598⟩,
⟨128,1029627586,1029628335⟩]
theorem checked12882 : checkPrefixCuts (2^48) 1692401665 9 Manual.Count131072.C012882.packed 128 cuts12882 = true := by
 decide +kernel
def pointBounds12882 : List (Nat × Nat × Nat) := [(1692428288,94264266796598,94264643434094),(1692481536,94264690225987,94265066863789)]
theorem point_links_checked12882 : (cuts12882.take 2).map (fun c => (1692401665-1+2*2^9*c.k,94264061895844+c.lower,94264438533191+c.upper)) = pointBounds12882 := by
 decide +kernel
def cuts12883 : List PrefixCut := [⟨2,15299954,15299965⟩,
⟨54,429556054,429556369⟩,
⟨106,851615057,851615681⟩,
⟨128,1019902730,1019903480⟩]
theorem checked12883 : checkPrefixCuts (2^48) 1692532737 9 Manual.Count131072.C012883.packed 128 cuts12883 = true := by
 decide +kernel
def pointBounds12883 : List (Nat × Nat × Nat) := [(1692534784,94265106823384,94265483461491),(1692588032,94265521079484,94265897717895),(1692641280,94265943138487,94266319777207)]
theorem point_links_checked12883 : (cuts12883.take 3).map (fun c => (1692532737-1+2*2^9*c.k,94265091523430+c.lower,94265468161526+c.upper)) = pointBounds12883 := by
 decide +kernel
def cuts12884 : List PrefixCut := [⟨30,246108575,246108755⟩,
⟨82,662487319,662487808⟩,
⟨128,1035620732,1035621496⟩]
theorem checked12884 : checkPrefixCuts (2^48) 1692663809 9 Manual.Count131072.C012884.packed 128 cuts12884 = true := by
 decide +kernel
def pointBounds12884 : List (Nat × Nat × Nat) := [(1692694528,94266357534735,94266734173761),(1692747776,94266773913479,94267150552814)]
theorem point_links_checked12884 : (cuts12884.take 2).map (fun c => (1692663809-1+2*2^9*c.k,94266111426160+c.lower,94266488065006+c.upper)) = pointBounds12884 := by
 decide +kernel
def cuts12885 : List PrefixCut := [⟨6,50548481,50548518⟩,
⟨58,468896276,468896610⟩,
⟨110,885069400,885070039⟩,
⟨128,1028390894,1028391637⟩]
theorem checked12885 : checkPrefixCuts (2^48) 1692794881 9 Manual.Count131072.C012885.packed 128 cuts12885 = true := by
 decide +kernel
def pointBounds12885 : List (Nat × Nat × Nat) := [(1692801024,94267197595373,94267574235020),(1692854272,94267615943168,94267992583112),(1692907520,94268032116292,94268408756541)]
theorem point_links_checked12885 : (cuts12885.take 3).map (fun c => (1692794881-1+2*2^9*c.k,94267147046892+c.lower,94267523686502+c.upper)) = pointBounds12885 := by
 decide +kernel
def cuts12886 : List PrefixCut := [⟨34,273337382,273337578⟩,
⟨86,690814475,690814976⟩,
⟨128,1024321097,1024321843⟩]
theorem checked12886 : checkPrefixCuts (2^48) 1692925953 9 Manual.Count131072.C012886.packed 128 cuts12886 = true := by
 decide +kernel
def pointBounds12886 : List (Nat × Nat × Nat) := [(1692960768,94268448775168,94268825415717),(1693014016,94268866252261,94269242893115)]
theorem point_links_checked12886 : (cuts12886.take 2).map (fun c => (1692925953-1+2*2^9*c.k,94268175437786+c.lower,94268552078139+c.upper)) = pointBounds12886 := by
 decide +kernel
def cuts12887 : List PrefixCut := [⟨10,82460957,82461016⟩,
⟨62,502405443,502405805⟩,
⟨114,919011876,919012543⟩,
⟨128,1030725341,1030726091⟩]
theorem checked12887 : checkPrefixCuts (2^48) 1693057025 9 Manual.Count131072.C012887.packed 128 cuts12887 = true := by
 decide +kernel
def pointBounds12887 : List (Nat × Nat × Nat) := [(1693067264,94269282219840,94269658860998),(1693120512,94269702164326,94270078805787),(1693173760,94270118770759,94270495412525)]
theorem point_links_checked12887 : (cuts12887.take 3).map (fun c => (1693057025-1+2*2^9*c.k,94269199758883+c.lower,94269576399982+c.upper)) = pointBounds12887 := by
 decide +kernel
def cuts12888 : List PrefixCut := [⟨38,305046149,305046371⟩,
⟨90,710322506,710323025⟩,
⟨128,1017180547,1017181289⟩]
theorem checked12888 : checkPrefixCuts (2^48) 1693188097 9 Manual.Count131072.C012888.packed 128 cuts12888 = true := by
 decide +kernel
def pointBounds12888 : List (Nat × Nat × Nat) := [(1693227008,94270535530373,94270912172444),(1693280256,94270940806730,94271317449098)]
theorem point_links_checked12888 : (cuts12888.take 2).map (fun c => (1693188097-1+2*2^9*c.k,94270230484224+c.lower,94270607126073+c.upper)) = pointBounds12888 := by
 decide +kernel
def cuts12889 : List PrefixCut := [⟨14,114695939,114696025⟩,
⟨66,530917548,530917939⟩,
⟨118,949951882,949952586⟩,
⟨128,1027573986,1027574747⟩]
theorem checked12889 : checkPrefixCuts (2^48) 1693319169 9 Manual.Count131072.C012889.packed 128 cuts12889 = true := by
 decide +kernel
def pointBounds12889 : List (Nat × Nat × Nat) := [(1693333504,94271362360710,94271739003387),(1693386752,94271778582319,94272155225301),(1693440000,94272197616653,94272574259948)]
theorem point_links_checked12889 : (cuts12889.take 3).map (fun c => (1693319169-1+2*2^9*c.k,94271247664771+c.lower,94271624307362+c.upper)) = pointBounds12889 := by
 decide +kernel
def cuts12890 : List PrefixCut := [⟨42,341897584,341897835⟩,
⟨94,757415149,757415705⟩,
⟨128,1032314442,1032315197⟩]
theorem checked12890 : checkPrefixCuts (2^48) 1693450241 9 Manual.Count131072.C012890.packed 128 cuts12890 = true := by
 decide +kernel
def pointBounds12890 : List (Nat × Nat × Nat) := [(1693493248,94272617136341,94272993779944),(1693546496,94273032653906,94273409297814)]
theorem point_links_checked12890 : (cuts12890.take 2).map (fun c => (1693450241-1+2*2^9*c.k,94272275238757+c.lower,94272651882109+c.upper)) = pointBounds12890 := by
 decide +kernel
def cuts12891 : List PrefixCut := [⟨18,143929273,143929376⟩,
⟨70,554933415,554933821⟩,
⟨122,977557912,977558629⟩,
⟨128,1023425915,1023426666⟩]
theorem checked12891 : checkPrefixCuts (2^48) 1693581313 9 Manual.Count131072.C012891.packed 128 cuts12891 = true := by
 decide +kernel
def pointBounds12891 : List (Nat × Nat × Nat) := [(1693599744,94273451482472,94273828126682),(1693652992,94273862486614,94274239131127),(1693706240,94274285111111,94274661755935)]
theorem point_links_checked12891 : (cuts12891.take 3).map (fun c => (1693581313-1+2*2^9*c.k,94273307553199+c.lower,94273684197306+c.upper)) = pointBounds12891 := by
 decide +kernel
def cuts12892 : List PrefixCut := [⟨46,358795111,358795371⟩,
⟨98,781891583,781892153⟩,
⟨128,1022847871,1022848617⟩]
theorem checked12892 : checkPrefixCuts (2^48) 1693712385 9 Manual.Count131072.C012892.packed 128 cuts12892 = true := by
 decide +kernel
def pointBounds12892 : List (Nat × Nat × Nat) := [(1693759488,94274689774225,94275066419343),(1693812736,94275112870697,94275489516125)]
theorem point_links_checked12892 : (cuts12892.take 2).map (fun c => (1693712385-1+2*2^9*c.k,94274330979114+c.lower,94274707623972+c.upper)) = pointBounds12892 := by
 decide +kernel
def cuts12893 : List PrefixCut := [⟨22,177806299,177806428⟩,
⟨74,592235315,592235748⟩,
⟨126,1000004786,1000005516⟩,
⟨128,1016288711,1016289452⟩]
theorem checked12893 : checkPrefixCuts (2^48) 1693843457 9 Manual.Count131072.C012893.packed 128 cuts12893 = true := by
 decide +kernel
def pointBounds12893 : List (Nat × Nat × Nat) := [(1693865984,94275531633284,94275908279017),(1693919232,94275946062300,94276322708337),(1693972480,94276353831771,94276730478105)]
theorem point_links_checked12893 : (cuts12893.take 3).map (fun c => (1693843457-1+2*2^9*c.k,94275353826985+c.lower,94275730472589+c.upper)) = pointBounds12893 := by
 decide +kernel
def cuts12894 : List PrefixCut := [⟨50,402605434,402605725⟩,
⟨102,816829315,816829912⟩,
⟨128,1027176293,1027177045⟩]
theorem checked12894 : checkPrefixCuts (2^48) 1693974529 9 Manual.Count131072.C012894.packed 128 cuts12894 = true := by
 decide +kernel
def pointBounds12894 : List (Nat × Nat × Nat) := [(1694025728,94276772721130,94277149367766),(1694078976,94277186945011,94277563591953)]
theorem point_links_checked12894 : (cuts12894.take 2).map (fun c => (1693974529-1+2*2^9*c.k,94276370115696+c.lower,94276746762041+c.upper)) = pointBounds12894 := by
 decide +kernel
def cuts12895 : List PrefixCut := [⟨26,201371650,201371799⟩,
⟨78,618061583,618062033⟩,
⟨128,1020118480,1020119217⟩]
theorem checked12895 : checkPrefixCuts (2^48) 1694105601 9 Manual.Count131072.C012895.packed 128 cuts12895 = true := by
 decide +kernel
def pointBounds12895 : List (Nat × Nat × Nat) := [(1694132224,94277598663639,94277975310885),(1694185472,94278015353572,94278392001119)]
theorem point_links_checked12895 : (cuts12895.take 2).map (fun c => (1694105601-1+2*2^9*c.k,94277397291989+c.lower,94277773939086+c.upper)) = pointBounds12895 := by
 decide +kernel
def cuts12896 : List PrefixCut := [⟨2,17610478,17610492⟩,
⟨54,435437130,435437449⟩,
⟨106,848599130,848599750⟩,
⟨128,1026020555,1026021305⟩]
theorem checked12896 : checkPrefixCuts (2^48) 1694236673 9 Manual.Count131072.C012896.packed 128 cuts12896 = true := by
 decide +kernel
def pointBounds12896 : List (Nat × Nat × Nat) := [(1694238720,94278435020947,94278811668795),(1694291968,94278852847599,94279229495752),(1694345216,94279266009599,94279642658053)]
theorem point_links_checked12896 : (cuts12896.take 3).map (fun c => (1694236673-1+2*2^9*c.k,94278417410469+c.lower,94278794058303+c.upper)) = pointBounds12896 := by
 decide +kernel
def cuts12897 : List PrefixCut := [⟨30,238219402,238219571⟩,
⟨82,647036224,647036689⟩,
⟨128,1021123409,1021124147⟩]
theorem checked12897 : checkPrefixCuts (2^48) 1694367745 9 Manual.Count131072.C012897.packed 128 cuts12897 = true := by
 decide +kernel
def pointBounds12897 : List (Nat × Nat × Nat) := [(1694398464,94279681650426,94280058299179),(1694451712,94280090467248,94280467116297)]
theorem point_links_checked12897 : (cuts12897.take 2).map (fun c => (1694367745-1+2*2^9*c.k,94279443431024+c.lower,94279820079608+c.upper)) = pointBounds12897 := by
 decide +kernel
def cuts12898 : List PrefixCut := [⟨6,49002655,49002690⟩,
⟨58,462278888,462279223⟩,
⟨110,876704723,876705355⟩,
⟨128,1019217693,1019218430⟩]
theorem checked12898 : checkPrefixCuts (2^48) 1694498817 9 Manual.Count131072.C012898.packed 128 cuts12898 = true := by
 decide +kernel
def pointBounds12898 : List (Nat × Nat × Nat) := [(1694504960,94280513557088,94280890206445),(1694558208,94280926833321,94281303482978),(1694611456,94281341259156,94281717909110)]
theorem point_links_checked12898 : (cuts12898.take 3).map (fun c => (1694498817-1+2*2^9*c.k,94280464554433+c.lower,94280841203755+c.upper)) = pointBounds12898 := by
 decide +kernel
def cuts12899 : List PrefixCut := [⟨34,273726923,273727120⟩,
⟨86,691946882,691947381⟩,
⟨128,1024952086,1024952826⟩]
theorem checked12899 : checkPrefixCuts (2^48) 1694629889 9 Manual.Count131072.C012899.packed 128 cuts12899 = true := by
 decide +kernel
def pointBounds12899 : List (Nat × Nat × Nat) := [(1694664704,94281757499049,94282134149305),(1694717952,94282175719008,94282552369566)]
theorem point_links_checked12899 : (cuts12899.take 2).map (fun c => (1694629889-1+2*2^9*c.k,94281483772126+c.lower,94281860422185+c.upper)) = pointBounds12899 := by
 decide +kernel
def cuts12900 : List PrefixCut := [⟨10,81215461,81215520⟩,
⟨62,495921499,495921857⟩,
⟨114,908123260,908123921⟩,
⟨128,1020222644,1020223389⟩]
theorem checked12900 : checkPrefixCuts (2^48) 1694760961 9 Manual.Count131072.C012900.packed 128 cuts12900 = true := by
 decide +kernel
def pointBounds12900 : List (Nat × Nat × Nat) := [(1694771200,94282589939673,94282966590531),(1694824448,94283004645711,94283381296868),(1694877696,94283416847472,94283793498932)]
theorem point_links_checked12900 : (cuts12900.take 3).map (fun c => (1694760961-1+2*2^9*c.k,94282508724212+c.lower,94282885375011+c.upper)) = pointBounds12900 := by
 decide +kernel
def cuts12901 : List PrefixCut := [⟨38,303743014,303743233⟩,
⟨90,714258307,714258828⟩,
⟨128,1018815079,1018815820⟩]
theorem checked12901 : checkPrefixCuts (2^48) 1694892033 9 Manual.Count131072.C012901.packed 128 cuts12901 = true := by
 decide +kernel
def pointBounds12901 : List (Nat × Nat × Nat) := [(1694930944,94283832689870,94284209341633),(1694984192,94284243205163,94284619857228)]
theorem point_links_checked12901 : (cuts12901.take 2).map (fun c => (1694892033-1+2*2^9*c.k,94283528946856+c.lower,94283905598400+c.upper)) = pointBounds12901 := by
 decide +kernel
def cuts12902 : List PrefixCut := [⟨14,111259468,111259552⟩,
⟨66,539849072,539849467⟩,
⟨118,949163343,949164036⟩,
⟨128,1029696272,1029697022⟩]
theorem checked12902 : checkPrefixCuts (2^48) 1695023105 9 Manual.Count131072.C012902.packed 128 cuts12902 = true := by
 decide +kernel
def pointBounds12902 : List (Nat × Nat × Nat) := [(1695037440,94284659021403,94285035673772),(1695090688,94285087611007,94285464263687),(1695143936,94285496925278,94285873578256)]
theorem point_links_checked12902 : (cuts12902.take 3).map (fun c => (1695023105-1+2*2^9*c.k,94284547761935+c.lower,94284924414220+c.upper)) = pointBounds12902 := by
 decide +kernel
def cuts12903 : List PrefixCut := [⟨42,326443726,326443967⟩,
⟨94,740381371,740381912⟩,
⟨128,1008030847,1008031585⟩]
theorem checked12903 : checkPrefixCuts (2^48) 1695154177 9 Manual.Count131072.C012903.packed 128 cuts12903 = true := by
 decide +kernel
def pointBounds12903 : List (Nat × Nat × Nat) := [(1695197184,94285903901933,94286280555209),(1695250432,94286317839578,94286694493154)]
theorem point_links_checked12903 : (cuts12903.take 2).map (fun c => (1695154177-1+2*2^9*c.k,94285577458207+c.lower,94285954111242+c.upper)) = pointBounds12903 := by
 decide +kernel
def cuts12904 : List PrefixCut := [⟨18,144614768,144614875⟩,
⟨70,555869882,555870286⟩,
⟨122,973753121,973753827⟩,
⟨128,1022397388,1022398129⟩]
theorem checked12904 : checkPrefixCuts (2^48) 1695285249 9 Manual.Count131072.C012904.packed 128 cuts12904 = true := by
 decide +kernel
def pointBounds12904 : List (Nat × Nat × Nat) := [(1695303680,94286730103822,94287106757702),(1695356928,94287141358936,94287518013113),(1695410176,94287559242175,94287935896654)]
theorem point_links_checked12904 : (cuts12904.take 3).map (fun c => (1695285249-1+2*2^9*c.k,94286585489054+c.lower,94286962142827+c.upper)) = pointBounds12904 := by
 decide +kernel
def cuts12905 : List PrefixCut := [⟨46,374870409,374870682⟩,
⟨98,790901152,790901730⟩,
⟨128,1027299052,1027299805⟩]
theorem checked12905 : checkPrefixCuts (2^48) 1695416321 9 Manual.Count131072.C012905.packed 128 cuts12905 = true := by
 decide +kernel
def pointBounds12905 : List (Nat × Nat × Nat) := [(1695463424,94287982756851,94288359411638),(1695516672,94288398787594,94288775442686)]
theorem point_links_checked12905 : (cuts12905.take 2).map (fun c => (1695416321-1+2*2^9*c.k,94287607886442+c.lower,94287984540956+c.upper)) = pointBounds12905 := by
 decide +kernel
def cuts12906 : List PrefixCut := [⟨22,177129664,177129790⟩,
⟨74,588154276,588154696⟩,
⟨126,1003315833,1003316558⟩,
⟨128,1020247377,1020248114⟩]
theorem checked12906 : checkPrefixCuts (2^48) 1695547393 9 Manual.Count131072.C012906.packed 128 cuts12906 = true := by
 decide +kernel
def pointBounds12906 : List (Nat × Nat × Nat) := [(1695569920,94288812315158,94289188970551),(1695623168,94289223339770,94289599995457),(1695676416,94289638501327,94290015157319)]
theorem point_links_checked12906 : (cuts12906.take 3).map (fun c => (1695547393-1+2*2^9*c.k,94288635185494+c.lower,94289011840761+c.upper)) = pointBounds12906 := by
 decide +kernel
def cuts12907 : List PrefixCut := [⟨50,404026771,404027068⟩,
⟨102,825469827,825470430⟩,
⟨128,1039423056,1039423816⟩]
theorem checked12907 : checkPrefixCuts (2^48) 1695678465 9 Manual.Count131072.C012907.packed 128 cuts12907 = true := by
 decide +kernel
def pointBounds12907 : List (Nat × Nat × Nat) := [(1695729664,94290059459642,94290436115943),(1695782912,94290480902698,94290857559305)]
theorem point_links_checked12907 : (cuts12907.take 2).map (fun c => (1695678465-1+2*2^9*c.k,94289655432871+c.lower,94290032088875+c.upper)) = pointBounds12907 := by
 decide +kernel
def cuts12908 : List PrefixCut := [⟨26,211128247,211128397⟩,
⟨78,627897478,627897932⟩,
⟨128,1025401044,1025401789⟩]
theorem checked12908 : checkPrefixCuts (2^48) 1695809537 9 Manual.Count131072.C012908.packed 128 cuts12908 = true := by
 decide +kernel
def pointBounds12908 : List (Nat × Nat × Nat) := [(1695836160,94290905984174,94291282641088),(1695889408,94291322753405,94291699410623)]
theorem point_links_checked12908 : (cuts12908.take 2).map (fun c => (1695809537-1+2*2^9*c.k,94290694855927+c.lower,94291071512691+c.upper)) = pointBounds12908 := by
 decide +kernel
def cuts12909 : List PrefixCut := [⟨2,17260846,17260859⟩,
⟨54,420560552,420560862⟩,
⟨106,837124530,837125146⟩,
⟨128,1012542173,1012542915⟩]
theorem checked12909 : checkPrefixCuts (2^48) 1695940609 9 Manual.Count131072.C012909.packed 128 cuts12909 = true := by
 decide +kernel
def pointBounds12909 : List (Nat × Nat × Nat) := [(1695942656,94291737517817,94292114175339),(1695995904,94292140817523,94292517475342),(1696049152,94292557381501,94292934039626)]
theorem point_links_checked12909 : (cuts12909.take 3).map (fun c => (1695940609-1+2*2^9*c.k,94291720256971+c.lower,94292096914480+c.upper)) = pointBounds12909 := by
 decide +kernel
def cuts12910 : List PrefixCut := [⟨30,248269380,248269555⟩,
⟨82,659164869,659165343⟩,
⟨128,1031880447,1031881188⟩]
theorem checked12910 : checkPrefixCuts (2^48) 1696071681 9 Manual.Count131072.C012910.packed 128 cuts12910 = true := by
 decide +kernel
def pointBounds12910 : List (Nat × Nat × Nat) := [(1696102400,94292981068524,94293357726950),(1696155648,94293391964013,94293768622738)]
theorem point_links_checked12910 : (cuts12910.take 2).map (fun c => (1696071681-1+2*2^9*c.k,94292732799144+c.lower,94293109457395+c.upper)) = pointBounds12910 := by
 decide +kernel
def cuts12911 : List PrefixCut := [⟨6,47128041,47128076⟩,
⟨58,464801340,464801680⟩,
⟨110,889430736,889431384⟩,
⟨128,1034455475,1034456231⟩]
theorem checked12911 : checkPrefixCuts (2^48) 1696202753 9 Manual.Count131072.C012911.packed 128 cuts12911 = true := by
 decide +kernel
def pointBounds12911 : List (Nat × Nat × Nat) := [(1696208896,94293811807632,94294188466659),(1696262144,94294229480931,94294606140263),(1696315392,94294654110327,94295030769967)]
theorem point_links_checked12911 : (cuts12911.take 3).map (fun c => (1696202753-1+2*2^9*c.k,94293764679591+c.lower,94294141338583+c.upper)) = pointBounds12911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000090
