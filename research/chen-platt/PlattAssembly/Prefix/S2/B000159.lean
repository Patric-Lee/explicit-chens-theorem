import PlattAssemblyKernel
import PlattCertificates.Count131072.C015088
import PlattCertificates.Count131072.C015089
import PlattCertificates.Count131072.C015090
import PlattCertificates.Count131072.C015091
import PlattCertificates.Count131072.C015092
import PlattCertificates.Count131072.C015093
import PlattCertificates.Count131072.C015094
import PlattCertificates.Count131072.C015095
import PlattCertificates.Count131072.C015096
import PlattCertificates.Count131072.C015097
import PlattCertificates.Count131072.C015098
import PlattCertificates.Count131072.C015099
import PlattCertificates.Count131072.C015100
import PlattCertificates.Count131072.C015101
import PlattCertificates.Count131072.C015102
import PlattCertificates.Count131072.C015103
import PlattCertificates.Count131072.C015104
import PlattCertificates.Count131072.C015105
import PlattCertificates.Count131072.C015106
import PlattCertificates.Count131072.C015107
import PlattCertificates.Count131072.C015108
import PlattCertificates.Count131072.C015109
import PlattCertificates.Count131072.C015110
import PlattCertificates.Count131072.C015111
import PlattCertificates.Count131072.C015112
import PlattCertificates.Count131072.C015113
import PlattCertificates.Count131072.C015114
import PlattCertificates.Count131072.C015115
import PlattCertificates.Count131072.C015116
import PlattCertificates.Count131072.C015117
import PlattCertificates.Count131072.C015118
import PlattCertificates.Count131072.C015119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15088 : List PrefixCut := [⟨41,281678352,281678540⟩,
⟨102,701130780,701131248⟩,
⟨128,875981586,875982171⟩]
theorem checked15088 : checkPrefixCuts (2^48) 1981546497 9 Manual.Count131072.C015088.packed 128 cuts15088 = true := by
 decide +kernel
def pointBounds15088 : List (Nat × Nat × Nat) := [(1981588480,96345852179143,96346230264266),(1981650944,96346271631571,96346649716974)]
theorem point_links_checked15088 : (cuts15088.take 2).map (fun c => (1981546497-1+2*2^9*c.k,96345570500791+c.lower,96345948585726+c.upper)) = pointBounds15088 := by
 decide +kernel
def cuts15089 : List PrefixCut := [⟨35,239333021,239333179⟩,
⟨96,658048847,658049289⟩,
⟨128,871804743,871805330⟩]
theorem checked15089 : checkPrefixCuts (2^48) 1981677569 9 Manual.Count131072.C015089.packed 128 cuts15089 = true := by
 decide +kernel
def pointBounds15089 : List (Nat × Nat × Nat) := [(1981713408,96346685815398,96347063901076),(1981775872,96347104531224,96347482617186)]
theorem point_links_checked15089 : (cuts15089.take 2).map (fun c => (1981677569-1+2*2^9*c.k,96346446482377+c.lower,96346824567897+c.upper)) = pointBounds15089 := by
 decide +kernel
def cuts15090 : List PrefixCut := [⟨29,200117766,200117905⟩,
⟨90,612274120,612274527⟩,
⟨128,871747008,871747587⟩]
theorem checked15090 : checkPrefixCuts (2^48) 1981808641 9 Manual.Count131072.C015090.packed 128 cuts15090 = true := by
 decide +kernel
def pointBounds15090 : List (Nat × Nat × Nat) := [(1981838336,96347518404886,96347896491132),(1981900800,96347930561240,96348308647754)]
theorem point_links_checked15090 : (cuts15090.take 2).map (fun c => (1981808641-1+2*2^9*c.k,96347318287120+c.lower,96347696373227+c.upper)) = pointBounds15090 := by
 decide +kernel
def cuts15091 : List PrefixCut := [⟨23,160055441,160055548⟩,
⟨84,571759799,571760180⟩,
⟨128,870127286,870127866⟩]
theorem checked15091 : checkPrefixCuts (2^48) 1981939713 9 Manual.Count131072.C015091.packed 128 cuts15091 = true := by
 decide +kernel
def pointBounds15091 : List (Nat × Nat × Nat) := [(1981963264,96348350089569,96348728176362),(1982025728,96348761793927,96349139880994)]
theorem point_links_checked15091 : (cuts15091.take 2).map (fun c => (1981939713-1+2*2^9*c.k,96348190034128+c.lower,96348568120814+c.upper)) = pointBounds15091 := by
 decide +kernel
def cuts15092 : List PrefixCut := [⟨17,118010200,118010280⟩,
⟨78,531676680,531677036⟩,
⟨128,868649739,868650317⟩]
theorem checked15092 : checkPrefixCuts (2^48) 1982070785 9 Manual.Count131072.C015092.packed 128 cuts15092 = true := by
 decide +kernel
def pointBounds15092 : List (Nat × Nat × Nat) := [(1982088192,96349178171614,96349556258960),(1982150656,96349591838094,96349969925716)]
theorem point_links_checked15092 : (cuts15092.take 2).map (fun c => (1982070785-1+2*2^9*c.k,96349060161414+c.lower,96349438248680+c.upper)) = pointBounds15092 := by
 decide +kernel
def cuts15093 : List PrefixCut := [⟨11,67166342,67166388⟩,
⟨72,480380643,480380961⟩,
⟨128,864473791,864474363⟩]
theorem checked15093 : checkPrefixCuts (2^48) 1982201857 9 Manual.Count131072.C015093.packed 128 cuts15093 = true := by
 decide +kernel
def pointBounds15093 : List (Nat × Nat × Nat) := [(1982213120,96349995977495,96350374065385),(1982275584,96350409191796,96350787279958)]
theorem point_links_checked15093 : (cuts15093.take 2).map (fun c => (1982201857-1+2*2^9*c.k,96349928811153+c.lower,96350306898997+c.upper)) = pointBounds15093 := by
 decide +kernel
def cuts15094 : List PrefixCut := [⟨5,32800049,32800071⟩,
⟨66,443148515,443148807⟩,
⟨127,861861306,861861878⟩,
⟨128,868392495,868393072⟩]
theorem checked15094 : checkPrefixCuts (2^48) 1982332929 9 Manual.Count131072.C015094.packed 128 cuts15094 = true := by
 decide +kernel
def pointBounds15094 : List (Nat × Nat × Nat) := [(1982338048,96350826084993,96351204173431),(1982400512,96351236433459,96351614522167),(1982462976,96351655146250,96352033235238)]
theorem point_links_checked15094 : (cuts15094.take 3).map (fun c => (1982332929-1+2*2^9*c.k,96350793284944+c.lower,96351171373360+c.upper)) = pointBounds15094 := by
 decide +kernel
def cuts15095 : List PrefixCut := [⟨60,405495228,405495504⟩,
⟨121,816798830,816799382⟩,
⟨128,861804340,861804923⟩]
theorem checked15095 : checkPrefixCuts (2^48) 1982464001 9 Manual.Count131072.C015095.packed 128 cuts15095 = true := by
 decide +kernel
def pointBounds15095 : List (Nat × Nat × Nat) := [(1982525440,96352067172667,96352445261936),(1982587904,96352478476269,96352856565814)]
theorem point_links_checked15095 : (cuts15095.take 2).map (fun c => (1982464001-1+2*2^9*c.k,96351661677439+c.lower,96352039766432+c.upper)) = pointBounds15095 := by
 decide +kernel
def cuts15096 : List PrefixCut := [⟨54,363303750,363303997⟩,
⟨115,781821800,781822319⟩,
⟨128,869413619,869414197⟩]
theorem checked15096 : checkPrefixCuts (2^48) 1982595073 9 Manual.Count131072.C015096.packed 128 cuts15096 = true := by
 decide +kernel
def pointBounds15096 : List (Nat × Nat × Nat) := [(1982650368,96352886785529,96353264875352),(1982712832,96353305303579,96353683393674)]
theorem point_links_checked15096 : (cuts15096.take 2).map (fun c => (1982595073-1+2*2^9*c.k,96352523481779+c.lower,96352901571355+c.upper)) = pointBounds15096 := by
 decide +kernel
def cuts15097 : List PrefixCut := [⟨48,320265839,320266049⟩,
⟨109,737763772,737764261⟩,
⟨128,866516858,866517434⟩]
theorem checked15097 : checkPrefixCuts (2^48) 1982726145 9 Manual.Count131072.C015097.packed 128 cuts15097 = true := by
 decide +kernel
def pointBounds15097 : List (Nat × Nat × Nat) := [(1982775296,96353713161237,96354091251601),(1982837760,96354130659170,96354508749813)]
theorem point_links_checked15097 : (cuts15097.take 2).map (fun c => (1982726145-1+2*2^9*c.k,96353392895398+c.lower,96353770985552+c.upper)) = pointBounds15097 := by
 decide +kernel
def cuts15098 : List PrefixCut := [⟨42,288305816,288306007⟩,
⟨103,695415205,695415669⟩,
⟨128,867027569,867028147⟩]
theorem checked15098 : checkPrefixCuts (2^48) 1982857217 9 Manual.Count131072.C015098.packed 128 cuts15098 = true := by
 decide +kernel
def pointBounds15098 : List (Nat × Nat × Nat) := [(1982900224,96354547718072,96354925808993),(1982962688,96354954827461,96355332918655)]
theorem point_links_checked15098 : (cuts15098.take 2).map (fun c => (1982857217-1+2*2^9*c.k,96354259412256+c.lower,96354637502986+c.upper)) = pointBounds15098 := by
 decide +kernel
def cuts15099 : List PrefixCut := [⟨36,249678560,249678726⟩,
⟨97,663717263,663717702⟩,
⟨128,876054367,876054945⟩]
theorem checked15099 : checkPrefixCuts (2^48) 1982988289 9 Manual.Count131072.C015099.packed 128 cuts15099 = true := by
 decide +kernel
def pointBounds15099 : List (Nat × Nat × Nat) := [(1983025152,96355376118385,96355754209859),(1983087616,96355790157088,96356168248835)]
theorem point_links_checked15099 : (cuts15099.take 2).map (fun c => (1982988289-1+2*2^9*c.k,96355126439825+c.lower,96355504531133+c.upper)) = pointBounds15099 := by
 decide +kernel
def cuts15100 : List PrefixCut := [⟨30,201262867,201263006⟩,
⟨91,613430472,613430884⟩,
⟨128,859106789,859107363⟩]
theorem checked15100 : checkPrefixCuts (2^48) 1983119361 9 Manual.Count131072.C015100.packed 128 cuts15100 = true := by
 decide +kernel
def pointBounds15100 : List (Nat × Nat × Nat) := [(1983150080,96356203757059,96356581849084),(1983212544,96356615924664,96356994016962)]
theorem point_links_checked15100 : (cuts15100.take 2).map (fun c => (1983119361-1+2*2^9*c.k,96356002494192+c.lower,96356380586078+c.upper)) = pointBounds15100 := by
 decide +kernel
def cuts15101 : List PrefixCut := [⟨24,162362387,162362498⟩,
⟨85,576065211,576065597⟩,
⟨128,867423348,867423928⟩]
theorem checked15101 : checkPrefixCuts (2^48) 1983250433 9 Manual.Count131072.C015101.packed 128 cuts15101 = true := by
 decide +kernel
def pointBounds15101 : List (Nat × Nat × Nat) := [(1983275008,96357023963368,96357402055939),(1983337472,96357437666192,96357815759038)]
theorem point_links_checked15101 : (cuts15101.take 2).map (fun c => (1983250433-1+2*2^9*c.k,96356861600981+c.lower,96357239693441+c.upper)) = pointBounds15101 := by
 decide +kernel
def cuts15102 : List PrefixCut := [⟨18,122331592,122331672⟩,
⟨79,545090753,545091110⟩,
⟨128,878151393,878151966⟩]
theorem checked15102 : checkPrefixCuts (2^48) 1983381505 9 Manual.Count131072.C015102.packed 128 cuts15102 = true := by
 decide +kernel
def pointBounds15102 : List (Nat × Nat × Nat) := [(1983399936,96357851355921,96358229449041),(1983462400,96358274115082,96358652208479)]
theorem point_links_checked15102 : (cuts15102.take 2).map (fun c => (1983381505-1+2*2^9*c.k,96357729024329+c.lower,96358107117369+c.upper)) = pointBounds15102 := by
 decide +kernel
def cuts15103 : List PrefixCut := [⟨12,84434573,84434631⟩,
⟨73,491273742,491274064⟩,
⟨128,872133036,872133613⟩]
theorem checked15103 : checkPrefixCuts (2^48) 1983512577 9 Manual.Count131072.C015103.packed 128 cuts15103 = true := by
 decide +kernel
def pointBounds15103 : List (Nat × Nat × Nat) := [(1983524864,96358691610295,96359069703966),(1983587328,96359098449464,96359476543399)]
theorem point_links_checked15103 : (cuts15103.take 2).map (fun c => (1983512577-1+2*2^9*c.k,96358607175722+c.lower,96358985269335+c.upper)) = pointBounds15103 := by
 decide +kernel
def cuts15104 : List PrefixCut := [⟨6,37886680,37886706⟩,
⟨67,449524793,449525093⟩,
⟨128,855899910,855900476⟩]
theorem checked15104 : checkPrefixCuts (2^48) 1983643649 9 Manual.Count131072.C015104.packed 128 cuts15104 = true := by
 decide +kernel
def pointBounds15104 : List (Nat × Nat × Nat) := [(1983649792,96359517195438,96359895289654),(1983712256,96359928833551,96360306928041),(1983774720,96360335208668,96360713303424)]
theorem point_links_checked15104 : (cuts15104.take 3).map (fun c => (1983643649-1+2*2^9*c.k,96359479308758+c.lower,96359857402948+c.upper)) = pointBounds15104 := by
 decide +kernel
def cuts15105 : List PrefixCut := [⟨61,418138846,418139121⟩,
⟨122,825197779,825198326⟩,
⟨128,866200917,866201491⟩]
theorem checked15105 : checkPrefixCuts (2^48) 1983774721 9 Manual.Count131072.C015105.packed 128 cuts15105 = true := by
 decide +kernel
def pointBounds15105 : List (Nat × Nat × Nat) := [(1983837184,96360753347514,96361131442545),(1983899648,96361160406447,96361538501750)]
theorem point_links_checked15105 : (cuts15105.take 2).map (fun c => (1983774721-1+2*2^9*c.k,96360335208668+c.lower,96360713303424+c.upper)) = pointBounds15105 := by
 decide +kernel
def cuts15106 : List PrefixCut := [⟨55,369731809,369732051⟩,
⟨116,792371192,792371710⟩,
⟨128,874797792,874798365⟩]
theorem checked15106 : checkPrefixCuts (2^48) 1983905793 9 Manual.Count131072.C015106.packed 128 cuts15106 = true := by
 decide +kernel
def pointBounds15106 : List (Nat × Nat × Nat) := [(1983962112,96361571141394,96361949236966),(1984024576,96361993780777,96362371876625)]
theorem point_links_checked15106 : (cuts15106.take 2).map (fun c => (1983905793-1+2*2^9*c.k,96361201409585+c.lower,96361579504915+c.upper)) = pointBounds15106 := by
 decide +kernel
def cuts15107 : List PrefixCut := [⟨49,333531680,333531896⟩,
⟨110,757704879,757705383⟩,
⟨128,876868176,876868760⟩]
theorem checked15107 : checkPrefixCuts (2^48) 1984036865 9 Manual.Count131072.C015107.packed 128 cuts15107 = true := by
 decide +kernel
def pointBounds15107 : List (Nat × Nat × Nat) := [(1984087040,96362409739057,96362787835176),(1984149504,96362833912256,96363212008663)]
theorem point_links_checked15107 : (cuts15107.take 2).map (fun c => (1984036865-1+2*2^9*c.k,96362076207377+c.lower,96362454303280+c.upper)) = pointBounds15107 := by
 decide +kernel
def cuts15108 : List PrefixCut := [⟨43,298187309,298187503⟩,
⟨104,718220132,718220601⟩,
⟨128,877236122,877236697⟩]
theorem checked15108 : checkPrefixCuts (2^48) 1984167937 9 Manual.Count131072.C015108.packed 128 cuts15108 = true := by
 decide +kernel
def pointBounds15108 : List (Nat × Nat × Nat) := [(1984211968,96363251262862,96363629359543),(1984274432,96363671295685,96364049392641)]
theorem point_links_checked15108 : (cuts15108.take 2).map (fun c => (1984167937-1+2*2^9*c.k,96362953075553+c.lower,96363331172040+c.upper)) = pointBounds15108 := by
 decide +kernel
def cuts15109 : List PrefixCut := [⟨37,251925054,251925223⟩,
⟨98,660016267,660016710⟩,
⟨128,865830113,865830694⟩]
theorem checked15109 : checkPrefixCuts (2^48) 1984299009 9 Manual.Count131072.C015109.packed 128 cuts15109 = true := by
 decide +kernel
def pointBounds15109 : List (Nat × Nat × Nat) := [(1984336896,96364082236729,96364460333960),(1984399360,96364490327942,96364868425447)]
theorem point_links_checked15109 : (cuts15109.take 2).map (fun c => (1984299009-1+2*2^9*c.k,96363830311675+c.lower,96364208408737+c.upper)) = pointBounds15109 := by
 decide +kernel
def cuts15110 : List PrefixCut := [⟨31,212193432,212193570⟩,
⟨92,626074274,626074686⟩,
⟨128,870595452,870596024⟩]
theorem checked15110 : checkPrefixCuts (2^48) 1984430081 9 Manual.Count131072.C015110.packed 128 cuts15110 = true := by
 decide +kernel
def pointBounds15110 : List (Nat × Nat × Nat) := [(1984461824,96364908335220,96365286433001),(1984524288,96365322216062,96365700314117)]
theorem point_links_checked15110 : (cuts15110.take 2).map (fun c => (1984430081-1+2*2^9*c.k,96364696141788+c.lower,96365074239431+c.upper)) = pointBounds15110 := by
 decide +kernel
def cuts15111 : List PrefixCut := [⟨25,173176121,173176232⟩,
⟨86,586889038,586889419⟩,
⟨128,874650893,874651463⟩]
theorem checked15111 : checkPrefixCuts (2^48) 1984561153 9 Manual.Count131072.C015111.packed 128 cuts15111 = true := by
 decide +kernel
def pointBounds15111 : List (Nat × Nat × Nat) := [(1984586752,96365739913361,96366118011687),(1984649216,96366153626278,96366531724874)]
theorem point_links_checked15111 : (cuts15111.take 2).map (fun c => (1984561153-1+2*2^9*c.k,96365566737240+c.lower,96365944835455+c.upper)) = pointBounds15111 := by
 decide +kernel
def cuts15112 : List PrefixCut := [⟨19,128916415,128916499⟩,
⟨80,546716097,546716463⟩,
⟨128,872607764,872608349⟩]
theorem checked15112 : checkPrefixCuts (2^48) 1984692225 9 Manual.Count131072.C015112.packed 128 cuts15112 = true := by
 decide +kernel
def pointBounds15112 : List (Nat × Nat × Nat) := [(1984711680,96366570304548,96366948403417),(1984774144,96366988104230,96367366203381)]
theorem point_links_checked15112 : (cuts15112.take 2).map (fun c => (1984692225-1+2*2^9*c.k,96366441388133+c.lower,96366819486918+c.upper)) = pointBounds15112 := by
 decide +kernel
def cuts15113 : List PrefixCut := [⟨13,88207749,88207807⟩,
⟨74,498748852,498749189⟩,
⟨128,854540438,854541010⟩]
theorem checked15113 : checkPrefixCuts (2^48) 1984823297 9 Manual.Count131072.C015113.packed 128 cuts15113 = true := by
 decide +kernel
def pointBounds15113 : List (Nat × Nat × Nat) := [(1984836608,96367402203646,96367780303074),(1984899072,96367812744749,96368190844456)]
theorem point_links_checked15113 : (cuts15113.take 2).map (fun c => (1984823297-1+2*2^9*c.k,96367313995897+c.lower,96367692095267+c.upper)) = pointBounds15113 := by
 decide +kernel
def cuts15114 : List PrefixCut := [⟨7,49205971,49206004⟩,
⟨68,457594185,457594495⟩,
⟨128,866253237,866253819⟩]
theorem checked15114 : checkPrefixCuts (2^48) 1984954369 9 Manual.Count131072.C015114.packed 128 cuts15114 = true := by
 decide +kernel
def pointBounds15114 : List (Nat × Nat × Nat) := [(1984961536,96368217742306,96368595842281),(1985024000,96368626130520,96369004230772)]
theorem point_links_checked15114 : (cuts15114.take 2).map (fun c => (1984954369-1+2*2^9*c.k,96368168536335+c.lower,96368546636277+c.upper)) = pointBounds15114 := by
 decide +kernel
def cuts15115 : List PrefixCut := [⟨1,7231535,7231540⟩,
⟨62,421832997,421833275⟩,
⟨123,838973533,838974090⟩,
⟨128,870308162,870308742⟩]
theorem checked15115 : checkPrefixCuts (2^48) 1985085441 9 Manual.Count131072.C015115.packed 128 cuts15115 = true := by
 decide +kernel
def pointBounds15115 : List (Nat × Nat × Nat) := [(1985086464,96369042021107,96369420121636),(1985148928,96369456622569,96369834723371),(1985211392,96369873763105,96370251864186)]
theorem point_links_checked15115 : (cuts15115.take 3).map (fun c => (1985085441-1+2*2^9*c.k,96369034789572+c.lower,96369412890096+c.upper)) = pointBounds15115 := by
 decide +kernel
def cuts15116 : List PrefixCut := [⟨56,381113833,381114088⟩,
⟨117,792698734,792699261⟩,
⟨128,864721219,864721793⟩]
theorem checked15116 : checkPrefixCuts (2^48) 1985216513 9 Manual.Count131072.C015116.packed 128 cuts15116 = true := by
 decide +kernel
def pointBounds15116 : List (Nat × Nat × Nat) := [(1985273856,96370286211567,96370664312926),(1985336320,96370697796468,96371075898099)]
theorem point_links_checked15116 : (cuts15116.take 2).map (fun c => (1985216513-1+2*2^9*c.k,96369905097734+c.lower,96370283198838+c.upper)) = pointBounds15116 := by
 decide +kernel
def cuts15117 : List PrefixCut := [⟨50,341534324,341534551⟩,
⟨111,751250339,751250838⟩,
⟨128,867216066,867216643⟩]
theorem checked15117 : checkPrefixCuts (2^48) 1985347585 9 Manual.Count131072.C015117.packed 128 cuts15117 = true := by
 decide +kernel
def pointBounds15117 : List (Nat × Nat × Nat) := [(1985398784,96371111353277,96371489455182),(1985461248,96371521069292,96371899171469)]
theorem point_links_checked15117 : (cuts15117.take 2).map (fun c => (1985347585-1+2*2^9*c.k,96370769818953+c.lower,96371147920631+c.upper)) = pointBounds15117 := by
 decide +kernel
def cuts15118 : List PrefixCut := [⟨44,298132133,298132333⟩,
⟨105,712500467,712500941⟩,
⟨128,869285081,869285658⟩]
theorem checked15118 : checkPrefixCuts (2^48) 1985478657 9 Manual.Count131072.C015118.packed 128 cuts15118 = true := by
 decide +kernel
def pointBounds15118 : List (Nat × Nat × Nat) := [(1985523712,96371935167152,96372313269607),(1985586176,96372349535486,96372727638215)]
theorem point_links_checked15118 : (cuts15118.take 2).map (fun c => (1985478657-1+2*2^9*c.k,96371637035019+c.lower,96372015137274+c.upper)) = pointBounds15118 := by
 decide +kernel
def cuts15119 : List PrefixCut := [⟨38,254877300,254877469⟩,
⟨99,659580399,659580834⟩,
⟨128,865258376,865258945⟩]
theorem checked15119 : checkPrefixCuts (2^48) 1985609729 9 Manual.Count131072.C015119.packed 128 cuts15119 = true := by
 decide +kernel
def pointBounds15119 : List (Nat × Nat × Nat) := [(1985648640,96372761197400,96373139300401),(1985711104,96373165900499,96373544003766)]
theorem point_links_checked15119 : (cuts15119.take 2).map (fun c => (1985609729-1+2*2^9*c.k,96372506320100+c.lower,96372884422932+c.upper)) = pointBounds15119 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000159
