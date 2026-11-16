import PlattAssemblyKernel
import PlattCertificates.Count131072.C012656
import PlattCertificates.Count131072.C012657
import PlattCertificates.Count131072.C012658
import PlattCertificates.Count131072.C012659
import PlattCertificates.Count131072.C012660
import PlattCertificates.Count131072.C012661
import PlattCertificates.Count131072.C012662
import PlattCertificates.Count131072.C012663
import PlattCertificates.Count131072.C012664
import PlattCertificates.Count131072.C012665
import PlattCertificates.Count131072.C012666
import PlattCertificates.Count131072.C012667
import PlattCertificates.Count131072.C012668
import PlattCertificates.Count131072.C012669
import PlattCertificates.Count131072.C012670
import PlattCertificates.Count131072.C012671
import PlattCertificates.Count131072.C012672
import PlattCertificates.Count131072.C012673
import PlattCertificates.Count131072.C012674
import PlattCertificates.Count131072.C012675
import PlattCertificates.Count131072.C012676
import PlattCertificates.Count131072.C012677
import PlattCertificates.Count131072.C012678
import PlattCertificates.Count131072.C012679
import PlattCertificates.Count131072.C012680
import PlattCertificates.Count131072.C012681
import PlattCertificates.Count131072.C012682
import PlattCertificates.Count131072.C012683
import PlattCertificates.Count131072.C012684
import PlattCertificates.Count131072.C012685
import PlattCertificates.Count131072.C012686
import PlattCertificates.Count131072.C012687
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000083
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12656 : List PrefixCut := [⟨47,381889552,381889835⟩,
⟨98,794744284,794744870⟩,
⟨128,1044075940,1044076711⟩]
theorem checked12656 : checkPrefixCuts (2^48) 1662779393 9 Manual.Count131072.C012656.packed 128 cuts12656 = true := by
 decide +kernel
def pointBounds12656 : List (Nat × Nat × Nat) := [(1662827520,94030409836482,94030786302333),(1662879744,94030822691214,94031199157368)]
theorem point_links_checked12656 : (cuts12656.take 2).map (fun c => (1662779393-1+2*2^9*c.k,94030027946930+c.lower,94030404412498+c.upper)) = pointBounds12656 := by
 decide +kernel
def cuts12657 : List PrefixCut := [⟨21,170450166,170450292⟩,
⟨72,583279088,583279522⟩,
⟨123,1001172768,1001173510⟩,
⟨128,1041285807,1041286579⟩]
theorem checked12657 : checkPrefixCuts (2^48) 1662910465 9 Manual.Count131072.C012657.packed 128 cuts12657 = true := by
 decide +kernel
def pointBounds12657 : List (Nat × Nat × Nat) := [(1662931968,94031242473036,94031618939501),(1662984192,94031655301958,94032031768731),(1663036416,94032073195638,94032449662719)]
theorem point_links_checked12657 : (cuts12657.take 3).map (fun c => (1662910465-1+2*2^9*c.k,94031072022870+c.lower,94031448489209+c.upper)) = pointBounds12657 := by
 decide +kernel
def cuts12658 : List PrefixCut := [⟨46,370658865,370659137⟩,
⟨97,778709972,778710545⟩,
⟨128,1042218725,1042219490⟩]
theorem checked12658 : checkPrefixCuts (2^48) 1663041537 9 Manual.Count131072.C012658.packed 128 cuts12658 = true := by
 decide +kernel
def pointBounds12658 : List (Nat × Nat × Nat) := [(1663088640,94032483967542,94032860434925),(1663140864,94032892018649,94033268486333)]
theorem point_links_checked12658 : (cuts12658.take 2).map (fun c => (1663041537-1+2*2^9*c.k,94032113308677+c.lower,94032489775788+c.upper)) = pointBounds12658 := by
 decide +kernel
def cuts12659 : List PrefixCut := [⟨20,164838481,164838602⟩,
⟨71,579633381,579633813⟩,
⟨122,996615312,996616050⟩,
⟨128,1043998786,1043999560⟩]
theorem checked12659 : checkPrefixCuts (2^48) 1663172609 9 Manual.Count131072.C012659.packed 128 cuts12659 = true := by
 decide +kernel
def pointBounds12659 : List (Nat × Nat × Nat) := [(1663193088,94033320365883,94033696833880),(1663245312,94033735160783,94034111629091),(1663297536,94034152142714,94034528611328)]
theorem point_links_checked12659 : (cuts12659.take 3).map (fun c => (1663172609-1+2*2^9*c.k,94033155527402+c.lower,94033531995278+c.upper)) = pointBounds12659 := by
 decide +kernel
def cuts12660 : List PrefixCut := [⟨45,356385793,356386055⟩,
⟨96,768941845,768942411⟩,
⟨128,1030717025,1030717785⟩]
theorem checked12660 : checkPrefixCuts (2^48) 1663303681 9 Manual.Count131072.C012660.packed 128 cuts12660 = true := by
 decide +kernel
def pointBounds12660 : List (Nat × Nat × Nat) := [(1663349760,94034555911981,94034932380893),(1663401984,94034968468033,94035344937249)]
theorem point_links_checked12660 : (cuts12660.take 2).map (fun c => (1663303681-1+2*2^9*c.k,94034199526188+c.lower,94034575994838+c.upper)) = pointBounds12660 := by
 decide +kernel
def cuts12661 : List PrefixCut := [⟨19,154490630,154490743⟩,
⟨70,577173235,577173656⟩,
⟨121,996289365,996290092⟩,
⟨128,1050433392,1050434159⟩]
theorem checked12661 : checkPrefixCuts (2^48) 1663434753 9 Manual.Count131072.C012661.packed 128 cuts12661 = true := by
 decide +kernel
def pointBounds12661 : List (Nat × Nat × Nat) := [(1663454208,94035384733843,94035761203366),(1663506432,94035807416448,94036183886279),(1663558656,94036226532578,94036603002715)]
theorem point_links_checked12661 : (cuts12661.take 3).map (fun c => (1663434753-1+2*2^9*c.k,94035230243213+c.lower,94035606712623+c.upper)) = pointBounds12661 := by
 decide +kernel
def cuts12662 : List PrefixCut := [⟨44,355314663,355314924⟩,
⟨95,770851442,770852011⟩,
⟨128,1046458855,1046459628⟩]
theorem checked12662 : checkPrefixCuts (2^48) 1663565825 9 Manual.Count131072.C012662.packed 128 cuts12662 = true := by
 decide +kernel
def pointBounds12662 : List (Nat × Nat × Nat) := [(1663610880,94036635991268,94037012461706),(1663663104,94037051528047,94037427998793)]
theorem point_links_checked12662 : (cuts12662.take 2).map (fun c => (1663565825-1+2*2^9*c.k,94036280676605+c.lower,94036657146782+c.upper)) = pointBounds12662 := by
 decide +kernel
def cuts12663 : List PrefixCut := [⟨18,144146015,144146122⟩,
⟨69,565408792,565409213⟩,
⟨120,973970197,973970921⟩,
⟨128,1043669670,1043670445⟩]
theorem checked12663 : checkPrefixCuts (2^48) 1663696897 9 Manual.Count131072.C012663.packed 128 cuts12663 = true := by
 decide +kernel
def pointBounds12663 : List (Nat × Nat × Nat) := [(1663715328,94037471281475,94037847752532),(1663767552,94037892544252,94038269015623),(1663819776,94038301105657,94038677577331)]
theorem point_links_checked12663 : (cuts12663.take 3).map (fun c => (1663696897-1+2*2^9*c.k,94037327135460+c.lower,94037703606410+c.upper)) = pointBounds12663 := by
 decide +kernel
def cuts12664 : List PrefixCut := [⟨43,357627115,357627376⟩,
⟨94,782741143,782741715⟩,
⟨128,1050692923,1050693695⟩]
theorem checked12664 : checkPrefixCuts (2^48) 1663827969 9 Manual.Count131072.C012664.packed 128 cuts12664 = true := by
 decide +kernel
def pointBounds12664 : List (Nat × Nat × Nat) := [(1663872000,94038728432245,94039104904231),(1663924224,94039153546273,94039530018570)]
theorem point_links_checked12664 : (cuts12664.take 2).map (fun c => (1663827969-1+2*2^9*c.k,94038370805130+c.lower,94038747276855+c.upper)) = pointBounds12664 := by
 decide +kernel
def cuts12665 : List PrefixCut := [⟨17,139894367,139894471⟩,
⟨68,550265134,550265544⟩,
⟨119,970264611,970265329⟩,
⟨128,1039276542,1039277309⟩]
theorem checked12665 : checkPrefixCuts (2^48) 1663959041 9 Manual.Count131072.C012665.packed 128 cuts12665 = true := by
 decide +kernel
def pointBounds12665 : List (Nat × Nat × Nat) := [(1663976448,94039561392420,94039937865021),(1664028672,94039971763187,94040348236094),(1664080896,94040391762664,94040768235879)]
theorem point_links_checked12665 : (cuts12665.take 3).map (fun c => (1663959041-1+2*2^9*c.k,94039421498053+c.lower,94039797970550+c.upper)) = pointBounds12665 := by
 decide +kernel
def cuts12666 : List PrefixCut := [⟨42,337781041,337781296⟩,
⟨93,754202147,754202709⟩,
⟨128,1036995724,1036996496⟩]
theorem checked12666 : checkPrefixCuts (2^48) 1664090113 9 Manual.Count131072.C012666.packed 128 cuts12666 = true := by
 decide +kernel
def pointBounds12666 : List (Nat × Nat × Nat) := [(1664133120,94040798555636,94041175029155),(1664185344,94041214976742,94041591450568)]
theorem point_links_checked12666 : (cuts12666.take 2).map (fun c => (1664090113-1+2*2^9*c.k,94040460774595+c.lower,94040837247859+c.upper)) = pointBounds12666 := by
 decide +kernel
def cuts12667 : List PrefixCut := [⟨16,130570100,130570196⟩,
⟨67,534787881,534788282⟩,
⟨118,948125630,948126337⟩,
⟨128,1026766570,1026767336⟩]
theorem checked12667 : checkPrefixCuts (2^48) 1664221185 9 Manual.Count131072.C012667.packed 128 cuts12667 = true := by
 decide +kernel
def pointBounds12667 : List (Nat × Nat × Nat) := [(1664237568,94041628340419,94042004814551),(1664289792,94042032558200,94042409032637),(1664342016,94042445895949,94042822370692)]
theorem point_links_checked12667 : (cuts12667.take 3).map (fun c => (1664221185-1+2*2^9*c.k,94041497770319+c.lower,94041874244355+c.upper)) = pointBounds12667 := by
 decide +kernel
def cuts12668 : List PrefixCut := [⟨41,339588184,339588433⟩,
⟨92,754929346,754929904⟩,
⟨128,1046133862,1046134637⟩]
theorem checked12668 : checkPrefixCuts (2^48) 1664352257 9 Manual.Count131072.C012668.packed 128 cuts12668 = true := by
 decide +kernel
def pointBounds12668 : List (Nat × Nat × Nat) := [(1664394240,94042864125073,94043240600124),(1664446464,94043279466235,94043655941595)]
theorem point_links_checked12668 : (cuts12668.take 2).map (fun c => (1664352257-1+2*2^9*c.k,94042524536889+c.lower,94042901011691+c.upper)) = pointBounds12668 := by
 decide +kernel
def cuts12669 : List PrefixCut := [⟨15,126321928,126322020⟩,
⟨66,535549359,535549754⟩,
⟨117,950344152,950344850⟩,
⟨128,1038611071,1038611834⟩]
theorem checked12669 : checkPrefixCuts (2^48) 1664483329 9 Manual.Count131072.C012669.packed 128 cuts12669 = true := by
 decide +kernel
def pointBounds12669 : List (Nat × Nat × Nat) := [(1664498688,94043696992679,94044073468348),(1664550912,94044106220110,94044482696082),(1664603136,94044521014903,94044897491178)]
theorem point_links_checked12669 : (cuts12669.take 3).map (fun c => (1664483329-1+2*2^9*c.k,94043570670751+c.lower,94043947146328+c.upper)) = pointBounds12669 := by
 decide +kernel
def cuts12670 : List PrefixCut := [⟨40,330573014,330573258⟩,
⟨91,750921557,750922111⟩,
⟨128,1051548925,1051549698⟩]
theorem checked12670 : checkPrefixCuts (2^48) 1664614401 9 Manual.Count131072.C012670.packed 128 cuts12670 = true := by
 decide +kernel
def pointBounds12670 : List (Nat × Nat × Nat) := [(1664655360,94044939854836,94045316331420),(1664707584,94045360203379,94045736680273)]
theorem point_links_checked12670 : (cuts12670.take 2).map (fun c => (1664614401-1+2*2^9*c.k,94044609281822+c.lower,94044985758162+c.upper)) = pointBounds12670 := by
 decide +kernel
def cuts12671 : List PrefixCut := [⟨14,113790240,113790324⟩,
⟨65,514837880,514838256⟩,
⟨116,931089304,931089989⟩,
⟨128,1034558392,1034559154⟩]
theorem checked12671 : checkPrefixCuts (2^48) 1664745473 9 Manual.Count131072.C012671.packed 128 cuts12671 = true := by
 decide +kernel
def pointBounds12671 : List (Nat × Nat × Nat) := [(1664759808,94045774620987,94046151098184),(1664812032,94046175668627,94046552146116),(1664864256,94046591920051,94046968397849)]
theorem point_links_checked12671 : (cuts12671.take 3).map (fun c => (1664745473-1+2*2^9*c.k,94045660830747+c.lower,94046037307860+c.upper)) = pointBounds12671 := by
 decide +kernel
def cuts12672 : List PrefixCut := [⟨39,319531929,319532165⟩,
⟨90,736433456,736433997⟩,
⟨128,1052735736,1052736511⟩]
theorem checked12672 : checkPrefixCuts (2^48) 1664876545 9 Manual.Count131072.C012672.packed 128 cuts12672 = true := by
 decide +kernel
def pointBounds12672 : List (Nat × Nat × Nat) := [(1664916480,94047014921068,94047391399179),(1664968704,94047431822595,94047808301011)]
theorem point_links_checked12672 : (cuts12672.take 2).map (fun c => (1664876545-1+2*2^9*c.k,94046695389139+c.lower,94047071867014+c.upper)) = pointBounds12672 := by
 decide +kernel
def cuts12673 : List PrefixCut := [⟨13,109377000,109377080⟩,
⟨64,525914130,525914511⟩,
⟨115,940409802,940410489⟩,
⟨128,1044200727,1044201491⟩]
theorem checked12673 : checkPrefixCuts (2^48) 1665007617 9 Manual.Count131072.C012673.packed 128 cuts12673 = true := by
 decide +kernel
def pointBounds12673 : List (Nat × Nat × Nat) := [(1665020928,94047857501875,94048233980605),(1665073152,94048274039005,94048650518036),(1665125376,94048688534677,94049065014014)]
theorem point_links_checked12673 : (cuts12673.take 3).map (fun c => (1665007617-1+2*2^9*c.k,94047748124875+c.lower,94048124603525+c.upper)) = pointBounds12673 := by
 decide +kernel
def cuts12674 : List PrefixCut := [⟨38,314072433,314072665⟩,
⟨89,725330390,725330925⟩,
⟨128,1045808578,1045809351⟩]
theorem checked12674 : checkPrefixCuts (2^48) 1665138689 9 Manual.Count131072.C012674.packed 128 cuts12674 = true := by
 decide +kernel
def pointBounds12674 : List (Nat × Nat × Nat) := [(1665177600,94049106398035,94049482877681),(1665229824,94049517655992,94049894135941)]
theorem point_links_checked12674 : (cuts12674.take 2).map (fun c => (1665138689-1+2*2^9*c.k,94048792325602+c.lower,94049168805016+c.upper)) = pointBounds12674 := by
 decide +kernel
def cuts12675 : List PrefixCut := [⟨12,98711170,98711245⟩,
⟨63,523296111,523296500⟩,
⟨114,938402771,938403468⟩,
⟨128,1059416802,1059417586⟩]
theorem checked12675 : checkPrefixCuts (2^48) 1665269761 9 Manual.Count131072.C012675.packed 128 cuts12675 = true := by
 decide +kernel
def pointBounds12675 : List (Nat × Nat × Nat) := [(1665282048,94049936845350,94050313325612),(1665334272,94050361430291,94050737910867),(1665386496,94050776536951,94051153017835)]
theorem point_links_checked12675 : (cuts12675.take 3).map (fun c => (1665269761-1+2*2^9*c.k,94049838134180+c.lower,94050214614367+c.upper)) = pointBounds12675 := by
 decide +kernel
def cuts12676 : List PrefixCut := [⟨37,294755802,294756021⟩,
⟨88,706456335,706456860⟩,
⟨128,1032968348,1032969117⟩]
theorem checked12676 : checkPrefixCuts (2^48) 1665400833 9 Manual.Count131072.C012676.packed 128 cuts12676 = true := by
 decide +kernel
def pointBounds12676 : List (Nat × Nat × Nat) := [(1665438720,94051192306784,94051568787974),(1665490944,94051604007317,94051980488813)]
theorem point_links_checked12676 : (cuts12676.take 2).map (fun c => (1665400833-1+2*2^9*c.k,94050897550982+c.lower,94051274031953+c.upper)) = pointBounds12676 := by
 decide +kernel
def cuts12677 : List PrefixCut := [⟨11,91597686,91597755⟩,
⟨62,522368952,522369337⟩,
⟨113,941973381,941974074⟩,
⟨128,1058743729,1058744509⟩]
theorem checked12677 : checkPrefixCuts (2^48) 1665531905 9 Manual.Count131072.C012677.packed 128 cuts12677 = true := by
 decide +kernel
def pointBounds12677 : List (Nat × Nat × Nat) := [(1665543168,94052022117016,94052398598825),(1665595392,94052452888282,94052829370407),(1665647616,94052872492711,94053248975144)]
theorem point_links_checked12677 : (cuts12677.take 3).map (fun c => (1665531905-1+2*2^9*c.k,94051930519330+c.lower,94052307001070+c.upper)) = pointBounds12677 := by
 decide +kernel
def cuts12678 : List PrefixCut := [⟨36,293526641,293526860⟩,
⟨87,721046825,721047353⟩,
⟨128,1062208443,1062209218⟩]
theorem checked12678 : checkPrefixCuts (2^48) 1665662977 9 Manual.Count131072.C012678.packed 128 cuts12678 = true := by
 decide +kernel
def pointBounds12678 : List (Nat × Nat × Nat) := [(1665699840,94053282789700,94053659272439),(1665752064,94053710309884,94054086792932)]
theorem point_links_checked12678 : (cuts12678.take 2).map (fun c => (1665662977-1+2*2^9*c.k,94052989263059+c.lower,94053365745579+c.upper)) = pointBounds12678 := by
 decide +kernel
def cuts12679 : List PrefixCut := [⟨10,80769039,80769097⟩,
⟨61,499307044,499307409⟩,
⟨112,906342230,906342899⟩,
⟨128,1040328245,1040329012⟩]
theorem checked12679 : checkPrefixCuts (2^48) 1665794049 9 Manual.Count131072.C012679.packed 128 cuts12679 = true := by
 decide +kernel
def pointBounds12679 : List (Nat × Nat × Nat) := [(1665804288,94054132240541,94054508723894),(1665856512,94054550778546,94054927262206),(1665908736,94054957813732,94055334297696)]
theorem point_links_checked12679 : (cuts12679.take 3).map (fun c => (1665794049-1+2*2^9*c.k,94054051471502+c.lower,94054427954797+c.upper)) = pointBounds12679 := by
 decide +kernel
def cuts12680 : List PrefixCut := [⟨35,282836178,282836384⟩,
⟨86,695759345,695759858⟩,
⟨128,1032981508,1032982270⟩]
theorem checked12680 : checkPrefixCuts (2^48) 1665925121 9 Manual.Count131072.C012680.packed 128 cuts12680 = true := by
 decide +kernel
def pointBounds12680 : List (Nat × Nat × Nat) := [(1665960960,94055374635925,94055751120193),(1666013184,94055787559092,94056164043667)]
theorem point_links_checked12680 : (cuts12680.take 2).map (fun c => (1665925121-1+2*2^9*c.k,94055091799747+c.lower,94055468283809+c.upper)) = pointBounds12680 := by
 decide +kernel
def cuts12681 : List PrefixCut := [⟨9,69605891,69605944⟩,
⟨60,489598788,489599149⟩,
⟨111,900624754,900625423⟩,
⟨128,1035434429,1035435198⟩]
theorem checked12681 : checkPrefixCuts (2^48) 1666056193 9 Manual.Count131072.C012681.packed 128 cuts12681 = true := by
 decide +kernel
def pointBounds12681 : List (Nat × Nat × Nat) := [(1666065408,94056194387146,94056570872023),(1666117632,94056614380043,94056990865228),(1666169856,94057025406009,94057401891502)]
theorem point_links_checked12681 : (cuts12681.take 3).map (fun c => (1666056193-1+2*2^9*c.k,94056124781255+c.lower,94056501266079+c.upper)) = pointBounds12681 := by
 decide +kernel
def cuts12682 : List PrefixCut := [⟨34,277554873,277555076⟩,
⟨85,699873173,699873691⟩,
⟨128,1054779260,1054780040⟩]
theorem checked12682 : checkPrefixCuts (2^48) 1666187265 9 Manual.Count131072.C012682.packed 128 cuts12682 = true := by
 decide +kernel
def pointBounds12682 : List (Nat × Nat × Nat) := [(1666222080,94057437770557,94057814256353),(1666274304,94057860088857,94058236574968)]
theorem point_links_checked12682 : (cuts12682.take 2).map (fun c => (1666187265-1+2*2^9*c.k,94057160215684+c.lower,94057536701277+c.upper)) = pointBounds12682 := by
 decide +kernel
def cuts12683 : List PrefixCut := [⟨8,65540885,65540932⟩,
⟨59,484623325,484623688⟩,
⟨110,890686476,890687136⟩,
⟨128,1036791803,1036792572⟩]
theorem checked12683 : checkPrefixCuts (2^48) 1666318337 9 Manual.Count131072.C012683.packed 128 cuts12683 = true := by
 decide +kernel
def pointBounds12683 : List (Nat × Nat × Nat) := [(1666326528,94058280535829,94058657022249),(1666378752,94058699618269,94059076105005),(1666430976,94059105681420,94059482168453)]
theorem point_links_checked12683 : (cuts12683.take 3).map (fun c => (1666318337-1+2*2^9*c.k,94058214994944+c.lower,94058591481317+c.upper)) = pointBounds12683 := by
 decide +kernel
def cuts12684 : List PrefixCut := [⟨33,271092874,271093078⟩,
⟨84,691318143,691318656⟩,
⟨128,1049208658,1049209437⟩]
theorem checked12684 : checkPrefixCuts (2^48) 1666449409 9 Manual.Count131072.C012684.packed 128 cuts12684 = true := by
 decide +kernel
def pointBounds12684 : List (Nat × Nat × Nat) := [(1666483200,94059522879621,94059899366967),(1666535424,94059943104890,94060319592545)]
theorem point_links_checked12684 : (cuts12684.take 2).map (fun c => (1666449409-1+2*2^9*c.k,94059251786747+c.lower,94059628273889+c.upper)) = pointBounds12684 := by
 decide +kernel
def cuts12685 : List PrefixCut := [⟨7,58774866,58774910⟩,
⟨58,477284983,477285328⟩,
⟨109,892066540,892067190⟩,
⟨128,1050477242,1050478010⟩]
theorem checked12685 : checkPrefixCuts (2^48) 1666580481 9 Manual.Count131072.C012685.packed 128 cuts12685 = true := by
 decide +kernel
def pointBounds12685 : List (Nat × Nat × Nat) := [(1666587648,94060359770271,94060736258236),(1666639872,94060778280388,94061154768654),(1666692096,94061193061945,94061569550516)]
theorem point_links_checked12685 : (cuts12685.take 3).map (fun c => (1666580481-1+2*2^9*c.k,94060300995405+c.lower,94060677483326+c.upper)) = pointBounds12685 := by
 decide +kernel
def cuts12686 : List PrefixCut := [⟨32,260748760,260748956⟩,
⟨83,665878472,665878971⟩,
⟨128,1034013855,1034014625⟩]
theorem checked12686 : checkPrefixCuts (2^48) 1666711553 9 Manual.Count131072.C012686.packed 128 cuts12686 = true := by
 decide +kernel
def pointBounds12686 : List (Nat × Nat × Nat) := [(1666744320,94061612221407,94061988710292),(1666796544,94062017351119,94062393840307)]
theorem point_links_checked12686 : (cuts12686.take 2).map (fun c => (1666711553-1+2*2^9*c.k,94061351472647+c.lower,94061727961336+c.upper)) = pointBounds12686 := by
 decide +kernel
def cuts12687 : List PrefixCut := [⟨6,46100629,46100664⟩,
⟨57,461336820,461337163⟩,
⟨108,869299129,869299774⟩,
⟨128,1035114618,1035115383⟩]
theorem checked12687 : checkPrefixCuts (2^48) 1666842625 9 Manual.Count131072.C012687.packed 128 cuts12687 = true := by
 decide +kernel
def pointBounds12687 : List (Nat × Nat × Nat) := [(1666848768,94062431587131,94062808076625),(1666900992,94062846823322,94063223313124),(1666953216,94063254785631,94063631275735)]
theorem point_links_checked12687 : (cuts12687.take 3).map (fun c => (1666842625-1+2*2^9*c.k,94062385486502+c.lower,94062761975961+c.upper)) = pointBounds12687 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000083
