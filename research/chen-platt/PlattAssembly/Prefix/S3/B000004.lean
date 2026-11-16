import PlattAssemblyKernel
import PlattCertificates.Count131072.C020128
import PlattCertificates.Count131072.C020129
import PlattCertificates.Count131072.C020130
import PlattCertificates.Count131072.C020131
import PlattCertificates.Count131072.C020132
import PlattCertificates.Count131072.C020133
import PlattCertificates.Count131072.C020134
import PlattCertificates.Count131072.C020135
import PlattCertificates.Count131072.C020136
import PlattCertificates.Count131072.C020137
import PlattCertificates.Count131072.C020138
import PlattCertificates.Count131072.C020139
import PlattCertificates.Count131072.C020140
import PlattCertificates.Count131072.C020141
import PlattCertificates.Count131072.C020142
import PlattCertificates.Count131072.C020143
import PlattCertificates.Count131072.C020144
import PlattCertificates.Count131072.C020145
import PlattCertificates.Count131072.C020146
import PlattCertificates.Count131072.C020147
import PlattCertificates.Count131072.C020148
import PlattCertificates.Count131072.C020149
import PlattCertificates.Count131072.C020150
import PlattCertificates.Count131072.C020151
import PlattCertificates.Count131072.C020152
import PlattCertificates.Count131072.C020153
import PlattCertificates.Count131072.C020154
import PlattCertificates.Count131072.C020155
import PlattCertificates.Count131072.C020156
import PlattCertificates.Count131072.C020157
import PlattCertificates.Count131072.C020158
import PlattCertificates.Count131072.C020159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20128 : List PrefixCut := [⟨71,363484032,363484237⟩,
⟨128,647275762,647276139⟩]
theorem checked20128 : checkPrefixCuts (2^48) 2642149377 9 Manual.Count131072.C020128.packed 128 cuts20128 = true := by
 decide +kernel
def pointBounds20128 : List (Nat × Nat × Nat) := [(2642222080,100103858750168,100104239168590)]
theorem point_links_checked20128 : (cuts20128.take 1).map (fun c => (2642149377-1+2*2^9*c.k,100103495266136+c.lower,100103875684353+c.upper)) = pointBounds20128 := by
 decide +kernel
def cuts20129 : List PrefixCut := [⟨24,125701576,125701647⟩,
⟨105,528151432,528151745⟩,
⟨128,645113078,645113459⟩]
theorem checked20129 : checkPrefixCuts (2^48) 2642280449 9 Manual.Count131072.C020129.packed 128 cuts20129 = true := by
 decide +kernel
def pointBounds20129 : List (Nat × Nat × Nat) := [(2642305024,100104268243474,100104648662139),(2642387968,100104670693330,100105051112237)]
theorem point_links_checked20129 : (cuts20129.take 2).map (fun c => (2642280449-1+2*2^9*c.k,100104142541898+c.lower,100104522960492+c.upper)) = pointBounds20129 := by
 decide +kernel
def cuts20130 : List PrefixCut := [⟨58,283877891,283878066⟩,
⟨128,643270107,643270491⟩]
theorem checked20130 : checkPrefixCuts (2^48) 2642411521 9 Manual.Count131072.C020130.packed 128 cuts20130 = true := by
 decide +kernel
def pointBounds20130 : List (Nat × Nat × Nat) := [(2642470912,100105071532867,100105451952017)]
theorem point_links_checked20130 : (cuts20130.take 1).map (fun c => (2642411521-1+2*2^9*c.k,100104787654976+c.lower,100105168073951+c.upper)) = pointBounds20130 := by
 decide +kernel
def cuts20131 : List PrefixCut := [⟨11,55495078,55495109⟩,
⟨92,461848156,461848424⟩,
⟨128,644196940,644197318⟩]
theorem checked20131 : checkPrefixCuts (2^48) 2642542593 9 Manual.Count131072.C020131.packed 128 cuts20131 = true := by
 decide +kernel
def pointBounds20131 : List (Nat × Nat × Nat) := [(2642553856,100105486420161,100105866839551),(2642636800,100105892773239,100106273192866)]
theorem point_links_checked20131 : (cuts20131.take 2).map (fun c => (2642542593-1+2*2^9*c.k,100105430925083+c.lower,100105811344442+c.upper)) = pointBounds20131 := by
 decide +kernel
def cuts20132 : List PrefixCut := [⟨45,223885042,223885177⟩,
⟨126,630212617,630212991⟩,
⟨128,640117691,640118071⟩]
theorem checked20132 : checkPrefixCuts (2^48) 2642673665 9 Manual.Count131072.C020132.packed 128 cuts20132 = true := by
 decide +kernel
def pointBounds20132 : List (Nat × Nat × Nat) := [(2642719744,100106299007065,100106679426937),(2642802688,100106705334640,100107085754751)]
theorem point_links_checked20132 : (cuts20132.take 2).map (fun c => (2642673665-1+2*2^9*c.k,100106075122023+c.lower,100106455541760+c.upper)) = pointBounds20132 := by
 decide +kernel
def cuts20133 : List PrefixCut := [⟨79,391617089,391617323⟩,
⟨128,639766418,639766799⟩]
theorem checked20133 : checkPrefixCuts (2^48) 2642804737 9 Manual.Count131072.C020133.packed 128 cuts20133 = true := by
 decide +kernel
def pointBounds20133 : List (Nat × Nat × Nat) := [(2642885632,100107106856803,100107487277154)]
theorem point_links_checked20133 : (cuts20133.take 1).map (fun c => (2642804737-1+2*2^9*c.k,100106715239714+c.lower,100107095659831+c.upper)) = pointBounds20133 := by
 decide +kernel
def cuts20134 : List PrefixCut := [⟨32,159643806,159643901⟩,
⟨113,565826750,565827082⟩,
⟨128,641545314,641545691⟩]
theorem checked20134 : checkPrefixCuts (2^48) 2642935809 9 Manual.Count131072.C020134.packed 128 cuts20134 = true := by
 decide +kernel
def pointBounds20134 : List (Nat × Nat × Nat) := [(2642968576,100107514649938,100107895070531),(2643051520,100107920832882,100108301253712)]
theorem point_links_checked20134 : (cuts20134.take 2).map (fun c => (2642935809-1+2*2^9*c.k,100107355006132+c.lower,100107735426630+c.upper)) = pointBounds20134 := by
 decide +kernel
def cuts20135 : List PrefixCut := [⟨66,333326849,333327046⟩,
⟨128,645347145,645347525⟩]
theorem checked20135 : checkPrefixCuts (2^48) 2643066881 9 Manual.Count131072.C020135.packed 128 cuts20135 = true := by
 decide +kernel
def pointBounds20135 : List (Nat × Nat × Nat) := [(2643134464,100108329878295,100108710299367)]
theorem point_links_checked20135 : (cuts20135.take 1).map (fun c => (2643066881-1+2*2^9*c.k,100107996551446+c.lower,100108376972321+c.upper)) = pointBounds20135 := by
 decide +kernel
def cuts20136 : List PrefixCut := [⟨19,98716130,98716188⟩,
⟨100,502198530,502198823⟩,
⟨128,643078949,643079321⟩]
theorem checked20136 : checkPrefixCuts (2^48) 2643197953 9 Manual.Count131072.C020136.packed 128 cuts20136 = true := by
 decide +kernel
def pointBounds20136 : List (Nat × Nat × Nat) := [(2643217408,100108740614721,100109121036034),(2643300352,100109144097121,100109524518669)]
theorem point_links_checked20136 : (cuts20136.take 2).map (fun c => (2643197953-1+2*2^9*c.k,100108641898591+c.lower,100109022319846+c.upper)) = pointBounds20136 := by
 decide +kernel
def cuts20137 : List PrefixCut := [⟨53,264506025,264506181⟩,
⟨128,641982106,641982482⟩]
theorem checked20137 : checkPrefixCuts (2^48) 2643329025 9 Manual.Count131072.C020137.packed 128 cuts20137 = true := by
 decide +kernel
def pointBounds20137 : List (Nat × Nat × Nat) := [(2643383296,100109549483565,100109929905348)]
theorem point_links_checked20137 : (cuts20137.take 1).map (fun c => (2643329025-1+2*2^9*c.k,100109284977540+c.lower,100109665399167+c.upper)) = pointBounds20137 := by
 decide +kernel
def cuts20138 : List PrefixCut := [⟨6,32050360,32050377⟩,
⟨87,437943812,437944061⟩,
⟨128,647700124,647700494⟩]
theorem checked20138 : checkPrefixCuts (2^48) 2643460097 9 Manual.Count131072.C020138.packed 128 cuts20138 = true := by
 decide +kernel
def pointBounds20138 : List (Nat × Nat × Nat) := [(2643466240,100109959010006,100110339432026),(2643549184,100110364903458,100110745325710)]
theorem point_links_checked20138 : (cuts20138.take 2).map (fun c => (2643460097-1+2*2^9*c.k,100109926959646+c.lower,100110307381649+c.upper)) = pointBounds20138 := by
 decide +kernel
def cuts20139 : List PrefixCut := [⟨40,198147377,198147494⟩,
⟨121,606677123,606677475⟩,
⟨128,644367256,644367632⟩]
theorem checked20139 : checkPrefixCuts (2^48) 2643591169 9 Manual.Count131072.C020139.packed 128 cuts20139 = true := by
 decide +kernel
def pointBounds20139 : List (Nat × Nat × Nat) := [(2643632128,100110772807147,100111153229637),(2643715072,100111181336893,100111561759618)]
theorem point_links_checked20139 : (cuts20139.take 2).map (fun c => (2643591169-1+2*2^9*c.k,100110574659770+c.lower,100110955082143+c.upper)) = pointBounds20139 := by
 decide +kernel
def cuts20140 : List PrefixCut := [⟨74,367206943,367207157⟩,
⟨128,639331497,639331870⟩]
theorem checked20140 : checkPrefixCuts (2^48) 2643722241 9 Manual.Count131072.C020140.packed 128 cuts20140 = true := by
 decide +kernel
def pointBounds20140 : List (Nat × Nat × Nat) := [(2643798016,100111586233969,100111966656932)]
theorem point_links_checked20140 : (cuts20140.take 1).map (fun c => (2643722241-1+2*2^9*c.k,100111219027026+c.lower,100111599449775+c.upper)) = pointBounds20140 := by
 decide +kernel
def cuts20141 : List PrefixCut := [⟨27,129352946,129353022⟩,
⟨108,537950636,537950950⟩,
⟨128,637809199,637809570⟩]
theorem checked20141 : checkPrefixCuts (2^48) 2643853313 9 Manual.Count131072.C020141.packed 128 cuts20141 = true := by
 decide +kernel
def pointBounds20141 : List (Nat × Nat × Nat) := [(2643880960,100111987711469,100112368134667),(2643963904,100112396309159,100112776732595)]
theorem point_links_checked20141 : (cuts20141.take 2).map (fun c => (2643853313-1+2*2^9*c.k,100111858358523+c.lower,100112238781645+c.upper)) = pointBounds20141 := by
 decide +kernel
def cuts20142 : List PrefixCut := [⟨61,303296999,303297178⟩,
⟨128,640119724,640120102⟩]
theorem checked20142 : checkPrefixCuts (2^48) 2643984385 9 Manual.Count131072.C020142.packed 128 cuts20142 = true := by
 decide +kernel
def pointBounds20142 : List (Nat × Nat × Nat) := [(2644046848,100112799464721,100113179888393)]
theorem point_links_checked20142 : (cuts20142.take 1).map (fun c => (2643984385-1+2*2^9*c.k,100112496167722+c.lower,100112876591215+c.upper)) = pointBounds20142 := by
 decide +kernel
def cuts20143 : List PrefixCut := [⟨14,67810587,67810627⟩,
⟨95,473389252,473389526⟩,
⟨128,642962085,642962457⟩]
theorem checked20143 : checkPrefixCuts (2^48) 2644115457 9 Manual.Count131072.C020143.packed 128 cuts20143 = true := by
 decide +kernel
def pointBounds20143 : List (Nat × Nat × Nat) := [(2644129792,100113204098033,100113584521944),(2644212736,100113609676698,100113990100843)]
theorem point_links_checked20143 : (cuts20143.take 2).map (fun c => (2644115457-1+2*2^9*c.k,100113136287446+c.lower,100113516711317+c.upper)) = pointBounds20143 := by
 decide +kernel
def cuts20144 : List PrefixCut := [⟨48,243231522,243231666⟩,
⟨128,636650115,636650490⟩]
theorem checked20144 : checkPrefixCuts (2^48) 2644246529 9 Manual.Count131072.C020144.packed 128 cuts20144 = true := by
 decide +kernel
def pointBounds20144 : List (Nat × Nat × Nat) := [(2644295680,100114022481053,100114402905440)]
theorem point_links_checked20144 : (cuts20144.take 1).map (fun c => (2644246529-1+2*2^9*c.k,100113779249531+c.lower,100114159673774+c.upper)) = pointBounds20144 := by
 decide +kernel
def cuts20145 : List PrefixCut := [⟨1,5535023,5535027⟩,
⟨82,408627291,408627531⟩,
⟨128,633212427,633212799⟩]
theorem checked20145 : checkPrefixCuts (2^48) 2644377601 9 Manual.Count131072.C020145.packed 128 cuts20145 = true := by
 decide +kernel
def pointBounds20145 : List (Nat × Nat × Nat) := [(2644378624,100114421434669,100114801859291),(2644461568,100114824526937,100115204951795)]
theorem point_links_checked20145 : (cuts20145.take 2).map (fun c => (2644377601-1+2*2^9*c.k,100114415899646+c.lower,100114796324264+c.upper)) = pointBounds20145 := by
 decide +kernel
def cuts20146 : List PrefixCut := [⟨35,176791505,176791606⟩,
⟨116,587096085,587096426⟩,
⟨128,646378975,646379351⟩]
theorem checked20146 : checkPrefixCuts (2^48) 2644508673 9 Manual.Count131072.C020146.packed 128 cuts20146 = true := by
 decide +kernel
def pointBounds20146 : List (Nat × Nat × Nat) := [(2644544512,100115225903578,100115606328669),(2644627456,100115636208158,100116016633489)]
theorem point_links_checked20146 : (cuts20146.take 2).map (fun c => (2644508673-1+2*2^9*c.k,100115049112073+c.lower,100115429537063+c.upper)) = pointBounds20146 := by
 decide +kernel
def cuts20147 : List PrefixCut := [⟨69,353137396,353137598⟩,
⟨128,649007754,649008131⟩]
theorem checked20147 : checkPrefixCuts (2^48) 2644639745 9 Manual.Count131072.C020147.packed 128 cuts20147 = true := by
 decide +kernel
def pointBounds20147 : List (Nat × Nat × Nat) := [(2644710400,100116048628444,100116429054012)]
theorem point_links_checked20147 : (cuts20147.take 1).map (fun c => (2644639745-1+2*2^9*c.k,100115695491048+c.lower,100116075916414+c.upper)) = pointBounds20147 := by
 decide +kernel
def cuts20148 : List PrefixCut := [⟨22,112599234,112599301⟩,
⟨103,513606300,513606602⟩,
⟨128,640993670,640994048⟩]
theorem checked20148 : checkPrefixCuts (2^48) 2644770817 9 Manual.Count131072.C020148.packed 128 cuts20148 = true := by
 decide +kernel
def pointBounds20148 : List (Nat × Nat × Nat) := [(2644793344,100116457098036,100116837523846),(2644876288,100116858105102,100117238531147)]
theorem point_links_checked20148 : (cuts20148.take 2).map (fun c => (2644770817-1+2*2^9*c.k,100116344498802+c.lower,100116724924545+c.upper)) = pointBounds20148 := by
 decide +kernel
def cuts20149 : List PrefixCut := [⟨56,280418037,280418205⟩,
⟨128,641813212,641813597⟩]
theorem checked20149 : checkPrefixCuts (2^48) 2644901889 9 Manual.Count131072.C020149.packed 128 cuts20149 = true := by
 decide +kernel
def pointBounds20149 : List (Nat × Nat × Nat) := [(2644959232,100117265910509,100117646336798)]
theorem point_links_checked20149 : (cuts20149.take 1).map (fun c => (2644901889-1+2*2^9*c.k,100116985492472+c.lower,100117365918593+c.upper)) = pointBounds20149 := by
 decide +kernel
def cuts20150 : List PrefixCut := [⟨9,45652557,45652583⟩,
⟨90,452900282,452900545⟩,
⟨128,636567273,636567643⟩]
theorem checked20150 : checkPrefixCuts (2^48) 2645032961 9 Manual.Count131072.C020150.packed 128 cuts20150 = true := by
 decide +kernel
def pointBounds20150 : List (Nat × Nat × Nat) := [(2645042176,100117672958241,100118053384773),(2645125120,100118080205966,100118460632735)]
theorem point_links_checked20150 : (cuts20150.take 2).map (fun c => (2645032961-1+2*2^9*c.k,100117627305684+c.lower,100118007732190+c.upper)) = pointBounds20150 := by
 decide +kernel
def cuts20151 : List PrefixCut := [⟨43,211330736,211330866⟩,
⟨124,624086185,624086562⟩,
⟨128,644303313,644303702⟩]
theorem checked20151 : checkPrefixCuts (2^48) 2645164033 9 Manual.Count131072.C020151.packed 128 cuts20151 = true := by
 decide +kernel
def pointBounds20151 : List (Nat × Nat × Nat) := [(2645208064,100118475203693,100118855630699),(2645291008,100118887959142,100119268386395)]
theorem point_links_checked20151 : (cuts20151.take 2).map (fun c => (2645164033-1+2*2^9*c.k,100118263872957+c.lower,100118644299833+c.upper)) = pointBounds20151 := by
 decide +kernel
def cuts20152 : List PrefixCut := [⟨77,384864206,384864429⟩,
⟨128,641504907,641505286⟩]
theorem checked20152 : checkPrefixCuts (2^48) 2645295105 9 Manual.Count131072.C020152.packed 128 cuts20152 = true := by
 decide +kernel
def pointBounds20152 : List (Nat × Nat × Nat) := [(2645373952,100119293040476,100119673467964)]
theorem point_links_checked20152 : (cuts20152.take 1).map (fun c => (2645295105-1+2*2^9*c.k,100118908176270+c.lower,100119288603535+c.upper)) = pointBounds20152 := by
 decide +kernel
def cuts20153 : List PrefixCut := [⟨30,150236770,150236858⟩,
⟨111,553909611,553909939⟩,
⟨128,639345333,639345710⟩]
theorem checked20153 : checkPrefixCuts (2^48) 2645426177 9 Manual.Count131072.C020153.packed 128 cuts20153 = true := by
 decide +kernel
def pointBounds20153 : List (Nat × Nat × Nat) := [(2645456896,100119699917947,100120080345679),(2645539840,100120103590788,100120484018760)]
theorem point_links_checked20153 : (cuts20153.take 2).map (fun c => (2645426177-1+2*2^9*c.k,100119549681177+c.lower,100119930108821+c.upper)) = pointBounds20153 := by
 decide +kernel
def cuts20154 : List PrefixCut := [⟨64,324288884,324289076⟩,
⟨128,643462964,643463345⟩]
theorem checked20154 : checkPrefixCuts (2^48) 2645557249 9 Manual.Count131072.C020154.packed 128 cuts20154 = true := by
 decide +kernel
def pointBounds20154 : List (Nat × Nat × Nat) := [(2645622784,100120513315394,100120893743607)]
theorem point_links_checked20154 : (cuts20154.take 1).map (fun c => (2645557249-1+2*2^9*c.k,100120189026510+c.lower,100120569454531+c.upper)) = pointBounds20154 := by
 decide +kernel
def cuts20155 : List PrefixCut := [⟨17,85643702,85643755⟩,
⟨98,492363792,492364084⟩,
⟨128,639069258,639069639⟩]
theorem checked20155 : checkPrefixCuts (2^48) 2645688321 9 Manual.Count131072.C020155.packed 128 cuts20155 = true := by
 decide +kernel
def pointBounds20155 : List (Nat × Nat × Nat) := [(2645705728,100120918133176,100121298561631),(2645788672,100121324853266,100121705281960)]
theorem point_links_checked20155 : (cuts20155.take 2).map (fun c => (2645688321-1+2*2^9*c.k,100120832489474+c.lower,100121212917876+c.upper)) = pointBounds20155 := by
 decide +kernel
def cuts20156 : List PrefixCut := [⟨51,259363535,259363686⟩,
⟨128,650739552,650739931⟩]
theorem checked20156 : checkPrefixCuts (2^48) 2645819393 9 Manual.Count131072.C020156.packed 128 cuts20156 = true := by
 decide +kernel
def pointBounds20156 : List (Nat × Nat × Nat) := [(2645871616,100121730922267,100122111351201)]
theorem point_links_checked20156 : (cuts20156.take 1).map (fun c => (2645819393-1+2*2^9*c.k,100121471558732+c.lower,100121851987515+c.upper)) = pointBounds20156 := by
 decide +kernel
def cuts20157 : List PrefixCut := [⟨4,18722778,18722789⟩,
⟨85,424128073,424128324⟩,
⟨128,644111834,644112212⟩]
theorem checked20157 : checkPrefixCuts (2^48) 2645950465 9 Manual.Count131072.C020157.packed 128 cuts20157 = true := by
 decide +kernel
def pointBounds20157 : List (Nat × Nat × Nat) := [(2645954560,100122141021062,100122521450235),(2646037504,100122546426357,100122926855770)]
theorem point_links_checked20157 : (cuts20157.take 2).map (fun c => (2645950465-1+2*2^9*c.k,100122122298284+c.lower,100122502727446+c.upper)) = pointBounds20157 := by
 decide +kernel
def cuts20158 : List PrefixCut := [⟨38,192961472,192961584⟩,
⟨119,594618423,594618771⟩,
⟨128,641101745,641102121⟩]
theorem checked20158 : checkPrefixCuts (2^48) 2646081537 9 Manual.Count131072.C020158.packed 128 cuts20158 = true := by
 decide +kernel
def pointBounds20158 : List (Nat × Nat × Nat) := [(2646120448,100122959371590,100123339801242),(2646203392,100123361028541,100123741458429)]
theorem point_links_checked20158 : (cuts20158.take 2).map (fun c => (2646081537-1+2*2^9*c.k,100122766410118+c.lower,100123146839658+c.upper)) = pointBounds20158 := by
 decide +kernel
def cuts20159 : List PrefixCut := [⟨72,364521328,364521539⟩,
⟨128,643941739,643942112⟩]
theorem checked20159 : checkPrefixCuts (2^48) 2646212609 9 Manual.Count131072.C020159.packed 128 cuts20159 = true := by
 decide +kernel
def pointBounds20159 : List (Nat × Nat × Nat) := [(2646286336,100123772033191,100124152463318)]
theorem point_links_checked20159 : (cuts20159.take 1).map (fun c => (2646212609-1+2*2^9*c.k,100123407511863+c.lower,100123787941779+c.upper)) = pointBounds20159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000004
