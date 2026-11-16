import PlattAssemblyKernel
import PlattCertificates.Count131072.C021792
import PlattCertificates.Count131072.C021793
import PlattCertificates.Count131072.C021794
import PlattCertificates.Count131072.C021795
import PlattCertificates.Count131072.C021796
import PlattCertificates.Count131072.C021797
import PlattCertificates.Count131072.C021798
import PlattCertificates.Count131072.C021799
import PlattCertificates.Count131072.C021800
import PlattCertificates.Count131072.C021801
import PlattCertificates.Count131072.C021802
import PlattCertificates.Count131072.C021803
import PlattCertificates.Count131072.C021804
import PlattCertificates.Count131072.C021805
import PlattCertificates.Count131072.C021806
import PlattCertificates.Count131072.C021807
import PlattCertificates.Count131072.C021808
import PlattCertificates.Count131072.C021809
import PlattCertificates.Count131072.C021810
import PlattCertificates.Count131072.C021811
import PlattCertificates.Count131072.C021812
import PlattCertificates.Count131072.C021813
import PlattCertificates.Count131072.C021814
import PlattCertificates.Count131072.C021815
import PlattCertificates.Count131072.C021816
import PlattCertificates.Count131072.C021817
import PlattCertificates.Count131072.C021818
import PlattCertificates.Count131072.C021819
import PlattCertificates.Count131072.C021820
import PlattCertificates.Count131072.C021821
import PlattCertificates.Count131072.C021822
import PlattCertificates.Count131072.C021823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21792 : List PrefixCut := [⟨50,226338897,226339035⟩,
⟨128,592409050,592409400⟩]
theorem checked21792 : checkPrefixCuts (2^48) 2860253185 9 Manual.Count131072.C021792.packed 128 cuts21792 = true := by
 decide +kernel
def pointBounds21792 : List (Nat × Nat × Nat) := [(2860304384,101130887650641,101131268664836)]
theorem point_links_checked21792 : (cuts21792.take 1).map (fun c => (2860253185-1+2*2^9*c.k,101130661311744+c.lower,101131042325801+c.upper)) = pointBounds21792 := by
 decide +kernel
def cuts21793 : List PrefixCut := [⟨10,45561237,45561264⟩,
⟨98,452554610,452554867⟩,
⟨128,589036233,589036570⟩]
theorem checked21793 : checkPrefixCuts (2^48) 2860384257 9 Manual.Count131072.C021793.packed 128 cuts21793 = true := by
 decide +kernel
def pointBounds21793 : List (Nat × Nat × Nat) := [(2860394496,101131299282031,101131680296465),(2860484608,101131706275404,101132087290068)]
theorem point_links_checked21793 : (cuts21793.take 2).map (fun c => (2860384257-1+2*2^9*c.k,101131253720794+c.lower,101131634735201+c.upper)) = pointBounds21793 := by
 decide +kernel
def cuts21794 : List PrefixCut := [⟨58,267547017,267547169⟩,
⟨128,596192312,596192653⟩]
theorem checked21794 : checkPrefixCuts (2^48) 2860515329 9 Manual.Count131072.C021794.packed 128 cuts21794 = true := by
 decide +kernel
def pointBounds21794 : List (Nat × Nat × Nat) := [(2860574720,101132110304044,101132491318940)]
theorem point_links_checked21794 : (cuts21794.take 1).map (fun c => (2860515329-1+2*2^9*c.k,101131842757027+c.lower,101132223771771+c.upper)) = pointBounds21794 := by
 decide +kernel
def cuts21795 : List PrefixCut := [⟨18,83734349,83734398⟩,
⟨106,488032696,488032984⟩,
⟨128,588883915,588884264⟩]
theorem checked21795 : checkPrefixCuts (2^48) 2860646401 9 Manual.Count131072.C021795.packed 128 cuts21795 = true := by
 decide +kernel
def pointBounds21795 : List (Nat × Nat × Nat) := [(2860664832,101132522683688,101132903698822),(2860754944,101132926982035,101133307997408)]
theorem point_links_checked21795 : (cuts21795.take 2).map (fun c => (2860646401-1+2*2^9*c.k,101132438949339+c.lower,101132819964424+c.upper)) = pointBounds21795 := by
 decide +kernel
def cuts21796 : List PrefixCut := [⟨66,306681242,306681415⟩,
⟨128,595842482,595842817⟩]
theorem checked21796 : checkPrefixCuts (2^48) 2860777473 9 Manual.Count131072.C021796.packed 128 cuts21796 = true := by
 decide +kernel
def pointBounds21796 : List (Nat × Nat × Nat) := [(2860845056,101133334514496,101133715530103)]
theorem point_links_checked21796 : (cuts21796.take 1).map (fun c => (2860777473-1+2*2^9*c.k,101133027833254+c.lower,101133408848688+c.upper)) = pointBounds21796 := by
 decide +kernel
def cuts21797 : List PrefixCut := [⟨26,121014891,121014959⟩,
⟨114,528423412,528423709⟩,
⟨128,593847625,593847963⟩]
theorem checked21797 : checkPrefixCuts (2^48) 2860908545 9 Manual.Count131072.C021797.packed 128 cuts21797 = true := by
 decide +kernel
def pointBounds21797 : List (Nat × Nat × Nat) := [(2860935168,101133744690627,101134125706464),(2861025280,101134152099148,101134533115214)]
theorem point_links_checked21797 : (cuts21797.take 2).map (fun c => (2860908545-1+2*2^9*c.k,101133623675736+c.lower,101134004691505+c.upper)) = pointBounds21797 := by
 decide +kernel
def cuts21798 : List PrefixCut := [⟨74,345611524,345611717⟩,
⟨128,599821524,599821866⟩]
theorem checked21798 : checkPrefixCuts (2^48) 2861039617 9 Manual.Count131072.C021798.packed 128 cuts21798 = true := by
 decide +kernel
def pointBounds21798 : List (Nat × Nat × Nat) := [(2861115392,101134563134885,101134944151185)]
theorem point_links_checked21798 : (cuts21798.take 1).map (fun c => (2861039617-1+2*2^9*c.k,101134217523361+c.lower,101134598539468+c.upper)) = pointBounds21798 := by
 decide +kernel
def cuts21799 : List PrefixCut := [⟨34,162518694,162518786⟩,
⟨122,570773990,570774313⟩,
⟨128,601368033,601368373⟩]
theorem checked21799 : checkPrefixCuts (2^48) 2861170689 9 Manual.Count131072.C021799.packed 128 cuts21799 = true := by
 decide +kernel
def pointBounds21799 : List (Nat × Nat × Nat) := [(2861205504,101134979863579,101135360880120),(2861295616,101135388118875,101135769135647)]
theorem point_links_checked21799 : (cuts21799.take 2).map (fun c => (2861170689-1+2*2^9*c.k,101134817344885+c.lower,101135198361334+c.upper)) = pointBounds21799 := by
 decide +kernel
def cuts21800 : List PrefixCut := [⟨82,384337803,384338026⟩,
⟨128,599963380,599963721⟩]
theorem checked21800 : checkPrefixCuts (2^48) 2861301761 9 Manual.Count131072.C021800.packed 128 cuts21800 = true := by
 decide +kernel
def pointBounds21800 : List (Nat × Nat × Nat) := [(2861385728,101135803050721,101136184067733)]
theorem point_links_checked21800 : (cuts21800.take 1).map (fun c => (2861301761-1+2*2^9*c.k,101135418712918+c.lower,101135799729707+c.upper)) = pointBounds21800 := by
 decide +kernel
def cuts21801 : List PrefixCut := [⟨42,188374305,188374418⟩,
⟨128,584590589,584590933⟩]
theorem checked21801 : checkPrefixCuts (2^48) 2861432833 9 Manual.Count131072.C021801.packed 128 cuts21801 = true := by
 decide +kernel
def pointBounds21801 : List (Nat × Nat × Nat) := [(2861475840,101136207050603,101136588067846)]
theorem point_links_checked21801 : (cuts21801.take 1).map (fun c => (2861432833-1+2*2^9*c.k,101136018676298+c.lower,101136399693428+c.upper)) = pointBounds21801 := by
 decide +kernel
def cuts21802 : List PrefixCut := [⟨2,9344578,9344583⟩,
⟨90,426007683,426007924⟩,
⟨128,599121597,599121936⟩]
theorem checked21802 : checkPrefixCuts (2^48) 2861563905 9 Manual.Count131072.C021802.packed 128 cuts21802 = true := by
 decide +kernel
def pointBounds21802 : List (Nat × Nat × Nat) := [(2861565952,101136612611465,101136993628944),(2861656064,101137029274570,101137410292285)]
theorem point_links_checked21802 : (cuts21802.take 2).map (fun c => (2861563905-1+2*2^9*c.k,101136603266887+c.lower,101136984284361+c.upper)) = pointBounds21802 := by
 decide +kernel
def cuts21803 : List PrefixCut := [⟨50,226323167,226323298⟩,
⟨128,588274591,588274930⟩]
theorem checked21803 : checkPrefixCuts (2^48) 2861694977 9 Manual.Count131072.C021803.packed 128 cuts21803 = true := by
 decide +kernel
def pointBounds21803 : List (Nat × Nat × Nat) := [(2861746176,101137428711651,101137809729595)]
theorem point_links_checked21803 : (cuts21803.take 1).map (fun c => (2861694977-1+2*2^9*c.k,101137202388484+c.lower,101137583406297+c.upper)) = pointBounds21803 := by
 decide +kernel
def cuts21804 : List PrefixCut := [⟨10,46423478,46423505⟩,
⟨98,456064151,456064414⟩,
⟨128,592968775,592969118⟩]
theorem checked21804 : checkPrefixCuts (2^48) 2861826049 9 Manual.Count131072.C021804.packed 128 cuts21804 = true := by
 decide +kernel
def pointBounds21804 : List (Nat × Nat × Nat) := [(2861836288,101137837086553,101138218104732),(2861926400,101138246727226,101138627745641)]
theorem point_links_checked21804 : (cuts21804.take 2).map (fun c => (2861826049-1+2*2^9*c.k,101137790663075+c.lower,101138171681227+c.upper)) = pointBounds21804 := by
 decide +kernel
def cuts21805 : List PrefixCut := [⟨58,263773287,263773437⟩,
⟨128,590089341,590089680⟩]
theorem checked21805 : checkPrefixCuts (2^48) 2861957121 9 Manual.Count131072.C021805.packed 128 cuts21805 = true := by
 decide +kernel
def pointBounds21805 : List (Nat × Nat × Nat) := [(2862016512,101138647405137,101139028423782)]
theorem point_links_checked21805 : (cuts21805.take 1).map (fun c => (2861957121-1+2*2^9*c.k,101138383631850+c.lower,101138764650345+c.upper)) = pointBounds21805 := by
 decide +kernel
def cuts21806 : List PrefixCut := [⟨18,81528560,81528611⟩,
⟨106,495359330,495359617⟩,
⟨128,596159751,596160098⟩]
theorem checked21806 : checkPrefixCuts (2^48) 2862088193 9 Manual.Count131072.C021806.packed 128 cuts21806 = true := by
 decide +kernel
def pointBounds21806 : List (Nat × Nat × Nat) := [(2862106624,101139055249751,101139436268636),(2862196736,101139469080521,101139850099642)]
theorem point_links_checked21806 : (cuts21806.take 2).map (fun c => (2862088193-1+2*2^9*c.k,101138973721191+c.lower,101139354740025+c.upper)) = pointBounds21806 := by
 decide +kernel
def cuts21807 : List PrefixCut := [⟨66,304363327,304363506⟩,
⟨128,600754303,600754652⟩]
theorem checked21807 : checkPrefixCuts (2^48) 2862219265 9 Manual.Count131072.C021807.packed 128 cuts21807 = true := by
 decide +kernel
def pointBounds21807 : List (Nat × Nat × Nat) := [(2862286848,101139874244269,101140255263629)]
theorem point_links_checked21807 : (cuts21807.take 1).map (fun c => (2862219265-1+2*2^9*c.k,101139569880942+c.lower,101139950900123+c.upper)) = pointBounds21807 := by
 decide +kernel
def cuts21808 : List PrefixCut := [⟨26,118790514,118790584⟩,
⟨114,526878788,526879084⟩,
⟨128,589811729,589812063⟩]
theorem checked21808 : checkPrefixCuts (2^48) 2862350337 9 Manual.Count131072.C021808.packed 128 cuts21808 = true := by
 decide +kernel
def pointBounds21808 : List (Nat × Nat × Nat) := [(2862376960,101140289425759,101140670445359),(2862467072,101140697514033,101141078533859)]
theorem point_links_checked21808 : (cuts21808.take 2).map (fun c => (2862350337-1+2*2^9*c.k,101140170635245+c.lower,101140551654775+c.upper)) = pointBounds21808 := by
 decide +kernel
def cuts21809 : List PrefixCut := [⟨74,339439195,339439393⟩,
⟨128,588014679,588015020⟩]
theorem checked21809 : checkPrefixCuts (2^48) 2862481409 9 Manual.Count131072.C021809.packed 128 cuts21809 = true := by
 decide +kernel
def pointBounds21809 : List (Nat × Nat × Nat) := [(2862557184,101141099886169,101141480906231)]
theorem point_links_checked21809 : (cuts21809.take 1).map (fun c => (2862481409-1+2*2^9*c.k,101140760446974+c.lower,101141141466838+c.upper)) = pointBounds21809 := by
 decide +kernel
def cuts21810 : List PrefixCut := [⟨34,157225488,157225580⟩,
⟨122,567930054,567930378⟩,
⟨128,594870715,594871054⟩]
theorem checked21810 : checkPrefixCuts (2^48) 2862612481 9 Manual.Count131072.C021810.packed 128 cuts21810 = true := by
 decide +kernel
def pointBounds21810 : List (Nat × Nat × Nat) := [(2862647296,101141505687141,101141886707438),(2862737408,101141916391707,101142297412236)]
theorem point_links_checked21810 : (cuts21810.take 2).map (fun c => (2862612481-1+2*2^9*c.k,101141348461653+c.lower,101141729481858+c.upper)) = pointBounds21810 := by
 decide +kernel
def cuts21811 : List PrefixCut := [⟨82,379916238,379916454⟩,
⟨128,591598735,591599072⟩]
theorem checked21811 : checkPrefixCuts (2^48) 2862743553 9 Manual.Count131072.C021811.packed 128 cuts21811 = true := by
 decide +kernel
def pointBounds21811 : List (Nat × Nat × Nat) := [(2862827520,101142323248606,101142704269366)]
theorem point_links_checked21811 : (cuts21811.take 1).map (fun c => (2862743553-1+2*2^9*c.k,101141943332368+c.lower,101142324352912+c.upper)) = pointBounds21811 := by
 decide +kernel
def cuts21812 : List PrefixCut := [⟨42,192703728,192703837⟩,
⟨128,584001370,584001709⟩]
theorem checked21812 : checkPrefixCuts (2^48) 2862874625 9 Manual.Count131072.C021812.packed 128 cuts21812 = true := by
 decide +kernel
def pointBounds21812 : List (Nat × Nat × Nat) := [(2862917632,101142727634831,101143108655821)]
theorem point_links_checked21812 : (cuts21812.take 1).map (fun c => (2862874625-1+2*2^9*c.k,101142534931103+c.lower,101142915951984+c.upper)) = pointBounds21812 := by
 decide +kernel
def cuts21813 : List PrefixCut := [⟨2,8749985,8749990⟩,
⟨90,414978704,414978946⟩,
⟨128,589381793,589382135⟩]
theorem checked21813 : checkPrefixCuts (2^48) 2863005697 9 Manual.Count131072.C021813.packed 128 cuts21813 = true := by
 decide +kernel
def pointBounds21813 : List (Nat × Nat × Nat) := [(2863007744,101143127682458,101143508703683),(2863097856,101143533911177,101143914932639)]
theorem point_links_checked21813 : (cuts21813.take 2).map (fun c => (2863005697-1+2*2^9*c.k,101143118932473+c.lower,101143499953693+c.upper)) = pointBounds21813 := by
 decide +kernel
def cuts21814 : List PrefixCut := [⟨50,233189170,233189307⟩,
⟨128,597416048,597416388⟩]
theorem checked21814 : checkPrefixCuts (2^48) 2863136769 9 Manual.Count131072.C021814.packed 128 cuts21814 = true := by
 decide +kernel
def pointBounds21814 : List (Nat × Nat × Nat) := [(2863187968,101143941503436,101144322525135)]
theorem point_links_checked21814 : (cuts21814.take 1).map (fun c => (2863136769-1+2*2^9*c.k,101143708314266+c.lower,101144089335828+c.upper)) = pointBounds21814 := by
 decide +kernel
def cuts21815 : List PrefixCut := [⟨10,45318736,45318764⟩,
⟨98,456817527,456817788⟩,
⟨128,592571894,592572234⟩]
theorem checked21815 : checkPrefixCuts (2^48) 2863267841 9 Manual.Count131072.C021815.packed 128 cuts21815 = true := by
 decide +kernel
def pointBounds21815 : List (Nat × Nat × Nat) := [(2863278080,101144351049050,101144732070980),(2863368192,101144762547841,101145143570004)]
theorem point_links_checked21815 : (cuts21815.take 2).map (fun c => (2863267841-1+2*2^9*c.k,101144305730314+c.lower,101144686752216+c.upper)) = pointBounds21815 := by
 decide +kernel
def cuts21816 : List PrefixCut := [⟨58,260888115,260888264⟩,
⟨128,587334812,587335148⟩]
theorem checked21816 : checkPrefixCuts (2^48) 2863398913 9 Manual.Count131072.C021816.packed 128 cuts21816 = true := by
 decide +kernel
def pointBounds21816 : List (Nat × Nat × Nat) := [(2863458304,101145159190323,101145540212714)]
theorem point_links_checked21816 : (cuts21816.take 1).map (fun c => (2863398913-1+2*2^9*c.k,101144898302208+c.lower,101145279324450+c.upper)) = pointBounds21816 := by
 decide +kernel
def cuts21817 : List PrefixCut := [⟨18,83846619,83846669⟩,
⟨106,490195239,490195523⟩,
⟨128,592419286,592419628⟩]
theorem checked21817 : checkPrefixCuts (2^48) 2863529985 9 Manual.Count131072.C021817.packed 128 cuts21817 = true := by
 decide +kernel
def pointBounds21817 : List (Nat × Nat × Nat) := [(2863548416,101145569483639,101145950506267),(2863638528,101145975832259,101146356855121)]
theorem point_links_checked21817 : (cuts21817.take 2).map (fun c => (2863529985-1+2*2^9*c.k,101145485637020+c.lower,101145866659598+c.upper)) = pointBounds21817 := by
 decide +kernel
def cuts21818 : List PrefixCut := [⟨66,307355356,307355538⟩,
⟨128,590328131,590328480⟩]
theorem checked21818 : checkPrefixCuts (2^48) 2863661057 9 Manual.Count131072.C021818.packed 128 cuts21818 = true := by
 decide +kernel
def pointBounds21818 : List (Nat × Nat × Nat) := [(2863728640,101146385411662,101146766434764)]
theorem point_links_checked21818 : (cuts21818.take 1).map (fun c => (2863661057-1+2*2^9*c.k,101146078056306+c.lower,101146459079226+c.upper)) = pointBounds21818 := by
 decide +kernel
def cuts21819 : List PrefixCut := [⟨26,117944427,117944495⟩,
⟨114,521600921,521601222⟩,
⟨128,585779865,585780205⟩]
theorem checked21819 : checkPrefixCuts (2^48) 2863792129 9 Manual.Count131072.C021819.packed 128 cuts21819 = true := by
 decide +kernel
def pointBounds21819 : List (Nat × Nat × Nat) := [(2863818752,101146786328864,101147167352201),(2863908864,101147189985358,101147571008928)]
theorem point_links_checked21819 : (cuts21819.take 2).map (fun c => (2863792129-1+2*2^9*c.k,101146668384437+c.lower,101147049407706+c.upper)) = pointBounds21819 := by
 decide +kernel
def cuts21820 : List PrefixCut := [⟨74,341430540,341430734⟩,
⟨128,584279001,584279332⟩]
theorem checked21820 : checkPrefixCuts (2^48) 2863923201 9 Manual.Count131072.C021820.packed 128 cuts21820 = true := by
 decide +kernel
def pointBounds21820 : List (Nat × Nat × Nat) := [(2863998976,101147595594842,101147976618645)]
theorem point_links_checked21820 : (cuts21820.take 1).map (fun c => (2863923201-1+2*2^9*c.k,101147254164302+c.lower,101147635187911+c.upper)) = pointBounds21820 := by
 decide +kernel
def cuts21821 : List PrefixCut := [⟨34,155868724,155868817⟩,
⟨122,566071711,566072040⟩,
⟨128,594276373,594276719⟩]
theorem checked21821 : checkPrefixCuts (2^48) 2864054273 9 Manual.Count131072.C021821.packed 128 cuts21821 = true := by
 decide +kernel
def pointBounds21821 : List (Nat × Nat × Nat) := [(2864089088,101147994312027,101148375336060),(2864179200,101148404515014,101148785539283)]
theorem point_links_checked21821 : (cuts21821.take 2).map (fun c => (2864054273-1+2*2^9*c.k,101147838443303+c.lower,101148219467243+c.upper)) = pointBounds21821 := by
 decide +kernel
def cuts21822 : List PrefixCut := [⟨82,378840675,378840896⟩,
⟨128,588549464,588549806⟩]
theorem checked21822 : checkPrefixCuts (2^48) 2864185345 9 Manual.Count131072.C021822.packed 128 cuts21822 = true := by
 decide +kernel
def pointBounds21822 : List (Nat × Nat × Nat) := [(2864269312,101148811560351,101149192584858)]
theorem point_links_checked21822 : (cuts21822.take 1).map (fun c => (2864185345-1+2*2^9*c.k,101148432719676+c.lower,101148813743962+c.upper)) = pointBounds21822 := by
 decide +kernel
def cuts21823 : List PrefixCut := [⟨42,201057848,201057966⟩,
⟨128,602476430,602476778⟩]
theorem checked21823 : checkPrefixCuts (2^48) 2864316417 9 Manual.Count131072.C021823.packed 128 cuts21823 = true := by
 decide +kernel
def pointBounds21823 : List (Nat × Nat × Nat) := [(2864359424,101149222326988,101149603351734)]
theorem point_links_checked21823 : (cuts21823.take 1).map (fun c => (2864316417-1+2*2^9*c.k,101149021269140+c.lower,101149402293768+c.upper)) = pointBounds21823 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000056
