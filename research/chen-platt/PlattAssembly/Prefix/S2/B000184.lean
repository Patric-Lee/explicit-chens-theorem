import PlattAssemblyKernel
import PlattCertificates.Count131072.C015888
import PlattCertificates.Count131072.C015889
import PlattCertificates.Count131072.C015890
import PlattCertificates.Count131072.C015891
import PlattCertificates.Count131072.C015892
import PlattCertificates.Count131072.C015893
import PlattCertificates.Count131072.C015894
import PlattCertificates.Count131072.C015895
import PlattCertificates.Count131072.C015896
import PlattCertificates.Count131072.C015897
import PlattCertificates.Count131072.C015898
import PlattCertificates.Count131072.C015899
import PlattCertificates.Count131072.C015900
import PlattCertificates.Count131072.C015901
import PlattCertificates.Count131072.C015902
import PlattCertificates.Count131072.C015903
import PlattCertificates.Count131072.C015904
import PlattCertificates.Count131072.C015905
import PlattCertificates.Count131072.C015906
import PlattCertificates.Count131072.C015907
import PlattCertificates.Count131072.C015908
import PlattCertificates.Count131072.C015909
import PlattCertificates.Count131072.C015910
import PlattCertificates.Count131072.C015911
import PlattCertificates.Count131072.C015912
import PlattCertificates.Count131072.C015913
import PlattCertificates.Count131072.C015914
import PlattCertificates.Count131072.C015915
import PlattCertificates.Count131072.C015916
import PlattCertificates.Count131072.C015917
import PlattCertificates.Count131072.C015918
import PlattCertificates.Count131072.C015919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000184
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15888 : List PrefixCut := [⟨38,248500210,248500375⟩,
⟨102,654967381,654967814⟩,
⟨128,823864027,823864570⟩]
theorem checked15888 : checkPrefixCuts (2^48) 2086404097 9 Manual.Count131072.C015888.packed 128 cuts15888 = true := by
 decide +kernel
def pointBounds15888 : List (Nat × Nat × Nat) := [(2086443008,97022993242814,97023371771579),(2086508544,97023399709985,97023778239018)]
theorem point_links_checked15888 : (cuts15888.take 2).map (fun c => (2086404097-1+2*2^9*c.k,97022744742604+c.lower,97023123271204+c.upper)) = pointBounds15888 := by
 decide +kernel
def cuts15889 : List PrefixCut := [⟨38,248484624,248484781⟩,
⟨102,651958564,651958979⟩,
⟨128,815718662,815719186⟩]
theorem checked15889 : checkPrefixCuts (2^48) 2086535169 9 Manual.Count131072.C015889.packed 128 cuts15889 = true := by
 decide +kernel
def pointBounds15889 : List (Nat × Nat × Nat) := [(2086574080,97023817091255,97024195620555),(2086639616,97024220565195,97024599094753)]
theorem point_links_checked15889 : (cuts15889.take 2).map (fun c => (2086535169-1+2*2^9*c.k,97023568606631+c.lower,97023947135774+c.upper)) = pointBounds15889 := by
 decide +kernel
def cuts15890 : List PrefixCut := [⟨38,246040976,246041133⟩,
⟨102,660685188,660685613⟩,
⟨128,828751329,828751864⟩]
theorem checked15890 : checkPrefixCuts (2^48) 2086666241 9 Manual.Count131072.C015890.packed 128 cuts15890 = true := by
 decide +kernel
def pointBounds15890 : List (Nat × Nat × Nat) := [(2086705152,97024630366269,97025008896093),(2086770688,97025045010481,97025423540573)]
theorem point_links_checked15890 : (cuts15890.take 2).map (fun c => (2086666241-1+2*2^9*c.k,97024384325293+c.lower,97024762854960+c.upper)) = pointBounds15890 := by
 decide +kernel
def cuts15891 : List PrefixCut := [⟨38,242923246,242923400⟩,
⟨102,654304409,654304830⟩,
⟨128,826406262,826406793⟩]
theorem checked15891 : checkPrefixCuts (2^48) 2086797313 9 Manual.Count131072.C015891.packed 128 cuts15891 = true := by
 decide +kernel
def pointBounds15891 : List (Nat × Nat × Nat) := [(2086836224,97025455999868,97025834530224),(2086901760,97025867381031,97026245911654)]
theorem point_links_checked15891 : (cuts15891.take 2).map (fun c => (2086797313-1+2*2^9*c.k,97025213076622+c.lower,97025591606824+c.upper)) = pointBounds15891 := by
 decide +kernel
def cuts15892 : List PrefixCut := [⟨38,252484034,252484197⟩,
⟨102,661007006,661007436⟩,
⟨128,828242796,828243334⟩]
theorem checked15892 : checkPrefixCuts (2^48) 2086928385 9 Manual.Count131072.C015892.packed 128 cuts15892 = true := by
 decide +kernel
def pointBounds15892 : List (Nat × Nat × Nat) := [(2086967296,97026291966918,97026670497814),(2087032832,97026700489890,97027079021053)]
theorem point_links_checked15892 : (cuts15892.take 2).map (fun c => (2086928385-1+2*2^9*c.k,97026039482884+c.lower,97026418013617+c.upper)) = pointBounds15892 := by
 decide +kernel
def cuts15893 : List PrefixCut := [⟨38,246803830,246803990⟩,
⟨102,658402999,658403430⟩,
⟨128,825493458,825493997⟩]
theorem checked15893 : checkPrefixCuts (2^48) 2087059457 9 Manual.Count131072.C015893.packed 128 cuts15893 = true := by
 decide +kernel
def pointBounds15893 : List (Nat × Nat × Nat) := [(2087098368,97027114529510,97027493060941),(2087163904,97027526128679,97027904660381)]
theorem point_links_checked15893 : (cuts15893.take 2).map (fun c => (2087059457-1+2*2^9*c.k,97026867725680+c.lower,97027246256951+c.upper)) = pointBounds15893 := by
 decide +kernel
def cuts15894 : List PrefixCut := [⟨38,240315215,240315371⟩,
⟨102,649461140,649461560⟩,
⟨128,816406281,816406811⟩]
theorem checked15894 : checkPrefixCuts (2^48) 2087190529 9 Manual.Count131072.C015894.packed 128 cuts15894 = true := by
 decide +kernel
def pointBounds15894 : List (Nat × Nat × Nat) := [(2087229440,97027933534353,97028312066319),(2087294976,97028342680278,97028721212508)]
theorem point_links_checked15894 : (cuts15894.take 2).map (fun c => (2087190529-1+2*2^9*c.k,97027693219138+c.lower,97028071750948+c.upper)) = pointBounds15894 := by
 decide +kernel
def cuts15895 : List PrefixCut := [⟨38,252166809,252166970⟩,
⟨102,653600897,653601319⟩,
⟨128,817838695,817839225⟩]
theorem checked15895 : checkPrefixCuts (2^48) 2087321601 9 Manual.Count131072.C015895.packed 128 cuts15895 = true := by
 decide +kernel
def pointBounds15895 : List (Nat × Nat × Nat) := [(2087360512,97028761792228,97029140324729),(2087426048,97029163226316,97029541759078)]
theorem point_links_checked15895 : (cuts15895.take 2).map (fun c => (2087321601-1+2*2^9*c.k,97028509625419+c.lower,97028888157759+c.upper)) = pointBounds15895 := by
 decide +kernel
def cuts15896 : List PrefixCut := [⟨38,242442425,242442580⟩,
⟨102,644660313,644660724⟩,
⟨128,820213838,820214364⟩]
theorem checked15896 : checkPrefixCuts (2^48) 2087452673 9 Manual.Count131072.C015896.packed 128 cuts15896 = true := by
 decide +kernel
def pointBounds15896 : List (Nat × Nat × Nat) := [(2087491584,97029569906539,97029948439564),(2087557120,97029972124427,97030350657708)]
theorem point_links_checked15896 : (cuts15896.take 2).map (fun c => (2087452673-1+2*2^9*c.k,97029327464114+c.lower,97029705996984+c.upper)) = pointBounds15896 := by
 decide +kernel
def cuts15897 : List PrefixCut := [⟨38,242022718,242022872⟩,
⟨102,656215013,656215433⟩,
⟨128,822319739,822320267⟩]
theorem checked15897 : checkPrefixCuts (2^48) 2087583745 9 Manual.Count131072.C015897.packed 128 cuts15897 = true := by
 decide +kernel
def pointBounds15897 : List (Nat × Nat × Nat) := [(2087622656,97030389700670,97030768234220),(2087688192,97030803892965,97031182426781)]
theorem point_links_checked15897 : (cuts15897.take 2).map (fun c => (2087583745-1+2*2^9*c.k,97030147677952+c.lower,97030526211348+c.upper)) = pointBounds15897 := by
 decide +kernel
def cuts15898 : List PrefixCut := [⟨38,245782587,245782741⟩,
⟨102,669655927,669656353⟩,
⟨128,837772479,837773015⟩]
theorem checked15898 : checkPrefixCuts (2^48) 2087714817 9 Manual.Count131072.C015898.packed 128 cuts15898 = true := by
 decide +kernel
def pointBounds15898 : List (Nat × Nat × Nat) := [(2087753728,97031215780278,97031594314356),(2087819264,97031639653618,97032018187968)]
theorem point_links_checked15898 : (cuts15898.take 2).map (fun c => (2087714817-1+2*2^9*c.k,97030969997691+c.lower,97031348531615+c.upper)) = pointBounds15898 := by
 decide +kernel
def cuts15899 : List PrefixCut := [⟨38,248463447,248463610⟩,
⟨102,659637848,659638280⟩,
⟨128,830844409,830844953⟩]
theorem checked15899 : checkPrefixCuts (2^48) 2087845889 9 Manual.Count131072.C015899.packed 128 cuts15899 = true := by
 decide +kernel
def pointBounds15899 : List (Nat × Nat × Nat) := [(2087884800,97032056233617,97032434768240),(2087950336,97032467408018,97032845942910)]
theorem point_links_checked15899 : (cuts15899.take 2).map (fun c => (2087845889-1+2*2^9*c.k,97031807770170+c.lower,97032186304630+c.upper)) = pointBounds15899 := by
 decide +kernel
def cuts15900 : List PrefixCut := [⟨38,241707538,241707697⟩,
⟨102,651777736,651778160⟩,
⟨128,816233562,816234091⟩]
theorem checked15900 : checkPrefixCuts (2^48) 2087976961 9 Manual.Count131072.C015900.packed 128 cuts15900 = true := by
 decide +kernel
def pointBounds15900 : List (Nat × Nat × Nat) := [(2088015872,97032880322117,97033258857280),(2088081408,97033290392315,97033668927743)]
theorem point_links_checked15900 : (cuts15900.take 2).map (fun c => (2087976961-1+2*2^9*c.k,97032638614579+c.lower,97033017149583+c.upper)) = pointBounds15900 := by
 decide +kernel
def cuts15901 : List PrefixCut := [⟨38,241827207,241827363⟩,
⟨102,654702404,654702825⟩,
⟨128,825078747,825079276⟩]
theorem checked15901 : checkPrefixCuts (2^48) 2088108033 9 Manual.Count131072.C015901.packed 128 cuts15901 = true := by
 decide +kernel
def pointBounds15901 : List (Nat × Nat × Nat) := [(2088146944,97033696675348,97034075211037),(2088212480,97034109550545,97034488086499)]
theorem point_links_checked15901 : (cuts15901.take 2).map (fun c => (2088108033-1+2*2^9*c.k,97033454848141+c.lower,97033833383674+c.upper)) = pointBounds15901 := by
 decide +kernel
def cuts15902 : List PrefixCut := [⟨38,245720877,245721033⟩,
⟨102,653583070,653583489⟩,
⟨128,819096535,819097059⟩]
theorem checked15902 : checkPrefixCuts (2^48) 2088239105 9 Manual.Count131072.C015902.packed 128 cuts15902 = true := by
 decide +kernel
def pointBounds15902 : List (Nat × Nat × Nat) := [(2088278016,97034525647765,97034904183983),(2088343552,97034933509958,97035312046439)]
theorem point_links_checked15902 : (cuts15902.take 2).map (fun c => (2088239105-1+2*2^9*c.k,97034279926888+c.lower,97034658462950+c.upper)) = pointBounds15902 := by
 decide +kernel
def cuts15903 : List PrefixCut := [⟨38,251635792,251635952⟩,
⟨102,661494109,661494534⟩,
⟨128,826997174,826997708⟩]
theorem checked15903 : checkPrefixCuts (2^48) 2088370177 9 Manual.Count131072.C015903.packed 128 cuts15903 = true := by
 decide +kernel
def pointBounds15903 : List (Nat × Nat × Nat) := [(2088409088,97035350659215,97035729195961),(2088474624,97035760517532,97036139054543)]
theorem point_links_checked15903 : (cuts15903.take 2).map (fun c => (2088370177-1+2*2^9*c.k,97035099023423+c.lower,97035477560009+c.upper)) = pointBounds15903 := by
 decide +kernel
def cuts15904 : List PrefixCut := [⟨38,242590241,242590401⟩,
⟨102,650805475,650805902⟩,
⟨128,817780583,817781119⟩]
theorem checked15904 : checkPrefixCuts (2^48) 2088501249 9 Manual.Count131072.C015904.packed 128 cuts15904 = true := by
 decide +kernel
def pointBounds15904 : List (Nat × Nat × Nat) := [(2088540160,97036168610838,97036547148118),(2088605696,97036576826072,97036955363619)]
theorem point_links_checked15904 : (cuts15904.take 2).map (fun c => (2088501249-1+2*2^9*c.k,97035926020597+c.lower,97036304557717+c.upper)) = pointBounds15904 := by
 decide +kernel
def cuts15905 : List PrefixCut := [⟨38,247426573,247426729⟩,
⟨102,663971429,663971852⟩,
⟨128,832014118,832014647⟩]
theorem checked15905 : checkPrefixCuts (2^48) 2088632321 9 Manual.Count131072.C015905.packed 128 cuts15905 = true := by
 decide +kernel
def pointBounds15905 : List (Nat × Nat × Nat) := [(2088671232,97036991227753,97037369765565),(2088736768,97037407772609,97037786310688)]
theorem point_links_checked15905 : (cuts15905.take 2).map (fun c => (2088632321-1+2*2^9*c.k,97036743801180+c.lower,97037122338836+c.upper)) = pointBounds15905 := by
 decide +kernel
def cuts15906 : List PrefixCut := [⟨38,236361116,236361269⟩,
⟨102,647085480,647085898⟩,
⟨128,810536157,810536681⟩]
theorem checked15906 : checkPrefixCuts (2^48) 2088763393 9 Manual.Count131072.C015906.packed 128 cuts15906 = true := by
 decide +kernel
def pointBounds15906 : List (Nat × Nat × Nat) := [(2088802304,97037812176414,97038190714752),(2088867840,97038222900778,97038601439381)]
theorem point_links_checked15906 : (cuts15906.take 2).map (fun c => (2088763393-1+2*2^9*c.k,97037575815298+c.lower,97037954353483+c.upper)) = pointBounds15906 := by
 decide +kernel
def cuts15907 : List PrefixCut := [⟨38,241331877,241332032⟩,
⟨102,660654067,660654491⟩,
⟨128,821938652,821939182⟩]
theorem checked15907 : checkPrefixCuts (2^48) 2088894465 9 Manual.Count131072.C015907.packed 128 cuts15907 = true := by
 decide +kernel
def pointBounds15907 : List (Nat × Nat × Nat) := [(2088933376,97038627683332,97039006222196),(2088998912,97039047005522,97039425544655)]
theorem point_links_checked15907 : (cuts15907.take 2).map (fun c => (2088894465-1+2*2^9*c.k,97038386351455+c.lower,97038764890164+c.upper)) = pointBounds15907 := by
 decide +kernel
def cuts15908 : List PrefixCut := [⟨38,248996822,248996985⟩,
⟨102,664789494,664789925⟩,
⟨128,838459320,838459860⟩]
theorem checked15908 : checkPrefixCuts (2^48) 2089025537 9 Manual.Count131072.C015908.packed 128 cuts15908 = true := by
 decide +kernel
def pointBounds15908 : List (Nat × Nat × Nat) := [(2089064448,97039457286929,97039835826331),(2089129984,97039873079601,97040251619271)]
theorem point_links_checked15908 : (cuts15908.take 2).map (fun c => (2089025537-1+2*2^9*c.k,97039208290107+c.lower,97039586829346+c.upper)) = pointBounds15908 := by
 decide +kernel
def cuts15909 : List PrefixCut := [⟨38,241436360,241436514⟩,
⟨102,656394587,656395008⟩,
⟨128,823317308,823317835⟩]
theorem checked15909 : checkPrefixCuts (2^48) 2089156609 9 Manual.Count131072.C015909.packed 128 cuts15909 = true := by
 decide +kernel
def pointBounds15909 : List (Nat × Nat × Nat) := [(2089195520,97040288185787,97040666725720),(2089261056,97040703144014,97041081684214)]
theorem point_links_checked15909 : (cuts15909.take 2).map (fun c => (2089156609-1+2*2^9*c.k,97040046749427+c.lower,97040425289206+c.upper)) = pointBounds15909 := by
 decide +kernel
def cuts15910 : List PrefixCut := [⟨38,237918372,237918526⟩,
⟨102,653254793,653255215⟩,
⟨128,821918363,821918894⟩]
theorem checked15910 : checkPrefixCuts (2^48) 2089287681 9 Manual.Count131072.C015910.packed 128 cuts15910 = true := by
 decide +kernel
def pointBounds15910 : List (Nat × Nat × Nat) := [(2089326592,97041107985107,97041486525567),(2089392128,97041523321528,97041901862256)]
theorem point_links_checked15910 : (cuts15910.take 2).map (fun c => (2089287681-1+2*2^9*c.k,97040870066735+c.lower,97041248607041+c.upper)) = pointBounds15910 := by
 decide +kernel
def cuts15911 : List PrefixCut := [⟨38,249084706,249084867⟩,
⟨102,657390130,657390552⟩,
⟨128,829276079,829276612⟩]
theorem checked15911 : checkPrefixCuts (2^48) 2089418753 9 Manual.Count131072.C015911.packed 128 cuts15911 = true := by
 decide +kernel
def pointBounds15911 : List (Nat × Nat × Nat) := [(2089457664,97041941069804,97042319610802),(2089523200,97042349375228,97042727916487)]
theorem point_links_checked15911 : (cuts15911.take 2).map (fun c => (2089418753-1+2*2^9*c.k,97041691985098+c.lower,97042070525935+c.upper)) = pointBounds15911 := by
 decide +kernel
def cuts15912 : List PrefixCut := [⟨38,254457276,254457440⟩,
⟨102,660177864,660178294⟩,
⟨128,822624138,822624675⟩]
theorem checked15912 : checkPrefixCuts (2^48) 2089549825 9 Manual.Count131072.C015912.packed 128 cuts15912 = true := by
 decide +kernel
def pointBounds15912 : List (Nat × Nat × Nat) := [(2089588736,97042775718453,97043154259987),(2089654272,97043181439041,97043559980841)]
theorem point_links_checked15912 : (cuts15912.take 2).map (fun c => (2089549825-1+2*2^9*c.k,97042521261177+c.lower,97042899802547+c.upper)) = pointBounds15912 := by
 decide +kernel
def cuts15913 : List PrefixCut := [⟨38,249726935,249727098⟩,
⟨102,665793272,665793706⟩,
⟨128,828498729,828499267⟩]
theorem checked15913 : checkPrefixCuts (2^48) 2089680897 9 Manual.Count131072.C015913.packed 128 cuts15913 = true := by
 decide +kernel
def pointBounds15913 : List (Nat × Nat × Nat) := [(2089719808,97043593612250,97043972154320),(2089785344,97044009678587,97044388220928)]
theorem point_links_checked15913 : (cuts15913.take 2).map (fun c => (2089680897-1+2*2^9*c.k,97043343885315+c.lower,97043722427222+c.upper)) = pointBounds15913 := by
 decide +kernel
def cuts15914 : List PrefixCut := [⟨38,242303437,242303595⟩,
⟨102,653764524,653764954⟩,
⟨128,818614703,818615242⟩]
theorem checked15914 : checkPrefixCuts (2^48) 2089811969 9 Manual.Count131072.C015914.packed 128 cuts15914 = true := by
 decide +kernel
def pointBounds15914 : List (Nat × Nat × Nat) := [(2089850880,97044414687481,97044793230084),(2089916416,97044826148568,97045204691443)]
theorem point_links_checked15914 : (cuts15914.take 2).map (fun c => (2089811969-1+2*2^9*c.k,97044172384044+c.lower,97044550926489+c.upper)) = pointBounds15914 := by
 decide +kernel
def cuts15915 : List PrefixCut := [⟨38,244712493,244712648⟩,
⟨102,651972900,651973316⟩,
⟨128,822064990,822065516⟩]
theorem checked15915 : checkPrefixCuts (2^48) 2089943041 9 Manual.Count131072.C015915.packed 128 cuts15915 = true := by
 decide +kernel
def pointBounds15915 : List (Nat × Nat × Nat) := [(2089981952,97045235711240,97045614254379),(2090047488,97045642971647,97046021515047)]
theorem point_links_checked15915 : (cuts15915.take 2).map (fun c => (2089943041-1+2*2^9*c.k,97044990998747+c.lower,97045369541731+c.upper)) = pointBounds15915 := by
 decide +kernel
def cuts15916 : List PrefixCut := [⟨38,249275940,249276100⟩,
⟨102,658530761,658531183⟩,
⟨128,826188173,826188706⟩]
theorem checked15916 : checkPrefixCuts (2^48) 2090074113 9 Manual.Count131072.C015916.packed 128 cuts15916 = true := by
 decide +kernel
def pointBounds15916 : List (Nat × Nat × Nat) := [(2090113024,97046062339677,97046440883347),(2090178560,97046471594498,97046850138430)]
theorem point_links_checked15916 : (cuts15916.take 2).map (fun c => (2090074113-1+2*2^9*c.k,97045813063737+c.lower,97046191607247+c.upper)) = pointBounds15916 := by
 decide +kernel
def cuts15917 : List PrefixCut := [⟨38,241315194,241315353⟩,
⟨102,653641420,653641847⟩,
⟨128,817652665,817653197⟩]
theorem checked15917 : checkPrefixCuts (2^48) 2090205185 9 Manual.Count131072.C015917.packed 128 cuts15917 = true := by
 decide +kernel
def pointBounds15917 : List (Nat × Nat × Nat) := [(2090244096,97046880567104,97047259111306),(2090309632,97047292893330,97047671437800)]
theorem point_links_checked15917 : (cuts15917.take 2).map (fun c => (2090205185-1+2*2^9*c.k,97046639251910+c.lower,97047017795953+c.upper)) = pointBounds15917 := by
 decide +kernel
def cuts15918 : List PrefixCut := [⟨38,246416911,246417072⟩,
⟨102,659929184,659929613⟩,
⟨128,825411249,825411787⟩]
theorem checked15918 : checkPrefixCuts (2^48) 2090336257 9 Manual.Count131072.C015918.packed 128 cuts15918 = true := by
 decide +kernel
def pointBounds15918 : List (Nat × Nat × Nat) := [(2090375168,97047703321486,97048081866222),(2090440704,97048116833759,97048495378763)]
theorem point_links_checked15918 : (cuts15918.take 2).map (fun c => (2090336257-1+2*2^9*c.k,97047456904575+c.lower,97047835449150+c.upper)) = pointBounds15918 := by
 decide +kernel
def cuts15919 : List PrefixCut := [⟨38,251248746,251248904⟩,
⟨102,662850127,662850554⟩,
⟨128,834380579,834381116⟩]
theorem checked15919 : checkPrefixCuts (2^48) 2090467329 9 Manual.Count131072.C015919.packed 128 cuts15919 = true := by
 decide +kernel
def pointBounds15919 : List (Nat × Nat × Nat) := [(2090506240,97048533564570,97048912109841),(2090571776,97048945165951,97049323711491)]
theorem point_links_checked15919 : (cuts15919.take 2).map (fun c => (2090467329-1+2*2^9*c.k,97048282315824+c.lower,97048660860937+c.upper)) = pointBounds15919 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000184
