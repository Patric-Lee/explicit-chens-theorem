import PlattAssemblyKernel
import PlattCertificates.Count131072.C027872
import PlattCertificates.Count131072.C027873
import PlattCertificates.Count131072.C027874
import PlattCertificates.Count131072.C027875
import PlattCertificates.Count131072.C027876
import PlattCertificates.Count131072.C027877
import PlattCertificates.Count131072.C027878
import PlattCertificates.Count131072.C027879
import PlattCertificates.Count131072.C027880
import PlattCertificates.Count131072.C027881
import PlattCertificates.Count131072.C027882
import PlattCertificates.Count131072.C027883
import PlattCertificates.Count131072.C027884
import PlattCertificates.Count131072.C027885
import PlattCertificates.Count131072.C027886
import PlattCertificates.Count131072.C027887
import PlattCertificates.Count131072.C027888
import PlattCertificates.Count131072.C027889
import PlattCertificates.Count131072.C027890
import PlattCertificates.Count131072.C027891
import PlattCertificates.Count131072.C027892
import PlattCertificates.Count131072.C027893
import PlattCertificates.Count131072.C027894
import PlattCertificates.Count131072.C027895
import PlattCertificates.Count131072.C027896
import PlattCertificates.Count131072.C027897
import PlattCertificates.Count131072.C027898
import PlattCertificates.Count131072.C027899
import PlattCertificates.Count131072.C027900
import PlattCertificates.Count131072.C027901
import PlattCertificates.Count131072.C027902
import PlattCertificates.Count131072.C027903
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000246
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27872 : List PrefixCut := [⟨12,43639194,43639219⟩,
⟨124,440156327,440156573⟩,
⟨128,452547287,452547539⟩]
theorem checked27872 : checkPrefixCuts (2^48) 3657170945 9 Manual.Count131072.C027872.packed 128 cuts27872 = true := by
 decide +kernel
def pointBounds27872 : List (Nat × Nat × Nat) := [(3657183232,104290098072244,104290480867985),(3657297920,104290494589377,104290877385339)]
theorem point_links_checked27872 : (cuts27872.take 2).map (fun c => (3657170945-1+2*2^9*c.k,104290054433050+c.lower,104290437228766+c.upper)) = pointBounds27872 := by
 decide +kernel
def cuts27873 : List PrefixCut := [⟨108,384344577,384344791⟩,
⟨128,456532967,456533219⟩]
theorem checked27873 : checkPrefixCuts (2^48) 3657302017 9 Manual.Count131072.C027873.packed 128 cuts27873 = true := by
 decide +kernel
def pointBounds27873 : List (Nat × Nat × Nat) := [(3657412608,104290891324914,104291274121096)]
theorem point_links_checked27873 : (cuts27873.take 1).map (fun c => (3657302017-1+2*2^9*c.k,104290506980337+c.lower,104290889776305+c.upper)) = pointBounds27873 := by
 decide +kernel
def cuts27874 : List PrefixCut := [⟨92,329075381,329075564⟩,
⟨128,457594082,457594339⟩]
theorem checked27874 : checkPrefixCuts (2^48) 3657433089 9 Manual.Count131072.C027874.packed 128 cuts27874 = true := by
 decide +kernel
def pointBounds27874 : List (Nat × Nat × Nat) := [(3657527296,104291292588685,104291675385088)]
theorem point_links_checked27874 : (cuts27874.take 1).map (fun c => (3657433089-1+2*2^9*c.k,104290963513304+c.lower,104291346309524+c.upper)) = pointBounds27874 := by
 decide +kernel
def cuts27875 : List PrefixCut := [⟨76,268884635,268884786⟩,
⟨128,454807280,454807540⟩]
theorem checked27875 : checkPrefixCuts (2^48) 3657564161 9 Manual.Count131072.C027875.packed 128 cuts27875 = true := by
 decide +kernel
def pointBounds27875 : List (Nat × Nat × Nat) := [(3657641984,104291689992021,104292072788649)]
theorem point_links_checked27875 : (cuts27875.take 1).map (fun c => (3657564161-1+2*2^9*c.k,104291421107386+c.lower,104291803903863+c.upper)) = pointBounds27875 := by
 decide +kernel
def cuts27876 : List PrefixCut := [⟨60,220548810,220548931⟩,
⟨128,463871479,463871738⟩]
theorem checked27876 : checkPrefixCuts (2^48) 3657695233 9 Manual.Count131072.C027876.packed 128 cuts27876 = true := by
 decide +kernel
def pointBounds27876 : List (Nat × Nat × Nat) := [(3657756672,104292096463476,104292479260334)]
theorem point_links_checked27876 : (cuts27876.take 1).map (fun c => (3657695233-1+2*2^9*c.k,104291875914666+c.lower,104292258711403+c.upper)) = pointBounds27876 := by
 decide +kernel
def cuts27877 : List PrefixCut := [⟨44,158057226,158057318⟩,
⟨128,453389594,453389854⟩]
theorem checked27877 : checkPrefixCuts (2^48) 3657826305 9 Manual.Count131072.C027877.packed 128 cuts27877 = true := by
 decide +kernel
def pointBounds27877 : List (Nat × Nat × Nat) := [(3657871360,104292497843371,104292880640459)]
theorem point_links_checked27877 : (cuts27877.take 1).map (fun c => (3657826305-1+2*2^9*c.k,104292339786145+c.lower,104292722583141+c.upper)) = pointBounds27877 := by
 decide +kernel
def cuts27878 : List PrefixCut := [⟨28,96262384,96262443⟩,
⟨128,452065158,452065419⟩]
theorem checked27878 : checkPrefixCuts (2^48) 3657957377 9 Manual.Count131072.C027878.packed 128 cuts27878 = true := by
 decide +kernel
def pointBounds27878 : List (Nat × Nat × Nat) := [(3657986048,104292889438123,104293272235438)]
theorem point_links_checked27878 : (cuts27878.take 1).map (fun c => (3657957377-1+2*2^9*c.k,104292793175739+c.lower,104293175972995+c.upper)) = pointBounds27878 := by
 decide +kernel
def cuts27879 : List PrefixCut := [⟨12,42243227,42243251⟩,
⟨124,448663724,448663977⟩,
⟨128,463129042,463129302⟩]
theorem checked27879 : checkPrefixCuts (2^48) 3658088449 9 Manual.Count131072.C027879.packed 128 cuts27879 = true := by
 decide +kernel
def pointBounds27879 : List (Nat × Nat × Nat) := [(3658100736,104293287484124,104293670281665),(3658215424,104293693904621,104294076702391)]
theorem point_links_checked27879 : (cuts27879.take 2).map (fun c => (3658088449-1+2*2^9*c.k,104293245240897+c.lower,104293628038414+c.upper)) = pointBounds27879 := by
 decide +kernel
def cuts27880 : List PrefixCut := [⟨108,391326851,391327070⟩,
⟨128,463266316,463266574⟩]
theorem checked27880 : checkPrefixCuts (2^48) 3658219521 9 Manual.Count131072.C027880.packed 128 cuts27880 = true := by
 decide +kernel
def pointBounds27880 : List (Nat × Nat × Nat) := [(3658330112,104294099696790,104294482494786)]
theorem point_links_checked27880 : (cuts27880.take 1).map (fun c => (3658219521-1+2*2^9*c.k,104293708369939+c.lower,104294091167716+c.upper)) = pointBounds27880 := by
 decide +kernel
def cuts27881 : List PrefixCut := [⟨92,332378172,332378360⟩,
⟨128,456709995,456710253⟩]
theorem checked27881 : checkPrefixCuts (2^48) 3658350593 9 Manual.Count131072.C027881.packed 128 cuts27881 = true := by
 decide +kernel
def pointBounds27881 : List (Nat × Nat × Nat) := [(3658444800,104294504014427,104294886812650)]
theorem point_links_checked27881 : (cuts27881.take 1).map (fun c => (3658350593-1+2*2^9*c.k,104294171636255+c.lower,104294554434290+c.upper)) = pointBounds27881 := by
 decide +kernel
def cuts27882 : List PrefixCut := [⟨76,276895588,276895741⟩,
⟨128,461848371,461848628⟩]
theorem checked27882 : checkPrefixCuts (2^48) 3658481665 9 Manual.Count131072.C027882.packed 128 cuts27882 = true := by
 decide +kernel
def pointBounds27882 : List (Nat × Nat × Nat) := [(3658559488,104294905241838,104295288040284)]
theorem point_links_checked27882 : (cuts27882.take 1).map (fun c => (3658481665-1+2*2^9*c.k,104294628346250+c.lower,104295011144543+c.upper)) = pointBounds27882 := by
 decide +kernel
def cuts27883 : List PrefixCut := [⟨60,218262378,218262500⟩,
⟨128,462985744,462986001⟩]
theorem checked27883 : checkPrefixCuts (2^48) 3658612737 9 Manual.Count131072.C027883.packed 128 cuts27883 = true := by
 decide +kernel
def pointBounds27883 : List (Nat × Nat × Nat) := [(3658674176,104295308456999,104295691255671)]
theorem point_links_checked27883 : (cuts27883.take 1).map (fun c => (3658612737-1+2*2^9*c.k,104295090194621+c.lower,104295472993171+c.upper)) = pointBounds27883 := by
 decide +kernel
def cuts27884 : List PrefixCut := [⟨44,155401914,155402002⟩,
⟨128,452660447,452660704⟩]
theorem checked27884 : checkPrefixCuts (2^48) 3658743809 9 Manual.Count131072.C027884.packed 128 cuts27884 = true := by
 decide +kernel
def pointBounds27884 : List (Nat × Nat × Nat) := [(3658788864,104295708582279,104296091381174)]
theorem point_links_checked27884 : (cuts27884.take 1).map (fun c => (3658743809-1+2*2^9*c.k,104295553180365+c.lower,104295935979172+c.upper)) = pointBounds27884 := by
 decide +kernel
def cuts27885 : List PrefixCut := [⟨28,99546205,99546263⟩,
⟨128,453182786,453183040⟩]
theorem checked27885 : checkPrefixCuts (2^48) 3658874881 9 Manual.Count131072.C027885.packed 128 cuts27885 = true := by
 decide +kernel
def pointBounds27885 : List (Nat × Nat × Nat) := [(3658903552,104296105387017,104296488186139)]
theorem point_links_checked27885 : (cuts27885.take 1).map (fun c => (3658874881-1+2*2^9*c.k,104296005840812+c.lower,104296388639876+c.upper)) = pointBounds27885 := by
 decide +kernel
def cuts27886 : List PrefixCut := [⟨12,44001945,44001970⟩,
⟨124,445551128,445551374⟩,
⟨128,458012799,458013052⟩]
theorem checked27886 : checkPrefixCuts (2^48) 3659005953 9 Manual.Count131072.C027886.packed 128 cuts27886 = true := by
 decide +kernel
def pointBounds27886 : List (Nat × Nat × Nat) := [(3659018240,104296503025543,104296885824886),(3659132928,104296904574726,104297287374290)]
theorem point_links_checked27886 : (cuts27886.take 2).map (fun c => (3659005953-1+2*2^9*c.k,104296459023598+c.lower,104296841822916+c.upper)) = pointBounds27886 := by
 decide +kernel
def cuts27887 : List PrefixCut := [⟨108,385767306,385767522⟩,
⟨128,457150274,457150531⟩]
theorem checked27887 : checkPrefixCuts (2^48) 3659137025 9 Manual.Count131072.C027887.packed 128 cuts27887 = true := by
 decide +kernel
def pointBounds27887 : List (Nat × Nat × Nat) := [(3659247616,104297302803703,104297685603490)]
theorem point_links_checked27887 : (cuts27887.take 1).map (fun c => (3659137025-1+2*2^9*c.k,104296917036397+c.lower,104297299835968+c.upper)) = pointBounds27887 := by
 decide +kernel
def cuts27888 : List PrefixCut := [⟨92,331525654,331525839⟩,
⟨128,459364576,459364834⟩]
theorem checked27888 : checkPrefixCuts (2^48) 3659268097 9 Manual.Count131072.C027888.packed 128 cuts27888 = true := by
 decide +kernel
def pointBounds27888 : List (Nat × Nat × Nat) := [(3659362304,104297705712325,104298088512338)]
theorem point_links_checked27888 : (cuts27888.take 1).map (fun c => (3659268097-1+2*2^9*c.k,104297374186671+c.lower,104297756986499+c.upper)) = pointBounds27888 := by
 decide +kernel
def cuts27889 : List PrefixCut := [⟨76,270903473,270903632⟩,
⟨128,453963896,453964160⟩]
theorem checked27889 : checkPrefixCuts (2^48) 3659399169 9 Manual.Count131072.C027889.packed 128 cuts27889 = true := by
 decide +kernel
def pointBounds27889 : List (Nat × Nat × Nat) := [(3659476992,104298104454720,104298487254965)]
theorem point_links_checked27889 : (cuts27889.take 1).map (fun c => (3659399169-1+2*2^9*c.k,104297833551247+c.lower,104298216351333+c.upper)) = pointBounds27889 := by
 decide +kernel
def cuts27890 : List PrefixCut := [⟨60,213438969,213439091⟩,
⟨128,462254328,462254587⟩]
theorem checked27890 : checkPrefixCuts (2^48) 3659530241 9 Manual.Count131072.C027890.packed 128 cuts27890 = true := by
 decide +kernel
def pointBounds27890 : List (Nat × Nat × Nat) := [(3659591680,104298500954112,104298883754584)]
theorem point_links_checked27890 : (cuts27890.take 1).map (fun c => (3659530241-1+2*2^9*c.k,104298287515143+c.lower,104298670315493+c.upper)) = pointBounds27890 := by
 decide +kernel
def cuts27891 : List PrefixCut := [⟨44,155901335,155901423⟩,
⟨128,453008436,453008693⟩]
theorem checked27891 : checkPrefixCuts (2^48) 3659661313 9 Manual.Count131072.C027891.packed 128 cuts27891 = true := by
 decide +kernel
def pointBounds27891 : List (Nat × Nat × Nat) := [(3659706368,104298905670806,104299288471503)]
theorem point_links_checked27891 : (cuts27891.take 1).map (fun c => (3659661313-1+2*2^9*c.k,104298749769471+c.lower,104299132570080+c.upper)) = pointBounds27891 := by
 decide +kernel
def cuts27892 : List PrefixCut := [⟨28,99675068,99675124⟩,
⟨128,458375798,458376052⟩]
theorem checked27892 : checkPrefixCuts (2^48) 3659792385 9 Manual.Count131072.C027892.packed 128 cuts27892 = true := by
 decide +kernel
def pointBounds27892 : List (Nat × Nat × Nat) := [(3659821056,104299302452975,104299685253897)]
theorem point_links_checked27892 : (cuts27892.take 1).map (fun c => (3659792385-1+2*2^9*c.k,104299202777907+c.lower,104299585578773+c.upper)) = pointBounds27892 := by
 decide +kernel
def cuts27893 : List PrefixCut := [⟨12,44683078,44683103⟩,
⟨124,440901973,440902224⟩,
⟨128,455129325,455129584⟩]
theorem checked27893 : checkPrefixCuts (2^48) 3659923457 9 Manual.Count131072.C027893.packed 128 cuts27893 = true := by
 decide +kernel
def pointBounds27893 : List (Nat × Nat × Nat) := [(3659935744,104299705836783,104300088637928),(3660050432,104300102055678,104300484857049)]
theorem point_links_checked27893 : (cuts27893.take 2).map (fun c => (3659923457-1+2*2^9*c.k,104299661153705+c.lower,104300043954825+c.upper)) = pointBounds27893 := by
 decide +kernel
def cuts27894 : List PrefixCut := [⟨108,388208355,388208571⟩,
⟨128,457573985,457574241⟩]
theorem checked27894 : checkPrefixCuts (2^48) 3660054529 9 Manual.Count131072.C027894.packed 128 cuts27894 = true := by
 decide +kernel
def pointBounds27894 : List (Nat × Nat × Nat) := [(3660165120,104300504491385,104300887292980)]
theorem point_links_checked27894 : (cuts27894.take 1).map (fun c => (3660054529-1+2*2^9*c.k,104300116283030+c.lower,104300499084409+c.upper)) = pointBounds27894 := by
 decide +kernel
def cuts27895 : List PrefixCut := [⟨92,327213001,327213192⟩,
⟨128,455788874,455789139⟩]
theorem checked27895 : checkPrefixCuts (2^48) 3660185601 9 Manual.Count131072.C027895.packed 128 cuts27895 = true := by
 decide +kernel
def pointBounds27895 : List (Nat × Nat × Nat) := [(3660279808,104300901070016,104301283871842)]
theorem point_links_checked27895 : (cuts27895.take 1).map (fun c => (3660185601-1+2*2^9*c.k,104300573857015+c.lower,104300956658650+c.upper)) = pointBounds27895 := by
 decide +kernel
def cuts27896 : List PrefixCut := [⟨76,272988762,272988913⟩,
⟨128,458002615,458002871⟩]
theorem checked27896 : checkPrefixCuts (2^48) 3660316673 9 Manual.Count131072.C027896.packed 128 cuts27896 = true := by
 decide +kernel
def pointBounds27896 : List (Nat × Nat × Nat) := [(3660394496,104301302634651,104301685436702)]
theorem point_links_checked27896 : (cuts27896.take 1).map (fun c => (3660316673-1+2*2^9*c.k,104301029645889+c.lower,104301412447789+c.upper)) = pointBounds27896 := by
 decide +kernel
def cuts27897 : List PrefixCut := [⟨60,210002061,210002182⟩,
⟨128,455371691,455371948⟩]
theorem checked27897 : checkPrefixCuts (2^48) 3660447745 9 Manual.Count131072.C027897.packed 128 cuts27897 = true := by
 decide +kernel
def pointBounds27897 : List (Nat × Nat × Nat) := [(3660509184,104301697650565,104302080452842)]
theorem point_links_checked27897 : (cuts27897.take 1).map (fun c => (3660447745-1+2*2^9*c.k,104301487648504+c.lower,104301870450660+c.upper)) = pointBounds27897 := by
 decide +kernel
def cuts27898 : List PrefixCut := [⟨44,157861494,157861581⟩,
⟨128,459815220,459815476⟩]
theorem checked27898 : checkPrefixCuts (2^48) 3660578817 9 Manual.Count131072.C027898.packed 128 cuts27898 = true := by
 decide +kernel
def pointBounds27898 : List (Nat × Nat × Nat) := [(3660623872,104302100881689,104302483684189)]
theorem point_links_checked27898 : (cuts27898.take 1).map (fun c => (3660578817-1+2*2^9*c.k,104301943020195+c.lower,104302325822608+c.upper)) = pointBounds27898 := by
 decide +kernel
def cuts27899 : List PrefixCut := [⟨28,97189585,97189637⟩,
⟨128,456799968,456800222⟩]
theorem checked27899 : checkPrefixCuts (2^48) 3660709889 9 Manual.Count131072.C027899.packed 128 cuts27899 = true := by
 decide +kernel
def pointBounds27899 : List (Nat × Nat × Nat) := [(3660738560,104302500025000,104302882827721)]
theorem point_links_checked27899 : (cuts27899.take 1).map (fun c => (3660709889-1+2*2^9*c.k,104302402835415+c.lower,104302785638084+c.upper)) = pointBounds27899 := by
 decide +kernel
def cuts27900 : List PrefixCut := [⟨12,44210554,44210577⟩,
⟨124,443636331,443636580⟩,
⟨128,459551595,459551852⟩]
theorem checked27900 : checkPrefixCuts (2^48) 3660840961 9 Manual.Count131072.C027900.packed 128 cuts27900 = true := by
 decide +kernel
def pointBounds27900 : List (Nat × Nat × Nat) := [(3660853248,104302903845937,104303286648883),(3660967936,104303303271714,104303686074886)]
theorem point_links_checked27900 : (cuts27900.take 2).map (fun c => (3660840961-1+2*2^9*c.k,104302859635383+c.lower,104303242438306+c.upper)) = pointBounds27900 := by
 decide +kernel
def cuts27901 : List PrefixCut := [⟨108,379115613,379115827⟩,
⟨128,449309566,449309820⟩]
theorem checked27901 : checkPrefixCuts (2^48) 3660972033 9 Manual.Count131072.C027901.packed 128 cuts27901 = true := by
 decide +kernel
def pointBounds27901 : List (Nat × Nat × Nat) := [(3661082624,104303698302591,104304081105985)]
theorem point_links_checked27901 : (cuts27901.take 1).map (fun c => (3660972033-1+2*2^9*c.k,104303319186978+c.lower,104303701990158+c.upper)) = pointBounds27901 := by
 decide +kernel
def cuts27902 : List PrefixCut := [⟨92,327515347,327515531⟩,
⟨128,456135885,456136141⟩]
theorem checked27902 : checkPrefixCuts (2^48) 3661103105 9 Manual.Count131072.C027902.packed 128 cuts27902 = true := by
 decide +kernel
def pointBounds27902 : List (Nat × Nat × Nat) := [(3661197312,104304096011891,104304478815509)]
theorem point_links_checked27902 : (cuts27902.take 1).map (fun c => (3661103105-1+2*2^9*c.k,104303768496544+c.lower,104304151299978+c.upper)) = pointBounds27902 := by
 decide +kernel
def cuts27903 : List PrefixCut := [⟨76,275534228,275534386⟩,
⟨128,462039249,462039508⟩]
theorem checked27903 : checkPrefixCuts (2^48) 3661234177 9 Manual.Count131072.C027903.packed 128 cuts27903 = true := by
 decide +kernel
def pointBounds27903 : List (Nat × Nat × Nat) := [(3661312000,104304500166657,104304882970505)]
theorem point_links_checked27903 : (cuts27903.take 1).map (fun c => (3661234177-1+2*2^9*c.k,104304224632429+c.lower,104304607436119+c.upper)) = pointBounds27903 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000246
