import PlattAssemblyKernel
import PlattCertificates.Count131072.C018032
import PlattCertificates.Count131072.C018033
import PlattCertificates.Count131072.C018034
import PlattCertificates.Count131072.C018035
import PlattCertificates.Count131072.C018036
import PlattCertificates.Count131072.C018037
import PlattCertificates.Count131072.C018038
import PlattCertificates.Count131072.C018039
import PlattCertificates.Count131072.C018040
import PlattCertificates.Count131072.C018041
import PlattCertificates.Count131072.C018042
import PlattCertificates.Count131072.C018043
import PlattCertificates.Count131072.C018044
import PlattCertificates.Count131072.C018045
import PlattCertificates.Count131072.C018046
import PlattCertificates.Count131072.C018047
import PlattCertificates.Count131072.C018048
import PlattCertificates.Count131072.C018049
import PlattCertificates.Count131072.C018050
import PlattCertificates.Count131072.C018051
import PlattCertificates.Count131072.C018052
import PlattCertificates.Count131072.C018053
import PlattCertificates.Count131072.C018054
import PlattCertificates.Count131072.C018055
import PlattCertificates.Count131072.C018056
import PlattCertificates.Count131072.C018057
import PlattCertificates.Count131072.C018058
import PlattCertificates.Count131072.C018059
import PlattCertificates.Count131072.C018060
import PlattCertificates.Count131072.C018061
import PlattCertificates.Count131072.C018062
import PlattCertificates.Count131072.C018063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000251
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18032 : List PrefixCut := [⟨24,136134154,136134237⟩,
⟨97,549046012,549046344⟩,
⟨128,728212180,728212619⟩]
theorem checked18032 : checkPrefixCuts (2^48) 2367422465 9 Manual.Count131072.C018032.packed 128 cuts18032 = true := by
 decide +kernel
def pointBounds18032 : List (Nat × Nat × Nat) := [(2367447040,98675492652159,98675872216905),(2367521792,98675905564017,98676285129012)]
theorem point_links_checked18032 : (cuts18032.take 2).map (fun c => (2367422465-1+2*2^9*c.k,98675356518005+c.lower,98675736082668+c.upper)) = pointBounds18032 := by
 decide +kernel
def cuts18033 : List PrefixCut := [⟨42,239677052,239677200⟩,
⟨115,651849451,651849849⟩,
⟨128,726269743,726270186⟩]
theorem checked18033 : checkPrefixCuts (2^48) 2367553537 9 Manual.Count131072.C018033.packed 128 cuts18033 = true := by
 decide +kernel
def pointBounds18033 : List (Nat × Nat × Nat) := [(2367596544,98676324407237,98676703972487),(2367671296,98676736579636,98677116145136)]
theorem point_links_checked18033 : (cuts18033.take 2).map (fun c => (2367553537-1+2*2^9*c.k,98676084730185+c.lower,98676464295287+c.upper)) = pointBounds18033 := by
 decide +kernel
def cuts18034 : List PrefixCut := [⟨60,336907034,336907240⟩,
⟨128,725159601,725160042⟩]
theorem checked18034 : checkPrefixCuts (2^48) 2367684609 9 Manual.Count131072.C018034.packed 128 cuts18034 = true := by
 decide +kernel
def pointBounds18034 : List (Nat × Nat × Nat) := [(2367746048,98677147906962,98677527472713)]
theorem point_links_checked18034 : (cuts18034.take 1).map (fun c => (2367684609-1+2*2^9*c.k,98676810999928+c.lower,98677190565473+c.upper)) = pointBounds18034 := by
 decide +kernel
def cuts18035 : List PrefixCut := [⟨5,30432054,30432071⟩,
⟨78,437810525,437810791⟩,
⟨128,723217527,723217968⟩]
theorem checked18035 : checkPrefixCuts (2^48) 2367815681 9 Manual.Count131072.C018035.packed 128 cuts18035 = true := by
 decide +kernel
def pointBounds18035 : List (Nat × Nat × Nat) := [(2367820800,98677566591583,98677946157586),(2367895552,98677973970054,98678353536306)]
theorem point_links_checked18035 : (cuts18035.take 2).map (fun c => (2367815681-1+2*2^9*c.k,98677536159529+c.lower,98677915725515+c.upper)) = pointBounds18035 := by
 decide +kernel
def cuts18036 : List PrefixCut := [⟨23,131824788,131824870⟩,
⟨96,541436015,541436349⟩,
⟨128,725554833,725555280⟩]
theorem checked18036 : checkPrefixCuts (2^48) 2367946753 9 Manual.Count131072.C018036.packed 128 cuts18036 = true := by
 decide +kernel
def pointBounds18036 : List (Nat × Nat × Nat) := [(2367970304,98678391201844,98678770768353),(2368045056,98678800813071,98679180379832)]
theorem point_links_checked18036 : (cuts18036.take 2).map (fun c => (2367946753-1+2*2^9*c.k,98678259377056+c.lower,98678638943483+c.upper)) = pointBounds18036 := by
 decide +kernel
def cuts18037 : List PrefixCut := [⟨41,229401936,229402081⟩,
⟨114,645999924,646000318⟩,
⟨128,727297399,727297841⟩]
theorem checked18037 : checkPrefixCuts (2^48) 2368077825 9 Manual.Count131072.C018037.packed 128 cuts18037 = true := by
 decide +kernel
def pointBounds18037 : List (Nat × Nat × Nat) := [(2368119808,98679214333825,98679593900844),(2368194560,98679630931813,98680010499081)]
theorem point_links_checked18037 : (cuts18037.take 2).map (fun c => (2368077825-1+2*2^9*c.k,98678984931889+c.lower,98679364498763+c.upper)) = pointBounds18037 := by
 decide +kernel
def cuts18038 : List PrefixCut := [⟨59,335525056,335525259⟩,
⟨128,720245076,720245506⟩]
theorem checked18038 : checkPrefixCuts (2^48) 2368208897 9 Manual.Count131072.C018038.packed 128 cuts18038 = true := by
 decide +kernel
def pointBounds18038 : List (Nat × Nat × Nat) := [(2368269312,98680047754344,98680427321863)]
theorem point_links_checked18038 : (cuts18038.take 1).map (fun c => (2368208897-1+2*2^9*c.k,98679712229288+c.lower,98680091796604+c.upper)) = pointBounds18038 := by
 decide +kernel
def cuts18039 : List PrefixCut := [⟨4,23294388,23294401⟩,
⟨77,430464036,430464300⟩,
⟨128,719610866,719611307⟩]
theorem checked18039 : checkPrefixCuts (2^48) 2368339969 9 Manual.Count131072.C018039.packed 128 cuts18039 = true := by
 decide +kernel
def pointBounds18039 : List (Nat × Nat × Nat) := [(2368344064,98680455768752,98680835336511),(2368418816,98680862938400,98681242506410)]
theorem point_links_checked18039 : (cuts18039.take 2).map (fun c => (2368339969-1+2*2^9*c.k,98680432474364+c.lower,98680812042110+c.upper)) = pointBounds18039 := by
 decide +kernel
def cuts18040 : List PrefixCut := [⟨22,120743355,120743432⟩,
⟨95,534542360,534542691⟩,
⟨128,717907416,717907859⟩]
theorem checked18040 : checkPrefixCuts (2^48) 2368471041 9 Manual.Count131072.C018040.packed 128 cuts18040 = true := by
 decide +kernel
def pointBounds18040 : List (Nat × Nat × Nat) := [(2368493568,98681272828585,98681652396849),(2368568320,98681686627590,98682066196108)]
theorem point_links_checked18040 : (cuts18040.take 2).map (fun c => (2368471041-1+2*2^9*c.k,98681152085230+c.lower,98681531653417+c.upper)) = pointBounds18040 := by
 decide +kernel
def cuts18041 : List PrefixCut := [⟨40,233629318,233629458⟩,
⟨113,647877382,647877766⟩,
⟨128,731771128,731771564⟩]
theorem checked18041 : checkPrefixCuts (2^48) 2368602113 9 Manual.Count131072.C018041.packed 128 cuts18041 = true := by
 decide +kernel
def pointBounds18041 : List (Nat × Nat × Nat) := [(2368643072,98682103621964,98682483190734),(2368717824,98682517870028,98682897439042)]
theorem point_links_checked18041 : (cuts18041.take 2).map (fun c => (2368602113-1+2*2^9*c.k,98681869992646+c.lower,98682249561276+c.upper)) = pointBounds18041 := by
 decide +kernel
def cuts18042 : List PrefixCut := [⟨58,329747124,329747324⟩,
⟨128,727809199,727809635⟩]
theorem checked18042 : checkPrefixCuts (2^48) 2368733185 9 Manual.Count131072.C018042.packed 128 cuts18042 = true := by
 decide +kernel
def pointBounds18042 : List (Nat × Nat × Nat) := [(2368792576,98682931510898,98683311080164)]
theorem point_links_checked18042 : (cuts18042.take 1).map (fun c => (2368733185-1+2*2^9*c.k,98682601763774+c.lower,98682981332840+c.upper)) = pointBounds18042 := by
 decide +kernel
def cuts18043 : List PrefixCut := [⟨3,15446943,15446952⟩,
⟨76,424784260,424784525⟩,
⟨128,710065051,710065493⟩]
theorem checked18043 : checkPrefixCuts (2^48) 2368864257 9 Manual.Count131072.C018043.packed 128 cuts18043 = true := by
 decide +kernel
def pointBounds18043 : List (Nat × Nat × Nat) := [(2368867328,98683345019916,98683724589427),(2368942080,98683754357233,98684133927000)]
theorem point_links_checked18043 : (cuts18043.take 2).map (fun c => (2368864257-1+2*2^9*c.k,98683329572973+c.lower,98683709142475+c.upper)) = pointBounds18043 := by
 decide +kernel
def cuts18044 : List PrefixCut := [⟨21,118815609,118815682⟩,
⟨94,530859734,530860056⟩,
⟨128,719411910,719412347⟩]
theorem checked18044 : checkPrefixCuts (2^48) 2368995329 9 Manual.Count131072.C018044.packed 128 cuts18044 = true := by
 decide +kernel
def pointBounds18044 : List (Nat × Nat × Nat) := [(2369016832,98684158453633,98684538023650),(2369091584,98684570497758,98684950068024)]
theorem point_links_checked18044 : (cuts18044.take 2).map (fun c => (2368995329-1+2*2^9*c.k,98684039638024+c.lower,98684419207968+c.upper)) = pointBounds18044 := by
 decide +kernel
def cuts18045 : List PrefixCut := [⟨39,223003678,223003811⟩,
⟨112,640249292,640249678⟩,
⟨128,726262955,726263392⟩]
theorem checked18045 : checkPrefixCuts (2^48) 2369126401 9 Manual.Count131072.C018045.packed 128 cuts18045 = true := by
 decide +kernel
def pointBounds18045 : List (Nat × Nat × Nat) := [(2369166336,98684982053612,98685361624126),(2369241088,98685399299226,98685778869993)]
theorem point_links_checked18045 : (cuts18045.take 2).map (fun c => (2369126401-1+2*2^9*c.k,98684759049934+c.lower,98685138620315+c.upper)) = pointBounds18045 := by
 decide +kernel
def cuts18046 : List PrefixCut := [⟨57,320051368,320051565⟩,
⟨128,721945837,721946280⟩]
theorem checked18046 : checkPrefixCuts (2^48) 2369257473 9 Manual.Count131072.C018046.packed 128 cuts18046 = true := by
 decide +kernel
def pointBounds18046 : List (Nat × Nat × Nat) := [(2369315840,98685805364257,98686184935272)]
theorem point_links_checked18046 : (cuts18046.take 1).map (fun c => (2369257473-1+2*2^9*c.k,98685485312889+c.lower,98685864883707+c.upper)) = pointBounds18046 := by
 decide +kernel
def cuts18047 : List PrefixCut := [⟨2,12830009,12830016⟩,
⟨75,423858766,423859026⟩,
⟨128,722143533,722143971⟩]
theorem checked18047 : checkPrefixCuts (2^48) 2369388545 9 Manual.Count131072.C018047.packed 128 cuts18047 = true := by
 decide +kernel
def pointBounds18047 : List (Nat × Nat × Nat) := [(2369390592,98686220088735,98686599660003),(2369465344,98686631117492,98687010689013)]
theorem point_links_checked18047 : (cuts18047.take 2).map (fun c => (2369388545-1+2*2^9*c.k,98686207258726+c.lower,98686586829987+c.upper)) = pointBounds18047 := by
 decide +kernel
def cuts18048 : List PrefixCut := [⟨20,114156553,114156624⟩,
⟨93,519813906,519814227⟩,
⟨128,712481846,712482286⟩]
theorem checked18048 : checkPrefixCuts (2^48) 2369519617 9 Manual.Count131072.C018048.packed 128 cuts18048 = true := by
 decide +kernel
def pointBounds18048 : List (Nat × Nat × Nat) := [(2369540096,98687043558812,98687423130582),(2369614848,98687449216165,98687828788185)]
theorem point_links_checked18048 : (cuts18048.take 2).map (fun c => (2369519617-1+2*2^9*c.k,98686929402259+c.lower,98687308973958+c.upper)) = pointBounds18048 := by
 decide +kernel
def cuts18049 : List PrefixCut := [⟨38,219153337,219153467⟩,
⟨111,635712926,635713307⟩,
⟨128,727290118,727290556⟩]
theorem checked18049 : checkPrefixCuts (2^48) 2369650689 9 Manual.Count131072.C018049.packed 128 cuts18049 = true := by
 decide +kernel
def pointBounds18049 : List (Nat × Nat × Nat) := [(2369689600,98687861037442,98688240609711),(2369764352,98688277597031,98688657169551)]
theorem point_links_checked18049 : (cuts18049.take 2).map (fun c => (2369650689-1+2*2^9*c.k,98687641884105+c.lower,98688021456244+c.upper)) = pointBounds18049 := by
 decide +kernel
def cuts18050 : List PrefixCut := [⟨56,314992063,314992259⟩,
⟨128,722855191,722855633⟩]
theorem checked18050 : checkPrefixCuts (2^48) 2369781761 9 Manual.Count131072.C018050.packed 128 cuts18050 = true := by
 decide +kernel
def pointBounds18050 : List (Nat × Nat × Nat) := [(2369839104,98688684166286,98689063739059)]
theorem point_links_checked18050 : (cuts18050.take 1).map (fun c => (2369781761-1+2*2^9*c.k,98688369174223+c.lower,98688748746800+c.upper)) = pointBounds18050 := by
 decide +kernel
def cuts18051 : List PrefixCut := [⟨1,6532357,6532360⟩,
⟨74,416876551,416876799⟩,
⟨128,718420800,718421229⟩]
theorem checked18051 : checkPrefixCuts (2^48) 2369912833 9 Manual.Count131072.C018051.packed 128 cuts18051 = true := by
 decide +kernel
def pointBounds18051 : List (Nat × Nat × Nat) := [(2369913856,98689098561771,98689478134793),(2369988608,98689508905965,98689888479232)]
theorem point_links_checked18051 : (cuts18051.take 2).map (fun c => (2369912833-1+2*2^9*c.k,98689092029414+c.lower,98689471602433+c.upper)) = pointBounds18051 := by
 decide +kernel
def cuts18052 : List PrefixCut := [⟨19,104511523,104511587⟩,
⟨92,527180931,527181249⟩,
⟨128,726337966,726338405⟩]
theorem checked18052 : checkPrefixCuts (2^48) 2370043905 9 Manual.Count131072.C018052.packed 128 cuts18052 = true := by
 decide +kernel
def pointBounds18052 : List (Nat × Nat × Nat) := [(2370063360,98689914961737,98690294535249),(2370138112,98690337631145,98690717204911)]
theorem point_links_checked18052 : (cuts18052.take 2).map (fun c => (2370043905-1+2*2^9*c.k,98689810450214+c.lower,98690190023662+c.upper)) = pointBounds18052 := by
 decide +kernel
def cuts18053 : List PrefixCut := [⟨37,210910783,210910912⟩,
⟨110,617046842,617047227⟩,
⟨128,721191377,721191824⟩]
theorem checked18053 : checkPrefixCuts (2^48) 2370174977 9 Manual.Count131072.C018053.packed 128 cuts18053 = true := by
 decide +kernel
def pointBounds18053 : List (Nat × Nat × Nat) := [(2370212864,98690747698963,98691127272979),(2370287616,98691153835022,98691533409294)]
theorem point_links_checked18053 : (cuts18053.take 2).map (fun c => (2370174977-1+2*2^9*c.k,98690536788180+c.lower,98690916362067+c.upper)) = pointBounds18053 := by
 decide +kernel
def cuts18054 : List PrefixCut := [⟨55,311241166,311241355⟩,
⟨128,722695172,722695609⟩]
theorem checked18054 : checkPrefixCuts (2^48) 2370306049 9 Manual.Count131072.C018054.packed 128 cuts18054 = true := by
 decide +kernel
def pointBounds18054 : List (Nat × Nat × Nat) := [(2370362368,98691569220723,98691948795246),(2370437120,98691980674729,98692360249500)]
theorem point_links_checked18054 : (cuts18054.take 2).map (fun c => (2370306049-1+2*2^9*c.k,98691257979557+c.lower,98691637553891+c.upper)) = pointBounds18054 := by
 decide +kernel
def cuts18055 : List PrefixCut := [⟨73,416903143,416903400⟩,
⟨128,729779704,729780153⟩]
theorem checked18055 : checkPrefixCuts (2^48) 2370437121 9 Manual.Count131072.C018055.packed 128 cuts18055 = true := by
 decide +kernel
def pointBounds18055 : List (Nat × Nat × Nat) := [(2370511872,98692397577872,98692777152900)]
theorem point_links_checked18055 : (cuts18055.take 1).map (fun c => (2370437121-1+2*2^9*c.k,98691980674729+c.lower,98692360249500+c.upper)) = pointBounds18055 := by
 decide +kernel
def cuts18056 : List PrefixCut := [⟨18,100807579,100807639⟩,
⟨91,512935160,512935471⟩,
⟨128,712523134,712523566⟩]
theorem checked18056 : checkPrefixCuts (2^48) 2370568193 9 Manual.Count131072.C018056.packed 128 cuts18056 = true := by
 decide +kernel
def pointBounds18056 : List (Nat × Nat × Nat) := [(2370586624,98692811262012,98693190837292),(2370661376,98693223389593,98693602965124)]
theorem point_links_checked18056 : (cuts18056.take 2).map (fun c => (2370568193-1+2*2^9*c.k,98692710454433+c.lower,98693090029653+c.upper)) = pointBounds18056 := by
 decide +kernel
def cuts18057 : List PrefixCut := [⟨36,198872444,198872567⟩,
⟨109,605749941,605750316⟩,
⟨128,716757520,716757962⟩]
theorem checked18057 : checkPrefixCuts (2^48) 2370699265 9 Manual.Count131072.C018057.packed 128 cuts18057 = true := by
 decide +kernel
def pointBounds18057 : List (Nat × Nat × Nat) := [(2370736128,98693621850011,98694001425786),(2370810880,98694028727508,98694408303535)]
theorem point_links_checked18057 : (cuts18057.take 2).map (fun c => (2370699265-1+2*2^9*c.k,98693422977567+c.lower,98693802553219+c.upper)) = pointBounds18057 := by
 decide +kernel
def cuts18058 : List PrefixCut := [⟨54,305473765,305473946⟩,
⟨127,713275433,713275863⟩,
⟨128,718142856,718143289⟩]
theorem checked18058 : checkPrefixCuts (2^48) 2370830337 9 Manual.Count131072.C018058.packed 128 cuts18058 = true := by
 decide +kernel
def pointBounds18058 : List (Nat × Nat × Nat) := [(2370885632,98694445208852,98694824785127),(2370960384,98694853010520,98695232587044)]
theorem point_links_checked18058 : (cuts18058.take 2).map (fun c => (2370830337-1+2*2^9*c.k,98694139735087+c.lower,98694519311181+c.upper)) = pointBounds18058 := by
 decide +kernel
def cuts18059 : List PrefixCut := [⟨72,404583262,404583510⟩,
⟨128,724869595,724870036⟩]
theorem checked18059 : checkPrefixCuts (2^48) 2370961409 9 Manual.Count131072.C018059.packed 128 cuts18059 = true := by
 decide +kernel
def pointBounds18059 : List (Nat × Nat × Nat) := [(2371035136,98695262461205,98695642037980)]
theorem point_links_checked18059 : (cuts18059.take 1).map (fun c => (2370961409-1+2*2^9*c.k,98694857877943+c.lower,98695237454470+c.upper)) = pointBounds18059 := by
 decide +kernel
def cuts18060 : List PrefixCut := [⟨17,96511741,96511799⟩,
⟨90,505936685,505936993⟩,
⟨128,723405108,723405548⟩]
theorem checked18060 : checkPrefixCuts (2^48) 2371092481 9 Manual.Count131072.C018060.packed 128 cuts18060 = true := by
 decide +kernel
def pointBounds18060 : List (Nat × Nat × Nat) := [(2371109888,98695679259279,98696058836305),(2371184640,98696088684223,98696468261499)]
theorem point_links_checked18060 : (cuts18060.take 2).map (fun c => (2371092481-1+2*2^9*c.k,98695582747538+c.lower,98695962324506+c.upper)) = pointBounds18060 := by
 decide +kernel
def cuts18061 : List PrefixCut := [⟨35,197166674,197166796⟩,
⟨108,611907391,611907767⟩,
⟨128,719448186,719448630⟩]
theorem checked18061 : checkPrefixCuts (2^48) 2371223553 9 Manual.Count131072.C018061.packed 128 cuts18061 = true := by
 decide +kernel
def pointBounds18061 : List (Nat × Nat × Nat) := [(2371259392,98696503319320,98696882896850),(2371334144,98696918060037,98697297637821)]
theorem point_links_checked18061 : (cuts18061.take 2).map (fun c => (2371223553-1+2*2^9*c.k,98696306152646+c.lower,98696685730054+c.upper)) = pointBounds18061 := by
 decide +kernel
def cuts18062 : List PrefixCut := [⟨53,296147971,296148147⟩,
⟨126,705640015,705640440⟩,
⟨128,716203551,716203983⟩]
theorem checked18062 : checkPrefixCuts (2^48) 2371354625 9 Manual.Count131072.C018062.packed 128 cuts18062 = true := by
 decide +kernel
def pointBounds18062 : List (Nat × Nat × Nat) := [(2371408896,98697321748803,98697701326831),(2371483648,98697731240847,98698110819124)]
theorem point_links_checked18062 : (cuts18062.take 2).map (fun c => (2371354625-1+2*2^9*c.k,98697025600832+c.lower,98697405178684+c.upper)) = pointBounds18062 := by
 decide +kernel
def cuts18063 : List PrefixCut := [⟨71,399390320,399390566⟩,
⟨128,713078136,713078573⟩]
theorem checked18063 : checkPrefixCuts (2^48) 2371485697 9 Manual.Count131072.C018063.packed 128 cuts18063 = true := by
 decide +kernel
def pointBounds18063 : List (Nat × Nat × Nat) := [(2371558400,98698141194703,98698520773233)]
theorem point_links_checked18063 : (cuts18063.take 1).map (fun c => (2371485697-1+2*2^9*c.k,98697741804383+c.lower,98698121382667+c.upper)) = pointBounds18063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000251
