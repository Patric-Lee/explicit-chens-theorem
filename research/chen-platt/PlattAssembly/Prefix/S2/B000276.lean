import PlattAssemblyKernel
import PlattCertificates.Count131072.C018832
import PlattCertificates.Count131072.C018833
import PlattCertificates.Count131072.C018834
import PlattCertificates.Count131072.C018835
import PlattCertificates.Count131072.C018836
import PlattCertificates.Count131072.C018837
import PlattCertificates.Count131072.C018838
import PlattCertificates.Count131072.C018839
import PlattCertificates.Count131072.C018840
import PlattCertificates.Count131072.C018841
import PlattCertificates.Count131072.C018842
import PlattCertificates.Count131072.C018843
import PlattCertificates.Count131072.C018844
import PlattCertificates.Count131072.C018845
import PlattCertificates.Count131072.C018846
import PlattCertificates.Count131072.C018847
import PlattCertificates.Count131072.C018848
import PlattCertificates.Count131072.C018849
import PlattCertificates.Count131072.C018850
import PlattCertificates.Count131072.C018851
import PlattCertificates.Count131072.C018852
import PlattCertificates.Count131072.C018853
import PlattCertificates.Count131072.C018854
import PlattCertificates.Count131072.C018855
import PlattCertificates.Count131072.C018856
import PlattCertificates.Count131072.C018857
import PlattCertificates.Count131072.C018858
import PlattCertificates.Count131072.C018859
import PlattCertificates.Count131072.C018860
import PlattCertificates.Count131072.C018861
import PlattCertificates.Count131072.C018862
import PlattCertificates.Count131072.C018863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000276
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18832 : List PrefixCut := [⟨70,384473781,384474014⟩,
⟨128,702905734,702906160⟩]
theorem checked18832 : checkPrefixCuts (2^48) 2472280065 9 Manual.Count131072.C018832.packed 128 cuts18832 = true := by
 decide +kernel
def pointBounds18832 : List (Nat × Nat × Nat) := [(2472351744,99240269601324,99240649507574)]
theorem point_links_checked18832 : (cuts18832.take 1).map (fun c => (2472280065-1+2*2^9*c.k,99239885127543+c.lower,99240265033560+c.upper)) = pointBounds18832 := by
 decide +kernel
def cuts18833 : List PrefixCut := [⟨18,95972084,95972142⟩,
⟨94,508883186,508883490⟩,
⟨128,695013370,695013784⟩]
theorem checked18833 : checkPrefixCuts (2^48) 2472411137 9 Manual.Count131072.C018833.packed 128 cuts18833 = true := by
 decide +kernel
def pointBounds18833 : List (Nat × Nat × Nat) := [(2472429568,99240684005361,99241063911862),(2472507392,99241096916463,99241476823210)]
theorem point_links_checked18833 : (cuts18833.take 2).map (fun c => (2472411137-1+2*2^9*c.k,99240588033277+c.lower,99240967939720+c.upper)) = pointBounds18833 := by
 decide +kernel
def cuts18834 : List PrefixCut := [⟨42,225287966,225288101⟩,
⟨118,634757877,634758258⟩,
⟨128,690650605,690651019⟩]
theorem checked18834 : checkPrefixCuts (2^48) 2472542209 9 Manual.Count131072.C018834.packed 128 cuts18834 = true := by
 decide +kernel
def pointBounds18834 : List (Nat × Nat × Nat) := [(2472585216,99241508334613,99241888241605),(2472663040,99241917804524,99242297711762)]
theorem point_links_checked18834 : (cuts18834.take 2).map (fun c => (2472542209-1+2*2^9*c.k,99241283046647+c.lower,99241662953504+c.upper)) = pointBounds18834 := by
 decide +kernel
def cuts18835 : List PrefixCut := [⟨66,361304939,361305162⟩,
⟨128,697899291,697899714⟩]
theorem checked18835 : checkPrefixCuts (2^48) 2472673281 9 Manual.Count131072.C018835.packed 128 cuts18835 = true := by
 decide +kernel
def pointBounds18835 : List (Nat × Nat × Nat) := [(2472740864,99242335002191,99242714909685)]
theorem point_links_checked18835 : (cuts18835.take 1).map (fun c => (2472673281-1+2*2^9*c.k,99241973697252+c.lower,99242353604523+c.upper)) = pointBounds18835 := by
 decide +kernel
def cuts18836 : List PrefixCut := [⟨14,72394533,72394577⟩,
⟨90,472264441,472264724⟩,
⟨128,688642109,688642516⟩]
theorem checked18836 : checkPrefixCuts (2^48) 2472804353 9 Manual.Count131072.C018836.packed 128 cuts18836 = true := by
 decide +kernel
def pointBounds18836 : List (Nat × Nat × Nat) := [(2472818688,99242743991076,99243123898814),(2472896512,99243143860984,99243523768961)]
theorem point_links_checked18836 : (cuts18836.take 2).map (fun c => (2472804353-1+2*2^9*c.k,99242671596543+c.lower,99243051504237+c.upper)) = pointBounds18836 := by
 decide +kernel
def cuts18837 : List PrefixCut := [⟨38,205788889,205789011⟩,
⟨114,617584631,617584992⟩,
⟨128,695321278,695321685⟩]
theorem checked18837 : checkPrefixCuts (2^48) 2472935425 9 Manual.Count131072.C018837.packed 128 cuts18837 = true := by
 decide +kernel
def pointBounds18837 : List (Nat × Nat × Nat) := [(2472974336,99243566027541,99243945935764),(2473052160,99243977823283,99244357731745)]
theorem point_links_checked18837 : (cuts18837.take 2).map (fun c => (2472935425-1+2*2^9*c.k,99243360238652+c.lower,99243740146753+c.upper)) = pointBounds18837 := by
 decide +kernel
def cuts18838 : List PrefixCut := [⟨62,337346753,337346960⟩,
⟨128,693691112,693691531⟩]
theorem checked18838 : checkPrefixCuts (2^48) 2473066497 9 Manual.Count131072.C018838.packed 128 cuts18838 = true := by
 decide +kernel
def pointBounds18838 : List (Nat × Nat × Nat) := [(2473129984,99244392906683,99244772815398)]
theorem point_links_checked18838 : (cuts18838.take 1).map (fun c => (2473066497-1+2*2^9*c.k,99244055559930+c.lower,99244435468438+c.upper)) = pointBounds18838 := by
 decide +kernel
def cuts18839 : List PrefixCut := [⟨10,55880652,55880685⟩,
⟨86,467637466,467637746⟩,
⟨128,691605859,691606270⟩]
theorem checked18839 : checkPrefixCuts (2^48) 2473197569 9 Manual.Count131072.C018839.packed 128 cuts18839 = true := by
 decide +kernel
def pointBounds18839 : List (Nat × Nat × Nat) := [(2473207808,99244805131694,99245185040654),(2473285632,99245216888508,99245596797715)]
theorem point_links_checked18839 : (cuts18839.take 2).map (fun c => (2473197569-1+2*2^9*c.k,99244749251042+c.lower,99245129159969+c.upper)) = pointBounds18839 := by
 decide +kernel
def cuts18840 : List PrefixCut := [⟨34,185499330,185499441⟩,
⟨110,597002646,597002997⟩,
⟨128,692934763,692935173⟩]
theorem checked18840 : checkPrefixCuts (2^48) 2473328641 9 Manual.Count131072.C018840.packed 128 cuts18840 = true := by
 decide +kernel
def pointBounds18840 : List (Nat × Nat × Nat) := [(2473363456,99245626356231,99246006265680),(2473441280,99246037859547,99246417769236)]
theorem point_links_checked18840 : (cuts18840.take 2).map (fun c => (2473328641-1+2*2^9*c.k,99245440856901+c.lower,99245820766239+c.upper)) = pointBounds18840 := by
 decide +kernel
def cuts18841 : List PrefixCut := [⟨58,319996251,319996443⟩,
⟨128,697336080,697336499⟩]
theorem checked18841 : checkPrefixCuts (2^48) 2473459713 9 Manual.Count131072.C018841.packed 128 cuts18841 = true := by
 decide +kernel
def pointBounds18841 : List (Nat × Nat × Nat) := [(2473519104,99246453787915,99246833697855)]
theorem point_links_checked18841 : (cuts18841.take 1).map (fun c => (2473459713-1+2*2^9*c.k,99246133791664+c.lower,99246513701412+c.upper)) = pointBounds18841 := by
 decide +kernel
def cuts18842 : List PrefixCut := [⟨6,30268640,30268660⟩,
⟨82,442757209,442757474⟩,
⟨128,694112838,694113250⟩]
theorem checked18842 : checkPrefixCuts (2^48) 2473590785 9 Manual.Count131072.C018842.packed 128 cuts18842 = true := by
 decide +kernel
def pointBounds18842 : List (Nat × Nat × Nat) := [(2473596928,99246861396384,99247241306571),(2473674752,99247273884953,99247653795385)]
theorem point_links_checked18842 : (cuts18842.take 2).map (fun c => (2473590785-1+2*2^9*c.k,99246831127744+c.lower,99247211037911+c.upper)) = pointBounds18842 := by
 decide +kernel
def cuts18843 : List PrefixCut := [⟨30,158389116,158389206⟩,
⟨106,570168963,570169296⟩,
⟨128,688955783,688956189⟩]
theorem checked18843 : checkPrefixCuts (2^48) 2473721857 9 Manual.Count131072.C018843.packed 128 cuts18843 = true := by
 decide +kernel
def pointBounds18843 : List (Nat × Nat × Nat) := [(2473752576,99247683629698,99248063540367),(2473830400,99248095409545,99248475320457)]
theorem point_links_checked18843 : (cuts18843.take 2).map (fun c => (2473721857-1+2*2^9*c.k,99247525240582+c.lower,99247905151161+c.upper)) = pointBounds18843 := by
 decide +kernel
def cuts18844 : List PrefixCut := [⟨54,287973853,287974026⟩,
⟨128,685847408,685847818⟩]
theorem checked18844 : checkPrefixCuts (2^48) 2473852929 9 Manual.Count131072.C018844.packed 128 cuts18844 = true := by
 decide +kernel
def pointBounds18844 : List (Nat × Nat × Nat) := [(2473908224,99248502170218,99248882081376)]
theorem point_links_checked18844 : (cuts18844.take 1).map (fun c => (2473852929-1+2*2^9*c.k,99248214196365+c.lower,99248594107350+c.upper)) = pointBounds18844 := by
 decide +kernel
def cuts18845 : List PrefixCut := [⟨2,10467197,10467204⟩,
⟨78,423004624,423004877⟩,
⟨128,695936652,695937068⟩]
theorem checked18845 : checkPrefixCuts (2^48) 2473984001 9 Manual.Count131072.C018845.packed 128 cuts18845 = true := by
 decide +kernel
def pointBounds18845 : List (Nat × Nat × Nat) := [(2473986048,99248910510970,99249290422372),(2474063872,99249323048397,99249702960045)]
theorem point_links_checked18845 : (cuts18845.take 2).map (fun c => (2473984001-1+2*2^9*c.k,99248900043773+c.lower,99249279955168+c.upper)) = pointBounds18845 := by
 decide +kernel
def cuts18846 : List PrefixCut := [⟨26,136634513,136634593⟩,
⟨102,546529507,546529830⟩,
⟨128,687936284,687936695⟩]
theorem checked18846 : checkPrefixCuts (2^48) 2474115073 9 Manual.Count131072.C018846.packed 128 cuts18846 = true := by
 decide +kernel
def pointBounds18846 : List (Nat × Nat × Nat) := [(2474141696,99249732614938,99250112526829),(2474219520,99250142509932,99250522422066)]
theorem point_links_checked18846 : (cuts18846.take 2).map (fun c => (2474115073-1+2*2^9*c.k,99249595980425+c.lower,99249975892236+c.upper)) = pointBounds18846 := by
 decide +kernel
def cuts18847 : List PrefixCut := [⟨50,270181670,270181832⟩,
⟨126,679823283,679823689⟩,
⟨128,690743850,690744263⟩]
theorem checked18847 : checkPrefixCuts (2^48) 2474246145 9 Manual.Count131072.C018847.packed 128 cuts18847 = true := by
 decide +kernel
def pointBounds18847 : List (Nat × Nat × Nat) := [(2474297344,99250554098379,99250934010763),(2474375168,99250963739992,99251343652620)]
theorem point_links_checked18847 : (cuts18847.take 2).map (fun c => (2474246145-1+2*2^9*c.k,99250283916709+c.lower,99250663828931+c.upper)) = pointBounds18847 := by
 decide +kernel
def cuts18848 : List PrefixCut := [⟨74,400641989,400642224⟩,
⟨128,689228556,689228963⟩]
theorem checked18848 : checkPrefixCuts (2^48) 2474377217 9 Manual.Count131072.C018848.packed 128 cuts18848 = true := by
 decide +kernel
def pointBounds18848 : List (Nat × Nat × Nat) := [(2474452992,99251375302548,99251755215418)]
theorem point_links_checked18848 : (cuts18848.take 1).map (fun c => (2474377217-1+2*2^9*c.k,99250974660559+c.lower,99251354573194+c.upper)) = pointBounds18848 := by
 decide +kernel
def cuts18849 : List PrefixCut := [⟨22,121711747,121711820⟩,
⟨98,535978298,535978615⟩,
⟨128,699884138,699884553⟩]
theorem checked18849 : checkPrefixCuts (2^48) 2474508289 9 Manual.Count131072.C018849.packed 128 cuts18849 = true := by
 decide +kernel
def pointBounds18849 : List (Nat × Nat × Nat) := [(2474530816,99251785600862,99252165513977),(2474608640,99252199867413,99252579780772)]
theorem point_links_checked18849 : (cuts18849.take 2).map (fun c => (2474508289-1+2*2^9*c.k,99251663889115+c.lower,99252043802157+c.upper)) = pointBounds18849 := by
 decide +kernel
def cuts18850 : List PrefixCut := [⟨46,246707989,246708137⟩,
⟨122,660493573,660493972⟩,
⟨128,690975337,690975755⟩]
theorem checked18850 : checkPrefixCuts (2^48) 2474639361 9 Manual.Count131072.C018850.packed 128 cuts18850 = true := by
 decide +kernel
def pointBounds18850 : List (Nat × Nat × Nat) := [(2474686464,99252610481242,99252990394847),(2474764288,99253024266826,99253404180682)]
theorem point_links_checked18850 : (cuts18850.take 2).map (fun c => (2474639361-1+2*2^9*c.k,99252363773253+c.lower,99252743686710+c.upper)) = pointBounds18850 := by
 decide +kernel
def cuts18851 : List PrefixCut := [⟨70,373964361,373964590⟩,
⟨128,685024468,685024886⟩]
theorem checked18851 : checkPrefixCuts (2^48) 2474770433 9 Manual.Count131072.C018851.packed 128 cuts18851 = true := by
 decide +kernel
def pointBounds18851 : List (Nat × Nat × Nat) := [(2474842112,99253428712951,99253808627055)]
theorem point_links_checked18851 : (cuts18851.take 1).map (fun c => (2474770433-1+2*2^9*c.k,99253054748590+c.lower,99253434662465+c.upper)) = pointBounds18851 := by
 decide +kernel
def cuts18852 : List PrefixCut := [⟨18,96330449,96330509⟩,
⟨94,496429458,496429766⟩,
⟨128,676117375,676117796⟩]
theorem checked18852 : checkPrefixCuts (2^48) 2474901505 9 Manual.Count131072.C018852.packed 128 cuts18852 = true := by
 decide +kernel
def pointBounds18852 : List (Nat × Nat × Nat) := [(2474919936,99253836103507,99254216017860),(2474997760,99254236202516,99254616117117)]
theorem point_links_checked18852 : (cuts18852.take 2).map (fun c => (2474901505-1+2*2^9*c.k,99253739773058+c.lower,99254119687351+c.upper)) = pointBounds18852 := by
 decide +kernel
def cuts18853 : List PrefixCut := [⟨42,224606373,224606504⟩,
⟨118,626044952,626045323⟩,
⟨128,678697288,678697691⟩]
theorem checked18853 : checkPrefixCuts (2^48) 2475032577 9 Manual.Count131072.C018853.packed 128 cuts18853 = true := by
 decide +kernel
def pointBounds18853 : List (Nat × Nat × Nat) := [(2475075584,99254640496806,99255020411651),(2475153408,99255041935385,99255421850470)]
theorem point_links_checked18853 : (cuts18853.take 2).map (fun c => (2475032577-1+2*2^9*c.k,99254415890433+c.lower,99254795805147+c.upper)) = pointBounds18853 := by
 decide +kernel
def cuts18854 : List PrefixCut := [⟨66,353549731,353549941⟩,
⟨128,686166486,686166894⟩]
theorem checked18854 : checkPrefixCuts (2^48) 2475163649 9 Manual.Count131072.C018854.packed 128 cuts18854 = true := by
 decide +kernel
def pointBounds18854 : List (Nat × Nat × Nat) := [(2475231232,99255448137452,99255828052779)]
theorem point_links_checked18854 : (cuts18854.take 1).map (fun c => (2475163649-1+2*2^9*c.k,99255094587721+c.lower,99255474502838+c.upper)) = pointBounds18854 := by
 decide +kernel
def cuts18855 : List PrefixCut := [⟨14,76301656,76301703⟩,
⟨90,488049991,488050282⟩,
⟨128,691360915,691361330⟩]
theorem checked18855 : checkPrefixCuts (2^48) 2475294721 9 Manual.Count131072.C018855.packed 128 cuts18855 = true := by
 decide +kernel
def pointBounds18855 : List (Nat × Nat × Nat) := [(2475309056,99255857055863,99256236971435),(2475386880,99256268804198,99256648720014)]
theorem point_links_checked18855 : (cuts18855.take 2).map (fun c => (2475294721-1+2*2^9*c.k,99255780754207+c.lower,99256160669732+c.upper)) = pointBounds18855 := by
 decide +kernel
def cuts18856 : List PrefixCut := [⟨38,202284353,202284476⟩,
⟨114,621511379,621511748⟩,
⟨128,693029921,693030335⟩]
theorem checked18856 : checkPrefixCuts (2^48) 2475425793 9 Manual.Count131072.C018856.packed 128 cuts18856 = true := by
 decide +kernel
def pointBounds18856 : List (Nat × Nat × Nat) := [(2475464704,99256674399475,99257054315538),(2475542528,99257093626501,99257473542810)]
theorem point_links_checked18856 : (cuts18856.take 2).map (fun c => (2475425793-1+2*2^9*c.k,99256472115122+c.lower,99256852031062+c.upper)) = pointBounds18856 := by
 decide +kernel
def cuts18857 : List PrefixCut := [⟨62,333482673,333482875⟩,
⟨128,687194590,687195002⟩]
theorem checked18857 : checkPrefixCuts (2^48) 2475556865 9 Manual.Count131072.C018857.packed 128 cuts18857 = true := by
 decide +kernel
def pointBounds18857 : List (Nat × Nat × Nat) := [(2475620352,99257498627716,99257878544272)]
theorem point_links_checked18857 : (cuts18857.take 1).map (fun c => (2475556865-1+2*2^9*c.k,99257165145043+c.lower,99257545061397+c.upper)) = pointBounds18857 := by
 decide +kernel
def cuts18858 : List PrefixCut := [⟨10,54573791,54573823⟩,
⟨86,456479918,456480195⟩,
⟨128,683178985,683179394⟩]
theorem checked18858 : checkPrefixCuts (2^48) 2475687937 9 Manual.Count131072.C018858.packed 128 cuts18858 = true := by
 decide +kernel
def pointBounds18858 : List (Nat × Nat × Nat) := [(2475698176,99257906913424,99258286830222),(2475776000,99258308819551,99258688736594)]
theorem point_links_checked18858 : (cuts18858.take 2).map (fun c => (2475687937-1+2*2^9*c.k,99257852339633+c.lower,99258232256399+c.upper)) = pointBounds18858 := by
 decide +kernel
def cuts18859 : List PrefixCut := [⟨34,182243134,182243246⟩,
⟨110,595265154,595265516⟩,
⟨128,692464996,692465415⟩]
theorem checked18859 : checkPrefixCuts (2^48) 2475819009 9 Manual.Count131072.C018859.packed 128 cuts18859 = true := by
 decide +kernel
def pointBounds18859 : List (Nat × Nat × Nat) := [(2475853824,99258717761752,99259097679039),(2475931648,99259130783772,99259510701309)]
theorem point_links_checked18859 : (cuts18859.take 2).map (fun c => (2475819009-1+2*2^9*c.k,99258535518618+c.lower,99258915435793+c.upper)) = pointBounds18859 := by
 decide +kernel
def cuts18860 : List PrefixCut := [⟨58,306487315,306487506⟩,
⟨128,683561266,683561680⟩]
theorem checked18860 : checkPrefixCuts (2^48) 2475950081 9 Manual.Count131072.C018860.packed 128 cuts18860 = true := by
 decide +kernel
def pointBounds18860 : List (Nat × Nat × Nat) := [(2476009472,99259534470929,99259914388714)]
theorem point_links_checked18860 : (cuts18860.take 1).map (fun c => (2475950081-1+2*2^9*c.k,99259227983614+c.lower,99259607901208+c.upper)) = pointBounds18860 := by
 decide +kernel
def cuts18861 : List PrefixCut := [⟨6,33648520,33648541⟩,
⟨82,443448712,443448978⟩,
⟨128,693414871,693415287⟩]
theorem checked18861 : checkPrefixCuts (2^48) 2476081153 9 Manual.Count131072.C018861.packed 128 cuts18861 = true := by
 decide +kernel
def pointBounds18861 : List (Nat × Nat × Nat) := [(2476087296,99259945193400,99260325111429),(2476165120,99260354993592,99260734911866)]
theorem point_links_checked18861 : (cuts18861.take 2).map (fun c => (2476081153-1+2*2^9*c.k,99259911544880+c.lower,99260291462888+c.upper)) = pointBounds18861 := by
 decide +kernel
def cuts18862 : List PrefixCut := [⟨30,160389562,160389659⟩,
⟨106,569254617,569254960⟩,
⟨128,685648651,685649065⟩]
theorem checked18862 : checkPrefixCuts (2^48) 2476212225 9 Manual.Count131072.C018862.packed 128 cuts18862 = true := by
 decide +kernel
def pointBounds18862 : List (Nat × Nat × Nat) := [(2476242944,99260765349313,99261145267834),(2476320768,99261174214368,99261554133135)]
theorem point_links_checked18862 : (cuts18862.take 2).map (fun c => (2476212225-1+2*2^9*c.k,99260604959751+c.lower,99260984878175+c.upper)) = pointBounds18862 := by
 decide +kernel
def cuts18863 : List PrefixCut := [⟨54,294731444,294731616⟩,
⟨128,701638789,701639202⟩]
theorem checked18863 : checkPrefixCuts (2^48) 2476343297 9 Manual.Count131072.C018863.packed 128 cuts18863 = true := by
 decide +kernel
def pointBounds18863 : List (Nat × Nat × Nat) := [(2476398592,99261585339846,99261965258856)]
theorem point_links_checked18863 : (cuts18863.take 1).map (fun c => (2476343297-1+2*2^9*c.k,99261290608402+c.lower,99261670527240+c.upper)) = pointBounds18863 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000276
