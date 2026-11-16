import PlattAssemblyKernel
import PlattCertificates.Count131072.C018096
import PlattCertificates.Count131072.C018097
import PlattCertificates.Count131072.C018098
import PlattCertificates.Count131072.C018099
import PlattCertificates.Count131072.C018100
import PlattCertificates.Count131072.C018101
import PlattCertificates.Count131072.C018102
import PlattCertificates.Count131072.C018103
import PlattCertificates.Count131072.C018104
import PlattCertificates.Count131072.C018105
import PlattCertificates.Count131072.C018106
import PlattCertificates.Count131072.C018107
import PlattCertificates.Count131072.C018108
import PlattCertificates.Count131072.C018109
import PlattCertificates.Count131072.C018110
import PlattCertificates.Count131072.C018111
import PlattCertificates.Count131072.C018112
import PlattCertificates.Count131072.C018113
import PlattCertificates.Count131072.C018114
import PlattCertificates.Count131072.C018115
import PlattCertificates.Count131072.C018116
import PlattCertificates.Count131072.C018117
import PlattCertificates.Count131072.C018118
import PlattCertificates.Count131072.C018119
import PlattCertificates.Count131072.C018120
import PlattCertificates.Count131072.C018121
import PlattCertificates.Count131072.C018122
import PlattCertificates.Count131072.C018123
import PlattCertificates.Count131072.C018124
import PlattCertificates.Count131072.C018125
import PlattCertificates.Count131072.C018126
import PlattCertificates.Count131072.C018127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000253
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18096 : List PrefixCut := [⟨8,44902053,44902079⟩,
⟨81,454818679,454818947⟩,
⟨128,721494532,721494962⟩]
theorem checked18096 : checkPrefixCuts (2^48) 2375811073 9 Manual.Count131072.C018096.packed 128 cuts18096 = true := by
 decide +kernel
def pointBounds18096 : List (Nat × Nat × Nat) := [(2375819264,98721532653562,98721912246341),(2375894016,98721942570188,98722322163209)]
theorem point_links_checked18096 : (cuts18096.take 2).map (fun c => (2375811073-1+2*2^9*c.k,98721487751509+c.lower,98721867344262+c.upper)) = pointBounds18096 := by
 decide +kernel
def cuts18097 : List PrefixCut := [⟨26,146308080,146308167⟩,
⟨99,558923665,558924001⟩,
⟨128,725008729,725009166⟩]
theorem checked18097 : checkPrefixCuts (2^48) 2375942145 9 Manual.Count131072.C018097.packed 128 cuts18097 = true := by
 decide +kernel
def pointBounds18097 : List (Nat × Nat × Nat) := [(2375968768,98722355554121,98722735147391),(2376043520,98722768169706,98723147763225)]
theorem point_links_checked18097 : (cuts18097.take 2).map (fun c => (2375942145-1+2*2^9*c.k,98722209246041+c.lower,98722588839224+c.upper)) = pointBounds18097 := by
 decide +kernel
def cuts18098 : List PrefixCut := [⟨44,251374409,251374562⟩,
⟨117,665148520,665148921⟩,
⟨128,725797974,725798411⟩]
theorem checked18098 : checkPrefixCuts (2^48) 2376073217 9 Manual.Count131072.C018098.packed 128 cuts18098 = true := by
 decide +kernel
def pointBounds18098 : List (Nat × Nat × Nat) := [(2376118272,98723185629179,98723565222952),(2376193024,98723599403290,98723978997311)]
theorem point_links_checked18098 : (cuts18098.take 2).map (fun c => (2376073217-1+2*2^9*c.k,98722934254770+c.lower,98723313848390+c.upper)) = pointBounds18098 := by
 decide +kernel
def cuts18099 : List PrefixCut := [⟨62,348373491,348373697⟩,
⟨128,720545990,720546426⟩]
theorem checked18099 : checkPrefixCuts (2^48) 2376204289 9 Manual.Count131072.C018099.packed 128 cuts18099 = true := by
 decide +kernel
def pointBounds18099 : List (Nat × Nat × Nat) := [(2376267776,98724008426235,98724388020498)]
theorem point_links_checked18099 : (cuts18099.take 1).map (fun c => (2376204289-1+2*2^9*c.k,98723660052744+c.lower,98724039646801+c.upper)) = pointBounds18099 := by
 decide +kernel
def cuts18100 : List PrefixCut := [⟨7,38851259,38851282⟩,
⟨80,447848467,447848734⟩,
⟨128,719913959,719914394⟩]
theorem checked18100 : checkPrefixCuts (2^48) 2376335361 9 Manual.Count131072.C018100.packed 128 cuts18100 = true := by
 decide +kernel
def pointBounds18100 : List (Nat × Nat × Nat) := [(2376342528,98724419449993,98724799044509),(2376417280,98724828447201,98725208041961)]
theorem point_links_checked18100 : (cuts18100.take 2).map (fun c => (2376335361-1+2*2^9*c.k,98724380598734+c.lower,98724760193227+c.upper)) = pointBounds18100 := by
 decide +kernel
def cuts18101 : List PrefixCut := [⟨25,135971387,135971472⟩,
⟨98,543995306,543995638⟩,
⟨128,711228123,711228557⟩]
theorem checked18101 : checkPrefixCuts (2^48) 2376466433 9 Manual.Count131072.C018101.packed 128 cuts18101 = true := by
 decide +kernel
def pointBounds18101 : List (Nat × Nat × Nat) := [(2376492032,98725236484080,98725616079093),(2376566784,98725644507999,98726024103259)]
theorem point_links_checked18101 : (cuts18101.take 2).map (fun c => (2376466433-1+2*2^9*c.k,98725100512693+c.lower,98725480107621+c.upper)) = pointBounds18101 := by
 decide +kernel
def cuts18102 : List PrefixCut := [⟨43,239357077,239357226⟩,
⟨116,652566439,652566842⟩,
⟨128,722084770,722085216⟩]
theorem checked18102 : checkPrefixCuts (2^48) 2376597505 9 Manual.Count131072.C018102.packed 128 cuts18102 = true := by
 decide +kernel
def pointBounds18102 : List (Nat × Nat × Nat) := [(2376641536,98726051097893,98726430693404),(2376716288,98726464307255,98726843903020)]
theorem point_links_checked18102 : (cuts18102.take 2).map (fun c => (2376597505-1+2*2^9*c.k,98725811740816+c.lower,98726191336178+c.upper)) = pointBounds18102 := by
 decide +kernel
def cuts18103 : List PrefixCut := [⟨61,339059359,339059562⟩,
⟨128,715057847,715058279⟩]
theorem checked18103 : checkPrefixCuts (2^48) 2376728577 9 Manual.Count131072.C018103.packed 128 cuts18103 = true := by
 decide +kernel
def pointBounds18103 : List (Nat × Nat × Nat) := [(2376791040,98726872884945,98727252480956)]
theorem point_links_checked18103 : (cuts18103.take 1).map (fun c => (2376728577-1+2*2^9*c.k,98726533825586+c.lower,98726913421394+c.upper)) = pointBounds18103 := by
 decide +kernel
def cuts18104 : List PrefixCut := [⟨6,34579476,34579497⟩,
⟨79,454144609,454144876⟩,
⟨128,726742251,726742688⟩]
theorem checked18104 : checkPrefixCuts (2^48) 2376859649 9 Manual.Count131072.C018104.packed 128 cuts18104 = true := by
 decide +kernel
def pointBounds18104 : List (Nat × Nat × Nat) := [(2376865792,98727283462909,98727663059170),(2376940544,98727703028042,98728082624549)]
theorem point_links_checked18104 : (cuts18104.take 2).map (fun c => (2376859649-1+2*2^9*c.k,98727248883433+c.lower,98727628479673+c.upper)) = pointBounds18104 := by
 decide +kernel
def cuts18105 : List PrefixCut := [⟨24,133809958,133810039⟩,
⟨97,544112405,544112730⟩,
⟨128,721491712,721492145⟩]
theorem checked18105 : checkPrefixCuts (2^48) 2376990721 9 Manual.Count131072.C018105.packed 128 cuts18105 = true := by
 decide +kernel
def pointBounds18105 : List (Nat × Nat × Nat) := [(2377015296,98728109435642,98728489032400),(2377090048,98728519738089,98728899335091)]
theorem point_links_checked18105 : (cuts18105.take 2).map (fun c => (2376990721-1+2*2^9*c.k,98727975625684+c.lower,98728355222361+c.upper)) = pointBounds18105 := by
 decide +kernel
def cuts18106 : List PrefixCut := [⟨42,228055533,228055672⟩,
⟨115,642121178,642121577⟩,
⟨128,714702679,714703120⟩]
theorem checked18106 : checkPrefixCuts (2^48) 2377121793 9 Manual.Count131072.C018106.packed 128 cuts18106 = true := by
 decide +kernel
def pointBounds18106 : List (Nat × Nat × Nat) := [(2377164800,98728925172929,98729304770178),(2377239552,98729339238574,98729718836083)]
theorem point_links_checked18106 : (cuts18106.take 2).map (fun c => (2377121793-1+2*2^9*c.k,98728697117396+c.lower,98729076714506+c.upper)) = pointBounds18106 := by
 decide +kernel
def cuts18107 : List PrefixCut := [⟨60,341707892,341708091⟩,
⟨128,717623502,717623927⟩]
theorem checked18107 : checkPrefixCuts (2^48) 2377252865 9 Manual.Count131072.C018107.packed 128 cuts18107 = true := by
 decide +kernel
def pointBounds18107 : List (Nat × Nat × Nat) := [(2377314304,98729753527967,98730133125717)]
theorem point_links_checked18107 : (cuts18107.take 1).map (fun c => (2377252865-1+2*2^9*c.k,98729411820075+c.lower,98729791417626+c.upper)) = pointBounds18107 := by
 decide +kernel
def cuts18108 : List PrefixCut := [⟨5,28178431,28178449⟩,
⟨78,433917364,433917624⟩,
⟨128,711427413,711427841⟩]
theorem checked18108 : checkPrefixCuts (2^48) 2377383937 9 Manual.Count131072.C018108.packed 128 cuts18108 = true := by
 decide +kernel
def pointBounds18108 : List (Nat × Nat × Nat) := [(2377389056,98730157622008,98730537220002),(2377463808,98730563360941,98730942959177)]
theorem point_links_checked18108 : (cuts18108.take 2).map (fun c => (2377383937-1+2*2^9*c.k,98730129443577+c.lower,98730509041553+c.upper)) = pointBounds18108 := by
 decide +kernel
def cuts18109 : List PrefixCut := [⟨23,130702324,130702404⟩,
⟨96,540796094,540796424⟩,
⟨128,726896788,726897228⟩]
theorem checked18109 : checkPrefixCuts (2^48) 2377515009 9 Manual.Count131072.C018109.packed 128 cuts18109 = true := by
 decide +kernel
def pointBounds18109 : List (Nat × Nat × Nat) := [(2377538560,98730971573314,98731351171798),(2377613312,98731381667084,98731761265818)]
theorem point_links_checked18109 : (cuts18109.take 2).map (fun c => (2377515009-1+2*2^9*c.k,98730840870990+c.lower,98731220469394+c.upper)) = pointBounds18109 := by
 decide +kernel
def cuts18110 : List PrefixCut := [⟨41,228242053,228242190⟩,
⟨114,636060815,636061205⟩,
⟨128,714663594,714664031⟩]
theorem checked18110 : checkPrefixCuts (2^48) 2377646081 9 Manual.Count131072.C018110.packed 128 cuts18110 = true := by
 decide +kernel
def pointBounds18110 : List (Nat × Nat × Nat) := [(2377688064,98731796009831,98732175608812),(2377762816,98732203828593,98732583427827)]
theorem point_links_checked18110 : (cuts18110.take 2).map (fun c => (2377646081-1+2*2^9*c.k,98731567767778+c.lower,98731947366622+c.upper)) = pointBounds18110 := by
 decide +kernel
def cuts18111 : List PrefixCut := [⟨59,331925726,331925931⟩,
⟨128,719714235,719714675⟩]
theorem checked18111 : checkPrefixCuts (2^48) 2377777153 9 Manual.Count131072.C018111.packed 128 cuts18111 = true := by
 decide +kernel
def pointBounds18111 : List (Nat × Nat × Nat) := [(2377837568,98732614357098,98732993956584)]
theorem point_links_checked18111 : (cuts18111.take 1).map (fun c => (2377777153-1+2*2^9*c.k,98732282431372+c.lower,98732662030653+c.upper)) = pointBounds18111 := by
 decide +kernel
def cuts18112 : List PrefixCut := [⟨4,22016949,22016962⟩,
⟨77,431572741,431573006⟩,
⟨128,724054072,724054511⟩]
theorem checked18112 : checkPrefixCuts (2^48) 2377908225 9 Manual.Count131072.C018112.packed 128 cuts18112 = true := by
 decide +kernel
def pointBounds18112 : List (Nat × Nat × Nat) := [(2377912320,98733024162556,98733403762290),(2377987072,98733433718348,98733813318334)]
theorem point_links_checked18112 : (cuts18112.take 2).map (fun c => (2377908225-1+2*2^9*c.k,98733002145607+c.lower,98733381745328+c.upper)) = pointBounds18112 := by
 decide +kernel
def cuts18113 : List PrefixCut := [⟨22,121441180,121441258⟩,
⟨95,530971314,530971638⟩,
⟨128,714308771,714309203⟩]
theorem checked18113 : checkPrefixCuts (2^48) 2378039297 9 Manual.Count131072.C018113.packed 128 cuts18113 = true := by
 decide +kernel
def pointBounds18113 : List (Nat × Nat × Nat) := [(2378061824,98733847640859,98734227241097),(2378136576,98734257170993,98734636771477)]
theorem point_links_checked18113 : (cuts18113.take 2).map (fun c => (2378039297-1+2*2^9*c.k,98733726199679+c.lower,98734105799839+c.upper)) = pointBounds18113 := by
 decide +kernel
def cuts18114 : List PrefixCut := [⟨40,227599993,227600126⟩,
⟨113,632251727,632252112⟩,
⟨128,720305317,720305758⟩]
theorem checked18114 : checkPrefixCuts (2^48) 2378170369 9 Manual.Count131072.C018114.packed 128 cuts18114 = true := by
 decide +kernel
def pointBounds18114 : List (Nat × Nat × Nat) := [(2378211328,98734668108443,98735047709168),(2378286080,98735072760177,98735452361154)]
theorem point_links_checked18114 : (cuts18114.take 2).map (fun c => (2378170369-1+2*2^9*c.k,98734440508450+c.lower,98734820109042+c.upper)) = pointBounds18114 := by
 decide +kernel
def cuts18115 : List PrefixCut := [⟨58,327828808,327829007⟩,
⟨128,715650310,715650748⟩]
theorem checked18115 : checkPrefixCuts (2^48) 2378301441 9 Manual.Count131072.C018115.packed 128 cuts18115 = true := by
 decide +kernel
def pointBounds18115 : List (Nat × Nat × Nat) := [(2378360832,98735488642575,98735868243807)]
theorem point_links_checked18115 : (cuts18115.take 1).map (fun c => (2378301441-1+2*2^9*c.k,98735160813767+c.lower,98735540414800+c.upper)) = pointBounds18115 := by
 decide +kernel
def cuts18116 : List PrefixCut := [⟨3,17870039,17870051⟩,
⟨76,418223384,418223641⟩,
⟨128,706853467,706853896⟩]
theorem checked18116 : checkPrefixCuts (2^48) 2378432513 9 Manual.Count131072.C018116.packed 128 cuts18116 = true := by
 decide +kernel
def pointBounds18116 : List (Nat × Nat × Nat) := [(2378435584,98735894334116,98736273935599),(2378510336,98736294687461,98736674289189)]
theorem point_links_checked18116 : (cuts18116.take 2).map (fun c => (2378432513-1+2*2^9*c.k,98735876464077+c.lower,98736256065548+c.upper)) = pointBounds18116 := by
 decide +kernel
def cuts18117 : List PrefixCut := [⟨21,115852552,115852625⟩,
⟨94,528605978,528606300⟩,
⟨128,719476333,719476774⟩]
theorem checked18117 : checkPrefixCuts (2^48) 2378563585 9 Manual.Count131072.C018117.packed 128 cuts18117 = true := by
 decide +kernel
def pointBounds18117 : List (Nat × Nat × Nat) := [(2378585088,98736699170096,98737078772069),(2378659840,98737111923522,98737491525744)]
theorem point_links_checked18117 : (cuts18117.take 2).map (fun c => (2378563585-1+2*2^9*c.k,98736583317544+c.lower,98736962919444+c.upper)) = pointBounds18117 := by
 decide +kernel
def cuts18118 : List PrefixCut := [⟨39,217255076,217255203⟩,
⟨112,619806291,619806663⟩,
⟨128,710325334,710325762⟩]
theorem checked18118 : checkPrefixCuts (2^48) 2378694657 9 Manual.Count131072.C018118.packed 128 cuts18118 = true := by
 decide +kernel
def pointBounds18118 : List (Nat × Nat × Nat) := [(2378734592,98737520048953,98737899651421),(2378809344,98737922600168,98738302202881)]
theorem point_links_checked18118 : (cuts18118.take 2).map (fun c => (2378694657-1+2*2^9*c.k,98737302793877+c.lower,98737682396218+c.upper)) = pointBounds18118 := by
 decide +kernel
def cuts18119 : List PrefixCut := [⟨57,312729536,312729729⟩,
⟨128,713362516,713362949⟩]
theorem checked18119 : checkPrefixCuts (2^48) 2378825729 9 Manual.Count131072.C018119.packed 128 cuts18119 = true := by
 decide +kernel
def pointBounds18119 : List (Nat × Nat × Nat) := [(2378884096,98738325848747,98738705451709)]
theorem point_links_checked18119 : (cuts18119.take 1).map (fun c => (2378825729-1+2*2^9*c.k,98738013119211+c.lower,98738392721980+c.upper)) = pointBounds18119 := by
 decide +kernel
def cuts18120 : List PrefixCut := [⟨2,10885308,10885316⟩,
⟨75,421917366,421917628⟩,
⟨128,723498341,723498785⟩]
theorem checked18120 : checkPrefixCuts (2^48) 2378956801 9 Manual.Count131072.C018120.packed 128 cuts18120 = true := by
 decide +kernel
def pointBounds18120 : List (Nat × Nat × Nat) := [(2378958848,98738737367035,98739116970245),(2379033600,98739148399093,98739528002557)]
theorem point_links_checked18120 : (cuts18120.take 2).map (fun c => (2378956801-1+2*2^9*c.k,98738726481727+c.lower,98739106084929+c.upper)) = pointBounds18120 := by
 decide +kernel
def cuts18121 : List PrefixCut := [⟨20,113460815,113460885⟩,
⟨93,516185405,516185722⟩,
⟨128,709261585,709262023⟩]
theorem checked18121 : checkPrefixCuts (2^48) 2379087873 9 Manual.Count131072.C018121.packed 128 cuts18121 = true := by
 decide +kernel
def pointBounds18121 : List (Nat × Nat × Nat) := [(2379108352,98739563440883,98739943044599),(2379183104,98739966165473,98740345769436)]
theorem point_links_checked18121 : (cuts18121.take 2).map (fun c => (2379087873-1+2*2^9*c.k,98739449980068+c.lower,98739829583714+c.upper)) = pointBounds18121 := by
 decide +kernel
def cuts18122 : List PrefixCut := [⟨38,217207248,217207383⟩,
⟨111,627122900,627123283⟩,
⟨128,720579506,720579946⟩]
theorem checked18122 : checkPrefixCuts (2^48) 2379218945 9 Manual.Count131072.C018122.packed 128 cuts18122 = true := by
 decide +kernel
def pointBounds18122 : List (Nat × Nat × Nat) := [(2379257856,98740376448901,98740756053120),(2379332608,98740786364553,98741165969020)]
theorem point_links_checked18122 : (cuts18122.take 2).map (fun c => (2379218945-1+2*2^9*c.k,98740159241653+c.lower,98740538845737+c.upper)) = pointBounds18122 := by
 decide +kernel
def cuts18123 : List PrefixCut := [⟨56,319285325,319285517⟩,
⟨128,728702174,728702613⟩]
theorem checked18123 : checkPrefixCuts (2^48) 2379350017 9 Manual.Count131072.C018123.packed 128 cuts18123 = true := by
 decide +kernel
def pointBounds18123 : List (Nat × Nat × Nat) := [(2379407360,98741199106484,98741578711200)]
theorem point_links_checked18123 : (cuts18123.take 1).map (fun c => (2379350017-1+2*2^9*c.k,98740879821159+c.lower,98741259425683+c.upper)) = pointBounds18123 := by
 decide +kernel
def cuts18124 : List PrefixCut := [⟨1,5678041,5678045⟩,
⟨74,415555165,415555418⟩,
⟨128,715177191,715177623⟩]
theorem checked18124 : checkPrefixCuts (2^48) 2379481089 9 Manual.Count131072.C018124.packed 128 cuts18124 = true := by
 decide +kernel
def pointBounds18124 : List (Nat × Nat × Nat) := [(2379482112,98741614201374,98741993806341),(2379556864,98742024078498,98742403683714)]
theorem point_links_checked18124 : (cuts18124.take 2).map (fun c => (2379481089-1+2*2^9*c.k,98741608523333+c.lower,98741988128296+c.upper)) = pointBounds18124 := by
 decide +kernel
def cuts18125 : List PrefixCut := [⟨19,107758132,107758200⟩,
⟨92,520211658,520211979⟩,
⟨128,724008836,724009280⟩]
theorem checked18125 : checkPrefixCuts (2^48) 2379612161 9 Manual.Count131072.C018125.packed 128 cuts18125 = true := by
 decide +kernel
def pointBounds18125 : List (Nat × Nat × Nat) := [(2379631616,98742431458656,98742811064119),(2379706368,98742843912182,98743223517898)]
theorem point_links_checked18125 : (cuts18125.take 2).map (fun c => (2379612161-1+2*2^9*c.k,98742323700524+c.lower,98742703305919+c.upper)) = pointBounds18125 := by
 decide +kernel
def cuts18126 : List PrefixCut := [⟨37,207224074,207224202⟩,
⟨110,613146467,613146841⟩,
⟨128,712851005,712851435⟩]
theorem checked18126 : checkPrefixCuts (2^48) 2379743233 9 Manual.Count131072.C018126.packed 128 cuts18126 = true := by
 decide +kernel
def pointBounds18126 : List (Nat × Nat × Nat) := [(2379781120,98743254933434,98743634539401),(2379855872,98743660855827,98744040462040)]
theorem point_links_checked18126 : (cuts18126.take 2).map (fun c => (2379743233-1+2*2^9*c.k,98743047709360+c.lower,98743427315199+c.upper)) = pointBounds18126 := by
 decide +kernel
def cuts18127 : List PrefixCut := [⟨55,308925452,308925642⟩,
⟨128,727004054,727004499⟩]
theorem checked18127 : checkPrefixCuts (2^48) 2379874305 9 Manual.Count131072.C018127.packed 128 cuts18127 = true := by
 decide +kernel
def pointBounds18127 : List (Nat × Nat × Nat) := [(2379930624,98744069485817,98744449092276),(2380005376,98744487564419,98744867171133)]
theorem point_links_checked18127 : (cuts18127.take 2).map (fun c => (2379874305-1+2*2^9*c.k,98743760560365+c.lower,98744140166634+c.upper)) = pointBounds18127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000253
