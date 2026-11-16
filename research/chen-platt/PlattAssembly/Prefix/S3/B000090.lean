import PlattAssemblyKernel
import PlattCertificates.Count131072.C022880
import PlattCertificates.Count131072.C022881
import PlattCertificates.Count131072.C022882
import PlattCertificates.Count131072.C022883
import PlattCertificates.Count131072.C022884
import PlattCertificates.Count131072.C022885
import PlattCertificates.Count131072.C022886
import PlattCertificates.Count131072.C022887
import PlattCertificates.Count131072.C022888
import PlattCertificates.Count131072.C022889
import PlattCertificates.Count131072.C022890
import PlattCertificates.Count131072.C022891
import PlattCertificates.Count131072.C022892
import PlattCertificates.Count131072.C022893
import PlattCertificates.Count131072.C022894
import PlattCertificates.Count131072.C022895
import PlattCertificates.Count131072.C022896
import PlattCertificates.Count131072.C022897
import PlattCertificates.Count131072.C022898
import PlattCertificates.Count131072.C022899
import PlattCertificates.Count131072.C022900
import PlattCertificates.Count131072.C022901
import PlattCertificates.Count131072.C022902
import PlattCertificates.Count131072.C022903
import PlattCertificates.Count131072.C022904
import PlattCertificates.Count131072.C022905
import PlattCertificates.Count131072.C022906
import PlattCertificates.Count131072.C022907
import PlattCertificates.Count131072.C022908
import PlattCertificates.Count131072.C022909
import PlattCertificates.Count131072.C022910
import PlattCertificates.Count131072.C022911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22880 : List PrefixCut := [⟨24,104046105,104046169⟩,
⟨116,506349826,506350116⟩,
⟨128,558652123,558652444⟩]
theorem checked22880 : checkPrefixCuts (2^48) 3002859521 9 Manual.Count131072.C022880.packed 128 cuts22880 = true := by
 decide +kernel
def pointBounds22880 : List (Nat × Nat × Nat) := [(3002884096,101758970799979,101759352173047),(3002978304,101759373103700,101759754476994)]
theorem point_links_checked22880 : (cuts22880.take 2).map (fun c => (3002859521-1+2*2^9*c.k,101758866753874+c.lower,101759248126878+c.upper)) = pointBounds22880 := by
 decide +kernel
def cuts22881 : List PrefixCut := [⟨80,349988692,349988892⟩,
⟨128,559564924,559565248⟩]
theorem checked22881 : checkPrefixCuts (2^48) 3002990593 9 Manual.Count131072.C022881.packed 128 cuts22881 = true := by
 decide +kernel
def pointBounds22881 : List (Nat × Nat × Nat) := [(3003072512,101759775394689,101760156768214)]
theorem point_links_checked22881 : (cuts22881.take 1).map (fun c => (3002990593-1+2*2^9*c.k,101759425405997+c.lower,101759806779322+c.upper)) = pointBounds22881 := by
 decide +kernel
def cuts22882 : List PrefixCut := [⟨44,193545709,193545816⟩,
⟨128,558509672,558509990⟩]
theorem checked22882 : checkPrefixCuts (2^48) 3003121665 9 Manual.Count131072.C022882.packed 128 cuts22882 = true := by
 decide +kernel
def pointBounds22882 : List (Nat × Nat × Nat) := [(3003166720,101760178516630,101760559890386)]
theorem point_links_checked22882 : (cuts22882.take 1).map (fun c => (3003121665-1+2*2^9*c.k,101759984970921+c.lower,101760366344570+c.upper)) = pointBounds22882 := by
 decide +kernel
def cuts22883 : List PrefixCut := [⟨8,35895992,35896014⟩,
⟨100,439367552,439367807⟩,
⟨128,562234084,562234411⟩]
theorem checked22883 : checkPrefixCuts (2^48) 3003252737 9 Manual.Count131072.C022883.packed 128 cuts22883 = true := by
 decide +kernel
def pointBounds22883 : List (Nat × Nat × Nat) := [(3003260928,101760579376585,101760960750574),(3003355136,101760982848145,101761364222367)]
theorem point_links_checked22883 : (cuts22883.take 2).map (fun c => (3003252737-1+2*2^9*c.k,101760543480593+c.lower,101760924854560+c.upper)) = pointBounds22883 := by
 decide +kernel
def cuts22884 : List PrefixCut := [⟨64,279842659,279842816⟩,
⟨128,558367200,558367519⟩]
theorem checked22884 : checkPrefixCuts (2^48) 3003383809 9 Manual.Count131072.C022884.packed 128 cuts22884 = true := by
 decide +kernel
def pointBounds22884 : List (Nat × Nat × Nat) := [(3003449344,101761385557336,101761766931787)]
theorem point_links_checked22884 : (cuts22884.take 1).map (fun c => (3003383809-1+2*2^9*c.k,101761105714677+c.lower,101761487088971+c.upper)) = pointBounds22884 := by
 decide +kernel
def cuts22885 : List PrefixCut := [⟨28,122110277,122110349⟩,
⟨120,529105000,529105308⟩,
⟨128,562185057,562185383⟩]
theorem checked22885 : checkPrefixCuts (2^48) 3003514881 9 Manual.Count131072.C022885.packed 128 cuts22885 = true := by
 decide +kernel
def pointBounds22885 : List (Nat × Nat × Nat) := [(3003543552,101761786192154,101762167566839),(3003637760,101762193186877,101762574561798)]
theorem point_links_checked22885 : (cuts22885.take 2).map (fun c => (3003514881-1+2*2^9*c.k,101761664081877+c.lower,101762045456490+c.upper)) = pointBounds22885 := by
 decide +kernel
def cuts22886 : List PrefixCut := [⟨84,369216369,369216572⟩,
⟨128,564409500,564409813⟩]
theorem checked22886 : checkPrefixCuts (2^48) 3003645953 9 Manual.Count131072.C022886.packed 128 cuts22886 = true := by
 decide +kernel
def pointBounds22886 : List (Nat × Nat × Nat) := [(3003731968,101762595483303,101762976858445)]
theorem point_links_checked22886 : (cuts22886.take 1).map (fun c => (3003645953-1+2*2^9*c.k,101762226266934+c.lower,101762607641873+c.upper)) = pointBounds22886 := by
 decide +kernel
def cuts22887 : List PrefixCut := [⟨48,214024974,214025100⟩,
⟨128,562042348,562042678⟩]
theorem checked22887 : checkPrefixCuts (2^48) 3003777025 9 Manual.Count131072.C022887.packed 128 cuts22887 = true := by
 decide +kernel
def pointBounds22887 : List (Nat × Nat × Nat) := [(3003826176,101763004701408,101763386076786)]
theorem point_links_checked22887 : (cuts22887.take 1).map (fun c => (3003777025-1+2*2^9*c.k,101762790676434+c.lower,101763172051686+c.upper)) = pointBounds22887 := by
 decide +kernel
def cuts22888 : List PrefixCut := [⟨12,56315322,56315352⟩,
⟨104,465507800,465508058⟩,
⟨128,571668993,571669313⟩]
theorem checked22888 : checkPrefixCuts (2^48) 3003908097 9 Manual.Count131072.C022888.packed 128 cuts22888 = true := by
 decide +kernel
def pointBounds22888 : List (Nat × Nat × Nat) := [(3003920384,101763409034104,101763790409716),(3004014592,101763818226582,101764199602422)]
theorem point_links_checked22888 : (cuts22888.take 2).map (fun c => (3003908097-1+2*2^9*c.k,101763352718782+c.lower,101763734094364+c.upper)) = pointBounds22888 := by
 decide +kernel
def cuts22889 : List PrefixCut := [⟨68,298146195,298146362⟩,
⟨128,562461680,562461991⟩]
theorem checked22889 : checkPrefixCuts (2^48) 3004039169 9 Manual.Count131072.C022889.packed 128 cuts22889 = true := by
 decide +kernel
def pointBounds22889 : List (Nat × Nat × Nat) := [(3004108800,101764222533970,101764603910039)]
theorem point_links_checked22889 : (cuts22889.take 1).map (fun c => (3004039169-1+2*2^9*c.k,101763924387775+c.lower,101764305763677+c.upper)) = pointBounds22889 := by
 decide +kernel
def cuts22890 : List PrefixCut := [⟨32,135481838,135481922⟩,
⟨124,543324139,543324453⟩,
⟨128,562249660,562249985⟩]
theorem checked22890 : checkPrefixCuts (2^48) 3004170241 9 Manual.Count131072.C022890.packed 128 cuts22890 = true := by
 decide +kernel
def pointBounds22890 : List (Nat × Nat × Nat) := [(3004203008,101764622331293,101765003707590),(3004297216,101765030173594,101765411550121)]
theorem point_links_checked22890 : (cuts22890.take 2).map (fun c => (3004170241-1+2*2^9*c.k,101764486849455+c.lower,101764868225668+c.upper)) = pointBounds22890 := by
 decide +kernel
def cuts22891 : List PrefixCut := [⟨88,382814134,382814354⟩,
⟨128,554074315,554074639⟩]
theorem checked22891 : checkPrefixCuts (2^48) 3004301313 9 Manual.Count131072.C022891.packed 128 cuts22891 = true := by
 decide +kernel
def pointBounds22891 : List (Nat × Nat × Nat) := [(3004391424,101765431913249,101765813290007)]
theorem point_links_checked22891 : (cuts22891.take 1).map (fun c => (3004301313-1+2*2^9*c.k,101765049099115+c.lower,101765430475653+c.upper)) = pointBounds22891 := by
 decide +kernel
def cuts22892 : List PrefixCut := [⟨52,231310009,231310140⟩,
⟨128,559671295,559671609⟩]
theorem checked22892 : checkPrefixCuts (2^48) 3004432385 9 Manual.Count131072.C022892.packed 128 cuts22892 = true := by
 decide +kernel
def pointBounds22892 : List (Nat × Nat × Nat) := [(3004485632,101765834483439,101766215860432)]
theorem point_links_checked22892 : (cuts22892.take 1).map (fun c => (3004432385-1+2*2^9*c.k,101765603173430+c.lower,101765984550292+c.upper)) = pointBounds22892 := by
 decide +kernel
def cuts22893 : List PrefixCut := [⟨16,65483854,65483895⟩,
⟨108,474118110,474118389⟩,
⟨128,563862293,563862625⟩]
theorem checked22893 : checkPrefixCuts (2^48) 3004563457 9 Manual.Count131072.C022893.packed 128 cuts22893 = true := by
 decide +kernel
def pointBounds22893 : List (Nat × Nat × Nat) := [(3004579840,101766228328579,101766609705796),(3004674048,101766636962835,101767018340290)]
theorem point_links_checked22893 : (cuts22893.take 2).map (fun c => (3004563457-1+2*2^9*c.k,101766162844725+c.lower,101766544221901+c.upper)) = pointBounds22893 := by
 decide +kernel
def cuts22894 : List PrefixCut := [⟨72,318596258,318596447⟩,
⟨128,571238234,571238571⟩]
theorem checked22894 : checkPrefixCuts (2^48) 3004694529 9 Manual.Count131072.C022894.packed 128 cuts22894 = true := by
 decide +kernel
def pointBounds22894 : List (Nat × Nat × Nat) := [(3004768256,101767045303276,101767426680973)]
theorem point_links_checked22894 : (cuts22894.take 1).map (fun c => (3004694529-1+2*2^9*c.k,101766726707018+c.lower,101767108084526+c.upper)) = pointBounds22894 := by
 decide +kernel
def cuts22895 : List PrefixCut := [⟨36,158589618,158589708⟩,
⟨128,574585492,574585811⟩]
theorem checked22895 : checkPrefixCuts (2^48) 3004825601 9 Manual.Count131072.C022895.packed 128 cuts22895 = true := by
 decide +kernel
def pointBounds22895 : List (Nat × Nat × Nat) := [(3004862464,101767456534870,101767837912805),(3004956672,101767872530744,101768253908908)]
theorem point_links_checked22895 : (cuts22895.take 2).map (fun c => (3004825601-1+2*2^9*c.k,101767297945252+c.lower,101767679323097+c.upper)) = pointBounds22895 := by
 decide +kernel
def cuts22896 : List PrefixCut := [⟨92,404929929,404930163⟩,
⟨128,561915279,561915598⟩]
theorem checked22896 : checkPrefixCuts (2^48) 3004956673 9 Manual.Count131072.C022896.packed 128 cuts22896 = true := by
 decide +kernel
def pointBounds22896 : List (Nat × Nat × Nat) := [(3005050880,101768277460673,101768658839071)]
theorem point_links_checked22896 : (cuts22896.take 1).map (fun c => (3004956673-1+2*2^9*c.k,101767872530744+c.lower,101768253908908+c.upper)) = pointBounds22896 := by
 decide +kernel
def cuts22897 : List PrefixCut := [⟨56,245871194,245871331⟩,
⟨128,564044975,564045293⟩]
theorem checked22897 : checkPrefixCuts (2^48) 3005087745 9 Manual.Count131072.C022897.packed 128 cuts22897 = true := by
 decide +kernel
def pointBounds22897 : List (Nat × Nat × Nat) := [(3005145088,101768680317217,101769061695837)]
theorem point_links_checked22897 : (cuts22897.take 1).map (fun c => (3005087745-1+2*2^9*c.k,101768434446023+c.lower,101768815824506+c.upper)) = pointBounds22897 := by
 decide +kernel
def cuts22898 : List PrefixCut := [⟨20,87386375,87386426⟩,
⟨112,496305643,496305926⟩,
⟨128,569920986,569921312⟩]
theorem checked22898 : checkPrefixCuts (2^48) 3005218817 9 Manual.Count131072.C022898.packed 128 cuts22898 = true := by
 decide +kernel
def pointBounds22898 : List (Nat × Nat × Nat) := [(3005239296,101769085877373,101769467256225),(3005333504,101769494796641,101769876175725)]
theorem point_links_checked22898 : (cuts22898.take 2).map (fun c => (3005218817-1+2*2^9*c.k,101768998490998+c.lower,101769379869799+c.upper)) = pointBounds22898 := by
 decide +kernel
def cuts22899 : List PrefixCut := [⟨76,329203369,329203559⟩,
⟨128,554349246,554349560⟩]
theorem checked22899 : checkPrefixCuts (2^48) 3005349889 9 Manual.Count131072.C022899.packed 128 cuts22899 = true := by
 decide +kernel
def pointBounds22899 : List (Nat × Nat × Nat) := [(3005427712,101769897615353,101770278994670)]
theorem point_links_checked22899 : (cuts22899.take 1).map (fun c => (3005349889-1+2*2^9*c.k,101769568411984+c.lower,101769949791111+c.upper)) = pointBounds22899 := by
 decide +kernel
def cuts22900 : List PrefixCut := [⟨40,176723635,176723739⟩,
⟨128,560693487,560693813⟩]
theorem checked22900 : checkPrefixCuts (2^48) 3005480961 9 Manual.Count131072.C022900.packed 128 cuts22900 = true := by
 decide +kernel
def pointBounds22900 : List (Nat × Nat × Nat) := [(3005521920,101770299484865,101770680864410)]
theorem point_links_checked22900 : (cuts22900.take 1).map (fun c => (3005480961-1+2*2^9*c.k,101770122761230+c.lower,101770504140671+c.upper)) = pointBounds22900 := by
 decide +kernel
def cuts22901 : List PrefixCut := [⟨4,17793447,17793456⟩,
⟨96,420386898,420387135⟩,
⟨128,563478284,563478603⟩]
theorem checked22901 : checkPrefixCuts (2^48) 3005612033 9 Manual.Count131072.C022901.packed 128 cuts22901 = true := by
 decide +kernel
def pointBounds22901 : List (Nat × Nat × Nat) := [(3005616128,101770701248164,101771082627940),(3005710336,101771103841615,101771485221619)]
theorem point_links_checked22901 : (cuts22901.take 2).map (fun c => (3005612033-1+2*2^9*c.k,101770683454717+c.lower,101771064834484+c.upper)) = pointBounds22901 := by
 decide +kernel
def cuts22902 : List PrefixCut := [⟨60,263609966,263610120⟩,
⟨128,564296686,564297009⟩]
theorem checked22902 : checkPrefixCuts (2^48) 3005743105 9 Manual.Count131072.C022902.packed 128 cuts22902 = true := by
 decide +kernel
def pointBounds22902 : List (Nat × Nat × Nat) := [(3005804544,101771510542967,101771891923207)]
theorem point_links_checked22902 : (cuts22902.take 1).map (fun c => (3005743105-1+2*2^9*c.k,101771246933001+c.lower,101771628313087+c.upper)) = pointBounds22902 := by
 decide +kernel
def cuts22903 : List PrefixCut := [⟨24,104878168,104878225⟩,
⟨116,496384413,496384693⟩,
⟨128,549851549,549851863⟩]
theorem checked22903 : checkPrefixCuts (2^48) 3005874177 9 Manual.Count131072.C022903.packed 128 cuts22903 = true := by
 decide +kernel
def pointBounds22903 : List (Nat × Nat × Nat) := [(3005898752,101771916107855,101772297488321),(3005992960,101772307614100,101772688994789)]
theorem point_links_checked22903 : (cuts22903.take 2).map (fun c => (3005874177-1+2*2^9*c.k,101771811229687+c.lower,101772192610096+c.upper)) = pointBounds22903 := by
 decide +kernel
def cuts22904 : List PrefixCut := [⟨80,349731395,349731591⟩,
⟨128,564153744,564154057⟩]
theorem checked22904 : checkPrefixCuts (2^48) 3006005249 9 Manual.Count131072.C022904.packed 128 cuts22904 = true := by
 decide +kernel
def pointBounds22904 : List (Nat × Nat × Nat) := [(3006087168,101772710812631,101773092193550)]
theorem point_links_checked22904 : (cuts22904.take 1).map (fun c => (3006005249-1+2*2^9*c.k,101772361081236+c.lower,101772742461959+c.upper)) = pointBounds22904 := by
 decide +kernel
def cuts22905 : List PrefixCut := [⟨44,191759865,191759974⟩,
⟨128,556825955,556826272⟩]
theorem checked22905 : checkPrefixCuts (2^48) 3006136321 9 Manual.Count131072.C022905.packed 128 cuts22905 = true := by
 decide +kernel
def pointBounds22905 : List (Nat × Nat × Nat) := [(3006181376,101773116994845,101773498375990)]
theorem point_links_checked22905 : (cuts22905.take 1).map (fun c => (3006136321-1+2*2^9*c.k,101772925234980+c.lower,101773306616016+c.upper)) = pointBounds22905 := by
 decide +kernel
def cuts22906 : List PrefixCut := [⟨8,37358063,37358083⟩,
⟨100,444919157,444919416⟩,
⟨128,568411484,568411811⟩]
theorem checked22906 : checkPrefixCuts (2^48) 3006267393 9 Manual.Count131072.C022906.packed 128 cuts22906 = true := by
 decide +kernel
def pointBounds22906 : List (Nat × Nat × Nat) := [(3006275584,101773519418998,101773900800371),(3006369792,101773926980092,101774308361704)]
theorem point_links_checked22906 : (cuts22906.take 2).map (fun c => (3006267393-1+2*2^9*c.k,101773482060935+c.lower,101773863442288+c.upper)) = pointBounds22906 := by
 decide +kernel
def cuts22907 : List PrefixCut := [⟨64,280123772,280123932⟩,
⟨128,559024373,559024688⟩]
theorem checked22907 : checkPrefixCuts (2^48) 3006398465 9 Manual.Count131072.C022907.packed 128 cuts22907 = true := by
 decide +kernel
def pointBounds22907 : List (Nat × Nat × Nat) := [(3006464000,101774330596191,101774711978031)]
theorem point_links_checked22907 : (cuts22907.take 1).map (fun c => (3006398465-1+2*2^9*c.k,101774050472419+c.lower,101774431854099+c.upper)) = pointBounds22907 := by
 decide +kernel
def cuts22908 : List PrefixCut := [⟨28,126481634,126481706⟩,
⟨120,533629927,533630234⟩,
⟨128,568830010,568830336⟩]
theorem checked22908 : checkPrefixCuts (2^48) 3006529537 9 Manual.Count131072.C022908.packed 128 cuts22908 = true := by
 decide +kernel
def pointBounds22908 : List (Nat × Nat × Nat) := [(3006558208,101774735978426,101775117360493),(3006652416,101775143126719,101775524509021)]
theorem point_links_checked22908 : (cuts22908.take 2).map (fun c => (3006529537-1+2*2^9*c.k,101774609496792+c.lower,101774990878787+c.upper)) = pointBounds22908 := by
 decide +kernel
def cuts22909 : List PrefixCut := [⟨84,368378077,368378289⟩,
⟨128,561409578,561409905⟩]
theorem checked22909 : checkPrefixCuts (2^48) 3006660609 9 Manual.Count131072.C022909.packed 128 cuts22909 = true := by
 decide +kernel
def pointBounds22909 : List (Nat × Nat × Nat) := [(3006746624,101775546704879,101775928087412)]
theorem point_links_checked22909 : (cuts22909.take 1).map (fun c => (3006660609-1+2*2^9*c.k,101775178326802+c.lower,101775559709123+c.upper)) = pointBounds22909 := by
 decide +kernel
def cuts22910 : List PrefixCut := [⟨48,201266361,201266481⟩,
⟨128,547062491,547062819⟩]
theorem checked22910 : checkPrefixCuts (2^48) 3006791681 9 Manual.Count131072.C022910.packed 128 cuts22910 = true := by
 decide +kernel
def pointBounds22910 : List (Nat × Nat × Nat) := [(3006840832,101775941002741,101776322385509)]
theorem point_links_checked22910 : (cuts22910.take 1).map (fun c => (3006791681-1+2*2^9*c.k,101775739736380+c.lower,101776121119028+c.upper)) = pointBounds22910 := by
 decide +kernel
def cuts22911 : List PrefixCut := [⟨12,55229174,55229206⟩,
⟨104,459986318,459986593⟩,
⟨128,565947471,565947806⟩]
theorem checked22911 : checkPrefixCuts (2^48) 3006922753 9 Manual.Count131072.C022911.packed 128 cuts22911 = true := by
 decide +kernel
def pointBounds22911 : List (Nat × Nat × Nat) := [(3006935040,101776342028045,101776723411053),(3007029248,101776746785189,101777128168440)]
theorem point_links_checked22911 : (cuts22911.take 2).map (fun c => (3006922753-1+2*2^9*c.k,101776286798871+c.lower,101776668181847+c.upper)) = pointBounds22911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000090
