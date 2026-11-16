import PlattAssemblyKernel
import PlattCertificates.Count131072.C016144
import PlattCertificates.Count131072.C016145
import PlattCertificates.Count131072.C016146
import PlattCertificates.Count131072.C016147
import PlattCertificates.Count131072.C016148
import PlattCertificates.Count131072.C016149
import PlattCertificates.Count131072.C016150
import PlattCertificates.Count131072.C016151
import PlattCertificates.Count131072.C016152
import PlattCertificates.Count131072.C016153
import PlattCertificates.Count131072.C016154
import PlattCertificates.Count131072.C016155
import PlattCertificates.Count131072.C016156
import PlattCertificates.Count131072.C016157
import PlattCertificates.Count131072.C016158
import PlattCertificates.Count131072.C016159
import PlattCertificates.Count131072.C016160
import PlattCertificates.Count131072.C016161
import PlattCertificates.Count131072.C016162
import PlattCertificates.Count131072.C016163
import PlattCertificates.Count131072.C016164
import PlattCertificates.Count131072.C016165
import PlattCertificates.Count131072.C016166
import PlattCertificates.Count131072.C016167
import PlattCertificates.Count131072.C016168
import PlattCertificates.Count131072.C016169
import PlattCertificates.Count131072.C016170
import PlattCertificates.Count131072.C016171
import PlattCertificates.Count131072.C016172
import PlattCertificates.Count131072.C016173
import PlattCertificates.Count131072.C016174
import PlattCertificates.Count131072.C016175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16144 : List PrefixCut := [⟨61,385569329,385569574⟩,
⟨126,796618301,796618810⟩,
⟨128,809894863,809895381⟩]
theorem checked16144 : checkPrefixCuts (2^48) 2119958529 9 Manual.Count131072.C016144.packed 128 cuts16144 = true := by
 decide +kernel
def pointBounds16144 : List (Nat × Nat × Nat) := [(2120020992,97232450225067,97232828888549),(2120087552,97232861274039,97233239937785)]
theorem point_links_checked16144 : (cuts16144.take 2).map (fun c => (2119958529-1+2*2^9*c.k,97232064655738+c.lower,97232443318975+c.upper)) = pointBounds16144 := by
 decide +kernel
def cuts16145 : List PrefixCut := [⟨63,400016506,400016764⟩,
⟨128,801082797,801083308⟩]
theorem checked16145 : checkPrefixCuts (2^48) 2120089601 9 Manual.Count131072.C016145.packed 128 cuts16145 = true := by
 decide +kernel
def pointBounds16145 : List (Nat × Nat × Nat) := [(2120154112,97233274567107,97233653231120),(2120220672,97233675633398,97234054297664)]
theorem point_links_checked16145 : (cuts16145.take 2).map (fun c => (2120089601-1+2*2^9*c.k,97232874550601+c.lower,97233253214356+c.upper)) = pointBounds16145 := by
 decide +kernel
def cuts16146 : List PrefixCut := [⟨65,410346552,410346816⟩,
⟨128,815104844,815105369⟩]
theorem checked16146 : checkPrefixCuts (2^48) 2120220673 9 Manual.Count131072.C016146.packed 128 cuts16146 = true := by
 decide +kernel
def pointBounds16146 : List (Nat × Nat × Nat) := [(2120287232,97234085979950,97234464644480)]
theorem point_links_checked16146 : (cuts16146.take 1).map (fun c => (2120220673-1+2*2^9*c.k,97233675633398+c.lower,97234054297664+c.upper)) = pointBounds16146 := by
 decide +kernel
def cuts16147 : List PrefixCut := [⟨2,12743912,12743920⟩,
⟨67,418152971,418153242⟩,
⟨128,802178170,802178688⟩]
theorem checked16147 : checkPrefixCuts (2^48) 2120351745 9 Manual.Count131072.C016147.packed 128 cuts16147 = true := by
 decide +kernel
def pointBounds16147 : List (Nat × Nat × Nat) := [(2120353792,97234503482154,97234882146953),(2120420352,97234908891213,97235287556275)]
theorem point_links_checked16147 : (cuts16147.take 2).map (fun c => (2120351745-1+2*2^9*c.k,97234490738242+c.lower,97234869403033+c.upper)) = pointBounds16147 := by
 decide +kernel
def cuts16148 : List PrefixCut := [⟨4,23627866,23627881⟩,
⟨69,425029394,425029674⟩,
⟨128,795226305,795226822⟩]
theorem checked16148 : checkPrefixCuts (2^48) 2120482817 9 Manual.Count131072.C016148.packed 128 cuts16148 = true := by
 decide +kernel
def pointBounds16148 : List (Nat × Nat × Nat) := [(2120486912,97235316544278,97235695209602),(2120553472,97235717945806,97236096611395)]
theorem point_links_checked16148 : (cuts16148.take 2).map (fun c => (2120482817-1+2*2^9*c.k,97235292916412+c.lower,97235671581721+c.upper)) = pointBounds16148 := by
 decide +kernel
def cuts16149 : List PrefixCut := [⟨6,37961507,37961531⟩,
⟨71,446770747,446771028⟩,
⟨128,807919193,807919703⟩]
theorem checked16149 : checkPrefixCuts (2^48) 2120613889 9 Manual.Count131072.C016149.packed 128 cuts16149 = true := by
 decide +kernel
def pointBounds16149 : List (Nat × Nat × Nat) := [(2120620032,97236126104224,97236504770074),(2120686592,97236534913464,97236913579571)]
theorem point_links_checked16149 : (cuts16149.take 2).map (fun c => (2120613889-1+2*2^9*c.k,97236088142717+c.lower,97236466808543+c.upper)) = pointBounds16149 := by
 decide +kernel
def cuts16150 : List PrefixCut := [⟨8,49506156,49506189⟩,
⟨73,459218817,459219114⟩,
⟨128,806011151,806011666⟩]
theorem checked16150 : checkPrefixCuts (2^48) 2120744961 9 Manual.Count131072.C016150.packed 128 cuts16150 = true := by
 decide +kernel
def pointBounds16150 : List (Nat × Nat × Nat) := [(2120753152,97236945568066,97237324234435),(2120819712,97237355280727,97237733947360)]
theorem point_links_checked16150 : (cuts16150.take 2).map (fun c => (2120744961-1+2*2^9*c.k,97236896061910+c.lower,97237274728246+c.upper)) = pointBounds16150 := by
 decide +kernel
def cuts16151 : List PrefixCut := [⟨10,64499984,64500025⟩,
⟨75,478433737,478434040⟩,
⟨128,821886746,821887268⟩]
theorem checked16151 : checkPrefixCuts (2^48) 2120876033 9 Manual.Count131072.C016151.packed 128 cuts16151 = true := by
 decide +kernel
def pointBounds16151 : List (Nat × Nat × Nat) := [(2120886272,97237766573045,97238145239937),(2120952832,97238180506798,97238559173952)]
theorem point_links_checked16151 : (cuts16151.take 2).map (fun c => (2120876033-1+2*2^9*c.k,97237702073061+c.lower,97238080739912+c.upper)) = pointBounds16151 := by
 decide +kernel
def cuts16152 : List PrefixCut := [⟨12,78032157,78032207⟩,
⟨77,490347378,490347698⟩,
⟨128,815333547,815334074⟩]
theorem checked16152 : checkPrefixCuts (2^48) 2121007105 9 Manual.Count131072.C016152.packed 128 cuts16152 = true := by
 decide +kernel
def pointBounds16152 : List (Nat × Nat × Nat) := [(2121019392,97238601991964,97238980659387),(2121085952,97239014307185,97239392974878)]
theorem point_links_checked16152 : (cuts16152.take 2).map (fun c => (2121007105-1+2*2^9*c.k,97238523959807+c.lower,97238902627180+c.upper)) = pointBounds16152 := by
 decide +kernel
def cuts16153 : List PrefixCut := [⟨14,85591171,85591223⟩,
⟨79,500667265,500667581⟩,
⟨128,808383089,808383603⟩]
theorem checked16153 : checkPrefixCuts (2^48) 2121138177 9 Manual.Count131072.C016153.packed 128 cuts16153 = true := by
 decide +kernel
def pointBounds16153 : List (Nat × Nat × Nat) := [(2121152512,97239424884525,97239803552477),(2121219072,97239839960619,97240218628835)]
theorem point_links_checked16153 : (cuts16153.take 2).map (fun c => (2121138177-1+2*2^9*c.k,97239339293354+c.lower,97239717961254+c.upper)) = pointBounds16153 := by
 decide +kernel
def cuts16154 : List PrefixCut := [⟨16,99253032,99253095⟩,
⟨81,513905015,513905347⟩,
⟨128,806740857,806741381⟩]
theorem checked16154 : checkPrefixCuts (2^48) 2121269249 9 Manual.Count131072.C016154.packed 128 cuts16154 = true := by
 decide +kernel
def pointBounds16154 : List (Nat × Nat × Nat) := [(2121285632,97240246929475,97240625597952),(2121352192,97240661581458,97241040250204)]
theorem point_links_checked16154 : (cuts16154.take 2).map (fun c => (2121269249-1+2*2^9*c.k,97240147676443+c.lower,97240526344857+c.upper)) = pointBounds16154 := by
 decide +kernel
def cuts16155 : List PrefixCut := [⟨18,113311236,113311309⟩,
⟨83,528600545,528600881⟩,
⟨128,810140637,810141150⟩]
theorem checked16155 : checkPrefixCuts (2^48) 2121400321 9 Manual.Count131072.C016155.packed 128 cuts16155 = true := by
 decide +kernel
def pointBounds16155 : List (Nat × Nat × Nat) := [(2121418752,97241067728536,97241446397547),(2121485312,97241483017845,97241861687119)]
theorem point_links_checked16155 : (cuts16155.take 2).map (fun c => (2121400321-1+2*2^9*c.k,97240954417300+c.lower,97241333086238+c.upper)) = pointBounds16155 := by
 decide +kernel
def cuts16156 : List PrefixCut := [⟨20,123254806,123254886⟩,
⟨85,523128104,523128446⟩,
⟨128,799078626,799079144⟩]
theorem checked16156 : checkPrefixCuts (2^48) 2121531393 9 Manual.Count131072.C016156.packed 128 cuts16156 = true := by
 decide +kernel
def pointBounds16156 : List (Nat × Nat × Nat) := [(2121551872,97241887812743,97242266482274),(2121618432,97242287686041,97242666355834)]
theorem point_links_checked16156 : (cuts16156.take 2).map (fun c => (2121531393-1+2*2^9*c.k,97241764557937+c.lower,97242143227388+c.upper)) = pointBounds16156 := by
 decide +kernel
def cuts16157 : List PrefixCut := [⟨22,142881755,142881842⟩,
⟨87,561435524,561435880⟩,
⟨128,825960122,825960646⟩]
theorem checked16157 : checkPrefixCuts (2^48) 2121662465 9 Manual.Count131072.C016157.packed 128 cuts16157 = true := by
 decide +kernel
def pointBounds16157 : List (Nat × Nat × Nat) := [(2121684992,97242706518318,97243085188374),(2121751552,97243125072087,97243503742412)]
theorem point_links_checked16157 : (cuts16157.take 2).map (fun c => (2121662465-1+2*2^9*c.k,97242563636563+c.lower,97242942306532+c.upper)) = pointBounds16157 := by
 decide +kernel
def cuts16158 : List PrefixCut := [⟨24,149240443,149240542⟩,
⟨89,561400519,561400876⟩,
⟨128,808000562,808001077⟩]
theorem checked16158 : checkPrefixCuts (2^48) 2121793537 9 Manual.Count131072.C016158.packed 128 cuts16158 = true := by
 decide +kernel
def pointBounds16158 : List (Nat × Nat × Nat) := [(2121818112,97243538837128,97243917507720),(2121884672,97243950997204,97244329668054)]
theorem point_links_checked16158 : (cuts16158.take 2).map (fun c => (2121793537-1+2*2^9*c.k,97243389596685+c.lower,97243768267178+c.upper)) = pointBounds16158 := by
 decide +kernel
def cuts16159 : List PrefixCut := [⟨26,166210345,166210452⟩,
⟨91,570120521,570120891⟩,
⟨128,808879253,808879777⟩]
theorem checked16159 : checkPrefixCuts (2^48) 2121924609 9 Manual.Count131072.C016159.packed 128 cuts16159 = true := by
 decide +kernel
def pointBounds16159 : List (Nat × Nat × Nat) := [(2121951232,97244363807592,97244742478707),(2122017792,97244767717768,97245146389146)]
theorem point_links_checked16159 : (cuts16159.take 2).map (fun c => (2121924609-1+2*2^9*c.k,97244197597247+c.lower,97244576268255+c.upper)) = pointBounds16159 := by
 decide +kernel
def cuts16160 : List PrefixCut := [⟨28,183443418,183443534⟩,
⟨93,593164331,593164720⟩,
⟨128,816522502,816523032⟩]
theorem checked16160 : checkPrefixCuts (2^48) 2122055681 9 Manual.Count131072.C016160.packed 128 cuts16160 = true := by
 decide +kernel
def pointBounds16160 : List (Nat × Nat × Nat) := [(2122084352,97245189919918,97245568591566),(2122150912,97245599640831,97245978312752)]
theorem point_links_checked16160 : (cuts16160.take 2).map (fun c => (2122055681-1+2*2^9*c.k,97245006476500+c.lower,97245385148032+c.upper)) = pointBounds16160 := by
 decide +kernel
def cuts16161 : List PrefixCut := [⟨30,189400489,189400614⟩,
⟨95,606390307,606390696⟩,
⟨128,815676045,815676570⟩]
theorem checked16161 : checkPrefixCuts (2^48) 2122186753 9 Manual.Count131072.C016161.packed 128 cuts16161 = true := by
 decide +kernel
def pointBounds16161 : List (Nat × Nat × Nat) := [(2122217472,97246012399491,97246391071678),(2122284032,97246429389309,97246808061760)]
theorem point_links_checked16161 : (cuts16161.take 2).map (fun c => (2122186753-1+2*2^9*c.k,97245822999002+c.lower,97246201671064+c.upper)) = pointBounds16161 := by
 decide +kernel
def cuts16162 : List PrefixCut := [⟨32,196550436,196550562⟩,
⟨97,613779408,613779795⟩,
⟨128,806872613,806873125⟩]
theorem checked16162 : checkPrefixCuts (2^48) 2122317825 9 Manual.Count131072.C016162.packed 128 cuts16162 = true := by
 decide +kernel
def pointBounds16162 : List (Nat × Nat × Nat) := [(2122350592,97246835225483,97247213898196),(2122417152,97247252454455,97247631127429)]
theorem point_links_checked16162 : (cuts16162.take 2).map (fun c => (2122317825-1+2*2^9*c.k,97246638675047+c.lower,97247017347634+c.upper)) = pointBounds16162 := by
 decide +kernel
def cuts16163 : List PrefixCut := [⟨34,218287399,218287537⟩,
⟨99,623289682,623290084⟩,
⟨128,804038089,804038603⟩]
theorem checked16163 : checkPrefixCuts (2^48) 2122448897 9 Manual.Count131072.C016163.packed 128 cuts16163 = true := by
 decide +kernel
def pointBounds16163 : List (Nat × Nat × Nat) := [(2122483712,97247663835059,97248042508296),(2122550272,97248068837342,97248447510843)]
theorem point_links_checked16163 : (cuts16163.take 2).map (fun c => (2122448897-1+2*2^9*c.k,97247445547660+c.lower,97247824220759+c.upper)) = pointBounds16163 := by
 decide +kernel
def cuts16164 : List PrefixCut := [⟨36,224904242,224904389⟩,
⟨101,638235387,638235794⟩,
⟨128,809822978,809823494⟩]
theorem checked16164 : checkPrefixCuts (2^48) 2122579969 9 Manual.Count131072.C016164.packed 128 cuts16164 = true := by
 decide +kernel
def pointBounds16164 : List (Nat × Nat × Nat) := [(2122616832,97248474489991,97248853163751),(2122683392,97248887821136,97249266495156)]
theorem point_links_checked16164 : (cuts16164.take 2).map (fun c => (2122579969-1+2*2^9*c.k,97248249585749+c.lower,97248628259362+c.upper)) = pointBounds16164 := by
 decide +kernel
def cuts16165 : List PrefixCut := [⟨38,232978852,232979002⟩,
⟨103,633422078,633422484⟩,
⟨128,786700994,786701500⟩]
theorem checked16165 : checkPrefixCuts (2^48) 2122711041 9 Manual.Count131072.C016165.packed 128 cuts16165 = true := by
 decide +kernel
def pointBounds16165 : List (Nat × Nat × Nat) := [(2122749952,97249292387579,97249671061858),(2122816512,97249692830805,97250071505340)]
theorem point_links_checked16165 : (cuts16165.take 2).map (fun c => (2122711041-1+2*2^9*c.k,97249059408727+c.lower,97249438082856+c.upper)) = pointBounds16165 := by
 decide +kernel
def cuts16166 : List PrefixCut := [⟨40,247947273,247947435⟩,
⟨105,659370268,659370698⟩,
⟨128,803491232,803491756⟩]
theorem checked16166 : checkPrefixCuts (2^48) 2122842113 9 Manual.Count131072.C016166.packed 128 cuts16166 = true := by
 decide +kernel
def pointBounds16166 : List (Nat × Nat × Nat) := [(2122883072,97250094056994,97250472731791),(2122949632,97250505479989,97250884155054)]
theorem point_links_checked16166 : (cuts16166.take 2).map (fun c => (2122842113-1+2*2^9*c.k,97249846109721+c.lower,97250224784356+c.upper)) = pointBounds16166 := by
 decide +kernel
def cuts16167 : List PrefixCut := [⟨42,263046469,263046638⟩,
⟨107,674045839,674046274⟩,
⟨128,804767468,804767988⟩]
theorem checked16167 : checkPrefixCuts (2^48) 2122973185 9 Manual.Count131072.C016167.packed 128 cuts16167 = true := by
 decide +kernel
def pointBounds16167 : List (Nat × Nat × Nat) := [(2123016192,97250912647422,97251291322750),(2123082752,97251323646792,97251702322386)]
theorem point_links_checked16167 : (cuts16167.take 2).map (fun c => (2122973185-1+2*2^9*c.k,97250649600953+c.lower,97251028276112+c.upper)) = pointBounds16167 := by
 decide +kernel
def cuts16168 : List PrefixCut := [⟨44,278541431,278541612⟩,
⟨109,691105947,691106394⟩,
⟨128,813467550,813468074⟩]
theorem checked16168 : checkPrefixCuts (2^48) 2123104257 9 Manual.Count131072.C016168.packed 128 cuts16168 = true := by
 decide +kernel
def pointBounds16168 : List (Nat × Nat × Nat) := [(2123149312,97251732909852,97252111585712),(2123215872,97252145474368,97252524150494)]
theorem point_links_checked16168 : (cuts16168.take 2).map (fun c => (2123104257-1+2*2^9*c.k,97251454368421+c.lower,97251833044100+c.upper)) = pointBounds16168 := by
 decide +kernel
def cuts16169 : List PrefixCut := [⟨46,288864381,288864563⟩,
⟨111,695040013,695040455⟩,
⟨128,800823864,800824374⟩]
theorem checked16169 : checkPrefixCuts (2^48) 2123235329 9 Manual.Count131072.C016169.packed 128 cuts16169 = true := by
 decide +kernel
def pointBounds16169 : List (Nat × Nat × Nat) := [(2123282432,97252556700352,97252935376737),(2123348992,97252962875984,97253341552629)]
theorem point_links_checked16169 : (cuts16169.take 2).map (fun c => (2123235329-1+2*2^9*c.k,97252267835971+c.lower,97252646512174+c.upper)) = pointBounds16169 := by
 decide +kernel
def cuts16170 : List PrefixCut := [⟨48,303427896,303428089⟩,
⟨113,720580194,720580659⟩,
⟨128,814030039,814030564⟩]
theorem checked16170 : checkPrefixCuts (2^48) 2123366401 9 Manual.Count131072.C016170.packed 128 cuts16170 = true := by
 decide +kernel
def pointBounds16170 : List (Nat × Nat × Nat) := [(2123415552,97253372087731,97253750764637),(2123482112,97253789240029,97254167917207)]
theorem point_links_checked16170 : (cuts16170.take 2).map (fun c => (2123366401-1+2*2^9*c.k,97253068659835+c.lower,97253447336548+c.upper)) = pointBounds16170 := by
 decide +kernel
def cuts16171 : List PrefixCut := [⟨50,316266501,316266703⟩,
⟨115,726367570,726368034⟩,
⟨128,807750038,807750553⟩]
theorem checked16171 : checkPrefixCuts (2^48) 2123497473 9 Manual.Count131072.C016171.packed 128 cuts16171 = true := by
 decide +kernel
def pointBounds16171 : List (Nat × Nat × Nat) := [(2123548672,97254198956375,97254577633815),(2123615232,97254609057444,97254987735146)]
theorem point_links_checked16171 : (cuts16171.take 2).map (fun c => (2123497473-1+2*2^9*c.k,97253882689874+c.lower,97254261367112+c.upper)) = pointBounds16171 := by
 decide +kernel
def cuts16172 : List PrefixCut := [⟨52,325392191,325392401⟩,
⟨117,730431111,730431575⟩,
⟨128,799880231,799880740⟩]
theorem checked16172 : checkPrefixCuts (2^48) 2123628545 9 Manual.Count131072.C016172.packed 128 cuts16172 = true := by
 decide +kernel
def pointBounds16172 : List (Nat × Nat × Nat) := [(2123681792,97255015832103,97255394510066),(2123748352,97255420871023,97255799549240)]
theorem point_links_checked16172 : (cuts16172.take 2).map (fun c => (2123628545-1+2*2^9*c.k,97254690439912+c.lower,97255069117665+c.upper)) = pointBounds16172 := by
 decide +kernel
def cuts16173 : List PrefixCut := [⟨54,340215813,340216033⟩,
⟨119,757819775,757820262⟩,
⟨128,815337032,815337555⟩]
theorem checked16173 : checkPrefixCuts (2^48) 2123759617 9 Manual.Count131072.C016173.packed 128 cuts16173 = true := by
 decide +kernel
def pointBounds16173 : List (Nat × Nat × Nat) := [(2123814912,97255830535956,97256209214438),(2123881472,97256248139918,97256626818667)]
theorem point_links_checked16173 : (cuts16173.take 2).map (fun c => (2123759617-1+2*2^9*c.k,97255490320143+c.lower,97255868998405+c.upper)) = pointBounds16173 := by
 decide +kernel
def cuts16174 : List PrefixCut := [⟨56,345893336,345893557⟩,
⟨121,761880818,761881301⟩,
⟨128,805347377,805347887⟩]
theorem checked16174 : checkPrefixCuts (2^48) 2123890689 9 Manual.Count131072.C016174.packed 128 cuts16174 = true := by
 decide +kernel
def pointBounds16174 : List (Nat × Nat × Nat) := [(2123948032,97256651550511,97257030229517),(2124014592,97257067537993,97257446217261)]
theorem point_links_checked16174 : (cuts16174.take 2).map (fun c => (2123890689-1+2*2^9*c.k,97256305657175+c.lower,97256684335960+c.upper)) = pointBounds16174 := by
 decide +kernel
def cuts16175 : List PrefixCut := [⟨58,367207181,367207418⟩,
⟨123,776675463,776675964⟩,
⟨128,808213260,808213782⟩]
theorem checked16175 : checkPrefixCuts (2^48) 2124021761 9 Manual.Count131072.C016175.packed 128 cuts16175 = true := by
 decide +kernel
def pointBounds16175 : List (Nat × Nat × Nat) := [(2124081152,97257478211733,97257856891265),(2124147712,97257887680015,97258266359811)]
theorem point_links_checked16175 : (cuts16175.take 2).map (fun c => (2124021761-1+2*2^9*c.k,97257111004552+c.lower,97257489683847+c.upper)) = pointBounds16175 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000192
