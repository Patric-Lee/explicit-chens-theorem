import PlattAssemblyKernel
import PlattCertificates.Count131072.C026112
import PlattCertificates.Count131072.C026113
import PlattCertificates.Count131072.C026114
import PlattCertificates.Count131072.C026115
import PlattCertificates.Count131072.C026116
import PlattCertificates.Count131072.C026117
import PlattCertificates.Count131072.C026118
import PlattCertificates.Count131072.C026119
import PlattCertificates.Count131072.C026120
import PlattCertificates.Count131072.C026121
import PlattCertificates.Count131072.C026122
import PlattCertificates.Count131072.C026123
import PlattCertificates.Count131072.C026124
import PlattCertificates.Count131072.C026125
import PlattCertificates.Count131072.C026126
import PlattCertificates.Count131072.C026127
import PlattCertificates.Count131072.C026128
import PlattCertificates.Count131072.C026129
import PlattCertificates.Count131072.C026130
import PlattCertificates.Count131072.C026131
import PlattCertificates.Count131072.C026132
import PlattCertificates.Count131072.C026133
import PlattCertificates.Count131072.C026134
import PlattCertificates.Count131072.C026135
import PlattCertificates.Count131072.C026136
import PlattCertificates.Count131072.C026137
import PlattCertificates.Count131072.C026138
import PlattCertificates.Count131072.C026139
import PlattCertificates.Count131072.C026140
import PlattCertificates.Count131072.C026141
import PlattCertificates.Count131072.C026142
import PlattCertificates.Count131072.C026143
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000191
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26112 : List PrefixCut := [⟨59,224505407,224505535⟩,
⟨128,492132352,492132632⟩]
theorem checked26112 : checkPrefixCuts (2^48) 3426484225 9 Manual.Count131072.C026112.packed 128 cuts26112 = true := by
 decide +kernel
def pointBounds26112 : List (Nat × Nat × Nat) := [(3426544640,103456063255635,103456445584819)]
theorem point_links_checked26112 : (cuts26112.take 1).map (fun c => (3426484225-1+2*2^9*c.k,103455838750228+c.lower,103456221079284+c.upper)) = pointBounds26112 := by
 decide +kernel
def cuts26113 : List PrefixCut := [⟨36,141204273,141204349⟩,
⟨128,487513688,487513958⟩]
theorem checked26113 : checkPrefixCuts (2^48) 3426615297 9 Manual.Count131072.C026113.packed 128 cuts26113 = true := by
 decide +kernel
def pointBounds26113 : List (Nat × Nat × Nat) := [(3426652160,103456472086853,103456854416265)]
theorem point_links_checked26113 : (cuts26113.take 1).map (fun c => (3426615297-1+2*2^9*c.k,103456330882580+c.lower,103456713211916+c.upper)) = pointBounds26113 := by
 decide +kernel
def cuts26114 : List PrefixCut := [⟨13,48134282,48134309⟩,
⟨118,447904580,447904831⟩,
⟨128,486180680,486180952⟩]
theorem checked26114 : checkPrefixCuts (2^48) 3426746369 9 Manual.Count131072.C026114.packed 128 cuts26114 = true := by
 decide +kernel
def pointBounds26114 : List (Nat × Nat × Nat) := [(3426759680,103456866530550,103457248860183),(3426867200,103457266300848,103457648630705)]
theorem point_links_checked26114 : (cuts26114.take 2).map (fun c => (3426746369-1+2*2^9*c.k,103456818396268+c.lower,103457200725874+c.upper)) = pointBounds26114 := by
 decide +kernel
def cuts26115 : List PrefixCut := [⟨95,363863636,363863841⟩,
⟨128,489611855,489612131⟩]
theorem checked26115 : checkPrefixCuts (2^48) 3426877441 9 Manual.Count131072.C026115.packed 128 cuts26115 = true := by
 decide +kernel
def pointBounds26115 : List (Nat × Nat × Nat) := [(3426974720,103457668440584,103458050770667)]
theorem point_links_checked26115 : (cuts26115.take 1).map (fun c => (3426877441-1+2*2^9*c.k,103457304576948+c.lower,103457686906826+c.upper)) = pointBounds26115 := by
 decide +kernel
def cuts26116 : List PrefixCut := [⟨72,272354340,272354497⟩,
⟨128,492139121,492139400⟩]
theorem checked26116 : checkPrefixCuts (2^48) 3427008513 9 Manual.Count131072.C026116.packed 128 cuts26116 = true := by
 decide +kernel
def pointBounds26116 : List (Nat × Nat × Nat) := [(3427082240,103458066543143,103458448873454)]
theorem point_links_checked26116 : (cuts26116.take 1).map (fun c => (3427008513-1+2*2^9*c.k,103457794188803+c.lower,103458176518957+c.upper)) = pointBounds26116 := by
 decide +kernel
def cuts26117 : List PrefixCut := [⟨49,186764859,186764960⟩,
⟨128,491299075,491299343⟩]
theorem checked26117 : checkPrefixCuts (2^48) 3427139585 9 Manual.Count131072.C026117.packed 128 cuts26117 = true := by
 decide +kernel
def pointBounds26117 : List (Nat × Nat × Nat) := [(3427189760,103458473092783,103458855423317)]
theorem point_links_checked26117 : (cuts26117.take 1).map (fun c => (3427139585-1+2*2^9*c.k,103458286327924+c.lower,103458668658357+c.upper)) = pointBounds26117 := by
 decide +kernel
def cuts26118 : List PrefixCut := [⟨26,95925134,95925189⟩,
⟨128,491773020,491773298⟩]
theorem checked26118 : checkPrefixCuts (2^48) 3427270657 9 Manual.Count131072.C026118.packed 128 cuts26118 = true := by
 decide +kernel
def pointBounds26118 : List (Nat × Nat × Nat) := [(3427297280,103458873552133,103459255882889)]
theorem point_links_checked26118 : (cuts26118.take 1).map (fun c => (3427270657-1+2*2^9*c.k,103458777626999+c.lower,103459159957700+c.upper)) = pointBounds26118 := by
 decide +kernel
def cuts26119 : List PrefixCut := [⟨3,12072349,12072356⟩,
⟨108,418501559,418501800⟩,
⟨128,496188941,496189223⟩]
theorem checked26119 : checkPrefixCuts (2^48) 3427401729 9 Manual.Count131072.C026119.packed 128 cuts26119 = true := by
 decide +kernel
def pointBounds26119 : List (Nat × Nat × Nat) := [(3427404800,103459281472368,103459663803354),(3427512320,103459687901578,103460070232798)]
theorem point_links_checked26119 : (cuts26119.take 2).map (fun c => (3427401729-1+2*2^9*c.k,103459269400019+c.lower,103459651730998+c.upper)) = pointBounds26119 := by
 decide +kernel
def cuts26120 : List PrefixCut := [⟨85,328646942,328647122⟩,
⟨128,491324904,491325175⟩]
theorem checked26120 : checkPrefixCuts (2^48) 3427532801 9 Manual.Count131072.C026120.packed 128 cuts26120 = true := by
 decide +kernel
def pointBounds26120 : List (Nat × Nat × Nat) := [(3427619840,103460094235902,103460476567343)]
theorem point_links_checked26120 : (cuts26120.take 1).map (fun c => (3427532801-1+2*2^9*c.k,103459765588960+c.lower,103460147920221+c.upper)) = pointBounds26120 := by
 decide +kernel
def cuts26121 : List PrefixCut := [⟨62,237731108,237731242⟩,
⟨128,487939314,487939586⟩]
theorem checked26121 : checkPrefixCuts (2^48) 3427663873 9 Manual.Count131072.C026121.packed 128 cuts26121 = true := by
 decide +kernel
def pointBounds26121 : List (Nat × Nat × Nat) := [(3427727360,103460494644972,103460876976638)]
theorem point_links_checked26121 : (cuts26121.take 1).map (fun c => (3427663873-1+2*2^9*c.k,103460256913864+c.lower,103460639245396+c.upper)) = pointBounds26121 := by
 decide +kernel
def cuts26122 : List PrefixCut := [⟨39,150106157,150106242⟩,
⟨128,500484039,500484321⟩]
theorem checked26122 : checkPrefixCuts (2^48) 3427794945 9 Manual.Count131072.C026122.packed 128 cuts26122 = true := by
 decide +kernel
def pointBounds26122 : List (Nat × Nat × Nat) := [(3427834880,103460894959335,103461277291224)]
theorem point_links_checked26122 : (cuts26122.take 1).map (fun c => (3427794945-1+2*2^9*c.k,103460744853178+c.lower,103461127184982+c.upper)) = pointBounds26122 := by
 decide +kernel
def cuts26123 : List PrefixCut := [⟨16,59284944,59284977⟩,
⟨121,460641647,460641907⟩,
⟨128,487245043,487245319⟩]
theorem checked26123 : checkPrefixCuts (2^48) 3427926017 9 Manual.Count131072.C026123.packed 128 cuts26123 = true := by
 decide +kernel
def pointBounds26123 : List (Nat × Nat × Nat) := [(3427942400,103461304622161,103461686954280),(3428049920,103461705978864,103462088311210)]
theorem point_links_checked26123 : (cuts26123.take 2).map (fun c => (3427926017-1+2*2^9*c.k,103461245337217+c.lower,103461627669303+c.upper)) = pointBounds26123 := by
 decide +kernel
def cuts26124 : List PrefixCut := [⟨98,377039760,377039975⟩,
⟨128,489607618,489607897⟩]
theorem checked26124 : checkPrefixCuts (2^48) 3428057089 9 Manual.Count131072.C026124.packed 128 cuts26124 = true := by
 decide +kernel
def pointBounds26124 : List (Nat × Nat × Nat) := [(3428157440,103462109622020,103462491954597)]
theorem point_links_checked26124 : (cuts26124.take 1).map (fun c => (3428057089-1+2*2^9*c.k,103461732582260+c.lower,103462114914622+c.upper)) = pointBounds26124 := by
 decide +kernel
def cuts26125 : List PrefixCut := [⟨75,281948903,281949064⟩,
⟨128,489424578,489424854⟩]
theorem checked26125 : checkPrefixCuts (2^48) 3428188161 9 Manual.Count131072.C026125.packed 128 cuts26125 = true := by
 decide +kernel
def pointBounds26125 : List (Nat × Nat × Nat) := [(3428264960,103462504138781,103462886471583)]
theorem point_links_checked26125 : (cuts26125.take 1).map (fun c => (3428188161-1+2*2^9*c.k,103462222189878+c.lower,103462604522519+c.upper)) = pointBounds26125 := by
 decide +kernel
def cuts26126 : List PrefixCut := [⟨52,203613555,203613669⟩,
⟨128,498519183,498519462⟩]
theorem checked26126 : checkPrefixCuts (2^48) 3428319233 9 Manual.Count131072.C026126.packed 128 cuts26126 = true := by
 decide +kernel
def pointBounds26126 : List (Nat × Nat × Nat) := [(3428372480,103462915228011,103463297561042)]
theorem point_links_checked26126 : (cuts26126.take 1).map (fun c => (3428319233-1+2*2^9*c.k,103462711614456+c.lower,103463093947373+c.upper)) = pointBounds26126 := by
 decide +kernel
def cuts26127 : List PrefixCut := [⟨29,110341577,110341639⟩,
⟨128,490372384,490372662⟩]
theorem checked26127 : checkPrefixCuts (2^48) 3428450305 9 Manual.Count131072.C026127.packed 128 cuts26127 = true := by
 decide +kernel
def pointBounds26127 : List (Nat × Nat × Nat) := [(3428480000,103463320475216,103463702808474)]
theorem point_links_checked26127 : (cuts26127.take 1).map (fun c => (3428450305-1+2*2^9*c.k,103463210133639+c.lower,103463592466835+c.upper)) = pointBounds26127 := by
 decide +kernel
def cuts26128 : List PrefixCut := [⟨6,23151223,23151236⟩,
⟨111,425581751,425581986⟩,
⟨128,488465506,488465777⟩]
theorem checked26128 : checkPrefixCuts (2^48) 3428581377 9 Manual.Count131072.C026128.packed 128 cuts26128 = true := by
 decide +kernel
def pointBounds26128 : List (Nat × Nat × Nat) := [(3428587520,103463723657246,103464105990733),(3428695040,103464126087774,103464508421483)]
theorem point_links_checked26128 : (cuts26128.take 2).map (fun c => (3428581377-1+2*2^9*c.k,103463700506023+c.lower,103464082839497+c.upper)) = pointBounds26128 := by
 decide +kernel
def cuts26129 : List PrefixCut := [⟨88,335511587,335511780⟩,
⟨128,488775155,488775432⟩]
theorem checked26129 : checkPrefixCuts (2^48) 3428712449 9 Manual.Count131072.C026129.packed 128 cuts26129 = true := by
 decide +kernel
def pointBounds26129 : List (Nat × Nat × Nat) := [(3428802560,103464524483116,103464906817054)]
theorem point_links_checked26129 : (cuts26129.take 1).map (fun c => (3428712449-1+2*2^9*c.k,103464188971529+c.lower,103464571305274+c.upper)) = pointBounds26129 := by
 decide +kernel
def cuts26130 : List PrefixCut := [⟨65,247171570,247171709⟩,
⟨128,487360960,487361234⟩]
theorem checked26130 : checkPrefixCuts (2^48) 3428843521 9 Manual.Count131072.C026130.packed 128 cuts26130 = true := by
 decide +kernel
def pointBounds26130 : List (Nat × Nat × Nat) := [(3428910080,103464924918254,103465307252415)]
theorem point_links_checked26130 : (cuts26130.take 1).map (fun c => (3428843521-1+2*2^9*c.k,103464677746684+c.lower,103465060080706+c.upper)) = pointBounds26130 := by
 decide +kernel
def cuts26131 : List PrefixCut := [⟨42,155882601,155882688⟩,
⟨128,489722713,489722985⟩]
theorem checked26131 : checkPrefixCuts (2^48) 3428974593 9 Manual.Count131072.C026131.packed 128 cuts26131 = true := by
 decide +kernel
def pointBounds26131 : List (Nat × Nat × Nat) := [(3429017600,103465320990245,103465703324628)]
theorem point_links_checked26131 : (cuts26131.take 1).map (fun c => (3428974593-1+2*2^9*c.k,103465165107644+c.lower,103465547441940+c.upper)) = pointBounds26131 := by
 decide +kernel
def cuts26132 : List PrefixCut := [⟨19,72315848,72315889⟩,
⟨124,473123711,473123981⟩,
⟨128,488801176,488801454⟩]
theorem checked26132 : checkPrefixCuts (2^48) 3429105665 9 Manual.Count131072.C026132.packed 128 cuts26132 = true := by
 decide +kernel
def pointBounds26132 : List (Nat × Nat × Nat) := [(3429125120,103465727146205,103466109480814),(3429232640,103466127954068,103466510288906)]
theorem point_links_checked26132 : (cuts26132.take 2).map (fun c => (3429105665-1+2*2^9*c.k,103465654830357+c.lower,103466037164925+c.upper)) = pointBounds26132 := by
 decide +kernel
def cuts26133 : List PrefixCut := [⟨101,389960560,389960771⟩,
⟨128,495759247,495759517⟩]
theorem checked26133 : checkPrefixCuts (2^48) 3429236737 9 Manual.Count131072.C026133.packed 128 cuts26133 = true := by
 decide +kernel
def pointBounds26133 : List (Nat × Nat × Nat) := [(3429340160,103466533592093,103466915927150)]
theorem point_links_checked26133 : (cuts26133.take 1).map (fun c => (3429236737-1+2*2^9*c.k,103466143631533+c.lower,103466525966379+c.upper)) = pointBounds26133 := by
 decide +kernel
def cuts26134 : List PrefixCut := [⟨78,300975660,300975828⟩,
⟨128,492539309,492539586⟩]
theorem checked26134 : checkPrefixCuts (2^48) 3429367809 9 Manual.Count131072.C026134.packed 128 cuts26134 = true := by
 decide +kernel
def pointBounds26134 : List (Nat × Nat × Nat) := [(3429447680,103466940366440,103467322701724)]
theorem point_links_checked26134 : (cuts26134.take 1).map (fun c => (3429367809-1+2*2^9*c.k,103466639390780+c.lower,103467021725896+c.upper)) = pointBounds26134 := by
 decide +kernel
def cuts26135 : List PrefixCut := [⟨55,211832927,211833047⟩,
⟨128,498347647,498347928⟩]
theorem checked26135 : checkPrefixCuts (2^48) 3429498881 9 Manual.Count131072.C026135.packed 128 cuts26135 = true := by
 decide +kernel
def pointBounds26135 : List (Nat × Nat × Nat) := [(3429555200,103467343763016,103467726098529)]
theorem point_links_checked26135 : (cuts26135.take 1).map (fun c => (3429498881-1+2*2^9*c.k,103467131930089+c.lower,103467514265482+c.upper)) = pointBounds26135 := by
 decide +kernel
def cuts26136 : List PrefixCut := [⟨32,121054884,121054955⟩,
⟨128,488069900,488070178⟩]
theorem checked26136 : checkPrefixCuts (2^48) 3429629953 9 Manual.Count131072.C026136.packed 128 cuts26136 = true := by
 decide +kernel
def pointBounds26136 : List (Nat × Nat × Nat) := [(3429662720,103467751332620,103468133668365)]
theorem point_links_checked26136 : (cuts26136.take 1).map (fun c => (3429629953-1+2*2^9*c.k,103467630277736+c.lower,103468012613410+c.upper)) = pointBounds26136 := by
 decide +kernel
def cuts26137 : List PrefixCut := [⟨9,34386601,34386622⟩,
⟨114,432410932,432411176⟩,
⟨128,486902363,486902635⟩]
theorem checked26137 : checkPrefixCuts (2^48) 3429761025 9 Manual.Count131072.C026137.packed 128 cuts26137 = true := by
 decide +kernel
def pointBounds26137 : List (Nat × Nat × Nat) := [(3429770240,103468152734237,103468535070210),(3429877760,103468550758568,103468933094764)]
theorem point_links_checked26137 : (cuts26137.take 2).map (fun c => (3429761025-1+2*2^9*c.k,103468118347636+c.lower,103468500683588+c.upper)) = pointBounds26137 := by
 decide +kernel
def cuts26138 : List PrefixCut := [⟨91,350742046,350742239⟩,
⟨128,495090070,495090343⟩]
theorem checked26138 : checkPrefixCuts (2^48) 3429892097 9 Manual.Count131072.C026138.packed 128 cuts26138 = true := by
 decide +kernel
def pointBounds26138 : List (Nat × Nat × Nat) := [(3429985280,103468955992045,103469338328462)]
theorem point_links_checked26138 : (cuts26138.take 1).map (fun c => (3429892097-1+2*2^9*c.k,103468605249999+c.lower,103468987586223+c.upper)) = pointBounds26138 := by
 decide +kernel
def cuts26139 : List PrefixCut := [⟨68,258328870,258329010⟩,
⟨128,486208640,486208907⟩]
theorem checked26139 : checkPrefixCuts (2^48) 3430023169 9 Manual.Count131072.C026139.packed 128 cuts26139 = true := by
 decide +kernel
def pointBounds26139 : List (Nat × Nat × Nat) := [(3430092800,103469358668939,103469741005576)]
theorem point_links_checked26139 : (cuts26139.take 1).map (fun c => (3430023169-1+2*2^9*c.k,103469100340069+c.lower,103469482676566+c.upper)) = pointBounds26139 := by
 decide +kernel
def cuts26140 : List PrefixCut := [⟨45,170599450,170599544⟩,
⟨128,487092642,487092919⟩]
theorem checked26140 : checkPrefixCuts (2^48) 3430154241 9 Manual.Count131072.C026140.packed 128 cuts26140 = true := by
 decide +kernel
def pointBounds26140 : List (Nat × Nat × Nat) := [(3430200320,103469757148159,103470139485017)]
theorem point_links_checked26140 : (cuts26140.take 1).map (fun c => (3430154241-1+2*2^9*c.k,103469586548709+c.lower,103469968885473+c.upper)) = pointBounds26140 := by
 decide +kernel
def cuts26141 : List PrefixCut := [⟨22,78609223,78609267⟩,
⟨127,482725228,482725490⟩,
⟨128,486827863,486828127⟩]
theorem checked26141 : checkPrefixCuts (2^48) 3430285313 9 Manual.Count131072.C026141.packed 128 cuts26141 = true := by
 decide +kernel
def pointBounds26141 : List (Nat × Nat × Nat) := [(3430307840,103470152250574,103470534587659),(3430415360,103470556366579,103470938703882)]
theorem point_links_checked26141 : (cuts26141.take 2).map (fun c => (3430285313-1+2*2^9*c.k,103470073641351+c.lower,103470455978392+c.upper)) = pointBounds26141 := by
 decide +kernel
def cuts26142 : List PrefixCut := [⟨104,397703245,397703469⟩,
⟨128,485578633,485578909⟩]
theorem checked26142 : checkPrefixCuts (2^48) 3430416385 9 Manual.Count131072.C026142.packed 128 cuts26142 = true := by
 decide +kernel
def pointBounds26142 : List (Nat × Nat × Nat) := [(3430522880,103470958172459,103471340509988)]
theorem point_links_checked26142 : (cuts26142.take 1).map (fun c => (3430416385-1+2*2^9*c.k,103470560469214+c.lower,103470942806519+c.upper)) = pointBounds26142 := by
 decide +kernel
def cuts26143 : List PrefixCut := [⟨81,308338537,308338708⟩,
⟨128,483755019,483755291⟩]
theorem checked26143 : checkPrefixCuts (2^48) 3430547457 9 Manual.Count131072.C026143.packed 128 cuts26143 = true := by
 decide +kernel
def pointBounds26143 : List (Nat × Nat × Nat) := [(3430630400,103471354386384,103471736724136)]
theorem point_links_checked26143 : (cuts26143.take 1).map (fun c => (3430547457-1+2*2^9*c.k,103471046047847+c.lower,103471428385428+c.upper)) = pointBounds26143 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000191
