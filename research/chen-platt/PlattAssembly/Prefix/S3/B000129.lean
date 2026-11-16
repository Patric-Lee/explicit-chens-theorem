import PlattAssemblyKernel
import PlattCertificates.Count131072.C024128
import PlattCertificates.Count131072.C024129
import PlattCertificates.Count131072.C024130
import PlattCertificates.Count131072.C024131
import PlattCertificates.Count131072.C024132
import PlattCertificates.Count131072.C024133
import PlattCertificates.Count131072.C024134
import PlattCertificates.Count131072.C024135
import PlattCertificates.Count131072.C024136
import PlattCertificates.Count131072.C024137
import PlattCertificates.Count131072.C024138
import PlattCertificates.Count131072.C024139
import PlattCertificates.Count131072.C024140
import PlattCertificates.Count131072.C024141
import PlattCertificates.Count131072.C024142
import PlattCertificates.Count131072.C024143
import PlattCertificates.Count131072.C024144
import PlattCertificates.Count131072.C024145
import PlattCertificates.Count131072.C024146
import PlattCertificates.Count131072.C024147
import PlattCertificates.Count131072.C024148
import PlattCertificates.Count131072.C024149
import PlattCertificates.Count131072.C024150
import PlattCertificates.Count131072.C024151
import PlattCertificates.Count131072.C024152
import PlattCertificates.Count131072.C024153
import PlattCertificates.Count131072.C024154
import PlattCertificates.Count131072.C024155
import PlattCertificates.Count131072.C024156
import PlattCertificates.Count131072.C024157
import PlattCertificates.Count131072.C024158
import PlattCertificates.Count131072.C024159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000129
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24128 : List PrefixCut := [⟨79,328811887,328812074⟩,
⟨128,531926169,531926469⟩]
theorem checked24128 : checkPrefixCuts (2^48) 3166437377 9 Manual.Count131072.C024128.packed 128 cuts24128 = true := by
 decide +kernel
def pointBounds24128 : List (Nat × Nat × Nat) := [(3166518272,102442531414396,102442913174411)]
theorem point_links_checked24128 : (cuts24128.take 1).map (fun c => (3166437377-1+2*2^9*c.k,102442202602509+c.lower,102442584362337+c.upper)) = pointBounds24128 := by
 decide +kernel
def cuts24129 : List PrefixCut := [⟨48,197511072,197511186⟩,
⟨128,531726293,531726599⟩]
theorem checked24129 : checkPrefixCuts (2^48) 3166568449 9 Manual.Count131072.C024129.packed 128 cuts24129 = true := by
 decide +kernel
def pointBounds24129 : List (Nat × Nat × Nat) := [(3166617600,102442932039750,102443313799992)]
theorem point_links_checked24129 : (cuts24129.take 1).map (fun c => (3166568449-1+2*2^9*c.k,102442734528678+c.lower,102443116288806+c.upper)) = pointBounds24129 := by
 decide +kernel
def cuts24130 : List PrefixCut := [⟨17,69419691,69419729⟩,
⟨114,469308834,469309106⟩,
⟨128,525660281,525660584⟩]
theorem checked24130 : checkPrefixCuts (2^48) 3166699521 9 Manual.Count131072.C024130.packed 128 cuts24130 = true := by
 decide +kernel
def pointBounds24130 : List (Nat × Nat × Nat) := [(3166716928,102443335674662,102443717435134),(3166816256,102443735563805,102444117324511)]
theorem point_links_checked24130 : (cuts24130.take 2).map (fun c => (3166699521-1+2*2^9*c.k,102443266254971+c.lower,102443648015405+c.upper)) = pointBounds24130 := by
 decide +kernel
def cuts24131 : List PrefixCut := [⟨83,345302767,345302959⟩,
⟨128,529104906,529105203⟩]
theorem checked24131 : checkPrefixCuts (2^48) 3166830593 9 Manual.Count131072.C024131.packed 128 cuts24131 = true := by
 decide +kernel
def pointBounds24131 : List (Nat × Nat × Nat) := [(3166915584,102444137218019,102444518978948)]
theorem point_links_checked24131 : (cuts24131.take 1).map (fun c => (3166830593-1+2*2^9*c.k,102443791915252+c.lower,102444173675989+c.upper)) = pointBounds24131 := by
 decide +kernel
def cuts24132 : List PrefixCut := [⟨52,214462094,214462217⟩,
⟨128,532015888,532016189⟩]
theorem checked24132 : checkPrefixCuts (2^48) 3166961665 9 Manual.Count131072.C024132.packed 128 cuts24132 = true := by
 decide +kernel
def pointBounds24132 : List (Nat × Nat × Nat) := [(3167014912,102444535482252,102444917243409)]
theorem point_links_checked24132 : (cuts24132.take 1).map (fun c => (3166961665-1+2*2^9*c.k,102444321020158+c.lower,102444702781192+c.upper)) = pointBounds24132 := by
 decide +kernel
def cuts24133 : List PrefixCut := [⟨21,85675064,85675109⟩,
⟨118,488535722,488535994⟩,
⟨128,531105086,531105379⟩]
theorem checked24133 : checkPrefixCuts (2^48) 3167092737 9 Manual.Count131072.C024133.packed 128 cuts24133 = true := by
 decide +kernel
def pointBounds24133 : List (Nat × Nat × Nat) := [(3167114240,102444938711110,102445320472490),(3167213568,102445341571768,102445723333375)]
theorem point_links_checked24133 : (cuts24133.take 2).map (fun c => (3167092737-1+2*2^9*c.k,102444853036046+c.lower,102445234797381+c.upper)) = pointBounds24133 := by
 decide +kernel
def cuts24134 : List PrefixCut := [⟨87,364544397,364544603⟩,
⟨128,538992447,538992759⟩]
theorem checked24134 : checkPrefixCuts (2^48) 3167223809 9 Manual.Count131072.C024134.packed 128 cuts24134 = true := by
 decide +kernel
def pointBounds24134 : List (Nat × Nat × Nat) := [(3167312896,102445748685529,102446130447363)]
theorem point_links_checked24134 : (cuts24134.take 1).map (fun c => (3167223809-1+2*2^9*c.k,102445384141132+c.lower,102445765902760+c.upper)) = pointBounds24134 := by
 decide +kernel
def cuts24135 : List PrefixCut := [⟨56,234608049,234608181⟩,
⟨128,527328907,527329202⟩]
theorem checked24135 : checkPrefixCuts (2^48) 3167354881 9 Manual.Count131072.C024135.packed 128 cuts24135 = true := by
 decide +kernel
def pointBounds24135 : List (Nat × Nat × Nat) := [(3167412224,102446157741628,102446539503700)]
theorem point_links_checked24135 : (cuts24135.take 1).map (fun c => (3167354881-1+2*2^9*c.k,102445923133579+c.lower,102446304895519+c.upper)) = pointBounds24135 := by
 decide +kernel
def cuts24136 : List PrefixCut := [⟨25,101570936,101570997⟩,
⟨122,511756648,511756945⟩,
⟨128,537259534,537259845⟩]
theorem checked24136 : checkPrefixCuts (2^48) 3167485953 9 Manual.Count131072.C024136.packed 128 cuts24136 = true := by
 decide +kernel
def pointBounds24136 : List (Nat × Nat × Nat) := [(3167511552,102446552033422,102446933795718),(3167610880,102446962219134,102447343981666)]
theorem point_links_checked24136 : (cuts24136.take 2).map (fun c => (3167485953-1+2*2^9*c.k,102446450462486+c.lower,102446832224721+c.upper)) = pointBounds24136 := by
 decide +kernel
def cuts24137 : List PrefixCut := [⟨91,382181868,382182087⟩,
⟨128,528795929,528796229⟩]
theorem checked24137 : checkPrefixCuts (2^48) 3167617025 9 Manual.Count131072.C024137.packed 128 cuts24137 = true := by
 decide +kernel
def pointBounds24137 : List (Nat × Nat × Nat) := [(3167710208,102447369903888,102447751666653)]
theorem point_links_checked24137 : (cuts24137.take 1).map (fun c => (3167617025-1+2*2^9*c.k,102446987722020+c.lower,102447369484566+c.upper)) = pointBounds24137 := by
 decide +kernel
def cuts24138 : List PrefixCut := [⟨60,250217395,250217534⟩,
⟨128,535615703,535616004⟩]
theorem checked24138 : checkPrefixCuts (2^48) 3167748097 9 Manual.Count131072.C024138.packed 128 cuts24138 = true := by
 decide +kernel
def pointBounds24138 : List (Nat × Nat × Nat) := [(3167809536,102447766735344,102448148498329)]
theorem point_links_checked24138 : (cuts24138.take 1).map (fun c => (3167748097-1+2*2^9*c.k,102447516517949+c.lower,102447898280795+c.upper)) = pointBounds24138 := by
 decide +kernel
def cuts24139 : List PrefixCut := [⟨29,120394960,120395025⟩,
⟨126,518445500,518445796⟩,
⟨128,527330414,527330715⟩]
theorem checked24139 : checkPrefixCuts (2^48) 3167879169 9 Manual.Count131072.C024139.packed 128 cuts24139 = true := by
 decide +kernel
def pointBounds24139 : List (Nat × Nat × Nat) := [(3167908864,102448172528612,102448554291824),(3168008192,102448570579152,102448952342595)]
theorem point_links_checked24139 : (cuts24139.take 2).map (fun c => (3167879169-1+2*2^9*c.k,102448052133652+c.lower,102448433896799+c.upper)) = pointBounds24139 := by
 decide +kernel
def cuts24140 : List PrefixCut := [⟨95,394039785,394040004⟩,
⟨128,532461709,532462004⟩]
theorem checked24140 : checkPrefixCuts (2^48) 3168010241 9 Manual.Count131072.C024140.packed 128 cuts24140 = true := by
 decide +kernel
def pointBounds24140 : List (Nat × Nat × Nat) := [(3168107520,102448973503851,102449355267518)]
theorem point_links_checked24140 : (cuts24140.take 1).map (fun c => (3168010241-1+2*2^9*c.k,102448579464066+c.lower,102448961227514+c.upper)) = pointBounds24140 := by
 decide +kernel
def cuts24141 : List PrefixCut := [⟨64,267066598,267066748⟩,
⟨128,530218618,530218920⟩]
theorem checked24141 : checkPrefixCuts (2^48) 3168141313 9 Manual.Count131072.C024141.packed 128 cuts24141 = true := by
 decide +kernel
def pointBounds24141 : List (Nat × Nat × Nat) := [(3168206848,102449378992373,102449760756266)]
theorem point_links_checked24141 : (cuts24141.take 1).map (fun c => (3168141313-1+2*2^9*c.k,102449111925775+c.lower,102449493689518+c.upper)) = pointBounds24141 := by
 decide +kernel
def cuts24142 : List PrefixCut := [⟨33,135038738,135038814⟩,
⟨128,527176112,527176411⟩]
theorem checked24142 : checkPrefixCuts (2^48) 3168272385 9 Manual.Count131072.C024142.packed 128 cuts24142 = true := by
 decide +kernel
def pointBounds24142 : List (Nat × Nat × Nat) := [(3168306176,102449777183131,102450158947252)]
theorem point_links_checked24142 : (cuts24142.take 1).map (fun c => (3168272385-1+2*2^9*c.k,102449642144393+c.lower,102450023908438+c.upper)) = pointBounds24142 := by
 decide +kernel
def cuts24143 : List PrefixCut := [⟨2,8439616,8439620⟩,
⟨99,412912887,412913121⟩,
⟨128,535593786,535594086⟩]
theorem checked24143 : checkPrefixCuts (2^48) 3168403457 9 Manual.Count131072.C024143.packed 128 cuts24143 = true := by
 decide +kernel
def pointBounds24143 : List (Nat × Nat × Nat) := [(3168405504,102450177760121,102450559524469),(3168504832,102450582233392,102450963997970)]
theorem point_links_checked24143 : (cuts24143.take 2).map (fun c => (3168403457-1+2*2^9*c.k,102450169320505+c.lower,102450551084849+c.upper)) = pointBounds24143 := by
 decide +kernel
def cuts24144 : List PrefixCut := [⟨68,287376162,287376324⟩,
⟨128,539569026,539569329⟩]
theorem checked24144 : checkPrefixCuts (2^48) 3168534529 9 Manual.Count131072.C024144.packed 128 cuts24144 = true := by
 decide +kernel
def pointBounds24144 : List (Nat × Nat × Nat) := [(3168604160,102450992290453,102451374055259)]
theorem point_links_checked24144 : (cuts24144.take 1).map (fun c => (3168534529-1+2*2^9*c.k,102450704914291+c.lower,102451086678935+c.upper)) = pointBounds24144 := by
 decide +kernel
def cuts24145 : List PrefixCut := [⟨37,154031580,154031670⟩,
⟨128,531552108,531552412⟩]
theorem checked24145 : checkPrefixCuts (2^48) 3168665601 9 Manual.Count131072.C024145.packed 128 cuts24145 = true := by
 decide +kernel
def pointBounds24145 : List (Nat × Nat × Nat) := [(3168703488,102451398514897,102451780279934)]
theorem point_links_checked24145 : (cuts24145.take 1).map (fun c => (3168665601-1+2*2^9*c.k,102451244483317+c.lower,102451626248264+c.upper)) = pointBounds24145 := by
 decide +kernel
def cuts24146 : List PrefixCut := [⟨6,23450321,23450336⟩,
⟨103,424142202,424142450⟩,
⟨128,526644808,526645112⟩]
theorem checked24146 : checkPrefixCuts (2^48) 3168796673 9 Manual.Count131072.C024146.packed 128 cuts24146 = true := by
 decide +kernel
def pointBounds24146 : List (Nat × Nat × Nat) := [(3168802816,102451799485746,102452181251012),(3168902144,102452200177627,102452581943126)]
theorem point_links_checked24146 : (cuts24146.take 2).map (fun c => (3168796673-1+2*2^9*c.k,102451776035425+c.lower,102452157800676+c.upper)) = pointBounds24146 := by
 decide +kernel
def cuts24147 : List PrefixCut := [⟨72,301374241,301374405⟩,
⟨128,531597021,531597315⟩]
theorem checked24147 : checkPrefixCuts (2^48) 3168927745 9 Manual.Count131072.C024147.packed 128 cuts24147 = true := by
 decide +kernel
def pointBounds24147 : List (Nat × Nat × Nat) := [(3169001472,102452604054474,102452985820193)]
theorem point_links_checked24147 : (cuts24147.take 1).map (fun c => (3168927745-1+2*2^9*c.k,102452302680233+c.lower,102452684445788+c.upper)) = pointBounds24147 := by
 decide +kernel
def cuts24148 : List PrefixCut := [⟨41,167868130,167868225⟩,
⟨128,535038826,535039124⟩]
theorem checked24148 : checkPrefixCuts (2^48) 3169058817 9 Manual.Count131072.C024148.packed 128 cuts24148 = true := by
 decide +kernel
def pointBounds24148 : List (Nat × Nat × Nat) := [(3169100800,102453002145384,102453383911328)]
theorem point_links_checked24148 : (cuts24148.take 1).map (fun c => (3169058817-1+2*2^9*c.k,102452834277254+c.lower,102453216043103+c.upper)) = pointBounds24148 := by
 decide +kernel
def cuts24149 : List PrefixCut := [⟨10,40944127,40944150⟩,
⟨107,440164666,440164911⟩,
⟨128,525868895,525869188⟩]
theorem checked24149 : checkPrefixCuts (2^48) 3169189889 9 Manual.Count131072.C024149.packed 128 cuts24149 = true := by
 decide +kernel
def pointBounds24149 : List (Nat × Nat × Nat) := [(3169200128,102453410260207,102453792026377),(3169299456,102453809480746,102454191247138)]
theorem point_links_checked24149 : (cuts24149.take 2).map (fun c => (3169189889-1+2*2^9*c.k,102453369316080+c.lower,102453751082227+c.upper)) = pointBounds24149 := by
 decide +kernel
def cuts24150 : List PrefixCut := [⟨76,323273052,323273232⟩,
⟨128,539612810,539613116⟩]
theorem checked24150 : checkPrefixCuts (2^48) 3169320961 9 Manual.Count131072.C024150.packed 128 cuts24150 = true := by
 decide +kernel
def pointBounds24150 : List (Nat × Nat × Nat) := [(3169398784,102454218458027,102454600224647)]
theorem point_links_checked24150 : (cuts24150.take 1).map (fun c => (3169320961-1+2*2^9*c.k,102453895184975+c.lower,102454276951415+c.upper)) = pointBounds24150 := by
 decide +kernel
def cuts24151 : List PrefixCut := [⟨45,187029759,187029857⟩,
⟨128,533906790,533907088⟩]
theorem checked24151 : checkPrefixCuts (2^48) 3169452033 9 Manual.Count131072.C024151.packed 128 cuts24151 = true := by
 decide +kernel
def pointBounds24151 : List (Nat × Nat × Nat) := [(3169498112,102454621827544,102455003594388)]
theorem point_links_checked24151 : (cuts24151.take 1).map (fun c => (3169452033-1+2*2^9*c.k,102454434797785+c.lower,102454816564531+c.upper)) = pointBounds24151 := by
 decide +kernel
def cuts24152 : List PrefixCut := [⟨14,58966405,58966439⟩,
⟨111,462044245,462044502⟩,
⟨128,530599077,530599374⟩]
theorem checked24152 : checkPrefixCuts (2^48) 3169583105 9 Manual.Count131072.C024152.packed 128 cuts24152 = true := by
 decide +kernel
def pointBounds24152 : List (Nat × Nat × Nat) := [(3169597440,102455027670980,102455409438058),(3169696768,102455430748820,102455812516121)]
theorem point_links_checked24152 : (cuts24152.take 2).map (fun c => (3169583105-1+2*2^9*c.k,102454968704575+c.lower,102455350471619+c.upper)) = pointBounds24152 := by
 decide +kernel
def cuts24153 : List PrefixCut := [⟨80,340726378,340726563⟩,
⟨128,537059557,537059851⟩]
theorem checked24153 : checkPrefixCuts (2^48) 3169714177 9 Manual.Count131072.C024153.packed 128 cuts24153 = true := by
 decide +kernel
def pointBounds24153 : List (Nat × Nat × Nat) := [(3169796096,102455840030030,102456221797556)]
theorem point_links_checked24153 : (cuts24153.take 1).map (fun c => (3169714177-1+2*2^9*c.k,102455499303652+c.lower,102455881070993+c.upper)) = pointBounds24153 := by
 decide +kernel
def cuts24154 : List PrefixCut := [⟨49,202190706,202190823⟩,
⟨128,529311995,529312293⟩]
theorem checked24154 : checkPrefixCuts (2^48) 3169845249 9 Manual.Count131072.C024154.packed 128 cuts24154 = true := by
 decide +kernel
def pointBounds24154 : List (Nat × Nat × Nat) := [(3169895424,102456238553915,102456620321667)]
theorem point_links_checked24154 : (cuts24154.take 1).map (fun c => (3169845249-1+2*2^9*c.k,102456036363209+c.lower,102456418130844+c.upper)) = pointBounds24154 := by
 decide +kernel
def cuts24155 : List PrefixCut := [⟨18,75297099,75297142⟩,
⟨115,477525278,477525548⟩,
⟨128,528313453,528313755⟩]
theorem checked24155 : checkPrefixCuts (2^48) 3169976321 9 Manual.Count131072.C024155.packed 128 cuts24155 = true := by
 decide +kernel
def pointBounds24155 : List (Nat × Nat × Nat) := [(3169994752,102456640972303,102457022740279),(3170094080,102457043200482,102457424968685)]
theorem point_links_checked24155 : (cuts24155.take 2).map (fun c => (3169976321-1+2*2^9*c.k,102456565675204+c.lower,102456947443137+c.upper)) = pointBounds24155 := by
 decide +kernel
def cuts24156 : List PrefixCut := [⟨84,350184295,350184496⟩,
⟨128,530156152,530156450⟩]
theorem checked24156 : checkPrefixCuts (2^48) 3170107393 9 Manual.Count131072.C024156.packed 128 cuts24156 = true := by
 decide +kernel
def pointBounds24156 : List (Nat × Nat × Nat) := [(3170193408,102457444172952,102457825941388)]
theorem point_links_checked24156 : (cuts24156.take 1).map (fun c => (3170107393-1+2*2^9*c.k,102457093988657+c.lower,102457475756892+c.upper)) = pointBounds24156 := by
 decide +kernel
def cuts24157 : List PrefixCut := [⟨53,219745114,219745237⟩,
⟨128,531909887,531910186⟩]
theorem checked24157 : checkPrefixCuts (2^48) 3170238465 9 Manual.Count131072.C024157.packed 128 cuts24157 = true := by
 decide +kernel
def pointBounds24157 : List (Nat × Nat × Nat) := [(3170292736,102457843889923,102458225658579)]
theorem point_links_checked24157 : (cuts24157.take 1).map (fun c => (3170238465-1+2*2^9*c.k,102457624144809+c.lower,102458005913342+c.upper)) = pointBounds24157 := by
 decide +kernel
def cuts24158 : List PrefixCut := [⟨22,87983638,87983689⟩,
⟨119,492647270,492647548⟩,
⟨128,528425387,528425686⟩]
theorem checked24158 : checkPrefixCuts (2^48) 3170369537 9 Manual.Count131072.C024158.packed 128 cuts24158 = true := by
 decide +kernel
def pointBounds24158 : List (Nat × Nat × Nat) := [(3170392064,102458244038334,102458625807217),(3170491392,102458648701966,102459030471076)]
theorem point_links_checked24158 : (cuts24158.take 2).map (fun c => (3170369537-1+2*2^9*c.k,102458156054696+c.lower,102458537823528+c.upper)) = pointBounds24158 := by
 decide +kernel
def cuts24159 : List PrefixCut := [⟨88,368340237,368340442⟩,
⟨128,537192625,537192923⟩]
theorem checked24159 : checkPrefixCuts (2^48) 3170500609 9 Manual.Count131072.C024159.packed 128 cuts24159 = true := by
 decide +kernel
def pointBounds24159 : List (Nat × Nat × Nat) := [(3170590720,102459052820320,102459434589656)]
theorem point_links_checked24159 : (cuts24159.take 1).map (fun c => (3170500609-1+2*2^9*c.k,102458684480083+c.lower,102459066249214+c.upper)) = pointBounds24159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000129
