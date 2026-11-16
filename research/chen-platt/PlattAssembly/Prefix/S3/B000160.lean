import PlattAssemblyKernel
import PlattCertificates.Count131072.C025120
import PlattCertificates.Count131072.C025121
import PlattCertificates.Count131072.C025122
import PlattCertificates.Count131072.C025123
import PlattCertificates.Count131072.C025124
import PlattCertificates.Count131072.C025125
import PlattCertificates.Count131072.C025126
import PlattCertificates.Count131072.C025127
import PlattCertificates.Count131072.C025128
import PlattCertificates.Count131072.C025129
import PlattCertificates.Count131072.C025130
import PlattCertificates.Count131072.C025131
import PlattCertificates.Count131072.C025132
import PlattCertificates.Count131072.C025133
import PlattCertificates.Count131072.C025134
import PlattCertificates.Count131072.C025135
import PlattCertificates.Count131072.C025136
import PlattCertificates.Count131072.C025137
import PlattCertificates.Count131072.C025138
import PlattCertificates.Count131072.C025139
import PlattCertificates.Count131072.C025140
import PlattCertificates.Count131072.C025141
import PlattCertificates.Count131072.C025142
import PlattCertificates.Count131072.C025143
import PlattCertificates.Count131072.C025144
import PlattCertificates.Count131072.C025145
import PlattCertificates.Count131072.C025146
import PlattCertificates.Count131072.C025147
import PlattCertificates.Count131072.C025148
import PlattCertificates.Count131072.C025149
import PlattCertificates.Count131072.C025150
import PlattCertificates.Count131072.C025151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000160
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25120 : List PrefixCut := [⟨53,210221061,210221177⟩,
⟨128,509408684,509408971⟩]
theorem checked25120 : checkPrefixCuts (2^48) 3296460801 9 Manual.Count131072.C025120.packed 128 cuts25120 = true := by
 decide +kernel
def pointBounds25120 : List (Nat × Nat × Nat) := [(3296515072,102959642150438,102960024201545)]
theorem point_links_checked25120 : (cuts25120.take 1).map (fun c => (3296460801-1+2*2^9*c.k,102959431929377+c.lower,102959813980368+c.upper)) = pointBounds25120 := by
 decide +kernel
def cuts25121 : List PrefixCut := [⟨26,104082198,104082254⟩,
⟨127,510925383,510925670⟩,
⟨128,515792056,515792345⟩]
theorem checked25121 : checkPrefixCuts (2^48) 3296591873 9 Manual.Count131072.C025121.packed 128 cuts25121 = true := by
 decide +kernel
def pointBounds25121 : List (Nat × Nat × Nat) := [(3296618496,102960045420259,102960427471593),(3296721920,102960452263444,102960834315009)]
theorem point_links_checked25121 : (cuts25121.take 2).map (fun c => (3296591873-1+2*2^9*c.k,102959941338061+c.lower,102960323389339+c.upper)) = pointBounds25121 := by
 decide +kernel
def cuts25122 : List PrefixCut := [⟨100,396328815,396329037⟩,
⟨128,509112074,509112363⟩]
theorem checked25122 : checkPrefixCuts (2^48) 3296722945 9 Manual.Count131072.C025122.packed 128 cuts25122 = true := by
 decide +kernel
def pointBounds25122 : List (Nat × Nat × Nat) := [(3296825344,102960853458932,102961235510721)]
theorem point_links_checked25122 : (cuts25122.take 1).map (fun c => (3296722945-1+2*2^9*c.k,102960457130117+c.lower,102960839181684+c.upper)) = pointBounds25122 := by
 decide +kernel
def cuts25123 : List PrefixCut := [⟨73,288570349,288570508⟩,
⟨128,508664895,508665179⟩]
theorem checked25123 : checkPrefixCuts (2^48) 3296854017 9 Manual.Count131072.C025123.packed 128 cuts25123 = true := by
 decide +kernel
def pointBounds25123 : List (Nat × Nat × Nat) := [(3296928768,102961254812540,102961636864555)]
theorem point_links_checked25123 : (cuts25123.take 1).map (fun c => (3296854017-1+2*2^9*c.k,102960966242191+c.lower,102961348294047+c.upper)) = pointBounds25123 := by
 decide +kernel
def cuts25124 : List PrefixCut := [⟨46,181417220,181417322⟩,
⟨128,506851945,506852222⟩]
theorem checked25124 : checkPrefixCuts (2^48) 3296985089 9 Manual.Count131072.C025124.packed 128 cuts25124 = true := by
 decide +kernel
def pointBounds25124 : List (Nat × Nat × Nat) := [(3297032192,102961656324306,102962038376548)]
theorem point_links_checked25124 : (cuts25124.take 1).map (fun c => (3296985089-1+2*2^9*c.k,102961474907086+c.lower,102961856959226+c.upper)) = pointBounds25124 := by
 decide +kernel
def cuts25125 : List PrefixCut := [⟨19,76320579,76320620⟩,
⟨120,480112114,480112378⟩,
⟨128,512295375,512295658⟩]
theorem checked25125 : checkPrefixCuts (2^48) 3297116161 9 Manual.Count131072.C025125.packed 128 cuts25125 = true := by
 decide +kernel
def pointBounds25125 : List (Nat × Nat × Nat) := [(3297135616,102962058079610,102962440132068),(3297239040,102962461871145,102962843923826)]
theorem point_links_checked25125 : (cuts25125.take 2).map (fun c => (3297116161-1+2*2^9*c.k,102961981759031+c.lower,102962363811448+c.upper)) = pointBounds25125 := by
 decide +kernel
def cuts25126 : List PrefixCut := [⟨93,372193123,372193326⟩,
⟨128,515348047,515348331⟩]
theorem checked25126 : checkPrefixCuts (2^48) 3297247233 9 Manual.Count131072.C025126.packed 128 cuts25126 = true := by
 decide +kernel
def pointBounds25126 : List (Nat × Nat × Nat) := [(3297342464,102962866247529,102963248300432)]
theorem point_links_checked25126 : (cuts25126.take 1).map (fun c => (3297247233-1+2*2^9*c.k,102962494054406+c.lower,102962876107106+c.upper)) = pointBounds25126 := by
 decide +kernel
def cuts25127 : List PrefixCut := [⟨66,266501312,266501463⟩,
⟨128,514474091,514474382⟩]
theorem checked25127 : checkPrefixCuts (2^48) 3297378305 9 Manual.Count131072.C025127.packed 128 cuts25127 = true := by
 decide +kernel
def pointBounds25127 : List (Nat × Nat × Nat) := [(3297445888,102963275903765,102963657956900)]
theorem point_links_checked25127 : (cuts25127.take 1).map (fun c => (3297378305-1+2*2^9*c.k,102963009402453+c.lower,102963391455437+c.upper)) = pointBounds25127 := by
 decide +kernel
def cuts25128 : List PrefixCut := [⟨39,151939606,151939690⟩,
⟨128,502844785,502845064⟩]
theorem checked25128 : checkPrefixCuts (2^48) 3297509377 9 Manual.Count131072.C025128.packed 128 cuts25128 = true := by
 decide +kernel
def pointBounds25128 : List (Nat × Nat × Nat) := [(3297549312,102963675816150,102964057869509)]
theorem point_links_checked25128 : (cuts25128.take 1).map (fun c => (3297509377-1+2*2^9*c.k,102963523876544+c.lower,102963905929819+c.upper)) = pointBounds25128 := by
 decide +kernel
def cuts25129 : List PrefixCut := [⟨12,49933432,49933461⟩,
⟨113,459380459,459380713⟩,
⟨128,516055024,516055310⟩]
theorem checked25129 : checkPrefixCuts (2^48) 3297640449 9 Manual.Count131072.C025129.packed 128 cuts25129 = true := by
 decide +kernel
def pointBounds25129 : List (Nat × Nat × Nat) := [(3297652736,102964076654761,102964458708344),(3297756160,102964486101788,102964868155596)]
theorem point_links_checked25129 : (cuts25129.take 2).map (fun c => (3297640449-1+2*2^9*c.k,102964026721329+c.lower,102964408774883+c.upper)) = pointBounds25129 := by
 decide +kernel
def cuts25130 : List PrefixCut := [⟨86,344821760,344821959⟩,
⟨128,513900573,513900865⟩]
theorem checked25130 : checkPrefixCuts (2^48) 3297771521 9 Manual.Count131072.C025130.packed 128 cuts25130 = true := by
 decide +kernel
def pointBounds25130 : List (Nat × Nat × Nat) := [(3297859584,102964887598113,102965269652152)]
theorem point_links_checked25130 : (cuts25130.take 1).map (fun c => (3297771521-1+2*2^9*c.k,102964542776353+c.lower,102964924830193+c.upper)) = pointBounds25130 := by
 decide +kernel
def cuts25131 : List PrefixCut := [⟨59,234965506,234965635⟩,
⟨128,507649761,507650049⟩]
theorem checked25131 : checkPrefixCuts (2^48) 3297902593 9 Manual.Count131072.C025131.packed 128 cuts25131 = true := by
 decide +kernel
def pointBounds25131 : List (Nat × Nat × Nat) := [(3297963008,102965291642432,102965673696693)]
theorem point_links_checked25131 : (cuts25131.take 1).map (fun c => (3297902593-1+2*2^9*c.k,102965056676926+c.lower,102965438731058+c.upper)) = pointBounds25131 := by
 decide +kernel
def cuts25132 : List PrefixCut := [⟨32,129213623,129213701⟩,
⟨128,509592568,509592861⟩]
theorem checked25132 : checkPrefixCuts (2^48) 3298033665 9 Manual.Count131072.C025132.packed 128 cuts25132 = true := by
 decide +kernel
def pointBounds25132 : List (Nat × Nat × Nat) := [(3298066432,102965693540310,102966075594808)]
theorem point_links_checked25132 : (cuts25132.take 1).map (fun c => (3298033665-1+2*2^9*c.k,102965564326687+c.lower,102965946381107+c.upper)) = pointBounds25132 := by
 decide +kernel
def cuts25133 : List PrefixCut := [⟨5,20738304,20738317⟩,
⟨106,422013605,422013845⟩,
⟨128,507950770,507951061⟩]
theorem checked25133 : checkPrefixCuts (2^48) 3298164737 9 Manual.Count131072.C025133.packed 128 cuts25133 = true := by
 decide +kernel
def pointBounds25133 : List (Nat × Nat × Nat) := [(3298169856,102966094657559,102966476712285),(3298273280,102966495932860,102966877987813)]
theorem point_links_checked25133 : (cuts25133.take 2).map (fun c => (3298164737-1+2*2^9*c.k,102966073919255+c.lower,102966455973968+c.upper)) = pointBounds25133 := by
 decide +kernel
def cuts25134 : List PrefixCut := [⟨79,314386857,314387035⟩,
⟨128,520475118,520475413⟩]
theorem checked25134 : checkPrefixCuts (2^48) 3298295809 9 Manual.Count131072.C025134.packed 128 cuts25134 = true := by
 decide +kernel
def pointBounds25134 : List (Nat × Nat × Nat) := [(3298376704,102966896256882,102967278312064)]
theorem point_links_checked25134 : (cuts25134.take 1).map (fun c => (3298295809-1+2*2^9*c.k,102966581870025+c.lower,102966963925029+c.upper)) = pointBounds25134 := by
 decide +kernel
def cuts25135 : List PrefixCut := [⟨52,203695626,203695744⟩,
⟨128,508678348,508678640⟩]
theorem checked25135 : checkPrefixCuts (2^48) 3298426881 9 Manual.Count131072.C025135.packed 128 cuts25135 = true := by
 decide +kernel
def pointBounds25135 : List (Nat × Nat × Nat) := [(3298480128,102967306040769,102967688096186)]
theorem point_links_checked25135 : (cuts25135.take 1).map (fun c => (3298426881-1+2*2^9*c.k,102967102345143+c.lower,102967484400442+c.upper)) = pointBounds25135 := by
 decide +kernel
def cuts25136 : List PrefixCut := [⟨25,100009555,100009610⟩,
⟨126,496968044,496968315⟩,
⟨128,504733015,504733291⟩]
theorem checked25136 : checkPrefixCuts (2^48) 3298557953 9 Manual.Count131072.C025136.packed 128 cuts25136 = true := by
 decide +kernel
def pointBounds25136 : List (Nat × Nat × Nat) := [(3298583552,102967711033046,102968093088692),(3298686976,102968107991535,102968490047397)]
theorem point_links_checked25136 : (cuts25136.take 2).map (fun c => (3298557953-1+2*2^9*c.k,102967611023491+c.lower,102967993079082+c.upper)) = pointBounds25136 := by
 decide +kernel
def cuts25137 : List PrefixCut := [⟨99,390460990,390461204⟩,
⟨128,501982488,501982766⟩]
theorem checked25137 : checkPrefixCuts (2^48) 3298689025 9 Manual.Count131072.C025137.packed 128 cuts25137 = true := by
 decide +kernel
def pointBounds25137 : List (Nat × Nat × Nat) := [(3298790400,102968506217496,102968888273577)]
theorem point_links_checked25137 : (cuts25137.take 1).map (fun c => (3298689025-1+2*2^9*c.k,102968115756506+c.lower,102968497812373+c.upper)) = pointBounds25137 := by
 decide +kernel
def cuts25138 : List PrefixCut := [⟨72,292067388,292067549⟩,
⟨128,515870343,515870626⟩]
theorem checked25138 : checkPrefixCuts (2^48) 3298820097 9 Manual.Count131072.C025138.packed 128 cuts25138 = true := by
 decide +kernel
def pointBounds25138 : List (Nat × Nat × Nat) := [(3298893824,102968909806382,102969291862688)]
theorem point_links_checked25138 : (cuts25138.take 1).map (fun c => (3298820097-1+2*2^9*c.k,102968617738994+c.lower,102968999795139+c.upper)) = pointBounds25138 := by
 decide +kernel
def cuts25139 : List PrefixCut := [⟨45,177213680,177213780⟩,
⟨128,506293887,506294179⟩]
theorem checked25139 : checkPrefixCuts (2^48) 3298951169 9 Manual.Count131072.C025139.packed 128 cuts25139 = true := by
 decide +kernel
def pointBounds25139 : List (Nat × Nat × Nat) := [(3298997248,102969310823017,102969692879545)]
theorem point_links_checked25139 : (cuts25139.take 1).map (fun c => (3298951169-1+2*2^9*c.k,102969133609337+c.lower,102969515665765+c.upper)) = pointBounds25139 := by
 decide +kernel
def cuts25140 : List PrefixCut := [⟨18,70644058,70644095⟩,
⟨119,470014551,470014813⟩,
⟨128,505164694,505164975⟩]
theorem checked25140 : checkPrefixCuts (2^48) 3299082241 9 Manual.Count131072.C025140.packed 128 cuts25140 = true := by
 decide +kernel
def pointBounds25140 : List (Nat × Nat × Nat) := [(3299100672,102969710547282,102970092604039),(3299204096,102970109917775,102970491974757)]
theorem point_links_checked25140 : (cuts25140.take 2).map (fun c => (3299082241-1+2*2^9*c.k,102969639903224+c.lower,102970021959944+c.upper)) = pointBounds25140 := by
 decide +kernel
def cuts25141 : List PrefixCut := [⟨92,361392423,361392633⟩,
⟨128,505400515,505400806⟩]
theorem checked25141 : checkPrefixCuts (2^48) 3299213313 9 Manual.Count131072.C025141.packed 128 cuts25141 = true := by
 decide +kernel
def pointBounds25141 : List (Nat × Nat × Nat) := [(3299307520,102970506460341,102970888517552)]
theorem point_links_checked25141 : (cuts25141.take 1).map (fun c => (3299213313-1+2*2^9*c.k,102970145067918+c.lower,102970527124919+c.upper)) = pointBounds25141 := by
 decide +kernel
def cuts25142 : List PrefixCut := [⟨65,261479773,261479924⟩,
⟨128,508963541,508963832⟩]
theorem checked25142 : checkPrefixCuts (2^48) 3299344385 9 Manual.Count131072.C025142.packed 128 cuts25142 = true := by
 decide +kernel
def pointBounds25142 : List (Nat × Nat × Nat) := [(3299410944,102970911948206,102971294005649)]
theorem point_links_checked25142 : (cuts25142.take 1).map (fun c => (3299344385-1+2*2^9*c.k,102970650468433+c.lower,102971032525725+c.upper)) = pointBounds25142 := by
 decide +kernel
def cuts25143 : List PrefixCut := [⟨38,148436758,148436843⟩,
⟨128,503739469,503739757⟩]
theorem checked25143 : checkPrefixCuts (2^48) 3299475457 9 Manual.Count131072.C025143.packed 128 cuts25143 = true := by
 decide +kernel
def pointBounds25143 : List (Nat × Nat × Nat) := [(3299514368,102971307868732,102971689926400)]
theorem point_links_checked25143 : (cuts25143.take 1).map (fun c => (3299475457-1+2*2^9*c.k,102971159431974+c.lower,102971541489557+c.upper)) = pointBounds25143 := by
 decide +kernel
def cuts25144 : List PrefixCut := [⟨11,42482114,42482137⟩,
⟨112,449638004,449638253⟩,
⟨128,513273606,513273892⟩]
theorem checked25144 : checkPrefixCuts (2^48) 3299606529 9 Manual.Count131072.C025144.packed 128 cuts25144 = true := by
 decide +kernel
def pointBounds25144 : List (Nat × Nat × Nat) := [(3299617792,102971705653557,102972087711451),(3299721216,102972112809447,102972494867567)]
theorem point_links_checked25144 : (cuts25144.take 2).map (fun c => (3299606529-1+2*2^9*c.k,102971663171443+c.lower,102972045229314+c.upper)) = pointBounds25144 := by
 decide +kernel
def cuts25145 : List PrefixCut := [⟨85,333612487,333612672⟩,
⟨128,506684950,506685228⟩]
theorem checked25145 : checkPrefixCuts (2^48) 3299737601 9 Manual.Count131072.C025145.packed 128 cuts25145 = true := by
 decide +kernel
def pointBounds25145 : List (Nat × Nat × Nat) := [(3299824640,102972510057536,102972892115878)]
theorem point_links_checked25145 : (cuts25145.take 1).map (fun c => (3299737601-1+2*2^9*c.k,102972176445049+c.lower,102972558503206+c.upper)) = pointBounds25145 := by
 decide +kernel
def cuts25146 : List PrefixCut := [⟨58,235337350,235337479⟩,
⟨128,511782852,511783142⟩]
theorem checked25146 : checkPrefixCuts (2^48) 3299868673 9 Manual.Count131072.C025146.packed 128 cuts25146 = true := by
 decide +kernel
def pointBounds25146 : List (Nat × Nat × Nat) := [(3299928064,102972918467349,102973300525913)]
theorem point_links_checked25146 : (cuts25146.take 1).map (fun c => (3299868673-1+2*2^9*c.k,102972683129999+c.lower,102973065188434+c.upper)) = pointBounds25146 := by
 decide +kernel
def cuts25147 : List PrefixCut := [⟨31,125127796,125127869⟩,
⟨128,513041827,513042120⟩]
theorem checked25147 : checkPrefixCuts (2^48) 3299999745 9 Manual.Count131072.C025147.packed 128 cuts25147 = true := by
 decide +kernel
def pointBounds25147 : List (Nat × Nat × Nat) := [(3300031488,102973320040647,102973702099445)]
theorem point_links_checked25147 : (cuts25147.take 1).map (fun c => (3299999745-1+2*2^9*c.k,102973194912851+c.lower,102973576971576+c.upper)) = pointBounds25147 := by
 decide +kernel
def cuts25148 : List PrefixCut := [⟨4,16120185,16120194⟩,
⟨105,415962469,415962711⟩,
⟨128,503724806,503725100⟩]
theorem checked25148 : checkPrefixCuts (2^48) 3300130817 9 Manual.Count131072.C025148.packed 128 cuts25148 = true := by
 decide +kernel
def pointBounds25148 : List (Nat × Nat × Nat) := [(3300134912,102973724074863,102974106133890),(3300238336,102974123917147,102974505976407)]
theorem point_links_checked25148 : (cuts25148.take 2).map (fun c => (3300130817-1+2*2^9*c.k,102973707954678+c.lower,102974090013696+c.upper)) = pointBounds25148 := by
 decide +kernel
def cuts25149 : List PrefixCut := [⟨78,318549251,318549431⟩,
⟨128,518118323,518118613⟩]
theorem checked25149 : checkPrefixCuts (2^48) 3300261889 9 Manual.Count131072.C025149.packed 128 cuts25149 = true := by
 decide +kernel
def pointBounds25149 : List (Nat × Nat × Nat) := [(3300341760,102974530228735,102974912288227)]
theorem point_links_checked25149 : (cuts25149.take 1).map (fun c => (3300261889-1+2*2^9*c.k,102974211679484+c.lower,102974593738796+c.upper)) = pointBounds25149 := by
 decide +kernel
def cuts25150 : List PrefixCut := [⟨51,199224801,199224916⟩,
⟨128,508119435,508119723⟩]
theorem checked25150 : checkPrefixCuts (2^48) 3300392961 9 Manual.Count131072.C025150.packed 128 cuts25150 = true := by
 decide +kernel
def pointBounds25150 : List (Nat × Nat × Nat) := [(3300445184,102974929022608,102975311082325)]
theorem point_links_checked25150 : (cuts25150.take 1).map (fun c => (3300392961-1+2*2^9*c.k,102974729797807+c.lower,102975111857409+c.upper)) = pointBounds25150 := by
 decide +kernel
def cuts25151 : List PrefixCut := [⟨24,95003669,95003719⟩,
⟨125,493516724,493517004⟩,
⟨128,504602933,504603219⟩]
theorem checked25151 : checkPrefixCuts (2^48) 3300524033 9 Manual.Count131072.C025151.packed 128 cuts25151 = true := by
 decide +kernel
def pointBounds25151 : List (Nat × Nat × Nat) := [(3300548608,102975332920911,102975714980851),(3300652032,102975731433966,102976113494136)]
theorem point_links_checked25151 : (cuts25151.take 2).map (fun c => (3300524033-1+2*2^9*c.k,102975237917242+c.lower,102975619977132+c.upper)) = pointBounds25151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000160
