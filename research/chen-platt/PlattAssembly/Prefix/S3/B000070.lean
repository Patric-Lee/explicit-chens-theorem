import PlattAssemblyKernel
import PlattCertificates.Count131072.C022240
import PlattCertificates.Count131072.C022241
import PlattCertificates.Count131072.C022242
import PlattCertificates.Count131072.C022243
import PlattCertificates.Count131072.C022244
import PlattCertificates.Count131072.C022245
import PlattCertificates.Count131072.C022246
import PlattCertificates.Count131072.C022247
import PlattCertificates.Count131072.C022248
import PlattCertificates.Count131072.C022249
import PlattCertificates.Count131072.C022250
import PlattCertificates.Count131072.C022251
import PlattCertificates.Count131072.C022252
import PlattCertificates.Count131072.C022253
import PlattCertificates.Count131072.C022254
import PlattCertificates.Count131072.C022255
import PlattCertificates.Count131072.C022256
import PlattCertificates.Count131072.C022257
import PlattCertificates.Count131072.C022258
import PlattCertificates.Count131072.C022259
import PlattCertificates.Count131072.C022260
import PlattCertificates.Count131072.C022261
import PlattCertificates.Count131072.C022262
import PlattCertificates.Count131072.C022263
import PlattCertificates.Count131072.C022264
import PlattCertificates.Count131072.C022265
import PlattCertificates.Count131072.C022266
import PlattCertificates.Count131072.C022267
import PlattCertificates.Count131072.C022268
import PlattCertificates.Count131072.C022269
import PlattCertificates.Count131072.C022270
import PlattCertificates.Count131072.C022271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22240 : List PrefixCut := [⟨58,261803142,261803294⟩,
⟨128,576056351,576056680⟩]
theorem checked22240 : checkPrefixCuts (2^48) 2918973441 9 Manual.Count131072.C022240.packed 128 cuts22240 = true := by
 decide +kernel
def pointBounds22240 : List (Nat × Nat × Nat) := [(2919032832,101393491629157,101393872793640)]
theorem point_links_checked22240 : (cuts22240.take 1).map (fun c => (2918973441-1+2*2^9*c.k,101393229826015+c.lower,101393610990346+c.upper)) = pointBounds22240 := by
 decide +kernel
def cuts22241 : List PrefixCut := [⟨20,90928527,90928582⟩,
⟨110,499279423,499279714⟩,
⟨128,580948062,580948401⟩]
theorem checked22241 : checkPrefixCuts (2^48) 2919104513 9 Manual.Count131072.C022241.packed 128 cuts22241 = true := by
 decide +kernel
def pointBounds22241 : List (Nat × Nat × Nat) := [(2919124992,101393896810893,101394277975608),(2919217152,101394305161789,101394686326740)]
theorem point_links_checked22241 : (cuts22241.take 2).map (fun c => (2919104513-1+2*2^9*c.k,101393805882366+c.lower,101394187047026+c.upper)) = pointBounds22241 := by
 decide +kernel
def cuts22242 : List PrefixCut := [⟨72,326958669,326958860⟩,
⟨128,578993634,578993972⟩]
theorem checked22242 : checkPrefixCuts (2^48) 2919235585 9 Manual.Count131072.C022242.packed 128 cuts22242 = true := by
 decide +kernel
def pointBounds22242 : List (Nat × Nat × Nat) := [(2919309312,101394713789097,101395094954287)]
theorem point_links_checked22242 : (cuts22242.take 1).map (fun c => (2919235585-1+2*2^9*c.k,101394386830428+c.lower,101394767995427+c.upper)) = pointBounds22242 := by
 decide +kernel
def cuts22243 : List PrefixCut := [⟨34,156482925,156483014⟩,
⟨124,566627047,566627370⟩,
⟨128,584752534,584752867⟩]
theorem checked22243 : checkPrefixCuts (2^48) 2919366657 9 Manual.Count131072.C022243.packed 128 cuts22243 = true := by
 decide +kernel
def pointBounds22243 : List (Nat × Nat × Nat) := [(2919401472,101395122306987,101395503472413),(2919493632,101395532451109,101395913616769)]
theorem point_links_checked22243 : (cuts22243.take 2).map (fun c => (2919366657-1+2*2^9*c.k,101394965824062+c.lower,101395346989399+c.upper)) = pointBounds22243 := by
 decide +kernel
def cuts22244 : List PrefixCut := [⟨86,390848714,390848935⟩,
⟨128,583762056,583762387⟩]
theorem checked22244 : checkPrefixCuts (2^48) 2919497729 9 Manual.Count131072.C022244.packed 128 cuts22244 = true := by
 decide +kernel
def pointBounds22244 : List (Nat × Nat × Nat) := [(2919585792,101395941425310,101396322591201)]
theorem point_links_checked22244 : (cuts22244.take 1).map (fun c => (2919497729-1+2*2^9*c.k,101395550576596+c.lower,101395931742266+c.upper)) = pointBounds22244 := by
 decide +kernel
def cuts22245 : List PrefixCut := [⟨48,219422235,219422359⟩,
⟨128,577662435,577662768⟩]
theorem checked22245 : checkPrefixCuts (2^48) 2919628801 9 Manual.Count131072.C022245.packed 128 cuts22245 = true := by
 decide +kernel
def pointBounds22245 : List (Nat × Nat × Nat) := [(2919677952,101396353760887,101396734927012)]
theorem point_links_checked22245 : (cuts22245.take 1).map (fun c => (2919628801-1+2*2^9*c.k,101396134338652+c.lower,101396515504653+c.upper)) = pointBounds22245 := by
 decide +kernel
def cuts22246 : List PrefixCut := [⟨10,44152699,44152725⟩,
⟨100,447496823,447497075⟩,
⟨128,573298279,573298602⟩]
theorem checked22246 : checkPrefixCuts (2^48) 2919759873 9 Manual.Count131072.C022246.packed 128 cuts22246 = true := by
 decide +kernel
def pointBounds22246 : List (Nat × Nat × Nat) := [(2919770112,101396756153786,101397137320146),(2919862272,101397159497910,101397540664496)]
theorem point_links_checked22246 : (cuts22246.take 2).map (fun c => (2919759873-1+2*2^9*c.k,101396712001087+c.lower,101397093167421+c.upper)) = pointBounds22246 := by
 decide +kernel
def cuts22247 : List PrefixCut := [⟨62,280711163,280711327⟩,
⟨128,578478137,578478471⟩]
theorem checked22247 : checkPrefixCuts (2^48) 2919890945 9 Manual.Count131072.C022247.packed 128 cuts22247 = true := by
 decide +kernel
def pointBounds22247 : List (Nat × Nat × Nat) := [(2919954432,101397566010529,101397947177350)]
theorem point_links_checked22247 : (cuts22247.take 1).map (fun c => (2919890945-1+2*2^9*c.k,101397285299366+c.lower,101397666466023+c.upper)) = pointBounds22247 := by
 decide +kernel
def cuts22248 : List PrefixCut := [⟨24,113456199,113456261⟩,
⟨114,519654015,519654315⟩,
⟨128,584332179,584332515⟩]
theorem checked22248 : checkPrefixCuts (2^48) 2920022017 9 Manual.Count131072.C022248.packed 128 cuts22248 = true := by
 decide +kernel
def pointBounds22248 : List (Nat × Nat × Nat) := [(2920046592,101397977233702,101398358400755),(2920138752,101398383431518,101398764598809)]
theorem point_links_checked22248 : (cuts22248.take 2).map (fun c => (2920022017-1+2*2^9*c.k,101397863777503+c.lower,101398244944494+c.upper)) = pointBounds22248 := by
 decide +kernel
def cuts22249 : List PrefixCut := [⟨76,342470795,342470989⟩,
⟨128,576787663,576787985⟩]
theorem checked22249 : checkPrefixCuts (2^48) 2920153089 9 Manual.Count131072.C022249.packed 128 cuts22249 = true := by
 decide +kernel
def pointBounds22249 : List (Nat × Nat × Nat) := [(2920230912,101398790580477,101399171747998)]
theorem point_links_checked22249 : (cuts22249.take 1).map (fun c => (2920153089-1+2*2^9*c.k,101398448109682+c.lower,101398829277009+c.upper)) = pointBounds22249 := by
 decide +kernel
def cuts22250 : List PrefixCut := [⟨38,169542088,169542182⟩,
⟨128,582737371,582737699⟩]
theorem checked22250 : checkPrefixCuts (2^48) 2920284161 9 Manual.Count131072.C022250.packed 128 cuts22250 = true := by
 decide +kernel
def pointBounds22250 : List (Nat × Nat × Nat) := [(2920323072,101399194439433,101399575607176),(2920415232,101399607634716,101399988802693)]
theorem point_links_checked22250 : (cuts22250.take 2).map (fun c => (2920284161-1+2*2^9*c.k,101399024897345+c.lower,101399406064994+c.upper)) = pointBounds22250 := by
 decide +kernel
def cuts22251 : List PrefixCut := [⟨90,406917497,406917730⟩,
⟨128,583674982,583675318⟩]
theorem checked22251 : checkPrefixCuts (2^48) 2920415233 9 Manual.Count131072.C022251.packed 128 cuts22251 = true := by
 decide +kernel
def pointBounds22251 : List (Nat × Nat × Nat) := [(2920507392,101400014552213,101400395720423)]
theorem point_links_checked22251 : (cuts22251.take 1).map (fun c => (2920415233-1+2*2^9*c.k,101399607634716+c.lower,101399988802693+c.upper)) = pointBounds22251 := by
 decide +kernel
def cuts22252 : List PrefixCut := [⟨52,228798055,228798187⟩,
⟨128,571794656,571794989⟩]
theorem checked22252 : checkPrefixCuts (2^48) 2920546305 9 Manual.Count131072.C022252.packed 128 cuts22252 = true := by
 decide +kernel
def pointBounds22252 : List (Nat × Nat × Nat) := [(2920599552,101400420107753,101400801276198)]
theorem point_links_checked22252 : (cuts22252.take 1).map (fun c => (2920546305-1+2*2^9*c.k,101400191309698+c.lower,101400572478011+c.upper)) = pointBounds22252 := by
 decide +kernel
def cuts22253 : List PrefixCut := [⟨14,62449655,62449689⟩,
⟨104,471545152,471545427⟩,
⟨128,579189595,579189929⟩]
theorem checked22253 : checkPrefixCuts (2^48) 2920677377 9 Manual.Count131072.C022253.packed 128 cuts22253 = true := by
 decide +kernel
def pointBounds22253 : List (Nat × Nat × Nat) := [(2920691712,101400825554009,101401206722689),(2920783872,101401234649506,101401615818427)]
theorem point_links_checked22253 : (cuts22253.take 2).map (fun c => (2920677377-1+2*2^9*c.k,101400763104354+c.lower,101401144273000+c.upper)) = pointBounds22253 := by
 decide +kernel
def cuts22254 : List PrefixCut := [⟨66,294403407,294403578⟩,
⟨128,574730773,574731105⟩]
theorem checked22254 : checkPrefixCuts (2^48) 2920808449 9 Manual.Count131072.C022254.packed 128 cuts22254 = true := by
 decide +kernel
def pointBounds22254 : List (Nat × Nat × Nat) := [(2920876032,101401636697356,101402017866507)]
theorem point_links_checked22254 : (cuts22254.take 1).map (fun c => (2920808449-1+2*2^9*c.k,101401342293949+c.lower,101401723462929+c.upper)) = pointBounds22254 := by
 decide +kernel
def cuts22255 : List PrefixCut := [⟨28,127296883,127296961⟩,
⟨118,533848312,533848626⟩,
⟨128,578463156,578463496⟩]
theorem checked22255 : checkPrefixCuts (2^48) 2920939521 9 Manual.Count131072.C022255.packed 128 cuts22255 = true := by
 decide +kernel
def pointBounds22255 : List (Nat × Nat × Nat) := [(2920968192,101402044321605,101402425490995),(2921060352,101402450873034,101402832042660)]
theorem point_links_checked22255 : (cuts22255.take 2).map (fun c => (2920939521-1+2*2^9*c.k,101401917024722+c.lower,101402298194034+c.upper)) = pointBounds22255 := by
 decide +kernel
def cuts22256 : List PrefixCut := [⟨80,358647581,358647793⟩,
⟨128,585374840,585375183⟩]
theorem checked22256 : checkPrefixCuts (2^48) 2921070593 9 Manual.Count131072.C022256.packed 128 cuts22256 = true := by
 decide +kernel
def pointBounds22256 : List (Nat × Nat × Nat) := [(2921152512,101402854135459,101403235305323)]
theorem point_links_checked22256 : (cuts22256.take 1).map (fun c => (2921070593-1+2*2^9*c.k,101402495487878+c.lower,101402876657530+c.upper)) = pointBounds22256 := by
 decide +kernel
def cuts22257 : List PrefixCut := [⟨42,197142619,197142733⟩,
⟨128,590262806,590263154⟩]
theorem checked22257 : checkPrefixCuts (2^48) 2921201665 9 Manual.Count131072.C022257.packed 128 cuts22257 = true := by
 decide +kernel
def pointBounds22257 : List (Nat × Nat × Nat) := [(2921244672,101403278005337,101403659175446)]
theorem point_links_checked22257 : (cuts22257.take 1).map (fun c => (2921201665-1+2*2^9*c.k,101403080862718+c.lower,101403462032713+c.upper)) = pointBounds22257 := by
 decide +kernel
def cuts22258 : List PrefixCut := [⟨4,16957857,16957868⟩,
⟨94,419603979,419604226⟩,
⟨128,571929833,571930171⟩]
theorem checked22258 : checkPrefixCuts (2^48) 2921332737 9 Manual.Count131072.C022258.packed 128 cuts22258 = true := by
 decide +kernel
def pointBounds22258 : List (Nat × Nat × Nat) := [(2921336832,101403688083381,101404069253735),(2921428992,101404090729503,101404471900093)]
theorem point_links_checked22258 : (cuts22258.take 2).map (fun c => (2921332737-1+2*2^9*c.k,101403671125524+c.lower,101404052295867+c.upper)) = pointBounds22258 := by
 decide +kernel
def cuts22259 : List PrefixCut := [⟨56,252330874,252331014⟩,
⟨128,585777806,585778131⟩]
theorem checked22259 : checkPrefixCuts (2^48) 2921463809 9 Manual.Count131072.C022259.packed 128 cuts22259 = true := by
 decide +kernel
def pointBounds22259 : List (Nat × Nat × Nat) := [(2921521152,101404495386231,101404876557052)]
theorem point_links_checked22259 : (cuts22259.take 1).map (fun c => (2921463809-1+2*2^9*c.k,101404243055357+c.lower,101404624226038+c.upper)) = pointBounds22259 := by
 decide +kernel
def cuts22260 : List PrefixCut := [⟨18,81120454,81120501⟩,
⟨108,489894291,489894570⟩,
⟨128,581897952,581898281⟩]
theorem checked22260 : checkPrefixCuts (2^48) 2921594881 9 Manual.Count131072.C022260.packed 128 cuts22260 = true := by
 decide +kernel
def pointBounds22260 : List (Nat × Nat × Nat) := [(2921613312,101404909953617,101405291124670),(2921705472,101405318727454,101405699898739)]
theorem point_links_checked22260 : (cuts22260.take 2).map (fun c => (2921594881-1+2*2^9*c.k,101404828833163+c.lower,101405210004169+c.upper)) = pointBounds22260 := by
 decide +kernel
def cuts22261 : List PrefixCut := [⟨70,314156270,314156456⟩,
⟨128,577825793,577826127⟩]
theorem checked22261 : checkPrefixCuts (2^48) 2921725953 9 Manual.Count131072.C022261.packed 128 cuts22261 = true := by
 decide +kernel
def pointBounds22261 : List (Nat × Nat × Nat) := [(2921797632,101405724887385,101406106058906)]
theorem point_links_checked22261 : (cuts22261.take 1).map (fun c => (2921725953-1+2*2^9*c.k,101405410731115+c.lower,101405791902450+c.upper)) = pointBounds22261 := by
 decide +kernel
def cuts22262 : List PrefixCut := [⟨32,141995888,141995968⟩,
⟨122,551116428,551116740⟩,
⟨128,577221865,577222193⟩]
theorem checked22262 : checkPrefixCuts (2^48) 2921857025 9 Manual.Count131072.C022262.packed 128 cuts22262 = true := by
 decide +kernel
def pointBounds22262 : List (Nat × Nat × Nat) := [(2921889792,101406130552796,101406511724545),(2921981952,101406539673336,101406920845317)]
theorem point_links_checked22262 : (cuts22262.take 2).map (fun c => (2921857025-1+2*2^9*c.k,101405988556908+c.lower,101406369728577+c.upper)) = pointBounds22262 := by
 decide +kernel
def cuts22263 : List PrefixCut := [⟨84,375006888,375007098⟩,
⟨128,573824465,573824791⟩]
theorem checked22263 : checkPrefixCuts (2^48) 2921988097 9 Manual.Count131072.C022263.packed 128 cuts22263 = true := by
 decide +kernel
def pointBounds22263 : List (Nat × Nat × Nat) := [(2922074112,101406940785661,101407321957868)]
theorem point_links_checked22263 : (cuts22263.take 1).map (fun c => (2921988097-1+2*2^9*c.k,101406565778773+c.lower,101406946950770+c.upper)) = pointBounds22263 := by
 decide +kernel
def cuts22264 : List PrefixCut := [⟨46,210662418,210662541⟩,
⟨128,585742911,585743246⟩]
theorem checked22264 : checkPrefixCuts (2^48) 2922119169 9 Manual.Count131072.C022264.packed 128 cuts22264 = true := by
 decide +kernel
def pointBounds22264 : List (Nat × Nat × Nat) := [(2922166272,101407350265656,101407731438102)]
theorem point_links_checked22264 : (cuts22264.take 1).map (fun c => (2922119169-1+2*2^9*c.k,101407139603238+c.lower,101407520775561+c.upper)) = pointBounds22264 := by
 decide +kernel
def cuts22265 : List PrefixCut := [⟨8,36313075,36313094⟩,
⟨98,444900316,444900565⟩,
⟨128,580322670,580322999⟩]
theorem checked22265 : checkPrefixCuts (2^48) 2922250241 9 Manual.Count131072.C022265.packed 128 cuts22265 = true := by
 decide +kernel
def pointBounds22265 : List (Nat × Nat × Nat) := [(2922258432,101407761659224,101408142831901),(2922350592,101408170246465,101408551419372)]
theorem point_links_checked22265 : (cuts22265.take 2).map (fun c => (2922250241-1+2*2^9*c.k,101407725346149+c.lower,101408106518807+c.upper)) = pointBounds22265 := by
 decide +kernel
def cuts22266 : List PrefixCut := [⟨60,271803608,271803764⟩,
⟨128,574614184,574614514⟩]
theorem checked22266 : checkPrefixCuts (2^48) 2922381313 9 Manual.Count131072.C022266.packed 128 cuts22266 = true := by
 decide +kernel
def pointBounds22266 : List (Nat × Nat × Nat) := [(2922442752,101408577472427,101408958645570)]
theorem point_links_checked22266 : (cuts22266.take 1).map (fun c => (2922381313-1+2*2^9*c.k,101408305668819+c.lower,101408686841806+c.upper)) = pointBounds22266 := by
 decide +kernel
def cuts22267 : List PrefixCut := [⟨22,98912703,98912759⟩,
⟨112,506787203,506787494⟩,
⟨128,577959250,577959580⟩]
theorem checked22267 : checkPrefixCuts (2^48) 2922512385 9 Manual.Count131072.C022267.packed 128 cuts22267 = true := by
 decide +kernel
def pointBounds22267 : List (Nat × Nat × Nat) := [(2922534912,101408979195706,101409360369079),(2922627072,101409387070206,101409768243814)]
theorem point_links_checked22267 : (cuts22267.take 2).map (fun c => (2922512385-1+2*2^9*c.k,101408880283003+c.lower,101409261456320+c.upper)) = pointBounds22267 := by
 decide +kernel
def cuts22268 : List PrefixCut := [⟨74,341601202,341601395⟩,
⟨128,586023072,586023405⟩]
theorem checked22268 : checkPrefixCuts (2^48) 2922643457 9 Manual.Count131072.C022268.packed 128 cuts22268 = true := by
 decide +kernel
def pointBounds22268 : List (Nat × Nat × Nat) := [(2922719232,101409799843455,101410181017295)]
theorem point_links_checked22268 : (cuts22268.take 1).map (fun c => (2922643457-1+2*2^9*c.k,101409458242253+c.lower,101409839415900+c.upper)) = pointBounds22268 := by
 decide +kernel
def cuts22269 : List PrefixCut := [⟨36,164004679,164004774⟩,
⟨126,573285145,573285469⟩,
⟨128,582241019,582241349⟩]
theorem checked22269 : checkPrefixCuts (2^48) 2922774529 9 Manual.Count131072.C022269.packed 128 cuts22269 = true := by
 decide +kernel
def pointBounds22269 : List (Nat × Nat × Nat) := [(2922811392,101410208270004,101410589444079),(2922903552,101410617550470,101410998724774)]
theorem point_links_checked22269 : (cuts22269.take 2).map (fun c => (2922774529-1+2*2^9*c.k,101410044265325+c.lower,101410425439305+c.upper)) = pointBounds22269 := by
 decide +kernel
def cuts22270 : List PrefixCut := [⟨88,403970970,403971202⟩,
⟨128,584911210,584911544⟩]
theorem checked22270 : checkPrefixCuts (2^48) 2922905601 9 Manual.Count131072.C022270.packed 128 cuts22270 = true := by
 decide +kernel
def pointBounds22270 : List (Nat × Nat × Nat) := [(2922995712,101411030477314,101411411651856)]
theorem point_links_checked22270 : (cuts22270.take 1).map (fun c => (2922905601-1+2*2^9*c.k,101410626506344+c.lower,101411007680654+c.upper)) = pointBounds22270 := by
 decide +kernel
def cuts22271 : List PrefixCut := [⟨50,222536673,222536802⟩,
⟨128,577855473,577855805⟩]
theorem checked22271 : checkPrefixCuts (2^48) 2923036673 9 Manual.Count131072.C022271.packed 128 cuts22271 = true := by
 decide +kernel
def pointBounds22271 : List (Nat × Nat × Nat) := [(2923087872,101411433954227,101411815129000)]
theorem point_links_checked22271 : (cuts22271.take 1).map (fun c => (2923036673-1+2*2^9*c.k,101411211417554+c.lower,101411592592198+c.upper)) = pointBounds22271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000070
