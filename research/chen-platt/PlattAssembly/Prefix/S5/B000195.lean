import PlattAssemblyKernel
import PlattCertificates.Count131072.C046240
import PlattCertificates.Count131072.C046241
import PlattCertificates.Count131072.C046242
import PlattCertificates.Count131072.C046243
import PlattCertificates.Count131072.C046244
import PlattCertificates.Count131072.C046245
import PlattCertificates.Count131072.C046246
import PlattCertificates.Count131072.C046247
import PlattCertificates.Count131072.C046248
import PlattCertificates.Count131072.C046249
import PlattCertificates.Count131072.C046250
import PlattCertificates.Count131072.C046251
import PlattCertificates.Count131072.C046252
import PlattCertificates.Count131072.C046253
import PlattCertificates.Count131072.C046254
import PlattCertificates.Count131072.C046255
import PlattCertificates.Count131072.C046256
import PlattCertificates.Count131072.C046257
import PlattCertificates.Count131072.C046258
import PlattCertificates.Count131072.C046259
import PlattCertificates.Count131072.C046260
import PlattCertificates.Count131072.C046261
import PlattCertificates.Count131072.C046262
import PlattCertificates.Count131072.C046263
import PlattCertificates.Count131072.C046264
import PlattCertificates.Count131072.C046265
import PlattCertificates.Count131072.C046266
import PlattCertificates.Count131072.C046267
import PlattCertificates.Count131072.C046268
import PlattCertificates.Count131072.C046269
import PlattCertificates.Count131072.C046270
import PlattCertificates.Count131072.C046271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000195
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46240 : List PrefixCut := [⟨64,268536925,268537078⟩]
theorem checked46240 : checkPrefixCuts (2^48) 6064701441 10 Manual.Count131072.C046240.packed 64 cuts46240 = true := by
 decide +kernel
def cuts46241 : List PrefixCut := [⟨4,15454850,15454859⟩,
⟨64,266953129,266953274⟩]
theorem checked46241 : checkPrefixCuts (2^48) 6064832513 10 Manual.Count131072.C046241.packed 64 cuts46241 = true := by
 decide +kernel
def pointBounds46241 : List (Nat × Nat × Nat) := [(6064840704,110682534378612,110682920943612)]
theorem point_links_checked46241 : (cuts46241.take 1).map (fun c => (6064832513-1+2*2^10*c.k,110682518923762+c.lower,110682905488753+c.upper)) = pointBounds46241 := by
 decide +kernel
def cuts46242 : List PrefixCut := [⟨33,138300994,138301069⟩,
⟨64,269035795,269035941⟩]
theorem checked46242 : checkPrefixCuts (2^48) 6064963585 10 Manual.Count131072.C046242.packed 64 cuts46242 = true := by
 decide +kernel
def pointBounds46242 : List (Nat × Nat × Nat) := [(6065031168,110682924177885,110683310743096)]
theorem point_links_checked46242 : (cuts46242.take 1).map (fun c => (6064963585-1+2*2^10*c.k,110682785876891+c.lower,110683172442027+c.upper)) = pointBounds46242 := by
 decide +kernel
def cuts46243 : List PrefixCut := [⟨62,261697525,261697677⟩,
⟨64,269958149,269958305⟩]
theorem checked46243 : checkPrefixCuts (2^48) 6065094657 10 Manual.Count131072.C046243.packed 64 cuts46243 = true := by
 decide +kernel
def pointBounds46243 : List (Nat × Nat × Nat) := [(6065221632,110683316610211,110683703175645)]
theorem point_links_checked46243 : (cuts46243.take 1).map (fun c => (6065094657-1+2*2^10*c.k,110683054912686+c.lower,110683441477968+c.upper)) = pointBounds46243 := by
 decide +kernel
def cuts46244 : List PrefixCut := [⟨64,269070593,269070750⟩]
theorem checked46244 : checkPrefixCuts (2^48) 6065225729 10 Manual.Count131072.C046244.packed 64 cuts46244 = true := by
 decide +kernel
def cuts46245 : List PrefixCut := [⟨27,114439096,114439162⟩,
⟨64,268879154,268879308⟩]
theorem checked46245 : checkPrefixCuts (2^48) 6065356801 10 Manual.Count131072.C046245.packed 64 cuts46245 = true := by
 decide +kernel
def pointBounds46245 : List (Nat × Nat × Nat) := [(6065412096,110683708380524,110684094946185)]
theorem point_links_checked46245 : (cuts46245.take 1).map (fun c => (6065356801-1+2*2^10*c.k,110683593941428+c.lower,110683980507023+c.upper)) = pointBounds46245 := by
 decide +kernel
def cuts46246 : List PrefixCut := [⟨56,240102261,240102400⟩,
⟨64,275555711,275555870⟩]
theorem checked46246 : checkPrefixCuts (2^48) 6065487873 10 Manual.Count131072.C046246.packed 64 cuts46246 = true := by
 decide +kernel
def pointBounds46246 : List (Nat × Nat × Nat) := [(6065602560,110684102922843,110684489488731)]
theorem point_links_checked46246 : (cuts46246.take 1).map (fun c => (6065487873-1+2*2^10*c.k,110683862820582+c.lower,110684249386331+c.upper)) = pointBounds46246 := by
 decide +kernel
def cuts46247 : List PrefixCut := [⟨64,270538052,270538208⟩]
theorem checked46247 : checkPrefixCuts (2^48) 6065618945 10 Manual.Count131072.C046247.packed 64 cuts46247 = true := by
 decide +kernel
def cuts46248 : List PrefixCut := [⟨21,87285567,87285615⟩,
⟨64,268212067,268212217⟩]
theorem checked46248 : checkPrefixCuts (2^48) 6065750017 10 Manual.Count131072.C046248.packed 64 cuts46248 = true := by
 decide +kernel
def pointBounds46248 : List (Nat × Nat × Nat) := [(6065793024,110684496199912,110684882766024)]
theorem point_links_checked46248 : (cuts46248.take 1).map (fun c => (6065750017-1+2*2^10*c.k,110684408914345+c.lower,110684795480409+c.upper)) = pointBounds46248 := by
 decide +kernel
def cuts46249 : List PrefixCut := [⟨50,212755808,212755930⟩,
⟨64,271500837,271500994⟩]
theorem checked46249 : checkPrefixCuts (2^48) 6065881089 10 Manual.Count131072.C046249.packed 64 cuts46249 = true := by
 decide +kernel
def pointBounds46249 : List (Nat × Nat × Nat) := [(6065983488,110684889882220,110685276448556)]
theorem point_links_checked46249 : (cuts46249.take 1).map (fun c => (6065881089-1+2*2^10*c.k,110684677126412+c.lower,110685063692626+c.upper)) = pointBounds46249 := by
 decide +kernel
def cuts46250 : List PrefixCut := [⟨64,267875666,267875816⟩]
theorem checked46250 : checkPrefixCuts (2^48) 6066012161 10 Manual.Count131072.C046250.packed 64 cuts46250 = true := by
 decide +kernel
def cuts46251 : List PrefixCut := [⟨15,63197954,63197990⟩,
⟨64,273623521,273623673⟩]
theorem checked46251 : checkPrefixCuts (2^48) 6066143233 10 Manual.Count131072.C046251.packed 64 cuts46251 = true := by
 decide +kernel
def pointBounds46251 : List (Nat × Nat × Nat) := [(6066173952,110685279700869,110685666267426)]
theorem point_links_checked46251 : (cuts46251.take 1).map (fun c => (6066143233-1+2*2^10*c.k,110685216502915+c.lower,110685603069436+c.upper)) = pointBounds46251 := by
 decide +kernel
def cuts46252 : List PrefixCut := [⟨44,186062466,186062574⟩,
⟨64,272086427,272086585⟩]
theorem checked46252 : checkPrefixCuts (2^48) 6066274305 10 Manual.Count131072.C046252.packed 64 cuts46252 = true := by
 decide +kernel
def pointBounds46252 : List (Nat × Nat × Nat) := [(6066364416,110685676188902,110686062755683)]
theorem point_links_checked46252 : (cuts46252.take 1).map (fun c => (6066274305-1+2*2^10*c.k,110685490126436+c.lower,110685876693109+c.upper)) = pointBounds46252 := by
 decide +kernel
def cuts46253 : List PrefixCut := [⟨64,271245397,271245550⟩]
theorem checked46253 : checkPrefixCuts (2^48) 6066405377 10 Manual.Count131072.C046253.packed 64 cuts46253 = true := by
 decide +kernel
def cuts46254 : List PrefixCut := [⟨9,39206214,39206238⟩,
⟨64,272028286,272028440⟩]
theorem checked46254 : checkPrefixCuts (2^48) 6066536449 10 Manual.Count131072.C046254.packed 64 cuts46254 = true := by
 decide +kernel
def pointBounds46254 : List (Nat × Nat × Nat) := [(6066554880,110686072664474,110686459231482)]
theorem point_links_checked46254 : (cuts46254.take 1).map (fun c => (6066536449-1+2*2^10*c.k,110686033458260+c.lower,110686420025244+c.upper)) = pointBounds46254 := by
 decide +kernel
def cuts46255 : List PrefixCut := [⟨38,161970720,161970815⟩,
⟨64,272579160,272579318⟩]
theorem checked46255 : checkPrefixCuts (2^48) 6066667521 10 Manual.Count131072.C046255.packed 64 cuts46255 = true := by
 decide +kernel
def pointBounds46255 : List (Nat × Nat × Nat) := [(6066745344,110686467457266,110686854024499)]
theorem point_links_checked46255 : (cuts46255.take 1).map (fun c => (6066667521-1+2*2^10*c.k,110686305486546+c.lower,110686692053684+c.upper)) = pointBounds46255 := by
 decide +kernel
def cuts46256 : List PrefixCut := [⟨64,270021517,270021678⟩]
theorem checked46256 : checkPrefixCuts (2^48) 6066798593 10 Manual.Count131072.C046256.packed 64 cuts46256 = true := by
 decide +kernel
def cuts46257 : List PrefixCut := [⟨3,12990580,12990587⟩,
⟨64,272149835,272149988⟩]
theorem checked46257 : checkPrefixCuts (2^48) 6066929665 10 Manual.Count131072.C046257.packed 64 cuts46257 = true := by
 decide +kernel
def pointBounds46257 : List (Nat × Nat × Nat) := [(6066935808,110686861077803,110687247645267)]
theorem point_links_checked46257 : (cuts46257.take 1).map (fun c => (6066929665-1+2*2^10*c.k,110686848087223+c.lower,110687234654680+c.upper)) = pointBounds46257 := by
 decide +kernel
def cuts46258 : List PrefixCut := [⟨32,136907802,136907880⟩,
⟨64,272375939,272376095⟩]
theorem checked46258 : checkPrefixCuts (2^48) 6067060737 10 Manual.Count131072.C046258.packed 64 cuts46258 = true := by
 decide +kernel
def pointBounds46258 : List (Nat × Nat × Nat) := [(6067126272,110687257144860,110687643712548)]
theorem point_links_checked46258 : (cuts46258.take 1).map (fun c => (6067060737-1+2*2^10*c.k,110687120237058+c.lower,110687506804668+c.upper)) = pointBounds46258 := by
 decide +kernel
def cuts46259 : List PrefixCut := [⟨61,253952359,253952501⟩,
⟨64,266802934,266803083⟩]
theorem checked46259 : checkPrefixCuts (2^48) 6067191809 10 Manual.Count131072.C046259.packed 64 cuts46259 = true := by
 decide +kernel
def pointBounds46259 : List (Nat × Nat × Nat) := [(6067316736,110687646565356,110688033133264)]
theorem point_links_checked46259 : (cuts46259.take 1).map (fun c => (6067191809-1+2*2^10*c.k,110687392612997+c.lower,110687779180763+c.upper)) = pointBounds46259 := by
 decide +kernel
def cuts46260 : List PrefixCut := [⟨64,269766248,269766411⟩]
theorem checked46260 : checkPrefixCuts (2^48) 6067322881 10 Manual.Count131072.C046260.packed 64 cuts46260 = true := by
 decide +kernel
def cuts46261 : List PrefixCut := [⟨26,111291380,111291440⟩,
⟨64,272451050,272451199⟩]
theorem checked46261 : checkPrefixCuts (2^48) 6067453953 10 Manual.Count131072.C046261.packed 64 cuts46261 = true := by
 decide +kernel
def pointBounds46261 : List (Nat × Nat × Nat) := [(6067507200,110688040473559,110688427041697)]
theorem point_links_checked46261 : (cuts46261.take 1).map (fun c => (6067453953-1+2*2^10*c.k,110687929182179+c.lower,110688315750257+c.upper)) = pointBounds46261 := by
 decide +kernel
def cuts46262 : List PrefixCut := [⟨55,233571154,233571282⟩,
⟨64,270311248,270311398⟩]
theorem checked46262 : checkPrefixCuts (2^48) 6067585025 10 Manual.Count131072.C046262.packed 64 cuts46262 = true := by
 decide +kernel
def pointBounds46262 : List (Nat × Nat × Nat) := [(6067697664,110688435204383,110688821772738)]
theorem point_links_checked46262 : (cuts46262.take 1).map (fun c => (6067585025-1+2*2^10*c.k,110688201633229+c.lower,110688588201456+c.upper)) = pointBounds46262 := by
 decide +kernel
def cuts46263 : List PrefixCut := [⟨64,272021786,272021938⟩]
theorem checked46263 : checkPrefixCuts (2^48) 6067716097 10 Manual.Count131072.C046263.packed 64 cuts46263 = true := by
 decide +kernel
def cuts46264 : List PrefixCut := [⟨20,82941346,82941395⟩,
⟨64,270253167,270253320⟩]
theorem checked46264 : checkPrefixCuts (2^48) 6067847169 10 Manual.Count131072.C046264.packed 64 cuts46264 = true := by
 decide +kernel
def pointBounds46264 : List (Nat × Nat × Nat) := [(6067888128,110688826907609,110689213476187)]
theorem point_links_checked46264 : (cuts46264.take 1).map (fun c => (6067847169-1+2*2^10*c.k,110688743966263+c.lower,110689130534792+c.upper)) = pointBounds46264 := by
 decide +kernel
def cuts46265 : List PrefixCut := [⟨49,206002671,206002793⟩,
⟨64,268670220,268670379⟩]
theorem checked46265 : checkPrefixCuts (2^48) 6067978241 10 Manual.Count131072.C046265.packed 64 cuts46265 = true := by
 decide +kernel
def pointBounds46265 : List (Nat × Nat × Nat) := [(6068078592,110689220222101,110689606790905)]
theorem point_links_checked46265 : (cuts46265.take 1).map (fun c => (6067978241-1+2*2^10*c.k,110689014219430+c.lower,110689400788112+c.upper)) = pointBounds46265 := by
 decide +kernel
def cuts46266 : List PrefixCut := [⟨64,265602987,265603141⟩]
theorem checked46266 : checkPrefixCuts (2^48) 6068109313 10 Manual.Count131072.C046266.packed 64 cuts46266 = true := by
 decide +kernel
def cuts46267 : List PrefixCut := [⟨14,58955108,58955140⟩,
⟨64,273250650,273250802⟩]
theorem checked46267 : checkPrefixCuts (2^48) 6068240385 10 Manual.Count131072.C046267.packed 64 cuts46267 = true := by
 decide +kernel
def pointBounds46267 : List (Nat × Nat × Nat) := [(6068269056,110689607447745,110689994016772)]
theorem point_links_checked46267 : (cuts46267.take 1).map (fun c => (6068240385-1+2*2^10*c.k,110689548492637+c.lower,110689935061632+c.upper)) = pointBounds46267 := by
 decide +kernel
def cuts46268 : List PrefixCut := [⟨43,179736402,179736506⟩,
⟨64,266611931,266612084⟩]
theorem checked46268 : checkPrefixCuts (2^48) 6068371457 10 Manual.Count131072.C046268.packed 64 cuts46268 = true := by
 decide +kernel
def pointBounds46268 : List (Nat × Nat × Nat) := [(6068459520,110690001479689,110690388048940)]
theorem point_links_checked46268 : (cuts46268.take 1).map (fun c => (6068371457-1+2*2^10*c.k,110689821743287+c.lower,110690208312434+c.upper)) = pointBounds46268 := by
 decide +kernel
def cuts46269 : List PrefixCut := [⟨64,268461472,268461624⟩]
theorem checked46269 : checkPrefixCuts (2^48) 6068502529 10 Manual.Count131072.C046269.packed 64 cuts46269 = true := by
 decide +kernel
def cuts46270 : List PrefixCut := [⟨8,33673229,33673251⟩,
⟨64,267388908,267389068⟩]
theorem checked46270 : checkPrefixCuts (2^48) 6068633601 10 Manual.Count131072.C046270.packed 64 cuts46270 = true := by
 decide +kernel
def pointBounds46270 : List (Nat × Nat × Nat) := [(6068649984,110690390489919,110690777059393)]
theorem point_links_checked46270 : (cuts46270.take 1).map (fun c => (6068633601-1+2*2^10*c.k,110690356816690+c.lower,110690743386142+c.upper)) = pointBounds46270 := by
 decide +kernel
def cuts46271 : List PrefixCut := [⟨37,154586645,154586734⟩,
⟨64,270536977,270537131⟩]
theorem checked46271 : checkPrefixCuts (2^48) 6068764673 10 Manual.Count131072.C046271.packed 64 cuts46271 = true := by
 decide +kernel
def pointBounds46271 : List (Nat × Nat × Nat) := [(6068840448,110690778792243,110691165361944)]
theorem point_links_checked46271 : (cuts46271.take 1).map (fun c => (6068764673-1+2*2^10*c.k,110690624205598+c.lower,110691010775210+c.upper)) = pointBounds46271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000195
