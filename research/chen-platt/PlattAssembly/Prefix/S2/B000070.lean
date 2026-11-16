import PlattAssemblyKernel
import PlattCertificates.Count131072.C012240
import PlattCertificates.Count131072.C012241
import PlattCertificates.Count131072.C012242
import PlattCertificates.Count131072.C012243
import PlattCertificates.Count131072.C012244
import PlattCertificates.Count131072.C012245
import PlattCertificates.Count131072.C012246
import PlattCertificates.Count131072.C012247
import PlattCertificates.Count131072.C012248
import PlattCertificates.Count131072.C012249
import PlattCertificates.Count131072.C012250
import PlattCertificates.Count131072.C012251
import PlattCertificates.Count131072.C012252
import PlattCertificates.Count131072.C012253
import PlattCertificates.Count131072.C012254
import PlattCertificates.Count131072.C012255
import PlattCertificates.Count131072.C012256
import PlattCertificates.Count131072.C012257
import PlattCertificates.Count131072.C012258
import PlattCertificates.Count131072.C012259
import PlattCertificates.Count131072.C012260
import PlattCertificates.Count131072.C012261
import PlattCertificates.Count131072.C012262
import PlattCertificates.Count131072.C012263
import PlattCertificates.Count131072.C012264
import PlattCertificates.Count131072.C012265
import PlattCertificates.Count131072.C012266
import PlattCertificates.Count131072.C012267
import PlattCertificates.Count131072.C012268
import PlattCertificates.Count131072.C012269
import PlattCertificates.Count131072.C012270
import PlattCertificates.Count131072.C012271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12240 : List PrefixCut := [⟨28,231898088,231898264⟩,
⟨78,647554091,647554585⟩,
⟨128,1075097362,1075098176⟩]
theorem checked12240 : checkPrefixCuts (2^48) 1608253441 9 Manual.Count131072.C012240.packed 128 cuts12240 = true := by
 decide +kernel
def pointBounds12240 : List (Nat × Nat × Nat) := [(1608282112,93587980449481,93588356585026),(1608333312,93588396105484,93588772241347),(1608384512,93588823648755,93589199784938)]
theorem point_links_checked12240 : (cuts12240.take 3).map (fun c => (1608253441-1+2*2^9*c.k,93587748551393+c.lower,93588124686762+c.upper)) = pointBounds12240 := by
 decide +kernel
def cuts12241 : List PrefixCut := [⟨50,428404654,428404982⟩,
⟨100,852770760,852771410⟩,
⟨128,1081835257,1081836080⟩]
theorem checked12241 : checkPrefixCuts (2^48) 1608384513 9 Manual.Count131072.C012241.packed 128 cuts12241 = true := by
 decide +kernel
def pointBounds12241 : List (Nat × Nat × Nat) := [(1608435712,93589252053409,93589628189920),(1608486912,93589676419515,93590052556348)]
theorem point_links_checked12241 : (cuts12241.take 2).map (fun c => (1608384513-1+2*2^9*c.k,93588823648755+c.lower,93589199784938+c.upper)) = pointBounds12241 := by
 decide +kernel
def cuts12242 : List PrefixCut := [⟨22,189688315,189688457⟩,
⟨72,613152421,613152882⟩,
⟨122,1032053702,1032054478⟩,
⟨128,1081047133,1081047947⟩]
theorem checked12242 : checkPrefixCuts (2^48) 1608515585 9 Manual.Count131072.C012242.packed 128 cuts12242 = true := by
 decide +kernel
def pointBounds12242 : List (Nat × Nat × Nat) := [(1608538112,93590095172327,93590471309475),(1608589312,93590518636433,93590894773900),(1608640512,93590937537714,93591313675496)]
theorem point_links_checked12242 : (cuts12242.take 3).map (fun c => (1608515585-1+2*2^9*c.k,93589905484012+c.lower,93590281621018+c.upper)) = pointBounds12242 := by
 decide +kernel
def cuts12243 : List PrefixCut := [⟨44,370944374,370944652⟩,
⟨94,798042519,798043122⟩,
⟨128,1075710122,1075710933⟩]
theorem checked12243 : checkPrefixCuts (2^48) 1608646657 9 Manual.Count131072.C012243.packed 128 cuts12243 = true := by
 decide +kernel
def pointBounds12243 : List (Nat × Nat × Nat) := [(1608691712,93591357475519,93591733613617),(1608742912,93591784573664,93592160712087)]
theorem point_links_checked12243 : (cuts12243.take 2).map (fun c => (1608646657-1+2*2^9*c.k,93590986531145+c.lower,93591362668965+c.upper)) = pointBounds12243 := by
 decide +kernel
def cuts12244 : List PrefixCut := [⟨16,137169456,137169559⟩,
⟨66,558466699,558467122⟩,
⟨116,973627257,973627998⟩,
⟨128,1075972037,1075972857⟩]
theorem checked12244 : checkPrefixCuts (2^48) 1608777729 9 Manual.Count131072.C012244.packed 128 cuts12244 = true := by
 decide +kernel
def pointBounds12244 : List (Nat × Nat × Nat) := [(1608794112,93592199410723,93592575549457),(1608845312,93592620707966,93592996847020),(1608896512,93593035868524,93593412007896)]
theorem point_links_checked12244 : (cuts12244.take 3).map (fun c => (1608777729-1+2*2^9*c.k,93592062241267+c.lower,93592438379898+c.upper)) = pointBounds12244 := by
 decide +kernel
def cuts12245 : List PrefixCut := [⟨38,323649268,323649511⟩,
⟨88,741582482,741583042⟩,
⟨128,1081132679,1081133492⟩]
theorem checked12245 : checkPrefixCuts (2^48) 1608908801 9 Manual.Count131072.C012245.packed 128 cuts12245 = true := by
 decide +kernel
def pointBounds12245 : List (Nat × Nat × Nat) := [(1608947712,93593461862572,93593838002266),(1608998912,93593879795786,93594255935797)]
theorem point_links_checked12245 : (cuts12245.take 2).map (fun c => (1608908801-1+2*2^9*c.k,93593138213304+c.lower,93593514352755+c.upper)) = pointBounds12245 := by
 decide +kernel
def cuts12246 : List PrefixCut := [⟨10,84492569,84492635⟩,
⟨60,509571280,509571665⟩,
⟨110,934986335,934987039⟩,
⟨128,1084193248,1084194065⟩]
theorem checked12246 : checkPrefixCuts (2^48) 1609039873 9 Manual.Count131072.C012246.packed 128 cuts12246 = true := by
 decide +kernel
def pointBounds12246 : List (Nat × Nat × Nat) := [(1609050112,93594303838552,93594679978882),(1609101312,93594728917263,93595105057912),(1609152512,93595154332318,93595530473286)]
theorem point_links_checked12246 : (cuts12246.take 3).map (fun c => (1609039873-1+2*2^9*c.k,93594219345983+c.lower,93594595486247+c.upper)) = pointBounds12246 := by
 decide +kernel
def cuts12247 : List PrefixCut := [⟨32,273395879,273396085⟩,
⟨82,692661939,692662464⟩,
⟨128,1076059220,1076060034⟩]
theorem checked12247 : checkPrefixCuts (2^48) 1609170945 9 Manual.Count131072.C012247.packed 128 cuts12247 = true := by
 decide +kernel
def pointBounds12247 : List (Nat × Nat × Nat) := [(1609203712,93595576935110,93595953076397),(1609254912,93595996201170,93596372342776)]
theorem point_links_checked12247 : (cuts12247.take 2).map (fun c => (1609170945-1+2*2^9*c.k,93595303539231+c.lower,93595679680312+c.upper)) = pointBounds12247 := by
 decide +kernel
def cuts12248 : List PrefixCut := [⟨4,33406800,33406826⟩,
⟨54,449672891,449673234⟩,
⟨104,864176799,864177453⟩,
⟨128,1069325131,1069325937⟩]
theorem checked12248 : checkPrefixCuts (2^48) 1609302017 9 Manual.Count131072.C012248.packed 128 cuts12248 = true := by
 decide +kernel
def pointBounds12248 : List (Nat × Nat × Nat) := [(1609306112,93596413005251,93596789147172),(1609357312,93596829271342,93597205413580),(1609408512,93597243775250,93597619917799)]
theorem point_links_checked12248 : (cuts12248.take 3).map (fun c => (1609302017-1+2*2^9*c.k,93596379598451+c.lower,93596755740346+c.upper)) = pointBounds12248 := by
 decide +kernel
def cuts12249 : List PrefixCut := [⟨26,224382946,224383111⟩,
⟨76,654949833,654950326⟩,
⟨126,1084803502,1084804314⟩,
⟨128,1099842887,1099843711⟩]
theorem checked12249 : checkPrefixCuts (2^48) 1609433089 9 Manual.Count131072.C012249.packed 128 cuts12249 = true := by
 decide +kernel
def pointBounds12249 : List (Nat × Nat × Nat) := [(1609459712,93597673306528,93598049449394),(1609510912,93598103873415,93598480016609),(1609562112,93598533727084,93598909870597)]
theorem point_links_checked12249 : (cuts12249.take 3).map (fun c => (1609433089-1+2*2^9*c.k,93597448923582+c.lower,93597825066283+c.upper)) = pointBounds12249 := by
 decide +kernel
def cuts12250 : List PrefixCut := [⟨48,405882067,405882373⟩,
⟨98,832560858,832561488⟩,
⟨128,1082965934,1082966751⟩]
theorem checked12250 : checkPrefixCuts (2^48) 1609564161 9 Manual.Count131072.C012250.packed 128 cuts12250 = true := by
 decide +kernel
def pointBounds12250 : List (Nat × Nat × Nat) := [(1609613312,93598954648536,93599330792367),(1609664512,93599381327327,93599757471482)]
theorem point_links_checked12250 : (cuts12250.take 2).map (fun c => (1609564161-1+2*2^9*c.k,93598548766469+c.lower,93598924909994+c.upper)) = pointBounds12250 := by
 decide +kernel
def cuts12251 : List PrefixCut := [⟨20,169964952,169965080⟩,
⟨70,589797108,589797549⟩,
⟨120,1019057921,1019058686⟩,
⟨128,1084451233,1084452048⟩]
theorem checked12251 : checkPrefixCuts (2^48) 1609695233 9 Manual.Count131072.C012251.packed 128 cuts12251 = true := by
 decide +kernel
def pointBounds12251 : List (Nat × Nat × Nat) := [(1609715712,93599801697355,93600177841825),(1609766912,93600221529511,93600597674294),(1609818112,93600650790324,93601026935431)]
theorem point_links_checked12251 : (cuts12251.take 3).map (fun c => (1609695233-1+2*2^9*c.k,93599631732403+c.lower,93600007876745+c.upper)) = pointBounds12251 := by
 decide +kernel
def cuts12252 : List PrefixCut := [⟨42,346718904,346719166⟩,
⟨92,768084584,768085168⟩,
⟨128,1071424548,1071425360⟩]
theorem checked12252 : checkPrefixCuts (2^48) 1609826305 9 Manual.Count131072.C012252.packed 128 cuts12252 = true := by
 decide +kernel
def pointBounds12252 : List (Nat × Nat × Nat) := [(1609869312,93601062902540,93601439047959),(1609920512,93601484268220,93601860413961)]
theorem point_links_checked12252 : (cuts12252.take 2).map (fun c => (1609826305-1+2*2^9*c.k,93600716183636+c.lower,93601092328793+c.upper)) = pointBounds12252 := by
 decide +kernel
def cuts12253 : List PrefixCut := [⟨14,120459925,120460017⟩,
⟨64,542323244,542323654⟩,
⟨114,963998420,963999143⟩,
⟨128,1077456774,1077457583⟩]
theorem checked12253 : checkPrefixCuts (2^48) 1609957377 9 Manual.Count131072.C012253.packed 128 cuts12253 = true := by
 decide +kernel
def pointBounds12253 : List (Nat × Nat × Nat) := [(1609971712,93601908068109,93602284214170),(1610022912,93602329931428,93602706077807),(1610074112,93602751606604,93603127753296)]
theorem point_links_checked12253 : (cuts12253.take 3).map (fun c => (1609957377-1+2*2^9*c.k,93601787608184+c.lower,93602163754153+c.upper)) = pointBounds12253 := by
 decide +kernel
def cuts12254 : List PrefixCut := [⟨36,304706885,304707115⟩,
⟨86,730201147,730201700⟩,
⟨128,1082613242,1082614065⟩]
theorem checked12254 : checkPrefixCuts (2^48) 1610088449 9 Manual.Count131072.C012254.packed 128 cuts12254 = true := by
 decide +kernel
def pointBounds12254 : List (Nat × Nat × Nat) := [(1610125312,93603169771843,93603545918851),(1610176512,93603595266105,93603971413436)]
theorem point_links_checked12254 : (cuts12254.take 2).map (fun c => (1610088449-1+2*2^9*c.k,93602865064958+c.lower,93603241211736+c.upper)) = pointBounds12254 := by
 decide +kernel
def cuts12255 : List PrefixCut := [⟨8,66950253,66950305⟩,
⟨58,485425361,485425732⟩,
⟨108,904586289,904586979⟩,
⟨128,1069240535,1069241350⟩]
theorem checked12255 : checkPrefixCuts (2^48) 1610219521 9 Manual.Count131072.C012255.packed 128 cuts12255 = true := by
 decide +kernel
def pointBounds12255 : List (Nat × Nat × Nat) := [(1610227712,93604014628453,93604390776106),(1610278912,93604433103561,93604809251533),(1610330112,93604852264489,93605228412780)]
theorem point_links_checked12255 : (cuts12255.take 3).map (fun c => (1610219521-1+2*2^9*c.k,93603947678200+c.lower,93604323825801+c.upper)) = pointBounds12255 := by
 decide +kernel
def cuts12256 : List PrefixCut := [⟨30,259212644,259212839⟩,
⟨80,682017397,682017911⟩,
⟨128,1076669516,1076670327⟩]
theorem checked12256 : checkPrefixCuts (2^48) 1610350593 9 Manual.Count131072.C012256.packed 128 cuts12256 = true := by
 decide +kernel
def pointBounds12256 : List (Nat × Nat × Nat) := [(1610381312,93605276131379,93605652279990),(1610432512,93605698936132,93606075085062)]
theorem point_links_checked12256 : (cuts12256.take 2).map (fun c => (1610350593-1+2*2^9*c.k,93605016918735+c.lower,93605393067151+c.upper)) = pointBounds12256 := by
 decide +kernel
def cuts12257 : List PrefixCut := [⟨2,17477672,17477685⟩,
⟨52,448994325,448994662⟩,
⟨102,865991478,865992131⟩,
⟨128,1082524143,1082524959⟩]
theorem checked12257 : checkPrefixCuts (2^48) 1610481665 9 Manual.Count131072.C012257.packed 128 cuts12257 = true := by
 decide +kernel
def pointBounds12257 : List (Nat × Nat × Nat) := [(1610483712,93606111065923,93606487215163),(1610534912,93606542582576,93606918732140),(1610586112,93606959579729,93607335729609)]
theorem point_links_checked12257 : (cuts12257.take 3).map (fun c => (1610481665-1+2*2^9*c.k,93606093588251+c.lower,93606469737478+c.upper)) = pointBounds12257 := by
 decide +kernel
def cuts12258 : List PrefixCut := [⟨24,196606443,196606592⟩,
⟨74,609208078,609208544⟩,
⟨124,1025990610,1025991390⟩,
⟨128,1063037315,1063038123⟩]
theorem checked12258 : checkPrefixCuts (2^48) 1610612737 9 Manual.Count131072.C012258.packed 128 cuts12258 = true := by
 decide +kernel
def pointBounds12258 : List (Nat × Nat × Nat) := [(1610637312,93607372718837,93607748869029),(1610688512,93607785320472,93608161470981),(1610739712,93608202103004,93608578253827)]
theorem point_links_checked12258 : (cuts12258.take 3).map (fun c => (1610612737-1+2*2^9*c.k,93607176112394+c.lower,93607552262437+c.upper)) = pointBounds12258 := by
 decide +kernel
def cuts12259 : List PrefixCut := [⟨46,393003360,393003657⟩,
⟨96,820593334,820593956⟩,
⟨128,1087939338,1087940161⟩]
theorem checked12259 : checkPrefixCuts (2^48) 1610743809 9 Manual.Count131072.C012259.packed 128 cuts12259 = true := by
 decide +kernel
def pointBounds12259 : List (Nat × Nat × Nat) := [(1610790912,93608632153069,93609008304217),(1610842112,93609059743043,93609435894516)]
theorem point_links_checked12259 : (cuts12259.take 2).map (fun c => (1610743809-1+2*2^9*c.k,93608239149709+c.lower,93608615300560+c.upper)) = pointBounds12259 := by
 decide +kernel
def cuts12260 : List PrefixCut := [⟨18,151668382,151668495⟩,
⟨68,568398053,568398478⟩,
⟨118,993501179,993501921⟩,
⟨128,1081560304,1081561110⟩]
theorem checked12260 : checkPrefixCuts (2^48) 1610874881 9 Manual.Count131072.C012260.packed 128 cuts12260 = true := by
 decide +kernel
def pointBounds12260 : List (Nat × Nat × Nat) := [(1610893312,93609478757429,93609854909216),(1610944512,93609895487100,93610271639199),(1610995712,93610320590226,93610696742642)]
theorem point_links_checked12260 : (cuts12260.take 3).map (fun c => (1610874881-1+2*2^9*c.k,93609327089047+c.lower,93609703240721+c.upper)) = pointBounds12260 := by
 decide +kernel
def cuts12261 : List PrefixCut := [⟨40,330041772,330042019⟩,
⟨90,749352266,749352829⟩,
⟨128,1064001096,1064001894⟩]
theorem checked12261 : checkPrefixCuts (2^48) 1611005953 9 Manual.Count131072.C012261.packed 128 cuts12261 = true := by
 decide +kernel
def pointBounds12261 : List (Nat × Nat × Nat) := [(1611046912,93610738691123,93611114843850),(1611098112,93611158001617,93611534154660)]
theorem point_links_checked12261 : (cuts12261.take 2).map (fun c => (1611005953-1+2*2^9*c.k,93610408649351+c.lower,93610784801831+c.upper)) = pointBounds12261 := by
 decide +kernel
def cuts12262 : List PrefixCut := [⟨12,102551870,102551947⟩,
⟨62,520962257,520962651⟩,
⟨112,939184621,939185334⟩,
⟨128,1073697784,1073698597⟩]
theorem checked12262 : checkPrefixCuts (2^48) 1611137025 9 Manual.Count131072.C012262.packed 128 cuts12262 = true := by
 decide +kernel
def pointBounds12262 : List (Nat × Nat × Nat) := [(1611149312,93611575202317,93611951355672),(1611200512,93611993612704,93612369766376),(1611251712,93612411835068,93612787989059)]
theorem point_links_checked12262 : (cuts12262.take 3).map (fun c => (1611137025-1+2*2^9*c.k,93611472650447+c.lower,93611848803725+c.upper)) = pointBounds12262 := by
 decide +kernel
def cuts12263 : List PrefixCut := [⟨34,289984762,289984981⟩,
⟨84,713071728,713072267⟩,
⟨128,1087585106,1087585926⟩]
theorem checked12263 : checkPrefixCuts (2^48) 1611268097 9 Manual.Count131072.C012263.packed 128 cuts12263 = true := by
 decide +kernel
def pointBounds12263 : List (Nat × Nat × Nat) := [(1611302912,93612836332993,93613212487303),(1611354112,93613259419959,93613635574589)]
theorem point_links_checked12263 : (cuts12263.take 2).map (fun c => (1611268097-1+2*2^9*c.k,93612546348231+c.lower,93612922502322+c.upper)) = pointBounds12263 := by
 decide +kernel
def cuts12264 : List PrefixCut := [⟨6,50132297,50132334⟩,
⟨56,471795114,471795470⟩,
⟨106,897461736,897462408⟩,
⟨128,1079461979,1079462788⟩]
theorem checked12264 : checkPrefixCuts (2^48) 1611399169 9 Manual.Count131072.C012264.packed 128 cuts12264 = true := by
 decide +kernel
def pointBounds12264 : List (Nat × Nat × Nat) := [(1611405312,93613684065634,93614060220582),(1611456512,93614105728451,93614481883718),(1611507712,93614531395073,93614907550656)]
theorem point_links_checked12264 : (cuts12264.take 3).map (fun c => (1611399169-1+2*2^9*c.k,93613633933337+c.lower,93614010088248+c.upper)) = pointBounds12264 := by
 decide +kernel
def cuts12265 : List PrefixCut := [⟨28,234221150,234221326⟩,
⟨78,663877845,663878348⟩,
⟨128,1074833273,1074834087⟩]
theorem checked12265 : checkPrefixCuts (2^48) 1611530241 9 Manual.Count131072.C012265.packed 128 cuts12265 = true := by
 decide +kernel
def pointBounds12265 : List (Nat × Nat × Nat) := [(1611558912,93614947616466,93615323772362),(1611610112,93615377273161,93615753429384),(1611661312,93615788228589,93616164385123)]
theorem point_links_checked12265 : (cuts12265.take 3).map (fun c => (1611530241-1+2*2^9*c.k,93614713395316+c.lower,93615089551036+c.upper)) = pointBounds12265 := by
 decide +kernel
def cuts12266 : List PrefixCut := [⟨50,421071749,421072066⟩,
⟨100,851036924,851037572⟩,
⟨128,1089240782,1089241609⟩]
theorem checked12266 : checkPrefixCuts (2^48) 1611661313 9 Manual.Count131072.C012266.packed 128 cuts12266 = true := by
 decide +kernel
def pointBounds12266 : List (Nat × Nat × Nat) := [(1611712512,93616209300338,93616585457189),(1611763712,93616639265513,93617015422695)]
theorem point_links_checked12266 : (cuts12266.take 2).map (fun c => (1611661313-1+2*2^9*c.k,93615788228589+c.lower,93616164385123+c.upper)) = pointBounds12266 := by
 decide +kernel
def cuts12267 : List PrefixCut := [⟨22,185460739,185460880⟩,
⟨72,603872953,603873409⟩,
⟨122,1026288305,1026289077⟩,
⟨128,1076055240,1076056048⟩]
theorem checked12267 : checkPrefixCuts (2^48) 1611792385 9 Manual.Count131072.C012267.packed 128 cuts12267 = true := by
 decide +kernel
def pointBounds12267 : List (Nat × Nat × Nat) := [(1611814912,93617062930110,93617439087612),(1611866112,93617481342324,93617857500141),(1611917312,93617903757676,93618279915809)]
theorem point_links_checked12267 : (cuts12267.take 3).map (fun c => (1611792385-1+2*2^9*c.k,93616877469371+c.lower,93617253626732+c.upper)) = pointBounds12267 := by
 decide +kernel
def cuts12268 : List PrefixCut := [⟨44,368793346,368793625⟩,
⟨94,793800948,793801546⟩,
⟨128,1072475559,1072476371⟩]
theorem checked12268 : checkPrefixCuts (2^48) 1611923457 9 Manual.Count131072.C012268.packed 128 cuts12268 = true := by
 decide +kernel
def pointBounds12268 : List (Nat × Nat × Nat) := [(1611968512,93618322317957,93618698476405),(1612019712,93618747325559,93619123484326)]
theorem point_links_checked12268 : (cuts12268.take 2).map (fun c => (1611923457-1+2*2^9*c.k,93617953524611+c.lower,93618329682780+c.upper)) = pointBounds12268 := by
 decide +kernel
def cuts12269 : List PrefixCut := [⟨16,132700115,132700214⟩,
⟨66,570775971,570776398⟩,
⟨116,991378287,991379036⟩,
⟨128,1090896169,1090896994⟩]
theorem checked12269 : checkPrefixCuts (2^48) 1612054529 9 Manual.Count131072.C012269.packed 128 cuts12269 = true := by
 decide +kernel
def pointBounds12269 : List (Nat × Nat × Nat) := [(1612070912,93619158700285,93619534859365),(1612122112,93619596776141,93619972935549),(1612173312,93620017378457,93620393538187)]
theorem point_links_checked12269 : (cuts12269.take 3).map (fun c => (1612054529-1+2*2^9*c.k,93619026000170+c.lower,93619402159151+c.upper)) = pointBounds12269 := by
 decide +kernel
def cuts12270 : List PrefixCut := [⟨38,315484108,315484346⟩,
⟨88,737456360,737456918⟩,
⟨128,1080157177,1080157991⟩]
theorem checked12270 : checkPrefixCuts (2^48) 1612185601 9 Manual.Count131072.C012270.packed 128 cuts12270 = true := by
 decide +kernel
def pointBounds12270 : List (Nat × Nat × Nat) := [(1612224512,93620432380447,93620808540491),(1612275712,93620854352699,93621230513063)]
theorem point_links_checked12270 : (cuts12270.take 2).map (fun c => (1612185601-1+2*2^9*c.k,93620116896339+c.lower,93620493056145+c.upper)) = pointBounds12270 := by
 decide +kernel
def cuts12271 : List PrefixCut := [⟨10,88510718,88510787⟩,
⟨60,510456102,510456491⟩,
⟨110,940069076,940069791⟩,
⟨128,1087227132,1087227959⟩]
theorem checked12271 : checkPrefixCuts (2^48) 1612316673 9 Manual.Count131072.C012271.packed 128 cuts12271 = true := by
 decide +kernel
def pointBounds12271 : List (Nat × Nat × Nat) := [(1612326912,93621285564234,93621661724923),(1612378112,93621707509618,93622083670627),(1612429312,93622137122592,93622513283927)]
theorem point_links_checked12271 : (cuts12271.take 3).map (fun c => (1612316673-1+2*2^9*c.k,93621197053516+c.lower,93621573214136+c.upper)) = pointBounds12271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000070
