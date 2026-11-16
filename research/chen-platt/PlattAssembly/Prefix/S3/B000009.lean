import PlattAssemblyKernel
import PlattCertificates.Count131072.C020288
import PlattCertificates.Count131072.C020289
import PlattCertificates.Count131072.C020290
import PlattCertificates.Count131072.C020291
import PlattCertificates.Count131072.C020292
import PlattCertificates.Count131072.C020293
import PlattCertificates.Count131072.C020294
import PlattCertificates.Count131072.C020295
import PlattCertificates.Count131072.C020296
import PlattCertificates.Count131072.C020297
import PlattCertificates.Count131072.C020298
import PlattCertificates.Count131072.C020299
import PlattCertificates.Count131072.C020300
import PlattCertificates.Count131072.C020301
import PlattCertificates.Count131072.C020302
import PlattCertificates.Count131072.C020303
import PlattCertificates.Count131072.C020304
import PlattCertificates.Count131072.C020305
import PlattCertificates.Count131072.C020306
import PlattCertificates.Count131072.C020307
import PlattCertificates.Count131072.C020308
import PlattCertificates.Count131072.C020309
import PlattCertificates.Count131072.C020310
import PlattCertificates.Count131072.C020311
import PlattCertificates.Count131072.C020312
import PlattCertificates.Count131072.C020313
import PlattCertificates.Count131072.C020314
import PlattCertificates.Count131072.C020315
import PlattCertificates.Count131072.C020316
import PlattCertificates.Count131072.C020317
import PlattCertificates.Count131072.C020318
import PlattCertificates.Count131072.C020319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20288 : List PrefixCut := [⟨28,140360374,140360459⟩,
⟨110,550440764,550441092⟩,
⟨128,642601378,642601762⟩]
theorem checked20288 : checkPrefixCuts (2^48) 2663120897 9 Manual.Count131072.C020288.packed 128 cuts20288 = true := by
 decide +kernel
def pointBounds20288 : List (Nat × Nat × Nat) := [(2663149568,100206157916166,100206538394623),(2663233536,100206567996556,100206948475256)]
theorem point_links_checked20288 : (cuts20288.take 2).map (fun c => (2663120897-1+2*2^9*c.k,100206017555792+c.lower,100206398034164+c.upper)) = pointBounds20288 := by
 decide +kernel
def cuts20289 : List PrefixCut := [⟨64,311776998,311777182⟩,
⟨128,627139597,627139968⟩]
theorem checked20289 : checkPrefixCuts (2^48) 2663251969 9 Manual.Count131072.C020289.packed 128 cuts20289 = true := by
 decide +kernel
def pointBounds20289 : List (Nat × Nat × Nat) := [(2663317504,100206971934168,100207352413108)]
theorem point_links_checked20289 : (cuts20289.take 1).map (fun c => (2663251969-1+2*2^9*c.k,100206660157170+c.lower,100207040635926+c.upper)) = pointBounds20289 := by
 decide +kernel
def cuts20290 : List PrefixCut := [⟨18,90358830,90358883⟩,
⟨100,501245887,501246179⟩,
⟨128,642115432,642115807⟩]
theorem checked20290 : checkPrefixCuts (2^48) 2663383041 9 Manual.Count131072.C020290.packed 128 cuts20290 = true := by
 decide +kernel
def pointBounds20290 : List (Nat × Nat × Nat) := [(2663401472,100207377655597,100207758134777),(2663485440,100207788542654,100208169022073)]
theorem point_links_checked20290 : (cuts20290.take 2).map (fun c => (2663383041-1+2*2^9*c.k,100207287296767+c.lower,100207667775894+c.upper)) = pointBounds20290 := by
 decide +kernel
def cuts20291 : List PrefixCut := [⟨54,271061295,271061456⟩,
⟨128,639970369,639970747⟩]
theorem checked20291 : checkPrefixCuts (2^48) 2663514113 9 Manual.Count131072.C020291.packed 128 cuts20291 = true := by
 decide +kernel
def pointBounds20291 : List (Nat × Nat × Nat) := [(2663569408,100208200473494,100208580953157)]
theorem point_links_checked20291 : (cuts20291.take 1).map (fun c => (2663514113-1+2*2^9*c.k,100207929412199+c.lower,100208309891701+c.upper)) = pointBounds20291 := by
 decide +kernel
def cuts20292 : List PrefixCut := [⟨8,38993210,38993231⟩,
⟨90,450158386,450158649⟩,
⟨128,633704384,633704755⟩]
theorem checked20292 : checkPrefixCuts (2^48) 2663645185 9 Manual.Count131072.C020292.packed 128 cuts20292 = true := by
 decide +kernel
def pointBounds20292 : List (Nat × Nat × Nat) := [(2663653376,100208608375778,100208988855679),(2663737344,100209019540954,100209400021097)]
theorem point_links_checked20292 : (cuts20292.take 2).map (fun c => (2663645185-1+2*2^9*c.k,100208569382568+c.lower,100208949862448+c.upper)) = pointBounds20292 := by
 decide +kernel
def cuts20293 : List PrefixCut := [⟨44,221371797,221371926⟩,
⟨126,624269199,624269563⟩,
⟨128,635152433,635152803⟩]
theorem checked20293 : checkPrefixCuts (2^48) 2663776257 9 Manual.Count131072.C020293.packed 128 cuts20293 = true := by
 decide +kernel
def pointBounds20293 : List (Nat × Nat × Nat) := [(2663821312,100209424458749,100209804939129),(2663905280,100209827356151,100210207836766)]
theorem point_links_checked20293 : (cuts20293.take 2).map (fun c => (2663776257-1+2*2^9*c.k,100209203086952+c.lower,100209583567203+c.upper)) = pointBounds20293 := by
 decide +kernel
def cuts20294 : List PrefixCut := [⟨80,394114791,394115023⟩,
⟨128,631951365,631951739⟩]
theorem checked20294 : checkPrefixCuts (2^48) 2663907329 9 Manual.Count131072.C020294.packed 128 cuts20294 = true := by
 decide +kernel
def pointBounds20294 : List (Nat × Nat × Nat) := [(2663989248,100210232354176,100210612835029)]
theorem point_links_checked20294 : (cuts20294.take 1).map (fun c => (2663907329-1+2*2^9*c.k,100209838239385+c.lower,100210218720006+c.upper)) = pointBounds20294 := by
 decide +kernel
def cuts20295 : List PrefixCut := [⟨34,172008819,172008919⟩,
⟨116,578143446,578143778⟩,
⟨128,637520023,637520390⟩]
theorem checked20295 : checkPrefixCuts (2^48) 2664038401 9 Manual.Count131072.C020295.packed 128 cuts20295 = true := by
 decide +kernel
def pointBounds20295 : List (Nat × Nat × Nat) := [(2664073216,100210642199569,100211022680664),(2664157184,100211048334196,100211428815523)]
theorem point_links_checked20295 : (cuts20295.take 2).map (fun c => (2664038401-1+2*2^9*c.k,100210470190750+c.lower,100210850671745+c.upper)) = pointBounds20295 := by
 decide +kernel
def cuts20296 : List PrefixCut := [⟨70,344949241,344949445⟩,
⟨128,628508462,628508831⟩]
theorem checked20296 : checkPrefixCuts (2^48) 2664169473 9 Manual.Count131072.C020296.packed 128 cuts20296 = true := by
 decide +kernel
def pointBounds20296 : List (Nat × Nat × Nat) := [(2664241152,100211452660014,100211833141580)]
theorem point_links_checked20296 : (cuts20296.take 1).map (fun c => (2664169473-1+2*2^9*c.k,100211107710773+c.lower,100211488192135+c.upper)) = pointBounds20296 := by
 decide +kernel
def cuts20297 : List PrefixCut := [⟨24,119697303,119697376⟩,
⟨106,535829788,535830103⟩,
⟨128,652775565,652775946⟩]
theorem checked20297 : checkPrefixCuts (2^48) 2664300545 9 Manual.Count131072.C020297.packed 128 cuts20297 = true := by
 decide +kernel
def pointBounds20297 : List (Nat × Nat × Nat) := [(2664325120,100211855916538,100212236398342),(2664409088,100212272049023,100212652531069)]
theorem point_links_checked20297 : (cuts20297.take 2).map (fun c => (2664300545-1+2*2^9*c.k,100211736219235+c.lower,100212116700966+c.upper)) = pointBounds20297 := by
 decide +kernel
def cuts20298 : List PrefixCut := [⟨60,301814690,301814866⟩,
⟨128,641651514,641651888⟩]
theorem checked20298 : checkPrefixCuts (2^48) 2664431617 9 Manual.Count131072.C020298.packed 128 cuts20298 = true := by
 decide +kernel
def pointBounds20298 : List (Nat × Nat × Nat) := [(2664493056,100212690809490,100213071291778)]
theorem point_links_checked20298 : (cuts20298.take 1).map (fun c => (2664431617-1+2*2^9*c.k,100212388994800+c.lower,100212769476912+c.upper)) = pointBounds20298 := by
 decide +kernel
def cuts20299 : List PrefixCut := [⟨14,66867678,66867717⟩,
⟨96,474721252,474721533⟩,
⟨128,634436644,634437021⟩]
theorem checked20299 : checkPrefixCuts (2^48) 2664562689 9 Manual.Count131072.C020299.packed 128 cuts20299 = true := by
 decide +kernel
def pointBounds20299 : List (Nat × Nat × Nat) := [(2664577024,100213097513992,100213477996517),(2664660992,100213505367566,100213885850333)]
theorem point_links_checked20299 : (cuts20299.take 2).map (fun c => (2664562689-1+2*2^9*c.k,100213030646314+c.lower,100213411128800+c.upper)) = pointBounds20299 := by
 decide +kernel
def cuts20300 : List PrefixCut := [⟨50,253195632,253195779⟩,
⟨128,640637776,640638150⟩]
theorem checked20300 : checkPrefixCuts (2^48) 2664693761 9 Manual.Count131072.C020300.packed 128 cuts20300 = true := by
 decide +kernel
def pointBounds20300 : List (Nat × Nat × Nat) := [(2664744960,100213918278590,100214298761600)]
theorem point_links_checked20300 : (cuts20300.take 1).map (fun c => (2664693761-1+2*2^9*c.k,100213665082958+c.lower,100214045565821+c.upper)) = pointBounds20300 := by
 decide +kernel
def cuts20301 : List PrefixCut := [⟨4,19540802,19540814⟩,
⟨86,435383357,435383618⟩,
⟨128,651590961,651591343⟩]
theorem checked20301 : checkPrefixCuts (2^48) 2664824833 9 Manual.Count131072.C020301.packed 128 cuts20301 = true := by
 decide +kernel
def pointBounds20301 : List (Nat × Nat × Nat) := [(2664828928,100214325261536,100214705744785),(2664912896,100214741104091,100215121587589)]
theorem point_links_checked20301 : (cuts20301.take 2).map (fun c => (2664824833-1+2*2^9*c.k,100214305720734+c.lower,100214686203971+c.upper)) = pointBounds20301 := by
 decide +kernel
def cuts20302 : List PrefixCut := [⟨40,198037570,198037685⟩,
⟨122,605721371,605721726⟩,
⟨128,634976940,634977312⟩]
theorem checked20302 : checkPrefixCuts (2^48) 2664955905 9 Manual.Count131072.C020302.packed 128 cuts20302 = true := by
 decide +kernel
def pointBounds20302 : List (Nat × Nat × Nat) := [(2664996864,100215155349265,100215535832999),(2665080832,100215563033066,100215943517040)]
theorem point_links_checked20302 : (cuts20302.take 2).map (fun c => (2664955905-1+2*2^9*c.k,100214957311695+c.lower,100215337795314+c.upper)) = pointBounds20302 := by
 decide +kernel
def cuts20303 : List PrefixCut := [⟨76,379577073,379577300⟩,
⟨128,636846725,636847100⟩]
theorem checked20303 : checkPrefixCuts (2^48) 2665086977 9 Manual.Count131072.C020303.packed 128 cuts20303 = true := by
 decide +kernel
def pointBounds20303 : List (Nat × Nat × Nat) := [(2665164800,100215971865708,100216352349926)]
theorem point_links_checked20303 : (cuts20303.take 1).map (fun c => (2665086977-1+2*2^9*c.k,100215592288635+c.lower,100215972772626+c.upper)) = pointBounds20303 := by
 decide +kernel
def cuts20304 : List PrefixCut := [⟨30,150177203,150177293⟩,
⟨112,562363502,562363830⟩,
⟨128,637343476,637343847⟩]
theorem checked20304 : checkPrefixCuts (2^48) 2665218049 9 Manual.Count131072.C020304.packed 128 cuts20304 = true := by
 decide +kernel
def pointBounds20304 : List (Nat × Nat × Nat) := [(2665248768,100216379312563,100216759797019),(2665332736,100216791498862,100217171983556)]
theorem point_links_checked20304 : (cuts20304.take 2).map (fun c => (2665218049-1+2*2^9*c.k,100216229135360+c.lower,100216609619726+c.upper)) = pointBounds20304 := by
 decide +kernel
def cuts20305 : List PrefixCut := [⟨66,327372132,327372328⟩,
⟨128,634038380,634038760⟩]
theorem checked20305 : checkPrefixCuts (2^48) 2665349121 9 Manual.Count131072.C020305.packed 128 cuts20305 = true := by
 decide +kernel
def pointBounds20305 : List (Nat × Nat × Nat) := [(2665416704,100217193850968,100217574335901)]
theorem point_links_checked20305 : (cuts20305.take 1).map (fun c => (2665349121-1+2*2^9*c.k,100216866478836+c.lower,100217246963573+c.upper)) = pointBounds20305 := by
 decide +kernel
def cuts20306 : List PrefixCut := [⟨20,99686089,99686145⟩,
⟨102,507503926,507504221⟩,
⟨128,640237345,640237715⟩]
theorem checked20306 : checkPrefixCuts (2^48) 2665480193 9 Manual.Count131072.C020306.packed 128 cuts20306 = true := by
 decide +kernel
def pointBounds20306 : List (Nat × Nat × Nat) := [(2665500672,100217600203305,100217980688478),(2665584640,100218008021142,100218388506554)]
theorem point_links_checked20306 : (cuts20306.take 2).map (fun c => (2665480193-1+2*2^9*c.k,100217500517216+c.lower,100217881002333+c.upper)) = pointBounds20306 := by
 decide +kernel
def cuts20307 : List PrefixCut := [⟨56,275810858,275811022⟩,
⟨128,635771051,635771427⟩]
theorem checked20307 : checkPrefixCuts (2^48) 2665611265 9 Manual.Count131072.C020307.packed 128 cuts20307 = true := by
 decide +kernel
def pointBounds20307 : List (Nat × Nat × Nat) := [(2665668608,100218416565419,100218797051070)]
theorem point_links_checked20307 : (cuts20307.take 1).map (fun c => (2665611265-1+2*2^9*c.k,100218140754561+c.lower,100218521240048+c.upper)) = pointBounds20307 := by
 decide +kernel
def cuts20308 : List PrefixCut := [⟨10,49732648,49732674⟩,
⟨92,459518148,459518407⟩,
⟨128,636373405,636373769⟩]
theorem checked20308 : checkPrefixCuts (2^48) 2665742337 9 Manual.Count131072.C020308.packed 128 cuts20308 = true := by
 decide +kernel
def pointBounds20308 : List (Nat × Nat × Nat) := [(2665752576,100218826258260,100219206744149),(2665836544,100219236043760,100219616529882)]
theorem point_links_checked20308 : (cuts20308.take 2).map (fun c => (2665742337-1+2*2^9*c.k,100218776525612+c.lower,100219157011475+c.upper)) = pointBounds20308 := by
 decide +kernel
def cuts20309 : List PrefixCut := [⟨46,227954921,227955055⟩,
⟨128,638348110,638348486⟩]
theorem checked20309 : checkPrefixCuts (2^48) 2665873409 9 Manual.Count131072.C020309.packed 128 cuts20309 = true := by
 decide +kernel
def pointBounds20309 : List (Nat × Nat × Nat) := [(2665920512,100219640853938,100220021340299),(2666004480,100220051247127,100220431733730)]
theorem point_links_checked20309 : (cuts20309.take 2).map (fun c => (2665873409-1+2*2^9*c.k,100219412899017+c.lower,100219793385244+c.upper)) = pointBounds20309 := by
 decide +kernel
def cuts20310 : List PrefixCut := [⟨82,405101381,405101624⟩,
⟨128,636944181,636944559⟩]
theorem checked20310 : checkPrefixCuts (2^48) 2666004481 9 Manual.Count131072.C020310.packed 128 cuts20310 = true := by
 decide +kernel
def pointBounds20310 : List (Nat × Nat × Nat) := [(2666088448,100220456348508,100220836835354)]
theorem point_links_checked20310 : (cuts20310.take 1).map (fun c => (2666004481-1+2*2^9*c.k,100220051247127+c.lower,100220431733730+c.upper)) = pointBounds20310 := by
 decide +kernel
def cuts20311 : List PrefixCut := [⟨36,180530469,180530575⟩,
⟨118,581277913,581278257⟩,
⟨128,633956906,633957279⟩]
theorem checked20311 : checkPrefixCuts (2^48) 2666135553 9 Manual.Count131072.C020311.packed 128 cuts20311 = true := by
 decide +kernel
def pointBounds20311 : List (Nat × Nat × Nat) := [(2666172416,100220868721777,100221249208864),(2666256384,100221269469221,100221649956546)]
theorem point_links_checked20311 : (cuts20311.take 2).map (fun c => (2666135553-1+2*2^9*c.k,100220688191308+c.lower,100221068678289+c.upper)) = pointBounds20311 := by
 decide +kernel
def cuts20312 : List PrefixCut := [⟨72,356079055,356079262⟩,
⟨128,636564885,636565252⟩]
theorem checked20312 : checkPrefixCuts (2^48) 2666266625 9 Manual.Count131072.C020312.packed 128 cuts20312 = true := by
 decide +kernel
def pointBounds20312 : List (Nat × Nat × Nat) := [(2666340352,100221678227269,100222058714830)]
theorem point_links_checked20312 : (cuts20312.take 1).map (fun c => (2666266625-1+2*2^9*c.k,100221322148214+c.lower,100221702635568+c.upper)) = pointBounds20312 := by
 decide +kernel
def cuts20313 : List PrefixCut := [⟨26,129631620,129631693⟩,
⟨108,536674887,536675200⟩,
⟨128,636533649,636534022⟩]
theorem checked20313 : checkPrefixCuts (2^48) 2666397697 9 Manual.Count131072.C020313.packed 128 cuts20313 = true := by
 decide +kernel
def pointBounds20313 : List (Nat × Nat × Nat) := [(2666424320,100222088344719,100222468832513),(2666508288,100222495387986,100222875876020)]
theorem point_links_checked20313 : (cuts20313.take 2).map (fun c => (2666397697-1+2*2^9*c.k,100221958713099+c.lower,100222339200820+c.upper)) = pointBounds20313 := by
 decide +kernel
def cuts20314 : List PrefixCut := [⟨62,304532803,304532983⟩,
⟨128,635657845,635658219⟩]
theorem checked20314 : checkPrefixCuts (2^48) 2666528769 9 Manual.Count131072.C020314.packed 128 cuts20314 = true := by
 decide +kernel
def pointBounds20314 : List (Nat × Nat × Nat) := [(2666592256,100222899779551,100223280267825)]
theorem point_links_checked20314 : (cuts20314.take 1).map (fun c => (2666528769-1+2*2^9*c.k,100222595246748+c.lower,100222975734842+c.upper)) = pointBounds20314 := by
 decide +kernel
def cuts20315 : List PrefixCut := [⟨16,77687024,77687070⟩,
⟨98,492713724,492714012⟩,
⟨128,645442800,645443180⟩]
theorem checked20315 : checkPrefixCuts (2^48) 2666659841 9 Manual.Count131072.C020315.packed 128 cuts20315 = true := by
 decide +kernel
def pointBounds20315 : List (Nat × Nat × Nat) := [(2666676224,100223308591617,100223689080131),(2666760192,100223723618317,100224104107073)]
theorem point_links_checked20315 : (cuts20315.take 2).map (fun c => (2666659841-1+2*2^9*c.k,100223230904593+c.lower,100223611393061+c.upper)) = pointBounds20315 := by
 decide +kernel
def cuts20316 : List PrefixCut := [⟨52,253629723,253629872⟩,
⟨128,628734866,628735232⟩]
theorem checked20316 : checkPrefixCuts (2^48) 2666790913 9 Manual.Count131072.C020316.packed 128 cuts20316 = true := by
 decide +kernel
def pointBounds20316 : List (Nat × Nat × Nat) := [(2666844160,100224129977116,100224510466113)]
theorem point_links_checked20316 : (cuts20316.take 1).map (fun c => (2666790913-1+2*2^9*c.k,100223876347393+c.lower,100224256836241+c.upper)) = pointBounds20316 := by
 decide +kernel
def cuts20317 : List PrefixCut := [⟨6,30501887,30501905⟩,
⟨88,439579136,439579395⟩,
⟨128,639996947,639997320⟩]
theorem checked20317 : checkPrefixCuts (2^48) 2666921985 9 Manual.Count131072.C020317.packed 128 cuts20317 = true := by
 decide +kernel
def pointBounds20317 : List (Nat × Nat × Nat) := [(2666928128,100224535584146,100224916073378),(2667012096,100224944661395,100225325150868)]
theorem point_links_checked20317 : (cuts20317.take 2).map (fun c => (2666921985-1+2*2^9*c.k,100224505082259+c.lower,100224885571473+c.upper)) = pointBounds20317 := by
 decide +kernel
def cuts20318 : List PrefixCut := [⟨42,209701922,209702042⟩,
⟨124,618647798,618648160⟩,
⟨128,639437739,639438111⟩]
theorem checked20318 : checkPrefixCuts (2^48) 2667053057 9 Manual.Count131072.C020318.packed 128 cuts20318 = true := by
 decide +kernel
def pointBounds20318 : List (Nat × Nat × Nat) := [(2667096064,100225354781128,100225735270835),(2667180032,100225763727004,100226144216953)]
theorem point_links_checked20318 : (cuts20318.take 2).map (fun c => (2667053057-1+2*2^9*c.k,100225145079206+c.lower,100225525568793+c.upper)) = pointBounds20318 := by
 decide +kernel
def cuts20319 : List PrefixCut := [⟨78,387298884,387299106⟩,
⟨128,640250549,640250919⟩]
theorem checked20319 : checkPrefixCuts (2^48) 2667184129 9 Manual.Count131072.C020319.packed 128 cuts20319 = true := by
 decide +kernel
def pointBounds20319 : List (Nat × Nat × Nat) := [(2667264000,100226171815829,100226552306010)]
theorem point_links_checked20319 : (cuts20319.take 1).map (fun c => (2667184129-1+2*2^9*c.k,100225784516945+c.lower,100226165006904+c.upper)) = pointBounds20319 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000009
