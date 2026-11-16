import PlattAssemblyKernel
import PlattCertificates.Count131072.C022272
import PlattCertificates.Count131072.C022273
import PlattCertificates.Count131072.C022274
import PlattCertificates.Count131072.C022275
import PlattCertificates.Count131072.C022276
import PlattCertificates.Count131072.C022277
import PlattCertificates.Count131072.C022278
import PlattCertificates.Count131072.C022279
import PlattCertificates.Count131072.C022280
import PlattCertificates.Count131072.C022281
import PlattCertificates.Count131072.C022282
import PlattCertificates.Count131072.C022283
import PlattCertificates.Count131072.C022284
import PlattCertificates.Count131072.C022285
import PlattCertificates.Count131072.C022286
import PlattCertificates.Count131072.C022287
import PlattCertificates.Count131072.C022288
import PlattCertificates.Count131072.C022289
import PlattCertificates.Count131072.C022290
import PlattCertificates.Count131072.C022291
import PlattCertificates.Count131072.C022292
import PlattCertificates.Count131072.C022293
import PlattCertificates.Count131072.C022294
import PlattCertificates.Count131072.C022295
import PlattCertificates.Count131072.C022296
import PlattCertificates.Count131072.C022297
import PlattCertificates.Count131072.C022298
import PlattCertificates.Count131072.C022299
import PlattCertificates.Count131072.C022300
import PlattCertificates.Count131072.C022301
import PlattCertificates.Count131072.C022302
import PlattCertificates.Count131072.C022303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22272 : List PrefixCut := [⟨12,56330146,56330177⟩,
⟨102,460263067,460263333⟩,
⟨128,577348280,577348614⟩]
theorem checked22272 : checkPrefixCuts (2^48) 2923167745 9 Manual.Count131072.C022272.packed 128 cuts22272 = true := by
 decide +kernel
def pointBounds22272 : List (Nat × Nat × Nat) := [(2923180032,101411845603173,101412226778180),(2923272192,101412249536094,101412630711336)]
theorem point_links_checked22272 : (cuts22272.take 2).map (fun c => (2923167745-1+2*2^9*c.k,101411789273027+c.lower,101412170448003+c.upper)) = pointBounds22272 := by
 decide +kernel
def cuts22273 : List PrefixCut := [⟨64,290204943,290205107⟩,
⟨128,579440565,579440890⟩]
theorem checked22273 : checkPrefixCuts (2^48) 2923298817 9 Manual.Count131072.C022273.packed 128 cuts22273 = true := by
 decide +kernel
def pointBounds22273 : List (Nat × Nat × Nat) := [(2923364352,101412656826250,101413038001724)]
theorem point_links_checked22273 : (cuts22273.take 1).map (fun c => (2923298817-1+2*2^9*c.k,101412366621307+c.lower,101412747796617+c.upper)) = pointBounds22273 := by
 decide +kernel
def cuts22274 : List PrefixCut := [⟨26,115634651,115634723⟩,
⟨116,524247057,524247362⟩,
⟨128,577681518,577681854⟩]
theorem checked22274 : checkPrefixCuts (2^48) 2923429889 9 Manual.Count131072.C022274.packed 128 cuts22274 = true := by
 decide +kernel
def pointBounds22274 : List (Nat × Nat × Nat) := [(2923456512,101413061696523,101413442872230),(2923548672,101413470308929,101413851484869)]
theorem point_links_checked22274 : (cuts22274.take 2).map (fun c => (2923429889-1+2*2^9*c.k,101412946061872+c.lower,101413327237507+c.upper)) = pointBounds22274 := by
 decide +kernel
def cuts22275 : List PrefixCut := [⟨78,348810788,348810985⟩,
⟨128,573900873,573901194⟩]
theorem checked22275 : checkPrefixCuts (2^48) 2923560961 9 Manual.Count131072.C022275.packed 128 cuts22275 = true := by
 decide +kernel
def pointBounds22275 : List (Nat × Nat × Nat) := [(2923640832,101413872554178,101414253730346)]
theorem point_links_checked22275 : (cuts22275.take 1).map (fun c => (2923560961-1+2*2^9*c.k,101413523743390+c.lower,101413904919361+c.upper)) = pointBounds22275 := by
 decide +kernel
def cuts22276 : List PrefixCut := [⟨40,182148727,182148833⟩,
⟨128,586197870,586198203⟩]
theorem checked22276 : checkPrefixCuts (2^48) 2923692033 9 Manual.Count131072.C022276.packed 128 cuts22276 = true := by
 decide +kernel
def pointBounds22276 : List (Nat × Nat × Nat) := [(2923732992,101414279792990,101414660969388)]
theorem point_links_checked22276 : (cuts22276.take 1).map (fun c => (2923692033-1+2*2^9*c.k,101414097644263+c.lower,101414478820555+c.upper)) = pointBounds22276 := by
 decide +kernel
def cuts22277 : List PrefixCut := [⟨2,8086633,8086637⟩,
⟨92,413952087,413952320⟩,
⟨128,575293501,575293828⟩]
theorem checked22277 : checkPrefixCuts (2^48) 2923823105 9 Manual.Count131072.C022277.packed 128 cuts22277 = true := by
 decide +kernel
def pointBounds22277 : List (Nat × Nat × Nat) := [(2923825152,101414691928766,101415073105395),(2923917312,101415097794220,101415478971078)]
theorem point_links_checked22277 : (cuts22277.take 2).map (fun c => (2923823105-1+2*2^9*c.k,101414683842133+c.lower,101415065018758+c.upper)) = pointBounds22277 := by
 decide +kernel
def cuts22278 : List PrefixCut := [⟨54,245858877,245859014⟩,
⟨128,570935969,570936293⟩]
theorem checked22278 : checkPrefixCuts (2^48) 2923954177 9 Manual.Count131072.C022278.packed 128 cuts22278 = true := by
 decide +kernel
def pointBounds22278 : List (Nat × Nat × Nat) := [(2924009472,101415504994511,101415886171600)]
theorem point_links_checked22278 : (cuts22278.take 1).map (fun c => (2923954177-1+2*2^9*c.k,101415259135634+c.lower,101415640312586+c.upper)) = pointBounds22278 := by
 decide +kernel
def cuts22279 : List PrefixCut := [⟨16,72099169,72099212⟩,
⟨106,473305777,473306052⟩,
⟨128,571872831,571873163⟩]
theorem checked22279 : checkPrefixCuts (2^48) 2924085249 9 Manual.Count131072.C022279.packed 128 cuts22279 = true := by
 decide +kernel
def pointBounds22279 : List (Nat × Nat × Nat) := [(2924101632,101415902170772,101416283348091),(2924193792,101416303377380,101416684554931)]
theorem point_links_checked22279 : (cuts22279.take 2).map (fun c => (2924085249-1+2*2^9*c.k,101415830071603+c.lower,101416211248879+c.upper)) = pointBounds22279 := by
 decide +kernel
def cuts22280 : List PrefixCut := [⟨68,311193647,311193819⟩,
⟨128,580125117,580125447⟩]
theorem checked22280 : checkPrefixCuts (2^48) 2924216321 9 Manual.Count131072.C022280.packed 128 cuts22280 = true := by
 decide +kernel
def pointBounds22280 : List (Nat × Nat × Nat) := [(2924285952,101416713138081,101417094315861)]
theorem point_links_checked22280 : (cuts22280.take 1).map (fun c => (2924216321-1+2*2^9*c.k,101416401944434+c.lower,101416783122042+c.upper)) = pointBounds22280 := by
 decide +kernel
def cuts22281 : List PrefixCut := [⟨30,132923595,132923675⟩,
⟨120,537364794,537365107⟩,
⟨128,574612781,574613116⟩]
theorem checked22281 : checkPrefixCuts (2^48) 2924347393 9 Manual.Count131072.C022281.packed 128 cuts22281 = true := by
 decide +kernel
def pointBounds22281 : List (Nat × Nat × Nat) := [(2924378112,101417114993146,101417496171164),(2924470272,101417519434345,101417900612596)]
theorem point_links_checked22281 : (cuts22281.take 2).map (fun c => (2924347393-1+2*2^9*c.k,101416982069551+c.lower,101417363247489+c.upper)) = pointBounds22281 := by
 decide +kernel
def cuts22282 : List PrefixCut := [⟨82,368431667,368431878⟩,
⟨128,576126998,576127331⟩]
theorem checked22282 : checkPrefixCuts (2^48) 2924478465 9 Manual.Count131072.C022282.packed 128 cuts22282 = true := by
 decide +kernel
def pointBounds22282 : List (Nat × Nat × Nat) := [(2924562432,101417925113999,101418306292483)]
theorem point_links_checked22282 : (cuts22282.take 1).map (fun c => (2924478465-1+2*2^9*c.k,101417556682332+c.lower,101417937860605+c.upper)) = pointBounds22282 := by
 decide +kernel
def cuts22283 : List PrefixCut := [⟨44,200088871,200088984⟩,
⟨128,573021562,573021890⟩]
theorem checked22283 : checkPrefixCuts (2^48) 2924609537 9 Manual.Count131072.C022283.packed 128 cuts22283 = true := by
 decide +kernel
def pointBounds22283 : List (Nat × Nat × Nat) := [(2924654592,101418332898201,101418714076920)]
theorem point_links_checked22283 : (cuts22283.take 1).map (fun c => (2924609537-1+2*2^9*c.k,101418132809330+c.lower,101418513987936+c.upper)) = pointBounds22283 := by
 decide +kernel
def cuts22284 : List PrefixCut := [⟨6,28294315,28294332⟩,
⟨96,442211934,442212187⟩,
⟨128,586180244,586180579⟩]
theorem checked22284 : checkPrefixCuts (2^48) 2924740609 9 Manual.Count131072.C022284.packed 128 cuts22284 = true := by
 decide +kernel
def pointBounds22284 : List (Nat × Nat × Nat) := [(2924746752,101418734125207,101419115304158),(2924838912,101419148042826,101419529222013)]
theorem point_links_checked22284 : (cuts22284.take 2).map (fun c => (2924740609-1+2*2^9*c.k,101418705830892+c.lower,101419087009826+c.upper)) = pointBounds22284 := by
 decide +kernel
def cuts22285 : List PrefixCut := [⟨58,263584847,263585001⟩,
⟨128,581727260,581727596⟩]
theorem checked22285 : checkPrefixCuts (2^48) 2924871681 9 Manual.Count131072.C022285.packed 128 cuts22285 = true := by
 decide +kernel
def pointBounds22285 : List (Nat × Nat × Nat) := [(2924931072,101419555595983,101419936775406)]
theorem point_links_checked22285 : (cuts22285.take 1).map (fun c => (2924871681-1+2*2^9*c.k,101419292011136+c.lower,101419673190405+c.upper)) = pointBounds22285 := by
 decide +kernel
def cuts22286 : List PrefixCut := [⟨20,93439629,93439685⟩,
⟨110,512322054,512322343⟩,
⟨128,593826012,593826349⟩]
theorem checked22286 : checkPrefixCuts (2^48) 2925002753 9 Manual.Count131072.C022286.packed 128 cuts22286 = true := by
 decide +kernel
def pointBounds22286 : List (Nat × Nat × Nat) := [(2925023232,101419967178025,101420348357686),(2925115392,101420386060450,101420767240344)]
theorem point_links_checked22286 : (cuts22286.take 2).map (fun c => (2925002753-1+2*2^9*c.k,101419873738396+c.lower,101420254918001+c.upper)) = pointBounds22286 := by
 decide +kernel
def cuts22287 : List PrefixCut := [⟨72,326106935,326107124⟩,
⟨128,575901722,575902050⟩]
theorem checked22287 : checkPrefixCuts (2^48) 2925133825 9 Manual.Count131072.C022287.packed 128 cuts22287 = true := by
 decide +kernel
def pointBounds22287 : List (Nat × Nat × Nat) := [(2925207552,101420793671343,101421174851474)]
theorem point_links_checked22287 : (cuts22287.take 1).map (fun c => (2925133825-1+2*2^9*c.k,101420467564408+c.lower,101420848744350+c.upper)) = pointBounds22287 := by
 decide +kernel
def cuts22288 : List PrefixCut := [⟨34,155108977,155109065⟩,
⟨124,567409012,567409332⟩,
⟨128,584150905,584151235⟩]
theorem checked22288 : checkPrefixCuts (2^48) 2925264897 9 Manual.Count131072.C022288.packed 128 cuts22288 = true := by
 decide +kernel
def pointBounds22288 : List (Nat × Nat × Nat) := [(2925299712,101421198575107,101421579755465),(2925391872,101421610875142,101421992055732)]
theorem point_links_checked22288 : (cuts22288.take 2).map (fun c => (2925264897-1+2*2^9*c.k,101421043466130+c.lower,101421424646400+c.upper)) = pointBounds22288 := by
 decide +kernel
def cuts22289 : List PrefixCut := [⟨86,384480243,384480466⟩,
⟨128,576042533,576042859⟩]
theorem checked22289 : checkPrefixCuts (2^48) 2925395969 9 Manual.Count131072.C022289.packed 128 cuts22289 = true := by
 decide +kernel
def pointBounds22289 : List (Nat × Nat × Nat) := [(2925484032,101422012097278,101422393278101)]
theorem point_links_checked22289 : (cuts22289.take 1).map (fun c => (2925395969-1+2*2^9*c.k,101421627617035+c.lower,101422008797635+c.upper)) = pointBounds22289 := by
 decide +kernel
def cuts22290 : List PrefixCut := [⟨48,216478337,216478467⟩,
⟨128,581500654,581500993⟩]
theorem checked22290 : checkPrefixCuts (2^48) 2925527041 9 Manual.Count131072.C022290.packed 128 cuts22290 = true := by
 decide +kernel
def pointBounds22290 : List (Nat × Nat × Nat) := [(2925576192,101422420137905,101422801318961)]
theorem point_links_checked22290 : (cuts22290.take 1).map (fun c => (2925527041-1+2*2^9*c.k,101422203659568+c.lower,101422584840494+c.upper)) = pointBounds22290 := by
 decide +kernel
def cuts22291 : List PrefixCut := [⟨10,46853744,46853769⟩,
⟨100,452271017,452271275⟩,
⟨128,578299893,578300224⟩]
theorem checked22291 : checkPrefixCuts (2^48) 2925658113 9 Manual.Count131072.C022291.packed 128 cuts22291 = true := by
 decide +kernel
def pointBounds22291 : List (Nat × Nat × Nat) := [(2925668352,101422832013966,101423213195256),(2925760512,101423237431239,101423618612762)]
theorem point_links_checked22291 : (cuts22291.take 2).map (fun c => (2925658113-1+2*2^9*c.k,101422785160222+c.lower,101423166341487+c.upper)) = pointBounds22291 := by
 decide +kernel
def cuts22292 : List PrefixCut := [⟨62,275238888,275239048⟩,
⟨128,570962519,570962854⟩]
theorem checked22292 : checkPrefixCuts (2^48) 2925789185 9 Manual.Count131072.C022292.packed 128 cuts22292 = true := by
 decide +kernel
def pointBounds22292 : List (Nat × Nat × Nat) := [(2925852672,101423638699003,101424019880759)]
theorem point_links_checked22292 : (cuts22292.take 1).map (fun c => (2925789185-1+2*2^9*c.k,101423363460115+c.lower,101423744641711+c.upper)) = pointBounds22292 := by
 decide +kernel
def cuts22293 : List PrefixCut := [⟨24,110341475,110341540⟩,
⟨114,516682452,516682749⟩,
⟨128,579883485,579883819⟩]
theorem checked22293 : checkPrefixCuts (2^48) 2925920257 9 Manual.Count131072.C022293.packed 128 cuts22293 = true := by
 decide +kernel
def pointBounds22293 : List (Nat × Nat × Nat) := [(2925944832,101424044764109,101424425946105),(2926036992,101424451105086,101424832287314)]
theorem point_links_checked22293 : (cuts22293.take 2).map (fun c => (2925920257-1+2*2^9*c.k,101423934422634+c.lower,101424315604565+c.upper)) = pointBounds22293 := by
 decide +kernel
def cuts22294 : List PrefixCut := [⟨76,344281450,344281640⟩,
⟨128,575240168,575240495⟩]
theorem checked22294 : checkPrefixCuts (2^48) 2926051329 9 Manual.Count131072.C022294.packed 128 cuts22294 = true := by
 decide +kernel
def pointBounds22294 : List (Nat × Nat × Nat) := [(2926129152,101424858587569,101425239770024)]
theorem point_links_checked22294 : (cuts22294.take 1).map (fun c => (2926051329-1+2*2^9*c.k,101424514306119+c.lower,101424895488384+c.upper)) = pointBounds22294 := by
 decide +kernel
def cuts22295 : List PrefixCut := [⟨38,177376594,177376692⟩,
⟨128,591085770,591086099⟩]
theorem checked22295 : checkPrefixCuts (2^48) 2926182401 9 Manual.Count131072.C022295.packed 128 cuts22295 = true := by
 decide +kernel
def pointBounds22295 : List (Nat × Nat × Nat) := [(2926221312,101425266922881,101425648105571),(2926313472,101425680632057,101426061814978)]
theorem point_links_checked22295 : (cuts22295.take 2).map (fun c => (2926182401-1+2*2^9*c.k,101425089546287+c.lower,101425470728879+c.upper)) = pointBounds22295 := by
 decide +kernel
def cuts22296 : List PrefixCut := [⟨90,409752512,409752747⟩,
⟨128,581056000,581056332⟩]
theorem checked22296 : checkPrefixCuts (2^48) 2926313473 9 Manual.Count131072.C022296.packed 128 cuts22296 = true := by
 decide +kernel
def pointBounds22296 : List (Nat × Nat × Nat) := [(2926405632,101426090384569,101426471567725)]
theorem point_links_checked22296 : (cuts22296.take 1).map (fun c => (2926313473-1+2*2^9*c.k,101425680632057+c.lower,101426061814978+c.upper)) = pointBounds22296 := by
 decide +kernel
def cuts22297 : List PrefixCut := [⟨52,233530744,233530878⟩,
⟨128,574585788,574586116⟩]
theorem checked22297 : checkPrefixCuts (2^48) 2926444545 9 Manual.Count131072.C022297.packed 128 cuts22297 = true := by
 decide +kernel
def pointBounds22297 : List (Nat × Nat × Nat) := [(2926497792,101426495218801,101426876402188)]
theorem point_links_checked22297 : (cuts22297.take 1).map (fun c => (2926444545-1+2*2^9*c.k,101426261688057+c.lower,101426642871310+c.upper)) = pointBounds22297 := by
 decide +kernel
def cuts22298 : List PrefixCut := [⟨14,64439720,64439758⟩,
⟨104,475980870,475981146⟩,
⟨128,580811645,580811979⟩]
theorem checked22298 : checkPrefixCuts (2^48) 2926575617 9 Manual.Count131072.C022298.packed 128 cuts22298 = true := by
 decide +kernel
def pointBounds22298 : List (Nat × Nat × Nat) := [(2926589952,101426900713565,101427281897184),(2926682112,101427312254715,101427693438572)]
theorem point_links_checked22298 : (cuts22298.take 2).map (fun c => (2926575617-1+2*2^9*c.k,101426836273845+c.lower,101427217457426+c.upper)) = pointBounds22298 := by
 decide +kernel
def cuts22299 : List PrefixCut := [⟨66,295444998,295445168⟩,
⟨128,573957260,573957590⟩]
theorem checked22299 : checkPrefixCuts (2^48) 2926706689 9 Manual.Count131072.C022299.packed 128 cuts22299 = true := by
 decide +kernel
def pointBounds22299 : List (Nat × Nat × Nat) := [(2926774272,101427712530488,101428093714573)]
theorem point_links_checked22299 : (cuts22299.take 1).map (fun c => (2926706689-1+2*2^9*c.k,101427417085490+c.lower,101427798269405+c.upper)) = pointBounds22299 := by
 decide +kernel
def cuts22300 : List PrefixCut := [⟨28,124443777,124443851⟩,
⟨118,533157178,533157481⟩,
⟨128,576912783,576913112⟩]
theorem checked22300 : checkPrefixCuts (2^48) 2926837761 9 Manual.Count131072.C022300.packed 128 cuts22300 = true := by
 decide +kernel
def pointBounds22300 : List (Nat × Nat × Nat) := [(2926866432,101428115486527,101428496670846),(2926958592,101428524199928,101428905384476)]
theorem point_links_checked22300 : (cuts22300.take 2).map (fun c => (2926837761-1+2*2^9*c.k,101427991042750+c.lower,101428372226995+c.upper)) = pointBounds22300 := by
 decide +kernel
def cuts22301 : List PrefixCut := [⟨80,371676406,371676621⟩,
⟨128,585926451,585926788⟩]
theorem checked22301 : checkPrefixCuts (2^48) 2926968833 9 Manual.Count131072.C022301.packed 128 cuts22301 = true := by
 decide +kernel
def pointBounds22301 : List (Nat × Nat × Nat) := [(2927050752,101428939631939,101429320816728)]
theorem point_links_checked22301 : (cuts22301.take 1).map (fun c => (2926968833-1+2*2^9*c.k,101428567955533+c.lower,101428949140107+c.upper)) = pointBounds22301 := by
 decide +kernel
def cuts22302 : List PrefixCut := [⟨42,186167686,186167795⟩,
⟨128,579745847,579746186⟩]
theorem checked22302 : checkPrefixCuts (2^48) 2927099905 9 Manual.Count131072.C022302.packed 128 cuts22302 = true := by
 decide +kernel
def pointBounds22302 : List (Nat × Nat × Nat) := [(2927142912,101429340049670,101429721234690)]
theorem point_links_checked22302 : (cuts22302.take 1).map (fun c => (2927099905-1+2*2^9*c.k,101429153881984+c.lower,101429535066895+c.upper)) = pointBounds22302 := by
 decide +kernel
def cuts22303 : List PrefixCut := [⟨4,18558364,18558373⟩,
⟨94,422893330,422893576⟩,
⟨128,578085338,578085671⟩]
theorem checked22303 : checkPrefixCuts (2^48) 2927230977 9 Manual.Count131072.C022303.packed 128 cuts22303 = true := by
 decide +kernel
def pointBounds22303 : List (Nat × Nat × Nat) := [(2927235072,101429752186195,101430133371454),(2927327232,101430156521161,101430537706657)]
theorem point_links_checked22303 : (cuts22303.take 2).map (fun c => (2927230977-1+2*2^9*c.k,101429733627831+c.lower,101430114813081+c.upper)) = pointBounds22303 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000071
