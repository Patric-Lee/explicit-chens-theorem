import PlattAssemblyKernel
import PlattCertificates.Count131072.C026272
import PlattCertificates.Count131072.C026273
import PlattCertificates.Count131072.C026274
import PlattCertificates.Count131072.C026275
import PlattCertificates.Count131072.C026276
import PlattCertificates.Count131072.C026277
import PlattCertificates.Count131072.C026278
import PlattCertificates.Count131072.C026279
import PlattCertificates.Count131072.C026280
import PlattCertificates.Count131072.C026281
import PlattCertificates.Count131072.C026282
import PlattCertificates.Count131072.C026283
import PlattCertificates.Count131072.C026284
import PlattCertificates.Count131072.C026285
import PlattCertificates.Count131072.C026286
import PlattCertificates.Count131072.C026287
import PlattCertificates.Count131072.C026288
import PlattCertificates.Count131072.C026289
import PlattCertificates.Count131072.C026290
import PlattCertificates.Count131072.C026291
import PlattCertificates.Count131072.C026292
import PlattCertificates.Count131072.C026293
import PlattCertificates.Count131072.C026294
import PlattCertificates.Count131072.C026295
import PlattCertificates.Count131072.C026296
import PlattCertificates.Count131072.C026297
import PlattCertificates.Count131072.C026298
import PlattCertificates.Count131072.C026299
import PlattCertificates.Count131072.C026300
import PlattCertificates.Count131072.C026301
import PlattCertificates.Count131072.C026302
import PlattCertificates.Count131072.C026303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000196
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26272 : List PrefixCut := [⟨11,40415267,40415289⟩,
⟨117,440152044,440152294⟩,
⟨128,481953859,481954131⟩]
theorem checked26272 : checkPrefixCuts (2^48) 3447455745 9 Manual.Count131072.C026272.packed 128 cuts26272 = true := by
 decide +kernel
def pointBounds26272 : List (Nat × Nat × Nat) := [(3447467008,103534118424994,103534500797915),(3447575552,103534518161771,103534900534920)]
theorem point_links_checked26272 : (cuts26272.take 2).map (fun c => (3447455745-1+2*2^9*c.k,103534078009727+c.lower,103534460382626+c.upper)) = pointBounds26272 := by
 decide +kernel
def cuts26273 : List PrefixCut := [⟨95,365841749,365841947⟩,
⟨128,492304177,492304443⟩]
theorem checked26273 : checkPrefixCuts (2^48) 3447586817 9 Manual.Count131072.C026273.packed 128 cuts26273 = true := by
 decide +kernel
def pointBounds26273 : List (Nat × Nat × Nat) := [(3447684096,103534925805335,103535308178704)]
theorem point_links_checked26273 : (cuts26273.take 1).map (fun c => (3447586817-1+2*2^9*c.k,103534559963586+c.lower,103534942336757+c.upper)) = pointBounds26273 := by
 decide +kernel
def cuts26274 : List PrefixCut := [⟨73,278719110,278719263⟩,
⟨128,490734271,490734541⟩]
theorem checked26274 : checkPrefixCuts (2^48) 3447717889 9 Manual.Count131072.C026274.packed 128 cuts26274 = true := by
 decide +kernel
def pointBounds26274 : List (Nat × Nat × Nat) := [(3447792640,103535330986873,103535713360463)]
theorem point_links_checked26274 : (cuts26274.take 1).map (fun c => (3447717889-1+2*2^9*c.k,103535052267763+c.lower,103535434641200+c.upper)) = pointBounds26274 := by
 decide +kernel
def cuts26275 : List PrefixCut := [⟨51,196908927,196909035⟩,
⟨128,489572784,489573055⟩]
theorem checked26275 : checkPrefixCuts (2^48) 3447848961 9 Manual.Count131072.C026275.packed 128 cuts26275 = true := by
 decide +kernel
def pointBounds26275 : List (Nat × Nat × Nat) := [(3447901184,103535739910961,103536122284776)]
theorem point_links_checked26275 : (cuts26275.take 1).map (fun c => (3447848961-1+2*2^9*c.k,103535543002034+c.lower,103535925375741+c.upper)) = pointBounds26275 := by
 decide +kernel
def cuts26276 : List PrefixCut := [⟨29,108165546,108165608⟩,
⟨128,481554051,481554324⟩]
theorem checked26276 : checkPrefixCuts (2^48) 3447980033 9 Manual.Count131072.C026276.packed 128 cuts26276 = true := by
 decide +kernel
def pointBounds26276 : List (Nat × Nat × Nat) := [(3448009728,103536140740364,103536523114404)]
theorem point_links_checked26276 : (cuts26276.take 1).map (fun c => (3447980033-1+2*2^9*c.k,103536032574818+c.lower,103536414948796+c.upper)) = pointBounds26276 := by
 decide +kernel
def cuts26277 : List PrefixCut := [⟨7,25795567,25795581⟩,
⟨113,424640544,424640780⟩,
⟨128,480474577,480474846⟩]
theorem checked26277 : checkPrefixCuts (2^48) 3448111105 9 Manual.Count131072.C026277.packed 128 cuts26277 = true := by
 decide +kernel
def pointBounds26277 : List (Nat × Nat × Nat) := [(3448118272,103536539924436,103536922298701),(3448226816,103536938769413,103537321143900)]
theorem point_links_checked26277 : (cuts26277.take 2).map (fun c => (3448111105-1+2*2^9*c.k,103536514128869+c.lower,103536896503120+c.upper)) = pointBounds26277 := by
 decide +kernel
def cuts26278 : List PrefixCut := [⟨91,348712304,348712498⟩,
⟨128,490333178,490333451⟩]
theorem checked26278 : checkPrefixCuts (2^48) 3448242177 9 Manual.Count131072.C026278.packed 128 cuts26278 = true := by
 decide +kernel
def pointBounds26278 : List (Nat × Nat × Nat) := [(3448335360,103537343315750,103537725690464)]
theorem point_links_checked26278 : (cuts26278.take 1).map (fun c => (3448242177-1+2*2^9*c.k,103536994603446+c.lower,103537376977966+c.upper)) = pointBounds26278 := by
 decide +kernel
def cuts26279 : List PrefixCut := [⟨69,260790536,260790677⟩,
⟨128,485825214,485825482⟩]
theorem checked26279 : checkPrefixCuts (2^48) 3448373249 9 Manual.Count131072.C026279.packed 128 cuts26279 = true := by
 decide +kernel
def pointBounds26279 : List (Nat × Nat × Nat) := [(3448443904,103537745727160,103538128102094)]
theorem point_links_checked26279 : (cuts26279.take 1).map (fun c => (3448373249-1+2*2^9*c.k,103537484936624+c.lower,103537867311417+c.upper)) = pointBounds26279 := by
 decide +kernel
def cuts26280 : List PrefixCut := [⟨47,177037543,177037644⟩,
⟨128,486704612,486704887⟩]
theorem checked26280 : checkPrefixCuts (2^48) 3448504321 9 Manual.Count131072.C026280.packed 128 cuts26280 = true := by
 decide +kernel
def pointBounds26280 : List (Nat × Nat × Nat) := [(3448552448,103538147799381,103538530174543)]
theorem point_links_checked26280 : (cuts26280.take 1).map (fun c => (3448504321-1+2*2^9*c.k,103537970761838+c.lower,103538353136899+c.upper)) = pointBounds26280 := by
 decide +kernel
def cuts26281 : List PrefixCut := [⟨25,91168318,91168369⟩,
⟨128,486114708,486114982⟩]
theorem checked26281 : checkPrefixCuts (2^48) 3448635393 9 Manual.Count131072.C026281.packed 128 cuts26281 = true := by
 decide +kernel
def pointBounds26281 : List (Nat × Nat × Nat) := [(3448660992,103538548634768,103538931010155)]
theorem point_links_checked26281 : (cuts26281.take 1).map (fun c => (3448635393-1+2*2^9*c.k,103538457466450+c.lower,103538839841786+c.upper)) = pointBounds26281 := by
 decide +kernel
def cuts26282 : List PrefixCut := [⟨3,11671098,11671105⟩,
⟨109,415337577,415337809⟩,
⟨128,483974312,483974583⟩]
theorem checked26282 : checkPrefixCuts (2^48) 3448766465 9 Manual.Count131072.C026282.packed 128 cuts26282 = true := by
 decide +kernel
def pointBounds26282 : List (Nat × Nat × Nat) := [(3448769536,103538955252256,103539337627873),(3448878080,103539358918735,103539741294577)]
theorem point_links_checked26282 : (cuts26282.take 2).map (fun c => (3448766465-1+2*2^9*c.k,103538943581158+c.lower,103539325956768+c.upper)) = pointBounds26282 := by
 decide +kernel
def cuts26283 : List PrefixCut := [⟨87,331262864,331263058⟩,
⟨128,483058216,483058495⟩]
theorem checked26283 : checkPrefixCuts (2^48) 3448897537 9 Manual.Count131072.C026283.packed 128 cuts26283 = true := by
 decide +kernel
def pointBounds26283 : List (Nat × Nat × Nat) := [(3448986624,103539758818334,103540141194409)]
theorem point_links_checked26283 : (cuts26283.take 1).map (fun c => (3448897537-1+2*2^9*c.k,103539427555470+c.lower,103539809931351+c.upper)) = pointBounds26283 := by
 decide +kernel
def cuts26284 : List PrefixCut := [⟨65,245480238,245480374⟩,
⟨128,485569664,485569936⟩]
theorem checked26284 : checkPrefixCuts (2^48) 3449028609 9 Manual.Count131072.C026284.packed 128 cuts26284 = true := by
 decide +kernel
def pointBounds26284 : List (Nat × Nat × Nat) := [(3449095168,103540156093924,103540538470220)]
theorem point_links_checked26284 : (cuts26284.take 1).map (fun c => (3449028609-1+2*2^9*c.k,103539910613686+c.lower,103540292989846+c.upper)) = pointBounds26284 := by
 decide +kernel
def cuts26285 : List PrefixCut := [⟨43,160111524,160111614⟩,
⟨128,489876262,489876536⟩]
theorem checked26285 : checkPrefixCuts (2^48) 3449159681 9 Manual.Count131072.C026285.packed 128 cuts26285 = true := by
 decide +kernel
def pointBounds26285 : List (Nat × Nat × Nat) := [(3449203712,103540556294874,103540938671396)]
theorem point_links_checked26285 : (cuts26285.take 1).map (fun c => (3449159681-1+2*2^9*c.k,103540396183350+c.lower,103540778559782+c.upper)) = pointBounds26285 := by
 decide +kernel
def cuts26286 : List PrefixCut := [⟨21,82256280,82256325⟩,
⟨127,481697675,481697944⟩,
⟨128,485124901,485125172⟩]
theorem checked26286 : checkPrefixCuts (2^48) 3449290753 9 Manual.Count131072.C026286.packed 128 cuts26286 = true := by
 decide +kernel
def pointBounds26286 : List (Nat × Nat × Nat) := [(3449312256,103540968315892,103541350692643),(3449420800,103541367757287,103541750134262)]
theorem point_links_checked26286 : (cuts26286.take 2).map (fun c => (3449290753-1+2*2^9*c.k,103540886059612+c.lower,103541268436318+c.upper)) = pointBounds26286 := by
 decide +kernel
def cuts26287 : List PrefixCut := [⟨105,400489535,400489758⟩,
⟨128,488533545,488533817⟩]
theorem checked26287 : checkPrefixCuts (2^48) 3449421825 9 Manual.Count131072.C026287.packed 128 cuts26287 = true := by
 decide +kernel
def pointBounds26287 : List (Nat × Nat × Nat) := [(3449529344,103541771674048,103542154051248)]
theorem point_links_checked26287 : (cuts26287.take 1).map (fun c => (3449421825-1+2*2^9*c.k,103541371184513+c.lower,103541753561490+c.upper)) = pointBounds26287 := by
 decide +kernel
def cuts26288 : List PrefixCut := [⟨83,312514588,312514766⟩,
⟨128,485414285,485414557⟩]
theorem checked26288 : checkPrefixCuts (2^48) 3449552897 9 Manual.Count131072.C026288.packed 128 cuts26288 = true := by
 decide +kernel
def pointBounds26288 : List (Nat × Nat × Nat) := [(3449637888,103542172232646,103542554610073)]
theorem point_links_checked26288 : (cuts26288.take 1).map (fun c => (3449552897-1+2*2^9*c.k,103541859718058+c.lower,103542242095307+c.upper)) = pointBounds26288 := by
 decide +kernel
def cuts26289 : List PrefixCut := [⟨61,235560908,235561039⟩,
⟨128,491760112,491760388⟩]
theorem checked26289 : checkPrefixCuts (2^48) 3449683969 9 Manual.Count131072.C026289.packed 128 cuts26289 = true := by
 decide +kernel
def pointBounds26289 : List (Nat × Nat × Nat) := [(3449746432,103542580693251,103542963070903)]
theorem point_links_checked26289 : (cuts26289.take 1).map (fun c => (3449683969-1+2*2^9*c.k,103542345132343+c.lower,103542727509864+c.upper)) = pointBounds26289 := by
 decide +kernel
def cuts26290 : List PrefixCut := [⟨39,146945084,146945167⟩,
⟨128,482766601,482766877⟩]
theorem checked26290 : checkPrefixCuts (2^48) 3449815041 9 Manual.Count131072.C026290.packed 128 cuts26290 = true := by
 decide +kernel
def pointBounds26290 : List (Nat × Nat × Nat) := [(3449854976,103542983837539,103543366215419)]
theorem point_links_checked26290 : (cuts26290.take 1).map (fun c => (3449815041-1+2*2^9*c.k,103542836892455+c.lower,103543219270252+c.upper)) = pointBounds26290 := by
 decide +kernel
def cuts26291 : List PrefixCut := [⟨17,67146923,67146959⟩,
⟨123,465289093,465289354⟩,
⟨128,483482584,483482856⟩]
theorem checked26291 : checkPrefixCuts (2^48) 3449946113 9 Manual.Count131072.C026291.packed 128 cuts26291 = true := by
 decide +kernel
def pointBounds26291 : List (Nat × Nat × Nat) := [(3449963520,103543386805979,103543769184088),(3450072064,103543784948149,103544167326483)]
theorem point_links_checked26291 : (cuts26291.take 2).map (fun c => (3449946113-1+2*2^9*c.k,103543319659056+c.lower,103543702037129+c.upper)) = pointBounds26291 := by
 decide +kernel
def cuts26292 : List PrefixCut := [⟨101,385402223,385402446⟩,
⟨128,491377667,491377948⟩]
theorem checked26292 : checkPrefixCuts (2^48) 3450077185 9 Manual.Count131072.C026292.packed 128 cuts26292 = true := by
 decide +kernel
def pointBounds26292 : List (Nat × Nat × Nat) := [(3450180608,103544188543863,103544570922431)]
theorem point_links_checked26292 : (cuts26292.take 1).map (fun c => (3450077185-1+2*2^9*c.k,103543803141640+c.lower,103544185519985+c.upper)) = pointBounds26292 := by
 decide +kernel
def cuts26293 : List PrefixCut := [⟨79,299239262,299239434⟩,
⟨128,488829998,488830278⟩]
theorem checked26293 : checkPrefixCuts (2^48) 3450208257 9 Manual.Count131072.C026293.packed 128 cuts26293 = true := by
 decide +kernel
def pointBounds26293 : List (Nat × Nat × Nat) := [(3450289152,103544593758569,103544976137367)]
theorem point_links_checked26293 : (cuts26293.take 1).map (fun c => (3450208257-1+2*2^9*c.k,103544294519307+c.lower,103544676897933+c.upper)) = pointBounds26293 := by
 decide +kernel
def cuts26294 : List PrefixCut := [⟨57,215692789,215692907⟩,
⟨128,490035103,490035377⟩]
theorem checked26294 : checkPrefixCuts (2^48) 3450339329 9 Manual.Count131072.C026294.packed 128 cuts26294 = true := by
 decide +kernel
def pointBounds26294 : List (Nat × Nat × Nat) := [(3450397696,103544999042094,103545381421118)]
theorem point_links_checked26294 : (cuts26294.take 1).map (fun c => (3450339329-1+2*2^9*c.k,103544783349305+c.lower,103545165728211+c.upper)) = pointBounds26294 := by
 decide +kernel
def cuts26295 : List PrefixCut := [⟨35,133457313,133457387⟩,
⟨128,487895677,487895949⟩]
theorem checked26295 : checkPrefixCuts (2^48) 3450470401 9 Manual.Count131072.C026295.packed 128 cuts26295 = true := by
 decide +kernel
def pointBounds26295 : List (Nat × Nat × Nat) := [(3450506240,103545406841721,103545789220975)]
theorem point_links_checked26295 : (cuts26295.take 1).map (fun c => (3450470401-1+2*2^9*c.k,103545273384408+c.lower,103545655763588+c.upper)) = pointBounds26295 := by
 decide +kernel
def cuts26296 : List PrefixCut := [⟨13,48290951,48290979⟩,
⟨119,452720554,452720808⟩,
⟨128,487958671,487958946⟩]
theorem checked26296 : checkPrefixCuts (2^48) 3450601473 9 Manual.Count131072.C026296.packed 128 cuts26296 = true := by
 decide +kernel
def pointBounds26296 : List (Nat × Nat × Nat) := [(3450614784,103545809571036,103546191950516),(3450723328,103546214000639,103546596380345)]
theorem point_links_checked26296 : (cuts26296.take 2).map (fun c => (3450601473-1+2*2^9*c.k,103545761280085+c.lower,103546143659537+c.upper)) = pointBounds26296 := by
 decide +kernel
def cuts26297 : List PrefixCut := [⟨97,364284597,364284803⟩,
⟨128,481496202,481496475⟩]
theorem checked26297 : checkPrefixCuts (2^48) 3450732545 9 Manual.Count131072.C026297.packed 128 cuts26297 = true := by
 decide +kernel
def pointBounds26297 : List (Nat × Nat × Nat) := [(3450831872,103546613523353,103546995903286)]
theorem point_links_checked26297 : (cuts26297.take 1).map (fun c => (3450732545-1+2*2^9*c.k,103546249238756+c.lower,103546631618483+c.upper)) = pointBounds26297 := by
 decide +kernel
def cuts26298 : List PrefixCut := [⟨75,286866249,286866410⟩,
⟨128,490857967,490858241⟩]
theorem checked26298 : checkPrefixCuts (2^48) 3450863617 9 Manual.Count131072.C026298.packed 128 cuts26298 = true := by
 decide +kernel
def pointBounds26298 : List (Nat × Nat × Nat) := [(3450940416,103547017601207,103547399981368)]
theorem point_links_checked26298 : (cuts26298.take 1).map (fun c => (3450863617-1+2*2^9*c.k,103546730734958+c.lower,103547113114958+c.upper)) = pointBounds26298 := by
 decide +kernel
def cuts26299 : List PrefixCut := [⟨53,201215363,201215474⟩,
⟨128,488473990,488474263⟩]
theorem checked26299 : checkPrefixCuts (2^48) 3450994689 9 Manual.Count131072.C026299.packed 128 cuts26299 = true := by
 decide +kernel
def pointBounds26299 : List (Nat × Nat × Nat) := [(3451048960,103547422808288,103547805188673)]
theorem point_links_checked26299 : (cuts26299.take 1).map (fun c => (3450994689-1+2*2^9*c.k,103547221592925+c.lower,103547603973199+c.upper)) = pointBounds26299 := by
 decide +kernel
def cuts26300 : List PrefixCut := [⟨31,118017234,118017300⟩,
⟨128,490086569,490086843⟩]
theorem checked26300 : checkPrefixCuts (2^48) 3451125761 9 Manual.Count131072.C026300.packed 128 cuts26300 = true := by
 decide +kernel
def pointBounds26300 : List (Nat × Nat × Nat) := [(3451157504,103547828084149,103548210464762)]
theorem point_links_checked26300 : (cuts26300.take 1).map (fun c => (3451125761-1+2*2^9*c.k,103547710066915+c.lower,103548092447462+c.upper)) = pointBounds26300 := by
 decide +kernel
def cuts26301 : List PrefixCut := [⟨9,33438416,33438434⟩,
⟨115,435997435,435997677⟩,
⟨128,487458181,487458454⟩]
theorem checked26301 : checkPrefixCuts (2^48) 3451256833 9 Manual.Count131072.C026301.packed 128 cuts26301 = true := by
 decide +kernel
def pointBounds26301 : List (Nat × Nat × Nat) := [(3451266048,103548233591900,103548615972739),(3451374592,103548636150919,103549018531982)]
theorem point_links_checked26301 : (cuts26301.take 2).map (fun c => (3451256833-1+2*2^9*c.k,103548200153484+c.lower,103548582534305+c.upper)) = pointBounds26301 := by
 decide +kernel
def cuts26302 : List PrefixCut := [⟨93,354755550,354755749⟩,
⟨128,488255273,488255547⟩]
theorem checked26302 : checkPrefixCuts (2^48) 3451387905 9 Manual.Count131072.C026302.packed 128 cuts26302 = true := by
 decide +kernel
def pointBounds26302 : List (Nat × Nat × Nat) := [(3451483136,103549042367215,103549424748508)]
theorem point_links_checked26302 : (cuts26302.take 1).map (fun c => (3451387905-1+2*2^9*c.k,103548687611665+c.lower,103549069992759+c.upper)) = pointBounds26302 := by
 decide +kernel
def cuts26303 : List PrefixCut := [⟨71,268381575,268381724⟩,
⟨128,484730053,484730325⟩]
theorem checked26303 : checkPrefixCuts (2^48) 3451518977 9 Manual.Count131072.C026303.packed 128 cuts26303 = true := by
 decide +kernel
def pointBounds26303 : List (Nat × Nat × Nat) := [(3451591680,103549444248513,103549826630030)]
theorem point_links_checked26303 : (cuts26303.take 1).map (fun c => (3451518977-1+2*2^9*c.k,103549175866938+c.lower,103549558248306+c.upper)) = pointBounds26303 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000196
