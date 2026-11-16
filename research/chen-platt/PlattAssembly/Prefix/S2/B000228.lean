import PlattAssemblyKernel
import PlattCertificates.Count131072.C017296
import PlattCertificates.Count131072.C017297
import PlattCertificates.Count131072.C017298
import PlattCertificates.Count131072.C017299
import PlattCertificates.Count131072.C017300
import PlattCertificates.Count131072.C017301
import PlattCertificates.Count131072.C017302
import PlattCertificates.Count131072.C017303
import PlattCertificates.Count131072.C017304
import PlattCertificates.Count131072.C017305
import PlattCertificates.Count131072.C017306
import PlattCertificates.Count131072.C017307
import PlattCertificates.Count131072.C017308
import PlattCertificates.Count131072.C017309
import PlattCertificates.Count131072.C017310
import PlattCertificates.Count131072.C017311
import PlattCertificates.Count131072.C017312
import PlattCertificates.Count131072.C017313
import PlattCertificates.Count131072.C017314
import PlattCertificates.Count131072.C017315
import PlattCertificates.Count131072.C017316
import PlattCertificates.Count131072.C017317
import PlattCertificates.Count131072.C017318
import PlattCertificates.Count131072.C017319
import PlattCertificates.Count131072.C017320
import PlattCertificates.Count131072.C017321
import PlattCertificates.Count131072.C017322
import PlattCertificates.Count131072.C017323
import PlattCertificates.Count131072.C017324
import PlattCertificates.Count131072.C017325
import PlattCertificates.Count131072.C017326
import PlattCertificates.Count131072.C017327
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000228
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17296 : List PrefixCut := [⟨28,164722768,164722871⟩,
⟨98,579557166,579557528⟩,
⟨128,759764997,759765473⟩]
theorem checked17296 : checkPrefixCuts (2^48) 2270953473 9 Manual.Count131072.C017296.packed 128 cuts17296 = true := by
 decide +kernel
def pointBounds17296 : List (Nat × Nat × Nat) := [(2270982144,98132555097294,98132934327962),(2271053824,98132969931692,98133349162619)]
theorem point_links_checked17296 : (cuts17296.take 2).map (fun c => (2270953473-1+2*2^9*c.k,98132390374526+c.lower,98132769605091+c.upper)) = pointBounds17296 := by
 decide +kernel
def cuts17297 : List PrefixCut := [⟨40,236968344,236968492⟩,
⟨110,656981831,656982237⟩,
⟨128,758729912,758730385⟩]
theorem checked17297 : checkPrefixCuts (2^48) 2271084545 9 Manual.Count131072.C017297.packed 128 cuts17297 = true := by
 decide +kernel
def pointBounds17297 : List (Nat × Nat × Nat) := [(2271125504,98133387107867,98133766339056),(2271197184,98133807121354,98134186352801)]
theorem point_links_checked17297 : (cuts17297.take 2).map (fun c => (2271084545-1+2*2^9*c.k,98133150139523+c.lower,98133529370564+c.upper)) = pointBounds17297 := by
 decide +kernel
def cuts17298 : List PrefixCut := [⟨52,301521511,301521694⟩,
⟨122,711098703,711099142⟩,
⟨128,748028178,748028639⟩]
theorem checked17298 : checkPrefixCuts (2^48) 2271215617 9 Manual.Count131072.C017298.packed 128 cuts17298 = true := by
 decide +kernel
def pointBounds17298 : List (Nat × Nat × Nat) := [(2271268864,98134210390946,98134589622643),(2271340544,98134619968138,98134999200091)]
theorem point_links_checked17298 : (cuts17298.take 2).map (fun c => (2271215617-1+2*2^9*c.k,98133908869435+c.lower,98134288100949+c.upper)) = pointBounds17298 := by
 decide +kernel
def cuts17299 : List PrefixCut := [⟨64,378954858,378955091⟩,
⟨128,759261900,759262373⟩]
theorem checked17299 : checkPrefixCuts (2^48) 2271346689 9 Manual.Count131072.C017299.packed 128 cuts17299 = true := by
 decide +kernel
def pointBounds17299 : List (Nat × Nat × Nat) := [(2271412224,98135035852471,98135415084679)]
theorem point_links_checked17299 : (cuts17299.take 1).map (fun c => (2271346689-1+2*2^9*c.k,98134656897613+c.lower,98135036129588+c.upper)) = pointBounds17299 := by
 decide +kernel
def cuts17300 : List PrefixCut := [⟨6,37175075,37175099⟩,
⟨76,452537450,452537731⟩,
⟨128,753146488,753146957⟩]
theorem checked17300 : checkPrefixCuts (2^48) 2271477761 9 Manual.Count131072.C017300.packed 128 cuts17300 = true := by
 decide +kernel
def pointBounds17300 : List (Nat × Nat × Nat) := [(2271483904,98135453334588,98135832567060),(2271555584,98135868696963,98136247929692)]
theorem point_links_checked17300 : (cuts17300.take 2).map (fun c => (2271477761-1+2*2^9*c.k,98135416159513+c.lower,98135795391961+c.upper)) = pointBounds17300 := by
 decide +kernel
def cuts17301 : List PrefixCut := [⟨18,107181662,107181729⟩,
⟨88,527226254,527226579⟩,
⟨128,755581166,755581634⟩]
theorem checked17301 : checkPrefixCuts (2^48) 2271608833 9 Manual.Count131072.C017301.packed 128 cuts17301 = true := by
 decide +kernel
def pointBounds17301 : List (Nat × Nat × Nat) := [(2271627264,98136276487663,98136655720647),(2271698944,98136696532255,98137075765497)]
theorem point_links_checked17301 : (cuts17301.take 2).map (fun c => (2271608833-1+2*2^9*c.k,98136169306001+c.lower,98136548538918+c.upper)) = pointBounds17301 := by
 decide +kernel
def cuts17302 : List PrefixCut := [⟨30,180277326,180277441⟩,
⟨100,593356998,593357365⟩,
⟨128,757643649,757644117⟩]
theorem checked17302 : checkPrefixCuts (2^48) 2271739905 9 Manual.Count131072.C017302.packed 128 cuts17302 = true := by
 decide +kernel
def pointBounds17302 : List (Nat × Nat × Nat) := [(2271770624,98137105164493,98137484397993),(2271842304,98137518244165,98137897477917)]
theorem point_links_checked17302 : (cuts17302.take 2).map (fun c => (2271739905-1+2*2^9*c.k,98136924887167+c.lower,98137304120552+c.upper)) = pointBounds17302 := by
 decide +kernel
def cuts17303 : List PrefixCut := [⟨42,252496900,252497057⟩,
⟨112,671497358,671497776⟩,
⟨128,766272391,766272869⟩]
theorem checked17303 : checkPrefixCuts (2^48) 2271870977 9 Manual.Count131072.C017303.packed 128 cuts17303 = true := by
 decide +kernel
def pointBounds17303 : List (Nat × Nat × Nat) := [(2271913984,98137935027716,98138314261726),(2271985664,98138354028174,98138733262445)]
theorem point_links_checked17303 : (cuts17303.take 2).map (fun c => (2271870977-1+2*2^9*c.k,98137682530816+c.lower,98138061764669+c.upper)) = pointBounds17303 := by
 decide +kernel
def cuts17304 : List PrefixCut := [⟨54,320495599,320495796⟩,
⟨124,722993108,722993562⟩,
⟨128,747769398,747769867⟩]
theorem checked17304 : checkPrefixCuts (2^48) 2272002049 9 Manual.Count131072.C017304.packed 128 cuts17304 = true := by
 decide +kernel
def pointBounds17304 : List (Nat × Nat × Nat) := [(2272057344,98138769298806,98139148533334),(2272129024,98139171796315,98139551031100)]
theorem point_links_checked17304 : (cuts17304.take 2).map (fun c => (2272002049-1+2*2^9*c.k,98138448803207+c.lower,98138828037538+c.upper)) = pointBounds17304 := by
 decide +kernel
def cuts17305 : List PrefixCut := [⟨66,395299449,395299690⟩,
⟨128,751938196,751938658⟩]
theorem checked17305 : checkPrefixCuts (2^48) 2272133121 9 Manual.Count131072.C017305.packed 128 cuts17305 = true := by
 decide +kernel
def pointBounds17305 : List (Nat × Nat × Nat) := [(2272200704,98139591872054,98139971107095)]
theorem point_links_checked17305 : (cuts17305.take 1).map (fun c => (2272133121-1+2*2^9*c.k,98139196572605+c.lower,98139575807405+c.upper)) = pointBounds17305 := by
 decide +kernel
def cuts17306 : List PrefixCut := [⟨8,49797337,49797367⟩,
⟨78,458078756,458079043⟩,
⟨128,750160529,750161001⟩]
theorem checked17306 : checkPrefixCuts (2^48) 2272264193 9 Manual.Count131072.C017306.packed 128 cuts17306 = true := by
 decide +kernel
def pointBounds17306 : List (Nat × Nat × Nat) := [(2272272384,98139998308138,98140377543430),(2272344064,98140406589557,98140785825106)]
theorem point_links_checked17306 : (cuts17306.take 2).map (fun c => (2272264193-1+2*2^9*c.k,98139948510801+c.lower,98140327746063+c.upper)) = pointBounds17306 := by
 decide +kernel
def cuts17307 : List PrefixCut := [⟨20,120398219,120398293⟩,
⟨90,530016380,530016709⟩,
⟨128,752842264,752842732⟩]
theorem checked17307 : checkPrefixCuts (2^48) 2272395265 9 Manual.Count131072.C017307.packed 128 cuts17307 = true := by
 decide +kernel
def pointBounds17307 : List (Nat × Nat × Nat) := [(2272415744,98140819069549,98141198305357),(2272487424,98141228687710,98141607923773)]
theorem point_links_checked17307 : (cuts17307.take 2).map (fun c => (2272395265-1+2*2^9*c.k,98140698671330+c.lower,98141077907064+c.upper)) = pointBounds17307 := by
 decide +kernel
def cuts17308 : List PrefixCut := [⟨32,187150969,187151088⟩,
⟨102,601202137,601202508⟩,
⟨128,756762119,756762588⟩]
theorem checked17308 : checkPrefixCuts (2^48) 2272526337 9 Manual.Count131072.C017308.packed 128 cuts17308 = true := by
 decide +kernel
def pointBounds17308 : List (Nat × Nat × Nat) := [(2272559104,98141638664563,98142017900884),(2272630784,98142052715731,98142431952304)]
theorem point_links_checked17308 : (cuts17308.take 2).map (fun c => (2272526337-1+2*2^9*c.k,98141451513594+c.lower,98141830749796+c.upper)) = pointBounds17308 := by
 decide +kernel
def cuts17309 : List PrefixCut := [⟨44,259592787,259592948⟩,
⟨114,678200240,678200662⟩,
⟨128,761796294,761796767⟩]
theorem checked17309 : checkPrefixCuts (2^48) 2272657409 9 Manual.Count131072.C017309.packed 128 cuts17309 = true := by
 decide +kernel
def pointBounds17309 : List (Nat × Nat × Nat) := [(2272702464,98142467868500,98142847105332),(2272774144,98142886475953,98143265713046)]
theorem point_links_checked17309 : (cuts17309.take 2).map (fun c => (2272657409-1+2*2^9*c.k,98142208275713+c.lower,98142587512384+c.upper)) = pointBounds17309 := by
 decide +kernel
def cuts17310 : List PrefixCut := [⟨56,327072140,327072343⟩,
⟨126,736984306,736984763⟩,
⟨128,749120482,749120946⟩]
theorem checked17310 : checkPrefixCuts (2^48) 2272788481 9 Manual.Count131072.C017310.packed 128 cuts17310 = true := by
 decide +kernel
def pointBounds17310 : List (Nat × Nat × Nat) := [(2272845824,98143297144147,98143676381494),(2272917504,98143707056313,98144086293914)]
theorem point_links_checked17310 : (cuts17310.take 2).map (fun c => (2272788481-1+2*2^9*c.k,98142970072007+c.lower,98143349309151+c.upper)) = pointBounds17310 := by
 decide +kernel
def cuts17311 : List PrefixCut := [⟨68,409156076,409156328⟩,
⟨128,764680635,764681100⟩]
theorem checked17311 : checkPrefixCuts (2^48) 2272919553 9 Manual.Count131072.C017311.packed 128 cuts17311 = true := by
 decide +kernel
def pointBounds17311 : List (Nat × Nat × Nat) := [(2272989184,98144128348565,98144507586425)]
theorem point_links_checked17311 : (cuts17311.take 1).map (fun c => (2272919553-1+2*2^9*c.k,98143719192489+c.lower,98144098430097+c.upper)) = pointBounds17311 := by
 decide +kernel
def cuts17312 : List PrefixCut := [⟨10,63649159,63649197⟩,
⟨80,465721395,465721682⟩,
⟨128,746557636,746558099⟩]
theorem checked17312 : checkPrefixCuts (2^48) 2273050625 9 Manual.Count131072.C017312.packed 128 cuts17312 = true := by
 decide +kernel
def pointBounds17312 : List (Nat × Nat × Nat) := [(2273060864,98144547522283,98144926760394),(2273132544,98144949594519,98145328832879)]
theorem point_links_checked17312 : (cuts17312.take 2).map (fun c => (2273050625-1+2*2^9*c.k,98144483873124+c.lower,98144863111197+c.upper)) = pointBounds17312 := by
 decide +kernel
def cuts17313 : List PrefixCut := [⟨22,129271823,129271901⟩,
⟨92,545186682,545187025⟩,
⟨128,759763346,759763822⟩]
theorem checked17313 : checkPrefixCuts (2^48) 2273181697 9 Manual.Count131072.C017313.packed 128 cuts17313 = true := by
 decide +kernel
def pointBounds17313 : List (Nat × Nat × Nat) := [(2273204224,98145359702583,98145738941197),(2273275904,98145775617442,98146154856321)]
theorem point_links_checked17313 : (cuts17313.take 2).map (fun c => (2273181697-1+2*2^9*c.k,98145230430760+c.lower,98145609669296+c.upper)) = pointBounds17313 := by
 decide +kernel
def cuts17314 : List PrefixCut := [⟨34,203925131,203925255⟩,
⟨104,619194625,619195010⟩,
⟨128,759472032,759472505⟩]
theorem checked17314 : checkPrefixCuts (2^48) 2273312769 9 Manual.Count131072.C017314.packed 128 cuts17314 = true := by
 decide +kernel
def pointBounds17314 : List (Nat × Nat × Nat) := [(2273347584,98146194119237,98146573358373),(2273419264,98146609388731,98146988628128)]
theorem point_links_checked17314 : (cuts17314.take 2).map (fun c => (2273312769-1+2*2^9*c.k,98145990194106+c.lower,98146369433118+c.upper)) = pointBounds17314 := by
 decide +kernel
def cuts17315 : List PrefixCut := [⟨46,272874196,272874362⟩,
⟨116,686136657,686137076⟩,
⟨128,757694859,757695325⟩]
theorem checked17315 : checkPrefixCuts (2^48) 2273443841 9 Manual.Count131072.C017315.packed 128 cuts17315 = true := by
 decide +kernel
def pointBounds17315 : List (Nat × Nat × Nat) := [(2273490944,98147022540334,98147401779985),(2273562624,98147435802795,98147815042699)]
theorem point_links_checked17315 : (cuts17315.take 2).map (fun c => (2273443841-1+2*2^9*c.k,98146749666138+c.lower,98147128905623+c.upper)) = pointBounds17315 := by
 decide +kernel
def cuts17316 : List PrefixCut := [⟨58,341567369,341567571⟩,
⟨128,755175123,755175580⟩]
theorem checked17316 : checkPrefixCuts (2^48) 2273574913 9 Manual.Count131072.C017316.packed 128 cuts17316 = true := by
 decide +kernel
def pointBounds17316 : List (Nat × Nat × Nat) := [(2273634304,98147848928366,98148228168519),(2273705984,98148262536120,98148641776528)]
theorem point_links_checked17316 : (cuts17316.take 2).map (fun c => (2273574913-1+2*2^9*c.k,98147507360997+c.lower,98147886600948+c.upper)) = pointBounds17316 := by
 decide +kernel
def cuts17317 : List PrefixCut := [⟨70,418794156,418794412⟩,
⟨128,760826293,760826759⟩]
theorem checked17317 : checkPrefixCuts (2^48) 2273705985 9 Manual.Count131072.C017317.packed 128 cuts17317 = true := by
 decide +kernel
def pointBounds17317 : List (Nat × Nat × Nat) := [(2273777664,98148681330276,98149060570940)]
theorem point_links_checked17317 : (cuts17317.take 1).map (fun c => (2273705985-1+2*2^9*c.k,98148262536120+c.lower,98148641776528+c.upper)) = pointBounds17317 := by
 decide +kernel
def cuts17318 : List PrefixCut := [⟨12,69568950,69568993⟩,
⟨82,476453219,476453509⟩,
⟨128,750136683,750137144⟩]
theorem checked17318 : checkPrefixCuts (2^48) 2273837057 9 Manual.Count131072.C017318.packed 128 cuts17318 = true := by
 decide +kernel
def pointBounds17318 : List (Nat × Nat × Nat) := [(2273849344,98149092931363,98149472172280),(2273921024,98149499815632,98149879056796)]
theorem point_links_checked17318 : (cuts17318.take 2).map (fun c => (2273837057-1+2*2^9*c.k,98149023362413+c.lower,98149402603287+c.upper)) = pointBounds17318 := by
 decide +kernel
def cuts17319 : List PrefixCut := [⟨24,142842932,142843019⟩,
⟨94,549082568,549082903⟩,
⟨128,746875316,746875773⟩]
theorem checked17319 : checkPrefixCuts (2^48) 2273968129 9 Manual.Count131072.C017319.packed 128 cuts17319 = true := by
 decide +kernel
def pointBounds17319 : List (Nat × Nat × Nat) := [(2273992704,98149916342028,98150295583450),(2274064384,98150322581664,98150701823334)]
theorem point_links_checked17319 : (cuts17319.take 2).map (fun c => (2273968129-1+2*2^9*c.k,98149773499096+c.lower,98150152740431+c.upper)) = pointBounds17319 := by
 decide +kernel
def cuts17320 : List PrefixCut := [⟨36,224524634,224524768⟩,
⟨106,642373060,642373454⟩,
⟨128,773443081,773443553⟩]
theorem checked17320 : checkPrefixCuts (2^48) 2274099201 9 Manual.Count131072.C017320.packed 128 cuts17320 = true := by
 decide +kernel
def pointBounds17320 : List (Nat × Nat × Nat) := [(2274136064,98150744899046,98151124140972),(2274207744,98151162747472,98151541989658)]
theorem point_links_checked17320 : (cuts17320.take 2).map (fun c => (2274099201-1+2*2^9*c.k,98150520374412+c.lower,98150899616204+c.upper)) = pointBounds17320 := by
 decide +kernel
def cuts17321 : List PrefixCut := [⟨48,284289918,284290094⟩,
⟨118,694067495,694067922⟩,
⟨128,753101135,753101597⟩]
theorem checked17321 : checkPrefixCuts (2^48) 2274230273 9 Manual.Count131072.C017321.packed 128 cuts17321 = true := by
 decide +kernel
def pointBounds17321 : List (Nat × Nat × Nat) := [(2274279424,98151578107411,98151957349851),(2274351104,98151987884988,98152367127679)]
theorem point_links_checked17321 : (cuts17321.take 2).map (fun c => (2274230273-1+2*2^9*c.k,98151293817493+c.lower,98151673059757+c.upper)) = pointBounds17321 := by
 decide +kernel
def cuts17322 : List PrefixCut := [⟨60,347513284,347513502⟩,
⟨128,750334935,750335401⟩]
theorem checked17322 : checkPrefixCuts (2^48) 2274361345 9 Manual.Count131072.C017322.packed 128 cuts17322 = true := by
 decide +kernel
def pointBounds17322 : List (Nat × Nat × Nat) := [(2274422784,98152394431912,98152773674856)]
theorem point_links_checked17322 : (cuts17322.take 1).map (fun c => (2274361345-1+2*2^9*c.k,98152046918628+c.lower,98152426161354+c.upper)) = pointBounds17322 := by
 decide +kernel
def cuts17323 : List PrefixCut := [⟨2,12994042,12994050⟩,
⟨72,423722883,423723141⟩,
⟨128,750291997,750292460⟩]
theorem checked17323 : checkPrefixCuts (2^48) 2274492417 9 Manual.Count131072.C017323.packed 128 cuts17323 = true := by
 decide +kernel
def pointBounds17323 : List (Nat × Nat × Nat) := [(2274494464,98152810247605,98153189490805),(2274566144,98153220976446,98153600219896)]
theorem point_links_checked17323 : (cuts17323.take 2).map (fun c => (2274492417-1+2*2^9*c.k,98152797253563+c.lower,98153176496755+c.upper)) = pointBounds17323 := by
 decide +kernel
def cuts17324 : List PrefixCut := [⟨14,84889280,84889331⟩,
⟨84,509822706,509823018⟩,
⟨128,768933883,768934357⟩]
theorem checked17324 : checkPrefixCuts (2^48) 2274623489 9 Manual.Count131072.C017324.packed 128 cuts17324 = true := by
 decide +kernel
def pointBounds17324 : List (Nat × Nat × Nat) := [(2274637824,98153632434840,98154011678546),(2274709504,98154057368266,98154436612233)]
theorem point_links_checked17324 : (cuts17324.take 2).map (fun c => (2274623489-1+2*2^9*c.k,98153547545560+c.lower,98153926789215+c.upper)) = pointBounds17324 := by
 decide +kernel
def cuts17325 : List PrefixCut := [⟨26,157147082,157147178⟩,
⟨96,556069293,556069647⟩,
⟨128,743895023,743895495⟩]
theorem checked17325 : checkPrefixCuts (2^48) 2274754561 9 Manual.Count131072.C017325.packed 128 cuts17325 = true := by
 decide +kernel
def pointBounds17325 : List (Nat × Nat × Nat) := [(2274781184,98154473626525,98154852870750),(2274852864,98154872548736,98155251793219)]
theorem point_links_checked17325 : (cuts17325.take 2).map (fun c => (2274754561-1+2*2^9*c.k,98154316479443+c.lower,98154695723572+c.upper)) = pointBounds17325 := by
 decide +kernel
def cuts17326 : List PrefixCut := [⟨38,222467249,222467386⟩,
⟨108,641408161,641408557⟩,
⟨128,752760561,752761029⟩]
theorem checked17326 : checkPrefixCuts (2^48) 2274885633 9 Manual.Count131072.C017326.packed 128 cuts17326 = true := by
 decide +kernel
def pointBounds17326 : List (Nat × Nat × Nat) := [(2274924544,98155282841715,98155662086453),(2274996224,98155701782627,98156081027624)]
theorem point_links_checked17326 : (cuts17326.take 2).map (fun c => (2274885633-1+2*2^9*c.k,98155060374466+c.lower,98155439619067+c.upper)) = pointBounds17326 := by
 decide +kernel
def cuts17327 : List PrefixCut := [⟨50,297182450,297182634⟩,
⟨120,706817987,706818425⟩,
⟨128,755067776,755068244⟩]
theorem checked17327 : checkPrefixCuts (2^48) 2275016705 9 Manual.Count131072.C017327.packed 128 cuts17327 = true := by
 decide +kernel
def pointBounds17327 : List (Nat × Nat × Nat) := [(2275067904,98156110317477,98156489562730),(2275139584,98156519953014,98156899198521)]
theorem point_links_checked17327 : (cuts17327.take 2).map (fun c => (2275016705-1+2*2^9*c.k,98155813135027+c.lower,98156192380096+c.upper)) = pointBounds17327 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000228
