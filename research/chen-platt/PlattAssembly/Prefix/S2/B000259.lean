import PlattAssemblyKernel
import PlattCertificates.Count131072.C018288
import PlattCertificates.Count131072.C018289
import PlattCertificates.Count131072.C018290
import PlattCertificates.Count131072.C018291
import PlattCertificates.Count131072.C018292
import PlattCertificates.Count131072.C018293
import PlattCertificates.Count131072.C018294
import PlattCertificates.Count131072.C018295
import PlattCertificates.Count131072.C018296
import PlattCertificates.Count131072.C018297
import PlattCertificates.Count131072.C018298
import PlattCertificates.Count131072.C018299
import PlattCertificates.Count131072.C018300
import PlattCertificates.Count131072.C018301
import PlattCertificates.Count131072.C018302
import PlattCertificates.Count131072.C018303
import PlattCertificates.Count131072.C018304
import PlattCertificates.Count131072.C018305
import PlattCertificates.Count131072.C018306
import PlattCertificates.Count131072.C018307
import PlattCertificates.Count131072.C018308
import PlattCertificates.Count131072.C018309
import PlattCertificates.Count131072.C018310
import PlattCertificates.Count131072.C018311
import PlattCertificates.Count131072.C018312
import PlattCertificates.Count131072.C018313
import PlattCertificates.Count131072.C018314
import PlattCertificates.Count131072.C018315
import PlattCertificates.Count131072.C018316
import PlattCertificates.Count131072.C018317
import PlattCertificates.Count131072.C018318
import PlattCertificates.Count131072.C018319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000259
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18288 : List PrefixCut := [⟨4,20750308,20750321⟩,
⟨78,430239681,430239948⟩,
⟨128,708070851,708071282⟩]
theorem checked18288 : checkPrefixCuts (2^48) 2400976897 9 Manual.Count131072.C018288.packed 128 cuts18288 = true := by
 decide +kernel
def pointBounds18288 : List (Nat × Nat × Nat) := [(2400980992,98858833748529,98859213424817),(2401056768,98859243237902,98859622914444)]
theorem point_links_checked18288 : (cuts18288.take 2).map (fun c => (2400976897-1+2*2^9*c.k,98858812998221+c.lower,98859192674496+c.upper)) = pointBounds18288 := by
 decide +kernel
def cuts18289 : List PrefixCut := [⟨24,132700393,132700475⟩,
⟨98,541812301,541812631⟩,
⟨128,706273972,706274401⟩]
theorem checked18289 : checkPrefixCuts (2^48) 2401107969 9 Manual.Count131072.C018289.packed 128 cuts18289 = true := by
 decide +kernel
def pointBounds18289 : List (Nat × Nat × Nat) := [(2401132544,98859653769465,98860033446253),(2401208320,98860062881373,98860442558409)]
theorem point_links_checked18289 : (cuts18289.take 2).map (fun c => (2401107969-1+2*2^9*c.k,98859521069072+c.lower,98859900745778+c.upper)) = pointBounds18289 := by
 decide +kernel
def cuts18290 : List PrefixCut := [⟨44,247333357,247333503⟩,
⟨118,660053079,660053474⟩,
⟨128,716902128,716902556⟩]
theorem checked18290 : checkPrefixCuts (2^48) 2401239041 9 Manual.Count131072.C018290.packed 128 cuts18290 = true := by
 decide +kernel
def pointBounds18290 : List (Nat × Nat × Nat) := [(2401284096,98860474676401,98860854353682),(2401359872,98860887396123,98861267073653)]
theorem point_links_checked18290 : (cuts18290.take 2).map (fun c => (2401239041-1+2*2^9*c.k,98860227343044+c.lower,98860607020179+c.upper)) = pointBounds18290 := by
 decide +kernel
def cuts18291 : List PrefixCut := [⟨64,354802784,354803004⟩,
⟨128,706900107,706900540⟩]
theorem checked18291 : checkPrefixCuts (2^48) 2401370113 9 Manual.Count131072.C018291.packed 128 cuts18291 = true := by
 decide +kernel
def pointBounds18291 : List (Nat × Nat × Nat) := [(2401435648,98861299047956,98861678725739)]
theorem point_links_checked18291 : (cuts18291.take 1).map (fun c => (2401370113-1+2*2^9*c.k,98860944245172+c.lower,98861323922735+c.upper)) = pointBounds18291 := by
 decide +kernel
def cuts18292 : List PrefixCut := [⟨10,55790837,55790872⟩,
⟨84,468237089,468237373⟩,
⟨128,720691443,720691880⟩]
theorem checked18292 : checkPrefixCuts (2^48) 2401501185 9 Manual.Count131072.C018292.packed 128 cuts18292 = true := by
 decide +kernel
def pointBounds18292 : List (Nat × Nat × Nat) := [(2401511424,98861706936116,98862086614147),(2401587200,98862119382368,98862499060648)]
theorem point_links_checked18292 : (cuts18292.take 2).map (fun c => (2401501185-1+2*2^9*c.k,98861651145279+c.lower,98862030823275+c.upper)) = pointBounds18292 := by
 decide +kernel
def cuts18293 : List PrefixCut := [⟨30,164784271,164784372⟩,
⟨104,579665754,579666105⟩,
⟨128,708815401,708815833⟩]
theorem checked18293 : checkPrefixCuts (2^48) 2401632257 9 Manual.Count131072.C018293.packed 128 cuts18293 = true := by
 decide +kernel
def pointBounds18293 : List (Nat × Nat × Nat) := [(2401662976,98862536620993,98862916299527),(2401738752,98862951502476,98863331181260)]
theorem point_links_checked18293 : (cuts18293.take 2).map (fun c => (2401632257-1+2*2^9*c.k,98862371836722+c.lower,98862751515155+c.upper)) = pointBounds18293 := by
 decide +kernel
def cuts18294 : List PrefixCut := [⟨50,282202796,282202962⟩,
⟨124,690143752,690144165⟩,
⟨128,710886170,710886596⟩]
theorem checked18294 : checkPrefixCuts (2^48) 2401763329 9 Manual.Count131072.C018294.packed 128 cuts18294 = true := by
 decide +kernel
def pointBounds18294 : List (Nat × Nat × Nat) := [(2401814528,98863362854919,98863742533950),(2401890304,98863770795875,98864150475153)]
theorem point_links_checked18294 : (cuts18294.take 2).map (fun c => (2401763329-1+2*2^9*c.k,98863080652123+c.lower,98863460330988+c.upper)) = pointBounds18294 := by
 decide +kernel
def cuts18295 : List PrefixCut := [⟨70,386248253,386248490⟩,
⟨128,702527218,702527649⟩]
theorem checked18295 : checkPrefixCuts (2^48) 2401894401 9 Manual.Count131072.C018295.packed 128 cuts18295 = true := by
 decide +kernel
def pointBounds18295 : List (Nat × Nat × Nat) := [(2401966080,98864177786546,98864557466074)]
theorem point_links_checked18295 : (cuts18295.take 1).map (fun c => (2401894401-1+2*2^9*c.k,98863791538293+c.lower,98864171217584+c.upper)) = pointBounds18295 := by
 decide +kernel
def cuts18296 : List PrefixCut := [⟨16,90347253,90347309⟩,
⟨90,503991522,503991829⟩,
⟨128,708582325,708582756⟩]
theorem checked18296 : checkPrefixCuts (2^48) 2402025473 9 Manual.Count131072.C018296.packed 128 cuts18296 = true := by
 decide +kernel
def pointBounds18296 : List (Nat × Nat × Nat) := [(2402041856,98864584412764,98864964092542),(2402117632,98864998057033,98865377737062)]
theorem point_links_checked18296 : (cuts18296.take 2).map (fun c => (2402025473-1+2*2^9*c.k,98864494065511+c.lower,98864873745233+c.upper)) = pointBounds18296 := by
 decide +kernel
def cuts18297 : List PrefixCut := [⟨36,201658191,201658312⟩,
⟨110,603441926,603442295⟩,
⟨128,703973763,703974192⟩]
theorem checked18297 : checkPrefixCuts (2^48) 2402156545 9 Manual.Count131072.C018297.packed 128 cuts18297 = true := by
 decide +kernel
def pointBounds18297 : List (Nat × Nat × Nat) := [(2402193408,98865404306027,98865783986301),(2402269184,98865806089762,98866185770284)]
theorem point_links_checked18297 : (cuts18297.take 2).map (fun c => (2402156545-1+2*2^9*c.k,98865202647836+c.lower,98865582327989+c.upper)) = pointBounds18297 := by
 decide +kernel
def cuts18298 : List PrefixCut := [⟨56,313893377,313893570⟩,
⟨128,713308604,713309038⟩]
theorem checked18298 : checkPrefixCuts (2^48) 2402287617 9 Manual.Count131072.C018298.packed 128 cuts18298 = true := by
 decide +kernel
def pointBounds18298 : List (Nat × Nat × Nat) := [(2402344960,98866220514976,98866600195751)]
theorem point_links_checked18298 : (cuts18298.take 1).map (fun c => (2402287617-1+2*2^9*c.k,98865906621599+c.lower,98866286302181+c.upper)) = pointBounds18298 := by
 decide +kernel
def cuts18299 : List PrefixCut := [⟨2,10193187,10193194⟩,
⟨76,413813458,413813706⟩,
⟨128,701436471,701436894⟩]
theorem checked18299 : checkPrefixCuts (2^48) 2402418689 9 Manual.Count131072.C018299.packed 128 cuts18299 = true := by
 decide +kernel
def pointBounds18299 : List (Nat × Nat × Nat) := [(2402420736,98866630123390,98867009804413),(2402496512,98867033743661,98867413424925)]
theorem point_links_checked18299 : (cuts18299.take 2).map (fun c => (2402418689-1+2*2^9*c.k,98866619930203+c.lower,98866999611219+c.upper)) = pointBounds18299 := by
 decide +kernel
def cuts18300 : List PrefixCut := [⟨22,123365479,123365553⟩,
⟨96,540784373,540784702⟩,
⟨128,718854096,718854536⟩]
theorem checked18300 : checkPrefixCuts (2^48) 2402549761 9 Manual.Count131072.C018300.packed 128 cuts18300 = true := by
 decide +kernel
def pointBounds18300 : List (Nat × Nat × Nat) := [(2402572288,98867444732153,98867824413666),(2402648064,98867862151047,98868241832815)]
theorem point_links_checked18300 : (cuts18300.take 2).map (fun c => (2402549761-1+2*2^9*c.k,98867321366674+c.lower,98867701048113+c.upper)) = pointBounds18300 := by
 decide +kernel
def cuts18301 : List PrefixCut := [⟨42,235587226,235587369⟩,
⟨116,648879688,648880083⟩,
⟨128,717877660,717878095⟩]
theorem checked18301 : checkPrefixCuts (2^48) 2402680833 9 Manual.Count131072.C018301.packed 128 cuts18301 = true := by
 decide +kernel
def pointBounds18301 : List (Nat × Nat × Nat) := [(2402723840,98868275807996,98868655490018),(2402799616,98868689100458,98869068782732)]
theorem point_links_checked18301 : (cuts18301.take 2).map (fun c => (2402680833-1+2*2^9*c.k,98868040220770+c.lower,98868419902649+c.upper)) = pointBounds18301 := by
 decide +kernel
def cuts18302 : List PrefixCut := [⟨62,344398655,344398861⟩,
⟨128,712215745,712216175⟩]
theorem checked18302 : checkPrefixCuts (2^48) 2402811905 9 Manual.Count131072.C018302.packed 128 cuts18302 = true := by
 decide +kernel
def pointBounds18302 : List (Nat × Nat × Nat) := [(2402875392,98869102497085,98869482179605)]
theorem point_links_checked18302 : (cuts18302.take 1).map (fun c => (2402811905-1+2*2^9*c.k,98868758098430+c.lower,98869137780744+c.upper)) = pointBounds18302 := by
 decide +kernel
def cuts18303 : List PrefixCut := [⟨8,45449299,45449324⟩,
⟨82,455540099,455540377⟩,
⟨128,715573861,715574295⟩]
theorem checked18303 : checkPrefixCuts (2^48) 2402942977 9 Manual.Count131072.C018303.packed 128 cuts18303 = true := by
 decide +kernel
def pointBounds18303 : List (Nat × Nat × Nat) := [(2402951168,98869515763474,98869895446243),(2403026944,98869925854274,98870305537296)]
theorem point_links_checked18303 : (cuts18303.take 2).map (fun c => (2402942977-1+2*2^9*c.k,98869470314175+c.lower,98869849996919+c.upper)) = pointBounds18303 := by
 decide +kernel
def cuts18304 : List PrefixCut := [⟨28,151801099,151801191⟩,
⟨102,562451610,562451950⟩,
⟨128,708389908,708390336⟩]
theorem checked18304 : checkPrefixCuts (2^48) 2403074049 9 Manual.Count131072.C018304.packed 128 cuts18304 = true := by
 decide +kernel
def pointBounds18304 : List (Nat × Nat × Nat) := [(2403102720,98870337689135,98870717372405),(2403178496,98870748339646,98871128023164)]
theorem point_links_checked18304 : (cuts18304.take 2).map (fun c => (2403074049-1+2*2^9*c.k,98870185888036+c.lower,98870565571214+c.upper)) = pointBounds18304 := by
 decide +kernel
def cuts18305 : List PrefixCut := [⟨48,263176688,263176852⟩,
⟨122,677197876,677198287⟩,
⟨128,710693781,710694212⟩]
theorem checked18305 : checkPrefixCuts (2^48) 2403205121 9 Manual.Count131072.C018305.packed 128 cuts18305 = true := by
 decide +kernel
def pointBounds18305 : List (Nat × Nat × Nat) := [(2403254272,98871157454632,98871537138402),(2403330048,98871571475820,98871951159837)]
theorem point_links_checked18305 : (cuts18305.take 2).map (fun c => (2403205121-1+2*2^9*c.k,98870894277944+c.lower,98871273961550+c.upper)) = pointBounds18305 := by
 decide +kernel
def cuts18306 : List PrefixCut := [⟨68,374187941,374188166⟩,
⟨128,707961403,707961830⟩]
theorem checked18306 : checkPrefixCuts (2^48) 2403336193 9 Manual.Count131072.C018306.packed 128 cuts18306 = true := by
 decide +kernel
def pointBounds18306 : List (Nat × Nat × Nat) := [(2403405824,98871979159666,98872358843928)]
theorem point_links_checked18306 : (cuts18306.take 1).map (fun c => (2403336193-1+2*2^9*c.k,98871604971725+c.lower,98871984655762+c.upper)) = pointBounds18306 := by
 decide +kernel
def cuts18307 : List PrefixCut := [⟨14,78113483,78113528⟩,
⟨88,491744131,491744426⟩,
⟨128,714949355,714949786⟩]
theorem checked18307 : checkPrefixCuts (2^48) 2403467265 9 Manual.Count131072.C018307.packed 128 cuts18307 = true := by
 decide +kernel
def pointBounds18307 : List (Nat × Nat × Nat) := [(2403481600,98872391046611,98872770731120),(2403557376,98872804677259,98873184362018)]
theorem point_links_checked18307 : (cuts18307.take 2).map (fun c => (2403467265-1+2*2^9*c.k,98872312933128+c.lower,98872692617592+c.upper)) = pointBounds18307 := by
 decide +kernel
def cuts18308 : List PrefixCut := [⟨34,188655818,188655936⟩,
⟨108,602260456,602260827⟩,
⟨128,710343513,710343951⟩]
theorem checked18308 : checkPrefixCuts (2^48) 2403598337 9 Manual.Count131072.C018308.packed 128 cuts18308 = true := by
 decide +kernel
def pointBounds18308 : List (Nat × Nat × Nat) := [(2403633152,98873216538301,98873596223314),(2403708928,98873630142939,98874009828205)]
theorem point_links_checked18308 : (cuts18308.take 2).map (fun c => (2403598337-1+2*2^9*c.k,98873027882483+c.lower,98873407567378+c.upper)) = pointBounds18308 := by
 decide +kernel
def cuts18309 : List PrefixCut := [⟨54,298131243,298131422⟩,
⟨128,705152447,705152873⟩]
theorem checked18309 : checkPrefixCuts (2^48) 2403729409 9 Manual.Count131072.C018309.packed 128 cuts18309 = true := by
 decide +kernel
def pointBounds18309 : List (Nat × Nat × Nat) := [(2403784704,98874036357239,98874416042751),(2403860480,98874443378443,98874823064202)]
theorem point_links_checked18309 : (cuts18309.take 2).map (fun c => (2403729409-1+2*2^9*c.k,98873738225996+c.lower,98874117911329+c.upper)) = pointBounds18309 := by
 decide +kernel
def cuts18310 : List PrefixCut := [⟨74,410638133,410638381⟩,
⟨128,706987440,706987868⟩]
theorem checked18310 : checkPrefixCuts (2^48) 2403860481 9 Manual.Count131072.C018310.packed 128 cuts18310 = true := by
 decide +kernel
def pointBounds18310 : List (Nat × Nat × Nat) := [(2403936256,98874854016576,98875233702583)]
theorem point_links_checked18310 : (cuts18310.take 1).map (fun c => (2403860481-1+2*2^9*c.k,98874443378443+c.lower,98874823064202+c.upper)) = pointBounds18310 := by
 decide +kernel
def cuts18311 : List PrefixCut := [⟨20,114158829,114158898⟩,
⟨94,521726930,521727245⟩,
⟨128,712685935,712686364⟩]
theorem checked18311 : checkPrefixCuts (2^48) 2403991553 9 Manual.Count131072.C018311.packed 128 cuts18311 = true := by
 decide +kernel
def pointBounds18311 : List (Nat × Nat × Nat) := [(2404012032,98875264524712,98875644210968),(2404087808,98875672092813,98876051779315)]
theorem point_links_checked18311 : (cuts18311.take 2).map (fun c => (2403991553-1+2*2^9*c.k,98875150365883+c.lower,98875530052070+c.upper)) = pointBounds18311 := by
 decide +kernel
def cuts18312 : List PrefixCut := [⟨40,221279519,221279651⟩,
⟨114,634909914,634910295⟩,
⟨128,714169055,714169484⟩]
theorem checked18312 : checkPrefixCuts (2^48) 2404122625 9 Manual.Count131072.C018312.packed 128 cuts18312 = true := by
 decide +kernel
def pointBounds18312 : List (Nat × Nat × Nat) := [(2404163584,98876084331337,98876464018085),(2404239360,98876497961732,98876877648729)]
theorem point_links_checked18312 : (cuts18312.take 2).map (fun c => (2404122625-1+2*2^9*c.k,98875863051818+c.lower,98876242738434+c.upper)) = pointBounds18312 := by
 decide +kernel
def cuts18313 : List PrefixCut := [⟨60,332250969,332251168⟩,
⟨128,707808319,707808743⟩]
theorem checked18313 : checkPrefixCuts (2^48) 2404253697 9 Manual.Count131072.C018313.packed 128 cuts18313 = true := by
 decide +kernel
def pointBounds18313 : List (Nat × Nat × Nat) := [(2404315136,98876909471842,98877289159086)]
theorem point_links_checked18313 : (cuts18313.take 1).map (fun c => (2404253697-1+2*2^9*c.k,98876577220873+c.lower,98876956907918+c.upper)) = pointBounds18313 := by
 decide +kernel
def cuts18314 : List PrefixCut := [⟨6,33247078,33247097⟩,
⟨80,439229073,439229334⟩,
⟨128,705662492,705662913⟩]
theorem checked18314 : checkPrefixCuts (2^48) 2404384769 9 Manual.Count131072.C018314.packed 128 cuts18314 = true := by
 decide +kernel
def pointBounds18314 : List (Nat × Nat × Nat) := [(2404390912,98877318276270,98877697963758),(2404466688,98877724258265,98878103945995)]
theorem point_links_checked18314 : (cuts18314.take 2).map (fun c => (2404384769-1+2*2^9*c.k,98877285029192+c.lower,98877664716661+c.upper)) = pointBounds18314 := by
 decide +kernel
def cuts18315 : List PrefixCut := [⟨26,144101225,144101314⟩,
⟨100,550877099,550877434⟩,
⟨128,705038900,705039325⟩]
theorem checked18315 : checkPrefixCuts (2^48) 2404515841 9 Manual.Count131072.C018315.packed 128 cuts18315 = true := by
 decide +kernel
def pointBounds18315 : List (Nat × Nat × Nat) := [(2404542464,98878134792909,98878514480888),(2404618240,98878541568783,98878921257008)]
theorem point_links_checked18315 : (cuts18315.take 2).map (fun c => (2404515841-1+2*2^9*c.k,98877990691684+c.lower,98878370379574+c.upper)) = pointBounds18315 := by
 decide +kernel
def cuts18316 : List PrefixCut := [⟨46,258453966,258454121⟩,
⟨120,665906437,665906833⟩,
⟨128,708512049,708512473⟩]
theorem checked18316 : checkPrefixCuts (2^48) 2404646913 9 Manual.Count131072.C018316.packed 128 cuts18316 = true := by
 decide +kernel
def pointBounds18316 : List (Nat × Nat × Nat) := [(2404694016,98878954184550,98879333873020),(2404769792,98879361637021,98879741325732)]
theorem point_links_checked18316 : (cuts18316.take 2).map (fun c => (2404646913-1+2*2^9*c.k,98878695730584+c.lower,98879075418899+c.upper)) = pointBounds18316 := by
 decide +kernel
def cuts18317 : List PrefixCut := [⟨66,363429521,363429745⟩,
⟨128,706951745,706952178⟩]
theorem checked18317 : checkPrefixCuts (2^48) 2404777985 9 Manual.Count131072.C018317.packed 128 cuts18317 = true := by
 decide +kernel
def pointBounds18317 : List (Nat × Nat × Nat) := [(2404845568,98879767672154,98880147361117)]
theorem point_links_checked18317 : (cuts18317.take 1).map (fun c => (2404777985-1+2*2^9*c.k,98879404242633+c.lower,98879783931372+c.upper)) = pointBounds18317 := by
 decide +kernel
def cuts18318 : List PrefixCut := [⟨12,65777326,65777367⟩,
⟨86,477053673,477053967⟩,
⟨128,709137014,709137445⟩]
theorem checked18318 : checkPrefixCuts (2^48) 2404909057 9 Manual.Count131072.C018318.packed 128 cuts18318 = true := by
 decide +kernel
def pointBounds18318 : List (Nat × Nat × Nat) := [(2404921344,98880176971704,98880556660917),(2404997120,98880588248051,98880967937517)]
theorem point_links_checked18318 : (cuts18318.take 2).map (fun c => (2404909057-1+2*2^9*c.k,98880111194378+c.lower,98880490883550+c.upper)) = pointBounds18318 := by
 decide +kernel
def cuts18319 : List PrefixCut := [⟨32,176137091,176137202⟩,
⟨106,586100174,586100539⟩,
⟨128,713311346,713311789⟩]
theorem checked18319 : checkPrefixCuts (2^48) 2405040129 9 Manual.Count131072.C018319.packed 128 cuts18319 = true := by
 decide +kernel
def pointBounds18319 : List (Nat × Nat × Nat) := [(2405072896,98880996468483,98881376158197),(2405148672,98881406431566,98881786121534)]
theorem point_links_checked18319 : (cuts18319.take 2).map (fun c => (2405040129-1+2*2^9*c.k,98880820331392+c.lower,98881200020995+c.upper)) = pointBounds18319 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000259
