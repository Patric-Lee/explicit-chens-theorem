import PlattAssemblyKernel
import PlattCertificates.Count131072.C030256
import PlattCertificates.Count131072.C030257
import PlattCertificates.Count131072.C030258
import PlattCertificates.Count131072.C030259
import PlattCertificates.Count131072.C030260
import PlattCertificates.Count131072.C030261
import PlattCertificates.Count131072.C030262
import PlattCertificates.Count131072.C030263
import PlattCertificates.Count131072.C030264
import PlattCertificates.Count131072.C030265
import PlattCertificates.Count131072.C030266
import PlattCertificates.Count131072.C030267
import PlattCertificates.Count131072.C030268
import PlattCertificates.Count131072.C030269
import PlattCertificates.Count131072.C030270
import PlattCertificates.Count131072.C030271
import PlattCertificates.Count131072.C030272
import PlattCertificates.Count131072.C030273
import PlattCertificates.Count131072.C030274
import PlattCertificates.Count131072.C030275
import PlattCertificates.Count131072.C030276
import PlattCertificates.Count131072.C030277
import PlattCertificates.Count131072.C030278
import PlattCertificates.Count131072.C030279
import PlattCertificates.Count131072.C030280
import PlattCertificates.Count131072.C030281
import PlattCertificates.Count131072.C030282
import PlattCertificates.Count131072.C030283
import PlattCertificates.Count131072.C030284
import PlattCertificates.Count131072.C030285
import PlattCertificates.Count131072.C030286
import PlattCertificates.Count131072.C030287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30256 : List PrefixCut := [⟨65,215696645,215696763⟩,
⟨128,415719723,415719956⟩]
theorem checked30256 : checkPrefixCuts (2^48) 3969646593 9 Manual.Count131072.C030256.packed 128 cuts30256 = true := by
 decide +kernel
def pointBounds30256 : List (Nat × Nat × Nat) := [(3969713152,105336344690705,105336728072897)]
theorem point_links_checked30256 : (cuts30256.take 1).map (fun c => (3969646593-1+2*2^9*c.k,105336128994060+c.lower,105336512376134+c.upper)) = pointBounds30256 := by
 decide +kernel
def cuts30257 : List PrefixCut := [⟨59,198034622,198034727⟩,
⟨128,425136080,425136314⟩]
theorem checked30257 : checkPrefixCuts (2^48) 3969777665 9 Manual.Count131072.C030257.packed 128 cuts30257 = true := by
 decide +kernel
def pointBounds30257 : List (Nat × Nat × Nat) := [(3969838080,105336742748405,105337126130817)]
theorem point_links_checked30257 : (cuts30257.take 1).map (fun c => (3969777665-1+2*2^9*c.k,105336544713783+c.lower,105336928096090+c.upper)) = pointBounds30257 := by
 decide +kernel
def cuts30258 : List PrefixCut := [⟨53,173496291,173496388⟩,
⟨128,421931473,421931708⟩]
theorem checked30258 : checkPrefixCuts (2^48) 3969908737 9 Manual.Count131072.C030258.packed 128 cuts30258 = true := by
 decide +kernel
def pointBounds30258 : List (Nat × Nat × Nat) := [(3969963008,105337143346154,105337526728792)]
theorem point_links_checked30258 : (cuts30258.take 1).map (fun c => (3969908737-1+2*2^9*c.k,105336969849863+c.lower,105337353232404+c.upper)) = pointBounds30258 := by
 decide +kernel
def cuts30259 : List PrefixCut := [⟨47,158743618,158743709⟩,
⟨128,426100622,426100857⟩]
theorem checked30259 : checkPrefixCuts (2^48) 3970039809 9 Manual.Count131072.C030259.packed 128 cuts30259 = true := by
 decide +kernel
def pointBounds30259 : List (Nat × Nat × Nat) := [(3970087936,105337550524954,105337933907821)]
theorem point_links_checked30259 : (cuts30259.take 1).map (fun c => (3970039809-1+2*2^9*c.k,105337391781336+c.lower,105337775164112+c.upper)) = pointBounds30259 := by
 decide +kernel
def cuts30260 : List PrefixCut := [⟨41,132931970,132932046⟩,
⟨128,413821445,413821681⟩]
theorem checked30260 : checkPrefixCuts (2^48) 3970170881 9 Manual.Count131072.C030260.packed 128 cuts30260 = true := by
 decide +kernel
def pointBounds30260 : List (Nat × Nat × Nat) := [(3970212864,105337950813928,105338334197015)]
theorem point_links_checked30260 : (cuts30260.take 1).map (fun c => (3970170881-1+2*2^9*c.k,105337817881958+c.lower,105338201264969+c.upper)) = pointBounds30260 := by
 decide +kernel
def cuts30261 : List PrefixCut := [⟨35,117614408,117614475⟩,
⟨128,426426960,426427195⟩]
theorem checked30261 : checkPrefixCuts (2^48) 3970301953 9 Manual.Count131072.C030261.packed 128 cuts30261 = true := by
 decide +kernel
def pointBounds30261 : List (Nat × Nat × Nat) := [(3970337792,105338349317811,105338732701125)]
theorem point_links_checked30261 : (cuts30261.take 1).map (fun c => (3970301953-1+2*2^9*c.k,105338231703403+c.lower,105338615086650+c.upper)) = pointBounds30261 := by
 decide +kernel
def cuts30262 : List PrefixCut := [⟨29,96271982,96272036⟩,
⟨128,419465432,419465670⟩]
theorem checked30262 : checkPrefixCuts (2^48) 3970433025 9 Manual.Count131072.C030262.packed 128 cuts30262 = true := by
 decide +kernel
def pointBounds30262 : List (Nat × Nat × Nat) := [(3970462720,105338754402345,105339137785881)]
theorem point_links_checked30262 : (cuts30262.take 1).map (fun c => (3970433025-1+2*2^9*c.k,105338658130363+c.lower,105339041513845+c.upper)) = pointBounds30262 := by
 decide +kernel
def cuts30263 : List PrefixCut := [⟨23,73938475,73938517⟩,
⟨128,415056476,415056709⟩]
theorem checked30263 : checkPrefixCuts (2^48) 3970564097 9 Manual.Count131072.C030263.packed 128 cuts30263 = true := by
 decide +kernel
def pointBounds30263 : List (Nat × Nat × Nat) := [(3970587648,105339151534270,105339534918032)]
theorem point_links_checked30263 : (cuts30263.take 1).map (fun c => (3970564097-1+2*2^9*c.k,105339077595795+c.lower,105339460979515+c.upper)) = pointBounds30263 := by
 decide +kernel
def cuts30264 : List PrefixCut := [⟨17,56143224,56143256⟩,
⟨128,419792229,419792461⟩]
theorem checked30264 : checkPrefixCuts (2^48) 3970695169 9 Manual.Count131072.C030264.packed 128 cuts30264 = true := by
 decide +kernel
def pointBounds30264 : List (Nat × Nat × Nat) := [(3970712576,105339548795495,105339932179480)]
theorem point_links_checked30264 : (cuts30264.take 1).map (fun c => (3970695169-1+2*2^9*c.k,105339492652271+c.lower,105339876036224+c.upper)) = pointBounds30264 := by
 decide +kernel
def cuts30265 : List PrefixCut := [⟨11,37002297,37002318⟩,
⟨128,421337822,421338054⟩]
theorem checked30265 : checkPrefixCuts (2^48) 3970826241 9 Manual.Count131072.C030265.packed 128 cuts30265 = true := by
 decide +kernel
def pointBounds30265 : List (Nat × Nat × Nat) := [(3970837504,105339949446797,105340332831003)]
theorem point_links_checked30265 : (cuts30265.take 1).map (fun c => (3970826241-1+2*2^9*c.k,105339912444500+c.lower,105340295828685+c.upper)) = pointBounds30265 := by
 decide +kernel
def cuts30266 : List PrefixCut := [⟨5,16090519,16090527⟩,
⟨127,412392750,412392990⟩,
⟨128,416007684,416007926⟩]
theorem checked30266 : checkPrefixCuts (2^48) 3970957313 9 Manual.Count131072.C030266.packed 128 cuts30266 = true := by
 decide +kernel
def pointBounds30266 : List (Nat × Nat × Nat) := [(3970962432,105340349872841,105340733257266),(3971087360,105340746175072,105341129559729)]
theorem point_links_checked30266 : (cuts30266.take 2).map (fun c => (3970957313-1+2*2^9*c.k,105340333782322+c.lower,105340717166739+c.upper)) = pointBounds30266 := by
 decide +kernel
def cuts30267 : List PrefixCut := [⟨121,393029315,393029537⟩,
⟨128,416135792,416136028⟩]
theorem checked30267 : checkPrefixCuts (2^48) 3971088385 9 Manual.Count131072.C030267.packed 128 cuts30267 = true := by
 decide +kernel
def pointBounds30267 : List (Nat × Nat × Nat) := [(3971212288,105341142819321,105341526204202)]
theorem point_links_checked30267 : (cuts30267.take 1).map (fun c => (3971088385-1+2*2^9*c.k,105340749790006+c.lower,105341133174665+c.upper)) = pointBounds30267 := by
 decide +kernel
def cuts30268 : List PrefixCut := [⟨115,374446656,374446860⟩,
⟨128,415625895,415626120⟩]
theorem checked30268 : checkPrefixCuts (2^48) 3971219457 9 Manual.Count131072.C030268.packed 128 cuts30268 = true := by
 decide +kernel
def pointBounds30268 : List (Nat × Nat × Nat) := [(3971337216,105341540372454,105341923757553)]
theorem point_links_checked30268 : (cuts30268.take 1).map (fun c => (3971219457-1+2*2^9*c.k,105341165925798+c.lower,105341549310693+c.upper)) = pointBounds30268 := by
 decide +kernel
def cuts30269 : List PrefixCut := [⟨109,360472178,360472381⟩,
⟨128,422912352,422912588⟩]
theorem checked30269 : checkPrefixCuts (2^48) 3971350529 9 Manual.Count131072.C030269.packed 128 cuts30269 = true := by
 decide +kernel
def pointBounds30269 : List (Nat × Nat × Nat) := [(3971462144,105341942023871,105342325409194)]
theorem point_links_checked30269 : (cuts30269.take 1).map (fun c => (3971350529-1+2*2^9*c.k,105341581551693+c.lower,105341964936813+c.upper)) = pointBounds30269 := by
 decide +kernel
def cuts30270 : List PrefixCut := [⟨103,344655832,344656024⟩,
⟨128,424103253,424103490⟩]
theorem checked30270 : checkPrefixCuts (2^48) 3971481601 9 Manual.Count131072.C030270.packed 128 cuts30270 = true := by
 decide +kernel
def pointBounds30270 : List (Nat × Nat × Nat) := [(3971587072,105342349119877,105342732505425)]
theorem point_links_checked30270 : (cuts30270.take 1).map (fun c => (3971481601-1+2*2^9*c.k,105342004464045+c.lower,105342387849401+c.upper)) = pointBounds30270 := by
 decide +kernel
def cuts30271 : List PrefixCut := [⟨97,312752865,312753038⟩,
⟨128,415797309,415797543⟩]
theorem checked30271 : checkPrefixCuts (2^48) 3971612673 9 Manual.Count131072.C030271.packed 128 cuts30271 = true := by
 decide +kernel
def pointBounds30271 : List (Nat × Nat × Nat) := [(3971712000,105342741320163,105343124705929)]
theorem point_links_checked30271 : (cuts30271.take 1).map (fun c => (3971612673-1+2*2^9*c.k,105342428567298+c.lower,105342811952891+c.upper)) = pointBounds30271 := by
 decide +kernel
def cuts30272 : List PrefixCut := [⟨91,296797358,296797522⟩,
⟨128,418547462,418547695⟩]
theorem checked30272 : checkPrefixCuts (2^48) 3971743745 9 Manual.Count131072.C030272.packed 128 cuts30272 = true := by
 decide +kernel
def pointBounds30272 : List (Nat × Nat × Nat) := [(3971836928,105343141161965,105343524547956)]
theorem point_links_checked30272 : (cuts30272.take 1).map (fun c => (3971743745-1+2*2^9*c.k,105342844364607+c.lower,105343227750434+c.upper)) = pointBounds30272 := by
 decide +kernel
def cuts30273 : List PrefixCut := [⟨85,278079116,278079275⟩,
⟨128,420659632,420659873⟩]
theorem checked30273 : checkPrefixCuts (2^48) 3971874817 9 Manual.Count131072.C030273.packed 128 cuts30273 = true := by
 decide +kernel
def pointBounds30273 : List (Nat × Nat × Nat) := [(3971961856,105343540991185,105343924377404)]
theorem point_links_checked30273 : (cuts30273.take 1).map (fun c => (3971874817-1+2*2^9*c.k,105343262912069+c.lower,105343646298129+c.upper)) = pointBounds30273 := by
 decide +kernel
def cuts30274 : List PrefixCut := [⟨79,259999825,259999975⟩,
⟨128,415897940,415898179⟩]
theorem checked30274 : checkPrefixCuts (2^48) 3972005889 9 Manual.Count131072.C030274.packed 128 cuts30274 = true := by
 decide +kernel
def pointBounds30274 : List (Nat × Nat × Nat) := [(3972086784,105343943571526,105344326957977)]
theorem point_links_checked30274 : (cuts30274.take 1).map (fun c => (3972005889-1+2*2^9*c.k,105343683571701+c.lower,105344066958002+c.upper)) = pointBounds30274 := by
 decide +kernel
def cuts30275 : List PrefixCut := [⟨73,240646224,240646361⟩,
⟨128,421836524,421836756⟩]
theorem checked30275 : checkPrefixCuts (2^48) 3972136961 9 Manual.Count131072.C030275.packed 128 cuts30275 = true := by
 decide +kernel
def pointBounds30275 : List (Nat × Nat × Nat) := [(3972211712,105344340115865,105344723502542)]
theorem point_links_checked30275 : (cuts30275.take 1).map (fun c => (3972136961-1+2*2^9*c.k,105344099469641+c.lower,105344482856181+c.upper)) = pointBounds30275 := by
 decide +kernel
def cuts30276 : List PrefixCut := [⟨67,222852769,222852896⟩,
⟨128,420051165,420051401⟩]
theorem checked30276 : checkPrefixCuts (2^48) 3972268033 9 Manual.Count131072.C030276.packed 128 cuts30276 = true := by
 decide +kernel
def pointBounds30276 : List (Nat × Nat × Nat) := [(3972336640,105344744158934,105345127545833)]
theorem point_links_checked30276 : (cuts30276.take 1).map (fun c => (3972268033-1+2*2^9*c.k,105344521306165+c.lower,105344904692937+c.upper)) = pointBounds30276 := by
 decide +kernel
def cuts30277 : List PrefixCut := [⟨61,201659312,201659424⟩,
⟨128,424501217,424501450⟩]
theorem checked30277 : checkPrefixCuts (2^48) 3972399105 9 Manual.Count131072.C030277.packed 128 cuts30277 = true := by
 decide +kernel
def pointBounds30277 : List (Nat × Nat × Nat) := [(3972461568,105345143016642,105345526403762)]
theorem point_links_checked30277 : (cuts30277.take 1).map (fun c => (3972399105-1+2*2^9*c.k,105344941357330+c.lower,105345324744338+c.upper)) = pointBounds30277 := by
 decide +kernel
def cuts30278 : List PrefixCut := [⟨55,175790799,175790898⟩,
⟨128,416693196,416693433⟩]
theorem checked30278 : checkPrefixCuts (2^48) 3972530177 9 Manual.Count131072.C030278.packed 128 cuts30278 = true := by
 decide +kernel
def pointBounds30278 : List (Nat × Nat × Nat) := [(3972586496,105345541649346,105345925036686)]
theorem point_links_checked30278 : (cuts30278.take 1).map (fun c => (3972530177-1+2*2^9*c.k,105345365858547+c.lower,105345749245788+c.upper)) = pointBounds30278 := by
 decide +kernel
def cuts30279 : List PrefixCut := [⟨49,158922229,158922319⟩,
⟨128,423410426,423410660⟩]
theorem checked30279 : checkPrefixCuts (2^48) 3972661249 9 Manual.Count131072.C030279.packed 128 cuts30279 = true := by
 decide +kernel
def pointBounds30279 : List (Nat × Nat × Nat) := [(3972711424,105345941473972,105346324861540)]
theorem point_links_checked30279 : (cuts30279.take 1).map (fun c => (3972661249-1+2*2^9*c.k,105345782551743+c.lower,105346165939221+c.upper)) = pointBounds30279 := by
 decide +kernel
def cuts30280 : List PrefixCut := [⟨43,137874584,137874664⟩,
⟨128,418791200,418791441⟩]
theorem checked30280 : checkPrefixCuts (2^48) 3972792321 9 Manual.Count131072.C030280.packed 128 cuts30280 = true := by
 decide +kernel
def pointBounds30280 : List (Nat × Nat × Nat) := [(3972836352,105346343836753,105346727224545)]
theorem point_links_checked30280 : (cuts30280.take 1).map (fun c => (3972792321-1+2*2^9*c.k,105346205962169+c.lower,105346589349881+c.upper)) = pointBounds30280 := by
 decide +kernel
def cuts30281 : List PrefixCut := [⟨37,121150033,121150103⟩,
⟨128,422036379,422036617⟩]
theorem checked30281 : checkPrefixCuts (2^48) 3972923393 9 Manual.Count131072.C030281.packed 128 cuts30281 = true := by
 decide +kernel
def pointBounds30281 : List (Nat × Nat × Nat) := [(3972961280,105346745903402,105347129291425)]
theorem point_links_checked30281 : (cuts30281.take 1).map (fun c => (3972923393-1+2*2^9*c.k,105346624753369+c.lower,105347008141322+c.upper)) = pointBounds30281 := by
 decide +kernel
def cuts30282 : List PrefixCut := [⟨31,101167660,101167714⟩,
⟨128,416709142,416709374⟩]
theorem checked30282 : checkPrefixCuts (2^48) 3973054465 9 Manual.Count131072.C030282.packed 128 cuts30282 = true := by
 decide +kernel
def pointBounds30282 : List (Nat × Nat × Nat) := [(3973086208,105347147957408,105347531345653)]
theorem point_links_checked30282 : (cuts30282.take 1).map (fun c => (3973054465-1+2*2^9*c.k,105347046789748+c.lower,105347430177939+c.upper)) = pointBounds30282 := by
 decide +kernel
def cuts30283 : List PrefixCut := [⟨25,82957623,82957672⟩,
⟨128,423637940,423638186⟩]
theorem checked30283 : checkPrefixCuts (2^48) 3973185537 9 Manual.Count131072.C030283.packed 128 cuts30283 = true := by
 decide +kernel
def pointBounds30283 : List (Nat × Nat × Nat) := [(3973211136,105347546456513,105347929844985)]
theorem point_links_checked30283 : (cuts30283.take 1).map (fun c => (3973185537-1+2*2^9*c.k,105347463498890+c.lower,105347846887313+c.upper)) = pointBounds30283 := by
 decide +kernel
def cuts30284 : List PrefixCut := [⟨19,64961312,64961347⟩,
⟨128,419656977,419657212⟩]
theorem checked30284 : checkPrefixCuts (2^48) 3973316609 9 Manual.Count131072.C030284.packed 128 cuts30284 = true := by
 decide +kernel
def pointBounds30284 : List (Nat × Nat × Nat) := [(3973336064,105347952098142,105348335486846)]
theorem point_links_checked30284 : (cuts30284.take 1).map (fun c => (3973316609-1+2*2^9*c.k,105347887136830+c.lower,105348270525499+c.upper)) = pointBounds30284 := by
 decide +kernel
def cuts30285 : List PrefixCut := [⟨13,42574142,42574167⟩,
⟨128,418297188,418297424⟩]
theorem checked30285 : checkPrefixCuts (2^48) 3973447681 9 Manual.Count131072.C030285.packed 128 cuts30285 = true := by
 decide +kernel
def pointBounds30285 : List (Nat × Nat × Nat) := [(3973460992,105348349367949,105348732756878)]
theorem point_links_checked30285 : (cuts30285.take 1).map (fun c => (3973447681-1+2*2^9*c.k,105348306793807+c.lower,105348690182711+c.upper)) = pointBounds30285 := by
 decide +kernel
def cuts30286 : List PrefixCut := [⟨7,23163554,23163568⟩,
⟨128,426500275,426500514⟩]
theorem checked30286 : checkPrefixCuts (2^48) 3973578753 9 Manual.Count131072.C030286.packed 128 cuts30286 = true := by
 decide +kernel
def pointBounds30286 : List (Nat × Nat × Nat) := [(3973585920,105348748254549,105349131643703)]
theorem point_links_checked30286 : (cuts30286.take 1).map (fun c => (3973578753-1+2*2^9*c.k,105348725090995+c.lower,105349108480135+c.upper)) = pointBounds30286 := by
 decide +kernel
def cuts30287 : List PrefixCut := [⟨1,3116708,3116710⟩,
⟨123,406015644,406015874⟩,
⟨128,421811179,421811418⟩]
theorem checked30287 : checkPrefixCuts (2^48) 3973709825 9 Manual.Count131072.C030287.packed 128 cuts30287 = true := by
 decide +kernel
def pointBounds30287 : List (Nat × Nat × Nat) := [(3973710848,105349154707978,105349538097359),(3973835776,105349557606914,105349940996523)]
theorem point_links_checked30287 : (cuts30287.take 2).map (fun c => (3973709825-1+2*2^9*c.k,105349151591270+c.lower,105349534980649+c.upper)) = pointBounds30287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000008
