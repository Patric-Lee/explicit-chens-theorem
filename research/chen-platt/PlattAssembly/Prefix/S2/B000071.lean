import PlattAssemblyKernel
import PlattCertificates.Count131072.C012272
import PlattCertificates.Count131072.C012273
import PlattCertificates.Count131072.C012274
import PlattCertificates.Count131072.C012275
import PlattCertificates.Count131072.C012276
import PlattCertificates.Count131072.C012277
import PlattCertificates.Count131072.C012278
import PlattCertificates.Count131072.C012279
import PlattCertificates.Count131072.C012280
import PlattCertificates.Count131072.C012281
import PlattCertificates.Count131072.C012282
import PlattCertificates.Count131072.C012283
import PlattCertificates.Count131072.C012284
import PlattCertificates.Count131072.C012285
import PlattCertificates.Count131072.C012286
import PlattCertificates.Count131072.C012287
import PlattCertificates.Count131072.C012288
import PlattCertificates.Count131072.C012289
import PlattCertificates.Count131072.C012290
import PlattCertificates.Count131072.C012291
import PlattCertificates.Count131072.C012292
import PlattCertificates.Count131072.C012293
import PlattCertificates.Count131072.C012294
import PlattCertificates.Count131072.C012295
import PlattCertificates.Count131072.C012296
import PlattCertificates.Count131072.C012297
import PlattCertificates.Count131072.C012298
import PlattCertificates.Count131072.C012299
import PlattCertificates.Count131072.C012300
import PlattCertificates.Count131072.C012301
import PlattCertificates.Count131072.C012302
import PlattCertificates.Count131072.C012303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12272 : List PrefixCut := [⟨32,272142043,272142248⟩,
⟨82,694047359,694047886⟩,
⟨128,1083647665,1083648481⟩]
theorem checked12272 : checkPrefixCuts (2^48) 1612447745 9 Manual.Count131072.C012272.packed 128 cuts12272 = true := by
 decide +kernel
def pointBounds12272 : List (Nat × Nat × Nat) := [(1612480512,93622556422691,93622932584343),(1612531712,93622978328007,93623354489981)]
theorem point_links_checked12272 : (cuts12272.take 2).map (fun c => (1612447745-1+2*2^9*c.k,93622284280648+c.lower,93622660442095+c.upper)) = pointBounds12272 := by
 decide +kernel
def cuts12273 : List PrefixCut := [⟨4,32989819,32989844⟩,
⟨54,457137311,457137653⟩,
⟨104,882493173,882493836⟩,
⟨128,1088795490,1088796310⟩]
theorem checked12273 : checkPrefixCuts (2^48) 1612578817 9 Manual.Count131072.C012273.packed 128 cuts12273 = true := by
 decide +kernel
def pointBounds12273 : List (Nat × Nat × Nat) := [(1612582912,93623400918132,93623777080420),(1612634112,93623825065624,93624201228229),(1612685312,93624250421486,93624626584412)]
theorem point_links_checked12273 : (cuts12273.take 3).map (fun c => (1612578817-1+2*2^9*c.k,93623367928313+c.lower,93623744090576+c.upper)) = pointBounds12273 := by
 decide +kernel
def cuts12274 : List PrefixCut := [⟨26,220087237,220087403⟩,
⟨76,646114137,646114624⟩,
⟨126,1063575882,1063576683⟩,
⟨128,1081726094,1081726909⟩]
theorem checked12274 : checkPrefixCuts (2^48) 1612709889 9 Manual.Count131072.C012274.packed 128 cuts12274 = true := by
 decide +kernel
def pointBounds12274 : List (Nat × Nat × Nat) := [(1612736512,93624676811040,93625052974289),(1612787712,93625102837940,93625479001510),(1612838912,93625520299685,93625896463569)]
theorem point_links_checked12274 : (cuts12274.take 3).map (fun c => (1612709889-1+2*2^9*c.k,93624456723803+c.lower,93624832886886+c.upper)) = pointBounds12274 := by
 decide +kernel
def cuts12275 : List PrefixCut := [⟨48,402265240,402265546⟩,
⟨98,821445641,821446259⟩,
⟨128,1071691036,1071691844⟩]
theorem checked12275 : checkPrefixCuts (2^48) 1612840961 9 Manual.Count131072.C012275.packed 128 cuts12275 = true := by
 decide +kernel
def pointBounds12275 : List (Nat × Nat × Nat) := [(1612890112,93625940715137,93626316879341),(1612941312,93626359895538,93626736060054)]
theorem point_links_checked12275 : (cuts12275.take 2).map (fun c => (1612840961-1+2*2^9*c.k,93625538449897+c.lower,93625914613795+c.upper)) = pointBounds12275 := by
 decide +kernel
def cuts12276 : List PrefixCut := [⟨20,173633341,173633468⟩,
⟨70,595404635,595405081⟩,
⟨120,1008088754,1008089512⟩,
⟨128,1078409531,1078410341⟩]
theorem checked12276 : checkPrefixCuts (2^48) 1612972033 9 Manual.Count131072.C012276.packed 128 cuts12276 = true := by
 decide +kernel
def pointBounds12276 : List (Nat × Nat × Nat) := [(1612992512,93626783774274,93627159939107),(1613043712,93627205545568,93627581710720),(1613094912,93627618229687,93627994395151)]
theorem point_links_checked12276 : (cuts12276.take 3).map (fun c => (1612972033-1+2*2^9*c.k,93626610140933+c.lower,93626986305639+c.upper)) = pointBounds12276 := by
 decide +kernel
def cuts12277 : List PrefixCut := [⟨42,348980924,348981190⟩,
⟨92,762685835,762686409⟩,
⟨128,1070295225,1070296029⟩]
theorem checked12277 : checkPrefixCuts (2^48) 1613103105 9 Manual.Count131072.C012277.packed 128 cuts12277 = true := by
 decide +kernel
def pointBounds12277 : List (Nat × Nat × Nat) := [(1613146112,93628037531388,93628413697170),(1613197312,93628451236299,93628827402389)]
theorem point_links_checked12277 : (cuts12277.take 2).map (fun c => (1613103105-1+2*2^9*c.k,93627688550464+c.lower,93628064715980+c.upper)) = pointBounds12277 := by
 decide +kernel
def cuts12278 : List PrefixCut := [⟨14,118819424,118819515⟩,
⟨64,532497854,532498262⟩,
⟨114,957678249,957678981⟩,
⟨128,1078408179,1078409005⟩]
theorem checked12278 : checkPrefixCuts (2^48) 1613234177 9 Manual.Count131072.C012278.packed 128 cuts12278 = true := by
 decide +kernel
def pointBounds12278 : List (Nat × Nat × Nat) := [(1613248512,93628877665113,93629253831524),(1613299712,93629291343543,93629667510271),(1613350912,93629716523938,93630092690990)]
theorem point_links_checked12278 : (cuts12278.take 3).map (fun c => (1613234177-1+2*2^9*c.k,93628758845689+c.lower,93629135012009+c.upper)) = pointBounds12278 := by
 decide +kernel
def cuts12279 : List PrefixCut := [⟨36,301471139,301471366⟩,
⟨86,733079436,733079981⟩,
⟨128,1083729133,1083729942⟩]
theorem checked12279 : checkPrefixCuts (2^48) 1613365249 9 Manual.Count131072.C012279.packed 128 cuts12279 = true := by
 decide +kernel
def pointBounds12279 : List (Nat × Nat × Nat) := [(1613402112,93630138725007,93630514892380),(1613453312,93630570333304,93630946500995)]
theorem point_links_checked12279 : (cuts12279.take 2).map (fun c => (1613365249-1+2*2^9*c.k,93629837253868+c.lower,93630213421014+c.upper)) = pointBounds12279 := by
 decide +kernel
def cuts12280 : List PrefixCut := [⟨8,71524433,71524486⟩,
⟨58,491417471,491417837⟩,
⟨108,907982735,907983418⟩,
⟨128,1075268034,1075268844⟩]
theorem checked12280 : checkPrefixCuts (2^48) 1613496321 9 Manual.Count131072.C012280.packed 128 cuts12280 = true := by
 decide +kernel
def pointBounds12280 : List (Nat × Nat × Nat) := [(1613504512,93630992507434,93631368675442),(1613555712,93631412400472,93631788568793),(1613606912,93631828965736,93632205134374)]
theorem point_links_checked12280 : (cuts12280.take 3).map (fun c => (1613496321-1+2*2^9*c.k,93630920983001+c.lower,93631297150956+c.upper)) = pointBounds12280 := by
 decide +kernel
def cuts12281 : List PrefixCut := [⟨30,253453228,253453418⟩,
⟨80,672957437,672957946⟩,
⟨128,1072738533,1072739344⟩]
theorem checked12281 : checkPrefixCuts (2^48) 1613627393 9 Manual.Count131072.C012281.packed 128 cuts12281 = true := by
 decide +kernel
def pointBounds12281 : List (Nat × Nat × Nat) := [(1613658112,93632249704263,93632625873218),(1613709312,93632669208472,93633045377746)]
theorem point_links_checked12281 : (cuts12281.take 2).map (fun c => (1613627393-1+2*2^9*c.k,93631996251035+c.lower,93632372419800+c.upper)) = pointBounds12281 := by
 decide +kernel
def cuts12282 : List PrefixCut := [⟨2,15697964,15697975⟩,
⟨52,447210477,447210815⟩,
⟨102,872081522,872082182⟩,
⟨128,1096022926,1096023754⟩]
theorem checked12282 : checkPrefixCuts (2^48) 1613758465 9 Manual.Count131072.C012282.packed 128 cuts12282 = true := by
 decide +kernel
def pointBounds12282 : List (Nat × Nat × Nat) := [(1613760512,93633084687532,93633460857119),(1613811712,93633516200045,93633892369959),(1613862912,93633941071090,93634317241326)]
theorem point_links_checked12282 : (cuts12282.take 3).map (fun c => (1613758465-1+2*2^9*c.k,93633068989568+c.lower,93633445159144+c.upper)) = pointBounds12282 := by
 decide +kernel
def cuts12283 : List PrefixCut := [⟨24,199172139,199172291⟩,
⟨74,619481792,619482262⟩,
⟨124,1049195482,1049196278⟩,
⟨128,1080411976,1080412796⟩]
theorem checked12283 : checkPrefixCuts (2^48) 1613889537 9 Manual.Count131072.C012283.packed 128 cuts12283 = true := by
 decide +kernel
def pointBounds12283 : List (Nat × Nat × Nat) := [(1613914112,93634364184633,93634740355189),(1613965312,93634784494286,93635160665160),(1614016512,93635214207976,93635590379176)]
theorem point_links_checked12283 : (cuts12283.take 3).map (fun c => (1613889537-1+2*2^9*c.k,93634165012494+c.lower,93634541182898+c.upper)) = pointBounds12283 := by
 decide +kernel
def cuts12284 : List PrefixCut := [⟨46,383834732,383835018⟩,
⟨96,799570341,799570941⟩,
⟨128,1070035568,1070036374⟩]
theorem checked12284 : checkPrefixCuts (2^48) 1614020609 9 Manual.Count131072.C012284.packed 128 cuts12284 = true := by
 decide +kernel
def pointBounds12284 : List (Nat × Nat × Nat) := [(1614067712,93635629259202,93636005430712),(1614118912,93636044994811,93636421166635)]
theorem point_links_checked12284 : (cuts12284.take 2).map (fun c => (1614020609-1+2*2^9*c.k,93635245424470+c.lower,93635621595694+c.upper)) = pointBounds12284 := by
 decide +kernel
def cuts12285 : List PrefixCut := [⟨18,149093574,149093683⟩,
⟨68,573347218,573347648⟩,
⟨118,995320533,995321284⟩,
⟨128,1083200909,1083201724⟩]
theorem checked12285 : checkPrefixCuts (2^48) 1614151681 9 Manual.Count131072.C012285.packed 128 cuts12285 = true := by
 decide +kernel
def pointBounds12285 : List (Nat × Nat × Nat) := [(1614170112,93636464553612,93636840725751),(1614221312,93636888807256,93637264979716),(1614272512,93637310780571,93637686953352)]
theorem point_links_checked12285 : (cuts12285.take 3).map (fun c => (1614151681-1+2*2^9*c.k,93636315460038+c.lower,93636691632068+c.upper)) = pointBounds12285 := by
 decide +kernel
def cuts12286 : List PrefixCut := [⟨40,329023046,329023297⟩,
⟨90,759164540,759165114⟩,
⟨128,1074395222,1074396032⟩]
theorem checked12286 : checkPrefixCuts (2^48) 1614282753 9 Manual.Count131072.C012286.packed 128 cuts12286 = true := by
 decide +kernel
def pointBounds12286 : List (Nat × Nat × Nat) := [(1614323712,93637727683993,93638103857089),(1614374912,93638157825487,93638533998906)]
theorem point_links_checked12286 : (cuts12286.take 2).map (fun c => (1614282753-1+2*2^9*c.k,93637398660947+c.lower,93637774833792+c.upper)) = pointBounds12286 := by
 decide +kernel
def cuts12287 : List PrefixCut := [⟨12,94672283,94672356⟩,
⟨62,519207286,519207684⟩,
⟨112,939370192,939370904⟩,
⟨128,1070646598,1070647408⟩]
theorem checked12287 : checkPrefixCuts (2^48) 1614413825 9 Manual.Count131072.C012287.packed 128 cuts12287 = true := by
 decide +kernel
def pointBounds12287 : List (Nat × Nat × Nat) := [(1614426112,93638567728452,93638943902180),(1614477312,93638992263455,93639368437508),(1614528512,93639412426361,93639788600728)]
theorem point_links_checked12287 : (cuts12287.take 3).map (fun c => (1614413825-1+2*2^9*c.k,93638473056169+c.lower,93638849229824+c.upper)) = pointBounds12287 := by
 decide +kernel
def cuts12288 : List PrefixCut := [⟨34,286781279,286781495⟩,
⟨84,701513437,701513967⟩,
⟨128,1070908645,1070909453⟩]
theorem checked12288 : checkPrefixCuts (2^48) 1614544897 9 Manual.Count131072.C012288.packed 128 cuts12288 = true := by
 decide +kernel
def pointBounds12288 : List (Nat × Nat × Nat) := [(1614579712,93639830484046,93640206658727),(1614630912,93640245216204,93640621391199)]
theorem point_links_checked12288 : (cuts12288.take 2).map (fun c => (1614544897-1+2*2^9*c.k,93639543702767+c.lower,93639919877232+c.upper)) = pointBounds12288 := by
 decide +kernel
def cuts12289 : List PrefixCut := [⟨6,47415714,47415749⟩,
⟨56,472580622,472580976⟩,
⟨106,885181567,885182235⟩,
⟨128,1067509704,1067510510⟩]
theorem checked12289 : checkPrefixCuts (2^48) 1614675969 9 Manual.Count131072.C012289.packed 128 cuts12289 = true := by
 decide +kernel
def pointBounds12289 : List (Nat × Nat × Nat) := [(1614682112,93640662027126,93641038202434),(1614733312,93641087192034,93641463367661),(1614784512,93641499792979,93641875968920)]
theorem point_links_checked12289 : (cuts12289.take 3).map (fun c => (1614675969-1+2*2^9*c.k,93640614611412+c.lower,93640990786685+c.upper)) = pointBounds12289 := by
 decide +kernel
def cuts12290 : List PrefixCut := [⟨28,238103547,238103729⟩,
⟨78,663402354,663402857⟩,
⟨128,1078055511,1078056327⟩]
theorem checked12290 : checkPrefixCuts (2^48) 1614807041 9 Manual.Count131072.C012290.packed 128 cuts12290 = true := by
 decide +kernel
def pointBounds12290 : List (Nat × Nat × Nat) := [(1614835712,93641920224663,93642296400924),(1614886912,93642345523470,93642721700052),(1614938112,93642760176627,93643136353522)]
theorem point_links_checked12290 : (cuts12290.take 3).map (fun c => (1614807041-1+2*2^9*c.k,93641682121116+c.lower,93642058297195+c.upper)) = pointBounds12290 := by
 decide +kernel
def cuts12291 : List PrefixCut := [⟨50,426317641,426317958⟩,
⟨100,841467559,841468188⟩,
⟨128,1079536691,1079537499⟩]
theorem checked12291 : checkPrefixCuts (2^48) 1614938113 9 Manual.Count131072.C012291.packed 128 cuts12291 = true := by
 decide +kernel
def pointBounds12291 : List (Nat × Nat × Nat) := [(1614989312,93643186494268,93643562671480),(1615040512,93643601644186,93643977821710)]
theorem point_links_checked12291 : (cuts12291.take 2).map (fun c => (1614938113-1+2*2^9*c.k,93642760176627+c.lower,93643136353522+c.upper)) = pointBounds12291 := by
 decide +kernel
def cuts12292 : List PrefixCut := [⟨22,181424611,181424750⟩,
⟨72,607178886,607179347⟩,
⟨122,1037450703,1037451486⟩,
⟨128,1088336542,1088337362⟩]
theorem checked12292 : checkPrefixCuts (2^48) 1615069185 9 Manual.Count131072.C012292.packed 128 cuts12292 = true := by
 decide +kernel
def pointBounds12292 : List (Nat × Nat × Nat) := [(1615091712,93644021137929,93644397315771),(1615142912,93644446892204,93644823070368),(1615194112,93644877164021,93645253342507)]
theorem point_links_checked12292 : (cuts12292.take 3).map (fun c => (1615069185-1+2*2^9*c.k,93643839713318+c.lower,93644215891021+c.upper)) = pointBounds12292 := by
 decide +kernel
def cuts12293 : List PrefixCut := [⟨44,374841363,374841650⟩,
⟨94,789925463,789926065⟩,
⟨128,1072739728,1072740541⟩]
theorem checked12293 : checkPrefixCuts (2^48) 1615200257 9 Manual.Count131072.C012293.packed 128 cuts12293 = true := by
 decide +kernel
def pointBounds12293 : List (Nat × Nat × Nat) := [(1615245312,93645302891223,93645679070033),(1615296512,93645717975323,93646094154448)]
theorem point_links_checked12293 : (cuts12293.take 2).map (fun c => (1615200257-1+2*2^9*c.k,93644928049860+c.lower,93645304228383+c.upper)) = pointBounds12293 := by
 decide +kernel
def cuts12294 : List PrefixCut := [⟨16,135567435,135567534⟩,
⟨66,561428554,561428971⟩,
⟨116,990238204,990238940⟩,
⟨128,1089554219,1089555030⟩]
theorem checked12294 : checkPrefixCuts (2^48) 1615331329 9 Manual.Count131072.C012294.packed 128 cuts12294 = true := by
 decide +kernel
def pointBounds12294 : List (Nat × Nat × Nat) := [(1615347712,93646136357023,93646512536458),(1615398912,93646562218142,93646938397895),(1615450112,93646991027792,93647367207864)]
theorem point_links_checked12294 : (cuts12294.take 3).map (fun c => (1615331329-1+2*2^9*c.k,93646000789588+c.lower,93646376968924+c.upper)) = pointBounds12294 := by
 decide +kernel
def cuts12295 : List PrefixCut := [⟨38,307352059,307352294⟩,
⟨88,735437652,735438210⟩,
⟨128,1071868131,1071868941⟩]
theorem checked12295 : checkPrefixCuts (2^48) 1615462401 9 Manual.Count131072.C012295.packed 128 cuts12295 = true := by
 decide +kernel
def pointBounds12295 : List (Nat × Nat × Nat) := [(1615501312,93647397695866,93647773876248),(1615552512,93647825781459,93648201962164)]
theorem point_links_checked12295 : (cuts12295.take 2).map (fun c => (1615462401-1+2*2^9*c.k,93647090343807+c.lower,93647466523954+c.upper)) = pointBounds12295 := by
 decide +kernel
def cuts12296 : List PrefixCut := [⟨10,85717858,85717923⟩,
⟨60,498444926,498445300⟩,
⟨110,908023040,908023722⟩,
⟨128,1057321609,1057322403⟩]
theorem checked12296 : checkPrefixCuts (2^48) 1615593473 9 Manual.Count131072.C012296.packed 128 cuts12296 = true := by
 decide +kernel
def pointBounds12296 : List (Nat × Nat × Nat) := [(1615603712,93648247929796,93648624110818),(1615654912,93648660656864,93649036838195),(1615706112,93649070234978,93649446416617)]
theorem point_links_checked12296 : (cuts12296.take 3).map (fun c => (1615593473-1+2*2^9*c.k,93648162211938+c.lower,93648538392895+c.upper)) = pointBounds12296 := by
 decide +kernel
def cuts12297 : List PrefixCut := [⟨32,276119566,276119773⟩,
⟨82,711105463,711105996⟩,
⟨128,1094689627,1094690448⟩]
theorem checked12297 : checkPrefixCuts (2^48) 1615724545 9 Manual.Count131072.C012297.packed 128 cuts12297 = true := by
 decide +kernel
def pointBounds12297 : List (Nat × Nat × Nat) := [(1615757312,93649495653113,93649871835071),(1615808512,93649930639010,93650306821294)]
theorem point_links_checked12297 : (cuts12297.take 2).map (fun c => (1615724545-1+2*2^9*c.k,93649219533547+c.lower,93649595715298+c.upper)) = pointBounds12297 := by
 decide +kernel
def cuts12298 : List PrefixCut := [⟨4,33097115,33097139⟩,
⟨54,449765294,449765633⟩,
⟨104,874258724,874259382⟩,
⟨128,1074568897,1074569708⟩]
theorem checked12298 : checkPrefixCuts (2^48) 1615855617 9 Manual.Count131072.C012298.packed 128 cuts12298 = true := by
 decide +kernel
def pointBounds12298 : List (Nat × Nat × Nat) := [(1615859712,93650347320289,93650723502885),(1615910912,93650763988468,93651140171379),(1615962112,93651188481898,93651564665128)]
theorem point_links_checked12298 : (cuts12298.take 3).map (fun c => (1615855617-1+2*2^9*c.k,93650314223174+c.lower,93650690405746+c.upper)) = pointBounds12298 := by
 decide +kernel
def cuts12299 : List PrefixCut := [⟨26,230614366,230614538⟩,
⟨76,653338959,653339449⟩,
⟨126,1071695927,1071696732⟩,
⟨128,1088241831,1088242648⟩]
theorem checked12299 : checkPrefixCuts (2^48) 1615986689 9 Manual.Count131072.C012299.packed 128 cuts12299 = true := by
 decide +kernel
def pointBounds12299 : List (Nat × Nat × Nat) := [(1616013312,93651619406437,93651995589992),(1616064512,93652042131030,93652418314903),(1616115712,93652460487998,93652836672186)]
theorem point_links_checked12299 : (cuts12299.take 3).map (fun c => (1615986689-1+2*2^9*c.k,93651388792071+c.lower,93651764975454+c.upper)) = pointBounds12299 := by
 decide +kernel
def cuts12300 : List PrefixCut := [⟨48,401797926,401798229⟩,
⟨98,813858678,813859293⟩,
⟨128,1066034857,1066035659⟩]
theorem checked12300 : checkPrefixCuts (2^48) 1616117761 9 Manual.Count131072.C012300.packed 128 cuts12300 = true := by
 decide +kernel
def pointBounds12300 : List (Nat × Nat × Nat) := [(1616166912,93652878831828,93653255016331),(1616218112,93653290892580,93653667077395)]
theorem point_links_checked12300 : (cuts12300.take 2).map (fun c => (1616117761-1+2*2^9*c.k,93652477033902+c.lower,93652853218102+c.upper)) = pointBounds12300 := by
 decide +kernel
def cuts12301 : List PrefixCut := [⟨20,173281328,173281458⟩,
⟨70,590366305,590366753⟩,
⟨120,1020498799,1020499575⟩,
⟨128,1086323529,1086324354⟩]
theorem checked12301 : checkPrefixCuts (2^48) 1616248833 9 Manual.Count131072.C012301.packed 128 cuts12301 = true := by
 decide +kernel
def pointBounds12301 : List (Nat × Nat × Nat) := [(1616269312,93653716350087,93654092535219),(1616320512,93654133435064,93654509620514),(1616371712,93654563567558,93654939753336)]
theorem point_links_checked12301 : (cuts12301.take 3).map (fun c => (1616248833-1+2*2^9*c.k,93653543068759+c.lower,93653919253761+c.upper)) = pointBounds12301 := by
 decide +kernel
def cuts12302 : List PrefixCut := [⟨42,351756143,351756407⟩,
⟨92,776985730,776986307⟩,
⟨128,1079095873,1079096677⟩]
theorem checked12302 : checkPrefixCuts (2^48) 1616379905 9 Manual.Count131072.C012302.packed 128 cuts12302 = true := by
 decide +kernel
def pointBounds12302 : List (Nat × Nat × Nat) := [(1616422912,93654981148431,93655357334522),(1616474112,93655406378018,93655782564422)]
theorem point_links_checked12302 : (cuts12302.take 2).map (fun c => (1616379905-1+2*2^9*c.k,93654629392288+c.lower,93655005578115+c.upper)) = pointBounds12302 := by
 decide +kernel
def cuts12303 : List PrefixCut := [⟨14,116837312,116837402⟩,
⟨64,538035038,538035444⟩,
⟨114,954692573,954693300⟩,
⟨128,1071173224,1071174040⟩]
theorem checked12303 : checkPrefixCuts (2^48) 1616510977 9 Manual.Count131072.C012303.packed 128 cuts12303 = true := by
 decide +kernel
def pointBounds12303 : List (Nat × Nat × Nat) := [(1616525312,93655825325473,93656201512194),(1616576512,93656246523199,93656622710236),(1616627712,93656663180734,93657039368092)]
theorem point_links_checked12303 : (cuts12303.take 3).map (fun c => (1616510977-1+2*2^9*c.k,93655708488161+c.lower,93656084674792+c.upper)) = pointBounds12303 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000071
