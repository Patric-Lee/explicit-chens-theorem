import PlattAssemblyKernel
import PlattCertificates.Count131072.C015408
import PlattCertificates.Count131072.C015409
import PlattCertificates.Count131072.C015410
import PlattCertificates.Count131072.C015411
import PlattCertificates.Count131072.C015412
import PlattCertificates.Count131072.C015413
import PlattCertificates.Count131072.C015414
import PlattCertificates.Count131072.C015415
import PlattCertificates.Count131072.C015416
import PlattCertificates.Count131072.C015417
import PlattCertificates.Count131072.C015418
import PlattCertificates.Count131072.C015419
import PlattCertificates.Count131072.C015420
import PlattCertificates.Count131072.C015421
import PlattCertificates.Count131072.C015422
import PlattCertificates.Count131072.C015423
import PlattCertificates.Count131072.C015424
import PlattCertificates.Count131072.C015425
import PlattCertificates.Count131072.C015426
import PlattCertificates.Count131072.C015427
import PlattCertificates.Count131072.C015428
import PlattCertificates.Count131072.C015429
import PlattCertificates.Count131072.C015430
import PlattCertificates.Count131072.C015431
import PlattCertificates.Count131072.C015432
import PlattCertificates.Count131072.C015433
import PlattCertificates.Count131072.C015434
import PlattCertificates.Count131072.C015435
import PlattCertificates.Count131072.C015436
import PlattCertificates.Count131072.C015437
import PlattCertificates.Count131072.C015438
import PlattCertificates.Count131072.C015439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000169
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15408 : List PrefixCut := [⟨34,228545434,228545582⟩,
⟨96,632489371,632489786⟩,
⟨128,843497723,843498277⟩]
theorem checked15408 : checkPrefixCuts (2^48) 2023489537 9 Manual.Count131072.C015408.packed 128 cuts15408 = true := by
 decide +kernel
def pointBounds15408 : List (Nat × Nat × Nat) := [(2023524352,96621146750606,96621525017581),(2023587840,96621550694543,96621928961785)]
theorem point_links_checked15408 : (cuts15408.take 2).map (fun c => (2023489537-1+2*2^9*c.k,96620918205172+c.lower,96621296471999+c.upper)) = pointBounds15408 := by
 decide +kernel
def cuts15409 : List PrefixCut := [⟨30,193896546,193896672⟩,
⟨92,605465092,605465494⟩,
⟨128,845668263,845668824⟩]
theorem checked15409 : checkPrefixCuts (2^48) 2023620609 9 Manual.Count131072.C015409.packed 128 cuts15409 = true := by
 decide +kernel
def pointBounds15409 : List (Nat × Nat × Nat) := [(2023651328,96621955599441,96622333866948),(2023714816,96622367167987,96622745435770)]
theorem point_links_checked15409 : (cuts15409.take 2).map (fun c => (2023620609-1+2*2^9*c.k,96621761702895+c.lower,96622139970276+c.upper)) = pointBounds15409 := by
 decide +kernel
def cuts15410 : List PrefixCut := [⟨26,175942240,175942354⟩,
⟨88,577749230,577749607⟩,
⟨128,847838920,847839472⟩]
theorem checked15410 : checkPrefixCuts (2^48) 2023751681 9 Manual.Count131072.C015410.packed 128 cuts15410 = true := by
 decide +kernel
def pointBounds15410 : List (Nat × Nat × Nat) := [(2023778304,96622783313398,96623161581454),(2023841792,96623185120388,96623563388707)]
theorem point_links_checked15410 : (cuts15410.take 2).map (fun c => (2023751681-1+2*2^9*c.k,96622607371158+c.lower,96622985639100+c.upper)) = pointBounds15410 := by
 decide +kernel
def cuts15411 : List PrefixCut := [⟨22,140883859,140883951⟩,
⟨84,560049896,560050265⟩,
⟨128,846532461,846533021⟩]
theorem checked15411 : checkPrefixCuts (2^48) 2023882753 9 Manual.Count131072.C015411.packed 128 cuts15411 = true := by
 decide +kernel
def pointBounds15411 : List (Nat × Nat × Nat) := [(2023905280,96623596093937,96623974362523),(2023968768,96624015259974,96624393528837)]
theorem point_links_checked15411 : (cuts15411.take 2).map (fun c => (2023882753-1+2*2^9*c.k,96623455210078+c.lower,96623833478572+c.upper)) = pointBounds15411 := by
 decide +kernel
def cuts15412 : List PrefixCut := [⟨18,118763255,118763331⟩,
⟨80,534982383,534982732⟩,
⟨128,857880478,857881035⟩]
theorem checked15412 : checkPrefixCuts (2^48) 2024013825 9 Manual.Count131072.C015412.packed 128 cuts15412 = true := by
 decide +kernel
def pointBounds15412 : List (Nat × Nat × Nat) := [(2024032256,96624420505794,96624798774924),(2024095744,96624836724922,96625214994325)]
theorem point_links_checked15412 : (cuts15412.take 2).map (fun c => (2024013825-1+2*2^9*c.k,96624301742539+c.lower,96624680011593+c.upper)) = pointBounds15412 := by
 decide +kernel
def cuts15413 : List PrefixCut := [⟨14,91917457,91917518⟩,
⟨76,512143280,512143618⟩,
⟨128,862413984,862414551⟩]
theorem checked15413 : checkPrefixCuts (2^48) 2024144897 9 Manual.Count131072.C015413.packed 128 cuts15413 = true := by
 decide +kernel
def pointBounds15413 : List (Nat × Nat × Nat) := [(2024159232,96625251540474,96625629810146),(2024222720,96625671766297,96626050036246)]
theorem point_links_checked15413 : (cuts15413.take 2).map (fun c => (2024144897-1+2*2^9*c.k,96625159623017+c.lower,96625537892628+c.upper)) = pointBounds15413 := by
 decide +kernel
def cuts15414 : List PrefixCut := [⟨10,69385607,69385652⟩,
⟨72,473733596,473733911⟩,
⟨128,841918455,841919016⟩]
theorem checked15414 : checkPrefixCuts (2^48) 2024275969 9 Manual.Count131072.C015414.packed 128 cuts15414 = true := by
 decide +kernel
def pointBounds15414 : List (Nat × Nat × Nat) := [(2024286208,96626091422608,96626469692831),(2024349696,96626495770597,96626874041090)]
theorem point_links_checked15414 : (cuts15414.take 2).map (fun c => (2024275969-1+2*2^9*c.k,96626022037001+c.lower,96626400307179+c.upper)) = pointBounds15414 := by
 decide +kernel
def cuts15415 : List PrefixCut := [⟨6,39626528,39626554⟩,
⟨68,447425161,447425448⟩,
⟨128,845061726,845062274⟩]
theorem checked15415 : checkPrefixCuts (2^48) 2024407041 9 Manual.Count131072.C015415.packed 128 cuts15415 = true := by
 decide +kernel
def pointBounds15415 : List (Nat × Nat × Nat) := [(2024413184,96626903581984,96627281852749),(2024476672,96627311380617,96627689651643)]
theorem point_links_checked15415 : (cuts15415.take 2).map (fun c => (2024407041-1+2*2^9*c.k,96626863955456+c.lower,96627242226195+c.upper)) = pointBounds15415 := by
 decide +kernel
def cuts15416 : List PrefixCut := [⟨2,12512844,12512851⟩,
⟨64,428488650,428488927⟩,
⟨126,834719570,834720113⟩,
⟨128,849177934,849178486⟩]
theorem checked15416 : checkPrefixCuts (2^48) 2024538113 9 Manual.Count131072.C015416.packed 128 cuts15416 = true := by
 decide +kernel
def pointBounds15416 : List (Nat × Nat × Nat) := [(2024540160,96627721530026,96628099801320),(2024603648,96628137505832,96628515777396),(2024667136,96628543736752,96628922008582)]
theorem point_links_checked15416 : (cuts15416.take 3).map (fun c => (2024538113-1+2*2^9*c.k,96627709017182+c.lower,96628087288469+c.upper)) = pointBounds15416 := by
 decide +kernel
def cuts15417 : List PrefixCut := [⟨60,402186394,402186665⟩,
⟨122,813952494,813953035⟩,
⟨128,851903277,851903843⟩]
theorem checked15417 : checkPrefixCuts (2^48) 2024669185 9 Manual.Count131072.C015417.packed 128 cuts15417 = true := by
 decide +kernel
def pointBounds15417 : List (Nat × Nat × Nat) := [(2024730624,96628960381510,96629338653620),(2024794112,96629372147610,96629750419990)]
theorem point_links_checked15417 : (cuts15417.take 2).map (fun c => (2024669185-1+2*2^9*c.k,96628558195116+c.lower,96628936466955+c.upper)) = pointBounds15417 := by
 decide +kernel
def cuts15418 : List PrefixCut := [⟨56,373663407,373663649⟩,
⟨118,791798069,791798587⟩,
⟨128,857547438,857547998⟩]
theorem checked15418 : checkPrefixCuts (2^48) 2024800257 9 Manual.Count131072.C015418.packed 128 cuts15418 = true := by
 decide +kernel
def pointBounds15418 : List (Nat × Nat × Nat) := [(2024857600,96629783761800,96630162034447),(2024921088,96630201896462,96630580169385)]
theorem point_links_checked15418 : (cuts15418.take 2).map (fun c => (2024800257-1+2*2^9*c.k,96629410098393+c.lower,96629788370798+c.upper)) = pointBounds15418 := by
 decide +kernel
def cuts15419 : List PrefixCut := [⟨52,346673054,346673281⟩,
⟨114,757692486,757692977⟩,
⟨128,851931867,851932419⟩]
theorem checked15419 : checkPrefixCuts (2^48) 2024931329 9 Manual.Count131072.C015419.packed 128 cuts15419 = true := by
 decide +kernel
def pointBounds15419 : List (Nat × Nat × Nat) := [(2024984576,96630614318885,96630992592077),(2025048064,96631025338317,96631403611773)]
theorem point_links_checked15419 : (cuts15419.take 2).map (fun c => (2024931329-1+2*2^9*c.k,96630267645831+c.lower,96630645918796+c.upper)) = pointBounds15419 := by
 decide +kernel
def cuts15420 : List PrefixCut := [⟨48,321354045,321354251⟩,
⟨110,731652808,731653282⟩,
⟨128,853405689,853406242⟩]
theorem checked15420 : checkPrefixCuts (2^48) 2025062401 9 Manual.Count131072.C015420.packed 128 cuts15420 = true := by
 decide +kernel
def pointBounds15420 : List (Nat × Nat × Nat) := [(2025111552,96631440931743,96631819205466),(2025175040,96631851230506,96632229504497)]
theorem point_links_checked15420 : (cuts15420.take 2).map (fun c => (2025062401-1+2*2^9*c.k,96631119577698+c.lower,96631497851215+c.upper)) = pointBounds15420 := by
 decide +kernel
def cuts15421 : List PrefixCut := [⟨44,295482364,295482557⟩,
⟨106,702558762,702559224⟩,
⟨128,854323219,854323781⟩]
theorem checked15421 : checkPrefixCuts (2^48) 2025193473 9 Manual.Count131072.C015421.packed 128 cuts15421 = true := by
 decide +kernel
def pointBounds15421 : List (Nat × Nat × Nat) := [(2025238528,96632268465751,96632646740014),(2025302016,96632675542149,96633053816681)]
theorem point_links_checked15421 : (cuts15421.take 2).map (fun c => (2025193473-1+2*2^9*c.k,96631972983387+c.lower,96632351257457+c.upper)) = pointBounds15421 := by
 decide +kernel
def cuts15422 : List PrefixCut := [⟨40,258217888,258218059⟩,
⟨102,672773352,672773791⟩,
⟨128,840509644,840510195⟩]
theorem checked15422 : checkPrefixCuts (2^48) 2025324545 9 Manual.Count131072.C015422.packed 128 cuts15422 = true := by
 decide +kernel
def pointBounds15422 : List (Nat × Nat × Nat) := [(2025365504,96633085524494,96633463799297),(2025428992,96633500079958,96633878355029)]
theorem point_links_checked15422 : (cuts15422.take 2).map (fun c => (2025324545-1+2*2^9*c.k,96632827306606+c.lower,96633205581238+c.upper)) = pointBounds15422 := by
 decide +kernel
def cuts15423 : List PrefixCut := [⟨36,250419276,250419437⟩,
⟨98,656749891,656750321⟩,
⟨128,850322192,850322746⟩]
theorem checked15423 : checkPrefixCuts (2^48) 2025455617 9 Manual.Count131072.C015423.packed 128 cuts15423 = true := by
 decide +kernel
def pointBounds15423 : List (Nat × Nat × Nat) := [(2025492480,96633918235526,96634296510870),(2025555968,96634324566141,96634702841754)]
theorem point_links_checked15423 : (cuts15423.take 2).map (fun c => (2025455617-1+2*2^9*c.k,96633667816250+c.lower,96634046091433+c.upper)) = pointBounds15423 := by
 decide +kernel
def cuts15424 : List PrefixCut := [⟨32,210939091,210939228⟩,
⟨94,629055402,629055808⟩,
⟨128,855546983,855547537⟩]
theorem checked15424 : checkPrefixCuts (2^48) 2025586689 9 Manual.Count131072.C015424.packed 128 cuts15424 = true := by
 decide +kernel
def pointBounds15424 : List (Nat × Nat × Nat) := [(2025619456,96634729077533,96635107353407),(2025682944,96635147193844,96635525469987)]
theorem point_links_checked15424 : (cuts15424.take 2).map (fun c => (2025586689-1+2*2^9*c.k,96634518138442+c.lower,96634896414179+c.upper)) = pointBounds15424 := by
 decide +kernel
def cuts15425 : List PrefixCut := [⟨28,183830446,183830566⟩,
⟨90,588581817,588582204⟩,
⟨128,842291812,842292371⟩]
theorem checked15425 : checkPrefixCuts (2^48) 2025717761 9 Manual.Count131072.C015425.packed 128 cuts15425 = true := by
 decide +kernel
def pointBounds15425 : List (Nat × Nat × Nat) := [(2025746432,96635557515871,96635935792282),(2025809920,96635962267242,96636340543920)]
theorem point_links_checked15425 : (cuts15425.take 2).map (fun c => (2025717761-1+2*2^9*c.k,96635373685425+c.lower,96635751961716+c.upper)) = pointBounds15425 := by
 decide +kernel
def cuts15426 : List PrefixCut := [⟨24,160337738,160337846⟩,
⟨86,568815040,568815412⟩,
⟨128,848211773,848212332⟩]
theorem checked15426 : checkPrefixCuts (2^48) 2025848833 9 Manual.Count131072.C015426.packed 128 cuts15426 = true := by
 decide +kernel
def pointBounds15426 : List (Nat × Nat × Nat) := [(2025873408,96636376314975,96636754591933),(2025936896,96636784792277,96637163069499)]
theorem point_links_checked15426 : (cuts15426.take 2).map (fun c => (2025848833-1+2*2^9*c.k,96636215977237+c.lower,96636594254087+c.upper)) = pointBounds15426 := by
 decide +kernel
def cuts15427 : List PrefixCut := [⟨20,133652590,133652677⟩,
⟨82,546411134,546411492⟩,
⟨128,857326078,857326637⟩]
theorem checked15427 : checkPrefixCuts (2^48) 2025979905 9 Manual.Count131072.C015427.packed 128 cuts15427 = true := by
 decide +kernel
def pointBounds15427 : List (Nat × Nat × Nat) := [(2026000384,96637197841600,96637576119096),(2026063872,96637610600144,96637988877911)]
theorem point_links_checked15427 : (cuts15427.take 2).map (fun c => (2025979905-1+2*2^9*c.k,96637064189010+c.lower,96637442466419+c.upper)) = pointBounds15427 := by
 decide +kernel
def cuts15428 : List PrefixCut := [⟨16,107109754,107109825⟩,
⟨78,521509330,521509677⟩,
⟨128,858659624,858660189⟩]
theorem checked15428 : checkPrefixCuts (2^48) 2026110977 9 Manual.Count131072.C015428.packed 128 cuts15428 = true := by
 decide +kernel
def pointBounds15428 : List (Nat × Nat × Nat) := [(2026127360,96638028624842,96638406902881),(2026190848,96638443024418,96638821302733)]
theorem point_links_checked15428 : (cuts15428.take 2).map (fun c => (2026110977-1+2*2^9*c.k,96637921515088+c.lower,96638299793056+c.upper)) = pointBounds15428 := by
 decide +kernel
def cuts15429 : List PrefixCut := [⟨12,76125051,76125100⟩,
⟨74,492860347,492860668⟩,
⟨128,849991985,849992543⟩]
theorem checked15429 : checkPrefixCuts (2^48) 2026242049 9 Manual.Count131072.C015429.packed 128 cuts15429 = true := by
 decide +kernel
def pointBounds15429 : List (Nat × Nat × Nat) := [(2026254336,96638856299763,96639234578345),(2026317824,96639273035059,96639651313913)]
theorem point_links_checked15429 : (cuts15429.take 2).map (fun c => (2026242049-1+2*2^9*c.k,96638780174712+c.lower,96639158453245+c.upper)) = pointBounds15429 := by
 decide +kernel
def cuts15430 : List PrefixCut := [⟨8,52784077,52784112⟩,
⟨70,464353679,464353989⟩,
⟨128,849797894,849798464⟩]
theorem checked15430 : checkPrefixCuts (2^48) 2026373121 9 Manual.Count131072.C015430.packed 128 cuts15430 = true := by
 decide +kernel
def pointBounds15430 : List (Nat × Nat × Nat) := [(2026381312,96639682950774,96640061229900),(2026444800,96640094520376,96640472799777)]
theorem point_links_checked15430 : (cuts15430.take 2).map (fun c => (2026373121-1+2*2^9*c.k,96639630166697+c.lower,96640008445788+c.upper)) = pointBounds15430 := by
 decide +kernel
def cuts15431 : List PrefixCut := [⟨4,23612427,23612443⟩,
⟨66,431128322,431128599⟩,
⟨128,843770326,843770874⟩]
theorem checked15431 : checkPrefixCuts (2^48) 2026504193 9 Manual.Count131072.C015431.packed 128 cuts15431 = true := by
 decide +kernel
def pointBounds15431 : List (Nat × Nat × Nat) := [(2026508288,96640503577018,96640881856695),(2026571776,96640911092913,96641289372851),(2026635264,96641323734917,96641702015126)]
theorem point_links_checked15431 : (cuts15431.take 3).map (fun c => (2026504193-1+2*2^9*c.k,96640479964591+c.lower,96640858244252+c.upper)) = pointBounds15431 := by
 decide +kernel
def cuts15432 : List PrefixCut := [⟨62,413045772,413046039⟩,
⟨124,821495556,821496093⟩,
⟨128,847743675,847744230⟩]
theorem checked15432 : checkPrefixCuts (2^48) 2026635265 9 Manual.Count131072.C015432.packed 128 cuts15432 = true := by
 decide +kernel
def pointBounds15432 : List (Nat × Nat × Nat) := [(2026698752,96641736780689,96642115061165),(2026762240,96642145230473,96642523511219)]
theorem point_links_checked15432 : (cuts15432.take 2).map (fun c => (2026635265-1+2*2^9*c.k,96641323734917+c.lower,96641702015126+c.upper)) = pointBounds15432 := by
 decide +kernel
def cuts15433 : List PrefixCut := [⟨58,383160977,383161229⟩,
⟨120,797556620,797557143⟩,
⟨128,852826919,852827479⟩]
theorem checked15433 : checkPrefixCuts (2^48) 2026766337 9 Manual.Count131072.C015433.packed 128 cuts15433 = true := by
 decide +kernel
def pointBounds15433 : List (Nat × Nat × Nat) := [(2026825728,96642554639569,96642932920585),(2026889216,96642969035212,96643347316499)]
theorem point_links_checked15433 : (cuts15433.take 2).map (fun c => (2026766337-1+2*2^9*c.k,96642171478592+c.lower,96642549759356+c.upper)) = pointBounds15433 := by
 decide +kernel
def cuts15434 : List PrefixCut := [⟨54,355779634,355779863⟩,
⟨116,770566079,770566580⟩,
⟨128,849994723,849995276⟩]
theorem checked15434 : checkPrefixCuts (2^48) 2026897409 9 Manual.Count131072.C015434.packed 128 cuts15434 = true := by
 decide +kernel
def pointBounds15434 : List (Nat × Nat × Nat) := [(2026952704,96643380085145,96643758366698),(2027016192,96643794871590,96644173153415)]
theorem point_links_checked15434 : (cuts15434.take 2).map (fun c => (2026897409-1+2*2^9*c.k,96643024305511+c.lower,96643402586835+c.upper)) = pointBounds15434 := by
 decide +kernel
def cuts15435 : List PrefixCut := [⟨50,335205879,335206098⟩,
⟨112,740940711,740941194⟩,
⟨128,848412483,848413035⟩]
theorem checked15435 : checkPrefixCuts (2^48) 2027028481 9 Manual.Count131072.C015435.packed 128 cuts15435 = true := by
 decide +kernel
def pointBounds15435 : List (Nat × Nat × Nat) := [(2027079680,96644209506113,96644587788209),(2027143168,96644615240945,96644993523305)]
theorem point_links_checked15435 : (cuts15435.take 2).map (fun c => (2027028481-1+2*2^9*c.k,96643874300234+c.lower,96644252582111+c.upper)) = pointBounds15435 := by
 decide +kernel
def cuts15436 : List PrefixCut := [⟨46,304220895,304221093⟩,
⟨108,714789812,714790282⟩,
⟨128,840443266,840443819⟩]
theorem checked15436 : checkPrefixCuts (2^48) 2027159553 9 Manual.Count131072.C015436.packed 128 cuts15436 = true := by
 decide +kernel
def pointBounds15436 : List (Nat × Nat × Nat) := [(2027206656,96645026933612,96645405216239),(2027270144,96645437502529,96645815785428)]
theorem point_links_checked15436 : (cuts15436.take 2).map (fun c => (2027159553-1+2*2^9*c.k,96644722712717+c.lower,96645100995146+c.upper)) = pointBounds15436 := by
 decide +kernel
def cuts15437 : List PrefixCut := [⟨42,282681146,282681332⟩,
⟨104,693085659,693086121⟩,
⟨128,854133987,854134553⟩]
theorem checked15437 : checkPrefixCuts (2^48) 2027290625 9 Manual.Count131072.C015437.packed 128 cuts15437 = true := by
 decide +kernel
def pointBounds15437 : List (Nat × Nat × Nat) := [(2027333632,96645845837129,96646224120297),(2027397120,96646256241642,96646634525086)]
theorem point_links_checked15437 : (cuts15437.take 2).map (fun c => (2027290625-1+2*2^9*c.k,96645563155983+c.lower,96645941438965+c.upper)) = pointBounds15437 := by
 decide +kernel
def cuts15438 : List PrefixCut := [⟨38,260172240,260172412⟩,
⟨100,668052050,668052485⟩,
⟨128,857410590,857411152⟩]
theorem checked15438 : checkPrefixCuts (2^48) 2027421697 9 Manual.Count131072.C015438.packed 128 cuts15438 = true := by
 decide +kernel
def pointBounds15438 : List (Nat × Nat × Nat) := [(2027460608,96646677462210,96647055745930),(2027524096,96647085342020,96647463626003)]
theorem point_links_checked15438 : (cuts15438.take 2).map (fun c => (2027421697-1+2*2^9*c.k,96646417289970+c.lower,96646795573518+c.upper)) = pointBounds15438 := by
 decide +kernel
def cuts15439 : List PrefixCut := [⟨34,224616838,224616984⟩,
⟨96,625113722,625114133⟩,
⟨128,834588700,834589249⟩]
theorem checked15439 : checkPrefixCuts (2^48) 2027552769 9 Manual.Count131072.C015439.packed 128 cuts15439 = true := by
 decide +kernel
def pointBounds15439 : List (Nat × Nat × Nat) := [(2027587584,96647499317398,96647877601654),(2027651072,96647899814282,96648278098803)]
theorem point_links_checked15439 : (cuts15439.take 2).map (fun c => (2027552769-1+2*2^9*c.k,96647274700560+c.lower,96647652984670+c.upper)) = pointBounds15439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000169
