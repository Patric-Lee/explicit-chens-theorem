import PlattAssemblyKernel
import PlattCertificates.Count131072.C041408
import PlattCertificates.Count131072.C041409
import PlattCertificates.Count131072.C041410
import PlattCertificates.Count131072.C041411
import PlattCertificates.Count131072.C041412
import PlattCertificates.Count131072.C041413
import PlattCertificates.Count131072.C041414
import PlattCertificates.Count131072.C041415
import PlattCertificates.Count131072.C041416
import PlattCertificates.Count131072.C041417
import PlattCertificates.Count131072.C041418
import PlattCertificates.Count131072.C041419
import PlattCertificates.Count131072.C041420
import PlattCertificates.Count131072.C041421
import PlattCertificates.Count131072.C041422
import PlattCertificates.Count131072.C041423
import PlattCertificates.Count131072.C041424
import PlattCertificates.Count131072.C041425
import PlattCertificates.Count131072.C041426
import PlattCertificates.Count131072.C041427
import PlattCertificates.Count131072.C041428
import PlattCertificates.Count131072.C041429
import PlattCertificates.Count131072.C041430
import PlattCertificates.Count131072.C041431
import PlattCertificates.Count131072.C041432
import PlattCertificates.Count131072.C041433
import PlattCertificates.Count131072.C041434
import PlattCertificates.Count131072.C041435
import PlattCertificates.Count131072.C041436
import PlattCertificates.Count131072.C041437
import PlattCertificates.Count131072.C041438
import PlattCertificates.Count131072.C041439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41408 : List PrefixCut := [⟨64,306327981,306328162⟩]
theorem checked41408 : checkPrefixCuts (2^48) 5431361537 10 Manual.Count131072.C041408.packed 64 cuts41408 = true := by
 decide +kernel
def cuts41409 : List PrefixCut := [⟨17,80014078,80014125⟩,
⟨64,302641217,302641395⟩]
theorem checked41409 : checkPrefixCuts (2^48) 5431492609 10 Manual.Count131072.C041409.packed 64 cuts41409 = true := by
 decide +kernel
def pointBounds41409 : List (Nat × Nat × Nat) := [(5431527424,109300997277824,109301383040577)]
theorem point_links_checked41409 : (cuts41409.take 1).map (fun c => (5431492609-1+2*2^10*c.k,109300917263746+c.lower,109301303026452+c.upper)) = pointBounds41409 := by
 decide +kernel
def cuts41410 : List PrefixCut := [⟨36,170336125,170336225⟩,
⟨64,304914036,304914215⟩]
theorem checked41410 : checkPrefixCuts (2^48) 5431623681 10 Manual.Count131072.C041410.packed 64 cuts41410 = true := by
 decide +kernel
def pointBounds41410 : List (Nat × Nat × Nat) := [(5431697408,109301390241088,109301776004072)]
theorem point_links_checked41410 : (cuts41410.take 1).map (fun c => (5431623681-1+2*2^10*c.k,109301219904963+c.lower,109301605667847+c.upper)) = pointBounds41410 := by
 decide +kernel
def cuts41411 : List PrefixCut := [⟨55,258891273,258891422⟩,
⟨64,301382926,301383098⟩]
theorem checked41411 : checkPrefixCuts (2^48) 5431754753 10 Manual.Count131072.C041411.packed 64 cuts41411 = true := by
 decide +kernel
def pointBounds41411 : List (Nat × Nat × Nat) := [(5431867392,109301783710272,109302169473484)]
theorem point_links_checked41411 : (cuts41411.take 1).map (fun c => (5431754753-1+2*2^10*c.k,109301524818999+c.lower,109301910582062+c.upper)) = pointBounds41411 := by
 decide +kernel
def cuts41412 : List PrefixCut := [⟨64,301375693,301375876⟩]
theorem checked41412 : checkPrefixCuts (2^48) 5431885825 10 Manual.Count131072.C041412.packed 64 cuts41412 = true := by
 decide +kernel
def cuts41413 : List PrefixCut := [⟨10,46584067,46584095⟩,
⟨64,301834737,301834912⟩]
theorem checked41413 : checkPrefixCuts (2^48) 5432016897 10 Manual.Count131072.C041413.packed 64 cuts41413 = true := by
 decide +kernel
def pointBounds41413 : List (Nat × Nat × Nat) := [(5432037376,109302174161685,109302559925131)]
theorem point_links_checked41413 : (cuts41413.take 1).map (fun c => (5432016897-1+2*2^10*c.k,109302127577618+c.lower,109302513341036+c.upper)) = pointBounds41413 := by
 decide +kernel
def cuts41414 : List PrefixCut := [⟨29,135913944,135914025⟩,
⟨64,299081253,299081429⟩]
theorem checked41414 : checkPrefixCuts (2^48) 5432147969 10 Manual.Count131072.C041414.packed 64 cuts41414 = true := by
 decide +kernel
def pointBounds41414 : List (Nat × Nat × Nat) := [(5432207360,109302565326299,109302951089973)]
theorem point_links_checked41414 : (cuts41414.take 1).map (fun c => (5432147969-1+2*2^10*c.k,109302429412355+c.lower,109302815175948+c.upper)) = pointBounds41414 := by
 decide +kernel
def cuts41415 : List PrefixCut := [⟨48,229694902,229695038⟩,
⟨64,304100029,304100211⟩]
theorem checked41415 : checkPrefixCuts (2^48) 5432279041 10 Manual.Count131072.C041415.packed 64 cuts41415 = true := by
 decide +kernel
def pointBounds41415 : List (Nat × Nat × Nat) := [(5432377344,109302958188510,109303343952415)]
theorem point_links_checked41415 : (cuts41415.take 1).map (fun c => (5432279041-1+2*2^10*c.k,109302728493608+c.lower,109303114257377+c.upper)) = pointBounds41415 := by
 decide +kernel
def cuts41416 : List PrefixCut := [⟨64,298445024,298445204⟩]
theorem checked41416 : checkPrefixCuts (2^48) 5432410113 10 Manual.Count131072.C041416.packed 64 cuts41416 = true := by
 decide +kernel
def cuts41417 : List PrefixCut := [⟨3,16061943,16061952⟩,
⟨64,301391160,301391333⟩]
theorem checked41417 : checkPrefixCuts (2^48) 5432541185 10 Manual.Count131072.C041417.packed 64 cuts41417 = true := by
 decide +kernel
def pointBounds41417 : List (Nat × Nat × Nat) := [(5432547328,109303347100604,109303732864744)]
theorem point_links_checked41417 : (cuts41417.take 1).map (fun c => (5432541185-1+2*2^10*c.k,109303331038661+c.lower,109303716802792+c.upper)) = pointBounds41417 := by
 decide +kernel
def cuts41418 : List PrefixCut := [⟨22,107093934,107093996⟩,
⟨64,309310944,309311127⟩]
theorem checked41418 : checkPrefixCuts (2^48) 5432672257 10 Manual.Count131072.C041418.packed 64 cuts41418 = true := by
 decide +kernel
def pointBounds41418 : List (Nat × Nat × Nat) := [(5432717312,109303739523755,109304125288121)]
theorem point_links_checked41418 : (cuts41418.take 1).map (fun c => (5432672257-1+2*2^10*c.k,109303632429821+c.lower,109304018194125+c.upper)) = pointBounds41418 := by
 decide +kernel
def cuts41419 : List PrefixCut := [⟨41,194494165,194494283⟩,
⟨64,304226105,304226285⟩]
theorem checked41419 : checkPrefixCuts (2^48) 5432803329 10 Manual.Count131072.C041419.packed 64 cuts41419 = true := by
 decide +kernel
def pointBounds41419 : List (Nat × Nat × Nat) := [(5432887296,109304136234930,109304521999535)]
theorem point_links_checked41419 : (cuts41419.take 1).map (fun c => (5432803329-1+2*2^10*c.k,109303941740765+c.lower,109304327505252+c.upper)) = pointBounds41419 := by
 decide +kernel
def cuts41420 : List PrefixCut := [⟨60,284065558,284065725⟩,
⟨64,302405514,302405692⟩]
theorem checked41420 : checkPrefixCuts (2^48) 5432934401 10 Manual.Count131072.C041420.packed 64 cuts41420 = true := by
 decide +kernel
def pointBounds41420 : List (Nat × Nat × Nat) := [(5433057280,109304530032428,109304915797262)]
theorem point_links_checked41420 : (cuts41420.take 1).map (fun c => (5432934401-1+2*2^10*c.k,109304245966870+c.lower,109304631731537+c.upper)) = pointBounds41420 := by
 decide +kernel
def cuts41421 : List PrefixCut := [⟨64,302553614,302553791⟩]
theorem checked41421 : checkPrefixCuts (2^48) 5433065473 10 Manual.Count131072.C041421.packed 64 cuts41421 = true := by
 decide +kernel
def cuts41422 : List PrefixCut := [⟨15,68747028,68747067⟩,
⟨64,298764474,298764650⟩]
theorem checked41422 : checkPrefixCuts (2^48) 5433196545 10 Manual.Count131072.C041422.packed 64 cuts41422 = true := by
 decide +kernel
def pointBounds41422 : List (Nat × Nat × Nat) := [(5433227264,109304919673026,109305305438087)]
theorem point_links_checked41422 : (cuts41422.take 1).map (fun c => (5433196545-1+2*2^10*c.k,109304850925998+c.lower,109305236691020+c.upper)) = pointBounds41422 := by
 decide +kernel
def cuts41423 : List PrefixCut := [⟨34,160180815,160180907⟩,
⟨64,303005259,303005432⟩]
theorem checked41423 : checkPrefixCuts (2^48) 5433327617 10 Manual.Count131072.C041423.packed 64 cuts41423 = true := by
 decide +kernel
def pointBounds41423 : List (Nat × Nat × Nat) := [(5433397248,109305309871287,109305695636577)]
theorem point_links_checked41423 : (cuts41423.take 1).map (fun c => (5433327617-1+2*2^10*c.k,109305149690472+c.lower,109305535455670+c.upper)) = pointBounds41423 := by
 decide +kernel
def cuts41424 : List PrefixCut := [⟨53,250003589,250003737⟩,
⟨64,300770389,300770567⟩]
theorem checked41424 : checkPrefixCuts (2^48) 5433458689 10 Manual.Count131072.C041424.packed 64 cuts41424 = true := by
 decide +kernel
def pointBounds41424 : List (Nat × Nat × Nat) := [(5433567232,109305702699320,109306088464839)]
theorem point_links_checked41424 : (cuts41424.take 1).map (fun c => (5433458689-1+2*2^10*c.k,109305452695731+c.lower,109305838461102+c.upper)) = pointBounds41424 := by
 decide +kernel
def cuts41425 : List PrefixCut := [⟨64,303871274,303871452⟩]
theorem checked41425 : checkPrefixCuts (2^48) 5433589761 10 Manual.Count131072.C041425.packed 64 cuts41425 = true := by
 decide +kernel
def cuts41426 : List PrefixCut := [⟨8,37297025,37297048⟩,
⟨64,300496849,300497029⟩]
theorem checked41426 : checkPrefixCuts (2^48) 5433720833 10 Manual.Count131072.C041426.packed 64 cuts41426 = true := by
 decide +kernel
def pointBounds41426 : List (Nat × Nat × Nat) := [(5433737216,109306094634419,109306480400169)]
theorem point_links_checked41426 : (cuts41426.take 1).map (fun c => (5433720833-1+2*2^10*c.k,109306057337394+c.lower,109306443103121+c.upper)) = pointBounds41426 := by
 decide +kernel
def cuts41427 : List PrefixCut := [⟨27,126443760,126443836⟩,
⟨64,300178823,300178998⟩]
theorem checked41427 : checkPrefixCuts (2^48) 5433851905 10 Manual.Count131072.C041427.packed 64 cuts41427 = true := by
 decide +kernel
def pointBounds41427 : List (Nat × Nat × Nat) := [(5433907200,109306484278003,109306870043986)]
theorem point_links_checked41427 : (cuts41427.take 1).map (fun c => (5433851905-1+2*2^10*c.k,109306357834243+c.lower,109306743600150+c.upper)) = pointBounds41427 := by
 decide +kernel
def cuts41428 : List PrefixCut := [⟨46,214653222,214653349⟩,
⟨64,299860814,299860991⟩]
theorem checked41428 : checkPrefixCuts (2^48) 5433982977 10 Manual.Count131072.C041428.packed 64 cuts41428 = true := by
 decide +kernel
def pointBounds41428 : List (Nat × Nat × Nat) := [(5434077184,109306872666288,109307258432497)]
theorem point_links_checked41428 : (cuts41428.take 1).map (fun c => (5433982977-1+2*2^10*c.k,109306658013066+c.lower,109307043779148+c.upper)) = pointBounds41428 := by
 decide +kernel
def cuts41429 : List PrefixCut := [⟨64,304567090,304567267⟩]
theorem checked41429 : checkPrefixCuts (2^48) 5434114049 10 Manual.Count131072.C041429.packed 64 cuts41429 = true := by
 decide +kernel
def cuts41430 : List PrefixCut := [⟨1,4661684,4661687⟩,
⟨64,306217245,306217422⟩]
theorem checked41430 : checkPrefixCuts (2^48) 5434245121 10 Manual.Count131072.C041430.packed 64 cuts41430 = true := by
 decide +kernel
def pointBounds41430 : List (Nat × Nat × Nat) := [(5434247168,109307267102654,109307652869093)]
theorem point_links_checked41430 : (cuts41430.take 1).map (fun c => (5434245121-1+2*2^10*c.k,109307262440970+c.lower,109307648207406+c.upper)) = pointBounds41430 := by
 decide +kernel
def cuts41431 : List PrefixCut := [⟨20,95717268,95717325⟩,
⟨64,297249413,297249589⟩]
theorem checked41431 : checkPrefixCuts (2^48) 5434376193 10 Manual.Count131072.C041431.packed 64 cuts41431 = true := by
 decide +kernel
def pointBounds41431 : List (Nat × Nat × Nat) := [(5434417152,109307664375483,109308050142153)]
theorem point_links_checked41431 : (cuts41431.take 1).map (fun c => (5434376193-1+2*2^10*c.k,109307568658215+c.lower,109307954424828+c.upper)) = pointBounds41431 := by
 decide +kernel
def cuts41432 : List PrefixCut := [⟨39,186612434,186612544⟩,
⟨64,304337922,304338098⟩]
theorem checked41432 : checkPrefixCuts (2^48) 5434507265 10 Manual.Count131072.C041432.packed 64 cuts41432 = true := by
 decide +kernel
def pointBounds41432 : List (Nat × Nat × Nat) := [(5434587136,109308052520062,109308438286961)]
theorem point_links_checked41432 : (cuts41432.take 1).map (fun c => (5434507265-1+2*2^10*c.k,109307865907628+c.lower,109308251674417+c.upper)) = pointBounds41432 := by
 decide +kernel
def cuts41433 : List PrefixCut := [⟨58,273307403,273307562⟩,
⟨64,301689179,301689356⟩]
theorem checked41433 : checkPrefixCuts (2^48) 5434638337 10 Manual.Count131072.C041433.packed 64 cuts41433 = true := by
 decide +kernel
def pointBounds41433 : List (Nat × Nat × Nat) := [(5434757120,109308443552953,109308829320077)]
theorem point_links_checked41433 : (cuts41433.take 1).map (fun c => (5434638337-1+2*2^10*c.k,109308170245550+c.lower,109308556012515+c.upper)) = pointBounds41433 := by
 decide +kernel
def cuts41434 : List PrefixCut := [⟨64,298522653,298522831⟩]
theorem checked41434 : checkPrefixCuts (2^48) 5434769409 10 Manual.Count131072.C041434.packed 64 cuts41434 = true := by
 decide +kernel
def cuts41435 : List PrefixCut := [⟨13,63080379,63080415⟩,
⟨64,302969374,302969550⟩]
theorem checked41435 : checkPrefixCuts (2^48) 5434900481 10 Manual.Count131072.C041435.packed 64 cuts41435 = true := by
 decide +kernel
def pointBounds41435 : List (Nat × Nat × Nat) := [(5434927104,109308833537761,109309219305117)]
theorem point_links_checked41435 : (cuts41435.take 1).map (fun c => (5434900481-1+2*2^10*c.k,109308770457382+c.lower,109309156224702+c.upper)) = pointBounds41435 := by
 decide +kernel
def cuts41436 : List PrefixCut := [⟨32,151378352,151378443⟩,
⟨64,302806671,302806855⟩]
theorem checked41436 : checkPrefixCuts (2^48) 5435031553 10 Manual.Count131072.C041436.packed 64 cuts41436 = true := by
 decide +kernel
def pointBounds41436 : List (Nat × Nat × Nat) := [(5435097088,109309224805108,109309610572695)]
theorem point_links_checked41436 : (cuts41436.take 1).map (fun c => (5435031553-1+2*2^10*c.k,109309073426756+c.lower,109309459194252+c.upper)) = pointBounds41436 := by
 decide +kernel
def cuts41437 : List PrefixCut := [⟨51,239982180,239982322⟩,
⟨64,301038626,301038803⟩]
theorem checked41437 : checkPrefixCuts (2^48) 5435162625 10 Manual.Count131072.C041437.packed 64 cuts41437 = true := by
 decide +kernel
def pointBounds41437 : List (Nat × Nat × Nat) := [(5435267072,109309616215607,109310001983429)]
theorem point_links_checked41437 : (cuts41437.take 1).map (fun c => (5435162625-1+2*2^10*c.k,109309376233427+c.lower,109309762001107+c.upper)) = pointBounds41437 := by
 decide +kernel
def cuts41438 : List PrefixCut := [⟨64,304759931,304760113⟩]
theorem checked41438 : checkPrefixCuts (2^48) 5435293697 10 Manual.Count131072.C041438.packed 64 cuts41438 = true := by
 decide +kernel
def cuts41439 : List PrefixCut := [⟨6,28947929,28947946⟩,
⟨64,302111584,302111764⟩]
theorem checked41439 : checkPrefixCuts (2^48) 5435424769 10 Manual.Count131072.C041439.packed 64 cuts41439 = true := by
 decide +kernel
def pointBounds41439 : List (Nat × Nat × Nat) := [(5435437056,109310010979913,109310396747969)]
theorem point_links_checked41439 : (cuts41439.take 1).map (fun c => (5435424769-1+2*2^10*c.k,109309982031984+c.lower,109310367800023+c.upper)) = pointBounds41439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000044
