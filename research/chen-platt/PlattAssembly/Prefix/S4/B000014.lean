import PlattAssemblyKernel
import PlattCertificates.Count131072.C030448
import PlattCertificates.Count131072.C030449
import PlattCertificates.Count131072.C030450
import PlattCertificates.Count131072.C030451
import PlattCertificates.Count131072.C030452
import PlattCertificates.Count131072.C030453
import PlattCertificates.Count131072.C030454
import PlattCertificates.Count131072.C030455
import PlattCertificates.Count131072.C030456
import PlattCertificates.Count131072.C030457
import PlattCertificates.Count131072.C030458
import PlattCertificates.Count131072.C030459
import PlattCertificates.Count131072.C030460
import PlattCertificates.Count131072.C030461
import PlattCertificates.Count131072.C030462
import PlattCertificates.Count131072.C030463
import PlattCertificates.Count131072.C030464
import PlattCertificates.Count131072.C030465
import PlattCertificates.Count131072.C030466
import PlattCertificates.Count131072.C030467
import PlattCertificates.Count131072.C030468
import PlattCertificates.Count131072.C030469
import PlattCertificates.Count131072.C030470
import PlattCertificates.Count131072.C030471
import PlattCertificates.Count131072.C030472
import PlattCertificates.Count131072.C030473
import PlattCertificates.Count131072.C030474
import PlattCertificates.Count131072.C030475
import PlattCertificates.Count131072.C030476
import PlattCertificates.Count131072.C030477
import PlattCertificates.Count131072.C030478
import PlattCertificates.Count131072.C030479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30448 : List PrefixCut := [⟨11,36357363,36357382⟩,
⟨128,421978613,421978845⟩]
theorem checked30448 : checkPrefixCuts (2^48) 3994812417 9 Manual.Count131072.C030448.packed 128 cuts30448 = true := by
 decide +kernel
def pointBounds30448 : List (Nat × Nat × Nat) := [(3994823680,105416587771571,105416971198896)]
theorem point_links_checked30448 : (cuts30448.take 1).map (fun c => (3994812417-1+2*2^9*c.k,105416551414208+c.lower,105416934841514+c.upper)) = pointBounds30448 := by
 decide +kernel
def cuts30449 : List PrefixCut := [⟨5,16557570,16557579⟩,
⟨127,416116974,416117208⟩,
⟨128,418723827,418724063⟩]
theorem checked30449 : checkPrefixCuts (2^48) 3994943489 9 Manual.Count131072.C030449.packed 128 cuts30449 = true := by
 decide +kernel
def pointBounds30449 : List (Nat × Nat × Nat) := [(3994948608,105416989950391,105417373377938),(3995073536,105417389509795,105417772937567)]
theorem point_links_checked30449 : (cuts30449.take 2).map (fun c => (3994943489-1+2*2^9*c.k,105416973392821+c.lower,105417356820359+c.upper)) = pointBounds30449 := by
 decide +kernel
def cuts30450 : List PrefixCut := [⟨121,392642297,392642519⟩,
⟨128,417300928,417301164⟩]
theorem checked30450 : checkPrefixCuts (2^48) 3995074561 9 Manual.Count131072.C030450.packed 128 cuts30450 = true := by
 decide +kernel
def pointBounds30450 : List (Nat × Nat × Nat) := [(3995198464,105417784758945,105418168186941)]
theorem point_links_checked30450 : (cuts30450.take 1).map (fun c => (3995074561-1+2*2^9*c.k,105417392116648+c.lower,105417775544422+c.upper)) = pointBounds30450 := by
 decide +kernel
def cuts30451 : List PrefixCut := [⟨115,370366830,370367037⟩,
⟨128,414116882,414117115⟩]
theorem checked30451 : checkPrefixCuts (2^48) 3995205633 9 Manual.Count131072.C030451.packed 128 cuts30451 = true := by
 decide +kernel
def pointBounds30451 : List (Nat × Nat × Nat) := [(3995323392,105418179784406,105418563212623)]
theorem point_links_checked30451 : (cuts30451.take 1).map (fun c => (3995205633-1+2*2^9*c.k,105417809417576+c.lower,105418192845586+c.upper)) = pointBounds30451 := by
 decide +kernel
def cuts30452 : List PrefixCut := [⟨109,354010581,354010784⟩,
⟨128,414596475,414596713⟩]
theorem checked30452 : checkPrefixCuts (2^48) 3995336705 9 Manual.Count131072.C030452.packed 128 cuts30452 = true := by
 decide +kernel
def pointBounds30452 : List (Nat × Nat × Nat) := [(3995448320,105418577545039,105418960973485)]
theorem point_links_checked30452 : (cuts30452.take 1).map (fun c => (3995336705-1+2*2^9*c.k,105418223534458+c.lower,105418606962701+c.upper)) = pointBounds30452 := by
 decide +kernel
def cuts30453 : List PrefixCut := [⟨103,334696614,334696798⟩,
⟨128,418457464,418457695⟩]
theorem checked30453 : checkPrefixCuts (2^48) 3995467777 9 Manual.Count131072.C030453.packed 128 cuts30453 = true := by
 decide +kernel
def pointBounds30453 : List (Nat × Nat × Nat) := [(3995573248,105418972827547,105419356256212)]
theorem point_links_checked30453 : (cuts30453.take 1).map (fun c => (3995467777-1+2*2^9*c.k,105418638130933+c.lower,105419021559414+c.upper)) = pointBounds30453 := by
 decide +kernel
def cuts30454 : List PrefixCut := [⟨97,317356314,317356486⟩,
⟨128,416471310,416471539⟩]
theorem checked30454 : checkPrefixCuts (2^48) 3995598849 9 Manual.Count131072.C030454.packed 128 cuts30454 = true := by
 decide +kernel
def pointBounds30454 : List (Nat × Nat × Nat) := [(3995698176,105419373944711,105419757373595)]
theorem point_links_checked30454 : (cuts30454.take 1).map (fun c => (3995598849-1+2*2^9*c.k,105419056588397+c.lower,105419440017109+c.upper)) = pointBounds30454 := by
 decide +kernel
def cuts30455 : List PrefixCut := [⟨91,297058580,297058753⟩,
⟨128,417655204,417655446⟩]
theorem checked30455 : checkPrefixCuts (2^48) 3995729921 9 Manual.Count131072.C030455.packed 128 cuts30455 = true := by
 decide +kernel
def pointBounds30455 : List (Nat × Nat × Nat) := [(3995823104,105419770118287,105420153547401)]
theorem point_links_checked30455 : (cuts30455.take 1).map (fun c => (3995729921-1+2*2^9*c.k,105419473059707+c.lower,105419856488648+c.upper)) = pointBounds30455 := by
 decide +kernel
def cuts30456 : List PrefixCut := [⟨85,277043858,277044015⟩,
⟨128,417711934,417712170⟩]
theorem checked30456 : checkPrefixCuts (2^48) 3995860993 9 Manual.Count131072.C030456.packed 128 cuts30456 = true := by
 decide +kernel
def pointBounds30456 : List (Nat × Nat × Nat) := [(3995948032,105420167758769,105420551188109)]
theorem point_links_checked30456 : (cuts30456.take 1).map (fun c => (3995860993-1+2*2^9*c.k,105419890714911+c.lower,105420274144094+c.upper)) = pointBounds30456 := by
 decide +kernel
def cuts30457 : List PrefixCut := [⟨79,256396478,256396626⟩,
⟨128,418825208,418825449⟩]
theorem checked30457 : checkPrefixCuts (2^48) 3995992065 9 Manual.Count131072.C030457.packed 128 cuts30457 = true := by
 decide +kernel
def pointBounds30457 : List (Nat × Nat × Nat) := [(3996072960,105420564823323,105420948252890)]
theorem point_links_checked30457 : (cuts30457.take 1).map (fun c => (3995992065-1+2*2^9*c.k,105420308426845+c.lower,105420691856264+c.upper)) = pointBounds30457 := by
 decide +kernel
def cuts30458 : List PrefixCut := [⟨73,244625411,244625544⟩,
⟨128,421065543,421065774⟩]
theorem checked30458 : checkPrefixCuts (2^48) 3996123137 9 Manual.Count131072.C030458.packed 128 cuts30458 = true := by
 decide +kernel
def pointBounds30458 : List (Nat × Nat × Nat) := [(3996197888,105420971877464,105421355307257)]
theorem point_links_checked30458 : (cuts30458.take 1).map (fun c => (3996123137-1+2*2^9*c.k,105420727252053+c.lower,105421110681713+c.upper)) = pointBounds30458 := by
 decide +kernel
def cuts30459 : List PrefixCut := [⟨67,218416036,218416161⟩,
⟨128,418938567,418938806⟩]
theorem checked30459 : checkPrefixCuts (2^48) 3996254209 9 Manual.Count131072.C030459.packed 128 cuts30459 = true := by
 decide +kernel
def pointBounds30459 : List (Nat × Nat × Nat) := [(3996322816,105421366733632,105421750163648)]
theorem point_links_checked30459 : (cuts30459.take 1).map (fun c => (3996254209-1+2*2^9*c.k,105421148317596+c.lower,105421531747487+c.upper)) = pointBounds30459 := by
 decide +kernel
def cuts30460 : List PrefixCut := [⟨61,200801119,200801234⟩,
⟨128,418431895,418432129⟩]
theorem checked30460 : checkPrefixCuts (2^48) 3996385281 9 Manual.Count131072.C030460.packed 128 cuts30460 = true := by
 decide +kernel
def pointBounds30460 : List (Nat × Nat × Nat) := [(3996447744,105421768057282,105422151487527)]
theorem point_links_checked30460 : (cuts30460.take 1).map (fun c => (3996385281-1+2*2^9*c.k,105421567256163+c.lower,105421950686293+c.upper)) = pointBounds30460 := by
 decide +kernel
def cuts30461 : List PrefixCut := [⟨55,183187286,183187390⟩,
⟨128,419404162,419404403⟩]
theorem checked30461 : checkPrefixCuts (2^48) 3996516353 9 Manual.Count131072.C030461.packed 128 cuts30461 = true := by
 decide +kernel
def pointBounds30461 : List (Nat × Nat × Nat) := [(3996572672,105422168875344,105422552305812)]
theorem point_links_checked30461 : (cuts30461.take 1).map (fun c => (3996516353-1+2*2^9*c.k,105421985688058+c.lower,105422369118422+c.upper)) = pointBounds30461 := by
 decide +kernel
def cuts30462 : List PrefixCut := [⟨49,161912386,161912476⟩,
⟨128,423122962,423123196⟩]
theorem checked30462 : checkPrefixCuts (2^48) 3996647425 9 Manual.Count131072.C030462.packed 128 cuts30462 = true := by
 decide +kernel
def pointBounds30462 : List (Nat × Nat × Nat) := [(3996697600,105422567004606,105422950435301)]
theorem point_links_checked30462 : (cuts30462.take 1).map (fun c => (3996647425-1+2*2^9*c.k,105422405092220+c.lower,105422788522825+c.upper)) = pointBounds30462 := by
 decide +kernel
def cuts30463 : List PrefixCut := [⟨43,138244381,138244462⟩,
⟨128,415432827,415433065⟩]
theorem checked30463 : checkPrefixCuts (2^48) 3996778497 9 Manual.Count131072.C030463.packed 128 cuts30463 = true := by
 decide +kernel
def pointBounds30463 : List (Nat × Nat × Nat) := [(3996822528,105422966459563,105423349890483)]
theorem point_links_checked30463 : (cuts30463.take 1).map (fun c => (3996778497-1+2*2^9*c.k,105422828215182+c.lower,105423211646021+c.upper)) = pointBounds30463 := by
 decide +kernel
def cuts30464 : List PrefixCut := [⟨37,121549761,121549830⟩,
⟨128,418165701,418165939⟩]
theorem checked30464 : checkPrefixCuts (2^48) 3996909569 9 Manual.Count131072.C030464.packed 128 cuts30464 = true := by
 decide +kernel
def pointBounds30464 : List (Nat × Nat × Nat) := [(3996947456,105423365197770,105423748628916)]
theorem point_links_checked30464 : (cuts30464.take 1).map (fun c => (3996909569-1+2*2^9*c.k,105423243648009+c.lower,105423627079086+c.upper)) = pointBounds30464 := by
 decide +kernel
def cuts30465 : List PrefixCut := [⟨31,101898527,101898584⟩,
⟨128,418574471,418574705⟩]
theorem checked30465 : checkPrefixCuts (2^48) 3997040641 9 Manual.Count131072.C030465.packed 128 cuts30465 = true := by
 decide +kernel
def pointBounds30465 : List (Nat × Nat × Nat) := [(3997072384,105423763712237,105424147143609)]
theorem point_links_checked30465 : (cuts30465.take 1).map (fun c => (3997040641-1+2*2^9*c.k,105423661813710+c.lower,105424045245025+c.upper)) = pointBounds30465 := by
 decide +kernel
def cuts30466 : List PrefixCut := [⟨25,83164001,83164045⟩,
⟨128,421025448,421025686⟩]
theorem checked30466 : checkPrefixCuts (2^48) 3997171713 9 Manual.Count131072.C030466.packed 128 cuts30466 = true := by
 decide +kernel
def pointBounds30466 : List (Nat × Nat × Nat) := [(3997197312,105424163552182,105424546983775)]
theorem point_links_checked30466 : (cuts30466.take 1).map (fun c => (3997171713-1+2*2^9*c.k,105424080388181+c.lower,105424463819730+c.upper)) = pointBounds30466 := by
 decide +kernel
def cuts30467 : List PrefixCut := [⟨19,61050700,61050735⟩,
⟨128,419955381,419955617⟩]
theorem checked30467 : checkPrefixCuts (2^48) 3997302785 9 Manual.Count131072.C030467.packed 128 cuts30467 = true := by
 decide +kernel
def pointBounds30467 : List (Nat × Nat × Nat) := [(3997322240,105424562464329,105424945896151)]
theorem point_links_checked30467 : (cuts30467.take 1).map (fun c => (3997302785-1+2*2^9*c.k,105424501413629+c.lower,105424884845416+c.upper)) = pointBounds30467 := by
 decide +kernel
def cuts30468 : List PrefixCut := [⟨13,41755374,41755398⟩,
⟨128,415223962,415224198⟩]
theorem checked30468 : checkPrefixCuts (2^48) 3997433857 9 Manual.Count131072.C030468.packed 128 cuts30468 = true := by
 decide +kernel
def pointBounds30468 : List (Nat × Nat × Nat) := [(3997447168,105424963124384,105425346556431)]
theorem point_links_checked30468 : (cuts30468.take 1).map (fun c => (3997433857-1+2*2^9*c.k,105424921369010+c.lower,105425304801033+c.upper)) = pointBounds30468 := by
 decide +kernel
def cuts30469 : List PrefixCut := [⟨7,23939919,23939932⟩,
⟨128,420350365,420350598⟩]
theorem checked30469 : checkPrefixCuts (2^48) 3997564929 9 Manual.Count131072.C030469.packed 128 cuts30469 = true := by
 decide +kernel
def pointBounds30469 : List (Nat × Nat × Nat) := [(3997572096,105425360532891,105425743965163)]
theorem point_links_checked30469 : (cuts30469.take 1).map (fun c => (3997564929-1+2*2^9*c.k,105425336592972+c.lower,105425720025231+c.upper)) = pointBounds30469 := by
 decide +kernel
def cuts30470 : List PrefixCut := [⟨1,3450054,3450056⟩,
⟨123,399988802,399989027⟩,
⟨128,416041602,416041836⟩]
theorem checked30470 : checkPrefixCuts (2^48) 3997696001 9 Manual.Count131072.C030470.packed 128 cuts30470 = true := by
 decide +kernel
def pointBounds30470 : List (Nat × Nat × Nat) := [(3997697024,105425760393391,105426143825885),(3997821952,105426156932139,105426540364856)]
theorem point_links_checked30470 : (cuts30470.take 2).map (fun c => (3997696001-1+2*2^9*c.k,105425756943337+c.lower,105426140375829+c.upper)) = pointBounds30470 := by
 decide +kernel
def cuts30471 : List PrefixCut := [⟨118,387302831,387303048⟩,
⟨128,419618613,419618850⟩]
theorem checked30471 : checkPrefixCuts (2^48) 3997827073 9 Manual.Count131072.C030471.packed 128 cuts30471 = true := by
 decide +kernel
def pointBounds30471 : List (Nat × Nat × Nat) := [(3997947904,105426560287770,105426943720713)]
theorem point_links_checked30471 : (cuts30471.take 1).map (fun c => (3997827073-1+2*2^9*c.k,105426172984939+c.lower,105426556417665+c.upper)) = pointBounds30471 := by
 decide +kernel
def cuts30472 : List PrefixCut := [⟨113,364620466,364620672⟩,
⟨128,413620602,413620836⟩]
theorem checked30472 : checkPrefixCuts (2^48) 3997958145 9 Manual.Count131072.C030472.packed 128 cuts30472 = true := by
 decide +kernel
def pointBounds30472 : List (Nat × Nat × Nat) := [(3998073856,105426957224018,105427340657187)]
theorem point_links_checked30472 : (cuts30472.take 1).map (fun c => (3997958145-1+2*2^9*c.k,105426592603552+c.lower,105426976036515+c.upper)) = pointBounds30472 := by
 decide +kernel
def cuts30473 : List PrefixCut := [⟨108,354752584,354752787⟩,
⟨128,420435998,420436238⟩]
theorem checked30473 : checkPrefixCuts (2^48) 3998089217 9 Manual.Count131072.C030473.packed 128 cuts30473 = true := by
 decide +kernel
def pointBounds30473 : List (Nat × Nat × Nat) := [(3998199808,105427360976738,105427744410138)]
theorem point_links_checked30473 : (cuts30473.take 1).map (fun c => (3998089217-1+2*2^9*c.k,105427006224154+c.lower,105427389657351+c.upper)) = pointBounds30473 := by
 decide +kernel
def cuts30474 : List PrefixCut := [⟨103,335099794,335099982⟩,
⟨128,416550239,416550473⟩]
theorem checked30474 : checkPrefixCuts (2^48) 3998220289 9 Manual.Count131072.C030474.packed 128 cuts30474 = true := by
 decide +kernel
def pointBounds30474 : List (Nat × Nat × Nat) := [(3998325760,105427761759946,105428145193571)]
theorem point_links_checked30474 : (cuts30474.take 1).map (fun c => (3998220289-1+2*2^9*c.k,105427426660152+c.lower,105427810093589+c.upper)) = pointBounds30474 := by
 decide +kernel
def cuts30475 : List PrefixCut := [⟨98,319812919,319813098⟩,
⟨128,417944523,417944759⟩]
theorem checked30475 : checkPrefixCuts (2^48) 3998351361 9 Manual.Count131072.C030475.packed 128 cuts30475 = true := by
 decide +kernel
def pointBounds30475 : List (Nat × Nat × Nat) := [(3998451712,105428163023310,105428546457160)]
theorem point_links_checked30475 : (cuts30475.take 1).map (fun c => (3998351361-1+2*2^9*c.k,105427843210391+c.lower,105428226644062+c.upper)) = pointBounds30475 := by
 decide +kernel
def cuts30476 : List PrefixCut := [⟨93,302626397,302626568⟩,
⟨128,416452587,416452821⟩]
theorem checked30476 : checkPrefixCuts (2^48) 3998482433 9 Manual.Count131072.C030476.packed 128 cuts30476 = true := by
 decide +kernel
def pointBounds30476 : List (Nat × Nat × Nat) := [(3998577664,105428563781311,105428947215389)]
theorem point_links_checked30476 : (cuts30476.take 1).map (fun c => (3998482433-1+2*2^9*c.k,105428261154914+c.lower,105428644588821+c.upper)) = pointBounds30476 := by
 decide +kernel
def cuts30477 : List PrefixCut := [⟨88,295436610,295436779⟩,
⟨128,424956375,424956623⟩]
theorem checked30477 : checkPrefixCuts (2^48) 3998613505 9 Manual.Count131072.C030477.packed 128 cuts30477 = true := by
 decide +kernel
def pointBounds30477 : List (Nat × Nat × Nat) := [(3998703616,105428973044111,105429356478421)]
theorem point_links_checked30477 : (cuts30477.take 1).map (fun c => (3998613505-1+2*2^9*c.k,105428677607501+c.lower,105429061041642+c.upper)) = pointBounds30477 := by
 decide +kernel
def cuts30478 : List PrefixCut := [⟨83,269453193,269453343⟩,
⟨128,417199526,417199761⟩]
theorem checked30478 : checkPrefixCuts (2^48) 3998744577 9 Manual.Count131072.C030478.packed 128 cuts30478 = true := by
 decide +kernel
def pointBounds30478 : List (Nat × Nat × Nat) := [(3998829568,105429372017069,105429755451608)]
theorem point_links_checked30478 : (cuts30478.take 1).map (fun c => (3998744577-1+2*2^9*c.k,105429102563876+c.lower,105429485998265+c.upper)) = pointBounds30478 := by
 decide +kernel
def cuts30479 : List PrefixCut := [⟨78,254803865,254804012⟩,
⟨128,413525778,413526020⟩]
theorem checked30479 : checkPrefixCuts (2^48) 3998875649 9 Manual.Count131072.C030479.packed 128 cuts30479 = true := by
 decide +kernel
def pointBounds30479 : List (Nat × Nat × Nat) := [(3998955520,105429774567267,105430158002038)]
theorem point_links_checked30479 : (cuts30479.take 1).map (fun c => (3998875649-1+2*2^9*c.k,105429519763402+c.lower,105429903198026+c.upper)) = pointBounds30479 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000014
