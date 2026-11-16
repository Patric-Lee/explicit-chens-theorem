import PlattAssemblyKernel
import PlattCertificates.Count131072.C014448
import PlattCertificates.Count131072.C014449
import PlattCertificates.Count131072.C014450
import PlattCertificates.Count131072.C014451
import PlattCertificates.Count131072.C014452
import PlattCertificates.Count131072.C014453
import PlattCertificates.Count131072.C014454
import PlattCertificates.Count131072.C014455
import PlattCertificates.Count131072.C014456
import PlattCertificates.Count131072.C014457
import PlattCertificates.Count131072.C014458
import PlattCertificates.Count131072.C014459
import PlattCertificates.Count131072.C014460
import PlattCertificates.Count131072.C014461
import PlattCertificates.Count131072.C014462
import PlattCertificates.Count131072.C014463
import PlattCertificates.Count131072.C014464
import PlattCertificates.Count131072.C014465
import PlattCertificates.Count131072.C014466
import PlattCertificates.Count131072.C014467
import PlattCertificates.Count131072.C014468
import PlattCertificates.Count131072.C014469
import PlattCertificates.Count131072.C014470
import PlattCertificates.Count131072.C014471
import PlattCertificates.Count131072.C014472
import PlattCertificates.Count131072.C014473
import PlattCertificates.Count131072.C014474
import PlattCertificates.Count131072.C014475
import PlattCertificates.Count131072.C014476
import PlattCertificates.Count131072.C014477
import PlattCertificates.Count131072.C014478
import PlattCertificates.Count131072.C014479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000139
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14448 : List PrefixCut := [⟨34,241771294,241771456⟩,
⟨92,650844060,650844504⟩,
⟨128,903727148,903727761⟩]
theorem checked14448 : checkPrefixCuts (2^48) 1897660417 9 Manual.Count131072.C014448.packed 128 cuts14448 = true := by
 decide +kernel
def pointBounds14448 : List (Nat × Nat × Nat) := [(1897695232,95776468486673,95776846189394),(1897754624,95776877559439,95777255262442)]
theorem point_links_checked14448 : (cuts14448.take 2).map (fun c => (1897660417-1+2*2^9*c.k,95776226715379+c.lower,95776604417938+c.upper)) = pointBounds14448 := by
 decide +kernel
def cuts14449 : List PrefixCut := [⟨22,157660122,157660228⟩,
⟨80,568932019,568932411⟩,
⟨128,917605956,917606586⟩]
theorem checked14449 : checkPrefixCuts (2^48) 1897791489 9 Manual.Count131072.C014449.packed 128 cuts14449 = true := by
 decide +kernel
def pointBounds14449 : List (Nat × Nat × Nat) := [(1897814016,95777288102649,95777665805927),(1897873408,95777699374546,95778077078110)]
theorem point_links_checked14449 : (cuts14449.take 2).map (fun c => (1897791489-1+2*2^9*c.k,95777130442527+c.lower,95777508145699+c.upper)) = pointBounds14449 := by
 decide +kernel
def cuts14450 : List PrefixCut := [⟨10,73263375,73263423⟩,
⟨68,490441718,490442044⟩,
⟨126,913687289,913687899⟩,
⟨128,926440802,926441421⟩]
theorem checked14450 : checkPrefixCuts (2^48) 1897922561 9 Manual.Count131072.C014450.packed 128 cuts14450 = true := by
 decide +kernel
def pointBounds14450 : List (Nat × Nat × Nat) := [(1897932800,95778121311858,95778499015708),(1897992192,95778538490201,95778916194329),(1898051584,95778961735772,95779339440184)]
theorem point_links_checked14450 : (cuts14450.take 3).map (fun c => (1897922561-1+2*2^9*c.k,95778048048483+c.lower,95778425752285+c.upper)) = pointBounds14450 := by
 decide +kernel
def cuts14451 : List PrefixCut := [⟨56,401284488,401284763⟩,
⟨114,810564193,810564750⟩,
⟨128,910212997,910213625⟩]
theorem checked14451 : checkPrefixCuts (2^48) 1898053633 9 Manual.Count131072.C014451.packed 128 cuts14451 = true := by
 decide +kernel
def pointBounds14451 : List (Nat × Nat × Nat) := [(1898110976,95779375773773,95779753478469),(1898170368,95779785053478,95780162758456)]
theorem point_links_checked14451 : (cuts14451.take 2).map (fun c => (1898053633-1+2*2^9*c.k,95778974489285+c.lower,95779352193706+c.upper)) = pointBounds14451 := by
 decide +kernel
def cuts14452 : List PrefixCut := [⟨44,312435549,312435760⟩,
⟨102,727324393,727324882⟩,
⟨128,912819129,912819743⟩]
theorem checked14452 : checkPrefixCuts (2^48) 1898184705 9 Manual.Count131072.C014452.packed 128 cuts14452 = true := by
 decide +kernel
def pointBounds14452 : List (Nat × Nat × Nat) := [(1898229760,95780197137831,95780574843091),(1898289152,95780612026675,95780989732213)]
theorem point_links_checked14452 : (cuts14452.take 2).map (fun c => (1898184705-1+2*2^9*c.k,95779884702282+c.lower,95780262407331+c.upper)) = pointBounds14452 := by
 decide +kernel
def cuts14453 : List PrefixCut := [⟨32,226860534,226860688⟩,
⟨90,643799286,643799723⟩,
⟨128,920466269,920466894⟩]
theorem checked14453 : checkPrefixCuts (2^48) 1898315777 9 Manual.Count131072.C014453.packed 128 cuts14453 = true := by
 decide +kernel
def pointBounds14453 : List (Nat × Nat × Nat) := [(1898348544,95781024381945,95781402087762),(1898407936,95781441320697,95781819026797)]
theorem point_links_checked14453 : (cuts14453.take 2).map (fun c => (1898315777-1+2*2^9*c.k,95780797521411+c.lower,95781175227074+c.upper)) = pointBounds14453 := by
 decide +kernel
def cuts14454 : List PrefixCut := [⟨20,136848674,136848772⟩,
⟨78,550944296,550944673⟩,
⟨128,900535793,900536406⟩]
theorem checked14454 : checkPrefixCuts (2^48) 1898446849 9 Manual.Count131072.C014454.packed 128 cuts14454 = true := by
 decide +kernel
def pointBounds14454 : List (Nat × Nat × Nat) := [(1898467328,95781854836354,95782232542740),(1898526720,95782268931976,95782646638641)]
theorem point_links_checked14454 : (cuts14454.take 2).map (fun c => (1898446849-1+2*2^9*c.k,95781717987680+c.lower,95782095693968+c.upper)) = pointBounds14454 := by
 decide +kernel
def cuts14455 : List PrefixCut := [⟨8,58264339,58264378⟩,
⟨66,470999862,471000181⟩,
⟨124,875568805,875569407⟩,
⟨128,902697745,902698364⟩]
theorem checked14455 : checkPrefixCuts (2^48) 1898577921 9 Manual.Count131072.C014455.packed 128 cuts14455 = true := by
 decide +kernel
def pointBounds14455 : List (Nat × Nat × Nat) := [(1898586112,95782676787812,95783054494752),(1898645504,95783089523335,95783467230555),(1898704896,95783494092278,95783871799781)]
theorem point_links_checked14455 : (cuts14455.take 3).map (fun c => (1898577921-1+2*2^9*c.k,95782618523473+c.lower,95782996230374+c.upper)) = pointBounds14455 := by
 decide +kernel
def cuts14456 : List PrefixCut := [⟨54,395957711,395957977⟩,
⟨112,803021303,803021851⟩,
⟨128,917014646,917015273⟩]
theorem checked14456 : checkPrefixCuts (2^48) 1898708993 9 Manual.Count131072.C014456.packed 128 cuts14456 = true := by
 decide +kernel
def pointBounds14456 : List (Nat × Nat × Nat) := [(1898764288,95783917178929,95784294886715),(1898823680,95784324242521,95784701950589)]
theorem point_links_checked14456 : (cuts14456.take 2).map (fun c => (1898708993-1+2*2^9*c.k,95783521221218+c.lower,95783898928738+c.upper)) = pointBounds14456 := by
 decide +kernel
def cuts14457 : List PrefixCut := [⟨42,290685862,290686052⟩,
⟨100,696834703,696835161⟩,
⟨128,895754079,895754671⟩]
theorem checked14457 : checkPrefixCuts (2^48) 1898840065 9 Manual.Count131072.C014457.packed 128 cuts14457 = true := by
 decide +kernel
def pointBounds14457 : List (Nat × Nat × Nat) := [(1898883072,95784728921726,95785106630063),(1898942464,95785135070567,95785512779172)]
theorem point_links_checked14457 : (cuts14457.take 2).map (fun c => (1898840065-1+2*2^9*c.k,95784438235864+c.lower,95784815944011+c.upper)) = pointBounds14457 := by
 decide +kernel
def cuts14458 : List PrefixCut := [⟨30,217592495,217592641⟩,
⟨88,627717861,627718279⟩,
⟨128,913478847,913479460⟩]
theorem checked14458 : checkPrefixCuts (2^48) 1898971137 9 Manual.Count131072.C014458.packed 128 cuts14458 = true := by
 decide +kernel
def pointBounds14458 : List (Nat × Nat × Nat) := [(1899001856,95785551582438,95785929291323),(1899061248,95785961707804,95786339416961)]
theorem point_links_checked14458 : (cuts14458.take 2).map (fun c => (1898971137-1+2*2^9*c.k,95785333989943+c.lower,95785711698682+c.upper)) = pointBounds14458 := by
 decide +kernel
def cuts14459 : List PrefixCut := [⟨18,129983667,129983754⟩,
⟨76,535192433,535192799⟩,
⟨128,902744711,902745324⟩]
theorem checked14459 : checkPrefixCuts (2^48) 1899102209 9 Manual.Count131072.C014459.packed 128 cuts14459 = true := by
 decide +kernel
def pointBounds14459 : List (Nat × Nat × Nat) := [(1899120640,95786377452457,95786755161896),(1899180032,95786782661223,95787160370941)]
theorem point_links_checked14459 : (cuts14459.take 2).map (fun c => (1899102209-1+2*2^9*c.k,95786247468790+c.lower,95786625178142+c.upper)) = pointBounds14459 := by
 decide +kernel
def cuts14460 : List PrefixCut := [⟨6,45350498,45350529⟩,
⟨64,457351188,457351498⟩,
⟨122,877934350,877934944⟩,
⟨128,920317976,920318599⟩]
theorem checked14460 : checkPrefixCuts (2^48) 1899233281 9 Manual.Count131072.C014460.packed 128 cuts14460 = true := by
 decide +kernel
def pointBounds14460 : List (Nat × Nat × Nat) := [(1899239424,95787195563999,95787573273995),(1899298816,95787607564689,95787985274964),(1899358208,95788028147851,95788405858410)]
theorem point_links_checked14460 : (cuts14460.take 3).map (fun c => (1899233281-1+2*2^9*c.k,95787150213501+c.lower,95787527923466+c.upper)) = pointBounds14460 := by
 decide +kernel
def cuts14461 : List PrefixCut := [⟨52,368553946,368554190⟩,
⟨110,775922214,775922732⟩,
⟨128,907806651,907807256⟩]
theorem checked14461 : checkPrefixCuts (2^48) 1899364353 9 Manual.Count131072.C014461.packed 128 cuts14461 = true := by
 decide +kernel
def pointBounds14461 : List (Nat × Nat × Nat) := [(1899417600,95788439085423,95788816796255),(1899476992,95788846453691,95789224164797)]
theorem point_links_checked14461 : (cuts14461.take 2).map (fun c => (1899364353-1+2*2^9*c.k,95788070531477+c.lower,95788448242065+c.upper)) = pointBounds14461 := by
 decide +kernel
def cuts14462 : List PrefixCut := [⟨40,287325725,287325923⟩,
⟨98,694520243,694520723⟩,
⟨128,914708290,914708921⟩]
theorem checked14462 : checkPrefixCuts (2^48) 1899495425 9 Manual.Count131072.C014462.packed 128 cuts14462 = true := by
 decide +kernel
def pointBounds14462 : List (Nat × Nat × Nat) := [(1899536384,95789265663853,95789643375244),(1899595776,95789672858371,95790050570044)]
theorem point_links_checked14462 : (cuts14462.take 2).map (fun c => (1899495425-1+2*2^9*c.k,95788978338128+c.lower,95789356049321+c.upper)) = pointBounds14462 := by
 decide +kernel
def cuts14463 : List PrefixCut := [⟨28,203441079,203441217⟩,
⟨86,612091876,612092292⟩,
⟨128,910348566,910349183⟩]
theorem checked14463 : checkPrefixCuts (2^48) 1899626497 9 Manual.Count131072.C014463.packed 128 cuts14463 = true := by
 decide +kernel
def pointBounds14463 : List (Nat × Nat × Nat) := [(1899655168,95790096487497,95790474199459),(1899714560,95790505138294,95790882850534)]
theorem point_links_checked14463 : (cuts14463.take 2).map (fun c => (1899626497-1+2*2^9*c.k,95789893046418+c.lower,95790270758242+c.upper)) = pointBounds14463 := by
 decide +kernel
def cuts14464 : List PrefixCut := [⟨16,115122606,115122686⟩,
⟨74,531304049,531304409⟩,
⟨128,918582605,918583229⟩]
theorem checked14464 : checkPrefixCuts (2^48) 1899757569 9 Manual.Count131072.C014464.packed 128 cuts14464 = true := by
 decide +kernel
def pointBounds14464 : List (Nat × Nat × Nat) := [(1899773952,95790918517590,95791296230111),(1899833344,95791334699033,95791712411834)]
theorem point_links_checked14464 : (cuts14464.take 2).map (fun c => (1899757569-1+2*2^9*c.k,95790803394984+c.lower,95791181107425+c.upper)) = pointBounds14464 := by
 decide +kernel
def cuts14465 : List PrefixCut := [⟨4,30371407,30371427⟩,
⟨62,440304447,440304745⟩,
⟨120,855113546,855114123⟩,
⟨128,913037640,913038256⟩]
theorem checked14465 : checkPrefixCuts (2^48) 1899888641 9 Manual.Count131072.C014465.packed 128 cuts14465 = true := by
 decide +kernel
def pointBounds14465 : List (Nat × Nat × Nat) := [(1899892736,95791752348996,95792130062081),(1899952128,95792162282036,95792539995399),(1900011520,95792577091135,95792954804777)]
theorem point_links_checked14465 : (cuts14465.take 3).map (fun c => (1899888641-1+2*2^9*c.k,95791721977589+c.lower,95792099690654+c.upper)) = pointBounds14465 := by
 decide +kernel
def cuts14466 : List PrefixCut := [⟨50,348576177,348576414⟩,
⟨108,767803404,767803923⟩,
⟨128,910752440,910753059⟩]
theorem checked14466 : checkPrefixCuts (2^48) 1900019713 9 Manual.Count131072.C014466.packed 128 cuts14466 = true := by
 decide +kernel
def pointBounds14466 : List (Nat × Nat × Nat) := [(1900070912,95792983591406,95793361305324),(1900130304,95793402818633,95793780532833)]
theorem point_links_checked14466 : (cuts14466.take 2).map (fun c => (1900019713-1+2*2^9*c.k,95792635015229+c.lower,95793012728910+c.upper)) = pointBounds14466 := by
 decide +kernel
def cuts14467 : List PrefixCut := [⟨38,276709444,276709634⟩,
⟨96,691910955,691911429⟩,
⟨128,918540643,918541269⟩]
theorem checked14467 : checkPrefixCuts (2^48) 1900150785 9 Manual.Count131072.C014467.packed 128 cuts14467 = true := by
 decide +kernel
def pointBounds14467 : List (Nat × Nat × Nat) := [(1900189696,95793822477113,95794200191603),(1900249088,95794237678624,95794615393398)]
theorem point_links_checked14467 : (cuts14467.take 2).map (fun c => (1900150785-1+2*2^9*c.k,95793545767669+c.lower,95793923481969+c.upper)) = pointBounds14467 := by
 decide +kernel
def cuts14468 : List PrefixCut := [⟨26,189595738,189595863⟩,
⟨84,604771392,604771798⟩,
⟨128,910331041,910331654⟩]
theorem checked14468 : checkPrefixCuts (2^48) 1900281857 9 Manual.Count131072.C014468.packed 128 cuts14468 = true := by
 decide +kernel
def pointBounds14468 : List (Nat × Nat × Nat) := [(1900308480,95794653904050,95795031619101),(1900367872,95795069079704,95795446795036)]
theorem point_links_checked14468 : (cuts14468.take 2).map (fun c => (1900281857-1+2*2^9*c.k,95794464308312+c.lower,95794842023238+c.upper)) = pointBounds14468 := by
 decide +kernel
def cuts14469 : List PrefixCut := [⟨14,101604774,101604844⟩,
⟨72,522678797,522679153⟩,
⟨128,921524262,921524884⟩]
theorem checked14469 : checkPrefixCuts (2^48) 1900412929 9 Manual.Count131072.C014469.packed 128 cuts14469 = true := by
 decide +kernel
def pointBounds14469 : List (Nat × Nat × Nat) := [(1900427264,95795476244127,95795853959736),(1900486656,95795897318150,95796275034045)]
theorem point_links_checked14469 : (cuts14469.take 2).map (fun c => (1900412929-1+2*2^9*c.k,95795374639353+c.lower,95795752354892+c.upper)) = pointBounds14469 := by
 decide +kernel
def cuts14470 : List PrefixCut := [⟨2,14662117,14662127⟩,
⟨60,423269441,423269726⟩,
⟨119,841638201,841638767⟩,
⟨128,904281289,904281898⟩]
theorem checked14470 : checkPrefixCuts (2^48) 1900544001 9 Manual.Count131072.C014470.packed 128 cuts14470 = true := by
 decide +kernel
def pointBounds14470 : List (Nat × Nat × Nat) := [(1900546048,95796310825732,95796688541903),(1900605440,95796719433056,95797097149502),(1900665856,95797137801816,95797515518543)]
theorem point_links_checked14470 : (cuts14470.take 3).map (fun c => (1900544001-1+2*2^9*c.k,95796296163615+c.lower,95796673879776+c.upper)) = pointBounds14470 := by
 decide +kernel
def cuts14471 : List PrefixCut := [⟨50,352750438,352750671⟩,
⟨109,774498499,774499022⟩,
⟨128,913844239,913844856⟩]
theorem checked14471 : checkPrefixCuts (2^48) 1900675073 9 Manual.Count131072.C014471.packed 128 cuts14471 = true := by
 decide +kernel
def pointBounds14471 : List (Nat × Nat × Nat) := [(1900726272,95797553195342,95797930912345),(1900786688,95797974943403,95798352660696)]
theorem point_links_checked14471 : (cuts14471.take 2).map (fun c => (1900675073-1+2*2^9*c.k,95797200444904+c.lower,95797578161674+c.upper)) = pointBounds14471 := by
 decide +kernel
def cuts14472 : List PrefixCut := [⟨40,288608441,288608636⟩,
⟨99,701741316,701741796⟩,
⟨128,904601027,904601646⟩]
theorem checked14472 : checkPrefixCuts (2^48) 1900806145 9 Manual.Count131072.C014472.packed 128 cuts14472 = true := by
 decide +kernel
def pointBounds14472 : List (Nat × Nat × Nat) := [(1900847104,95798402897584,95798780615166),(1900907520,95798816030459,95799193748326)]
theorem point_links_checked14472 : (cuts14472.take 2).map (fun c => (1900806145-1+2*2^9*c.k,95798114289143+c.lower,95798492006530+c.upper)) = pointBounds14472 := by
 decide +kernel
def cuts14473 : List PrefixCut := [⟨30,213961782,213961925⟩,
⟨89,627956690,627957112⟩,
⟨128,902317375,902317992⟩]
theorem checked14473 : checkPrefixCuts (2^48) 1900937217 9 Manual.Count131072.C014473.packed 128 cuts14473 = true := by
 decide +kernel
def pointBounds14473 : List (Nat × Nat × Nat) := [(1900967936,95799232851952,95799610570101),(1901028352,95799646846860,95800024565288)]
theorem point_links_checked14473 : (cuts14473.take 2).map (fun c => (1900937217-1+2*2^9*c.k,95799018890170+c.lower,95799396608176+c.upper)) = pointBounds14473 := by
 decide +kernel
def cuts14474 : List PrefixCut := [⟨20,142878493,142878593⟩,
⟨79,562769533,562769921⟩,
⟨128,908621720,908622343⟩]
theorem checked14474 : checkPrefixCuts (2^48) 1901068289 9 Manual.Count131072.C014474.packed 128 cuts14474 = true := by
 decide +kernel
def pointBounds14474 : List (Nat × Nat × Nat) := [(1901088768,95800064086038,95800441804761),(1901149184,95800483977078,95800861696089)]
theorem point_links_checked14474 : (cuts14474.take 2).map (fun c => (1901068289-1+2*2^9*c.k,95799921207545+c.lower,95800298926168+c.upper)) = pointBounds14474 := by
 decide +kernel
def cuts14475 : List PrefixCut := [⟨10,70324143,70324188⟩,
⟨69,497442833,497443167⟩,
⟨128,906042485,906043106⟩]
theorem checked14475 : checkPrefixCuts (2^48) 1901199361 9 Manual.Count131072.C014475.packed 128 cuts14475 = true := by
 decide +kernel
def pointBounds14475 : List (Nat × Nat × Nat) := [(1901209600,95800900153408,95801277872699),(1901270016,95801327272098,95801704991678),(1901330432,95801735871750,95802113591617)]
theorem point_links_checked14475 : (cuts14475.take 3).map (fun c => (1901199361-1+2*2^9*c.k,95800829829265+c.lower,95801207548511+c.upper)) = pointBounds14475 := by
 decide +kernel
def cuts14476 : List PrefixCut := [⟨59,417024921,417025204⟩,
⟨118,839661895,839662464⟩,
⟨128,909532619,909533236⟩]
theorem checked14476 : checkPrefixCuts (2^48) 1901330433 9 Manual.Count131072.C014476.packed 128 cuts14476 = true := by
 decide +kernel
def pointBounds14476 : List (Nat × Nat × Nat) := [(1901390848,95802152896671,95802530616821),(1901451264,95802575533645,95802953254081)]
theorem point_links_checked14476 : (cuts14476.take 2).map (fun c => (1901330433-1+2*2^9*c.k,95801735871750+c.lower,95802113591617+c.upper)) = pointBounds14476 := by
 decide +kernel
def cuts14477 : List PrefixCut := [⟨49,346979632,346979867⟩,
⟨108,756711598,756712112⟩,
⟨128,892891302,892891906⟩]
theorem checked14477 : checkPrefixCuts (2^48) 1901461505 9 Manual.Count131072.C014477.packed 128 cuts14477 = true := by
 decide +kernel
def pointBounds14477 : List (Nat × Nat × Nat) := [(1901511680,95802992384001,95803370104720),(1901572096,95803402115967,95803779836965)]
theorem point_links_checked14477 : (cuts14477.take 2).map (fun c => (1901461505-1+2*2^9*c.k,95802645404369+c.lower,95803023124853+c.upper)) = pointBounds14477 := by
 decide +kernel
def cuts14478 : List PrefixCut := [⟨39,277387664,277387852⟩,
⟨98,694938318,694938784⟩,
⟨128,905410765,905411372⟩]
theorem checked14478 : checkPrefixCuts (2^48) 1901592577 9 Manual.Count131072.C014478.packed 128 cuts14478 = true := by
 decide +kernel
def pointBounds14478 : List (Nat × Nat × Nat) := [(1901632512,95803815683335,95804193404611),(1901692928,95804233233989,95804610955543)]
theorem point_links_checked14478 : (cuts14478.take 2).map (fun c => (1901592577-1+2*2^9*c.k,95803538295671+c.lower,95803916016759+c.upper)) = pointBounds14478 := by
 decide +kernel
def cuts14479 : List PrefixCut := [⟨29,199812479,199812616⟩,
⟨88,620444733,620445160⟩,
⟨128,899576160,899576772⟩]
theorem checked14479 : checkPrefixCuts (2^48) 1901723649 9 Manual.Count131072.C014479.packed 128 cuts14479 = true := by
 decide +kernel
def pointBounds14479 : List (Nat × Nat × Nat) := [(1901753344,95804643518915,95805021240747),(1901813760,95805064151169,95805441873291)]
theorem point_links_checked14479 : (cuts14479.take 2).map (fun c => (1901723649-1+2*2^9*c.k,95804443706436+c.lower,95804821428131+c.upper)) = pointBounds14479 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000139
