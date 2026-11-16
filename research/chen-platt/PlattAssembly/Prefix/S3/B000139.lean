import PlattAssemblyKernel
import PlattCertificates.Count131072.C024448
import PlattCertificates.Count131072.C024449
import PlattCertificates.Count131072.C024450
import PlattCertificates.Count131072.C024451
import PlattCertificates.Count131072.C024452
import PlattCertificates.Count131072.C024453
import PlattCertificates.Count131072.C024454
import PlattCertificates.Count131072.C024455
import PlattCertificates.Count131072.C024456
import PlattCertificates.Count131072.C024457
import PlattCertificates.Count131072.C024458
import PlattCertificates.Count131072.C024459
import PlattCertificates.Count131072.C024460
import PlattCertificates.Count131072.C024461
import PlattCertificates.Count131072.C024462
import PlattCertificates.Count131072.C024463
import PlattCertificates.Count131072.C024464
import PlattCertificates.Count131072.C024465
import PlattCertificates.Count131072.C024466
import PlattCertificates.Count131072.C024467
import PlattCertificates.Count131072.C024468
import PlattCertificates.Count131072.C024469
import PlattCertificates.Count131072.C024470
import PlattCertificates.Count131072.C024471
import PlattCertificates.Count131072.C024472
import PlattCertificates.Count131072.C024473
import PlattCertificates.Count131072.C024474
import PlattCertificates.Count131072.C024475
import PlattCertificates.Count131072.C024476
import PlattCertificates.Count131072.C024477
import PlattCertificates.Count131072.C024478
import PlattCertificates.Count131072.C024479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000139
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24448 : List PrefixCut := [⟨60,252487843,252487986⟩,
⟨128,531727739,531728044⟩]
theorem checked24448 : checkPrefixCuts (2^48) 3208380417 9 Manual.Count131072.C024448.packed 128 cuts24448 = true := by
 decide +kernel
def pointBounds24448 : List (Nat × Nat × Nat) := [(3208441856,102611716920138,102612098775566)]
theorem point_links_checked24448 : (cuts24448.take 1).map (fun c => (3208380417-1+2*2^9*c.k,102611464432295+c.lower,102611846287580+c.upper)) = pointBounds24448 := by
 decide +kernel
def cuts24449 : List PrefixCut := [⟨30,122028465,122028538⟩,
⟨128,527231862,527232168⟩]
theorem checked24449 : checkPrefixCuts (2^48) 3208511489 9 Manual.Count131072.C024449.packed 128 cuts24449 = true := by
 decide +kernel
def pointBounds24449 : List (Nat × Nat × Nat) := [(3208542208,102612118188499,102612500044162),(3208642560,102612523391896,102612905247792)]
theorem point_links_checked24449 : (cuts24449.take 2).map (fun c => (3208511489-1+2*2^9*c.k,102611996160034+c.lower,102612378015624+c.upper)) = pointBounds24449 := by
 decide +kernel
def cuts24450 : List PrefixCut := [⟨98,403874967,403875201⟩,
⟨128,525105134,525105438⟩]
theorem checked24450 : checkPrefixCuts (2^48) 3208642561 9 Manual.Count131072.C024450.packed 128 cuts24450 = true := by
 decide +kernel
def pointBounds24450 : List (Nat × Nat × Nat) := [(3208742912,102612927266863,102613309122993)]
theorem point_links_checked24450 : (cuts24450.take 1).map (fun c => (3208642561-1+2*2^9*c.k,102612523391896+c.lower,102612905247792+c.upper)) = pointBounds24450 := by
 decide +kernel
def cuts24451 : List PrefixCut := [⟨68,283947844,283948004⟩,
⟨128,531750221,531750522⟩]
theorem checked24451 : checkPrefixCuts (2^48) 3208773633 9 Manual.Count131072.C024451.packed 128 cuts24451 = true := by
 decide +kernel
def pointBounds24451 : List (Nat × Nat × Nat) := [(3208843264,102613332444874,102613714301234)]
theorem point_links_checked24451 : (cuts24451.take 1).map (fun c => (3208773633-1+2*2^9*c.k,102613048497030+c.lower,102613430353230+c.upper)) = pointBounds24451 := by
 decide +kernel
def cuts24452 : List PrefixCut := [⟨38,155871851,155871939⟩,
⟨128,523658679,523658974⟩]
theorem checked24452 : checkPrefixCuts (2^48) 3208904705 9 Manual.Count131072.C024452.packed 128 cuts24452 = true := by
 decide +kernel
def pointBounds24452 : List (Nat × Nat × Nat) := [(3208943616,102613736119102,102614117975691)]
theorem point_links_checked24452 : (cuts24452.take 1).map (fun c => (3208904705-1+2*2^9*c.k,102613580247251+c.lower,102613962103752+c.upper)) = pointBounds24452 := by
 decide +kernel
def cuts24453 : List PrefixCut := [⟨8,32453855,32453873⟩,
⟨106,435664286,435664536⟩,
⟨128,525917837,525918142⟩]
theorem checked24453 : checkPrefixCuts (2^48) 3209035777 9 Manual.Count131072.C024453.packed 128 cuts24453 = true := by
 decide +kernel
def pointBounds24453 : List (Nat × Nat × Nat) := [(3209043968,102614136359785,102614518216599),(3209144320,102614539570216,102614921427262)]
theorem point_links_checked24453 : (cuts24453.take 2).map (fun c => (3209035777-1+2*2^9*c.k,102614103905930+c.lower,102614485762726+c.upper)) = pointBounds24453 := by
 decide +kernel
def cuts24454 : List PrefixCut := [⟨76,307067781,307067959⟩,
⟨128,518002612,518002909⟩]
theorem checked24454 : checkPrefixCuts (2^48) 3209166849 9 Manual.Count131072.C024454.packed 128 cuts24454 = true := by
 decide +kernel
def pointBounds24454 : List (Nat × Nat × Nat) := [(3209244672,102614936891548,102615318748827)]
theorem point_links_checked24454 : (cuts24454.take 1).map (fun c => (3209166849-1+2*2^9*c.k,102614629823767+c.lower,102615011680868+c.upper)) = pointBounds24454 := by
 decide +kernel
def cuts24455 : List PrefixCut := [⟨46,188654356,188654461⟩,
⟨128,528593688,528593983⟩]
theorem checked24455 : checkPrefixCuts (2^48) 3209297921 9 Manual.Count131072.C024455.packed 128 cuts24455 = true := by
 decide +kernel
def pointBounds24455 : List (Nat × Nat × Nat) := [(3209345024,102615336480735,102615718338238)]
theorem point_links_checked24455 : (cuts24455.take 1).map (fun c => (3209297921-1+2*2^9*c.k,102615147826379+c.lower,102615529683777+c.upper)) = pointBounds24455 := by
 decide +kernel
def cuts24456 : List PrefixCut := [⟨16,66916825,66916863⟩,
⟨114,462973042,462973305⟩,
⟨128,521205250,521205546⟩]
theorem checked24456 : checkPrefixCuts (2^48) 3209428993 9 Manual.Count131072.C024456.packed 128 cuts24456 = true := by
 decide +kernel
def pointBounds24456 : List (Nat × Nat × Nat) := [(3209445376,102615743336892,102616125194623),(3209545728,102616139393109,102616521251065)]
theorem point_links_checked24456 : (cuts24456.take 2).map (fun c => (3209428993-1+2*2^9*c.k,102615676420067+c.lower,102616058277760+c.upper)) = pointBounds24456 := by
 decide +kernel
def cuts24457 : List PrefixCut := [⟨84,343599726,343599921⟩,
⟨128,524691841,524692134⟩]
theorem checked24457 : checkPrefixCuts (2^48) 3209560065 9 Manual.Count131072.C024457.packed 128 cuts24457 = true := by
 decide +kernel
def pointBounds24457 : List (Nat × Nat × Nat) := [(3209646080,102616541225043,102616923083227)]
theorem point_links_checked24457 : (cuts24457.take 1).map (fun c => (3209560065-1+2*2^9*c.k,102616197625317+c.lower,102616579483306+c.upper)) = pointBounds24457 := by
 decide +kernel
def cuts24458 : List PrefixCut := [⟨54,226427359,226427488⟩,
⟨128,529493580,529493885⟩]
theorem checked24458 : checkPrefixCuts (2^48) 3209691137 9 Manual.Count131072.C024458.packed 128 cuts24458 = true := by
 decide +kernel
def pointBounds24458 : List (Nat × Nat × Nat) := [(3209746432,102616948744517,102617330602928)]
theorem point_links_checked24458 : (cuts24458.take 1).map (fun c => (3209691137-1+2*2^9*c.k,102616722317158+c.lower,102617104175440+c.upper)) = pointBounds24458 := by
 decide +kernel
def cuts24459 : List PrefixCut := [⟨24,99266671,99266726⟩,
⟨122,495097952,495098226⟩,
⟨128,520439853,520440141⟩]
theorem checked24459 : checkPrefixCuts (2^48) 3209822209 9 Manual.Count131072.C024459.packed 128 cuts24459 = true := by
 decide +kernel
def pointBounds24459 : List (Nat × Nat × Nat) := [(3209846784,102617351077409,102617732936051),(3209947136,102617746908690,102618128767551)]
theorem point_links_checked24459 : (cuts24459.take 2).map (fun c => (3209822209-1+2*2^9*c.k,102617251810738+c.lower,102617633669325+c.upper)) = pointBounds24459 := by
 decide +kernel
def cuts24460 : List PrefixCut := [⟨92,377141228,377141436⟩,
⟨128,527345761,527346050⟩]
theorem checked24460 : checkPrefixCuts (2^48) 3209953281 9 Manual.Count131072.C024460.packed 128 cuts24460 = true := by
 decide +kernel
def pointBounds24460 : List (Nat × Nat × Nat) := [(3210047488,102618149391819,102618531250902)]
theorem point_links_checked24460 : (cuts24460.take 1).map (fun c => (3209953281-1+2*2^9*c.k,102617772250591+c.lower,102618154109466+c.upper)) = pointBounds24460 := by
 decide +kernel
def cuts24461 : List PrefixCut := [⟨62,252178362,252178506⟩,
⟨128,524956838,524957137⟩]
theorem checked24461 : checkPrefixCuts (2^48) 3210084353 9 Manual.Count131072.C024461.packed 128 cuts24461 = true := by
 decide +kernel
def pointBounds24461 : List (Nat × Nat × Nat) := [(3210147840,102618551774714,102618933634022)]
theorem point_links_checked24461 : (cuts24461.take 1).map (fun c => (3210084353-1+2*2^9*c.k,102618299596352+c.lower,102618681455516+c.upper)) = pointBounds24461 := by
 decide +kernel
def cuts24462 : List PrefixCut := [⟨32,128802722,128802795⟩,
⟨128,525110785,525111074⟩]
theorem checked24462 : checkPrefixCuts (2^48) 3210215425 9 Manual.Count131072.C024462.packed 128 cuts24462 = true := by
 decide +kernel
def pointBounds24462 : List (Nat × Nat × Nat) := [(3210248192,102618953355912,102619335215448)]
theorem point_links_checked24462 : (cuts24462.take 1).map (fun c => (3210215425-1+2*2^9*c.k,102618824553190+c.lower,102619206412653+c.upper)) = pointBounds24462 := by
 decide +kernel
def cuts24463 : List PrefixCut := [⟨2,7364901,7364905⟩,
⟨100,405501580,405501808⟩,
⟨128,516672508,516672801⟩]
theorem checked24463 : checkPrefixCuts (2^48) 3210346497 9 Manual.Count131072.C024463.packed 128 cuts24463 = true := by
 decide +kernel
def pointBounds24463 : List (Nat × Nat × Nat) := [(3210348544,102619357028876,102619738888632),(3210448896,102619755165555,102620137025535)]
theorem point_links_checked24463 : (cuts24463.take 2).map (fun c => (3210346497-1+2*2^9*c.k,102619349663975+c.lower,102619731523727+c.upper)) = pointBounds24463 := by
 decide +kernel
def cuts24464 : List PrefixCut := [⟨70,288882070,288882231⟩,
⟨128,526383036,526383332⟩]
theorem checked24464 : checkPrefixCuts (2^48) 3210477569 9 Manual.Count131072.C024464.packed 128 cuts24464 = true := by
 decide +kernel
def pointBounds24464 : List (Nat × Nat × Nat) := [(3210549248,102620155218553,102620537078759)]
theorem point_links_checked24464 : (cuts24464.take 1).map (fun c => (3210477569-1+2*2^9*c.k,102619866336483+c.lower,102620248196528+c.upper)) = pointBounds24464 := by
 decide +kernel
def cuts24465 : List PrefixCut := [⟨40,162451977,162452071⟩,
⟨128,524082056,524082355⟩]
theorem checked24465 : checkPrefixCuts (2^48) 3210608641 9 Manual.Count131072.C024465.packed 128 cuts24465 = true := by
 decide +kernel
def pointBounds24465 : List (Nat × Nat × Nat) := [(3210649600,102620555171496,102620937031931)]
theorem point_links_checked24465 : (cuts24465.take 1).map (fun c => (3210608641-1+2*2^9*c.k,102620392719519+c.lower,102620774579860+c.upper)) = pointBounds24465 := by
 decide +kernel
def cuts24466 : List PrefixCut := [⟨10,41641608,41641629⟩,
⟨108,443322787,443323036⟩,
⟨128,526427676,526427970⟩]
theorem checked24466 : checkPrefixCuts (2^48) 3210739713 9 Manual.Count131072.C024466.packed 128 cuts24466 = true := by
 decide +kernel
def pointBounds24466 : List (Nat × Nat × Nat) := [(3210749952,102620958443183,102621340303844),(3210850304,102621360124362,102621741985251)]
theorem point_links_checked24466 : (cuts24466.take 2).map (fun c => (3210739713-1+2*2^9*c.k,102620916801575+c.lower,102621298662215+c.upper)) = pointBounds24466 := by
 decide +kernel
def cuts24467 : List PrefixCut := [⟨78,317950129,317950312⟩,
⟨128,521672516,521672812⟩]
theorem checked24467 : checkPrefixCuts (2^48) 3210870785 9 Manual.Count131072.C024467.packed 128 cuts24467 = true := by
 decide +kernel
def pointBounds24467 : List (Nat × Nat × Nat) := [(3210950656,102621761179380,102622143040497)]
theorem point_links_checked24467 : (cuts24467.take 1).map (fun c => (3210870785-1+2*2^9*c.k,102621443229251+c.lower,102621825090185+c.upper)) = pointBounds24467 := by
 decide +kernel
def cuts24468 : List PrefixCut := [⟨48,195917551,195917665⟩,
⟨128,524894549,524894848⟩]
theorem checked24468 : checkPrefixCuts (2^48) 3211001857 9 Manual.Count131072.C024468.packed 128 cuts24468 = true := by
 decide +kernel
def pointBounds24468 : List (Nat × Nat × Nat) := [(3211051008,102622160819318,102622542680662)]
theorem point_links_checked24468 : (cuts24468.take 1).map (fun c => (3211001857-1+2*2^9*c.k,102621964901767+c.lower,102622346762997+c.upper)) = pointBounds24468 := by
 decide +kernel
def cuts24469 : List PrefixCut := [⟨18,71088770,71088809⟩,
⟨116,477014810,477015081⟩,
⟨128,527327362,527327661⟩]
theorem checked24469 : checkPrefixCuts (2^48) 3211132929 9 Manual.Count131072.C024469.packed 128 cuts24469 = true := by
 decide +kernel
def pointBounds24469 : List (Nat × Nat × Nat) := [(3211151360,102622560885086,102622942746654),(3211251712,102622966811126,102623348672926)]
theorem point_links_checked24469 : (cuts24469.take 2).map (fun c => (3211132929-1+2*2^9*c.k,102622489796316+c.lower,102622871657845+c.upper)) = pointBounds24469 := by
 decide +kernel
def cuts24470 : List PrefixCut := [⟨86,352620624,352620831⟩,
⟨128,523624569,523624877⟩]
theorem checked24470 : checkPrefixCuts (2^48) 3211264001 9 Manual.Count131072.C024470.packed 128 cuts24470 = true := by
 decide +kernel
def pointBounds24470 : List (Nat × Nat × Nat) := [(3211352064,102623369744302,102623751606337)]
theorem point_links_checked24470 : (cuts24470.take 1).map (fun c => (3211264001-1+2*2^9*c.k,102623017123678+c.lower,102623398985506+c.upper)) = pointBounds24470 := by
 decide +kernel
def cuts24471 : List PrefixCut := [⟨57,233494285,233494418⟩,
⟨128,524129098,524129396⟩]
theorem checked24471 : checkPrefixCuts (2^48) 3211395073 9 Manual.Count131072.C024471.packed 128 cuts24471 = true := by
 decide +kernel
def pointBounds24471 : List (Nat × Nat × Nat) := [(3211453440,102623774242532,102624156104801)]
theorem point_links_checked24471 : (cuts24471.take 1).map (fun c => (3211395073-1+2*2^9*c.k,102623540748247+c.lower,102623922610383+c.upper)) = pointBounds24471 := by
 decide +kernel
def cuts24472 : List PrefixCut := [⟨28,117005826,117005891⟩,
⟨127,517534467,517534763⟩,
⟨128,520952491,520952789⟩]
theorem checked24472 : checkPrefixCuts (2^48) 3211526145 9 Manual.Count131072.C024472.packed 128 cuts24472 = true := by
 decide +kernel
def pointBounds24472 : List (Nat × Nat × Nat) := [(3211554816,102624181883171,102624563745670),(3211656192,102624582411812,102624964274542)]
theorem point_links_checked24472 : (cuts24472.take 2).map (fun c => (3211526145-1+2*2^9*c.k,102624064877345+c.lower,102624446739779+c.upper)) = pointBounds24472 := by
 decide +kernel
def cuts24473 : List PrefixCut := [⟨98,402882312,402882537⟩,
⟨128,527066034,527066334⟩]
theorem checked24473 : checkPrefixCuts (2^48) 3211657217 9 Manual.Count131072.C024473.packed 128 cuts24473 = true := by
 decide +kernel
def pointBounds24473 : List (Nat × Nat × Nat) := [(3211757568,102624988712148,102625370575105)]
theorem point_links_checked24473 : (cuts24473.take 1).map (fun c => (3211657217-1+2*2^9*c.k,102624585829836+c.lower,102624967692568+c.upper)) = pointBounds24473 := by
 decide +kernel
def cuts24474 : List PrefixCut := [⟨69,284382359,284382521⟩,
⟨128,526869280,526869576⟩]
theorem checked24474 : checkPrefixCuts (2^48) 3211788289 9 Manual.Count131072.C024474.packed 128 cuts24474 = true := by
 decide +kernel
def pointBounds24474 : List (Nat × Nat × Nat) := [(3211858944,102625397278229,102625779141423)]
theorem point_links_checked24474 : (cuts24474.take 1).map (fun c => (3211788289-1+2*2^9*c.k,102625112895870+c.lower,102625494758902+c.upper)) = pointBounds24474 := by
 decide +kernel
def cuts24475 : List PrefixCut := [⟨40,163437275,163437364⟩,
⟨128,523254876,523255163⟩]
theorem checked24475 : checkPrefixCuts (2^48) 3211919361 9 Manual.Count131072.C024475.packed 128 cuts24475 = true := by
 decide +kernel
def pointBounds24475 : List (Nat × Nat × Nat) := [(3211960320,102625803202425,102626185065842)]
theorem point_links_checked24475 : (cuts24475.take 1).map (fun c => (3211919361-1+2*2^9*c.k,102625639765150+c.lower,102626021628478+c.upper)) = pointBounds24475 := by
 decide +kernel
def cuts24476 : List PrefixCut := [⟨11,47232978,47233004⟩,
⟨110,450064479,450064726⟩,
⟨128,526475738,526476028⟩]
theorem checked24476 : checkPrefixCuts (2^48) 3212050433 9 Manual.Count131072.C024476.packed 128 cuts24476 = true := by
 decide +kernel
def pointBounds24476 : List (Nat × Nat × Nat) := [(3212061696,102626210253004,102626592116645),(3212163072,102626613084505,102626994948367)]
theorem point_links_checked24476 : (cuts24476.take 2).map (fun c => (3212050433-1+2*2^9*c.k,102626163020026+c.lower,102626544883641+c.upper)) = pointBounds24476 := by
 decide +kernel
def cuts24477 : List PrefixCut := [⟨81,330087905,330088093⟩,
⟨128,522248236,522248536⟩]
theorem checked24477 : checkPrefixCuts (2^48) 3212181505 9 Manual.Count131072.C024477.packed 128 cuts24477 = true := by
 decide +kernel
def pointBounds24477 : List (Nat × Nat × Nat) := [(3212264448,102627019583669,102627401447762)]
theorem point_links_checked24477 : (cuts24477.take 1).map (fun c => (3212181505-1+2*2^9*c.k,102626689495764+c.lower,102627071359669+c.upper)) = pointBounds24477 := by
 decide +kernel
def cuts24478 : List PrefixCut := [⟨52,212047730,212047853⟩,
⟨128,526520378,526520674⟩]
theorem checked24478 : checkPrefixCuts (2^48) 3212312577 9 Manual.Count131072.C024478.packed 128 cuts24478 = true := by
 decide +kernel
def pointBounds24478 : List (Nat × Nat × Nat) := [(3212365824,102627423791730,102627805656058)]
theorem point_links_checked24478 : (cuts24478.take 1).map (fun c => (3212312577-1+2*2^9*c.k,102627211744000+c.lower,102627593608205+c.upper)) = pointBounds24478 := by
 decide +kernel
def cuts24479 : List PrefixCut := [⟨23,97783770,97783825⟩,
⟨122,502229180,502229469⟩,
⟨128,528338954,528339258⟩]
theorem checked24479 : checkPrefixCuts (2^48) 3212443649 9 Manual.Count131072.C024479.packed 128 cuts24479 = true := by
 decide +kernel
def pointBounds24479 : List (Nat × Nat × Nat) := [(3212467200,102627836048148,102628217912704),(3212568576,102628240493558,102628622358348)]
theorem point_links_checked24479 : (cuts24479.take 2).map (fun c => (3212443649-1+2*2^9*c.k,102627738264378+c.lower,102628120128879+c.upper)) = pointBounds24479 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000139
