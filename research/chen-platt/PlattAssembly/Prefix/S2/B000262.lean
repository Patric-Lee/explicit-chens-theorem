import PlattAssemblyKernel
import PlattCertificates.Count131072.C018384
import PlattCertificates.Count131072.C018385
import PlattCertificates.Count131072.C018386
import PlattCertificates.Count131072.C018387
import PlattCertificates.Count131072.C018388
import PlattCertificates.Count131072.C018389
import PlattCertificates.Count131072.C018390
import PlattCertificates.Count131072.C018391
import PlattCertificates.Count131072.C018392
import PlattCertificates.Count131072.C018393
import PlattCertificates.Count131072.C018394
import PlattCertificates.Count131072.C018395
import PlattCertificates.Count131072.C018396
import PlattCertificates.Count131072.C018397
import PlattCertificates.Count131072.C018398
import PlattCertificates.Count131072.C018399
import PlattCertificates.Count131072.C018400
import PlattCertificates.Count131072.C018401
import PlattCertificates.Count131072.C018402
import PlattCertificates.Count131072.C018403
import PlattCertificates.Count131072.C018404
import PlattCertificates.Count131072.C018405
import PlattCertificates.Count131072.C018406
import PlattCertificates.Count131072.C018407
import PlattCertificates.Count131072.C018408
import PlattCertificates.Count131072.C018409
import PlattCertificates.Count131072.C018410
import PlattCertificates.Count131072.C018411
import PlattCertificates.Count131072.C018412
import PlattCertificates.Count131072.C018413
import PlattCertificates.Count131072.C018414
import PlattCertificates.Count131072.C018415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000262
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18384 : List PrefixCut := [⟨74,396976096,396976335⟩,
⟨128,695749644,695750063⟩]
theorem checked18384 : checkPrefixCuts (2^48) 2413559809 9 Manual.Count131072.C018384.packed 128 cuts18384 = true := by
 decide +kernel
def pointBounds18384 : List (Nat × Nat × Nat) := [(2413635584,98927300837770,98927680555496)]
theorem point_links_checked18384 : (cuts18384.take 1).map (fun c => (2413559809-1+2*2^9*c.k,98926903861674+c.lower,98927283579161+c.upper)) = pointBounds18384 := by
 decide +kernel
def cuts18385 : List PrefixCut := [⟨20,113117013,113117084⟩,
⟨94,521496194,521496515⟩,
⟨128,705041064,705041494⟩]
theorem checked18385 : checkPrefixCuts (2^48) 2413690881 9 Manual.Count131072.C018385.packed 128 cuts18385 = true := by
 decide +kernel
def pointBounds18385 : List (Nat × Nat × Nat) := [(2413711360,98927712728331,98928092446308),(2413787136,98928121107512,98928500825739)]
theorem point_links_checked18385 : (cuts18385.take 2).map (fun c => (2413690881-1+2*2^9*c.k,98927599611318+c.lower,98927979329224+c.upper)) = pointBounds18385 := by
 decide +kernel
def cuts18386 : List PrefixCut := [⟨40,232284415,232284556⟩,
⟨114,631892560,631892942⟩,
⟨128,710716630,710717057⟩]
theorem checked18386 : checkPrefixCuts (2^48) 2413821953 9 Manual.Count131072.C018386.packed 128 cuts18386 = true := by
 decide +kernel
def pointBounds18386 : List (Nat × Nat × Nat) := [(2413862912,98928536936797,98928916655274),(2413938688,98928936544942,98929316263660)]
theorem point_links_checked18386 : (cuts18386.take 2).map (fun c => (2413821953-1+2*2^9*c.k,98928304652382+c.lower,98928684370718+c.upper)) = pointBounds18386 := by
 decide +kernel
def cuts18387 : List PrefixCut := [⟨60,331265814,331266023⟩,
⟨128,712776635,712777070⟩]
theorem checked18387 : checkPrefixCuts (2^48) 2413953025 9 Manual.Count131072.C018387.packed 128 cuts18387 = true := by
 decide +kernel
def pointBounds18387 : List (Nat × Nat × Nat) := [(2414014464,98929346634826,98929726353798)]
theorem point_links_checked18387 : (cuts18387.take 1).map (fun c => (2413953025-1+2*2^9*c.k,98929015369012+c.lower,98929395087775+c.upper)) = pointBounds18387 := by
 decide +kernel
def cuts18388 : List PrefixCut := [⟨6,34396062,34396083⟩,
⟨80,440379304,440379572⟩,
⟨128,706675019,706675450⟩]
theorem checked18388 : checkPrefixCuts (2^48) 2414084097 9 Manual.Count131072.C018388.packed 128 cuts18388 = true := by
 decide +kernel
def pointBounds18388 : List (Nat × Nat × Nat) := [(2414090240,98929762541709,98930142260928),(2414166016,98930168524951,98930548244417)]
theorem point_links_checked18388 : (cuts18388.take 2).map (fun c => (2414084097-1+2*2^9*c.k,98929728145647+c.lower,98930107864845+c.upper)) = pointBounds18388 := by
 decide +kernel
def cuts18389 : List PrefixCut := [⟨26,145387717,145387808⟩,
⟨100,552977767,552978106⟩,
⟨128,704305116,704305547⟩]
theorem checked18389 : checkPrefixCuts (2^48) 2414215169 9 Manual.Count131072.C018389.packed 128 cuts18389 = true := by
 decide +kernel
def pointBounds18389 : List (Nat × Nat × Nat) := [(2414241792,98930580208383,98930959928103),(2414317568,98930987798433,98931367518401)]
theorem point_links_checked18389 : (cuts18389.take 2).map (fun c => (2414215169-1+2*2^9*c.k,98930434820666+c.lower,98930814540295+c.upper)) = pointBounds18389 := by
 decide +kernel
def cuts18390 : List PrefixCut := [⟨46,257648841,257648994⟩,
⟨120,669293566,669293964⟩,
⟨128,715225369,715225796⟩]
theorem checked18390 : checkPrefixCuts (2^48) 2414346241 9 Manual.Count131072.C018390.packed 128 cuts18390 = true := by
 decide +kernel
def pointBounds18390 : List (Nat × Nat × Nat) := [(2414393344,98931396774623,98931776494836),(2414469120,98931808419348,98932188139806)]
theorem point_links_checked18390 : (cuts18390.take 2).map (fun c => (2414346241-1+2*2^9*c.k,98931139125782+c.lower,98931518845842+c.upper)) = pointBounds18390 := by
 decide +kernel
def cuts18391 : List PrefixCut := [⟨66,362785569,362785792⟩,
⟨128,699798657,699799087⟩]
theorem checked18391 : checkPrefixCuts (2^48) 2414477313 9 Manual.Count131072.C018391.packed 128 cuts18391 = true := by
 decide +kernel
def pointBounds18391 : List (Nat × Nat × Nat) := [(2414544896,98932217136720,98932596857430)]
theorem point_links_checked18391 : (cuts18391.take 1).map (fun c => (2414477313-1+2*2^9*c.k,98931854351151+c.lower,98932234071638+c.upper)) = pointBounds18391 := by
 decide +kernel
def cuts18392 : List PrefixCut := [⟨12,68194244,68194285⟩,
⟨86,478517941,478518224⟩,
⟨128,711067826,711068247⟩]
theorem checked18392 : checkPrefixCuts (2^48) 2414608385 9 Manual.Count131072.C018392.packed 128 cuts18392 = true := by
 decide +kernel
def pointBounds18392 : List (Nat × Nat × Nat) := [(2414620672,98932622344052,98933002065010),(2414696448,98933032667749,98933412388949)]
theorem point_links_checked18392 : (cuts18392.take 2).map (fun c => (2414608385-1+2*2^9*c.k,98932554149808+c.lower,98932933870725+c.upper)) = pointBounds18392 := by
 decide +kernel
def cuts18393 : List PrefixCut := [⟨32,175779305,175779410⟩,
⟨106,587475962,587476318⟩,
⟨128,705434218,705434645⟩]
theorem checked18393 : checkPrefixCuts (2^48) 2414739457 9 Manual.Count131072.C018393.packed 128 cuts18393 = true := by
 decide +kernel
def pointBounds18393 : List (Nat × Nat × Nat) := [(2414772224,98933440996939,98933820718382),(2414848000,98933852693596,98934232415290)]
theorem point_links_checked18393 : (cuts18393.take 2).map (fun c => (2414739457-1+2*2^9*c.k,98933265217634+c.lower,98933644938972+c.upper)) = pointBounds18393 := by
 decide +kernel
def cuts18394 : List PrefixCut := [⟨52,285449852,285450030⟩,
⟨126,697819968,697820391⟩,
⟨128,708542818,708543248⟩]
theorem checked18394 : checkPrefixCuts (2^48) 2414870529 9 Manual.Count131072.C018394.packed 128 cuts18394 = true := by
 decide +kernel
def pointBounds18394 : List (Nat × Nat × Nat) := [(2414923776,98934256101704,98934635823647),(2414999552,98934668471820,98935048194008)]
theorem point_links_checked18394 : (cuts18394.take 2).map (fun c => (2414870529-1+2*2^9*c.k,98933970651852+c.lower,98934350373617+c.upper)) = pointBounds18394 := by
 decide +kernel
def cuts18395 : List PrefixCut := [⟨72,401051653,401051891⟩,
⟨128,708737661,708738085⟩]
theorem checked18395 : checkPrefixCuts (2^48) 2415001601 9 Manual.Count131072.C018395.packed 128 cuts18395 = true := by
 decide +kernel
def pointBounds18395 : List (Nat × Nat × Nat) := [(2415075328,98935080246323,98935459968756)]
theorem point_links_checked18395 : (cuts18395.take 1).map (fun c => (2415001601-1+2*2^9*c.k,98934679194670+c.lower,98935058916865+c.upper)) = pointBounds18395 := by
 decide +kernel
def cuts18396 : List PrefixCut := [⟨18,100812207,100812266⟩,
⟨92,503936582,503936882⟩,
⟨128,696695262,696695685⟩]
theorem checked18396 : checkPrefixCuts (2^48) 2415132673 9 Manual.Count131072.C018396.packed 128 cuts18396 = true := by
 decide +kernel
def pointBounds18396 : List (Nat × Nat × Nat) := [(2415151104,98935488744538,98935868467216),(2415226880,98935891868913,98936271591832)]
theorem point_links_checked18396 : (cuts18396.take 2).map (fun c => (2415132673-1+2*2^9*c.k,98935387932331+c.lower,98935767654950+c.upper)) = pointBounds18396 := by
 decide +kernel
def cuts18397 : List PrefixCut := [⟨38,213616150,213616281⟩,
⟨112,614268100,614268477⟩,
⟨128,702484419,702484849⟩]
theorem checked18397 : checkPrefixCuts (2^48) 2415263745 9 Manual.Count131072.C018397.packed 128 cuts18397 = true := by
 decide +kernel
def pointBounds18397 : List (Nat × Nat × Nat) := [(2415302656,98936298243743,98936677966916),(2415378432,98936698895693,98937078619112)]
theorem point_links_checked18397 : (cuts18397.take 2).map (fun c => (2415263745-1+2*2^9*c.k,98936084627593+c.lower,98936464350635+c.upper)) = pointBounds18397 := by
 decide +kernel
def cuts18398 : List PrefixCut := [⟨58,323143939,323144141⟩,
⟨128,701630495,701630921⟩]
theorem checked18398 : checkPrefixCuts (2^48) 2415394817 9 Manual.Count131072.C018398.packed 128 cuts18398 = true := by
 decide +kernel
def pointBounds18398 : List (Nat × Nat × Nat) := [(2415454208,98937110255951,98937489979625)]
theorem point_links_checked18398 : (cuts18398.take 1).map (fun c => (2415394817-1+2*2^9*c.k,98936787112012+c.lower,98937166835484+c.upper)) = pointBounds18398 := by
 decide +kernel
def cuts18399 : List PrefixCut := [⟨4,22839346,22839359⟩,
⟨78,435688692,435688958⟩,
⟨128,707884735,707885167⟩]
theorem checked18399 : checkPrefixCuts (2^48) 2415525889 9 Manual.Count131072.C018399.packed 128 cuts18399 = true := by
 decide +kernel
def pointBounds18399 : List (Nat × Nat × Nat) := [(2415529984,98937511581853,98937891305764),(2415605760,98937924431199,98938304155363)]
theorem point_links_checked18399 : (cuts18399.take 2).map (fun c => (2415525889-1+2*2^9*c.k,98937488742507+c.lower,98937868466405+c.upper)) = pointBounds18399 := by
 decide +kernel
def cuts18400 : List PrefixCut := [⟨24,133299417,133299498⟩,
⟨98,540529971,540530297⟩,
⟨128,709593928,709594356⟩]
theorem checked18400 : checkPrefixCuts (2^48) 2415656961 9 Manual.Count131072.C018400.packed 128 cuts18400 = true := by
 decide +kernel
def pointBounds18400 : List (Nat × Nat × Nat) := [(2415681536,98938329926659,98938709651070),(2415757312,98938737157213,98939116881869)]
theorem point_links_checked18400 : (cuts18400.take 2).map (fun c => (2415656961-1+2*2^9*c.k,98938196627242+c.lower,98938576351572+c.upper)) = pointBounds18400 := by
 decide +kernel
def cuts18401 : List PrefixCut := [⟨44,241066695,241066838⟩,
⟨118,646640591,646640983⟩,
⟨128,699535523,699535947⟩]
theorem checked18401 : checkPrefixCuts (2^48) 2415788033 9 Manual.Count131072.C018401.packed 128 cuts18401 = true := by
 decide +kernel
def pointBounds18401 : List (Nat × Nat × Nat) := [(2415833088,98939147287865,98939527012766),(2415908864,98939552861761,98939932586911)]
theorem point_links_checked18401 : (cuts18401.take 2).map (fun c => (2415788033-1+2*2^9*c.k,98938906221170+c.lower,98939285945928+c.upper)) = pointBounds18401 := by
 decide +kernel
def cuts18402 : List PrefixCut := [⟨64,357559466,357559685⟩,
⟨128,704623938,704624365⟩]
theorem checked18402 : checkPrefixCuts (2^48) 2415919105 9 Manual.Count131072.C018402.packed 128 cuts18402 = true := by
 decide +kernel
def pointBounds18402 : List (Nat × Nat × Nat) := [(2415984640,98939963316159,98940343041560)]
theorem point_links_checked18402 : (cuts18402.take 1).map (fun c => (2415919105-1+2*2^9*c.k,98939605756693+c.lower,98939985481875+c.upper)) = pointBounds18402 := by
 decide +kernel
def cuts18403 : List PrefixCut := [⟨10,57901414,57901450⟩,
⟨84,457379067,457379347⟩,
⟨128,702954417,702954843⟩]
theorem checked18403 : checkPrefixCuts (2^48) 2416050177 9 Manual.Count131072.C018403.packed 128 cuts18403 = true := by
 decide +kernel
def pointBounds18403 : List (Nat × Nat × Nat) := [(2416060416,98940368282045,98940748007690),(2416136192,98940767759698,98941147485587)]
theorem point_links_checked18403 : (cuts18403.take 2).map (fun c => (2416050177-1+2*2^9*c.k,98940310380631+c.lower,98940690106240+c.upper)) = pointBounds18403 := by
 decide +kernel
def cuts18404 : List PrefixCut := [⟨30,167053859,167053956⟩,
⟨104,577922723,577923069⟩,
⟨128,711653284,711653713⟩]
theorem checked18404 : checkPrefixCuts (2^48) 2416181249 9 Manual.Count131072.C018404.packed 128 cuts18404 = true := by
 decide +kernel
def pointBounds18404 : List (Nat × Nat × Nat) := [(2416211968,98941180388907,98941560115039),(2416287744,98941591257771,98941970984152)]
theorem point_links_checked18404 : (cuts18404.take 2).map (fun c => (2416181249-1+2*2^9*c.k,98941013335048+c.lower,98941393061083+c.upper)) = pointBounds18404 := by
 decide +kernel
def cuts18405 : List PrefixCut := [⟨50,277358452,277358618⟩,
⟨124,685755428,685755841⟩,
⟨128,707188343,707188767⟩]
theorem checked18405 : checkPrefixCuts (2^48) 2416312321 9 Manual.Count131072.C018405.packed 128 cuts18405 = true := by
 decide +kernel
def pointBounds18405 : List (Nat × Nat × Nat) := [(2416363520,98942002346784,98942382073414),(2416439296,98942410743760,98942790470637)]
theorem point_links_checked18405 : (cuts18405.take 2).map (fun c => (2416312321-1+2*2^9*c.k,98941724988332+c.lower,98942104714796+c.upper)) = pointBounds18405 := by
 decide +kernel
def cuts18406 : List PrefixCut := [⟨70,381243668,381243898⟩,
⟨128,706683898,706684322⟩]
theorem checked18406 : checkPrefixCuts (2^48) 2416443393 9 Manual.Count131072.C018406.packed 128 cuts18406 = true := by
 decide +kernel
def pointBounds18406 : List (Nat × Nat × Nat) := [(2416515072,98942813420343,98943193147461)]
theorem point_links_checked18406 : (cuts18406.take 1).map (fun c => (2416443393-1+2*2^9*c.k,98942432176675+c.lower,98942811903563+c.upper)) = pointBounds18406 := by
 decide +kernel
def cuts18407 : List PrefixCut := [⟨16,82348828,82348877⟩,
⟨90,491289679,491289977⟩,
⟨128,701287642,701288065⟩]
theorem checked18407 : checkPrefixCuts (2^48) 2416574465 9 Manual.Count131072.C018407.packed 128 cuts18407 = true := by
 decide +kernel
def pointBounds18407 : List (Nat × Nat × Nat) := [(2416590848,98943221209401,98943600936762),(2416666624,98943630150252,98944009877862)]
theorem point_links_checked18407 : (cuts18407.take 2).map (fun c => (2416574465-1+2*2^9*c.k,98943138860573+c.lower,98943518587885+c.upper)) = pointBounds18407 := by
 decide +kernel
def cuts18408 : List PrefixCut := [⟨36,198813629,198813752⟩,
⟨110,608660659,608661032⟩,
⟨128,709751950,709752383⟩]
theorem checked18408 : checkPrefixCuts (2^48) 2416705537 9 Manual.Count131072.C018408.packed 128 cuts18408 = true := by
 decide +kernel
def pointBounds18408 : List (Nat × Nat × Nat) := [(2416742400,98944038961844,98944418689702),(2416818176,98944448808874,98944828536982)]
theorem point_links_checked18408 : (cuts18408.take 2).map (fun c => (2416705537-1+2*2^9*c.k,98943840148215+c.lower,98944219875950+c.upper)) = pointBounds18408 := by
 decide +kernel
def cuts18409 : List PrefixCut := [⟨56,307461792,307461975⟩,
⟨128,709131083,709131506⟩]
theorem checked18409 : checkPrefixCuts (2^48) 2416836609 9 Manual.Count131072.C018409.packed 128 cuts18409 = true := by
 decide +kernel
def pointBounds18409 : List (Nat × Nat × Nat) := [(2416893952,98944857361957,98945237090308)]
theorem point_links_checked18409 : (cuts18409.take 1).map (fun c => (2416836609-1+2*2^9*c.k,98944549900165+c.lower,98944929628333+c.upper)) = pointBounds18409 := by
 decide +kernel
def cuts18410 : List PrefixCut := [⟨2,10830577,10830584⟩,
⟨76,425180824,425181082⟩,
⟨128,707462512,707462941⟩]
theorem checked18410 : checkPrefixCuts (2^48) 2416967681 9 Manual.Count131072.C018410.packed 128 cuts18410 = true := by
 decide +kernel
def pointBounds18410 : List (Nat × Nat × Nat) := [(2416969728,98945269861825,98945649590423),(2417045504,98945684212072,98946063940921)]
theorem point_links_checked18410 : (cuts18410.take 2).map (fun c => (2416967681-1+2*2^9*c.k,98945259031248+c.lower,98945638759839+c.upper)) = pointBounds18410 := by
 decide +kernel
def cuts18411 : List PrefixCut := [⟨22,119828094,119828165⟩,
⟨96,526466759,526467076⟩,
⟨128,705560732,705561156⟩]
theorem checked18411 : checkPrefixCuts (2^48) 2417098753 9 Manual.Count131072.C018411.packed 128 cuts18411 = true := by
 decide +kernel
def pointBounds18411 : List (Nat × Nat × Nat) := [(2417121280,98946086321854,98946466050945),(2417197056,98946492960519,98946872689856)]
theorem point_links_checked18411 : (cuts18411.take 2).map (fun c => (2417098753-1+2*2^9*c.k,98945966493760+c.lower,98946346222780+c.upper)) = pointBounds18411 := by
 decide +kernel
def cuts18412 : List PrefixCut := [⟨42,234402160,234402301⟩,
⟨116,641830420,641830812⟩,
⟨128,711344635,711345068⟩]
theorem checked18412 : checkPrefixCuts (2^48) 2417229825 9 Manual.Count131072.C018412.packed 128 cuts18412 = true := by
 decide +kernel
def pointBounds18412 : List (Nat × Nat × Nat) := [(2417272832,98946906456652,98947286186237),(2417348608,98947313884912,98947693614748)]
theorem point_links_checked18412 : (cuts18412.take 2).map (fun c => (2417229825-1+2*2^9*c.k,98946672054492+c.lower,98947051783936+c.upper)) = pointBounds18412 := by
 decide +kernel
def cuts18413 : List PrefixCut := [⟨62,342093035,342093241⟩,
⟨128,704203507,704203928⟩]
theorem checked18413 : checkPrefixCuts (2^48) 2417360897 9 Manual.Count131072.C018413.packed 128 cuts18413 = true := by
 decide +kernel
def pointBounds18413 : List (Nat × Nat × Nat) := [(2417424384,98947725492162,98948105222245)]
theorem point_links_checked18413 : (cuts18413.take 1).map (fun c => (2417360897-1+2*2^9*c.k,98947383399127+c.lower,98947763129004+c.upper)) = pointBounds18413 := by
 decide +kernel
def cuts18414 : List PrefixCut := [⟨8,48319452,48319480⟩,
⟨82,452565806,452566075⟩,
⟨128,708706161,708706584⟩]
theorem checked18414 : checkPrefixCuts (2^48) 2417491969 9 Manual.Count131072.C018414.packed 128 cuts18414 = true := by
 decide +kernel
def pointBounds18414 : List (Nat × Nat × Nat) := [(2417500160,98948135922086,98948515652412),(2417575936,98948540168440,98948919899007)]
theorem point_links_checked18414 : (cuts18414.take 2).map (fun c => (2417491969-1+2*2^9*c.k,98948087602634+c.lower,98948467332932+c.upper)) = pointBounds18414 := by
 decide +kernel
def cuts18415 : List PrefixCut := [⟨28,153565380,153565473⟩,
⟨102,567798745,567799090⟩,
⟨128,713673789,713674219⟩]
theorem checked18415 : checkPrefixCuts (2^48) 2417623041 9 Manual.Count131072.C018415.packed 128 cuts18415 = true := by
 decide +kernel
def pointBounds18415 : List (Nat × Nat × Nat) := [(2417651712,98948949874175,98949329604989),(2417727488,98949364107540,98949743838606)]
theorem point_links_checked18415 : (cuts18415.take 2).map (fun c => (2417623041-1+2*2^9*c.k,98948796308795+c.lower,98949176039516+c.upper)) = pointBounds18415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000262
