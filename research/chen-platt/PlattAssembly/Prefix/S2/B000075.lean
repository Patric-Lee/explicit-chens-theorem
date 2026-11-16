import PlattAssemblyKernel
import PlattCertificates.Count131072.C012400
import PlattCertificates.Count131072.C012401
import PlattCertificates.Count131072.C012402
import PlattCertificates.Count131072.C012403
import PlattCertificates.Count131072.C012404
import PlattCertificates.Count131072.C012405
import PlattCertificates.Count131072.C012406
import PlattCertificates.Count131072.C012407
import PlattCertificates.Count131072.C012408
import PlattCertificates.Count131072.C012409
import PlattCertificates.Count131072.C012410
import PlattCertificates.Count131072.C012411
import PlattCertificates.Count131072.C012412
import PlattCertificates.Count131072.C012413
import PlattCertificates.Count131072.C012414
import PlattCertificates.Count131072.C012415
import PlattCertificates.Count131072.C012416
import PlattCertificates.Count131072.C012417
import PlattCertificates.Count131072.C012418
import PlattCertificates.Count131072.C012419
import PlattCertificates.Count131072.C012420
import PlattCertificates.Count131072.C012421
import PlattCertificates.Count131072.C012422
import PlattCertificates.Count131072.C012423
import PlattCertificates.Count131072.C012424
import PlattCertificates.Count131072.C012425
import PlattCertificates.Count131072.C012426
import PlattCertificates.Count131072.C012427
import PlattCertificates.Count131072.C012428
import PlattCertificates.Count131072.C012429
import PlattCertificates.Count131072.C012430
import PlattCertificates.Count131072.C012431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12400 : List PrefixCut := [⟨48,397183302,397183602⟩,
⟨98,814567075,814567680⟩,
⟨128,1055904210,1055904993⟩]
theorem checked12400 : checkPrefixCuts (2^48) 1629224961 9 Manual.Count131072.C012400.packed 128 cuts12400 = true := by
 decide +kernel
def pointBounds12400 : List (Nat × Nat × Nat) := [(1629274112,93760065320668,93760441585642),(1629325312,93760482704441,93760858969720)]
theorem point_links_checked12400 : (cuts12400.take 2).map (fun c => (1629224961-1+2*2^9*c.k,93759668137366+c.lower,93760044402040+c.upper)) = pointBounds12400 := by
 decide +kernel
def cuts12401 : List PrefixCut := [⟨20,165668337,165668458⟩,
⟨70,587517313,587517746⟩,
⟨120,1007107450,1007108192⟩,
⟨128,1072229959,1072230752⟩]
theorem checked12401 : checkPrefixCuts (2^48) 1629356033 9 Manual.Count131072.C012401.packed 128 cuts12401 = true := by
 decide +kernel
def pointBounds12401 : List (Nat × Nat × Nat) := [(1629376512,93760889709913,93761265975491),(1629427712,93761311558889,93761687824779),(1629478912,93761731149026,93762107415225)]
theorem point_links_checked12401 : (cuts12401.take 3).map (fun c => (1629356033-1+2*2^9*c.k,93760724041576+c.lower,93761100307033+c.upper)) = pointBounds12401 := by
 decide +kernel
def cuts12402 : List PrefixCut := [⟨42,344090249,344090507⟩,
⟨92,760544839,760545405⟩,
⟨128,1063852322,1063853111⟩]
theorem checked12402 : checkPrefixCuts (2^48) 1629487105 9 Manual.Count131072.C012402.packed 128 cuts12402 = true := by
 decide +kernel
def pointBounds12402 : List (Nat × Nat × Nat) := [(1629530112,93762140361784,93762516628292),(1629581312,93762556816374,93762933083190)]
theorem point_links_checked12402 : (cuts12402.take 2).map (fun c => (1629487105-1+2*2^9*c.k,93761796271535+c.lower,93762172537785+c.upper)) = pointBounds12402 := by
 decide +kernel
def cuts12403 : List PrefixCut := [⟨14,115552141,115552228⟩,
⟨64,541825660,541826064⟩,
⟨114,954614086,954614797⟩,
⟨128,1069639801,1069640599⟩]
theorem checked12403 : checkPrefixCuts (2^48) 1629618177 9 Manual.Count131072.C012403.packed 128 cuts12403 = true := by
 decide +kernel
def pointBounds12403 : List (Nat × Nat × Nat) := [(1629632512,93762975675998,93763351943124),(1629683712,93763401949517,93763778216960),(1629734912,93763814737943,93764191005693)]
theorem point_links_checked12403 : (cuts12403.take 3).map (fun c => (1629618177-1+2*2^9*c.k,93762860123857+c.lower,93763236390896+c.upper)) = pointBounds12403 := by
 decide +kernel
def cuts12404 : List PrefixCut := [⟨36,304657915,304658144⟩,
⟨86,714311670,714312204⟩,
⟨128,1065581330,1065582128⟩]
theorem checked12404 : checkPrefixCuts (2^48) 1629749249 9 Manual.Count131072.C012404.packed 128 cuts12404 = true := by
 decide +kernel
def pointBounds12404 : List (Nat × Nat × Nat) := [(1629786112,93764234421573,93764610689639),(1629837312,93764644075328,93765020343699)]
theorem point_links_checked12404 : (cuts12404.take 2).map (fun c => (1629749249-1+2*2^9*c.k,93763929763658+c.lower,93764306031495+c.upper)) = pointBounds12404 := by
 decide +kernel
def cuts12405 : List PrefixCut := [⟨8,70978141,70978194⟩,
⟨58,488377333,488377694⟩,
⟨108,909044454,909045132⟩,
⟨128,1076375109,1076375913⟩]
theorem checked12405 : checkPrefixCuts (2^48) 1629880321 9 Manual.Count131072.C012405.packed 128 cuts12405 = true := by
 decide +kernel
def pointBounds12405 : List (Nat × Nat × Nat) := [(1629888512,93765066323129,93765442591817),(1629939712,93765483722321,93765859991317),(1629990912,93765904389442,93766280658755)]
theorem point_links_checked12405 : (cuts12405.take 3).map (fun c => (1629880321-1+2*2^9*c.k,93764995344988+c.lower,93765371613623+c.upper)) = pointBounds12405 := by
 decide +kernel
def cuts12406 : List PrefixCut := [⟨30,251078394,251078584⟩,
⟨80,673100440,673100948⟩,
⟨128,1071453468,1071454275⟩]
theorem checked12406 : checkPrefixCuts (2^48) 1630011393 9 Manual.Count131072.C012406.packed 128 cuts12406 = true := by
 decide +kernel
def pointBounds12406 : List (Nat × Nat × Nat) := [(1630042112,93766322798491,93766699068120),(1630093312,93766744820537,93767121090484)]
theorem point_links_checked12406 : (cuts12406.take 2).map (fun c => (1630011393-1+2*2^9*c.k,93766071720097+c.lower,93766447989536+c.upper)) = pointBounds12406 := by
 decide +kernel
def cuts12407 : List PrefixCut := [⟨2,17784883,17784896⟩,
⟨52,431837772,431838094⟩,
⟨102,847431669,847432307⟩,
⟨128,1058072475,1058073271⟩]
theorem checked12407 : checkPrefixCuts (2^48) 1630142465 9 Manual.Count131072.C012407.packed 128 cuts12407 = true := by
 decide +kernel
def pointBounds12407 : List (Nat × Nat × Nat) := [(1630144512,93767160958448,93767537228707),(1630195712,93767575011337,93767951281905),(1630246912,93767990605234,93768366876118)]
theorem point_links_checked12407 : (cuts12407.take 3).map (fun c => (1630142465-1+2*2^9*c.k,93767143173565+c.lower,93767519443811+c.upper)) = pointBounds12407 := by
 decide +kernel
def cuts12408 : List PrefixCut := [⟨24,199760332,199760483⟩,
⟨74,626723004,626723474⟩,
⟨124,1046766539,1046767326⟩,
⟨128,1080086314,1080087125⟩]
theorem checked12408 : checkPrefixCuts (2^48) 1630273537 9 Manual.Count131072.C012408.packed 128 cuts12408 = true := by
 decide +kernel
def pointBounds12408 : List (Nat × Nat × Nat) := [(1630298112,93768401006372,93768777277565),(1630349312,93768827969044,93769204240556),(1630400512,93769248012579,93769624284408)]
theorem point_links_checked12408 : (cuts12408.take 3).map (fun c => (1630273537-1+2*2^9*c.k,93768201246040+c.lower,93768577517082+c.upper)) = pointBounds12408 := by
 decide +kernel
def cuts12409 : List PrefixCut := [⟨46,384638852,384639139⟩,
⟨96,795506359,795506957⟩,
⟨128,1077236830,1077237641⟩]
theorem checked12409 : checkPrefixCuts (2^48) 1630404609 9 Manual.Count131072.C012409.packed 128 cuts12409 = true := by
 decide +kernel
def pointBounds12409 : List (Nat × Nat × Nat) := [(1630451712,93769665971206,93770042243346),(1630502912,93770076838713,93770453111164)]
theorem point_links_checked12409 : (cuts12409.take 2).map (fun c => (1630404609-1+2*2^9*c.k,93769281332354+c.lower,93769657604207+c.upper)) = pointBounds12409 := by
 decide +kernel
def cuts12410 : List PrefixCut := [⟨18,151047999,151048109⟩,
⟨68,563270813,563271230⟩,
⟨118,987218479,987219213⟩,
⟨128,1068001783,1068002578⟩]
theorem checked12410 : checkPrefixCuts (2^48) 1630535681 9 Manual.Count131072.C012410.packed 128 cuts12410 = true := by
 decide +kernel
def pointBounds12410 : List (Nat × Nat × Nat) := [(1630554112,93770509617183,93770885889957),(1630605312,93770921839997,93771298113078),(1630656512,93771345787663,93771722061061)]
theorem point_links_checked12410 : (cuts12410.take 3).map (fun c => (1630535681-1+2*2^9*c.k,93770358569184+c.lower,93770734841848+c.upper)) = pointBounds12410 := by
 decide +kernel
def cuts12411 : List PrefixCut := [⟨40,329859959,329860211⟩,
⟨90,743769918,743770483⟩,
⟨128,1062047179,1062047985⟩]
theorem checked12411 : checkPrefixCuts (2^48) 1630666753 9 Manual.Count131072.C012411.packed 128 cuts12411 = true := by
 decide +kernel
def pointBounds12411 : List (Nat × Nat × Nat) := [(1630707712,93771756430926,93772132704637),(1630758912,93772170340885,93772546614909)]
theorem point_links_checked12411 : (cuts12411.take 2).map (fun c => (1630666753-1+2*2^9*c.k,93771426570967+c.lower,93771802844426+c.upper)) = pointBounds12411 := by
 decide +kernel
def cuts12412 : List PrefixCut := [⟨12,104077099,104077176⟩,
⟨62,523829368,523829761⟩,
⟨112,934593735,934594434⟩,
⟨128,1066449821,1066450619⟩]
theorem checked12412 : checkPrefixCuts (2^48) 1630797825 9 Manual.Count131072.C012412.packed 128 cuts12412 = true := by
 decide +kernel
def pointBounds12412 : List (Nat × Nat × Nat) := [(1630810112,93772592695245,93772968969587),(1630861312,93773012447514,93773388722172),(1630912512,93773423211881,93773799486845)]
theorem point_links_checked12412 : (cuts12412.take 3).map (fun c => (1630797825-1+2*2^9*c.k,93772488618146+c.lower,93772864892411+c.upper)) = pointBounds12412 := by
 decide +kernel
def cuts12413 : List PrefixCut := [⟨34,274408256,274408461⟩,
⟨84,695501637,695502151⟩,
⟨128,1063257099,1063257883⟩]
theorem checked12413 : checkPrefixCuts (2^48) 1630928897 9 Manual.Count131072.C012413.packed 128 cuts12413 = true := by
 decide +kernel
def pointBounds12413 : List (Nat × Nat × Nat) := [(1630963712,93773829476223,93774205751491),(1631014912,93774250569604,93774626845181)]
theorem point_links_checked12413 : (cuts12413.take 2).map (fun c => (1630928897-1+2*2^9*c.k,93773555067967+c.lower,93773931343030+c.upper)) = pointBounds12413 := by
 decide +kernel
def cuts12414 : List PrefixCut := [⟨6,49010288,49010323⟩,
⟨56,470422247,470422595⟩,
⟨106,888887498,888888158⟩,
⟨128,1070419611,1070420405⟩]
theorem checked12414 : checkPrefixCuts (2^48) 1631059969 9 Manual.Count131072.C012414.packed 128 cuts12414 = true := by
 decide +kernel
def pointBounds12414 : List (Nat × Nat × Nat) := [(1631066112,93774667335354,93775043611236),(1631117312,93775088747313,93775465023508),(1631168512,93775507212564,93775883489071)]
theorem point_links_checked12414 : (cuts12414.take 3).map (fun c => (1631059969-1+2*2^9*c.k,93774618325066+c.lower,93774994600913+c.upper)) = pointBounds12414 := by
 decide +kernel
def cuts12415 : List PrefixCut := [⟨28,229845065,229845235⟩,
⟨78,646558398,646558882⟩,
⟨128,1059117578,1059118372⟩]
theorem checked12415 : checkPrefixCuts (2^48) 1631191041 9 Manual.Count131072.C012415.packed 128 cuts12415 = true := by
 decide +kernel
def pointBounds12415 : List (Nat × Nat × Nat) := [(1631219712,93775918589742,93776294866553),(1631270912,93776335303075,93776711580200),(1631322112,93776747862255,93777124139690)]
theorem point_links_checked12415 : (cuts12415.take 3).map (fun c => (1631191041-1+2*2^9*c.k,93775688744677+c.lower,93776065021318+c.upper)) = pointBounds12415 := by
 decide +kernel
def cuts12416 : List PrefixCut := [⟨50,415651996,415652305⟩,
⟨100,834569115,834569734⟩,
⟨128,1063518634,1063519424⟩]
theorem checked12416 : checkPrefixCuts (2^48) 1631322113 9 Manual.Count131072.C012416.packed 128 cuts12416 = true := by
 decide +kernel
def pointBounds12416 : List (Nat × Nat × Nat) := [(1631373312,93777163514251,93777539791995),(1631424512,93777582431370,93777958709424)]
theorem point_links_checked12416 : (cuts12416.take 2).map (fun c => (1631322113-1+2*2^9*c.k,93776747862255+c.lower,93777124139690+c.upper)) = pointBounds12416 := by
 decide +kernel
def cuts12417 : List PrefixCut := [⟨22,182363086,182363221⟩,
⟨72,599011132,599011581⟩,
⟨122,1021511708,1021512474⟩,
⟨128,1069988877,1069989679⟩]
theorem checked12417 : checkPrefixCuts (2^48) 1631453185 9 Manual.Count131072.C012417.packed 128 cuts12417 = true := by
 decide +kernel
def pointBounds12417 : List (Nat × Nat × Nat) := [(1631475712,93777993743975,93778370022335),(1631526912,93778410392021,93778786670695),(1631578112,93778832892597,93779209171588)]
theorem point_links_checked12417 : (cuts12417.take 3).map (fun c => (1631453185-1+2*2^9*c.k,93777811380889+c.lower,93778187659114+c.upper)) = pointBounds12417 := by
 decide +kernel
def cuts12418 : List PrefixCut := [⟨44,368834673,368834946⟩,
⟨94,779750756,779751338⟩,
⟨128,1065072856,1065073652⟩]
theorem checked12418 : checkPrefixCuts (2^48) 1631584257 9 Manual.Count131072.C012418.packed 128 cuts12418 = true := by
 decide +kernel
def pointBounds12418 : List (Nat × Nat × Nat) := [(1631629312,93779250204439,93779626483739),(1631680512,93779661120522,93780037400131)]
theorem point_links_checked12418 : (cuts12418.take 2).map (fun c => (1631584257-1+2*2^9*c.k,93778881369766+c.lower,93779257648793+c.upper)) = pointBounds12418 := by
 decide +kernel
def cuts12419 : List PrefixCut := [⟨16,136966242,136966346⟩,
⟨66,545096525,545096932⟩,
⟨116,963736078,963736794⟩,
⟨128,1065159742,1065160533⟩]
theorem checked12419 : checkPrefixCuts (2^48) 1631715329 9 Manual.Count131072.C012419.packed 128 cuts12419 = true := by
 decide +kernel
def pointBounds12419 : List (Nat × Nat × Nat) := [(1631731712,93780083408864,93780459688791),(1631782912,93780491539147,93780867819377),(1631834112,93780910178700,93781286459239)]
theorem point_links_checked12419 : (cuts12419.take 3).map (fun c => (1631715329-1+2*2^9*c.k,93779946442622+c.lower,93780322722445+c.upper)) = pointBounds12419 := by
 decide +kernel
def cuts12420 : List PrefixCut := [⟨38,313925490,313925725⟩,
⟨88,725811892,725812437⟩,
⟨128,1059037205,1059037997⟩]
theorem checked12420 : checkPrefixCuts (2^48) 1631846401 9 Manual.Count131072.C012420.packed 128 cuts12420 = true := by
 decide +kernel
def pointBounds12420 : List (Nat × Nat × Nat) := [(1631885312,93781325527854,93781701808703),(1631936512,93781737414256,93782113695415)]
theorem point_links_checked12420 : (cuts12420.take 2).map (fun c => (1631846401-1+2*2^9*c.k,93781011602364+c.lower,93781387882978+c.upper)) = pointBounds12420 := by
 decide +kernel
def cuts12421 : List PrefixCut := [⟨10,87789361,87789426⟩,
⟨60,501202207,501202582⟩,
⟨110,916844075,916844762⟩,
⟨128,1064126515,1064127310⟩]
theorem checked12421 : checkPrefixCuts (2^48) 1631977473 9 Manual.Count131072.C012421.packed 128 cuts12421 = true := by
 decide +kernel
def pointBounds12421 : List (Nat × Nat × Nat) := [(1631987712,93782158428930,93782534710401),(1632038912,93782571841776,93782948123557),(1632090112,93782987483644,93783363765737)]
theorem point_links_checked12421 : (cuts12421.take 3).map (fun c => (1631977473-1+2*2^9*c.k,93782070639569+c.lower,93782446920975+c.upper)) = pointBounds12421 := by
 decide +kernel
def cuts12422 : List PrefixCut := [⟨32,270588376,270588580⟩,
⟨82,682927660,682928176⟩,
⟨128,1072491087,1072491897⟩]
theorem checked12422 : checkPrefixCuts (2^48) 1632108545 9 Manual.Count131072.C012422.packed 128 cuts12422 = true := by
 decide +kernel
def pointBounds12422 : List (Nat × Nat × Nat) := [(1632141312,93783405354460,93783781636865),(1632192512,93783817693744,93784193976461)]
theorem point_links_checked12422 : (cuts12422.take 2).map (fun c => (1632108545-1+2*2^9*c.k,93783134766084+c.lower,93783511048285+c.upper)) = pointBounds12422 := by
 decide +kernel
def cuts12423 : List PrefixCut := [⟨4,36041382,36041409⟩,
⟨54,451803579,451803919⟩,
⟨104,872725906,872726560⟩,
⟨128,1071025584,1071026389⟩]
theorem checked12423 : checkPrefixCuts (2^48) 1632239617 9 Manual.Count131072.C012423.packed 128 cuts12423 = true := by
 decide +kernel
def pointBounds12423 : List (Nat × Nat × Nat) := [(1632243712,93784243298553,93784619581591),(1632294912,93784659060750,93785035344101),(1632346112,93785079983077,93785456266742)]
theorem point_links_checked12423 : (cuts12423.take 3).map (fun c => (1632239617-1+2*2^9*c.k,93784207257171+c.lower,93784583540182+c.upper)) = pointBounds12423 := by
 decide +kernel
def cuts12424 : List PrefixCut := [⟨26,222092170,222092334⟩,
⟨76,626262648,626263118⟩,
⟨126,1041800341,1041801124⟩,
⟨128,1055076638,1055077432⟩]
theorem checked12424 : checkPrefixCuts (2^48) 1632370689 9 Manual.Count131072.C012424.packed 128 cuts12424 = true := by
 decide +kernel
def pointBounds12424 : List (Nat × Nat × Nat) := [(1632397312,93785500374925,93785876658905),(1632448512,93785904545403,93786280829689),(1632499712,93786320083096,93786696367695)]
theorem point_links_checked12424 : (cuts12424.take 3).map (fun c => (1632370689-1+2*2^9*c.k,93785278282755+c.lower,93785654566571+c.upper)) = pointBounds12424 := by
 decide +kernel
def cuts12425 : List PrefixCut := [⟨48,394317108,394317403⟩,
⟨98,810690753,810691359⟩,
⟨128,1062922387,1062923180⟩]
theorem checked12425 : checkPrefixCuts (2^48) 1632501761 9 Manual.Count131072.C012425.packed 128 cuts12425 = true := by
 decide +kernel
def pointBounds12425 : List (Nat × Nat × Nat) := [(1632550912,93786727676501,93787103961406),(1632602112,93787144050146,93787520335362)]
theorem point_links_checked12425 : (cuts12425.take 2).map (fun c => (1632501761-1+2*2^9*c.k,93786333359393+c.lower,93786709644003+c.upper)) = pointBounds12425 := by
 decide +kernel
def cuts12426 : List PrefixCut := [⟨20,164473811,164473934⟩,
⟨70,590475775,590476219⟩,
⟨120,1006637851,1006638607⟩,
⟨128,1075077518,1075078325⟩]
theorem checked12426 : checkPrefixCuts (2^48) 1632632833 9 Manual.Count131072.C012426.packed 128 cuts12426 = true := by
 decide +kernel
def pointBounds12426 : List (Nat × Nat × Nat) := [(1632653312,93787560755591,93787937041117),(1632704512,93787986757555,93788363043402),(1632755712,93788402919631,93788779205790)]
theorem point_links_checked12426 : (cuts12426.take 3).map (fun c => (1632632833-1+2*2^9*c.k,93787396281780+c.lower,93787772567183+c.upper)) = pointBounds12426 := by
 decide +kernel
def cuts12427 : List PrefixCut := [⟨42,354949699,354949967⟩,
⟨92,778153454,778154041⟩,
⟨128,1086713242,1086714056⟩]
theorem checked12427 : checkPrefixCuts (2^48) 1632763905 9 Manual.Count131072.C012427.packed 128 cuts12427 = true := by
 decide +kernel
def pointBounds12427 : List (Nat × Nat × Nat) := [(1632806912,93788826308997,93789202595475),(1632858112,93789249512752,93789625799549)]
theorem point_links_checked12427 : (cuts12427.take 2).map (fun c => (1632763905-1+2*2^9*c.k,93788471359298+c.lower,93788847645508+c.upper)) = pointBounds12427 := by
 decide +kernel
def cuts12428 : List PrefixCut := [⟨14,120146802,120146891⟩,
⟨64,546771472,546771880⟩,
⟨114,960627525,960628243⟩,
⟨128,1081282833,1081283642⟩]
theorem checked12428 : checkPrefixCuts (2^48) 1632894977 9 Manual.Count131072.C012428.packed 128 cuts12428 = true := by
 decide +kernel
def pointBounds12428 : List (Nat × Nat × Nat) := [(1632909312,93789678219342,93790054506455),(1632960512,93790104844012,93790481131444),(1633011712,93790518700065,93790894987807)]
theorem point_links_checked12428 : (cuts12428.take 3).map (fun c => (1632894977-1+2*2^9*c.k,93789558072540+c.lower,93789934359564+c.upper)) = pointBounds12428 := by
 decide +kernel
def cuts12429 : List PrefixCut := [⟨36,306459702,306459930⟩,
⟨86,717015071,717015604⟩,
⟨128,1063443422,1063444215⟩]
theorem checked12429 : checkPrefixCuts (2^48) 1633026049 9 Manual.Count131072.C012429.packed 128 cuts12429 = true := by
 decide +kernel
def pointBounds12429 : List (Nat × Nat × Nat) := [(1633062912,93790945815075,93791322103136),(1633114112,93791356370444,93791732658810)]
theorem point_links_checked12429 : (cuts12429.take 2).map (fun c => (1633026049-1+2*2^9*c.k,93790639355373+c.lower,93791015643206+c.upper)) = pointBounds12429 := by
 decide +kernel
def cuts12430 : List PrefixCut := [⟨8,65148192,65148240⟩,
⟨58,489637747,489638113⟩,
⟨108,909116255,909116936⟩,
⟨128,1073353796,1073354601⟩]
theorem checked12430 : checkPrefixCuts (2^48) 1633157121 9 Manual.Count131072.C012430.packed 128 cuts12430 = true := by
 decide +kernel
def pointBounds12430 : List (Nat × Nat × Nat) := [(1633165312,93791767946987,93792144235661),(1633216512,93792192436542,93792568725534),(1633267712,93792611915050,93792988204357)]
theorem point_links_checked12430 : (cuts12430.take 3).map (fun c => (1633157121-1+2*2^9*c.k,93791702798795+c.lower,93792079087421+c.upper)) = pointBounds12430 := by
 decide +kernel
def cuts12431 : List PrefixCut := [⟨30,252815008,252815195⟩,
⟨80,664512180,664512671⟩,
⟨128,1055690160,1055690943⟩]
theorem checked12431 : checkPrefixCuts (2^48) 1633288193 9 Manual.Count131072.C012431.packed 128 cuts12431 = true := by
 decide +kernel
def pointBounds12431 : List (Nat × Nat × Nat) := [(1633318912,93793028967599,93793405257217),(1633370112,93793440664771,93793816954693)]
theorem point_links_checked12431 : (cuts12431.take 2).map (fun c => (1633288193-1+2*2^9*c.k,93792776152591+c.lower,93793152442022+c.upper)) = pointBounds12431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000075
