import PlattAssemblyKernel
import PlattCertificates.Count131072.C032528
import PlattCertificates.Count131072.C032529
import PlattCertificates.Count131072.C032530
import PlattCertificates.Count131072.C032531
import PlattCertificates.Count131072.C032532
import PlattCertificates.Count131072.C032533
import PlattCertificates.Count131072.C032534
import PlattCertificates.Count131072.C032535
import PlattCertificates.Count131072.C032536
import PlattCertificates.Count131072.C032537
import PlattCertificates.Count131072.C032538
import PlattCertificates.Count131072.C032539
import PlattCertificates.Count131072.C032540
import PlattCertificates.Count131072.C032541
import PlattCertificates.Count131072.C032542
import PlattCertificates.Count131072.C032543
import PlattCertificates.Count131072.C032544
import PlattCertificates.Count131072.C032545
import PlattCertificates.Count131072.C032546
import PlattCertificates.Count131072.C032547
import PlattCertificates.Count131072.C032548
import PlattCertificates.Count131072.C032549
import PlattCertificates.Count131072.C032550
import PlattCertificates.Count131072.C032551
import PlattCertificates.Count131072.C032552
import PlattCertificates.Count131072.C032553
import PlattCertificates.Count131072.C032554
import PlattCertificates.Count131072.C032555
import PlattCertificates.Count131072.C032556
import PlattCertificates.Count131072.C032557
import PlattCertificates.Count131072.C032558
import PlattCertificates.Count131072.C032559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32528 : List PrefixCut := [⟨118,357886733,357886942⟩,
⟨128,388226836,388227062⟩]
theorem checked32528 : checkPrefixCuts (2^48) 4267442177 9 Manual.Count131072.C032528.packed 128 cuts32528 = true := by
 decide +kernel
def pointBounds32528 : List (Nat × Nat × Nat) := [(4267563008,106256097095675,106256480997230)]
theorem point_links_checked32528 : (cuts32528.take 1).map (fun c => (4267442177-1+2*2^9*c.k,106255739208942+c.lower,106256123110288+c.upper)) = pointBounds32528 := by
 decide +kernel
def cuts32529 : List PrefixCut := [⟨121,367571161,367571370⟩,
⟨128,388346890,388347111⟩]
theorem checked32529 : checkPrefixCuts (2^48) 4267573249 9 Manual.Count131072.C032529.packed 128 cuts32529 = true := by
 decide +kernel
def pointBounds32529 : List (Nat × Nat × Nat) := [(4267697152,106256495006939,106256878908720)]
theorem point_links_checked32529 : (cuts32529.take 1).map (fun c => (4267573249-1+2*2^9*c.k,106256127435778+c.lower,106256511337350+c.upper)) = pointBounds32529 := by
 decide +kernel
def cuts32530 : List PrefixCut := [⟨124,377188984,377189199⟩,
⟨128,389456175,389456398⟩]
theorem checked32530 : checkPrefixCuts (2^48) 4267704321 9 Manual.Count131072.C032530.packed 128 cuts32530 = true := by
 decide +kernel
def pointBounds32530 : List (Nat × Nat × Nat) := [(4267831296,106256892971652,106257276873660)]
theorem point_links_checked32530 : (cuts32530.take 1).map (fun c => (4267704321-1+2*2^9*c.k,106256515782668+c.lower,106256899684461+c.upper)) = pointBounds32530 := by
 decide +kernel
def cuts32531 : List PrefixCut := [⟨127,387201869,387202088⟩,
⟨128,390697251,390697471⟩]
theorem checked32531 : checkPrefixCuts (2^48) 4267835393 9 Manual.Count131072.C032531.packed 128 cuts32531 = true := by
 decide +kernel
def pointBounds32531 : List (Nat × Nat × Nat) := [(4267965440,106257292440712,106257676342947)]
theorem point_links_checked32531 : (cuts32531.take 1).map (fun c => (4267835393-1+2*2^9*c.k,106256905238843+c.lower,106257289140859+c.upper)) = pointBounds32531 := by
 decide +kernel
def cuts32532 : List PrefixCut := [⟨128,390553417,390553636⟩]
theorem checked32532 : checkPrefixCuts (2^48) 4267966465 9 Manual.Count131072.C032532.packed 128 cuts32532 = true := by
 decide +kernel
def cuts32533 : List PrefixCut := [⟨2,6199164,6199167⟩,
⟨128,393179270,393179494⟩]
theorem checked32533 : checkPrefixCuts (2^48) 4268097537 9 Manual.Count131072.C032533.packed 128 cuts32533 = true := by
 decide +kernel
def pointBounds32533 : List (Nat × Nat × Nat) := [(4268099584,106257692688675,106258076591133)]
theorem point_links_checked32533 : (cuts32533.take 1).map (fun c => (4268097537-1+2*2^9*c.k,106257686489511+c.lower,106258070391966+c.upper)) = pointBounds32533 := by
 decide +kernel
def cuts32534 : List PrefixCut := [⟨5,15497428,15497436⟩,
⟨128,387364066,387364294⟩]
theorem checked32534 : checkPrefixCuts (2^48) 4268228609 9 Manual.Count131072.C032534.packed 128 cuts32534 = true := by
 decide +kernel
def pointBounds32534 : List (Nat × Nat × Nat) := [(4268233728,106258095166209,106258479068896)]
theorem point_links_checked32534 : (cuts32534.take 1).map (fun c => (4268228609-1+2*2^9*c.k,106258079668781+c.lower,106258463571460+c.upper)) = pointBounds32534 := by
 decide +kernel
def cuts32535 : List PrefixCut := [⟨8,24531335,24531349⟩,
⟨128,390978987,390979208⟩]
theorem checked32535 : checkPrefixCuts (2^48) 4268359681 9 Manual.Count131072.C032535.packed 128 cuts32535 = true := by
 decide +kernel
def pointBounds32535 : List (Nat × Nat × Nat) := [(4268367872,106258491564182,106258875467103)]
theorem point_links_checked32535 : (cuts32535.take 1).map (fun c => (4268359681-1+2*2^9*c.k,106258467032847+c.lower,106258850935754+c.upper)) = pointBounds32535 := by
 decide +kernel
def cuts32536 : List PrefixCut := [⟨11,31322638,31322658⟩,
⟨128,389186555,389186780⟩]
theorem checked32536 : checkPrefixCuts (2^48) 4268490753 9 Manual.Count131072.C032536.packed 128 cuts32536 = true := by
 decide +kernel
def pointBounds32536 : List (Nat × Nat × Nat) := [(4268502016,106258889334472,106259273237620)]
theorem point_links_checked32536 : (cuts32536.take 1).map (fun c => (4268490753-1+2*2^9*c.k,106258858011834+c.lower,106259241914962+c.upper)) = pointBounds32536 := by
 decide +kernel
def cuts32537 : List PrefixCut := [⟨14,41080835,41080863⟩,
⟨128,393196912,393197130⟩]
theorem checked32537 : checkPrefixCuts (2^48) 4268621825 9 Manual.Count131072.C032537.packed 128 cuts32537 = true := by
 decide +kernel
def pointBounds32537 : List (Nat × Nat × Nat) := [(4268636160,106259288279224,106259672182605)]
theorem point_links_checked32537 : (cuts32537.take 1).map (fun c => (4268621825-1+2*2^9*c.k,106259247198389+c.lower,106259631101742+c.upper)) = pointBounds32537 := by
 decide +kernel
def cuts32538 : List PrefixCut := [⟨17,52355013,52355042⟩,
⟨128,394371720,394371944⟩]
theorem checked32538 : checkPrefixCuts (2^48) 4268752897 9 Manual.Count131072.C032538.packed 128 cuts32538 = true := by
 decide +kernel
def pointBounds32538 : List (Nat × Nat × Nat) := [(4268770304,106259692750314,106260076653914)]
theorem point_links_checked32538 : (cuts32538.take 1).map (fun c => (4268752897-1+2*2^9*c.k,106259640395301+c.lower,106260024298872+c.upper)) = pointBounds32538 := by
 decide +kernel
def cuts32539 : List PrefixCut := [⟨20,63694425,63694463⟩,
⟨128,392777225,392777452⟩]
theorem checked32539 : checkPrefixCuts (2^48) 4268883969 9 Manual.Count131072.C032539.packed 128 cuts32539 = true := by
 decide +kernel
def pointBounds32539 : List (Nat × Nat × Nat) := [(4268904448,106260098461446,106260482365279)]
theorem point_links_checked32539 : (cuts32539.take 1).map (fun c => (4268883969-1+2*2^9*c.k,106260034767021+c.lower,106260418670816+c.upper)) = pointBounds32539 := by
 decide +kernel
def cuts32540 : List PrefixCut := [⟨23,72857303,72857343⟩,
⟨128,391446448,391446675⟩]
theorem checked32540 : checkPrefixCuts (2^48) 4269015041 9 Manual.Count131072.C032540.packed 128 cuts32540 = true := by
 decide +kernel
def pointBounds32540 : List (Nat × Nat × Nat) := [(4269038592,106260500401549,106260884305611)]
theorem point_links_checked32540 : (cuts32540.take 1).map (fun c => (4269015041-1+2*2^9*c.k,106260427544246+c.lower,106260811448268+c.upper)) = pointBounds32540 := by
 decide +kernel
def cuts32541 : List PrefixCut := [⟨26,79052659,79052703⟩,
⟨128,387544506,387544731⟩]
theorem checked32541 : checkPrefixCuts (2^48) 4269146113 9 Manual.Count131072.C032541.packed 128 cuts32541 = true := by
 decide +kernel
def pointBounds32541 : List (Nat × Nat × Nat) := [(4269172736,106260898043353,106261281947646)]
theorem point_links_checked32541 : (cuts32541.take 1).map (fun c => (4269146113-1+2*2^9*c.k,106260818990694+c.lower,106261202894943+c.upper)) = pointBounds32541 := by
 decide +kernel
def cuts32542 : List PrefixCut := [⟨29,84720191,84720238⟩,
⟨128,383379028,383379247⟩]
theorem checked32542 : checkPrefixCuts (2^48) 4269277185 9 Manual.Count131072.C032542.packed 128 cuts32542 = true := by
 decide +kernel
def pointBounds32542 : List (Nat × Nat × Nat) := [(4269306880,106261291255391,106261675159912)]
theorem point_links_checked32542 : (cuts32542.take 1).map (fun c => (4269277185-1+2*2^9*c.k,106261206535200+c.lower,106261590439674+c.upper)) = pointBounds32542 := by
 decide +kernel
def cuts32543 : List PrefixCut := [⟨32,92299290,92299346⟩,
⟨128,390223622,390223850⟩]
theorem checked32543 : checkPrefixCuts (2^48) 4269408257 9 Manual.Count131072.C032543.packed 128 cuts32543 = true := by
 decide +kernel
def pointBounds32543 : List (Nat × Nat × Nat) := [(4269441024,106261682213518,106262066118267)]
theorem point_links_checked32543 : (cuts32543.take 1).map (fun c => (4269408257-1+2*2^9*c.k,106261589914228+c.lower,106261973818921+c.upper)) = pointBounds32543 := by
 decide +kernel
def cuts32544 : List PrefixCut := [⟨35,108975705,108975768⟩,
⟨128,388761415,388761637⟩]
theorem checked32544 : checkPrefixCuts (2^48) 4269539329 9 Manual.Count131072.C032544.packed 128 cuts32544 = true := by
 decide +kernel
def pointBounds32544 : List (Nat × Nat × Nat) := [(4269575168,106262089113555,106262473018539)]
theorem point_links_checked32544 : (cuts32544.take 1).map (fun c => (4269539329-1+2*2^9*c.k,106261980137850+c.lower,106262364042771+c.upper)) = pointBounds32544 := by
 decide +kernel
def cuts32545 : List PrefixCut := [⟨38,116092107,116092169⟩,
⟨128,388090225,388090445⟩]
theorem checked32545 : checkPrefixCuts (2^48) 4269670401 9 Manual.Count131072.C032545.packed 128 cuts32545 = true := by
 decide +kernel
def pointBounds32545 : List (Nat × Nat × Nat) := [(4269709312,106262484991372,106262868896577)]
theorem point_links_checked32545 : (cuts32545.take 1).map (fun c => (4269670401-1+2*2^9*c.k,106262368899265+c.lower,106262752804408+c.upper)) = pointBounds32545 := by
 decide +kernel
def cuts32546 : List PrefixCut := [⟨41,128547746,128547814⟩,
⟨128,389199003,389199218⟩]
theorem checked32546 : checkPrefixCuts (2^48) 4269801473 9 Manual.Count131072.C032546.packed 128 cuts32546 = true := by
 decide +kernel
def pointBounds32546 : List (Nat × Nat × Nat) := [(4269843456,106262885537236,106263269442667)]
theorem point_links_checked32546 : (cuts32546.take 1).map (fun c => (4269801473-1+2*2^9*c.k,106262756989490+c.lower,106263140894853+c.upper)) = pointBounds32546 := by
 decide +kernel
def cuts32547 : List PrefixCut := [⟨44,132498953,132499025⟩,
⟨128,387407223,387407431⟩]
theorem checked32547 : checkPrefixCuts (2^48) 4269932545 9 Manual.Count131072.C032547.packed 128 cuts32547 = true := by
 decide +kernel
def pointBounds32547 : List (Nat × Nat × Nat) := [(4269977600,106263278687446,106263662593096)]
theorem point_links_checked32547 : (cuts32547.take 1).map (fun c => (4269932545-1+2*2^9*c.k,106263146188493+c.lower,106263530094071+c.upper)) = pointBounds32547 := by
 decide +kernel
def cuts32548 : List PrefixCut := [⟨47,142382508,142382588⟩,
⟨128,389240930,389241144⟩]
theorem checked32548 : checkPrefixCuts (2^48) 4270063617 9 Manual.Count131072.C032548.packed 128 cuts32548 = true := by
 decide +kernel
def pointBounds32548 : List (Nat × Nat × Nat) := [(4270111744,106263675978224,106264059884090)]
theorem point_links_checked32548 : (cuts32548.take 1).map (fun c => (4270063617-1+2*2^9*c.k,106263533595716+c.lower,106263917501502+c.upper)) = pointBounds32548 := by
 decide +kernel
def cuts32549 : List PrefixCut := [⟨50,151210809,151210898⟩,
⟨128,388108483,388108711⟩]
theorem checked32549 : checkPrefixCuts (2^48) 4270194689 9 Manual.Count131072.C032549.packed 128 cuts32549 = true := by
 decide +kernel
def pointBounds32549 : List (Nat × Nat × Nat) := [(4270245888,106264074047455,106264457953544)]
theorem point_links_checked32549 : (cuts32549.take 1).map (fun c => (4270194689-1+2*2^9*c.k,106263922836646+c.lower,106264306742646+c.upper)) = pointBounds32549 := by
 decide +kernel
def cuts32550 : List PrefixCut := [⟨53,161488649,161488736⟩,
⟨128,391458133,391458348⟩]
theorem checked32550 : checkPrefixCuts (2^48) 4270325761 9 Manual.Count131072.C032550.packed 128 cuts32550 = true := by
 decide +kernel
def pointBounds32550 : List (Nat × Nat × Nat) := [(4270380032,106264472433778,106264856340093)]
theorem point_links_checked32550 : (cuts32550.take 1).map (fun c => (4270325761-1+2*2^9*c.k,106264310945129+c.lower,106264694851357+c.upper)) = pointBounds32550 := by
 decide +kernel
def cuts32551 : List PrefixCut := [⟨56,168074806,168074901⟩,
⟨128,386305057,386305273⟩]
theorem checked32551 : checkPrefixCuts (2^48) 4270456833 9 Manual.Count131072.C032551.packed 128 cuts32551 = true := by
 decide +kernel
def pointBounds32551 : List (Nat × Nat × Nat) := [(4270514176,106264870478068,106265254384606)]
theorem point_links_checked32551 : (cuts32551.take 1).map (fun c => (4270456833-1+2*2^9*c.k,106264702403262+c.lower,106265086309705+c.upper)) = pointBounds32551 := by
 decide +kernel
def cuts32552 : List PrefixCut := [⟨59,179340126,179340225⟩,
⟨128,387084111,387084332⟩]
theorem checked32552 : checkPrefixCuts (2^48) 4270587905 9 Manual.Count131072.C032552.packed 128 cuts32552 = true := by
 decide +kernel
def pointBounds32552 : List (Nat × Nat × Nat) := [(4270648320,106265268048445,106265651955203)]
theorem point_links_checked32552 : (cuts32552.take 1).map (fun c => (4270587905-1+2*2^9*c.k,106265088708319+c.lower,106265472614978+c.upper)) = pointBounds32552 := by
 decide +kernel
def cuts32553 : List PrefixCut := [⟨62,191461560,191461666⟩,
⟨128,395244711,395244924⟩]
theorem checked32553 : checkPrefixCuts (2^48) 4270718977 9 Manual.Count131072.C032553.packed 128 cuts32553 = true := by
 decide +kernel
def pointBounds32553 : List (Nat × Nat × Nat) := [(4270782464,106265667253990,106266051160976)]
theorem point_links_checked32553 : (cuts32553.take 1).map (fun c => (4270718977-1+2*2^9*c.k,106265475792430+c.lower,106265859699310+c.upper)) = pointBounds32553 := by
 decide +kernel
def cuts32554 : List PrefixCut := [⟨65,199627902,199628014⟩,
⟨128,389828386,389828597⟩]
theorem checked32554 : checkPrefixCuts (2^48) 4270850049 9 Manual.Count131072.C032554.packed 128 cuts32554 = true := by
 decide +kernel
def pointBounds32554 : List (Nat × Nat × Nat) := [(4270916608,106266070665043,106266454572248)]
theorem point_links_checked32554 : (cuts32554.take 1).map (fun c => (4270850049-1+2*2^9*c.k,106265871037141+c.lower,106266254944234+c.upper)) = pointBounds32554 := by
 decide +kernel
def cuts32555 : List PrefixCut := [⟨68,210363970,210364087⟩,
⟨128,391332213,391332430⟩]
theorem checked32555 : checkPrefixCuts (2^48) 4270981121 9 Manual.Count131072.C032555.packed 128 cuts32555 = true := by
 decide +kernel
def pointBounds32555 : List (Nat × Nat × Nat) := [(4271050752,106266471229497,106266855136918)]
theorem point_links_checked32555 : (cuts32555.take 1).map (fun c => (4270981121-1+2*2^9*c.k,106266260865527+c.lower,106266644772831+c.upper)) = pointBounds32555 := by
 decide +kernel
def cuts32556 : List PrefixCut := [⟨71,220835763,220835888⟩,
⟨128,396460437,396460666⟩]
theorem checked32556 : checkPrefixCuts (2^48) 4271112193 9 Manual.Count131072.C032556.packed 128 cuts32556 = true := by
 decide +kernel
def pointBounds32556 : List (Nat × Nat × Nat) := [(4271184896,106266873033503,106267256941149)]
theorem point_links_checked32556 : (cuts32556.take 1).map (fun c => (4271112193-1+2*2^9*c.k,106266652197740+c.lower,106267036105261+c.upper)) = pointBounds32556 := by
 decide +kernel
def cuts32557 : List PrefixCut := [⟨74,221553825,221553951⟩,
⟨128,378589708,378589927⟩]
theorem checked32557 : checkPrefixCuts (2^48) 4271243265 9 Manual.Count131072.C032557.packed 128 cuts32557 = true := by
 decide +kernel
def pointBounds32557 : List (Nat × Nat × Nat) := [(4271319040,106267270212002,106267654119878)]
theorem point_links_checked32557 : (cuts32557.take 1).map (fun c => (4271243265-1+2*2^9*c.k,106267048658177+c.lower,106267432565927+c.upper)) = pointBounds32557 := by
 decide +kernel
def cuts32558 : List PrefixCut := [⟨77,233144887,233145021⟩,
⟨128,392416361,392416585⟩]
theorem checked32558 : checkPrefixCuts (2^48) 4271374337 9 Manual.Count131072.C032558.packed 128 cuts32558 = true := by
 decide +kernel
def pointBounds32558 : List (Nat × Nat × Nat) := [(4271453184,106267660392772,106268044300875)]
theorem point_links_checked32558 : (cuts32558.take 1).map (fun c => (4271374337-1+2*2^9*c.k,106267427247885+c.lower,106267811155854+c.upper)) = pointBounds32558 := by
 decide +kernel
def cuts32559 : List PrefixCut := [⟨80,246646130,246646271⟩,
⟨128,392074878,392075101⟩]
theorem checked32559 : checkPrefixCuts (2^48) 4271505409 9 Manual.Count131072.C032559.packed 128 cuts32559 = true := by
 decide +kernel
def pointBounds32559 : List (Nat × Nat × Nat) := [(4271587328,106268066310376,106268450218710)]
theorem point_links_checked32559 : (cuts32559.take 1).map (fun c => (4271505409-1+2*2^9*c.k,106267819664246+c.lower,106268203572439+c.upper)) = pointBounds32559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000079
