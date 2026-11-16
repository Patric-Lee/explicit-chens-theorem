import PlattAssemblyKernel
import PlattCertificates.Count131072.C023424
import PlattCertificates.Count131072.C023425
import PlattCertificates.Count131072.C023426
import PlattCertificates.Count131072.C023427
import PlattCertificates.Count131072.C023428
import PlattCertificates.Count131072.C023429
import PlattCertificates.Count131072.C023430
import PlattCertificates.Count131072.C023431
import PlattCertificates.Count131072.C023432
import PlattCertificates.Count131072.C023433
import PlattCertificates.Count131072.C023434
import PlattCertificates.Count131072.C023435
import PlattCertificates.Count131072.C023436
import PlattCertificates.Count131072.C023437
import PlattCertificates.Count131072.C023438
import PlattCertificates.Count131072.C023439
import PlattCertificates.Count131072.C023440
import PlattCertificates.Count131072.C023441
import PlattCertificates.Count131072.C023442
import PlattCertificates.Count131072.C023443
import PlattCertificates.Count131072.C023444
import PlattCertificates.Count131072.C023445
import PlattCertificates.Count131072.C023446
import PlattCertificates.Count131072.C023447
import PlattCertificates.Count131072.C023448
import PlattCertificates.Count131072.C023449
import PlattCertificates.Count131072.C023450
import PlattCertificates.Count131072.C023451
import PlattCertificates.Count131072.C023452
import PlattCertificates.Count131072.C023453
import PlattCertificates.Count131072.C023454
import PlattCertificates.Count131072.C023455
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000107
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23424 : List PrefixCut := [⟨14,58690777,58690811⟩,
⟨108,464757719,464757979⟩,
⟨128,550455894,550456201⟩]
theorem checked23424 : checkPrefixCuts (2^48) 3074162689 9 Manual.Count131072.C023424.packed 128 cuts23424 = true := by
 decide +kernel
def pointBounds23424 : List (Nat × Nat × Nat) := [(3074177024,102061499067070,102061880611818),(3074273280,102061905134012,102062286678986)]
theorem point_links_checked23424 : (cuts23424.take 2).map (fun c => (3074162689-1+2*2^9*c.k,102061440376293+c.lower,102061821921007+c.upper)) = pointBounds23424 := by
 decide +kernel
def cuts23425 : List PrefixCut := [⟨74,315137287,315137468⟩,
⟨128,549059056,549059365⟩]
theorem checked23425 : checkPrefixCuts (2^48) 3074293761 9 Manual.Count131072.C023425.packed 128 cuts23425 = true := by
 decide +kernel
def pointBounds23425 : List (Nat × Nat × Nat) := [(3074369536,102062305969474,102062687514676)]
theorem point_links_checked23425 : (cuts23425.take 1).map (fun c => (3074293761-1+2*2^9*c.k,102061990832187+c.lower,102062372377208+c.upper)) = pointBounds23425 := by
 decide +kernel
def cuts23426 : List PrefixCut := [⟨40,170105610,170105710⟩,
⟨128,548761018,548761334⟩]
theorem checked23426 : checkPrefixCuts (2^48) 3074424833 9 Manual.Count131072.C023426.packed 128 cuts23426 = true := by
 decide +kernel
def pointBounds23426 : List (Nat × Nat × Nat) := [(3074465792,102062709996853,102063091542283)]
theorem point_links_checked23426 : (cuts23426.take 1).map (fun c => (3074424833-1+2*2^9*c.k,102062539891243+c.lower,102062921436573+c.upper)) = pointBounds23426 := by
 decide +kernel
def cuts23427 : List PrefixCut := [⟨6,30211396,30211411⟩,
⟨100,440163985,440164227⟩,
⟨128,557343238,557343548⟩]
theorem checked23427 : checkPrefixCuts (2^48) 3074555905 9 Manual.Count131072.C023427.packed 128 cuts23427 = true := by
 decide +kernel
def pointBounds23427 : List (Nat × Nat × Nat) := [(3074562048,102063118863657,102063500409318),(3074658304,102063528816246,102063910362134)]
theorem point_links_checked23427 : (cuts23427.take 2).map (fun c => (3074555905-1+2*2^9*c.k,102063088652261+c.lower,102063470197907+c.upper)) = pointBounds23427 := by
 decide +kernel
def cuts23428 : List PrefixCut := [⟨66,278479459,278479616⟩,
⟨128,545510151,545510463⟩]
theorem checked23428 : checkPrefixCuts (2^48) 3074686977 9 Manual.Count131072.C023428.packed 128 cuts23428 = true := by
 decide +kernel
def pointBounds23428 : List (Nat × Nat × Nat) := [(3074754560,102063924474958,102064306021071)]
theorem point_links_checked23428 : (cuts23428.take 1).map (fun c => (3074686977-1+2*2^9*c.k,102063645995499+c.lower,102064027541455+c.upper)) = pointBounds23428 := by
 decide +kernel
def cuts23429 : List PrefixCut := [⟨32,133559029,133559101⟩,
⟨126,537614665,537614968⟩,
⟨128,545395403,545395711⟩]
theorem checked23429 : checkPrefixCuts (2^48) 3074818049 9 Manual.Count131072.C023429.packed 128 cuts23429 = true := by
 decide +kernel
def pointBounds23429 : List (Nat × Nat × Nat) := [(3074850816,102064325064679,102064706611019),(3074947072,102064729120315,102065110666886)]
theorem point_links_checked23429 : (cuts23429.take 2).map (fun c => (3074818049-1+2*2^9*c.k,102064191505650+c.lower,102064573051918+c.upper)) = pointBounds23429 := by
 decide +kernel
def cuts23430 : List PrefixCut := [⟨92,396536867,396537093⟩,
⟨128,548484489,548484807⟩]
theorem checked23430 : checkPrefixCuts (2^48) 3074949121 9 Manual.Count131072.C023430.packed 128 cuts23430 = true := by
 decide +kernel
def pointBounds23430 : List (Nat × Nat × Nat) := [(3075043328,102065133437920,102065514984722)]
theorem point_links_checked23430 : (cuts23430.take 1).map (fun c => (3074949121-1+2*2^9*c.k,102064736901053+c.lower,102065118447629+c.upper)) = pointBounds23430 := by
 decide +kernel
def cuts23431 : List PrefixCut := [⟨58,250343551,250343698⟩,
⟨128,547271217,547271532⟩]
theorem checked23431 : checkPrefixCuts (2^48) 3075080193 9 Manual.Count131072.C023431.packed 128 cuts23431 = true := by
 decide +kernel
def pointBounds23431 : List (Nat × Nat × Nat) := [(3075139584,102065535729093,102065917276134)]
theorem point_links_checked23431 : (cuts23431.take 1).map (fun c => (3075080193-1+2*2^9*c.k,102065285385542+c.lower,102065666932436+c.upper)) = pointBounds23431 := by
 decide +kernel
def cuts23432 : List PrefixCut := [⟨24,102971130,102971185⟩,
⟨118,508715225,508715503⟩,
⟨128,549444523,549444824⟩]
theorem checked23432 : checkPrefixCuts (2^48) 3075211265 9 Manual.Count131072.C023432.packed 128 cuts23432 = true := by
 decide +kernel
def pointBounds23432 : List (Nat × Nat × Nat) := [(3075235840,102065935627889,102066317175153),(3075332096,102066341371984,102066722919471)]
theorem point_links_checked23432 : (cuts23432.take 2).map (fun c => (3075211265-1+2*2^9*c.k,102065832656759+c.lower,102066214203968+c.upper)) = pointBounds23432 := by
 decide +kernel
def cuts23433 : List PrefixCut := [⟨84,361798651,361798857⟩,
⟨128,547499084,547499399⟩]
theorem checked23433 : checkPrefixCuts (2^48) 3075342337 9 Manual.Count131072.C023433.packed 128 cuts23433 = true := by
 decide +kernel
def pointBounds23433 : List (Nat × Nat × Nat) := [(3075428352,102066743899933,102067125447649)]
theorem point_links_checked23433 : (cuts23433.take 1).map (fun c => (3075342337-1+2*2^9*c.k,102066382101282+c.lower,102066763648792+c.upper)) = pointBounds23433 := by
 decide +kernel
def cuts23434 : List PrefixCut := [⟨50,216174265,216174391⟩,
⟨128,548116425,548116738⟩]
theorem checked23434 : checkPrefixCuts (2^48) 3075473409 9 Manual.Count131072.C023434.packed 128 cuts23434 = true := by
 decide +kernel
def pointBounds23434 : List (Nat × Nat × Nat) := [(3075524608,102067145774631,102067527322582)]
theorem point_links_checked23434 : (cuts23434.take 1).map (fun c => (3075473409-1+2*2^9*c.k,102066929600366+c.lower,102067311148191+c.upper)) = pointBounds23434 := by
 decide +kernel
def cuts23435 : List PrefixCut := [⟨16,72940097,72940139⟩,
⟨110,474240530,474240802⟩,
⟨128,552760343,552760658⟩]
theorem checked23435 : checkPrefixCuts (2^48) 3075604481 9 Manual.Count131072.C023435.packed 128 cuts23435 = true := by
 decide +kernel
def pointBounds23435 : List (Nat × Nat × Nat) := [(3075620864,102067550656888,102067932205068),(3075717120,102067951957321,102068333505731)]
theorem point_links_checked23435 : (cuts23435.take 2).map (fun c => (3075604481-1+2*2^9*c.k,102067477716791+c.lower,102067859264929+c.upper)) = pointBounds23435 := by
 decide +kernel
def cuts23436 : List PrefixCut := [⟨76,327160740,327160923⟩,
⟨128,547978105,547978412⟩]
theorem checked23436 : checkPrefixCuts (2^48) 3075735553 9 Manual.Count131072.C023436.packed 128 cuts23436 = true := by
 decide +kernel
def pointBounds23436 : List (Nat × Nat × Nat) := [(3075813376,102068357637874,102068739186510)]
theorem point_links_checked23436 : (cuts23436.take 1).map (fun c => (3075735553-1+2*2^9*c.k,102068030477134+c.lower,102068412025587+c.upper)) = pointBounds23436 := by
 decide +kernel
def cuts23437 : List PrefixCut := [⟨42,182288154,182288259⟩,
⟨128,551523580,551523892⟩]
theorem checked23437 : checkPrefixCuts (2^48) 3075866625 9 Manual.Count131072.C023437.packed 128 cuts23437 = true := by
 decide +kernel
def pointBounds23437 : List (Nat × Nat × Nat) := [(3075909632,102068760743393,102069142292258)]
theorem point_links_checked23437 : (cuts23437.take 1).map (fun c => (3075866625-1+2*2^9*c.k,102068578455239+c.lower,102068960003999+c.upper)) = pointBounds23437 := by
 decide +kernel
def cuts23438 : List PrefixCut := [⟨8,34132015,34132034⟩,
⟨102,438859536,438859793⟩,
⟨128,552140686,552141008⟩]
theorem checked23438 : checkPrefixCuts (2^48) 3075997697 9 Manual.Count131072.C023438.packed 128 cuts23438 = true := by
 decide +kernel
def pointBounds23438 : List (Nat × Nat × Nat) := [(3076005888,102069164110834,102069545659925),(3076102144,102069568838355,102069950387684)]
theorem point_links_checked23438 : (cuts23438.take 2).map (fun c => (3075997697-1+2*2^9*c.k,102069129978819+c.lower,102069511527891+c.upper)) = pointBounds23438 := by
 decide +kernel
def cuts23439 : List PrefixCut := [⟨68,294453202,294453371⟩,
⟨128,550744645,550744954⟩]
theorem checked23439 : checkPrefixCuts (2^48) 3076128769 9 Manual.Count131072.C023439.packed 128 cuts23439 = true := by
 decide +kernel
def pointBounds23439 : List (Nat × Nat × Nat) := [(3076198400,102069976572707,102070358122270)]
theorem point_links_checked23439 : (cuts23439.take 1).map (fun c => (3076128769-1+2*2^9*c.k,102069682119505+c.lower,102070063668899+c.upper)) = pointBounds23439 := by
 decide +kernel
def cuts23440 : List PrefixCut := [⟨34,145848680,145848763⟩,
⟨128,548708221,548708535⟩]
theorem checked23440 : checkPrefixCuts (2^48) 3076259841 9 Manual.Count131072.C023440.packed 128 cuts23440 = true := by
 decide +kernel
def pointBounds23440 : List (Nat × Nat × Nat) := [(3076294656,102070378712830,102070760262616),(3076390912,102070781572371,102071163122388)]
theorem point_links_checked23440 : (cuts23440.take 2).map (fun c => (3076259841-1+2*2^9*c.k,102070232864150+c.lower,102070614413853+c.upper)) = pointBounds23440 := by
 decide +kernel
def cuts23441 : List PrefixCut := [⟨94,397906286,397906509⟩,
⟨128,542097349,542097653⟩]
theorem checked23441 : checkPrefixCuts (2^48) 3076390913 9 Manual.Count131072.C023441.packed 128 cuts23441 = true := by
 decide +kernel
def pointBounds23441 : List (Nat × Nat × Nat) := [(3076487168,102071179478657,102071561028897)]
theorem point_links_checked23441 : (cuts23441.take 1).map (fun c => (3076390913-1+2*2^9*c.k,102070781572371+c.lower,102071163122388+c.upper)) = pointBounds23441 := by
 decide +kernel
def cuts23442 : List PrefixCut := [⟨60,255807032,255807174⟩,
⟨128,545550813,545551123⟩]
theorem checked23442 : checkPrefixCuts (2^48) 3076521985 9 Manual.Count131072.C023442.packed 128 cuts23442 = true := by
 decide +kernel
def pointBounds23442 : List (Nat × Nat × Nat) := [(3076583424,102071579476752,102071961027215)]
theorem point_links_checked23442 : (cuts23442.take 1).map (fun c => (3076521985-1+2*2^9*c.k,102071323669720+c.lower,102071705220041+c.upper)) = pointBounds23442 := by
 decide +kernel
def cuts23443 : List PrefixCut := [⟨26,113443857,113443918⟩,
⟨120,520095374,520095670⟩,
⟨128,555225077,555225392⟩]
theorem checked23443 : checkPrefixCuts (2^48) 3076653057 9 Manual.Count131072.C023443.packed 128 cuts23443 = true := by
 decide +kernel
def pointBounds23443 : List (Nat × Nat × Nat) := [(3076679680,102071982664390,102072364215082),(3076775936,102072389315907,102072770866834)]
theorem point_links_checked23443 : (cuts23443.take 2).map (fun c => (3076653057-1+2*2^9*c.k,102071869220533+c.lower,102072250771164+c.upper)) = pointBounds23443 := by
 decide +kernel
def cuts23444 : List PrefixCut := [⟨86,371783530,371783737⟩,
⟨128,555475799,555476103⟩]
theorem checked23444 : checkPrefixCuts (2^48) 3076784129 9 Manual.Count131072.C023444.packed 128 cuts23444 = true := by
 decide +kernel
def pointBounds23444 : List (Nat × Nat × Nat) := [(3076872192,102072796229140,102073177780293)]
theorem point_links_checked23444 : (cuts23444.take 1).map (fun c => (3076784129-1+2*2^9*c.k,102072424445610+c.lower,102072805996556+c.upper)) = pointBounds23444 := by
 decide +kernel
def cuts23445 : List PrefixCut := [⟨52,220555337,220555463⟩,
⟨128,535967495,535967802⟩]
theorem checked23445 : checkPrefixCuts (2^48) 3076915201 9 Manual.Count131072.C023445.packed 128 cuts23445 = true := by
 decide +kernel
def pointBounds23445 : List (Nat × Nat × Nat) := [(3076968448,102073200476746,102073582028122)]
theorem point_links_checked23445 : (cuts23445.take 1).map (fun c => (3076915201-1+2*2^9*c.k,102072979921409+c.lower,102073361472659+c.upper)) = pointBounds23445 := by
 decide +kernel
def cuts23446 : List PrefixCut := [⟨18,76747870,76747911⟩,
⟨112,482159337,482159609⟩,
⟨128,550214529,550214838⟩]
theorem checked23446 : checkPrefixCuts (2^48) 3077046273 9 Manual.Count131072.C023446.packed 128 cuts23446 = true := by
 decide +kernel
def pointBounds23446 : List (Nat × Nat × Nat) := [(3077064704,102073592636774,102073974188372),(3077160960,102073998048241,102074379600070)]
theorem point_links_checked23446 : (cuts23446.take 2).map (fun c => (3077046273-1+2*2^9*c.k,102073515888904+c.lower,102073897440461+c.upper)) = pointBounds23446 := by
 decide +kernel
def cuts23447 : List PrefixCut := [⟨78,331214999,331215189⟩,
⟨128,545526011,545526324⟩]
theorem checked23447 : checkPrefixCuts (2^48) 3077177345 9 Manual.Count131072.C023447.packed 128 cuts23447 = true := by
 decide +kernel
def pointBounds23447 : List (Nat × Nat × Nat) := [(3077257216,102074397318432,102074778870488)]
theorem point_links_checked23447 : (cuts23447.take 1).map (fun c => (3077177345-1+2*2^9*c.k,102074066103433+c.lower,102074447655299+c.upper)) = pointBounds23447 := by
 decide +kernel
def cuts23448 : List PrefixCut := [⟨44,186959004,186959110⟩,
⟨128,544405247,544405553⟩]
theorem checked23448 : checkPrefixCuts (2^48) 3077308417 9 Manual.Count131072.C023448.packed 128 cuts23448 = true := by
 decide +kernel
def pointBounds23448 : List (Nat × Nat × Nat) := [(3077353472,102074798588448,102075180140733)]
theorem point_links_checked23448 : (cuts23448.take 1).map (fun c => (3077308417-1+2*2^9*c.k,102074611629444+c.lower,102074993181623+c.upper)) = pointBounds23448 := by
 decide +kernel
def cuts23449 : List PrefixCut := [⟨10,41890441,41890465⟩,
⟨104,445239032,445239283⟩,
⟨128,548040590,548040898⟩]
theorem checked23449 : checkPrefixCuts (2^48) 3077439489 9 Manual.Count131072.C023449.packed 128 cuts23449 = true := by
 decide +kernel
def pointBounds23449 : List (Nat × Nat × Nat) := [(3077449728,102075197925132,102075579477641),(3077545984,102075601273723,102075982826459)]
theorem point_links_checked23449 : (cuts23449.take 2).map (fun c => (3077439489-1+2*2^9*c.k,102075156034691+c.lower,102075537587176+c.upper)) = pointBounds23449 := by
 decide +kernel
def cuts23450 : List PrefixCut := [⟨70,300259993,300260157⟩,
⟨128,544999119,544999431⟩]
theorem checked23450 : checkPrefixCuts (2^48) 3077570561 9 Manual.Count131072.C023450.packed 128 cuts23450 = true := by
 decide +kernel
def pointBounds23450 : List (Nat × Nat × Nat) := [(3077642240,102076004335274,102076385888231)]
theorem point_links_checked23450 : (cuts23450.take 1).map (fun c => (3077570561-1+2*2^9*c.k,102075704075281+c.lower,102076085628074+c.upper)) = pointBounds23450 := by
 decide +kernel
def cuts23451 : List PrefixCut := [⟨36,157760998,157761085⟩,
⟨128,553023832,553024136⟩]
theorem checked23451 : checkPrefixCuts (2^48) 3077701633 9 Manual.Count131072.C023451.packed 128 cuts23451 = true := by
 decide +kernel
def pointBounds23451 : List (Nat × Nat × Nat) := [(3077738496,102076406835398,102076788388590)]
theorem point_links_checked23451 : (cuts23451.take 1).map (fun c => (3077701633-1+2*2^9*c.k,102076249074400+c.lower,102076630627505+c.upper)) = pointBounds23451 := by
 decide +kernel
def cuts23452 : List PrefixCut := [⟨2,7041825,7041829⟩,
⟨96,404578466,404578699⟩,
⟨128,542026161,542026473⟩]
theorem checked23452 : checkPrefixCuts (2^48) 3077832705 9 Manual.Count131072.C023452.packed 128 cuts23452 = true := by
 decide +kernel
def pointBounds23452 : List (Nat × Nat × Nat) := [(3077834752,102076809140057,102077190693470),(3077931008,102077206676698,102077588230340)]
theorem point_links_checked23452 : (cuts23452.take 2).map (fun c => (3077832705-1+2*2^9*c.k,102076802098232+c.lower,102077183651641+c.upper)) = pointBounds23452 := by
 decide +kernel
def cuts23453 : List PrefixCut := [⟨62,264191728,264191875⟩,
⟨128,549410315,549410627⟩]
theorem checked23453 : checkPrefixCuts (2^48) 3077963777 9 Manual.Count131072.C023453.packed 128 cuts23453 = true := by
 decide +kernel
def pointBounds23453 : List (Nat × Nat × Nat) := [(3078027264,102077608316121,102077989869989)]
theorem point_links_checked23453 : (cuts23453.take 1).map (fun c => (3077963777-1+2*2^9*c.k,102077344124393+c.lower,102077725678114+c.upper)) = pointBounds23453 := by
 decide +kernel
def cuts23454 : List PrefixCut := [⟨28,121254865,121254934⟩,
⟨122,525703837,525704139⟩,
⟨128,553044610,553044927⟩]
theorem checked23454 : checkPrefixCuts (2^48) 3078094849 9 Manual.Count131072.C023454.packed 128 cuts23454 = true := by
 decide +kernel
def pointBounds23454 : List (Nat × Nat × Nat) := [(3078123520,102078014789573,102078396343675),(3078219776,102078419238545,102078800792880)]
theorem point_links_checked23454 : (cuts23454.take 2).map (fun c => (3078094849-1+2*2^9*c.k,102077893534708+c.lower,102078275088741+c.upper)) = pointBounds23454 := by
 decide +kernel
def cuts23455 : List PrefixCut := [⟨88,379198769,379198985⟩,
⟨128,551923891,551924197⟩]
theorem checked23455 : checkPrefixCuts (2^48) 3078225921 9 Manual.Count131072.C023455.packed 128 cuts23455 = true := by
 decide +kernel
def pointBounds23455 : List (Nat × Nat × Nat) := [(3078316032,102078825778087,102079207332653)]
theorem point_links_checked23455 : (cuts23455.take 1).map (fun c => (3078225921-1+2*2^9*c.k,102078446579318+c.lower,102078828133668+c.upper)) = pointBounds23455 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000107
