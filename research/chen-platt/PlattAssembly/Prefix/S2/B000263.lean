import PlattAssemblyKernel
import PlattCertificates.Count131072.C018416
import PlattCertificates.Count131072.C018417
import PlattCertificates.Count131072.C018418
import PlattCertificates.Count131072.C018419
import PlattCertificates.Count131072.C018420
import PlattCertificates.Count131072.C018421
import PlattCertificates.Count131072.C018422
import PlattCertificates.Count131072.C018423
import PlattCertificates.Count131072.C018424
import PlattCertificates.Count131072.C018425
import PlattCertificates.Count131072.C018426
import PlattCertificates.Count131072.C018427
import PlattCertificates.Count131072.C018428
import PlattCertificates.Count131072.C018429
import PlattCertificates.Count131072.C018430
import PlattCertificates.Count131072.C018431
import PlattCertificates.Count131072.C018432
import PlattCertificates.Count131072.C018433
import PlattCertificates.Count131072.C018434
import PlattCertificates.Count131072.C018435
import PlattCertificates.Count131072.C018436
import PlattCertificates.Count131072.C018437
import PlattCertificates.Count131072.C018438
import PlattCertificates.Count131072.C018439
import PlattCertificates.Count131072.C018440
import PlattCertificates.Count131072.C018441
import PlattCertificates.Count131072.C018442
import PlattCertificates.Count131072.C018443
import PlattCertificates.Count131072.C018444
import PlattCertificates.Count131072.C018445
import PlattCertificates.Count131072.C018446
import PlattCertificates.Count131072.C018447
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000263
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18416 : List PrefixCut := [⟨48,254258630,254258787⟩,
⟨122,664857136,664857538⟩,
⟨128,699199213,699199636⟩]
theorem checked18416 : checkPrefixCuts (2^48) 2417754113 9 Manual.Count131072.C018416.packed 128 cuts18416 = true := by
 decide +kernel
def pointBounds18416 : List (Nat × Nat × Nat) := [(2417803264,98949764241214,98950143972522),(2417879040,98950174839720,98950554571273)]
theorem point_links_checked18416 : (cuts18416.take 2).map (fun c => (2417754113-1+2*2^9*c.k,98949509982584+c.lower,98949889713735+c.upper)) = pointBounds18416 := by
 decide +kernel
def cuts18417 : List PrefixCut := [⟨68,369258877,369259104⟩,
⟨128,699976398,699976825⟩]
theorem checked18417 : checkPrefixCuts (2^48) 2417885185 9 Manual.Count131072.C018417.packed 128 cuts18417 = true := by
 decide +kernel
def pointBounds18417 : List (Nat × Nat × Nat) := [(2417954816,98950578440674,98950958172475)]
theorem point_links_checked18417 : (cuts18417.take 1).map (fun c => (2417885185-1+2*2^9*c.k,98950209181797+c.lower,98950588913371+c.upper)) = pointBounds18417 := by
 decide +kernel
def cuts18418 : List PrefixCut := [⟨14,77643482,77643529⟩,
⟨88,483547100,483547387⟩,
⟨128,705060174,705060598⟩]
theorem checked18418 : checkPrefixCuts (2^48) 2418016257 9 Manual.Count131072.C018418.packed 128 cuts18418 = true := by
 decide +kernel
def pointBounds18418 : List (Nat × Nat × Nat) := [(2418030592,98950986801677,98951366533725),(2418106368,98951392705295,98951772437583)]
theorem point_links_checked18418 : (cuts18418.take 2).map (fun c => (2418016257-1+2*2^9*c.k,98950909158195+c.lower,98951288890196+c.upper)) = pointBounds18418 := by
 decide +kernel
def cuts18419 : List PrefixCut := [⟨34,181118737,181118848⟩,
⟨108,593166170,593166526⟩,
⟨128,706418733,706419157⟩]
theorem checked18419 : checkPrefixCuts (2^48) 2418147329 9 Manual.Count131072.C018419.packed 128 cuts18419 = true := by
 decide +kernel
def pointBounds18419 : List (Nat × Nat × Nat) := [(2418182144,98951795337106,98952175069642),(2418257920,98952207384539,98952587117320)]
theorem point_links_checked18419 : (cuts18419.take 2).map (fun c => (2418147329-1+2*2^9*c.k,98951614218369+c.lower,98951993950794+c.upper)) = pointBounds18419 := by
 decide +kernel
def cuts18420 : List PrefixCut := [⟨54,296570387,296570567⟩,
⟨128,705100177,705100605⟩]
theorem checked18420 : checkPrefixCuts (2^48) 2418278401 9 Manual.Count131072.C018420.packed 128 cuts18420 = true := by
 decide +kernel
def pointBounds18420 : List (Nat × Nat × Nat) := [(2418333696,98952617207489,98952996940518),(2418409472,98953025737279,98953405470556)]
theorem point_links_checked18420 : (cuts18420.take 2).map (fun c => (2418278401-1+2*2^9*c.k,98952320637102+c.lower,98952700369951+c.upper)) = pointBounds18420 := by
 decide +kernel
def cuts18421 : List PrefixCut := [⟨74,415383810,415384060⟩,
⟨128,714954849,714955274⟩]
theorem checked18421 : checkPrefixCuts (2^48) 2418409473 9 Manual.Count131072.C018421.packed 128 cuts18421 = true := by
 decide +kernel
def pointBounds18421 : List (Nat × Nat × Nat) := [(2418485248,98953441121089,98953820854616)]
theorem point_links_checked18421 : (cuts18421.take 1).map (fun c => (2418409473-1+2*2^9*c.k,98953025737279+c.lower,98953405470556+c.upper)) = pointBounds18421 := by
 decide +kernel
def cuts18422 : List PrefixCut := [⟨20,110446182,110446250⟩,
⟨94,528364297,528364613⟩,
⟨128,717709119,717709550⟩]
theorem checked18422 : checkPrefixCuts (2^48) 2418540545 9 Manual.Count131072.C018422.packed 128 cuts18422 = true := by
 decide +kernel
def pointBounds18422 : List (Nat × Nat × Nat) := [(2418561024,98953851138310,98954230872080),(2418636800,98954269056425,98954648790443)]
theorem point_links_checked18422 : (cuts18422.take 2).map (fun c => (2418540545-1+2*2^9*c.k,98953740692128+c.lower,98954120425830+c.upper)) = pointBounds18422 := by
 decide +kernel
def cuts18423 : List PrefixCut := [⟨40,220879400,220879535⟩,
⟨114,636560325,636560709⟩,
⟨128,715575459,715575889⟩]
theorem checked18423 : checkPrefixCuts (2^48) 2418671617 9 Manual.Count131072.C018423.packed 128 cuts18423 = true := by
 decide +kernel
def pointBounds18423 : List (Nat × Nat × Nat) := [(2418712576,98954679280647,98955059014915),(2418788352,98955094961572,98955474696089)]
theorem point_links_checked18423 : (cuts18423.take 2).map (fun c => (2418671617-1+2*2^9*c.k,98954458401247+c.lower,98954838135380+c.upper)) = pointBounds18423 := by
 decide +kernel
def cuts18424 : List PrefixCut := [⟨60,330950694,330950899⟩,
⟨128,702271023,702271453⟩]
theorem checked18424 : checkPrefixCuts (2^48) 2418802689 9 Manual.Count131072.C018424.packed 128 cuts18424 = true := by
 decide +kernel
def pointBounds18424 : List (Nat × Nat × Nat) := [(2418864128,98955504927400,98955884662168)]
theorem point_links_checked18424 : (cuts18424.take 1).map (fun c => (2418802689-1+2*2^9*c.k,98955173976706+c.lower,98955553711269+c.upper)) = pointBounds18424 := by
 decide +kernel
def cuts18425 : List PrefixCut := [⟨6,33396198,33396218⟩,
⟨80,443569062,443569326⟩,
⟨128,708051044,708051462⟩]
theorem checked18425 : checkPrefixCuts (2^48) 2418933761 9 Manual.Count131072.C018425.packed 128 cuts18425 = true := by
 decide +kernel
def pointBounds18425 : List (Nat × Nat × Nat) := [(2418939904,98955909643927,98956289378940),(2419015680,98956319816791,98956699552048)]
theorem point_links_checked18425 : (cuts18425.take 2).map (fun c => (2418933761-1+2*2^9*c.k,98955876247729+c.lower,98956255982722+c.upper)) = pointBounds18425 := by
 decide +kernel
def cuts18426 : List PrefixCut := [⟨26,136951329,136951412⟩,
⟨100,547796525,547796856⟩,
⟨128,702311030,702311452⟩]
theorem checked18426 : checkPrefixCuts (2^48) 2419064833 9 Manual.Count131072.C018426.packed 128 cuts18426 = true := by
 decide +kernel
def pointBounds18426 : List (Nat × Nat × Nat) := [(2419091456,98956721250102,98957100985596),(2419167232,98957132095298,98957511831040)]
theorem point_links_checked18426 : (cuts18426.take 2).map (fun c => (2419064833-1+2*2^9*c.k,98956584298773+c.lower,98956964034184+c.upper)) = pointBounds18426 := by
 decide +kernel
def cuts18427 : List PrefixCut := [⟨46,250965806,250965956⟩,
⟨120,665857482,665857887⟩,
⟨128,710882803,710883235⟩]
theorem checked18427 : checkPrefixCuts (2^48) 2419195905 9 Manual.Count131072.C018427.packed 128 cuts18427 = true := by
 decide +kernel
def pointBounds18427 : List (Nat × Nat × Nat) := [(2419243008,98957537575609,98957917311592),(2419318784,98957952467285,98958332203523)]
theorem point_links_checked18427 : (cuts18427.take 2).map (fun c => (2419195905-1+2*2^9*c.k,98957286609803+c.lower,98957666345636+c.upper)) = pointBounds18427 := by
 decide +kernel
def cuts18428 : List PrefixCut := [⟨66,364268893,364269111⟩,
⟨128,707586775,707587204⟩]
theorem checked18428 : checkPrefixCuts (2^48) 2419326977 9 Manual.Count131072.C018428.packed 128 cuts18428 = true := by
 decide +kernel
def pointBounds18428 : List (Nat × Nat × Nat) := [(2419394560,98958361761499,98958741497982)]
theorem point_links_checked18428 : (cuts18428.take 1).map (fun c => (2419326977-1+2*2^9*c.k,98957997492606+c.lower,98958377228871+c.upper)) = pointBounds18428 := by
 decide +kernel
def cuts18429 : List PrefixCut := [⟨12,66545163,66545204⟩,
⟨86,478722112,478722401⟩,
⟨128,708246597,708247024⟩]
theorem checked18429 : checkPrefixCuts (2^48) 2419458049 9 Manual.Count131072.C018429.packed 128 cuts18429 = true := by
 decide +kernel
def pointBounds18429 : List (Nat × Nat × Nat) := [(2419470336,98958771624544,98959151361279),(2419546112,98959183801493,98959563538476)]
theorem point_links_checked18429 : (cuts18429.take 2).map (fun c => (2419458049-1+2*2^9*c.k,98958705079381+c.lower,98959084816075+c.upper)) = pointBounds18429 := by
 decide +kernel
def cuts18430 : List PrefixCut := [⟨32,173798370,173798476⟩,
⟨106,584204550,584204902⟩,
⟨128,705416170,705416595⟩]
theorem checked18430 : checkPrefixCuts (2^48) 2419589121 9 Manual.Count131072.C018430.packed 128 cuts18430 = true := by
 decide +kernel
def pointBounds18430 : List (Nat × Nat × Nat) := [(2419621888,98959587124348,98959966861575),(2419697664,98959997530528,98960377268001)]
theorem point_links_checked18430 : (cuts18430.take 2).map (fun c => (2419589121-1+2*2^9*c.k,98959413325978+c.lower,98959793063099+c.upper)) = pointBounds18430 := by
 decide +kernel
def cuts18431 : List PrefixCut := [⟨52,283830791,283830965⟩,
⟨126,694211314,694211737⟩,
⟨128,704563717,704564147⟩]
theorem checked18431 : checkPrefixCuts (2^48) 2419720193 9 Manual.Count131072.C018431.packed 128 cuts18431 = true := by
 decide +kernel
def pointBounds18431 : List (Nat × Nat × Nat) := [(2419773440,98960402572939,98960782310659),(2419849216,98960812953462,98961192691431)]
theorem point_links_checked18431 : (cuts18431.take 2).map (fun c => (2419720193-1+2*2^9*c.k,98960118742148+c.lower,98960498479694+c.upper)) = pointBounds18431 := by
 decide +kernel
def cuts18432 : List PrefixCut := [⟨72,394199355,394199592⟩,
⟨128,700687193,700687619⟩]
theorem checked18432 : checkPrefixCuts (2^48) 2419851265 9 Manual.Count131072.C018432.packed 128 cuts18432 = true := by
 decide +kernel
def pointBounds18432 : List (Nat × Nat × Nat) := [(2419924992,98961217505220,98961597243433)]
theorem point_links_checked18432 : (cuts18432.take 1).map (fun c => (2419851265-1+2*2^9*c.k,98960823305865+c.lower,98961203043841+c.upper)) = pointBounds18432 := by
 decide +kernel
def cuts18433 : List PrefixCut := [⟨18,99214425,99214487⟩,
⟨92,499437357,499437661⟩,
⟨128,701579557,701579983⟩]
theorem checked18433 : checkPrefixCuts (2^48) 2419982337 9 Manual.Count131072.C018433.packed 128 cuts18433 = true := by
 decide +kernel
def pointBounds18433 : List (Nat × Nat × Nat) := [(2420000768,98961623207483,98962002945947),(2420076544,98962023430415,98962403169121)]
theorem point_links_checked18433 : (cuts18433.take 2).map (fun c => (2419982337-1+2*2^9*c.k,98961523993058+c.lower,98961903731460+c.upper)) = pointBounds18433 := by
 decide +kernel
def cuts18434 : List PrefixCut := [⟨38,209698938,209699069⟩,
⟨112,618852205,618852581⟩,
⟨128,705612436,705612863⟩]
theorem checked18434 : checkPrefixCuts (2^48) 2420113409 9 Manual.Count131072.C018434.packed 128 cuts18434 = true := by
 decide +kernel
def pointBounds18434 : List (Nat × Nat × Nat) := [(2420152320,98962435271553,98962815010512),(2420228096,98962844424820,98963224164024)]
theorem point_links_checked18434 : (cuts18434.take 2).map (fun c => (2420113409-1+2*2^9*c.k,98962225572615+c.lower,98962605311443+c.upper)) = pointBounds18434 := by
 decide +kernel
def cuts18435 : List PrefixCut := [⟨58,321798710,321798908⟩,
⟨128,707551255,707551684⟩]
theorem checked18435 : checkPrefixCuts (2^48) 2420244481 9 Manual.Count131072.C018435.packed 128 cuts18435 = true := by
 decide +kernel
def pointBounds18435 : List (Nat × Nat × Nat) := [(2420303872,98963252983761,98963632723214)]
theorem point_links_checked18435 : (cuts18435.take 1).map (fun c => (2420244481-1+2*2^9*c.k,98962931185051+c.lower,98963310924306+c.upper)) = pointBounds18435 := by
 decide +kernel
def cuts18436 : List PrefixCut := [⟨4,21281763,21281776⟩,
⟨78,423884231,423884490⟩,
⟨128,701581916,701582342⟩]
theorem checked18436 : checkPrefixCuts (2^48) 2420375553 9 Manual.Count131072.C018436.packed 128 cuts18436 = true := by
 decide +kernel
def pointBounds18436 : List (Nat × Nat × Nat) := [(2420379648,98963660018069,98964039757766),(2420455424,98964062620537,98964442360480)]
theorem point_links_checked18436 : (cuts18436.take 2).map (fun c => (2420375553-1+2*2^9*c.k,98963638736306+c.lower,98964018475990+c.upper)) = pointBounds18436 := by
 decide +kernel
def cuts18437 : List PrefixCut := [⟨24,133032328,133032409⟩,
⟨98,540726237,540726569⟩,
⟨128,707358405,707358839⟩]
theorem checked18437 : checkPrefixCuts (2^48) 2420506625 9 Manual.Count131072.C018437.packed 128 cuts18437 = true := by
 decide +kernel
def pointBounds18437 : List (Nat × Nat × Nat) := [(2420531200,98964473350550,98964853090741),(2420606976,98964881044459,98965260784901)]
theorem point_links_checked18437 : (cuts18437.take 2).map (fun c => (2420506625-1+2*2^9*c.k,98964340318222+c.lower,98964720058332+c.upper)) = pointBounds18437 := by
 decide +kernel
def cuts18438 : List PrefixCut := [⟨44,243258232,243258379⟩,
⟨118,650577712,650578103⟩,
⟨128,707087479,707087903⟩]
theorem checked18438 : checkPrefixCuts (2^48) 2420637697 9 Manual.Count131072.C018438.packed 128 cuts18438 = true := by
 decide +kernel
def pointBounds18438 : List (Nat × Nat × Nat) := [(2420682752,98965290934859,98965670675550),(2420758528,98965698254339,98966077995274)]
theorem point_links_checked18438 : (cuts18438.take 2).map (fun c => (2420637697-1+2*2^9*c.k,98965047676627+c.lower,98965427417171+c.upper)) = pointBounds18438 := by
 decide +kernel
def cuts18439 : List PrefixCut := [⟨64,353354927,353355143⟩,
⟨128,709490757,709491184⟩]
theorem checked18439 : checkPrefixCuts (2^48) 2420768769 9 Manual.Count131072.C018439.packed 128 cuts18439 = true := by
 decide +kernel
def pointBounds18439 : List (Nat × Nat × Nat) := [(2420834304,98966108119033,98966487860217)]
theorem point_links_checked18439 : (cuts18439.take 1).map (fun c => (2420768769-1+2*2^9*c.k,98965754764106+c.lower,98966134505074+c.upper)) = pointBounds18439 := by
 decide +kernel
def cuts18440 : List PrefixCut := [⟨10,52785881,52785912⟩,
⟨84,459020661,459020935⟩,
⟨128,693291606,693292019⟩]
theorem checked18440 : checkPrefixCuts (2^48) 2420899841 9 Manual.Count131072.C018440.packed 128 cuts18440 = true := by
 decide +kernel
def pointBounds18440 : List (Nat × Nat × Nat) := [(2420910080,98966517040744,98966896782170),(2420985856,98966923275524,98967303017193)]
theorem point_links_checked18440 : (cuts18440.take 2).map (fun c => (2420899841-1+2*2^9*c.k,98966464254863+c.lower,98966843996258+c.upper)) = pointBounds18440 := by
 decide +kernel
def cuts18441 : List PrefixCut := [⟨30,169393255,169393358⟩,
⟨104,573277464,573277804⟩,
⟨128,706623897,706624317⟩]
theorem checked18441 : checkPrefixCuts (2^48) 2421030913 9 Manual.Count131072.C018441.packed 128 cuts18441 = true := by
 decide +kernel
def pointBounds18441 : List (Nat × Nat × Nat) := [(2421061632,98967326939724,98967706681635),(2421137408,98967730823933,98968110566081)]
theorem point_links_checked18441 : (cuts18441.take 2).map (fun c => (2421030913-1+2*2^9*c.k,98967157546469+c.lower,98967537288277+c.upper)) = pointBounds18441 := by
 decide +kernel
def cuts18442 : List PrefixCut := [⟨50,269246314,269246481⟩,
⟨124,674616412,674616825⟩,
⟨128,696122647,696123074⟩]
theorem checked18442 : checkPrefixCuts (2^48) 2421161985 9 Manual.Count131072.C018442.packed 128 cuts18442 = true := by
 decide +kernel
def pointBounds18442 : List (Nat × Nat × Nat) := [(2421213184,98968133416680,98968513159075),(2421288960,98968538786778,98968918529419)]
theorem point_links_checked18442 : (cuts18442.take 2).map (fun c => (2421161985-1+2*2^9*c.k,98967864170366+c.lower,98968243912594+c.upper)) = pointBounds18442 := by
 decide +kernel
def cuts18443 : List PrefixCut := [⟨70,385013689,385013924⟩,
⟨128,702827394,702827822⟩]
theorem checked18443 : checkPrefixCuts (2^48) 2421293057 9 Manual.Count131072.C018443.packed 128 cuts18443 = true := by
 decide +kernel
def pointBounds18443 : List (Nat × Nat × Nat) := [(2421364736,98968945306702,98969325049592)]
theorem point_links_checked18443 : (cuts18443.take 1).map (fun c => (2421293057-1+2*2^9*c.k,98968560293013+c.lower,98968940035668+c.upper)) = pointBounds18443 := by
 decide +kernel
def cuts18444 : List PrefixCut := [⟨16,90669645,90669698⟩,
⟨90,495536766,495537058⟩,
⟨128,702440709,702441127⟩]
theorem checked18444 : checkPrefixCuts (2^48) 2421424129 9 Manual.Count131072.C018444.packed 128 cuts18444 = true := by
 decide +kernel
def pointBounds18444 : List (Nat × Nat × Nat) := [(2421440512,98969353790052,98969733533188),(2421516288,98969758657173,98970138400548)]
theorem point_links_checked18444 : (cuts18444.take 2).map (fun c => (2421424129-1+2*2^9*c.k,98969263120407+c.lower,98969642863490+c.upper)) = pointBounds18444 := by
 decide +kernel
def cuts18445 : List PrefixCut := [⟨36,197369375,197369494⟩,
⟨110,608371548,608371915⟩,
⟨128,704378672,704379097⟩]
theorem checked18445 : checkPrefixCuts (2^48) 2421555201 9 Manual.Count131072.C018445.packed 128 cuts18445 = true := by
 decide +kernel
def pointBounds18445 : List (Nat × Nat × Nat) := [(2421592064,98970162930491,98970542674111),(2421667840,98970573932664,98970953676532)]
theorem point_links_checked18445 : (cuts18445.take 2).map (fun c => (2421555201-1+2*2^9*c.k,98969965561116+c.lower,98970345304617+c.upper)) = pointBounds18445 := by
 decide +kernel
def cuts18446 : List PrefixCut := [⟨56,313006230,313006418⟩,
⟨128,706781391,706781814⟩]
theorem checked18446 : checkPrefixCuts (2^48) 2421686273 9 Manual.Count131072.C018446.packed 128 cuts18446 = true := by
 decide +kernel
def pointBounds18446 : List (Nat × Nat × Nat) := [(2421743616,98970982946018,98971362690132)]
theorem point_links_checked18446 : (cuts18446.take 1).map (fun c => (2421686273-1+2*2^9*c.k,98970669939788+c.lower,98971049683714+c.upper)) = pointBounds18446 := by
 decide +kernel
def cuts18447 : List PrefixCut := [⟨2,11157562,11157569⟩,
⟨76,415961375,415961622⟩,
⟨128,705580727,705581146⟩]
theorem checked18447 : checkPrefixCuts (2^48) 2421817345 9 Manual.Count131072.C018447.packed 128 cuts18447 = true := by
 decide +kernel
def pointBounds18447 : List (Nat × Nat × Nat) := [(2421819392,98971387878741,98971767623097),(2421895168,98971792682554,98972172427150)]
theorem point_links_checked18447 : (cuts18447.take 2).map (fun c => (2421817345-1+2*2^9*c.k,98971376721179+c.lower,98971756465528+c.upper)) = pointBounds18447 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000263
