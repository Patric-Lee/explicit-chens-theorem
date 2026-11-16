import PlattAssemblyKernel
import PlattCertificates.Count131072.C013424
import PlattCertificates.Count131072.C013425
import PlattCertificates.Count131072.C013426
import PlattCertificates.Count131072.C013427
import PlattCertificates.Count131072.C013428
import PlattCertificates.Count131072.C013429
import PlattCertificates.Count131072.C013430
import PlattCertificates.Count131072.C013431
import PlattCertificates.Count131072.C013432
import PlattCertificates.Count131072.C013433
import PlattCertificates.Count131072.C013434
import PlattCertificates.Count131072.C013435
import PlattCertificates.Count131072.C013436
import PlattCertificates.Count131072.C013437
import PlattCertificates.Count131072.C013438
import PlattCertificates.Count131072.C013439
import PlattCertificates.Count131072.C013440
import PlattCertificates.Count131072.C013441
import PlattCertificates.Count131072.C013442
import PlattCertificates.Count131072.C013443
import PlattCertificates.Count131072.C013444
import PlattCertificates.Count131072.C013445
import PlattCertificates.Count131072.C013446
import PlattCertificates.Count131072.C013447
import PlattCertificates.Count131072.C013448
import PlattCertificates.Count131072.C013449
import PlattCertificates.Count131072.C013450
import PlattCertificates.Count131072.C013451
import PlattCertificates.Count131072.C013452
import PlattCertificates.Count131072.C013453
import PlattCertificates.Count131072.C013454
import PlattCertificates.Count131072.C013455
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000107
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13424 : List PrefixCut := [⟨28,212926963,212927117⟩,
⟨82,630949782,630950238⟩,
⟨128,980967788,980968491⟩]
theorem checked13424 : checkPrefixCuts (2^48) 1763442689 9 Manual.Count131072.C013424.packed 128 cuts13424 = true := by
 decide +kernel
def pointBounds13424 : List (Nat × Nat × Nat) := [(1763471360,94808411740495,94808788770000),(1763526656,94808829763314,94809206793121)]
theorem point_links_checked13424 : (cuts13424.take 2).map (fun c => (1763442689-1+2*2^9*c.k,94808198813532+c.lower,94808575842883+c.upper)) = pointBounds13424 := by
 decide +kernel
def cuts13425 : List PrefixCut := [⟨8,62564944,62564987⟩,
⟨62,473219775,473220109⟩,
⟨116,880989032,880989656⟩,
⟨128,977543102,977543793⟩]
theorem checked13425 : checkPrefixCuts (2^48) 1763573761 9 Manual.Count131072.C013425.packed 128 cuts13425 = true := by
 decide +kernel
def pointBounds13425 : List (Nat × Nat × Nat) := [(1763581952,94809242346264,94809619376361),(1763637248,94809653001095,94810030031483),(1763692544,94810060770352,94810437801030)]
theorem point_links_checked13425 : (cuts13425.take 3).map (fun c => (1763573761-1+2*2^9*c.k,94809179781320+c.lower,94809556811374+c.upper)) = pointBounds13425 := by
 decide +kernel
def cuts13426 : List PrefixCut := [⟨42,319341622,319341849⟩,
⟨96,742246059,742246588⟩,
⟨128,987205335,987206040⟩]
theorem checked13426 : checkPrefixCuts (2^48) 1763704833 9 Manual.Count131072.C013426.packed 128 cuts13426 = true := by
 decide +kernel
def pointBounds13426 : List (Nat × Nat × Nat) := [(1763747840,94810476666044,94810853697016),(1763803136,94810899570481,94811276601755)]
theorem point_links_checked13426 : (cuts13426.take 2).map (fun c => (1763704833-1+2*2^9*c.k,94810157324422+c.lower,94810534355167+c.upper)) = pointBounds13426 := by
 decide +kernel
def cuts13427 : List PrefixCut := [⟨22,159260908,159261024⟩,
⟨76,574000481,574000890⟩,
⟨128,973567962,973568657⟩]
theorem checked13427 : checkPrefixCuts (2^48) 1763835905 9 Manual.Count131072.C013427.packed 128 cuts13427 = true := by
 decide +kernel
def pointBounds13427 : List (Nat × Nat × Nat) := [(1763858432,94811303790665,94811680822231),(1763913728,94811718530238,94812095562097)]
theorem point_links_checked13427 : (cuts13427.take 2).map (fun c => (1763835905-1+2*2^9*c.k,94811144529757+c.lower,94811521561207+c.upper)) = pointBounds13427 := by
 decide +kernel
def cuts13428 : List PrefixCut := [⟨2,16754761,16754773⟩,
⟨56,438010477,438010782⟩,
⟨110,847764555,847765151⟩,
⟨128,985144174,985144872⟩]
theorem checked13428 : checkPrefixCuts (2^48) 1763966977 9 Manual.Count131072.C013428.packed 128 cuts13428 = true := by
 decide +kernel
def pointBounds13428 : List (Nat × Nat × Nat) := [(1763969024,94812134852480,94812511884637),(1764024320,94812556108196,94812933140646),(1764079616,94812965862274,94813342895015)]
theorem point_links_checked13428 : (cuts13428.take 3).map (fun c => (1763966977-1+2*2^9*c.k,94812118097719+c.lower,94812495129864+c.upper)) = pointBounds13428 := by
 decide +kernel
def cuts13429 : List PrefixCut := [⟨36,266777141,266777332⟩,
⟨90,678579741,678580223⟩,
⟨128,975178128,975178816⟩]
theorem checked13429 : checkPrefixCuts (2^48) 1764098049 9 Manual.Count131072.C013429.packed 128 cuts13429 = true := by
 decide +kernel
def pointBounds13429 : List (Nat × Nat × Nat) := [(1764134912,94813370019034,94813747052068),(1764190208,94813781821634,94814158854959)]
theorem point_links_checked13429 : (cuts13429.take 2).map (fun c => (1764098049-1+2*2^9*c.k,94813103241893+c.lower,94813480274736+c.upper)) = pointBounds13429 := by
 decide +kernel
def cuts13430 : List PrefixCut := [⟨16,125880841,125880931⟩,
⟨70,533190455,533190835⟩,
⟨124,939530112,939530785⟩,
⟨128,970320149,970320844⟩]
theorem checked13430 : checkPrefixCuts (2^48) 1764229121 9 Manual.Count131072.C013430.packed 128 cuts13430 = true := by
 decide +kernel
def pointBounds13430 : List (Nat × Nat × Nat) := [(1764245504,94814204300862,94814581334483),(1764300800,94814611610476,94814988644387),(1764356096,94815017950133,94815394984337)]
theorem point_links_checked13430 : (cuts13430.take 3).map (fun c => (1764229121-1+2*2^9*c.k,94814078420021+c.lower,94814455453552+c.upper)) = pointBounds13430 := by
 decide +kernel
def cuts13431 : List PrefixCut := [⟨50,384789627,384789899⟩,
⟨104,799239642,799240206⟩,
⟨128,986679103,986679800⟩]
theorem checked13431 : checkPrefixCuts (2^48) 1764360193 9 Manual.Count131072.C013431.packed 128 cuts13431 = true := by
 decide +kernel
def pointBounds13431 : List (Nat × Nat × Nat) := [(1764411392,94815433529797,94815810564295),(1764466688,94815847979812,94816225014602)]
theorem point_links_checked13431 : (cuts13431.take 2).map (fun c => (1764360193-1+2*2^9*c.k,94815048740170+c.lower,94815425774396+c.upper)) = pointBounds13431 := by
 decide +kernel
def cuts13432 : List PrefixCut := [⟨30,233218896,233219059⟩,
⟨84,648121521,648121981⟩,
⟨128,984053867,984054568⟩]
theorem checked13432 : checkPrefixCuts (2^48) 1764491265 9 Manual.Count131072.C013432.packed 128 cuts13432 = true := by
 decide +kernel
def pointBounds13432 : List (Nat × Nat × Nat) := [(1764521984,94816268638169,94816645673255),(1764577280,94816683540794,94817060576177)]
theorem point_links_checked13432 : (cuts13432.take 2).map (fun c => (1764491265-1+2*2^9*c.k,94816035419273+c.lower,94816412454196+c.upper)) = pointBounds13432 := by
 decide +kernel
def cuts13433 : List PrefixCut := [⟨10,79116717,79116772⟩,
⟨64,503085036,503085388⟩,
⟨118,924009692,924010343⟩,
⟨128,1000090526,1000091230⟩]
theorem checked13433 : checkPrefixCuts (2^48) 1764622337 9 Manual.Count131072.C013433.packed 128 cuts13433 = true := by
 decide +kernel
def pointBounds13433 : List (Nat × Nat × Nat) := [(1764632576,94817098589857,94817475625536),(1764687872,94817522558176,94817899594152),(1764743168,94817943482832,94818320519107)]
theorem point_links_checked13433 : (cuts13433.take 3).map (fun c => (1764622337-1+2*2^9*c.k,94817019473140+c.lower,94817396508764+c.upper)) = pointBounds13433 := by
 decide +kernel
def cuts13434 : List PrefixCut := [⟨44,342597667,342597907⟩,
⟨98,760625095,760625637⟩,
⟨128,989968381,989969088⟩]
theorem checked13434 : checkPrefixCuts (2^48) 1764753409 9 Manual.Count131072.C013434.packed 128 cuts13434 = true := by
 decide +kernel
def pointBounds13434 : List (Nat × Nat × Nat) := [(1764798464,94818362161333,94818739197901),(1764853760,94818780188761,94819157225631)]
theorem point_links_checked13434 : (cuts13434.take 2).map (fun c => (1764753409-1+2*2^9*c.k,94818019563666+c.lower,94818396599994+c.upper)) = pointBounds13434 := by
 decide +kernel
def cuts13435 : List PrefixCut := [⟨24,187873535,187873666⟩,
⟨78,587374821,587375240⟩,
⟨128,976657642,976658338⟩]
theorem checked13435 : checkPrefixCuts (2^48) 1764884481 9 Manual.Count131072.C013435.packed 128 cuts13435 = true := by
 decide +kernel
def pointBounds13435 : List (Nat × Nat × Nat) := [(1764909056,94819197405582,94819574442748),(1764964352,94819596906868,94819973944322)]
theorem point_links_checked13435 : (cuts13435.take 2).map (fun c => (1764884481-1+2*2^9*c.k,94819009532047+c.lower,94819386569082+c.upper)) = pointBounds13435 := by
 decide +kernel
def cuts13436 : List PrefixCut := [⟨4,31416430,31416451⟩,
⟨58,448434640,448434956⟩,
⟨112,863685807,863686417⟩,
⟨128,987110444,987111140⟩]
theorem checked13436 : checkPrefixCuts (2^48) 1765015553 9 Manual.Count131072.C013436.packed 128 cuts13436 = true := by
 decide +kernel
def pointBounds13436 : List (Nat × Nat × Nat) := [(1765019648,94820017606119,94820394643871),(1765074944,94820434624329,94820811662376),(1765130240,94820849875496,94821226913837)]
theorem point_links_checked13436 : (cuts13436.take 3).map (fun c => (1765015553-1+2*2^9*c.k,94819986189689+c.lower,94820363227420+c.upper)) = pointBounds13436 := by
 decide +kernel
def cuts13437 : List PrefixCut := [⟨38,291972847,291973051⟩,
⟨92,703211412,703211907⟩,
⟨128,981615340,981616033⟩]
theorem checked13437 : checkPrefixCuts (2^48) 1765146625 9 Manual.Count131072.C013437.packed 128 cuts13437 = true := by
 decide +kernel
def pointBounds13437 : List (Nat × Nat × Nat) := [(1765185536,94821265272980,94821642311611),(1765240832,94821676511545,94822053550467)]
theorem point_links_checked13437 : (cuts13437.take 2).map (fun c => (1765146625-1+2*2^9*c.k,94820973300133+c.lower,94821350338560+c.upper)) = pointBounds13437 := by
 decide +kernel
def cuts13438 : List PrefixCut := [⟨18,139359240,139359343⟩,
⟨72,548020824,548021221⟩,
⟨126,951248548,951249233⟩,
⟨128,966076377,966077073⟩]
theorem checked13438 : checkPrefixCuts (2^48) 1765277697 9 Manual.Count131072.C013438.packed 128 cuts13438 = true := by
 decide +kernel
def pointBounds13438 : List (Nat × Nat × Nat) := [(1765296128,94822094274713,94822471313936),(1765351424,94822502936297,94822879975814),(1765406720,94822906164021,94823283203826)]
theorem point_links_checked13438 : (cuts13438.take 3).map (fun c => (1765277697-1+2*2^9*c.k,94821954915473+c.lower,94822331954593+c.upper)) = pointBounds13438 := by
 decide +kernel
def cuts13439 : List PrefixCut := [⟨52,402098902,402099184⟩,
⟨106,816780478,816781058⟩,
⟨128,988325105,988325806⟩]
theorem checked13439 : checkPrefixCuts (2^48) 1765408769 9 Manual.Count131072.C013439.packed 128 cuts13439 = true := by
 decide +kernel
def pointBounds13439 : List (Nat × Nat × Nat) := [(1765462016,94823323090752,94823700130850),(1765517312,94823737772328,94824114812724)]
theorem point_links_checked13439 : (cuts13439.take 2).map (fun c => (1765408769-1+2*2^9*c.k,94822920991850+c.lower,94823298031666+c.upper)) = pointBounds13439 := by
 decide +kernel
def cuts13440 : List PrefixCut := [⟨32,244240076,244240249⟩,
⟨86,659374041,659374504⟩,
⟨128,987773506,987774204⟩]
theorem checked13440 : checkPrefixCuts (2^48) 1765539841 9 Manual.Count131072.C013440.packed 128 cuts13440 = true := by
 decide +kernel
def pointBounds13440 : List (Nat × Nat × Nat) := [(1765572608,94824153557031,94824530597721),(1765627904,94824568690996,94824945731976)]
theorem point_links_checked13440 : (cuts13440.take 2).map (fun c => (1765539841-1+2*2^9*c.k,94823909316955+c.lower,94824286357472+c.upper)) = pointBounds13440 := by
 decide +kernel
def cuts13441 : List PrefixCut := [⟨12,97880626,97880693⟩,
⟨66,509003292,509003655⟩,
⟨120,933503222,933503886⟩,
⟨128,998858780,998859490⟩]
theorem checked13441 : checkPrefixCuts (2^48) 1765670913 9 Manual.Count131072.C013441.packed 128 cuts13441 = true := by
 decide +kernel
def pointBounds13441 : List (Nat × Nat × Nat) := [(1765683200,94824994971087,94825372012369),(1765738496,94825406093753,94825783135331),(1765793792,94825830593683,94826207635562)]
theorem point_links_checked13441 : (cuts13441.take 3).map (fun c => (1765670913-1+2*2^9*c.k,94824897090461+c.lower,94825274131676+c.upper)) = pointBounds13441 := by
 decide +kernel
def cuts13442 : List PrefixCut := [⟨46,349885801,349886054⟩,
⟨100,762085612,762086161⟩,
⟨128,974715710,974716415⟩]
theorem checked13442 : checkPrefixCuts (2^48) 1765801985 9 Manual.Count131072.C013442.packed 128 cuts13442 = true := by
 decide +kernel
def pointBounds13442 : List (Nat × Nat × Nat) := [(1765849088,94826245835042,94826622877220),(1765904384,94826658034853,94827035077327)]
theorem point_links_checked13442 : (cuts13442.take 2).map (fun c => (1765801985-1+2*2^9*c.k,94825895949241+c.lower,94826272991166+c.upper)) = pointBounds13442 := by
 decide +kernel
def cuts13443 : List PrefixCut := [⟨26,195731383,195731520⟩,
⟨80,610614872,610615304⟩,
⟨128,982931180,982931877⟩]
theorem checked13443 : checkPrefixCuts (2^48) 1765933057 9 Manual.Count131072.C013443.packed 128 cuts13443 = true := by
 decide +kernel
def pointBounds13443 : List (Nat × Nat × Nat) := [(1765959680,94827066396334,94827443439101),(1766014976,94827481279823,94827858322885)]
theorem point_links_checked13443 : (cuts13443.take 2).map (fun c => (1765933057-1+2*2^9*c.k,94826870664951+c.lower,94827247707581+c.upper)) = pointBounds13443 := by
 decide +kernel
def cuts13444 : List PrefixCut := [⟨6,45741913,45741946⟩,
⟨60,458208775,458209103⟩,
⟨114,867953438,867954054⟩,
⟨128,975527244,975527934⟩]
theorem checked13444 : checkPrefixCuts (2^48) 1766064129 9 Manual.Count131072.C013444.packed 128 cuts13444 = true := by
 decide +kernel
def pointBounds13444 : List (Nat × Nat × Nat) := [(1766070272,94827899338044,94828276381404),(1766125568,94828311804906,94828688848561),(1766180864,94828721549569,94829098593512)]
theorem point_links_checked13444 : (cuts13444.take 3).map (fun c => (1766064129-1+2*2^9*c.k,94827853596131+c.lower,94828230639458+c.upper)) = pointBounds13444 := by
 decide +kernel
def cuts13445 : List PrefixCut := [⟨40,311401368,311401590⟩,
⟨94,723032746,723033260⟩,
⟨128,985016762,985017464⟩]
theorem checked13445 : checkPrefixCuts (2^48) 1766195201 9 Manual.Count131072.C013445.packed 128 cuts13445 = true := by
 decide +kernel
def pointBounds13445 : List (Nat × Nat × Nat) := [(1766236160,94829140524743,94829517568982),(1766291456,94829552156121,94829929200652)]
theorem point_links_checked13445 : (cuts13445.take 2).map (fun c => (1766195201-1+2*2^9*c.k,94828829123375+c.lower,94829206167392+c.upper)) = pointBounds13445 := by
 decide +kernel
def cuts13446 : List PrefixCut := [⟨20,152980959,152981068⟩,
⟨74,570482544,570482949⟩,
⟨128,975063938,975064634⟩]
theorem checked13446 : checkPrefixCuts (2^48) 1766326273 9 Manual.Count131072.C013446.packed 128 cuts13446 = true := by
 decide +kernel
def pointBounds13446 : List (Nat × Nat × Nat) := [(1766346752,94829967121096,94830344165924),(1766402048,94830384622681,94830761667805),(1766457344,94830789204075,94831166249490)]
theorem point_links_checked13446 : (cuts13446.take 3).map (fun c => (1766326273-1+2*2^9*c.k,94829814140137+c.lower,94830191184856+c.upper)) = pointBounds13446 := by
 decide +kernel
def cuts13447 : List PrefixCut := [⟨54,410942417,410942714⟩,
⟨108,825058761,825059351⟩,
⟨128,985826127,985826829⟩]
theorem checked13447 : checkPrefixCuts (2^48) 1766457345 9 Manual.Count131072.C013447.packed 128 cuts13447 = true := by
 decide +kernel
def pointBounds13447 : List (Nat × Nat × Nat) := [(1766512640,94831200146492,94831577192204),(1766567936,94831614262836,94831991308841)]
theorem point_links_checked13447 : (cuts13447.take 2).map (fun c => (1766457345-1+2*2^9*c.k,94830789204075+c.lower,94831166249490+c.upper)) = pointBounds13447 := by
 decide +kernel
def cuts13448 : List PrefixCut := [⟨34,256841388,256841570⟩,
⟨88,674596302,674596779⟩,
⟨128,984478500,984479193⟩]
theorem checked13448 : checkPrefixCuts (2^48) 1766588417 9 Manual.Count131072.C013448.packed 128 cuts13448 = true := by
 decide +kernel
def pointBounds13448 : List (Nat × Nat × Nat) := [(1766623232,94832031871590,94832408917889),(1766678528,94832449626504,94832826673098)]
theorem point_links_checked13448 : (cuts13448.take 2).map (fun c => (1766588417-1+2*2^9*c.k,94831775030202+c.lower,94832152076319+c.upper)) = pointBounds13448 := by
 decide +kernel
def cuts13449 : List PrefixCut := [⟨14,109771461,109771535⟩,
⟨68,521605543,521605909⟩,
⟨122,921637613,921638262⟩,
⟨128,968315179,968315862⟩]
theorem checked13449 : checkPrefixCuts (2^48) 1766719489 9 Manual.Count131072.C013449.packed 128 cuts13449 = true := by
 decide +kernel
def pointBounds13449 : List (Nat × Nat × Nat) := [(1766733824,94832869280163,94833246327047),(1766789120,94833281114245,94833658161421),(1766844416,94833681146315,94834058193774)]
theorem point_links_checked13449 : (cuts13449.take 3).map (fun c => (1766719489-1+2*2^9*c.k,94832759508702+c.lower,94833136555512+c.upper)) = pointBounds13449 := by
 decide +kernel
def cuts13450 : List PrefixCut := [⟨48,371980970,371981235⟩,
⟨102,781546100,781546649⟩,
⟨128,977164282,977164973⟩]
theorem checked13450 : checkPrefixCuts (2^48) 1766850561 9 Manual.Count131072.C013450.packed 128 cuts13450 = true := by
 decide +kernel
def pointBounds13450 : List (Nat × Nat × Nat) := [(1766899712,94834099804851,94834476852609),(1766955008,94834509369981,94834886418023)]
theorem point_links_checked13450 : (cuts13450.take 2).map (fun c => (1766850561-1+2*2^9*c.k,94833727823881+c.lower,94834104871374+c.upper)) = pointBounds13450 := by
 decide +kernel
def cuts13451 : List PrefixCut := [⟨28,216004975,216005130⟩,
⟨82,625863146,625863593⟩,
⟨128,976135912,976136612⟩]
theorem checked13451 : checkPrefixCuts (2^48) 1766981633 9 Manual.Count131072.C013451.packed 128 cuts13451 = true := by
 decide +kernel
def pointBounds13451 : List (Nat × Nat × Nat) := [(1767010304,94834920993138,94835298041477),(1767065600,94835330851309,94835707899940)]
theorem point_links_checked13451 : (cuts13451.take 2).map (fun c => (1766981633-1+2*2^9*c.k,94834704988163+c.lower,94835082036347+c.upper)) = pointBounds13451 := by
 decide +kernel
def cuts13452 : List PrefixCut := [⟨8,56227541,56227581⟩,
⟨62,468289967,468290303⟩,
⟨116,882887946,882888575⟩,
⟨128,975426093,975426789⟩]
theorem checked13452 : checkPrefixCuts (2^48) 1767112705 9 Manual.Count131072.C013452.packed 128 cuts13452 = true := by
 decide +kernel
def pointBounds13452 : List (Nat × Nat × Nat) := [(1767120896,94835737351616,94836114400540),(1767176192,94836149414042,94836526463262),(1767231488,94836564012021,94836941061534)]
theorem point_links_checked13452 : (cuts13452.take 3).map (fun c => (1767112705-1+2*2^9*c.k,94835681124075+c.lower,94836058172959+c.upper)) = pointBounds13452 := by
 decide +kernel
def cuts13453 : List PrefixCut := [⟨42,323321038,323321268⟩,
⟨96,740282215,740282737⟩,
⟨128,989528882,989529583⟩]
theorem checked13453 : checkPrefixCuts (2^48) 1767243777 9 Manual.Count131072.C013453.packed 128 cuts13453 = true := by
 decide +kernel
def pointBounds13453 : List (Nat × Nat × Nat) := [(1767286784,94836979871206,94837356921016),(1767342080,94837396832383,94837773882485)]
theorem point_links_checked13453 : (cuts13453.take 2).map (fun c => (1767243777-1+2*2^9*c.k,94836656550168+c.lower,94837033599748+c.upper)) = pointBounds13453 := by
 decide +kernel
def cuts13454 : List PrefixCut := [⟨22,167382833,167382955⟩,
⟨76,580336324,580336735⟩,
⟨128,987862581,987863274⟩]
theorem checked13454 : checkPrefixCuts (2^48) 1767374849 9 Manual.Count131072.C013454.packed 128 cuts13454 = true := by
 decide +kernel
def pointBounds13454 : List (Nat × Nat × Nat) := [(1767397376,94837813461883,94838190512286),(1767452672,94838226415374,94838603466066)]
theorem point_links_checked13454 : (cuts13454.take 2).map (fun c => (1767374849-1+2*2^9*c.k,94837646079050+c.lower,94838023129331+c.upper)) = pointBounds13454 := by
 decide +kernel
def cuts13455 : List PrefixCut := [⟨2,14173220,14173229⟩,
⟨56,431082093,431082393⟩,
⟨110,845589320,845589918⟩,
⟨128,988744965,988745664⟩]
theorem checked13455 : checkPrefixCuts (2^48) 1767505921 9 Manual.Count131072.C013455.packed 128 cuts13455 = true := by
 decide +kernel
def pointBounds13455 : List (Nat × Nat × Nat) := [(1767507968,94838648114851,94839025165834),(1767563264,94839065023724,94839442074998),(1767618560,94839479530951,94839856582523)]
theorem point_links_checked13455 : (cuts13455.take 3).map (fun c => (1767505921-1+2*2^9*c.k,94838633941631+c.lower,94839010992605+c.upper)) = pointBounds13455 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000107
