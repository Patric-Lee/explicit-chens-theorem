import PlattAssemblyKernel
import PlattCertificates.Count131072.C016560
import PlattCertificates.Count131072.C016561
import PlattCertificates.Count131072.C016562
import PlattCertificates.Count131072.C016563
import PlattCertificates.Count131072.C016564
import PlattCertificates.Count131072.C016565
import PlattCertificates.Count131072.C016566
import PlattCertificates.Count131072.C016567
import PlattCertificates.Count131072.C016568
import PlattCertificates.Count131072.C016569
import PlattCertificates.Count131072.C016570
import PlattCertificates.Count131072.C016571
import PlattCertificates.Count131072.C016572
import PlattCertificates.Count131072.C016573
import PlattCertificates.Count131072.C016574
import PlattCertificates.Count131072.C016575
import PlattCertificates.Count131072.C016576
import PlattCertificates.Count131072.C016577
import PlattCertificates.Count131072.C016578
import PlattCertificates.Count131072.C016579
import PlattCertificates.Count131072.C016580
import PlattCertificates.Count131072.C016581
import PlattCertificates.Count131072.C016582
import PlattCertificates.Count131072.C016583
import PlattCertificates.Count131072.C016584
import PlattCertificates.Count131072.C016585
import PlattCertificates.Count131072.C016586
import PlattCertificates.Count131072.C016587
import PlattCertificates.Count131072.C016588
import PlattCertificates.Count131072.C016589
import PlattCertificates.Count131072.C016590
import PlattCertificates.Count131072.C016591
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000205
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16560 : List PrefixCut := [⟨30,181091471,181091590⟩,
⟨97,589476458,589476835⟩,
⟨128,778843624,778844120⟩]
theorem checked16560 : checkPrefixCuts (2^48) 2174484481 9 Manual.Count131072.C016560.packed 128 cuts16560 = true := by
 decide +kernel
def pointBounds16560 : List (Nat × Nat × Nat) := [(2174515200,97564804877758,97565183752708),(2174583808,97565213262745,97565592137953)]
theorem point_links_checked16560 : (cuts16560.take 2).map (fun c => (2174484481-1+2*2^9*c.k,97564623786287+c.lower,97565002661118+c.upper)) = pointBounds16560 := by
 decide +kernel
def cuts16561 : List PrefixCut := [⟨36,221593589,221593732⟩,
⟨103,629564499,629564902⟩,
⟨128,791222047,791222553⟩]
theorem checked16561 : checkPrefixCuts (2^48) 2174615553 9 Manual.Count131072.C016561.packed 128 cuts16561 = true := by
 decide +kernel
def pointBounds16561 : List (Nat × Nat × Nat) := [(2174652416,97565624223500,97566003098970),(2174721024,97566032194410,97566411070140)]
theorem point_links_checked16561 : (cuts16561.take 2).map (fun c => (2174615553-1+2*2^9*c.k,97565402629911+c.lower,97565781505238+c.upper)) = pointBounds16561 := by
 decide +kernel
def cuts16562 : List PrefixCut := [⟨42,259890504,259890668⟩,
⟨109,676895343,676895774⟩,
⟨128,795445523,795446026⟩]
theorem checked16562 : checkPrefixCuts (2^48) 2174746625 9 Manual.Count131072.C016562.packed 128 cuts16562 = true := by
 decide +kernel
def pointBounds16562 : List (Nat × Nat × Nat) := [(2174789632,97566453742462,97566832618459),(2174858240,97566870747301,97567249623565)]
theorem point_links_checked16562 : (cuts16562.take 2).map (fun c => (2174746625-1+2*2^9*c.k,97566193851958+c.lower,97566572727791+c.upper)) = pointBounds16562 := by
 decide +kernel
def cuts16563 : List PrefixCut := [⟨48,292617614,292617800⟩,
⟨115,708690190,708690638⟩,
⟨128,789703113,789703614⟩]
theorem checked16563 : checkPrefixCuts (2^48) 2174877697 9 Manual.Count131072.C016563.packed 128 cuts16563 = true := by
 decide +kernel
def pointBounds16563 : List (Nat × Nat × Nat) := [(2174926848,97567281915095,97567660791617),(2174995456,97567697987671,97568076864455)]
theorem point_links_checked16563 : (cuts16563.take 2).map (fun c => (2174877697-1+2*2^9*c.k,97566989297481+c.lower,97567368173817+c.upper)) = pointBounds16563 := by
 decide +kernel
def cuts16564 : List PrefixCut := [⟨54,332975994,332976205⟩,
⟨121,751092897,751093368⟩,
⟨128,794443785,794444283⟩]
theorem checked16564 : checkPrefixCuts (2^48) 2175008769 9 Manual.Count131072.C016564.packed 128 cuts16564 = true := by
 decide +kernel
def pointBounds16564 : List (Nat × Nat × Nat) := [(2175064064,97568111976588,97568490853636),(2175132672,97568530093491,97568908970799)]
theorem point_links_checked16564 : (cuts16564.take 2).map (fun c => (2175008769-1+2*2^9*c.k,97567779000594+c.lower,97568157877431+c.upper)) = pointBounds16564 := by
 decide +kernel
def cuts16565 : List PrefixCut := [⟨60,369706055,369706287⟩,
⟨127,785596761,785597259⟩,
⟨128,791031462,791031964⟩]
theorem checked16565 : checkPrefixCuts (2^48) 2175139841 9 Manual.Count131072.C016565.packed 128 cuts16565 = true := by
 decide +kernel
def pointBounds16565 : List (Nat × Nat × Nat) := [(2175201280,97568943150434,97569322028001),(2175269888,97569359041140,97569737918973)]
theorem point_links_checked16565 : (cuts16565.take 2).map (fun c => (2175139841-1+2*2^9*c.k,97568573444379+c.lower,97568952321714+c.upper)) = pointBounds16565 := by
 decide +kernel
def cuts16566 : List PrefixCut := [⟨66,411089912,411090174⟩,
⟨128,786325930,786326434⟩]
theorem checked16566 : checkPrefixCuts (2^48) 2175270913 9 Manual.Count131072.C016566.packed 128 cuts16566 = true := by
 decide +kernel
def pointBounds16566 : List (Nat × Nat × Nat) := [(2175338496,97569775565753,97570154443852)]
theorem point_links_checked16566 : (cuts16566.take 1).map (fun c => (2175270913-1+2*2^9*c.k,97569364475841+c.lower,97569743353678+c.upper)) = pointBounds16566 := by
 decide +kernel
def cuts16567 : List PrefixCut := [⟨5,31312302,31312320⟩,
⟨72,450010201,450010481⟩,
⟨128,799993214,799993712⟩]
theorem checked16567 : checkPrefixCuts (2^48) 2175401985 9 Manual.Count131072.C016567.packed 128 cuts16567 = true := by
 decide +kernel
def pointBounds16567 : List (Nat × Nat × Nat) := [(2175407104,97570182114073,97570560992432),(2175475712,97570600811972,97570979690593)]
theorem point_links_checked16567 : (cuts16567.take 2).map (fun c => (2175401985-1+2*2^9*c.k,97570150801771+c.lower,97570529680112+c.upper)) = pointBounds16567 := by
 decide +kernel
def cuts16568 : List PrefixCut := [⟨11,69348584,69348629⟩,
⟨78,483362464,483362770⟩,
⟨128,798909921,798910424⟩]
theorem checked16568 : checkPrefixCuts (2^48) 2175533057 9 Manual.Count131072.C016568.packed 128 cuts16568 = true := by
 decide +kernel
def pointBounds16568 : List (Nat × Nat × Nat) := [(2175544320,97571020143569,97571399022453),(2175612928,97571434157449,97571813036594)]
theorem point_links_checked16568 : (cuts16568.take 2).map (fun c => (2175533057-1+2*2^9*c.k,97570950794985+c.lower,97571329673824+c.upper)) = pointBounds16568 := by
 decide +kernel
def cuts16569 : List PrefixCut := [⟨17,105568965,105569034⟩,
⟨84,511276999,511277323⟩,
⟨128,778033357,778033851⟩]
theorem checked16569 : checkPrefixCuts (2^48) 2175664129 9 Manual.Count131072.C016569.packed 128 cuts16569 = true := by
 decide +kernel
def pointBounds16569 : List (Nat × Nat × Nat) := [(2175681536,97571855273871,97572234153282),(2175750144,97572260981905,97572639861571)]
theorem point_links_checked16569 : (cuts16569.take 2).map (fun c => (2175664129-1+2*2^9*c.k,97571749704906+c.lower,97572128584248+c.upper)) = pointBounds16569 := by
 decide +kernel
def cuts16570 : List PrefixCut := [⟨23,144760250,144760343⟩,
⟨90,557557587,557557939⟩,
⟨128,790405259,790405760⟩]
theorem checked16570 : checkPrefixCuts (2^48) 2175795201 9 Manual.Count131072.C016570.packed 128 cuts16570 = true := by
 decide +kernel
def pointBounds16570 : List (Nat × Nat × Nat) := [(2175818752,97572672498513,97573051378442),(2175887360,97573085295850,97573464176038)]
theorem point_links_checked16570 : (cuts16570.take 2).map (fun c => (2175795201-1+2*2^9*c.k,97572527738263+c.lower,97572906618099+c.upper)) = pointBounds16570 := by
 decide +kernel
def cuts16571 : List PrefixCut := [⟨29,179160492,179160602⟩,
⟨96,586369463,586369832⟩,
⟨128,781820080,781820576⟩]
theorem checked16571 : checkPrefixCuts (2^48) 2175926273 9 Manual.Count131072.C016571.packed 128 cuts16571 = true := by
 decide +kernel
def pointBounds16571 : List (Nat × Nat × Nat) := [(2175955968,97573497304014,97573876184461),(2176024576,97573904512985,97574283393691)]
theorem point_links_checked16571 : (cuts16571.take 2).map (fun c => (2175926273-1+2*2^9*c.k,97573318143522+c.lower,97573697023859+c.upper)) = pointBounds16571 := by
 decide +kernel
def cuts16572 : List PrefixCut := [⟨35,218989200,218989338⟩,
⟨102,638201878,638202277⟩,
⟨128,800528433,800528931⟩]
theorem checked16572 : checkPrefixCuts (2^48) 2176057345 9 Manual.Count131072.C016572.packed 128 cuts16572 = true := by
 decide +kernel
def pointBounds16572 : List (Nat × Nat × Nat) := [(2176093184,97574318952802,97574697833773),(2176161792,97574738165480,97575117046712)]
theorem point_links_checked16572 : (cuts16572.take 2).map (fun c => (2176057345-1+2*2^9*c.k,97574099963602+c.lower,97574478844435+c.upper)) = pointBounds16572 := by
 decide +kernel
def cuts16573 : List PrefixCut := [⟨41,250664443,250664604⟩,
⟨108,668169219,668169645⟩,
⟨128,790520974,790521478⟩]
theorem checked16573 : checkPrefixCuts (2^48) 2176188417 9 Manual.Count131072.C016573.packed 128 cuts16573 = true := by
 decide +kernel
def pointBounds16573 : List (Nat × Nat × Nat) := [(2176230400,97575151156478,97575530037970),(2176299008,97575568661254,97575947543011)]
theorem point_links_checked16573 : (cuts16573.take 2).map (fun c => (2176188417-1+2*2^9*c.k,97574900492035+c.lower,97575279373366+c.upper)) = pointBounds16573 := by
 decide +kernel
def cuts16574 : List PrefixCut := [⟨47,289319828,289320011⟩,
⟨114,696063844,696064287⟩,
⟨128,779480357,779480853⟩]
theorem checked16574 : checkPrefixCuts (2^48) 2176319489 9 Manual.Count131072.C016574.packed 128 cuts16574 = true := by
 decide +kernel
def pointBounds16574 : List (Nat × Nat × Nat) := [(2176367616,97575980332837,97576359214855),(2176436224,97576387076853,97576765959131)]
theorem point_links_checked16574 : (cuts16574.take 2).map (fun c => (2176319489-1+2*2^9*c.k,97575691013009+c.lower,97576069894844+c.upper)) = pointBounds16574 := by
 decide +kernel
def cuts16575 : List PrefixCut := [⟨53,322280082,322280289⟩,
⟨120,736111235,736111706⟩,
⟨128,784088935,784089435⟩]
theorem checked16575 : checkPrefixCuts (2^48) 2176450561 9 Manual.Count131072.C016575.packed 128 cuts16575 = true := by
 decide +kernel
def pointBounds16575 : List (Nat × Nat × Nat) := [(2176504832,97576792773448,97577171655986),(2176573440,97577206604601,97577585487403)]
theorem point_links_checked16575 : (cuts16575.take 2).map (fun c => (2176450561-1+2*2^9*c.k,97576470493366+c.lower,97576849375697+c.upper)) = pointBounds16575 := by
 decide +kernel
def cuts16576 : List PrefixCut := [⟨59,369331902,369332133⟩,
⟨126,787275018,787275517⟩,
⟨128,798395848,798396354⟩]
theorem checked16576 : checkPrefixCuts (2^48) 2176581633 9 Manual.Count131072.C016576.packed 128 cuts16576 = true := by
 decide +kernel
def pointBounds16576 : List (Nat × Nat × Nat) := [(2176642048,97577623914203,97578002797265),(2176710656,97578041857319,97578420740649)]
theorem point_links_checked16576 : (cuts16576.take 2).map (fun c => (2176581633-1+2*2^9*c.k,97577254582301+c.lower,97577633465132+c.upper)) = pointBounds16576 := by
 decide +kernel
def cuts16577 : List PrefixCut := [⟨65,407714249,407714502⟩,
⟨128,801968385,801968893⟩]
theorem checked16577 : checkPrefixCuts (2^48) 2176712705 9 Manual.Count131072.C016577.packed 128 cuts16577 = true := by
 decide +kernel
def pointBounds16577 : List (Nat × Nat × Nat) := [(2176779264,97578460692398,97578839575988)]
theorem point_links_checked16577 : (cuts16577.take 1).map (fun c => (2176712705-1+2*2^9*c.k,97578052978149+c.lower,97578431861486+c.upper)) = pointBounds16577 := by
 decide +kernel
def cuts16578 : List PrefixCut := [⟨4,23404026,23404039⟩,
⟨71,437428511,437428784⟩,
⟨128,788214146,788214641⟩]
theorem checked16578 : checkPrefixCuts (2^48) 2176843777 9 Manual.Count131072.C016578.packed 128 cuts16578 = true := by
 decide +kernel
def pointBounds16578 : List (Nat × Nat × Nat) := [(2176847872,97578878350560,97579257234418),(2176916480,97579292375045,97579671259163)]
theorem point_links_checked16578 : (cuts16578.take 2).map (fun c => (2176843777-1+2*2^9*c.k,97578854946534+c.lower,97579233830379+c.upper)) = pointBounds16578 := by
 decide +kernel
def cuts16579 : List PrefixCut := [⟨10,61157021,61157056⟩,
⟨77,474250437,474250727⟩,
⟨128,783124526,783125009⟩]
theorem checked16579 : checkPrefixCuts (2^48) 2176974849 9 Manual.Count131072.C016579.packed 128 cuts16579 = true := by
 decide +kernel
def pointBounds16579 : List (Nat × Nat × Nat) := [(2176985088,97579704317701,97580083202076),(2177053696,97580117411117,97580496295747)]
theorem point_links_checked16579 : (cuts16579.take 2).map (fun c => (2176974849-1+2*2^9*c.k,97579643160680+c.lower,97580022045020+c.upper)) = pointBounds16579 := by
 decide +kernel
def cuts16580 : List PrefixCut := [⟨16,99551820,99551882⟩,
⟨83,518049131,518049460⟩,
⟨128,788507380,788507882⟩]
theorem checked16580 : checkPrefixCuts (2^48) 2177105921 9 Manual.Count131072.C016580.packed 128 cuts16580 = true := by
 decide +kernel
def pointBounds16580 : List (Nat × Nat × Nat) := [(2177122304,97580525837026,97580904721911),(2177190912,97580944334337,97581323219489)]
theorem point_links_checked16580 : (cuts16580.take 2).map (fun c => (2177105921-1+2*2^9*c.k,97580426285206+c.lower,97580805170029+c.upper)) = pointBounds16580 := by
 decide +kernel
def cuts16581 : List PrefixCut := [⟨22,135356284,135356372⟩,
⟨89,543485047,543485395⟩,
⟨128,784322830,784323329⟩]
theorem checked16581 : checkPrefixCuts (2^48) 2177236993 9 Manual.Count131072.C016581.packed 128 cuts16581 = true := by
 decide +kernel
def pointBounds16581 : List (Nat × Nat × Nat) := [(2177259520,97581350148870,97581729034283),(2177328128,97581758277633,97582137163306)]
theorem point_links_checked16581 : (cuts16581.take 2).map (fun c => (2177236993-1+2*2^9*c.k,97581214792586+c.lower,97581593677911+c.upper)) = pointBounds16581 := by
 decide +kernel
def cuts16582 : List PrefixCut := [⟨28,174000309,174000416⟩,
⟨95,585076517,585076883⟩,
⟨128,786990331,786990828⟩]
theorem checked16582 : checkPrefixCuts (2^48) 2177368065 9 Manual.Count131072.C016582.packed 128 cuts16582 = true := by
 decide +kernel
def pointBounds16582 : List (Nat × Nat × Nat) := [(2177396736,97582173115725,97582552001656),(2177465344,97582584191933,97582963078123)]
theorem point_links_checked16582 : (cuts16582.take 2).map (fun c => (2177368065-1+2*2^9*c.k,97581999115416+c.lower,97582378001240+c.upper)) = pointBounds16582 := by
 decide +kernel
def cuts16583 : List PrefixCut := [⟨34,202298466,202298595⟩,
⟨101,619682561,619682951⟩,
⟨128,787718282,787718780⟩]
theorem checked16583 : checkPrefixCuts (2^48) 2177499137 9 Manual.Count131072.C016583.packed 128 cuts16583 = true := by
 decide +kernel
def pointBounds16583 : List (Nat × Nat × Nat) := [(2177533952,97582988404213,97583367290663),(2177602560,97583405788308,97583784675019)]
theorem point_links_checked16583 : (cuts16583.take 2).map (fun c => (2177499137-1+2*2^9*c.k,97582786105747+c.lower,97583164992068+c.upper)) = pointBounds16583 := by
 decide +kernel
def cuts16584 : List PrefixCut := [⟨40,247525689,247525846⟩,
⟨107,654413990,654414406⟩,
⟨128,783793531,783794030⟩]
theorem checked16584 : checkPrefixCuts (2^48) 2177630209 9 Manual.Count131072.C016584.packed 128 cuts16584 = true := by
 decide +kernel
def pointBounds16584 : List (Nat × Nat × Nat) := [(2177671168,97583821349718,97584200236694),(2177739776,97584228238019,97584607125254)]
theorem point_links_checked16584 : (cuts16584.take 2).map (fun c => (2177630209-1+2*2^9*c.k,97583573824029+c.lower,97583952710848+c.upper)) = pointBounds16584 := by
 decide +kernel
def cuts16585 : List PrefixCut := [⟨46,281890497,281890675⟩,
⟨113,692630518,692630952⟩,
⟨128,784392567,784393057⟩]
theorem checked16585 : checkPrefixCuts (2^48) 2177761281 9 Manual.Count131072.C016585.packed 128 cuts16585 = true := by
 decide +kernel
def pointBounds16585 : List (Nat × Nat × Nat) := [(2177808384,97584639508057,97585018395553),(2177876992,97585050248078,97585429135830)]
theorem point_links_checked16585 : (cuts16585.take 2).map (fun c => (2177761281-1+2*2^9*c.k,97584357617560+c.lower,97584736504878+c.upper)) = pointBounds16585 := by
 decide +kernel
def cuts16586 : List PrefixCut := [⟨52,326073225,326073427⟩,
⟨119,739501336,739501793⟩,
⟨128,792358192,792358682⟩]
theorem checked16586 : checkPrefixCuts (2^48) 2177892353 9 Manual.Count131072.C016586.packed 128 cuts16586 = true := by
 decide +kernel
def pointBounds16586 : List (Nat × Nat × Nat) := [(2177945600,97585468083352,97585846971362),(2178014208,97585881511463,97586260399728)]
theorem point_links_checked16586 : (cuts16586.take 2).map (fun c => (2177892353-1+2*2^9*c.k,97585142010127+c.lower,97585520897935+c.upper)) = pointBounds16586 := by
 decide +kernel
def cuts16587 : List PrefixCut := [⟨58,359782820,359783045⟩,
⟨125,779904849,779905339⟩,
⟨128,796445830,796446331⟩]
theorem checked16587 : checkPrefixCuts (2^48) 2178023425 9 Manual.Count131072.C016587.packed 128 cuts16587 = true := by
 decide +kernel
def pointBounds16587 : List (Nat × Nat × Nat) := [(2178082816,97586294151139,97586673039662),(2178151424,97586714273168,97587093161956)]
theorem point_links_checked16587 : (cuts16587.take 2).map (fun c => (2178023425-1+2*2^9*c.k,97585934368319+c.lower,97586313256617+c.upper)) = pointBounds16587 := by
 decide +kernel
def cuts16588 : List PrefixCut := [⟨64,394263593,394263848⟩,
⟨128,790841223,790841730⟩]
theorem checked16588 : checkPrefixCuts (2^48) 2178154497 9 Manual.Count131072.C016588.packed 128 cuts16588 = true := by
 decide +kernel
def pointBounds16588 : List (Nat × Nat × Nat) := [(2178220032,97587125077742,97587503966796)]
theorem point_links_checked16588 : (cuts16588.take 1).map (fun c => (2178154497-1+2*2^9*c.k,97586730814149+c.lower,97587109702948+c.upper)) = pointBounds16588 := by
 decide +kernel
def cuts16589 : List PrefixCut := [⟨3,17702928,17702940⟩,
⟨70,432874970,432875246⟩,
⟨128,795445351,795445857⟩]
theorem checked16589 : checkPrefixCuts (2^48) 2178285569 9 Manual.Count131072.C016589.packed 128 cuts16589 = true := by
 decide +kernel
def pointBounds16589 : List (Nat × Nat × Nat) := [(2178288640,97587539358300,97587918247618),(2178357248,97587954530342,97588333419924)]
theorem point_links_checked16589 : (cuts16589.take 2).map (fun c => (2178285569-1+2*2^9*c.k,97587521655372+c.lower,97587900544678+c.upper)) = pointBounds16589 := by
 decide +kernel
def cuts16590 : List PrefixCut := [⟨9,58015512,58015548⟩,
⟨76,467863857,467864146⟩,
⟨128,790875338,790875830⟩]
theorem checked16590 : checkPrefixCuts (2^48) 2178416641 9 Manual.Count131072.C016590.packed 128 cuts16590 = true := by
 decide +kernel
def pointBounds16590 : List (Nat × Nat × Nat) := [(2178425856,97588375116235,97588754006083),(2178494464,97588784964580,97589163854681)]
theorem point_links_checked16590 : (cuts16590.take 2).map (fun c => (2178416641-1+2*2^9*c.k,97588317100723+c.lower,97588695990535+c.upper)) = pointBounds16590 := by
 decide +kernel
def cuts16591 : List PrefixCut := [⟨15,97935522,97935582⟩,
⟨82,507887215,507887538⟩,
⟨128,793670143,793670644⟩]
theorem checked16591 : checkPrefixCuts (2^48) 2178547713 9 Manual.Count131072.C016591.packed 128 cuts16591 = true := by
 decide +kernel
def pointBounds16591 : List (Nat × Nat × Nat) := [(2178563072,97589205911583,97589584801947),(2178631680,97589615863276,97589994753903)]
theorem point_links_checked16591 : (cuts16591.take 2).map (fun c => (2178547713-1+2*2^9*c.k,97589107976061+c.lower,97589486866365+c.upper)) = pointBounds16591 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000205
