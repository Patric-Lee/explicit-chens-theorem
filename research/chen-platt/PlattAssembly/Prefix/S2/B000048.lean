import PlattAssemblyKernel
import PlattCertificates.Count131072.C011536
import PlattCertificates.Count131072.C011537
import PlattCertificates.Count131072.C011538
import PlattCertificates.Count131072.C011539
import PlattCertificates.Count131072.C011540
import PlattCertificates.Count131072.C011541
import PlattCertificates.Count131072.C011542
import PlattCertificates.Count131072.C011543
import PlattCertificates.Count131072.C011544
import PlattCertificates.Count131072.C011545
import PlattCertificates.Count131072.C011546
import PlattCertificates.Count131072.C011547
import PlattCertificates.Count131072.C011548
import PlattCertificates.Count131072.C011549
import PlattCertificates.Count131072.C011550
import PlattCertificates.Count131072.C011551
import PlattCertificates.Count131072.C011552
import PlattCertificates.Count131072.C011553
import PlattCertificates.Count131072.C011554
import PlattCertificates.Count131072.C011555
import PlattCertificates.Count131072.C011556
import PlattCertificates.Count131072.C011557
import PlattCertificates.Count131072.C011558
import PlattCertificates.Count131072.C011559
import PlattCertificates.Count131072.C011560
import PlattCertificates.Count131072.C011561
import PlattCertificates.Count131072.C011562
import PlattCertificates.Count131072.C011563
import PlattCertificates.Count131072.C011564
import PlattCertificates.Count131072.C011565
import PlattCertificates.Count131072.C011566
import PlattCertificates.Count131072.C011567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11536 : List PrefixCut := [⟨31,283332583,283332806⟩,
⟨78,709062936,709063489⟩,
⟨125,1132737473,1132738360⟩,
⟨128,1160400243,1160401151⟩]
theorem checked11536 : checkPrefixCuts (2^48) 1515978753 9 Manual.Count131072.C011536.packed 128 cuts11536 = true := by
 decide +kernel
def pointBounds11536 : List (Nat × Nat × Nat) := [(1516010496,92802339604815,92802715135068),(1516058624,92802765335168,92803140865751),(1516106752,92803189009705,92803564540622)]
theorem point_links_checked11536 : (cuts11536.take 3).map (fun c => (1515978753-1+2*2^9*c.k,92802056272232+c.lower,92802431802262+c.upper)) = pointBounds11536 := by
 decide +kernel
def cuts11537 : List PrefixCut := [⟨44,398968763,398969077⟩,
⟨91,815190501,815191143⟩,
⟨128,1149717793,1149718699⟩]
theorem checked11537 : checkPrefixCuts (2^48) 1516109825 9 Manual.Count131072.C011537.packed 128 cuts11537 = true := by
 decide +kernel
def pointBounds11537 : List (Nat × Nat × Nat) := [(1516154880,92803615641238,92803991172490),(1516203008,92804031862976,92804407394556)]
theorem point_links_checked11537 : (cuts11537.take 2).map (fun c => (1516109825-1+2*2^9*c.k,92803216672475+c.lower,92803592203413+c.upper)) = pointBounds11537 := by
 decide +kernel
def cuts11538 : List PrefixCut := [⟨10,93747847,93747921⟩,
⟨57,528321082,528321495⟩,
⟨104,947658924,947659663⟩,
⟨128,1159643117,1159644024⟩]
theorem checked11538 : checkPrefixCuts (2^48) 1516240897 9 Manual.Count131072.C011538.packed 128 cuts11538 = true := by
 decide +kernel
def pointBounds11538 : List (Nat × Nat × Nat) := [(1516251136,92804460138115,92804835670033),(1516299264,92804894711350,92805270243607),(1516347392,92805314049192,92805689581775)]
theorem point_links_checked11538 : (cuts11538.take 3).map (fun c => (1516240897-1+2*2^9*c.k,92804366390268+c.lower,92804741922112+c.upper)) = pointBounds11538 := by
 decide +kernel
def cuts11539 : List PrefixCut := [⟨23,207897099,207897263⟩,
⟨70,623310223,623310716⟩,
⟨117,1046505940,1046506762⟩,
⟨128,1148776258,1148777159⟩]
theorem checked11539 : checkPrefixCuts (2^48) 1516371969 9 Manual.Count131072.C011539.packed 128 cuts11539 = true := by
 decide +kernel
def pointBounds11539 : List (Nat × Nat × Nat) := [(1516395520,92805733930484,92806109463399),(1516443648,92806149343608,92806524876852),(1516491776,92806572539325,92806948072898)]
theorem point_links_checked11539 : (cuts11539.take 3).map (fun c => (1516371969-1+2*2^9*c.k,92805526033385+c.lower,92805901566136+c.upper)) = pointBounds11539 := by
 decide +kernel
def cuts11540 : List PrefixCut := [⟨36,335760523,335760787⟩,
⟨83,765796617,765797213⟩,
⟨128,1176517527,1176518449⟩]
theorem checked11540 : checkPrefixCuts (2^48) 1516503041 9 Manual.Count131072.C011540.packed 128 cuts11540 = true := by
 decide +kernel
def pointBounds11540 : List (Nat × Nat × Nat) := [(1516539904,92807010570166,92807386104082),(1516588032,92807440606260,92807816140508)]
theorem point_links_checked11540 : (cuts11540.take 2).map (fun c => (1516503041-1+2*2^9*c.k,92806674809643+c.lower,92807050343295+c.upper)) = pointBounds11540 := by
 decide +kernel
def cuts11541 : List PrefixCut := [⟨2,17631209,17631223⟩,
⟨49,445412993,445413345⟩,
⟨96,864829965,864830649⟩,
⟨128,1153403412,1153404323⟩]
theorem checked11541 : checkPrefixCuts (2^48) 1516634113 9 Manual.Count131072.C011541.packed 128 cuts11541 = true := by
 decide +kernel
def pointBounds11541 : List (Nat × Nat × Nat) := [(1516636160,92807868958379,92808244492967),(1516684288,92808296740163,92808672275089),(1516732416,92808716157135,92809091692393)]
theorem point_links_checked11541 : (cuts11541.take 3).map (fun c => (1516634113-1+2*2^9*c.k,92807851327170+c.lower,92808226861744+c.upper)) = pointBounds11541 := by
 decide +kernel
def cuts11542 : List PrefixCut := [⟨15,128603359,128603461⟩,
⟨62,548364857,548365287⟩,
⟨109,973123255,973124020⟩,
⟨128,1138829162,1138830059⟩]
theorem checked11542 : checkPrefixCuts (2^48) 1516765185 9 Manual.Count131072.C011542.packed 128 cuts11542 = true := by
 decide +kernel
def pointBounds11542 : List (Nat × Nat × Nat) := [(1516780544,92809133333941,92809508869528),(1516828672,92809553095439,92809928631354),(1516876800,92809977853837,92810353390087)]
theorem point_links_checked11542 : (cuts11542.take 3).map (fun c => (1516765185-1+2*2^9*c.k,92809004730582+c.lower,92809380266067+c.upper)) = pointBounds11542 := by
 decide +kernel
def cuts11543 : List PrefixCut := [⟨28,248833260,248833455⟩,
⟨75,665214832,665215352⟩,
⟨122,1078985539,1078986386⟩,
⟨128,1133535494,1133536386⟩]
theorem checked11543 : checkPrefixCuts (2^48) 1516896257 9 Manual.Count131072.C011543.packed 128 cuts11543 = true := by
 decide +kernel
def pointBounds11543 : List (Nat × Nat × Nat) := [(1516924928,92810392393004,92810767929581),(1516973056,92810808774576,92811184311478),(1517021184,92811222545283,92811598082512)]
theorem point_links_checked11543 : (cuts11543.take 3).map (fun c => (1516896257-1+2*2^9*c.k,92810143559744+c.lower,92810519096126+c.upper)) = pointBounds11543 := by
 decide +kernel
def cuts11544 : List PrefixCut := [⟨41,376648508,376648805⟩,
⟨88,800226365,800226996⟩,
⟨128,1162566790,1162567708⟩]
theorem checked11544 : checkPrefixCuts (2^48) 1517027329 9 Manual.Count131072.C011544.packed 128 cuts11544 = true := by
 decide +kernel
def pointBounds11544 : List (Nat × Nat × Nat) := [(1517069312,92811653743746,92812029281317),(1517117440,92812077321603,92812452859508)]
theorem point_links_checked11544 : (cuts11544.take 2).map (fun c => (1517027329-1+2*2^9*c.k,92811277095238+c.lower,92811652632512+c.upper)) = pointBounds11544 := by
 decide +kernel
def cuts11545 : List PrefixCut := [⟨7,62893724,62893772⟩,
⟨54,471231844,471232214⟩,
⟨101,896068017,896068723⟩,
⟨128,1133525079,1133525973⟩]
theorem checked11545 : checkPrefixCuts (2^48) 1517158401 9 Manual.Count131072.C011545.packed 128 cuts11545 = true := by
 decide +kernel
def pointBounds11545 : List (Nat × Nat × Nat) := [(1517165568,92812502555752,92812878093992),(1517213696,92812910893872,92813286432434),(1517261824,92813335730045,92813711268943)]
theorem point_links_checked11545 : (cuts11545.take 3).map (fun c => (1517158401-1+2*2^9*c.k,92812439662028+c.lower,92812815200220+c.upper)) = pointBounds11545 := by
 decide +kernel
def cuts11546 : List PrefixCut := [⟨20,182171219,182171362⟩,
⟨67,606609283,606609759⟩,
⟨114,1032703542,1032704354⟩,
⟨128,1160325123,1160326036⟩]
theorem checked11546 : checkPrefixCuts (2^48) 1517289473 9 Manual.Count131072.C011546.packed 128 cuts11546 = true := by
 decide +kernel
def pointBounds11546 : List (Nat × Nat × Nat) := [(1517309952,92813755358326,92814130897555),(1517358080,92814179796390,92814555335952),(1517406208,92814605890649,92814981430547)]
theorem point_links_checked11546 : (cuts11546.take 3).map (fun c => (1517289473-1+2*2^9*c.k,92813573187107+c.lower,92813948726193+c.upper)) = pointBounds11546 := by
 decide +kernel
def cuts11547 : List PrefixCut := [⟨33,294192794,294193023⟩,
⟨80,714880717,714881276⟩,
⟨127,1139079647,1139080539⟩,
⟨128,1146869793,1146870691⟩]
theorem checked11547 : checkPrefixCuts (2^48) 1517420545 9 Manual.Count131072.C011547.packed 128 cuts11547 = true := by
 decide +kernel
def pointBounds11547 : List (Nat × Nat × Nat) := [(1517454336,92815027705024,92815403245252),(1517502464,92815448392947,92815823933505),(1517550592,92815872591877,92816248132768)]
theorem point_links_checked11547 : (cuts11547.take 3).map (fun c => (1517420545-1+2*2^9*c.k,92814733512230+c.lower,92815109052229+c.upper)) = pointBounds11547 := by
 decide +kernel
def cuts11548 : List PrefixCut := [⟨46,412500228,412500550⟩,
⟨93,827955121,827955772⟩,
⟨128,1156044065,1156044967⟩]
theorem checked11548 : checkPrefixCuts (2^48) 1517551617 9 Manual.Count131072.C011548.packed 128 cuts11548 = true := by
 decide +kernel
def pointBounds11548 : List (Nat × Nat × Nat) := [(1517598720,92816292882251,92816668423470),(1517646848,92816708337144,92817083878692)]
theorem point_links_checked11548 : (cuts11548.take 2).map (fun c => (1517551617-1+2*2^9*c.k,92815880382023+c.lower,92816255922920+c.upper)) = pointBounds11548 := by
 decide +kernel
def cuts11549 : List PrefixCut := [⟨12,108310291,108310375⟩,
⟨59,534124444,534124855⟩,
⟨106,948426974,948427712⟩,
⟨128,1147413673,1147414570⟩]
theorem checked11549 : checkPrefixCuts (2^48) 1517682689 9 Manual.Count131072.C011549.packed 128 cuts11549 = true := by
 decide +kernel
def pointBounds11549 : List (Nat × Nat × Nat) := [(1517694976,92817144736379,92817520278262),(1517743104,92817570550532,92817946092742),(1517791232,92817984853062,92818360395599)]
theorem point_links_checked11549 : (cuts11549.take 3).map (fun c => (1517682689-1+2*2^9*c.k,92817036426088+c.lower,92817411967887+c.upper)) = pointBounds11549 := by
 decide +kernel
def cuts11550 : List PrefixCut := [⟨25,218826266,218826435⟩,
⟨72,639963933,639964429⟩,
⟨119,1054597987,1054598811⟩,
⟨128,1133035775,1133036660⟩]
theorem checked11550 : checkPrefixCuts (2^48) 1517813761 9 Manual.Count131072.C011550.packed 128 cuts11550 = true := by
 decide +kernel
def pointBounds11550 : List (Nat × Nat × Nat) := [(1517839360,92818402666027,92818778208892),(1517887488,92818823803694,92819199346886),(1517935616,92819238437748,92819613981268)]
theorem point_links_checked11550 : (cuts11550.take 3).map (fun c => (1517813761-1+2*2^9*c.k,92818183839761+c.lower,92818559382457+c.upper)) = pointBounds11550 := by
 decide +kernel
def cuts11551 : List PrefixCut := [⟨38,337295716,337295977⟩,
⟨85,754313978,754314567⟩,
⟨128,1140725632,1140726521⟩]
theorem checked11551 : checkPrefixCuts (2^48) 1517944833 9 Manual.Count131072.C011551.packed 128 cuts11551 = true := by
 decide +kernel
def pointBounds11551 : List (Nat × Nat × Nat) := [(1517983744,92819654171252,92820029715094),(1518031872,92820071189514,92820446733684)]
theorem point_links_checked11551 : (cuts11551.take 2).map (fun c => (1517944833-1+2*2^9*c.k,92819316875536+c.lower,92819692419117+c.upper)) = pointBounds11551 := by
 decide +kernel
def cuts11552 : List PrefixCut := [⟨4,36897644,36897673⟩,
⟨51,462047526,462047886⟩,
⟨98,880509411,880510100⟩,
⟨128,1148785249,1148786147⟩]
theorem checked11552 : checkPrefixCuts (2^48) 1518075905 9 Manual.Count131072.C011552.packed 128 cuts11552 = true := by
 decide +kernel
def pointBounds11552 : List (Nat × Nat × Nat) := [(1518080000,92820494498812,92820870043311),(1518128128,92820919648694,92821295193524),(1518176256,92821338110579,92821713655738)]
theorem point_links_checked11552 : (cuts11552.take 3).map (fun c => (1518075905-1+2*2^9*c.k,92820457601168+c.lower,92820833145638+c.upper)) = pointBounds11552 := by
 decide +kernel
def cuts11553 : List PrefixCut := [⟨17,147577176,147577290⟩,
⟨64,570647328,570647772⟩,
⟨111,1002231914,1002232702⟩,
⟨128,1154432679,1154433588⟩]
theorem checked11553 : checkPrefixCuts (2^48) 1518206977 9 Manual.Count131072.C011553.packed 128 cuts11553 = true := by
 decide +kernel
def pointBounds11553 : List (Nat × Nat × Nat) := [(1518224384,92821753963593,92822129509075),(1518272512,92822177033745,92822552579557),(1518320640,92822608618331,92822984164487)]
theorem point_links_checked11553 : (cuts11553.take 3).map (fun c => (1518206977-1+2*2^9*c.k,92821606386417+c.lower,92821981931785+c.upper)) = pointBounds11553 := by
 decide +kernel
def cuts11554 : List PrefixCut := [⟨30,268988788,268989001⟩,
⟨77,693687073,693687618⟩,
⟨124,1119854901,1119855780⟩,
⟨128,1158782134,1158783043⟩]
theorem checked11554 : checkPrefixCuts (2^48) 1518338049 9 Manual.Count131072.C011554.packed 128 cuts11554 = true := by
 decide +kernel
def pointBounds11554 : List (Nat × Nat × Nat) := [(1518368768,92823029807884,92823405354374),(1518416896,92823454506169,92823830052991),(1518465024,92823880673997,92824256221153)]
theorem point_links_checked11554 : (cuts11554.take 3).map (fun c => (1518338049-1+2*2^9*c.k,92822760819096+c.lower,92823136365373+c.upper)) = pointBounds11554 := by
 decide +kernel
def cuts11555 : List PrefixCut := [⟨43,384075924,384076224⟩,
⟨90,800021998,800022622⟩,
⟨128,1153121073,1153121973⟩]
theorem checked11555 : checkPrefixCuts (2^48) 1518469121 9 Manual.Count131072.C011555.packed 128 cuts11555 = true := by
 decide +kernel
def pointBounds11555 : List (Nat × Nat × Nat) := [(1518513152,92824303677154,92824679224640),(1518561280,92824719623228,92825095171038)]
theorem point_links_checked11555 : (cuts11555.take 2).map (fun c => (1518469121-1+2*2^9*c.k,92823919601230+c.lower,92824295148416+c.upper)) = pointBounds11555 := by
 decide +kernel
def cuts11556 : List PrefixCut := [⟨9,79515560,79515621⟩,
⟨56,493767235,493767620⟩,
⟨103,926169120,926169838⟩,
⟨128,1147461629,1147462520⟩]
theorem checked11556 : checkPrefixCuts (2^48) 1518600193 9 Manual.Count131072.C011556.packed 128 cuts11556 = true := by
 decide +kernel
def pointBounds11556 : List (Nat × Nat × Nat) := [(1518609408,92825152237863,92825527786010),(1518657536,92825566489538,92825942038009),(1518705664,92825998891423,92826374440227)]
theorem point_links_checked11556 : (cuts11556.take 3).map (fun c => (1518600193-1+2*2^9*c.k,92825072722303+c.lower,92825448270389+c.upper)) = pointBounds11556 := by
 decide +kernel
def cuts11557 : List PrefixCut := [⟨22,203867531,203867690⟩,
⟨69,637910068,637910563⟩,
⟨116,1060448672,1060449502⟩,
⟨128,1168861036,1168861951⟩]
theorem checked11557 : checkPrefixCuts (2^48) 1518731265 9 Manual.Count131072.C011557.packed 128 cuts11557 = true := by
 decide +kernel
def pointBounds11557 : List (Nat × Nat × Nat) := [(1518753792,92826424051463,92826799600599),(1518801920,92826858094000,92827233643472),(1518850048,92827280632604,92827656182411)]
theorem point_links_checked11557 : (cuts11557.take 3).map (fun c => (1518731265-1+2*2^9*c.k,92826220183932+c.lower,92826595732909+c.upper)) = pointBounds11557 := by
 decide +kernel
def cuts11558 : List PrefixCut := [⟨35,305773579,305773819⟩,
⟨82,734215392,734215966⟩,
⟨128,1159678877,1159679780⟩]
theorem checked11558 : checkPrefixCuts (2^48) 1518862337 9 Manual.Count131072.C011558.packed 128 cuts11558 = true := by
 decide +kernel
def pointBounds11558 : List (Nat × Nat × Nat) := [(1518898176,92827694818547,92828070368679),(1518946304,92828123260360,92828498810826)]
theorem point_links_checked11558 : (cuts11558.take 2).map (fun c => (1518862337-1+2*2^9*c.k,92827389044968+c.lower,92827764594860+c.upper)) = pointBounds11558 := by
 decide +kernel
def cuts11559 : List PrefixCut := [⟨1,9079871,9079878⟩,
⟨48,429897234,429897575⟩,
⟨95,857371973,857372649⟩,
⟨128,1157170582,1157171491⟩]
theorem checked11559 : checkPrefixCuts (2^48) 1518993409 9 Manual.Count131072.C011559.packed 128 cuts11559 = true := by
 decide +kernel
def pointBounds11559 : List (Nat × Nat × Nat) := [(1518994432,92828557803716,92828933354518),(1519042560,92828978621079,92829354172215),(1519090688,92829406095818,92829781647289)]
theorem point_links_checked11559 : (cuts11559.take 3).map (fun c => (1518993409-1+2*2^9*c.k,92828548723845+c.lower,92828924274640+c.upper)) = pointBounds11559 := by
 decide +kernel
def cuts11560 : List PrefixCut := [⟨14,124327369,124327468⟩,
⟨61,545475384,545475816⟩,
⟨108,968277491,968278254⟩,
⟨128,1145583572,1145584475⟩]
theorem checked11560 : checkPrefixCuts (2^48) 1519124481 9 Manual.Count131072.C011560.packed 128 cuts11560 = true := by
 decide +kernel
def pointBounds11560 : List (Nat × Nat × Nat) := [(1519138816,92829830221796,92830205773599),(1519186944,92830251369811,92830626921947),(1519235072,92830674171918,92831049724385)]
theorem point_links_checked11560 : (cuts11560.take 3).map (fun c => (1519124481-1+2*2^9*c.k,92829705894427+c.lower,92830081446131+c.upper)) = pointBounds11560 := by
 decide +kernel
def cuts11561 : List PrefixCut := [⟨27,244926760,244926953⟩,
⟨74,671222261,671222787⟩,
⟨121,1087500124,1087500977⟩,
⟨128,1146596793,1146597694⟩]
theorem checked11561 : checkPrefixCuts (2^48) 1519255553 9 Manual.Count131072.C011561.packed 128 cuts11561 = true := by
 decide +kernel
def pointBounds11561 : List (Nat × Nat × Nat) := [(1519283200,92831096404759,92831471957559),(1519331328,92831522700260,92831898253393),(1519379456,92831938978123,92832314531583)]
theorem point_links_checked11561 : (cuts11561.take 3).map (fun c => (1519255553-1+2*2^9*c.k,92830851477999+c.lower,92831227030606+c.upper)) = pointBounds11561 := by
 decide +kernel
def cuts11562 : List PrefixCut := [⟨40,363837179,363837464⟩,
⟨87,780644453,780645067⟩,
⟨128,1145942042,1145942942⟩]
theorem checked11562 : checkPrefixCuts (2^48) 1519386625 9 Manual.Count131072.C011562.packed 128 cuts11562 = true := by
 decide +kernel
def pointBounds11562 : List (Nat × Nat × Nat) := [(1519427584,92832361911971,92832737465764),(1519475712,92832778719245,92833154273367)]
theorem point_links_checked11562 : (cuts11562.take 2).map (fun c => (1519386625-1+2*2^9*c.k,92831998074792+c.lower,92832373628300+c.upper)) = pointBounds11562 := by
 decide +kernel
def cuts11563 : List PrefixCut := [⟨6,57424162,57424208⟩,
⟨53,473649340,473649712⟩,
⟨100,899863775,899864478⟩,
⟨128,1156771385,1156772290⟩]
theorem checked11563 : checkPrefixCuts (2^48) 1519517697 9 Manual.Count131072.C011563.packed 128 cuts11563 = true := by
 decide +kernel
def pointBounds11563 : List (Nat × Nat × Nat) := [(1519523840,92833201440996,92833576995450),(1519571968,92833617666174,92833993220954),(1519620096,92834043880609,92834419435720)]
theorem point_links_checked11563 : (cuts11563.take 3).map (fun c => (1519517697-1+2*2^9*c.k,92833144016834+c.lower,92833519571242+c.upper)) = pointBounds11563 := by
 decide +kernel
def cuts11564 : List PrefixCut := [⟨19,170589879,170590010⟩,
⟨66,586590072,586590528⟩,
⟨113,1000169506,1000170281⟩,
⟨128,1136483011,1136483894⟩]
theorem checked11564 : checkPrefixCuts (2^48) 1519648769 9 Manual.Count131072.C011564.packed 128 cuts11564 = true := by
 decide +kernel
def pointBounds11564 : List (Nat × Nat × Nat) := [(1519668224,92834471378098,92834846933542),(1519716352,92834887378291,92835262934060),(1519764480,92835300957725,92835676513813)]
theorem point_links_checked11564 : (cuts11564.take 3).map (fun c => (1519648769-1+2*2^9*c.k,92834300788219+c.lower,92834676343532+c.upper)) = pointBounds11564 := by
 decide +kernel
def cuts11565 : List PrefixCut := [⟨32,299107199,299107432⟩,
⟨79,722846449,722847013⟩,
⟨126,1145831505,1145832399⟩,
⟨128,1163609920,1163610827⟩]
theorem checked11565 : checkPrefixCuts (2^48) 1519779841 9 Manual.Count131072.C011565.packed 128 cuts11565 = true := by
 decide +kernel
def pointBounds11565 : List (Nat × Nat × Nat) := [(1519812608,92835736378429,92836111934858),(1519860736,92836160117679,92836535674439),(1519908864,92836583102735,92836958659825)]
theorem point_links_checked11565 : (cuts11565.take 3).map (fun c => (1519779841-1+2*2^9*c.k,92835437271230+c.lower,92835812827426+c.upper)) = pointBounds11565 := by
 decide +kernel
def cuts11566 : List PrefixCut := [⟨45,400933885,400934200⟩,
⟨92,812966399,812967038⟩,
⟨128,1134250095,1134250985⟩]
theorem checked11566 : checkPrefixCuts (2^48) 1519910913 9 Manual.Count131072.C011566.packed 128 cuts11566 = true := by
 decide +kernel
def pointBounds11566 : List (Nat × Nat × Nat) := [(1519956992,92837001815035,92837377372453),(1520005120,92837413847549,92837789405291)]
theorem point_links_checked11566 : (cuts11566.take 2).map (fun c => (1519910913-1+2*2^9*c.k,92836600881150+c.lower,92836976438253+c.upper)) = pointBounds11566 := by
 decide +kernel
def cuts11567 : List PrefixCut := [⟨11,103327667,103327748⟩,
⟨58,526074011,526074428⟩,
⟨105,950843776,950844525⟩,
⟨128,1158964932,1158965843⟩]
theorem checked11567 : checkPrefixCuts (2^48) 1520041985 9 Manual.Count131072.C011567.packed 128 cuts11567 = true := by
 decide +kernel
def pointBounds11567 : List (Nat × Nat × Nat) := [(1520053248,92837838458912,92838214016986),(1520101376,92838261205256,92838636763666),(1520149504,92838685975021,92839061533763)]
theorem point_links_checked11567 : (cuts11567.take 3).map (fun c => (1520041985-1+2*2^9*c.k,92837735131245+c.lower,92838110689238+c.upper)) = pointBounds11567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000048
