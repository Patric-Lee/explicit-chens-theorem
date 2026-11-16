import PlattAssemblyKernel
import PlattCertificates.Count131072.C015600
import PlattCertificates.Count131072.C015601
import PlattCertificates.Count131072.C015602
import PlattCertificates.Count131072.C015603
import PlattCertificates.Count131072.C015604
import PlattCertificates.Count131072.C015605
import PlattCertificates.Count131072.C015606
import PlattCertificates.Count131072.C015607
import PlattCertificates.Count131072.C015608
import PlattCertificates.Count131072.C015609
import PlattCertificates.Count131072.C015610
import PlattCertificates.Count131072.C015611
import PlattCertificates.Count131072.C015612
import PlattCertificates.Count131072.C015613
import PlattCertificates.Count131072.C015614
import PlattCertificates.Count131072.C015615
import PlattCertificates.Count131072.C015616
import PlattCertificates.Count131072.C015617
import PlattCertificates.Count131072.C015618
import PlattCertificates.Count131072.C015619
import PlattCertificates.Count131072.C015620
import PlattCertificates.Count131072.C015621
import PlattCertificates.Count131072.C015622
import PlattCertificates.Count131072.C015623
import PlattCertificates.Count131072.C015624
import PlattCertificates.Count131072.C015625
import PlattCertificates.Count131072.C015626
import PlattCertificates.Count131072.C015627
import PlattCertificates.Count131072.C015628
import PlattCertificates.Count131072.C015629
import PlattCertificates.Count131072.C015630
import PlattCertificates.Count131072.C015631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15600 : List PrefixCut := [⟨26,173253906,173254019⟩,
⟨89,574847770,574848141⟩,
⟨128,835609200,835609746⟩]
theorem checked15600 : checkPrefixCuts (2^48) 2048655361 9 Manual.Count131072.C015600.packed 128 cuts15600 = true := by
 decide +kernel
def pointBounds15600 : List (Nat × Nat × Nat) := [(2048681984,96783373229654,96783751602866),(2048746496,96783774823518,96784153196988)]
theorem point_links_checked15600 : (cuts15600.take 2).map (fun c => (2048655361-1+2*2^9*c.k,96783199975748+c.lower,96783578348847+c.upper)) = pointBounds15600 := by
 decide +kernel
def cuts15601 : List PrefixCut := [⟨24,154283725,154283826⟩,
⟨87,574948484,574948854⟩,
⟨128,849843406,849843951⟩]
theorem checked15601 : checkPrefixCuts (2^48) 2048786433 9 Manual.Count131072.C015601.packed 128 cuts15601 = true := by
 decide +kernel
def pointBounds15601 : List (Nat × Nat × Nat) := [(2048811008,96784189868673,96784568242419),(2048875520,96784610533432,96784988907447)]
theorem point_links_checked15601 : (cuts15601.take 2).map (fun c => (2048786433-1+2*2^9*c.k,96784035584948+c.lower,96784413958593+c.upper)) = pointBounds15601 := by
 decide +kernel
def cuts15602 : List PrefixCut := [⟨22,145207075,145207171⟩,
⟨85,558701903,558702267⟩,
⟨128,834403576,834404118⟩]
theorem checked15602 : checkPrefixCuts (2^48) 2048917505 9 Manual.Count131072.C015602.packed 128 cuts15602 = true := by
 decide +kernel
def pointBounds15602 : List (Nat × Nat × Nat) := [(2048940032,96785030635429,96785409009715),(2049004544,96785444130257,96785822504811)]
theorem point_links_checked15602 : (cuts15602.take 2).map (fun c => (2048917505-1+2*2^9*c.k,96784885428354+c.lower,96785263802544+c.upper)) = pointBounds15602 := by
 decide +kernel
def cuts15603 : List PrefixCut := [⟨20,129537940,129538024⟩,
⟨83,539710010,539710358⟩,
⟨128,834487425,834487967⟩]
theorem checked15603 : checkPrefixCuts (2^48) 2049048577 9 Manual.Count131072.C015603.packed 128 cuts15603 = true := by
 decide +kernel
def pointBounds15603 : List (Nat × Nat × Nat) := [(2049069056,96785849369870,96786227744686),(2049133568,96786259541940,96786637917020)]
theorem point_links_checked15603 : (cuts15603.take 2).map (fun c => (2049048577-1+2*2^9*c.k,96785719831930+c.lower,96786098206662+c.upper)) = pointBounds15603 := by
 decide +kernel
def cuts15604 : List PrefixCut := [⟨18,115106981,115107055⟩,
⟨81,530060662,530061011⟩,
⟨128,836494365,836494908⟩]
theorem checked15604 : checkPrefixCuts (2^48) 2049179649 9 Manual.Count131072.C015604.packed 128 cuts15604 = true := by
 decide +kernel
def pointBounds15604 : List (Nat × Nat × Nat) := [(2049198080,96786669426336,96787047801684),(2049262592,96787084380017,96787462755640)]
theorem point_links_checked15604 : (cuts15604.take 2).map (fun c => (2049179649-1+2*2^9*c.k,96786554319355+c.lower,96786932694629+c.upper)) = pointBounds15604 := by
 decide +kernel
def cuts15605 : List PrefixCut := [⟨16,108781561,108781630⟩,
⟨79,530851167,530851509⟩,
⟨128,852235910,852236463⟩]
theorem checked15605 : checkPrefixCuts (2^48) 2049310721 9 Manual.Count131072.C015605.packed 128 cuts15605 = true := by
 decide +kernel
def pointBounds15605 : List (Nat × Nat × Nat) := [(2049327104,96787499595281,96787877971167),(2049391616,96787921664887,96788300041046)]
theorem point_links_checked15605 : (cuts15605.take 2).map (fun c => (2049310721-1+2*2^9*c.k,96787390813720+c.lower,96787769189537+c.upper)) = pointBounds15605 := by
 decide +kernel
def cuts15606 : List PrefixCut := [⟨14,94491128,94491190⟩,
⟨77,510491213,510491549⟩,
⟨128,848061125,848061678⟩]
theorem checked15606 : checkPrefixCuts (2^48) 2049441793 9 Manual.Count131072.C015606.packed 128 cuts15606 = true := by
 decide +kernel
def pointBounds15606 : List (Nat × Nat × Nat) := [(2049456128,96788337540758,96788715917190),(2049520640,96788753540843,96789131917549)]
theorem point_links_checked15606 : (cuts15606.take 2).map (fun c => (2049441793-1+2*2^9*c.k,96788243049630+c.lower,96788621426000+c.upper)) = pointBounds15606 := by
 decide +kernel
def cuts15607 : List PrefixCut := [⟨12,78005159,78005210⟩,
⟨75,498373656,498373982⟩,
⟨128,845397658,845398209⟩]
theorem checked15607 : checkPrefixCuts (2^48) 2049572865 9 Manual.Count131072.C015607.packed 128 cuts15607 = true := by
 decide +kernel
def pointBounds15607 : List (Nat × Nat × Nat) := [(2049585152,96789169115914,96789547492888),(2049649664,96789589484411,96789967861660)]
theorem point_links_checked15607 : (cuts15607.take 2).map (fun c => (2049572865-1+2*2^9*c.k,96789091110755+c.lower,96789469487678+c.upper)) = pointBounds15607 := by
 decide +kernel
def cuts15608 : List PrefixCut := [⟨10,68524834,68524878⟩,
⟨73,482275522,482275836⟩,
⟨128,848227325,848227874⟩]
theorem checked15608 : checkPrefixCuts (2^48) 2049703937 9 Manual.Count131072.C015608.packed 128 cuts15608 = true := by
 decide +kernel
def pointBounds15608 : List (Nat × Nat × Nat) := [(2049714176,96790005033247,96790383410765),(2049778688,96790418783935,96790797161723)]
theorem point_links_checked15608 : (cuts15608.take 2).map (fun c => (2049703937-1+2*2^9*c.k,96789936508413+c.lower,96790314885887+c.upper)) = pointBounds15608 := by
 decide +kernel
def cuts15609 : List PrefixCut := [⟨8,50532142,50532174⟩,
⟨71,460823835,460824137⟩,
⟨128,837187897,837188445⟩]
theorem checked15609 : checkPrefixCuts (2^48) 2049835009 9 Manual.Count131072.C015609.packed 128 cuts15609 = true := by
 decide +kernel
def pointBounds15609 : List (Nat × Nat × Nat) := [(2049843200,96790835267880,96791213645935),(2049907712,96791245559573,96791623937898)]
theorem point_links_checked15609 : (cuts15609.take 2).map (fun c => (2049835009-1+2*2^9*c.k,96790784735738+c.lower,96791163113761+c.upper)) = pointBounds15609 := by
 decide +kernel
def cuts15610 : List PrefixCut := [⟨6,38583238,38583263⟩,
⟨69,455988912,455989211⟩,
⟨128,837958397,837958950⟩]
theorem checked15610 : checkPrefixCuts (2^48) 2049966081 9 Manual.Count131072.C015610.packed 128 cuts15610 = true := by
 decide +kernel
def pointBounds15610 : List (Nat × Nat × Nat) := [(2049972224,96791660506873,96792038885469),(2050036736,96792077912547,96792456291417)]
theorem point_links_checked15610 : (cuts15610.take 2).map (fun c => (2049966081-1+2*2^9*c.k,96791621923635+c.lower,96792000302206+c.upper)) = pointBounds15610 := by
 decide +kernel
def cuts15611 : List PrefixCut := [⟨4,28832616,28832635⟩,
⟨67,436875933,436876216⟩,
⟨128,848064406,848064956⟩]
theorem checked15611 : checkPrefixCuts (2^48) 2050097153 9 Manual.Count131072.C015611.packed 128 cuts15611 = true := by
 decide +kernel
def pointBounds15611 : List (Nat × Nat × Nat) := [(2050101248,96792488714648,96792867093791),(2050165760,96792896757965,96793275137372)]
theorem point_links_checked15611 : (cuts15611.take 2).map (fun c => (2050097153-1+2*2^9*c.k,96792459882032+c.lower,96792838261156+c.upper)) = pointBounds15611 := by
 decide +kernel
def cuts15612 : List PrefixCut := [⟨2,11669605,11669612⟩,
⟨65,427375255,427375530⟩,
⟨128,845264438,845264985⟩]
theorem checked15612 : checkPrefixCuts (2^48) 2050228225 9 Manual.Count131072.C015612.packed 128 cuts15612 = true := by
 decide +kernel
def pointBounds15612 : List (Nat × Nat × Nat) := [(2050230272,96793319616043,96793697995724),(2050294784,96793735321693,96794113701642),(2050359296,96794153210876,96794531591097)]
theorem point_links_checked15612 : (cuts15612.take 3).map (fun c => (2050228225-1+2*2^9*c.k,96793307946438+c.lower,96793686326112+c.upper)) = pointBounds15612 := by
 decide +kernel
def cuts15613 : List PrefixCut := [⟨63,399617986,399618246⟩,
⟨126,814323670,814324201⟩,
⟨128,827227243,827227783⟩]
theorem checked15613 : checkPrefixCuts (2^48) 2050359297 9 Manual.Count131072.C015613.packed 128 cuts15613 = true := by
 decide +kernel
def pointBounds15613 : List (Nat × Nat × Nat) := [(2050423808,96794552828862,96794931209343),(2050488320,96794967534546,96795345915298)]
theorem point_links_checked15613 : (cuts15613.take 2).map (fun c => (2050359297-1+2*2^9*c.k,96794153210876+c.lower,96794531591097+c.upper)) = pointBounds15613 := by
 decide +kernel
def cuts15614 : List PrefixCut := [⟨61,405632492,405632753⟩,
⟨124,829508791,829509329⟩,
⟨128,854353459,854354013⟩]
theorem checked15614 : checkPrefixCuts (2^48) 2050490369 9 Manual.Count131072.C015614.packed 128 cuts15614 = true := by
 decide +kernel
def pointBounds15614 : List (Nat × Nat × Nat) := [(2050552832,96795386070611,96795764451633),(2050617344,96795809946910,96796188328209)]
theorem point_links_checked15614 : (cuts15614.take 2).map (fun c => (2050490369-1+2*2^9*c.k,96794980438119+c.lower,96795358818880+c.upper)) = pointBounds15614 := by
 decide +kernel
def cuts15615 : List PrefixCut := [⟨59,390645344,390645592⟩,
⟨122,801592959,801593480⟩,
⟨128,844141897,844142445⟩]
theorem checked15615 : checkPrefixCuts (2^48) 2050621441 9 Manual.Count131072.C015615.packed 128 cuts15615 = true := by
 decide +kernel
def pointBounds15615 : List (Nat × Nat × Nat) := [(2050681856,96796225436922,96796603818485),(2050746368,96796636384537,96797014766373)]
theorem point_links_checked15615 : (cuts15615.take 2).map (fun c => (2050621441-1+2*2^9*c.k,96795834791578+c.lower,96796213172893+c.upper)) = pointBounds15615 := by
 decide +kernel
def cuts15616 : List PrefixCut := [⟨57,376071771,376072017⟩,
⟨120,792757833,792758354⟩,
⟨128,842715360,842715913⟩]
theorem checked15616 : checkPrefixCuts (2^48) 2050752513 9 Manual.Count131072.C015616.packed 128 cuts15616 = true := by
 decide +kernel
def pointBounds15616 : List (Nat × Nat × Nat) := [(2050810880,96797055005246,96797433387355),(2050875392,96797471691308,96797850073692)]
theorem point_links_checked15616 : (cuts15616.take 2).map (fun c => (2050752513-1+2*2^9*c.k,96796678933475+c.lower,96797057315338+c.upper)) = pointBounds15616 := by
 decide +kernel
def cuts15617 : List PrefixCut := [⟨55,362049071,362049309⟩,
⟨118,775552438,775552947⟩,
⟨128,841563540,841564093⟩]
theorem checked15617 : checkPrefixCuts (2^48) 2050883585 9 Manual.Count131072.C015617.packed 128 cuts15617 = true := by
 decide +kernel
def pointBounds15617 : List (Nat × Nat × Nat) := [(2050939904,96797883697906,96798262080560),(2051004416,96798297201273,96798675584198)]
theorem point_links_checked15617 : (cuts15617.take 2).map (fun c => (2050883585-1+2*2^9*c.k,96797521648835+c.lower,96797900031251+c.upper)) = pointBounds15617 := by
 decide +kernel
def cuts15618 : List PrefixCut := [⟨53,344597355,344597580⟩,
⟨116,753134387,753134878⟩,
⟨128,831217430,831217971⟩]
theorem checked15618 : checkPrefixCuts (2^48) 2051014657 9 Manual.Count131072.C015618.packed 128 cuts15618 = true := by
 decide +kernel
def pointBounds15618 : List (Nat × Nat × Nat) := [(2051068928,96798707809730,96799086192924),(2051133440,96799116346762,96799494730222)]
theorem point_links_checked15618 : (cuts15618.take 2).map (fun c => (2051014657-1+2*2^9*c.k,96798363212375+c.lower,96798741595344+c.upper)) = pointBounds15618 := by
 decide +kernel
def cuts15619 : List PrefixCut := [⟨51,330029463,330029678⟩,
⟨114,735659090,735659570⟩,
⟨128,828419698,828420240⟩]
theorem checked15619 : checkPrefixCuts (2^48) 2051145729 9 Manual.Count131072.C015619.packed 128 cuts15619 = true := by
 decide +kernel
def pointBounds15619 : List (Nat × Nat × Nat) := [(2051197952,96799524459268,96799902842993),(2051262464,96799930088895,96800308472885)]
theorem point_links_checked15619 : (cuts15619.take 2).map (fun c => (2051145729-1+2*2^9*c.k,96799194429805+c.lower,96799572813315+c.upper)) = pointBounds15619 := by
 decide +kernel
def cuts15620 : List PrefixCut := [⟨49,317247301,317247511⟩,
⟨112,732867934,732868414⟩,
⟨128,836873982,836874528⟩]
theorem checked15620 : checkPrefixCuts (2^48) 2051276801 9 Manual.Count131072.C015620.packed 128 cuts15620 = true := by
 decide +kernel
def pointBounds15620 : List (Nat × Nat × Nat) := [(2051326976,96800340096804,96800718481066),(2051391488,96800755717437,96801134101969)]
theorem point_links_checked15620 : (cuts15620.take 2).map (fun c => (2051276801-1+2*2^9*c.k,96800022849503+c.lower,96800401233555+c.upper)) = pointBounds15620 := by
 decide +kernel
def cuts15621 : List PrefixCut := [⟨47,308582991,308583192⟩,
⟨110,716768498,716768964⟩,
⟨128,838329863,838330407⟩]
theorem checked15621 : checkPrefixCuts (2^48) 2051407873 9 Manual.Count131072.C015621.packed 128 cuts15621 = true := by
 decide +kernel
def pointBounds15621 : List (Nat × Nat × Nat) := [(2051456000,96801168306476,96801546691275),(2051520512,96801576491983,96801954877047)]
theorem point_links_checked15621 : (cuts15621.take 2).map (fun c => (2051407873-1+2*2^9*c.k,96800859723485+c.lower,96801238108083+c.upper)) = pointBounds15621 := by
 decide +kernel
def cuts15622 : List PrefixCut := [⟨45,290178615,290178797⟩,
⟨108,701219590,701220042⟩,
⟨128,834434726,834435263⟩]
theorem checked15622 : checkPrefixCuts (2^48) 2051538945 9 Manual.Count131072.C015622.packed 128 cuts15622 = true := by
 decide +kernel
def pointBounds15622 : List (Nat × Nat × Nat) := [(2051585024,96801988231963,96802366617287),(2051649536,96802399272938,96802777658532)]
theorem point_links_checked15622 : (cuts15622.take 2).map (fun c => (2051538945-1+2*2^9*c.k,96801698053348+c.lower,96802076438490+c.upper)) = pointBounds15622 := by
 decide +kernel
def cuts15623 : List PrefixCut := [⟨43,283026229,283026411⟩,
⟨106,700077640,700078091⟩,
⟨128,843984767,843985309⟩]
theorem checked15623 : checkPrefixCuts (2^48) 2051670017 9 Manual.Count131072.C015623.packed 128 cuts15623 = true := by
 decide +kernel
def pointBounds15623 : List (Nat × Nat × Nat) := [(2051714048,96802815514303,96803193900164),(2051778560,96803232565714,96803610951844)]
theorem point_links_checked15623 : (cuts15623.take 2).map (fun c => (2051670017-1+2*2^9*c.k,96802532488074+c.lower,96802910873753+c.upper)) = pointBounds15623 := by
 decide +kernel
def cuts15624 : List PrefixCut := [⟨41,266271968,266272146⟩,
⟨104,675477938,675478383⟩,
⟨128,829938524,829939069⟩]
theorem checked15624 : checkPrefixCuts (2^48) 2051801089 9 Manual.Count131072.C015624.packed 128 cuts15624 = true := by
 decide +kernel
def pointBounds15624 : List (Nat × Nat × Nat) := [(2051843072,96803642744809,96804021131208),(2051907584,96804051950779,96804430337445)]
theorem point_links_checked15624 : (cuts15624.take 2).map (fun c => (2051801089-1+2*2^9*c.k,96803376472841+c.lower,96803754859062+c.upper)) = pointBounds15624 := by
 decide +kernel
def cuts15625 : List PrefixCut := [⟨39,258573404,258573567⟩,
⟨102,676121030,676121459⟩,
⟨128,844974411,844974954⟩]
theorem checked15625 : checkPrefixCuts (2^48) 2051932161 9 Manual.Count131072.C015625.packed 128 cuts15625 = true := by
 decide +kernel
def pointBounds15625 : List (Nat × Nat × Nat) := [(2051972096,96804464984769,96804843371698),(2052036608,96804882532395,96805260919590)]
theorem point_links_checked15625 : (cuts15625.take 2).map (fun c => (2051932161-1+2*2^9*c.k,96804206411365+c.lower,96804584798131+c.upper)) = pointBounds15625 := by
 decide +kernel
def cuts15626 : List PrefixCut := [⟨37,247172236,247172399⟩,
⟨100,661401733,661402171⟩,
⟨128,839296894,839297451⟩]
theorem checked15626 : checkPrefixCuts (2^48) 2052063233 9 Manual.Count131072.C015626.packed 128 cuts15626 = true := by
 decide +kernel
def pointBounds15626 : List (Nat × Nat × Nat) := [(2052101120,96805298558012,96805676945484),(2052165632,96805712787509,96806091175256)]
theorem point_links_checked15626 : (cuts15626.take 2).map (fun c => (2052063233-1+2*2^9*c.k,96805051385776+c.lower,96805429773085+c.upper)) = pointBounds15626 := by
 decide +kernel
def cuts15627 : List PrefixCut := [⟨35,231657838,231657993⟩,
⟨98,648192891,648193314⟩,
⟨128,844866373,844866924⟩]
theorem checked15627 : checkPrefixCuts (2^48) 2052194305 9 Manual.Count131072.C015627.packed 128 cuts15627 = true := by
 decide +kernel
def pointBounds15627 : List (Nat × Nat × Nat) := [(2052230144,96806122340508,96806500728529),(2052294656,96806538875561,96806917263850)]
theorem point_links_checked15627 : (cuts15627.take 2).map (fun c => (2052194305-1+2*2^9*c.k,96805890682670+c.lower,96806269070536+c.upper)) = pointBounds15627 := by
 decide +kernel
def cuts15628 : List PrefixCut := [⟨33,222865697,222865837⟩,
⟨96,636083192,636083601⟩,
⟨128,848104077,848104624⟩]
theorem checked15628 : checkPrefixCuts (2^48) 2052325377 9 Manual.Count131072.C015628.packed 128 cuts15628 = true := by
 decide +kernel
def pointBounds15628 : List (Nat × Nat × Nat) := [(2052359168,96806958414740,96807336803297),(2052423680,96807371632235,96807750021061)]
theorem point_links_checked15628 : (cuts15628.take 2).map (fun c => (2052325377-1+2*2^9*c.k,96806735549043+c.lower,96807113937460+c.upper)) = pointBounds15628 := by
 decide +kernel
def cuts15629 : List PrefixCut := [⟨31,202143496,202143628⟩,
⟨94,613140749,613141149⟩,
⟨128,833787600,833788150⟩]
theorem checked15629 : checkPrefixCuts (2^48) 2052456449 9 Manual.Count131072.C015629.packed 128 cuts15629 = true := by
 decide +kernel
def pointBounds15629 : List (Nat × Nat × Nat) := [(2052488192,96807785796616,96808164185712),(2052552704,96808196793869,96808575183233)]
theorem point_links_checked15629 : (cuts15629.take 2).map (fun c => (2052456449-1+2*2^9*c.k,96807583653120+c.lower,96807962042084+c.upper)) = pointBounds15629 := by
 decide +kernel
def cuts15630 : List PrefixCut := [⟨29,191845893,191846019⟩,
⟨92,600074769,600075165⟩,
⟨128,831951808,831952361⟩]
theorem checked15630 : checkPrefixCuts (2^48) 2052587521 9 Manual.Count131072.C015630.packed 128 cuts15630 = true := by
 decide +kernel
def pointBounds15630 : List (Nat × Nat × Nat) := [(2052617216,96808609286613,96808987676253),(2052681728,96809017515489,96809395905399)]
theorem point_links_checked15630 : (cuts15630.take 2).map (fun c => (2052587521-1+2*2^9*c.k,96808417440720+c.lower,96808795830234+c.upper)) = pointBounds15630 := by
 decide +kernel
def cuts15631 : List PrefixCut := [⟨27,175241991,175242107⟩,
⟨90,583170916,583171298⟩,
⟨128,832721191,832721734⟩]
theorem checked15631 : checkPrefixCuts (2^48) 2052718593 9 Manual.Count131072.C015631.packed 128 cuts15631 = true := by
 decide +kernel
def pointBounds15631 : List (Nat × Nat × Nat) := [(2052746240,96809424634519,96809803024702),(2052810752,96809832563444,96810210953893)]
theorem point_links_checked15631 : (cuts15631.take 2).map (fun c => (2052718593-1+2*2^9*c.k,96809249392528+c.lower,96809627782595+c.upper)) = pointBounds15631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000175
