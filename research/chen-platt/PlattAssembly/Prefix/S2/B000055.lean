import PlattAssemblyKernel
import PlattCertificates.Count131072.C011760
import PlattCertificates.Count131072.C011761
import PlattCertificates.Count131072.C011762
import PlattCertificates.Count131072.C011763
import PlattCertificates.Count131072.C011764
import PlattCertificates.Count131072.C011765
import PlattCertificates.Count131072.C011766
import PlattCertificates.Count131072.C011767
import PlattCertificates.Count131072.C011768
import PlattCertificates.Count131072.C011769
import PlattCertificates.Count131072.C011770
import PlattCertificates.Count131072.C011771
import PlattCertificates.Count131072.C011772
import PlattCertificates.Count131072.C011773
import PlattCertificates.Count131072.C011774
import PlattCertificates.Count131072.C011775
import PlattCertificates.Count131072.C011776
import PlattCertificates.Count131072.C011777
import PlattCertificates.Count131072.C011778
import PlattCertificates.Count131072.C011779
import PlattCertificates.Count131072.C011780
import PlattCertificates.Count131072.C011781
import PlattCertificates.Count131072.C011782
import PlattCertificates.Count131072.C011783
import PlattCertificates.Count131072.C011784
import PlattCertificates.Count131072.C011785
import PlattCertificates.Count131072.C011786
import PlattCertificates.Count131072.C011787
import PlattCertificates.Count131072.C011788
import PlattCertificates.Count131072.C011789
import PlattCertificates.Count131072.C011790
import PlattCertificates.Count131072.C011791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11760 : List PrefixCut := [⟨41,368108865,368109149⟩,
⟨89,784473158,784473763⟩,
⟨128,1125058774,1125059647⟩]
theorem checked11760 : checkPrefixCuts (2^48) 1545338881 9 Manual.Count131072.C011760.packed 128 cuts11760 = true := by
 decide +kernel
def pointBounds11760 : List (Nat × Nat × Nat) := [(1545380864,93057742154421,93058117884088),(1545430016,93058158518714,93058534248702)]
theorem point_links_checked11760 : (cuts11760.take 2).map (fun c => (1545338881-1+2*2^9*c.k,93057374045556+c.lower,93057749774939+c.upper)) = pointBounds11760 := by
 decide +kernel
def cuts11761 : List PrefixCut := [⟨9,75765443,75765503⟩,
⟨57,497931180,497931564⟩,
⟨105,921358367,921359075⟩,
⟨128,1120409979,1120410845⟩]
theorem checked11761 : checkPrefixCuts (2^48) 1545469953 9 Manual.Count131072.C011761.packed 128 cuts11761 = true := by
 decide +kernel
def pointBounds11761 : List (Nat × Nat × Nat) := [(1545479168,93058574869773,93058950600089),(1545528320,93058997035510,93059372766150),(1545577472,93059420462697,93059796193661)]
theorem point_links_checked11761 : (cuts11761.take 3).map (fun c => (1545469953-1+2*2^9*c.k,93058499104330+c.lower,93058874834586+c.upper)) = pointBounds11761 := by
 decide +kernel
def cuts11762 : List PrefixCut := [⟨25,220537694,220537867⟩,
⟨73,653043337,653043841⟩,
⟨121,1078615289,1078616124⟩,
⟨128,1142167674,1142168557⟩]
theorem checked11762 : checkPrefixCuts (2^48) 1545601025 9 Manual.Count131072.C011762.packed 128 cuts11762 = true := by
 decide +kernel
def pointBounds11762 : List (Nat × Nat × Nat) := [(1545626624,93059840052003,93060215783298),(1545675776,93060272557646,93060648289272),(1545724928,93060698129598,93061073861555)]
theorem point_links_checked11762 : (cuts11762.take 3).map (fun c => (1545601025-1+2*2^9*c.k,93059619514309+c.lower,93059995245431+c.upper)) = pointBounds11762 := by
 decide +kernel
def cuts11763 : List PrefixCut := [⟨41,359456730,359457010⟩,
⟨89,792831584,792832200⟩,
⟨128,1136425910,1136426790⟩]
theorem checked11763 : checkPrefixCuts (2^48) 1545732097 9 Manual.Count131072.C011763.packed 128 cuts11763 = true := by
 decide +kernel
def pointBounds11763 : List (Nat × Nat × Nat) := [(1545774080,93061121138713,93061496870998),(1545823232,93061554513567,93061930246188)]
theorem point_links_checked11763 : (cuts11763.take 2).map (fun c => (1545732097-1+2*2^9*c.k,93060761681983+c.lower,93061137413988+c.upper)) = pointBounds11763 := by
 decide +kernel
def cuts11764 : List PrefixCut := [⟨9,77749057,77749117⟩,
⟨57,497986707,497987101⟩,
⟨105,925857886,925858611⟩,
⟨128,1122674015,1122674897⟩]
theorem checked11764 : checkPrefixCuts (2^48) 1545863169 9 Manual.Count131072.C011764.packed 128 cuts11764 = true := by
 decide +kernel
def pointBounds11764 : List (Nat × Nat × Nat) := [(1545872384,93061975856950,93062351589895),(1545921536,93062396094600,93062771827879),(1545970688,93062823965779,93063199699389)]
theorem point_links_checked11764 : (cuts11764.take 3).map (fun c => (1545863169-1+2*2^9*c.k,93061898107893+c.lower,93062273840778+c.upper)) = pointBounds11764 := by
 decide +kernel
def cuts11765 : List PrefixCut := [⟨25,226489739,226489914⟩,
⟨73,653423420,653423924⟩,
⟨121,1072697360,1072698191⟩,
⟨128,1136597680,1136598560⟩]
theorem checked11765 : checkPrefixCuts (2^48) 1545994241 9 Manual.Count131072.C011765.packed 128 cuts11765 = true := by
 decide +kernel
def pointBounds11765 : List (Nat × Nat × Nat) := [(1546019840,93063247271647,93063623005589),(1546068992,93063674205328,93064049939599),(1546118144,93064093479268,93064469213866)]
theorem point_links_checked11765 : (cuts11765.take 3).map (fun c => (1545994241-1+2*2^9*c.k,93063020781908+c.lower,93063396515675+c.upper)) = pointBounds11765 := by
 decide +kernel
def cuts11766 : List PrefixCut := [⟨41,361185825,361186106⟩,
⟨89,778066379,778066981⟩,
⟨128,1125214193,1125215066⟩]
theorem checked11766 : checkPrefixCuts (2^48) 1546125313 9 Manual.Count131072.C011766.packed 128 cuts11766 = true := by
 decide +kernel
def pointBounds11766 : List (Nat × Nat × Nat) := [(1546167296,93064518565413,93064894300341),(1546216448,93064935445967,93065311181216)]
theorem point_links_checked11766 : (cuts11766.take 2).map (fun c => (1546125313-1+2*2^9*c.k,93064157379588+c.lower,93064533114235+c.upper)) = pointBounds11766 := by
 decide +kernel
def cuts11767 : List PrefixCut := [⟨9,81734067,81734131⟩,
⟨57,500408528,500408915⟩,
⟨105,941094925,941095649⟩,
⟨128,1140227340,1140228219⟩]
theorem checked11767 : checkPrefixCuts (2^48) 1546256385 9 Manual.Count131072.C011767.packed 128 cuts11767 = true := by
 decide +kernel
def pointBounds11767 : List (Nat × Nat × Nat) := [(1546265600,93065364327848,93065740063432),(1546314752,93065783002309,93066158738216),(1546363904,93066223688706,93066599424950)]
theorem point_links_checked11767 : (cuts11767.take 3).map (fun c => (1546256385-1+2*2^9*c.k,93065282593781+c.lower,93065658329301+c.upper)) = pointBounds11767 := by
 decide +kernel
def cuts11768 : List PrefixCut := [⟨25,225522036,225522212⟩,
⟨73,655623545,655624056⟩,
⟨121,1082981152,1082981996⟩,
⟨128,1147411250,1147412143⟩]
theorem checked11768 : checkPrefixCuts (2^48) 1546387457 9 Manual.Count131072.C011768.packed 128 cuts11768 = true := by
 decide +kernel
def pointBounds11768 : List (Nat × Nat × Nat) := [(1546413056,93066648343157,93067024079732),(1546462208,93067078444666,93067454181576),(1546511360,93067505802273,93067881539516)]
theorem point_links_checked11768 : (cuts11768.take 3).map (fun c => (1546387457-1+2*2^9*c.k,93066422821121+c.lower,93066798557520+c.upper)) = pointBounds11768 := by
 decide +kernel
def cuts11769 : List PrefixCut := [⟨41,359455893,359456172⟩,
⟨89,782600443,782601054⟩,
⟨128,1123108211,1123109086⟩]
theorem checked11769 : checkPrefixCuts (2^48) 1546518529 9 Manual.Count131072.C011769.packed 128 cuts11769 = true := by
 decide +kernel
def pointBounds11769 : List (Nat × Nat × Nat) := [(1546560512,93067929688264,93068305425835),(1546609664,93068352832814,93068728570717)]
theorem point_links_checked11769 : (cuts11769.take 2).map (fun c => (1546518529-1+2*2^9*c.k,93067570232371+c.lower,93067945969663+c.upper)) = pointBounds11769 := by
 decide +kernel
def cuts11770 : List PrefixCut := [⟨9,77891522,77891583⟩,
⟨57,500827166,500827554⟩,
⟨105,914468423,914469133⟩,
⟨128,1114278094,1114278958⟩]
theorem checked11770 : checkPrefixCuts (2^48) 1546649601 9 Manual.Count131072.C011770.packed 128 cuts11770 = true := by
 decide +kernel
def pointBounds11770 : List (Nat × Nat × Nat) := [(1546658816,93068771232104,93069146970332),(1546707968,93069194167748,93069569906303),(1546757120,93069607809005,93069983547882)]
theorem point_links_checked11770 : (cuts11770.take 3).map (fun c => (1546649601-1+2*2^9*c.k,93068693340582+c.lower,93069069078749+c.upper)) = pointBounds11770 := by
 decide +kernel
def cuts11771 : List PrefixCut := [⟨25,219277639,219277810⟩,
⟨73,636713961,636714456⟩,
⟨121,1058868054,1058868874⟩,
⟨128,1122735895,1122736764⟩]
theorem checked11771 : checkPrefixCuts (2^48) 1546780673 9 Manual.Count131072.C011771.packed 128 cuts11771 = true := by
 decide +kernel
def pointBounds11771 : List (Nat × Nat × Nat) := [(1546806272,93070026896315,93070402635517),(1546855424,93070444332637,93070820072163),(1546904576,93070866486730,93071242226581)]
theorem point_links_checked11771 : (cuts11771.take 3).map (fun c => (1546780673-1+2*2^9*c.k,93069807618676+c.lower,93070183357707+c.upper)) = pointBounds11771 := by
 decide +kernel
def cuts11772 : List PrefixCut := [⟨41,364095476,364095757⟩,
⟨89,794410506,794411117⟩,
⟨128,1137924775,1137925652⟩]
theorem checked11772 : checkPrefixCuts (2^48) 1546911745 9 Manual.Count131072.C011772.packed 128 cuts11772 = true := by
 decide +kernel
def pointBounds11772 : List (Nat × Nat × Nat) := [(1546953728,93071294450047,93071670190228),(1547002880,93071724765077,93072100505588)]
theorem point_links_checked11772 : (cuts11772.take 2).map (fun c => (1546911745-1+2*2^9*c.k,93070930354571+c.lower,93071306094471+c.upper)) = pointBounds11772 := by
 decide +kernel
def cuts11773 : List PrefixCut := [⟨9,79691154,79691217⟩,
⟨57,499790192,499790580⟩,
⟨105,926243612,926244328⟩,
⟨128,1131096559,1131097432⟩]
theorem checked11773 : checkPrefixCuts (2^48) 1547042817 9 Manual.Count131072.C011773.packed 128 cuts11773 = true := by
 decide +kernel
def pointBounds11773 : List (Nat × Nat × Nat) := [(1547052032,93072147970500,93072523711340),(1547101184,93072568069538,93072943810703),(1547150336,93072994522958,93073370264451)]
theorem point_links_checked11773 : (cuts11773.take 3).map (fun c => (1547042817-1+2*2^9*c.k,93072068279346+c.lower,93072444020123+c.upper)) = pointBounds11773 := by
 decide +kernel
def cuts11774 : List PrefixCut := [⟨25,219403818,219403988⟩,
⟨73,636915903,636916397⟩,
⟨121,1062055172,1062055996⟩,
⟨128,1122814247,1122815118⟩]
theorem checked11774 : checkPrefixCuts (2^48) 1547173889 9 Manual.Count131072.C011774.packed 128 cuts11774 = true := by
 decide +kernel
def pointBounds11774 : List (Nat × Nat × Nat) := [(1547199488,93073418779723,93073794521543),(1547248640,93073836291808,93074212033952),(1547297792,93074261431077,93074637173551)]
theorem point_links_checked11774 : (cuts11774.take 3).map (fun c => (1547173889-1+2*2^9*c.k,93073199375905+c.lower,93073575117555+c.upper)) = pointBounds11774 := by
 decide +kernel
def cuts11775 : List PrefixCut := [⟨41,366549694,366549983⟩,
⟨89,785659181,785659794⟩,
⟨128,1124538649,1124539525⟩]
theorem checked11775 : checkPrefixCuts (2^48) 1547304961 9 Manual.Count131072.C011775.packed 128 cuts11775 = true := by
 decide +kernel
def pointBounds11775 : List (Nat × Nat × Nat) := [(1547346944,93074688739846,93075064482656),(1547396096,93075107849333,93075483592467)]
theorem point_links_checked11775 : (cuts11775.take 2).map (fun c => (1547304961-1+2*2^9*c.k,93074322190152+c.lower,93074697932673+c.upper)) = pointBounds11775 := by
 decide +kernel
def cuts11776 : List PrefixCut := [⟨9,77851924,77851984⟩,
⟨57,493296911,493297295⟩,
⟨105,920369638,920370354⟩,
⟨128,1124442972,1124443850⟩]
theorem checked11776 : checkPrefixCuts (2^48) 1547436033 9 Manual.Count131072.C011776.packed 128 cuts11776 = true := by
 decide +kernel
def pointBounds11776 : List (Nat × Nat × Nat) := [(1547445248,93075524580725,93075900324182),(1547494400,93075940025712,93076315769493),(1547543552,93076367098439,93076742842552)]
theorem point_links_checked11776 : (cuts11776.take 3).map (fun c => (1547436033-1+2*2^9*c.k,93075446728801+c.lower,93075822472198+c.upper)) = pointBounds11776 := by
 decide +kernel
def cuts11777 : List PrefixCut := [⟨25,220075598,220075768⟩,
⟨73,646393693,646394192⟩,
⟨121,1071424990,1071425819⟩,
⟨128,1135260370,1135261248⟩]
theorem checked11777 : checkPrefixCuts (2^48) 1547567105 9 Manual.Count131072.C011777.packed 128 cuts11777 = true := by
 decide +kernel
def pointBounds11777 : List (Nat × Nat × Nat) := [(1547592704,93076791247371,93077166991816),(1547641856,93077217565466,93077593310240),(1547691008,93077642596763,93078018341867)]
theorem point_links_checked11777 : (cuts11777.take 3).map (fun c => (1547567105-1+2*2^9*c.k,93076571171773+c.lower,93076946916048+c.upper)) = pointBounds11777 := by
 decide +kernel
def cuts11778 : List PrefixCut := [⟨41,348270226,348270500⟩,
⟨89,775638744,775639351⟩,
⟨128,1116978144,1116979018⟩]
theorem checked11778 : checkPrefixCuts (2^48) 1547698177 9 Manual.Count131072.C011778.packed 128 cuts11778 = true := by
 decide +kernel
def pointBounds11778 : List (Nat × Nat × Nat) := [(1547740160,93078054702369,93078430447796),(1547789312,93078482070887,93078857816647)]
theorem point_links_checked11778 : (cuts11778.take 2).map (fun c => (1547698177-1+2*2^9*c.k,93077706432143+c.lower,93078082177296+c.upper)) = pointBounds11778 := by
 decide +kernel
def cuts11779 : List PrefixCut := [⟨9,78014011,78014073⟩,
⟨57,490080277,490080656⟩,
⟨105,914680468,914681177⟩,
⟨128,1120702208,1120703073⟩]
theorem checked11779 : checkPrefixCuts (2^48) 1547829249 9 Manual.Count131072.C011779.packed 128 cuts11779 = true := by
 decide +kernel
def pointBounds11779 : List (Nat × Nat × Nat) := [(1547838464,93078901424298,93079277170387),(1547887616,93079313490564,93079689236970),(1547936768,93079738090755,93080113837491)]
theorem point_links_checked11779 : (cuts11779.take 3).map (fun c => (1547829249-1+2*2^9*c.k,93078823410287+c.lower,93079199156314+c.upper)) = pointBounds11779 := by
 decide +kernel
def cuts11780 : List PrefixCut := [⟨25,221110705,221110876⟩,
⟨73,640774599,640775096⟩,
⟨121,1061334142,1061334967⟩,
⟨128,1124426030,1124426904⟩]
theorem checked11780 : checkPrefixCuts (2^48) 1547960321 9 Manual.Count131072.C011780.packed 128 cuts11780 = true := by
 decide +kernel
def pointBounds11780 : List (Nat × Nat × Nat) := [(1547985920,93080165223200,93080540970263),(1548035072,93080584887094,93080960634483),(1548084224,93081005446637,93081381194354)]
theorem point_links_checked11780 : (cuts11780.take 3).map (fun c => (1547960321-1+2*2^9*c.k,93079944112495+c.lower,93080319859387+c.upper)) = pointBounds11780 := by
 decide +kernel
def cuts11781 : List PrefixCut := [⟨41,366908909,366909195⟩,
⟨89,795805129,795805752⟩,
⟨128,1141421206,1141422097⟩]
theorem checked11781 : checkPrefixCuts (2^48) 1548091393 9 Manual.Count131072.C011781.packed 128 cuts11781 = true := by
 decide +kernel
def pointBounds11781 : List (Nat × Nat × Nat) := [(1548133376,93081435447434,93081811195486),(1548182528,93081864343654,93082240092043)]
theorem point_links_checked11781 : (cuts11781.take 2).map (fun c => (1548091393-1+2*2^9*c.k,93081068538525+c.lower,93081444286291+c.upper)) = pointBounds11781 := by
 decide +kernel
def cuts11782 : List PrefixCut := [⟨9,78539608,78539668⟩,
⟨57,501954556,501954939⟩,
⟨105,927901199,927901907⟩,
⟨128,1124599265,1124600125⟩]
theorem checked11782 : checkPrefixCuts (2^48) 1548222465 9 Manual.Count131072.C011782.packed 128 cuts11782 = true := by
 decide +kernel
def pointBounds11782 : List (Nat × Nat × Nat) := [(1548231680,93082288499339,93082664248056),(1548280832,93082711914287,93083087663327),(1548329984,93083137860930,93083513610295)]
theorem point_links_checked11782 : (cuts11782.take 3).map (fun c => (1548222465-1+2*2^9*c.k,93082209959731+c.lower,93082585708388+c.upper)) = pointBounds11782 := by
 decide +kernel
def cuts11783 : List PrefixCut := [⟨25,219782056,219782222⟩,
⟨73,630613677,630614167⟩,
⟨121,1058155780,1058156600⟩,
⟨128,1120140996,1120141864⟩]
theorem checked11783 : checkPrefixCuts (2^48) 1548353537 9 Manual.Count131072.C011783.packed 128 cuts11783 = true := by
 decide +kernel
def pointBounds11783 : List (Nat × Nat × Nat) := [(1548379136,93083554341052,93083930090735),(1548428288,93083965172673,93084340922680),(1548477440,93084392714776,93084768465113)]
theorem point_links_checked11783 : (cuts11783.take 3).map (fun c => (1548353537-1+2*2^9*c.k,93083334558996+c.lower,93083710308513+c.upper)) = pointBounds11783 := by
 decide +kernel
def cuts11784 : List PrefixCut := [⟨41,360817241,360817521⟩,
⟨89,780516284,780516888⟩,
⟨128,1130770442,1130771317⟩]
theorem checked11784 : checkPrefixCuts (2^48) 1548484609 9 Manual.Count131072.C011784.packed 128 cuts11784 = true := by
 decide +kernel
def pointBounds11784 : List (Nat × Nat × Nat) := [(1548526592,93084815517233,93085191267898),(1548575744,93085235216276,93085610967265)]
theorem point_links_checked11784 : (cuts11784.take 2).map (fun c => (1548484609-1+2*2^9*c.k,93084454699992+c.lower,93084830450377+c.upper)) = pointBounds11784 := by
 decide +kernel
def cuts11785 : List PrefixCut := [⟨9,78519661,78519722⟩,
⟨57,501645524,501645911⟩,
⟨105,928211191,928211909⟩,
⟨128,1126131488,1126132361⟩]
theorem checked11785 : checkPrefixCuts (2^48) 1548615681 9 Manual.Count131072.C011785.packed 128 cuts11785 = true := by
 decide +kernel
def pointBounds11785 : List (Nat × Nat × Nat) := [(1548624896,93085663990095,93086039741416),(1548674048,93086087115958,93086462867605),(1548723200,93086513681625,93086889433603)]
theorem point_links_checked11785 : (cuts11785.take 3).map (fun c => (1548615681-1+2*2^9*c.k,93085585470434+c.lower,93085961221694+c.upper)) = pointBounds11785 := by
 decide +kernel
def cuts11786 : List PrefixCut := [⟨25,218272321,218272489⟩,
⟨73,641903006,641903502⟩,
⟨121,1053162474,1053163282⟩,
⟨128,1113132943,1113133797⟩]
theorem checked11786 : checkPrefixCuts (2^48) 1548746753 9 Manual.Count131072.C011786.packed 128 cuts11786 = true := by
 decide +kernel
def pointBounds11786 : List (Nat × Nat × Nat) := [(1548772352,93086929874243,93087305626544),(1548821504,93087353504928,93087729257557),(1548870656,93087764764396,93088140517337)]
theorem point_links_checked11786 : (cuts11786.take 3).map (fun c => (1548746753-1+2*2^9*c.k,93086711601922+c.lower,93087087354055+c.upper)) = pointBounds11786 := by
 decide +kernel
def cuts11787 : List PrefixCut := [⟨41,353274955,353275230⟩,
⟨89,782862085,782862696⟩,
⟨128,1126303802,1126304676⟩]
theorem checked11787 : checkPrefixCuts (2^48) 1548877825 9 Manual.Count131072.C011787.packed 128 cuts11787 = true := by
 decide +kernel
def pointBounds11787 : List (Nat × Nat × Nat) := [(1548919808,93088178009820,93088553763082),(1548968960,93088607596950,93088983350548)]
theorem point_links_checked11787 : (cuts11787.take 2).map (fun c => (1548877825-1+2*2^9*c.k,93087824734865+c.lower,93088200487852+c.upper)) = pointBounds11787 := by
 decide +kernel
def cuts11788 : List PrefixCut := [⟨9,78318018,78318080⟩,
⟨57,498792481,498792872⟩,
⟨105,913620774,913621484⟩,
⟨128,1119303946,1119304817⟩]
theorem checked11788 : checkPrefixCuts (2^48) 1549008897 9 Manual.Count131072.C011788.packed 128 cuts11788 = true := by
 decide +kernel
def pointBounds11788 : List (Nat × Nat × Nat) := [(1549018112,93089029356685,93089405110608),(1549067264,93089449831148,93089825585400),(1549116416,93089864659441,93090240414012)]
theorem point_links_checked11788 : (cuts11788.take 3).map (fun c => (1549008897-1+2*2^9*c.k,93088951038667+c.lower,93089326792528+c.upper)) = pointBounds11788 := by
 decide +kernel
def cuts11789 : List PrefixCut := [⟨25,216036533,216036700⟩,
⟨73,642830268,642830760⟩,
⟨121,1066703407,1066704230⟩,
⟨128,1125568553,1125569422⟩]
theorem checked11789 : checkPrefixCuts (2^48) 1549139969 9 Manual.Count131072.C011789.packed 128 cuts11789 = true := by
 decide +kernel
def pointBounds11789 : List (Nat × Nat × Nat) := [(1549165568,93090286379146,93090662134045),(1549214720,93090713172881,93091088928105),(1549263872,93091137046020,93091512801575)]
theorem point_links_checked11789 : (cuts11789.take 3).map (fun c => (1549139969-1+2*2^9*c.k,93090070342613+c.lower,93090446097345+c.upper)) = pointBounds11789 := by
 decide +kernel
def cuts11790 : List PrefixCut := [⟨41,361724273,361724556⟩,
⟨89,782663660,782664266⟩,
⟨128,1121294877,1121295748⟩]
theorem checked11790 : checkPrefixCuts (2^48) 1549271041 9 Manual.Count131072.C011790.packed 128 cuts11790 = true := by
 decide +kernel
def pointBounds11790 : List (Nat × Nat × Nat) := [(1549313024,93091557635439,93091933391323),(1549362176,93091978574826,93092354331033)]
theorem point_links_checked11790 : (cuts11790.take 2).map (fun c => (1549271041-1+2*2^9*c.k,93091195911166+c.lower,93091571666767+c.upper)) = pointBounds11790 := by
 decide +kernel
def cuts11791 : List PrefixCut := [⟨9,82476468,82476533⟩,
⟨57,508657468,508657863⟩,
⟨105,927377018,927377736⟩,
⟨128,1127376719,1127377590⟩]
theorem checked11791 : checkPrefixCuts (2^48) 1549402113 9 Manual.Count131072.C011791.packed 128 cuts11791 = true := by
 decide +kernel
def pointBounds11791 : List (Nat × Nat × Nat) := [(1549411328,93092399682511,93092775439048),(1549460480,93092825863511,93093201620378),(1549509632,93093244583061,93093620340251)]
theorem point_links_checked11791 : (cuts11791.take 3).map (fun c => (1549402113-1+2*2^9*c.k,93092317206043+c.lower,93092692962515+c.upper)) = pointBounds11791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000055
