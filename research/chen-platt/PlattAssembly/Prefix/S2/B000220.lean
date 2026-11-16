import PlattAssemblyKernel
import PlattCertificates.Count131072.C017040
import PlattCertificates.Count131072.C017041
import PlattCertificates.Count131072.C017042
import PlattCertificates.Count131072.C017043
import PlattCertificates.Count131072.C017044
import PlattCertificates.Count131072.C017045
import PlattCertificates.Count131072.C017046
import PlattCertificates.Count131072.C017047
import PlattCertificates.Count131072.C017048
import PlattCertificates.Count131072.C017049
import PlattCertificates.Count131072.C017050
import PlattCertificates.Count131072.C017051
import PlattCertificates.Count131072.C017052
import PlattCertificates.Count131072.C017053
import PlattCertificates.Count131072.C017054
import PlattCertificates.Count131072.C017055
import PlattCertificates.Count131072.C017056
import PlattCertificates.Count131072.C017057
import PlattCertificates.Count131072.C017058
import PlattCertificates.Count131072.C017059
import PlattCertificates.Count131072.C017060
import PlattCertificates.Count131072.C017061
import PlattCertificates.Count131072.C017062
import PlattCertificates.Count131072.C017063
import PlattCertificates.Count131072.C017064
import PlattCertificates.Count131072.C017065
import PlattCertificates.Count131072.C017066
import PlattCertificates.Count131072.C017067
import PlattCertificates.Count131072.C017068
import PlattCertificates.Count131072.C017069
import PlattCertificates.Count131072.C017070
import PlattCertificates.Count131072.C017071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000220
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17040 : List PrefixCut := [⟨21,122029791,122029866⟩,
⟨90,537803126,537803462⟩,
⟨128,758956427,758956899⟩]
theorem checked17040 : checkPrefixCuts (2^48) 2237399041 9 Manual.Count131072.C017040.packed 128 cuts17040 = true := by
 decide +kernel
def pointBounds17040 : List (Nat × Nat × Nat) := [(2237420544,97937875387029,97938254496420),(2237491200,97938291160364,97938670270016)]
theorem point_links_checked17040 : (cuts17040.take 2).map (fun c => (2237399041-1+2*2^9*c.k,97937753357238+c.lower,97938132466554+c.upper)) = pointBounds17040 := by
 decide +kernel
def cuts17041 : List PrefixCut := [⟨31,184039900,184040015⟩,
⟨100,592239313,592239685⟩,
⟨128,759540793,759541265⟩]
theorem checked17041 : checkPrefixCuts (2^48) 2237530113 9 Manual.Count131072.C017041.packed 128 cuts17041 = true := by
 decide +kernel
def pointBounds17041 : List (Nat × Nat × Nat) := [(2237561856,97938696353565,97939075463468),(2237632512,97939104552978,97939483663138)]
theorem point_links_checked17041 : (cuts17041.take 2).map (fun c => (2237530113-1+2*2^9*c.k,97938512313665+c.lower,97938891423453+c.upper)) = pointBounds17041 := by
 decide +kernel
def cuts17042 : List PrefixCut := [⟨41,242897791,242897941⟩,
⟨110,657612306,657612708⟩,
⟨128,760880087,760880551⟩]
theorem checked17042 : checkPrefixCuts (2^48) 2237661185 9 Manual.Count131072.C017042.packed 128 cuts17042 = true := by
 decide +kernel
def pointBounds17042 : List (Nat × Nat × Nat) := [(2237703168,97939514752249,97939893862659),(2237773824,97939929466764,97940308577426)]
theorem point_links_checked17042 : (cuts17042.take 2).map (fun c => (2237661185-1+2*2^9*c.k,97939271854458+c.lower,97939650964718+c.upper)) = pointBounds17042 := by
 decide +kernel
def cuts17043 : List PrefixCut := [⟨51,306150792,306150986⟩,
⟨120,711154319,711154770⟩,
⟨128,757062291,757062769⟩]
theorem checked17043 : checkPrefixCuts (2^48) 2237792257 9 Manual.Count131072.C017043.packed 128 cuts17043 = true := by
 decide +kernel
def pointBounds17043 : List (Nat × Nat × Nat) := [(2237844480,97940338885337,97940717996255),(2237915136,97940743888864,97941123000039)]
theorem point_links_checked17043 : (cuts17043.take 2).map (fun c => (2237792257-1+2*2^9*c.k,97940032734545+c.lower,97940411845269+c.upper)) = pointBounds17043 := by
 decide +kernel
def cuts17044 : List PrefixCut := [⟨61,358076569,358076794⟩,
⟨128,763809281,763809754⟩]
theorem checked17044 : checkPrefixCuts (2^48) 2237923329 9 Manual.Count131072.C017044.packed 128 cuts17044 = true := by
 decide +kernel
def pointBounds17044 : List (Nat × Nat × Nat) := [(2237985792,97941147873405,97941526984832)]
theorem point_links_checked17044 : (cuts17044.take 1).map (fun c => (2237923329-1+2*2^9*c.k,97940789796836+c.lower,97941168908038+c.upper)) = pointBounds17044 := by
 decide +kernel
def cuts17045 : List PrefixCut := [⟨2,11444852,11444860⟩,
⟨71,428734976,428735247⟩,
⟨128,770052954,770053440⟩]
theorem checked17045 : checkPrefixCuts (2^48) 2238054401 9 Manual.Count131072.C017045.packed 128 cuts17045 = true := by
 decide +kernel
def pointBounds17045 : List (Nat × Nat × Nat) := [(2238056448,97941565050969,97941944162652),(2238127104,97941982341093,97942361453039)]
theorem point_links_checked17045 : (cuts17045.take 2).map (fun c => (2238054401-1+2*2^9*c.k,97941553606117+c.lower,97941932717792+c.upper)) = pointBounds17045 := by
 decide +kernel
def cuts17046 : List PrefixCut := [⟨12,73318052,73318097⟩,
⟨81,484796977,484797273⟩,
⟨128,764474533,764475005⟩]
theorem checked17046 : checkPrefixCuts (2^48) 2238185473 9 Manual.Count131072.C017046.packed 128 cuts17046 = true := by
 decide +kernel
def pointBounds17046 : List (Nat × Nat × Nat) := [(2238197760,97942396977123,97942776089329),(2238268416,97942808456048,97943187568505)]
theorem point_links_checked17046 : (cuts17046.take 2).map (fun c => (2238185473-1+2*2^9*c.k,97942323659071+c.lower,97942702771232+c.upper)) = pointBounds17046 := by
 decide +kernel
def cuts17047 : List PrefixCut := [⟨22,125123556,125123635⟩,
⟨91,535822077,535822411⟩,
⟨128,761411538,761412017⟩]
theorem checked17047 : checkPrefixCuts (2^48) 2238316545 9 Manual.Count131072.C017047.packed 128 cuts17047 = true := by
 decide +kernel
def pointBounds17047 : List (Nat × Nat × Nat) := [(2238339072,97943213257160,97943592369872),(2238409728,97943623955681,97944003068648)]
theorem point_links_checked17047 : (cuts17047.take 2).map (fun c => (2238316545-1+2*2^9*c.k,97943088133604+c.lower,97943467246237+c.upper)) = pointBounds17047 := by
 decide +kernel
def cuts17048 : List PrefixCut := [⟨32,185599093,185599211⟩,
⟨101,598786581,598786959⟩,
⟨128,760235435,760235916⟩]
theorem checked17048 : checkPrefixCuts (2^48) 2238447617 9 Manual.Count131072.C017048.packed 128 cuts17048 = true := by
 decide +kernel
def pointBounds17048 : List (Nat × Nat × Nat) := [(2238480384,97944035144235,97944414257465),(2238551040,97944448331723,97944827445213)]
theorem point_links_checked17048 : (cuts17048.take 2).map (fun c => (2238447617-1+2*2^9*c.k,97943849545142+c.lower,97944228658254+c.upper)) = pointBounds17048 := by
 decide +kernel
def cuts17049 : List PrefixCut := [⟨42,247073201,247073353⟩,
⟨111,661114680,661115086⟩,
⟨128,760316711,760317182⟩]
theorem checked17049 : checkPrefixCuts (2^48) 2238578689 9 Manual.Count131072.C017049.packed 128 cuts17049 = true := by
 decide +kernel
def pointBounds17049 : List (Nat × Nat × Nat) := [(2238621696,97944856853778,97945235967523),(2238692352,97945270895257,97945650009256)]
theorem point_links_checked17049 : (cuts17049.take 2).map (fun c => (2238578689-1+2*2^9*c.k,97944609780577+c.lower,97944988894170+c.upper)) = pointBounds17049 := by
 decide +kernel
def cuts17050 : List PrefixCut := [⟨52,307156851,307157043⟩,
⟨121,728464261,728464713⟩,
⟨128,770581699,770582177⟩]
theorem checked17050 : checkPrefixCuts (2^48) 2238709761 9 Manual.Count131072.C017050.packed 128 cuts17050 = true := by
 decide +kernel
def pointBounds17050 : List (Nat × Nat × Nat) := [(2238763008,97945677254139,97946056368395),(2238833664,97946098561549,97946477676065)]
theorem point_links_checked17050 : (cuts17050.take 2).map (fun c => (2238709761-1+2*2^9*c.k,97945370097288+c.lower,97945749211352+c.upper)) = pointBounds17050 := by
 decide +kernel
def cuts17051 : List PrefixCut := [⟨62,372639203,372639435⟩,
⟨128,771919687,771920172⟩]
theorem checked17051 : checkPrefixCuts (2^48) 2238840833 9 Manual.Count131072.C017051.packed 128 cuts17051 = true := by
 decide +kernel
def pointBounds17051 : List (Nat × Nat × Nat) := [(2238904320,97946513318190,97946892432964)]
theorem point_links_checked17051 : (cuts17051.take 1).map (fun c => (2238840833-1+2*2^9*c.k,97946140678987+c.lower,97946519793529+c.upper)) = pointBounds17051 := by
 decide +kernel
def cuts17052 : List PrefixCut := [⟨3,16343086,16343097⟩,
⟨72,439496322,439496596⟩,
⟨128,769988905,769989387⟩]
theorem checked17052 : checkPrefixCuts (2^48) 2238971905 9 Manual.Count131072.C017052.packed 128 cuts17052 = true := by
 decide +kernel
def pointBounds17052 : List (Nat × Nat × Nat) := [(2238974976,97946928941760,97947308056798),(2239045632,97947352094996,97947731210297)]
theorem point_links_checked17052 : (cuts17052.take 2).map (fun c => (2238971905-1+2*2^9*c.k,97946912598674+c.lower,97947291713701+c.upper)) = pointBounds17052 := by
 decide +kernel
def cuts17053 : List PrefixCut := [⟨13,74293671,74293717⟩,
⟨82,488117977,488118280⟩,
⟨128,762652741,762653214⟩]
theorem checked17053 : checkPrefixCuts (2^48) 2239102977 9 Manual.Count131072.C017053.packed 128 cuts17053 = true := by
 decide +kernel
def pointBounds17053 : List (Nat × Nat × Nat) := [(2239116288,97947756881250,97948135996805),(2239186944,97948170705556,97948549821368)]
theorem point_links_checked17053 : (cuts17053.take 2).map (fun c => (2239102977-1+2*2^9*c.k,97947682587579+c.lower,97948061703088+c.upper)) = pointBounds17053 := by
 decide +kernel
def cuts17054 : List PrefixCut := [⟨23,140533439,140533525⟩,
⟨92,559233753,559234094⟩,
⟨128,775429314,775429792⟩]
theorem checked17054 : checkPrefixCuts (2^48) 2239234049 9 Manual.Count131072.C017054.packed 128 cuts17054 = true := by
 decide +kernel
def pointBounds17054 : List (Nat × Nat × Nat) := [(2239257600,97948585773759,97948964889827),(2239328256,97949004474073,97949383590396)]
theorem point_links_checked17054 : (cuts17054.take 2).map (fun c => (2239234049-1+2*2^9*c.k,97948445240320+c.lower,97948824356302+c.upper)) = pointBounds17054 := by
 decide +kernel
def cuts17055 : List PrefixCut := [⟨33,197966641,197966762⟩,
⟨102,604825789,604826161⟩,
⟨128,760678229,760678697⟩]
theorem checked17055 : checkPrefixCuts (2^48) 2239365121 9 Manual.Count131072.C017055.packed 128 cuts17055 = true := by
 decide +kernel
def pointBounds17055 : List (Nat × Nat × Nat) := [(2239398912,97949418636275,97949797752856),(2239469568,97949825495423,97950204612255)]
theorem point_links_checked17055 : (cuts17055.take 2).map (fun c => (2239365121-1+2*2^9*c.k,97949220669634+c.lower,97949599786094+c.upper)) = pointBounds17055 := by
 decide +kernel
def cuts17056 : List PrefixCut := [⟨43,249988377,249988537⟩,
⟨112,659084133,659084552⟩,
⟨128,758245497,758245978⟩]
theorem checked17056 : checkPrefixCuts (2^48) 2239496193 9 Manual.Count131072.C017056.packed 128 cuts17056 = true := by
 decide +kernel
def pointBounds17056 : List (Nat × Nat × Nat) := [(2239540224,97950231336240,97950610453328),(2239610880,97950640431996,97951019549343)]
theorem point_links_checked17056 : (cuts17056.take 2).map (fun c => (2239496193-1+2*2^9*c.k,97949981347863+c.lower,97950360464791+c.upper)) = pointBounds17056 := by
 decide +kernel
def cuts17057 : List PrefixCut := [⟨53,315828451,315828651⟩,
⟨122,726280771,726281223⟩,
⟨128,762977043,762977519⟩]
theorem checked17057 : checkPrefixCuts (2^48) 2239627265 9 Manual.Count131072.C017057.packed 128 cuts17057 = true := by
 decide +kernel
def pointBounds17057 : List (Nat × Nat × Nat) := [(2239681536,97951055421811,97951434539420),(2239752192,97951465874131,97951844991992)]
theorem point_links_checked17057 : (cuts17057.take 2).map (fun c => (2239627265-1+2*2^9*c.k,97950739593360+c.lower,97951118710769+c.upper)) = pointBounds17057 := by
 decide +kernel
def cuts17058 : List PrefixCut := [⟨63,381157643,381157881⟩,
⟨128,776630185,776630667⟩]
theorem checked17058 : checkPrefixCuts (2^48) 2239758337 9 Manual.Count131072.C017058.packed 128 cuts17058 = true := by
 decide +kernel
def pointBounds17058 : List (Nat × Nat × Nat) := [(2239822848,97951883728046,97952262846169)]
theorem point_links_checked17058 : (cuts17058.take 1).map (fun c => (2239758337-1+2*2^9*c.k,97951502570403+c.lower,97951881688288+c.upper)) = pointBounds17058 := by
 decide +kernel
def cuts17059 : List PrefixCut := [⟨4,22242621,22242634⟩,
⟨73,429388916,429389184⟩,
⟨128,763264524,763265004⟩]
theorem checked17059 : checkPrefixCuts (2^48) 2239889409 9 Manual.Count131072.C017059.packed 128 cuts17059 = true := by
 decide +kernel
def pointBounds17059 : List (Nat × Nat × Nat) := [(2239893504,97952301443209,97952680561589),(2239964160,97952708589504,97953087708139)]
theorem point_links_checked17059 : (cuts17059.take 2).map (fun c => (2239889409-1+2*2^9*c.k,97952279200588+c.lower,97952658318955+c.upper)) = pointBounds17059 := by
 decide +kernel
def cuts17060 : List PrefixCut := [⟨14,80294741,80294793⟩,
⟨83,490682335,490682643⟩,
⟨128,760329856,760330331⟩]
theorem checked17060 : checkPrefixCuts (2^48) 2240020481 9 Manual.Count131072.C017060.packed 128 cuts17060 = true := by
 decide +kernel
def pointBounds17060 : List (Nat × Nat × Nat) := [(2240034816,97953122759853,97953501878752),(2240105472,97953533147447,97953912266602)]
theorem point_links_checked17060 : (cuts17060.take 2).map (fun c => (2240020481-1+2*2^9*c.k,97953042465112+c.lower,97953421583959+c.upper)) = pointBounds17060 := by
 decide +kernel
def cuts17061 : List PrefixCut := [⟨24,144747921,144748011⟩,
⟨93,558879053,558879391⟩,
⟨128,768578213,768578682⟩]
theorem checked17061 : checkPrefixCuts (2^48) 2240151553 9 Manual.Count131072.C017061.packed 128 cuts17061 = true := by
 decide +kernel
def pointBounds17061 : List (Nat × Nat × Nat) := [(2240176128,97953947542889,97954326662301),(2240246784,97954361674021,97954740793681)]
theorem point_links_checked17061 : (cuts17061.take 2).map (fun c => (2240151553-1+2*2^9*c.k,97953802794968+c.lower,97954181914290+c.upper)) = pointBounds17061 := by
 decide +kernel
def cuts17062 : List PrefixCut := [⟨34,204167590,204167719⟩,
⟨103,614880286,614880672⟩,
⟨128,764010154,764010634⟩]
theorem checked17062 : checkPrefixCuts (2^48) 2240282625 9 Manual.Count131072.C017062.packed 128 cuts17062 = true := by
 decide +kernel
def pointBounds17062 : List (Nat × Nat × Nat) := [(2240317440,97954775540771,97955154660691),(2240388096,97955186253467,97955565373644)]
theorem point_links_checked17062 : (cuts17062.take 2).map (fun c => (2240282625-1+2*2^9*c.k,97954571373181+c.lower,97954950492972+c.upper)) = pointBounds17062 := by
 decide +kernel
def cuts17063 : List PrefixCut := [⟨44,263077515,263077681⟩,
⟨113,669869840,669870258⟩,
⟨128,758814679,758815153⟩]
theorem checked17063 : checkPrefixCuts (2^48) 2240413697 9 Manual.Count131072.C017063.packed 128 cuts17063 = true := by
 decide +kernel
def pointBounds17063 : List (Nat × Nat × Nat) := [(2240458752,97955598460850,97955977581287),(2240529408,97956005253175,97956384373864)]
theorem point_links_checked17063 : (cuts17063.take 2).map (fun c => (2240413697-1+2*2^9*c.k,97955335383335+c.lower,97955714503606+c.upper)) = pointBounds17063 := by
 decide +kernel
def cuts17064 : List PrefixCut := [⟨54,319216493,319216690⟩,
⟨123,738545354,738545808⟩,
⟨128,766935625,766936097⟩]
theorem checked17064 : checkPrefixCuts (2^48) 2240544769 9 Manual.Count131072.C017064.packed 128 cuts17064 = true := by
 decide +kernel
def pointBounds17064 : List (Nat × Nat × Nat) := [(2240600064,97956413414507,97956792535449),(2240670720,97956832743368,97957211864567)]
theorem point_links_checked17064 : (cuts17064.take 2).map (fun c => (2240544769-1+2*2^9*c.k,97956094198014+c.lower,97956473318759+c.upper)) = pointBounds17064 := by
 decide +kernel
def cuts17065 : List PrefixCut := [⟨64,380875891,380876132⟩,
⟨128,758600211,758600687⟩]
theorem checked17065 : checkPrefixCuts (2^48) 2240675841 9 Manual.Count131072.C017065.packed 128 cuts17065 = true := by
 decide +kernel
def pointBounds17065 : List (Nat × Nat × Nat) := [(2240741376,97957242009530,97957621130988)]
theorem point_links_checked17065 : (cuts17065.take 1).map (fun c => (2240675841-1+2*2^9*c.k,97956861133639+c.lower,97957240254856+c.upper)) = pointBounds17065 := by
 decide +kernel
def cuts17066 : List PrefixCut := [⟨5,28765386,28765405⟩,
⟨74,441145935,441146208⟩,
⟨128,765589813,765590290⟩]
theorem checked17066 : checkPrefixCuts (2^48) 2240806913 9 Manual.Count131072.C017066.packed 128 cuts17066 = true := by
 decide +kernel
def pointBounds17066 : List (Nat × Nat × Nat) := [(2240812032,97957648499236,97958027620948),(2240882688,97958060879785,97958440001751)]
theorem point_links_checked17066 : (cuts17066.take 2).map (fun c => (2240806913-1+2*2^9*c.k,97957619733850+c.lower,97957998855543+c.upper)) = pointBounds17066 := by
 decide +kernel
def cuts17067 : List PrefixCut := [⟨15,88300602,88300660⟩,
⟨84,504674484,504674801⟩,
⟨128,768308342,768308823⟩]
theorem checked17067 : checkPrefixCuts (2^48) 2240937985 9 Manual.Count131072.C017067.packed 128 cuts17067 = true := by
 decide +kernel
def pointBounds17067 : List (Nat × Nat × Nat) := [(2240953344,97958473624265,97958852746493),(2241024000,97958889998147,97959269120634)]
theorem point_links_checked17067 : (cuts17067.take 2).map (fun c => (2240937985-1+2*2^9*c.k,97958385323663+c.lower,97958764445833+c.upper)) = pointBounds17067 := by
 decide +kernel
def cuts17068 : List PrefixCut := [⟨25,147702968,147703060⟩,
⟨94,566436943,566437292⟩,
⟨128,772784805,772785280⟩]
theorem checked17068 : checkPrefixCuts (2^48) 2241069057 9 Manual.Count131072.C017068.packed 128 cuts17068 = true := by
 decide +kernel
def pointBounds17068 : List (Nat × Nat × Nat) := [(2241094656,97959301334973,97959680457716),(2241165312,97959720068948,97960099191948)]
theorem point_links_checked17068 : (cuts17068.take 2).map (fun c => (2241069057-1+2*2^9*c.k,97959153632005+c.lower,97959532754656+c.upper)) = pointBounds17068 := by
 decide +kernel
def cuts17069 : List PrefixCut := [⟨35,209861115,209861245⟩,
⟨104,627187204,627187596⟩,
⟨128,765832478,765832959⟩]
theorem checked17069 : checkPrefixCuts (2^48) 2241200129 9 Manual.Count131072.C017069.packed 128 cuts17069 = true := by
 decide +kernel
def pointBounds17069 : List (Nat × Nat × Nat) := [(2241235968,97960136277925,97960515401181),(2241306624,97960553604014,97960932727532)]
theorem point_links_checked17069 : (cuts17069.take 2).map (fun c => (2241200129-1+2*2^9*c.k,97959926416810+c.lower,97960305539936+c.upper)) = pointBounds17069 := by
 decide +kernel
def cuts17070 : List PrefixCut := [⟨45,270127944,270128112⟩,
⟨114,683660405,683660836⟩,
⟨128,767420166,767420648⟩]
theorem checked17070 : checkPrefixCuts (2^48) 2241331201 9 Manual.Count131072.C017070.packed 128 cuts17070 = true := by
 decide +kernel
def pointBounds17070 : List (Nat × Nat × Nat) := [(2241377280,97960962377232,97961341501007),(2241447936,97961375909693,97961755033731)]
theorem point_links_checked17070 : (cuts17070.take 2).map (fun c => (2241331201-1+2*2^9*c.k,97960692249288+c.lower,97961071372895+c.upper)) = pointBounds17070 := by
 decide +kernel
def cuts17071 : List PrefixCut := [⟨55,335912768,335912978⟩,
⟨124,747661128,747661592⟩,
⟨128,773151681,773152160⟩]
theorem checked17071 : checkPrefixCuts (2^48) 2241462273 9 Manual.Count131072.C017071.packed 128 cuts17071 = true := by
 decide +kernel
def pointBounds17071 : List (Nat × Nat × Nat) := [(2241518592,97961795582222,97962174706521),(2241589248,97962207330582,97962586455135)]
theorem point_links_checked17071 : (cuts17071.take 2).map (fun c => (2241462273-1+2*2^9*c.k,97961459669454+c.lower,97961838793543+c.upper)) = pointBounds17071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000220
