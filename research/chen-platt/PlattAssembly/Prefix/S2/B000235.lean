import PlattAssemblyKernel
import PlattCertificates.Count131072.C017520
import PlattCertificates.Count131072.C017521
import PlattCertificates.Count131072.C017522
import PlattCertificates.Count131072.C017523
import PlattCertificates.Count131072.C017524
import PlattCertificates.Count131072.C017525
import PlattCertificates.Count131072.C017526
import PlattCertificates.Count131072.C017527
import PlattCertificates.Count131072.C017528
import PlattCertificates.Count131072.C017529
import PlattCertificates.Count131072.C017530
import PlattCertificates.Count131072.C017531
import PlattCertificates.Count131072.C017532
import PlattCertificates.Count131072.C017533
import PlattCertificates.Count131072.C017534
import PlattCertificates.Count131072.C017535
import PlattCertificates.Count131072.C017536
import PlattCertificates.Count131072.C017537
import PlattCertificates.Count131072.C017538
import PlattCertificates.Count131072.C017539
import PlattCertificates.Count131072.C017540
import PlattCertificates.Count131072.C017541
import PlattCertificates.Count131072.C017542
import PlattCertificates.Count131072.C017543
import PlattCertificates.Count131072.C017544
import PlattCertificates.Count131072.C017545
import PlattCertificates.Count131072.C017546
import PlattCertificates.Count131072.C017547
import PlattCertificates.Count131072.C017548
import PlattCertificates.Count131072.C017549
import PlattCertificates.Count131072.C017550
import PlattCertificates.Count131072.C017551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000235
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17520 : List PrefixCut := [⟨5,29979075,29979094⟩,
⟨76,446987024,446987294⟩,
⟨128,751781229,751781687⟩]
theorem checked17520 : checkPrefixCuts (2^48) 2300313601 9 Manual.Count131072.C017520.packed 128 cuts17520 = true := by
 decide +kernel
def pointBounds17520 : List (Nat × Nat × Nat) := [(2300318720,98300274553702,98300653888172),(2300391424,98300691561651,98301070896372)]
theorem point_links_checked17520 : (cuts17520.take 2).map (fun c => (2300313601-1+2*2^9*c.k,98300244574627+c.lower,98300623909078+c.upper)) = pointBounds17520 := by
 decide +kernel
def cuts17521 : List PrefixCut := [⟨19,112078297,112078365⟩,
⟨90,524899875,524900201⟩,
⟨128,738157342,738157800⟩]
theorem checked17521 : checkPrefixCuts (2^48) 2300444673 9 Manual.Count131072.C017521.packed 128 cuts17521 = true := by
 decide +kernel
def pointBounds17521 : List (Nat × Nat × Nat) := [(2300464128,98301108434153,98301487769130),(2300536832,98301521255731,98301900590966)]
theorem point_links_checked17521 : (cuts17521.take 2).map (fun c => (2300444673-1+2*2^9*c.k,98300996355856+c.lower,98301375690765+c.upper)) = pointBounds17521 := by
 decide +kernel
def cuts17522 : List PrefixCut := [⟨33,199550973,199551098⟩,
⟨104,603659844,603660226⟩,
⟨128,745088874,745089341⟩]
theorem checked17522 : checkPrefixCuts (2^48) 2300575745 9 Manual.Count131072.C017522.packed 128 cuts17522 = true := by
 decide +kernel
def pointBounds17522 : List (Nat × Nat × Nat) := [(2300609536,98301934064171,98302313399663),(2300682240,98302338173042,98302717508791)]
theorem point_links_checked17522 : (cuts17522.take 2).map (fun c => (2300575745-1+2*2^9*c.k,98301734513198+c.lower,98302113848565+c.upper)) = pointBounds17522 := by
 decide +kernel
def cuts17523 : List PrefixCut := [⟨47,268784276,268784441⟩,
⟨118,683144049,683144463⟩,
⟨128,739296312,739296762⟩]
theorem checked17523 : checkPrefixCuts (2^48) 2300706817 9 Manual.Count131072.C017523.packed 128 cuts17523 = true := by
 decide +kernel
def pointBounds17523 : List (Nat × Nat × Nat) := [(2300754944,98302748386348,98303127722347),(2300827648,98303162746121,98303542082369)]
theorem point_links_checked17523 : (cuts17523.take 2).map (fun c => (2300706817-1+2*2^9*c.k,98302479602072+c.lower,98302858937906+c.upper)) = pointBounds17523 := by
 decide +kernel
def cuts17524 : List PrefixCut := [⟨61,352322377,352322597⟩,
⟨128,741823203,741823663⟩]
theorem checked17524 : checkPrefixCuts (2^48) 2300837889 9 Manual.Count131072.C017524.packed 128 cuts17524 = true := by
 decide +kernel
def pointBounds17524 : List (Nat × Nat × Nat) := [(2300900352,98303571220761,98303950557265)]
theorem point_links_checked17524 : (cuts17524.take 1).map (fun c => (2300837889-1+2*2^9*c.k,98303218898384+c.lower,98303598234668+c.upper)) = pointBounds17524 := by
 decide +kernel
def cuts17525 : List PrefixCut := [⟨4,24710407,24710421⟩,
⟨75,438052307,438052581⟩,
⟨128,750955340,750955806⟩]
theorem checked17525 : checkPrefixCuts (2^48) 2300968961 9 Manual.Count131072.C017525.packed 128 cuts17525 = true := by
 decide +kernel
def pointBounds17525 : List (Nat × Nat × Nat) := [(2300973056,98303985431994,98304364768752),(2301045760,98304398773894,98304778110912)]
theorem point_links_checked17525 : (cuts17525.take 2).map (fun c => (2300968961-1+2*2^9*c.k,98303960721587+c.lower,98304340058331+c.upper)) = pointBounds17525 := by
 decide +kernel
def cuts17526 : List PrefixCut := [⟨18,103361570,103361633⟩,
⟨89,511907006,511907324⟩,
⟨128,725715325,725715780⟩]
theorem checked17526 : checkPrefixCuts (2^48) 2301100033 9 Manual.Count131072.C017526.packed 128 cuts17526 = true := by
 decide +kernel
def pointBounds17526 : List (Nat × Nat × Nat) := [(2301118464,98304815038497,98305194375770),(2301191168,98305223583933,98305602921461)]
theorem point_links_checked17526 : (cuts17526.take 2).map (fun c => (2301100033-1+2*2^9*c.k,98304711676927+c.lower,98305091014137+c.upper)) = pointBounds17526 := by
 decide +kernel
def cuts17527 : List PrefixCut := [⟨32,188730553,188730666⟩,
⟨103,599329323,599329695⟩,
⟨128,744509681,744510141⟩]
theorem checked17527 : checkPrefixCuts (2^48) 2301231105 9 Manual.Count131072.C017527.packed 128 cuts17527 = true := by
 decide +kernel
def pointBounds17527 : List (Nat × Nat × Nat) := [(2301263872,98305626122805,98306005460583),(2301336576,98306036721575,98306416059612)]
theorem point_links_checked17527 : (cuts17527.take 2).map (fun c => (2301231105-1+2*2^9*c.k,98305437392252+c.lower,98305816729917+c.upper)) = pointBounds17527 := by
 decide +kernel
def cuts17528 : List PrefixCut := [⟨46,263326311,263326475⟩,
⟨117,682093583,682094006⟩,
⟨128,744956444,744956904⟩]
theorem checked17528 : checkPrefixCuts (2^48) 2301362177 9 Manual.Count131072.C017528.packed 128 cuts17528 = true := by
 decide +kernel
def pointBounds17528 : List (Nat × Nat × Nat) := [(2301409280,98306445228244,98306824566533),(2301481984,98306863995516,98307243334064)]
theorem point_links_checked17528 : (cuts17528.take 2).map (fun c => (2301362177-1+2*2^9*c.k,98306181901933+c.lower,98306561240058+c.upper)) = pointBounds17528 := by
 decide +kernel
def cuts17529 : List PrefixCut := [⟨60,348797778,348797994⟩,
⟨128,743935795,743936259⟩]
theorem checked17529 : checkPrefixCuts (2^48) 2301493249 9 Manual.Count131072.C017529.packed 128 cuts17529 = true := by
 decide +kernel
def pointBounds17529 : List (Nat × Nat × Nat) := [(2301554688,98307275656155,98307654994956)]
theorem point_links_checked17529 : (cuts17529.take 1).map (fun c => (2301493249-1+2*2^9*c.k,98306926858377+c.lower,98307306196962+c.upper)) = pointBounds17529 := by
 decide +kernel
def cuts17530 : List PrefixCut := [⟨3,17854915,17854926⟩,
⟨74,439884333,439884601⟩,
⟨128,748051458,748051917⟩]
theorem checked17530 : checkPrefixCuts (2^48) 2301624321 9 Manual.Count131072.C017530.packed 128 cuts17530 = true := by
 decide +kernel
def pointBounds17530 : List (Nat × Nat × Nat) := [(2301627392,98307688649087,98308067988147),(2301700096,98308110678505,98308490017822)]
theorem point_links_checked17530 : (cuts17530.take 2).map (fun c => (2301624321-1+2*2^9*c.k,98307670794172+c.lower,98308050133221+c.upper)) = pointBounds17530 := by
 decide +kernel
def cuts17531 : List PrefixCut := [⟨17,98196127,98196190⟩,
⟨88,510293851,510294172⟩,
⟨128,740060211,740060675⟩]
theorem checked17531 : checkPrefixCuts (2^48) 2301755393 9 Manual.Count131072.C017531.packed 128 cuts17531 = true := by
 decide +kernel
def pointBounds17531 : List (Nat × Nat × Nat) := [(2301772800,98308517041757,98308896381328),(2301845504,98308929139481,98309308479310)]
theorem point_links_checked17531 : (cuts17531.take 2).map (fun c => (2301755393-1+2*2^9*c.k,98308418845630+c.lower,98308798185138+c.upper)) = pointBounds17531 := by
 decide +kernel
def cuts17532 : List PrefixCut := [⟨31,178894531,178894644⟩,
⟨102,589865741,589866116⟩,
⟨128,742585753,742586224⟩]
theorem checked17532 : checkPrefixCuts (2^48) 2301886465 9 Manual.Count131072.C017532.packed 128 cuts17532 = true := by
 decide +kernel
def pointBounds17532 : List (Nat × Nat × Nat) := [(2301918208,98309337800372,98309717140457),(2301990912,98309748771582,98310128111929)]
theorem point_links_checked17532 : (cuts17532.take 2).map (fun c => (2301886465-1+2*2^9*c.k,98309158905841+c.lower,98309538245813+c.upper)) = pointBounds17532 := by
 decide +kernel
def cuts17533 : List PrefixCut := [⟨45,262640060,262640229⟩,
⟨116,677864787,677865211⟩,
⟨128,746334018,746334486⟩]
theorem checked17533 : checkPrefixCuts (2^48) 2302017537 9 Manual.Count131072.C017533.packed 128 cuts17533 = true := by
 decide +kernel
def pointBounds17533 : List (Nat × Nat × Nat) := [(2302063616,98310164131654,98310543472266),(2302136320,98310579356381,98310958697248)]
theorem point_links_checked17533 : (cuts17533.take 2).map (fun c => (2302017537-1+2*2^9*c.k,98309901491594+c.lower,98310280832037+c.upper)) = pointBounds17533 := by
 decide +kernel
def cuts17534 : List PrefixCut := [⟨59,341607203,341607416⟩,
⟨128,733698372,733698828⟩]
theorem checked17534 : checkPrefixCuts (2^48) 2302148609 9 Manual.Count131072.C017534.packed 128 cuts17534 = true := by
 decide +kernel
def pointBounds17534 : List (Nat × Nat × Nat) := [(2302209024,98310989432815,98311368773939)]
theorem point_links_checked17534 : (cuts17534.take 1).map (fun c => (2302148609-1+2*2^9*c.k,98310647825612+c.lower,98311027166523+c.upper)) = pointBounds17534 := by
 decide +kernel
def cuts17535 : List PrefixCut := [⟨2,11736878,11736886⟩,
⟨73,423743577,423743845⟩,
⟨128,740136259,740136725⟩]
theorem checked17535 : checkPrefixCuts (2^48) 2302279681 9 Manual.Count131072.C017535.packed 128 cuts17535 = true := by
 decide +kernel
def pointBounds17535 : List (Nat × Nat × Nat) := [(2302281728,98311393260862,98311772602237),(2302354432,98311805267561,98312184609196)]
theorem point_links_checked17535 : (cuts17535.take 2).map (fun c => (2302279681-1+2*2^9*c.k,98311381523984+c.lower,98311760865351+c.upper)) = pointBounds17535 := by
 decide +kernel
def cuts17536 : List PrefixCut := [⟨16,91688859,91688916⟩,
⟨87,504280722,504281033⟩,
⟨128,737037863,737038325⟩]
theorem checked17536 : checkPrefixCuts (2^48) 2302410753 9 Manual.Count131072.C017536.packed 128 cuts17536 = true := by
 decide +kernel
def pointBounds17536 : List (Nat × Nat × Nat) := [(2302427136,98312213349102,98312592690992),(2302499840,98312625940965,98313005283109)]
theorem point_links_checked17536 : (cuts17536.take 2).map (fun c => (2302410753-1+2*2^9*c.k,98312121660243+c.lower,98312501002076+c.upper)) = pointBounds17536 := by
 decide +kernel
def cuts17537 : List PrefixCut := [⟨30,174931830,174931942⟩,
⟨101,593242995,593243367⟩,
⟨128,746286306,746286772⟩]
theorem checked17537 : checkPrefixCuts (2^48) 2302541825 9 Manual.Count131072.C017537.packed 128 cuts17537 = true := by
 decide +kernel
def pointBounds17537 : List (Nat × Nat × Nat) := [(2302572544,98313033629936,98313412972343),(2302645248,98313451941101,98313831283768)]
theorem point_links_checked17537 : (cuts17537.take 2).map (fun c => (2302541825-1+2*2^9*c.k,98312858698106+c.lower,98313238040401+c.upper)) = pointBounds17537 := by
 decide +kernel
def cuts17538 : List PrefixCut := [⟨44,255964536,255964695⟩,
⟨115,669115525,669115938⟩,
⟨128,746365975,746366434⟩]
theorem checked17538 : checkPrefixCuts (2^48) 2302672897 9 Manual.Count131072.C017538.packed 128 cuts17538 = true := by
 decide +kernel
def pointBounds17538 : List (Nat × Nat × Nat) := [(2302717952,98313860948948,98314240291868),(2302790656,98314274099937,98314653443111)]
theorem point_links_checked17538 : (cuts17538.take 2).map (fun c => (2302672897-1+2*2^9*c.k,98313604984412+c.lower,98313984327173+c.upper)) = pointBounds17538 := by
 decide +kernel
def cuts17539 : List PrefixCut := [⟨58,335276343,335276550⟩,
⟨128,742412198,742412654⟩]
theorem checked17539 : checkPrefixCuts (2^48) 2302803969 9 Manual.Count131072.C017539.packed 128 cuts17539 = true := by
 decide +kernel
def pointBounds17539 : List (Nat × Nat × Nat) := [(2302863360,98314686626730,98315065970157)]
theorem point_links_checked17539 : (cuts17539.take 1).map (fun c => (2302803969-1+2*2^9*c.k,98314351350387+c.lower,98314730693607+c.upper)) = pointBounds17539 := by
 decide +kernel
def cuts17540 : List PrefixCut := [⟨1,6233444,6233448⟩,
⟨72,412134155,412134404⟩,
⟨128,741514300,741514748⟩]
theorem checked17540 : checkPrefixCuts (2^48) 2302935041 9 Manual.Count131072.C017540.packed 128 cuts17540 = true := by
 decide +kernel
def pointBounds17540 : List (Nat × Nat × Nat) := [(2302936064,98315099996029,98315479339709),(2303008768,98315505896740,98315885240665)]
theorem point_links_checked17540 : (cuts17540.take 2).map (fun c => (2302935041-1+2*2^9*c.k,98315093762585+c.lower,98315473106261+c.upper)) = pointBounds17540 := by
 decide +kernel
def cuts17541 : List PrefixCut := [⟨15,91662787,91662841⟩,
⟨86,503037515,503037819⟩,
⟨128,744161118,744161569⟩]
theorem checked17541 : checkPrefixCuts (2^48) 2303066113 9 Manual.Count131072.C017541.packed 128 cuts17541 = true := by
 decide +kernel
def pointBounds17541 : List (Nat × Nat × Nat) := [(2303081472,98315926939672,98316306283850),(2303154176,98316338314400,98316717658828)]
theorem point_links_checked17541 : (cuts17541.take 2).map (fun c => (2303066113-1+2*2^9*c.k,98315835276885+c.lower,98316214621009+c.upper)) = pointBounds17541 := by
 decide +kernel
def cuts17542 : List PrefixCut := [⟨29,166082998,166083106⟩,
⟨100,578042857,578043215⟩,
⟨128,741430016,741430473⟩]
theorem checked17542 : checkPrefixCuts (2^48) 2303197185 9 Manual.Count131072.C017542.packed 128 cuts17542 = true := by
 decide +kernel
def pointBounds17542 : List (Nat × Nat × Nat) := [(2303226880,98316745521001,98317124865684),(2303299584,98317157480860,98317536825793)]
theorem point_links_checked17542 : (cuts17542.take 2).map (fun c => (2303197185-1+2*2^9*c.k,98316579438003+c.lower,98316958782578+c.upper)) = pointBounds17542 := by
 decide +kernel
def cuts17543 : List PrefixCut := [⟨43,251614704,251614859⟩,
⟨114,662326462,662326878⟩,
⟨128,741754495,741754962⟩]
theorem checked17543 : checkPrefixCuts (2^48) 2303328257 9 Manual.Count131072.C017543.packed 128 cuts17543 = true := by
 decide +kernel
def pointBounds17543 : List (Nat × Nat × Nat) := [(2303372288,98317572482723,98317951827910),(2303444992,98317983194481,98318362539929)]
theorem point_links_checked17543 : (cuts17543.take 2).map (fun c => (2303328257-1+2*2^9*c.k,98317320868019+c.lower,98317700213051+c.upper)) = pointBounds17543 := by
 decide +kernel
def cuts17544 : List PrefixCut := [⟨57,330293280,330293484⟩,
⟨128,743667383,743667845⟩]
theorem checked17544 : checkPrefixCuts (2^48) 2303459329 9 Manual.Count131072.C017544.packed 128 cuts17544 = true := by
 decide +kernel
def pointBounds17544 : List (Nat × Nat × Nat) := [(2303517696,98318392915794,98318772261497),(2303590400,98318806289897,98319185635858)]
theorem point_links_checked17544 : (cuts17544.take 2).map (fun c => (2303459329-1+2*2^9*c.k,98318062622514+c.lower,98318441968013+c.upper)) = pointBounds17544 := by
 decide +kernel
def cuts17545 : List PrefixCut := [⟨71,413116678,413116928⟩,
⟨128,748512372,748512825⟩]
theorem checked17545 : checkPrefixCuts (2^48) 2303590401 9 Manual.Count131072.C017545.packed 128 cuts17545 = true := by
 decide +kernel
def pointBounds17545 : List (Nat × Nat × Nat) := [(2303663104,98319219406575,98319598752786)]
theorem point_links_checked17545 : (cuts17545.take 1).map (fun c => (2303590401-1+2*2^9*c.k,98318806289897+c.lower,98319185635858+c.upper)) = pointBounds17545 := by
 decide +kernel
def cuts17546 : List PrefixCut := [⟨14,83328340,83328390⟩,
⟨85,491898321,491898623⟩,
⟨128,743704924,743705378⟩]
theorem checked17546 : checkPrefixCuts (2^48) 2303721473 9 Manual.Count131072.C017546.packed 128 cuts17546 = true := by
 decide +kernel
def pointBounds17546 : List (Nat × Nat × Nat) := [(2303735808,98319638130609,98320017477073),(2303808512,98320046700590,98320426047306)]
theorem point_links_checked17546 : (cuts17546.take 2).map (fun c => (2303721473-1+2*2^9*c.k,98319554802269+c.lower,98319934148683+c.upper)) = pointBounds17546 := by
 decide +kernel
def cuts17547 : List PrefixCut := [⟨28,164447507,164447609⟩,
⟨99,573969039,573969394⟩,
⟨128,742563022,742563480⟩]
theorem checked17547 : checkPrefixCuts (2^48) 2303852545 9 Manual.Count131072.C017547.packed 128 cuts17547 = true := by
 decide +kernel
def pointBounds17547 : List (Nat × Nat × Nat) := [(2303881216,98320462954700,98320842301670),(2303953920,98320872476232,98321251823455)]
theorem point_links_checked17547 : (cuts17547.take 2).map (fun c => (2303852545-1+2*2^9*c.k,98320298507193+c.lower,98320677854061+c.upper)) = pointBounds17547 := by
 decide +kernel
def cuts17548 : List PrefixCut := [⟨42,240303774,240303922⟩,
⟨113,646501108,646501507⟩,
⟨128,730793055,730793506⟩]
theorem checked17548 : checkPrefixCuts (2^48) 2303983617 9 Manual.Count131072.C017548.packed 128 cuts17548 = true := by
 decide +kernel
def pointBounds17548 : List (Nat × Nat × Nat) := [(2304026624,98321281373989,98321660721463),(2304099328,98321687571323,98322066919048)]
theorem point_links_checked17548 : (cuts17548.take 2).map (fun c => (2303983617-1+2*2^9*c.k,98321041070215+c.lower,98321420417541+c.upper)) = pointBounds17548 := by
 decide +kernel
def cuts17549 : List PrefixCut := [⟨56,328000488,328000680⟩,
⟨127,746143433,746143886⟩,
⟨128,752251179,752251636⟩]
theorem checked17549 : checkPrefixCuts (2^48) 2304114689 9 Manual.Count131072.C017549.packed 128 cuts17549 = true := by
 decide +kernel
def pointBounds17549 : List (Nat × Nat × Nat) := [(2304172032,98322099863758,98322479211727),(2304244736,98322518006703,98322897354933)]
theorem point_links_checked17549 : (cuts17549.take 2).map (fun c => (2304114689-1+2*2^9*c.k,98321771863270+c.lower,98322151211047+c.upper)) = pointBounds17549 := by
 decide +kernel
def cuts17550 : List PrefixCut := [⟨70,407135952,407136192⟩,
⟨128,748299591,748300041⟩]
theorem checked17550 : checkPrefixCuts (2^48) 2304245761 9 Manual.Count131072.C017550.packed 128 cuts17550 = true := by
 decide +kernel
def pointBounds17550 : List (Nat × Nat × Nat) := [(2304317440,98322931250401,98323310598875)]
theorem point_links_checked17550 : (cuts17550.take 1).map (fun c => (2304245761-1+2*2^9*c.k,98322524114449+c.lower,98322903462683+c.upper)) = pointBounds17550 := by
 decide +kernel
def cuts17551 : List PrefixCut := [⟨13,74387887,74387932⟩,
⟨84,482719652,482719944⟩,
⟨128,736408946,736409396⟩]
theorem checked17551 : checkPrefixCuts (2^48) 2304376833 9 Manual.Count131072.C017551.packed 128 cuts17551 = true := by
 decide +kernel
def pointBounds17551 : List (Nat × Nat × Nat) := [(2304390144,98323346801927,98323726150656),(2304462848,98323755133692,98324134482668)]
theorem point_links_checked17551 : (cuts17551.take 2).map (fun c => (2304376833-1+2*2^9*c.k,98323272414040+c.lower,98323651762724+c.upper)) = pointBounds17551 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000235
