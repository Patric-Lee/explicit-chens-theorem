import PlattAssemblyKernel
import PlattCertificates.Count131072.C025600
import PlattCertificates.Count131072.C025601
import PlattCertificates.Count131072.C025602
import PlattCertificates.Count131072.C025603
import PlattCertificates.Count131072.C025604
import PlattCertificates.Count131072.C025605
import PlattCertificates.Count131072.C025606
import PlattCertificates.Count131072.C025607
import PlattCertificates.Count131072.C025608
import PlattCertificates.Count131072.C025609
import PlattCertificates.Count131072.C025610
import PlattCertificates.Count131072.C025611
import PlattCertificates.Count131072.C025612
import PlattCertificates.Count131072.C025613
import PlattCertificates.Count131072.C025614
import PlattCertificates.Count131072.C025615
import PlattCertificates.Count131072.C025616
import PlattCertificates.Count131072.C025617
import PlattCertificates.Count131072.C025618
import PlattCertificates.Count131072.C025619
import PlattCertificates.Count131072.C025620
import PlattCertificates.Count131072.C025621
import PlattCertificates.Count131072.C025622
import PlattCertificates.Count131072.C025623
import PlattCertificates.Count131072.C025624
import PlattCertificates.Count131072.C025625
import PlattCertificates.Count131072.C025626
import PlattCertificates.Count131072.C025627
import PlattCertificates.Count131072.C025628
import PlattCertificates.Count131072.C025629
import PlattCertificates.Count131072.C025630
import PlattCertificates.Count131072.C025631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25600 : List PrefixCut := [⟨51,200251442,200251557⟩,
⟨128,504309333,504309614⟩]
theorem checked25600 : checkPrefixCuts (2^48) 3359375361 9 Manual.Count131072.C025600.packed 128 cuts25600 = true := by
 decide +kernel
def pointBounds25600 : List (Nat × Nat × Nat) := [(3359427584,103202305387200,103202687574227)]
theorem point_links_checked25600 : (cuts25600.take 1).map (fun c => (3359375361-1+2*2^9*c.k,103202105135758+c.lower,103202487322670+c.upper)) = pointBounds25600 := by
 decide +kernel
def cuts25601 : List PrefixCut := [⟨26,103054654,103054711⟩,
⟨128,495827640,495827917⟩]
theorem checked25601 : checkPrefixCuts (2^48) 3359506433 9 Manual.Count131072.C025601.packed 128 cuts25601 = true := by
 decide +kernel
def pointBounds25601 : List (Nat × Nat × Nat) := [(3359533056,103202712499745,103203094686995)]
theorem point_links_checked25601 : (cuts25601.take 1).map (fun c => (3359506433-1+2*2^9*c.k,103202609445091+c.lower,103202991632284+c.upper)) = pointBounds25601 := by
 decide +kernel
def cuts25602 : List PrefixCut := [⟨1,3099909,3099911⟩,
⟨104,404154754,404154980⟩,
⟨128,498572970,498573251⟩]
theorem checked25602 : checkPrefixCuts (2^48) 3359637505 9 Manual.Count131072.C025602.packed 128 cuts25602 = true := by
 decide +kernel
def pointBounds25602 : List (Nat × Nat × Nat) := [(3359638528,103203108372640,103203490560112),(3359744000,103203509427485,103203891615181)]
theorem point_links_checked25602 : (cuts25602.take 2).map (fun c => (3359637505-1+2*2^9*c.k,103203105272731+c.lower,103203487460201+c.upper)) = pointBounds25602 := by
 decide +kernel
def cuts25603 : List PrefixCut := [⟨79,314750392,314750569⟩,
⟨128,507936512,507936796⟩]
theorem checked25603 : checkPrefixCuts (2^48) 3359768577 9 Manual.Count131072.C025603.packed 128 cuts25603 = true := by
 decide +kernel
def pointBounds25603 : List (Nat × Nat × Nat) := [(3359849472,103203918596093,103204300784021)]
theorem point_links_checked25603 : (cuts25603.take 1).map (fun c => (3359768577-1+2*2^9*c.k,103203603845701+c.lower,103203986033452+c.upper)) = pointBounds25603 := by
 decide +kernel
def cuts25604 : List PrefixCut := [⟨54,208681271,208681387⟩,
⟨128,496691057,496691335⟩]
theorem checked25604 : checkPrefixCuts (2^48) 3359899649 9 Manual.Count131072.C025604.packed 128 cuts25604 = true := by
 decide +kernel
def pointBounds25604 : List (Nat × Nat × Nat) := [(3359954944,103204320463484,103204702651635)]
theorem point_links_checked25604 : (cuts25604.take 1).map (fun c => (3359899649-1+2*2^9*c.k,103204111782213+c.lower,103204493970248+c.upper)) = pointBounds25604 := by
 decide +kernel
def cuts25605 : List PrefixCut := [⟨29,114180084,114180145⟩,
⟨128,502870613,502870896⟩]
theorem checked25605 : checkPrefixCuts (2^48) 3360030721 9 Manual.Count131072.C025605.packed 128 cuts25605 = true := by
 decide +kernel
def pointBounds25605 : List (Nat × Nat × Nat) := [(3360060416,103204722653354,103205104841728)]
theorem point_links_checked25605 : (cuts25605.take 1).map (fun c => (3360030721-1+2*2^9*c.k,103204608473270+c.lower,103204990661583+c.upper)) = pointBounds25605 := by
 decide +kernel
def cuts25606 : List PrefixCut := [⟨4,16334801,16334810⟩,
⟨107,418248047,418248277⟩,
⟨128,501594476,501594750⟩]
theorem checked25606 : checkPrefixCuts (2^48) 3360161793 9 Manual.Count131072.C025606.packed 128 cuts25606 = true := by
 decide +kernel
def pointBounds25606 : List (Nat × Nat × Nat) := [(3360165888,103205127678684,103205509867289),(3360271360,103205529591930,103205911780756)]
theorem point_links_checked25606 : (cuts25606.take 2).map (fun c => (3360161793-1+2*2^9*c.k,103205111343883+c.lower,103205493532479+c.upper)) = pointBounds25606 := by
 decide +kernel
def cuts25607 : List PrefixCut := [⟨82,320983461,320983641⟩,
⟨128,503417762,503418045⟩]
theorem checked25607 : checkPrefixCuts (2^48) 3360292865 9 Manual.Count131072.C025607.packed 128 cuts25607 = true := by
 decide +kernel
def pointBounds25607 : List (Nat × Nat × Nat) := [(3360376832,103205933921820,103206316110870)]
theorem point_links_checked25607 : (cuts25607.take 1).map (fun c => (3360292865-1+2*2^9*c.k,103205612938359+c.lower,103205995127229+c.upper)) = pointBounds25607 := by
 decide +kernel
def cuts25608 : List PrefixCut := [⟨57,221799105,221799228⟩,
⟨128,496362276,496362560⟩]
theorem checked25608 : checkPrefixCuts (2^48) 3360423937 9 Manual.Count131072.C025608.packed 128 cuts25608 = true := by
 decide +kernel
def pointBounds25608 : List (Nat × Nat × Nat) := [(3360482304,103206338155226,103206720344502)]
theorem point_links_checked25608 : (cuts25608.take 1).map (fun c => (3360423937-1+2*2^9*c.k,103206116356121+c.lower,103206498545274+c.upper)) = pointBounds25608 := by
 decide +kernel
def cuts25609 : List PrefixCut := [⟨32,127228472,127228540⟩,
⟨128,509157715,509157996⟩]
theorem checked25609 : checkPrefixCuts (2^48) 3360555009 9 Manual.Count131072.C025609.packed 128 cuts25609 = true := by
 decide +kernel
def pointBounds25609 : List (Nat × Nat × Nat) := [(3360587776,103206739946869,103207122136374)]
theorem point_links_checked25609 : (cuts25609.take 1).map (fun c => (3360555009-1+2*2^9*c.k,103206612718397+c.lower,103206994907834+c.upper)) = pointBounds25609 := by
 decide +kernel
def cuts25610 : List PrefixCut := [⟨7,27471673,27471688⟩,
⟨110,425552966,425553204⟩,
⟨128,494564738,494565013⟩]
theorem checked25610 : checkPrefixCuts (2^48) 3360686081 9 Manual.Count131072.C025610.packed 128 cuts25610 = true := by
 decide +kernel
def pointBounds25610 : List (Nat × Nat × Nat) := [(3360693248,103207149347785,103207531537518),(3360798720,103207547429078,103207929619034)]
theorem point_links_checked25610 : (cuts25610.take 2).map (fun c => (3360686081-1+2*2^9*c.k,103207121876112+c.lower,103207504065830+c.upper)) = pointBounds25610 := by
 decide +kernel
def cuts25611 : List PrefixCut := [⟨85,332574580,332574763⟩,
⟨128,498984257,498984531⟩]
theorem checked25611 : checkPrefixCuts (2^48) 3360817153 9 Manual.Count131072.C025611.packed 128 cuts25611 = true := by
 decide +kernel
def pointBounds25611 : List (Nat × Nat × Nat) := [(3360904192,103207949015430,103208331205606)]
theorem point_links_checked25611 : (cuts25611.take 1).map (fun c => (3360817153-1+2*2^9*c.k,103207616440850+c.lower,103207998630843+c.upper)) = pointBounds25611 := by
 decide +kernel
def cuts25612 : List PrefixCut := [⟨60,238430216,238430346⟩,
⟨128,504659555,504659836⟩]
theorem checked25612 : checkPrefixCuts (2^48) 3360948225 9 Manual.Count131072.C025612.packed 128 cuts25612 = true := by
 decide +kernel
def pointBounds25612 : List (Nat × Nat × Nat) := [(3361009664,103208353855323,103208736045720)]
theorem point_links_checked25612 : (cuts25612.take 1).map (fun c => (3360948225-1+2*2^9*c.k,103208115425107+c.lower,103208497615374+c.upper)) = pointBounds25612 := by
 decide +kernel
def cuts25613 : List PrefixCut := [⟨35,138011673,138011749⟩,
⟨128,510585695,510585977⟩]
theorem checked25613 : checkPrefixCuts (2^48) 3361079297 9 Manual.Count131072.C025613.packed 128 cuts25613 = true := by
 decide +kernel
def pointBounds25613 : List (Nat × Nat × Nat) := [(3361115136,103208758096335,103209140286959)]
theorem point_links_checked25613 : (cuts25613.take 1).map (fun c => (3361079297-1+2*2^9*c.k,103208620084662+c.lower,103209002275210+c.upper)) = pointBounds25613 := by
 decide +kernel
def cuts25614 : List PrefixCut := [⟨10,41536033,41536056⟩,
⟨113,441397186,441397440⟩,
⟨128,498590956,498591243⟩]
theorem checked25614 : checkPrefixCuts (2^48) 3361210369 9 Manual.Count131072.C025614.packed 128 cuts25614 = true := by
 decide +kernel
def pointBounds25614 : List (Nat × Nat × Nat) := [(3361220608,103209172206390,103209554397243),(3361326080,103209572067543,103209954258627)]
theorem point_links_checked25614 : (cuts25614.take 2).map (fun c => (3361210369-1+2*2^9*c.k,103209130670357+c.lower,103209512861187+c.upper)) = pointBounds25614 := by
 decide +kernel
def cuts25615 : List PrefixCut := [⟨88,344078376,344078568⟩,
⟨128,500581164,500581442⟩]
theorem checked25615 : checkPrefixCuts (2^48) 3361341441 9 Manual.Count131072.C025615.packed 128 cuts25615 = true := by
 decide +kernel
def pointBounds25615 : List (Nat × Nat × Nat) := [(3361431552,103209973339689,103210355530998)]
theorem point_links_checked25615 : (cuts25615.take 1).map (fun c => (3361341441-1+2*2^9*c.k,103209629261313+c.lower,103210011452430+c.upper)) = pointBounds25615 := by
 decide +kernel
def cuts25616 : List PrefixCut := [⟨63,247268824,247268965⟩,
⟨128,497798414,497798696⟩]
theorem checked25616 : checkPrefixCuts (2^48) 3361472513 9 Manual.Count131072.C025616.packed 128 cuts25616 = true := by
 decide +kernel
def pointBounds25616 : List (Nat × Nat × Nat) := [(3361537024,103210377111301,103210759302837)]
theorem point_links_checked25616 : (cuts25616.take 1).map (fun c => (3361472513-1+2*2^9*c.k,103210129842477+c.lower,103210512033872+c.upper)) = pointBounds25616 := by
 decide +kernel
def cuts25617 : List PrefixCut := [⟨38,149712549,149712630⟩,
⟨128,498281407,498281682⟩]
theorem checked25617 : checkPrefixCuts (2^48) 3361603585 9 Manual.Count131072.C025617.packed 128 cuts25617 = true := by
 decide +kernel
def pointBounds25617 : List (Nat × Nat × Nat) := [(3361642496,103210777353440,103211159545198)]
theorem point_links_checked25617 : (cuts25617.take 1).map (fun c => (3361603585-1+2*2^9*c.k,103210627640891+c.lower,103211009832568+c.upper)) = pointBounds25617 := by
 decide +kernel
def cuts25618 : List PrefixCut := [⟨13,51493275,51493303⟩,
⟨116,449449698,449449951⟩,
⟨128,495666423,495666701⟩]
theorem checked25618 : checkPrefixCuts (2^48) 3361734657 9 Manual.Count131072.C025618.packed 128 cuts25618 = true := by
 decide +kernel
def pointBounds25618 : List (Nat × Nat × Nat) := [(3361747968,103211177415573,103211559607553),(3361853440,103211575371996,103211957564201)]
theorem point_links_checked25618 : (cuts25618.take 2).map (fun c => (3361734657-1+2*2^9*c.k,103211125922298+c.lower,103211508114250+c.upper)) = pointBounds25618 := by
 decide +kernel
def cuts25619 : List PrefixCut := [⟨91,353317970,353318172⟩,
⟨128,504437984,504438270⟩]
theorem checked25619 : checkPrefixCuts (2^48) 3361865729 9 Manual.Count131072.C025619.packed 128 cuts25619 = true := by
 decide +kernel
def pointBounds25619 : List (Nat × Nat × Nat) := [(3361958912,103211974906691,103212357099123)]
theorem point_links_checked25619 : (cuts25619.take 1).map (fun c => (3361865729-1+2*2^9*c.k,103211621588721+c.lower,103212003780951+c.upper)) = pointBounds25619 := by
 decide +kernel
def cuts25620 : List PrefixCut := [⟨66,261127943,261128085⟩,
⟨128,503497518,503497796⟩]
theorem checked25620 : checkPrefixCuts (2^48) 3361996801 9 Manual.Count131072.C025620.packed 128 cuts25620 = true := by
 decide +kernel
def pointBounds25620 : List (Nat × Nat × Nat) := [(3362064384,103212387154648,103212769347306)]
theorem point_links_checked25620 : (cuts25620.take 1).map (fun c => (3361996801-1+2*2^9*c.k,103212126026705+c.lower,103212508219221+c.upper)) = pointBounds25620 := by
 decide +kernel
def cuts25621 : List PrefixCut := [⟨41,161326041,161326128⟩,
⟨128,505570839,505571126⟩]
theorem checked25621 : checkPrefixCuts (2^48) 3362127873 9 Manual.Count131072.C025621.packed 128 cuts25621 = true := by
 decide +kernel
def pointBounds25621 : List (Nat × Nat × Nat) := [(3362169856,103212790850264,103213173043145)]
theorem point_links_checked25621 : (cuts25621.take 1).map (fun c => (3362127873-1+2*2^9*c.k,103212629524223+c.lower,103213011717017+c.upper)) = pointBounds25621 := by
 decide +kernel
def cuts25622 : List PrefixCut := [⟨16,63540297,63540333⟩,
⟨119,471563653,471563918⟩,
⟨128,506471915,506472199⟩]
theorem checked25622 : checkPrefixCuts (2^48) 3362258945 9 Manual.Count131072.C025622.packed 128 cuts25622 = true := by
 decide +kernel
def pointBounds25622 : List (Nat × Nat × Nat) := [(3362275328,103213198635359,103213580828476),(3362380800,103213606658715,103213988852061)]
theorem point_links_checked25622 : (cuts25622.take 2).map (fun c => (3362258945-1+2*2^9*c.k,103213135095062+c.lower,103213517288143+c.upper)) = pointBounds25622 := by
 decide +kernel
def cuts25623 : List PrefixCut := [⟨94,371428117,371428324⟩,
⟨128,500006551,500006834⟩]
theorem checked25623 : checkPrefixCuts (2^48) 3362390017 9 Manual.Count131072.C025623.packed 128 cuts25623 = true := by
 decide +kernel
def pointBounds25623 : List (Nat × Nat × Nat) := [(3362486272,103214012995094,103214395188666)]
theorem point_links_checked25623 : (cuts25623.take 1).map (fun c => (3362390017-1+2*2^9*c.k,103213641566977+c.lower,103214023760342+c.upper)) = pointBounds25623 := by
 decide +kernel
def cuts25624 : List PrefixCut := [⟨69,265021436,265021585⟩,
⟨128,499233522,499233802⟩]
theorem checked25624 : checkPrefixCuts (2^48) 3362521089 9 Manual.Count131072.C025624.packed 128 cuts25624 = true := by
 decide +kernel
def pointBounds25624 : List (Nat × Nat × Nat) := [(3362591744,103214406594964,103214788788761)]
theorem point_links_checked25624 : (cuts25624.take 1).map (fun c => (3362521089-1+2*2^9*c.k,103214141573528+c.lower,103214523767176+c.upper)) = pointBounds25624 := by
 decide +kernel
def cuts25625 : List PrefixCut := [⟨44,170843255,170843352⟩,
⟨128,496200816,496201102⟩]
theorem checked25625 : checkPrefixCuts (2^48) 3362652161 9 Manual.Count131072.C025625.packed 128 cuts25625 = true := by
 decide +kernel
def pointBounds25625 : List (Nat × Nat × Nat) := [(3362697216,103214811650305,103215193844330)]
theorem point_links_checked25625 : (cuts25625.take 1).map (fun c => (3362652161-1+2*2^9*c.k,103214640807050+c.lower,103215023000978+c.upper)) = pointBounds25625 := by
 decide +kernel
def cuts25626 : List PrefixCut := [⟨19,74662823,74662867⟩,
⟨122,482789615,482789894⟩,
⟨128,507564749,507565041⟩]
theorem checked25626 : checkPrefixCuts (2^48) 3362783233 9 Manual.Count131072.C025626.packed 128 cuts25626 = true := by
 decide +kernel
def pointBounds25626 : List (Nat × Nat × Nat) := [(3362802688,103215211670689,103215593864947),(3362908160,103215619797481,103216001991974)]
theorem point_links_checked25626 : (cuts25626.take 2).map (fun c => (3362783233-1+2*2^9*c.k,103215137007866+c.lower,103215519202080+c.upper)) = pointBounds25626 := by
 decide +kernel
def cuts25627 : List PrefixCut := [⟨97,375889818,375890030⟩,
⟨128,496999131,496999411⟩]
theorem checked25627 : checkPrefixCuts (2^48) 3362914305 9 Manual.Count131072.C025627.packed 128 cuts25627 = true := by
 decide +kernel
def pointBounds25627 : List (Nat × Nat × Nat) := [(3363013632,103216020462433,103216402657151)]
theorem point_links_checked25627 : (cuts25627.take 1).map (fun c => (3362914305-1+2*2^9*c.k,103215644572615+c.lower,103216026767121+c.upper)) = pointBounds25627 := by
 decide +kernel
def cuts25628 : List PrefixCut := [⟨72,283978887,283979044⟩,
⟨128,503173160,503173442⟩]
theorem checked25628 : checkPrefixCuts (2^48) 3363045377 9 Manual.Count131072.C025628.packed 128 cuts25628 = true := by
 decide +kernel
def pointBounds25628 : List (Nat × Nat × Nat) := [(3363119104,103216425550633,103216807745576)]
theorem point_links_checked25628 : (cuts25628.take 1).map (fun c => (3363045377-1+2*2^9*c.k,103216141571746+c.lower,103216523766532+c.upper)) = pointBounds25628 := by
 decide +kernel
def cuts25629 : List PrefixCut := [⟨47,186132289,186132392⟩,
⟨128,506501223,506501503⟩]
theorem checked25629 : checkPrefixCuts (2^48) 3363176449 9 Manual.Count131072.C025629.packed 128 cuts25629 = true := by
 decide +kernel
def pointBounds25629 : List (Nat × Nat × Nat) := [(3363224576,103216830877195,103217213072366)]
theorem point_links_checked25629 : (cuts25629.take 1).map (fun c => (3363176449-1+2*2^9*c.k,103216644744906+c.lower,103217026939974+c.upper)) = pointBounds25629 := by
 decide +kernel
def cuts25630 : List PrefixCut := [⟨22,85363422,85363470⟩,
⟨125,493175232,493175509⟩,
⟨128,504138188,504138471⟩]
theorem checked25630 : checkPrefixCuts (2^48) 3363307521 9 Manual.Count131072.C025630.packed 128 cuts25630 = true := by
 decide +kernel
def pointBounds25630 : List (Nat × Nat × Nat) := [(3363330048,103217236609551,103217618804947),(3363435520,103217644421361,103218026616986)]
theorem point_links_checked25630 : (cuts25630.take 2).map (fun c => (3363307521-1+2*2^9*c.k,103217151246129+c.lower,103217533441477+c.upper)) = pointBounds25630 := by
 decide +kernel
def cuts25631 : List PrefixCut := [⟨100,389973814,389974032⟩,
⟨128,497758480,497758756⟩]
theorem checked25631 : checkPrefixCuts (2^48) 3363438593 9 Manual.Count131072.C025631.packed 128 cuts25631 = true := by
 decide +kernel
def pointBounds25631 : List (Nat × Nat × Nat) := [(3363540992,103218045358131,103218427553980)]
theorem point_links_checked25631 : (cuts25631.take 1).map (fun c => (3363438593-1+2*2^9*c.k,103217655384317+c.lower,103218037579948+c.upper)) = pointBounds25631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000175
