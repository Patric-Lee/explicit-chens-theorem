import PlattAssemblyKernel
import PlattCertificates.Count131072.C016624
import PlattCertificates.Count131072.C016625
import PlattCertificates.Count131072.C016626
import PlattCertificates.Count131072.C016627
import PlattCertificates.Count131072.C016628
import PlattCertificates.Count131072.C016629
import PlattCertificates.Count131072.C016630
import PlattCertificates.Count131072.C016631
import PlattCertificates.Count131072.C016632
import PlattCertificates.Count131072.C016633
import PlattCertificates.Count131072.C016634
import PlattCertificates.Count131072.C016635
import PlattCertificates.Count131072.C016636
import PlattCertificates.Count131072.C016637
import PlattCertificates.Count131072.C016638
import PlattCertificates.Count131072.C016639
import PlattCertificates.Count131072.C016640
import PlattCertificates.Count131072.C016641
import PlattCertificates.Count131072.C016642
import PlattCertificates.Count131072.C016643
import PlattCertificates.Count131072.C016644
import PlattCertificates.Count131072.C016645
import PlattCertificates.Count131072.C016646
import PlattCertificates.Count131072.C016647
import PlattCertificates.Count131072.C016648
import PlattCertificates.Count131072.C016649
import PlattCertificates.Count131072.C016650
import PlattCertificates.Count131072.C016651
import PlattCertificates.Count131072.C016652
import PlattCertificates.Count131072.C016653
import PlattCertificates.Count131072.C016654
import PlattCertificates.Count131072.C016655
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000207
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16624 : List PrefixCut := [⟨12,72467994,72468039⟩,
⟨79,483671130,483671435⟩,
⟨128,780879476,780879972⟩]
theorem checked16624 : checkPrefixCuts (2^48) 2182873089 9 Manual.Count131072.C016624.packed 128 cuts16624 = true := by
 decide +kernel
def pointBounds16624 : List (Nat × Nat × Nat) := [(2182885376,97615084253178,97615463159936),(2182953984,97615495456314,97615874363332)]
theorem point_links_checked16624 : (cuts16624.take 2).map (fun c => (2182873089-1+2*2^9*c.k,97615011785184+c.lower,97615390691897+c.upper)) = pointBounds16624 := by
 decide +kernel
def cuts16625 : List PrefixCut := [⟨18,110758346,110758416⟩,
⟨85,529027090,529027426⟩,
⟨128,797594082,797594585⟩]
theorem checked16625 : checkPrefixCuts (2^48) 2183004161 9 Manual.Count131072.C016625.packed 128 cuts16625 = true := by
 decide +kernel
def pointBounds16625 : List (Nat × Nat × Nat) := [(2183022592,97615903423006,97616282330285),(2183091200,97616321691750,97616700599295)]
theorem point_links_checked16625 : (cuts16625.take 2).map (fun c => (2183004161-1+2*2^9*c.k,97615792664660+c.lower,97616171571869+c.upper)) = pointBounds16625 := by
 decide +kernel
def cuts16626 : List PrefixCut := [⟨24,149301828,149301923⟩,
⟨91,555038358,555038708⟩,
⟨128,784782464,784782959⟩]
theorem checked16626 : checkPrefixCuts (2^48) 2183135233 9 Manual.Count131072.C016626.packed 128 cuts16626 = true := by
 decide +kernel
def pointBounds16626 : List (Nat × Nat × Nat) := [(2183159808,97616739560570,97617118468377),(2183228416,97617145297100,97617524205162)]
theorem point_links_checked16626 : (cuts16626.take 2).map (fun c => (2183135233-1+2*2^9*c.k,97616590258742+c.lower,97616969166454+c.upper)) = pointBounds16626 := by
 decide +kernel
def cuts16627 : List PrefixCut := [⟨30,186680269,186680384⟩,
⟨97,589941741,589942108⟩,
⟨128,782414727,782415213⟩]
theorem checked16627 : checkPrefixCuts (2^48) 2183266305 9 Manual.Count131072.C016627.packed 128 cuts16627 = true := by
 decide +kernel
def pointBounds16627 : List (Nat × Nat × Nat) := [(2183297024,97617561721475,97617940629797),(2183365632,97617964982947,97618343891521)]
theorem point_links_checked16627 : (cuts16627.take 2).map (fun c => (2183266305-1+2*2^9*c.k,97617375041206+c.lower,97617753949413+c.upper)) = pointBounds16627 := by
 decide +kernel
def cuts16628 : List PrefixCut := [⟨36,218381879,218382016⟩,
⟨103,625743169,625743560⟩,
⟨128,781207452,781207941⟩]
theorem checked16628 : checkPrefixCuts (2^48) 2183397377 9 Manual.Count131072.C016628.packed 128 cuts16628 = true := by
 decide +kernel
def pointBounds16628 : List (Nat × Nat × Nat) := [(2183434240,97618375837812,97618754746642),(2183502848,97618783199102,97619162108186)]
theorem point_links_checked16628 : (cuts16628.take 2).map (fun c => (2183397377-1+2*2^9*c.k,97618157455933+c.lower,97618536364626+c.upper)) = pointBounds16628 := by
 decide +kernel
def cuts16629 : List PrefixCut := [⟨42,259231984,259232146⟩,
⟨109,664634183,664634597⟩,
⟨128,782449802,782450288⟩]
theorem checked16629 : checkPrefixCuts (2^48) 2183528449 9 Manual.Count131072.C016629.packed 128 cuts16629 = true := by
 decide +kernel
def pointBounds16629 : List (Nat × Nat × Nat) := [(2183571456,97619197895369,97619576804713),(2183640064,97619603297568,97619982207164)]
theorem point_links_checked16629 : (cuts16629.take 2).map (fun c => (2183528449-1+2*2^9*c.k,97618938663385+c.lower,97619317572567+c.upper)) = pointBounds16629 := by
 decide +kernel
def cuts16630 : List PrefixCut := [⟨48,295436671,295436859⟩,
⟨115,702360108,702360548⟩,
⟨128,783047250,783047740⟩]
theorem checked16630 : checkPrefixCuts (2^48) 2183659521 9 Manual.Count131072.C016630.packed 128 cuts16630 = true := by
 decide +kernel
def pointBounds16630 : List (Nat × Nat × Nat) := [(2183708672,97620016549858,97620395459714),(2183777280,97620423473295,97620802383403)]
theorem point_links_checked16630 : (cuts16630.take 2).map (fun c => (2183659521-1+2*2^9*c.k,97619721113187+c.lower,97620100022855+c.upper)) = pointBounds16630 := by
 decide +kernel
def cuts16631 : List PrefixCut := [⟨54,335503767,335503975⟩,
⟨121,749619292,749619764⟩,
⟨128,792666978,792667478⟩]
theorem checked16631 : checkPrefixCuts (2^48) 2183790593 9 Manual.Count131072.C016631.packed 128 cuts16631 = true := by
 decide +kernel
def pointBounds16631 : List (Nat × Nat × Nat) := [(2183845888,97620839664204,97621218574570),(2183914496,97621253779729,97621632690359)]
theorem point_links_checked16631 : (cuts16631.take 2).map (fun c => (2183790593-1+2*2^9*c.k,97620504160437+c.lower,97620883070595+c.upper)) = pointBounds16631 := by
 decide +kernel
def cuts16632 : List PrefixCut := [⟨60,367446143,367446377⟩,
⟨127,782695642,782696139⟩,
⟨128,788752878,788753379⟩]
theorem checked16632 : checkPrefixCuts (2^48) 2183921665 9 Manual.Count131072.C016632.packed 128 cuts16632 = true := by
 decide +kernel
def pointBounds16632 : List (Nat × Nat × Nat) := [(2183983104,97621664273558,97622043184450),(2184051712,97622079523057,97622458434212)]
theorem point_links_checked16632 : (cuts16632.take 2).map (fun c => (2183921665-1+2*2^9*c.k,97621296827415+c.lower,97621675738073+c.upper)) = pointBounds16632 := by
 decide +kernel
def cuts16633 : List PrefixCut := [⟨66,397838230,397838482⟩,
⟨128,780586541,780587035⟩]
theorem checked16633 : checkPrefixCuts (2^48) 2184052737 9 Manual.Count131072.C016633.packed 128 cuts16633 = true := by
 decide +kernel
def pointBounds16633 : List (Nat × Nat × Nat) := [(2184120320,97622483418523,97622862329934)]
theorem point_links_checked16633 : (cuts16633.take 1).map (fun c => (2184052737-1+2*2^9*c.k,97622085580293+c.lower,97622464491452+c.upper)) = pointBounds16633 := by
 decide +kernel
def cuts16634 : List PrefixCut := [⟨5,29897712,29897731⟩,
⟨72,447041101,447041381⟩,
⟨128,787756346,787756842⟩]
theorem checked16634 : checkPrefixCuts (2^48) 2184183809 9 Manual.Count131072.C016634.packed 128 cuts16634 = true := by
 decide +kernel
def pointBounds16634 : List (Nat × Nat × Nat) := [(2184188928,97622896064546,97623274976218),(2184257536,97623313207935,97623692119868)]
theorem point_links_checked16634 : (cuts16634.take 2).map (fun c => (2184183809-1+2*2^9*c.k,97622866166834+c.lower,97623245078487+c.upper)) = pointBounds16634 := by
 decide +kernel
def cuts16635 : List PrefixCut := [⟨11,67781171,67781214⟩,
⟨78,477939906,477940210⟩,
⟨128,786678045,786678545⟩]
theorem checked16635 : checkPrefixCuts (2^48) 2184314881 9 Manual.Count131072.C016635.packed 128 cuts16635 = true := by
 decide +kernel
def pointBounds16635 : List (Nat × Nat × Nat) := [(2184326144,97623721704351,97624100616543),(2184394752,97624131863086,97624510775539)]
theorem point_links_checked16635 : (cuts16635.take 2).map (fun c => (2184314881-1+2*2^9*c.k,97623653923180+c.lower,97624032835329+c.upper)) = pointBounds16635 := by
 decide +kernel
def cuts16636 : List PrefixCut := [⟨17,108494735,108494805⟩,
⟨84,511412057,511412382⟩,
⟨128,778899940,778900435⟩]
theorem checked16636 : checkPrefixCuts (2^48) 2184445953 9 Manual.Count131072.C016636.packed 128 cuts16636 = true := by
 decide +kernel
def pointBounds16636 : List (Nat × Nat × Nat) := [(2184463360,97624549095960,97624928008679),(2184531968,97624952013282,97625330926256)]
theorem point_links_checked16636 : (cuts16636.take 2).map (fun c => (2184445953-1+2*2^9*c.k,97624440601225+c.lower,97624819513874+c.upper)) = pointBounds16636 := by
 decide +kernel
def cuts16637 : List PrefixCut := [⟨23,144049487,144049577⟩,
⟨90,551837514,551837860⟩,
⟨128,785681804,785682301⟩]
theorem checked16637 : checkPrefixCuts (2^48) 2184577025 9 Manual.Count131072.C016637.packed 128 cuts16637 = true := by
 decide +kernel
def pointBounds16637 : List (Nat × Nat × Nat) := [(2184600576,97625363550652,97625742463886),(2184669184,97625771338679,97626150252169)]
theorem point_links_checked16637 : (cuts16637.take 2).map (fun c => (2184577025-1+2*2^9*c.k,97625219501165+c.lower,97625598414309+c.upper)) = pointBounds16637 := by
 decide +kernel
def cuts16638 : List PrefixCut := [⟨29,180372929,180373037⟩,
⟨96,592129269,592129638⟩,
⟨128,792591717,792592209⟩]
theorem checked16638 : checkPrefixCuts (2^48) 2184708097 9 Manual.Count131072.C016638.packed 128 cuts16638 = true := by
 decide +kernel
def pointBounds16638 : List (Nat × Nat × Nat) := [(2184737792,97626185555898,97626564469647),(2184806400,97626597312238,97626976226248)]
theorem point_links_checked16638 : (cuts16638.take 2).map (fun c => (2184708097-1+2*2^9*c.k,97626005182969+c.lower,97626384096610+c.upper)) = pointBounds16638 := by
 decide +kernel
def cuts16639 : List PrefixCut := [⟨35,211538636,211538769⟩,
⟨102,623913229,623913620⟩,
⟨128,780434383,780434873⟩]
theorem checked16639 : checkPrefixCuts (2^48) 2184839169 9 Manual.Count131072.C016639.packed 128 cuts16639 = true := by
 decide +kernel
def pointBounds16639 : List (Nat × Nat × Nat) := [(2184875008,97627009313322,97627388227588),(2184943616,97627421687915,97627800602439)]
theorem point_links_checked16639 : (cuts16639.take 2).map (fun c => (2184839169-1+2*2^9*c.k,97626797774686+c.lower,97627176688819+c.upper)) = pointBounds16639 := by
 decide +kernel
def cuts16640 : List PrefixCut := [⟨41,246307637,246307794⟩,
⟨108,661490410,661490825⟩,
⟨128,782835163,782835653⟩]
theorem checked16640 : checkPrefixCuts (2^48) 2184970241 9 Manual.Count131072.C016640.packed 128 cuts16640 = true := by
 decide +kernel
def pointBounds16640 : List (Nat × Nat × Nat) := [(2185012224,97627824516706,97628203431486),(2185080832,97628239699479,97628618614517)]
theorem point_links_checked16640 : (cuts16640.take 2).map (fun c => (2184970241-1+2*2^9*c.k,97627578209069+c.lower,97627957123692+c.upper)) = pointBounds16640 := by
 decide +kernel
def cuts16641 : List PrefixCut := [⟨47,293824906,293825092⟩,
⟨114,703957868,703958317⟩,
⟨128,790388156,790388660⟩]
theorem checked16641 : checkPrefixCuts (2^48) 2185101313 9 Manual.Count131072.C016641.packed 128 cuts16641 = true := by
 decide +kernel
def pointBounds16641 : List (Nat × Nat × Nat) := [(2185149440,97628654869138,97629033784437),(2185218048,97629065002100,97629443917662)]
theorem point_links_checked16641 : (cuts16641.take 2).map (fun c => (2185101313-1+2*2^9*c.k,97628361044232+c.lower,97628739959345+c.upper)) = pointBounds16641 := by
 decide +kernel
def cuts16642 : List PrefixCut := [⟨53,323174681,323174887⟩,
⟨120,729804296,729804759⟩,
⟨128,776429995,776430489⟩]
theorem checked16642 : checkPrefixCuts (2^48) 2185232385 9 Manual.Count131072.C016642.packed 128 cuts16642 = true := by
 decide +kernel
def pointBounds16642 : List (Nat × Nat × Nat) := [(2185286656,97629474607069,97629853522892),(2185355264,97629881236684,97630260152764)]
theorem point_links_checked16642 : (cuts16642.take 2).map (fun c => (2185232385-1+2*2^9*c.k,97629151432388+c.lower,97629530348005+c.upper)) = pointBounds16642 := by
 decide +kernel
def cuts16643 : List PrefixCut := [⟨59,362051945,362052176⟩,
⟨126,771360742,771361234⟩,
⟨128,783209640,783210140⟩]
theorem checked16643 : checkPrefixCuts (2^48) 2185363457 9 Manual.Count131072.C016643.packed 128 cuts16643 = true := by
 decide +kernel
def pointBounds16643 : List (Nat × Nat × Nat) := [(2185423872,97630289914328,97630668830670),(2185492480,97630699223125,97631078139728)]
theorem point_links_checked16643 : (cuts16643.take 2).map (fun c => (2185363457-1+2*2^9*c.k,97629927862383+c.lower,97630306778494+c.upper)) = pointBounds16643 := by
 decide +kernel
def cuts16644 : List PrefixCut := [⟨65,396416732,396416984⟩,
⟨128,781230777,781231276⟩]
theorem checked16644 : checkPrefixCuts (2^48) 2185494529 9 Manual.Count131072.C016644.packed 128 cuts16644 = true := by
 decide +kernel
def pointBounds16644 : List (Nat × Nat × Nat) := [(2185561088,97631107488755,97631486405618)]
theorem point_links_checked16644 : (cuts16644.take 1).map (fun c => (2185494529-1+2*2^9*c.k,97630711072023+c.lower,97631089988634+c.upper)) = pointBounds16644 := by
 decide +kernel
def cuts16645 : List PrefixCut := [⟨4,24340264,24340279⟩,
⟨71,435542250,435542525⟩,
⟨128,795349590,795350088⟩]
theorem checked16645 : checkPrefixCuts (2^48) 2185625601 9 Manual.Count131072.C016645.packed 128 cuts16645 = true := by
 decide +kernel
def pointBounds16645 : List (Nat × Nat × Nat) := [(2185629696,97631516643064,97631895560189),(2185698304,97631927845050,97632306762435)]
theorem point_links_checked16645 : (cuts16645.take 2).map (fun c => (2185625601-1+2*2^9*c.k,97631492302800+c.lower,97631871219910+c.upper)) = pointBounds16645 := by
 decide +kernel
def cuts16646 : List PrefixCut := [⟨10,62327849,62327889⟩,
⟨77,468868096,468868388⟩,
⟨128,782424708,782425196⟩]
theorem checked16646 : checkPrefixCuts (2^48) 2185756673 9 Manual.Count131072.C016646.packed 128 cuts16646 = true := by
 decide +kernel
def pointBounds16646 : List (Nat × Nat × Nat) := [(2185766912,97632349980239,97632728897887),(2185835520,97632756520486,97633135438386)]
theorem point_links_checked16646 : (cuts16646.take 2).map (fun c => (2185756673-1+2*2^9*c.k,97632287652390+c.lower,97632666569998+c.upper)) = pointBounds16646 := by
 decide +kernel
def cuts16647 : List PrefixCut := [⟨16,96962814,96962878⟩,
⟨83,511976202,511976529⟩,
⟨128,781991727,781992231⟩]
theorem checked16647 : checkPrefixCuts (2^48) 2185887745 9 Manual.Count131072.C016647.packed 128 cuts16647 = true := by
 decide +kernel
def pointBounds16647 : List (Nat × Nat × Nat) := [(2185904128,97633167039912,97633545958072),(2185972736,97633582053300,97633960971723)]
theorem point_links_checked16647 : (cuts16647.take 2).map (fun c => (2185887745-1+2*2^9*c.k,97633070077098+c.lower,97633448995194+c.upper)) = pointBounds16647 := by
 decide +kernel
def cuts16648 : List PrefixCut := [⟨22,128503240,128503325⟩,
⟨89,539370261,539370600⟩,
⟨128,773704144,773704634⟩]
theorem checked16648 : checkPrefixCuts (2^48) 2186018817 9 Manual.Count131072.C016648.packed 128 cuts16648 = true := by
 decide +kernel
def pointBounds16648 : List (Nat × Nat × Nat) := [(2186041344,97633980572065,97634359490750),(2186109952,97634391439086,97634770358025)]
theorem point_links_checked16648 : (cuts16648.take 2).map (fun c => (2186018817-1+2*2^9*c.k,97633852068825+c.lower,97634230987425+c.upper)) = pointBounds16648 := by
 decide +kernel
def cuts16649 : List PrefixCut := [⟨28,173687596,173687706⟩,
⟨95,588262620,588262994⟩,
⟨128,792326560,792327060⟩]
theorem checked16649 : checkPrefixCuts (2^48) 2186149889 9 Manual.Count131072.C016649.packed 128 cuts16649 = true := by
 decide +kernel
def pointBounds16649 : List (Nat × Nat × Nat) := [(2186178560,97634799460565,97635178379765),(2186247168,97635214035589,97635592955053)]
theorem point_links_checked16649 : (cuts16649.take 2).map (fun c => (2186149889-1+2*2^9*c.k,97634625772969+c.lower,97635004692059+c.upper)) = pointBounds16649 := by
 decide +kernel
def cuts16650 : List PrefixCut := [⟨34,205348223,205348353⟩,
⟨101,613975054,613975440⟩,
⟨128,781850814,781851306⟩]
theorem checked16650 : checkPrefixCuts (2^48) 2186280961 9 Manual.Count131072.C016650.packed 128 cuts16650 = true := by
 decide +kernel
def pointBounds16650 : List (Nat × Nat × Nat) := [(2186315776,97635623447752,97636002367472),(2186384384,97636032074583,97636410994559)]
theorem point_links_checked16650 : (cuts16650.take 2).map (fun c => (2186280961-1+2*2^9*c.k,97635418099529+c.lower,97635797019119+c.upper)) = pointBounds16650 := by
 decide +kernel
def cuts16651 : List PrefixCut := [⟨40,252324618,252324779⟩,
⟨107,657449987,657450406⟩,
⟨128,792231538,792232039⟩]
theorem checked16651 : checkPrefixCuts (2^48) 2186412033 9 Manual.Count131072.C016651.packed 128 cuts16651 = true := by
 decide +kernel
def pointBounds16651 : List (Nat × Nat × Nat) := [(2186452992,97636452274961,97636831195204),(2186521600,97636857400330,97637236320831)]
theorem point_links_checked16651 : (cuts16651.take 2).map (fun c => (2186412033-1+2*2^9*c.k,97636199950343+c.lower,97636578870425+c.upper)) = pointBounds16651 := by
 decide +kernel
def cuts16652 : List PrefixCut := [⟨46,286551102,286551275⟩,
⟨113,699632050,699632484⟩,
⟨128,787678763,787679255⟩]
theorem checked16652 : checkPrefixCuts (2^48) 2186543105 9 Manual.Count131072.C016652.packed 128 cuts16652 = true := by
 decide +kernel
def pointBounds16652 : List (Nat × Nat × Nat) := [(2186590208,97637278732983,97637657653739),(2186658816,97637691813931,97638070734948)]
theorem point_links_checked16652 : (cuts16652.take 2).map (fun c => (2186543105-1+2*2^9*c.k,97636992181881+c.lower,97637371102464+c.upper)) = pointBounds16652 := by
 decide +kernel
def cuts16653 : List PrefixCut := [⟨52,315367093,315367291⟩,
⟨119,736402643,736403102⟩,
⟨128,791364114,791364608⟩]
theorem checked16653 : checkPrefixCuts (2^48) 2186674177 9 Manual.Count131072.C016653.packed 128 cuts16653 = true := by
 decide +kernel
def pointBounds16653 : List (Nat × Nat × Nat) := [(2186727424,97638095227737,97638474149010),(2186796032,97638516263287,97638895184821)]
theorem point_links_checked16653 : (cuts16653.take 2).map (fun c => (2186674177-1+2*2^9*c.k,97637779860644+c.lower,97638158781719+c.upper)) = pointBounds16653 := by
 decide +kernel
def cuts16654 : List PrefixCut := [⟨58,357951857,357952085⟩,
⟨125,767119744,767120230⟩,
⟨128,787069406,787069904⟩]
theorem checked16654 : checkPrefixCuts (2^48) 2186805249 9 Manual.Count131072.C016654.packed 128 cuts16654 = true := by
 decide +kernel
def pointBounds16654 : List (Nat × Nat × Nat) := [(2186864640,97638929176615,97639308098412),(2186933248,97639338344502,97639717266557)]
theorem point_links_checked16654 : (cuts16654.take 2).map (fun c => (2186805249-1+2*2^9*c.k,97638571224758+c.lower,97638950146327+c.upper)) = pointBounds16654 := by
 decide +kernel
def cuts16655 : List PrefixCut := [⟨64,390106323,390106567⟩,
⟨128,784576733,784577227⟩]
theorem checked16655 : checkPrefixCuts (2^48) 2186936321 9 Manual.Count131072.C016655.packed 128 cuts16655 = true := by
 decide +kernel
def pointBounds16655 : List (Nat × Nat × Nat) := [(2187001856,97639748400487,97640127322798)]
theorem point_links_checked16655 : (cuts16655.take 1).map (fun c => (2186936321-1+2*2^9*c.k,97639358294164+c.lower,97639737216231+c.upper)) = pointBounds16655 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000207
