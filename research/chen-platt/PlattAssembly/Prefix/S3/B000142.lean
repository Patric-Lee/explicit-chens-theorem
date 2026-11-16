import PlattAssemblyKernel
import PlattCertificates.Count131072.C024544
import PlattCertificates.Count131072.C024545
import PlattCertificates.Count131072.C024546
import PlattCertificates.Count131072.C024547
import PlattCertificates.Count131072.C024548
import PlattCertificates.Count131072.C024549
import PlattCertificates.Count131072.C024550
import PlattCertificates.Count131072.C024551
import PlattCertificates.Count131072.C024552
import PlattCertificates.Count131072.C024553
import PlattCertificates.Count131072.C024554
import PlattCertificates.Count131072.C024555
import PlattCertificates.Count131072.C024556
import PlattCertificates.Count131072.C024557
import PlattCertificates.Count131072.C024558
import PlattCertificates.Count131072.C024559
import PlattCertificates.Count131072.C024560
import PlattCertificates.Count131072.C024561
import PlattCertificates.Count131072.C024562
import PlattCertificates.Count131072.C024563
import PlattCertificates.Count131072.C024564
import PlattCertificates.Count131072.C024565
import PlattCertificates.Count131072.C024566
import PlattCertificates.Count131072.C024567
import PlattCertificates.Count131072.C024568
import PlattCertificates.Count131072.C024569
import PlattCertificates.Count131072.C024570
import PlattCertificates.Count131072.C024571
import PlattCertificates.Count131072.C024572
import PlattCertificates.Count131072.C024573
import PlattCertificates.Count131072.C024574
import PlattCertificates.Count131072.C024575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000142
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24544 : List PrefixCut := [⟨19,79523220,79523266⟩,
⟨118,486656994,486657271⟩,
⟨128,528252257,528252556⟩]
theorem checked24544 : checkPrefixCuts (2^48) 3220963329 9 Manual.Count131072.C024544.packed 128 cuts24544 = true := by
 decide +kernel
def pointBounds24544 : List (Nat × Nat × Nat) := [(3220982784,102661833669038,102662215552772),(3221084160,102662240802812,102662622686777)]
theorem point_links_checked24544 : (cuts24544.take 2).map (fun c => (3220963329-1+2*2^9*c.k,102661754145818+c.lower,102662136029506+c.upper)) = pointBounds24544 := by
 decide +kernel
def cuts24545 : List PrefixCut := [⟨89,364564523,364564720⟩,
⟨128,529366705,529366992⟩]
theorem checked24545 : checkPrefixCuts (2^48) 3221094401 9 Manual.Count131072.C024545.packed 128 cuts24545 = true := by
 decide +kernel
def pointBounds24545 : List (Nat × Nat × Nat) := [(3221185536,102662646962598,102663028846782)]
theorem point_links_checked24545 : (cuts24545.take 1).map (fun c => (3221094401-1+2*2^9*c.k,102662282398075+c.lower,102662664282062+c.upper)) = pointBounds24545 := by
 decide +kernel
def cuts24546 : List PrefixCut := [⟨60,247723651,247723797⟩,
⟨128,523665618,523665925⟩]
theorem checked24546 : checkPrefixCuts (2^48) 3221225473 9 Manual.Count131072.C024546.packed 128 cuts24546 = true := by
 decide +kernel
def pointBounds24546 : List (Nat × Nat × Nat) := [(3221286912,102663059488431,102663441372851)]
theorem point_links_checked24546 : (cuts24546.take 1).map (fun c => (3221225473-1+2*2^9*c.k,102662811764780+c.lower,102663193649054+c.upper)) = pointBounds24546 := by
 decide +kernel
def cuts24547 : List PrefixCut := [⟨31,129056313,129056386⟩,
⟨128,520760819,520761114⟩]
theorem checked24547 : checkPrefixCuts (2^48) 3221356545 9 Manual.Count131072.C024547.packed 128 cuts24547 = true := by
 decide +kernel
def pointBounds24547 : List (Nat × Nat × Nat) := [(3221388288,102663464486711,102663846371365)]
theorem point_links_checked24547 : (cuts24547.take 1).map (fun c => (3221356545-1+2*2^9*c.k,102663335430398+c.lower,102663717314979+c.upper)) = pointBounds24547 := by
 decide +kernel
def cuts24548 : List PrefixCut := [⟨2,7339430,7339435⟩,
⟨101,411263699,411263927⟩,
⟨128,522487011,522487300⟩]
theorem checked24548 : checkPrefixCuts (2^48) 3221487617 9 Manual.Count131072.C024548.packed 128 cuts24548 = true := by
 decide +kernel
def pointBounds24548 : List (Nat × Nat × Nat) := [(3221489664,102663863530647,102664245415528),(3221591040,102664267454916,102664649340020)]
theorem point_links_checked24548 : (cuts24548.take 2).map (fun c => (3221487617-1+2*2^9*c.k,102663856191217+c.lower,102664238076093+c.upper)) = pointBounds24548 := by
 decide +kernel
def cuts24549 : List PrefixCut := [⟨72,294785186,294785352⟩,
⟨128,522465885,522466178⟩]
theorem checked24549 : checkPrefixCuts (2^48) 3221618689 9 Manual.Count131072.C024549.packed 128 cuts24549 = true := by
 decide +kernel
def pointBounds24549 : List (Nat × Nat × Nat) := [(3221692416,102664673463414,102665055348745)]
theorem point_links_checked24549 : (cuts24549.take 1).map (fun c => (3221618689-1+2*2^9*c.k,102664378678228+c.lower,102664760563393+c.upper)) = pointBounds24549 := by
 decide +kernel
def cuts24550 : List PrefixCut := [⟨43,177965543,177965640⟩,
⟨128,525851813,525852110⟩]
theorem checked24550 : checkPrefixCuts (2^48) 3221749761 9 Manual.Count131072.C024550.packed 128 cuts24550 = true := by
 decide +kernel
def pointBounds24550 : List (Nat × Nat × Nat) := [(3221793792,102665079109656,102665460995211)]
theorem point_links_checked24550 : (cuts24550.take 1).map (fun c => (3221749761-1+2*2^9*c.k,102664901144113+c.lower,102665283029571+c.upper)) = pointBounds24550 := by
 decide +kernel
def cuts24551 : List PrefixCut := [⟨14,57921894,57921927⟩,
⟨113,464328849,464329108⟩,
⟨128,524345300,524345589⟩]
theorem checked24551 : checkPrefixCuts (2^48) 3221880833 9 Manual.Count131072.C024551.packed 128 cuts24551 = true := by
 decide +kernel
def pointBounds24551 : List (Nat × Nat × Nat) := [(3221895168,102665484917820,102665866803608),(3221996544,102665891324775,102666273210789)]
theorem point_links_checked24551 : (cuts24551.take 2).map (fun c => (3221880833-1+2*2^9*c.k,102665426995926+c.lower,102665808881681+c.upper)) = pointBounds24551 := by
 decide +kernel
def cuts24552 : List PrefixCut := [⟨84,341048792,341048983⟩,
⟨128,521091629,521091919⟩]
theorem checked24552 : checkPrefixCuts (2^48) 3222011905 9 Manual.Count131072.C024552.packed 128 cuts24552 = true := by
 decide +kernel
def pointBounds24552 : List (Nat × Nat × Nat) := [(3222097920,102666292390018,102666674276253)]
theorem point_links_checked24552 : (cuts24552.take 1).map (fun c => (3222011905-1+2*2^9*c.k,102665951341226+c.lower,102666333227270+c.upper)) = pointBounds24552 := by
 decide +kernel
def cuts24553 : List PrefixCut := [⟨55,223979946,223980073⟩,
⟨128,519847565,519847859⟩]
theorem checked24553 : checkPrefixCuts (2^48) 3222142977 9 Manual.Count131072.C024553.packed 128 cuts24553 = true := by
 decide +kernel
def pointBounds24553 : List (Nat × Nat × Nat) := [(3222199296,102666696412801,102667078299262)]
theorem point_links_checked24553 : (cuts24553.take 1).map (fun c => (3222142977-1+2*2^9*c.k,102666472432855+c.lower,102666854319189+c.upper)) = pointBounds24553 := by
 decide +kernel
def cuts24554 : List PrefixCut := [⟨26,109540042,109540101⟩,
⟨125,510654810,510655094⟩,
⟨128,522359625,522359916⟩]
theorem checked24554 : checkPrefixCuts (2^48) 3222274049 9 Manual.Count131072.C024554.packed 128 cuts24554 = true := by
 decide +kernel
def pointBounds24554 : List (Nat × Nat × Nat) := [(3222300672,102667101820462,102667483707149),(3222402048,102667502935230,102667884822142)]
theorem point_links_checked24554 : (cuts24554.take 2).map (fun c => (3222274049-1+2*2^9*c.k,102666992280420+c.lower,102667374167048+c.upper)) = pointBounds24554 := by
 decide +kernel
def cuts24555 : List PrefixCut := [⟨96,390096103,390096319⟩,
⟨128,518757073,518757357⟩]
theorem checked24555 : checkPrefixCuts (2^48) 3222405121 9 Manual.Count131072.C024555.packed 128 cuts24555 = true := by
 decide +kernel
def pointBounds24555 : List (Nat × Nat × Nat) := [(3222503424,102667904736148,102668286623283)]
theorem point_links_checked24555 : (cuts24555.take 1).map (fun c => (3222405121-1+2*2^9*c.k,102667514640045+c.lower,102667896526964+c.upper)) = pointBounds24555 := by
 decide +kernel
def cuts24556 : List PrefixCut := [⟨67,266052406,266052551⟩,
⟨128,511835774,511836054⟩]
theorem checked24556 : checkPrefixCuts (2^48) 3222536193 9 Manual.Count131072.C024556.packed 128 cuts24556 = true := by
 decide +kernel
def pointBounds24556 : List (Nat × Nat × Nat) := [(3222604800,102668299449524,102668681336872)]
theorem point_links_checked24556 : (cuts24556.take 1).map (fun c => (3222536193-1+2*2^9*c.k,102668033397118+c.lower,102668415284321+c.upper)) = pointBounds24556 := by
 decide +kernel
def cuts24557 : List PrefixCut := [⟨38,160534018,160534105⟩,
⟨128,531815978,531816272⟩]
theorem checked24557 : checkPrefixCuts (2^48) 3222667265 9 Manual.Count131072.C024557.packed 128 cuts24557 = true := by
 decide +kernel
def pointBounds24557 : List (Nat × Nat × Nat) := [(3222706176,102668705766910,102669087654480)]
theorem point_links_checked24557 : (cuts24557.take 1).map (fun c => (3222667265-1+2*2^9*c.k,102668545232892+c.lower,102668927120375+c.upper)) = pointBounds24557 := by
 decide +kernel
def cuts24558 : List PrefixCut := [⟨9,37206216,37206237⟩,
⟨108,443934782,443935041⟩,
⟨128,525593369,525593674⟩]
theorem checked24558 : checkPrefixCuts (2^48) 3222798337 9 Manual.Count131072.C024558.packed 128 cuts24558 = true := by
 decide +kernel
def pointBounds24558 : List (Nat × Nat × Nat) := [(3222807552,102669114255086,102669496142884),(3222908928,102669520983652,102669902871688)]
theorem point_links_checked24558 : (cuts24558.take 2).map (fun c => (3222798337-1+2*2^9*c.k,102669077048870+c.lower,102669458936647+c.upper)) = pointBounds24558 := by
 decide +kernel
def cuts24559 : List PrefixCut := [⟨79,324096548,324096733⟩,
⟨128,529065303,529065604⟩]
theorem checked24559 : checkPrefixCuts (2^48) 3222929409 9 Manual.Count131072.C024559.packed 128 cuts24559 = true := by
 decide +kernel
def pointBounds24559 : List (Nat × Nat × Nat) := [(3223010304,102669926738787,102670308627054)]
theorem point_links_checked24559 : (cuts24559.take 1).map (fun c => (3222929409-1+2*2^9*c.k,102669602642239+c.lower,102669984530321+c.upper)) = pointBounds24559 := by
 decide +kernel
def cuts24560 : List PrefixCut := [⟨50,202170940,202171055⟩,
⟨128,523280003,523280289⟩]
theorem checked24560 : checkPrefixCuts (2^48) 3223060481 9 Manual.Count131072.C024560.packed 128 cuts24560 = true := by
 decide +kernel
def pointBounds24560 : List (Nat × Nat × Nat) := [(3223111680,102670333878482,102670715766980)]
theorem point_links_checked24560 : (cuts24560.take 1).map (fun c => (3223060481-1+2*2^9*c.k,102670131707542+c.lower,102670513595925+c.upper)) = pointBounds24560 := by
 decide +kernel
def cuts24561 : List PrefixCut := [⟨21,86192455,86192505⟩,
⟨120,491210704,491210983⟩,
⟨128,524656013,524656310⟩]
theorem checked24561 : checkPrefixCuts (2^48) 3223191553 9 Manual.Count131072.C024561.packed 128 cuts24561 = true := by
 decide +kernel
def pointBounds24561 : List (Nat × Nat × Nat) := [(3223213056,102670741180000,102671123068719),(3223314432,102671146198249,102671528087197)]
theorem point_links_checked24561 : (cuts24561.take 2).map (fun c => (3223191553-1+2*2^9*c.k,102670654987545+c.lower,102671036876214+c.upper)) = pointBounds24561 := by
 decide +kernel
def cuts24562 : List PrefixCut := [⟨91,368416555,368416763⟩,
⟨128,521054388,521054679⟩]
theorem checked24562 : checkPrefixCuts (2^48) 3223322625 9 Manual.Count131072.C024562.packed 128 cuts24562 = true := by
 decide +kernel
def pointBounds24562 : List (Nat × Nat × Nat) := [(3223415808,102671548060113,102671929949287)]
theorem point_links_checked24562 : (cuts24562.take 1).map (fun c => (3223322625-1+2*2^9*c.k,102671179643558+c.lower,102671561532524+c.upper)) = pointBounds24562 := by
 decide +kernel
def cuts24563 : List PrefixCut := [⟨62,255236506,255236645⟩,
⟨128,524264053,524264348⟩]
theorem checked24563 : checkPrefixCuts (2^48) 3223453697 9 Manual.Count131072.C024563.packed 128 cuts24563 = true := by
 decide +kernel
def pointBounds24563 : List (Nat × Nat × Nat) := [(3223517184,102671955934452,102672337823848)]
theorem point_links_checked24563 : (cuts24563.take 1).map (fun c => (3223453697-1+2*2^9*c.k,102671700697946+c.lower,102672082587203+c.upper)) = pointBounds24563 := by
 decide +kernel
def cuts24564 : List PrefixCut := [⟨33,130888031,130888104⟩,
⟨128,520138865,520139155⟩]
theorem checked24564 : checkPrefixCuts (2^48) 3223584769 9 Manual.Count131072.C024564.packed 128 cuts24564 = true := by
 decide +kernel
def pointBounds24564 : List (Nat × Nat × Nat) := [(3223618560,102672355850030,102672737739655)]
theorem point_links_checked24564 : (cuts24564.take 1).map (fun c => (3223584769-1+2*2^9*c.k,102672224961999+c.lower,102672606851551+c.upper)) = pointBounds24564 := by
 decide +kernel
def cuts24565 : List PrefixCut := [⟨4,16676925,16676935⟩,
⟨103,422068009,422068256⟩,
⟨128,525618391,525618697⟩]
theorem checked24565 : checkPrefixCuts (2^48) 3223715841 9 Manual.Count131072.C024565.packed 128 cuts24565 = true := by
 decide +kernel
def pointBounds24565 : List (Nat × Nat × Nat) := [(3223719936,102672761777789,102673143667641),(3223821312,102673167168873,102673549058962)]
theorem point_links_checked24565 : (cuts24565.take 2).map (fun c => (3223715841-1+2*2^9*c.k,102672745100864+c.lower,102673126990706+c.upper)) = pointBounds24565 := by
 decide +kernel
def cuts24566 : List PrefixCut := [⟨74,303486871,303487037⟩,
⟨128,525509726,525510018⟩]
theorem checked24566 : checkPrefixCuts (2^48) 3223846913 9 Manual.Count131072.C024566.packed 128 cuts24566 = true := by
 decide +kernel
def pointBounds24566 : List (Nat × Nat × Nat) := [(3223922688,102673574206126,102673956096440)]
theorem point_links_checked24566 : (cuts24566.take 1).map (fun c => (3223846913-1+2*2^9*c.k,102673270719255+c.lower,102673652609403+c.upper)) = pointBounds24566 := by
 decide +kernel
def cuts24567 : List PrefixCut := [⟨45,184128534,184128645⟩,
⟨128,530290101,530290406⟩]
theorem checked24567 : checkPrefixCuts (2^48) 3223977985 9 Manual.Count131072.C024567.packed 128 cuts24567 = true := by
 decide +kernel
def pointBounds24567 : List (Nat × Nat × Nat) := [(3224024064,102673980357515,102674362248066)]
theorem point_links_checked24567 : (cuts24567.take 1).map (fun c => (3223977985-1+2*2^9*c.k,102673796228981+c.lower,102674178119421+c.upper)) = pointBounds24567 := by
 decide +kernel
def cuts24568 : List PrefixCut := [⟨16,64254963,64255000⟩,
⟨115,473087103,473087374⟩,
⟨128,525117778,525118078⟩]
theorem checked24568 : checkPrefixCuts (2^48) 3224109057 9 Manual.Count131072.C024568.packed 128 cuts24568 = true := by
 decide +kernel
def pointBounds24568 : List (Nat × Nat × Nat) := [(3224125440,102674390774045,102674772664827),(3224226816,102674799606185,102675181497201)]
theorem point_links_checked24568 : (cuts24568.take 2).map (fun c => (3224109057-1+2*2^9*c.k,102674326519082+c.lower,102674708409827+c.upper)) = pointBounds24568 := by
 decide +kernel
def cuts24569 : List PrefixCut := [⟨86,349106383,349106578⟩,
⟨128,523263179,523263472⟩]
theorem checked24569 : checkPrefixCuts (2^48) 3224240129 9 Manual.Count131072.C024569.packed 128 cuts24569 = true := by
 decide +kernel
def pointBounds24569 : List (Nat × Nat × Nat) := [(3224328192,102675200743243,102675582634483)]
theorem point_links_checked24569 : (cuts24569.take 1).map (fun c => (3224240129-1+2*2^9*c.k,102674851636860+c.lower,102675233527905+c.upper)) = pointBounds24569 := by
 decide +kernel
def cuts24570 : List PrefixCut := [⟨57,226705803,226705930⟩,
⟨128,515298108,515298393⟩]
theorem checked24570 : checkPrefixCuts (2^48) 3224371201 9 Manual.Count131072.C024570.packed 128 cuts24570 = true := by
 decide +kernel
def pointBounds24570 : List (Nat × Nat × Nat) := [(3224429568,102675601605842,102675983497307)]
theorem point_links_checked24570 : (cuts24570.take 1).map (fun c => (3224371201-1+2*2^9*c.k,102675374900039+c.lower,102675756791377+c.upper)) = pointBounds24570 := by
 decide +kernel
def cuts24571 : List PrefixCut := [⟨28,113130584,113130650⟩,
⟨127,516324758,516325051⟩,
⟨128,520078184,520078479⟩]
theorem checked24571 : checkPrefixCuts (2^48) 3224502273 9 Manual.Count131072.C024571.packed 128 cuts24571 = true := by
 decide +kernel
def pointBounds24571 : List (Nat × Nat × Nat) := [(3224530944,102676003328731,102676385220420),(3224632320,102676406522905,102676788414821)]
theorem point_links_checked24571 : (cuts24571.take 2).map (fun c => (3224502273-1+2*2^9*c.k,102675890198147+c.lower,102676272089770+c.upper)) = pointBounds24571 := by
 decide +kernel
def cuts24572 : List PrefixCut := [⟨98,401784832,401785058⟩,
⟨128,524508718,524509011⟩]
theorem checked24572 : checkPrefixCuts (2^48) 3224633345 9 Manual.Count131072.C024572.packed 128 cuts24572 = true := by
 decide +kernel
def pointBounds24572 : List (Nat × Nat × Nat) := [(3224733696,102676812061163,102677193953307)]
theorem point_links_checked24572 : (cuts24572.take 1).map (fun c => (3224633345-1+2*2^9*c.k,102676410276331+c.lower,102676792168249+c.upper)) = pointBounds24572 := by
 decide +kernel
def cuts24573 : List PrefixCut := [⟨69,280619546,280619704⟩,
⟨128,521868869,521869167⟩]
theorem checked24573 : checkPrefixCuts (2^48) 3224764417 9 Manual.Count131072.C024573.packed 128 cuts24573 = true := by
 decide +kernel
def pointBounds24573 : List (Nat × Nat × Nat) := [(3224835072,102677215404595,102677597296964)]
theorem point_links_checked24573 : (cuts24573.take 1).map (fun c => (3224764417-1+2*2^9*c.k,102676934785049+c.lower,102677316677260+c.upper)) = pointBounds24573 := by
 decide +kernel
def cuts24574 : List PrefixCut := [⟨40,158328298,158328388⟩,
⟨128,513992453,513992746⟩]
theorem checked24574 : checkPrefixCuts (2^48) 3224895489 9 Manual.Count131072.C024574.packed 128 cuts24574 = true := by
 decide +kernel
def pointBounds24574 : List (Nat × Nat × Nat) := [(3224936448,102677614982216,102677996874815)]
theorem point_links_checked24574 : (cuts24574.take 1).map (fun c => (3224895489-1+2*2^9*c.k,102677456653918+c.lower,102677838546427+c.upper)) = pointBounds24574 := by
 decide +kernel
def cuts24575 : List PrefixCut := [⟨11,44860978,44861002⟩,
⟨110,450871879,450872133⟩,
⟨128,525492024,525492318⟩]
theorem checked24575 : checkPrefixCuts (2^48) 3225026561 9 Manual.Count131072.C024575.packed 128 cuts24575 = true := by
 decide +kernel
def pointBounds24575 : List (Nat × Nat × Nat) := [(3225037824,102678015507349,102678397400175),(3225139200,102678421518250,102678803411306)]
theorem point_links_checked24575 : (cuts24575.take 2).map (fun c => (3225026561-1+2*2^9*c.k,102677970646371+c.lower,102678352539173+c.upper)) = pointBounds24575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000142
