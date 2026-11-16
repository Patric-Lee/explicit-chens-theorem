import PlattAssemblyKernel
import PlattCertificates.Count131072.C017744
import PlattCertificates.Count131072.C017745
import PlattCertificates.Count131072.C017746
import PlattCertificates.Count131072.C017747
import PlattCertificates.Count131072.C017748
import PlattCertificates.Count131072.C017749
import PlattCertificates.Count131072.C017750
import PlattCertificates.Count131072.C017751
import PlattCertificates.Count131072.C017752
import PlattCertificates.Count131072.C017753
import PlattCertificates.Count131072.C017754
import PlattCertificates.Count131072.C017755
import PlattCertificates.Count131072.C017756
import PlattCertificates.Count131072.C017757
import PlattCertificates.Count131072.C017758
import PlattCertificates.Count131072.C017759
import PlattCertificates.Count131072.C017760
import PlattCertificates.Count131072.C017761
import PlattCertificates.Count131072.C017762
import PlattCertificates.Count131072.C017763
import PlattCertificates.Count131072.C017764
import PlattCertificates.Count131072.C017765
import PlattCertificates.Count131072.C017766
import PlattCertificates.Count131072.C017767
import PlattCertificates.Count131072.C017768
import PlattCertificates.Count131072.C017769
import PlattCertificates.Count131072.C017770
import PlattCertificates.Count131072.C017771
import PlattCertificates.Count131072.C017772
import PlattCertificates.Count131072.C017773
import PlattCertificates.Count131072.C017774
import PlattCertificates.Count131072.C017775
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000242
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17744 : List PrefixCut := [⟨60,342766292,342766502⟩,
⟨128,723459444,723459891⟩]
theorem checked17744 : checkPrefixCuts (2^48) 2329673729 9 Manual.Count131072.C017744.packed 128 cuts17744 = true := by
 decide +kernel
def pointBounds17744 : List (Nat × Nat × Nat) := [(2329735168,98466085676609,98466465113161)]
theorem point_links_checked17744 : (cuts17744.take 1).map (fun c => (2329673729-1+2*2^9*c.k,98465742910317+c.lower,98466122346659+c.upper)) = pointBounds17744 := by
 decide +kernel
def cuts17745 : List PrefixCut := [⟨4,25612715,25612730⟩,
⟨76,442537267,442537536⟩,
⟨128,741178050,741178507⟩]
theorem checked17745 : checkPrefixCuts (2^48) 2329804801 9 Manual.Count131072.C017745.packed 128 cuts17745 = true := by
 decide +kernel
def pointBounds17745 : List (Nat × Nat × Nat) := [(2329808896,98466491982476,98466871419280),(2329882624,98466908907028,98467288344086)]
theorem point_links_checked17745 : (cuts17745.take 2).map (fun c => (2329804801-1+2*2^9*c.k,98466466369761+c.lower,98466845806550+c.upper)) = pointBounds17745 := by
 decide +kernel
def cuts17746 : List PrefixCut := [⟨20,114404670,114404745⟩,
⟨92,526228999,526229322⟩,
⟨128,731351075,731351524⟩]
theorem checked17746 : checkPrefixCuts (2^48) 2329935873 9 Manual.Count131072.C017746.packed 128 cuts17746 = true := by
 decide +kernel
def pointBounds17746 : List (Nat × Nat × Nat) := [(2329956352,98467321952481,98467701389802),(2330030080,98467733776810,98468113214379)]
theorem point_links_checked17746 : (cuts17746.take 2).map (fun c => (2329935873-1+2*2^9*c.k,98467207547811+c.lower,98467586985057+c.upper)) = pointBounds17746 := by
 decide +kernel
def cuts17747 : List PrefixCut := [⟨36,208380415,208380544⟩,
⟨108,612085262,612085644⟩,
⟨128,726115691,726116143⟩]
theorem checked17747 : checkPrefixCuts (2^48) 2330066945 9 Manual.Count131072.C017747.packed 128 cuts17747 = true := by
 decide +kernel
def pointBounds17747 : List (Nat × Nat × Nat) := [(2330103808,98468147279301,98468526717125),(2330177536,98468550984148,98468930422225)]
theorem point_links_checked17747 : (cuts17747.take 2).map (fun c => (2330066945-1+2*2^9*c.k,98467938898886+c.lower,98468318336581+c.upper)) = pointBounds17747 := by
 decide +kernel
def cuts17748 : List PrefixCut := [⟨52,289661714,289661893⟩,
⟨124,701554766,701555195⟩,
⟨128,723900494,723900937⟩]
theorem checked17748 : checkPrefixCuts (2^48) 2330198017 9 Manual.Count131072.C017748.packed 128 cuts17748 = true := by
 decide +kernel
def pointBounds17748 : List (Nat × Nat × Nat) := [(2330251264,98468954676291,98469334114617),(2330324992,98469366569343,98469746007919)]
theorem point_links_checked17748 : (cuts17748.take 2).map (fun c => (2330198017-1+2*2^9*c.k,98468665014577+c.lower,98469044452724+c.upper)) = pointBounds17748 := by
 decide +kernel
def cuts17749 : List PrefixCut := [⟨68,382528488,382528730⟩,
⟨128,728207764,728208211⟩]
theorem checked17749 : checkPrefixCuts (2^48) 2330329089 9 Manual.Count131072.C017749.packed 128 cuts17749 = true := by
 decide +kernel
def pointBounds17749 : List (Nat × Nat × Nat) := [(2330398720,98469771443559,98470150882391)]
theorem point_links_checked17749 : (cuts17749.take 1).map (fun c => (2330329089-1+2*2^9*c.k,98469388915071+c.lower,98469768353661+c.upper)) = pointBounds17749 := by
 decide +kernel
def cuts17750 : List PrefixCut := [⟨12,71381283,71381327⟩,
⟨84,478524857,478525155⟩,
⟨128,732635929,732636380⟩]
theorem checked17750 : checkPrefixCuts (2^48) 2330460161 9 Manual.Count131072.C017750.packed 128 cuts17750 = true := by
 decide +kernel
def pointBounds17750 : List (Nat × Nat × Nat) := [(2330472448,98470188504118,98470567943199),(2330546176,98470595647692,98470975087027)]
theorem point_links_checked17750 : (cuts17750.take 2).map (fun c => (2330460161-1+2*2^9*c.k,98470117122835+c.lower,98470496561872+c.upper)) = pointBounds17750 := by
 decide +kernel
def cuts17751 : List PrefixCut := [⟨28,154589801,154589896⟩,
⟨100,569557684,569558029⟩,
⟨128,734768277,734768718⟩]
theorem checked17751 : checkPrefixCuts (2^48) 2330591233 9 Manual.Count131072.C017751.packed 128 cuts17751 = true := by
 decide +kernel
def pointBounds17751 : List (Nat × Nat × Nat) := [(2330619904,98471004348565,98471383788148),(2330693632,98471419316448,98471798756281)]
theorem point_links_checked17751 : (cuts17751.take 2).map (fun c => (2330591233-1+2*2^9*c.k,98470849758764+c.lower,98471229198252+c.upper)) = pointBounds17751 := by
 decide +kernel
def cuts17752 : List PrefixCut := [⟨44,256024032,256024191⟩,
⟨116,670241098,670241511⟩,
⟨128,738712450,738712904⟩]
theorem checked17752 : checkPrefixCuts (2^48) 2330722305 9 Manual.Count131072.C017752.packed 128 cuts17752 = true := by
 decide +kernel
def pointBounds17752 : List (Nat × Nat × Nat) := [(2330767360,98471840551073,98472219991161),(2330841088,98472254768139,98472634208481)]
theorem point_links_checked17752 : (cuts17752.take 2).map (fun c => (2330722305-1+2*2^9*c.k,98471584527041+c.lower,98471963966970+c.upper)) = pointBounds17752 := by
 decide +kernel
def cuts17753 : List PrefixCut := [⟨60,342351327,342351542⟩,
⟨128,735168804,735169260⟩]
theorem checked17753 : checkPrefixCuts (2^48) 2330853377 9 Manual.Count131072.C017753.packed 128 cuts17753 = true := by
 decide +kernel
def pointBounds17753 : List (Nat × Nat × Nat) := [(2330914816,98472665590818,98473045031416)]
theorem point_links_checked17753 : (cuts17753.take 1).map (fun c => (2330853377-1+2*2^9*c.k,98472323239491+c.lower,98472702679874+c.upper)) = pointBounds17753 := by
 decide +kernel
def cuts17754 : List PrefixCut := [⟨4,24392216,24392232⟩,
⟨76,436275721,436275991⟩,
⟨128,730539203,730539654⟩]
theorem checked17754 : checkPrefixCuts (2^48) 2330984449 9 Manual.Count131072.C017754.packed 128 cuts17754 = true := by
 decide +kernel
def pointBounds17754 : List (Nat × Nat × Nat) := [(2330988544,98473082800511,98473462241366),(2331062272,98473494684016,98473874125125)]
theorem point_links_checked17754 : (cuts17754.take 2).map (fun c => (2330984449-1+2*2^9*c.k,98473058408295+c.lower,98473437849134+c.upper)) = pointBounds17754 := by
 decide +kernel
def cuts17755 : List PrefixCut := [⟨20,118814392,118814462⟩,
⟨92,536346767,536347092⟩,
⟨128,746919112,746919567⟩]
theorem checked17755 : checkPrefixCuts (2^48) 2331115521 9 Manual.Count131072.C017755.packed 128 cuts17755 = true := by
 decide +kernel
def pointBounds17755 : List (Nat × Nat × Nat) := [(2331136000,98473907761890,98474287203250),(2331209728,98474325294265,98474704735880)]
theorem point_links_checked17755 : (cuts17755.take 2).map (fun c => (2331115521-1+2*2^9*c.k,98473788947498+c.lower,98474168388788+c.upper)) = pointBounds17755 := by
 decide +kernel
def cuts17756 : List PrefixCut := [⟨36,208757937,208758068⟩,
⟨108,618898991,618899378⟩,
⟨128,733354654,733355109⟩]
theorem checked17756 : checkPrefixCuts (2^48) 2331246593 9 Manual.Count131072.C017756.packed 128 cuts17756 = true := by
 decide +kernel
def pointBounds17756 : List (Nat × Nat × Nat) := [(2331283456,98474744624547,98475124066423),(2331357184,98475154765601,98475534207733)]
theorem point_links_checked17756 : (cuts17756.take 2).map (fun c => (2331246593-1+2*2^9*c.k,98474535866610+c.lower,98474915308355+c.upper)) = pointBounds17756 := by
 decide +kernel
def cuts17757 : List PrefixCut := [⟨52,296879761,296879945⟩,
⟨124,705304655,705305085⟩,
⟨128,728001257,728001700⟩]
theorem checked17757 : checkPrefixCuts (2^48) 2331377665 9 Manual.Count131072.C017757.packed 128 cuts17757 = true := by
 decide +kernel
def pointBounds17757 : List (Nat × Nat × Nat) := [(2331430912,98475566101025,98475945543409),(2331504640,98475974525919,98476353968549)]
theorem point_links_checked17757 : (cuts17757.take 2).map (fun c => (2331377665-1+2*2^9*c.k,98475269221264+c.lower,98475648663464+c.upper)) = pointBounds17757 := by
 decide +kernel
def cuts17758 : List PrefixCut := [⟨68,391751686,391751929⟩,
⟨128,730616379,730616835⟩]
theorem checked17758 : checkPrefixCuts (2^48) 2331508737 9 Manual.Count131072.C017758.packed 128 cuts17758 = true := by
 decide +kernel
def pointBounds17758 : List (Nat × Nat × Nat) := [(2331578368,98476388974207,98476768417093)]
theorem point_links_checked17758 : (cuts17758.take 1).map (fun c => (2331508737-1+2*2^9*c.k,98475997222521+c.lower,98476376665164+c.upper)) = pointBounds17758 := by
 decide +kernel
def cuts17759 : List PrefixCut := [⟨12,69896527,69896570⟩,
⟨84,485767185,485767485⟩,
⟨128,740956781,740957236⟩]
theorem checked17759 : checkPrefixCuts (2^48) 2331639809 9 Manual.Count131072.C017759.packed 128 cuts17759 = true := by
 decide +kernel
def pointBounds17759 : List (Nat × Nat × Nat) := [(2331652096,98476797735427,98477177178569),(2331725824,98477213606085,98477593049484)]
theorem point_links_checked17759 : (cuts17759.take 2).map (fun c => (2331639809-1+2*2^9*c.k,98476727838900+c.lower,98477107281999+c.upper)) = pointBounds17759 := by
 decide +kernel
def cuts17760 : List PrefixCut := [⟨28,157650138,157650232⟩,
⟨100,569148998,569149341⟩,
⟨128,731137638,731138082⟩]
theorem checked17760 : checkPrefixCuts (2^48) 2331770881 9 Manual.Count131072.C017760.packed 128 cuts17760 = true := by
 decide +kernel
def pointBounds17760 : List (Nat × Nat × Nat) := [(2331799552,98477626445819,98478005889467),(2331873280,98478037944679,98478417388576)]
theorem point_links_checked17760 : (cuts17760.take 2).map (fun c => (2331770881-1+2*2^9*c.k,98477468795681+c.lower,98477848239235+c.upper)) = pointBounds17760 := by
 decide +kernel
def cuts17761 : List PrefixCut := [⟨44,252756219,252756370⟩,
⟨116,667125807,667126212⟩,
⟨128,735200421,735200869⟩]
theorem checked17761 : checkPrefixCuts (2^48) 2331901953 9 Manual.Count131072.C017761.packed 128 cuts17761 = true := by
 decide +kernel
def pointBounds17761 : List (Nat × Nat × Nat) := [(2331947008,98478452689538,98478832133687),(2332020736,98478867059126,98479246503529)]
theorem point_links_checked17761 : (cuts17761.take 2).map (fun c => (2331901953-1+2*2^9*c.k,98478199933319+c.lower,98478579377317+c.upper)) = pointBounds17761 := by
 decide +kernel
def cuts17762 : List PrefixCut := [⟨60,343867949,343868164⟩,
⟨128,729727844,729728298⟩]
theorem checked17762 : checkPrefixCuts (2^48) 2332033025 9 Manual.Count131072.C017762.packed 128 cuts17762 = true := by
 decide +kernel
def pointBounds17762 : List (Nat × Nat × Nat) := [(2332094464,98479279001689,98479658446350)]
theorem point_links_checked17762 : (cuts17762.take 1).map (fun c => (2332033025-1+2*2^9*c.k,98478935133740+c.lower,98479314578186+c.upper)) = pointBounds17762 := by
 decide +kernel
def cuts17763 : List PrefixCut := [⟨4,19431488,19431500⟩,
⟨76,437744624,437744892⟩,
⟨128,735841973,735842424⟩]
theorem checked17763 : checkPrefixCuts (2^48) 2332164097 9 Manual.Count131072.C017763.packed 128 cuts17763 = true := by
 decide +kernel
def pointBounds17763 : List (Nat × Nat × Nat) := [(2332168192,98479684293072,98480063737984),(2332241920,98480102606208,98480482051376)]
theorem point_links_checked17763 : (cuts17763.take 2).map (fun c => (2332164097-1+2*2^9*c.k,98479664861584+c.lower,98480044306484+c.upper)) = pointBounds17763 := by
 decide +kernel
def cuts17764 : List PrefixCut := [⟨20,113685515,113685583⟩,
⟨92,519662564,519662877⟩,
⟨128,720473991,720474428⟩]
theorem checked17764 : checkPrefixCuts (2^48) 2332295169 9 Manual.Count131072.C017764.packed 128 cuts17764 = true := by
 decide +kernel
def pointBounds17764 : List (Nat × Nat × Nat) := [(2332315648,98480514389072,98480893834491),(2332389376,98480920366121,98481299811785)]
theorem point_links_checked17764 : (cuts17764.take 2).map (fun c => (2332295169-1+2*2^9*c.k,98480400703557+c.lower,98480780148908+c.upper)) = pointBounds17764 := by
 decide +kernel
def cuts17765 : List PrefixCut := [⟨36,208893724,208893853⟩,
⟨108,615931222,615931604⟩,
⟨128,731777078,731777529⟩]
theorem checked17765 : checkPrefixCuts (2^48) 2332426241 9 Manual.Count131072.C017765.packed 128 cuts17765 = true := by
 decide +kernel
def pointBounds17765 : List (Nat × Nat × Nat) := [(2332463104,98481330071272,98481709517189),(2332536832,98481737108770,98482116554940)]
theorem point_links_checked17765 : (cuts17765.take 2).map (fun c => (2332426241-1+2*2^9*c.k,98481121177548+c.lower,98481500623336+c.upper)) = pointBounds17765 := by
 decide +kernel
def cuts17766 : List PrefixCut := [⟨52,296126269,296126447⟩,
⟨124,713394708,713395141⟩,
⟨128,736803825,736804272⟩]
theorem checked17766 : checkPrefixCuts (2^48) 2332557313 9 Manual.Count131072.C017766.packed 128 cuts17766 = true := by
 decide +kernel
def pointBounds17766 : List (Nat × Nat × Nat) := [(2332610560,98482149080895,98482528527312),(2332684288,98482566349334,98482945796006)]
theorem point_links_checked17766 : (cuts17766.take 2).map (fun c => (2332557313-1+2*2^9*c.k,98481852954626+c.lower,98482232400865+c.upper)) = pointBounds17766 := by
 decide +kernel
def cuts17767 : List PrefixCut := [⟨68,393363476,393363712⟩,
⟨128,738813744,738814192⟩]
theorem checked17767 : checkPrefixCuts (2^48) 2332688385 9 Manual.Count131072.C017767.packed 128 cuts17767 = true := by
 decide +kernel
def pointBounds17767 : List (Nat × Nat × Nat) := [(2332758016,98482983121927,98483362568849)]
theorem point_links_checked17767 : (cuts17767.take 1).map (fun c => (2332688385-1+2*2^9*c.k,98482589758451+c.lower,98482969205137+c.upper)) = pointBounds17767 := by
 decide +kernel
def cuts17768 : List PrefixCut := [⟨12,66362091,66362134⟩,
⟨84,484435530,484435828⟩,
⟨128,731532950,731533400⟩]
theorem checked17768 : checkPrefixCuts (2^48) 2332819457 9 Manual.Count131072.C017768.packed 128 cuts17768 = true := by
 decide +kernel
def pointBounds17768 : List (Nat × Nat × Nat) := [(2332831744,98483394934286,98483774381463),(2332905472,98483813007725,98484192455157)]
theorem point_links_checked17768 : (cuts17768.take 2).map (fun c => (2332819457-1+2*2^9*c.k,98483328572195+c.lower,98483708019329+c.upper)) = pointBounds17768 := by
 decide +kernel
def cuts17769 : List PrefixCut := [⟨28,160948639,160948734⟩,
⟨100,572721927,572722278⟩,
⟨128,731853814,731854261⟩]
theorem checked17769 : checkPrefixCuts (2^48) 2332950529 9 Manual.Count131072.C017769.packed 128 cuts17769 = true := by
 decide +kernel
def pointBounds17769 : List (Nat × Nat × Nat) := [(2332979200,98484221053784,98484600501463),(2333052928,98484632827072,98485012275007)]
theorem point_links_checked17769 : (cuts17769.take 2).map (fun c => (2332950529-1+2*2^9*c.k,98484060105145+c.lower,98484439552729+c.upper)) = pointBounds17769 := by
 decide +kernel
def cuts17770 : List PrefixCut := [⟨44,253111017,253111176⟩,
⟨116,671252292,671252706⟩,
⟨128,739654404,739654859⟩]
theorem checked17770 : checkPrefixCuts (2^48) 2333081601 9 Manual.Count131072.C017770.packed 128 cuts17770 = true := by
 decide +kernel
def pointBounds17770 : List (Nat × Nat × Nat) := [(2333126656,98485045069976,98485424518166),(2333200384,98485463211251,98485842659696)]
theorem point_links_checked17770 : (cuts17770.take 2).map (fun c => (2333081601-1+2*2^9*c.k,98484791958959+c.lower,98485171406990+c.upper)) = pointBounds17770 := by
 decide +kernel
def cuts17771 : List PrefixCut := [⟨60,341763909,341764114⟩,
⟨128,734184169,734184616⟩]
theorem checked17771 : checkPrefixCuts (2^48) 2333212673 9 Manual.Count131072.C017771.packed 128 cuts17771 = true := by
 decide +kernel
def pointBounds17771 : List (Nat × Nat × Nat) := [(2333274112,98485873377272,98486252825963)]
theorem point_links_checked17771 : (cuts17771.take 1).map (fun c => (2333212673-1+2*2^9*c.k,98485531613363+c.lower,98485911061849+c.upper)) = pointBounds17771 := by
 decide +kernel
def cuts17772 : List PrefixCut := [⟨4,23885026,23885040⟩,
⟨76,433542570,433542829⟩,
⟨128,736434839,736435282⟩]
theorem checked17772 : checkPrefixCuts (2^48) 2333343745 9 Manual.Count131072.C017772.packed 128 cuts17772 = true := by
 decide +kernel
def pointBounds17772 : List (Nat × Nat × Nat) := [(2333347840,98486289682558,98486669131505),(2333421568,98486699340102,98487078789294)]
theorem point_links_checked17772 : (cuts17772.take 2).map (fun c => (2333343745-1+2*2^9*c.k,98486265797532+c.lower,98486645246465+c.upper)) = pointBounds17772 := by
 decide +kernel
def cuts17773 : List PrefixCut := [⟨20,108923723,108923788⟩,
⟨92,528567053,528567371⟩,
⟨128,731568764,731569204⟩]
theorem checked17773 : checkPrefixCuts (2^48) 2333474817 9 Manual.Count131072.C017773.packed 128 cuts17773 = true := by
 decide +kernel
def pointBounds17773 : List (Nat × Nat × Nat) := [(2333495296,98487111156094,98487490605535),(2333569024,98487530799424,98487910249118)]
theorem point_links_checked17773 : (cuts17773.take 2).map (fun c => (2333474817-1+2*2^9*c.k,98487002232371+c.lower,98487381681747+c.upper)) = pointBounds17773 := by
 decide +kernel
def cuts17774 : List PrefixCut := [⟨36,210597366,210597492⟩,
⟨108,620444439,620444815⟩,
⟨128,735025609,735026054⟩]
theorem checked17774 : checkPrefixCuts (2^48) 2333605889 9 Manual.Count131072.C017774.packed 128 cuts17774 = true := by
 decide +kernel
def pointBounds17774 : List (Nat × Nat × Nat) := [(2333642752,98487944398501,98488323848443),(2333716480,98488354245574,98488733695766)]
theorem point_links_checked17774 : (cuts17774.take 2).map (fun c => (2333605889-1+2*2^9*c.k,98487733801135+c.lower,98488113250951+c.upper)) = pointBounds17774 := by
 decide +kernel
def cuts17775 : List PrefixCut := [⟨52,299112426,299112611⟩,
⟨124,711828152,711828584⟩,
⟨128,733416369,733416813⟩]
theorem checked17775 : checkPrefixCuts (2^48) 2333736961 9 Manual.Count131072.C017775.packed 128 cuts17775 = true := by
 decide +kernel
def pointBounds17775 : List (Nat × Nat × Nat) := [(2333790208,98488767939170,98489147389616),(2333863936,98489180654896,98489560105589)]
theorem point_links_checked17775 : (cuts17775.take 2).map (fun c => (2333736961-1+2*2^9*c.k,98488468826744+c.lower,98488848277005+c.upper)) = pointBounds17775 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000242
