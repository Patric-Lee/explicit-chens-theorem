import PlattAssemblyKernel
import PlattCertificates.Count131072.C024800
import PlattCertificates.Count131072.C024801
import PlattCertificates.Count131072.C024802
import PlattCertificates.Count131072.C024803
import PlattCertificates.Count131072.C024804
import PlattCertificates.Count131072.C024805
import PlattCertificates.Count131072.C024806
import PlattCertificates.Count131072.C024807
import PlattCertificates.Count131072.C024808
import PlattCertificates.Count131072.C024809
import PlattCertificates.Count131072.C024810
import PlattCertificates.Count131072.C024811
import PlattCertificates.Count131072.C024812
import PlattCertificates.Count131072.C024813
import PlattCertificates.Count131072.C024814
import PlattCertificates.Count131072.C024815
import PlattCertificates.Count131072.C024816
import PlattCertificates.Count131072.C024817
import PlattCertificates.Count131072.C024818
import PlattCertificates.Count131072.C024819
import PlattCertificates.Count131072.C024820
import PlattCertificates.Count131072.C024821
import PlattCertificates.Count131072.C024822
import PlattCertificates.Count131072.C024823
import PlattCertificates.Count131072.C024824
import PlattCertificates.Count131072.C024825
import PlattCertificates.Count131072.C024826
import PlattCertificates.Count131072.C024827
import PlattCertificates.Count131072.C024828
import PlattCertificates.Count131072.C024829
import PlattCertificates.Count131072.C024830
import PlattCertificates.Count131072.C024831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24800 : List PrefixCut := [⟨23,91503383,91503436⟩,
⟨123,496255203,496255477⟩,
⟨128,517097854,517098138⟩]
theorem checked24800 : checkPrefixCuts (2^48) 3254517761 9 Manual.Count131072.C024800.packed 128 cuts24800 = true := by
 decide +kernel
def pointBounds24800 : List (Nat × Nat × Nat) := [(3254541312,102795074180444,102795456139070),(3254643712,102795478932264,102795860891111)]
theorem point_links_checked24800 : (cuts24800.take 2).map (fun c => (3254517761-1+2*2^9*c.k,102794982677061+c.lower,102795364635634+c.upper)) = pointBounds24800 := by
 decide +kernel
def cuts24801 : List PrefixCut := [⟨95,386318152,386318371⟩,
⟨128,517942114,517942410⟩]
theorem checked24801 : checkPrefixCuts (2^48) 3254648833 9 Manual.Count131072.C024801.packed 128 cuts24801 = true := by
 decide +kernel
def pointBounds24801 : List (Nat × Nat × Nat) := [(3254746112,102795886093067,102796268052143)]
theorem point_links_checked24801 : (cuts24801.take 1).map (fun c => (3254648833-1+2*2^9*c.k,102795499774915+c.lower,102795881733772+c.upper)) = pointBounds24801 := by
 decide +kernel
def cuts24802 : List PrefixCut := [⟨67,273275411,273275565⟩,
⟨128,513597281,513597572⟩]
theorem checked24802 : checkPrefixCuts (2^48) 3254779905 9 Manual.Count131072.C024802.packed 128 cuts24802 = true := by
 decide +kernel
def pointBounds24802 : List (Nat × Nat × Nat) := [(3254848512,102796290992440,102796672951747)]
theorem point_links_checked24802 : (cuts24802.take 1).map (fun c => (3254779905-1+2*2^9*c.k,102796017717029+c.lower,102796399676182+c.upper)) = pointBounds24802 := by
 decide +kernel
def cuts24803 : List PrefixCut := [⟨39,156003530,156003619⟩,
⟨128,514008824,514009111⟩]
theorem checked24803 : checkPrefixCuts (2^48) 3254910977 9 Manual.Count131072.C024803.packed 128 cuts24803 = true := by
 decide +kernel
def pointBounds24803 : List (Nat × Nat × Nat) := [(3254950912,102796687317840,102797069277373)]
theorem point_links_checked24803 : (cuts24803.take 1).map (fun c => (3254910977-1+2*2^9*c.k,102796531314310+c.lower,102796913273754+c.upper)) = pointBounds24803 := by
 decide +kernel
def cuts24804 : List PrefixCut := [⟨11,45398511,45398538⟩,
⟨111,456572152,456572413⟩,
⟨128,521597785,521598084⟩]
theorem checked24804 : checkPrefixCuts (2^48) 3255042049 9 Manual.Count131072.C024804.packed 128 cuts24804 = true := by
 decide +kernel
def pointBounds24804 : List (Nat × Nat × Nat) := [(3255053312,102797090721645,102797472681403),(3255155712,102797501895286,102797883855278)]
theorem point_links_checked24804 : (cuts24804.take 2).map (fun c => (3255042049-1+2*2^9*c.k,102797045323134+c.lower,102797427282865+c.upper)) = pointBounds24804 := by
 decide +kernel
def cuts24805 : List PrefixCut := [⟨83,333683453,333683639⟩,
⟨128,516042678,516042966⟩]
theorem checked24805 : checkPrefixCuts (2^48) 3255173121 9 Manual.Count131072.C024805.packed 128 cuts24805 = true := by
 decide +kernel
def pointBounds24805 : List (Nat × Nat × Nat) := [(3255258112,102797900604372,102798282564588)]
theorem point_links_checked24805 : (cuts24805.take 1).map (fun c => (3255173121-1+2*2^9*c.k,102797566920919+c.lower,102797948880949+c.upper)) = pointBounds24805 := by
 decide +kernel
def cuts24806 : List PrefixCut := [⟨55,227145658,227145789⟩,
⟨128,525273699,525273999⟩]
theorem checked24806 : checkPrefixCuts (2^48) 3255304193 9 Manual.Count131072.C024806.packed 128 cuts24806 = true := by
 decide +kernel
def pointBounds24806 : List (Nat × Nat × Nat) := [(3255360512,102798310109255,102798692069704)]
theorem point_links_checked24806 : (cuts24806.take 1).map (fun c => (3255304193-1+2*2^9*c.k,102798082963597+c.lower,102798464923915+c.upper)) = pointBounds24806 := by
 decide +kernel
def cuts24807 : List PrefixCut := [⟨27,108510681,108510742⟩,
⟨127,505193614,505193892⟩,
⟨128,509084296,509084576⟩]
theorem checked24807 : checkPrefixCuts (2^48) 3255435265 9 Manual.Count131072.C024807.packed 128 cuts24807 = true := by
 decide +kernel
def pointBounds24807 : List (Nat × Nat × Nat) := [(3255462912,102798716747977,102799098708656),(3255565312,102799113430910,102799495391806)]
theorem point_links_checked24807 : (cuts24807.take 2).map (fun c => (3255435265-1+2*2^9*c.k,102798608237296+c.lower,102798990197914+c.upper)) = pointBounds24807 := by
 decide +kernel
def cuts24808 : List PrefixCut := [⟨99,403759894,403760125⟩,
⟨128,526787490,526787789⟩]
theorem checked24808 : checkPrefixCuts (2^48) 3255566337 9 Manual.Count131072.C024808.packed 128 cuts24808 = true := by
 decide +kernel
def pointBounds24808 : List (Nat × Nat × Nat) := [(3255667712,102799521081486,102799903042615)]
theorem point_links_checked24808 : (cuts24808.take 1).map (fun c => (3255566337-1+2*2^9*c.k,102799117321592+c.lower,102799499282490+c.upper)) = pointBounds24808 := by
 decide +kernel
def cuts24809 : List PrefixCut := [⟨71,290575673,290575842⟩,
⟨128,521406217,521406518⟩]
theorem checked24809 : checkPrefixCuts (2^48) 3255697409 9 Manual.Count131072.C024809.packed 128 cuts24809 = true := by
 decide +kernel
def pointBounds24809 : List (Nat × Nat × Nat) := [(3255770112,102799934684755,102800316646121)]
theorem point_links_checked24809 : (cuts24809.take 1).map (fun c => (3255697409-1+2*2^9*c.k,102799644109082+c.lower,102800026070279+c.upper)) = pointBounds24809 := by
 decide +kernel
def cuts24810 : List PrefixCut := [⟨43,173076973,173077066⟩,
⟨128,515765948,515766232⟩]
theorem checked24810 : checkPrefixCuts (2^48) 3255828481 9 Manual.Count131072.C024810.packed 128 cuts24810 = true := by
 decide +kernel
def pointBounds24810 : List (Nat × Nat × Nat) := [(3255872512,102800338592272,102800720553863)]
theorem point_links_checked24810 : (cuts24810.take 1).map (fun c => (3255828481-1+2*2^9*c.k,102800165515299+c.lower,102800547476797+c.upper)) = pointBounds24810 := by
 decide +kernel
def cuts24811 : List PrefixCut := [⟨15,64490906,64490941⟩,
⟨115,466038887,466039147⟩,
⟨128,517992835,517993122⟩]
theorem checked24811 : checkPrefixCuts (2^48) 3255959553 9 Manual.Count131072.C024811.packed 128 cuts24811 = true := by
 decide +kernel
def pointBounds24811 : List (Nat × Nat × Nat) := [(3255974912,102800745772153,102801127733970),(3256077312,102801147320134,102801529282176)]
theorem point_links_checked24811 : (cuts24811.take 2).map (fun c => (3255959553-1+2*2^9*c.k,102800681281247+c.lower,102801063243029+c.upper)) = pointBounds24811 := by
 decide +kernel
def cuts24812 : List PrefixCut := [⟨87,350013675,350013872⟩,
⟨128,513909076,513909366⟩]
theorem checked24812 : checkPrefixCuts (2^48) 3256090625 9 Manual.Count131072.C024812.packed 128 cuts24812 = true := by
 decide +kernel
def pointBounds24812 : List (Nat × Nat × Nat) := [(3256179712,102801549287757,102801931250023)]
theorem point_links_checked24812 : (cuts24812.take 1).map (fun c => (3256090625-1+2*2^9*c.k,102801199274082+c.lower,102801581236151+c.upper)) = pointBounds24812 := by
 decide +kernel
def cuts24813 : List PrefixCut := [⟨59,239010383,239010512⟩,
⟨128,517951058,517951344⟩]
theorem checked24813 : checkPrefixCuts (2^48) 3256221697 9 Manual.Count131072.C024813.packed 128 cuts24813 = true := by
 decide +kernel
def pointBounds24813 : List (Nat × Nat × Nat) := [(3256282112,102801952193541,102802334156029)]
theorem point_links_checked24813 : (cuts24813.take 1).map (fun c => (3256221697-1+2*2^9*c.k,102801713183158+c.lower,102802095145517+c.upper)) = pointBounds24813 := by
 decide +kernel
def cuts24814 : List PrefixCut := [⟨31,122137281,122137351⟩,
⟨128,516201478,516201771⟩]
theorem checked24814 : checkPrefixCuts (2^48) 3256352769 9 Manual.Count131072.C024814.packed 128 cuts24814 = true := by
 decide +kernel
def pointBounds24814 : List (Nat × Nat × Nat) := [(3256384512,102802353271497,102802735234212)]
theorem point_links_checked24814 : (cuts24814.take 1).map (fun c => (3256352769-1+2*2^9*c.k,102802231134216+c.lower,102802613096861+c.upper)) = pointBounds24814 := by
 decide +kernel
def cuts24815 : List PrefixCut := [⟨3,11582314,11582321⟩,
⟨103,411597883,411598109⟩,
⟨128,512377687,512377969⟩]
theorem checked24815 : checkPrefixCuts (2^48) 3256483841 9 Manual.Count131072.C024815.packed 128 cuts24815 = true := by
 decide +kernel
def pointBounds24815 : List (Nat × Nat × Nat) := [(3256486912,102802758918008,102803140880953),(3256589312,102803158933577,102803540896741)]
theorem point_links_checked24815 : (cuts24815.take 2).map (fun c => (3256483841-1+2*2^9*c.k,102802747335694+c.lower,102803129298632+c.upper)) = pointBounds24815 := by
 decide +kernel
def cuts24816 : List PrefixCut := [⟨75,302766846,302767018⟩,
⟨128,518061462,518061755⟩]
theorem checked24816 : checkPrefixCuts (2^48) 3256614913 9 Manual.Count131072.C024816.packed 128 cuts24816 = true := by
 decide +kernel
def pointBounds24816 : List (Nat × Nat × Nat) := [(3256691712,102803562480227,102803944443619)]
theorem point_links_checked24816 : (cuts24816.take 1).map (fun c => (3256614913-1+2*2^9*c.k,102803259713381+c.lower,102803641676601+c.upper)) = pointBounds24816 := by
 decide +kernel
def cuts24817 : List PrefixCut := [⟨47,189622223,189622329⟩,
⟨128,518818415,518818701⟩]
theorem checked24817 : checkPrefixCuts (2^48) 3256745985 9 Manual.Count131072.C024817.packed 128 cuts24817 = true := by
 decide +kernel
def pointBounds24817 : List (Nat × Nat × Nat) := [(3256794112,102803967397066,102804349360685)]
theorem point_links_checked24817 : (cuts24817.take 1).map (fun c => (3256745985-1+2*2^9*c.k,102803777774843+c.lower,102804159738356+c.upper)) = pointBounds24817 := by
 decide +kernel
def cuts24818 : List PrefixCut := [⟨19,77436377,77436422⟩,
⟨119,475759608,475759881⟩,
⟨128,511451658,511451954⟩]
theorem checked24818 : checkPrefixCuts (2^48) 3256877057 9 Manual.Count131072.C024818.packed 128 cuts24818 = true := by
 decide +kernel
def pointBounds24818 : List (Nat × Nat × Nat) := [(3256896512,102804374029635,102804755993479),(3256998912,102804772352866,102805154316938)]
theorem point_links_checked24818 : (cuts24818.take 2).map (fun c => (3256877057-1+2*2^9*c.k,102804296593258+c.lower,102804678557057+c.upper)) = pointBounds24818 := by
 decide +kernel
def cuts24819 : List PrefixCut := [⟨91,361668029,361668224⟩,
⟨128,510307568,510307850⟩]
theorem checked24819 : checkPrefixCuts (2^48) 3257008129 9 Manual.Count131072.C024819.packed 128 cuts24819 = true := by
 decide +kernel
def pointBounds24819 : List (Nat × Nat × Nat) := [(3257101312,102805169712945,102805551677235)]
theorem point_links_checked24819 : (cuts24819.take 1).map (fun c => (3257008129-1+2*2^9*c.k,102804808044916+c.lower,102805190009011+c.upper)) = pointBounds24819 := by
 decide +kernel
def cuts24820 : List PrefixCut := [⟨63,248794449,248794591⟩,
⟨128,515299072,515299364⟩]
theorem checked24820 : checkPrefixCuts (2^48) 3257139201 9 Manual.Count131072.C024820.packed 128 cuts24820 = true := by
 decide +kernel
def pointBounds24820 : List (Nat × Nat × Nat) := [(3257203712,102805567146933,102805949111452)]
theorem point_links_checked24820 : (cuts24820.take 1).map (fun c => (3257139201-1+2*2^9*c.k,102805318352484+c.lower,102805700316861+c.upper)) = pointBounds24820 := by
 decide +kernel
def cuts24821 : List PrefixCut := [⟨35,141978017,141978096⟩,
⟨128,519685477,519685770⟩]
theorem checked24821 : checkPrefixCuts (2^48) 3257270273 9 Manual.Count131072.C024821.packed 128 cuts24821 = true := by
 decide +kernel
def pointBounds24821 : List (Nat × Nat × Nat) := [(3257306112,102805975629573,102806357594321)]
theorem point_links_checked24821 : (cuts24821.take 1).map (fun c => (3257270273-1+2*2^9*c.k,102805833651556+c.lower,102806215616225+c.upper)) = pointBounds24821 := by
 decide +kernel
def cuts24822 : List PrefixCut := [⟨7,27046574,27046590⟩,
⟨107,437577311,437577562⟩,
⟨128,524157810,524158112⟩]
theorem checked24822 : checkPrefixCuts (2^48) 3257401345 9 Manual.Count131072.C024822.packed 128 cuts24822 = true := by
 decide +kernel
def pointBounds24822 : List (Nat × Nat × Nat) := [(3257408512,102806380383607,102806762348585),(3257510912,102806790914344,102807172879557)]
theorem point_links_checked24822 : (cuts24822.take 2).map (fun c => (3257401345-1+2*2^9*c.k,102806353337033+c.lower,102806735301995+c.upper)) = pointBounds24822 := by
 decide +kernel
def cuts24823 : List PrefixCut := [⟨79,317456854,317457035⟩,
⟨128,516965053,516965347⟩]
theorem checked24823 : checkPrefixCuts (2^48) 3257532417 9 Manual.Count131072.C024823.packed 128 cuts24823 = true := by
 decide +kernel
def pointBounds24823 : List (Nat × Nat × Nat) := [(3257613312,102807194951697,102807576917142)]
theorem point_links_checked24823 : (cuts24823.take 1).map (fun c => (3257532417-1+2*2^9*c.k,102806877494843+c.lower,102807259460107+c.upper)) = pointBounds24823 := by
 decide +kernel
def cuts24824 : List PrefixCut := [⟨51,205639672,205639789⟩,
⟨128,518326703,518326992⟩]
theorem checked24824 : checkPrefixCuts (2^48) 3257663489 9 Manual.Count131072.C024824.packed 128 cuts24824 = true := by
 decide +kernel
def pointBounds24824 : List (Nat × Nat × Nat) := [(3257715712,102807600099568,102807982065243)]
theorem point_links_checked24824 : (cuts24824.take 1).map (fun c => (3257663489-1+2*2^9*c.k,102807394459896+c.lower,102807776425454+c.upper)) = pointBounds24824 := by
 decide +kernel
def cuts24825 : List PrefixCut := [⟨23,92880142,92880195⟩,
⟨123,496447314,496447593⟩,
⟨128,515973044,515973334⟩]
theorem checked24825 : checkPrefixCuts (2^48) 3257794561 9 Manual.Count131072.C024825.packed 128 cuts24825 = true := by
 decide +kernel
def pointBounds24825 : List (Nat × Nat × Nat) := [(3257818112,102808005666741,102808387632641),(3257920512,102808409233913,102808791200039)]
theorem point_links_checked24825 : (cuts24825.take 2).map (fun c => (3257794561-1+2*2^9*c.k,102807912786599+c.lower,102808294752446+c.upper)) = pointBounds24825 := by
 decide +kernel
def cuts24826 : List PrefixCut := [⟨95,386015903,386016114⟩,
⟨128,517075512,517075801⟩]
theorem checked24826 : checkPrefixCuts (2^48) 3257925633 9 Manual.Count131072.C024826.packed 128 cuts24826 = true := by
 decide +kernel
def pointBounds24826 : List (Nat × Nat × Nat) := [(3258022912,102808814775546,102809196741894)]
theorem point_links_checked24826 : (cuts24826.take 1).map (fun c => (3257925633-1+2*2^9*c.k,102808428759643+c.lower,102808810725780+c.upper)) = pointBounds24826 := by
 decide +kernel
def cuts24827 : List PrefixCut := [⟨67,270063233,270063384⟩,
⟨128,516363561,516363861⟩]
theorem checked24827 : checkPrefixCuts (2^48) 3258056705 9 Manual.Count131072.C024827.packed 128 cuts24827 = true := by
 decide +kernel
def pointBounds24827 : List (Nat × Nat × Nat) := [(3258125312,102809215898388,102809597864965)]
theorem point_links_checked24827 : (cuts24827.take 1).map (fun c => (3258056705-1+2*2^9*c.k,102808945835155+c.lower,102809327801581+c.upper)) = pointBounds24827 := by
 decide +kernel
def cuts24828 : List PrefixCut := [⟨39,156624147,156624232⟩,
⟨128,524549550,524549839⟩]
theorem checked24828 : checkPrefixCuts (2^48) 3258187777 9 Manual.Count131072.C024828.packed 128 cuts24828 = true := by
 decide +kernel
def pointBounds24828 : List (Nat × Nat × Nat) := [(3258227712,102809618822863,102810000789674)]
theorem point_links_checked24828 : (cuts24828.take 1).map (fun c => (3258187777-1+2*2^9*c.k,102809462198716+c.lower,102809844165442+c.upper)) = pointBounds24828 := by
 decide +kernel
def cuts24829 : List PrefixCut := [⟨11,44920923,44920947⟩,
⟨111,450411629,450411882⟩,
⟨128,516494853,516495143⟩]
theorem checked24829 : checkPrefixCuts (2^48) 3258318849 9 Manual.Count131072.C024829.packed 128 cuts24829 = true := by
 decide +kernel
def pointBounds24829 : List (Nat × Nat × Nat) := [(3258330112,102810031669189,102810413636228),(3258432512,102810437159895,102810819127163)]
theorem point_links_checked24829 : (cuts24829.take 2).map (fun c => (3258318849-1+2*2^9*c.k,102809986748266+c.lower,102810368715281+c.upper)) = pointBounds24829 := by
 decide +kernel
def cuts24830 : List PrefixCut := [⟨83,331706645,331706835⟩,
⟨128,515005435,515005731⟩]
theorem checked24830 : checkPrefixCuts (2^48) 3258449921 9 Manual.Count131072.C024830.packed 128 cuts24830 = true := by
 decide +kernel
def pointBounds24830 : List (Nat × Nat × Nat) := [(3258534912,102810834949764,102811216917259)]
theorem point_links_checked24830 : (cuts24830.take 1).map (fun c => (3258449921-1+2*2^9*c.k,102810503243119+c.lower,102810885210424+c.upper)) = pointBounds24830 := by
 decide +kernel
def cuts24831 : List PrefixCut := [⟨55,217588285,217588411⟩,
⟨128,513170708,513170999⟩]
theorem checked24831 : checkPrefixCuts (2^48) 3258580993 9 Manual.Count131072.C024831.packed 128 cuts24831 = true := by
 decide +kernel
def pointBounds24831 : List (Nat × Nat × Nat) := [(3258637312,102811235836839,102811617804566)]
theorem point_links_checked24831 : (cuts24831.take 1).map (fun c => (3258580993-1+2*2^9*c.k,102811018248554+c.lower,102811400216155+c.upper)) = pointBounds24831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000150
