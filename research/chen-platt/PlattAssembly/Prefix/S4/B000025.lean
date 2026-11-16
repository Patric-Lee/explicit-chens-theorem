import PlattAssemblyKernel
import PlattCertificates.Count131072.C030800
import PlattCertificates.Count131072.C030801
import PlattCertificates.Count131072.C030802
import PlattCertificates.Count131072.C030803
import PlattCertificates.Count131072.C030804
import PlattCertificates.Count131072.C030805
import PlattCertificates.Count131072.C030806
import PlattCertificates.Count131072.C030807
import PlattCertificates.Count131072.C030808
import PlattCertificates.Count131072.C030809
import PlattCertificates.Count131072.C030810
import PlattCertificates.Count131072.C030811
import PlattCertificates.Count131072.C030812
import PlattCertificates.Count131072.C030813
import PlattCertificates.Count131072.C030814
import PlattCertificates.Count131072.C030815
import PlattCertificates.Count131072.C030816
import PlattCertificates.Count131072.C030817
import PlattCertificates.Count131072.C030818
import PlattCertificates.Count131072.C030819
import PlattCertificates.Count131072.C030820
import PlattCertificates.Count131072.C030821
import PlattCertificates.Count131072.C030822
import PlattCertificates.Count131072.C030823
import PlattCertificates.Count131072.C030824
import PlattCertificates.Count131072.C030825
import PlattCertificates.Count131072.C030826
import PlattCertificates.Count131072.C030827
import PlattCertificates.Count131072.C030828
import PlattCertificates.Count131072.C030829
import PlattCertificates.Count131072.C030830
import PlattCertificates.Count131072.C030831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30800 : List PrefixCut := [⟨31,100025086,100025145⟩,
⟨128,410404325,410404559⟩]
theorem checked30800 : checkPrefixCuts (2^48) 4040949761 9 Manual.Count131072.C030800.packed 128 cuts30800 = true := by
 decide +kernel
def pointBounds30800 : List (Nat × Nat × Nat) := [(4040981504,105562783570339,105563167079878)]
theorem point_links_checked30800 : (cuts30800.take 1).map (fun c => (4040949761-1+2*2^9*c.k,105562683545253+c.lower,105563067054733+c.upper)) = pointBounds30800 := by
 decide +kernel
def cuts30801 : List PrefixCut := [⟨27,89086360,89086408⟩,
⟨128,413107502,413107737⟩]
theorem checked30801 : checkPrefixCuts (2^48) 4041080833 9 Manual.Count131072.C030801.packed 128 cuts30801 = true := by
 decide +kernel
def pointBounds30801 : List (Nat × Nat × Nat) := [(4041108480,105563183035938,105563566545700)]
theorem point_links_checked30801 : (cuts30801.take 1).map (fun c => (4041080833-1+2*2^9*c.k,105563093949578+c.lower,105563477459292+c.upper)) = pointBounds30801 := by
 decide +kernel
def cuts30802 : List PrefixCut := [⟨23,71879734,71879773⟩,
⟨128,408357811,408358037⟩]
theorem checked30802 : checkPrefixCuts (2^48) 4041211905 9 Manual.Count131072.C030802.packed 128 cuts30802 = true := by
 decide +kernel
def pointBounds30802 : List (Nat × Nat × Nat) := [(4041235456,105563578936814,105563962446802)]
theorem point_links_checked30802 : (cuts30802.take 1).map (fun c => (4041211905-1+2*2^9*c.k,105563507057080+c.lower,105563890567029+c.upper)) = pointBounds30802 := by
 decide +kernel
def cuts30803 : List PrefixCut := [⟨19,59967519,59967553⟩,
⟨128,412593083,412593316⟩]
theorem checked30803 : checkPrefixCuts (2^48) 4041342977 9 Manual.Count131072.C030803.packed 128 cuts30803 = true := by
 decide +kernel
def pointBounds30803 : List (Nat × Nat × Nat) := [(4041362432,105563975382410,105564358892619)]
theorem point_links_checked30803 : (cuts30803.take 1).map (fun c => (4041342977-1+2*2^9*c.k,105563915414891+c.lower,105564298925066+c.upper)) = pointBounds30803 := by
 decide +kernel
def cuts30804 : List PrefixCut := [⟨15,47777469,47777499⟩,
⟨128,415365539,415365774⟩]
theorem checked30804 : checkPrefixCuts (2^48) 4041474049 9 Manual.Count131072.C030804.packed 128 cuts30804 = true := by
 decide +kernel
def pointBounds30804 : List (Nat × Nat × Nat) := [(4041489408,105564375785443,105564759295881)]
theorem point_links_checked30804 : (cuts30804.take 1).map (fun c => (4041474049-1+2*2^9*c.k,105564328007974+c.lower,105564711518382+c.upper)) = pointBounds30804 := by
 decide +kernel
def cuts30805 : List PrefixCut := [⟨11,36284649,36284668⟩,
⟨128,420853879,420854105⟩]
theorem checked30805 : checkPrefixCuts (2^48) 4041605121 9 Manual.Count131072.C030805.packed 128 cuts30805 = true := by
 decide +kernel
def pointBounds30805 : List (Nat × Nat × Nat) := [(4041616384,105564779658162,105565163168824)]
theorem point_links_checked30805 : (cuts30805.take 1).map (fun c => (4041605121-1+2*2^9*c.k,105564743373513+c.lower,105565126884156+c.upper)) = pointBounds30805 := by
 decide +kernel
def cuts30806 : List PrefixCut := [⟨7,22494371,22494382⟩,
⟨128,413806504,413806737⟩]
theorem checked30806 : checkPrefixCuts (2^48) 4041736193 9 Manual.Count131072.C030806.packed 128 cuts30806 = true := by
 decide +kernel
def pointBounds30806 : List (Nat × Nat × Nat) := [(4041743360,105565186721763,105565570232643)]
theorem point_links_checked30806 : (cuts30806.take 1).map (fun c => (4041736193-1+2*2^9*c.k,105565164227392+c.lower,105565547738261+c.upper)) = pointBounds30806 := by
 decide +kernel
def cuts30807 : List PrefixCut := [⟨3,9331732,9331738⟩,
⟨127,408639883,408640109⟩,
⟨128,411773574,411773801⟩]
theorem checked30807 : checkPrefixCuts (2^48) 4041867265 9 Manual.Count131072.C030807.packed 128 cuts30807 = true := by
 decide +kernel
def pointBounds30807 : List (Nat × Nat × Nat) := [(4041870336,105565587365628,105565970876736),(4041997312,105565986673779,105566370185107)]
theorem point_links_checked30807 : (cuts30807.take 2).map (fun c => (4041867265-1+2*2^9*c.k,105565578033896+c.lower,105565961544998+c.upper)) = pointBounds30807 := by
 decide +kernel
def cuts30808 : List PrefixCut := [⟨123,395744087,395744310⟩,
⟨128,411620946,411621178⟩]
theorem checked30808 : checkPrefixCuts (2^48) 4041998337 9 Manual.Count131072.C030808.packed 128 cuts30808 = true := by
 decide +kernel
def pointBounds30808 : List (Nat × Nat × Nat) := [(4042124288,105566385551557,105566769063109)]
theorem point_links_checked30808 : (cuts30808.take 1).map (fun c => (4041998337-1+2*2^9*c.k,105565989807470+c.lower,105566373318799+c.upper)) = pointBounds30808 := by
 decide +kernel
def cuts30809 : List PrefixCut := [⟨119,387375355,387375569⟩,
⟨128,416412367,416412596⟩]
theorem checked30809 : checkPrefixCuts (2^48) 4042129409 9 Manual.Count131072.C030809.packed 128 cuts30809 = true := by
 decide +kernel
def pointBounds30809 : List (Nat × Nat × Nat) := [(4042251264,105566788803771,105567172315546)]
theorem point_links_checked30809 : (cuts30809.take 1).map (fun c => (4042129409-1+2*2^9*c.k,105566401428416+c.lower,105566784939977+c.upper)) = pointBounds30809 := by
 decide +kernel
def cuts30810 : List PrefixCut := [⟨115,372740281,372740487⟩,
⟨128,414588452,414588680⟩]
theorem checked30810 : checkPrefixCuts (2^48) 4042260481 9 Manual.Count131072.C030810.packed 128 cuts30810 = true := by
 decide +kernel
def pointBounds30810 : List (Nat × Nat × Nat) := [(4042378240,105567190581064,105567574093060)]
theorem point_links_checked30810 : (cuts30810.take 1).map (fun c => (4042260481-1+2*2^9*c.k,105566817840783+c.lower,105567201352573+c.upper)) = pointBounds30810 := by
 decide +kernel
def cuts30811 : List PrefixCut := [⟨111,361657173,361657375⟩,
⟨128,415271253,415271485⟩]
theorem checked30811 : checkPrefixCuts (2^48) 4042391553 9 Manual.Count131072.C030811.packed 128 cuts30811 = true := by
 decide +kernel
def pointBounds30811 : List (Nat × Nat × Nat) := [(4042505216,105567594086408,105567977598628)]
theorem point_links_checked30811 : (cuts30811.take 1).map (fun c => (4042391553-1+2*2^9*c.k,105567232429235+c.lower,105567615941253+c.upper)) = pointBounds30811 := by
 decide +kernel
def cuts30812 : List PrefixCut := [⟨107,347372023,347372216⟩,
⟨128,416302211,416302442⟩]
theorem checked30812 : checkPrefixCuts (2^48) 4042522625 9 Manual.Count131072.C030812.packed 128 cuts30812 = true := by
 decide +kernel
def pointBounds30812 : List (Nat × Nat × Nat) := [(4042632192,105567995072511,105568378584954)]
theorem point_links_checked30812 : (cuts30812.take 1).map (fun c => (4042522625-1+2*2^9*c.k,105567647700488+c.lower,105568031212738+c.upper)) = pointBounds30812 := by
 decide +kernel
def cuts30813 : List PrefixCut := [⟨103,333157380,333157569⟩,
⟨128,415244355,415244592⟩]
theorem checked30813 : checkPrefixCuts (2^48) 4042653697 9 Manual.Count131072.C030813.packed 128 cuts30813 = true := by
 decide +kernel
def pointBounds30813 : List (Nat × Nat × Nat) := [(4042759168,105568397160079,105568780672749)]
theorem point_links_checked30813 : (cuts30813.take 1).map (fun c => (4042653697-1+2*2^9*c.k,105568064002699+c.lower,105568447515180+c.upper)) = pointBounds30813 := by
 decide +kernel
def cuts30814 : List PrefixCut := [⟨99,323608319,323608502⟩,
⟨128,418294249,418294485⟩]
theorem checked30814 : checkPrefixCuts (2^48) 4042784769 9 Manual.Count131072.C030814.packed 128 cuts30814 = true := by
 decide +kernel
def pointBounds30814 : List (Nat × Nat × Nat) := [(4042886144,105568802855373,105569186368274)]
theorem point_links_checked30814 : (cuts30814.take 1).map (fun c => (4042784769-1+2*2^9*c.k,105568479247054+c.lower,105568862759772+c.upper)) = pointBounds30814 := by
 decide +kernel
def cuts30815 : List PrefixCut := [⟨95,306053515,306053688⟩,
⟨128,410692054,410692287⟩]
theorem checked30815 : checkPrefixCuts (2^48) 4042915841 9 Manual.Count131072.C030815.packed 128 cuts30815 = true := by
 decide +kernel
def pointBounds30815 : List (Nat × Nat × Nat) := [(4043013120,105569203594818,105569587107945)]
theorem point_links_checked30815 : (cuts30815.take 1).map (fun c => (4042915841-1+2*2^9*c.k,105568897541303+c.lower,105569281054257+c.upper)) = pointBounds30815 := by
 decide +kernel
def cuts30816 : List PrefixCut := [⟨91,288917611,288917772⟩,
⟨128,407685185,407685414⟩]
theorem checked30816 : checkPrefixCuts (2^48) 4043046913 9 Manual.Count131072.C030816.packed 128 cuts30816 = true := by
 decide +kernel
def pointBounds30816 : List (Nat × Nat × Nat) := [(4043140096,105569597150968,105569980664316)]
theorem point_links_checked30816 : (cuts30816.take 1).map (fun c => (4043046913-1+2*2^9*c.k,105569308233357+c.lower,105569691746544+c.upper)) = pointBounds30816 := by
 decide +kernel
def cuts30817 : List PrefixCut := [⟨87,272130781,272130936⟩,
⟨128,405165696,405165927⟩]
theorem checked30817 : checkPrefixCuts (2^48) 4043177985 9 Manual.Count131072.C030817.packed 128 cuts30817 = true := by
 decide +kernel
def pointBounds30817 : List (Nat × Nat × Nat) := [(4043267072,105569988049323,105570371562894)]
theorem point_links_checked30817 : (cuts30817.take 1).map (fun c => (4043177985-1+2*2^9*c.k,105569715918542+c.lower,105570099431958+c.upper)) = pointBounds30817 := by
 decide +kernel
def cuts30818 : List PrefixCut := [⟨83,268293340,268293491⟩,
⟨128,416290845,416291075⟩]
theorem checked30818 : checkPrefixCuts (2^48) 4043309057 9 Manual.Count131072.C030818.packed 128 cuts30818 = true := by
 decide +kernel
def pointBounds30818 : List (Nat × Nat × Nat) := [(4043394048,105570389377578,105570772891376)]
theorem point_links_checked30818 : (cuts30818.take 1).map (fun c => (4043309057-1+2*2^9*c.k,105570121084238+c.lower,105570504597885+c.upper)) = pointBounds30818 := by
 decide +kernel
def cuts30819 : List PrefixCut := [⟨79,253387802,253387947⟩,
⟨128,408411285,408411520⟩]
theorem checked30819 : checkPrefixCuts (2^48) 4043440129 9 Manual.Count131072.C030819.packed 128 cuts30819 = true := by
 decide +kernel
def pointBounds30819 : List (Nat × Nat × Nat) := [(4043521024,105570790762885,105571174276907)]
theorem point_links_checked30819 : (cuts30819.take 1).map (fun c => (4043440129-1+2*2^9*c.k,105570537375083+c.lower,105570920888960+c.upper)) = pointBounds30819 := by
 decide +kernel
def cuts30820 : List PrefixCut := [⟨75,238900858,238900988⟩,
⟨128,411460763,411460991⟩]
theorem checked30820 : checkPrefixCuts (2^48) 4043571201 9 Manual.Count131072.C030820.packed 128 cuts30820 = true := by
 decide +kernel
def pointBounds30820 : List (Nat × Nat × Nat) := [(4043648000,105571184687226,105571568201468)]
theorem point_links_checked30820 : (cuts30820.take 1).map (fun c => (4043571201-1+2*2^9*c.k,105570945786368+c.lower,105571329300480+c.upper)) = pointBounds30820 := by
 decide +kernel
def cuts30821 : List PrefixCut := [⟨71,231027577,231027704⟩,
⟨128,413187673,413187898⟩]
theorem checked30821 : checkPrefixCuts (2^48) 4043702273 9 Manual.Count131072.C030821.packed 128 cuts30821 = true := by
 decide +kernel
def pointBounds30821 : List (Nat × Nat × Nat) := [(4043774976,105571588274708,105571971789175)]
theorem point_links_checked30821 : (cuts30821.take 1).map (fun c => (4043702273-1+2*2^9*c.k,105571357247131+c.lower,105571740761471+c.upper)) = pointBounds30821 := by
 decide +kernel
def cuts30822 : List PrefixCut := [⟨67,215637420,215637546⟩,
⟨128,409415629,409415863⟩]
theorem checked30822 : checkPrefixCuts (2^48) 4043833345 9 Manual.Count131072.C030822.packed 128 cuts30822 = true := by
 decide +kernel
def pointBounds30822 : List (Nat × Nat × Nat) := [(4043901952,105571986072224,105572369586915)]
theorem point_links_checked30822 : (cuts30822.take 1).map (fun c => (4043833345-1+2*2^9*c.k,105571770434804+c.lower,105572153949369+c.upper)) = pointBounds30822 := by
 decide +kernel
def cuts30823 : List PrefixCut := [⟨63,200387444,200387555⟩,
⟨128,411490358,411490581⟩]
theorem checked30823 : checkPrefixCuts (2^48) 4043964417 9 Manual.Count131072.C030823.packed 128 cuts30823 = true := by
 decide +kernel
def pointBounds30823 : List (Nat × Nat × Nat) := [(4044028928,105572380237877,105572763752787)]
theorem point_links_checked30823 : (cuts30823.take 1).map (fun c => (4043964417-1+2*2^9*c.k,105572179850433+c.lower,105572563365232+c.upper)) = pointBounds30823 := by
 decide +kernel
def cuts30824 : List PrefixCut := [⟨59,189453733,189453835⟩,
⟨128,415096281,415096509⟩]
theorem checked30824 : checkPrefixCuts (2^48) 4044095489 9 Manual.Count131072.C030824.packed 128 cuts30824 = true := by
 decide +kernel
def pointBounds30824 : List (Nat × Nat × Nat) := [(4044155904,105572780794524,105573164309648)]
theorem point_links_checked30824 : (cuts30824.take 1).map (fun c => (4044095489-1+2*2^9*c.k,105572591340791+c.lower,105572974855813+c.upper)) = pointBounds30824 := by
 decide +kernel
def cuts30825 : List PrefixCut := [⟨55,171352016,171352112⟩,
⟨128,404086329,404086554⟩]
theorem checked30825 : checkPrefixCuts (2^48) 4044226561 9 Manual.Count131072.C030825.packed 128 cuts30825 = true := by
 decide +kernel
def pointBounds30825 : List (Nat × Nat × Nat) := [(4044282880,105573177789088,105573561304434)]
theorem point_links_checked30825 : (cuts30825.take 1).map (fun c => (4044226561-1+2*2^9*c.k,105573006437072+c.lower,105573389952322+c.upper)) = pointBounds30825 := by
 decide +kernel
def cuts30826 : List PrefixCut := [⟨51,164108516,164108610⟩,
⟨128,413886255,413886487⟩]
theorem checked30826 : checkPrefixCuts (2^48) 4044357633 9 Manual.Count131072.C030826.packed 128 cuts30826 = true := by
 decide +kernel
def pointBounds30826 : List (Nat × Nat × Nat) := [(4044409856,105573574631917,105573958147486)]
theorem point_links_checked30826 : (cuts30826.take 1).map (fun c => (4044357633-1+2*2^9*c.k,105573410523401+c.lower,105573794038876+c.upper)) = pointBounds30826 := by
 decide +kernel
def cuts30827 : List PrefixCut := [⟨47,151297942,151298025⟩,
⟨128,407261481,407261711⟩]
theorem checked30827 : checkPrefixCuts (2^48) 4044488705 9 Manual.Count131072.C030827.packed 128 cuts30827 = true := by
 decide +kernel
def pointBounds30827 : List (Nat × Nat × Nat) := [(4044536832,105573975707598,105574359223388)]
theorem point_links_checked30827 : (cuts30827.take 1).map (fun c => (4044488705-1+2*2^9*c.k,105573824409656+c.lower,105574207925363+c.upper)) = pointBounds30827 := by
 decide +kernel
def cuts30828 : List PrefixCut := [⟨43,141341448,141341525⟩,
⟨128,412328495,412328721⟩]
theorem checked30828 : checkPrefixCuts (2^48) 4044619777 9 Manual.Count131072.C030828.packed 128 cuts30828 = true := by
 decide +kernel
def pointBounds30828 : List (Nat × Nat × Nat) := [(4044663808,105574373012585,105574756528599)]
theorem point_links_checked30828 : (cuts30828.take 1).map (fun c => (4044619777-1+2*2^9*c.k,105574231671137+c.lower,105574615187074+c.upper)) = pointBounds30828 := by
 decide +kernel
def cuts30829 : List PrefixCut := [⟨39,126862243,126862312⟩,
⟨128,415585724,415585957⟩]
theorem checked30829 : checkPrefixCuts (2^48) 4044750849 9 Manual.Count131072.C030829.packed 128 cuts30829 = true := by
 decide +kernel
def pointBounds30829 : List (Nat × Nat × Nat) := [(4044790784,105574770861875,105575154378107)]
theorem point_links_checked30829 : (cuts30829.take 1).map (fun c => (4044750849-1+2*2^9*c.k,105574643999632+c.lower,105575027515795+c.upper)) = pointBounds30829 := by
 decide +kernel
def cuts30830 : List PrefixCut := [⟨35,112453577,112453639⟩,
⟨128,408961566,408961795⟩]
theorem checked30830 : checkPrefixCuts (2^48) 4044881921 9 Manual.Count131072.C030830.packed 128 cuts30830 = true := by
 decide +kernel
def pointBounds30830 : List (Nat × Nat × Nat) := [(4044917760,105575172038933,105575555555391)]
theorem point_links_checked30830 : (cuts30830.take 1).map (fun c => (4044881921-1+2*2^9*c.k,105575059585356+c.lower,105575443101752+c.upper)) = pointBounds30830 := by
 decide +kernel
def cuts30831 : List PrefixCut := [⟨31,97002022,97002081⟩,
⟨128,407208660,407208899⟩]
theorem checked30831 : checkPrefixCuts (2^48) 4045012993 9 Manual.Count131072.C030831.packed 128 cuts30831 = true := by
 decide +kernel
def pointBounds30831 : List (Nat × Nat × Nat) := [(4045044736,105575565548944,105575949065628)]
theorem point_links_checked30831 : (cuts30831.take 1).map (fun c => (4045012993-1+2*2^9*c.k,105575468546922+c.lower,105575852063547+c.upper)) = pointBounds30831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000025
