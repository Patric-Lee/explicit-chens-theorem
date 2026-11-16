import PlattAssemblyKernel
import PlattCertificates.Count131072.C018800
import PlattCertificates.Count131072.C018801
import PlattCertificates.Count131072.C018802
import PlattCertificates.Count131072.C018803
import PlattCertificates.Count131072.C018804
import PlattCertificates.Count131072.C018805
import PlattCertificates.Count131072.C018806
import PlattCertificates.Count131072.C018807
import PlattCertificates.Count131072.C018808
import PlattCertificates.Count131072.C018809
import PlattCertificates.Count131072.C018810
import PlattCertificates.Count131072.C018811
import PlattCertificates.Count131072.C018812
import PlattCertificates.Count131072.C018813
import PlattCertificates.Count131072.C018814
import PlattCertificates.Count131072.C018815
import PlattCertificates.Count131072.C018816
import PlattCertificates.Count131072.C018817
import PlattCertificates.Count131072.C018818
import PlattCertificates.Count131072.C018819
import PlattCertificates.Count131072.C018820
import PlattCertificates.Count131072.C018821
import PlattCertificates.Count131072.C018822
import PlattCertificates.Count131072.C018823
import PlattCertificates.Count131072.C018824
import PlattCertificates.Count131072.C018825
import PlattCertificates.Count131072.C018826
import PlattCertificates.Count131072.C018827
import PlattCertificates.Count131072.C018828
import PlattCertificates.Count131072.C018829
import PlattCertificates.Count131072.C018830
import PlattCertificates.Count131072.C018831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000275
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18800 : List PrefixCut := [⟨62,334378004,334378208⟩,
⟨128,691669589,691670007⟩]
theorem checked18800 : checkPrefixCuts (2^48) 2468085761 9 Manual.Count131072.C018800.packed 128 cuts18800 = true := by
 decide +kernel
def pointBounds18800 : List (Nat × Nat × Nat) := [(2468149248,99218122046978,99218501939947)]
theorem point_links_checked18800 : (cuts18800.take 1).map (fun c => (2468085761-1+2*2^9*c.k,99217787668974+c.lower,99218167561739+c.upper)) = pointBounds18800 := by
 decide +kernel
def cuts18801 : List PrefixCut := [⟨10,52344155,52344186⟩,
⟨86,465159805,465160087⟩,
⟨128,692430996,692431413⟩]
theorem checked18801 : checkPrefixCuts (2^48) 2468216833 9 Manual.Count131072.C018801.packed 128 cuts18801 = true := by
 decide +kernel
def pointBounds18801 : List (Nat × Nat × Nat) := [(2468227072,99218531682718,99218911575932),(2468304896,99218944498368,99219324391833)]
theorem point_links_checked18801 : (cuts18801.take 2).map (fun c => (2468216833-1+2*2^9*c.k,99218479338563+c.lower,99218859231746+c.upper)) = pointBounds18801 := by
 decide +kernel
def cuts18802 : List PrefixCut := [⟨34,180856214,180856327⟩,
⟨110,592163652,592164012⟩,
⟨128,688403360,688403781⟩]
theorem checked18802 : checkPrefixCuts (2^48) 2468347905 9 Manual.Count131072.C018802.packed 128 cuts18802 = true := by
 decide +kernel
def pointBounds18802 : List (Nat × Nat × Nat) := [(2468382720,99219352625773,99219732519486),(2468460544,99219763933211,99220143827171)]
theorem point_links_checked18802 : (cuts18802.take 2).map (fun c => (2468347905-1+2*2^9*c.k,99219171769559+c.lower,99219551663159+c.upper)) = pointBounds18802 := by
 decide +kernel
def cuts18803 : List PrefixCut := [⟨58,318703469,318703660⟩,
⟨128,694524124,694524539⟩]
theorem checked18803 : checkPrefixCuts (2^48) 2468478977 9 Manual.Count131072.C018803.packed 128 cuts18803 = true := by
 decide +kernel
def pointBounds18803 : List (Nat × Nat × Nat) := [(2468538368,99220178876388,99220558770600)]
theorem point_links_checked18803 : (cuts18803.take 1).map (fun c => (2468478977-1+2*2^9*c.k,99219860172919+c.lower,99220240066940+c.upper)) = pointBounds18803 := by
 decide +kernel
def cuts18804 : List PrefixCut := [⟨6,33636333,33636351⟩,
⟨82,444334714,444334986⟩,
⟨128,686506045,686506461⟩]
theorem checked18804 : checkPrefixCuts (2^48) 2468610049 9 Manual.Count131072.C018804.packed 128 cuts18804 = true := by
 decide +kernel
def pointBounds18804 : List (Nat × Nat × Nat) := [(2468616192,99220588333376,99220968227830),(2468694016,99220999031757,99221378926465)]
theorem point_links_checked18804 : (cuts18804.take 2).map (fun c => (2468610049-1+2*2^9*c.k,99220554697043+c.lower,99220934591479+c.upper)) = pointBounds18804 := by
 decide +kernel
def cuts18805 : List PrefixCut := [⟨30,157796554,157796646⟩,
⟨106,570293203,570293543⟩,
⟨128,692511950,692512359⟩]
theorem checked18805 : checkPrefixCuts (2^48) 2468741121 9 Manual.Count131072.C018805.packed 128 cuts18805 = true := by
 decide +kernel
def pointBounds18805 : List (Nat × Nat × Nat) := [(2468771840,99221398999642,99221778894586),(2468849664,99221811496291,99222191391483)]
theorem point_links_checked18805 : (cuts18805.take 2).map (fun c => (2468741121-1+2*2^9*c.k,99221241203088+c.lower,99221621097940+c.upper)) = pointBounds18805 := by
 decide +kernel
def cuts18806 : List PrefixCut := [⟨54,292317098,292317273⟩,
⟨128,686547076,686547488⟩]
theorem checked18806 : checkPrefixCuts (2^48) 2468872193 9 Manual.Count131072.C018806.packed 128 cuts18806 = true := by
 decide +kernel
def pointBounds18806 : List (Nat × Nat × Nat) := [(2468927488,99222226032136,99222605927572)]
theorem point_links_checked18806 : (cuts18806.take 1).map (fun c => (2468872193-1+2*2^9*c.k,99221933715038+c.lower,99222313610299+c.upper)) = pointBounds18806 := by
 decide +kernel
def cuts18807 : List PrefixCut := [⟨2,10944326,10944334⟩,
⟨78,410405844,410406087⟩,
⟨128,678644492,678644893⟩]
theorem checked18807 : checkPrefixCuts (2^48) 2469003265 9 Manual.Count131072.C018807.packed 128 cuts18807 = true := by
 decide +kernel
def pointBounds18807 : List (Nat × Nat × Nat) := [(2469005312,99222631206440,99223011102121),(2469083136,99223030667958,99223410563874)]
theorem point_links_checked18807 : (cuts18807.take 2).map (fun c => (2469003265-1+2*2^9*c.k,99222620262114+c.lower,99223000157787+c.upper)) = pointBounds18807 := by
 decide +kernel
def cuts18808 : List PrefixCut := [⟨26,143179961,143180042⟩,
⟨102,553901724,553902053⟩,
⟨128,696505668,696506081⟩]
theorem checked18808 : checkPrefixCuts (2^48) 2469134337 9 Manual.Count131072.C018808.packed 128 cuts18808 = true := by
 decide +kernel
def pointBounds18808 : List (Nat × Nat × Nat) := [(2469160960,99223442086567,99223821982722),(2469238784,99223852808330,99224232704733)]
theorem point_links_checked18808 : (cuts18808.take 2).map (fun c => (2469134337-1+2*2^9*c.k,99223298906606+c.lower,99223678802680+c.upper)) = pointBounds18808 := by
 decide +kernel
def cuts18809 : List PrefixCut := [⟨50,267648898,267649061⟩,
⟨126,673329382,673329791⟩,
⟨128,684044004,684044420⟩]
theorem checked18809 : checkPrefixCuts (2^48) 2469265409 9 Manual.Count131072.C018809.packed 128 cuts18809 = true := by
 decide +kernel
def pointBounds18809 : List (Nat × Nat × Nat) := [(2469316608,99224263061172,99224642957822),(2469394432,99224668741656,99225048638552)]
theorem point_links_checked18809 : (cuts18809.take 2).map (fun c => (2469265409-1+2*2^9*c.k,99223995412274+c.lower,99224375308761+c.upper)) = pointBounds18809 := by
 decide +kernel
def cuts18810 : List PrefixCut := [⟨74,395978843,395979082⟩,
⟨128,686287243,686287653⟩]
theorem checked18810 : checkPrefixCuts (2^48) 2469396481 9 Manual.Count131072.C018810.packed 128 cuts18810 = true := by
 decide +kernel
def pointBounds18810 : List (Nat × Nat × Nat) := [(2469472256,99225075435121,99225455332263)]
theorem point_links_checked18810 : (cuts18810.take 1).map (fun c => (2469396481-1+2*2^9*c.k,99224679456278+c.lower,99225059353181+c.upper)) = pointBounds18810 := by
 decide +kernel
def cuts18811 : List PrefixCut := [⟨22,124350780,124350853⟩,
⟨98,544353864,544354188⟩,
⟨128,712807297,712807718⟩]
theorem checked18811 : checkPrefixCuts (2^48) 2469527553 9 Manual.Count131072.C018811.packed 128 cuts18811 = true := by
 decide +kernel
def pointBounds18811 : List (Nat × Nat × Nat) := [(2469550080,99225490094301,99225869991687),(2469627904,99225910097385,99226289995022)]
theorem point_links_checked18811 : (cuts18811.take 2).map (fun c => (2469527553-1+2*2^9*c.k,99225365743521+c.lower,99225745640834+c.upper)) = pointBounds18811 := by
 decide +kernel
def cuts18812 : List PrefixCut := [⟨46,253701901,253702052⟩,
⟨122,667866003,667866404⟩,
⟨128,700004779,700005199⟩]
theorem checked18812 : checkPrefixCuts (2^48) 2469658625 9 Manual.Count131072.C018812.packed 128 cuts18812 = true := by
 decide +kernel
def pointBounds18812 : List (Nat × Nat × Nat) := [(2469705728,99226332252719,99226712150604),(2469783552,99226746416821,99227126314956)]
theorem point_links_checked18812 : (cuts18812.take 2).map (fun c => (2469658625-1+2*2^9*c.k,99226078550818+c.lower,99226458448552+c.upper)) = pointBounds18812 := by
 decide +kernel
def cuts18813 : List PrefixCut := [⟨70,379619087,379619315⟩,
⟨128,686747980,686748394⟩]
theorem checked18813 : checkPrefixCuts (2^48) 2469789697 9 Manual.Count131072.C018813.packed 128 cuts18813 = true := by
 decide +kernel
def pointBounds18813 : List (Nat × Nat × Nat) := [(2469861376,99227158174684,99227538073066)]
theorem point_links_checked18813 : (cuts18813.take 1).map (fun c => (2469789697-1+2*2^9*c.k,99226778555597+c.lower,99227158453751+c.upper)) = pointBounds18813 := by
 decide +kernel
def cuts18814 : List PrefixCut := [⟨18,99145785,99145844⟩,
⟨94,507686837,507687139⟩,
⟨128,694118615,694119030⟩]
theorem checked18814 : checkPrefixCuts (2^48) 2469920769 9 Manual.Count131072.C018814.packed 128 cuts18814 = true := by
 decide +kernel
def pointBounds18814 : List (Nat × Nat × Nat) := [(2469939200,99227564449362,99227944347989),(2470017024,99227972990414,99228352889284)]
theorem point_links_checked18814 : (cuts18814.take 2).map (fun c => (2469920769-1+2*2^9*c.k,99227465303577+c.lower,99227845202145+c.upper)) = pointBounds18814 := by
 decide +kernel
def cuts18815 : List PrefixCut := [⟨42,227224417,227224551⟩,
⟨118,633916519,633916898⟩,
⟨128,688156359,688156771⟩]
theorem checked18815 : checkPrefixCuts (2^48) 2470051841 9 Manual.Count131072.C018815.packed 128 cuts18815 = true := by
 decide +kernel
def pointBounds18815 : List (Nat × Nat × Nat) := [(2470094848,99228386646609,99228766545726),(2470172672,99228793338711,99229173238073)]
theorem point_links_checked18815 : (cuts18815.take 2).map (fun c => (2470051841-1+2*2^9*c.k,99228159422192+c.lower,99228539321175+c.upper)) = pointBounds18815 := by
 decide +kernel
def cuts18816 : List PrefixCut := [⟨66,354376548,354376761⟩,
⟨128,689942887,689943301⟩]
theorem checked18816 : checkPrefixCuts (2^48) 2470182913 9 Manual.Count131072.C018816.packed 128 cuts18816 = true := by
 decide +kernel
def pointBounds18816 : List (Nat × Nat × Nat) := [(2470250496,99229201955099,99229581854707)]
theorem point_links_checked18816 : (cuts18816.take 1).map (fun c => (2470182913-1+2*2^9*c.k,99228847578551+c.lower,99229227477946+c.upper)) = pointBounds18816 := by
 decide +kernel
def cuts18817 : List PrefixCut := [⟨14,78962247,78962294⟩,
⟨90,495186916,495187218⟩,
⟨128,697084699,697085123⟩]
theorem checked18817 : checkPrefixCuts (2^48) 2470313985 9 Manual.Count131072.C018817.packed 128 cuts18817 = true := by
 decide +kernel
def pointBounds18817 : List (Nat × Nat × Nat) := [(2470328320,99229616483685,99229996383541),(2470406144,99230032708354,99230412608465)]
theorem point_links_checked18817 : (cuts18817.take 2).map (fun c => (2470313985-1+2*2^9*c.k,99229537521438+c.lower,99229917421247+c.upper)) = pointBounds18817 := by
 decide +kernel
def cuts18818 : List PrefixCut := [⟨38,207135694,207135815⟩,
⟨114,613763762,613764126⟩,
⟨128,690211592,690212000⟩]
theorem checked18818 : checkPrefixCuts (2^48) 2470445057 9 Manual.Count131072.C018818.packed 128 cuts18818 = true := by
 decide +kernel
def pointBounds18818 : List (Nat × Nat × Nat) := [(2470483968,99230441741831,99230821642185),(2470561792,99230848369899,99231228270496)]
theorem point_links_checked18818 : (cuts18818.take 2).map (fun c => (2470445057-1+2*2^9*c.k,99230234606137+c.lower,99230614506370+c.upper)) = pointBounds18818 := by
 decide +kernel
def cuts18819 : List PrefixCut := [⟨62,340648950,340649152⟩,
⟨128,689605438,689605851⟩]
theorem checked18819 : checkPrefixCuts (2^48) 2470576129 9 Manual.Count131072.C018819.packed 128 cuts18819 = true := by
 decide +kernel
def pointBounds18819 : List (Nat × Nat × Nat) := [(2470639616,99231265466679,99231645367522)]
theorem point_links_checked18819 : (cuts18819.take 1).map (fun c => (2470576129-1+2*2^9*c.k,99230924817729+c.lower,99231304718370+c.upper)) = pointBounds18819 := by
 decide +kernel
def cuts18820 : List PrefixCut := [⟨10,54114182,54114212⟩,
⟨86,467539147,467539429⟩,
⟨128,691847185,691847602⟩]
theorem checked18820 : checkPrefixCuts (2^48) 2470707201 9 Manual.Count131072.C018820.packed 128 cuts18820 = true := by
 decide +kernel
def pointBounds18820 : List (Nat × Nat × Nat) := [(2470717440,99231668537349,99232048438433),(2470795264,99232081962314,99232461863650)]
theorem point_links_checked18820 : (cuts18820.take 2).map (fun c => (2470707201-1+2*2^9*c.k,99231614423167+c.lower,99231994324221+c.upper)) = pointBounds18820 := by
 decide +kernel
def cuts18821 : List PrefixCut := [⟨34,184433206,184433320⟩,
⟨110,592591979,592592334⟩,
⟨128,693291220,693291636⟩]
theorem checked18821 : checkPrefixCuts (2^48) 2470838273 9 Manual.Count131072.C018821.packed 128 cuts18821 = true := by
 decide +kernel
def pointBounds18821 : List (Nat × Nat × Nat) := [(2470873088,99232490703558,99232870605143),(2470950912,99232898862331,99233278764157)]
theorem point_links_checked18821 : (cuts18821.take 2).map (fun c => (2470838273-1+2*2^9*c.k,99232306270352+c.lower,99232686171823+c.upper)) = pointBounds18821 := by
 decide +kernel
def cuts18822 : List PrefixCut := [⟨58,310636324,310636510⟩,
⟨128,689267668,689268075⟩]
theorem checked18822 : checkPrefixCuts (2^48) 2470969345 9 Manual.Count131072.C018822.packed 128 cuts18822 = true := by
 decide +kernel
def pointBounds18822 : List (Nat × Nat × Nat) := [(2471028736,99233310197896,99233690099969)]
theorem point_links_checked18822 : (cuts18822.take 1).map (fun c => (2470969345-1+2*2^9*c.k,99232999561572+c.lower,99233379463459+c.upper)) = pointBounds18822 := by
 decide +kernel
def cuts18823 : List PrefixCut := [⟨6,31893837,31893857⟩,
⟨82,440469724,440469994⟩,
⟨128,682852641,682853057⟩]
theorem checked18823 : checkPrefixCuts (2^48) 2471100417 9 Manual.Count131072.C018823.packed 128 cuts18823 = true := by
 decide +kernel
def pointBounds18823 : List (Nat × Nat × Nat) := [(2471106560,99233720723077,99234100625391),(2471184384,99234129298964,99234509201528)]
theorem point_links_checked18823 : (cuts18823.take 2).map (fun c => (2471100417-1+2*2^9*c.k,99233688829240+c.lower,99234068731534+c.upper)) = pointBounds18823 := by
 decide +kernel
def cuts18824 : List PrefixCut := [⟨30,160257226,160257319⟩,
⟨106,576210724,576211069⟩,
⟨128,697964618,697965036⟩]
theorem checked18824 : checkPrefixCuts (2^48) 2471231489 9 Manual.Count131072.C018824.packed 128 cuts18824 = true := by
 decide +kernel
def pointBounds18824 : List (Nat × Nat × Nat) := [(2471262208,99234531939107,99234911841910),(2471340032,99234947892605,99235327795660)]
theorem point_links_checked18824 : (cuts18824.take 2).map (fun c => (2471231489-1+2*2^9*c.k,99234371681881+c.lower,99234751584591+c.upper)) = pointBounds18824 := by
 decide +kernel
def cuts18825 : List PrefixCut := [⟨54,284961163,284961338⟩,
⟨128,684830069,684830481⟩]
theorem checked18825 : checkPrefixCuts (2^48) 2471362561 9 Manual.Count131072.C018825.packed 128 cuts18825 = true := by
 decide +kernel
def pointBounds18825 : List (Nat × Nat × Nat) := [(2471417856,99235354607662,99235734510965)]
theorem point_links_checked18825 : (cuts18825.take 1).map (fun c => (2471362561-1+2*2^9*c.k,99235069646499+c.lower,99235449549627+c.upper)) = pointBounds18825 := by
 decide +kernel
def cuts18826 : List PrefixCut := [⟨2,11958296,11958302⟩,
⟨78,418761593,418761842⟩,
⟨128,694360163,694360580⟩]
theorem checked18826 : checkPrefixCuts (2^48) 2471493633 9 Manual.Count131072.C018826.packed 128 cuts18826 = true := by
 decide +kernel
def pointBounds18826 : List (Nat × Nat × Nat) := [(2471495680,99235766434864,99236146338410),(2471573504,99236173238161,99236553141950)]
theorem point_links_checked18826 : (cuts18826.take 2).map (fun c => (2471493633-1+2*2^9*c.k,99235754476568+c.lower,99236134380108+c.upper)) = pointBounds18826 := by
 decide +kernel
def cuts18827 : List PrefixCut := [⟨26,139960882,139960963⟩,
⟨102,548218908,548219233⟩,
⟨128,679860845,679861250⟩]
theorem checked18827 : checkPrefixCuts (2^48) 2471624705 9 Manual.Count131072.C018827.packed 128 cuts18827 = true := by
 decide +kernel
def pointBounds18827 : List (Nat × Nat × Nat) := [(2471651328,99236588797613,99236968701651),(2471729152,99236997055639,99237376959921)]
theorem point_links_checked18827 : (cuts18827.take 2).map (fun c => (2471624705-1+2*2^9*c.k,99236448836731+c.lower,99236828740688+c.upper)) = pointBounds18827 := by
 decide +kernel
def cuts18828 : List PrefixCut := [⟨50,276147650,276147815⟩,
⟨126,680052861,680053264⟩,
⟨128,691553782,691554192⟩]
theorem checked18828 : checkPrefixCuts (2^48) 2471755777 9 Manual.Count131072.C018828.packed 128 cuts18828 = true := by
 decide +kernel
def pointBounds18828 : List (Nat × Nat × Nat) := [(2471806976,99237404845226,99237784749753),(2471884800,99237808750437,99238188655202)]
theorem point_links_checked18828 : (cuts18828.take 2).map (fun c => (2471755777-1+2*2^9*c.k,99237128697576+c.lower,99237508601938+c.upper)) = pointBounds18828 := by
 decide +kernel
def cuts18829 : List PrefixCut := [⟨74,391252985,391253223⟩,
⟨128,680927331,680927745⟩]
theorem checked18829 : checkPrefixCuts (2^48) 2471886849 9 Manual.Count131072.C018829.packed 128 cuts18829 = true := by
 decide +kernel
def pointBounds18829 : List (Nat × Nat × Nat) := [(2471962624,99238211504343,99238591409353)]
theorem point_links_checked18829 : (cuts18829.take 1).map (fun c => (2471886849-1+2*2^9*c.k,99237820251358+c.lower,99238200156130+c.upper)) = pointBounds18829 := by
 decide +kernel
def cuts18830 : List PrefixCut := [⟨22,119898690,119898764⟩,
⟨98,529345036,529345358⟩,
⟨128,691935835,691936252⟩]
theorem checked18830 : checkPrefixCuts (2^48) 2472017921 9 Manual.Count131072.C018830.packed 128 cuts18830 = true := by
 decide +kernel
def pointBounds18830 : List (Nat × Nat × Nat) := [(2472040448,99238621077379,99239000982639),(2472118272,99239030523725,99239410429233)]
theorem point_links_checked18830 : (cuts18830.take 2).map (fun c => (2472017921-1+2*2^9*c.k,99238501178689+c.lower,99238881083875+c.upper)) = pointBounds18830 := by
 decide +kernel
def cuts18831 : List PrefixCut := [⟨46,252649357,252649506⟩,
⟨122,659109648,659110042⟩,
⟨128,692013019,692013433⟩]
theorem checked18831 : checkPrefixCuts (2^48) 2472148993 9 Manual.Count131072.C018831.packed 128 cuts18831 = true := by
 decide +kernel
def pointBounds18831 : List (Nat × Nat × Nat) := [(2472196096,99239445763881,99239825669633),(2472273920,99239852224172,99240232130169)]
theorem point_links_checked18831 : (cuts18831.take 2).map (fun c => (2472148993-1+2*2^9*c.k,99239193114524+c.lower,99239573020127+c.upper)) = pointBounds18831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000275
