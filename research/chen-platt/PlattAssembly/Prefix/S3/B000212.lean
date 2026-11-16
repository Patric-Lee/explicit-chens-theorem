import PlattAssemblyKernel
import PlattCertificates.Count131072.C026784
import PlattCertificates.Count131072.C026785
import PlattCertificates.Count131072.C026786
import PlattCertificates.Count131072.C026787
import PlattCertificates.Count131072.C026788
import PlattCertificates.Count131072.C026789
import PlattCertificates.Count131072.C026790
import PlattCertificates.Count131072.C026791
import PlattCertificates.Count131072.C026792
import PlattCertificates.Count131072.C026793
import PlattCertificates.Count131072.C026794
import PlattCertificates.Count131072.C026795
import PlattCertificates.Count131072.C026796
import PlattCertificates.Count131072.C026797
import PlattCertificates.Count131072.C026798
import PlattCertificates.Count131072.C026799
import PlattCertificates.Count131072.C026800
import PlattCertificates.Count131072.C026801
import PlattCertificates.Count131072.C026802
import PlattCertificates.Count131072.C026803
import PlattCertificates.Count131072.C026804
import PlattCertificates.Count131072.C026805
import PlattCertificates.Count131072.C026806
import PlattCertificates.Count131072.C026807
import PlattCertificates.Count131072.C026808
import PlattCertificates.Count131072.C026809
import PlattCertificates.Count131072.C026810
import PlattCertificates.Count131072.C026811
import PlattCertificates.Count131072.C026812
import PlattCertificates.Count131072.C026813
import PlattCertificates.Count131072.C026814
import PlattCertificates.Count131072.C026815
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000212
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26784 : List PrefixCut := [⟨8,29152045,29152061⟩,
⟨116,435591935,435592178⟩,
⟨128,480439692,480439960⟩]
theorem checked26784 : checkPrefixCuts (2^48) 3514564609 9 Manual.Count131072.C026784.packed 128 cuts26784 = true := by
 decide +kernel
def pointBounds26784 : List (Nat × Nat × Nat) := [(3514572800,103781157330869,103781539841813),(3514683392,103781563770759,103781946281930)]
theorem point_links_checked26784 : (cuts26784.take 2).map (fun c => (3514564609-1+2*2^9*c.k,103781128178824+c.lower,103781510689752+c.upper)) = pointBounds26784 := by
 decide +kernel
def cuts26785 : List PrefixCut := [⟨96,358776421,358776625⟩,
⟨128,476017240,476017509⟩]
theorem checked26785 : checkPrefixCuts (2^48) 3514695681 9 Manual.Count131072.C026785.packed 128 cuts26785 = true := by
 decide +kernel
def pointBounds26785 : List (Nat × Nat × Nat) := [(3514793984,103781967394937,103782349906337)]
theorem point_links_checked26785 : (cuts26785.take 1).map (fun c => (3514695681-1+2*2^9*c.k,103781608618516+c.lower,103781991129712+c.upper)) = pointBounds26785 := by
 decide +kernel
def cuts26786 : List PrefixCut := [⟨76,289093365,289093525⟩,
⟨128,478161719,478161988⟩]
theorem checked26786 : checkPrefixCuts (2^48) 3514826753 9 Manual.Count131072.C026786.packed 128 cuts26786 = true := by
 decide +kernel
def pointBounds26786 : List (Nat × Nat × Nat) := [(3514904576,103782373729121,103782756240746)]
theorem point_links_checked26786 : (cuts26786.take 1).map (fun c => (3514826753-1+2*2^9*c.k,103782084635756+c.lower,103782467147221+c.upper)) = pointBounds26786 := by
 decide +kernel
def cuts26787 : List PrefixCut := [⟨56,209965872,209965985⟩,
⟨128,481507068,481507335⟩]
theorem checked26787 : checkPrefixCuts (2^48) 3514957825 9 Manual.Count131072.C026787.packed 128 cuts26787 = true := by
 decide +kernel
def pointBounds26787 : List (Nat × Nat × Nat) := [(3515015168,103782772763347,103783155275194)]
theorem point_links_checked26787 : (cuts26787.take 1).map (fun c => (3514957825-1+2*2^9*c.k,103782562797475+c.lower,103782945309209+c.upper)) = pointBounds26787 := by
 decide +kernel
def cuts26788 : List PrefixCut := [⟨36,133646439,133646519⟩,
⟨128,474842916,474843183⟩]
theorem checked26788 : checkPrefixCuts (2^48) 3515088897 9 Manual.Count131072.C026788.packed 128 cuts26788 = true := by
 decide +kernel
def pointBounds26788 : List (Nat × Nat × Nat) := [(3515125760,103783177950982,103783560463063)]
theorem point_links_checked26788 : (cuts26788.take 1).map (fun c => (3515088897-1+2*2^9*c.k,103783044304543+c.lower,103783426816544+c.upper)) = pointBounds26788 := by
 decide +kernel
def cuts26789 : List PrefixCut := [⟨16,57252206,57252238⟩,
⟨124,456408905,456409160⟩,
⟨128,471942535,471942799⟩]
theorem checked26789 : checkPrefixCuts (2^48) 3515219969 9 Manual.Count131072.C026789.packed 128 cuts26789 = true := by
 decide +kernel
def pointBounds26789 : List (Nat × Nat × Nat) := [(3515236352,103783576399665,103783958911965),(3515346944,103783975556364,103784358068887)]
theorem point_links_checked26789 : (cuts26789.take 2).map (fun c => (3515219969-1+2*2^9*c.k,103783519147459+c.lower,103783901659727+c.upper)) = pointBounds26789 := by
 decide +kernel
def cuts26790 : List PrefixCut := [⟨104,393539151,393539369⟩,
⟨128,484335701,484335969⟩]
theorem checked26790 : checkPrefixCuts (2^48) 3515351041 9 Manual.Count131072.C026790.packed 128 cuts26790 = true := by
 decide +kernel
def pointBounds26790 : List (Nat × Nat × Nat) := [(3515457536,103784384629145,103784767141895)]
theorem point_links_checked26790 : (cuts26790.take 1).map (fun c => (3515351041-1+2*2^9*c.k,103783991089994+c.lower,103784373602526+c.upper)) = pointBounds26790 := by
 decide +kernel
def cuts26791 : List PrefixCut := [⟨84,314820471,314820643⟩,
⟨128,477512041,477512302⟩]
theorem checked26791 : checkPrefixCuts (2^48) 3515482113 9 Manual.Count131072.C026791.packed 128 cuts26791 = true := by
 decide +kernel
def pointBounds26791 : List (Nat × Nat × Nat) := [(3515568128,103784790246166,103785172759138)]
theorem point_links_checked26791 : (cuts26791.take 1).map (fun c => (3515482113-1+2*2^9*c.k,103784475425695+c.lower,103784857938495+c.upper)) = pointBounds26791 := by
 decide +kernel
def cuts26792 : List PrefixCut := [⟨64,238989519,238989648⟩,
⟨128,475092338,475092600⟩]
theorem checked26792 : checkPrefixCuts (2^48) 3515613185 9 Manual.Count131072.C026792.packed 128 cuts26792 = true := by
 decide +kernel
def pointBounds26792 : List (Nat × Nat × Nat) := [(3515678720,103785191927255,103785574440445)]
theorem point_links_checked26792 : (cuts26792.take 1).map (fun c => (3515613185-1+2*2^9*c.k,103784952937736+c.lower,103785335450797+c.upper)) = pointBounds26792 := by
 decide +kernel
def cuts26793 : List PrefixCut := [⟨44,161162267,161162358⟩,
⟨128,477636455,477636720⟩]
theorem checked26793 : checkPrefixCuts (2^48) 3515744257 9 Manual.Count131072.C026793.packed 128 cuts26793 = true := by
 decide +kernel
def pointBounds26793 : List (Nat × Nat × Nat) := [(3515789312,103785589192341,103785971705755)]
theorem point_links_checked26793 : (cuts26793.take 1).map (fun c => (3515744257-1+2*2^9*c.k,103785428030074+c.lower,103785810543397+c.upper)) = pointBounds26793 := by
 decide +kernel
def cuts26794 : List PrefixCut := [⟨24,87423323,87423372⟩,
⟨128,478579394,478579657⟩]
theorem checked26794 : checkPrefixCuts (2^48) 3515875329 9 Manual.Count131072.C026794.packed 128 cuts26794 = true := by
 decide +kernel
def pointBounds26794 : List (Nat × Nat × Nat) := [(3515899904,103785993089852,103786375603489)]
theorem point_links_checked26794 : (cuts26794.take 1).map (fun c => (3515875329-1+2*2^9*c.k,103785905666529+c.lower,103786288180117+c.upper)) = pointBounds26794 := by
 decide +kernel
def cuts26795 : List PrefixCut := [⟨4,14249833,14249841⟩,
⟨112,420283409,420283645⟩,
⟨128,482404137,482404407⟩]
theorem checked26795 : checkPrefixCuts (2^48) 3516006401 9 Manual.Count131072.C026795.packed 128 cuts26795 = true := by
 decide +kernel
def pointBounds26795 : List (Nat × Nat × Nat) := [(3516010496,103786398495756,103786781009615),(3516121088,103786804529332,103787187043419)]
theorem point_links_checked26795 : (cuts26795.take 2).map (fun c => (3516006401-1+2*2^9*c.k,103786384245923+c.lower,103786766759774+c.upper)) = pointBounds26795 := by
 decide +kernel
def cuts26796 : List PrefixCut := [⟨92,343499818,343500005⟩,
⟨128,476462426,476462687⟩]
theorem checked26796 : checkPrefixCuts (2^48) 3516137473 9 Manual.Count131072.C026796.packed 128 cuts26796 = true := by
 decide +kernel
def pointBounds26796 : List (Nat × Nat × Nat) := [(3516231680,103787210149878,103787592664186)]
theorem point_links_checked26796 : (cuts26796.take 1).map (fun c => (3516137473-1+2*2^9*c.k,103786866650060+c.lower,103787249164181+c.upper)) = pointBounds26796 := by
 decide +kernel
def cuts26797 : List PrefixCut := [⟨72,271604505,271604659⟩,
⟨128,485970323,485970597⟩]
theorem checked26797 : checkPrefixCuts (2^48) 3516268545 9 Manual.Count131072.C026797.packed 128 cuts26797 = true := by
 decide +kernel
def pointBounds26797 : List (Nat × Nat × Nat) := [(3516342272,103787614716991,103787997231527)]
theorem point_links_checked26797 : (cuts26797.take 1).map (fun c => (3516268545-1+2*2^9*c.k,103787343112486+c.lower,103787725626868+c.upper)) = pointBounds26797 := by
 decide +kernel
def cuts26798 : List PrefixCut := [⟨52,192269831,192269940⟩,
⟨128,478347927,478348201⟩]
theorem checked26798 : checkPrefixCuts (2^48) 3516399617 9 Manual.Count131072.C026798.packed 128 cuts26798 = true := by
 decide +kernel
def pointBounds26798 : List (Nat × Nat × Nat) := [(3516452864,103788021352640,103788403867405)]
theorem point_links_checked26798 : (cuts26798.take 1).map (fun c => (3516399617-1+2*2^9*c.k,103787829082809+c.lower,103788211597465+c.upper)) = pointBounds26798 := by
 decide +kernel
def cuts26799 : List PrefixCut := [⟨32,119904372,119904437⟩,
⟨128,475928834,475929103⟩]
theorem checked26799 : checkPrefixCuts (2^48) 3516530689 9 Manual.Count131072.C026799.packed 128 cuts26799 = true := by
 decide +kernel
def pointBounds26799 : List (Nat × Nat × Nat) := [(3516563456,103788427335108,103788809850103)]
theorem point_links_checked26799 : (cuts26799.take 1).map (fun c => (3516530689-1+2*2^9*c.k,103788307430736+c.lower,103788689945666+c.upper)) = pointBounds26799 := by
 decide +kernel
def cuts26800 : List PrefixCut := [⟨12,44742485,44742512⟩,
⟨120,442535503,442535750⟩,
⟨128,473349929,473350195⟩]
theorem checked26800 : checkPrefixCuts (2^48) 3516661761 9 Manual.Count131072.C026800.packed 128 cuts26800 = true := by
 decide +kernel
def pointBounds26800 : List (Nat × Nat × Nat) := [(3516674048,103788828102055,103789210617281),(3516784640,103789225895073,103789608410519)]
theorem point_links_checked26800 : (cuts26800.take 2).map (fun c => (3516661761-1+2*2^9*c.k,103788783359570+c.lower,103789165874769+c.upper)) = pointBounds26800 := by
 decide +kernel
def cuts26801 : List PrefixCut := [⟨100,376170205,376170414⟩,
⟨128,480055273,480055542⟩]
theorem checked26801 : checkPrefixCuts (2^48) 3516792833 9 Manual.Count131072.C026801.packed 128 cuts26801 = true := by
 decide +kernel
def pointBounds26801 : List (Nat × Nat × Nat) := [(3516895232,103789632879704,103790015395378)]
theorem point_links_checked26801 : (cuts26801.take 1).map (fun c => (3516792833-1+2*2^9*c.k,103789256709499+c.lower,103789639224964+c.upper)) = pointBounds26801 := by
 decide +kernel
def cuts26802 : List PrefixCut := [⟨80,297724472,297724638⟩,
⟨128,476996105,476996374⟩]
theorem checked26802 : checkPrefixCuts (2^48) 3516923905 9 Manual.Count131072.C026802.packed 128 cuts26802 = true := by
 decide +kernel
def pointBounds26802 : List (Nat × Nat × Nat) := [(3517005824,103790034489244,103790417005144)]
theorem point_links_checked26802 : (cuts26802.take 1).map (fun c => (3516923905-1+2*2^9*c.k,103789736764772+c.lower,103790119280506+c.upper)) = pointBounds26802 := by
 decide +kernel
def cuts26803 : List PrefixCut := [⟨60,224406129,224406255⟩,
⟨128,478899050,478899317⟩]
theorem checked26803 : checkPrefixCuts (2^48) 3517054977 9 Manual.Count131072.C026803.packed 128 cuts26803 = true := by
 decide +kernel
def pointBounds26803 : List (Nat × Nat × Nat) := [(3517116416,103790438167006,103790820683135)]
theorem point_links_checked26803 : (cuts26803.take 1).map (fun c => (3517054977-1+2*2^9*c.k,103790213760877+c.lower,103790596276880+c.upper)) = pointBounds26803 := by
 decide +kernel
def cuts26804 : List PrefixCut := [⟨40,149652301,149652386⟩,
⟨128,475280025,475280298⟩]
theorem checked26804 : checkPrefixCuts (2^48) 3517186049 9 Manual.Count131072.C026804.packed 128 cuts26804 = true := by
 decide +kernel
def pointBounds26804 : List (Nat × Nat × Nat) := [(3517227008,103790842312228,103791224828583)]
theorem point_links_checked26804 : (cuts26804.take 1).map (fun c => (3517186049-1+2*2^9*c.k,103790692659927+c.lower,103791075176197+c.upper)) = pointBounds26804 := by
 decide +kernel
def cuts26805 : List PrefixCut := [⟨20,73863288,73863328⟩,
⟨128,477022853,477023121⟩]
theorem checked26805 : checkPrefixCuts (2^48) 3517317121 9 Manual.Count131072.C026805.packed 128 cuts26805 = true := by
 decide +kernel
def pointBounds26805 : List (Nat × Nat × Nat) := [(3517337600,103791241803240,103791624319823),(3517448192,103791644962805,103792027479616)]
theorem point_links_checked26805 : (cuts26805.take 2).map (fun c => (3517317121-1+2*2^9*c.k,103791167939952+c.lower,103791550456495+c.upper)) = pointBounds26805 := by
 decide +kernel
def cuts26806 : List PrefixCut := [⟨108,398585642,398585869⟩,
⟨128,473003988,473004257⟩]
theorem checked26806 : checkPrefixCuts (2^48) 3517448193 9 Manual.Count131072.C026806.packed 128 cuts26806 = true := by
 decide +kernel
def pointBounds26806 : List (Nat × Nat × Nat) := [(3517558784,103792043548447,103792426065485)]
theorem point_links_checked26806 : (cuts26806.take 1).map (fun c => (3517448193-1+2*2^9*c.k,103791644962805+c.lower,103792027479616+c.upper)) = pointBounds26806 := by
 decide +kernel
def cuts26807 : List PrefixCut := [⟨88,329355986,329356168⟩,
⟨128,476027099,476027364⟩]
theorem checked26807 : checkPrefixCuts (2^48) 3517579265 9 Manual.Count131072.C026807.packed 128 cuts26807 = true := by
 decide +kernel
def pointBounds26807 : List (Nat × Nat × Nat) := [(3517669376,103792447322779,103792829840041)]
theorem point_links_checked26807 : (cuts26807.take 1).map (fun c => (3517579265-1+2*2^9*c.k,103792117966793+c.lower,103792500483873+c.upper)) = pointBounds26807 := by
 decide +kernel
def cuts26808 : List PrefixCut := [⟨68,253409777,253409917⟩,
⟨128,471848607,471848872⟩]
theorem checked26808 : checkPrefixCuts (2^48) 3517710337 9 Manual.Count131072.C026808.packed 128 cuts26808 = true := by
 decide +kernel
def pointBounds26808 : List (Nat × Nat × Nat) := [(3517779968,103792847403669,103793229921154)]
theorem point_links_checked26808 : (cuts26808.take 1).map (fun c => (3517710337-1+2*2^9*c.k,103792593993892+c.lower,103792976511237+c.upper)) = pointBounds26808 := by
 decide +kernel
def cuts26809 : List PrefixCut := [⟨48,181469402,181469504⟩,
⟨128,475351541,475351809⟩]
theorem checked26809 : checkPrefixCuts (2^48) 3517841409 9 Manual.Count131072.C026809.packed 128 cuts26809 = true := by
 decide +kernel
def pointBounds26809 : List (Nat × Nat × Nat) := [(3517890560,103793247311901,103793629829613)]
theorem point_links_checked26809 : (cuts26809.take 1).map (fun c => (3517841409-1+2*2^9*c.k,103793065842499+c.lower,103793448360109+c.upper)) = pointBounds26809 := by
 decide +kernel
def cuts26810 : List PrefixCut := [⟨28,102653105,102653161⟩,
⟨128,477093996,477094263⟩]
theorem checked26810 : checkPrefixCuts (2^48) 3517972481 9 Manual.Count131072.C026810.packed 128 cuts26810 = true := by
 decide +kernel
def pointBounds26810 : List (Nat × Nat × Nat) := [(3518001152,103793643847145,103794026365079)]
theorem point_links_checked26810 : (cuts26810.take 1).map (fun c => (3517972481-1+2*2^9*c.k,103793541194040+c.lower,103793923711918+c.upper)) = pointBounds26810 := by
 decide +kernel
def cuts26811 : List PrefixCut := [⟨8,31122908,31122925⟩,
⟨116,431633562,431633803⟩,
⟨128,475556158,475556423⟩]
theorem checked26811 : checkPrefixCuts (2^48) 3518103553 9 Manual.Count131072.C026811.packed 128 cuts26811 = true := by
 decide +kernel
def pointBounds26811 : List (Nat × Nat × Nat) := [(3518111744,103794049410944,103794431929106),(3518222336,103794449921598,103794832439984)]
theorem point_links_checked26811 : (cuts26811.take 2).map (fun c => (3518103553-1+2*2^9*c.k,103794018288036+c.lower,103794400806181+c.upper)) = pointBounds26811 := by
 decide +kernel
def cuts26812 : List PrefixCut := [⟨96,356815452,356815654⟩,
⟨128,478738456,478738729⟩]
theorem checked26812 : checkPrefixCuts (2^48) 3518234625 9 Manual.Count131072.C026812.packed 128 cuts26812 = true := by
 decide +kernel
def pointBounds26812 : List (Nat × Nat × Nat) := [(3518332928,103794850659646,103795233178258)]
theorem point_links_checked26812 : (cuts26812.take 1).map (fun c => (3518234625-1+2*2^9*c.k,103794493844194+c.lower,103794876362604+c.upper)) = pointBounds26812 := by
 decide +kernel
def cuts26813 : List PrefixCut := [⟨76,279362516,279362675⟩,
⟨128,471120656,471120921⟩]
theorem checked26813 : checkPrefixCuts (2^48) 3518365697 9 Manual.Count131072.C026813.packed 128 cuts26813 = true := by
 decide +kernel
def pointBounds26813 : List (Nat × Nat × Nat) := [(3518443520,103795251945166,103795634464008)]
theorem point_links_checked26813 : (cuts26813.take 1).map (fun c => (3518365697-1+2*2^9*c.k,103794972582650+c.lower,103795355101333+c.upper)) = pointBounds26813 := by
 decide +kernel
def cuts26814 : List PrefixCut := [⟨56,206234760,206234878⟩,
⟨128,475342931,475343196⟩]
theorem checked26814 : checkPrefixCuts (2^48) 3518496769 9 Manual.Count131072.C026814.packed 128 cuts26814 = true := by
 decide +kernel
def pointBounds26814 : List (Nat × Nat × Nat) := [(3518554112,103795649938066,103796032457132)]
theorem point_links_checked26814 : (cuts26814.take 1).map (fun c => (3518496769-1+2*2^9*c.k,103795443703306+c.lower,103795826222254+c.upper)) = pointBounds26814 := by
 decide +kernel
def cuts26815 : List PrefixCut := [⟨36,136151880,136151954⟩,
⟨128,473965404,473965670⟩]
theorem checked26815 : checkPrefixCuts (2^48) 3518627841 9 Manual.Count131072.C026815.packed 128 cuts26815 = true := by
 decide +kernel
def pointBounds26815 : List (Nat × Nat × Nat) := [(3518664704,103796055198117,103796437717404)]
theorem point_links_checked26815 : (cuts26815.take 1).map (fun c => (3518627841-1+2*2^9*c.k,103795919046237+c.lower,103796301565450+c.upper)) = pointBounds26815 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000212
