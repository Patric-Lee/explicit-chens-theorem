import PlattAssemblyKernel
import PlattCertificates.Count131072.C060896
import PlattCertificates.Count131072.C060897
import PlattCertificates.Count131072.C060898
import PlattCertificates.Count131072.C060899
import PlattCertificates.Count131072.C060900
import PlattCertificates.Count131072.C060901
import PlattCertificates.Count131072.C060902
import PlattCertificates.Count131072.C060903
import PlattCertificates.Count131072.C060904
import PlattCertificates.Count131072.C060905
import PlattCertificates.Count131072.C060906
import PlattCertificates.Count131072.C060907
import PlattCertificates.Count131072.C060908
import PlattCertificates.Count131072.C060909
import PlattCertificates.Count131072.C060910
import PlattCertificates.Count131072.C060911
import PlattCertificates.Count131072.C060912
import PlattCertificates.Count131072.C060913
import PlattCertificates.Count131072.C060914
import PlattCertificates.Count131072.C060915
import PlattCertificates.Count131072.C060916
import PlattCertificates.Count131072.C060917
import PlattCertificates.Count131072.C060918
import PlattCertificates.Count131072.C060919
import PlattCertificates.Count131072.C060920
import PlattCertificates.Count131072.C060921
import PlattCertificates.Count131072.C060922
import PlattCertificates.Count131072.C060923
import PlattCertificates.Count131072.C060924
import PlattCertificates.Count131072.C060925
import PlattCertificates.Count131072.C060926
import PlattCertificates.Count131072.C060927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60896 : List PrefixCut := [⟨46,146698813,146698899⟩,
⟨64,202318424,202318542⟩]
theorem checked60896 : checkPrefixCuts (2^48) 7985692673 10 Manual.Count131072.C060896.packed 64 cuts60896 = true := by
 decide +kernel
def pointBounds60896 : List (Nat × Nat × Nat) := [(7985786880,114099914082558,114100302594450)]
theorem point_links_checked60896 : (cuts60896.take 1).map (fun c => (7985692673-1+2*2^10*c.k,114099767383745+c.lower,114100155895551+c.upper)) = pointBounds60896 := by
 decide +kernel
def cuts60897 : List PrefixCut := [⟨64,201222457,201222570⟩]
theorem checked60897 : checkPrefixCuts (2^48) 7985823745 10 Manual.Count131072.C060897.packed 64 cuts60897 = true := by
 decide +kernel
def cuts60898 : List PrefixCut := [⟨40,127238279,127238349⟩,
⟨64,201888822,201888938⟩]
theorem checked60898 : checkPrefixCuts (2^48) 7985954817 10 Manual.Count131072.C060898.packed 64 cuts60898 = true := by
 decide +kernel
def pointBounds60898 : List (Nat × Nat × Nat) := [(7986036736,114100298162905,114100686675012)]
theorem point_links_checked60898 : (cuts60898.take 1).map (fun c => (7985954817-1+2*2^10*c.k,114100170924626+c.lower,114100559436663+c.upper)) = pointBounds60898 := by
 decide +kernel
def cuts60899 : List PrefixCut := [⟨64,200898643,200898756⟩]
theorem checked60899 : checkPrefixCuts (2^48) 7986085889 10 Manual.Count131072.C060899.packed 64 cuts60899 = true := by
 decide +kernel
def cuts60900 : List PrefixCut := [⟨34,108201944,108202006⟩,
⟨64,202939542,202939658⟩]
theorem checked60900 : checkPrefixCuts (2^48) 7986216961 10 Manual.Count131072.C060900.packed 64 cuts60900 = true := by
 decide +kernel
def pointBounds60900 : List (Nat × Nat × Nat) := [(7986286592,114100681914035,114101070426363)]
theorem point_links_checked60900 : (cuts60900.take 1).map (fun c => (7986216961-1+2*2^10*c.k,114100573712091+c.lower,114100962224357+c.upper)) = pointBounds60900 := by
 decide +kernel
def cuts60901 : List PrefixCut := [⟨64,200610084,200610197⟩]
theorem checked60901 : checkPrefixCuts (2^48) 7986348033 10 Manual.Count131072.C060901.packed 64 cuts60901 = true := by
 decide +kernel
def cuts60902 : List PrefixCut := [⟨28,92303513,92303566⟩,
⟨64,205858112,205858230⟩]
theorem checked60902 : checkPrefixCuts (2^48) 7986479105 10 Manual.Count131072.C060902.packed 64 cuts60902 = true := by
 decide +kernel
def pointBounds60902 : List (Nat × Nat × Nat) := [(7986536448,114101069565230,114101458077778)]
theorem point_links_checked60902 : (cuts60902.take 1).map (fun c => (7986479105-1+2*2^10*c.k,114100977261717+c.lower,114101365774212+c.upper)) = pointBounds60902 := by
 decide +kernel
def cuts60903 : List PrefixCut := [⟨64,203563913,203564027⟩]
theorem checked60903 : checkPrefixCuts (2^48) 7986610177 10 Manual.Count131072.C060903.packed 64 cuts60903 = true := by
 decide +kernel
def cuts60904 : List PrefixCut := [⟨22,71260686,71260726⟩,
⟨64,207719188,207719306⟩]
theorem checked60904 : checkPrefixCuts (2^48) 7986741249 10 Manual.Count131072.C060904.packed 64 cuts60904 = true := by
 decide +kernel
def pointBounds60904 : List (Nat × Nat × Nat) := [(7986786304,114101457944428,114101846457195)]
theorem point_links_checked60904 : (cuts60904.take 1).map (fun c => (7986741249-1+2*2^10*c.k,114101386683742+c.lower,114101775196469+c.upper)) = pointBounds60904 := by
 decide +kernel
def cuts60905 : List PrefixCut := [⟨64,199892086,199892201⟩]
theorem checked60905 : checkPrefixCuts (2^48) 7986872321 10 Manual.Count131072.C060905.packed 64 cuts60905 = true := by
 decide +kernel
def cuts60906 : List PrefixCut := [⟨16,49549608,49549637⟩,
⟨64,202990022,202990139⟩]
theorem checked60906 : checkPrefixCuts (2^48) 7987003393 10 Manual.Count131072.C060906.packed 64 cuts60906 = true := by
 decide +kernel
def pointBounds60906 : List (Nat × Nat × Nat) := [(7987036160,114101843844624,114102232357613)]
theorem point_links_checked60906 : (cuts60906.take 1).map (fun c => (7987003393-1+2*2^10*c.k,114101794295016+c.lower,114102182807976+c.upper)) = pointBounds60906 := by
 decide +kernel
def cuts60907 : List PrefixCut := [⟨64,200308407,200308525⟩]
theorem checked60907 : checkPrefixCuts (2^48) 7987134465 10 Manual.Count131072.C060907.packed 64 cuts60907 = true := by
 decide +kernel
def cuts60908 : List PrefixCut := [⟨10,31258247,31258265⟩,
⟨64,204252019,204252133⟩]
theorem checked60908 : checkPrefixCuts (2^48) 7987265537 10 Manual.Count131072.C060908.packed 64 cuts60908 = true := by
 decide +kernel
def pointBounds60908 : List (Nat × Nat × Nat) := [(7987286016,114102228851692,114102617364905)]
theorem point_links_checked60908 : (cuts60908.take 1).map (fun c => (7987265537-1+2*2^10*c.k,114102197593445+c.lower,114102586106640+c.upper)) = pointBounds60908 := by
 decide +kernel
def cuts60909 : List PrefixCut := [⟨64,205376347,205376460⟩]
theorem checked60909 : checkPrefixCuts (2^48) 7987396609 10 Manual.Count131072.C060909.packed 64 cuts60909 = true := by
 decide +kernel
def cuts60910 : List PrefixCut := [⟨4,13109013,13109021⟩,
⟨64,204033890,204034005⟩]
theorem checked60910 : checkPrefixCuts (2^48) 7987527681 10 Manual.Count131072.C060910.packed 64 cuts60910 = true := by
 decide +kernel
def pointBounds60910 : List (Nat × Nat × Nat) := [(7987535872,114102620330824,114103008844254)]
theorem point_links_checked60910 : (cuts60910.take 1).map (fun c => (7987527681-1+2*2^10*c.k,114102607221811+c.lower,114102995735233+c.upper)) = pointBounds60910 := by
 decide +kernel
def cuts60911 : List PrefixCut := [⟨62,198004821,198004933⟩,
⟨64,204594356,204594471⟩]
theorem checked60911 : checkPrefixCuts (2^48) 7987658753 10 Manual.Count131072.C060911.packed 64 cuts60911 = true := by
 decide +kernel
def pointBounds60911 : List (Nat × Nat × Nat) := [(7987785728,114103009260522,114103397774171)]
theorem point_links_checked60911 : (cuts60911.take 1).map (fun c => (7987658753-1+2*2^10*c.k,114102811255701+c.lower,114103199769238+c.upper)) = pointBounds60911 := by
 decide +kernel
def cuts60912 : List PrefixCut := [⟨64,201208160,201208275⟩]
theorem checked60912 : checkPrefixCuts (2^48) 7987789825 10 Manual.Count131072.C060912.packed 64 cuts60912 = true := by
 decide +kernel
def cuts60913 : List PrefixCut := [⟨56,178617938,178618039⟩,
⟨64,203671463,203671579⟩]
theorem checked60913 : checkPrefixCuts (2^48) 7987920897 10 Manual.Count131072.C060913.packed 64 cuts60913 = true := by
 decide +kernel
def pointBounds60913 : List (Nat × Nat × Nat) := [(7988035584,114103395676155,114103784190023)]
theorem point_links_checked60913 : (cuts60913.take 1).map (fun c => (7987920897-1+2*2^10*c.k,114103217058217+c.lower,114103605571984+c.upper)) = pointBounds60913 := by
 decide +kernel
def cuts60914 : List PrefixCut := [⟨64,203350988,203351106⟩]
theorem checked60914 : checkPrefixCuts (2^48) 7988051969 10 Manual.Count131072.C060914.packed 64 cuts60914 = true := by
 decide +kernel
def cuts60915 : List PrefixCut := [⟨50,160254168,160254261⟩,
⟨64,204686633,204686750⟩]
theorem checked60915 : checkPrefixCuts (2^48) 7988183041 10 Manual.Count131072.C060915.packed 64 cuts60915 = true := by
 decide +kernel
def pointBounds60915 : List (Nat × Nat × Nat) := [(7988285440,114103784334836,114104172848930)]
theorem point_links_checked60915 : (cuts60915.take 1).map (fun c => (7988183041-1+2*2^10*c.k,114103624080668+c.lower,114104012594669+c.upper)) = pointBounds60915 := by
 decide +kernel
def cuts60916 : List PrefixCut := [⟨64,199609347,199609458⟩]
theorem checked60916 : checkPrefixCuts (2^48) 7988314113 10 Manual.Count131072.C060916.packed 64 cuts60916 = true := by
 decide +kernel
def cuts60917 : List PrefixCut := [⟨44,137804309,137804388⟩,
⟨64,201085953,201086067⟩]
theorem checked60917 : checkPrefixCuts (2^48) 7988445185 10 Manual.Count131072.C060917.packed 64 cuts60917 = true := by
 decide +kernel
def pointBounds60917 : List (Nat × Nat × Nat) := [(7988535296,114104166180957,114104554695265)]
theorem point_links_checked60917 : (cuts60917.take 1).map (fun c => (7988445185-1+2*2^10*c.k,114104028376648+c.lower,114104416890877+c.upper)) = pointBounds60917 := by
 decide +kernel
def cuts60918 : List PrefixCut := [⟨64,201575933,201576047⟩]
theorem checked60918 : checkPrefixCuts (2^48) 7988576257 10 Manual.Count131072.C060918.packed 64 cuts60918 = true := by
 decide +kernel
def cuts60919 : List PrefixCut := [⟨38,120887604,120887676⟩,
⟨64,202629643,202629764⟩]
theorem checked60919 : checkPrefixCuts (2^48) 7988707329 10 Manual.Count131072.C060919.packed 64 cuts60919 = true := by
 decide +kernel
def pointBounds60919 : List (Nat × Nat × Nat) := [(7988785152,114104551926138,114104940440667)]
theorem point_links_checked60919 : (cuts60919.take 1).map (fun c => (7988707329-1+2*2^10*c.k,114104431038534+c.lower,114104819552991+c.upper)) = pointBounds60919 := by
 decide +kernel
def cuts60920 : List PrefixCut := [⟨64,201216968,201217087⟩]
theorem checked60920 : checkPrefixCuts (2^48) 7988838401 10 Manual.Count131072.C060920.packed 64 cuts60920 = true := by
 decide +kernel
def cuts60921 : List PrefixCut := [⟨32,100977196,100977253⟩,
⟨64,203398102,203398214⟩]
theorem checked60921 : checkPrefixCuts (2^48) 7988969473 10 Manual.Count131072.C060921.packed 64 cuts60921 = true := by
 decide +kernel
def pointBounds60921 : List (Nat × Nat × Nat) := [(7989035008,114104935862341,114105324377095)]
theorem point_links_checked60921 : (cuts60921.take 1).map (fun c => (7988969473-1+2*2^10*c.k,114104834885145+c.lower,114105223399842+c.upper)) = pointBounds60921 := by
 decide +kernel
def cuts60922 : List PrefixCut := [⟨64,205262075,205262190⟩]
theorem checked60922 : checkPrefixCuts (2^48) 7989100545 10 Manual.Count131072.C060922.packed 64 cuts60922 = true := by
 decide +kernel
def cuts60923 : List PrefixCut := [⟨26,81279459,81279509⟩,
⟨64,203778973,203779091⟩]
theorem checked60923 : checkPrefixCuts (2^48) 7989231617 10 Manual.Count131072.C060923.packed 64 cuts60923 = true := by
 decide +kernel
def pointBounds60923 : List (Nat × Nat × Nat) := [(7989284864,114105324824781,114105713339755)]
theorem point_links_checked60923 : (cuts60923.take 1).map (fun c => (7989231617-1+2*2^10*c.k,114105243545322+c.lower,114105632060246+c.upper)) = pointBounds60923 := by
 decide +kernel
def cuts60924 : List PrefixCut := [⟨64,204585949,204586067⟩]
theorem checked60924 : checkPrefixCuts (2^48) 7989362689 10 Manual.Count131072.C060924.packed 64 cuts60924 = true := by
 decide +kernel
def cuts60925 : List PrefixCut := [⟨20,61723908,61723944⟩,
⟨64,200284486,200284602⟩]
theorem checked60925 : checkPrefixCuts (2^48) 7989493761 10 Manual.Count131072.C060925.packed 64 cuts60925 = true := by
 decide +kernel
def pointBounds60925 : List (Nat × Nat × Nat) := [(7989534720,114105713634152,114106102149348)]
theorem point_links_checked60925 : (cuts60925.take 1).map (fun c => (7989493761-1+2*2^10*c.k,114105651910244+c.lower,114106040425404+c.upper)) = pointBounds60925 := by
 decide +kernel
def cuts60926 : List PrefixCut := [⟨64,200703982,200704100⟩]
theorem checked60926 : checkPrefixCuts (2^48) 7989624833 10 Manual.Count131072.C060926.packed 64 cuts60926 = true := by
 decide +kernel
def cuts60927 : List PrefixCut := [⟨14,44248139,44248163⟩,
⟨64,205209988,205210103⟩]
theorem checked60927 : checkPrefixCuts (2^48) 7989755905 10 Manual.Count131072.C060927.packed 64 cuts60927 = true := by
 decide +kernel
def pointBounds60927 : List (Nat × Nat × Nat) := [(7989784576,114106097146851,114106485662269)]
theorem point_links_checked60927 : (cuts60927.take 1).map (fun c => (7989755905-1+2*2^10*c.k,114106052898712+c.lower,114106441414106+c.upper)) = pointBounds60927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000028
