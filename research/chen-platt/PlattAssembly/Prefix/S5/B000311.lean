import PlattAssemblyKernel
import PlattCertificates.Count131072.C049952
import PlattCertificates.Count131072.C049953
import PlattCertificates.Count131072.C049954
import PlattCertificates.Count131072.C049955
import PlattCertificates.Count131072.C049956
import PlattCertificates.Count131072.C049957
import PlattCertificates.Count131072.C049958
import PlattCertificates.Count131072.C049959
import PlattCertificates.Count131072.C049960
import PlattCertificates.Count131072.C049961
import PlattCertificates.Count131072.C049962
import PlattCertificates.Count131072.C049963
import PlattCertificates.Count131072.C049964
import PlattCertificates.Count131072.C049965
import PlattCertificates.Count131072.C049966
import PlattCertificates.Count131072.C049967
import PlattCertificates.Count131072.C049968
import PlattCertificates.Count131072.C049969
import PlattCertificates.Count131072.C049970
import PlattCertificates.Count131072.C049971
import PlattCertificates.Count131072.C049972
import PlattCertificates.Count131072.C049973
import PlattCertificates.Count131072.C049974
import PlattCertificates.Count131072.C049975
import PlattCertificates.Count131072.C049976
import PlattCertificates.Count131072.C049977
import PlattCertificates.Count131072.C049978
import PlattCertificates.Count131072.C049979
import PlattCertificates.Count131072.C049980
import PlattCertificates.Count131072.C049981
import PlattCertificates.Count131072.C049982
import PlattCertificates.Count131072.C049983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000311
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49952 : List PrefixCut := [⟨64,245672131,245672266⟩]
theorem checked49952 : checkPrefixCuts (2^48) 6551240705 10 Manual.Count131072.C049952.packed 64 cuts49952 = true := by
 decide +kernel
def cuts49953 : List PrefixCut := [⟨2,7346887,7346892⟩,
⟨64,249405070,249405212⟩]
theorem checked49953 : checkPrefixCuts (2^48) 6551371777 10 Manual.Count131072.C049953.packed 64 cuts49953 = true := by
 decide +kernel
def pointBounds49953 : List (Nat × Nat × Nat) := [(6551375872,111645148511535,111645535626920)]
theorem point_links_checked49953 : (cuts49953.take 1).map (fun c => (6551371777-1+2*2^10*c.k,111645141164648+c.lower,111645528280028+c.upper)) = pointBounds49953 := by
 decide +kernel
def cuts49954 : List PrefixCut := [⟨38,148781397,148781482⟩,
⟨64,247810469,247810612⟩]
theorem checked49954 : checkPrefixCuts (2^48) 6551502849 10 Manual.Count131072.C049954.packed 64 cuts49954 = true := by
 decide +kernel
def pointBounds49954 : List (Nat × Nat × Nat) := [(6551580672,111645539351115,111645926466722)]
theorem point_links_checked49954 : (cuts49954.take 1).map (fun c => (6551502849-1+2*2^10*c.k,111645390569718+c.lower,111645777685240+c.upper)) = pointBounds49954 := by
 decide +kernel
def cuts49955 : List PrefixCut := [⟨64,249867716,249867855⟩]
theorem checked49955 : checkPrefixCuts (2^48) 6551633921 10 Manual.Count131072.C049955.packed 64 cuts49955 = true := by
 decide +kernel
def cuts49956 : List PrefixCut := [⟨10,38665459,38665480⟩,
⟨64,249304196,249304340⟩]
theorem checked49956 : checkPrefixCuts (2^48) 6551764993 10 Manual.Count131072.C049956.packed 64 cuts49956 = true := by
 decide +kernel
def pointBounds49956 : List (Nat × Nat × Nat) := [(6551785472,111645926913362,111646314029187)]
theorem point_links_checked49956 : (cuts49956.take 1).map (fun c => (6551764993-1+2*2^10*c.k,111645888247903+c.lower,111646275363707+c.upper)) = pointBounds49956 := by
 decide +kernel
def cuts49957 : List PrefixCut := [⟨46,181336354,181336459⟩,
⟨64,249771782,249771927⟩]
theorem checked49957 : checkPrefixCuts (2^48) 6551896065 10 Manual.Count131072.C049957.packed 64 cuts49957 = true := by
 decide +kernel
def pointBounds49957 : List (Nat × Nat × Nat) := [(6551990272,111646318888453,111646706004506)]
theorem point_links_checked49957 : (cuts49957.take 1).map (fun c => (6551896065-1+2*2^10*c.k,111646137552099+c.lower,111646524668047+c.upper)) = pointBounds49957 := by
 decide +kernel
def cuts49958 : List PrefixCut := [⟨64,249079417,249079558⟩]
theorem checked49958 : checkPrefixCuts (2^48) 6552027137 10 Manual.Count131072.C049958.packed 64 cuts49958 = true := by
 decide +kernel
def cuts49959 : List PrefixCut := [⟨18,69851317,69851355⟩,
⟨64,251265324,251265463⟩]
theorem checked49959 : checkPrefixCuts (2^48) 6552158209 10 Manual.Count131072.C049959.packed 64 cuts49959 = true := by
 decide +kernel
def pointBounds49959 : List (Nat × Nat × Nat) := [(6552195072,111646706254615,111647093370887)]
theorem point_links_checked49959 : (cuts49959.take 1).map (fun c => (6552158209-1+2*2^10*c.k,111646636403298+c.lower,111647023519532+c.upper)) = pointBounds49959 := by
 decide +kernel
def cuts49960 : List PrefixCut := [⟨54,211266895,211267011⟩,
⟨64,250229311,250229450⟩]
theorem checked49960 : checkPrefixCuts (2^48) 6552289281 10 Manual.Count131072.C049960.packed 64 cuts49960 = true := by
 decide +kernel
def pointBounds49960 : List (Nat × Nat × Nat) := [(6552399872,111647098935517,111647486052006)]
theorem point_links_checked49960 : (cuts49960.take 1).map (fun c => (6552289281-1+2*2^10*c.k,111646887668622+c.lower,111647274784995+c.upper)) = pointBounds49960 := by
 decide +kernel
def cuts49961 : List PrefixCut := [⟨64,250653865,250654012⟩]
theorem checked49961 : checkPrefixCuts (2^48) 6552420353 10 Manual.Count131072.C049961.packed 64 cuts49961 = true := by
 decide +kernel
def cuts49962 : List PrefixCut := [⟨26,102107267,102107325⟩,
⟨64,248973584,248973726⟩]
theorem checked49962 : checkPrefixCuts (2^48) 6552551425 10 Manual.Count131072.C049962.packed 64 cuts49962 = true := by
 decide +kernel
def pointBounds49962 : List (Nat × Nat × Nat) := [(6552604672,111647490659065,111647877775782)]
theorem point_links_checked49962 : (cuts49962.take 1).map (fun c => (6552551425-1+2*2^10*c.k,111647388551798+c.lower,111647775668457+c.upper)) = pointBounds49962 := by
 decide +kernel
def cuts49963 : List PrefixCut := [⟨62,240291697,240291837⟩,
⟨64,248667888,248668034⟩]
theorem checked49963 : checkPrefixCuts (2^48) 6552682497 10 Manual.Count131072.C049963.packed 64 cuts49963 = true := by
 decide +kernel
def pointBounds49963 : List (Nat × Nat × Nat) := [(6552809472,111647877817079,111648264934020)]
theorem point_links_checked49963 : (cuts49963.take 1).map (fun c => (6552682497-1+2*2^10*c.k,111647637525382+c.lower,111648024642183+c.upper)) = pointBounds49963 := by
 decide +kernel
def cuts49964 : List PrefixCut := [⟨64,250982463,250982609⟩]
theorem checked49964 : checkPrefixCuts (2^48) 6552813569 10 Manual.Count131072.C049964.packed 64 cuts49964 = true := by
 decide +kernel
def cuts49965 : List PrefixCut := [⟨34,133414265,133414344⟩,
⟨64,250290197,250290345⟩]
theorem checked49965 : checkPrefixCuts (2^48) 6552944641 10 Manual.Count131072.C049965.packed 64 cuts49965 = true := by
 decide +kernel
def pointBounds49965 : List (Nat × Nat × Nat) := [(6553014272,111648270589998,111648657707170)]
theorem point_links_checked49965 : (cuts49965.take 1).map (fun c => (6552944641-1+2*2^10*c.k,111648137175733+c.lower,111648524292826+c.upper)) = pointBounds49965 := by
 decide +kernel
def cuts49966 : List PrefixCut := [⟨64,251960344,251960488⟩]
theorem checked49966 : checkPrefixCuts (2^48) 6553075713 10 Manual.Count131072.C049966.packed 64 cuts49966 = true := by
 decide +kernel
def cuts49967 : List PrefixCut := [⟨6,22936474,22936488⟩,
⟨64,249893621,249893766⟩]
theorem checked49967 : checkPrefixCuts (2^48) 6553206785 10 Manual.Count131072.C049967.packed 64 cuts49967 = true := by
 decide +kernel
def pointBounds49967 : List (Nat × Nat × Nat) := [(6553219072,111648662362748,111649049480147)]
theorem point_links_checked49967 : (cuts49967.take 1).map (fun c => (6553206785-1+2*2^10*c.k,111648639426274+c.lower,111649026543659+c.upper)) = pointBounds49967 := by
 decide +kernel
def cuts49968 : List PrefixCut := [⟨42,162612848,162612939⟩,
⟨64,248643037,248643177⟩]
theorem checked49968 : checkPrefixCuts (2^48) 6553337857 10 Manual.Count131072.C049968.packed 64 cuts49968 = true := by
 decide +kernel
def pointBounds49968 : List (Nat × Nat × Nat) := [(6553423872,111649051932743,111649439050364)]
theorem point_links_checked49968 : (cuts49968.take 1).map (fun c => (6553337857-1+2*2^10*c.k,111648889319895+c.lower,111649276437425+c.upper)) = pointBounds49968 := by
 decide +kernel
def cuts49969 : List PrefixCut := [⟨64,247907919,247908061⟩]
theorem checked49969 : checkPrefixCuts (2^48) 6553468929 10 Manual.Count131072.C049969.packed 64 cuts49969 = true := by
 decide +kernel
def cuts49970 : List PrefixCut := [⟨14,55490841,55490874⟩,
⟨64,248504273,248504414⟩]
theorem checked49970 : checkPrefixCuts (2^48) 6553600001 10 Manual.Count131072.C049970.packed 64 cuts49970 = true := by
 decide +kernel
def pointBounds49970 : List (Nat × Nat × Nat) := [(6553628672,111649441361692,111649828479537)]
theorem point_links_checked49970 : (cuts49970.take 1).map (fun c => (6553600001-1+2*2^10*c.k,111649385870851+c.lower,111649772988663+c.upper)) = pointBounds49970 := by
 decide +kernel
def cuts49971 : List PrefixCut := [⟨50,193869391,193869502⟩,
⟨64,248499294,248499435⟩]
theorem checked49971 : checkPrefixCuts (2^48) 6553731073 10 Manual.Count131072.C049971.packed 64 cuts49971 = true := by
 decide +kernel
def pointBounds49971 : List (Nat × Nat × Nat) := [(6553833472,111649828244515,111650215362579)]
theorem point_links_checked49971 : (cuts49971.take 1).map (fun c => (6553731073-1+2*2^10*c.k,111649634375124+c.lower,111650021493077+c.upper)) = pointBounds49971 := by
 decide +kernel
def cuts49972 : List PrefixCut := [⟨64,244629026,244629168⟩]
theorem checked49972 : checkPrefixCuts (2^48) 6553862145 10 Manual.Count131072.C049972.packed 64 cuts49972 = true := by
 decide +kernel
def cuts49973 : List PrefixCut := [⟨23,90875706,90875755⟩,
⟨64,247243910,247244049⟩]
theorem checked49973 : checkPrefixCuts (2^48) 6553993217 10 Manual.Count131072.C049973.packed 64 cuts49973 = true := by
 decide +kernel
def pointBounds49973 : List (Nat × Nat × Nat) := [(6554040320,111650218379150,111650605497435)]
theorem point_links_checked49973 : (cuts49973.take 1).map (fun c => (6553993217-1+2*2^10*c.k,111650127503444+c.lower,111650514621680+c.upper)) = pointBounds49973 := by
 decide +kernel
def cuts49974 : List PrefixCut := [⟨60,235214280,235214418⟩,
⟨64,250502839,250502987⟩]
theorem checked49974 : checkPrefixCuts (2^48) 6554124289 10 Manual.Count131072.C049974.packed 64 cuts49974 = true := by
 decide +kernel
def pointBounds49974 : List (Nat × Nat × Nat) := [(6554247168,111650609961634,111650997080147)]
theorem point_links_checked49974 : (cuts49974.take 1).map (fun c => (6554124289-1+2*2^10*c.k,111650374747354+c.lower,111650761865729+c.upper)) = pointBounds49974 := by
 decide +kernel
def cuts49975 : List PrefixCut := [⟨64,246418029,246418168⟩]
theorem checked49975 : checkPrefixCuts (2^48) 6554255361 10 Manual.Count131072.C049975.packed 64 cuts49975 = true := by
 decide +kernel
def cuts49976 : List PrefixCut := [⟨33,131065954,131066031⟩,
⟨64,251609357,251609504⟩]
theorem checked49976 : checkPrefixCuts (2^48) 6554386433 10 Manual.Count131072.C049976.packed 64 cuts49976 = true := by
 decide +kernel
def pointBounds49976 : List (Nat × Nat × Nat) := [(6554454016,111651002734176,111651389852915)]
theorem point_links_checked49976 : (cuts49976.take 1).map (fun c => (6554386433-1+2*2^10*c.k,111650871668222+c.lower,111651258786884+c.upper)) = pointBounds49976 := by
 decide +kernel
def cuts49977 : List PrefixCut := [⟨64,251690207,251690349⟩]
theorem checked49977 : checkPrefixCuts (2^48) 6554517505 10 Manual.Count131072.C049977.packed 64 cuts49977 = true := by
 decide +kernel
def cuts49978 : List PrefixCut := [⟨6,23146141,23146154⟩,
⟨64,244256138,244256280⟩]
theorem checked49978 : checkPrefixCuts (2^48) 6554648577 10 Manual.Count131072.C049978.packed 64 cuts49978 = true := by
 decide +kernel
def pointBounds49978 : List (Nat × Nat × Nat) := [(6554660864,111651398113927,111651785232891)]
theorem point_links_checked49978 : (cuts49978.take 1).map (fun c => (6554648577-1+2*2^10*c.k,111651374967786+c.lower,111651762086737+c.upper)) = pointBounds49978 := by
 decide +kernel
def cuts49979 : List PrefixCut := [⟨43,164852964,164853061⟩,
⟨64,248631272,248631414⟩]
theorem checked49979 : checkPrefixCuts (2^48) 6554779649 10 Manual.Count131072.C049979.packed 64 cuts49979 = true := by
 decide +kernel
def pointBounds49979 : List (Nat × Nat × Nat) := [(6554867712,111651784076888,111652171196078)]
theorem point_links_checked49979 : (cuts49979.take 1).map (fun c => (6554779649-1+2*2^10*c.k,111651619223924+c.lower,111652006343017+c.upper)) = pointBounds49979 := by
 decide +kernel
def cuts49980 : List PrefixCut := [⟨64,254809755,254809895⟩]
theorem checked49980 : checkPrefixCuts (2^48) 6554910721 10 Manual.Count131072.C049980.packed 64 cuts49980 = true := by
 decide +kernel
def cuts49981 : List PrefixCut := [⟨16,61017893,61017928⟩,
⟨64,250811278,250811421⟩]
theorem checked49981 : checkPrefixCuts (2^48) 6555041793 10 Manual.Count131072.C049981.packed 64 cuts49981 = true := by
 decide +kernel
def pointBounds49981 : List (Nat × Nat × Nat) := [(6555074560,111652183682844,111652570802254)]
theorem point_links_checked49981 : (cuts49981.take 1).map (fun c => (6555041793-1+2*2^10*c.k,111652122664951+c.lower,111652509784326+c.upper)) = pointBounds49981 := by
 decide +kernel
def cuts49982 : List PrefixCut := [⟨53,204819040,204819158⟩,
⟨64,246254762,246254903⟩]
theorem checked49982 : checkPrefixCuts (2^48) 6555172865 10 Manual.Count131072.C049982.packed 64 cuts49982 = true := by
 decide +kernel
def pointBounds49982 : List (Nat × Nat × Nat) := [(6555281408,111652578295269,111652965414905)]
theorem point_links_checked49982 : (cuts49982.take 1).map (fun c => (6555172865-1+2*2^10*c.k,111652373476229+c.lower,111652760595747+c.upper)) = pointBounds49982 := by
 decide +kernel
def cuts49983 : List PrefixCut := [⟨64,247881468,247881610⟩]
theorem checked49983 : checkPrefixCuts (2^48) 6555303937 10 Manual.Count131072.C049983.packed 64 cuts49983 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000311
