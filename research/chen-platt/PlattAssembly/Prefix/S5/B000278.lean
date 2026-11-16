import PlattAssemblyKernel
import PlattCertificates.Count131072.C048896
import PlattCertificates.Count131072.C048897
import PlattCertificates.Count131072.C048898
import PlattCertificates.Count131072.C048899
import PlattCertificates.Count131072.C048900
import PlattCertificates.Count131072.C048901
import PlattCertificates.Count131072.C048902
import PlattCertificates.Count131072.C048903
import PlattCertificates.Count131072.C048904
import PlattCertificates.Count131072.C048905
import PlattCertificates.Count131072.C048906
import PlattCertificates.Count131072.C048907
import PlattCertificates.Count131072.C048908
import PlattCertificates.Count131072.C048909
import PlattCertificates.Count131072.C048910
import PlattCertificates.Count131072.C048911
import PlattCertificates.Count131072.C048912
import PlattCertificates.Count131072.C048913
import PlattCertificates.Count131072.C048914
import PlattCertificates.Count131072.C048915
import PlattCertificates.Count131072.C048916
import PlattCertificates.Count131072.C048917
import PlattCertificates.Count131072.C048918
import PlattCertificates.Count131072.C048919
import PlattCertificates.Count131072.C048920
import PlattCertificates.Count131072.C048921
import PlattCertificates.Count131072.C048922
import PlattCertificates.Count131072.C048923
import PlattCertificates.Count131072.C048924
import PlattCertificates.Count131072.C048925
import PlattCertificates.Count131072.C048926
import PlattCertificates.Count131072.C048927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000278
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48896 : List PrefixCut := [⟨64,253520321,253520469⟩]
theorem checked48896 : checkPrefixCuts (2^48) 6412828673 10 Manual.Count131072.C048896.packed 64 cuts48896 = true := by
 decide +kernel
def cuts48897 : List PrefixCut := [⟨6,23394187,23394201⟩,
⟨64,254524634,254524782⟩]
theorem checked48897 : checkPrefixCuts (2^48) 6412959745 10 Manual.Count131072.C048897.packed 64 cuts48897 = true := by
 decide +kernel
def pointBounds48897 : List (Nat × Nat × Nat) := [(6412972032,111379138674055,111379525637819)]
theorem point_links_checked48897 : (cuts48897.take 1).map (fun c => (6412959745-1+2*2^10*c.k,111379115279868+c.lower,111379502243618+c.upper)) = pointBounds48897 := by
 decide +kernel
def cuts48898 : List PrefixCut := [⟨40,159102695,159102783⟩,
⟨64,255002228,255002368⟩]
theorem checked48898 : checkPrefixCuts (2^48) 6413090817 10 Manual.Count131072.C048898.packed 64 cuts48898 = true := by
 decide +kernel
def pointBounds48898 : List (Nat × Nat × Nat) := [(6413172736,111379528907197,111379915871183)]
theorem point_links_checked48898 : (cuts48898.take 1).map (fun c => (6413090817-1+2*2^10*c.k,111379369804502+c.lower,111379756768400+c.upper)) = pointBounds48898 := by
 decide +kernel
def cuts48899 : List PrefixCut := [⟨64,253504772,253504920⟩]
theorem checked48899 : checkPrefixCuts (2^48) 6413221889 10 Manual.Count131072.C048899.packed 64 cuts48899 = true := by
 decide +kernel
def cuts48900 : List PrefixCut := [⟨10,41913816,41913840⟩,
⟨64,255167393,255167542⟩]
theorem checked48900 : checkPrefixCuts (2^48) 6413352961 10 Manual.Count131072.C048900.packed 64 cuts48900 = true := by
 decide +kernel
def pointBounds48900 : List (Nat × Nat × Nat) := [(6413373440,111379920225318,111380307189528)]
theorem point_links_checked48900 : (cuts48900.take 1).map (fun c => (6413352961-1+2*2^10*c.k,111379878311502+c.lower,111380265275688+c.upper)) = pointBounds48900 := by
 decide +kernel
def cuts48901 : List PrefixCut := [⟨44,172654118,172654217⟩,
⟨64,252704419,252704563⟩]
theorem checked48901 : checkPrefixCuts (2^48) 6413484033 10 Manual.Count131072.C048901.packed 64 cuts48901 = true := by
 decide +kernel
def pointBounds48901 : List (Nat × Nat × Nat) := [(6413574144,111380306133013,111380693097447)]
theorem point_links_checked48901 : (cuts48901.take 1).map (fun c => (6413484033-1+2*2^10*c.k,111380133478895+c.lower,111380520443230+c.upper)) = pointBounds48901 := by
 decide +kernel
def cuts48902 : List PrefixCut := [⟨64,255551909,255552051⟩]
theorem checked48902 : checkPrefixCuts (2^48) 6413615105 10 Manual.Count131072.C048902.packed 64 cuts48902 = true := by
 decide +kernel
def cuts48903 : List PrefixCut := [⟨14,56218091,56218122⟩,
⟨64,256907157,256907307⟩]
theorem checked48903 : checkPrefixCuts (2^48) 6413746177 10 Manual.Count131072.C048903.packed 64 cuts48903 = true := by
 decide +kernel
def pointBounds48903 : List (Nat × Nat × Nat) := [(6413774848,111380697953314,111381084917966)]
theorem point_links_checked48903 : (cuts48903.take 1).map (fun c => (6413746177-1+2*2^10*c.k,111380641735223+c.lower,111381028699844+c.upper)) = pointBounds48903 := by
 decide +kernel
def cuts48904 : List PrefixCut := [⟨48,193181601,193181714⟩,
⟨64,257999024,257999176⟩]
theorem checked48904 : checkPrefixCuts (2^48) 6413877249 10 Manual.Count131072.C048904.packed 64 cuts48904 = true := by
 decide +kernel
def pointBounds48904 : List (Nat × Nat × Nat) := [(6413975552,111381091823981,111381478788865)]
theorem point_links_checked48904 : (cuts48904.take 1).map (fun c => (6413877249-1+2*2^10*c.k,111380898642380+c.lower,111381285607151+c.upper)) = pointBounds48904 := by
 decide +kernel
def cuts48905 : List PrefixCut := [⟨64,254000277,254000428⟩]
theorem checked48905 : checkPrefixCuts (2^48) 6414008321 10 Manual.Count131072.C048905.packed 64 cuts48905 = true := by
 decide +kernel
def cuts48906 : List PrefixCut := [⟨18,70213400,70213440⟩,
⟨64,253644033,253644175⟩]
theorem checked48906 : checkPrefixCuts (2^48) 6414139393 10 Manual.Count131072.C048906.packed 64 cuts48906 = true := by
 decide +kernel
def pointBounds48906 : List (Nat × Nat × Nat) := [(6414176256,111381480855081,111381867820195)]
theorem point_links_checked48906 : (cuts48906.take 1).map (fun c => (6414139393-1+2*2^10*c.k,111381410641681+c.lower,111381797606755+c.upper)) = pointBounds48906 := by
 decide +kernel
def cuts48907 : List PrefixCut := [⟨52,204798433,204798550⟩,
⟨64,253156169,253156313⟩]
theorem checked48907 : checkPrefixCuts (2^48) 6414270465 10 Manual.Count131072.C048907.packed 64 cuts48907 = true := by
 decide +kernel
def pointBounds48907 : List (Nat × Nat × Nat) := [(6414376960,111381869084147,111382256049480)]
theorem point_links_checked48907 : (cuts48907.take 1).map (fun c => (6414270465-1+2*2^10*c.k,111381664285714+c.lower,111382051250930+c.upper)) = pointBounds48907 := by
 decide +kernel
def cuts48908 : List PrefixCut := [⟨64,257495221,257495370⟩]
theorem checked48908 : checkPrefixCuts (2^48) 6414401537 10 Manual.Count131072.C048908.packed 64 cuts48908 = true := by
 decide +kernel
def cuts48909 : List PrefixCut := [⟨22,86225489,86225539⟩,
⟨64,252312078,252312223⟩]
theorem checked48909 : checkPrefixCuts (2^48) 6414532609 10 Manual.Count131072.C048909.packed 64 cuts48909 = true := by
 decide +kernel
def pointBounds48909 : List (Nat × Nat × Nat) := [(6414577664,111382261162593,111382648128152)]
theorem point_links_checked48909 : (cuts48909.take 1).map (fun c => (6414532609-1+2*2^10*c.k,111382174937104+c.lower,111382561902613+c.upper)) = pointBounds48909 := by
 decide +kernel
def cuts48910 : List PrefixCut := [⟨56,220494606,220494734⟩,
⟨64,252219177,252219322⟩]
theorem checked48910 : checkPrefixCuts (2^48) 6414663681 10 Manual.Count131072.C048910.packed 64 cuts48910 = true := by
 decide +kernel
def pointBounds48910 : List (Nat × Nat × Nat) := [(6414778368,111382647743788,111383034709570)]
theorem point_links_checked48910 : (cuts48910.take 1).map (fun c => (6414663681-1+2*2^10*c.k,111382427249182+c.lower,111382814214836+c.upper)) = pointBounds48910 := by
 decide +kernel
def cuts48911 : List PrefixCut := [⟨64,252082400,252082541⟩]
theorem checked48911 : checkPrefixCuts (2^48) 6414794753 10 Manual.Count131072.C048911.packed 64 cuts48911 = true := by
 decide +kernel
def cuts48912 : List PrefixCut := [⟨26,101577426,101577485⟩,
⟨64,252384356,252384507⟩]
theorem checked48912 : checkPrefixCuts (2^48) 6414925825 10 Manual.Count131072.C048912.packed 64 cuts48912 = true := by
 decide +kernel
def pointBounds48912 : List (Nat × Nat × Nat) := [(6414979072,111383033128185,111383420094184)]
theorem point_links_checked48912 : (cuts48912.take 1).map (fun c => (6414925825-1+2*2^10*c.k,111382931550759+c.lower,111383318516699+c.upper)) = pointBounds48912 := by
 decide +kernel
def cuts48913 : List PrefixCut := [⟨60,241103042,241103175⟩,
⟨64,254967971,254968112⟩]
theorem checked48913 : checkPrefixCuts (2^48) 6415056897 10 Manual.Count131072.C048913.packed 64 cuts48913 = true := by
 decide +kernel
def pointBounds48913 : List (Nat × Nat × Nat) := [(6415179776,111383425038157,111383812004381)]
theorem point_links_checked48913 : (cuts48913.take 1).map (fun c => (6415056897-1+2*2^10*c.k,111383183935115+c.lower,111383570901206+c.upper)) = pointBounds48913 := by
 decide +kernel
def cuts48914 : List PrefixCut := [⟨64,255269881,255270028⟩]
theorem checked48914 : checkPrefixCuts (2^48) 6415187969 10 Manual.Count131072.C048914.packed 64 cuts48914 = true := by
 decide +kernel
def cuts48915 : List PrefixCut := [⟨30,121007868,121007935⟩,
⟨64,255045306,255045449⟩]
theorem checked48915 : checkPrefixCuts (2^48) 6415319041 10 Manual.Count131072.C048915.packed 64 cuts48915 = true := by
 decide +kernel
def pointBounds48915 : List (Nat × Nat × Nat) := [(6415380480,111383815180835,111384202147281)]
theorem point_links_checked48915 : (cuts48915.take 1).map (fun c => (6415319041-1+2*2^10*c.k,111383694172967+c.lower,111384081139346+c.upper)) = pointBounds48915 := by
 decide +kernel
def cuts48916 : List PrefixCut := [⟨64,253065718,253065868⟩]
theorem checked48916 : checkPrefixCuts (2^48) 6415450113 10 Manual.Count131072.C048916.packed 64 cuts48916 = true := by
 decide +kernel
def pointBounds48916 : List (Nat × Nat × Nat) := [(6415581184,111384202283991,111384589250663)]
theorem point_links_checked48916 : (cuts48916.take 1).map (fun c => (6415450113-1+2*2^10*c.k,111383949218273+c.lower,111384336184795+c.upper)) = pointBounds48916 := by
 decide +kernel
def cuts48917 : List PrefixCut := [⟨64,254552240,254552387⟩]
theorem checked48917 : checkPrefixCuts (2^48) 6415581185 10 Manual.Count131072.C048917.packed 64 cuts48917 = true := by
 decide +kernel
def cuts48918 : List PrefixCut := [⟨34,132714327,132714406⟩,
⟨64,254590900,254591046⟩]
theorem checked48918 : checkPrefixCuts (2^48) 6415712257 10 Manual.Count131072.C048918.packed 64 cuts48918 = true := by
 decide +kernel
def pointBounds48918 : List (Nat × Nat × Nat) := [(6415781888,111384589550558,111384976517456)]
theorem point_links_checked48918 : (cuts48918.take 1).map (fun c => (6415712257-1+2*2^10*c.k,111384456836231+c.lower,111384843803050+c.upper)) = pointBounds48918 := by
 decide +kernel
def cuts48919 : List PrefixCut := [⟨64,253050220,253050367⟩]
theorem checked48919 : checkPrefixCuts (2^48) 6415843329 10 Manual.Count131072.C048919.packed 64 cuts48919 = true := by
 decide +kernel
def cuts48920 : List PrefixCut := [⟨4,15486435,15486445⟩,
⟨64,251377993,251378141⟩]
theorem checked48920 : checkPrefixCuts (2^48) 6415974401 10 Manual.Count131072.C048920.packed 64 cuts48920 = true := by
 decide +kernel
def pointBounds48920 : List (Nat × Nat × Nat) := [(6415982592,111384979963786,111385366930908)]
theorem point_links_checked48920 : (cuts48920.take 1).map (fun c => (6415974401-1+2*2^10*c.k,111384964477351+c.lower,111385351444463+c.upper)) = pointBounds48920 := by
 decide +kernel
def cuts48921 : List PrefixCut := [⟨38,151964947,151965036⟩,
⟨64,256681063,256681212⟩]
theorem checked48921 : checkPrefixCuts (2^48) 6416105473 10 Manual.Count131072.C048921.packed 64 cuts48921 = true := by
 decide +kernel
def pointBounds48921 : List (Nat × Nat × Nat) := [(6416183296,111385367820291,111385754787640)]
theorem point_links_checked48921 : (cuts48921.take 1).map (fun c => (6416105473-1+2*2^10*c.k,111385215855344+c.lower,111385602822604+c.upper)) = pointBounds48921 := by
 decide +kernel
def cuts48922 : List PrefixCut := [⟨64,252946965,252947109⟩]
theorem checked48922 : checkPrefixCuts (2^48) 6416236545 10 Manual.Count131072.C048922.packed 64 cuts48922 = true := by
 decide +kernel
def cuts48923 : List PrefixCut := [⟨8,32462472,32462491⟩,
⟨64,255091337,255091487⟩]
theorem checked48923 : checkPrefixCuts (2^48) 6416367617 10 Manual.Count131072.C048923.packed 64 cuts48923 = true := by
 decide +kernel
def pointBounds48923 : List (Nat × Nat × Nat) := [(6416384000,111385757945844,111386144913416)]
theorem point_links_checked48923 : (cuts48923.take 1).map (fun c => (6416367617-1+2*2^10*c.k,111385725483372+c.lower,111386112450925+c.upper)) = pointBounds48923 := by
 decide +kernel
def cuts48924 : List PrefixCut := [⟨42,165729787,165729880⟩,
⟨64,251445175,251445315⟩]
theorem checked48924 : checkPrefixCuts (2^48) 6416498689 10 Manual.Count131072.C048924.packed 64 cuts48924 = true := by
 decide +kernel
def pointBounds48924 : List (Nat × Nat × Nat) := [(6416584704,111386146304496,111386533272292)]
theorem point_links_checked48924 : (cuts48924.take 1).map (fun c => (6416498689-1+2*2^10*c.k,111385980574709+c.lower,111386367542412+c.upper)) = pointBounds48924 := by
 decide +kernel
def cuts48925 : List PrefixCut := [⟨64,254115868,254116010⟩]
theorem checked48925 : checkPrefixCuts (2^48) 6416629761 10 Manual.Count131072.C048925.packed 64 cuts48925 = true := by
 decide +kernel
def cuts48926 : List PrefixCut := [⟨12,47813384,47813413⟩,
⟨64,252224496,252224643⟩]
theorem checked48926 : checkPrefixCuts (2^48) 6416760833 10 Manual.Count131072.C048926.packed 64 cuts48926 = true := by
 decide +kernel
def pointBounds48926 : List (Nat × Nat × Nat) := [(6416785408,111386533949136,111386920917150)]
theorem point_links_checked48926 : (cuts48926.take 1).map (fun c => (6416760833-1+2*2^10*c.k,111386486135752+c.lower,111386873103737+c.upper)) = pointBounds48926 := by
 decide +kernel
def cuts48927 : List PrefixCut := [⟨46,182431851,182431954⟩,
⟨64,252614104,252614246⟩]
theorem checked48927 : checkPrefixCuts (2^48) 6416891905 10 Manual.Count131072.C048927.packed 64 cuts48927 = true := by
 decide +kernel
def pointBounds48927 : List (Nat × Nat × Nat) := [(6416986112,111386920792099,111387307760334)]
theorem point_links_checked48927 : (cuts48927.take 1).map (fun c => (6416891905-1+2*2^10*c.k,111386738360248+c.lower,111387125328380+c.upper)) = pointBounds48927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000278
