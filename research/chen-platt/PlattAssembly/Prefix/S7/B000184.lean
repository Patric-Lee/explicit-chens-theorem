import PlattAssemblyKernel
import PlattCertificates.Count131072.C065888
import PlattCertificates.Count131072.C065889
import PlattCertificates.Count131072.C065890
import PlattCertificates.Count131072.C065891
import PlattCertificates.Count131072.C065892
import PlattCertificates.Count131072.C065893
import PlattCertificates.Count131072.C065894
import PlattCertificates.Count131072.C065895
import PlattCertificates.Count131072.C065896
import PlattCertificates.Count131072.C065897
import PlattCertificates.Count131072.C065898
import PlattCertificates.Count131072.C065899
import PlattCertificates.Count131072.C065900
import PlattCertificates.Count131072.C065901
import PlattCertificates.Count131072.C065902
import PlattCertificates.Count131072.C065903
import PlattCertificates.Count131072.C065904
import PlattCertificates.Count131072.C065905
import PlattCertificates.Count131072.C065906
import PlattCertificates.Count131072.C065907
import PlattCertificates.Count131072.C065908
import PlattCertificates.Count131072.C065909
import PlattCertificates.Count131072.C065910
import PlattCertificates.Count131072.C065911
import PlattCertificates.Count131072.C065912
import PlattCertificates.Count131072.C065913
import PlattCertificates.Count131072.C065914
import PlattCertificates.Count131072.C065915
import PlattCertificates.Count131072.C065916
import PlattCertificates.Count131072.C065917
import PlattCertificates.Count131072.C065918
import PlattCertificates.Count131072.C065919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000184
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65888 : List PrefixCut := [⟨27,77959134,77959183⟩,
⟨64,186540763,186540873⟩]
theorem checked65888 : checkPrefixCuts (2^48) 8640004097 10 Manual.Count131072.C065888.packed 64 cuts65888 = true := by
 decide +kernel
def pointBounds65888 : List (Nat × Nat × Nat) := [(8640059392,115070405198919,115070794269820)]
theorem point_links_checked65888 : (cuts65888.take 1).map (fun c => (8640004097-1+2*2^10*c.k,115070327239785+c.lower,115070716310637+c.upper)) = pointBounds65888 := by
 decide +kernel
def cuts65889 : List PrefixCut := [⟨64,185234852,185234965⟩]
theorem checked65889 : checkPrefixCuts (2^48) 8640135169 10 Manual.Count131072.C065889.packed 64 cuts65889 = true := by
 decide +kernel
def cuts65890 : List PrefixCut := [⟨31,91508764,91508814⟩,
⟨64,187512427,187512528⟩]
theorem checked65890 : checkPrefixCuts (2^48) 8640266241 10 Manual.Count131072.C065890.packed 64 cuts65890 = true := by
 decide +kernel
def pointBounds65890 : List (Nat × Nat × Nat) := [(8640329728,115070790524164,115071179595289)]
theorem point_links_checked65890 : (cuts65890.take 1).map (fun c => (8640266241-1+2*2^10*c.k,115070699015400+c.lower,115071088086475+c.upper)) = pointBounds65890 := by
 decide +kernel
def cuts65891 : List PrefixCut := [⟨64,186401979,186402091⟩]
theorem checked65891 : checkPrefixCuts (2^48) 8640397313 10 Manual.Count131072.C065891.packed 64 cuts65891 = true := by
 decide +kernel
def cuts65892 : List PrefixCut := [⟨35,101767375,101767433⟩,
⟨64,186562021,186562129⟩]
theorem checked65892 : checkPrefixCuts (2^48) 8640528385 10 Manual.Count131072.C065892.packed 64 cuts65892 = true := by
 decide +kernel
def pointBounds65892 : List (Nat × Nat × Nat) := [(8640600064,115071174697181,115071563768527)]
theorem point_links_checked65892 : (cuts65892.take 1).map (fun c => (8640528385-1+2*2^10*c.k,115071072929806+c.lower,115071462001094+c.upper)) = pointBounds65892 := by
 decide +kernel
def cuts65893 : List PrefixCut := [⟨64,187797066,187797177⟩]
theorem checked65893 : checkPrefixCuts (2^48) 8640659457 10 Manual.Count131072.C065893.packed 64 cuts65893 = true := by
 decide +kernel
def cuts65894 : List PrefixCut := [⟨39,115250287,115250350⟩,
⟨64,187826797,187826905⟩]
theorem checked65894 : checkPrefixCuts (2^48) 8640790529 10 Manual.Count131072.C065894.packed 64 cuts65894 = true := by
 decide +kernel
def pointBounds65894 : List (Nat × Nat × Nat) := [(8640870400,115071562539180,115071951610750)]
theorem point_links_checked65894 : (cuts65894.take 1).map (fun c => (8640790529-1+2*2^10*c.k,115071447288893+c.lower,115071836360400+c.upper)) = pointBounds65894 := by
 decide +kernel
def cuts65895 : List PrefixCut := [⟨64,186064923,186065035⟩]
theorem checked65895 : checkPrefixCuts (2^48) 8640921601 10 Manual.Count131072.C065895.packed 64 cuts65895 = true := by
 decide +kernel
def cuts65896 : List PrefixCut := [⟨43,123813683,123813757⟩,
⟨64,185084873,185084979⟩]
theorem checked65896 : checkPrefixCuts (2^48) 8641052673 10 Manual.Count131072.C065896.packed 64 cuts65896 = true := by
 decide +kernel
def pointBounds65896 : List (Nat × Nat × Nat) := [(8641140736,115071944994296,115072334066097)]
theorem point_links_checked65896 : (cuts65896.take 1).map (fun c => (8641052673-1+2*2^10*c.k,115071821180613+c.lower,115072210252340+c.upper)) = pointBounds65896 := by
 decide +kernel
def cuts65897 : List PrefixCut := [⟨64,184854058,184854167⟩]
theorem checked65897 : checkPrefixCuts (2^48) 8641183745 10 Manual.Count131072.C065897.packed 64 cuts65897 = true := by
 decide +kernel
def cuts65898 : List PrefixCut := [⟨47,137881406,137881488⟩,
⟨64,186349626,186349734⟩]
theorem checked65898 : checkPrefixCuts (2^48) 8641314817 10 Manual.Count131072.C065898.packed 64 cuts65898 = true := by
 decide +kernel
def pointBounds65898 : List (Nat × Nat × Nat) := [(8641411072,115072329000950,115072718072974)]
theorem point_links_checked65898 : (cuts65898.take 1).map (fun c => (8641314817-1+2*2^10*c.k,115072191119544+c.lower,115072580191486+c.upper)) = pointBounds65898 := by
 decide +kernel
def cuts65899 : List PrefixCut := [⟨64,189343442,189343547⟩]
theorem checked65899 : checkPrefixCuts (2^48) 8641445889 10 Manual.Count131072.C065899.packed 64 cuts65899 = true := by
 decide +kernel
def cuts65900 : List PrefixCut := [⟨51,149342481,149342568⟩,
⟨64,188493694,188493805⟩]
theorem checked65900 : checkPrefixCuts (2^48) 8641576961 10 Manual.Count131072.C065900.packed 64 cuts65900 = true := by
 decide +kernel
def pointBounds65900 : List (Nat × Nat × Nat) := [(8641681408,115072716155093,115073105227335)]
theorem point_links_checked65900 : (cuts65900.take 1).map (fun c => (8641576961-1+2*2^10*c.k,115072566812612+c.lower,115072955884767+c.upper)) = pointBounds65900 := by
 decide +kernel
def cuts65901 : List PrefixCut := [⟨64,185591983,185592092⟩]
theorem checked65901 : checkPrefixCuts (2^48) 8641708033 10 Manual.Count131072.C065901.packed 64 cuts65901 = true := by
 decide +kernel
def cuts65902 : List PrefixCut := [⟨55,160346872,160346970⟩,
⟨64,186664012,186664128⟩]
theorem checked65902 : checkPrefixCuts (2^48) 8641839105 10 Manual.Count131072.C065902.packed 64 cuts65902 = true := by
 decide +kernel
def pointBounds65902 : List (Nat × Nat × Nat) := [(8641951744,115073101245161,115073490317634)]
theorem point_links_checked65902 : (cuts65902.take 1).map (fun c => (8641839105-1+2*2^10*c.k,115072940898289+c.lower,115073329970664+c.upper)) = pointBounds65902 := by
 decide +kernel
def cuts65903 : List PrefixCut := [⟨64,184674384,184674494⟩]
theorem checked65903 : checkPrefixCuts (2^48) 8641970177 10 Manual.Count131072.C065903.packed 64 cuts65903 = true := by
 decide +kernel
def cuts65904 : List PrefixCut := [⟨59,169103249,169103352⟩,
⟨64,183727052,183727163⟩]
theorem checked65904 : checkPrefixCuts (2^48) 8642101249 10 Manual.Count131072.C065904.packed 64 cuts65904 = true := by
 decide +kernel
def pointBounds65904 : List (Nat × Nat × Nat) := [(8642222080,115073481339934,115073870412638)]
theorem point_links_checked65904 : (cuts65904.take 1).map (fun c => (8642101249-1+2*2^10*c.k,115073312236685+c.lower,115073701309286+c.upper)) = pointBounds65904 := by
 decide +kernel
def cuts65905 : List PrefixCut := [⟨64,183691714,183691823⟩]
theorem checked65905 : checkPrefixCuts (2^48) 8642232321 10 Manual.Count131072.C065905.packed 64 cuts65905 = true := by
 decide +kernel
def cuts65906 : List PrefixCut := [⟨63,185317400,185317504⟩,
⟨64,188150878,188150984⟩]
theorem checked65906 : checkPrefixCuts (2^48) 8642363393 10 Manual.Count131072.C065906.packed 64 cuts65906 = true := by
 decide +kernel
def pointBounds65906 : List (Nat × Nat × Nat) := [(8642492416,115073864972851,115074254045776)]
theorem point_links_checked65906 : (cuts65906.take 1).map (fun c => (8642363393-1+2*2^10*c.k,115073679655451+c.lower,115074068728272+c.upper)) = pointBounds65906 := by
 decide +kernel
def cuts65907 : List PrefixCut := [⟨64,189450747,189450854⟩]
theorem checked65907 : checkPrefixCuts (2^48) 8642494465 10 Manual.Count131072.C065907.packed 64 cuts65907 = true := by
 decide +kernel
def cuts65908 : List PrefixCut := [⟨64,187884610,187884719⟩]
theorem checked65908 : checkPrefixCuts (2^48) 8642625537 10 Manual.Count131072.C065908.packed 64 cuts65908 = true := by
 decide +kernel
def cuts65909 : List PrefixCut := [⟨3,8988689,8988693⟩,
⟨64,186351079,186351184⟩]
theorem checked65909 : checkPrefixCuts (2^48) 8642756609 10 Manual.Count131072.C065909.packed 64 cuts65909 = true := by
 decide +kernel
def pointBounds65909 : List (Nat × Nat × Nat) := [(8642762752,115074254130375,115074643203522)]
theorem point_links_checked65909 : (cuts65909.take 1).map (fun c => (8642756609-1+2*2^10*c.k,115074245141686+c.lower,115074634214829+c.upper)) = pointBounds65909 := by
 decide +kernel
def cuts65910 : List PrefixCut := [⟨64,187455547,187455658⟩]
theorem checked65910 : checkPrefixCuts (2^48) 8642887681 10 Manual.Count131072.C065910.packed 64 cuts65910 = true := by
 decide +kernel
def cuts65911 : List PrefixCut := [⟨7,19963391,19963403⟩,
⟨64,185889517,185889622⟩]
theorem checked65911 : checkPrefixCuts (2^48) 8643018753 10 Manual.Count131072.C065911.packed 64 cuts65911 = true := by
 decide +kernel
def pointBounds65911 : List (Nat × Nat × Nat) := [(8643033088,115074638911703,115075027985074)]
theorem point_links_checked65911 : (cuts65911.take 1).map (fun c => (8643018753-1+2*2^10*c.k,115074618948312+c.lower,115075008021671+c.upper)) = pointBounds65911 := by
 decide +kernel
def cuts65912 : List PrefixCut := [⟨64,187482426,187482526⟩]
theorem checked65912 : checkPrefixCuts (2^48) 8643149825 10 Manual.Count131072.C065912.packed 64 cuts65912 = true := by
 decide +kernel
def cuts65913 : List PrefixCut := [⟨11,31979521,31979541⟩,
⟨64,188749639,188749747⟩]
theorem checked65913 : checkPrefixCuts (2^48) 8643280897 10 Manual.Count131072.C065913.packed 64 cuts65913 = true := by
 decide +kernel
def pointBounds65913 : List (Nat × Nat × Nat) := [(8643303424,115075024299776,115075413373360)]
theorem point_links_checked65913 : (cuts65913.take 1).map (fun c => (8643280897-1+2*2^10*c.k,115074992320255+c.lower,115075381393819+c.upper)) = pointBounds65913 := by
 decide +kernel
def cuts65914 : List PrefixCut := [⟨64,184643595,184643704⟩]
theorem checked65914 : checkPrefixCuts (2^48) 8643411969 10 Manual.Count131072.C065914.packed 64 cuts65914 = true := by
 decide +kernel
def cuts65915 : List PrefixCut := [⟨15,42952840,42952865⟩,
⟨64,186334142,186334247⟩]
theorem checked65915 : checkPrefixCuts (2^48) 8643543041 10 Manual.Count131072.C065915.packed 64 cuts65915 = true := by
 decide +kernel
def pointBounds65915 : List (Nat × Nat × Nat) := [(8643573760,115075408666329,115075797740135)]
theorem point_links_checked65915 : (cuts65915.take 1).map (fun c => (8643543041-1+2*2^10*c.k,115075365713489+c.lower,115075754787270+c.upper)) = pointBounds65915 := by
 decide +kernel
def cuts65916 : List PrefixCut := [⟨64,185745159,185745269⟩]
theorem checked65916 : checkPrefixCuts (2^48) 8643674113 10 Manual.Count131072.C065916.packed 64 cuts65916 = true := by
 decide +kernel
def cuts65917 : List PrefixCut := [⟨19,56660834,56660868⟩,
⟨64,188445121,188445229⟩]
theorem checked65917 : checkPrefixCuts (2^48) 8643805185 10 Manual.Count131072.C065917.packed 64 cuts65917 = true := by
 decide +kernel
def pointBounds65917 : List (Nat × Nat × Nat) := [(8643844096,115075794453624,115076183527654)]
theorem point_links_checked65917 : (cuts65917.take 1).map (fun c => (8643805185-1+2*2^10*c.k,115075737792790+c.lower,115076126866786+c.upper)) = pointBounds65917 := by
 decide +kernel
def cuts65918 : List PrefixCut := [⟨64,186195412,186195512⟩]
theorem checked65918 : checkPrefixCuts (2^48) 8643936257 10 Manual.Count131072.C065918.packed 64 cuts65918 = true := by
 decide +kernel
def cuts65919 : List PrefixCut := [⟨23,66134830,66134868⟩,
⟨64,184792390,184792494⟩]
theorem checked65919 : checkPrefixCuts (2^48) 8644067329 10 Manual.Count131072.C065919.packed 64 cuts65919 = true := by
 decide +kernel
def pointBounds65919 : List (Nat × Nat × Nat) := [(8644114432,115076178568153,115076567642395)]
theorem point_links_checked65919 : (cuts65919.take 1).map (fun c => (8644067329-1+2*2^10*c.k,115076112433323+c.lower,115076501507527+c.upper)) = pointBounds65919 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000184
