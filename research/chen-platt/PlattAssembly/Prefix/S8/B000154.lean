import PlattAssemblyKernel
import PlattCertificates.Count131072.C074928
import PlattCertificates.Count131072.C074929
import PlattCertificates.Count131072.C074930
import PlattCertificates.Count131072.C074931
import PlattCertificates.Count131072.C074932
import PlattCertificates.Count131072.C074933
import PlattCertificates.Count131072.C074934
import PlattCertificates.Count131072.C074935
import PlattCertificates.Count131072.C074936
import PlattCertificates.Count131072.C074937
import PlattCertificates.Count131072.C074938
import PlattCertificates.Count131072.C074939
import PlattCertificates.Count131072.C074940
import PlattCertificates.Count131072.C074941
import PlattCertificates.Count131072.C074942
import PlattCertificates.Count131072.C074943
import PlattCertificates.Count131072.C074944
import PlattCertificates.Count131072.C074945
import PlattCertificates.Count131072.C074946
import PlattCertificates.Count131072.C074947
import PlattCertificates.Count131072.C074948
import PlattCertificates.Count131072.C074949
import PlattCertificates.Count131072.C074950
import PlattCertificates.Count131072.C074951
import PlattCertificates.Count131072.C074952
import PlattCertificates.Count131072.C074953
import PlattCertificates.Count131072.C074954
import PlattCertificates.Count131072.C074955
import PlattCertificates.Count131072.C074956
import PlattCertificates.Count131072.C074957
import PlattCertificates.Count131072.C074958
import PlattCertificates.Count131072.C074959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000154
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74928 : List PrefixCut := [⟨19,49792124,49792156⟩,
⟨64,164788818,164788922⟩]
theorem checked74928 : checkPrefixCuts (2^48) 9824894977 10 Manual.Count131072.C074928.packed 64 cuts74928 = true := by
 decide +kernel
def pointBounds74928 : List (Nat × Nat × Nat) := [(9824933888,116647029471883,116647419472220)]
theorem point_links_checked74928 : (cuts74928.take 1).map (fun c => (9824894977-1+2*2^10*c.k,116646979679759+c.lower,116647369680064+c.upper)) = pointBounds74928 := by
 decide +kernel
def cuts74929 : List PrefixCut := [⟨64,164815270,164815365⟩]
theorem checked74929 : checkPrefixCuts (2^48) 9825026049 10 Manual.Count131072.C074929.packed 64 cuts74929 = true := by
 decide +kernel
def cuts74930 : List PrefixCut := [⟨41,105396960,105397025⟩,
⟨64,162893638,162893738⟩]
theorem checked74930 : checkPrefixCuts (2^48) 9825157121 10 Manual.Count131072.C074930.packed 64 cuts74930 = true := by
 decide +kernel
def pointBounds74930 : List (Nat × Nat × Nat) := [(9825241088,116647414680807,116647804681376)]
theorem point_links_checked74930 : (cuts74930.take 1).map (fun c => (9825157121-1+2*2^10*c.k,116647309283847+c.lower,116647699284351+c.upper)) = pointBounds74930 := by
 decide +kernel
def cuts74931 : List PrefixCut := [⟨64,163349823,163349919⟩]
theorem checked74931 : checkPrefixCuts (2^48) 9825288193 10 Manual.Count131072.C074931.packed 64 cuts74931 = true := by
 decide +kernel
def cuts74932 : List PrefixCut := [⟨63,160540220,160540321⟩,
⟨64,162831999,162832102⟩]
theorem checked74932 : checkPrefixCuts (2^48) 9825419265 10 Manual.Count131072.C074932.packed 64 cuts74932 = true := by
 decide +kernel
def pointBounds74932 : List (Nat × Nat × Nat) := [(9825548288,116647796067528,116648186068329)]
theorem point_links_checked74932 : (cuts74932.take 1).map (fun c => (9825419265-1+2*2^10*c.k,116647635527308+c.lower,116648025528008+c.upper)) = pointBounds74932 := by
 decide +kernel
def cuts74933 : List PrefixCut := [⟨64,161769878,161769971⟩]
theorem checked74933 : checkPrefixCuts (2^48) 9825550337 10 Manual.Count131072.C074933.packed 64 cuts74933 = true := by
 decide +kernel
def cuts74934 : List PrefixCut := [⟨64,164116744,164116843⟩]
theorem checked74934 : checkPrefixCuts (2^48) 9825681409 10 Manual.Count131072.C074934.packed 64 cuts74934 = true := by
 decide +kernel
def cuts74935 : List PrefixCut := [⟨21,54657356,54657389⟩,
⟨64,164572904,164573002⟩]
theorem checked74935 : checkPrefixCuts (2^48) 9825812481 10 Manual.Count131072.C074935.packed 64 cuts74935 = true := by
 decide +kernel
def pointBounds74935 : List (Nat × Nat × Nat) := [(9825855488,116648178903285,116648568904313)]
theorem point_links_checked74935 : (cuts74935.take 1).map (fun c => (9825812481-1+2*2^10*c.k,116648124245929+c.lower,116648514246924+c.upper)) = pointBounds74935 := by
 decide +kernel
def cuts74936 : List PrefixCut := [⟨64,163367571,163367670⟩]
theorem checked74936 : checkPrefixCuts (2^48) 9825943553 10 Manual.Count131072.C074936.packed 64 cuts74936 = true := by
 decide +kernel
def cuts74937 : List PrefixCut := [⟨43,109311543,109311605⟩,
⟨64,163021652,163021747⟩]
theorem checked74937 : checkPrefixCuts (2^48) 9826074625 10 Manual.Count131072.C074937.packed 64 cuts74937 = true := by
 decide +kernel
def pointBounds74937 : List (Nat × Nat × Nat) := [(9826162688,116648561497947,116648951499201)]
theorem point_links_checked74937 : (cuts74937.take 1).map (fun c => (9826074625-1+2*2^10*c.k,116648452186404+c.lower,116648842187596+c.upper)) = pointBounds74937 := by
 decide +kernel
def cuts74938 : List PrefixCut := [⟨64,165110570,165110665⟩]
theorem checked74938 : checkPrefixCuts (2^48) 9826205697 10 Manual.Count131072.C074938.packed 64 cuts74938 = true := by
 decide +kernel
def cuts74939 : List PrefixCut := [⟨64,164048510,164048607⟩]
theorem checked74939 : checkPrefixCuts (2^48) 9826336769 10 Manual.Count131072.C074939.packed 64 cuts74939 = true := by
 decide +kernel
def cuts74940 : List PrefixCut := [⟨1,2635300,2635301⟩,
⟨64,162843263,162843358⟩]
theorem checked74940 : checkPrefixCuts (2^48) 9826467841 10 Manual.Count131072.C074940.packed 64 cuts74940 = true := by
 decide +kernel
def pointBounds74940 : List (Nat × Nat × Nat) := [(9826469888,116648947002436,116649337003916)]
theorem point_links_checked74940 : (cuts74940.take 1).map (fun c => (9826467841-1+2*2^10*c.k,116648944367136+c.lower,116649334368615+c.upper)) = pointBounds74940 := by
 decide +kernel
def cuts74941 : List PrefixCut := [⟨64,162067706,162067802⟩]
theorem checked74941 : checkPrefixCuts (2^48) 9826598913 10 Manual.Count131072.C074941.packed 64 cuts74941 = true := by
 decide +kernel
def cuts74942 : List PrefixCut := [⟨23,55769344,55769376⟩,
⟨64,160203697,160203797⟩]
theorem checked74942 : checkPrefixCuts (2^48) 9826729985 10 Manual.Count131072.C074942.packed 64 cuts74942 = true := by
 decide +kernel
def pointBounds74942 : List (Nat × Nat × Nat) := [(9826777088,116649325047449,116649715049151)]
theorem point_links_checked74942 : (cuts74942.take 1).map (fun c => (9826729985-1+2*2^10*c.k,116649269278105+c.lower,116649659279775+c.upper)) = pointBounds74942 := by
 decide +kernel
def cuts74943 : List PrefixCut := [⟨64,161805593,161805690⟩]
theorem checked74943 : checkPrefixCuts (2^48) 9826861057 10 Manual.Count131072.C074943.packed 64 cuts74943 = true := by
 decide +kernel
def cuts74944 : List PrefixCut := [⟨45,116605252,116605319⟩,
⟨64,165526999,165527097⟩]
theorem checked74944 : checkPrefixCuts (2^48) 9826992129 10 Manual.Count131072.C074944.packed 64 cuts74944 = true := by
 decide +kernel
def pointBounds74944 : List (Nat × Nat × Nat) := [(9827084288,116649707892647,116650097894581)]
theorem point_links_checked74944 : (cuts74944.take 1).map (fun c => (9826992129-1+2*2^10*c.k,116649591287395+c.lower,116649981289262+c.upper)) = pointBounds74944 := by
 decide +kernel
def cuts74945 : List PrefixCut := [⟨64,164178595,164178695⟩]
theorem checked74945 : checkPrefixCuts (2^48) 9827123201 10 Manual.Count131072.C074945.packed 64 cuts74945 = true := by
 decide +kernel
def cuts74946 : List PrefixCut := [⟨64,160452935,160453034⟩]
theorem checked74946 : checkPrefixCuts (2^48) 9827254273 10 Manual.Count131072.C074946.packed 64 cuts74946 = true := by
 decide +kernel
def cuts74947 : List PrefixCut := [⟨3,7360963,7360969⟩,
⟨64,163486807,163486910⟩]
theorem checked74947 : checkPrefixCuts (2^48) 9827385345 10 Manual.Count131072.C074947.packed 64 cuts74947 = true := by
 decide +kernel
def pointBounds74947 : List (Nat × Nat × Nat) := [(9827391488,116650088806887,116650478809057)]
theorem point_links_checked74947 : (cuts74947.take 1).map (fun c => (9827385345-1+2*2^10*c.k,116650081445924+c.lower,116650471448088+c.upper)) = pointBounds74947 := by
 decide +kernel
def cuts74948 : List PrefixCut := [⟨64,162768599,162768705⟩]
theorem checked74948 : checkPrefixCuts (2^48) 9827516417 10 Manual.Count131072.C074948.packed 64 cuts74948 = true := by
 decide +kernel
def cuts74949 : List PrefixCut := [⟨25,62294288,62294325⟩,
⟨64,161248464,161248557⟩]
theorem checked74949 : checkPrefixCuts (2^48) 9827647489 10 Manual.Count131072.C074949.packed 64 cuts74949 = true := by
 decide +kernel
def pointBounds74949 : List (Nat × Nat × Nat) := [(9827698688,116650469995618,116650859998028)]
theorem point_links_checked74949 : (cuts74949.take 1).map (fun c => (9827647489-1+2*2^10*c.k,116650407701330+c.lower,116650797703703+c.upper)) = pointBounds74949 := by
 decide +kernel
def cuts74950 : List PrefixCut := [⟨64,163709396,163709503⟩]
theorem checked74950 : checkPrefixCuts (2^48) 9827778561 10 Manual.Count131072.C074950.packed 64 cuts74950 = true := by
 decide +kernel
def cuts74951 : List PrefixCut := [⟨47,119887970,119888046⟩,
⟨64,161444655,161444757⟩]
theorem checked74951 : checkPrefixCuts (2^48) 9827909633 10 Manual.Count131072.C074951.packed 64 cuts74951 = true := by
 decide +kernel
def pointBounds74951 : List (Nat × Nat × Nat) := [(9828005888,116650852547160,116651242549809)]
theorem point_links_checked74951 : (cuts74951.take 1).map (fun c => (9827909633-1+2*2^10*c.k,116650732659190+c.lower,116651122661763+c.upper)) = pointBounds74951 := by
 decide +kernel
def cuts74952 : List PrefixCut := [⟨64,160611942,160612036⟩]
theorem checked74952 : checkPrefixCuts (2^48) 9828040705 10 Manual.Count131072.C074952.packed 64 cuts74952 = true := by
 decide +kernel
def cuts74953 : List PrefixCut := [⟨64,163130056,163130149⟩]
theorem checked74953 : checkPrefixCuts (2^48) 9828171777 10 Manual.Count131072.C074953.packed 64 cuts74953 = true := by
 decide +kernel
def cuts74954 : List PrefixCut := [⟨5,12458052,12458061⟩,
⟨64,163271082,163271182⟩]
theorem checked74954 : checkPrefixCuts (2^48) 9828302849 10 Manual.Count131072.C074954.packed 64 cuts74954 = true := by
 decide +kernel
def pointBounds74954 : List (Nat × Nat × Nat) := [(9828313088,116651230303895,116651620306766)]
theorem point_links_checked74954 : (cuts74954.take 1).map (fun c => (9828302849-1+2*2^10*c.k,116651217845843+c.lower,116651607848705+c.upper)) = pointBounds74954 := by
 decide +kernel
def cuts74955 : List PrefixCut := [⟨64,162896599,162896699⟩]
theorem checked74955 : checkPrefixCuts (2^48) 9828433921 10 Manual.Count131072.C074955.packed 64 cuts74955 = true := by
 decide +kernel
def cuts74956 : List PrefixCut := [⟨27,69075753,69075792⟩,
⟨64,162035289,162035393⟩]
theorem checked74956 : checkPrefixCuts (2^48) 9828564993 10 Manual.Count131072.C074956.packed 64 cuts74956 = true := by
 decide +kernel
def pointBounds74956 : List (Nat × Nat × Nat) := [(9828620288,116651613089277,116652003092378)]
theorem point_links_checked74956 : (cuts74956.take 1).map (fun c => (9828564993-1+2*2^10*c.k,116651544013524+c.lower,116651934016586+c.upper)) = pointBounds74956 := by
 decide +kernel
def cuts74957 : List PrefixCut := [⟨64,162634517,162634617⟩]
theorem checked74957 : checkPrefixCuts (2^48) 9828696065 10 Manual.Count131072.C074957.packed 64 cuts74957 = true := by
 decide +kernel
def cuts74958 : List PrefixCut := [⟨49,126205651,126205729⟩,
⟨64,165209724,165209826⟩]
theorem checked74958 : checkPrefixCuts (2^48) 9828827137 10 Manual.Count131072.C074958.packed 64 cuts74958 = true := by
 decide +kernel
def pointBounds74958 : List (Nat × Nat × Nat) := [(9828927488,116651994888981,116652384892325)]
theorem point_links_checked74958 : (cuts74958.take 1).map (fun c => (9828827137-1+2*2^10*c.k,116651868683330+c.lower,116652258686596+c.upper)) = pointBounds74958 := by
 decide +kernel
def cuts74959 : List PrefixCut := [⟨64,162544267,162544369⟩]
theorem checked74959 : checkPrefixCuts (2^48) 9828958209 10 Manual.Count131072.C074959.packed 64 cuts74959 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000154
