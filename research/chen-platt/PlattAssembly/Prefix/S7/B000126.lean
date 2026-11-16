import PlattAssemblyKernel
import PlattCertificates.Count131072.C064032
import PlattCertificates.Count131072.C064033
import PlattCertificates.Count131072.C064034
import PlattCertificates.Count131072.C064035
import PlattCertificates.Count131072.C064036
import PlattCertificates.Count131072.C064037
import PlattCertificates.Count131072.C064038
import PlattCertificates.Count131072.C064039
import PlattCertificates.Count131072.C064040
import PlattCertificates.Count131072.C064041
import PlattCertificates.Count131072.C064042
import PlattCertificates.Count131072.C064043
import PlattCertificates.Count131072.C064044
import PlattCertificates.Count131072.C064045
import PlattCertificates.Count131072.C064046
import PlattCertificates.Count131072.C064047
import PlattCertificates.Count131072.C064048
import PlattCertificates.Count131072.C064049
import PlattCertificates.Count131072.C064050
import PlattCertificates.Count131072.C064051
import PlattCertificates.Count131072.C064052
import PlattCertificates.Count131072.C064053
import PlattCertificates.Count131072.C064054
import PlattCertificates.Count131072.C064055
import PlattCertificates.Count131072.C064056
import PlattCertificates.Count131072.C064057
import PlattCertificates.Count131072.C064058
import PlattCertificates.Count131072.C064059
import PlattCertificates.Count131072.C064060
import PlattCertificates.Count131072.C064061
import PlattCertificates.Count131072.C064062
import PlattCertificates.Count131072.C064063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000126
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64032 : List PrefixCut := [⟨64,195129748,195129860⟩]
theorem checked64032 : checkPrefixCuts (2^48) 8396734465 10 Manual.Count131072.C064032.packed 64 cuts64032 = true := by
 decide +kernel
def cuts64033 : List PrefixCut := [⟨15,44918627,44918653⟩,
⟨64,195595984,195596095⟩]
theorem checked64033 : checkPrefixCuts (2^48) 8396865537 10 Manual.Count131072.C064033.packed 64 cuts64033 = true := by
 decide +kernel
def pointBounds64033 : List (Nat × Nat × Nat) := [(8396896256,114718975763391,114719364630940)]
theorem point_links_checked64033 : (cuts64033.take 1).map (fun c => (8396865537-1+2*2^10*c.k,114718930844764+c.lower,114719319712287+c.upper)) = pointBounds64033 := by
 decide +kernel
def cuts64034 : List PrefixCut := [⟨64,190832999,190833111⟩]
theorem checked64034 : checkPrefixCuts (2^48) 8396996609 10 Manual.Count131072.C064034.packed 64 cuts64034 = true := by
 decide +kernel
def cuts64035 : List PrefixCut := [⟨16,47230120,47230145⟩,
⟨64,192003217,192003327⟩]
theorem checked64035 : checkPrefixCuts (2^48) 8397127681 10 Manual.Count131072.C064035.packed 64 cuts64035 = true := by
 decide +kernel
def pointBounds64035 : List (Nat × Nat × Nat) := [(8397160448,114719364503867,114719753371638)]
theorem point_links_checked64035 : (cuts64035.take 1).map (fun c => (8397127681-1+2*2^10*c.k,114719317273747+c.lower,114719706141493+c.upper)) = pointBounds64035 := by
 decide +kernel
def cuts64036 : List PrefixCut := [⟨64,193810300,193810405⟩]
theorem checked64036 : checkPrefixCuts (2^48) 8397258753 10 Manual.Count131072.C064036.packed 64 cuts64036 = true := by
 decide +kernel
def cuts64037 : List PrefixCut := [⟨17,49574987,49575016⟩,
⟨64,190790529,190790636⟩]
theorem checked64037 : checkPrefixCuts (2^48) 8397389825 10 Manual.Count131072.C064037.packed 64 cuts64037 = true := by
 decide +kernel
def pointBounds64037 : List (Nat × Nat × Nat) := [(8397424640,114719752662251,114720141530241)]
theorem point_links_checked64037 : (cuts64037.take 1).map (fun c => (8397389825-1+2*2^10*c.k,114719703087264+c.lower,114720091955225+c.upper)) = pointBounds64037 := by
 decide +kernel
def cuts64038 : List PrefixCut := [⟨64,191860178,191860294⟩]
theorem checked64038 : checkPrefixCuts (2^48) 8397520897 10 Manual.Count131072.C064038.packed 64 cuts64038 = true := by
 decide +kernel
def cuts64039 : List PrefixCut := [⟨18,53193400,53193433⟩,
⟨64,194069357,194069469⟩]
theorem checked64039 : checkPrefixCuts (2^48) 8397651969 10 Manual.Count131072.C064039.packed 64 cuts64039 = true := by
 decide +kernel
def pointBounds64039 : List (Nat × Nat × Nat) := [(8397688832,114720138931371,114720527799588)]
theorem point_links_checked64039 : (cuts64039.take 1).map (fun c => (8397651969-1+2*2^10*c.k,114720085737971+c.lower,114720474606155+c.upper)) = pointBounds64039 := by
 decide +kernel
def cuts64040 : List PrefixCut := [⟨64,193798181,193798297⟩]
theorem checked64040 : checkPrefixCuts (2^48) 8397783041 10 Manual.Count131072.C064040.packed 64 cuts64040 = true := by
 decide +kernel
def cuts64041 : List PrefixCut := [⟨19,55940141,55940175⟩,
⟨64,191851158,191851270⟩]
theorem checked64041 : checkPrefixCuts (2^48) 8397914113 10 Manual.Count131072.C064041.packed 64 cuts64041 = true := by
 decide +kernel
def pointBounds64041 : List (Nat × Nat × Nat) := [(8397953024,114720529545650,114720918414096)]
theorem point_links_checked64041 : (cuts64041.take 1).map (fun c => (8397914113-1+2*2^10*c.k,114720473605509+c.lower,114720862473921+c.upper)) = pointBounds64041 := by
 decide +kernel
def cuts64042 : List PrefixCut := [⟨64,192149836,192149949⟩]
theorem checked64042 : checkPrefixCuts (2^48) 8398045185 10 Manual.Count131072.C064042.packed 64 cuts64042 = true := by
 decide +kernel
def cuts64043 : List PrefixCut := [⟨20,60831742,60831778⟩,
⟨64,193252865,193252975⟩]
theorem checked64043 : checkPrefixCuts (2^48) 8398176257 10 Manual.Count131072.C064043.packed 64 cuts64043 = true := by
 decide +kernel
def pointBounds64043 : List (Nat × Nat × Nat) := [(8398217216,114720918438245,114721307306918)]
theorem point_links_checked64043 : (cuts64043.take 1).map (fun c => (8398176257-1+2*2^10*c.k,114720857606503+c.lower,114721246475140+c.upper)) = pointBounds64043 := by
 decide +kernel
def cuts64044 : List PrefixCut := [⟨64,194121245,194121356⟩]
theorem checked64044 : checkPrefixCuts (2^48) 8398307329 10 Manual.Count131072.C064044.packed 64 cuts64044 = true := by
 decide +kernel
def cuts64045 : List PrefixCut := [⟨21,63276433,63276471⟩,
⟨64,192911672,192911788⟩]
theorem checked64045 : checkPrefixCuts (2^48) 8398438401 10 Manual.Count131072.C064045.packed 64 cuts64045 = true := by
 decide +kernel
def pointBounds64045 : List (Nat × Nat × Nat) := [(8398481408,114721308257046,114721697125942)]
theorem point_links_checked64045 : (cuts64045.take 1).map (fun c => (8398438401-1+2*2^10*c.k,114721244980613+c.lower,114721633849471+c.upper)) = pointBounds64045 := by
 decide +kernel
def cuts64046 : List PrefixCut := [⟨64,191467562,191467667⟩]
theorem checked64046 : checkPrefixCuts (2^48) 8398569473 10 Manual.Count131072.C064046.packed 64 cuts64046 = true := by
 decide +kernel
def cuts64047 : List PrefixCut := [⟨22,67128561,67128601⟩,
⟨64,194681891,194682003⟩]
theorem checked64047 : checkPrefixCuts (2^48) 8398700545 10 Manual.Count131072.C064047.packed 64 cuts64047 = true := by
 decide +kernel
def pointBounds64047 : List (Nat × Nat × Nat) := [(8398745600,114721696488408,114722085357527)]
theorem point_links_checked64047 : (cuts64047.take 1).map (fun c => (8398700545-1+2*2^10*c.k,114721629359847+c.lower,114722018228926+c.upper)) = pointBounds64047 := by
 decide +kernel
def cuts64048 : List PrefixCut := [⟨64,187976191,187976303⟩]
theorem checked64048 : checkPrefixCuts (2^48) 8398831617 10 Manual.Count131072.C064048.packed 64 cuts64048 = true := by
 decide +kernel
def cuts64049 : List PrefixCut := [⟨23,69908038,69908077⟩,
⟨64,192296413,192296517⟩]
theorem checked64049 : checkPrefixCuts (2^48) 8398962689 10 Manual.Count131072.C064049.packed 64 cuts64049 = true := by
 decide +kernel
def pointBounds64049 : List (Nat × Nat × Nat) := [(8399009792,114722081925967,114722470795309)]
theorem point_links_checked64049 : (cuts64049.take 1).map (fun c => (8398962689-1+2*2^10*c.k,114722012017929+c.lower,114722400887232+c.upper)) = pointBounds64049 := by
 decide +kernel
def cuts64050 : List PrefixCut := [⟨64,191254509,191254621⟩]
theorem checked64050 : checkPrefixCuts (2^48) 8399093761 10 Manual.Count131072.C064050.packed 64 cuts64050 = true := by
 decide +kernel
def cuts64051 : List PrefixCut := [⟨24,71313346,71313388⟩,
⟨64,191117495,191117602⟩]
theorem checked64051 : checkPrefixCuts (2^48) 8399224833 10 Manual.Count131072.C064051.packed 64 cuts64051 = true := by
 decide +kernel
def pointBounds64051 : List (Nat × Nat × Nat) := [(8399273984,114722466882197,114722855751758)]
theorem point_links_checked64051 : (cuts64051.take 1).map (fun c => (8399224833-1+2*2^10*c.k,114722395568851+c.lower,114722784438370+c.upper)) = pointBounds64051 := by
 decide +kernel
def cuts64052 : List PrefixCut := [⟨64,194532657,194532761⟩]
theorem checked64052 : checkPrefixCuts (2^48) 8399355905 10 Manual.Count131072.C064052.packed 64 cuts64052 = true := by
 decide +kernel
def cuts64053 : List PrefixCut := [⟨25,74695708,74695750⟩,
⟨64,191245571,191245680⟩]
theorem checked64053 : checkPrefixCuts (2^48) 8399486977 10 Manual.Count131072.C064053.packed 64 cuts64053 = true := by
 decide +kernel
def pointBounds64053 : List (Nat × Nat × Nat) := [(8399538176,114722855914711,114723244784483)]
theorem point_links_checked64053 : (cuts64053.take 1).map (fun c => (8399486977-1+2*2^10*c.k,114722781219003+c.lower,114723170088733+c.upper)) = pointBounds64053 := by
 decide +kernel
def cuts64054 : List PrefixCut := [⟨64,190538869,190538980⟩]
theorem checked64054 : checkPrefixCuts (2^48) 8399618049 10 Manual.Count131072.C064054.packed 64 cuts64054 = true := by
 decide +kernel
def cuts64055 : List PrefixCut := [⟨26,77005544,77005589⟩,
⟨64,191675221,191675333⟩]
theorem checked64055 : checkPrefixCuts (2^48) 8399749121 10 Manual.Count131072.C064055.packed 64 cuts64055 = true := by
 decide +kernel
def pointBounds64055 : List (Nat × Nat × Nat) := [(8399802368,114723240008987,114723628878982)]
theorem point_links_checked64055 : (cuts64055.take 1).map (fun c => (8399749121-1+2*2^10*c.k,114723163003443+c.lower,114723551873393+c.upper)) = pointBounds64055 := by
 decide +kernel
def cuts64056 : List PrefixCut := [⟨64,193816822,193816938⟩]
theorem checked64056 : checkPrefixCuts (2^48) 8399880193 10 Manual.Count131072.C064056.packed 64 cuts64056 = true := by
 decide +kernel
def cuts64057 : List PrefixCut := [⟨27,80756112,80756160⟩,
⟨64,191032586,191032699⟩]
theorem checked64057 : checkPrefixCuts (2^48) 8400011265 10 Manual.Count131072.C064057.packed 64 cuts64057 = true := by
 decide +kernel
def pointBounds64057 : List (Nat × Nat × Nat) := [(8400066560,114723629251598,114724018121824)]
theorem point_links_checked64057 : (cuts64057.take 1).map (fun c => (8400011265-1+2*2^10*c.k,114723548495486+c.lower,114723937365664+c.upper)) = pointBounds64057 := by
 decide +kernel
def cuts64058 : List PrefixCut := [⟨64,191900809,191900917⟩]
theorem checked64058 : checkPrefixCuts (2^48) 8400142337 10 Manual.Count131072.C064058.packed 64 cuts64058 = true := by
 decide +kernel
def cuts64059 : List PrefixCut := [⟨28,85076075,85076123⟩,
⟨64,193640217,193640331⟩]
theorem checked64059 : checkPrefixCuts (2^48) 8400273409 10 Manual.Count131072.C064059.packed 64 cuts64059 = true := by
 decide +kernel
def pointBounds64059 : List (Nat × Nat × Nat) := [(8400330752,114724016504956,114724405375403)]
theorem point_links_checked64059 : (cuts64059.take 1).map (fun c => (8400273409-1+2*2^10*c.k,114723931428881+c.lower,114724320299280+c.upper)) = pointBounds64059 := by
 decide +kernel
def cuts64060 : List PrefixCut := [⟨64,192967049,192967158⟩]
theorem checked64060 : checkPrefixCuts (2^48) 8400404481 10 Manual.Count131072.C064060.packed 64 cuts64060 = true := by
 decide +kernel
def cuts64061 : List PrefixCut := [⟨29,86782255,86782305⟩,
⟨64,192159881,192159994⟩]
theorem checked64061 : checkPrefixCuts (2^48) 8400535553 10 Manual.Count131072.C064061.packed 64 cuts64061 = true := by
 decide +kernel
def pointBounds64061 : List (Nat × Nat × Nat) := [(8400594944,114724404818402,114724793689074)]
theorem point_links_checked64061 : (cuts64061.take 1).map (fun c => (8400535553-1+2*2^10*c.k,114724318036147+c.lower,114724706906769+c.upper)) = pointBounds64061 := by
 decide +kernel
def cuts64062 : List PrefixCut := [⟨64,191520273,191520383⟩]
theorem checked64062 : checkPrefixCuts (2^48) 8400666625 10 Manual.Count131072.C064062.packed 64 cuts64062 = true := by
 decide +kernel
def cuts64063 : List PrefixCut := [⟨30,92341463,92341518⟩,
⟨64,194700312,194700425⟩]
theorem checked64063 : checkPrefixCuts (2^48) 8400797697 10 Manual.Count131072.C064063.packed 64 cuts64063 = true := by
 decide +kernel
def pointBounds64063 : List (Nat × Nat × Nat) := [(8400859136,114724794057764,114725182928664)]
theorem point_links_checked64063 : (cuts64063.take 1).map (fun c => (8400797697-1+2*2^10*c.k,114724701716301+c.lower,114725090587146+c.upper)) = pointBounds64063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000126
