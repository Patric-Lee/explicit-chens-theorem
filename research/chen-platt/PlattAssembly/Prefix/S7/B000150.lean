import PlattAssemblyKernel
import PlattCertificates.Count131072.C064800
import PlattCertificates.Count131072.C064801
import PlattCertificates.Count131072.C064802
import PlattCertificates.Count131072.C064803
import PlattCertificates.Count131072.C064804
import PlattCertificates.Count131072.C064805
import PlattCertificates.Count131072.C064806
import PlattCertificates.Count131072.C064807
import PlattCertificates.Count131072.C064808
import PlattCertificates.Count131072.C064809
import PlattCertificates.Count131072.C064810
import PlattCertificates.Count131072.C064811
import PlattCertificates.Count131072.C064812
import PlattCertificates.Count131072.C064813
import PlattCertificates.Count131072.C064814
import PlattCertificates.Count131072.C064815
import PlattCertificates.Count131072.C064816
import PlattCertificates.Count131072.C064817
import PlattCertificates.Count131072.C064818
import PlattCertificates.Count131072.C064819
import PlattCertificates.Count131072.C064820
import PlattCertificates.Count131072.C064821
import PlattCertificates.Count131072.C064822
import PlattCertificates.Count131072.C064823
import PlattCertificates.Count131072.C064824
import PlattCertificates.Count131072.C064825
import PlattCertificates.Count131072.C064826
import PlattCertificates.Count131072.C064827
import PlattCertificates.Count131072.C064828
import PlattCertificates.Count131072.C064829
import PlattCertificates.Count131072.C064830
import PlattCertificates.Count131072.C064831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64800 : List PrefixCut := [⟨64,189870099,189870210⟩]
theorem checked64800 : checkPrefixCuts (2^48) 8497397761 10 Manual.Count131072.C064800.packed 64 cuts64800 = true := by
 decide +kernel
def cuts64801 : List PrefixCut := [⟨46,135047119,135047199⟩,
⟨64,188608444,188608555⟩]
theorem checked64801 : checkPrefixCuts (2^48) 8497528833 10 Manual.Count131072.C064801.packed 64 cuts64801 = true := by
 decide +kernel
def pointBounds64801 : List (Nat × Nat × Nat) := [(8497623040,114865807351177,114866196303470)]
theorem point_links_checked64801 : (cuts64801.take 1).map (fun c => (8497528833-1+2*2^10*c.k,114865672304058+c.lower,114866061256271+c.upper)) = pointBounds64801 := by
 decide +kernel
def cuts64802 : List PrefixCut := [⟨64,191752280,191752384⟩]
theorem checked64802 : checkPrefixCuts (2^48) 8497659905 10 Manual.Count131072.C064802.packed 64 cuts64802 = true := by
 decide +kernel
def cuts64803 : List PrefixCut := [⟨48,142727486,142727570⟩,
⟨64,189761940,189762052⟩]
theorem checked64803 : checkPrefixCuts (2^48) 8497790977 10 Manual.Count131072.C064803.packed 64 cuts64803 = true := by
 decide +kernel
def pointBounds64803 : List (Nat × Nat × Nat) := [(8497889280,114866195392268,114866584344780)]
theorem point_links_checked64803 : (cuts64803.take 1).map (fun c => (8497790977-1+2*2^10*c.k,114866052664782+c.lower,114866441617210+c.upper)) = pointBounds64803 := by
 decide +kernel
def cuts64804 : List PrefixCut := [⟨64,191183272,191183384⟩]
theorem checked64804 : checkPrefixCuts (2^48) 8497922049 10 Manual.Count131072.C064804.packed 64 cuts64804 = true := by
 decide +kernel
def cuts64805 : List PrefixCut := [⟨50,148254439,148254526⟩,
⟨64,189027405,189027513⟩]
theorem checked64805 : checkPrefixCuts (2^48) 8498053121 10 Manual.Count131072.C064805.packed 64 cuts64805 = true := by
 decide +kernel
def pointBounds64805 : List (Nat × Nat × Nat) := [(8498155520,114866581864433,114866970817172)]
theorem point_links_checked64805 : (cuts64805.take 1).map (fun c => (8498053121-1+2*2^10*c.k,114866433609994+c.lower,114866822562646+c.upper)) = pointBounds64805 := by
 decide +kernel
def cuts64806 : List PrefixCut := [⟨64,188494543,188494654⟩]
theorem checked64806 : checkPrefixCuts (2^48) 8498184193 10 Manual.Count131072.C064806.packed 64 cuts64806 = true := by
 decide +kernel
def cuts64807 : List PrefixCut := [⟨52,153416699,153416794⟩,
⟨64,189187159,189187271⟩]
theorem checked64807 : checkPrefixCuts (2^48) 8498315265 10 Manual.Count131072.C064807.packed 64 cuts64807 = true := by
 decide +kernel
def pointBounds64807 : List (Nat × Nat × Nat) := [(8498421760,114866964548641,114867353501607)]
theorem point_links_checked64807 : (cuts64807.take 1).map (fun c => (8498315265-1+2*2^10*c.k,114866811131942+c.lower,114867200084813+c.upper)) = pointBounds64807 := by
 decide +kernel
def cuts64808 : List PrefixCut := [⟨64,191668284,191668395⟩]
theorem checked64808 : checkPrefixCuts (2^48) 8498446337 10 Manual.Count131072.C064808.packed 64 cuts64808 = true := by
 decide +kernel
def cuts64809 : List PrefixCut := [⟨54,160168416,160168510⟩,
⟨64,190771079,190771191⟩]
theorem checked64809 : checkPrefixCuts (2^48) 8498577409 10 Manual.Count131072.C064809.packed 64 cuts64809 = true := by
 decide +kernel
def pointBounds64809 : List (Nat × Nat × Nat) := [(8498688000,114867352155801,114867741108989)]
theorem point_links_checked64809 : (cuts64809.take 1).map (fun c => (8498577409-1+2*2^10*c.k,114867191987385+c.lower,114867580940479+c.upper)) = pointBounds64809 := by
 decide +kernel
def cuts64810 : List PrefixCut := [⟨64,188317307,188317420⟩]
theorem checked64810 : checkPrefixCuts (2^48) 8498708481 10 Manual.Count131072.C064810.packed 64 cuts64810 = true := by
 decide +kernel
def cuts64811 : List PrefixCut := [⟨56,167118433,167118533⟩,
⟨64,192123080,192123193⟩]
theorem checked64811 : checkPrefixCuts (2^48) 8498839553 10 Manual.Count131072.C064811.packed 64 cuts64811 = true := by
 decide +kernel
def pointBounds64811 : List (Nat × Nat × Nat) := [(8498954240,114867738194204,114868127147623)]
theorem point_links_checked64811 : (cuts64811.take 1).map (fun c => (8498839553-1+2*2^10*c.k,114867571075771+c.lower,114867960029090+c.upper)) = pointBounds64811 := by
 decide +kernel
def cuts64812 : List PrefixCut := [⟨64,189139462,189139567⟩]
theorem checked64812 : checkPrefixCuts (2^48) 8498970625 10 Manual.Count131072.C064812.packed 64 cuts64812 = true := by
 decide +kernel
def cuts64813 : List PrefixCut := [⟨58,174862835,174862937⟩,
⟨64,191984689,191984802⟩]
theorem checked64813 : checkPrefixCuts (2^48) 8499101697 10 Manual.Count131072.C064813.packed 64 cuts64813 = true := by
 decide +kernel
def pointBounds64813 : List (Nat × Nat × Nat) := [(8499220480,114868127201148,114868516154787)]
theorem point_links_checked64813 : (cuts64813.take 1).map (fun c => (8499101697-1+2*2^10*c.k,114867952338313+c.lower,114868341291850+c.upper)) = pointBounds64813 := by
 decide +kernel
def cuts64814 : List PrefixCut := [⟨64,192842774,192842882⟩]
theorem checked64814 : checkPrefixCuts (2^48) 8499232769 10 Manual.Count131072.C064814.packed 64 cuts64814 = true := by
 decide +kernel
def cuts64815 : List PrefixCut := [⟨60,180818456,180818560⟩,
⟨64,192607994,192608103⟩]
theorem checked64815 : checkPrefixCuts (2^48) 8499363841 10 Manual.Count131072.C064815.packed 64 cuts64815 = true := by
 decide +kernel
def pointBounds64815 : List (Nat × Nat × Nat) := [(8499486720,114868517984232,114868906938094)]
theorem point_links_checked64815 : (cuts64815.take 1).map (fun c => (8499363841-1+2*2^10*c.k,114868337165776+c.lower,114868726119534+c.upper)) = pointBounds64815 := by
 decide +kernel
def cuts64816 : List PrefixCut := [⟨64,185783034,185783147⟩]
theorem checked64816 : checkPrefixCuts (2^48) 8499494913 10 Manual.Count131072.C064816.packed 64 cuts64816 = true := by
 decide +kernel
def cuts64817 : List PrefixCut := [⟨62,182965363,182965469⟩,
⟨64,188826833,188826942⟩]
theorem checked64817 : checkPrefixCuts (2^48) 8499625985 10 Manual.Count131072.C064817.packed 64 cuts64817 = true := by
 decide +kernel
def pointBounds64817 : List (Nat × Nat × Nat) := [(8499752960,114868898522167,114869287476253)]
theorem point_links_checked64817 : (cuts64817.take 1).map (fun c => (8499625985-1+2*2^10*c.k,114868715556804+c.lower,114869104510784+c.upper)) = pointBounds64817 := by
 decide +kernel
def cuts64818 : List PrefixCut := [⟨64,188790809,188790920⟩]
theorem checked64818 : checkPrefixCuts (2^48) 8499757057 10 Manual.Count131072.C064818.packed 64 cuts64818 = true := by
 decide +kernel
def cuts64819 : List PrefixCut := [⟨64,188920374,188920483⟩]
theorem checked64819 : checkPrefixCuts (2^48) 8499888129 10 Manual.Count131072.C064819.packed 64 cuts64819 = true := by
 decide +kernel
def pointBounds64819 : List (Nat × Nat × Nat) := [(8500019200,114869282094820,114869671049129)]
theorem point_links_checked64819 : (cuts64819.take 1).map (fun c => (8499888129-1+2*2^10*c.k,114869093174446+c.lower,114869482128646+c.upper)) = pointBounds64819 := by
 decide +kernel
def cuts64820 : List PrefixCut := [⟨64,189414156,189414263⟩]
theorem checked64820 : checkPrefixCuts (2^48) 8500019201 10 Manual.Count131072.C064820.packed 64 cuts64820 = true := by
 decide +kernel
def cuts64821 : List PrefixCut := [⟨64,190570216,190570324⟩]
theorem checked64821 : checkPrefixCuts (2^48) 8500150273 10 Manual.Count131072.C064821.packed 64 cuts64821 = true := by
 decide +kernel
def cuts64822 : List PrefixCut := [⟨2,5761764,5761768⟩,
⟨64,191097100,191097214⟩]
theorem checked64822 : checkPrefixCuts (2^48) 8500281345 10 Manual.Count131072.C064822.packed 64 cuts64822 = true := by
 decide +kernel
def pointBounds64822 : List (Nat × Nat × Nat) := [(8500285440,114869667840956,114870056795484)]
theorem point_links_checked64822 : (cuts64822.take 1).map (fun c => (8500281345-1+2*2^10*c.k,114869662079192+c.lower,114870051033716+c.upper)) = pointBounds64822 := by
 decide +kernel
def cuts64823 : List PrefixCut := [⟨64,188875581,188875693⟩]
theorem checked64823 : checkPrefixCuts (2^48) 8500412417 10 Manual.Count131072.C064823.packed 64 cuts64823 = true := by
 decide +kernel
def cuts64824 : List PrefixCut := [⟨4,11754960,11754965⟩,
⟨64,189634270,189634372⟩]
theorem checked64824 : checkPrefixCuts (2^48) 8500543489 10 Manual.Count131072.C064824.packed 64 cuts64824 = true := by
 decide +kernel
def pointBounds64824 : List (Nat × Nat × Nat) := [(8500551680,114870053806833,114870442761588)]
theorem point_links_checked64824 : (cuts64824.take 1).map (fun c => (8500543489-1+2*2^10*c.k,114870042051873+c.lower,114870431006623+c.upper)) = pointBounds64824 := by
 decide +kernel
def cuts64825 : List PrefixCut := [⟨64,189233996,189234105⟩]
theorem checked64825 : checkPrefixCuts (2^48) 8500674561 10 Manual.Count131072.C064825.packed 64 cuts64825 = true := by
 decide +kernel
def cuts64826 : List PrefixCut := [⟨6,17151773,17151784⟩,
⟨64,189297292,189297399⟩]
theorem checked64826 : checkPrefixCuts (2^48) 8500805633 10 Manual.Count131072.C064826.packed 64 cuts64826 = true := by
 decide +kernel
def pointBounds64826 : List (Nat × Nat × Nat) := [(8500817920,114870438071912,114870827026884)]
theorem point_links_checked64826 : (cuts64826.take 1).map (fun c => (8500805633-1+2*2^10*c.k,114870420920139+c.lower,114870809875100+c.upper)) = pointBounds64826 := by
 decide +kernel
def cuts64827 : List PrefixCut := [⟨64,191247935,191248044⟩]
theorem checked64827 : checkPrefixCuts (2^48) 8500936705 10 Manual.Count131072.C064827.packed 64 cuts64827 = true := by
 decide +kernel
def cuts64828 : List PrefixCut := [⟨8,23574678,23574691⟩,
⟨64,189986773,189986879⟩]
theorem checked64828 : checkPrefixCuts (2^48) 8501067777 10 Manual.Count131072.C064828.packed 64 cuts64828 = true := by
 decide +kernel
def pointBounds64828 : List (Nat × Nat × Nat) := [(8501084160,114870825040044,114871213995234)]
theorem point_links_checked64828 : (cuts64828.take 1).map (fun c => (8501067777-1+2*2^10*c.k,114870801465366+c.lower,114871190420543+c.upper)) = pointBounds64828 := by
 decide +kernel
def cuts64829 : List PrefixCut := [⟨64,188659459,188659562⟩]
theorem checked64829 : checkPrefixCuts (2^48) 8501198849 10 Manual.Count131072.C064829.packed 64 cuts64829 = true := by
 decide +kernel
def cuts64830 : List PrefixCut := [⟨10,29566759,29566776⟩,
⟨64,189219403,189219512⟩]
theorem checked64830 : checkPrefixCuts (2^48) 8501329921 10 Manual.Count131072.C064830.packed 64 cuts64830 = true := by
 decide +kernel
def pointBounds64830 : List (Nat × Nat × Nat) := [(8501350400,114871209678357,114871598633760)]
theorem point_links_checked64830 : (cuts64830.take 1).map (fun c => (8501329921-1+2*2^10*c.k,114871180111598+c.lower,114871569066984+c.upper)) = pointBounds64830 := by
 decide +kernel
def cuts64831 : List PrefixCut := [⟨64,188918502,188918614⟩]
theorem checked64831 : checkPrefixCuts (2^48) 8501460993 10 Manual.Count131072.C064831.packed 64 cuts64831 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000150
