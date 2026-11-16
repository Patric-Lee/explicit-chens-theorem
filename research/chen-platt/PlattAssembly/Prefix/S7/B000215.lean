import PlattAssemblyKernel
import PlattCertificates.Count131072.C066880
import PlattCertificates.Count131072.C066881
import PlattCertificates.Count131072.C066882
import PlattCertificates.Count131072.C066883
import PlattCertificates.Count131072.C066884
import PlattCertificates.Count131072.C066885
import PlattCertificates.Count131072.C066886
import PlattCertificates.Count131072.C066887
import PlattCertificates.Count131072.C066888
import PlattCertificates.Count131072.C066889
import PlattCertificates.Count131072.C066890
import PlattCertificates.Count131072.C066891
import PlattCertificates.Count131072.C066892
import PlattCertificates.Count131072.C066893
import PlattCertificates.Count131072.C066894
import PlattCertificates.Count131072.C066895
import PlattCertificates.Count131072.C066896
import PlattCertificates.Count131072.C066897
import PlattCertificates.Count131072.C066898
import PlattCertificates.Count131072.C066899
import PlattCertificates.Count131072.C066900
import PlattCertificates.Count131072.C066901
import PlattCertificates.Count131072.C066902
import PlattCertificates.Count131072.C066903
import PlattCertificates.Count131072.C066904
import PlattCertificates.Count131072.C066905
import PlattCertificates.Count131072.C066906
import PlattCertificates.Count131072.C066907
import PlattCertificates.Count131072.C066908
import PlattCertificates.Count131072.C066909
import PlattCertificates.Count131072.C066910
import PlattCertificates.Count131072.C066911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000215
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66880 : List PrefixCut := [⟨2,6226448,6226451⟩,
⟨64,187401895,187402007⟩]
theorem checked66880 : checkPrefixCuts (2^48) 8770027521 10 Manual.Count131072.C066880.packed 64 cuts66880 = true := by
 decide +kernel
def pointBounds66880 : List (Nat × Nat × Nat) := [(8770031616,115253988840894,115254378018394)]
theorem point_links_checked66880 : (cuts66880.take 1).map (fun c => (8770027521-1+2*2^10*c.k,115253982614446+c.lower,115254371791943+c.upper)) = pointBounds66880 := by
 decide +kernel
def cuts66881 : List PrefixCut := [⟨64,183290999,183291101⟩]
theorem checked66881 : checkPrefixCuts (2^48) 8770158593 10 Manual.Count131072.C066881.packed 64 cuts66881 = true := by
 decide +kernel
def cuts66882 : List PrefixCut := [⟨8,22754724,22754738⟩,
⟨64,184218978,184219082⟩]
theorem checked66882 : checkPrefixCuts (2^48) 8770289665 10 Manual.Count131072.C066882.packed 64 cuts66882 = true := by
 decide +kernel
def pointBounds66882 : List (Nat × Nat × Nat) := [(8770306048,115254376062064,115254765239789)]
theorem point_links_checked66882 : (cuts66882.take 1).map (fun c => (8770289665-1+2*2^10*c.k,115254353307340+c.lower,115254742485051+c.upper)) = pointBounds66882 := by
 decide +kernel
def cuts66883 : List PrefixCut := [⟨64,187553942,187554051⟩]
theorem checked66883 : checkPrefixCuts (2^48) 8770420737 10 Manual.Count131072.C066883.packed 64 cuts66883 = true := by
 decide +kernel
def cuts66884 : List PrefixCut := [⟨14,40405248,40405270⟩,
⟨64,185336728,185336836⟩]
theorem checked66884 : checkPrefixCuts (2^48) 8770551809 10 Manual.Count131072.C066884.packed 64 cuts66884 = true := by
 decide +kernel
def pointBounds66884 : List (Nat × Nat × Nat) := [(8770580480,115254765485508,115255154663454)]
theorem point_links_checked66884 : (cuts66884.take 1).map (fun c => (8770551809-1+2*2^10*c.k,115254725080260+c.lower,115255114258184+c.upper)) = pointBounds66884 := by
 decide +kernel
def cuts66885 : List PrefixCut := [⟨64,184306983,184307095⟩]
theorem checked66885 : checkPrefixCuts (2^48) 8770682881 10 Manual.Count131072.C066885.packed 64 cuts66885 = true := by
 decide +kernel
def cuts66886 : List PrefixCut := [⟨20,57091927,57091960⟩,
⟨64,181736890,181736997⟩]
theorem checked66886 : checkPrefixCuts (2^48) 8770813953 10 Manual.Count131072.C066886.packed 64 cuts66886 = true := by
 decide +kernel
def pointBounds66886 : List (Nat × Nat × Nat) := [(8770854912,115255151815898,115255540994075)]
theorem point_links_checked66886 : (cuts66886.take 1).map (fun c => (8770813953-1+2*2^10*c.k,115255094723971+c.lower,115255483902115+c.upper)) = pointBounds66886 := by
 decide +kernel
def cuts66887 : List PrefixCut := [⟨64,182793200,182793301⟩]
theorem checked66887 : checkPrefixCuts (2^48) 8770945025 10 Manual.Count131072.C066887.packed 64 cuts66887 = true := by
 decide +kernel
def cuts66888 : List PrefixCut := [⟨26,73841766,73841811⟩,
⟨64,182341188,182341296⟩]
theorem checked66888 : checkPrefixCuts (2^48) 8771076097 10 Manual.Count131072.C066888.packed 64 cuts66888 = true := by
 decide +kernel
def pointBounds66888 : List (Nat × Nat × Nat) := [(8771129344,115255533095827,115255922274224)]
theorem point_links_checked66888 : (cuts66888.take 1).map (fun c => (8771076097-1+2*2^10*c.k,115255459254061+c.lower,115255848432413+c.upper)) = pointBounds66888 := by
 decide +kernel
def cuts66889 : List PrefixCut := [⟨64,186927407,186927517⟩]
theorem checked66889 : checkPrefixCuts (2^48) 8771207169 10 Manual.Count131072.C066889.packed 64 cuts66889 = true := by
 decide +kernel
def cuts66890 : List PrefixCut := [⟨32,88665171,88665224⟩,
⟨64,179896871,179896984⟩]
theorem checked66890 : checkPrefixCuts (2^48) 8771338241 10 Manual.Count131072.C066890.packed 64 cuts66890 = true := by
 decide +kernel
def pointBounds66890 : List (Nat × Nat × Nat) := [(8771403776,115255917187827,115256306366450)]
theorem point_links_checked66890 : (cuts66890.take 1).map (fun c => (8771338241-1+2*2^10*c.k,115255828522656+c.lower,115256217701226+c.upper)) = pointBounds66890 := by
 decide +kernel
def cuts66891 : List PrefixCut := [⟨64,186536749,186536858⟩]
theorem checked66891 : checkPrefixCuts (2^48) 8771469313 10 Manual.Count131072.C066891.packed 64 cuts66891 = true := by
 decide +kernel
def cuts66892 : List PrefixCut := [⟨38,108814479,108814544⟩,
⟨64,182811623,182811731⟩]
theorem checked66892 : checkPrefixCuts (2^48) 8771600385 10 Manual.Count131072.C066892.packed 64 cuts66892 = true := by
 decide +kernel
def pointBounds66892 : List (Nat × Nat × Nat) := [(8771678208,115256303770755,115256692949612)]
theorem point_links_checked66892 : (cuts66892.take 1).map (fun c => (8771600385-1+2*2^10*c.k,115256194956276+c.lower,115256584135068+c.upper)) = pointBounds66892 := by
 decide +kernel
def cuts66893 : List PrefixCut := [⟨64,184637934,184638036⟩]
theorem checked66893 : checkPrefixCuts (2^48) 8771731457 10 Manual.Count131072.C066893.packed 64 cuts66893 = true := by
 decide +kernel
def cuts66894 : List PrefixCut := [⟨44,122448647,122448722⟩,
⟨64,180656244,180656354⟩]
theorem checked66894 : checkPrefixCuts (2^48) 8771862529 10 Manual.Count131072.C066894.packed 64 cuts66894 = true := by
 decide +kernel
def pointBounds66894 : List (Nat × Nat × Nat) := [(8771952640,115256684854480,115257074033557)]
theorem point_links_checked66894 : (cuts66894.take 1).map (fun c => (8771862529-1+2*2^10*c.k,115256562405833+c.lower,115256951584835+c.upper)) = pointBounds66894 := by
 decide +kernel
def cuts66895 : List PrefixCut := [⟨64,179594665,179594777⟩]
theorem checked66895 : checkPrefixCuts (2^48) 8771993601 10 Manual.Count131072.C066895.packed 64 cuts66895 = true := by
 decide +kernel
def cuts66896 : List PrefixCut := [⟨50,144135873,144135956⟩,
⟨64,183410357,183410465⟩]
theorem checked66896 : checkPrefixCuts (2^48) 8772124673 10 Manual.Count131072.C066896.packed 64 cuts66896 = true := by
 decide +kernel
def pointBounds66896 : List (Nat × Nat × Nat) := [(8772227072,115257066792615,115257455971922)]
theorem point_links_checked66896 : (cuts66896.take 1).map (fun c => (8772124673-1+2*2^10*c.k,115256922656742+c.lower,115257311835966+c.upper)) = pointBounds66896 := by
 decide +kernel
def cuts66897 : List PrefixCut := [⟨64,183985173,183985280⟩]
theorem checked66897 : checkPrefixCuts (2^48) 8772255745 10 Manual.Count131072.C066897.packed 64 cuts66897 = true := by
 decide +kernel
def cuts66898 : List PrefixCut := [⟨56,160431298,160431392⟩,
⟨64,184303294,184303402⟩]
theorem checked66898 : checkPrefixCuts (2^48) 8772386817 10 Manual.Count131072.C066898.packed 64 cuts66898 = true := by
 decide +kernel
def pointBounds66898 : List (Nat × Nat × Nat) := [(8772501504,115257450483570,115257839663103)]
theorem point_links_checked66898 : (cuts66898.take 1).map (fun c => (8772386817-1+2*2^10*c.k,115257290052272+c.lower,115257679231711+c.upper)) = pointBounds66898 := by
 decide +kernel
def cuts66899 : List PrefixCut := [⟨64,185551884,185551984⟩]
theorem checked66899 : checkPrefixCuts (2^48) 8772517889 10 Manual.Count131072.C066899.packed 64 cuts66899 = true := by
 decide +kernel
def cuts66900 : List PrefixCut := [⟨62,178426215,178426321⟩,
⟨64,184426117,184426226⟩]
theorem checked66900 : checkPrefixCuts (2^48) 8772648961 10 Manual.Count131072.C066900.packed 64 cuts66900 = true := by
 decide +kernel
def pointBounds66900 : List (Nat × Nat × Nat) := [(8772775936,115257838333665,115258227513418)]
theorem point_links_checked66900 : (cuts66900.take 1).map (fun c => (8772648961-1+2*2^10*c.k,115257659907450+c.lower,115258049087097+c.upper)) = pointBounds66900 := by
 decide +kernel
def cuts66901 : List PrefixCut := [⟨64,185289660,185289764⟩]
theorem checked66901 : checkPrefixCuts (2^48) 8772780033 10 Manual.Count131072.C066901.packed 64 cuts66901 = true := by
 decide +kernel
def cuts66902 : List PrefixCut := [⟨64,184484775,184484888⟩]
theorem checked66902 : checkPrefixCuts (2^48) 8772911105 10 Manual.Count131072.C066902.packed 64 cuts66902 = true := by
 decide +kernel
def cuts66903 : List PrefixCut := [⟨4,11839017,11839023⟩,
⟨64,181915322,181915423⟩]
theorem checked66903 : checkPrefixCuts (2^48) 8773042177 10 Manual.Count131072.C066903.packed 64 cuts66903 = true := by
 decide +kernel
def pointBounds66903 : List (Nat × Nat × Nat) := [(8773050368,115258225947019,115258615126998)]
theorem point_links_checked66903 : (cuts66903.take 1).map (fun c => (8773042177-1+2*2^10*c.k,115258214108002+c.lower,115258603287975+c.upper)) = pointBounds66903 := by
 decide +kernel
def cuts66904 : List PrefixCut := [⟨64,181688005,181688112⟩]
theorem checked66904 : checkPrefixCuts (2^48) 8773173249 10 Manual.Count131072.C066904.packed 64 cuts66904 = true := by
 decide +kernel
def cuts66905 : List PrefixCut := [⟨10,29227680,29227697⟩,
⟨64,187139394,187139504⟩]
theorem checked66905 : checkPrefixCuts (2^48) 8773304321 10 Manual.Count131072.C066905.packed 64 cuts66905 = true := by
 decide +kernel
def pointBounds66905 : List (Nat × Nat × Nat) := [(8773324800,115258606939009,115258996119207)]
theorem point_links_checked66905 : (cuts66905.take 1).map (fun c => (8773304321-1+2*2^10*c.k,115258577711329+c.lower,115258966891510+c.upper)) = pointBounds66905 := by
 decide +kernel
def cuts66906 : List PrefixCut := [⟨64,182645054,182645159⟩]
theorem checked66906 : checkPrefixCuts (2^48) 8773435393 10 Manual.Count131072.C066906.packed 64 cuts66906 = true := by
 decide +kernel
def cuts66907 : List PrefixCut := [⟨16,45075340,45075365⟩,
⟨64,179337893,179338002⟩]
theorem checked66907 : checkPrefixCuts (2^48) 8773566465 10 Manual.Count131072.C066907.packed 64 cuts66907 = true := by
 decide +kernel
def pointBounds66907 : List (Nat × Nat × Nat) := [(8773599232,115258992571117,115259381751538)]
theorem point_links_checked66907 : (cuts66907.take 1).map (fun c => (8773566465-1+2*2^10*c.k,115258947495777+c.lower,115259336676173+c.upper)) = pointBounds66907 := by
 decide +kernel
def cuts66908 : List PrefixCut := [⟨64,187195165,187195275⟩]
theorem checked66908 : checkPrefixCuts (2^48) 8773697537 10 Manual.Count131072.C066908.packed 64 cuts66908 = true := by
 decide +kernel
def cuts66909 : List PrefixCut := [⟨22,63071468,63071504⟩,
⟨64,183021845,183021950⟩]
theorem checked66909 : checkPrefixCuts (2^48) 8773828609 10 Manual.Count131072.C066909.packed 64 cuts66909 = true := by
 decide +kernel
def pointBounds66909 : List (Nat × Nat × Nat) := [(8773873664,115259377100303,115259766280954)]
theorem point_links_checked66909 : (cuts66909.take 1).map (fun c => (8773828609-1+2*2^10*c.k,115259314028835+c.lower,115259703209450+c.upper)) = pointBounds66909 := by
 decide +kernel
def cuts66910 : List PrefixCut := [⟨64,185040161,185040265⟩]
theorem checked66910 : checkPrefixCuts (2^48) 8773959681 10 Manual.Count131072.C066910.packed 64 cuts66910 = true := by
 decide +kernel
def cuts66911 : List PrefixCut := [⟨28,80328646,80328693⟩,
⟨64,184042935,184043043⟩]
theorem checked66911 : checkPrefixCuts (2^48) 8774090753 10 Manual.Count131072.C066911.packed 64 cuts66911 = true := by
 decide +kernel
def pointBounds66911 : List (Nat × Nat × Nat) := [(8774148096,115259762419487,115260151600358)]
theorem point_links_checked66911 : (cuts66911.take 1).map (fun c => (8774090753-1+2*2^10*c.k,115259682090841+c.lower,115260071271665+c.upper)) = pointBounds66911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000215
