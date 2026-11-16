import PlattAssemblyKernel
import PlattCertificates.Count131072.C050032
import PlattCertificates.Count131072.C050033
import PlattCertificates.Count131072.C050034
import PlattCertificates.Count131072.C050035
import PlattCertificates.Count131072.C050036
import PlattCertificates.Count131072.C050037
import PlattCertificates.Count131072.C050038
import PlattCertificates.Count131072.C050039
import PlattCertificates.Count131072.C050040
import PlattCertificates.Count131072.C050041
import PlattCertificates.Count131072.C050042
import PlattCertificates.Count131072.C050043
import PlattCertificates.Count131072.C050044
import PlattCertificates.Count131072.C050045
import PlattCertificates.Count131072.C050046
import PlattCertificates.Count131072.C050047
import PlattCertificates.Count131072.C050048
import PlattCertificates.Count131072.C050049
import PlattCertificates.Count131072.C050050
import PlattCertificates.Count131072.C050051
import PlattCertificates.Count131072.C050052
import PlattCertificates.Count131072.C050053
import PlattCertificates.Count131072.C050054
import PlattCertificates.Count131072.C050055
import PlattCertificates.Count131072.C050056
import PlattCertificates.Count131072.C050057
import PlattCertificates.Count131072.C050058
import PlattCertificates.Count131072.C050059
import PlattCertificates.Count131072.C050060
import PlattCertificates.Count131072.C050061
import PlattCertificates.Count131072.C050062
import PlattCertificates.Count131072.C050063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50032 : List PrefixCut := [⟨64,255703263,255703407⟩]
theorem checked50032 : checkPrefixCuts (2^48) 6561726465 10 Manual.Count131072.C050032.packed 64 cuts50032 = true := by
 decide +kernel
def cuts50033 : List PrefixCut := [⟨21,81758767,81758817⟩,
⟨64,247419437,247419583⟩]
theorem checked50033 : checkPrefixCuts (2^48) 6561857537 10 Manual.Count131072.C050033.packed 64 cuts50033 = true := by
 decide +kernel
def pointBounds50033 : List (Nat × Nat × Nat) := [(6561900544,111665142915008,111665530041827)]
theorem point_links_checked50033 : (cuts50033.take 1).map (fun c => (6561857537-1+2*2^10*c.k,111665061156241+c.lower,111665448283010+c.upper)) = pointBounds50033 := by
 decide +kernel
def cuts50034 : List PrefixCut := [⟨58,226868287,226868417⟩,
⟨64,249430499,249430642⟩]
theorem checked50034 : checkPrefixCuts (2^48) 6561988609 10 Manual.Count131072.C050034.packed 64 cuts50034 = true := by
 decide +kernel
def pointBounds50034 : List (Nat × Nat × Nat) := [(6562107392,111665535443965,111665922571010)]
theorem point_links_checked50034 : (cuts50034.take 1).map (fun c => (6561988609-1+2*2^10*c.k,111665308575678+c.lower,111665695702593+c.upper)) = pointBounds50034 := by
 decide +kernel
def cuts50035 : List PrefixCut := [⟨64,249983133,249983282⟩]
theorem checked50035 : checkPrefixCuts (2^48) 6562119681 10 Manual.Count131072.C050035.packed 64 cuts50035 = true := by
 decide +kernel
def cuts50036 : List PrefixCut := [⟨31,121644071,121644140⟩,
⟨64,247919307,247919448⟩]
theorem checked50036 : checkPrefixCuts (2^48) 6562250753 10 Manual.Count131072.C050036.packed 64 cuts50036 = true := by
 decide +kernel
def pointBounds50036 : List (Nat × Nat × Nat) := [(6562314240,111665929633381,111666316760657)]
theorem point_links_checked50036 : (cuts50036.take 1).map (fun c => (6562250753-1+2*2^10*c.k,111665807989310+c.lower,111666195116517+c.upper)) = pointBounds50036 := by
 decide +kernel
def cuts50037 : List PrefixCut := [⟨64,249286896,249287037⟩]
theorem checked50037 : checkPrefixCuts (2^48) 6562381825 10 Manual.Count131072.C050037.packed 64 cuts50037 = true := by
 decide +kernel
def cuts50038 : List PrefixCut := [⟨4,16084238,16084248⟩,
⟨64,250225518,250225660⟩]
theorem checked50038 : checkPrefixCuts (2^48) 6562512897 10 Manual.Count131072.C050038.packed 64 cuts50038 = true := by
 decide +kernel
def pointBounds50038 : List (Nat × Nat × Nat) := [(6562521088,111666321279751,111666708407250)]
theorem point_links_checked50038 : (cuts50038.take 1).map (fun c => (6562512897-1+2*2^10*c.k,111666305195513+c.lower,111666692323002+c.upper)) = pointBounds50038 := by
 decide +kernel
def cuts50039 : List PrefixCut := [⟨41,158736621,158736712⟩,
⟨64,247432658,247432801⟩]
theorem checked50039 : checkPrefixCuts (2^48) 6562643969 10 Manual.Count131072.C050039.packed 64 cuts50039 = true := by
 decide +kernel
def pointBounds50039 : List (Nat × Nat × Nat) := [(6562727936,111666714157652,111667101285374)]
theorem point_links_checked50039 : (cuts50039.take 1).map (fun c => (6562643969-1+2*2^10*c.k,111666555421031+c.lower,111666942548662+c.upper)) = pointBounds50039 := by
 decide +kernel
def cuts50040 : List PrefixCut := [⟨64,244639896,244640037⟩]
theorem checked50040 : checkPrefixCuts (2^48) 6562775041 10 Manual.Count131072.C050040.packed 64 cuts50040 = true := by
 decide +kernel
def cuts50041 : List PrefixCut := [⟨14,53953941,53953972⟩,
⟨64,244249052,244249188⟩]
theorem checked50041 : checkPrefixCuts (2^48) 6562906113 10 Manual.Count131072.C050041.packed 64 cuts50041 = true := by
 decide +kernel
def pointBounds50041 : List (Nat × Nat × Nat) := [(6562934784,111667101447526,111667488575472)]
theorem point_links_checked50041 : (cuts50041.take 1).map (fun c => (6562906113-1+2*2^10*c.k,111667047493585+c.lower,111667434621500+c.upper)) = pointBounds50041 := by
 decide +kernel
def cuts50042 : List PrefixCut := [⟨51,202086186,202086300⟩,
⟨64,252907438,252907582⟩]
theorem checked50042 : checkPrefixCuts (2^48) 6563037185 10 Manual.Count131072.C050042.packed 64 cuts50042 = true := by
 decide +kernel
def pointBounds50042 : List (Nat × Nat × Nat) := [(6563141632,111667493828823,111667880956988)]
theorem point_links_checked50042 : (cuts50042.take 1).map (fun c => (6563037185-1+2*2^10*c.k,111667291742637+c.lower,111667678870688+c.upper)) = pointBounds50042 := by
 decide +kernel
def cuts50043 : List PrefixCut := [⟨64,245139906,245140040⟩]
theorem checked50043 : checkPrefixCuts (2^48) 6563168257 10 Manual.Count131072.C050043.packed 64 cuts50043 = true := by
 decide +kernel
def cuts50044 : List PrefixCut := [⟨24,92462277,92462331⟩,
⟨64,246378699,246378840⟩]
theorem checked50044 : checkPrefixCuts (2^48) 6563299329 10 Manual.Count131072.C050044.packed 64 cuts50044 = true := by
 decide +kernel
def pointBounds50044 : List (Nat × Nat × Nat) := [(6563348480,111667882252258,111668269380641)]
theorem point_links_checked50044 : (cuts50044.take 1).map (fun c => (6563299329-1+2*2^10*c.k,111667789789981+c.lower,111668176918310+c.upper)) = pointBounds50044 := by
 decide +kernel
def cuts50045 : List PrefixCut := [⟨61,234366131,234366262⟩,
⟨64,245987829,245987967⟩]
theorem checked50045 : checkPrefixCuts (2^48) 6563430401 10 Manual.Count131072.C050045.packed 64 cuts50045 = true := by
 decide +kernel
def pointBounds50045 : List (Nat × Nat × Nat) := [(6563555328,111668270534811,111668657663412)]
theorem point_links_checked50045 : (cuts50045.take 1).map (fun c => (6563430401-1+2*2^10*c.k,111668036168680+c.lower,111668423297150+c.upper)) = pointBounds50045 := by
 decide +kernel
def cuts50046 : List PrefixCut := [⟨64,250657291,250657430⟩]
theorem checked50046 : checkPrefixCuts (2^48) 6563561473 10 Manual.Count131072.C050046.packed 64 cuts50046 = true := by
 decide +kernel
def cuts50047 : List PrefixCut := [⟨34,130236873,130236948⟩,
⟨64,246321066,246321205⟩]
theorem checked50047 : checkPrefixCuts (2^48) 6563692545 10 Manual.Count131072.C050047.packed 64 cuts50047 = true := by
 decide +kernel
def pointBounds50047 : List (Nat × Nat × Nat) := [(6563762176,111668663050673,111669050179495)]
theorem point_links_checked50047 : (cuts50047.take 1).map (fun c => (6563692545-1+2*2^10*c.k,111668532813800+c.lower,111668919942547+c.upper)) = pointBounds50047 := by
 decide +kernel
def cuts50048 : List PrefixCut := [⟨64,245587123,245587267⟩]
theorem checked50048 : checkPrefixCuts (2^48) 6563823617 10 Manual.Count131072.C050048.packed 64 cuts50048 = true := by
 decide +kernel
def cuts50049 : List PrefixCut := [⟨7,27787446,27787462⟩,
⟨64,249913263,249913407⟩]
theorem checked50049 : checkPrefixCuts (2^48) 6563954689 10 Manual.Count131072.C050049.packed 64 cuts50049 = true := by
 decide +kernel
def pointBounds50049 : List (Nat × Nat × Nat) := [(6563969024,111669052509435,111669439638481)]
theorem point_links_checked50049 : (cuts50049.take 1).map (fun c => (6563954689-1+2*2^10*c.k,111669024721989+c.lower,111669411851019+c.upper)) = pointBounds50049 := by
 decide +kernel
def cuts50050 : List PrefixCut := [⟨44,172595040,172595136⟩,
⟨64,250808761,250808904⟩]
theorem checked50050 : checkPrefixCuts (2^48) 6564085761 10 Manual.Count131072.C050050.packed 64 cuts50050 = true := by
 decide +kernel
def pointBounds50050 : List (Nat × Nat × Nat) := [(6564175872,111669447230292,111669834359562)]
theorem point_links_checked50050 : (cuts50050.take 1).map (fun c => (6564085761-1+2*2^10*c.k,111669274635252+c.lower,111669661764426+c.upper)) = pointBounds50050 := by
 decide +kernel
def cuts50051 : List PrefixCut := [⟨64,246944564,246944703⟩]
theorem checked50051 : checkPrefixCuts (2^48) 6564216833 10 Manual.Count131072.C050051.packed 64 cuts50051 = true := by
 decide +kernel
def cuts50052 : List PrefixCut := [⟨17,66548555,66548592⟩,
⟨64,251098883,251099024⟩]
theorem checked50052 : checkPrefixCuts (2^48) 6564347905 10 Manual.Count131072.C050052.packed 64 cuts50052 = true := by
 decide +kernel
def pointBounds50052 : List (Nat × Nat × Nat) := [(6564382720,111669838937132,111670226066625)]
theorem point_links_checked50052 : (cuts50052.take 1).map (fun c => (6564347905-1+2*2^10*c.k,111669772388577+c.lower,111670159518033+c.upper)) = pointBounds50052 := by
 decide +kernel
def cuts50053 : List PrefixCut := [⟨54,210017032,210017150⟩,
⟨64,248135303,248135441⟩]
theorem checked50053 : checkPrefixCuts (2^48) 6564478977 10 Manual.Count131072.C050053.packed 64 cuts50053 = true := by
 decide +kernel
def pointBounds50053 : List (Nat × Nat × Nat) := [(6564589568,111670233504492,111670620634207)]
theorem point_links_checked50053 : (cuts50053.take 1).map (fun c => (6564478977-1+2*2^10*c.k,111670023487460+c.lower,111670410617057+c.upper)) = pointBounds50053 := by
 decide +kernel
def cuts50054 : List PrefixCut := [⟨64,251474750,251474888⟩]
theorem checked50054 : checkPrefixCuts (2^48) 6564610049 10 Manual.Count131072.C050054.packed 64 cuts50054 = true := by
 decide +kernel
def cuts50055 : List PrefixCut := [⟨27,105004762,105004825⟩,
⟨64,249497414,249497561⟩]
theorem checked50055 : checkPrefixCuts (2^48) 6564741121 10 Manual.Count131072.C050055.packed 64 cuts50055 = true := by
 decide +kernel
def pointBounds50055 : List (Nat × Nat × Nat) := [(6564796416,111670628102275,111671015232211)]
theorem point_links_checked50055 : (cuts50055.take 1).map (fun c => (6564741121-1+2*2^10*c.k,111670523097513+c.lower,111670910227386+c.upper)) = pointBounds50055 := by
 decide +kernel
def cuts50056 : List PrefixCut := [⟨64,251250355,251250496⟩]
theorem checked50056 : checkPrefixCuts (2^48) 6564872193 10 Manual.Count131072.C050056.packed 64 cuts50056 = true := by
 decide +kernel
def pointBounds50056 : List (Nat × Nat × Nat) := [(6565003264,111671023845282,111671410975443)]
theorem point_links_checked50056 : (cuts50056.take 1).map (fun c => (6564872193-1+2*2^10*c.k,111670772594927+c.lower,111671159724947+c.upper)) = pointBounds50056 := by
 decide +kernel
def cuts50057 : List PrefixCut := [⟨64,247215127,247215267⟩]
theorem checked50057 : checkPrefixCuts (2^48) 6565003265 10 Manual.Count131072.C050057.packed 64 cuts50057 = true := by
 decide +kernel
def cuts50058 : List PrefixCut := [⟨37,144956850,144956933⟩,
⟨64,249396760,249396902⟩]
theorem checked50058 : checkPrefixCuts (2^48) 6565134337 10 Manual.Count131072.C050058.packed 64 cuts50058 = true := by
 decide +kernel
def pointBounds50058 : List (Nat × Nat × Nat) := [(6565210112,111671416017259,111671803147643)]
theorem point_links_checked50058 : (cuts50058.take 1).map (fun c => (6565134337-1+2*2^10*c.k,111671271060409+c.lower,111671658190710+c.upper)) = pointBounds50058 := by
 decide +kernel
def cuts50059 : List PrefixCut := [⟨64,250292086,250292226⟩]
theorem checked50059 : checkPrefixCuts (2^48) 6565265409 10 Manual.Count131072.C050059.packed 64 cuts50059 = true := by
 decide +kernel
def cuts50060 : List PrefixCut := [⟨10,38585179,38585202⟩,
⟨64,250115605,250115745⟩]
theorem checked50060 : checkPrefixCuts (2^48) 6565396481 10 Manual.Count131072.C050060.packed 64 cuts50060 = true := by
 decide +kernel
def pointBounds50060 : List (Nat × Nat × Nat) := [(6565416960,111671809334434,111672196465040)]
theorem point_links_checked50060 : (cuts50060.take 1).map (fun c => (6565396481-1+2*2^10*c.k,111671770749255+c.lower,111672157879838+c.upper)) = pointBounds50060 := by
 decide +kernel
def cuts50061 : List PrefixCut := [⟨47,180359641,180359745⟩,
⟨64,245309045,245309185⟩]
theorem checked50061 : checkPrefixCuts (2^48) 6565527553 10 Manual.Count131072.C050061.packed 64 cuts50061 = true := by
 decide +kernel
def pointBounds50061 : List (Nat × Nat × Nat) := [(6565623808,111672201224501,111672588355328)]
theorem point_links_checked50061 : (cuts50061.take 1).map (fun c => (6565527553-1+2*2^10*c.k,111672020864860+c.lower,111672407995583+c.upper)) = pointBounds50061 := by
 decide +kernel
def cuts50062 : List PrefixCut := [⟨64,248262231,248262377⟩]
theorem checked50062 : checkPrefixCuts (2^48) 6565658625 10 Manual.Count131072.C050062.packed 64 cuts50062 = true := by
 decide +kernel
def cuts50063 : List PrefixCut := [⟨20,76694056,76694098⟩,
⟨64,248085765,248085901⟩]
theorem checked50063 : checkPrefixCuts (2^48) 6565789697 10 Manual.Count131072.C050063.packed 64 cuts50063 = true := by
 decide +kernel
def pointBounds50063 : List (Nat × Nat × Nat) := [(6565830656,111672591130192,111672978261243)]
theorem point_links_checked50063 : (cuts50063.take 1).map (fun c => (6565789697-1+2*2^10*c.k,111672514436136+c.lower,111672901567145+c.upper)) = pointBounds50063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000001
