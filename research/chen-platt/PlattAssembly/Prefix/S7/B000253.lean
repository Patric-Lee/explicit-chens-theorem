import PlattAssemblyKernel
import PlattCertificates.Count131072.C068096
import PlattCertificates.Count131072.C068097
import PlattCertificates.Count131072.C068098
import PlattCertificates.Count131072.C068099
import PlattCertificates.Count131072.C068100
import PlattCertificates.Count131072.C068101
import PlattCertificates.Count131072.C068102
import PlattCertificates.Count131072.C068103
import PlattCertificates.Count131072.C068104
import PlattCertificates.Count131072.C068105
import PlattCertificates.Count131072.C068106
import PlattCertificates.Count131072.C068107
import PlattCertificates.Count131072.C068108
import PlattCertificates.Count131072.C068109
import PlattCertificates.Count131072.C068110
import PlattCertificates.Count131072.C068111
import PlattCertificates.Count131072.C068112
import PlattCertificates.Count131072.C068113
import PlattCertificates.Count131072.C068114
import PlattCertificates.Count131072.C068115
import PlattCertificates.Count131072.C068116
import PlattCertificates.Count131072.C068117
import PlattCertificates.Count131072.C068118
import PlattCertificates.Count131072.C068119
import PlattCertificates.Count131072.C068120
import PlattCertificates.Count131072.C068121
import PlattCertificates.Count131072.C068122
import PlattCertificates.Count131072.C068123
import PlattCertificates.Count131072.C068124
import PlattCertificates.Count131072.C068125
import PlattCertificates.Count131072.C068126
import PlattCertificates.Count131072.C068127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000253
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68096 : List PrefixCut := [⟨64,180148184,180148290⟩]
theorem checked68096 : checkPrefixCuts (2^48) 8929411073 10 Manual.Count131072.C068096.packed 64 cuts68096 = true := by
 decide +kernel
def cuts68097 : List PrefixCut := [⟨48,134975441,134975523⟩,
⟨64,181564005,181564114⟩]
theorem checked68097 : checkPrefixCuts (2^48) 8929542145 10 Manual.Count131072.C068097.packed 64 cuts68097 = true := by
 decide +kernel
def pointBounds68097 : List (Nat × Nat × Nat) := [(8929640448,115475639106920,115476028413793)]
theorem point_links_checked68097 : (cuts68097.take 1).map (fun c => (8929542145-1+2*2^10*c.k,115475504131479+c.lower,115475893438270+c.upper)) = pointBounds68097 := by
 decide +kernel
def cuts68098 : List PrefixCut := [⟨64,181246136,181246246⟩]
theorem checked68098 : checkPrefixCuts (2^48) 8929673217 10 Manual.Count131072.C068098.packed 64 cuts68098 = true := by
 decide +kernel
def cuts68099 : List PrefixCut := [⟨57,159778072,159778168⟩,
⟨64,178721832,178721939⟩]
theorem checked68099 : checkPrefixCuts (2^48) 8929804289 10 Manual.Count131072.C068099.packed 64 cuts68099 = true := by
 decide +kernel
def pointBounds68099 : List (Nat × Nat × Nat) := [(8929921024,115476026719692,115476416026798)]
theorem point_links_checked68099 : (cuts68099.take 1).map (fun c => (8929804289-1+2*2^10*c.k,115475866941620+c.lower,115476256248630+c.upper)) = pointBounds68099 := by
 decide +kernel
def cuts68100 : List PrefixCut := [⟨64,179192010,179192120⟩]
theorem checked68100 : checkPrefixCuts (2^48) 8929935361 10 Manual.Count131072.C068100.packed 64 cuts68100 = true := by
 decide +kernel
def cuts68101 : List PrefixCut := [⟨64,182404380,182404485⟩]
theorem checked68101 : checkPrefixCuts (2^48) 8930066433 10 Manual.Count131072.C068101.packed 64 cuts68101 = true := by
 decide +kernel
def cuts68102 : List PrefixCut := [⟨2,5736538,5736542⟩,
⟨64,181802829,181802939⟩]
theorem checked68102 : checkPrefixCuts (2^48) 8930197505 10 Manual.Count131072.C068102.packed 64 cuts68102 = true := by
 decide +kernel
def pointBounds68102 : List (Nat × Nat × Nat) := [(8930201600,115476412996380,115476802303716)]
theorem point_links_checked68102 : (cuts68102.take 1).map (fun c => (8930197505-1+2*2^10*c.k,115476407259842+c.lower,115476796567174+c.upper)) = pointBounds68102 := by
 decide +kernel
def cuts68103 : List PrefixCut := [⟨64,178931959,178932073⟩]
theorem checked68103 : checkPrefixCuts (2^48) 8930328577 10 Manual.Count131072.C068103.packed 64 cuts68103 = true := by
 decide +kernel
def cuts68104 : List PrefixCut := [⟨11,30982669,30982687⟩,
⟨64,178803271,178803376⟩]
theorem checked68104 : checkPrefixCuts (2^48) 8930459649 10 Manual.Count131072.C068104.packed 64 cuts68104 = true := by
 decide +kernel
def pointBounds68104 : List (Nat × Nat × Nat) := [(8930482176,115476798977299,115477188284873)]
theorem point_links_checked68104 : (cuts68104.take 1).map (fun c => (8930459649-1+2*2^10*c.k,115476767994630+c.lower,115477157302186+c.upper)) = pointBounds68104 := by
 decide +kernel
def cuts68105 : List PrefixCut := [⟨64,178422429,178422533⟩]
theorem checked68105 : checkPrefixCuts (2^48) 8930590721 10 Manual.Count131072.C068105.packed 64 cuts68105 = true := by
 decide +kernel
def cuts68106 : List PrefixCut := [⟨20,58181351,58181386⟩,
⟨64,182580103,182580217⟩]
theorem checked68106 : checkPrefixCuts (2^48) 8930721793 10 Manual.Count131072.C068106.packed 64 cuts68106 = true := by
 decide +kernel
def pointBounds68106 : List (Nat × Nat × Nat) := [(8930762752,115477183401681,115477572709481)]
theorem point_links_checked68106 : (cuts68106.take 1).map (fun c => (8930721793-1+2*2^10*c.k,115477125220330+c.lower,115477514528095+c.upper)) = pointBounds68106 := by
 decide +kernel
def cuts68107 : List PrefixCut := [⟨64,180717930,180718038⟩]
theorem checked68107 : checkPrefixCuts (2^48) 8930852865 10 Manual.Count131072.C068107.packed 64 cuts68107 = true := by
 decide +kernel
def cuts68108 : List PrefixCut := [⟨29,82384307,82384354⟩,
⟨64,181061957,181062059⟩]
theorem checked68108 : checkPrefixCuts (2^48) 8930983937 10 Manual.Count131072.C068108.packed 64 cuts68108 = true := by
 decide +kernel
def pointBounds68108 : List (Nat × Nat × Nat) := [(8931043328,115477570902670,115477960210704)]
theorem point_links_checked68108 : (cuts68108.take 1).map (fun c => (8930983937-1+2*2^10*c.k,115477488518363+c.lower,115477877826350+c.upper)) = pointBounds68108 := by
 decide +kernel
def cuts68109 : List PrefixCut := [⟨64,180019268,180019377⟩]
theorem checked68109 : checkPrefixCuts (2^48) 8931115009 10 Manual.Count131072.C068109.packed 64 cuts68109 = true := by
 decide +kernel
def cuts68110 : List PrefixCut := [⟨38,109233110,109233175⟩,
⟨64,183262733,183262842⟩]
theorem checked68110 : checkPrefixCuts (2^48) 8931246081 10 Manual.Count131072.C068110.packed 64 cuts68110 = true := by
 decide +kernel
def pointBounds68110 : List (Nat × Nat × Nat) := [(8931323904,115477958832698,115478348140961)]
theorem point_links_checked68110 : (cuts68110.take 1).map (fun c => (8931246081-1+2*2^10*c.k,115477849599588+c.lower,115478238907786+c.upper)) = pointBounds68110 := by
 decide +kernel
def cuts68111 : List PrefixCut := [⟨64,181211563,181211669⟩]
theorem checked68111 : checkPrefixCuts (2^48) 8931377153 10 Manual.Count131072.C068111.packed 64 cuts68111 = true := by
 decide +kernel
def cuts68112 : List PrefixCut := [⟨47,132235480,132235557⟩,
⟨64,179128940,179129042⟩]
theorem checked68112 : checkPrefixCuts (2^48) 8931508225 10 Manual.Count131072.C068112.packed 64 cuts68112 = true := by
 decide +kernel
def pointBounds68112 : List (Nat × Nat × Nat) := [(8931604480,115478346309364,115478735617854)]
theorem point_links_checked68112 : (cuts68112.take 1).map (fun c => (8931508225-1+2*2^10*c.k,115478214073884+c.lower,115478603382297+c.upper)) = pointBounds68112 := by
 decide +kernel
def cuts68113 : List PrefixCut := [⟨64,179409930,179410037⟩]
theorem checked68113 : checkPrefixCuts (2^48) 8931639297 10 Manual.Count131072.C068113.packed 64 cuts68113 = true := by
 decide +kernel
def cuts68114 : List PrefixCut := [⟨56,156055829,156055920⟩,
⟨64,179344279,179344382⟩]
theorem checked68114 : checkPrefixCuts (2^48) 8931770369 10 Manual.Count131072.C068114.packed 64 cuts68114 = true := by
 decide +kernel
def pointBounds68114 : List (Nat × Nat × Nat) := [(8931885056,115478728668583,115479117977296)]
theorem point_links_checked68114 : (cuts68114.take 1).map (fun c => (8931770369-1+2*2^10*c.k,115478572612754+c.lower,115478961921376+c.upper)) = pointBounds68114 := by
 decide +kernel
def cuts68115 : List PrefixCut := [⟨64,183123232,183123335⟩]
theorem checked68115 : checkPrefixCuts (2^48) 8931901441 10 Manual.Count131072.C068115.packed 64 cuts68115 = true := by
 decide +kernel
def cuts68116 : List PrefixCut := [⟨64,178456661,178456767⟩]
theorem checked68116 : checkPrefixCuts (2^48) 8932032513 10 Manual.Count131072.C068116.packed 64 cuts68116 = true := by
 decide +kernel
def cuts68117 : List PrefixCut := [⟨1,2804613,2804615⟩,
⟨64,180155698,180155803⟩]
theorem checked68117 : checkPrefixCuts (2^48) 8932163585 10 Manual.Count131072.C068117.packed 64 cuts68117 = true := by
 decide +kernel
def pointBounds68117 : List (Nat × Nat × Nat) := [(8932165632,115479116341539,115479505650475)]
theorem point_links_checked68117 : (cuts68117.take 1).map (fun c => (8932163585-1+2*2^10*c.k,115479113536926+c.lower,115479502845860+c.upper)) = pointBounds68117 := by
 decide +kernel
def cuts68118 : List PrefixCut := [⟨64,181634118,181634222⟩]
theorem checked68118 : checkPrefixCuts (2^48) 8932294657 10 Manual.Count131072.C068118.packed 64 cuts68118 = true := by
 decide +kernel
def cuts68119 : List PrefixCut := [⟨10,27635629,27635644⟩,
⟨64,180370992,180371097⟩]
theorem checked68119 : checkPrefixCuts (2^48) 8932425729 10 Manual.Count131072.C068119.packed 64 cuts68119 = true := by
 decide +kernel
def pointBounds68119 : List (Nat × Nat × Nat) := [(8932446208,115479502962371,115479892271529)]
theorem point_links_checked68119 : (cuts68119.take 1).map (fun c => (8932425729-1+2*2^10*c.k,115479475326742+c.lower,115479864635885+c.upper)) = pointBounds68119 := by
 decide +kernel
def cuts68120 : List PrefixCut := [⟨64,178320132,178320241⟩]
theorem checked68120 : checkPrefixCuts (2^48) 8932556801 10 Manual.Count131072.C068120.packed 64 cuts68120 = true := by
 decide +kernel
def cuts68121 : List PrefixCut := [⟨19,52213051,52213081⟩,
⟨64,182728974,182729077⟩]
theorem checked68121 : checkPrefixCuts (2^48) 8932687873 10 Manual.Count131072.C068121.packed 64 cuts68121 = true := by
 decide +kernel
def pointBounds68121 : List (Nat × Nat × Nat) := [(8932726784,115479886230917,115480275540304)]
theorem point_links_checked68121 : (cuts68121.take 1).map (fun c => (8932687873-1+2*2^10*c.k,115479834017866+c.lower,115480223327223+c.upper)) = pointBounds68121 := by
 decide +kernel
def cuts68122 : List PrefixCut := [⟨64,180898713,180898821⟩]
theorem checked68122 : checkPrefixCuts (2^48) 8932818945 10 Manual.Count131072.C068122.packed 64 cuts68122 = true := by
 decide +kernel
def cuts68123 : List PrefixCut := [⟨28,79813902,79813953⟩,
⟨64,181778336,181778447⟩]
theorem checked68123 : checkPrefixCuts (2^48) 8932950017 10 Manual.Count131072.C068123.packed 64 cuts68123 = true := by
 decide +kernel
def pointBounds68123 : List (Nat × Nat × Nat) := [(8933007360,115480277459455,115480666769074)]
theorem point_links_checked68123 : (cuts68123.take 1).map (fun c => (8932950017-1+2*2^10*c.k,115480197645553+c.lower,115480586955121+c.upper)) = pointBounds68123 := by
 decide +kernel
def cuts68124 : List PrefixCut := [⟨64,180074168,180074269⟩]
theorem checked68124 : checkPrefixCuts (2^48) 8933081089 10 Manual.Count131072.C068124.packed 64 cuts68124 = true := by
 decide +kernel
def cuts68125 : List PrefixCut := [⟨37,103569021,103569082⟩,
⟨64,180670188,180670296⟩]
theorem checked68125 : checkPrefixCuts (2^48) 8933212161 10 Manual.Count131072.C068125.packed 64 cuts68125 = true := by
 decide +kernel
def pointBounds68125 : List (Nat × Nat × Nat) := [(8933287936,115480663067078,115481052376919)]
theorem point_links_checked68125 : (cuts68125.take 1).map (fun c => (8933212161-1+2*2^10*c.k,115480559498057+c.lower,115480948807837+c.upper)) = pointBounds68125 := by
 decide +kernel
def cuts68126 : List PrefixCut := [⟨64,180352469,180352582⟩]
theorem checked68126 : checkPrefixCuts (2^48) 8933343233 10 Manual.Count131072.C068126.packed 64 cuts68126 = true := by
 decide +kernel
def cuts68127 : List PrefixCut := [⟨46,130788551,130788627⟩,
⟨64,181011487,181011596⟩]
theorem checked68127 : checkPrefixCuts (2^48) 8933474305 10 Manual.Count131072.C068127.packed 64 cuts68127 = true := by
 decide +kernel
def pointBounds68127 : List (Nat × Nat × Nat) := [(8933568512,115481051309265,115481440619342)]
theorem point_links_checked68127 : (cuts68127.take 1).map (fun c => (8933474305-1+2*2^10*c.k,115480920520714+c.lower,115481309830715+c.upper)) = pointBounds68127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000253
