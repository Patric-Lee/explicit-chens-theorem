import PlattAssemblyKernel
import PlattCertificates.Count131072.C073104
import PlattCertificates.Count131072.C073105
import PlattCertificates.Count131072.C073106
import PlattCertificates.Count131072.C073107
import PlattCertificates.Count131072.C073108
import PlattCertificates.Count131072.C073109
import PlattCertificates.Count131072.C073110
import PlattCertificates.Count131072.C073111
import PlattCertificates.Count131072.C073112
import PlattCertificates.Count131072.C073113
import PlattCertificates.Count131072.C073114
import PlattCertificates.Count131072.C073115
import PlattCertificates.Count131072.C073116
import PlattCertificates.Count131072.C073117
import PlattCertificates.Count131072.C073118
import PlattCertificates.Count131072.C073119
import PlattCertificates.Count131072.C073120
import PlattCertificates.Count131072.C073121
import PlattCertificates.Count131072.C073122
import PlattCertificates.Count131072.C073123
import PlattCertificates.Count131072.C073124
import PlattCertificates.Count131072.C073125
import PlattCertificates.Count131072.C073126
import PlattCertificates.Count131072.C073127
import PlattCertificates.Count131072.C073128
import PlattCertificates.Count131072.C073129
import PlattCertificates.Count131072.C073130
import PlattCertificates.Count131072.C073131
import PlattCertificates.Count131072.C073132
import PlattCertificates.Count131072.C073133
import PlattCertificates.Count131072.C073134
import PlattCertificates.Count131072.C073135
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000097
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73104 : List PrefixCut := [⟨64,168546348,168546447⟩]
theorem checked73104 : checkPrefixCuts (2^48) 9585819649 10 Manual.Count131072.C073104.packed 64 cuts73104 = true := by
 decide +kernel
def cuts73105 : List PrefixCut := [⟨64,167868685,167868789⟩]
theorem checked73105 : checkPrefixCuts (2^48) 9585950721 10 Manual.Count131072.C073105.packed 64 cuts73105 = true := by
 decide +kernel
def cuts73106 : List PrefixCut := [⟨1,2906924,2906926⟩,
⟨64,166691891,166691994⟩]
theorem checked73106 : checkPrefixCuts (2^48) 9586081793 10 Manual.Count131072.C073106.packed 64 cuts73106 = true := by
 decide +kernel
def pointBounds73106 : List (Nat × Nat × Nat) := [(9586083840,116345732603213,116346122423548)]
theorem point_links_checked73106 : (cuts73106.take 1).map (fun c => (9586081793-1+2*2^10*c.k,116345729696289+c.lower,116346119516622+c.upper)) = pointBounds73106 := by
 decide +kernel
def cuts73107 : List PrefixCut := [⟨64,167834737,167834835⟩]
theorem checked73107 : checkPrefixCuts (2^48) 9586212865 10 Manual.Count131072.C073107.packed 64 cuts73107 = true := by
 decide +kernel
def cuts73108 : List PrefixCut := [⟨20,52910333,52910369⟩,
⟨64,168243502,168243611⟩]
theorem checked73108 : checkPrefixCuts (2^48) 9586343937 10 Manual.Count131072.C073108.packed 64 cuts73108 = true := by
 decide +kernel
def pointBounds73108 : List (Nat × Nat × Nat) := [(9586384896,116346117133250,116346506953820)]
theorem point_links_checked73108 : (cuts73108.take 1).map (fun c => (9586343937-1+2*2^10*c.k,116346064222917+c.lower,116346454043451+c.upper)) = pointBounds73108 := by
 decide +kernel
def cuts73109 : List PrefixCut := [⟨64,168534823,168534926⟩]
theorem checked73109 : checkPrefixCuts (2^48) 9586475009 10 Manual.Count131072.C073109.packed 64 cuts73109 = true := by
 decide +kernel
def cuts73110 : List PrefixCut := [⟨39,105318422,105318482⟩,
⟨64,170088665,170088762⟩]
theorem checked73110 : checkPrefixCuts (2^48) 9586606081 10 Manual.Count131072.C073110.packed 64 cuts73110 = true := by
 decide +kernel
def pointBounds73110 : List (Nat × Nat × Nat) := [(9586685952,116346506319664,116346896140470)]
theorem point_links_checked73110 : (cuts73110.take 1).map (fun c => (9586606081-1+2*2^10*c.k,116346401001242+c.lower,116346790821988+c.upper)) = pointBounds73110 := by
 decide +kernel
def cuts73111 : List PrefixCut := [⟨64,164449076,164449171⟩]
theorem checked73111 : checkPrefixCuts (2^48) 9586737153 10 Manual.Count131072.C073111.packed 64 cuts73111 = true := by
 decide +kernel
def cuts73112 : List PrefixCut := [⟨58,152702812,152702904⟩,
⟨64,168351734,168351836⟩]
theorem checked73112 : checkPrefixCuts (2^48) 9586868225 10 Manual.Count131072.C073112.packed 64 cuts73112 = true := by
 decide +kernel
def pointBounds73112 : List (Nat × Nat × Nat) := [(9586987008,116346888241795,116347278062825)]
theorem point_links_checked73112 : (cuts73112.take 1).map (fun c => (9586868225-1+2*2^10*c.k,116346735538983+c.lower,116347125359921+c.upper)) = pointBounds73112 := by
 decide +kernel
def cuts73113 : List PrefixCut := [⟨64,166998889,166998991⟩]
theorem checked73113 : checkPrefixCuts (2^48) 9586999297 10 Manual.Count131072.C073113.packed 64 cuts73113 = true := by
 decide +kernel
def cuts73114 : List PrefixCut := [⟨64,164882726,164882821⟩]
theorem checked73114 : checkPrefixCuts (2^48) 9587130369 10 Manual.Count131072.C073114.packed 64 cuts73114 = true := by
 decide +kernel
def cuts73115 : List PrefixCut := [⟨13,34232849,34232869⟩,
⟨64,167992532,167992630⟩]
theorem checked73115 : checkPrefixCuts (2^48) 9587261441 10 Manual.Count131072.C073115.packed 64 cuts73115 = true := by
 decide +kernel
def pointBounds73115 : List (Nat × Nat × Nat) := [(9587288064,116347270005181,116347659826438)]
theorem point_links_checked73115 : (cuts73115.take 1).map (fun c => (9587261441-1+2*2^10*c.k,116347235772332+c.lower,116347625593569+c.upper)) = pointBounds73115 := by
 decide +kernel
def cuts73116 : List PrefixCut := [⟨64,163791948,163792044⟩]
theorem checked73116 : checkPrefixCuts (2^48) 9587392513 10 Manual.Count131072.C073116.packed 64 cuts73116 = true := by
 decide +kernel
def cuts73117 : List PrefixCut := [⟨32,84757570,84757621⟩,
⟨64,169015478,169015577⟩]
theorem checked73117 : checkPrefixCuts (2^48) 9587523585 10 Manual.Count131072.C073117.packed 64 cuts73117 = true := by
 decide +kernel
def pointBounds73117 : List (Nat × Nat × Nat) := [(9587589120,116347652314382,116348042135864)]
theorem point_links_checked73117 : (cuts73117.take 1).map (fun c => (9587523585-1+2*2^10*c.k,116347567556812+c.lower,116347957378243+c.upper)) = pointBounds73117 := by
 decide +kernel
def cuts73118 : List PrefixCut := [⟨64,166547118,166547221⟩]
theorem checked73118 : checkPrefixCuts (2^48) 9587654657 10 Manual.Count131072.C073118.packed 64 cuts73118 = true := by
 decide +kernel
def cuts73119 : List PrefixCut := [⟨51,134662835,134662911⟩,
⟨64,167073285,167073383⟩]
theorem checked73119 : checkPrefixCuts (2^48) 9587785729 10 Manual.Count131072.C073119.packed 64 cuts73119 = true := by
 decide +kernel
def pointBounds73119 : List (Nat × Nat × Nat) := [(9587890176,116348037782243,116348427603952)]
theorem point_links_checked73119 : (cuts73119.take 1).map (fun c => (9587785729-1+2*2^10*c.k,116347903119408+c.lower,116348292941041+c.upper)) = pointBounds73119 := by
 decide +kernel
def cuts73120 : List PrefixCut := [⟨64,166307700,166307799⟩]
theorem checked73120 : checkPrefixCuts (2^48) 9587916801 10 Manual.Count131072.C073120.packed 64 cuts73120 = true := by
 decide +kernel
def cuts73121 : List PrefixCut := [⟨64,169857574,169857678⟩]
theorem checked73121 : checkPrefixCuts (2^48) 9588047873 10 Manual.Count131072.C073121.packed 64 cuts73121 = true := by
 decide +kernel
def cuts73122 : List PrefixCut := [⟨6,15999255,15999264⟩,
⟨64,167066412,167066514⟩]
theorem checked73122 : checkPrefixCuts (2^48) 9588178945 10 Manual.Count131072.C073122.packed 64 cuts73122 = true := by
 decide +kernel
def pointBounds73122 : List (Nat × Nat × Nat) := [(9588191232,116348422357222,116348812179165)]
theorem point_links_checked73122 : (cuts73122.take 1).map (fun c => (9588178945-1+2*2^10*c.k,116348406357967+c.lower,116348796179901+c.upper)) = pointBounds73122 := by
 decide +kernel
def cuts73123 : List PrefixCut := [⟨64,166183455,166183549⟩]
theorem checked73123 : checkPrefixCuts (2^48) 9588310017 10 Manual.Count131072.C073123.packed 64 cuts73123 = true := by
 decide +kernel
def cuts73124 : List PrefixCut := [⟨25,64758386,64758420⟩,
⟨64,165887617,165887716⟩]
theorem checked73124 : checkPrefixCuts (2^48) 9588441089 10 Manual.Count131072.C073124.packed 64 cuts73124 = true := by
 decide +kernel
def pointBounds73124 : List (Nat × Nat × Nat) := [(9588492288,116348804366220,116349194188384)]
theorem point_links_checked73124 : (cuts73124.take 1).map (fun c => (9588441089-1+2*2^10*c.k,116348739607834+c.lower,116349129429964+c.upper)) = pointBounds73124 := by
 decide +kernel
def cuts73125 : List PrefixCut := [⟨64,169055711,169055806⟩]
theorem checked73125 : checkPrefixCuts (2^48) 9588572161 10 Manual.Count131072.C073125.packed 64 cuts73125 = true := by
 decide +kernel
def cuts73126 : List PrefixCut := [⟨44,113367877,113367947⟩,
⟨64,165090516,165090622⟩]
theorem checked73126 : checkPrefixCuts (2^48) 9588703233 10 Manual.Count131072.C073126.packed 64 cuts73126 = true := by
 decide +kernel
def pointBounds73126 : List (Nat × Nat × Nat) := [(9588793344,116349187919039,116349577741433)]
theorem point_links_checked73126 : (cuts73126.take 1).map (fun c => (9588703233-1+2*2^10*c.k,116349074551162+c.lower,116349464373486+c.upper)) = pointBounds73126 := by
 decide +kernel
def cuts73127 : List PrefixCut := [⟨64,168258511,168258615⟩]
theorem checked73127 : checkPrefixCuts (2^48) 9588834305 10 Manual.Count131072.C073127.packed 64 cuts73127 = true := by
 decide +kernel
def cuts73128 : List PrefixCut := [⟨63,166172111,166172209⟩,
⟨64,168902000,168902099⟩]
theorem checked73128 : checkPrefixCuts (2^48) 9588965377 10 Manual.Count131072.C073128.packed 64 cuts73128 = true := by
 decide +kernel
def pointBounds73128 : List (Nat × Nat × Nat) := [(9589094400,116349574072300,116349963894932)]
theorem point_links_checked73128 : (cuts73128.take 1).map (fun c => (9588965377-1+2*2^10*c.k,116349407900189+c.lower,116349797722723+c.upper)) = pointBounds73128 := by
 decide +kernel
def cuts73129 : List PrefixCut := [⟨64,166610131,166610236⟩]
theorem checked73129 : checkPrefixCuts (2^48) 9589096449 10 Manual.Count131072.C073129.packed 64 cuts73129 = true := by
 decide +kernel
def cuts73130 : List PrefixCut := [⟨64,166725273,166725365⟩]
theorem checked73130 : checkPrefixCuts (2^48) 9589227521 10 Manual.Count131072.C073130.packed 64 cuts73130 = true := by
 decide +kernel
def cuts73131 : List PrefixCut := [⟨18,47228626,47228655⟩,
⟨64,169012482,169012589⟩]
theorem checked73131 : checkPrefixCuts (2^48) 9589358593 10 Manual.Count131072.C073131.packed 64 cuts73131 = true := by
 decide +kernel
def pointBounds73131 : List (Nat × Nat × Nat) := [(9589395456,116349957366219,116350347189078)]
theorem point_links_checked73131 : (cuts73131.take 1).map (fun c => (9589358593-1+2*2^10*c.k,116349910137593+c.lower,116350299960423+c.upper)) = pointBounds73131 := by
 decide +kernel
def cuts73132 : List PrefixCut := [⟨64,169479812,169479907⟩]
theorem checked73132 : checkPrefixCuts (2^48) 9589489665 10 Manual.Count131072.C073132.packed 64 cuts73132 = true := by
 decide +kernel
def cuts73133 : List PrefixCut := [⟨37,96567818,96567883⟩,
⟨64,166601021,166601130⟩]
theorem checked73133 : checkPrefixCuts (2^48) 9589620737 10 Manual.Count131072.C073133.packed 64 cuts73133 = true := by
 decide +kernel
def pointBounds73133 : List (Nat × Nat × Nat) := [(9589696512,116350345197705,116350735020802)]
theorem point_links_checked73133 : (cuts73133.take 1).map (fun c => (9589620737-1+2*2^10*c.k,116350248629887+c.lower,116350638452919+c.upper)) = pointBounds73133 := by
 decide +kernel
def cuts73134 : List PrefixCut := [⟨64,165982355,165982454⟩]
theorem checked73134 : checkPrefixCuts (2^48) 9589751809 10 Manual.Count131072.C073134.packed 64 cuts73134 = true := by
 decide +kernel
def cuts73135 : List PrefixCut := [⟨56,146813992,146814087⟩,
⟨64,168122713,168122823⟩]
theorem checked73135 : checkPrefixCuts (2^48) 9589882881 10 Manual.Count131072.C073135.packed 64 cuts73135 = true := by
 decide +kernel
def pointBounds73135 : List (Nat × Nat × Nat) := [(9589997568,116350728027255,116351117850590)]
theorem point_links_checked73135 : (cuts73135.take 1).map (fun c => (9589882881-1+2*2^10*c.k,116350581213263+c.lower,116350971036503+c.upper)) = pointBounds73135 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000097
