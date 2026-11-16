import PlattAssemblyKernel
import PlattCertificates.Count131072.C052112
import PlattCertificates.Count131072.C052113
import PlattCertificates.Count131072.C052114
import PlattCertificates.Count131072.C052115
import PlattCertificates.Count131072.C052116
import PlattCertificates.Count131072.C052117
import PlattCertificates.Count131072.C052118
import PlattCertificates.Count131072.C052119
import PlattCertificates.Count131072.C052120
import PlattCertificates.Count131072.C052121
import PlattCertificates.Count131072.C052122
import PlattCertificates.Count131072.C052123
import PlattCertificates.Count131072.C052124
import PlattCertificates.Count131072.C052125
import PlattCertificates.Count131072.C052126
import PlattCertificates.Count131072.C052127
import PlattCertificates.Count131072.C052128
import PlattCertificates.Count131072.C052129
import PlattCertificates.Count131072.C052130
import PlattCertificates.Count131072.C052131
import PlattCertificates.Count131072.C052132
import PlattCertificates.Count131072.C052133
import PlattCertificates.Count131072.C052134
import PlattCertificates.Count131072.C052135
import PlattCertificates.Count131072.C052136
import PlattCertificates.Count131072.C052137
import PlattCertificates.Count131072.C052138
import PlattCertificates.Count131072.C052139
import PlattCertificates.Count131072.C052140
import PlattCertificates.Count131072.C052141
import PlattCertificates.Count131072.C052142
import PlattCertificates.Count131072.C052143
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52112 : List PrefixCut := [⟨64,237307319,237307454⟩]
theorem checked52112 : checkPrefixCuts (2^48) 6834356225 10 Manual.Count131072.C052112.packed 64 cuts52112 = true := by
 decide +kernel
def cuts52113 : List PrefixCut := [⟨2,7536760,7536765⟩,
⟨64,236067241,236067377⟩]
theorem checked52113 : checkPrefixCuts (2^48) 6834487297 10 Manual.Count131072.C052113.packed 64 cuts52113 = true := by
 decide +kernel
def pointBounds52113 : List (Nat × Nat × Nat) := [(6834491392,112171542095252,112171929509962)]
theorem point_links_checked52113 : (cuts52113.take 1).map (fun c => (6834487297-1+2*2^10*c.k,112171534558492+c.lower,112171921973197+c.upper)) = pointBounds52113 := by
 decide +kernel
def cuts52114 : List PrefixCut := [⟨43,161397902,161397993⟩,
⟨64,240222246,240222381⟩]
theorem checked52114 : checkPrefixCuts (2^48) 6834618369 10 Manual.Count131072.C052114.packed 64 cuts52114 = true := by
 decide +kernel
def pointBounds52114 : List (Nat × Nat × Nat) := [(6834706432,112171932023635,112172319438567)]
theorem point_links_checked52114 : (cuts52114.take 1).map (fun c => (6834618369-1+2*2^10*c.k,112171770625733+c.lower,112172158040574+c.upper)) = pointBounds52114 := by
 decide +kernel
def cuts52115 : List PrefixCut := [⟨64,235687561,235687701⟩]
theorem checked52115 : checkPrefixCuts (2^48) 6834749441 10 Manual.Count131072.C052115.packed 64 cuts52115 = true := by
 decide +kernel
def cuts52116 : List PrefixCut := [⟨20,74292323,74292367⟩,
⟨64,240789557,240789695⟩]
theorem checked52116 : checkPrefixCuts (2^48) 6834880513 10 Manual.Count131072.C052116.packed 64 cuts52116 = true := by
 decide +kernel
def pointBounds52116 : List (Nat × Nat × Nat) := [(6834921472,112172320827863,112172708243023)]
theorem point_links_checked52116 : (cuts52116.take 1).map (fun c => (6834880513-1+2*2^10*c.k,112172246535540+c.lower,112172633950656+c.upper)) = pointBounds52116 := by
 decide +kernel
def cuts52117 : List PrefixCut := [⟨61,226495266,226495395⟩,
⟨64,237984643,237984778⟩]
theorem checked52117 : checkPrefixCuts (2^48) 6835011585 10 Manual.Count131072.C052117.packed 64 cuts52117 = true := by
 decide +kernel
def pointBounds52117 : List (Nat × Nat × Nat) := [(6835136512,112172713820363,112173101235746)]
theorem point_links_checked52117 : (cuts52117.take 1).map (fun c => (6835011585-1+2*2^10*c.k,112172487325097+c.lower,112172874740351+c.upper)) = pointBounds52117 := by
 decide +kernel
def cuts52118 : List PrefixCut := [⟨64,239544921,239545058⟩]
theorem checked52118 : checkPrefixCuts (2^48) 6835142657 10 Manual.Count131072.C052118.packed 64 cuts52118 = true := by
 decide +kernel
def cuts52119 : List PrefixCut := [⟨38,139063241,139063323⟩,
⟨64,233198726,233198863⟩]
theorem checked52119 : checkPrefixCuts (2^48) 6835273729 10 Manual.Count131072.C052119.packed 64 cuts52119 = true := by
 decide +kernel
def pointBounds52119 : List (Nat × Nat × Nat) := [(6835351552,112173103917902,112173491333510)]
theorem point_links_checked52119 : (cuts52119.take 1).map (fun c => (6835273729-1+2*2^10*c.k,112172964854661+c.lower,112173352270187+c.upper)) = pointBounds52119 := by
 decide +kernel
def cuts52120 : List PrefixCut := [⟨64,238465119,238465254⟩]
theorem checked52120 : checkPrefixCuts (2^48) 6835404801 10 Manual.Count131072.C052120.packed 64 cuts52120 = true := by
 decide +kernel
def cuts52121 : List PrefixCut := [⟨15,54519783,54519814⟩,
⟨64,235948674,235948813⟩]
theorem checked52121 : checkPrefixCuts (2^48) 6835535873 10 Manual.Count131072.C052121.packed 64 cuts52121 = true := by
 decide +kernel
def pointBounds52121 : List (Nat × Nat × Nat) := [(6835566592,112173491038289,112173878454118)]
theorem point_links_checked52121 : (cuts52121.take 1).map (fun c => (6835535873-1+2*2^10*c.k,112173436518506+c.lower,112173823934304+c.upper)) = pointBounds52121 := by
 decide +kernel
def cuts52122 : List PrefixCut := [⟨56,209097000,209097117⟩,
⟨64,239155951,239156085⟩]
theorem checked52122 : checkPrefixCuts (2^48) 6835666945 10 Manual.Count131072.C052122.packed 64 cuts52122 = true := by
 decide +kernel
def pointBounds52122 : List (Nat × Nat × Nat) := [(6835781632,112173881564180,112174268980234)]
theorem point_links_checked52122 : (cuts52122.take 1).map (fun c => (6835666945-1+2*2^10*c.k,112173672467180+c.lower,112174059883117+c.upper)) = pointBounds52122 := by
 decide +kernel
def cuts52123 : List PrefixCut := [⟨64,239439618,239439751⟩]
theorem checked52123 : checkPrefixCuts (2^48) 6835798017 10 Manual.Count131072.C052123.packed 64 cuts52123 = true := by
 decide +kernel
def cuts52124 : List PrefixCut := [⟨33,122826826,122826897⟩,
⟨64,238693867,238694001⟩]
theorem checked52124 : checkPrefixCuts (2^48) 6835929089 10 Manual.Count131072.C052124.packed 64 cuts52124 = true := by
 decide +kernel
def pointBounds52124 : List (Nat × Nat × Nat) := [(6835996672,112174273889575,112174661305850)]
theorem point_links_checked52124 : (cuts52124.take 1).map (fun c => (6835929089-1+2*2^10*c.k,112174151062749+c.lower,112174538478953+c.upper)) = pointBounds52124 := by
 decide +kernel
def cuts52125 : List PrefixCut := [⟨64,243630253,243630391⟩]
theorem checked52125 : checkPrefixCuts (2^48) 6836060161 10 Manual.Count131072.C052125.packed 64 cuts52125 = true := by
 decide +kernel
def cuts52126 : List PrefixCut := [⟨10,37427317,37427338⟩,
⟨64,239137632,239137768⟩]
theorem checked52126 : checkPrefixCuts (2^48) 6836191233 10 Manual.Count131072.C052126.packed 64 cuts52126 = true := by
 decide +kernel
def pointBounds52126 : List (Nat × Nat × Nat) := [(6836211712,112174670814186,112175058230683)]
theorem point_links_checked52126 : (cuts52126.take 1).map (fun c => (6836191233-1+2*2^10*c.k,112174633386869+c.lower,112175020803345+c.upper)) = pointBounds52126 := by
 decide +kernel
def cuts52127 : List PrefixCut := [⟨51,188778778,188778883⟩,
⟨64,236745008,236745141⟩]
theorem checked52127 : checkPrefixCuts (2^48) 6836322305 10 Manual.Count131072.C052127.packed 64 cuts52127 = true := by
 decide +kernel
def pointBounds52127 : List (Nat × Nat × Nat) := [(6836426752,112175061303279,112175448719996)]
theorem point_links_checked52127 : (cuts52127.take 1).map (fun c => (6836322305-1+2*2^10*c.k,112174872524501+c.lower,112175259941113+c.upper)) = pointBounds52127 := by
 decide +kernel
def cuts52128 : List PrefixCut := [⟨64,237852119,237852250⟩]
theorem checked52128 : checkPrefixCuts (2^48) 6836453377 10 Manual.Count131072.C052128.packed 64 cuts52128 = true := by
 decide +kernel
def cuts52129 : List PrefixCut := [⟨28,104534919,104534977⟩,
⟨64,238753330,238753468⟩]
theorem checked52129 : checkPrefixCuts (2^48) 6836584449 10 Manual.Count131072.C052129.packed 64 cuts52129 = true := by
 decide +kernel
def pointBounds52129 : List (Nat × Nat × Nat) := [(6836641792,112175451656547,112175839073481)]
theorem point_links_checked52129 : (cuts52129.take 1).map (fun c => (6836584449-1+2*2^10*c.k,112175347121628+c.lower,112175734538504+c.upper)) = pointBounds52129 := by
 decide +kernel
def cuts52130 : List PrefixCut := [⟨64,235413918,235414053⟩]
theorem checked52130 : checkPrefixCuts (2^48) 6836715521 10 Manual.Count131072.C052130.packed 64 cuts52130 = true := by
 decide +kernel
def cuts52131 : List PrefixCut := [⟨5,19432358,19432369⟩,
⟨64,239320563,239320701⟩]
theorem checked52131 : checkPrefixCuts (2^48) 6836846593 10 Manual.Count131072.C052131.packed 64 cuts52131 = true := by
 decide +kernel
def pointBounds52131 : List (Nat × Nat × Nat) := [(6836856832,112175840721234,112176228138394)]
theorem point_links_checked52131 : (cuts52131.take 1).map (fun c => (6836846593-1+2*2^10*c.k,112175821288876+c.lower,112176208706025+c.upper)) = pointBounds52131 := by
 decide +kernel
def cuts52132 : List PrefixCut := [⟨46,171099227,171099331⟩,
⟨64,237998545,237998686⟩]
theorem checked52132 : checkPrefixCuts (2^48) 6836977665 10 Manual.Count131072.C052132.packed 64 cuts52132 = true := by
 decide +kernel
def pointBounds52132 : List (Nat × Nat × Nat) := [(6837071872,112176231708666,112176619126057)]
theorem point_links_checked52132 : (cuts52132.take 1).map (fun c => (6836977665-1+2*2^10*c.k,112176060609439+c.lower,112176448026726+c.upper)) = pointBounds52132 := by
 decide +kernel
def cuts52133 : List PrefixCut := [⟨64,238858513,238858645⟩]
theorem checked52133 : checkPrefixCuts (2^48) 6837108737 10 Manual.Count131072.C052133.packed 64 cuts52133 = true := by
 decide +kernel
def cuts52134 : List PrefixCut := [⟨23,82664885,82664934⟩,
⟨64,236548531,236548666⟩]
theorem checked52134 : checkPrefixCuts (2^48) 6837239809 10 Manual.Count131072.C052134.packed 64 cuts52134 = true := by
 decide +kernel
def pointBounds52134 : List (Nat × Nat × Nat) := [(6837286912,112176620131382,112177007548991)]
theorem point_links_checked52134 : (cuts52134.take 1).map (fun c => (6837239809-1+2*2^10*c.k,112176537466497+c.lower,112176924884057+c.upper)) = pointBounds52134 := by
 decide +kernel
def cuts52135 : List PrefixCut := [⟨64,236379356,236379492⟩]
theorem checked52135 : checkPrefixCuts (2^48) 6837370881 10 Manual.Count131072.C052135.packed 64 cuts52135 = true := by
 decide +kernel
def pointBounds52135 : List (Nat × Nat × Nat) := [(6837501952,112177010394384,112177397812215)]
theorem point_links_checked52135 : (cuts52135.take 1).map (fun c => (6837370881-1+2*2^10*c.k,112176774015028+c.lower,112177161432723+c.upper)) = pointBounds52135 := by
 decide +kernel
def cuts52136 : List PrefixCut := [⟨64,240203267,240203401⟩]
theorem checked52136 : checkPrefixCuts (2^48) 6837501953 10 Manual.Count131072.C052136.packed 64 cuts52136 = true := by
 decide +kernel
def cuts52137 : List PrefixCut := [⟨41,153052569,153052654⟩,
⟨64,239169536,239169671⟩]
theorem checked52137 : checkPrefixCuts (2^48) 6837633025 10 Manual.Count131072.C052137.packed 64 cuts52137 = true := by
 decide +kernel
def pointBounds52137 : List (Nat × Nat × Nat) := [(6837716992,112177403650220,112177791068270)]
theorem point_links_checked52137 : (cuts52137.take 1).map (fun c => (6837633025-1+2*2^10*c.k,112177250597651+c.lower,112177638015616+c.upper)) = pointBounds52137 := by
 decide +kernel
def cuts52138 : List PrefixCut := [⟨64,236036469,236036603⟩]
theorem checked52138 : checkPrefixCuts (2^48) 6837764097 10 Manual.Count131072.C052138.packed 64 cuts52138 = true := by
 decide +kernel
def cuts52139 : List PrefixCut := [⟨18,68990623,68990664⟩,
⟨64,243235560,243235701⟩]
theorem checked52139 : checkPrefixCuts (2^48) 6837895169 10 Manual.Count131072.C052139.packed 64 cuts52139 = true := by
 decide +kernel
def pointBounds52139 : List (Nat × Nat × Nat) := [(6837932032,112177794794279,112178182212554)]
theorem point_links_checked52139 : (cuts52139.take 1).map (fun c => (6837895169-1+2*2^10*c.k,112177725803656+c.lower,112178113221890+c.upper)) = pointBounds52139 := by
 decide +kernel
def cuts52140 : List PrefixCut := [⟨59,221085495,221085620⟩,
⟨64,238949985,238950121⟩]
theorem checked52140 : checkPrefixCuts (2^48) 6838026241 10 Manual.Count131072.C052140.packed 64 cuts52140 = true := by
 decide +kernel
def pointBounds52140 : List (Nat × Nat × Nat) := [(6838147072,112178190124711,112178577543211)]
theorem point_links_checked52140 : (cuts52140.take 1).map (fun c => (6838026241-1+2*2^10*c.k,112177969039216+c.lower,112178356457591+c.upper)) = pointBounds52140 := by
 decide +kernel
def cuts52141 : List PrefixCut := [⟨64,236681489,236681622⟩]
theorem checked52141 : checkPrefixCuts (2^48) 6838157313 10 Manual.Count131072.C052141.packed 64 cuts52141 = true := by
 decide +kernel
def cuts52142 : List PrefixCut := [⟨36,136491138,136491214⟩,
⟨64,238199930,238200065⟩]
theorem checked52142 : checkPrefixCuts (2^48) 6838288385 10 Manual.Count131072.C052142.packed 64 cuts52142 = true := by
 decide +kernel
def pointBounds52142 : List (Nat × Nat × Nat) := [(6838362112,112178581161828,112178968580548)]
theorem point_links_checked52142 : (cuts52142.take 1).map (fun c => (6838288385-1+2*2^10*c.k,112178444670690+c.lower,112178832089334+c.upper)) = pointBounds52142 := by
 decide +kernel
def cuts52143 : List PrefixCut := [⟨64,238730442,238730577⟩]
theorem checked52143 : checkPrefixCuts (2^48) 6838419457 10 Manual.Count131072.C052143.packed 64 cuts52143 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000066
