import PlattAssemblyKernel
import PlattCertificates.Count131072.C061120
import PlattCertificates.Count131072.C061121
import PlattCertificates.Count131072.C061122
import PlattCertificates.Count131072.C061123
import PlattCertificates.Count131072.C061124
import PlattCertificates.Count131072.C061125
import PlattCertificates.Count131072.C061126
import PlattCertificates.Count131072.C061127
import PlattCertificates.Count131072.C061128
import PlattCertificates.Count131072.C061129
import PlattCertificates.Count131072.C061130
import PlattCertificates.Count131072.C061131
import PlattCertificates.Count131072.C061132
import PlattCertificates.Count131072.C061133
import PlattCertificates.Count131072.C061134
import PlattCertificates.Count131072.C061135
import PlattCertificates.Count131072.C061136
import PlattCertificates.Count131072.C061137
import PlattCertificates.Count131072.C061138
import PlattCertificates.Count131072.C061139
import PlattCertificates.Count131072.C061140
import PlattCertificates.Count131072.C061141
import PlattCertificates.Count131072.C061142
import PlattCertificates.Count131072.C061143
import PlattCertificates.Count131072.C061144
import PlattCertificates.Count131072.C061145
import PlattCertificates.Count131072.C061146
import PlattCertificates.Count131072.C061147
import PlattCertificates.Count131072.C061148
import PlattCertificates.Count131072.C061149
import PlattCertificates.Count131072.C061150
import PlattCertificates.Count131072.C061151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61120 : List PrefixCut := [⟨62,193219282,193219387⟩,
⟨64,199856531,199856640⟩]
theorem checked61120 : checkPrefixCuts (2^48) 8015052801 10 Manual.Count131072.C061120.packed 64 cuts61120 = true := by
 decide +kernel
def pointBounds61120 : List (Nat × Nat × Nat) := [(8015179776,114145286625088,114145675162914)]
theorem point_links_checked61120 : (cuts61120.take 1).map (fun c => (8015052801-1+2*2^10*c.k,114145093405806+c.lower,114145481943527+c.upper)) = pointBounds61120 := by
 decide +kernel
def cuts61121 : List PrefixCut := [⟨64,205120862,205120973⟩]
theorem checked61121 : checkPrefixCuts (2^48) 8015183873 10 Manual.Count131072.C061121.packed 64 cuts61121 = true := by
 decide +kernel
def cuts61122 : List PrefixCut := [⟨57,180676343,180676447⟩,
⟨64,202273048,202273164⟩]
theorem checked61122 : checkPrefixCuts (2^48) 8015314945 10 Manual.Count131072.C061122.packed 64 cuts61122 = true := by
 decide +kernel
def pointBounds61122 : List (Nat × Nat × Nat) := [(8015431680,114145679059542,114146067597587)]
theorem point_links_checked61122 : (cuts61122.take 1).map (fun c => (8015314945-1+2*2^10*c.k,114145498383199+c.lower,114145886921140+c.upper)) = pointBounds61122 := by
 decide +kernel
def cuts61123 : List PrefixCut := [⟨64,205992076,205992195⟩]
theorem checked61123 : checkPrefixCuts (2^48) 8015446017 10 Manual.Count131072.C061123.packed 64 cuts61123 = true := by
 decide +kernel
def cuts61124 : List PrefixCut := [⟨52,163850105,163850196⟩,
⟨64,201423654,201423766⟩]
theorem checked61124 : checkPrefixCuts (2^48) 8015577089 10 Manual.Count131072.C061124.packed 64 cuts61124 = true := by
 decide +kernel
def pointBounds61124 : List (Nat × Nat × Nat) := [(8015683584,114146070498428,114146459036695)]
theorem point_links_checked61124 : (cuts61124.take 1).map (fun c => (8015577089-1+2*2^10*c.k,114145906648323+c.lower,114146295186499+c.upper)) = pointBounds61124 := by
 decide +kernel
def cuts61125 : List PrefixCut := [⟨64,200226456,200226567⟩]
theorem checked61125 : checkPrefixCuts (2^48) 8015708161 10 Manual.Count131072.C061125.packed 64 cuts61125 = true := by
 decide +kernel
def cuts61126 : List PrefixCut := [⟨47,148850904,148850991⟩,
⟨64,202681190,202681307⟩]
theorem checked61126 : checkPrefixCuts (2^48) 8015839233 10 Manual.Count131072.C061126.packed 64 cuts61126 = true := by
 decide +kernel
def pointBounds61126 : List (Nat × Nat × Nat) := [(8015935488,114146457149337,114146845687823)]
theorem point_links_checked61126 : (cuts61126.take 1).map (fun c => (8015839233-1+2*2^10*c.k,114146308298433+c.lower,114146696836832+c.upper)) = pointBounds61126 := by
 decide +kernel
def cuts61127 : List PrefixCut := [⟨64,199974084,199974200⟩]
theorem checked61127 : checkPrefixCuts (2^48) 8015970305 10 Manual.Count131072.C061127.packed 64 cuts61127 = true := by
 decide +kernel
def cuts61128 : List PrefixCut := [⟨42,134695394,134695472⟩,
⟨64,203657748,203657864⟩]
theorem checked61128 : checkPrefixCuts (2^48) 8016101377 10 Manual.Count131072.C061128.packed 64 cuts61128 = true := by
 decide +kernel
def pointBounds61128 : List (Nat × Nat × Nat) := [(8016187392,114146845649101,114147234187811)]
theorem point_links_checked61128 : (cuts61128.take 1).map (fun c => (8016101377-1+2*2^10*c.k,114146710953707+c.lower,114147099492339+c.upper)) = pointBounds61128 := by
 decide +kernel
def cuts61129 : List PrefixCut := [⟨64,201512508,201512627⟩]
theorem checked61129 : checkPrefixCuts (2^48) 8016232449 10 Manual.Count131072.C061129.packed 64 cuts61129 = true := by
 decide +kernel
def cuts61130 : List PrefixCut := [⟨37,114606793,114606859⟩,
⟨64,198559795,198559912⟩]
theorem checked61130 : checkPrefixCuts (2^48) 8016363521 10 Manual.Count131072.C061130.packed 64 cuts61130 = true := by
 decide +kernel
def pointBounds61130 : List (Nat × Nat × Nat) := [(8016439296,114147230730756,114147619269689)]
theorem point_links_checked61130 : (cuts61130.take 1).map (fun c => (8016363521-1+2*2^10*c.k,114147116123963+c.lower,114147504662830+c.upper)) = pointBounds61130 := by
 decide +kernel
def cuts61131 : List PrefixCut := [⟨64,203226391,203226511⟩]
theorem checked61131 : checkPrefixCuts (2^48) 8016494593 10 Manual.Count131072.C061131.packed 64 cuts61131 = true := by
 decide +kernel
def cuts61132 : List PrefixCut := [⟨32,98416830,98416892⟩,
⟨64,202099507,202099626⟩]
theorem checked61132 : checkPrefixCuts (2^48) 8016625665 10 Manual.Count131072.C061132.packed 64 cuts61132 = true := by
 decide +kernel
def pointBounds61132 : List (Nat × Nat × Nat) := [(8016691200,114147616326979,114148004866145)]
theorem point_links_checked61132 : (cuts61132.take 1).map (fun c => (8016625665-1+2*2^10*c.k,114147517910149+c.lower,114147906449253+c.upper)) = pointBounds61132 := by
 decide +kernel
def cuts61133 : List PrefixCut := [⟨64,198725618,198725733⟩]
theorem checked61133 : checkPrefixCuts (2^48) 8016756737 10 Manual.Count131072.C061133.packed 64 cuts61133 = true := by
 decide +kernel
def cuts61134 : List PrefixCut := [⟨27,85352719,85352763⟩,
⟨64,201706726,201706835⟩]
theorem checked61134 : checkPrefixCuts (2^48) 8016887809 10 Manual.Count131072.C061134.packed 64 cuts61134 = true := by
 decide +kernel
def pointBounds61134 : List (Nat × Nat × Nat) := [(8016943104,114148004087993,114148392627375)]
theorem point_links_checked61134 : (cuts61134.take 1).map (fun c => (8016887809-1+2*2^10*c.k,114147918735274+c.lower,114148307274612+c.upper)) = pointBounds61134 := by
 decide +kernel
def cuts61135 : List PrefixCut := [⟨64,197876485,197876603⟩]
theorem checked61135 : checkPrefixCuts (2^48) 8017018881 10 Manual.Count131072.C061135.packed 64 cuts61135 = true := by
 decide +kernel
def cuts61136 : List PrefixCut := [⟨22,69656251,69656291⟩,
⟨64,202542721,202542842⟩]
theorem checked61136 : checkPrefixCuts (2^48) 8017149953 10 Manual.Count131072.C061136.packed 64 cuts61136 = true := by
 decide +kernel
def pointBounds61136 : List (Nat × Nat × Nat) := [(8017195008,114148387974736,114148776514341)]
theorem point_links_checked61136 : (cuts61136.take 1).map (fun c => (8017149953-1+2*2^10*c.k,114148318318485+c.lower,114148706858050+c.upper)) = pointBounds61136 := by
 decide +kernel
def cuts61137 : List PrefixCut := [⟨64,201064880,201064988⟩]
theorem checked61137 : checkPrefixCuts (2^48) 8017281025 10 Manual.Count131072.C061137.packed 64 cuts61137 = true := by
 decide +kernel
def cuts61138 : List PrefixCut := [⟨17,54698068,54698095⟩,
⟨64,201763742,201763855⟩]
theorem checked61138 : checkPrefixCuts (2^48) 8017412097 10 Manual.Count131072.C061138.packed 64 cuts61138 = true := by
 decide +kernel
def pointBounds61138 : List (Nat × Nat × Nat) := [(8017446912,114148776624154,114149165163975)]
theorem point_links_checked61138 : (cuts61138.take 1).map (fun c => (8017412097-1+2*2^10*c.k,114148721926086+c.lower,114149110465880+c.upper)) = pointBounds61138 := by
 decide +kernel
def cuts61139 : List PrefixCut := [⟨64,199302948,199303064⟩]
theorem checked61139 : checkPrefixCuts (2^48) 8017543169 10 Manual.Count131072.C061139.packed 64 cuts61139 = true := by
 decide +kernel
def cuts61140 : List PrefixCut := [⟨12,38090821,38090844⟩,
⟨64,202915665,202915782⟩]
theorem checked61140 : checkPrefixCuts (2^48) 8017674241 10 Manual.Count131072.C061140.packed 64 cuts61140 = true := by
 decide +kernel
def pointBounds61140 : List (Nat × Nat × Nat) := [(8017698816,114149161083597,114149549623643)]
theorem point_links_checked61140 : (cuts61140.take 1).map (fun c => (8017674241-1+2*2^10*c.k,114149122992776+c.lower,114149511532799+c.upper)) = pointBounds61140 := by
 decide +kernel
def cuts61141 : List PrefixCut := [⟨64,204456994,204457110⟩]
theorem checked61141 : checkPrefixCuts (2^48) 8017805313 10 Manual.Count131072.C061141.packed 64 cuts61141 = true := by
 decide +kernel
def cuts61142 : List PrefixCut := [⟨7,22256965,22256978⟩,
⟨64,203681343,203681460⟩]
theorem checked61142 : checkPrefixCuts (2^48) 8017936385 10 Manual.Count131072.C061142.packed 64 cuts61142 = true := by
 decide +kernel
def pointBounds61142 : List (Nat × Nat × Nat) := [(8017950720,114149552622400,114149941162669)]
theorem point_links_checked61142 : (cuts61142.take 1).map (fun c => (8017936385-1+2*2^10*c.k,114149530365435+c.lower,114149918905691+c.upper)) = pointBounds61142 := by
 decide +kernel
def cuts61143 : List PrefixCut := [⟨64,203993964,203994083⟩]
theorem checked61143 : checkPrefixCuts (2^48) 8018067457 10 Manual.Count131072.C061143.packed 64 cuts61143 = true := by
 decide +kernel
def cuts61144 : List PrefixCut := [⟨2,6704959,6704962⟩,
⟨64,200725926,200726046⟩]
theorem checked61144 : checkPrefixCuts (2^48) 8018198529 10 Manual.Count131072.C061144.packed 64 cuts61144 = true := by
 decide +kernel
def pointBounds61144 : List (Nat × Nat × Nat) := [(8018202624,114149944745701,114150333286196)]
theorem point_links_checked61144 : (cuts61144.take 1).map (fun c => (8018198529-1+2*2^10*c.k,114149938040742+c.lower,114150326581234+c.upper)) = pointBounds61144 := by
 decide +kernel
def cuts61145 : List PrefixCut := [⟨61,190367147,190367253⟩,
⟨64,199318506,199318618⟩]
theorem checked61145 : checkPrefixCuts (2^48) 8018329601 10 Manual.Count131072.C061145.packed 64 cuts61145 = true := by
 decide +kernel
def pointBounds61145 : List (Nat × Nat × Nat) := [(8018454528,114150329133815,114150717674533)]
theorem point_links_checked61145 : (cuts61145.take 1).map (fun c => (8018329601-1+2*2^10*c.k,114150138766668+c.lower,114150527307280+c.upper)) = pointBounds61145 := by
 decide +kernel
def cuts61146 : List PrefixCut := [⟨64,202018191,202018308⟩]
theorem checked61146 : checkPrefixCuts (2^48) 8018460673 10 Manual.Count131072.C061146.packed 64 cuts61146 = true := by
 decide +kernel
def cuts61147 : List PrefixCut := [⟨56,175968995,175969095⟩,
⟨64,200329954,200330069⟩]
theorem checked61147 : checkPrefixCuts (2^48) 8018591745 10 Manual.Count131072.C061147.packed 64 cuts61147 = true := by
 decide +kernel
def pointBounds61147 : List (Nat × Nat × Nat) := [(8018706432,114150716072360,114151104613301)]
theorem point_links_checked61147 : (cuts61147.take 1).map (fun c => (8018591745-1+2*2^10*c.k,114150540103365+c.lower,114150928644206+c.upper)) = pointBounds61147 := by
 decide +kernel
def cuts61148 : List PrefixCut := [⟨64,204258099,204258209⟩]
theorem checked61148 : checkPrefixCuts (2^48) 8018722817 10 Manual.Count131072.C061148.packed 64 cuts61148 = true := by
 decide +kernel
def cuts61149 : List PrefixCut := [⟨51,159149781,159149873⟩,
⟨64,200042587,200042704⟩]
theorem checked61149 : checkPrefixCuts (2^48) 8018853889 10 Manual.Count131072.C061149.packed 64 cuts61149 = true := by
 decide +kernel
def pointBounds61149 : List (Nat × Nat × Nat) := [(8018958336,114151103841199,114151492382357)]
theorem point_links_checked61149 : (cuts61149.take 1).map (fun c => (8018853889-1+2*2^10*c.k,114150944691418+c.lower,114151333232484+c.upper)) = pointBounds61149 := by
 decide +kernel
def cuts61150 : List PrefixCut := [⟨64,201724165,201724278⟩]
theorem checked61150 : checkPrefixCuts (2^48) 8018984961 10 Manual.Count131072.C061150.packed 64 cuts61150 = true := by
 decide +kernel
def cuts61151 : List PrefixCut := [⟨46,146613886,146613967⟩,
⟨64,203370581,203370697⟩]
theorem checked61151 : checkPrefixCuts (2^48) 8019116033 10 Manual.Count131072.C061151.packed 64 cuts61151 = true := by
 decide +kernel
def pointBounds61151 : List (Nat × Nat × Nat) := [(8019210240,114151493072056,114151881613433)]
theorem point_links_checked61151 : (cuts61151.take 1).map (fun c => (8019116033-1+2*2^10*c.k,114151346458170+c.lower,114151734999466+c.upper)) = pointBounds61151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000035
