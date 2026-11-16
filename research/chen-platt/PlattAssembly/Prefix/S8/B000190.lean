import PlattAssemblyKernel
import PlattCertificates.Count131072.C076080
import PlattCertificates.Count131072.C076081
import PlattCertificates.Count131072.C076082
import PlattCertificates.Count131072.C076083
import PlattCertificates.Count131072.C076084
import PlattCertificates.Count131072.C076085
import PlattCertificates.Count131072.C076086
import PlattCertificates.Count131072.C076087
import PlattCertificates.Count131072.C076088
import PlattCertificates.Count131072.C076089
import PlattCertificates.Count131072.C076090
import PlattCertificates.Count131072.C076091
import PlattCertificates.Count131072.C076092
import PlattCertificates.Count131072.C076093
import PlattCertificates.Count131072.C076094
import PlattCertificates.Count131072.C076095
import PlattCertificates.Count131072.C076096
import PlattCertificates.Count131072.C076097
import PlattCertificates.Count131072.C076098
import PlattCertificates.Count131072.C076099
import PlattCertificates.Count131072.C076100
import PlattCertificates.Count131072.C076101
import PlattCertificates.Count131072.C076102
import PlattCertificates.Count131072.C076103
import PlattCertificates.Count131072.C076104
import PlattCertificates.Count131072.C076105
import PlattCertificates.Count131072.C076106
import PlattCertificates.Count131072.C076107
import PlattCertificates.Count131072.C076108
import PlattCertificates.Count131072.C076109
import PlattCertificates.Count131072.C076110
import PlattCertificates.Count131072.C076111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts76080 : List PrefixCut := [⟨64,161165977,161166067⟩]
theorem checked76080 : checkPrefixCuts (2^48) 9975889921 10 Manual.Count131072.C076080.packed 64 cuts76080 = true := by
 decide +kernel
def cuts76081 : List PrefixCut := [⟨49,122735270,122735344⟩,
⟨64,159273459,159273557⟩]
theorem checked76081 : checkPrefixCuts (2^48) 9976020993 10 Manual.Count131072.C076081.packed 64 cuts76081 = true := by
 decide +kernel
def pointBounds76081 : List (Nat × Nat × Nat) := [(9976121344,116833778015773,116834168128421)]
theorem point_links_checked76081 : (cuts76081.take 1).map (fun c => (9976020993-1+2*2^10*c.k,116833655280503+c.lower,116834045393077+c.upper)) = pointBounds76081 := by
 decide +kernel
def cuts76082 : List PrefixCut := [⟨64,161726027,161726121⟩]
theorem checked76082 : checkPrefixCuts (2^48) 9976152065 10 Manual.Count131072.C076082.packed 64 cuts76082 = true := by
 decide +kernel
def cuts76083 : List PrefixCut := [⟨64,161582833,161582928⟩]
theorem checked76083 : checkPrefixCuts (2^48) 9976283137 10 Manual.Count131072.C076083.packed 64 cuts76083 = true := by
 decide +kernel
def cuts76084 : List PrefixCut := [⟨10,25505460,25505476⟩,
⟨64,161326783,161326883⟩]
theorem checked76084 : checkPrefixCuts (2^48) 9976414209 10 Manual.Count131072.C076084.packed 64 cuts76084 = true := by
 decide +kernel
def pointBounds76084 : List (Nat × Nat × Nat) := [(9976434688,116834163368282,116834553481159)]
theorem point_links_checked76084 : (cuts76084.take 1).map (fun c => (9976414209-1+2*2^10*c.k,116834137862822+c.lower,116834527975683+c.upper)) = pointBounds76084 := by
 decide +kernel
def cuts76085 : List PrefixCut := [⟨64,159039369,159039466⟩]
theorem checked76085 : checkPrefixCuts (2^48) 9976545281 10 Manual.Count131072.C076085.packed 64 cuts76085 = true := by
 decide +kernel
def cuts76086 : List PrefixCut := [⟨35,86360577,86360636⟩,
⟨64,160081166,160081267⟩]
theorem checked76086 : checkPrefixCuts (2^48) 9976676353 10 Manual.Count131072.C076086.packed 64 cuts76086 = true := by
 decide +kernel
def pointBounds76086 : List (Nat × Nat × Nat) := [(9976748032,116834544589551,116834934702668)]
theorem point_links_checked76086 : (cuts76086.take 1).map (fun c => (9976676353-1+2*2^10*c.k,116834458228974+c.lower,116834848342032+c.upper)) = pointBounds76086 := by
 decide +kernel
def cuts76087 : List PrefixCut := [⟨64,159938007,159938099⟩]
theorem checked76087 : checkPrefixCuts (2^48) 9976807425 10 Manual.Count131072.C076087.packed 64 cuts76087 = true := by
 decide +kernel
def cuts76088 : List PrefixCut := [⟨60,150315552,150315634⟩,
⟨64,160302668,160302756⟩]
theorem checked76088 : checkPrefixCuts (2^48) 9976938497 10 Manual.Count131072.C076088.packed 64 cuts76088 = true := by
 decide +kernel
def pointBounds76088 : List (Nat × Nat × Nat) := [(9977061376,116834928563699,116835318677032)]
theorem point_links_checked76088 : (cuts76088.take 1).map (fun c => (9976938497-1+2*2^10*c.k,116834778248147+c.lower,116835168361398+c.upper)) = pointBounds76088 := by
 decide +kernel
def cuts76089 : List PrefixCut := [⟨64,159623472,159623572⟩]
theorem checked76089 : checkPrefixCuts (2^48) 9977069569 10 Manual.Count131072.C076089.packed 64 cuts76089 = true := by
 decide +kernel
def cuts76090 : List PrefixCut := [⟨64,161116589,161116687⟩]
theorem checked76090 : checkPrefixCuts (2^48) 9977200641 10 Manual.Count131072.C076090.packed 64 cuts76090 = true := by
 decide +kernel
def cuts76091 : List PrefixCut := [⟨21,52078204,52078236⟩,
⟨64,160127073,160127167⟩]
theorem checked76091 : checkPrefixCuts (2^48) 9977331713 10 Manual.Count131072.C076091.packed 64 cuts76091 = true := by
 decide +kernel
def pointBounds76091 : List (Nat × Nat × Nat) := [(9977374720,116835311369080,116835701482649)]
theorem point_links_checked76091 : (cuts76091.take 1).map (fun c => (9977331713-1+2*2^10*c.k,116835259290876+c.lower,116835649404413+c.upper)) = pointBounds76091 := by
 decide +kernel
def cuts76092 : List PrefixCut := [⟨64,158940110,158940202⟩]
theorem checked76092 : checkPrefixCuts (2^48) 9977462785 10 Manual.Count131072.C076092.packed 64 cuts76092 = true := by
 decide +kernel
def cuts76093 : List PrefixCut := [⟨46,115465849,115465920⟩,
⟨64,159981830,159981927⟩]
theorem checked76093 : checkPrefixCuts (2^48) 9977593857 10 Manual.Count131072.C076093.packed 64 cuts76093 = true := by
 decide +kernel
def pointBounds76093 : List (Nat × Nat × Nat) := [(9977688064,116835693823908,116836083937702)]
theorem point_links_checked76093 : (cuts76093.take 1).map (fun c => (9977593857-1+2*2^10*c.k,116835578358059+c.lower,116835968471782+c.upper)) = pointBounds76093 := by
 decide +kernel
def cuts76094 : List PrefixCut := [⟨64,158484568,158484663⟩]
theorem checked76094 : checkPrefixCuts (2^48) 9977724929 10 Manual.Count131072.C076094.packed 64 cuts76094 = true := by
 decide +kernel
def cuts76095 : List PrefixCut := [⟨64,161190634,161190734⟩]
theorem checked76095 : checkPrefixCuts (2^48) 9977856001 10 Manual.Count131072.C076095.packed 64 cuts76095 = true := by
 decide +kernel
def cuts76096 : List PrefixCut := [⟨7,17377094,17377103⟩,
⟨64,160878215,160878316⟩]
theorem checked76096 : checkPrefixCuts (2^48) 9977987073 10 Manual.Count131072.C076096.packed 64 cuts76096 = true := by
 decide +kernel
def pointBounds76096 : List (Nat × Nat × Nat) := [(9978001408,116836075392185,116836465506209)]
theorem point_links_checked76096 : (cuts76096.take 1).map (fun c => (9977987073-1+2*2^10*c.k,116836058015091+c.lower,116836448129106+c.upper)) = pointBounds76096 := by
 decide +kernel
def cuts76097 : List PrefixCut := [⟨64,157321770,157321863⟩]
theorem checked76097 : checkPrefixCuts (2^48) 9978118145 10 Manual.Count131072.C076097.packed 64 cuts76097 = true := by
 decide +kernel
def cuts76098 : List PrefixCut := [⟨32,81692547,81692599⟩,
⟨64,162763976,162764075⟩]
theorem checked76098 : checkPrefixCuts (2^48) 9978249217 10 Manual.Count131072.C076098.packed 64 cuts76098 = true := by
 decide +kernel
def pointBounds76098 : List (Nat × Nat × Nat) := [(9978314752,116836457907623,116836848021884)]
theorem point_links_checked76098 : (cuts76098.take 1).map (fun c => (9978249217-1+2*2^10*c.k,116836376215076+c.lower,116836766329285+c.upper)) = pointBounds76098 := by
 decide +kernel
def cuts76099 : List PrefixCut := [⟨64,162536161,162536263⟩]
theorem checked76099 : checkPrefixCuts (2^48) 9978380289 10 Manual.Count131072.C076099.packed 64 cuts76099 = true := by
 decide +kernel
def cuts76100 : List PrefixCut := [⟨57,143578422,143578507⟩,
⟨64,160390244,160390339⟩]
theorem checked76100 : checkPrefixCuts (2^48) 9978511361 10 Manual.Count131072.C076100.packed 64 cuts76100 = true := by
 decide +kernel
def pointBounds76100 : List (Nat × Nat × Nat) := [(9978628096,116836845093635,116837235208130)]
theorem point_links_checked76100 : (cuts76100.take 1).map (fun c => (9978511361-1+2*2^10*c.k,116836701515213+c.lower,116837091629623+c.upper)) = pointBounds76100 := by
 decide +kernel
def cuts76101 : List PrefixCut := [⟨64,161883123,161883218⟩]
theorem checked76101 : checkPrefixCuts (2^48) 9978642433 10 Manual.Count131072.C076101.packed 64 cuts76101 = true := by
 decide +kernel
def cuts76102 : List PrefixCut := [⟨64,160780917,160781011⟩]
theorem checked76102 : checkPrefixCuts (2^48) 9978773505 10 Manual.Count131072.C076102.packed 64 cuts76102 = true := by
 decide +kernel
def cuts76103 : List PrefixCut := [⟨18,47246628,47246655⟩,
⟨64,160891650,160891744⟩]
theorem checked76103 : checkPrefixCuts (2^48) 9978904577 10 Manual.Count131072.C076103.packed 64 cuts76103 = true := by
 decide +kernel
def pointBounds76103 : List (Nat × Nat × Nat) := [(9978941440,116837231816125,116837621930846)]
theorem point_links_checked76103 : (cuts76103.take 1).map (fun c => (9978904577-1+2*2^10*c.k,116837184569497+c.lower,116837574684191+c.upper)) = pointBounds76103 := by
 decide +kernel
def cuts76104 : List PrefixCut := [⟨64,160692064,160692163⟩]
theorem checked76104 : checkPrefixCuts (2^48) 9979035649 10 Manual.Count131072.C076104.packed 64 cuts76104 = true := by
 decide +kernel
def cuts76105 : List PrefixCut := [⟨43,107098669,107098726⟩,
⟨64,159505311,159505399⟩]
theorem checked76105 : checkPrefixCuts (2^48) 9979166721 10 Manual.Count131072.C076105.packed 64 cuts76105 = true := by
 decide +kernel
def pointBounds76105 : List (Nat × Nat × Nat) := [(9979254784,116837613251880,116838003366824)]
theorem point_links_checked76105 : (cuts76105.take 1).map (fun c => (9979166721-1+2*2^10*c.k,116837506153211+c.lower,116837896268098+c.upper)) = pointBounds76105 := by
 decide +kernel
def cuts76106 : List PrefixCut := [⟨64,161562227,161562326⟩]
theorem checked76106 : checkPrefixCuts (2^48) 9979297793 10 Manual.Count131072.C076106.packed 64 cuts76106 = true := by
 decide +kernel
def cuts76107 : List PrefixCut := [⟨64,159303677,159303779⟩]
theorem checked76107 : checkPrefixCuts (2^48) 9979428865 10 Manual.Count131072.C076107.packed 64 cuts76107 = true := by
 decide +kernel
def cuts76108 : List PrefixCut := [⟨4,9589744,9589749⟩,
⟨64,161219524,161219615⟩]
theorem checked76108 : checkPrefixCuts (2^48) 9979559937 10 Manual.Count131072.C076108.packed 64 cuts76108 = true := by
 decide +kernel
def pointBounds76108 : List (Nat × Nat × Nat) := [(9979568128,116837996114170,116838386229351)]
theorem point_links_checked76108 : (cuts76108.take 1).map (fun c => (9979559937-1+2*2^10*c.k,116837986524426+c.lower,116838376639602+c.upper)) = pointBounds76108 := by
 decide +kernel
def cuts76109 : List PrefixCut := [⟨64,162176369,162176460⟩]
theorem checked76109 : checkPrefixCuts (2^48) 9979691009 10 Manual.Count131072.C076109.packed 64 cuts76109 = true := by
 decide +kernel
def cuts76110 : List PrefixCut := [⟨29,72626111,72626158⟩,
⟨64,159720467,159720567⟩]
theorem checked76110 : checkPrefixCuts (2^48) 9979822081 10 Manual.Count131072.C076110.packed 64 cuts76110 = true := by
 decide +kernel
def pointBounds76110 : List (Nat × Nat × Nat) := [(9979881472,116838382546430,116838772661835)]
theorem point_links_checked76110 : (cuts76110.take 1).map (fun c => (9979822081-1+2*2^10*c.k,116838309920319+c.lower,116838700035677+c.upper)) = pointBounds76110 := by
 decide +kernel
def cuts76111 : List PrefixCut := [⟨64,162651564,162651667⟩]
theorem checked76111 : checkPrefixCuts (2^48) 9979953153 10 Manual.Count131072.C076111.packed 64 cuts76111 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000190
