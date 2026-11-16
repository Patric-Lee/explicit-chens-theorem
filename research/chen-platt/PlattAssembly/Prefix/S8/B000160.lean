import PlattAssemblyKernel
import PlattCertificates.Count131072.C075120
import PlattCertificates.Count131072.C075121
import PlattCertificates.Count131072.C075122
import PlattCertificates.Count131072.C075123
import PlattCertificates.Count131072.C075124
import PlattCertificates.Count131072.C075125
import PlattCertificates.Count131072.C075126
import PlattCertificates.Count131072.C075127
import PlattCertificates.Count131072.C075128
import PlattCertificates.Count131072.C075129
import PlattCertificates.Count131072.C075130
import PlattCertificates.Count131072.C075131
import PlattCertificates.Count131072.C075132
import PlattCertificates.Count131072.C075133
import PlattCertificates.Count131072.C075134
import PlattCertificates.Count131072.C075135
import PlattCertificates.Count131072.C075136
import PlattCertificates.Count131072.C075137
import PlattCertificates.Count131072.C075138
import PlattCertificates.Count131072.C075139
import PlattCertificates.Count131072.C075140
import PlattCertificates.Count131072.C075141
import PlattCertificates.Count131072.C075142
import PlattCertificates.Count131072.C075143
import PlattCertificates.Count131072.C075144
import PlattCertificates.Count131072.C075145
import PlattCertificates.Count131072.C075146
import PlattCertificates.Count131072.C075147
import PlattCertificates.Count131072.C075148
import PlattCertificates.Count131072.C075149
import PlattCertificates.Count131072.C075150
import PlattCertificates.Count131072.C075151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000160
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75120 : List PrefixCut := [⟨64,164167760,164167860⟩]
theorem checked75120 : checkPrefixCuts (2^48) 9850060801 10 Manual.Count131072.C075120.packed 64 cuts75120 = true := by
 decide +kernel
def cuts75121 : List PrefixCut := [⟨31,78782607,78782657⟩,
⟨64,161536654,161536755⟩]
theorem checked75121 : checkPrefixCuts (2^48) 9850191873 10 Manual.Count131072.C075121.packed 64 cuts75121 = true := by
 decide +kernel
def pointBounds75121 : List (Nat × Nat × Nat) := [(9850255360,116678506507743,116678896526962)]
theorem point_links_checked75121 : (cuts75121.take 1).map (fun c => (9850191873-1+2*2^10*c.k,116678427725136+c.lower,116678817744305+c.upper)) = pointBounds75121 := by
 decide +kernel
def cuts75122 : List PrefixCut := [⟨64,164534877,164534968⟩]
theorem checked75122 : checkPrefixCuts (2^48) 9850322945 10 Manual.Count131072.C075122.packed 64 cuts75122 = true := by
 decide +kernel
def cuts75123 : List PrefixCut := [⟨54,136672569,136672653⟩,
⟨64,162075266,162075368⟩]
theorem checked75123 : checkPrefixCuts (2^48) 9850454017 10 Manual.Count131072.C075123.packed 64 cuts75123 = true := by
 decide +kernel
def pointBounds75123 : List (Nat × Nat × Nat) := [(9850564608,116678890469236,116679280488681)]
theorem point_links_checked75123 : (cuts75123.take 1).map (fun c => (9850454017-1+2*2^10*c.k,116678753796667+c.lower,116679143816028+c.upper)) = pointBounds75123 := by
 decide +kernel
def cuts75124 : List PrefixCut := [⟨64,162015952,162016053⟩]
theorem checked75124 : checkPrefixCuts (2^48) 9850585089 10 Manual.Count131072.C075124.packed 64 cuts75124 = true := by
 decide +kernel
def cuts75125 : List PrefixCut := [⟨64,164471152,164471247⟩]
theorem checked75125 : checkPrefixCuts (2^48) 9850716161 10 Manual.Count131072.C075125.packed 64 cuts75125 = true := by
 decide +kernel
def cuts75126 : List PrefixCut := [⟨13,32031043,32031065⟩,
⟨64,160268661,160268762⟩]
theorem checked75126 : checkPrefixCuts (2^48) 9850847233 10 Manual.Count131072.C075126.packed 64 cuts75126 = true := by
 decide +kernel
def pointBounds75126 : List (Nat × Nat × Nat) := [(9850873856,116679274390080,116679664409761)]
theorem point_links_checked75126 : (cuts75126.take 1).map (fun c => (9850847233-1+2*2^10*c.k,116679242359037+c.lower,116679632378696+c.upper)) = pointBounds75126 := by
 decide +kernel
def cuts75127 : List PrefixCut := [⟨64,162523821,162523912⟩]
theorem checked75127 : checkPrefixCuts (2^48) 9850978305 10 Manual.Count131072.C075127.packed 64 cuts75127 = true := by
 decide +kernel
def cuts75128 : List PrefixCut := [⟨36,93804525,93804581⟩,
⟨64,165264638,165264738⟩]
theorem checked75128 : checkPrefixCuts (2^48) 9851109377 10 Manual.Count131072.C075128.packed 64 cuts75128 = true := by
 decide +kernel
def pointBounds75128 : List (Nat × Nat × Nat) := [(9851183104,116679658956044,116680048975951)]
theorem point_links_checked75128 : (cuts75128.take 1).map (fun c => (9851109377-1+2*2^10*c.k,116679565151519+c.lower,116679955171370+c.upper)) = pointBounds75128 := by
 decide +kernel
def cuts75129 : List PrefixCut := [⟨64,159890826,159890924⟩]
theorem checked75129 : checkPrefixCuts (2^48) 9851240449 10 Manual.Count131072.C075129.packed 64 cuts75129 = true := by
 decide +kernel
def cuts75130 : List PrefixCut := [⟨59,151288613,151288703⟩,
⟨64,164174490,164174586⟩]
theorem checked75130 : checkPrefixCuts (2^48) 9851371521 10 Manual.Count131072.C075130.packed 64 cuts75130 = true := by
 decide +kernel
def pointBounds75130 : List (Nat × Nat × Nat) := [(9851492352,116680041595596,116680431615735)]
theorem point_links_checked75130 : (cuts75130.take 1).map (fun c => (9851371521-1+2*2^10*c.k,116679890306983+c.lower,116680280327032+c.upper)) = pointBounds75130 := by
 decide +kernel
def cuts75131 : List PrefixCut := [⟨64,162972303,162972402⟩]
theorem checked75131 : checkPrefixCuts (2^48) 9851502593 10 Manual.Count131072.C075131.packed 64 cuts75131 = true := by
 decide +kernel
def cuts75132 : List PrefixCut := [⟨64,163170123,163170218⟩]
theorem checked75132 : checkPrefixCuts (2^48) 9851633665 10 Manual.Count131072.C075132.packed 64 cuts75132 = true := by
 decide +kernel
def cuts75133 : List PrefixCut := [⟨18,45827817,45827845⟩,
⟨64,160168037,160168140⟩]
theorem checked75133 : checkPrefixCuts (2^48) 9851764737 10 Manual.Count131072.C075133.packed 64 cuts75133 = true := by
 decide +kernel
def pointBounds75133 : List (Nat × Nat × Nat) := [(9851801600,116680426451716,116680816472083)]
theorem point_links_checked75133 : (cuts75133.take 1).map (fun c => (9851764737-1+2*2^10*c.k,116680380623899+c.lower,116680770644238+c.upper)) = pointBounds75133 := by
 decide +kernel
def cuts75134 : List PrefixCut := [⟨64,161880134,161880231⟩]
theorem checked75134 : checkPrefixCuts (2^48) 9851895809 10 Manual.Count131072.C075134.packed 64 cuts75134 = true := by
 decide +kernel
def cuts75135 : List PrefixCut := [⟨41,104852381,104852440⟩,
⟨64,163135061,163135152⟩]
theorem checked75135 : checkPrefixCuts (2^48) 9852026881 10 Manual.Count131072.C075135.packed 64 cuts75135 = true := by
 decide +kernel
def pointBounds75135 : List (Nat × Nat × Nat) := [(9852110848,116680807524451,116681197545049)]
theorem point_links_checked75135 : (cuts75135.take 1).map (fun c => (9852026881-1+2*2^10*c.k,116680702672070+c.lower,116681092692609+c.upper)) = pointBounds75135 := by
 decide +kernel
def cuts75136 : List PrefixCut := [⟨64,163732854,163732948⟩]
theorem checked75136 : checkPrefixCuts (2^48) 9852157953 10 Manual.Count131072.C075136.packed 64 cuts75136 = true := by
 decide +kernel
def cuts75137 : List PrefixCut := [⟨64,166359046,166359135⟩]
theorem checked75137 : checkPrefixCuts (2^48) 9852289025 10 Manual.Count131072.C075137.packed 64 cuts75137 = true := by
 decide +kernel
def pointBounds75137 : List (Nat × Nat × Nat) := [(9852420096,116681195899031,116681585919844)]
theorem point_links_checked75137 : (cuts75137.take 1).map (fun c => (9852289025-1+2*2^10*c.k,116681029539985+c.lower,116681419560709+c.upper)) = pointBounds75137 := by
 decide +kernel
def cuts75138 : List PrefixCut := [⟨64,160385925,160386028⟩]
theorem checked75138 : checkPrefixCuts (2^48) 9852420097 10 Manual.Count131072.C075138.packed 64 cuts75138 = true := by
 decide +kernel
def cuts75139 : List PrefixCut := [⟨64,165783248,165783343⟩]
theorem checked75139 : checkPrefixCuts (2^48) 9852551169 10 Manual.Count131072.C075139.packed 64 cuts75139 = true := by
 decide +kernel
def cuts75140 : List PrefixCut := [⟨23,57993616,57993651⟩,
⟨64,161095866,161095962⟩]
theorem checked75140 : checkPrefixCuts (2^48) 9852682241 10 Manual.Count131072.C075140.packed 64 cuts75140 = true := by
 decide +kernel
def pointBounds75140 : List (Nat × Nat × Nat) := [(9852729344,116681580061820,116681970082866)]
theorem point_links_checked75140 : (cuts75140.take 1).map (fun c => (9852682241-1+2*2^10*c.k,116681522068204+c.lower,116681912089215+c.upper)) = pointBounds75140 := by
 decide +kernel
def cuts75141 : List PrefixCut := [⟨64,163036347,163036445⟩]
theorem checked75141 : checkPrefixCuts (2^48) 9852813313 10 Manual.Count131072.C075141.packed 64 cuts75141 = true := by
 decide +kernel
def cuts75142 : List PrefixCut := [⟨46,118240709,118240773⟩,
⟨64,163576960,163577049⟩]
theorem checked75142 : checkPrefixCuts (2^48) 9852944385 10 Manual.Count131072.C075142.packed 64 cuts75142 = true := by
 decide +kernel
def pointBounds75142 : List (Nat × Nat × Nat) := [(9853038592,116681964441126,116682354462395)]
theorem point_links_checked75142 : (cuts75142.take 1).map (fun c => (9852944385-1+2*2^10*c.k,116681846200417+c.lower,116682236221622+c.upper)) = pointBounds75142 := by
 decide +kernel
def cuts75143 : List PrefixCut := [⟨64,161175137,161175237⟩]
theorem checked75143 : checkPrefixCuts (2^48) 9853075457 10 Manual.Count131072.C075143.packed 64 cuts75143 = true := by
 decide +kernel
def cuts75144 : List PrefixCut := [⟨64,164858093,164858188⟩]
theorem checked75144 : checkPrefixCuts (2^48) 9853206529 10 Manual.Count131072.C075144.packed 64 cuts75144 = true := by
 decide +kernel
def cuts75145 : List PrefixCut := [⟨5,12712064,12712073⟩,
⟨64,162570599,162570690⟩]
theorem checked75145 : checkPrefixCuts (2^48) 9853337601 10 Manual.Count131072.C075145.packed 64 cuts75145 = true := by
 decide +kernel
def pointBounds75145 : List (Nat × Nat × Nat) := [(9853347840,116682348522671,116682738544169)]
theorem point_links_checked75145 : (cuts75145.take 1).map (fun c => (9853337601-1+2*2^10*c.k,116682335810607+c.lower,116682725832096+c.upper)) = pointBounds75145 := by
 decide +kernel
def cuts75146 : List PrefixCut := [⟨64,162082826,162082931⟩]
theorem checked75146 : checkPrefixCuts (2^48) 9853468673 10 Manual.Count131072.C075146.packed 64 cuts75146 = true := by
 decide +kernel
def cuts75147 : List PrefixCut := [⟨28,71299763,71299804⟩,
⟨64,162709104,162709200⟩]
theorem checked75147 : checkPrefixCuts (2^48) 9853599745 10 Manual.Count131072.C075147.packed 64 cuts75147 = true := by
 decide +kernel
def pointBounds75147 : List (Nat × Nat × Nat) := [(9853657088,116682731763795,116683121785521)]
theorem point_links_checked75147 : (cuts75147.take 1).map (fun c => (9853599745-1+2*2^10*c.k,116682660464032+c.lower,116683050485717+c.upper)) = pointBounds75147 := by
 decide +kernel
def cuts75148 : List PrefixCut := [⟨64,163278235,163278335⟩]
theorem checked75148 : checkPrefixCuts (2^48) 9853730817 10 Manual.Count131072.C075148.packed 64 cuts75148 = true := by
 decide +kernel
def cuts75149 : List PrefixCut := [⟨51,129055682,129055756⟩,
⟨64,161247976,161248069⟩]
theorem checked75149 : checkPrefixCuts (2^48) 9853861889 10 Manual.Count131072.C075149.packed 64 cuts75149 = true := by
 decide +kernel
def pointBounds75149 : List (Nat × Nat × Nat) := [(9853966336,116683115507053,116683505529008)]
theorem point_links_checked75149 : (cuts75149.take 1).map (fun c => (9853861889-1+2*2^10*c.k,116682986451371+c.lower,116683376473252+c.upper)) = pointBounds75149 := by
 decide +kernel
def cuts75150 : List PrefixCut := [⟨64,161103013,161103105⟩]
theorem checked75150 : checkPrefixCuts (2^48) 9853992961 10 Manual.Count131072.C075150.packed 64 cuts75150 = true := by
 decide +kernel
def cuts75151 : List PrefixCut := [⟨64,163757305,163757403⟩]
theorem checked75151 : checkPrefixCuts (2^48) 9854124033 10 Manual.Count131072.C075151.packed 64 cuts75151 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000160
