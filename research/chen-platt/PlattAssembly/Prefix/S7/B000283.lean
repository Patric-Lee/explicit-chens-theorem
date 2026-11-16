import PlattAssemblyKernel
import PlattCertificates.Count131072.C069056
import PlattCertificates.Count131072.C069057
import PlattCertificates.Count131072.C069058
import PlattCertificates.Count131072.C069059
import PlattCertificates.Count131072.C069060
import PlattCertificates.Count131072.C069061
import PlattCertificates.Count131072.C069062
import PlattCertificates.Count131072.C069063
import PlattCertificates.Count131072.C069064
import PlattCertificates.Count131072.C069065
import PlattCertificates.Count131072.C069066
import PlattCertificates.Count131072.C069067
import PlattCertificates.Count131072.C069068
import PlattCertificates.Count131072.C069069
import PlattCertificates.Count131072.C069070
import PlattCertificates.Count131072.C069071
import PlattCertificates.Count131072.C069072
import PlattCertificates.Count131072.C069073
import PlattCertificates.Count131072.C069074
import PlattCertificates.Count131072.C069075
import PlattCertificates.Count131072.C069076
import PlattCertificates.Count131072.C069077
import PlattCertificates.Count131072.C069078
import PlattCertificates.Count131072.C069079
import PlattCertificates.Count131072.C069080
import PlattCertificates.Count131072.C069081
import PlattCertificates.Count131072.C069082
import PlattCertificates.Count131072.C069083
import PlattCertificates.Count131072.C069084
import PlattCertificates.Count131072.C069085
import PlattCertificates.Count131072.C069086
import PlattCertificates.Count131072.C069087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000283
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69056 : List PrefixCut := [⟨64,176650235,176650341⟩]
theorem checked69056 : checkPrefixCuts (2^48) 9055240193 10 Manual.Count131072.C069056.packed 64 cuts69056 = true := by
 decide +kernel
def cuts69057 : List PrefixCut := [⟨21,57971054,57971088⟩,
⟨64,177362584,177362690⟩]
theorem checked69057 : checkPrefixCuts (2^48) 9055371265 10 Manual.Count131072.C069057.packed 64 cuts69057 = true := by
 decide +kernel
def pointBounds69057 : List (Nat × Nat × Nat) := [(9055414272,115647423290587,115647812698028)]
theorem point_links_checked69057 : (cuts69057.take 1).map (fun c => (9055371265-1+2*2^10*c.k,115647365319533+c.lower,115647754726940+c.upper)) = pointBounds69057 := by
 decide +kernel
def cuts69058 : List PrefixCut := [⟨64,176738372,176738478⟩]
theorem checked69058 : checkPrefixCuts (2^48) 9055502337 10 Manual.Count131072.C069058.packed 64 cuts69058 = true := by
 decide +kernel
def cuts69059 : List PrefixCut := [⟨32,87000580,87000632⟩,
⟨64,174311354,174311459⟩]
theorem checked69059 : checkPrefixCuts (2^48) 9055633409 10 Manual.Count131072.C069059.packed 64 cuts69059 = true := by
 decide +kernel
def pointBounds69059 : List (Nat × Nat × Nat) := [(9055698944,115647806421069,115648195828740)]
theorem point_links_checked69059 : (cuts69059.take 1).map (fun c => (9055633409-1+2*2^10*c.k,115647719420489+c.lower,115648108828108+c.upper)) = pointBounds69059 := by
 decide +kernel
def cuts69060 : List PrefixCut := [⟨64,176111601,176111705⟩]
theorem checked69060 : checkPrefixCuts (2^48) 9055764481 10 Manual.Count131072.C069060.packed 64 cuts69060 = true := by
 decide +kernel
def cuts69061 : List PrefixCut := [⟨43,121809569,121809639⟩,
⟨64,181175373,181175477⟩]
theorem checked69061 : checkPrefixCuts (2^48) 9055895553 10 Manual.Count131072.C069061.packed 64 cuts69061 = true := by
 decide +kernel
def pointBounds69061 : List (Nat × Nat × Nat) := [(9055983616,115648191653013,115648581060911)]
theorem point_links_checked69061 : (cuts69061.take 1).map (fun c => (9055895553-1+2*2^10*c.k,115648069843444+c.lower,115648459251272+c.upper)) = pointBounds69061 := by
 decide +kernel
def cuts69062 : List PrefixCut := [⟨64,177878130,177878236⟩]
theorem checked69062 : checkPrefixCuts (2^48) 9056026625 10 Manual.Count131072.C069062.packed 64 cuts69062 = true := by
 decide +kernel
def cuts69063 : List PrefixCut := [⟨54,148286781,148286870⟩,
⟨64,176352595,176352702⟩]
theorem checked69063 : checkPrefixCuts (2^48) 9056157697 10 Manual.Count131072.C069063.packed 64 cuts69063 = true := by
 decide +kernel
def pointBounds69063 : List (Nat × Nat × Nat) := [(9056268288,115648577183728,115648966591855)]
theorem point_links_checked69063 : (cuts69063.take 1).map (fun c => (9056157697-1+2*2^10*c.k,115648428896947+c.lower,115648818304985+c.upper)) = pointBounds69063 := by
 decide +kernel
def cuts69064 : List PrefixCut := [⟨64,180297254,180297359⟩]
theorem checked69064 : checkPrefixCuts (2^48) 9056288769 10 Manual.Count131072.C069064.packed 64 cuts69064 = true := by
 decide +kernel
def cuts69065 : List PrefixCut := [⟨64,176596150,176596252⟩]
theorem checked69065 : checkPrefixCuts (2^48) 9056419841 10 Manual.Count131072.C069065.packed 64 cuts69065 = true := by
 decide +kernel
def cuts69066 : List PrefixCut := [⟨1,2330977,2330979⟩,
⟨64,178116486,178116588⟩]
theorem checked69066 : checkPrefixCuts (2^48) 9056550913 10 Manual.Count131072.C069066.packed 64 cuts69066 = true := by
 decide +kernel
def pointBounds69066 : List (Nat × Nat × Nat) := [(9056552960,115648964473923,115649353882277)]
theorem point_links_checked69066 : (cuts69066.take 1).map (fun c => (9056550913-1+2*2^10*c.k,115648962142946+c.lower,115649351551298+c.upper)) = pointBounds69066 := by
 decide +kernel
def cuts69067 : List PrefixCut := [⟨64,177305847,177305953⟩]
theorem checked69067 : checkPrefixCuts (2^48) 9056681985 10 Manual.Count131072.C069067.packed 64 cuts69067 = true := by
 decide +kernel
def cuts69068 : List PrefixCut := [⟨12,33316430,33316448⟩,
⟨64,175562882,175562980⟩]
theorem checked69068 : checkPrefixCuts (2^48) 9056813057 10 Manual.Count131072.C069068.packed 64 cuts69068 = true := by
 decide +kernel
def pointBounds69068 : List (Nat × Nat × Nat) := [(9056837632,115649350881709,115649740290287)]
theorem point_links_checked69068 : (cuts69068.take 1).map (fun c => (9056813057-1+2*2^10*c.k,115649317565279+c.lower,115649706973839+c.upper)) = pointBounds69068 := by
 decide +kernel
def cuts69069 : List PrefixCut := [⟨64,177549333,177549439⟩]
theorem checked69069 : checkPrefixCuts (2^48) 9056944129 10 Manual.Count131072.C069069.packed 64 cuts69069 = true := by
 decide +kernel
def cuts69070 : List PrefixCut := [⟨23,63802766,63802804⟩,
⟨64,178323714,178323820⟩]
theorem checked69070 : checkPrefixCuts (2^48) 9057075201 10 Manual.Count131072.C069070.packed 64 cuts69070 = true := by
 decide +kernel
def pointBounds69070 : List (Nat × Nat × Nat) := [(9057122304,115649734480260,115650123889062)]
theorem point_links_checked69070 : (cuts69070.take 1).map (fun c => (9057075201-1+2*2^10*c.k,115649670677494+c.lower,115650060086258+c.upper)) = pointBounds69070 := by
 decide +kernel
def cuts69071 : List PrefixCut := [⟨64,178010363,178010466⟩]
theorem checked69071 : checkPrefixCuts (2^48) 9057206273 10 Manual.Count131072.C069071.packed 64 cuts69071 = true := by
 decide +kernel
def cuts69072 : List PrefixCut := [⟨34,94598031,94598087⟩,
⟨64,175894562,175894671⟩]
theorem checked69072 : checkPrefixCuts (2^48) 9057337345 10 Manual.Count131072.C069072.packed 64 cuts69072 = true := by
 decide +kernel
def pointBounds69072 : List (Nat × Nat × Nat) := [(9057406976,115650121609602,115650511018631)]
theorem point_links_checked69072 : (cuts69072.take 1).map (fun c => (9057337345-1+2*2^10*c.k,115650027011571+c.lower,115650416420544+c.upper)) = pointBounds69072 := by
 decide +kernel
def cuts69073 : List PrefixCut := [⟨64,177321525,177321628⟩]
theorem checked69073 : checkPrefixCuts (2^48) 9057468417 10 Manual.Count131072.C069073.packed 64 cuts69073 = true := by
 decide +kernel
def cuts69074 : List PrefixCut := [⟨45,125329284,125329357⟩,
⟨64,178593068,178593170⟩]
theorem checked69074 : checkPrefixCuts (2^48) 9057599489 10 Manual.Count131072.C069074.packed 64 cuts69074 = true := by
 decide +kernel
def pointBounds69074 : List (Nat × Nat × Nat) := [(9057691648,115650505556942,115650894966200)]
theorem point_links_checked69074 : (cuts69074.take 1).map (fun c => (9057599489-1+2*2^10*c.k,115650380227658+c.lower,115650769636843+c.upper)) = pointBounds69074 := by
 decide +kernel
def cuts69075 : List PrefixCut := [⟨64,178217589,178217694⟩]
theorem checked69075 : checkPrefixCuts (2^48) 9057730561 10 Manual.Count131072.C069075.packed 64 cuts69075 = true := by
 decide +kernel
def cuts69076 : List PrefixCut := [⟨56,157519208,157519294⟩,
⟨64,179520154,179520253⟩]
theorem checked69076 : checkPrefixCuts (2^48) 9057861633 10 Manual.Count131072.C069076.packed 64 cuts69076 = true := by
 decide +kernel
def pointBounds69076 : List (Nat × Nat × Nat) := [(9057976320,115650894557523,115651283967001)]
theorem point_links_checked69076 : (cuts69076.take 1).map (fun c => (9057861633-1+2*2^10*c.k,115650737038315+c.lower,115651126447707+c.upper)) = pointBounds69076 := by
 decide +kernel
def cuts69077 : List PrefixCut := [⟨64,177466636,177466740⟩]
theorem checked69077 : checkPrefixCuts (2^48) 9057992705 10 Manual.Count131072.C069077.packed 64 cuts69077 = true := by
 decide +kernel
def cuts69078 : List PrefixCut := [⟨64,176221104,176221212⟩]
theorem checked69078 : checkPrefixCuts (2^48) 9058123777 10 Manual.Count131072.C069078.packed 64 cuts69078 = true := by
 decide +kernel
def cuts69079 : List PrefixCut := [⟨3,7799535,7799540⟩,
⟨64,177181840,177181940⟩]
theorem checked69079 : checkPrefixCuts (2^48) 9058254849 10 Manual.Count131072.C069079.packed 64 cuts69079 = true := by
 decide +kernel
def pointBounds69079 : List (Nat × Nat × Nat) := [(9058260992,115651278045744,115651667455452)]
theorem point_links_checked69079 : (cuts69079.take 1).map (fun c => (9058254849-1+2*2^10*c.k,115651270246209+c.lower,115651659655912+c.upper)) = pointBounds69079 := by
 decide +kernel
def cuts69080 : List PrefixCut := [⟨64,175843128,175843232⟩]
theorem checked69080 : checkPrefixCuts (2^48) 9058385921 10 Manual.Count131072.C069080.packed 64 cuts69080 = true := by
 decide +kernel
def cuts69081 : List PrefixCut := [⟨14,39338301,39338322⟩,
⟨64,179010003,179010108⟩]
theorem checked69081 : checkPrefixCuts (2^48) 9058516993 10 Manual.Count131072.C069081.packed 64 cuts69081 = true := by
 decide +kernel
def pointBounds69081 : List (Nat × Nat × Nat) := [(9058545664,115651662609478,115652052019406)]
theorem point_links_checked69081 : (cuts69081.take 1).map (fun c => (9058516993-1+2*2^10*c.k,115651623271177+c.lower,115652012681084+c.upper)) = pointBounds69081 := by
 decide +kernel
def cuts69082 : List PrefixCut := [⟨64,179038484,179038589⟩]
theorem checked69082 : checkPrefixCuts (2^48) 9058648065 10 Manual.Count131072.C069082.packed 64 cuts69082 = true := by
 decide +kernel
def cuts69083 : List PrefixCut := [⟨25,70067288,70067331⟩,
⟨64,180371978,180372088⟩]
theorem checked69083 : checkPrefixCuts (2^48) 9058779137 10 Manual.Count131072.C069083.packed 64 cuts69083 = true := by
 decide +kernel
def pointBounds69083 : List (Nat × Nat × Nat) := [(9058830336,115652051386952,115652440797112)]
theorem point_links_checked69083 : (cuts69083.take 1).map (fun c => (9058779137-1+2*2^10*c.k,115651981319664+c.lower,115652370729781+c.upper)) = pointBounds69083 := by
 decide +kernel
def cuts69084 : List PrefixCut := [⟨64,177852588,177852692⟩]
theorem checked69084 : checkPrefixCuts (2^48) 9058910209 10 Manual.Count131072.C069084.packed 64 cuts69084 = true := by
 decide +kernel
def cuts69085 : List PrefixCut := [⟨36,100949781,100949838⟩,
⟨64,178720007,178720114⟩]
theorem checked69085 : checkPrefixCuts (2^48) 9059041281 10 Manual.Count131072.C069085.packed 64 cuts69085 = true := by
 decide +kernel
def pointBounds69085 : List (Nat × Nat × Nat) := [(9059115008,115652440494011,115652829904399)]
theorem point_links_checked69085 : (cuts69085.take 1).map (fun c => (9059041281-1+2*2^10*c.k,115652339544230+c.lower,115652728954561+c.upper)) = pointBounds69085 := by
 decide +kernel
def cuts69086 : List PrefixCut := [⟨64,176324994,176325102⟩]
theorem checked69086 : checkPrefixCuts (2^48) 9059172353 10 Manual.Count131072.C069086.packed 64 cuts69086 = true := by
 decide +kernel
def cuts69087 : List PrefixCut := [⟨47,128754459,128754532⟩,
⟨64,175359262,175359363⟩]
theorem checked69087 : checkPrefixCuts (2^48) 9059303425 10 Manual.Count131072.C069087.packed 64 cuts69087 = true := by
 decide +kernel
def pointBounds69087 : List (Nat × Nat × Nat) := [(9059399680,115652823343690,115653212754309)]
theorem point_links_checked69087 : (cuts69087.take 1).map (fun c => (9059303425-1+2*2^10*c.k,115652694589231+c.lower,115653083999777+c.upper)) = pointBounds69087 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000283
