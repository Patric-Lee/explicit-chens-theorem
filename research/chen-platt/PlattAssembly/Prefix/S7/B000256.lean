import PlattAssemblyKernel
import PlattCertificates.Count131072.C068192
import PlattCertificates.Count131072.C068193
import PlattCertificates.Count131072.C068194
import PlattCertificates.Count131072.C068195
import PlattCertificates.Count131072.C068196
import PlattCertificates.Count131072.C068197
import PlattCertificates.Count131072.C068198
import PlattCertificates.Count131072.C068199
import PlattCertificates.Count131072.C068200
import PlattCertificates.Count131072.C068201
import PlattCertificates.Count131072.C068202
import PlattCertificates.Count131072.C068203
import PlattCertificates.Count131072.C068204
import PlattCertificates.Count131072.C068205
import PlattCertificates.Count131072.C068206
import PlattCertificates.Count131072.C068207
import PlattCertificates.Count131072.C068208
import PlattCertificates.Count131072.C068209
import PlattCertificates.Count131072.C068210
import PlattCertificates.Count131072.C068211
import PlattCertificates.Count131072.C068212
import PlattCertificates.Count131072.C068213
import PlattCertificates.Count131072.C068214
import PlattCertificates.Count131072.C068215
import PlattCertificates.Count131072.C068216
import PlattCertificates.Count131072.C068217
import PlattCertificates.Count131072.C068218
import PlattCertificates.Count131072.C068219
import PlattCertificates.Count131072.C068220
import PlattCertificates.Count131072.C068221
import PlattCertificates.Count131072.C068222
import PlattCertificates.Count131072.C068223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000256
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68192 : List PrefixCut := [⟨64,179233663,179233763⟩]
theorem checked68192 : checkPrefixCuts (2^48) 8941993985 10 Manual.Count131072.C068192.packed 64 cuts68192 = true := by
 decide +kernel
def cuts68193 : List PrefixCut := [⟨64,179042169,179042274⟩]
theorem checked68193 : checkPrefixCuts (2^48) 8942125057 10 Manual.Count131072.C068193.packed 64 cuts68193 = true := by
 decide +kernel
def cuts68194 : List PrefixCut := [⟨5,13566554,13566564⟩,
⟨64,178756254,178756360⟩]
theorem checked68194 : checkPrefixCuts (2^48) 8942256129 10 Manual.Count131072.C068194.packed 64 cuts68194 = true := by
 decide +kernel
def pointBounds68194 : List (Nat × Nat × Nat) := [(8942266368,115492992467541,115493381784536)]
theorem point_links_checked68194 : (cuts68194.take 1).map (fun c => (8942256129-1+2*2^10*c.k,115492978900987+c.lower,115493368217972+c.upper)) = pointBounds68194 := by
 decide +kernel
def cuts68195 : List PrefixCut := [⟨64,180044160,180044260⟩]
theorem checked68195 : checkPrefixCuts (2^48) 8942387201 10 Manual.Count131072.C068195.packed 64 cuts68195 = true := by
 decide +kernel
def cuts68196 : List PrefixCut := [⟨14,38274778,38274803⟩,
⟨64,179947088,179947196⟩]
theorem checked68196 : checkPrefixCuts (2^48) 8942518273 10 Manual.Count131072.C068196.packed 64 cuts68196 = true := by
 decide +kernel
def pointBounds68196 : List (Nat × Nat × Nat) := [(8942546944,115493375976179,115493765293395)]
theorem point_links_checked68196 : (cuts68196.take 1).map (fun c => (8942518273-1+2*2^10*c.k,115493337701401+c.lower,115493727018592+c.upper)) = pointBounds68196 := by
 decide +kernel
def cuts68197 : List PrefixCut := [⟨64,181266429,181266534⟩]
theorem checked68197 : checkPrefixCuts (2^48) 8942649345 10 Manual.Count131072.C068197.packed 64 cuts68197 = true := by
 decide +kernel
def cuts68198 : List PrefixCut := [⟨23,66569654,66569693⟩,
⟨64,182617191,182617300⟩]
theorem checked68198 : checkPrefixCuts (2^48) 8942780417 10 Manual.Count131072.C068198.packed 64 cuts68198 = true := by
 decide +kernel
def pointBounds68198 : List (Nat × Nat × Nat) := [(8942827520,115493765484572,115494154802015)]
theorem point_links_checked68198 : (cuts68198.take 1).map (fun c => (8942780417-1+2*2^10*c.k,115493698914918+c.lower,115494088232322+c.upper)) = pointBounds68198 := by
 decide +kernel
def cuts68199 : List PrefixCut := [⟨64,180537197,180537303⟩]
theorem checked68199 : checkPrefixCuts (2^48) 8942911489 10 Manual.Count131072.C068199.packed 64 cuts68199 = true := by
 decide +kernel
def cuts68200 : List PrefixCut := [⟨32,88032947,88032998⟩,
⟨64,179244107,179244210⟩]
theorem checked68200 : checkPrefixCuts (2^48) 8943042561 10 Manual.Count131072.C068200.packed 64 cuts68200 = true := by
 decide +kernel
def pointBounds68200 : List (Nat × Nat × Nat) := [(8943108096,115494150102253,115494539419923)]
theorem point_links_checked68200 : (cuts68200.take 1).map (fun c => (8943042561-1+2*2^10*c.k,115494062069306+c.lower,115494451386925+c.upper)) = pointBounds68200 := by
 decide +kernel
def cuts68201 : List PrefixCut := [⟨64,178549070,178549176⟩]
theorem checked68201 : checkPrefixCuts (2^48) 8943173633 10 Manual.Count131072.C068201.packed 64 cuts68201 = true := by
 decide +kernel
def cuts68202 : List PrefixCut := [⟨41,117677946,117678014⟩,
⟨64,183015635,183015742⟩]
theorem checked68202 : checkPrefixCuts (2^48) 8943304705 10 Manual.Count131072.C068202.packed 64 cuts68202 = true := by
 decide +kernel
def pointBounds68202 : List (Nat × Nat × Nat) := [(8943388672,115494537540429,115494926858325)]
theorem point_links_checked68202 : (cuts68202.take 1).map (fun c => (8943304705-1+2*2^10*c.k,115494419862483+c.lower,115494809180311+c.upper)) = pointBounds68202 := by
 decide +kernel
def cuts68203 : List PrefixCut := [⟨64,183422101,183422204⟩]
theorem checked68203 : checkPrefixCuts (2^48) 8943435777 10 Manual.Count131072.C068203.packed 64 cuts68203 = true := by
 decide +kernel
def cuts68204 : List PrefixCut := [⟨50,142033811,142033892⟩,
⟨64,181405183,181405286⟩]
theorem checked68204 : checkPrefixCuts (2^48) 8943566849 10 Manual.Count131072.C068204.packed 64 cuts68204 = true := by
 decide +kernel
def pointBounds68204 : List (Nat × Nat × Nat) := [(8943669248,115494928334030,115495317652149)]
theorem point_links_checked68204 : (cuts68204.take 1).map (fun c => (8943566849-1+2*2^10*c.k,115494786300219+c.lower,115495175618257+c.upper)) = pointBounds68204 := by
 decide +kernel
def cuts68205 : List PrefixCut := [⟨64,180993401,180993510⟩]
theorem checked68205 : checkPrefixCuts (2^48) 8943697921 10 Manual.Count131072.C068205.packed 64 cuts68205 = true := by
 decide +kernel
def cuts68206 : List PrefixCut := [⟨59,168087669,168087765⟩,
⟨64,181840480,181840585⟩]
theorem checked68206 : checkPrefixCuts (2^48) 8943828993 10 Manual.Count131072.C068206.packed 64 cuts68206 = true := by
 decide +kernel
def pointBounds68206 : List (Nat × Nat × Nat) := [(8943949824,115495316786472,115495706104818)]
theorem point_links_checked68206 : (cuts68206.take 1).map (fun c => (8943828993-1+2*2^10*c.k,115495148698803+c.lower,115495538017053+c.upper)) = pointBounds68206 := by
 decide +kernel
def cuts68207 : List PrefixCut := [⟨64,179855154,179855255⟩]
theorem checked68207 : checkPrefixCuts (2^48) 8943960065 10 Manual.Count131072.C068207.packed 64 cuts68207 = true := by
 decide +kernel
def cuts68208 : List PrefixCut := [⟨64,177020193,177020297⟩]
theorem checked68208 : checkPrefixCuts (2^48) 8944091137 10 Manual.Count131072.C068208.packed 64 cuts68208 = true := by
 decide +kernel
def cuts68209 : List PrefixCut := [⟨4,11014504,11014511⟩,
⟨64,177584059,177584158⟩]
theorem checked68209 : checkPrefixCuts (2^48) 8944222209 10 Manual.Count131072.C068209.packed 64 cuts68209 = true := by
 decide +kernel
def pointBounds68209 : List (Nat × Nat × Nat) := [(8944230400,115495698429134,115496087747701)]
theorem point_links_checked68209 : (cuts68209.take 1).map (fun c => (8944222209-1+2*2^10*c.k,115495687414630+c.lower,115496076733190+c.upper)) = pointBounds68209 := by
 decide +kernel
def cuts68210 : List PrefixCut := [⟨64,182396257,182396359⟩]
theorem checked68210 : checkPrefixCuts (2^48) 8944353281 10 Manual.Count131072.C068210.packed 64 cuts68210 = true := by
 decide +kernel
def cuts68211 : List PrefixCut := [⟨13,38643999,38644021⟩,
⟨64,182928559,182928670⟩]
theorem checked68211 : checkPrefixCuts (2^48) 8944484353 10 Manual.Count131072.C068211.packed 64 cuts68211 = true := by
 decide +kernel
def pointBounds68211 : List (Nat × Nat × Nat) := [(8944510976,115496086038945,115496475357728)]
theorem point_links_checked68211 : (cuts68211.take 1).map (fun c => (8944484353-1+2*2^10*c.k,115496047394946+c.lower,115496436713707+c.upper)) = pointBounds68211 := by
 decide +kernel
def cuts68212 : List PrefixCut := [⟨64,178929387,178929491⟩]
theorem checked68212 : checkPrefixCuts (2^48) 8944615425 10 Manual.Count131072.C068212.packed 64 cuts68212 = true := by
 decide +kernel
def cuts68213 : List PrefixCut := [⟨22,60827839,60827876⟩,
⟨64,179776389,179776492⟩]
theorem checked68213 : checkPrefixCuts (2^48) 8944746497 10 Manual.Count131072.C068213.packed 64 cuts68213 = true := by
 decide +kernel
def pointBounds68213 : List (Nat × Nat × Nat) := [(8944791552,115496470080731,115496859399744)]
theorem point_links_checked68213 : (cuts68213.take 1).map (fun c => (8944746497-1+2*2^10*c.k,115496409252892+c.lower,115496798571868+c.upper)) = pointBounds68213 := by
 decide +kernel
def cuts68214 : List PrefixCut := [⟨64,178766805,178766911⟩]
theorem checked68214 : checkPrefixCuts (2^48) 8944877569 10 Manual.Count131072.C068214.packed 64 cuts68214 = true := by
 decide +kernel
def cuts68215 : List PrefixCut := [⟨31,86062644,86062699⟩,
⟨64,178512438,178512548⟩]
theorem checked68215 : checkPrefixCuts (2^48) 8945008641 10 Manual.Count131072.C068215.packed 64 cuts68215 = true := by
 decide +kernel
def pointBounds68215 : List (Nat × Nat × Nat) := [(8945072128,115496853858730,115497243177970)]
theorem point_links_checked68215 : (cuts68215.take 1).map (fun c => (8945008641-1+2*2^10*c.k,115496767796086+c.lower,115497157115271+c.upper)) = pointBounds68215 := by
 decide +kernel
def cuts68216 : List PrefixCut := [⟨64,180586627,180586734⟩]
theorem checked68216 : checkPrefixCuts (2^48) 8945139713 10 Manual.Count131072.C068216.packed 64 cuts68216 = true := by
 decide +kernel
def cuts68217 : List PrefixCut := [⟨40,113404153,113404216⟩,
⟨64,181181832,181181935⟩]
theorem checked68217 : checkPrefixCuts (2^48) 8945270785 10 Manual.Count131072.C068217.packed 64 cuts68217 = true := by
 decide +kernel
def pointBounds68217 : List (Nat × Nat × Nat) := [(8945352704,115497240299304,115497629618769)]
theorem point_links_checked68217 : (cuts68217.take 1).map (fun c => (8945270785-1+2*2^10*c.k,115497126895151+c.lower,115497516214553+c.upper)) = pointBounds68217 := by
 decide +kernel
def cuts68218 : List PrefixCut := [⟨64,180707186,180707293⟩]
theorem checked68218 : checkPrefixCuts (2^48) 8945401857 10 Manual.Count131072.C068218.packed 64 cuts68218 = true := by
 decide +kernel
def cuts68219 : List PrefixCut := [⟨49,134041913,134041988⟩,
⟨64,175607189,175607288⟩]
theorem checked68219 : checkPrefixCuts (2^48) 8945532929 10 Manual.Count131072.C068219.packed 64 cuts68219 = true := by
 decide +kernel
def pointBounds68219 : List (Nat × Nat × Nat) := [(8945633280,115497622826082,115498012145769)]
theorem point_links_checked68219 : (cuts68219.take 1).map (fun c => (8945532929-1+2*2^10*c.k,115497488784169+c.lower,115497878103781+c.upper)) = pointBounds68219 := by
 decide +kernel
def cuts68220 : List PrefixCut := [⟨64,184792301,184792412⟩]
theorem checked68220 : checkPrefixCuts (2^48) 8945664001 10 Manual.Count131072.C068220.packed 64 cuts68220 = true := by
 decide +kernel
def cuts68221 : List PrefixCut := [⟨58,163016450,163016544⟩,
⟨64,179283366,179283468⟩]
theorem checked68221 : checkPrefixCuts (2^48) 8945795073 10 Manual.Count131072.C068221.packed 64 cuts68221 = true := by
 decide +kernel
def pointBounds68221 : List (Nat × Nat × Nat) := [(8945913856,115498012200109,115498401520025)]
theorem point_links_checked68221 : (cuts68221.take 1).map (fun c => (8945795073-1+2*2^10*c.k,115497849183659+c.lower,115498238503481+c.upper)) = pointBounds68221 := by
 decide +kernel
def cuts68222 : List PrefixCut := [⟨64,179972943,179973045⟩]
theorem checked68222 : checkPrefixCuts (2^48) 8945926145 10 Manual.Count131072.C068222.packed 64 cuts68222 = true := by
 decide +kernel
def cuts68223 : List PrefixCut := [⟨64,179278110,179278217⟩]
theorem checked68223 : checkPrefixCuts (2^48) 8946057217 10 Manual.Count131072.C068223.packed 64 cuts68223 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000256
