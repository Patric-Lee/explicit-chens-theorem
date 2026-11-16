import PlattAssemblyKernel
import PlattCertificates.Count131072.C076240
import PlattCertificates.Count131072.C076241
import PlattCertificates.Count131072.C076242
import PlattCertificates.Count131072.C076243
import PlattCertificates.Count131072.C076244
import PlattCertificates.Count131072.C076245
import PlattCertificates.Count131072.C076246
import PlattCertificates.Count131072.C076247
import PlattCertificates.Count131072.C076248
import PlattCertificates.Count131072.C076249
import PlattCertificates.Count131072.C076250
import PlattCertificates.Count131072.C076251
import PlattCertificates.Count131072.C076252
import PlattCertificates.Count131072.C076253
import PlattCertificates.Count131072.C076254
import PlattCertificates.Count131072.C076255
import PlattCertificates.Count131072.C076256
import PlattCertificates.Count131072.C076257
import PlattCertificates.Count131072.C076258
import PlattCertificates.Count131072.C076259
import PlattCertificates.Count131072.C076260
import PlattCertificates.Count131072.C076261
import PlattCertificates.Count131072.C076262
import PlattCertificates.Count131072.C076263
import PlattCertificates.Count131072.C076264
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000195
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts76240 : List PrefixCut := [⟨64,158997730,158997829⟩]
theorem checked76240 : checkPrefixCuts (2^48) 9996861441 10 Manual.Count131072.C076240.packed 64 cuts76240 = true := by
 decide +kernel
def cuts76241 : List PrefixCut := [⟨60,151590753,151590842⟩,
⟨64,162233569,162233666⟩]
theorem checked76241 : checkPrefixCuts (2^48) 9996992513 10 Manual.Count131072.C076241.packed 64 cuts76241 = true := by
 decide +kernel
def pointBounds76241 : List (Nat × Nat × Nat) := [(9997115392,116859488142022,116859878270228)]
theorem point_links_checked76241 : (cuts76241.take 1).map (fun c => (9996992513-1+2*2^10*c.k,116859336551269+c.lower,116859726679386+c.upper)) = pointBounds76241 := by
 decide +kernel
def cuts76242 : List PrefixCut := [⟨64,160147932,160148030⟩]
theorem checked76242 : checkPrefixCuts (2^48) 9997123585 10 Manual.Count131072.C076242.packed 64 cuts76242 = true := by
 decide +kernel
def cuts76243 : List PrefixCut := [⟨64,161046798,161046895⟩]
theorem checked76243 : checkPrefixCuts (2^48) 9997254657 10 Manual.Count131072.C076243.packed 64 cuts76243 = true := by
 decide +kernel
def cuts76244 : List PrefixCut := [⟨21,52452372,52452404⟩,
⟨64,160284517,160284612⟩]
theorem checked76244 : checkPrefixCuts (2^48) 9997385729 10 Manual.Count131072.C076244.packed 64 cuts76244 = true := by
 decide +kernel
def pointBounds76244 : List (Nat × Nat × Nat) := [(9997428736,116859872431940,116860262560381)]
theorem point_links_checked76244 : (cuts76244.take 1).map (fun c => (9997385729-1+2*2^10*c.k,116859819979568+c.lower,116860210107977+c.upper)) = pointBounds76244 := by
 decide +kernel
def cuts76245 : List PrefixCut := [⟨64,162703663,162703761⟩]
theorem checked76245 : checkPrefixCuts (2^48) 9997516801 10 Manual.Count131072.C076245.packed 64 cuts76245 = true := by
 decide +kernel
def cuts76246 : List PrefixCut := [⟨46,115262391,115262463⟩,
⟨64,160195846,160195947⟩]
theorem checked76246 : checkPrefixCuts (2^48) 9997647873 10 Manual.Count131072.C076246.packed 64 cuts76246 = true := by
 decide +kernel
def pointBounds76246 : List (Nat × Nat × Nat) := [(9997742080,116860258230139,116860648358813)]
theorem point_links_checked76246 : (cuts76246.take 1).map (fun c => (9997647873-1+2*2^10*c.k,116860142967748+c.lower,116860533096350+c.upper)) = pointBounds76246 := by
 decide +kernel
def cuts76247 : List PrefixCut := [⟨64,159940369,159940461⟩]
theorem checked76247 : checkPrefixCuts (2^48) 9997778945 10 Manual.Count131072.C076247.packed 64 cuts76247 = true := by
 decide +kernel
def cuts76248 : List PrefixCut := [⟨64,158417998,158418094⟩]
theorem checked76248 : checkPrefixCuts (2^48) 9997910017 10 Manual.Count131072.C076248.packed 64 cuts76248 = true := by
 decide +kernel
def cuts76249 : List PrefixCut := [⟨7,16497649,16497659⟩,
⟨64,156783042,156783140⟩]
theorem checked76249 : checkPrefixCuts (2^48) 9998041089 10 Manual.Count131072.C076249.packed 64 cuts76249 = true := by
 decide +kernel
def pointBounds76249 : List (Nat × Nat × Nat) := [(9998055424,116860638019610,116861028148511)]
theorem point_links_checked76249 : (cuts76249.take 1).map (fun c => (9998041089-1+2*2^10*c.k,116860621521961+c.lower,116861011650852+c.upper)) = pointBounds76249 := by
 decide +kernel
def cuts76250 : List PrefixCut := [⟨64,161454308,161454403⟩]
theorem checked76250 : checkPrefixCuts (2^48) 9998172161 10 Manual.Count131072.C076250.packed 64 cuts76250 = true := by
 decide +kernel
def cuts76251 : List PrefixCut := [⟨32,81190871,81190918⟩,
⟨64,160410568,160410663⟩]
theorem checked76251 : checkPrefixCuts (2^48) 9998303233 10 Manual.Count131072.C076251.packed 64 cuts76251 = true := by
 decide +kernel
def pointBounds76251 : List (Nat × Nat × Nat) := [(9998368768,116861020950182,116861411079313)]
theorem point_links_checked76251 : (cuts76251.take 1).map (fun c => (9998303233-1+2*2^10*c.k,116860939759311+c.lower,116861329888395+c.upper)) = pointBounds76251 := by
 decide +kernel
def cuts76252 : List PrefixCut := [⟨64,160239542,160239642⟩]
theorem checked76252 : checkPrefixCuts (2^48) 9998434305 10 Manual.Count131072.C076252.packed 64 cuts76252 = true := by
 decide +kernel
def cuts76253 : List PrefixCut := [⟨57,143740858,143740941⟩,
⟨64,160659717,160659809⟩]
theorem checked76253 : checkPrefixCuts (2^48) 9998565377 10 Manual.Count131072.C076253.packed 64 cuts76253 = true := by
 decide +kernel
def pointBounds76253 : List (Nat × Nat × Nat) := [(9998682112,116861404150279,116861794279641)]
theorem point_links_checked76253 : (cuts76253.take 1).map (fun c => (9998565377-1+2*2^10*c.k,116861260409421+c.lower,116861650538700+c.upper)) = pointBounds76253 := by
 decide +kernel
def cuts76254 : List PrefixCut := [⟨64,159418963,159419062⟩]
theorem checked76254 : checkPrefixCuts (2^48) 9998696449 10 Manual.Count131072.C076254.packed 64 cuts76254 = true := by
 decide +kernel
def cuts76255 : List PrefixCut := [⟨64,159135373,159135468⟩]
theorem checked76255 : checkPrefixCuts (2^48) 9998827521 10 Manual.Count131072.C076255.packed 64 cuts76255 = true := by
 decide +kernel
def cuts76256 : List PrefixCut := [⟨18,43801973,43802002⟩,
⟨64,157556865,157556973⟩]
theorem checked76256 : checkPrefixCuts (2^48) 9998958593 10 Manual.Count131072.C076256.packed 64 cuts76256 = true := by
 decide +kernel
def pointBounds76256 : List (Nat × Nat × Nat) := [(9998995456,116861783425447,116862173555041)]
theorem point_links_checked76256 : (cuts76256.take 1).map (fun c => (9998958593-1+2*2^10*c.k,116861739623474+c.lower,116862129753039+c.upper)) = pointBounds76256 := by
 decide +kernel
def cuts76257 : List PrefixCut := [⟨64,163353671,163353772⟩]
theorem checked76257 : checkPrefixCuts (2^48) 9999089665 10 Manual.Count131072.C076257.packed 64 cuts76257 = true := by
 decide +kernel
def cuts76258 : List PrefixCut := [⟨43,108798049,108798109⟩,
⟨64,161381084,161381172⟩]
theorem checked76258 : checkPrefixCuts (2^48) 9999220737 10 Manual.Count131072.C076258.packed 64 cuts76258 = true := by
 decide +kernel
def pointBounds76258 : List (Nat × Nat × Nat) := [(9999308800,116862169332059,116862559461893)]
theorem point_links_checked76258 : (cuts76258.take 1).map (fun c => (9999220737-1+2*2^10*c.k,116862060534010+c.lower,116862450663784+c.upper)) = pointBounds76258 := by
 decide +kernel
def cuts76259 : List PrefixCut := [⟨64,159661848,159661942⟩]
theorem checked76259 : checkPrefixCuts (2^48) 9999351809 10 Manual.Count131072.C076259.packed 64 cuts76259 = true := by
 decide +kernel
def cuts76260 : List PrefixCut := [⟨64,162221307,162221400⟩]
theorem checked76260 : checkPrefixCuts (2^48) 9999482881 10 Manual.Count131072.C076260.packed 64 cuts76260 = true := by
 decide +kernel
def cuts76261 : List PrefixCut := [⟨4,9457917,9457924⟩,
⟨64,157940615,157940713⟩]
theorem checked76261 : checkPrefixCuts (2^48) 9999613953 10 Manual.Count131072.C076261.packed 64 cuts76261 = true := by
 decide +kernel
def pointBounds76261 : List (Nat × Nat × Nat) := [(9999622144,116862553256166,116862943386222)]
theorem point_links_checked76261 : (cuts76261.take 1).map (fun c => (9999613953-1+2*2^10*c.k,116862543798249+c.lower,116862933928298+c.upper)) = pointBounds76261 := by
 decide +kernel
def cuts76262 : List PrefixCut := [⟨64,159683733,159683826⟩]
theorem checked76262 : checkPrefixCuts (2^48) 9999745025 10 Manual.Count131072.C076262.packed 64 cuts76262 = true := by
 decide +kernel
def cuts76263 : List PrefixCut := [⟨29,71945660,71945706⟩,
⟨60,149126331,149126424⟩]
theorem checked76263 : checkPrefixCuts (2^48) 9999876097 10 Manual.Count131072.C076263.packed 60 cuts76263 = true := by
 decide +kernel
def pointBounds76263 : List (Nat × Nat × Nat) := [(9999935488,116862933368257,116863323498543)]
theorem point_links_checked76263 : (cuts76263.take 1).map (fun c => (9999876097-1+2*2^10*c.k,116862861422597+c.lower,116863251552837+c.upper)) = pointBounds76263 := by
 decide +kernel
def cuts76264 : List PrefixCut := [⟨1,1154047,1154048⟩]
theorem checked76264 : checkPrefixCuts (2^48) 9999998977 9 Manual.Count131072.C076264.packed 1 cuts76264 = true := by
 decide +kernel
def pointBounds76264 : List (Nat × Nat × Nat) := [(10000000000,116863011702975,116863401833309)]
theorem point_links_checked76264 : (cuts76264.take 1).map (fun c => (9999998977-1+2*2^9*c.k,116863010548928+c.lower,116863400679261+c.upper)) = pointBounds76264 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000195
