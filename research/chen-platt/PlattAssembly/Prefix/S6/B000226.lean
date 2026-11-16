import PlattAssemblyKernel
import PlattCertificates.Count131072.C057232
import PlattCertificates.Count131072.C057233
import PlattCertificates.Count131072.C057234
import PlattCertificates.Count131072.C057235
import PlattCertificates.Count131072.C057236
import PlattCertificates.Count131072.C057237
import PlattCertificates.Count131072.C057238
import PlattCertificates.Count131072.C057239
import PlattCertificates.Count131072.C057240
import PlattCertificates.Count131072.C057241
import PlattCertificates.Count131072.C057242
import PlattCertificates.Count131072.C057243
import PlattCertificates.Count131072.C057244
import PlattCertificates.Count131072.C057245
import PlattCertificates.Count131072.C057246
import PlattCertificates.Count131072.C057247
import PlattCertificates.Count131072.C057248
import PlattCertificates.Count131072.C057249
import PlattCertificates.Count131072.C057250
import PlattCertificates.Count131072.C057251
import PlattCertificates.Count131072.C057252
import PlattCertificates.Count131072.C057253
import PlattCertificates.Count131072.C057254
import PlattCertificates.Count131072.C057255
import PlattCertificates.Count131072.C057256
import PlattCertificates.Count131072.C057257
import PlattCertificates.Count131072.C057258
import PlattCertificates.Count131072.C057259
import PlattCertificates.Count131072.C057260
import PlattCertificates.Count131072.C057261
import PlattCertificates.Count131072.C057262
import PlattCertificates.Count131072.C057263
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000226
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57232 : List PrefixCut := [⟨64,213876373,213876493⟩]
theorem checked57232 : checkPrefixCuts (2^48) 7505444865 10 Manual.Count131072.C057232.packed 64 cuts57232 = true := by
 decide +kernel
def cuts57233 : List PrefixCut := [⟨44,148882469,148882553⟩,
⟨64,217022791,217022915⟩]
theorem checked57233 : checkPrefixCuts (2^48) 7505575937 10 Manual.Count131072.C057233.packed 64 cuts57233 = true := by
 decide +kernel
def pointBounds57233 : List (Nat × Nat × Nat) := [(7505666048,113333470706119,113333858780716)]
theorem point_links_checked57233 : (cuts57233.take 1).map (fun c => (7505575937-1+2*2^10*c.k,113333321823650+c.lower,113333709898163+c.upper)) = pointBounds57233 := by
 decide +kernel
def cuts57234 : List PrefixCut := [⟨64,213456380,213456503⟩]
theorem checked57234 : checkPrefixCuts (2^48) 7505707009 10 Manual.Count131072.C057234.packed 64 cuts57234 = true := by
 decide +kernel
def cuts57235 : List PrefixCut := [⟨31,105864298,105864359⟩,
⟨64,217165215,217165342⟩]
theorem checked57235 : checkPrefixCuts (2^48) 7505838081 10 Manual.Count131072.C057235.packed 64 cuts57235 = true := by
 decide +kernel
def pointBounds57235 : List (Nat × Nat × Nat) := [(7505901568,113333858167119,113334246241940)]
theorem point_links_checked57235 : (cuts57235.take 1).map (fun c => (7505838081-1+2*2^10*c.k,113333752302821+c.lower,113334140377581+c.upper)) = pointBounds57235 := by
 decide +kernel
def cuts57236 : List PrefixCut := [⟨64,216823910,216824029⟩]
theorem checked57236 : checkPrefixCuts (2^48) 7505969153 10 Manual.Count131072.C057236.packed 64 cuts57236 = true := by
 decide +kernel
def cuts57237 : List PrefixCut := [⟨18,60074028,60074063⟩,
⟨64,213332715,213332838⟩]
theorem checked57237 : checkPrefixCuts (2^48) 7506100225 10 Manual.Count131072.C057237.packed 64 cuts57237 = true := by
 decide +kernel
def pointBounds57237 : List (Nat × Nat × Nat) := [(7506137088,113334246365974,113334634441015)]
theorem point_links_checked57237 : (cuts57237.take 1).map (fun c => (7506100225-1+2*2^10*c.k,113334186291946+c.lower,113334574366952+c.upper)) = pointBounds57237 := by
 decide +kernel
def cuts57238 : List PrefixCut := [⟨64,213141520,213141643⟩]
theorem checked57238 : checkPrefixCuts (2^48) 7506231297 10 Manual.Count131072.C057238.packed 64 cuts57238 = true := by
 decide +kernel
def cuts57239 : List PrefixCut := [⟨5,17661628,17661639⟩,
⟨64,220374876,220375002⟩]
theorem checked57239 : checkPrefixCuts (2^48) 7506362369 10 Manual.Count131072.C057239.packed 64 cuts57239 = true := by
 decide +kernel
def pointBounds57239 : List (Nat × Nat × Nat) := [(7506372608,113334630427809,113335018503072)]
theorem point_links_checked57239 : (cuts57239.take 1).map (fun c => (7506362369-1+2*2^10*c.k,113334612766181+c.lower,113335000841433+c.upper)) = pointBounds57239 := by
 decide +kernel
def cuts57240 : List PrefixCut := [⟨56,187973630,187973738⟩,
⟨64,214071478,214071601⟩]
theorem checked57240 : checkPrefixCuts (2^48) 7506493441 10 Manual.Count131072.C057240.packed 64 cuts57240 = true := by
 decide +kernel
def pointBounds57240 : List (Nat × Nat × Nat) := [(7506608128,113335021114687,113335409190173)]
theorem point_links_checked57240 : (cuts57240.take 1).map (fun c => (7506493441-1+2*2^10*c.k,113334833141057+c.lower,113335221216435+c.upper)) = pointBounds57240 := by
 decide +kernel
def cuts57241 : List PrefixCut := [⟨64,218454833,218454958⟩]
theorem checked57241 : checkPrefixCuts (2^48) 7506624513 10 Manual.Count131072.C057241.packed 64 cuts57241 = true := by
 decide +kernel
def cuts57242 : List PrefixCut := [⟨43,144359574,144359658⟩,
⟨64,214926414,214926539⟩]
theorem checked57242 : checkPrefixCuts (2^48) 7506755585 10 Manual.Count131072.C057242.packed 64 cuts57242 = true := by
 decide +kernel
def pointBounds57242 : List (Nat × Nat × Nat) := [(7506843648,113335410026942,113335798102652)]
theorem point_links_checked57242 : (cuts57242.take 1).map (fun c => (7506755585-1+2*2^10*c.k,113335265667368+c.lower,113335653742994+c.upper)) = pointBounds57242 := by
 decide +kernel
def cuts57243 : List PrefixCut := [⟨64,216947406,216947527⟩]
theorem checked57243 : checkPrefixCuts (2^48) 7506886657 10 Manual.Count131072.C057243.packed 64 cuts57243 = true := by
 decide +kernel
def cuts57244 : List PrefixCut := [⟨30,102660625,102660682⟩,
⟨64,217431047,217431171⟩]
theorem checked57244 : checkPrefixCuts (2^48) 7507017729 10 Manual.Count131072.C057244.packed 64 cuts57244 = true := by
 decide +kernel
def pointBounds57244 : List (Nat × Nat × Nat) := [(7507079168,113335800201813,113336188277742)]
theorem point_links_checked57244 : (cuts57244.take 1).map (fun c => (7507017729-1+2*2^10*c.k,113335697541188+c.lower,113336085617060+c.upper)) = pointBounds57244 := by
 decide +kernel
def cuts57245 : List PrefixCut := [⟨64,214315246,214315369⟩]
theorem checked57245 : checkPrefixCuts (2^48) 7507148801 10 Manual.Count131072.C057245.packed 64 cuts57245 = true := by
 decide +kernel
def cuts57246 : List PrefixCut := [⟨17,56765167,56765199⟩,
⟨64,215623763,215623886⟩]
theorem checked57246 : checkPrefixCuts (2^48) 7507279873 10 Manual.Count131072.C057246.packed 64 cuts57246 = true := by
 decide +kernel
def pointBounds57246 : List (Nat × Nat × Nat) := [(7507314688,113336186052648,113336574128799)]
theorem point_links_checked57246 : (cuts57246.take 1).map (fun c => (7507279873-1+2*2^10*c.k,113336129287481+c.lower,113336517363600+c.upper)) = pointBounds57246 := by
 decide +kernel
def cuts57247 : List PrefixCut := [⟨64,214982633,214982755⟩]
theorem checked57247 : checkPrefixCuts (2^48) 7507410945 10 Manual.Count131072.C057247.packed 64 cuts57247 = true := by
 decide +kernel
def cuts57248 : List PrefixCut := [⟨4,13684676,13684684⟩,
⟨64,217453365,217453484⟩]
theorem checked57248 : checkPrefixCuts (2^48) 7507542017 10 Manual.Count131072.C057248.packed 64 cuts57248 = true := by
 decide +kernel
def pointBounds57248 : List (Nat × Nat × Nat) := [(7507550208,113336573578553,113336961654925)]
theorem point_links_checked57248 : (cuts57248.take 1).map (fun c => (7507542017-1+2*2^10*c.k,113336559893877+c.lower,113336947970241+c.upper)) = pointBounds57248 := by
 decide +kernel
def cuts57249 : List PrefixCut := [⟨55,185882105,185882212⟩,
⟨64,216774707,216774833⟩]
theorem checked57249 : checkPrefixCuts (2^48) 7507673089 10 Manual.Count131072.C057249.packed 64 cuts57249 = true := by
 decide +kernel
def pointBounds57249 : List (Nat × Nat × Nat) := [(7507785728,113336963229347,113337351305937)]
theorem point_links_checked57249 : (cuts57249.take 1).map (fun c => (7507673089-1+2*2^10*c.k,113336777347242+c.lower,113337165423725+c.upper)) = pointBounds57249 := by
 decide +kernel
def cuts57250 : List PrefixCut := [⟨64,217220824,217220947⟩]
theorem checked57250 : checkPrefixCuts (2^48) 7507804161 10 Manual.Count131072.C057250.packed 64 cuts57250 = true := by
 decide +kernel
def cuts57251 : List PrefixCut := [⟨42,142199966,142200046⟩,
⟨64,218116770,218116894⟩]
theorem checked57251 : checkPrefixCuts (2^48) 7507935233 10 Manual.Count131072.C057251.packed 64 cuts57251 = true := by
 decide +kernel
def pointBounds57251 : List (Nat × Nat × Nat) := [(7508021248,113337353542739,113337741619551)]
theorem point_links_checked57251 : (cuts57251.take 1).map (fun c => (7507935233-1+2*2^10*c.k,113337211342773+c.lower,113337599419505+c.upper)) = pointBounds57251 := by
 decide +kernel
def cuts57252 : List PrefixCut := [⟨64,217138238,217138355⟩]
theorem checked57252 : checkPrefixCuts (2^48) 7508066305 10 Manual.Count131072.C057252.packed 64 cuts57252 = true := by
 decide +kernel
def cuts57253 : List PrefixCut := [⟨29,96683778,96683834⟩,
⟨64,215672386,215672510⟩]
theorem checked57253 : checkPrefixCuts (2^48) 7508197377 10 Manual.Count131072.C057253.packed 64 cuts57253 = true := by
 decide +kernel
def pointBounds57253 : List (Nat × Nat × Nat) := [(7508256768,113337743281559,113338131358588)]
theorem point_links_checked57253 : (cuts57253.take 1).map (fun c => (7508197377-1+2*2^10*c.k,113337646597781+c.lower,113338034674754+c.upper)) = pointBounds57253 := by
 decide +kernel
def cuts57254 : List PrefixCut := [⟨64,217018199,217018321⟩]
theorem checked57254 : checkPrefixCuts (2^48) 7508328449 10 Manual.Count131072.C057254.packed 64 cuts57254 = true := by
 decide +kernel
def cuts57255 : List PrefixCut := [⟨16,53569808,53569839⟩,
⟨64,211916129,211916253⟩]
theorem checked57255 : checkPrefixCuts (2^48) 7508459521 10 Manual.Count131072.C057255.packed 64 cuts57255 = true := by
 decide +kernel
def pointBounds57255 : List (Nat × Nat × Nat) := [(7508492288,113338132858174,113338520935424)]
theorem point_links_checked57255 : (cuts57255.take 1).map (fun c => (7508459521-1+2*2^10*c.k,113338079288366+c.lower,113338467365585+c.upper)) = pointBounds57255 := by
 decide +kernel
def cuts57256 : List PrefixCut := [⟨64,216223422,216223545⟩]
theorem checked57256 : checkPrefixCuts (2^48) 7508590593 10 Manual.Count131072.C057256.packed 64 cuts57256 = true := by
 decide +kernel
def cuts57257 : List PrefixCut := [⟨3,10046350,10046355⟩,
⟨64,217306727,217306849⟩]
theorem checked57257 : checkPrefixCuts (2^48) 7508721665 10 Manual.Count131072.C057257.packed 64 cuts57257 = true := by
 decide +kernel
def pointBounds57257 : List (Nat × Nat × Nat) := [(7508727808,113338517474267,113338905551738)]
theorem point_links_checked57257 : (cuts57257.take 1).map (fun c => (7508721665-1+2*2^10*c.k,113338507427917+c.lower,113338895505383+c.upper)) = pointBounds57257 := by
 decide +kernel
def cuts57258 : List PrefixCut := [⟨54,180979802,180979908⟩,
⟨64,216328286,216328412⟩]
theorem checked57258 : checkPrefixCuts (2^48) 7508852737 10 Manual.Count131072.C057258.packed 64 cuts57258 = true := by
 decide +kernel
def pointBounds57258 : List (Nat × Nat × Nat) := [(7508963328,113338905714446,113339293792140)]
theorem point_links_checked57258 : (cuts57258.take 1).map (fun c => (7508852737-1+2*2^10*c.k,113338724734644+c.lower,113339112812232+c.upper)) = pointBounds57258 := by
 decide +kernel
def cuts57259 : List PrefixCut := [⟨64,215274948,215275072⟩]
theorem checked57259 : checkPrefixCuts (2^48) 7508983809 10 Manual.Count131072.C057259.packed 64 cuts57259 = true := by
 decide +kernel
def cuts57260 : List PrefixCut := [⟨41,136854890,136854971⟩,
⟨64,215008806,215008930⟩]
theorem checked57260 : checkPrefixCuts (2^48) 7509114881 10 Manual.Count131072.C057260.packed 64 cuts57260 = true := by
 decide +kernel
def pointBounds57260 : List (Nat × Nat × Nat) := [(7509198848,113339293192768,113339681270687)]
theorem point_links_checked57260 : (cuts57260.take 1).map (fun c => (7509114881-1+2*2^10*c.k,113339156337878+c.lower,113339544415716+c.upper)) = pointBounds57260 := by
 decide +kernel
def cuts57261 : List PrefixCut := [⟨64,216691827,216691949⟩]
theorem checked57261 : checkPrefixCuts (2^48) 7509245953 10 Manual.Count131072.C057261.packed 64 cuts57261 = true := by
 decide +kernel
def cuts57262 : List PrefixCut := [⟨28,94232207,94232262⟩,
⟨64,215638510,215638635⟩]
theorem checked57262 : checkPrefixCuts (2^48) 7509377025 10 Manual.Count131072.C057262.packed 64 cuts57262 = true := by
 decide +kernel
def pointBounds57262 : List (Nat × Nat × Nat) := [(7509434368,113339682270718,113340070348857)]
theorem point_links_checked57262 : (cuts57262.take 1).map (fun c => (7509377025-1+2*2^10*c.k,113339588038511+c.lower,113339976116595+c.upper)) = pointBounds57262 := by
 decide +kernel
def cuts57263 : List PrefixCut := [⟨64,215147494,215147621⟩]
theorem checked57263 : checkPrefixCuts (2^48) 7509508097 10 Manual.Count131072.C057263.packed 64 cuts57263 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000226
