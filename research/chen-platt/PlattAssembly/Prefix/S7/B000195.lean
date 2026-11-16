import PlattAssemblyKernel
import PlattCertificates.Count131072.C066240
import PlattCertificates.Count131072.C066241
import PlattCertificates.Count131072.C066242
import PlattCertificates.Count131072.C066243
import PlattCertificates.Count131072.C066244
import PlattCertificates.Count131072.C066245
import PlattCertificates.Count131072.C066246
import PlattCertificates.Count131072.C066247
import PlattCertificates.Count131072.C066248
import PlattCertificates.Count131072.C066249
import PlattCertificates.Count131072.C066250
import PlattCertificates.Count131072.C066251
import PlattCertificates.Count131072.C066252
import PlattCertificates.Count131072.C066253
import PlattCertificates.Count131072.C066254
import PlattCertificates.Count131072.C066255
import PlattCertificates.Count131072.C066256
import PlattCertificates.Count131072.C066257
import PlattCertificates.Count131072.C066258
import PlattCertificates.Count131072.C066259
import PlattCertificates.Count131072.C066260
import PlattCertificates.Count131072.C066261
import PlattCertificates.Count131072.C066262
import PlattCertificates.Count131072.C066263
import PlattCertificates.Count131072.C066264
import PlattCertificates.Count131072.C066265
import PlattCertificates.Count131072.C066266
import PlattCertificates.Count131072.C066267
import PlattCertificates.Count131072.C066268
import PlattCertificates.Count131072.C066269
import PlattCertificates.Count131072.C066270
import PlattCertificates.Count131072.C066271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000195
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66240 : List PrefixCut := [⟨64,185549950,185550063⟩]
theorem checked66240 : checkPrefixCuts (2^48) 8686141441 10 Manual.Count131072.C066240.packed 64 cuts66240 = true := by
 decide +kernel
def cuts66241 : List PrefixCut := [⟨5,14387620,14387627⟩,
⟨64,185611958,185612063⟩]
theorem checked66241 : checkPrefixCuts (2^48) 8686272513 10 Manual.Count131072.C066241.packed 64 cuts66241 = true := by
 decide +kernel
def pointBounds66241 : List (Nat × Nat × Nat) := [(8686282752,115136000192554,115136389301424)]
theorem point_links_checked66241 : (cuts66241.take 1).map (fun c => (8686272513-1+2*2^10*c.k,115135985804934+c.lower,115136374913797+c.upper)) = pointBounds66241 := by
 decide +kernel
def cuts66242 : List PrefixCut := [⟨64,184215787,184215896⟩]
theorem checked66242 : checkPrefixCuts (2^48) 8686403585 10 Manual.Count131072.C066242.packed 64 cuts66242 = true := by
 decide +kernel
def cuts66243 : List PrefixCut := [⟨10,29584443,29584460⟩,
⟨64,186610871,186610978⟩]
theorem checked66243 : checkPrefixCuts (2^48) 8686534657 10 Manual.Count131072.C066243.packed 64 cuts66243 = true := by
 decide +kernel
def pointBounds66243 : List (Nat × Nat × Nat) := [(8686555136,115136385217122,115136774326216)]
theorem point_links_checked66243 : (cuts66243.take 1).map (fun c => (8686534657-1+2*2^10*c.k,115136355632679+c.lower,115136744741756+c.upper)) = pointBounds66243 := by
 decide +kernel
def cuts66244 : List PrefixCut := [⟨64,186348824,186348929⟩]
theorem checked66244 : checkPrefixCuts (2^48) 8686665729 10 Manual.Count131072.C066244.packed 64 cuts66244 = true := by
 decide +kernel
def cuts66245 : List PrefixCut := [⟨15,42674162,42674188⟩,
⟨64,186540417,186540524⟩]
theorem checked66245 : checkPrefixCuts (2^48) 8686796801 10 Manual.Count131072.C066245.packed 64 cuts66245 = true := by
 decide +kernel
def pointBounds66245 : List (Nat × Nat × Nat) := [(8686827520,115136771266536,115137160375851)]
theorem point_links_checked66245 : (cuts66245.take 1).map (fun c => (8686796801-1+2*2^10*c.k,115136728592374+c.lower,115137117701663+c.upper)) = pointBounds66245 := by
 decide +kernel
def cuts66246 : List PrefixCut := [⟨64,186570012,186570125⟩]
theorem checked66246 : checkPrefixCuts (2^48) 8686927873 10 Manual.Count131072.C066246.packed 64 cuts66246 = true := by
 decide +kernel
def cuts66247 : List PrefixCut := [⟨20,57123945,57123981⟩,
⟨64,184687903,184688020⟩]
theorem checked66247 : checkPrefixCuts (2^48) 8687058945 10 Manual.Count131072.C066247.packed 64 cuts66247 = true := by
 decide +kernel
def pointBounds66247 : List (Nat × Nat × Nat) := [(8687099904,115137158826748,115137547936293)]
theorem point_links_checked66247 : (cuts66247.take 1).map (fun c => (8687058945-1+2*2^10*c.k,115137101702803+c.lower,115137490812312+c.upper)) = pointBounds66247 := by
 decide +kernel
def cuts66248 : List PrefixCut := [⟨64,184620338,184620447⟩]
theorem checked66248 : checkPrefixCuts (2^48) 8687190017 10 Manual.Count131072.C066248.packed 64 cuts66248 = true := by
 decide +kernel
def cuts66249 : List PrefixCut := [⟨25,72447652,72447697⟩,
⟨64,187598375,187598491⟩]
theorem checked66249 : checkPrefixCuts (2^48) 8687321089 10 Manual.Count131072.C066249.packed 64 cuts66249 = true := by
 decide +kernel
def pointBounds66249 : List (Nat × Nat × Nat) := [(8687372288,115137543458696,115137932568476)]
theorem point_links_checked66249 : (cuts66249.take 1).map (fun c => (8687321089-1+2*2^10*c.k,115137471011044+c.lower,115137860120779+c.upper)) = pointBounds66249 := by
 decide +kernel
def cuts66250 : List PrefixCut := [⟨64,185392360,185392465⟩]
theorem checked66250 : checkPrefixCuts (2^48) 8687452161 10 Manual.Count131072.C066250.packed 64 cuts66250 = true := by
 decide +kernel
def cuts66251 : List PrefixCut := [⟨30,87381624,87381676⟩,
⟨64,187884317,187884427⟩]
theorem checked66251 : checkPrefixCuts (2^48) 8687583233 10 Manual.Count131072.C066251.packed 64 cuts66251 = true := by
 decide +kernel
def pointBounds66251 : List (Nat × Nat × Nat) := [(8687644672,115137931383403,115138320493411)]
theorem point_links_checked66251 : (cuts66251.take 1).map (fun c => (8687583233-1+2*2^10*c.k,115137844001779+c.lower,115138233111735+c.upper)) = pointBounds66251 := by
 decide +kernel
def cuts66252 : List PrefixCut := [⟨64,189080243,189080351⟩]
theorem checked66252 : checkPrefixCuts (2^48) 8687714305 10 Manual.Count131072.C066252.packed 64 cuts66252 = true := by
 decide +kernel
def cuts66253 : List PrefixCut := [⟨35,100338362,100338420⟩,
⟨64,183342863,183342969⟩]
theorem checked66253 : checkPrefixCuts (2^48) 8687845377 10 Manual.Count131072.C066253.packed 64 cuts66253 = true := by
 decide +kernel
def pointBounds66253 : List (Nat × Nat × Nat) := [(8687917056,115138321304701,115138710414933)]
theorem point_links_checked66253 : (cuts66253.take 1).map (fun c => (8687845377-1+2*2^10*c.k,115138220966339+c.lower,115138610076513+c.upper)) = pointBounds66253 := by
 decide +kernel
def cuts66254 : List PrefixCut := [⟨64,186029115,186029223⟩]
theorem checked66254 : checkPrefixCuts (2^48) 8687976449 10 Manual.Count131072.C066254.packed 64 cuts66254 = true := by
 decide +kernel
def cuts66255 : List PrefixCut := [⟨40,116987626,116987688⟩,
⟨64,185119199,185119301⟩]
theorem checked66255 : checkPrefixCuts (2^48) 8688107521 10 Manual.Count131072.C066255.packed 64 cuts66255 = true := by
 decide +kernel
def pointBounds66255 : List (Nat × Nat × Nat) := [(8688189440,115138707325943,115139096436393)]
theorem point_links_checked66255 : (cuts66255.take 1).map (fun c => (8688107521-1+2*2^10*c.k,115138590338317+c.lower,115138979448705+c.upper)) = pointBounds66255 := by
 decide +kernel
def cuts66256 : List PrefixCut := [⟨64,187934931,187935041⟩]
theorem checked66256 : checkPrefixCuts (2^48) 8688238593 10 Manual.Count131072.C066256.packed 64 cuts66256 = true := by
 decide +kernel
def cuts66257 : List PrefixCut := [⟨45,130072242,130072320⟩,
⟨64,185016417,185016527⟩]
theorem checked66257 : checkPrefixCuts (2^48) 8688369665 10 Manual.Count131072.C066257.packed 64 cuts66257 = true := by
 decide +kernel
def pointBounds66257 : List (Nat × Nat × Nat) := [(8688461824,115139093464689,115139482575367)]
theorem point_links_checked66257 : (cuts66257.take 1).map (fun c => (8688369665-1+2*2^10*c.k,115138963392447+c.lower,115139352503047+c.upper)) = pointBounds66257 := by
 decide +kernel
def cuts66258 : List PrefixCut := [⟨64,185629149,185629257⟩]
theorem checked66258 : checkPrefixCuts (2^48) 8688500737 10 Manual.Count131072.C066258.packed 64 cuts66258 = true := by
 decide +kernel
def cuts66259 : List PrefixCut := [⟨50,145456135,145456216⟩,
⟨64,185399577,185399682⟩]
theorem checked66259 : checkPrefixCuts (2^48) 8688631809 10 Manual.Count131072.C066259.packed 64 cuts66259 = true := by
 decide +kernel
def pointBounds66259 : List (Nat × Nat × Nat) := [(8688734208,115139479494148,115139868605047)]
theorem point_links_checked66259 : (cuts66259.take 1).map (fun c => (8688631809-1+2*2^10*c.k,115139334038013+c.lower,115139723148831+c.upper)) = pointBounds66259 := by
 decide +kernel
def cuts66260 : List PrefixCut := [⟨64,185170023,185170132⟩]
theorem checked66260 : checkPrefixCuts (2^48) 8688762881 10 Manual.Count131072.C066260.packed 64 cuts66260 = true := by
 decide +kernel
def cuts66261 : List PrefixCut := [⟨55,159640482,159640575⟩,
⟨64,186398202,186398311⟩]
theorem checked66261 : checkPrefixCuts (2^48) 8688893953 10 Manual.Count131072.C066261.packed 64 cuts66261 = true := by
 decide +kernel
def pointBounds66261 : List (Nat × Nat × Nat) := [(8689006592,115139864248095,115140253359220)]
theorem point_links_checked66261 : (cuts66261.take 1).map (fun c => (8688893953-1+2*2^10*c.k,115139704607613+c.lower,115140093718645+c.upper)) = pointBounds66261 := by
 decide +kernel
def cuts66262 : List PrefixCut := [⟨64,186913709,186913818⟩]
theorem checked66262 : checkPrefixCuts (2^48) 8689025025 10 Manual.Count131072.C066262.packed 64 cuts66262 = true := by
 decide +kernel
def cuts66263 : List PrefixCut := [⟨60,173823968,173824074⟩,
⟨64,186101045,186101156⟩]
theorem checked66263 : checkPrefixCuts (2^48) 8689156097 10 Manual.Count131072.C066263.packed 64 cuts66263 = true := by
 decide +kernel
def pointBounds66263 : List (Nat × Nat × Nat) := [(8689278976,115140251743492,115140640854848)]
theorem point_links_checked66263 : (cuts66263.take 1).map (fun c => (8689156097-1+2*2^10*c.k,115140077919524+c.lower,115140467030774+c.upper)) = pointBounds66263 := by
 decide +kernel
def cuts66264 : List PrefixCut := [⟨64,182243464,182243566⟩]
theorem checked66264 : checkPrefixCuts (2^48) 8689287169 10 Manual.Count131072.C066264.packed 64 cuts66264 = true := by
 decide +kernel
def cuts66265 : List PrefixCut := [⟨64,185544754,185544865⟩]
theorem checked66265 : checkPrefixCuts (2^48) 8689418241 10 Manual.Count131072.C066265.packed 64 cuts66265 = true := by
 decide +kernel
def cuts66266 : List PrefixCut := [⟨1,2947703,2947705⟩,
⟨64,184829342,184829448⟩]
theorem checked66266 : checkPrefixCuts (2^48) 8689549313 10 Manual.Count131072.C066266.packed 64 cuts66266 = true := by
 decide +kernel
def pointBounds66266 : List (Nat × Nat × Nat) := [(8689551360,115140634756490,115141023868066)]
theorem point_links_checked66266 : (cuts66266.take 1).map (fun c => (8689549313-1+2*2^10*c.k,115140631808787+c.lower,115141020920361+c.upper)) = pointBounds66266 := by
 decide +kernel
def cuts66267 : List PrefixCut := [⟨64,181781755,181781858⟩]
theorem checked66267 : checkPrefixCuts (2^48) 8689680385 10 Manual.Count131072.C066267.packed 64 cuts66267 = true := by
 decide +kernel
def cuts66268 : List PrefixCut := [⟨6,16422412,16422422⟩,
⟨64,185763091,185763199⟩]
theorem checked66268 : checkPrefixCuts (2^48) 8689811457 10 Manual.Count131072.C066268.packed 64 cuts66268 = true := by
 decide +kernel
def pointBounds66268 : List (Nat × Nat × Nat) := [(8689823744,115141014842296,115141403954089)]
theorem point_links_checked66268 : (cuts66268.take 1).map (fun c => (8689811457-1+2*2^10*c.k,115140998419884+c.lower,115141387531667+c.upper)) = pointBounds66268 := by
 decide +kernel
def cuts66269 : List PrefixCut := [⟨64,186310936,186311044⟩]
theorem checked66269 : checkPrefixCuts (2^48) 8689942529 10 Manual.Count131072.C066269.packed 64 cuts66269 = true := by
 decide +kernel
def cuts66270 : List PrefixCut := [⟨11,32066445,32066465⟩,
⟨64,182712829,182712940⟩]
theorem checked66270 : checkPrefixCuts (2^48) 8690073601 10 Manual.Count131072.C066270.packed 64 cuts66270 = true := by
 decide +kernel
def pointBounds66270 : List (Nat × Nat × Nat) := [(8690096128,115141402560356,115141791672375)]
theorem point_links_checked66270 : (cuts66270.take 1).map (fun c => (8690073601-1+2*2^10*c.k,115141370493911+c.lower,115141759605910+c.upper)) = pointBounds66270 := by
 decide +kernel
def cuts66271 : List PrefixCut := [⟨64,185074524,185074632⟩]
theorem checked66271 : checkPrefixCuts (2^48) 8690204673 10 Manual.Count131072.C066271.packed 64 cuts66271 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000195
