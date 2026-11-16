import PlattAssemblyKernel
import PlattCertificates.Count131072.C058224
import PlattCertificates.Count131072.C058225
import PlattCertificates.Count131072.C058226
import PlattCertificates.Count131072.C058227
import PlattCertificates.Count131072.C058228
import PlattCertificates.Count131072.C058229
import PlattCertificates.Count131072.C058230
import PlattCertificates.Count131072.C058231
import PlattCertificates.Count131072.C058232
import PlattCertificates.Count131072.C058233
import PlattCertificates.Count131072.C058234
import PlattCertificates.Count131072.C058235
import PlattCertificates.Count131072.C058236
import PlattCertificates.Count131072.C058237
import PlattCertificates.Count131072.C058238
import PlattCertificates.Count131072.C058239
import PlattCertificates.Count131072.C058240
import PlattCertificates.Count131072.C058241
import PlattCertificates.Count131072.C058242
import PlattCertificates.Count131072.C058243
import PlattCertificates.Count131072.C058244
import PlattCertificates.Count131072.C058245
import PlattCertificates.Count131072.C058246
import PlattCertificates.Count131072.C058247
import PlattCertificates.Count131072.C058248
import PlattCertificates.Count131072.C058249
import PlattCertificates.Count131072.C058250
import PlattCertificates.Count131072.C058251
import PlattCertificates.Count131072.C058252
import PlattCertificates.Count131072.C058253
import PlattCertificates.Count131072.C058254
import PlattCertificates.Count131072.C058255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000257
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58224 : List PrefixCut := [⟨64,216206268,216206387⟩]
theorem checked58224 : checkPrefixCuts (2^48) 7635468289 10 Manual.Count131072.C058224.packed 64 cuts58224 = true := by
 decide +kernel
def cuts58225 : List PrefixCut := [⟨15,48844035,48844064⟩,
⟨64,212442503,212442628⟩]
theorem checked58225 : checkPrefixCuts (2^48) 7635599361 10 Manual.Count131072.C058225.packed 64 cuts58225 = true := by
 decide +kernel
def pointBounds58225 : List (Nat × Nat × Nat) := [(7635630080,113545844352709,113546232548291)]
theorem point_links_checked58225 : (cuts58225.take 1).map (fun c => (7635599361-1+2*2^10*c.k,113545795508674+c.lower,113546183704227+c.upper)) = pointBounds58225 := by
 decide +kernel
def cuts58226 : List PrefixCut := [⟨64,213139236,213139357⟩]
theorem checked58226 : checkPrefixCuts (2^48) 7635730433 10 Manual.Count131072.C058226.packed 64 cuts58226 = true := by
 decide +kernel
def cuts58227 : List PrefixCut := [⟨4,13417845,13417853⟩,
⟨64,211181919,211182042⟩]
theorem checked58227 : checkPrefixCuts (2^48) 7635861505 10 Manual.Count131072.C058227.packed 64 cuts58227 = true := by
 decide +kernel
def pointBounds58227 : List (Nat × Nat × Nat) := [(7635869696,113546234508258,113546622704065)]
theorem point_links_checked58227 : (cuts58227.take 1).map (fun c => (7635861505-1+2*2^10*c.k,113546221090413+c.lower,113546609286212+c.upper)) = pointBounds58227 := by
 decide +kernel
def cuts58228 : List PrefixCut := [⟨57,187034320,187034428⟩,
⟨64,209961863,209961983⟩]
theorem checked58228 : checkPrefixCuts (2^48) 7635992577 10 Manual.Count131072.C058228.packed 64 cuts58228 = true := by
 decide +kernel
def pointBounds58228 : List (Nat × Nat × Nat) := [(7636109312,113546619306652,113547007502682)]
theorem point_links_checked58228 : (cuts58228.take 1).map (fun c => (7635992577-1+2*2^10*c.k,113546432272332+c.lower,113546820468254+c.upper)) = pointBounds58228 := by
 decide +kernel
def cuts58229 : List PrefixCut := [⟨64,212022459,212022582⟩]
theorem checked58229 : checkPrefixCuts (2^48) 7636123649 10 Manual.Count131072.C058229.packed 64 cuts58229 = true := by
 decide +kernel
def cuts58230 : List PrefixCut := [⟨46,151347595,151347683⟩,
⟨64,213014024,213014147⟩]
theorem checked58230 : checkPrefixCuts (2^48) 7636254721 10 Manual.Count131072.C058230.packed 64 cuts58230 = true := by
 decide +kernel
def pointBounds58230 : List (Nat × Nat × Nat) := [(7636348928,113547005604249,113547393800502)]
theorem point_links_checked58230 : (cuts58230.take 1).map (fun c => (7636254721-1+2*2^10*c.k,113546854256654+c.lower,113547242452819+c.upper)) = pointBounds58230 := by
 decide +kernel
def cuts58231 : List PrefixCut := [⟨64,212162622,212162741⟩]
theorem checked58231 : checkPrefixCuts (2^48) 7636385793 10 Manual.Count131072.C058231.packed 64 cuts58231 = true := by
 decide +kernel
def cuts58232 : List PrefixCut := [⟨35,116326682,116326748⟩,
⟨64,210500349,210500469⟩]
theorem checked58232 : checkPrefixCuts (2^48) 7636516865 10 Manual.Count131072.C058232.packed 64 cuts58232 = true := by
 decide +kernel
def pointBounds58232 : List (Nat × Nat × Nat) := [(7636588544,113547395759982,113547783956455)]
theorem point_links_checked58232 : (cuts58232.take 1).map (fun c => (7636516865-1+2*2^10*c.k,113547279433300+c.lower,113547667629707+c.upper)) = pointBounds58232 := by
 decide +kernel
def cuts58233 : List PrefixCut := [⟨64,209980705,209980819⟩]
theorem checked58233 : checkPrefixCuts (2^48) 7636647937 10 Manual.Count131072.C058233.packed 64 cuts58233 = true := by
 decide +kernel
def cuts58234 : List PrefixCut := [⟨24,80128607,80128653⟩,
⟨64,211598847,211598969⟩]
theorem checked58234 : checkPrefixCuts (2^48) 7636779009 10 Manual.Count131072.C058234.packed 64 cuts58234 = true := by
 decide +kernel
def pointBounds58234 : List (Nat × Nat × Nat) := [(7636828160,113547780042961,113548168239648)]
theorem point_links_checked58234 : (cuts58234.take 1).map (fun c => (7636779009-1+2*2^10*c.k,113547699914354+c.lower,113548088110995+c.upper)) = pointBounds58234 := by
 decide +kernel
def cuts58235 : List PrefixCut := [⟨64,215465168,215465290⟩]
theorem checked58235 : checkPrefixCuts (2^48) 7636910081 10 Manual.Count131072.C058235.packed 64 cuts58235 = true := by
 decide +kernel
def cuts58236 : List PrefixCut := [⟨13,43269500,43269524⟩,
⟨64,213213243,213213363⟩]
theorem checked58236 : checkPrefixCuts (2^48) 7637041153 10 Manual.Count131072.C058236.packed 64 cuts58236 = true := by
 decide +kernel
def pointBounds58236 : List (Nat × Nat × Nat) := [(7637067776,113548170247869,113548558444778)]
theorem point_links_checked58236 : (cuts58236.take 1).map (fun c => (7637041153-1+2*2^10*c.k,113548126978369+c.lower,113548515175254+c.upper)) = pointBounds58236 := by
 decide +kernel
def cuts58237 : List PrefixCut := [⟨64,211219386,211219507⟩]
theorem checked58237 : checkPrefixCuts (2^48) 7637172225 10 Manual.Count131072.C058237.packed 64 cuts58237 = true := by
 decide +kernel
def cuts58238 : List PrefixCut := [⟨2,7223631,7223635⟩,
⟨64,213390192,213390315⟩]
theorem checked58238 : checkPrefixCuts (2^48) 7637303297 10 Manual.Count131072.C058238.packed 64 cuts58238 = true := by
 decide +kernel
def pointBounds58238 : List (Nat × Nat × Nat) := [(7637307392,113548558634629,113548946831759)]
theorem point_links_checked58238 : (cuts58238.take 1).map (fun c => (7637303297-1+2*2^10*c.k,113548551410998+c.lower,113548939608124+c.upper)) = pointBounds58238 := by
 decide +kernel
def cuts58239 : List PrefixCut := [⟨55,184603527,184603633⟩,
⟨64,214013061,214013184⟩]
theorem checked58239 : checkPrefixCuts (2^48) 7637434369 10 Manual.Count131072.C058239.packed 64 cuts58239 = true := by
 decide +kernel
def pointBounds58239 : List (Nat × Nat × Nat) := [(7637547008,113548949404717,113549337602072)]
theorem point_links_checked58239 : (cuts58239.take 1).map (fun c => (7637434369-1+2*2^10*c.k,113548764801190+c.lower,113549152998439+c.upper)) = pointBounds58239 := by
 decide +kernel
def cuts58240 : List PrefixCut := [⟨64,210766256,210766378⟩]
theorem checked58240 : checkPrefixCuts (2^48) 7637565441 10 Manual.Count131072.C058240.packed 64 cuts58240 = true := by
 decide +kernel
def cuts58241 : List PrefixCut := [⟨44,144943480,144943563⟩,
⟨64,212384181,212384302⟩]
theorem checked58241 : checkPrefixCuts (2^48) 7637696513 10 Manual.Count131072.C058241.packed 64 cuts58241 = true := by
 decide +kernel
def pointBounds58241 : List (Nat × Nat × Nat) := [(7637786624,113549334523987,113549722721564)]
theorem point_links_checked58241 : (cuts58241.take 1).map (fun c => (7637696513-1+2*2^10*c.k,113549189580507+c.lower,113549577778001+c.upper)) = pointBounds58241 := by
 decide +kernel
def cuts58242 : List PrefixCut := [⟨64,210832739,210832857⟩]
theorem checked58242 : checkPrefixCuts (2^48) 7637827585 10 Manual.Count131072.C058242.packed 64 cuts58242 = true := by
 decide +kernel
def cuts58243 : List PrefixCut := [⟨33,110224173,110224233⟩,
⟨64,214403733,214403849⟩]
theorem checked58243 : checkPrefixCuts (2^48) 7637958657 10 Manual.Count131072.C058243.packed 64 cuts58243 = true := by
 decide +kernel
def pointBounds58243 : List (Nat × Nat × Nat) := [(7638026240,113549723021600,113550111219393)]
theorem point_links_checked58243 : (cuts58243.take 1).map (fun c => (7637958657-1+2*2^10*c.k,113549612797427+c.lower,113550000995160+c.upper)) = pointBounds58243 := by
 decide +kernel
def cuts58244 : List PrefixCut := [⟨64,211783628,211783750⟩]
theorem checked58244 : checkPrefixCuts (2^48) 7638089729 10 Manual.Count131072.C058244.packed 64 cuts58244 = true := by
 decide +kernel
def cuts58245 : List PrefixCut := [⟨22,71748385,71748424⟩,
⟨64,213364562,213364678⟩]
theorem checked58245 : checkPrefixCuts (2^48) 7638220801 10 Manual.Count131072.C058245.packed 64 cuts58245 = true := by
 decide +kernel
def pointBounds58245 : List (Nat × Nat × Nat) := [(7638265856,113550110733173,113550498931183)]
theorem point_links_checked58245 : (cuts58245.take 1).map (fun c => (7638220801-1+2*2^10*c.k,113550038984788+c.lower,113550427182759+c.upper)) = pointBounds58245 := by
 decide +kernel
def cuts58246 : List PrefixCut := [⟨64,209860159,209860281⟩]
theorem checked58246 : checkPrefixCuts (2^48) 7638351873 10 Manual.Count131072.C058246.packed 64 cuts58246 = true := by
 decide +kernel
def cuts58247 : List PrefixCut := [⟨11,36738977,36738997⟩,
⟨64,213578322,213578445⟩]
theorem checked58247 : checkPrefixCuts (2^48) 7638482945 10 Manual.Count131072.C058247.packed 64 cuts58247 = true := by
 decide +kernel
def pointBounds58247 : List (Nat × Nat × Nat) := [(7638505472,113550498948486,113550887146715)]
theorem point_links_checked58247 : (cuts58247.take 1).map (fun c => (7638482945-1+2*2^10*c.k,113550462209509+c.lower,113550850407718+c.upper)) = pointBounds58247 := by
 decide +kernel
def cuts58248 : List PrefixCut := [⟨64,212174432,212174552⟩]
theorem checked58248 : checkPrefixCuts (2^48) 7638614017 10 Manual.Count131072.C058248.packed 64 cuts58248 = true := by
 decide +kernel
def pointBounds58248 : List (Nat × Nat × Nat) := [(7638745088,113550887962263,113551276160715)]
theorem point_links_checked58248 : (cuts58248.take 1).map (fun c => (7638614017-1+2*2^10*c.k,113550675787831+c.lower,113551063986163+c.upper)) = pointBounds58248 := by
 decide +kernel
def cuts58249 : List PrefixCut := [⟨64,208264924,208265045⟩]
theorem checked58249 : checkPrefixCuts (2^48) 7638745089 10 Manual.Count131072.C058249.packed 64 cuts58249 = true := by
 decide +kernel
def cuts58250 : List PrefixCut := [⟨53,175467428,175467528⟩,
⟨64,212167145,212167266⟩]
theorem checked58250 : checkPrefixCuts (2^48) 7638876161 10 Manual.Count131072.C058250.packed 64 cuts58250 = true := by
 decide +kernel
def pointBounds58250 : List (Nat × Nat × Nat) := [(7638984704,113551271694615,113551659893288)]
theorem point_links_checked58250 : (cuts58250.take 1).map (fun c => (7638876161-1+2*2^10*c.k,113551096227187+c.lower,113551484425760+c.upper)) = pointBounds58250 := by
 decide +kernel
def cuts58251 : List PrefixCut := [⟨64,211058107,211058225⟩]
theorem checked58251 : checkPrefixCuts (2^48) 7639007233 10 Manual.Count131072.C058251.packed 64 cuts58251 = true := by
 decide +kernel
def cuts58252 : List PrefixCut := [⟨42,137399535,137399611⟩,
⟨64,211275557,211275675⟩]
theorem checked58252 : checkPrefixCuts (2^48) 7639138305 10 Manual.Count131072.C058252.packed 64 cuts58252 = true := by
 decide +kernel
def pointBounds58252 : List (Nat × Nat × Nat) := [(7639224320,113551656851974,113552045050862)]
theorem point_links_checked58252 : (cuts58252.take 1).map (fun c => (7639138305-1+2*2^10*c.k,113551519452439+c.lower,113551907651251+c.upper)) = pointBounds58252 := by
 decide +kernel
def cuts58253 : List PrefixCut := [⟨64,209540209,209540325⟩]
theorem checked58253 : checkPrefixCuts (2^48) 7639269377 10 Manual.Count131072.C058253.packed 64 cuts58253 = true := by
 decide +kernel
def cuts58254 : List PrefixCut := [⟨31,104087133,104087191⟩,
⟨64,214105367,214105487⟩]
theorem checked58254 : checkPrefixCuts (2^48) 7639400449 10 Manual.Count131072.C058254.packed 64 cuts58254 = true := by
 decide +kernel
def pointBounds58254 : List (Nat × Nat × Nat) := [(7639463936,113552044355338,113552432554442)]
theorem point_links_checked58254 : (cuts58254.take 1).map (fun c => (7639400449-1+2*2^10*c.k,113551940268205+c.lower,113552328467251+c.upper)) = pointBounds58254 := by
 decide +kernel
def cuts58255 : List PrefixCut := [⟨64,210785724,210785843⟩]
theorem checked58255 : checkPrefixCuts (2^48) 7639531521 10 Manual.Count131072.C058255.packed 64 cuts58255 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000257
