import PlattAssemblyKernel
import PlattCertificates.Count131072.C067232
import PlattCertificates.Count131072.C067233
import PlattCertificates.Count131072.C067234
import PlattCertificates.Count131072.C067235
import PlattCertificates.Count131072.C067236
import PlattCertificates.Count131072.C067237
import PlattCertificates.Count131072.C067238
import PlattCertificates.Count131072.C067239
import PlattCertificates.Count131072.C067240
import PlattCertificates.Count131072.C067241
import PlattCertificates.Count131072.C067242
import PlattCertificates.Count131072.C067243
import PlattCertificates.Count131072.C067244
import PlattCertificates.Count131072.C067245
import PlattCertificates.Count131072.C067246
import PlattCertificates.Count131072.C067247
import PlattCertificates.Count131072.C067248
import PlattCertificates.Count131072.C067249
import PlattCertificates.Count131072.C067250
import PlattCertificates.Count131072.C067251
import PlattCertificates.Count131072.C067252
import PlattCertificates.Count131072.C067253
import PlattCertificates.Count131072.C067254
import PlattCertificates.Count131072.C067255
import PlattCertificates.Count131072.C067256
import PlattCertificates.Count131072.C067257
import PlattCertificates.Count131072.C067258
import PlattCertificates.Count131072.C067259
import PlattCertificates.Count131072.C067260
import PlattCertificates.Count131072.C067261
import PlattCertificates.Count131072.C067262
import PlattCertificates.Count131072.C067263
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000226
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67232 : List PrefixCut := [⟨64,184537476,184537582⟩]
theorem checked67232 : checkPrefixCuts (2^48) 8816164865 10 Manual.Count131072.C067232.packed 64 cuts67232 = true := by
 decide +kernel
def cuts67233 : List PrefixCut := [⟨46,130898610,130898693⟩,
⟨64,182587216,182587326⟩]
theorem checked67233 : checkPrefixCuts (2^48) 8816295937 10 Manual.Count131072.C067233.packed 64 cuts67233 = true := by
 decide +kernel
def pointBounds67233 : List (Nat × Nat × Nat) := [(8816390144,115318806267138,115319195482408)]
theorem point_links_checked67233 : (cuts67233.take 1).map (fun c => (8816295937-1+2*2^10*c.k,115318675368528+c.lower,115319064583715+c.upper)) = pointBounds67233 := by
 decide +kernel
def cuts67234 : List PrefixCut := [⟨64,183669991,183670089⟩]
theorem checked67234 : checkPrefixCuts (2^48) 8816427009 10 Manual.Count131072.C067234.packed 64 cuts67234 = true := by
 decide +kernel
def cuts67235 : List PrefixCut := [⟨53,150241471,150241560⟩,
⟨64,182581779,182581886⟩]
theorem checked67235 : checkPrefixCuts (2^48) 8816558081 10 Manual.Count131072.C067235.packed 64 cuts67235 = true := by
 decide +kernel
def pointBounds67235 : List (Nat × Nat × Nat) := [(8816666624,115319191867206,115319581082690)]
theorem point_links_checked67235 : (cuts67235.take 1).map (fun c => (8816558081-1+2*2^10*c.k,115319041625735+c.lower,115319430841130+c.upper)) = pointBounds67235 := by
 decide +kernel
def cuts67236 : List PrefixCut := [⟨64,182132122,182132231⟩]
theorem checked67236 : checkPrefixCuts (2^48) 8816689153 10 Manual.Count131072.C067236.packed 64 cuts67236 = true := by
 decide +kernel
def cuts67237 : List PrefixCut := [⟨60,172360582,172360684⟩,
⟨64,183566012,183566121⟩]
theorem checked67237 : checkPrefixCuts (2^48) 8816820225 10 Manual.Count131072.C067237.packed 64 cuts67237 = true := by
 decide +kernel
def pointBounds67237 : List (Nat × Nat × Nat) := [(8816943104,115319578700218,115319967915931)]
theorem point_links_checked67237 : (cuts67237.take 1).map (fun c => (8816820225-1+2*2^10*c.k,115319406339636+c.lower,115319795555247+c.upper)) = pointBounds67237 := by
 decide +kernel
def cuts67238 : List PrefixCut := [⟨64,180466672,180466779⟩]
theorem checked67238 : checkPrefixCuts (2^48) 8816951297 10 Manual.Count131072.C067238.packed 64 cuts67238 = true := by
 decide +kernel
def cuts67239 : List PrefixCut := [⟨64,181645148,181645253⟩]
theorem checked67239 : checkPrefixCuts (2^48) 8817082369 10 Manual.Count131072.C067239.packed 64 cuts67239 = true := by
 decide +kernel
def cuts67240 : List PrefixCut := [⟨3,8076602,8076607⟩,
⟨64,183908979,183909088⟩]
theorem checked67240 : checkPrefixCuts (2^48) 8817213441 10 Manual.Count131072.C067240.packed 64 cuts67240 = true := by
 decide +kernel
def pointBounds67240 : List (Nat × Nat × Nat) := [(8817219584,115319960094070,115320349310007)]
theorem point_links_checked67240 : (cuts67240.take 1).map (fun c => (8817213441-1+2*2^10*c.k,115319952017468+c.lower,115320341233400+c.upper)) = pointBounds67240 := by
 decide +kernel
def cuts67241 : List PrefixCut := [⟨64,184385097,184385208⟩]
theorem checked67241 : checkPrefixCuts (2^48) 8817344513 10 Manual.Count131072.C067241.packed 64 cuts67241 = true := by
 decide +kernel
def cuts67242 : List PrefixCut := [⟨10,28538584,28538600⟩,
⟨64,181573211,181573309⟩]
theorem checked67242 : checkPrefixCuts (2^48) 8817475585 10 Manual.Count131072.C067242.packed 64 cuts67242 = true := by
 decide +kernel
def pointBounds67242 : List (Nat × Nat × Nat) := [(8817496064,115320348850128,115320738066296)]
theorem point_links_checked67242 : (cuts67242.take 1).map (fun c => (8817475585-1+2*2^10*c.k,115320320311544+c.lower,115320709527696+c.upper)) = pointBounds67242 := by
 decide +kernel
def cuts67243 : List PrefixCut := [⟨64,182432381,182432489⟩]
theorem checked67243 : checkPrefixCuts (2^48) 8817606657 10 Manual.Count131072.C067243.packed 64 cuts67243 = true := by
 decide +kernel
def cuts67244 : List PrefixCut := [⟨17,49063158,49063187⟩,
⟨64,182812745,182812851⟩]
theorem checked67244 : checkPrefixCuts (2^48) 8817737729 10 Manual.Count131072.C067244.packed 64 cuts67244 = true := by
 decide +kernel
def pointBounds67244 : List (Nat × Nat × Nat) := [(8817772544,115320733380294,115321122596681)]
theorem point_links_checked67244 : (cuts67244.take 1).map (fun c => (8817737729-1+2*2^10*c.k,115320684317136+c.lower,115321073533494+c.upper)) = pointBounds67244 := by
 decide +kernel
def cuts67245 : List PrefixCut := [⟨64,183193070,183193173⟩]
theorem checked67245 : checkPrefixCuts (2^48) 8817868801 10 Manual.Count131072.C067245.packed 64 cuts67245 = true := by
 decide +kernel
def cuts67246 : List PrefixCut := [⟨24,69394955,69394994⟩,
⟨64,184562910,184563016⟩]
theorem checked67246 : checkPrefixCuts (2^48) 8817999873 10 Manual.Count131072.C067246.packed 64 cuts67246 = true := by
 decide +kernel
def pointBounds67246 : List (Nat × Nat × Nat) := [(8818049024,115321119717906,115321508934512)]
theorem point_links_checked67246 : (cuts67246.take 1).map (fun c => (8817999873-1+2*2^10*c.k,115321050322951+c.lower,115321439539518+c.upper)) = pointBounds67246 := by
 decide +kernel
def cuts67247 : List PrefixCut := [⟨64,182644981,182645088⟩]
theorem checked67247 : checkPrefixCuts (2^48) 8818130945 10 Manual.Count131072.C067247.packed 64 cuts67247 = true := by
 decide +kernel
def cuts67248 : List PrefixCut := [⟨31,88512577,88512626⟩,
⟨64,183567924,183568031⟩]
theorem checked67248 : checkPrefixCuts (2^48) 8818262017 10 Manual.Count131072.C067248.packed 64 cuts67248 = true := by
 decide +kernel
def pointBounds67248 : List (Nat × Nat × Nat) := [(8818325504,115321506043419,115321895260248)]
theorem point_links_checked67248 : (cuts67248.take 1).map (fun c => (8818262017-1+2*2^10*c.k,115321417530842+c.lower,115321806747622+c.upper)) = pointBounds67248 := by
 decide +kernel
def cuts67249 : List PrefixCut := [⟨64,183788620,183788729⟩]
theorem checked67249 : checkPrefixCuts (2^48) 8818393089 10 Manual.Count131072.C067249.packed 64 cuts67249 = true := by
 decide +kernel
def cuts67250 : List PrefixCut := [⟨38,107437516,107437575⟩,
⟨64,181870797,181870900⟩]
theorem checked67250 : checkPrefixCuts (2^48) 8818524161 10 Manual.Count131072.C067250.packed 64 cuts67250 = true := by
 decide +kernel
def pointBounds67250 : List (Nat × Nat × Nat) := [(8818601984,115321892324902,115322281541957)]
theorem point_links_checked67250 : (cuts67250.take 1).map (fun c => (8818524161-1+2*2^10*c.k,115321784887386+c.lower,115322174104382+c.upper)) = pointBounds67250 := by
 decide +kernel
def cuts67251 : List PrefixCut := [⟨64,183400152,183400259⟩]
theorem checked67251 : checkPrefixCuts (2^48) 8818655233 10 Manual.Count131072.C067251.packed 64 cuts67251 = true := by
 decide +kernel
def cuts67252 : List PrefixCut := [⟨45,129042366,129042443⟩,
⟨64,183620851,183620957⟩]
theorem checked67252 : checkPrefixCuts (2^48) 8818786305 10 Manual.Count131072.C067252.packed 64 cuts67252 = true := by
 decide +kernel
def pointBounds67252 : List (Nat × Nat × Nat) := [(8818878464,115322279200701,115322668417984)]
theorem point_links_checked67252 : (cuts67252.take 1).map (fun c => (8818786305-1+2*2^10*c.k,115322150158335+c.lower,115322539375541+c.upper)) = pointBounds67252 := by
 decide +kernel
def cuts67253 : List PrefixCut := [⟨64,182181862,182181964⟩]
theorem checked67253 : checkPrefixCuts (2^48) 8818917377 10 Manual.Count131072.C067253.packed 64 cuts67253 = true := by
 decide +kernel
def cuts67254 : List PrefixCut := [⟨52,144390273,144390356⟩,
⟨64,177774687,177774791⟩]
theorem checked67254 : checkPrefixCuts (2^48) 8819048449 10 Manual.Count131072.C067254.packed 64 cuts67254 = true := by
 decide +kernel
def pointBounds67254 : List (Nat × Nat × Nat) := [(8819154944,115322660351321,115323049568818)]
theorem point_links_checked67254 : (cuts67254.take 1).map (fun c => (8819048449-1+2*2^10*c.k,115322515961048+c.lower,115322905178462+c.upper)) = pointBounds67254 := by
 decide +kernel
def cuts67255 : List PrefixCut := [⟨64,183293516,183293621⟩]
theorem checked67255 : checkPrefixCuts (2^48) 8819179521 10 Manual.Count131072.C067255.packed 64 cuts67255 = true := by
 decide +kernel
def cuts67256 : List PrefixCut := [⟨59,168801229,168801325⟩,
⟨64,183386517,183386622⟩]
theorem checked67256 : checkPrefixCuts (2^48) 8819310593 10 Manual.Count131072.C067256.packed 64 cuts67256 = true := by
 decide +kernel
def pointBounds67256 : List (Nat × Nat × Nat) := [(8819431424,115323045830480,115323435048199)]
theorem point_links_checked67256 : (cuts67256.take 1).map (fun c => (8819310593-1+2*2^10*c.k,115322877029251+c.lower,115323266246874+c.upper)) = pointBounds67256 := by
 decide +kernel
def cuts67257 : List PrefixCut := [⟨64,184660394,184660502⟩]
theorem checked67257 : checkPrefixCuts (2^48) 8819441665 10 Manual.Count131072.C067257.packed 64 cuts67257 = true := by
 decide +kernel
def cuts67258 : List PrefixCut := [⟨64,182742786,182742889⟩]
theorem checked67258 : checkPrefixCuts (2^48) 8819572737 10 Manual.Count131072.C067258.packed 64 cuts67258 = true := by
 decide +kernel
def cuts67259 : List PrefixCut := [⟨2,5840321,5840323⟩,
⟨64,182899629,182899730⟩]
theorem checked67259 : checkPrefixCuts (2^48) 8819703809 10 Manual.Count131072.C067259.packed 64 cuts67259 = true := by
 decide +kernel
def pointBounds67259 : List (Nat × Nat × Nat) := [(8819707904,115323433659269,115323822877210)]
theorem point_links_checked67259 : (cuts67259.take 1).map (fun c => (8819703809-1+2*2^10*c.k,115323427818948+c.lower,115323817036887+c.upper)) = pointBounds67259 := by
 decide +kernel
def cuts67260 : List PrefixCut := [⟨64,183630937,183631045⟩]
theorem checked67260 : checkPrefixCuts (2^48) 8819834881 10 Manual.Count131072.C067260.packed 64 cuts67260 = true := by
 decide +kernel
def cuts67261 : List PrefixCut := [⟨9,25275368,25275385⟩,
⟨64,183692039,183692145⟩]
theorem checked67261 : checkPrefixCuts (2^48) 8819965953 10 Manual.Count131072.C067261.packed 64 cuts67261 = true := by
 decide +kernel
def pointBounds67261 : List (Nat × Nat × Nat) := [(8819984384,115323819624882,115324208843047)]
theorem point_links_checked67261 : (cuts67261.take 1).map (fun c => (8819965953-1+2*2^10*c.k,115323794349514+c.lower,115324183567662+c.upper)) = pointBounds67261 := by
 decide +kernel
def cuts67262 : List PrefixCut := [⟨64,183721215,183721321⟩]
theorem checked67262 : checkPrefixCuts (2^48) 8820097025 10 Manual.Count131072.C067262.packed 64 cuts67262 = true := by
 decide +kernel
def cuts67263 : List PrefixCut := [⟨16,45124090,45124113⟩,
⟨64,184133335,184133439⟩]
theorem checked67263 : checkPrefixCuts (2^48) 8820228097 10 Manual.Count131072.C067263.packed 64 cuts67263 = true := by
 decide +kernel
def pointBounds67263 : List (Nat × Nat × Nat) := [(8820260864,115324206886858,115324596105241)]
theorem point_links_checked67263 : (cuts67263.take 1).map (fun c => (8820228097-1+2*2^10*c.k,115324161762768+c.lower,115324550981128+c.upper)) = pointBounds67263 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000226
