import PlattAssemblyKernel
import PlattCertificates.Count131072.C027232
import PlattCertificates.Count131072.C027233
import PlattCertificates.Count131072.C027234
import PlattCertificates.Count131072.C027235
import PlattCertificates.Count131072.C027236
import PlattCertificates.Count131072.C027237
import PlattCertificates.Count131072.C027238
import PlattCertificates.Count131072.C027239
import PlattCertificates.Count131072.C027240
import PlattCertificates.Count131072.C027241
import PlattCertificates.Count131072.C027242
import PlattCertificates.Count131072.C027243
import PlattCertificates.Count131072.C027244
import PlattCertificates.Count131072.C027245
import PlattCertificates.Count131072.C027246
import PlattCertificates.Count131072.C027247
import PlattCertificates.Count131072.C027248
import PlattCertificates.Count131072.C027249
import PlattCertificates.Count131072.C027250
import PlattCertificates.Count131072.C027251
import PlattCertificates.Count131072.C027252
import PlattCertificates.Count131072.C027253
import PlattCertificates.Count131072.C027254
import PlattCertificates.Count131072.C027255
import PlattCertificates.Count131072.C027256
import PlattCertificates.Count131072.C027257
import PlattCertificates.Count131072.C027258
import PlattCertificates.Count131072.C027259
import PlattCertificates.Count131072.C027260
import PlattCertificates.Count131072.C027261
import PlattCertificates.Count131072.C027262
import PlattCertificates.Count131072.C027263
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000226
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27232 : List PrefixCut := [⟨8,29145619,29145636⟩,
⟨118,434341646,434341890⟩,
⟨128,471678273,471678538⟩]
theorem checked27232 : checkPrefixCuts (2^48) 3573284865 9 Manual.Count131072.C027232.packed 128 cuts27232 = true := by
 decide +kernel
def pointBounds27232 : List (Nat × Nat × Nat) := [(3573293056,103993296460828,103993679090573),(3573405696,103993701656855,103994084286827)]
theorem point_links_checked27232 : (cuts27232.take 2).map (fun c => (3573284865-1+2*2^9*c.k,103993267315209+c.lower,103993649944937+c.upper)) = pointBounds27232 := by
 decide +kernel
def cuts27233 : List PrefixCut := [⟨100,371863788,371863996⟩,
⟨128,473078820,473079086⟩]
theorem checked27233 : checkPrefixCuts (2^48) 3573415937 9 Manual.Count131072.C027233.packed 128 cuts27233 = true := by
 decide +kernel
def pointBounds27233 : List (Nat × Nat × Nat) := [(3573518336,103994110857270,103994493487471)]
theorem point_links_checked27233 : (cuts27233.take 1).map (fun c => (3573415937-1+2*2^9*c.k,103993738993482+c.lower,103994121623475+c.upper)) = pointBounds27233 := by
 decide +kernel
def cuts27234 : List PrefixCut := [⟨82,296472663,296472833⟩,
⟨128,466208826,466209089⟩]
theorem checked27234 : checkPrefixCuts (2^48) 3573547009 9 Manual.Count131072.C027234.packed 128 cuts27234 = true := by
 decide +kernel
def pointBounds27234 : List (Nat × Nat × Nat) := [(3573630976,103994508544965,103994891175394)]
theorem point_links_checked27234 : (cuts27234.take 1).map (fun c => (3573547009-1+2*2^9*c.k,103994212072302+c.lower,103994594702561+c.upper)) = pointBounds27234 := by
 decide +kernel
def cuts27235 : List PrefixCut := [⟨64,239438422,239438556⟩,
⟨128,475170703,475170970⟩]
theorem checked27235 : checkPrefixCuts (2^48) 3573678081 9 Manual.Count131072.C027235.packed 128 cuts27235 = true := by
 decide +kernel
def pointBounds27235 : List (Nat × Nat × Nat) := [(3573743616,103994917719550,103995300350206)]
theorem point_links_checked27235 : (cuts27235.take 1).map (fun c => (3573678081-1+2*2^9*c.k,103994678281128+c.lower,103995060911650+c.upper)) = pointBounds27235 := by
 decide +kernel
def cuts27236 : List PrefixCut := [⟨46,163190611,163190703⟩,
⟨128,462630479,462630741⟩]
theorem checked27236 : checkPrefixCuts (2^48) 3573809153 9 Manual.Count131072.C027236.packed 128 cuts27236 = true := by
 decide +kernel
def pointBounds27236 : List (Nat × Nat × Nat) := [(3573856256,103995316642442,103995699273323)]
theorem point_links_checked27236 : (cuts27236.take 1).map (fun c => (3573809153-1+2*2^9*c.k,103995153451831+c.lower,103995536082620+c.upper)) = pointBounds27236 := by
 decide +kernel
def cuts27237 : List PrefixCut := [⟨28,103093266,103093321⟩,
⟨128,463716154,463716414⟩]
theorem checked27237 : checkPrefixCuts (2^48) 3573940225 9 Manual.Count131072.C027237.packed 128 cuts27237 = true := by
 decide +kernel
def pointBounds27237 : List (Nat × Nat × Nat) := [(3573968896,103995719175576,103996101806682)]
theorem point_links_checked27237 : (cuts27237.take 1).map (fun c => (3573940225-1+2*2^9*c.k,103995616082310+c.lower,103995998713361+c.upper)) = pointBounds27237 := by
 decide +kernel
def cuts27238 : List PrefixCut := [⟨10,35675826,35675846⟩,
⟨120,438892377,438892619⟩,
⟨128,469526864,469527123⟩]
theorem checked27238 : checkPrefixCuts (2^48) 3574071297 9 Manual.Count131072.C027238.packed 128 cuts27238 = true := by
 decide +kernel
def pointBounds27238 : List (Nat × Nat × Nat) := [(3574081536,103996115474290,103996498105621),(3574194176,103996518690841,103996901322394)]
theorem point_links_checked27238 : (cuts27238.take 2).map (fun c => (3574071297-1+2*2^9*c.k,103996079798464+c.lower,103996462429775+c.upper)) = pointBounds27238 := by
 decide +kernel
def cuts27239 : List PrefixCut := [⟨102,374459339,374459548⟩,
⟨128,469903389,469903650⟩]
theorem checked27239 : checkPrefixCuts (2^48) 3574202369 9 Manual.Count131072.C027239.packed 128 cuts27239 = true := by
 decide +kernel
def pointBounds27239 : List (Nat × Nat × Nat) := [(3574306816,103996923784667,103997306416446)]
theorem point_links_checked27239 : (cuts27239.take 1).map (fun c => (3574202369-1+2*2^9*c.k,103996549325328+c.lower,103996931956898+c.upper)) = pointBounds27239 := by
 decide +kernel
def cuts27240 : List PrefixCut := [⟨84,302628490,302628661⟩,
⟨128,465870037,465870295⟩]
theorem checked27240 : checkPrefixCuts (2^48) 3574333441 9 Manual.Count131072.C027240.packed 128 cuts27240 = true := by
 decide +kernel
def pointBounds27240 : List (Nat × Nat × Nat) := [(3574419456,103997321857207,103997704489209)]
theorem point_links_checked27240 : (cuts27240.take 1).map (fun c => (3574333441-1+2*2^9*c.k,103997019228717+c.lower,103997401860548+c.upper)) = pointBounds27240 := by
 decide +kernel
def cuts27241 : List PrefixCut := [⟨66,239858154,239858291⟩,
⟨128,460183417,460183676⟩]
theorem checked27241 : checkPrefixCuts (2^48) 3574464513 9 Manual.Count131072.C027241.packed 128 cuts27241 = true := by
 decide +kernel
def pointBounds27241 : List (Nat × Nat × Nat) := [(3574532096,103997724956908,103998107589134)]
theorem point_links_checked27241 : (cuts27241.take 1).map (fun c => (3574464513-1+2*2^9*c.k,103997485098754+c.lower,103997867730843+c.upper)) = pointBounds27241 := by
 decide +kernel
def cuts27242 : List PrefixCut := [⟨48,175517276,175517374⟩,
⟨128,463079997,463080261⟩]
theorem checked27242 : checkPrefixCuts (2^48) 3574595585 9 Manual.Count131072.C027242.packed 128 cuts27242 = true := by
 decide +kernel
def pointBounds27242 : List (Nat × Nat × Nat) := [(3574644736,103998120799447,103998503431893)]
theorem point_links_checked27242 : (cuts27242.take 1).map (fun c => (3574595585-1+2*2^9*c.k,103997945282171+c.lower,103998327914519+c.upper)) = pointBounds27242 := by
 decide +kernel
def cuts27243 : List PrefixCut := [⟨30,109763446,109763509⟩,
⟨128,469755782,469756047⟩]
theorem checked27243 : checkPrefixCuts (2^48) 3574726657 9 Manual.Count131072.C027243.packed 128 cuts27243 = true := by
 decide +kernel
def pointBounds27243 : List (Nat × Nat × Nat) := [(3574757376,103998518125614,103998900758289)]
theorem point_links_checked27243 : (cuts27243.take 1).map (fun c => (3574726657-1+2*2^9*c.k,103998408362168+c.lower,103998790994780+c.upper)) = pointBounds27243 := by
 decide +kernel
def cuts27244 : List PrefixCut := [⟨12,44801489,44801515⟩,
⟨122,444622179,444622427⟩,
⟨128,465801775,465802034⟩]
theorem checked27244 : checkPrefixCuts (2^48) 3574857729 9 Manual.Count131072.C027244.packed 128 cuts27244 = true := by
 decide +kernel
def pointBounds27244 : List (Nat × Nat × Nat) := [(3574870016,103998922919439,103999305552342),(3574982656,103999322740129,103999705373254)]
theorem point_links_checked27244 : (cuts27244.take 2).map (fun c => (3574857729-1+2*2^9*c.k,103998878117950+c.lower,103999260750827+c.upper)) = pointBounds27244 := by
 decide +kernel
def cuts27245 : List PrefixCut := [⟨104,382407649,382407866⟩,
⟨128,468855229,468855497⟩]
theorem checked27245 : checkPrefixCuts (2^48) 3574988801 9 Manual.Count131072.C027245.packed 128 cuts27245 = true := by
 decide +kernel
def pointBounds27245 : List (Nat × Nat × Nat) := [(3575095296,103999726327374,104000108960727)]
theorem point_links_checked27245 : (cuts27245.take 1).map (fun c => (3574988801-1+2*2^9*c.k,103999343919725+c.lower,103999726552861+c.upper)) = pointBounds27245 := by
 decide +kernel
def cuts27246 : List PrefixCut := [⟨86,320040004,320040186⟩,
⟨128,472774621,472774891⟩]
theorem checked27246 : checkPrefixCuts (2^48) 3575119873 9 Manual.Count131072.C027246.packed 128 cuts27246 = true := by
 decide +kernel
def pointBounds27246 : List (Nat × Nat × Nat) := [(3575207936,104000132814958,104000515448544)]
theorem point_links_checked27246 : (cuts27246.take 1).map (fun c => (3575119873-1+2*2^9*c.k,103999812774954+c.lower,104000195408358+c.upper)) = pointBounds27246 := by
 decide +kernel
def cuts27247 : List PrefixCut := [⟨68,254606193,254606335⟩,
⟨128,469844444,469844705⟩]
theorem checked27247 : checkPrefixCuts (2^48) 3575250945 9 Manual.Count131072.C027247.packed 128 cuts27247 = true := by
 decide +kernel
def pointBounds27247 : List (Nat × Nat × Nat) := [(3575320576,104000540155768,104000922789584)]
theorem point_links_checked27247 : (cuts27247.take 1).map (fun c => (3575250945-1+2*2^9*c.k,104000285549575+c.lower,104000668183249+c.upper)) = pointBounds27247 := by
 decide +kernel
def cuts27248 : List PrefixCut := [⟨50,184138400,184138503⟩,
⟨128,469669688,469669950⟩]
theorem checked27248 : checkPrefixCuts (2^48) 3575382017 9 Manual.Count131072.C027248.packed 128 cuts27248 = true := by
 decide +kernel
def pointBounds27248 : List (Nat × Nat × Nat) := [(3575433216,104000939532419,104001322166457)]
theorem point_links_checked27248 : (cuts27248.take 1).map (fun c => (3575382017-1+2*2^9*c.k,104000755394019+c.lower,104001138027954+c.upper)) = pointBounds27248 := by
 decide +kernel
def cuts27249 : List PrefixCut := [⟨32,114934965,114935031⟩,
⟨128,466346147,466346408⟩]
theorem checked27249 : checkPrefixCuts (2^48) 3575513089 9 Manual.Count131072.C027249.packed 128 cuts27249 = true := by
 decide +kernel
def pointBounds27249 : List (Nat × Nat × Nat) := [(3575545856,104001339998672,104001722632935)]
theorem point_links_checked27249 : (cuts27249.take 1).map (fun c => (3575513089-1+2*2^9*c.k,104001225063707+c.lower,104001607697904+c.upper)) = pointBounds27249 := by
 decide +kernel
def cuts27250 : List PrefixCut := [⟨14,51718971,51719001⟩,
⟨124,458929806,458930065⟩,
⟨128,473964793,473965060⟩]
theorem checked27250 : checkPrefixCuts (2^48) 3575644161 9 Manual.Count131072.C027250.packed 128 cuts27250 = true := by
 decide +kernel
def pointBounds27250 : List (Nat × Nat × Nat) := [(3575658496,104001743128825,104002125763313),(3575771136,104002150339660,104002532974377)]
theorem point_links_checked27250 : (cuts27250.take 2).map (fun c => (3575644161-1+2*2^9*c.k,104001691409854+c.lower,104002074044312+c.upper)) = pointBounds27250 := by
 decide +kernel
def cuts27251 : List PrefixCut := [⟨106,387125211,387125429⟩,
⟨128,466626889,466627151⟩]
theorem checked27251 : checkPrefixCuts (2^48) 3575775233 9 Manual.Count131072.C027251.packed 128 cuts27251 = true := by
 decide +kernel
def pointBounds27251 : List (Nat × Nat × Nat) := [(3575883776,104002552499858,104002935134801)]
theorem point_links_checked27251 : (cuts27251.take 1).map (fun c => (3575775233-1+2*2^9*c.k,104002165374647+c.lower,104002548009372+c.upper)) = pointBounds27251 := by
 decide +kernel
def cuts27252 : List PrefixCut := [⟨88,323118057,323118234⟩,
⟨128,470781490,470781749⟩]
theorem checked27252 : checkPrefixCuts (2^48) 3575906305 9 Manual.Count131072.C027252.packed 128 cuts27252 = true := by
 decide +kernel
def pointBounds27252 : List (Nat × Nat × Nat) := [(3575996416,104002955119593,104003337754757)]
theorem point_links_checked27252 : (cuts27252.take 1).map (fun c => (3575906305-1+2*2^9*c.k,104002632001536+c.lower,104003014636523+c.upper)) = pointBounds27252 := by
 decide +kernel
def cuts27253 : List PrefixCut := [⟨70,253920415,253920557⟩,
⟨128,473518983,473519245⟩]
theorem checked27253 : checkPrefixCuts (2^48) 3576037377 9 Manual.Count131072.C027253.packed 128 cuts27253 = true := by
 decide +kernel
def pointBounds27253 : List (Nat × Nat × Nat) := [(3576109056,104003356703441,104003739338829)]
theorem point_links_checked27253 : (cuts27253.take 1).map (fun c => (3576037377-1+2*2^9*c.k,104003102783026+c.lower,104003485418272+c.upper)) = pointBounds27253 := by
 decide +kernel
def cuts27254 : List PrefixCut := [⟨52,189056439,189056544⟩,
⟨128,469015417,469015677⟩]
theorem checked27254 : checkPrefixCuts (2^48) 3576168449 9 Manual.Count131072.C027254.packed 128 cuts27254 = true := by
 decide +kernel
def pointBounds27254 : List (Nat × Nat × Nat) := [(3576221696,104003765358448,104004147994061)]
theorem point_links_checked27254 : (cuts27254.take 1).map (fun c => (3576168449-1+2*2^9*c.k,104003576302009+c.lower,104003958937517+c.upper)) = pointBounds27254 := by
 decide +kernel
def cuts27255 : List PrefixCut := [⟨34,122229245,122229315⟩,
⟨128,458766735,458766994⟩]
theorem checked27255 : checkPrefixCuts (2^48) 3576299521 9 Manual.Count131072.C027255.packed 128 cuts27255 = true := by
 decide +kernel
def pointBounds27255 : List (Nat × Nat × Nat) := [(3576334336,104004167546671,104004550182509)]
theorem point_links_checked27255 : (cuts27255.take 1).map (fun c => (3576299521-1+2*2^9*c.k,104004045317426+c.lower,104004427953194+c.upper)) = pointBounds27255 := by
 decide +kernel
def cuts27256 : List PrefixCut := [⟨16,58318600,58318632⟩,
⟨126,459537059,459537315⟩,
⟨128,467800546,467800807⟩]
theorem checked27256 : checkPrefixCuts (2^48) 3576430593 9 Manual.Count131072.C027256.packed 128 cuts27256 = true := by
 decide +kernel
def pointBounds27256 : List (Nat × Nat × Nat) := [(3576446976,104004562402761,104004945038820),(3576559616,104004963621220,104005346257503)]
theorem point_links_checked27256 : (cuts27256.take 2).map (fun c => (3576430593-1+2*2^9*c.k,104004504084161+c.lower,104004886720188+c.upper)) = pointBounds27256 := by
 decide +kernel
def cuts27257 : List PrefixCut := [⟨108,393729276,393729496⟩,
⟨128,465737216,465737479⟩]
theorem checked27257 : checkPrefixCuts (2^48) 3576561665 9 Manual.Count131072.C027257.packed 128 cuts27257 = true := by
 decide +kernel
def pointBounds27257 : List (Nat × Nat × Nat) := [(3576672256,104005365613983,104005748250491)]
theorem point_links_checked27257 : (cuts27257.take 1).map (fun c => (3576561665-1+2*2^9*c.k,104004971884707+c.lower,104005354520995+c.upper)) = pointBounds27257 := by
 decide +kernel
def cuts27258 : List PrefixCut := [⟨90,331703449,331703638⟩,
⟨128,468867987,468868253⟩]
theorem checked27258 : checkPrefixCuts (2^48) 3576692737 9 Manual.Count131072.C027258.packed 128 cuts27258 = true := by
 decide +kernel
def pointBounds27258 : List (Nat × Nat × Nat) := [(3576784896,104005769325372,104006151962112)]
theorem point_links_checked27258 : (cuts27258.take 1).map (fun c => (3576692737-1+2*2^9*c.k,104005437621923+c.lower,104005820258474+c.upper)) = pointBounds27258 := by
 decide +kernel
def cuts27259 : List PrefixCut := [⟨72,261419085,261419232⟩,
⟨128,466017882,466018144⟩]
theorem checked27259 : checkPrefixCuts (2^48) 3576823809 9 Manual.Count131072.C027259.packed 128 cuts27259 = true := by
 decide +kernel
def pointBounds27259 : List (Nat × Nat × Nat) := [(3576897536,104006167908995,104006550545959)]
theorem point_links_checked27259 : (cuts27259.take 1).map (fun c => (3576823809-1+2*2^9*c.k,104005906489910+c.lower,104006289126727+c.upper)) = pointBounds27259 := by
 decide +kernel
def cuts27260 : List PrefixCut := [⟨54,197749490,197749603⟩,
⟨128,470250039,470250301⟩]
theorem checked27260 : checkPrefixCuts (2^48) 3576954881 9 Manual.Count131072.C027260.packed 128 cuts27260 = true := by
 decide +kernel
def pointBounds27260 : List (Nat × Nat × Nat) := [(3577010176,104006570257282,104006952894474)]
theorem point_links_checked27260 : (cuts27260.take 1).map (fun c => (3576954881-1+2*2^9*c.k,104006372507792+c.lower,104006755144871+c.upper)) = pointBounds27260 := by
 decide +kernel
def cuts27261 : List PrefixCut := [⟨36,127002299,127002371⟩,
⟨128,462993587,462993849⟩]
theorem checked27261 : checkPrefixCuts (2^48) 3577085953 9 Manual.Count131072.C027261.packed 128 cuts27261 = true := by
 decide +kernel
def pointBounds27261 : List (Nat × Nat × Nat) := [(3577122816,104006969760130,104007352397543)]
theorem point_links_checked27261 : (cuts27261.take 1).map (fun c => (3577085953-1+2*2^9*c.k,104006842757831+c.lower,104007225395172+c.upper)) = pointBounds27261 := by
 decide +kernel
def cuts27262 : List PrefixCut := [⟨18,69400375,69400414⟩,
⟨128,476510302,476510570⟩]
theorem checked27262 : checkPrefixCuts (2^48) 3577217025 9 Manual.Count131072.C027262.packed 128 cuts27262 = true := by
 decide +kernel
def pointBounds27262 : List (Nat × Nat × Nat) := [(3577235456,104007375151793,104007757789435),(3577348096,104007782261720,104008164899591)]
theorem point_links_checked27262 : (cuts27262.take 2).map (fun c => (3577217025-1+2*2^9*c.k,104007305751418+c.lower,104007688389021+c.upper)) = pointBounds27262 := by
 decide +kernel
def cuts27263 : List PrefixCut := [⟨110,411109898,411110125⟩,
⟨128,477673075,477673339⟩]
theorem checked27263 : checkPrefixCuts (2^48) 3577348097 9 Manual.Count131072.C027263.packed 128 cuts27263 = true := by
 decide +kernel
def pointBounds27263 : List (Nat × Nat × Nat) := [(3577460736,104008193371618,104008576009716)]
theorem point_links_checked27263 : (cuts27263.take 1).map (fun c => (3577348097-1+2*2^9*c.k,104007782261720+c.lower,104008164899591+c.upper)) = pointBounds27263 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000226
