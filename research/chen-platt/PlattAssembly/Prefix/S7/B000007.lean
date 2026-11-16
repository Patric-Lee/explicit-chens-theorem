import PlattAssemblyKernel
import PlattCertificates.Count131072.C060224
import PlattCertificates.Count131072.C060225
import PlattCertificates.Count131072.C060226
import PlattCertificates.Count131072.C060227
import PlattCertificates.Count131072.C060228
import PlattCertificates.Count131072.C060229
import PlattCertificates.Count131072.C060230
import PlattCertificates.Count131072.C060231
import PlattCertificates.Count131072.C060232
import PlattCertificates.Count131072.C060233
import PlattCertificates.Count131072.C060234
import PlattCertificates.Count131072.C060235
import PlattCertificates.Count131072.C060236
import PlattCertificates.Count131072.C060237
import PlattCertificates.Count131072.C060238
import PlattCertificates.Count131072.C060239
import PlattCertificates.Count131072.C060240
import PlattCertificates.Count131072.C060241
import PlattCertificates.Count131072.C060242
import PlattCertificates.Count131072.C060243
import PlattCertificates.Count131072.C060244
import PlattCertificates.Count131072.C060245
import PlattCertificates.Count131072.C060246
import PlattCertificates.Count131072.C060247
import PlattCertificates.Count131072.C060248
import PlattCertificates.Count131072.C060249
import PlattCertificates.Count131072.C060250
import PlattCertificates.Count131072.C060251
import PlattCertificates.Count131072.C060252
import PlattCertificates.Count131072.C060253
import PlattCertificates.Count131072.C060254
import PlattCertificates.Count131072.C060255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60224 : List PrefixCut := [⟨64,202864102,202864217⟩]
theorem checked60224 : checkPrefixCuts (2^48) 7897612289 10 Manual.Count131072.C060224.packed 64 cuts60224 = true := by
 decide +kernel
def cuts60225 : List PrefixCut := [⟨54,173565167,173565270⟩,
⟨64,205284204,205284327⟩]
theorem checked60225 : checkPrefixCuts (2^48) 7897743361 10 Manual.Count131072.C060225.packed 64 cuts60225 = true := by
 decide +kernel
def pointBounds60225 : List (Nat × Nat × Nat) := [(7897853952,113963160406355,113963548840058)]
theorem point_links_checked60225 : (cuts60225.take 1).map (fun c => (7897743361-1+2*2^10*c.k,113962986841188+c.lower,113963375274788+c.upper)) = pointBounds60225 := by
 decide +kernel
def cuts60226 : List PrefixCut := [⟨64,204995674,204995790⟩]
theorem checked60226 : checkPrefixCuts (2^48) 7897874433 10 Manual.Count131072.C060226.packed 64 cuts60226 = true := by
 decide +kernel
def cuts60227 : List PrefixCut := [⟨47,153209972,153210055⟩,
⟨64,207593893,207594007⟩]
theorem checked60227 : checkPrefixCuts (2^48) 7898005505 10 Manual.Count131072.C060227.packed 64 cuts60227 = true := by
 decide +kernel
def pointBounds60227 : List (Nat × Nat × Nat) := [(7898101760,113963550331038,113963938764960)]
theorem point_links_checked60227 : (cuts60227.take 1).map (fun c => (7898005505-1+2*2^10*c.k,113963397121066+c.lower,113963785554905+c.upper)) = pointBounds60227 := by
 decide +kernel
def cuts60228 : List PrefixCut := [⟨64,202921893,202922012⟩]
theorem checked60228 : checkPrefixCuts (2^48) 7898136577 10 Manual.Count131072.C060228.packed 64 cuts60228 = true := by
 decide +kernel
def cuts60229 : List PrefixCut := [⟨40,127688690,127688762⟩,
⟨64,204629120,204629235⟩]
theorem checked60229 : checkPrefixCuts (2^48) 7898267649 10 Manual.Count131072.C060229.packed 64 cuts60229 = true := by
 decide +kernel
def pointBounds60229 : List (Nat × Nat × Nat) := [(7898349568,113963935325542,113964323759686)]
theorem point_links_checked60229 : (cuts60229.take 1).map (fun c => (7898267649-1+2*2^10*c.k,113963807636852+c.lower,113964196070924+c.upper)) = pointBounds60229 := by
 decide +kernel
def cuts60230 : List PrefixCut := [⟨64,204233723,204233835⟩]
theorem checked60230 : checkPrefixCuts (2^48) 7898398721 10 Manual.Count131072.C060230.packed 64 cuts60230 = true := by
 decide +kernel
def cuts60231 : List PrefixCut := [⟨33,107158095,107158152⟩,
⟨64,205014323,205014434⟩]
theorem checked60231 : checkPrefixCuts (2^48) 7898529793 10 Manual.Count131072.C060231.packed 64 cuts60231 = true := by
 decide +kernel
def pointBounds60231 : List (Nat × Nat × Nat) := [(7898597376,113964323657790,113964712092146)]
theorem point_links_checked60231 : (cuts60231.take 1).map (fun c => (7898529793-1+2*2^10*c.k,113964216499695+c.lower,113964604933994+c.upper)) = pointBounds60231 := by
 decide +kernel
def cuts60232 : List PrefixCut := [⟨64,206258129,206258245⟩]
theorem checked60232 : checkPrefixCuts (2^48) 7898660865 10 Manual.Count131072.C060232.packed 64 cuts60232 = true := by
 decide +kernel
def cuts60233 : List PrefixCut := [⟨26,84989623,84989672⟩,
⟨64,204544263,204544381⟩]
theorem checked60233 : checkPrefixCuts (2^48) 7898791937 10 Manual.Count131072.C060233.packed 64 cuts60233 = true := by
 decide +kernel
def pointBounds60233 : List (Nat × Nat × Nat) := [(7898845184,113964712761770,113965101196345)]
theorem point_links_checked60233 : (cuts60233.take 1).map (fun c => (7898791937-1+2*2^10*c.k,113964627772147+c.lower,113965016206673+c.upper)) = pointBounds60233 := by
 decide +kernel
def cuts60234 : List PrefixCut := [⟨64,204825922,204826043⟩]
theorem checked60234 : checkPrefixCuts (2^48) 7898923009 10 Manual.Count131072.C060234.packed 64 cuts60234 = true := by
 decide +kernel
def cuts60235 : List PrefixCut := [⟨19,60363849,60363884⟩,
⟨64,203824797,203824915⟩]
theorem checked60235 : checkPrefixCuts (2^48) 7899054081 10 Manual.Count131072.C060235.packed 64 cuts60235 = true := by
 decide +kernel
def pointBounds60235 : List (Nat × Nat × Nat) := [(7899092992,113965097506181,113965485940981)]
theorem point_links_checked60235 : (cuts60235.take 1).map (fun c => (7899054081-1+2*2^10*c.k,113965037142332+c.lower,113965425577097+c.upper)) = pointBounds60235 := by
 decide +kernel
def cuts60236 : List PrefixCut := [⟨64,205032935,205033053⟩]
theorem checked60236 : checkPrefixCuts (2^48) 7899185153 10 Manual.Count131072.C060236.packed 64 cuts60236 = true := by
 decide +kernel
def cuts60237 : List PrefixCut := [⟨12,38127054,38127077⟩,
⟨64,203675489,203675611⟩]
theorem checked60237 : checkPrefixCuts (2^48) 7899316225 10 Manual.Count131072.C060237.packed 64 cuts60237 = true := by
 decide +kernel
def pointBounds60237 : List (Nat × Nat × Nat) := [(7899340800,113965484127118,113965872562142)]
theorem point_links_checked60237 : (cuts60237.take 1).map (fun c => (7899316225-1+2*2^10*c.k,113965446000064+c.lower,113965834435065+c.upper)) = pointBounds60237 := by
 decide +kernel
def cuts60238 : List PrefixCut := [⟨64,206166345,206166461⟩]
theorem checked60238 : checkPrefixCuts (2^48) 7899447297 10 Manual.Count131072.C060238.packed 64 cuts60238 = true := by
 decide +kernel
def cuts60239 : List PrefixCut := [⟨5,15392856,15392866⟩,
⟨64,206590500,206590620⟩]
theorem checked60239 : checkPrefixCuts (2^48) 7899578369 10 Manual.Count131072.C060239.packed 64 cuts60239 = true := by
 decide +kernel
def pointBounds60239 : List (Nat × Nat × Nat) := [(7899588608,113965871234754,113966259670003)]
theorem point_links_checked60239 : (cuts60239.take 1).map (fun c => (7899578369-1+2*2^10*c.k,113965855841898+c.lower,113966244277137+c.upper)) = pointBounds60239 := by
 decide +kernel
def cuts60240 : List PrefixCut := [⟨62,199781668,199781786⟩,
⟨64,206302043,206302164⟩]
theorem checked60240 : checkPrefixCuts (2^48) 7899709441 10 Manual.Count131072.C060240.packed 64 cuts60240 = true := by
 decide +kernel
def pointBounds60240 : List (Nat × Nat × Nat) := [(7899836416,113966262214066,113966650649543)]
theorem point_links_checked60240 : (cuts60240.take 1).map (fun c => (7899709441-1+2*2^10*c.k,113966062432398+c.lower,113966450867757+c.upper)) = pointBounds60240 := by
 decide +kernel
def cuts60241 : List PrefixCut := [⟨64,205586019,205586141⟩]
theorem checked60241 : checkPrefixCuts (2^48) 7899840513 10 Manual.Count131072.C060241.packed 64 cuts60241 = true := by
 decide +kernel
def cuts60242 : List PrefixCut := [⟨55,175974628,175974732⟩,
⟨64,203943638,203943757⟩]
theorem checked60242 : checkPrefixCuts (2^48) 7899971585 10 Manual.Count131072.C060242.packed 64 cuts60242 = true := by
 decide +kernel
def pointBounds60242 : List (Nat × Nat × Nat) := [(7900084224,113966650295088,113967038730794)]
theorem point_links_checked60242 : (cuts60242.take 1).map (fun c => (7899971585-1+2*2^10*c.k,113966474320460+c.lower,113966862756062+c.upper)) = pointBounds60242 := by
 decide +kernel
def cuts60243 : List PrefixCut := [⟨64,204830986,204831103⟩]
theorem checked60243 : checkPrefixCuts (2^48) 7900102657 10 Manual.Count131072.C060243.packed 64 cuts60243 = true := by
 decide +kernel
def cuts60244 : List PrefixCut := [⟨48,150458980,150459069⟩,
⟨64,203438055,203438175⟩]
theorem checked60244 : checkPrefixCuts (2^48) 7900233729 10 Manual.Count131072.C060244.packed 64 cuts60244 = true := by
 decide +kernel
def pointBounds60244 : List (Nat × Nat × Nat) := [(7900332032,113967033554064,113967421989991)]
theorem point_links_checked60244 : (cuts60244.take 1).map (fun c => (7900233729-1+2*2^10*c.k,113966883095084+c.lower,113967271530922+c.upper)) = pointBounds60244 := by
 decide +kernel
def cuts60245 : List PrefixCut := [⟨64,204824177,204824295⟩]
theorem checked60245 : checkPrefixCuts (2^48) 7900364801 10 Manual.Count131072.C060245.packed 64 cuts60245 = true := by
 decide +kernel
def cuts60246 : List PrefixCut := [⟨41,129505264,129505338⟩,
⟨64,201044307,201044423⟩]
theorem checked60246 : checkPrefixCuts (2^48) 7900495873 10 Manual.Count131072.C060246.packed 64 cuts60246 = true := by
 decide +kernel
def pointBounds60246 : List (Nat × Nat × Nat) := [(7900579840,113967420862580,113967809298730)]
theorem point_links_checked60246 : (cuts60246.take 1).map (fun c => (7900495873-1+2*2^10*c.k,113967291357316+c.lower,113967679793392+c.upper)) = pointBounds60246 := by
 decide +kernel
def cuts60247 : List PrefixCut := [⟨64,206705593,206705713⟩]
theorem checked60247 : checkPrefixCuts (2^48) 7900626945 10 Manual.Count131072.C060247.packed 64 cuts60247 = true := by
 decide +kernel
def cuts60248 : List PrefixCut := [⟨34,107733511,107733568⟩,
⟨64,204350851,204350965⟩]
theorem checked60248 : checkPrefixCuts (2^48) 7900758017 10 Manual.Count131072.C060248.packed 64 cuts60248 = true := by
 decide +kernel
def pointBounds60248 : List (Nat × Nat × Nat) := [(7900827648,113967806840727,113968195277096)]
theorem point_links_checked60248 : (cuts60248.take 1).map (fun c => (7900758017-1+2*2^10*c.k,113967699107216+c.lower,113968087543528+c.upper)) = pointBounds60248 := by
 decide +kernel
def cuts60249 : List PrefixCut := [⟨64,205594344,205594463⟩]
theorem checked60249 : checkPrefixCuts (2^48) 7900889089 10 Manual.Count131072.C060249.packed 64 cuts60249 = true := by
 decide +kernel
def cuts60250 : List PrefixCut := [⟨27,86711271,86711321⟩,
⟨64,205840309,205840426⟩]
theorem checked60250 : checkPrefixCuts (2^48) 7901020161 10 Manual.Count131072.C060250.packed 64 cuts60250 = true := by
 decide +kernel
def pointBounds60250 : List (Nat × Nat × Nat) := [(7901075456,113968195763682,113968584200277)]
theorem point_links_checked60250 : (cuts60250.take 1).map (fun c => (7901020161-1+2*2^10*c.k,113968109052411+c.lower,113968497488956+c.upper)) = pointBounds60250 := by
 decide +kernel
def cuts60251 : List PrefixCut := [⟨64,202559465,202559582⟩]
theorem checked60251 : checkPrefixCuts (2^48) 7901151233 10 Manual.Count131072.C060251.packed 64 cuts60251 = true := by
 decide +kernel
def cuts60252 : List PrefixCut := [⟨20,64835423,64835459⟩,
⟨64,206439094,206439214⟩]
theorem checked60252 : checkPrefixCuts (2^48) 7901282305 10 Manual.Count131072.C060252.packed 64 cuts60252 = true := by
 decide +kernel
def pointBounds60252 : List (Nat × Nat × Nat) := [(7901323264,113968582287608,113968970724423)]
theorem point_links_checked60252 : (cuts60252.take 1).map (fun c => (7901282305-1+2*2^10*c.k,113968517452185+c.lower,113968905888964+c.upper)) = pointBounds60252 := by
 decide +kernel
def cuts60253 : List PrefixCut := [⟨64,207753696,207753815⟩]
theorem checked60253 : checkPrefixCuts (2^48) 7901413377 10 Manual.Count131072.C060253.packed 64 cuts60253 = true := by
 decide +kernel
def cuts60254 : List PrefixCut := [⟨13,41892307,41892331⟩,
⟨64,207287182,207287298⟩]
theorem checked60254 : checkPrefixCuts (2^48) 7901544449 10 Manual.Count131072.C060254.packed 64 cuts60254 = true := by
 decide +kernel
def pointBounds60254 : List (Nat × Nat × Nat) := [(7901571072,113968973537282,113969361974324)]
theorem point_links_checked60254 : (cuts60254.take 1).map (fun c => (7901544449-1+2*2^10*c.k,113968931644975+c.lower,113969320081993+c.upper)) = pointBounds60254 := by
 decide +kernel
def cuts60255 : List PrefixCut := [⟨64,207818066,207818182⟩]
theorem checked60255 : checkPrefixCuts (2^48) 7901675521 10 Manual.Count131072.C060255.packed 64 cuts60255 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000007
