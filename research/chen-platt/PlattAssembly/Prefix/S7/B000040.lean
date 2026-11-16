import PlattAssemblyKernel
import PlattCertificates.Count131072.C061280
import PlattCertificates.Count131072.C061281
import PlattCertificates.Count131072.C061282
import PlattCertificates.Count131072.C061283
import PlattCertificates.Count131072.C061284
import PlattCertificates.Count131072.C061285
import PlattCertificates.Count131072.C061286
import PlattCertificates.Count131072.C061287
import PlattCertificates.Count131072.C061288
import PlattCertificates.Count131072.C061289
import PlattCertificates.Count131072.C061290
import PlattCertificates.Count131072.C061291
import PlattCertificates.Count131072.C061292
import PlattCertificates.Count131072.C061293
import PlattCertificates.Count131072.C061294
import PlattCertificates.Count131072.C061295
import PlattCertificates.Count131072.C061296
import PlattCertificates.Count131072.C061297
import PlattCertificates.Count131072.C061298
import PlattCertificates.Count131072.C061299
import PlattCertificates.Count131072.C061300
import PlattCertificates.Count131072.C061301
import PlattCertificates.Count131072.C061302
import PlattCertificates.Count131072.C061303
import PlattCertificates.Count131072.C061304
import PlattCertificates.Count131072.C061305
import PlattCertificates.Count131072.C061306
import PlattCertificates.Count131072.C061307
import PlattCertificates.Count131072.C061308
import PlattCertificates.Count131072.C061309
import PlattCertificates.Count131072.C061310
import PlattCertificates.Count131072.C061311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61280 : List PrefixCut := [⟨31,98424460,98424516⟩,
⟨64,202382249,202382367⟩]
theorem checked61280 : checkPrefixCuts (2^48) 8036024321 10 Manual.Count131072.C061280.packed 64 cuts61280 = true := by
 decide +kernel
def pointBounds61280 : List (Nat × Nat × Nat) := [(8036087808,114177431709877,114177820266102)]
theorem point_links_checked61280 : (cuts61280.take 1).map (fun c => (8036024321-1+2*2^10*c.k,114177333285417+c.lower,114177721841586+c.upper)) = pointBounds61280 := by
 decide +kernel
def cuts61281 : List PrefixCut := [⟨64,198596163,198596281⟩]
theorem checked61281 : checkPrefixCuts (2^48) 8036155393 10 Manual.Count131072.C061281.packed 64 cuts61281 = true := by
 decide +kernel
def cuts61282 : List PrefixCut := [⟨26,81013694,81013744⟩,
⟨64,201815240,201815363⟩]
theorem checked61282 : checkPrefixCuts (2^48) 8036286465 10 Manual.Count131072.C061282.packed 64 cuts61282 = true := by
 decide +kernel
def pointBounds61282 : List (Nat × Nat × Nat) := [(8036339712,114177815277523,114178203833978)]
theorem point_links_checked61282 : (cuts61282.take 1).map (fun c => (8036286465-1+2*2^10*c.k,114177734263829+c.lower,114178122820234+c.upper)) = pointBounds61282 := by
 decide +kernel
def cuts61283 : List PrefixCut := [⟨64,200481023,200481136⟩]
theorem checked61283 : checkPrefixCuts (2^48) 8036417537 10 Manual.Count131072.C061283.packed 64 cuts61283 = true := by
 decide +kernel
def cuts61284 : List PrefixCut := [⟨21,64689804,64689843⟩,
⟨64,199392000,199392116⟩]
theorem checked61284 : checkPrefixCuts (2^48) 8036548609 10 Manual.Count131072.C061284.packed 64 cuts61284 = true := by
 decide +kernel
def pointBounds61284 : List (Nat × Nat × Nat) := [(8036591616,114178201249896,114178589806576)]
theorem point_links_checked61284 : (cuts61284.take 1).map (fun c => (8036548609-1+2*2^10*c.k,114178136560092+c.lower,114178525116733+c.upper)) = pointBounds61284 := by
 decide +kernel
def cuts61285 : List PrefixCut := [⟨64,200194300,200194415⟩]
theorem checked61285 : checkPrefixCuts (2^48) 8036679681 10 Manual.Count131072.C061285.packed 64 cuts61285 = true := by
 decide +kernel
def cuts61286 : List PrefixCut := [⟨16,51238850,51238880⟩,
⟨64,202152313,202152432⟩]
theorem checked61286 : checkPrefixCuts (2^48) 8036810753 10 Manual.Count131072.C061286.packed 64 cuts61286 = true := by
 decide +kernel
def pointBounds61286 : List (Nat × Nat × Nat) := [(8036843520,114178587385242,114178975942144)]
theorem point_links_checked61286 : (cuts61286.take 1).map (fun c => (8036810753-1+2*2^10*c.k,114178536146392+c.lower,114178924703264+c.upper)) = pointBounds61286 := by
 decide +kernel
def cuts61287 : List PrefixCut := [⟨64,203059586,203059700⟩]
theorem checked61287 : checkPrefixCuts (2^48) 8036941825 10 Manual.Count131072.C061287.packed 64 cuts61287 = true := by
 decide +kernel
def cuts61288 : List PrefixCut := [⟨11,34636775,34636794⟩,
⟨64,200779878,200779991⟩]
theorem checked61288 : checkPrefixCuts (2^48) 8037072897 10 Manual.Count131072.C061288.packed 64 cuts61288 = true := by
 decide +kernel
def pointBounds61288 : List (Nat × Nat × Nat) := [(8037095424,114178975995066,114179364552190)]
theorem point_links_checked61288 : (cuts61288.take 1).map (fun c => (8037072897-1+2*2^10*c.k,114178941358291+c.lower,114179329915396+c.upper)) = pointBounds61288 := by
 decide +kernel
def cuts61289 : List PrefixCut := [⟨64,204453821,204453935⟩]
theorem checked61289 : checkPrefixCuts (2^48) 8037203969 10 Manual.Count131072.C061289.packed 64 cuts61289 = true := by
 decide +kernel
def cuts61290 : List PrefixCut := [⟨6,18806221,18806232⟩,
⟨64,199792737,199792849⟩]
theorem checked61290 : checkPrefixCuts (2^48) 8037335041 10 Manual.Count131072.C061290.packed 64 cuts61290 = true := by
 decide +kernel
def pointBounds61290 : List (Nat × Nat × Nat) := [(8037347328,114179365398211,114179753955554)]
theorem point_links_checked61290 : (cuts61290.take 1).map (fun c => (8037335041-1+2*2^10*c.k,114179346591990+c.lower,114179735149322+c.upper)) = pointBounds61290 := by
 decide +kernel
def cuts61291 : List PrefixCut := [⟨64,205427696,205427815⟩]
theorem checked61291 : checkPrefixCuts (2^48) 8037466113 10 Manual.Count131072.C061291.packed 64 cuts61291 = true := by
 decide +kernel
def cuts61292 : List PrefixCut := [⟨1,3186800,3186802⟩,
⟨64,204934089,204934208⟩]
theorem checked61292 : checkPrefixCuts (2^48) 8037597185 10 Manual.Count131072.C061292.packed 64 cuts61292 = true := by
 decide +kernel
def pointBounds61292 : List (Nat × Nat × Nat) := [(8037599232,114179754999223,114180143556788)]
theorem point_links_checked61292 : (cuts61292.take 1).map (fun c => (8037597185-1+2*2^10*c.k,114179751812423+c.lower,114180140369986+c.upper)) = pointBounds61292 := by
 decide +kernel
def cuts61293 : List PrefixCut := [⟨60,188962209,188962313⟩,
⟨64,200903571,200903682⟩]
theorem checked61293 : checkPrefixCuts (2^48) 8037728257 10 Manual.Count131072.C061293.packed 64 cuts61293 = true := by
 decide +kernel
def pointBounds61293 : List (Nat × Nat × Nat) := [(8037851136,114180145708721,114180534266507)]
theorem point_links_checked61293 : (cuts61293.take 1).map (fun c => (8037728257-1+2*2^10*c.k,114179956746512+c.lower,114180345304194+c.upper)) = pointBounds61293 := by
 decide +kernel
def cuts61294 : List PrefixCut := [⟨64,204437150,204437265⟩]
theorem checked61294 : checkPrefixCuts (2^48) 8037859329 10 Manual.Count131072.C061294.packed 64 cuts61294 = true := by
 decide +kernel
def cuts61295 : List PrefixCut := [⟨55,171622343,171622445⟩,
⟨64,199951530,199951648⟩]
theorem checked61295 : checkPrefixCuts (2^48) 8037990401 10 Manual.Count131072.C061295.packed 64 cuts61295 = true := by
 decide +kernel
def pointBounds61295 : List (Nat × Nat × Nat) := [(8038103040,114180533709576,114180922267586)]
theorem point_links_checked61295 : (cuts61295.take 1).map (fun c => (8037990401-1+2*2^10*c.k,114180362087233+c.lower,114180750645141+c.upper)) = pointBounds61295 := by
 decide +kernel
def cuts61296 : List PrefixCut := [⟨64,199387999,199388120⟩]
theorem checked61296 : checkPrefixCuts (2^48) 8038121473 10 Manual.Count131072.C061296.packed 64 cuts61296 = true := by
 decide +kernel
def cuts61297 : List PrefixCut := [⟨50,158415571,158415662⟩,
⟨64,202641306,202641421⟩]
theorem checked61297 : checkPrefixCuts (2^48) 8038252545 10 Manual.Count131072.C061297.packed 64 cuts61297 = true := by
 decide +kernel
def pointBounds61297 : List (Nat × Nat × Nat) := [(8038354944,114180919842333,114181308400571)]
theorem point_links_checked61297 : (cuts61297.take 1).map (fun c => (8038252545-1+2*2^10*c.k,114180761426762+c.lower,114181149984909+c.upper)) = pointBounds61297 := by
 decide +kernel
def cuts61298 : List PrefixCut := [⟨64,198716180,198716291⟩]
theorem checked61298 : checkPrefixCuts (2^48) 8038383617 10 Manual.Count131072.C061298.packed 64 cuts61298 = true := by
 decide +kernel
def cuts61299 : List PrefixCut := [⟨45,140832681,140832757⟩,
⟨64,201549210,201549321⟩]
theorem checked61299 : checkPrefixCuts (2^48) 8038514689 10 Manual.Count131072.C061299.packed 64 cuts61299 = true := by
 decide +kernel
def pointBounds61299 : List (Nat × Nat × Nat) := [(8038606848,114181303616929,114181692175378)]
theorem point_links_checked61299 : (cuts61299.take 1).map (fun c => (8038514689-1+2*2^10*c.k,114181162784248+c.lower,114181551342621+c.upper)) = pointBounds61299 := by
 decide +kernel
def cuts61300 : List PrefixCut := [⟨64,202491327,202491442⟩]
theorem checked61300 : checkPrefixCuts (2^48) 8038645761 10 Manual.Count131072.C061300.packed 64 cuts61300 = true := by
 decide +kernel
def cuts61301 : List PrefixCut := [⟨40,125736937,125737011⟩,
⟨64,201507617,201507735⟩]
theorem checked61301 : checkPrefixCuts (2^48) 8038776833 10 Manual.Count131072.C061301.packed 64 cuts61301 = true := by
 decide +kernel
def pointBounds61301 : List (Nat × Nat × Nat) := [(8038858752,114181692561722,114182081120395)]
theorem point_links_checked61301 : (cuts61301.take 1).map (fun c => (8038776833-1+2*2^10*c.k,114181566824785+c.lower,114181955383384+c.upper)) = pointBounds61301 := by
 decide +kernel
def cuts61302 : List PrefixCut := [⟨64,202659805,202659921⟩]
theorem checked61302 : checkPrefixCuts (2^48) 8038907905 10 Manual.Count131072.C061302.packed 64 cuts61302 = true := by
 decide +kernel
def cuts61303 : List PrefixCut := [⟨35,111062332,111062395⟩,
⟨64,201501067,201501183⟩]
theorem checked61303 : checkPrefixCuts (2^48) 8039038977 10 Manual.Count131072.C061303.packed 64 cuts61303 = true := by
 decide +kernel
def pointBounds61303 : List (Nat × Nat × Nat) := [(8039110656,114182082054539,114182470613435)]
theorem point_links_checked61303 : (cuts61303.take 1).map (fun c => (8039038977-1+2*2^10*c.k,114181970992207+c.lower,114182359551040+c.upper)) = pointBounds61303 := by
 decide +kernel
def cuts61304 : List PrefixCut := [⟨64,203913638,203913760⟩]
theorem checked61304 : checkPrefixCuts (2^48) 8039170049 10 Manual.Count131072.C061304.packed 64 cuts61304 = true := by
 decide +kernel
def cuts61305 : List PrefixCut := [⟨30,93657699,93657749⟩,
⟨64,198308384,198308499⟩]
theorem checked61305 : checkPrefixCuts (2^48) 8039301121 10 Manual.Count131072.C061305.packed 64 cuts61305 = true := by
 decide +kernel
def pointBounds61305 : List (Nat × Nat × Nat) := [(8039362560,114182470064611,114182858623732)]
theorem point_links_checked61305 : (cuts61305.take 1).map (fun c => (8039301121-1+2*2^10*c.k,114182376406912+c.lower,114182764965983+c.upper)) = pointBounds61305 := by
 decide +kernel
def cuts61306 : List PrefixCut := [⟨64,198410183,198410301⟩]
theorem checked61306 : checkPrefixCuts (2^48) 8039432193 10 Manual.Count131072.C061306.packed 64 cuts61306 = true := by
 decide +kernel
def cuts61307 : List PrefixCut := [⟨25,76849378,76849420⟩,
⟨64,198757054,198757170⟩]
theorem checked61307 : checkPrefixCuts (2^48) 8039563265 10 Manual.Count131072.C061307.packed 64 cuts61307 = true := by
 decide +kernel
def pointBounds61307 : List (Nat × Nat × Nat) := [(8039614464,114182849974857,114183238534203)]
theorem point_links_checked61307 : (cuts61307.take 1).map (fun c => (8039563265-1+2*2^10*c.k,114182773125479+c.lower,114183161684783+c.upper)) = pointBounds61307 := by
 decide +kernel
def cuts61308 : List PrefixCut := [⟨64,199138923,199139040⟩]
theorem checked61308 : checkPrefixCuts (2^48) 8039694337 10 Manual.Count131072.C061308.packed 64 cuts61308 = true := by
 decide +kernel
def cuts61309 : List PrefixCut := [⟨20,62562842,62562880⟩,
⟨64,200150985,200151101⟩]
theorem checked61309 : checkPrefixCuts (2^48) 8039825409 10 Manual.Count131072.C061309.packed 64 cuts61309 = true := by
 decide +kernel
def pointBounds61309 : List (Nat × Nat × Nat) := [(8039866368,114183233584298,114183622143873)]
theorem point_links_checked61309 : (cuts61309.take 1).map (fun c => (8039825409-1+2*2^10*c.k,114183171021456+c.lower,114183559580993+c.upper)) = pointBounds61309 := by
 decide +kernel
def cuts61310 : List PrefixCut := [⟨64,198887368,198887484⟩]
theorem checked61310 : checkPrefixCuts (2^48) 8039956481 10 Manual.Count131072.C061310.packed 64 cuts61310 = true := by
 decide +kernel
def cuts61311 : List PrefixCut := [⟨15,48032167,48032191⟩,
⟨64,202700082,202700192⟩]
theorem checked61311 : checkPrefixCuts (2^48) 8040087553 10 Manual.Count131072.C061311.packed 64 cuts61311 = true := by
 decide +kernel
def pointBounds61311 : List (Nat × Nat × Nat) := [(8040118272,114183618091976,114184006651769)]
theorem point_links_checked61311 : (cuts61311.take 1).map (fun c => (8040087553-1+2*2^10*c.k,114183570059809+c.lower,114183958619578+c.upper)) = pointBounds61311 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000040
