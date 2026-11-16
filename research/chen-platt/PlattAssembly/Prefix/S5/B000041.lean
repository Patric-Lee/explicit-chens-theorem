import PlattAssemblyKernel
import PlattCertificates.Count131072.C041312
import PlattCertificates.Count131072.C041313
import PlattCertificates.Count131072.C041314
import PlattCertificates.Count131072.C041315
import PlattCertificates.Count131072.C041316
import PlattCertificates.Count131072.C041317
import PlattCertificates.Count131072.C041318
import PlattCertificates.Count131072.C041319
import PlattCertificates.Count131072.C041320
import PlattCertificates.Count131072.C041321
import PlattCertificates.Count131072.C041322
import PlattCertificates.Count131072.C041323
import PlattCertificates.Count131072.C041324
import PlattCertificates.Count131072.C041325
import PlattCertificates.Count131072.C041326
import PlattCertificates.Count131072.C041327
import PlattCertificates.Count131072.C041328
import PlattCertificates.Count131072.C041329
import PlattCertificates.Count131072.C041330
import PlattCertificates.Count131072.C041331
import PlattCertificates.Count131072.C041332
import PlattCertificates.Count131072.C041333
import PlattCertificates.Count131072.C041334
import PlattCertificates.Count131072.C041335
import PlattCertificates.Count131072.C041336
import PlattCertificates.Count131072.C041337
import PlattCertificates.Count131072.C041338
import PlattCertificates.Count131072.C041339
import PlattCertificates.Count131072.C041340
import PlattCertificates.Count131072.C041341
import PlattCertificates.Count131072.C041342
import PlattCertificates.Count131072.C041343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41312 : List PrefixCut := [⟨64,305169326,305169509⟩]
theorem checked41312 : checkPrefixCuts (2^48) 5418778625 10 Manual.Count131072.C041312.packed 64 cuts41312 = true := by
 decide +kernel
def cuts41313 : List PrefixCut := [⟨19,93601106,93601161⟩,
⟨64,307811026,307811207⟩]
theorem checked41313 : checkPrefixCuts (2^48) 5418909697 10 Manual.Count131072.C041313.packed 64 cuts41313 = true := by
 decide +kernel
def pointBounds41313 : List (Nat × Nat × Nat) := [(5418948608,109271912618104,109272298363759)]
theorem point_links_checked41313 : (cuts41313.take 1).map (fun c => (5418909697-1+2*2^10*c.k,109271819016998+c.lower,109272204762598+c.upper)) = pointBounds41313 := by
 decide +kernel
def cuts41314 : List PrefixCut := [⟨38,181015979,181016085⟩,
⟨64,302973040,302973219⟩]
theorem checked41314 : checkPrefixCuts (2^48) 5419040769 10 Manual.Count131072.C041314.packed 64 cuts41314 = true := by
 decide +kernel
def pointBounds41314 : List (Nat × Nat × Nat) := [(5419118592,109272307844003,109272693589890)]
theorem point_links_checked41314 : (cuts41314.take 1).map (fun c => (5419040769-1+2*2^10*c.k,109272126828024+c.lower,109272512573805+c.upper)) = pointBounds41314 := by
 decide +kernel
def cuts41315 : List PrefixCut := [⟨57,268062404,268062566⟩,
⟨64,301874946,301875126⟩]
theorem checked41315 : checkPrefixCuts (2^48) 5419171841 10 Manual.Count131072.C041315.packed 64 cuts41315 = true := by
 decide +kernel
def pointBounds41315 : List (Nat × Nat × Nat) := [(5419288576,109272697863468,109273083609590)]
theorem point_links_checked41315 : (cuts41315.take 1).map (fun c => (5419171841-1+2*2^10*c.k,109272429801064+c.lower,109272815547024+c.upper)) = pointBounds41315 := by
 decide +kernel
def cuts41316 : List PrefixCut := [⟨64,300413389,300413567⟩]
theorem checked41316 : checkPrefixCuts (2^48) 5419302913 10 Manual.Count131072.C041316.packed 64 cuts41316 = true := by
 decide +kernel
def cuts41317 : List PrefixCut := [⟨12,57079800,57079834⟩,
⟨64,305755685,305755861⟩]
theorem checked41317 : checkPrefixCuts (2^48) 5419433985 10 Manual.Count131072.C041317.packed 64 cuts41317 = true := by
 decide +kernel
def pointBounds41317 : List (Nat × Nat × Nat) := [(5419458560,109273089169199,109273474915551)]
theorem point_links_checked41317 : (cuts41317.take 1).map (fun c => (5419433985-1+2*2^10*c.k,109273032089399+c.lower,109273417835717+c.upper)) = pointBounds41317 := by
 decide +kernel
def cuts41318 : List PrefixCut := [⟨31,147395796,147395884⟩,
⟨64,303930523,303930702⟩]
theorem checked41318 : checkPrefixCuts (2^48) 5419565057 10 Manual.Count131072.C041318.packed 64 cuts41318 = true := by
 decide +kernel
def pointBounds41318 : List (Nat × Nat × Nat) := [(5419628544,109273485240880,109273870987462)]
theorem point_links_checked41318 : (cuts41318.take 1).map (fun c => (5419565057-1+2*2^10*c.k,109273337845084+c.lower,109273723591578+c.upper)) = pointBounds41318 := by
 decide +kernel
def cuts41319 : List PrefixCut := [⟨50,235109999,235110137⟩,
⟨64,300547380,300547555⟩]
theorem checked41319 : checkPrefixCuts (2^48) 5419696129 10 Manual.Count131072.C041319.packed 64 cuts41319 = true := by
 decide +kernel
def pointBounds41319 : List (Nat × Nat × Nat) := [(5419798528,109273876885606,109274262632417)]
theorem point_links_checked41319 : (cuts41319.take 1).map (fun c => (5419696129-1+2*2^10*c.k,109273641775607+c.lower,109274027522280+c.upper)) = pointBounds41319 := by
 decide +kernel
def cuts41320 : List PrefixCut := [⟨64,301319133,301319313⟩]
theorem checked41320 : checkPrefixCuts (2^48) 5419827201 10 Manual.Count131072.C041320.packed 64 cuts41320 = true := by
 decide +kernel
def cuts41321 : List PrefixCut := [⟨5,24148840,24148854⟩,
⟨64,305414488,305414668⟩]
theorem checked41321 : checkPrefixCuts (2^48) 5419958273 10 Manual.Count131072.C041321.packed 64 cuts41321 = true := by
 decide +kernel
def pointBounds41321 : List (Nat × Nat × Nat) := [(5419968512,109274267790960,109274653538002)]
theorem point_links_checked41321 : (cuts41321.take 1).map (fun c => (5419958273-1+2*2^10*c.k,109274243642120+c.lower,109274629389148+c.upper)) = pointBounds41321 := by
 decide +kernel
def cuts41322 : List PrefixCut := [⟨24,113574284,113574351⟩,
⟨64,301252626,301252803⟩]
theorem checked41322 : checkPrefixCuts (2^48) 5420089345 10 Manual.Count131072.C041322.packed 64 cuts41322 = true := by
 decide +kernel
def pointBounds41322 : List (Nat × Nat × Nat) := [(5420138496,109274662630892,109275048378167)]
theorem point_links_checked41322 : (cuts41322.take 1).map (fun c => (5420089345-1+2*2^10*c.k,109274549056608+c.lower,109274934803816+c.upper)) = pointBounds41322 := by
 decide +kernel
def cuts41323 : List PrefixCut := [⟨43,205227774,205227892⟩,
⟨64,304049571,304049749⟩]
theorem checked41323 : checkPrefixCuts (2^48) 5420220417 10 Manual.Count131072.C041323.packed 64 cuts41323 = true := by
 decide +kernel
def pointBounds41323 : List (Nat × Nat × Nat) := [(5420308480,109275055537008,109275441284511)]
theorem point_links_checked41323 : (cuts41323.take 1).map (fun c => (5420220417-1+2*2^10*c.k,109274850309234+c.lower,109275236056619+c.upper)) = pointBounds41323 := by
 decide +kernel
def cuts41324 : List PrefixCut := [⟨62,295058642,295058815⟩,
⟨64,304509544,304509723⟩]
theorem checked41324 : checkPrefixCuts (2^48) 5420351489 10 Manual.Count131072.C041324.packed 64 cuts41324 = true := by
 decide +kernel
def pointBounds41324 : List (Nat × Nat × Nat) := [(5420478464,109275449417447,109275835165183)]
theorem point_links_checked41324 : (cuts41324.take 1).map (fun c => (5420351489-1+2*2^10*c.k,109275154358805+c.lower,109275540106368+c.upper)) = pointBounds41324 := by
 decide +kernel
def cuts41325 : List PrefixCut := [⟨64,302892428,302892607⟩]
theorem checked41325 : checkPrefixCuts (2^48) 5420482561 10 Manual.Count131072.C041325.packed 64 cuts41325 = true := by
 decide +kernel
def cuts41326 : List PrefixCut := [⟨17,83705663,83705712⟩,
⟨64,304858354,304858535⟩]
theorem checked41326 : checkPrefixCuts (2^48) 5420613633 10 Manual.Count131072.C041326.packed 64 cuts41326 = true := by
 decide +kernel
def pointBounds41326 : List (Nat × Nat × Nat) := [(5420648448,109275845466440,109276231214410)]
theorem point_links_checked41326 : (cuts41326.take 1).map (fun c => (5420613633-1+2*2^10*c.k,109275761760777+c.lower,109276147508698+c.upper)) = pointBounds41326 := by
 decide +kernel
def cuts41327 : List PrefixCut := [⟨36,169743327,169743427⟩,
⟨64,303345127,303345302⟩]
theorem checked41327 : checkPrefixCuts (2^48) 5420744705 10 Manual.Count131072.C041327.packed 64 cuts41327 = true := by
 decide +kernel
def pointBounds41327 : List (Nat × Nat × Nat) := [(5420818432,109276236362458,109276622110660)]
theorem point_links_checked41327 : (cuts41327.take 1).map (fun c => (5420744705-1+2*2^10*c.k,109276066619131+c.lower,109276452367233+c.upper)) = pointBounds41327 := by
 decide +kernel
def cuts41328 : List PrefixCut := [⟨55,257385835,257385987⟩,
⟨64,298768530,298768707⟩]
theorem checked41328 : checkPrefixCuts (2^48) 5420875777 10 Manual.Count131072.C041328.packed 64 cuts41328 = true := by
 decide +kernel
def pointBounds41328 : List (Nat × Nat × Nat) := [(5420988416,109276627350093,109277013098522)]
theorem point_links_checked41328 : (cuts41328.take 1).map (fun c => (5420875777-1+2*2^10*c.k,109276369964258+c.lower,109276755712535+c.upper)) = pointBounds41328 := by
 decide +kernel
def cuts41329 : List PrefixCut := [⟨64,304991956,304992136⟩]
theorem checked41329 : checkPrefixCuts (2^48) 5421006849 10 Manual.Count131072.C041329.packed 64 cuts41329 = true := by
 decide +kernel
def cuts41330 : List PrefixCut := [⟨10,48131358,48131388⟩,
⟨64,301505872,301506049⟩]
theorem checked41330 : checkPrefixCuts (2^48) 5421137921 10 Manual.Count131072.C041330.packed 64 cuts41330 = true := by
 decide +kernel
def pointBounds41330 : List (Nat × Nat × Nat) := [(5421158400,109277021856102,109277407604766)]
theorem point_links_checked41330 : (cuts41330.take 1).map (fun c => (5421137921-1+2*2^10*c.k,109276973724744+c.lower,109277359473378+c.upper)) = pointBounds41330 := by
 decide +kernel
def cuts41331 : List PrefixCut := [⟨29,134525217,134525297⟩,
⟨64,300667831,300668004⟩]
theorem checked41331 : checkPrefixCuts (2^48) 5421268993 10 Manual.Count131072.C041331.packed 64 cuts41331 = true := by
 decide +kernel
def pointBounds41331 : List (Nat × Nat × Nat) := [(5421328384,109277409755833,109277795504724)]
theorem point_links_checked41331 : (cuts41331.take 1).map (fun c => (5421268993-1+2*2^10*c.k,109277275230616+c.lower,109277660979427+c.upper)) = pointBounds41331 := by
 decide +kernel
def cuts41332 : List PrefixCut := [⟨48,227559900,227560039⟩,
⟨64,302114330,302114514⟩]
theorem checked41332 : checkPrefixCuts (2^48) 5421400065 10 Manual.Count131072.C041332.packed 64 cuts41332 = true := by
 decide +kernel
def pointBounds41332 : List (Nat × Nat × Nat) := [(5421498368,109277803458347,109278189207470)]
theorem point_links_checked41332 : (cuts41332.take 1).map (fun c => (5421400065-1+2*2^10*c.k,109277575898447+c.lower,109277961647431+c.upper)) = pointBounds41332 := by
 decide +kernel
def cuts41333 : List PrefixCut := [⟨64,303249192,303249368⟩]
theorem checked41333 : checkPrefixCuts (2^48) 5421531137 10 Manual.Count131072.C041333.packed 64 cuts41333 = true := by
 decide +kernel
def cuts41334 : List PrefixCut := [⟨3,13134921,13134929⟩,
⟨64,304435954,304436133⟩]
theorem checked41334 : checkPrefixCuts (2^48) 5421662209 10 Manual.Count131072.C041334.packed 64 cuts41334 = true := by
 decide +kernel
def pointBounds41334 : List (Nat × Nat × Nat) := [(5421668352,109278194396890,109278580146242)]
theorem point_links_checked41334 : (cuts41334.take 1).map (fun c => (5421662209-1+2*2^10*c.k,109278181261969+c.lower,109278567011313+c.upper)) = pointBounds41334 := by
 decide +kernel
def cuts41335 : List PrefixCut := [⟨22,105076462,105076522⟩,
⟨64,309412398,309412578⟩]
theorem checked41335 : checkPrefixCuts (2^48) 5421793281 10 Manual.Count131072.C041335.packed 64 cuts41335 = true := by
 decide +kernel
def pointBounds41335 : List (Nat × Nat × Nat) := [(5421838336,109278590774385,109278976523968)]
theorem point_links_checked41335 : (cuts41335.take 1).map (fun c => (5421793281-1+2*2^10*c.k,109278485697923+c.lower,109278871447446+c.upper)) = pointBounds41335 := by
 decide +kernel
def cuts41336 : List PrefixCut := [⟨41,196389911,196390027⟩,
⟨64,303227221,303227401⟩]
theorem checked41336 : checkPrefixCuts (2^48) 5421924353 10 Manual.Count131072.C041336.packed 64 cuts41336 = true := by
 decide +kernel
def pointBounds41336 : List (Nat × Nat × Nat) := [(5422008320,109278991500232,109279377250051)]
theorem point_links_checked41336 : (cuts41336.take 1).map (fun c => (5421924353-1+2*2^10*c.k,109278795110321+c.lower,109279180860024+c.upper)) = pointBounds41336 := by
 decide +kernel
def cuts41337 : List PrefixCut := [⟨60,281728401,281728565⟩,
⟨64,300883831,300884006⟩]
theorem checked41337 : checkPrefixCuts (2^48) 5422055425 10 Manual.Count131072.C041337.packed 64 cuts41337 = true := by
 decide +kernel
def pointBounds41337 : List (Nat × Nat × Nat) := [(5422178304,109279380065943,109279765815990)]
theorem point_links_checked41337 : (cuts41337.take 1).map (fun c => (5422055425-1+2*2^10*c.k,109279098337542+c.lower,109279484087425+c.upper)) = pointBounds41337 := by
 decide +kernel
def cuts41338 : List PrefixCut := [⟨64,302537711,302537890⟩]
theorem checked41338 : checkPrefixCuts (2^48) 5422186497 10 Manual.Count131072.C041338.packed 64 cuts41338 = true := by
 decide +kernel
def cuts41339 : List PrefixCut := [⟨15,70753731,70753771⟩,
⟨64,299727259,299727435⟩]
theorem checked41339 : checkPrefixCuts (2^48) 5422317569 10 Manual.Count131072.C041339.packed 64 cuts41339 = true := by
 decide +kernel
def pointBounds41339 : List (Nat × Nat × Nat) := [(5422348288,109279772512815,109280158263092)]
theorem point_links_checked41339 : (cuts41339.take 1).map (fun c => (5422317569-1+2*2^10*c.k,109279701759084+c.lower,109280087509321+c.upper)) = pointBounds41339 := by
 decide +kernel
def cuts41340 : List PrefixCut := [⟨34,161125078,161125174⟩,
⟨64,302626894,302627071⟩]
theorem checked41340 : checkPrefixCuts (2^48) 5422448641 10 Manual.Count131072.C041340.packed 64 cuts41340 = true := by
 decide +kernel
def pointBounds41340 : List (Nat × Nat × Nat) := [(5422518272,109280162611421,109280548361930)]
theorem point_links_checked41340 : (cuts41340.take 1).map (fun c => (5422448641-1+2*2^10*c.k,109280001486343+c.lower,109280387236756+c.upper)) = pointBounds41340 := by
 decide +kernel
def cuts41341 : List PrefixCut := [⟨53,249103679,249103829⟩,
⟨64,301840972,301841154⟩]
theorem checked41341 : checkPrefixCuts (2^48) 5422579713 10 Manual.Count131072.C041341.packed 64 cuts41341 = true := by
 decide +kernel
def pointBounds41341 : List (Nat × Nat × Nat) := [(5422688256,109280553216916,109280938967656)]
theorem point_links_checked41341 : (cuts41341.take 1).map (fun c => (5422579713-1+2*2^10*c.k,109280304113237+c.lower,109280689863827+c.upper)) = pointBounds41341 := by
 decide +kernel
def cuts41342 : List PrefixCut := [⟨64,299913143,299913314⟩]
theorem checked41342 : checkPrefixCuts (2^48) 5422710785 10 Manual.Count131072.C041342.packed 64 cuts41342 = true := by
 decide +kernel
def cuts41343 : List PrefixCut := [⟨8,36748982,36749006⟩,
⟨64,300321128,300321309⟩]
theorem checked41343 : checkPrefixCuts (2^48) 5422841857 10 Manual.Count131072.C041343.packed 64 cuts41343 = true := by
 decide +kernel
def pointBounds41343 : List (Nat × Nat × Nat) := [(5422858240,109280942616334,109281328367301)]
theorem point_links_checked41343 : (cuts41343.take 1).map (fun c => (5422841857-1+2*2^10*c.k,109280905867352+c.lower,109281291618295+c.upper)) = pointBounds41343 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000041
