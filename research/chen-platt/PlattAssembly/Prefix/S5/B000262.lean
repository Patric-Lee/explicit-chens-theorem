import PlattAssemblyKernel
import PlattCertificates.Count131072.C048384
import PlattCertificates.Count131072.C048385
import PlattCertificates.Count131072.C048386
import PlattCertificates.Count131072.C048387
import PlattCertificates.Count131072.C048388
import PlattCertificates.Count131072.C048389
import PlattCertificates.Count131072.C048390
import PlattCertificates.Count131072.C048391
import PlattCertificates.Count131072.C048392
import PlattCertificates.Count131072.C048393
import PlattCertificates.Count131072.C048394
import PlattCertificates.Count131072.C048395
import PlattCertificates.Count131072.C048396
import PlattCertificates.Count131072.C048397
import PlattCertificates.Count131072.C048398
import PlattCertificates.Count131072.C048399
import PlattCertificates.Count131072.C048400
import PlattCertificates.Count131072.C048401
import PlattCertificates.Count131072.C048402
import PlattCertificates.Count131072.C048403
import PlattCertificates.Count131072.C048404
import PlattCertificates.Count131072.C048405
import PlattCertificates.Count131072.C048406
import PlattCertificates.Count131072.C048407
import PlattCertificates.Count131072.C048408
import PlattCertificates.Count131072.C048409
import PlattCertificates.Count131072.C048410
import PlattCertificates.Count131072.C048411
import PlattCertificates.Count131072.C048412
import PlattCertificates.Count131072.C048413
import PlattCertificates.Count131072.C048414
import PlattCertificates.Count131072.C048415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000262
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48384 : List PrefixCut := [⟨64,258640980,258641128⟩]
theorem checked48384 : checkPrefixCuts (2^48) 6345719809 10 Manual.Count131072.C048384.packed 64 cuts48384 = true := by
 decide +kernel
def cuts48385 : List PrefixCut := [⟨1,4302506,4302508⟩,
⟨64,259966284,259966433⟩]
theorem checked48385 : checkPrefixCuts (2^48) 6345850881 10 Manual.Count131072.C048385.packed 64 cuts48385 = true := by
 decide +kernel
def pointBounds48385 : List (Nat × Nat × Nat) := [(6345852928,111247985244627,111248372133433)]
theorem point_links_checked48385 : (cuts48385.take 1).map (fun c => (6345850881-1+2*2^10*c.k,111247980942121+c.lower,111248367830925+c.upper)) = pointBounds48385 := by
 decide +kernel
def cuts48386 : List PrefixCut := [⟨34,134837913,134837991⟩,
⟨64,252819870,252820016⟩]
theorem checked48386 : checkPrefixCuts (2^48) 6345981953 10 Manual.Count131072.C048386.packed 64 cuts48386 = true := by
 decide +kernel
def pointBounds48386 : List (Nat × Nat × Nat) := [(6346051584,111248375746318,111248762635349)]
theorem point_links_checked48386 : (cuts48386.take 1).map (fun c => (6345981953-1+2*2^10*c.k,111248240908405+c.lower,111248627797358+c.upper)) = pointBounds48386 := by
 decide +kernel
def cuts48387 : List PrefixCut := [⟨64,261463566,261463712⟩]
theorem checked48387 : checkPrefixCuts (2^48) 6346113025 10 Manual.Count131072.C048387.packed 64 cuts48387 = true := by
 decide +kernel
def cuts48388 : List PrefixCut := [⟨3,11930948,11930955⟩,
⟨64,256668098,256668249⟩]
theorem checked48388 : checkPrefixCuts (2^48) 6346244097 10 Manual.Count131072.C048388.packed 64 cuts48388 = true := by
 decide +kernel
def pointBounds48388 : List (Nat × Nat × Nat) := [(6346250240,111248767122789,111249154012041)]
theorem point_links_checked48388 : (cuts48388.take 1).map (fun c => (6346244097-1+2*2^10*c.k,111248755191841+c.lower,111249142081086+c.upper)) = pointBounds48388 := by
 decide +kernel
def cuts48389 : List PrefixCut := [⟨36,146405351,146405432⟩,
⟨64,258436879,258437022⟩]
theorem checked48389 : checkPrefixCuts (2^48) 6346375169 10 Manual.Count131072.C048389.packed 64 cuts48389 = true := by
 decide +kernel
def pointBounds48389 : List (Nat × Nat × Nat) := [(6346448896,111249158265290,111249545154767)]
theorem point_links_checked48389 : (cuts48389.take 1).map (fun c => (6346375169-1+2*2^10*c.k,111249011859939+c.lower,111249398749335+c.upper)) = pointBounds48389 := by
 decide +kernel
def cuts48390 : List PrefixCut := [⟨64,258076686,258076834⟩]
theorem checked48390 : checkPrefixCuts (2^48) 6346506241 10 Manual.Count131072.C048390.packed 64 cuts48390 = true := by
 decide +kernel
def cuts48391 : List PrefixCut := [⟨5,20622847,20622857⟩,
⟨64,258514901,258515045⟩]
theorem checked48391 : checkPrefixCuts (2^48) 6346637313 10 Manual.Count131072.C048391.packed 64 cuts48391 = true := by
 decide +kernel
def pointBounds48391 : List (Nat × Nat × Nat) := [(6346647552,111249548996351,111249935886048)]
theorem point_links_checked48391 : (cuts48391.take 1).map (fun c => (6346637313-1+2*2^10*c.k,111249528373504+c.lower,111249915263191+c.upper)) = pointBounds48391 := by
 decide +kernel
def cuts48392 : List PrefixCut := [⟨38,152782487,152782570⟩,
⟨64,258243454,258243597⟩]
theorem checked48392 : checkPrefixCuts (2^48) 6346768385 10 Manual.Count131072.C048392.packed 64 cuts48392 = true := by
 decide +kernel
def pointBounds48392 : List (Nat × Nat × Nat) := [(6346846208,111249939670892,111250326560806)]
theorem point_links_checked48392 : (cuts48392.take 1).map (fun c => (6346768385-1+2*2^10*c.k,111249786888405+c.lower,111250173778236+c.upper)) = pointBounds48392 := by
 decide +kernel
def cuts48393 : List PrefixCut := [⟨64,258060727,258060872⟩]
theorem checked48393 : checkPrefixCuts (2^48) 6346899457 10 Manual.Count131072.C048393.packed 64 cuts48393 = true := by
 decide +kernel
def cuts48394 : List PrefixCut := [⟨7,27628457,27628472⟩,
⟨64,258144101,258144244⟩]
theorem checked48394 : checkPrefixCuts (2^48) 6347030529 10 Manual.Count131072.C048394.packed 64 cuts48394 = true := by
 decide +kernel
def pointBounds48394 : List (Nat × Nat × Nat) := [(6347044864,111250330821043,111250717711177)]
theorem point_links_checked48394 : (cuts48394.take 1).map (fun c => (6347030529-1+2*2^10*c.k,111250303192586+c.lower,111250690082705+c.upper)) = pointBounds48394 := by
 decide +kernel
def cuts48395 : List PrefixCut := [⟨40,157340636,157340730⟩,
⟨64,253038945,253039092⟩]
theorem checked48395 : checkPrefixCuts (2^48) 6347161601 10 Manual.Count131072.C048395.packed 64 cuts48395 = true := by
 decide +kernel
def pointBounds48395 : List (Nat × Nat × Nat) := [(6347243520,111250718677323,111251105567679)]
theorem point_links_checked48395 : (cuts48395.take 1).map (fun c => (6347161601-1+2*2^10*c.k,111250561336687+c.lower,111250948226949+c.upper)) = pointBounds48395 := by
 decide +kernel
def cuts48396 : List PrefixCut := [⟨64,254142372,254142514⟩]
theorem checked48396 : checkPrefixCuts (2^48) 6347292673 10 Manual.Count131072.C048396.packed 64 cuts48396 = true := by
 decide +kernel
def cuts48397 : List PrefixCut := [⟨9,36406986,36407008⟩,
⟨64,253649336,253649482⟩]
theorem checked48397 : checkPrefixCuts (2^48) 6347423745 10 Manual.Count131072.C048397.packed 64 cuts48397 = true := by
 decide +kernel
def pointBounds48397 : List (Nat × Nat × Nat) := [(6347442176,111251104924990,111251491815563)]
theorem point_links_checked48397 : (cuts48397.take 1).map (fun c => (6347423745-1+2*2^10*c.k,111251068518004+c.lower,111251455408555+c.upper)) = pointBounds48397 := by
 decide +kernel
def cuts48398 : List PrefixCut := [⟨42,167263804,167263898⟩,
⟨64,256792467,256792615⟩]
theorem checked48398 : checkPrefixCuts (2^48) 6347554817 10 Manual.Count131072.C048398.packed 64 cuts48398 = true := by
 decide +kernel
def pointBounds48398 : List (Nat × Nat × Nat) := [(6347640832,111251489431144,111251876321935)]
theorem point_links_checked48398 : (cuts48398.take 1).map (fun c => (6347554817-1+2*2^10*c.k,111251322167340+c.lower,111251709058037+c.upper)) = pointBounds48398 := by
 decide +kernel
def cuts48399 : List PrefixCut := [⟨64,256077710,256077850⟩]
theorem checked48399 : checkPrefixCuts (2^48) 6347685889 10 Manual.Count131072.C048399.packed 64 cuts48399 = true := by
 decide +kernel
def cuts48400 : List PrefixCut := [⟨11,43233373,43233398⟩,
⟨64,258910247,258910398⟩]
theorem checked48400 : checkPrefixCuts (2^48) 6347816961 10 Manual.Count131072.C048400.packed 64 cuts48400 = true := by
 decide +kernel
def pointBounds48400 : List (Nat × Nat × Nat) := [(6347839488,111251878270890,111252265161900)]
theorem point_links_checked48400 : (cuts48400.take 1).map (fun c => (6347816961-1+2*2^10*c.k,111251835037517+c.lower,111252221928502+c.upper)) = pointBounds48400 := by
 decide +kernel
def cuts48401 : List PrefixCut := [⟨44,176830983,176831086⟩,
⟨64,256998267,256998417⟩]
theorem checked48401 : checkPrefixCuts (2^48) 6347948033 10 Manual.Count131072.C048401.packed 64 cuts48401 = true := by
 decide +kernel
def pointBounds48401 : List (Nat × Nat × Nat) := [(6348038144,111252270778747,111252657669986)]
theorem point_links_checked48401 : (cuts48401.take 1).map (fun c => (6347948033-1+2*2^10*c.k,111252093947764+c.lower,111252480838900+c.upper)) = pointBounds48401 := by
 decide +kernel
def cuts48402 : List PrefixCut := [⟨64,256904269,256904416⟩]
theorem checked48402 : checkPrefixCuts (2^48) 6348079105 10 Manual.Count131072.C048402.packed 64 cuts48402 = true := by
 decide +kernel
def cuts48403 : List PrefixCut := [⟨13,52408887,52408917⟩,
⟨64,258495188,258495329⟩]
theorem checked48403 : checkPrefixCuts (2^48) 6348210177 10 Manual.Count131072.C048403.packed 64 cuts48403 = true := by
 decide +kernel
def pointBounds48403 : List (Nat × Nat × Nat) := [(6348236800,111252660259187,111253047150650)]
theorem point_links_checked48403 : (cuts48403.take 1).map (fun c => (6348210177-1+2*2^10*c.k,111252607850300+c.lower,111252994741733+c.upper)) = pointBounds48403 := by
 decide +kernel
def cuts48404 : List PrefixCut := [⟨46,187461103,187461207⟩,
⟨64,261194449,261194597⟩]
theorem checked48404 : checkPrefixCuts (2^48) 6348341249 10 Manual.Count131072.C048404.packed 64 cuts48404 = true := by
 decide +kernel
def pointBounds48404 : List (Nat × Nat × Nat) := [(6348435456,111253053806591,111253440698269)]
theorem point_links_checked48404 : (cuts48404.take 1).map (fun c => (6348341249-1+2*2^10*c.k,111252866345488+c.lower,111253253237062+c.upper)) = pointBounds48404 := by
 decide +kernel
def cuts48405 : List PrefixCut := [⟨64,254627188,254627333⟩]
theorem checked48405 : checkPrefixCuts (2^48) 6348472321 10 Manual.Count131072.C048405.packed 64 cuts48405 = true := by
 decide +kernel
def cuts48406 : List PrefixCut := [⟨15,61982287,61982322⟩,
⟨64,259232900,259233048⟩]
theorem checked48406 : checkPrefixCuts (2^48) 6348603393 10 Manual.Count131072.C048406.packed 64 cuts48406 = true := by
 decide +kernel
def pointBounds48406 : List (Nat × Nat × Nat) := [(6348634112,111253444149412,111253831041314)]
theorem point_links_checked48406 : (cuts48406.take 1).map (fun c => (6348603393-1+2*2^10*c.k,111253382167125+c.lower,111253769058992+c.upper)) = pointBounds48406 := by
 decide +kernel
def cuts48407 : List PrefixCut := [⟨48,193922395,193922505⟩,
⟨64,258252175,258252323⟩]
theorem checked48407 : checkPrefixCuts (2^48) 6348734465 10 Manual.Count131072.C048407.packed 64 cuts48407 = true := by
 decide +kernel
def pointBounds48407 : List (Nat × Nat × Nat) := [(6348832768,111253835322420,111254222214545)]
theorem point_links_checked48407 : (cuts48407.take 1).map (fun c => (6348734465-1+2*2^10*c.k,111253641400025+c.lower,111254028292040+c.upper)) = pointBounds48407 := by
 decide +kernel
def cuts48408 : List PrefixCut := [⟨64,261704891,261705039⟩]
theorem checked48408 : checkPrefixCuts (2^48) 6348865537 10 Manual.Count131072.C048408.packed 64 cuts48408 = true := by
 decide +kernel
def cuts48409 : List PrefixCut := [⟨17,68539807,68539847⟩,
⟨64,257709483,257709633⟩]
theorem checked48409 : checkPrefixCuts (2^48) 6348996609 10 Manual.Count131072.C048409.packed 64 cuts48409 = true := by
 decide +kernel
def pointBounds48409 : List (Nat × Nat × Nat) := [(6349031424,111254229896898,111254616789249)]
theorem point_links_checked48409 : (cuts48409.take 1).map (fun c => (6348996609-1+2*2^10*c.k,111254161357091+c.lower,111254548249402+c.upper)) = pointBounds48409 := by
 decide +kernel
def cuts48410 : List PrefixCut := [⟨50,203840783,203840900⟩,
⟨64,259965129,259965279⟩]
theorem checked48410 : checkPrefixCuts (2^48) 6349127681 10 Manual.Count131072.C048410.packed 64 cuts48410 = true := by
 decide +kernel
def pointBounds48410 : List (Nat × Nat × Nat) := [(6349230080,111254622907357,111255009799935)]
theorem point_links_checked48410 : (cuts48410.take 1).map (fun c => (6349127681-1+2*2^10*c.k,111254419066574+c.lower,111254805959035+c.upper)) = pointBounds48410 := by
 decide +kernel
def cuts48411 : List PrefixCut := [⟨64,258408138,258408281⟩]
theorem checked48411 : checkPrefixCuts (2^48) 6349258753 10 Manual.Count131072.C048411.packed 64 cuts48411 = true := by
 decide +kernel
def cuts48412 : List PrefixCut := [⟨19,76116114,76116161⟩,
⟨64,258314158,258314312⟩]
theorem checked48412 : checkPrefixCuts (2^48) 6349389825 10 Manual.Count131072.C048412.packed 64 cuts48412 = true := by
 decide +kernel
def pointBounds48412 : List (Nat × Nat × Nat) := [(6349428736,111255013555955,111255400448756)]
theorem point_links_checked48412 : (cuts48412.take 1).map (fun c => (6349389825-1+2*2^10*c.k,111254937439841+c.lower,111255324332595+c.upper)) = pointBounds48412 := by
 decide +kernel
def cuts48413 : List PrefixCut := [⟨52,207330144,207330262⟩,
⟨64,256934599,256934744⟩]
theorem checked48413 : checkPrefixCuts (2^48) 6349520897 10 Manual.Count131072.C048413.packed 64 cuts48413 = true := by
 decide +kernel
def pointBounds48413 : List (Nat × Nat × Nat) := [(6349627392,111255403084143,111255789977169)]
theorem point_links_checked48413 : (cuts48413.take 1).map (fun c => (6349520897-1+2*2^10*c.k,111255195753999+c.lower,111255582646907+c.upper)) = pointBounds48413 := by
 decide +kernel
def cuts48414 : List PrefixCut := [⟨64,258613801,258613958⟩]
theorem checked48414 : checkPrefixCuts (2^48) 6349651969 10 Manual.Count131072.C048414.packed 64 cuts48414 = true := by
 decide +kernel
def cuts48415 : List PrefixCut := [⟨21,83115226,83115273⟩,
⟨64,255328177,255328319⟩]
theorem checked48415 : checkPrefixCuts (2^48) 6349783041 10 Manual.Count131072.C048415.packed 64 cuts48415 = true := by
 decide +kernel
def pointBounds48415 : List (Nat × Nat × Nat) := [(6349826048,111255794417625,111256181310882)]
theorem point_links_checked48415 : (cuts48415.take 1).map (fun c => (6349783041-1+2*2^10*c.k,111255711302399+c.lower,111256098195609+c.upper)) = pointBounds48415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000262
