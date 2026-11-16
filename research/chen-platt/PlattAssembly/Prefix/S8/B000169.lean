import PlattAssemblyKernel
import PlattCertificates.Count131072.C075408
import PlattCertificates.Count131072.C075409
import PlattCertificates.Count131072.C075410
import PlattCertificates.Count131072.C075411
import PlattCertificates.Count131072.C075412
import PlattCertificates.Count131072.C075413
import PlattCertificates.Count131072.C075414
import PlattCertificates.Count131072.C075415
import PlattCertificates.Count131072.C075416
import PlattCertificates.Count131072.C075417
import PlattCertificates.Count131072.C075418
import PlattCertificates.Count131072.C075419
import PlattCertificates.Count131072.C075420
import PlattCertificates.Count131072.C075421
import PlattCertificates.Count131072.C075422
import PlattCertificates.Count131072.C075423
import PlattCertificates.Count131072.C075424
import PlattCertificates.Count131072.C075425
import PlattCertificates.Count131072.C075426
import PlattCertificates.Count131072.C075427
import PlattCertificates.Count131072.C075428
import PlattCertificates.Count131072.C075429
import PlattCertificates.Count131072.C075430
import PlattCertificates.Count131072.C075431
import PlattCertificates.Count131072.C075432
import PlattCertificates.Count131072.C075433
import PlattCertificates.Count131072.C075434
import PlattCertificates.Count131072.C075435
import PlattCertificates.Count131072.C075436
import PlattCertificates.Count131072.C075437
import PlattCertificates.Count131072.C075438
import PlattCertificates.Count131072.C075439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000169
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75408 : List PrefixCut := [⟨64,161918423,161918524⟩]
theorem checked75408 : checkPrefixCuts (2^48) 9887809537 10 Manual.Count131072.C075408.packed 64 cuts75408 = true := by
 decide +kernel
def cuts75409 : List PrefixCut := [⟨21,53431470,53431504⟩,
⟨64,163140332,163140433⟩]
theorem checked75409 : checkPrefixCuts (2^48) 9887940609 10 Manual.Count131072.C075409.packed 64 cuts75409 = true := by
 decide +kernel
def pointBounds75409 : List (Nat × Nat × Nat) := [(9887983616,116725278024322,116725668071635)]
theorem point_links_checked75409 : (cuts75409.take 1).map (fun c => (9887940609-1+2*2^10*c.k,116725224592852+c.lower,116725614640131+c.upper)) = pointBounds75409 := by
 decide +kernel
def cuts75410 : List PrefixCut := [⟨64,158896750,158896850⟩]
theorem checked75410 : checkPrefixCuts (2^48) 9888071681 10 Manual.Count131072.C075410.packed 64 cuts75410 = true := by
 decide +kernel
def cuts75411 : List PrefixCut := [⟨44,111044291,111044367⟩,
⟨64,160716433,160716537⟩]
theorem checked75411 : checkPrefixCuts (2^48) 9888202753 10 Manual.Count131072.C075411.packed 64 cuts75411 = true := by
 decide +kernel
def pointBounds75411 : List (Nat × Nat × Nat) := [(9888292864,116725657674225,116726047721781)]
theorem point_links_checked75411 : (cuts75411.take 1).map (fun c => (9888202753-1+2*2^10*c.k,116725546629934+c.lower,116725936677414+c.upper)) = pointBounds75411 := by
 decide +kernel
def cuts75412 : List PrefixCut := [⟨64,164073198,164073292⟩]
theorem checked75412 : checkPrefixCuts (2^48) 9888333825 10 Manual.Count131072.C075412.packed 64 cuts75412 = true := by
 decide +kernel
def cuts75413 : List PrefixCut := [⟨64,160171344,160171440⟩]
theorem checked75413 : checkPrefixCuts (2^48) 9888464897 10 Manual.Count131072.C075413.packed 64 cuts75413 = true := by
 decide +kernel
def cuts75414 : List PrefixCut := [⟨3,7856226,7856230⟩,
⟨64,161507048,161507143⟩]
theorem checked75414 : checkPrefixCuts (2^48) 9888595969 10 Manual.Count131072.C075414.packed 64 cuts75414 = true := by
 decide +kernel
def pointBounds75414 : List (Nat × Nat × Nat) := [(9888602112,116726039447135,116726429494913)]
theorem point_links_checked75414 : (cuts75414.take 1).map (fun c => (9888595969-1+2*2^10*c.k,116726031590909+c.lower,116726421638683+c.upper)) = pointBounds75414 := by
 decide +kernel
def cuts75415 : List PrefixCut := [⟨64,161277193,161277291⟩]
theorem checked75415 : checkPrefixCuts (2^48) 9888727041 10 Manual.Count131072.C075415.packed 64 cuts75415 = true := by
 decide +kernel
def cuts75416 : List PrefixCut := [⟨26,64157328,64157365⟩,
⟨64,160392684,160392780⟩]
theorem checked75416 : checkPrefixCuts (2^48) 9888858113 10 Manual.Count131072.C075416.packed 64 cuts75416 = true := by
 decide +kernel
def pointBounds75416 : List (Nat × Nat × Nat) := [(9888911360,116726418532478,116726808580482)]
theorem point_links_checked75416 : (cuts75416.take 1).map (fun c => (9888858113-1+2*2^10*c.k,116726354375150+c.lower,116726744423117+c.upper)) = pointBounds75416 := by
 decide +kernel
def cuts75417 : List PrefixCut := [⟨64,164432341,164432440⟩]
theorem checked75417 : checkPrefixCuts (2^48) 9888989185 10 Manual.Count131072.C075417.packed 64 cuts75417 = true := by
 decide +kernel
def cuts75418 : List PrefixCut := [⟨49,122703752,122703823⟩,
⟨64,160246124,160246218⟩]
theorem checked75418 : checkPrefixCuts (2^48) 9889120257 10 Manual.Count131072.C075418.packed 64 cuts75418 = true := by
 decide +kernel
def pointBounds75418 : List (Nat × Nat × Nat) := [(9889220608,116726801903927,116727191952160)]
theorem point_links_checked75418 : (cuts75418.take 1).map (fun c => (9889120257-1+2*2^10*c.k,116726679200175+c.lower,116727069248337+c.upper)) = pointBounds75418 := by
 decide +kernel
def cuts75419 : List PrefixCut := [⟨64,161809441,161809534⟩]
theorem checked75419 : checkPrefixCuts (2^48) 9889251329 10 Manual.Count131072.C075419.packed 64 cuts75419 = true := by
 decide +kernel
def cuts75420 : List PrefixCut := [⟨64,160298788,160298887⟩]
theorem checked75420 : checkPrefixCuts (2^48) 9889382401 10 Manual.Count131072.C075420.packed 64 cuts75420 = true := by
 decide +kernel
def cuts75421 : List PrefixCut := [⟨8,20350283,20350292⟩,
⟨64,164850550,164850644⟩]
theorem checked75421 : checkPrefixCuts (2^48) 9889513473 10 Manual.Count131072.C075421.packed 64 cuts75421 = true := by
 decide +kernel
def pointBounds75421 : List (Nat × Nat × Nat) := [(9889529856,116727181904811,116727571953268)]
theorem point_links_checked75421 : (cuts75421.take 1).map (fun c => (9889513473-1+2*2^10*c.k,116727161554528+c.lower,116727551602976+c.upper)) = pointBounds75421 := by
 decide +kernel
def cuts75422 : List PrefixCut := [⟨64,161034527,161034628⟩]
theorem checked75422 : checkPrefixCuts (2^48) 9889644545 10 Manual.Count131072.C075422.packed 64 cuts75422 = true := by
 decide +kernel
def cuts75423 : List PrefixCut := [⟨31,78381897,78381942⟩,
⟨64,161630088,161630181⟩]
theorem checked75423 : checkPrefixCuts (2^48) 9889775617 10 Manual.Count131072.C075423.packed 64 cuts75423 = true := by
 decide +kernel
def pointBounds75423 : List (Nat × Nat × Nat) := [(9889839104,116727565821502,116727955870190)]
theorem point_links_checked75423 : (cuts75423.take 1).map (fun c => (9889775617-1+2*2^10*c.k,116727487439605+c.lower,116727877488248+c.upper)) = pointBounds75423 := by
 decide +kernel
def cuts75424 : List PrefixCut := [⟨64,163050963,163051062⟩]
theorem checked75424 : checkPrefixCuts (2^48) 9889906689 10 Manual.Count131072.C075424.packed 64 cuts75424 = true := by
 decide +kernel
def cuts75425 : List PrefixCut := [⟨54,137150121,137150208⟩,
⟨64,160885843,160885944⟩]
theorem checked75425 : checkPrefixCuts (2^48) 9890037761 10 Manual.Count131072.C075425.packed 64 cuts75425 = true := by
 decide +kernel
def pointBounds75425 : List (Nat × Nat × Nat) := [(9890148352,116727949270777,116728339319699)]
theorem point_links_checked75425 : (cuts75425.take 1).map (fun c => (9890037761-1+2*2^10*c.k,116727812120656+c.lower,116728202169491+c.upper)) = pointBounds75425 := by
 decide +kernel
def cuts75426 : List PrefixCut := [⟨64,162249782,162249878⟩]
theorem checked75426 : checkPrefixCuts (2^48) 9890168833 10 Manual.Count131072.C075426.packed 64 cuts75426 = true := by
 decide +kernel
def cuts75427 : List PrefixCut := [⟨64,160227013,160227113⟩]
theorem checked75427 : checkPrefixCuts (2^48) 9890299905 10 Manual.Count131072.C075427.packed 64 cuts75427 = true := by
 decide +kernel
def cuts75428 : List PrefixCut := [⟨13,33439652,33439671⟩,
⟨64,161192501,161192598⟩]
theorem checked75428 : checkPrefixCuts (2^48) 9890430977 10 Manual.Count131072.C075428.packed 64 cuts75428 = true := by
 decide +kernel
def pointBounds75428 : List (Nat × Nat × Nat) := [(9890457600,116728328922946,116728718972097)]
theorem point_links_checked75428 : (cuts75428.take 1).map (fun c => (9890430977-1+2*2^10*c.k,116728295483294+c.lower,116728685532426+c.upper)) = pointBounds75428 := by
 decide +kernel
def cuts75429 : List PrefixCut := [⟨64,162471006,162471104⟩]
theorem checked75429 : checkPrefixCuts (2^48) 9890562049 10 Manual.Count131072.C075429.packed 64 cuts75429 = true := by
 decide +kernel
def cuts75430 : List PrefixCut := [⟨36,90896305,90896359⟩,
⟨64,162041971,162042065⟩]
theorem checked75430 : checkPrefixCuts (2^48) 9890693121 10 Manual.Count131072.C075430.packed 64 cuts75430 = true := by
 decide +kernel
def pointBounds75430 : List (Nat × Nat × Nat) := [(9890766848,116728710043106,116729100092487)]
theorem point_links_checked75430 : (cuts75430.take 1).map (fun c => (9890693121-1+2*2^10*c.k,116728619146801+c.lower,116729009196128+c.upper)) = pointBounds75430 := by
 decide +kernel
def cuts75431 : List PrefixCut := [⟨64,162324402,162324498⟩]
theorem checked75431 : checkPrefixCuts (2^48) 9890824193 10 Manual.Count131072.C075431.packed 64 cuts75431 = true := by
 decide +kernel
def cuts75432 : List PrefixCut := [⟨59,150398594,150398689⟩,
⟨64,162720667,162720770⟩]
theorem checked75432 : checkPrefixCuts (2^48) 9890955265 10 Manual.Count131072.C075432.packed 64 cuts75432 = true := by
 decide +kernel
def pointBounds75432 : List (Nat × Nat × Nat) := [(9891076096,116729093911768,116729483961380)]
theorem point_links_checked75432 : (cuts75432.take 1).map (fun c => (9890955265-1+2*2^10*c.k,116728943513174+c.lower,116729333562691+c.upper)) = pointBounds75432 := by
 decide +kernel
def cuts75433 : List PrefixCut := [⟨64,159844328,159844415⟩]
theorem checked75433 : checkPrefixCuts (2^48) 9891086337 10 Manual.Count131072.C075433.packed 64 cuts75433 = true := by
 decide +kernel
def cuts75434 : List PrefixCut := [⟨64,160895104,160895209⟩]
theorem checked75434 : checkPrefixCuts (2^48) 9891217409 10 Manual.Count131072.C075434.packed 64 cuts75434 = true := by
 decide +kernel
def cuts75435 : List PrefixCut := [⟨18,45872075,45872105⟩,
⟨64,162657277,162657371⟩]
theorem checked75435 : checkPrefixCuts (2^48) 9891348481 10 Manual.Count131072.C075435.packed 64 cuts75435 = true := by
 decide +kernel
def pointBounds75435 : List (Nat × Nat × Nat) := [(9891385344,116729472845348,116729862895190)]
theorem point_links_checked75435 : (cuts75435.take 1).map (fun c => (9891348481-1+2*2^10*c.k,116729426973273+c.lower,116729817023085+c.upper)) = pointBounds75435 := by
 decide +kernel
def cuts75436 : List PrefixCut := [⟨64,162342098,162342195⟩]
theorem checked75436 : checkPrefixCuts (2^48) 9891479553 10 Manual.Count131072.C075436.packed 64 cuts75436 = true := by
 decide +kernel
def cuts75437 : List PrefixCut := [⟨41,103323008,103323070⟩,
⟨64,161400910,161401007⟩]
theorem checked75437 : checkPrefixCuts (2^48) 9891610625 10 Manual.Count131072.C075437.packed 64 cuts75437 = true := by
 decide +kernel
def pointBounds75437 : List (Nat × Nat × Nat) := [(9891694592,116729855295656,116730245345721)]
theorem point_links_checked75437 : (cuts75437.take 1).map (fun c => (9891610625-1+2*2^10*c.k,116729751972648+c.lower,116730142022651+c.upper)) = pointBounds75437 := by
 decide +kernel
def cuts75438 : List PrefixCut := [⟨64,161711778,161711877⟩]
theorem checked75438 : checkPrefixCuts (2^48) 9891741697 10 Manual.Count131072.C075438.packed 64 cuts75438 = true := by
 decide +kernel
def cuts75439 : List PrefixCut := [⟨64,163929138,163929240⟩]
theorem checked75439 : checkPrefixCuts (2^48) 9891872769 10 Manual.Count131072.C075439.packed 64 cuts75439 = true := by
 decide +kernel
def pointBounds75439 : List (Nat × Nat × Nat) := [(9892003840,116730239014474,116730629064775)]
theorem point_links_checked75439 : (cuts75439.take 1).map (fun c => (9891872769-1+2*2^10*c.k,116730075085336+c.lower,116730465135535+c.upper)) = pointBounds75439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000169
