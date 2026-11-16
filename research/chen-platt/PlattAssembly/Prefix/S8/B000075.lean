import PlattAssemblyKernel
import PlattCertificates.Count131072.C072400
import PlattCertificates.Count131072.C072401
import PlattCertificates.Count131072.C072402
import PlattCertificates.Count131072.C072403
import PlattCertificates.Count131072.C072404
import PlattCertificates.Count131072.C072405
import PlattCertificates.Count131072.C072406
import PlattCertificates.Count131072.C072407
import PlattCertificates.Count131072.C072408
import PlattCertificates.Count131072.C072409
import PlattCertificates.Count131072.C072410
import PlattCertificates.Count131072.C072411
import PlattCertificates.Count131072.C072412
import PlattCertificates.Count131072.C072413
import PlattCertificates.Count131072.C072414
import PlattCertificates.Count131072.C072415
import PlattCertificates.Count131072.C072416
import PlattCertificates.Count131072.C072417
import PlattCertificates.Count131072.C072418
import PlattCertificates.Count131072.C072419
import PlattCertificates.Count131072.C072420
import PlattCertificates.Count131072.C072421
import PlattCertificates.Count131072.C072422
import PlattCertificates.Count131072.C072423
import PlattCertificates.Count131072.C072424
import PlattCertificates.Count131072.C072425
import PlattCertificates.Count131072.C072426
import PlattCertificates.Count131072.C072427
import PlattCertificates.Count131072.C072428
import PlattCertificates.Count131072.C072429
import PlattCertificates.Count131072.C072430
import PlattCertificates.Count131072.C072431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72400 : List PrefixCut := [⟨43,110353372,110353446⟩,
⟨64,166656330,166656436⟩]
theorem checked72400 : checkPrefixCuts (2^48) 9493544961 10 Manual.Count131072.C072400.packed 64 cuts72400 = true := by
 decide +kernel
def pointBounds72400 : List (Nat × Nat × Nat) := [(9493633024,116227015116827,116227404866421)]
theorem point_links_checked72400 : (cuts72400.take 1).map (fun c => (9493544961-1+2*2^10*c.k,116226904763455+c.lower,116227294512975+c.upper)) = pointBounds72400 := by
 decide +kernel
def cuts72401 : List PrefixCut := [⟨64,169648542,169648642⟩]
theorem checked72401 : checkPrefixCuts (2^48) 9493676033 10 Manual.Count131072.C072401.packed 64 cuts72401 = true := by
 decide +kernel
def cuts72402 : List PrefixCut := [⟨60,159061889,159061982⟩,
⟨64,169972304,169972404⟩]
theorem checked72402 : checkPrefixCuts (2^48) 9493807105 10 Manual.Count131072.C072402.packed 64 cuts72402 = true := by
 decide +kernel
def pointBounds72402 : List (Nat × Nat × Nat) := [(9493929984,116227400130216,116227789880035)]
theorem point_links_checked72402 : (cuts72402.take 1).map (fun c => (9493807105-1+2*2^10*c.k,116227241068327+c.lower,116227630818053+c.upper)) = pointBounds72402 := by
 decide +kernel
def cuts72403 : List PrefixCut := [⟨64,173527695,173527792⟩]
theorem checked72403 : checkPrefixCuts (2^48) 9493938177 10 Manual.Count131072.C072403.packed 64 cuts72403 = true := by
 decide +kernel
def cuts72404 : List PrefixCut := [⟨64,168010909,168011010⟩]
theorem checked72404 : checkPrefixCuts (2^48) 9494069249 10 Manual.Count131072.C072404.packed 64 cuts72404 = true := by
 decide +kernel
def cuts72405 : List PrefixCut := [⟨13,34390512,34390534⟩,
⟨64,171299385,171299489⟩]
theorem checked72405 : checkPrefixCuts (2^48) 9494200321 10 Manual.Count131072.C072405.packed 64 cuts72405 = true := by
 decide +kernel
def pointBounds72405 : List (Nat × Nat × Nat) := [(9494226944,116227786969747,116228176719793)]
theorem point_links_checked72405 : (cuts72405.take 1).map (fun c => (9494200321-1+2*2^10*c.k,116227752579235+c.lower,116228142329259+c.upper)) = pointBounds72405 := by
 decide +kernel
def cuts72406 : List PrefixCut := [⟨64,170615153,170615254⟩]
theorem checked72406 : checkPrefixCuts (2^48) 9494331393 10 Manual.Count131072.C072406.packed 64 cuts72406 = true := by
 decide +kernel
def cuts72407 : List PrefixCut := [⟨30,79659131,79659175⟩,
⟨64,171057490,171057587⟩]
theorem checked72407 : checkPrefixCuts (2^48) 9494462465 10 Manual.Count131072.C072407.packed 64 cuts72407 = true := by
 decide +kernel
def pointBounds72407 : List (Nat × Nat × Nat) := [(9494523904,116228174152904,116228563903177)]
theorem point_links_checked72407 : (cuts72407.take 1).map (fun c => (9494462465-1+2*2^10*c.k,116228094493773+c.lower,116228484244002+c.upper)) = pointBounds72407 := by
 decide +kernel
def cuts72408 : List PrefixCut := [⟨64,169543204,169543307⟩]
theorem checked72408 : checkPrefixCuts (2^48) 9494593537 10 Manual.Count131072.C072408.packed 64 cuts72408 = true := by
 decide +kernel
def cuts72409 : List PrefixCut := [⟨47,123057432,123057499⟩,
⟨64,168443992,168444086⟩]
theorem checked72409 : checkPrefixCuts (2^48) 9494724609 10 Manual.Count131072.C072409.packed 64 cuts72409 = true := by
 decide +kernel
def pointBounds72409 : List (Nat × Nat × Nat) := [(9494820864,116228558151899,116228947902395)]
theorem point_links_checked72409 : (cuts72409.take 1).map (fun c => (9494724609-1+2*2^10*c.k,116228435094467+c.lower,116228824844896+c.upper)) = pointBounds72409 := by
 decide +kernel
def cuts72410 : List PrefixCut := [⟨64,168263797,168263896⟩]
theorem checked72410 : checkPrefixCuts (2^48) 9494855681 10 Manual.Count131072.C072410.packed 64 cuts72410 = true := by
 decide +kernel
def cuts72411 : List PrefixCut := [⟨64,172382042,172382145⟩]
theorem checked72411 : checkPrefixCuts (2^48) 9494986753 10 Manual.Count131072.C072411.packed 64 cuts72411 = true := by
 decide +kernel
def pointBounds72411 : List (Nat × Nat × Nat) := [(9495117824,116228944184298,116229333935023)]
theorem point_links_checked72411 : (cuts72411.take 1).map (fun c => (9494986753-1+2*2^10*c.k,116228771802256+c.lower,116229161552878+c.upper)) = pointBounds72411 := by
 decide +kernel
def cuts72412 : List PrefixCut := [⟨64,168733453,168733551⟩]
theorem checked72412 : checkPrefixCuts (2^48) 9495117825 10 Manual.Count131072.C072412.packed 64 cuts72412 = true := by
 decide +kernel
def cuts72413 : List PrefixCut := [⟨64,165826050,165826153⟩]
theorem checked72413 : checkPrefixCuts (2^48) 9495248897 10 Manual.Count131072.C072413.packed 64 cuts72413 = true := by
 decide +kernel
def cuts72414 : List PrefixCut := [⟨17,45146741,45146771⟩,
⟨64,168669514,168669621⟩]
theorem checked72414 : checkPrefixCuts (2^48) 9495379969 10 Manual.Count131072.C072414.packed 64 cuts72414 = true := by
 decide +kernel
def pointBounds72414 : List (Nat × Nat × Nat) := [(9495414784,116229323890542,116229713641498)]
theorem point_links_checked72414 : (cuts72414.take 1).map (fun c => (9495379969-1+2*2^10*c.k,116229278743801+c.lower,116229668494727+c.upper)) = pointBounds72414 := by
 decide +kernel
def cuts72415 : List PrefixCut := [⟨64,169200750,169200850⟩]
theorem checked72415 : checkPrefixCuts (2^48) 9495511041 10 Manual.Count131072.C072415.packed 64 cuts72415 = true := by
 decide +kernel
def cuts72416 : List PrefixCut := [⟨34,89786906,89786958⟩,
⟨64,169346629,169346725⟩]
theorem checked72416 : checkPrefixCuts (2^48) 9495642113 10 Manual.Count131072.C072416.packed 64 cuts72416 = true := by
 decide +kernel
def pointBounds72416 : List (Nat × Nat × Nat) := [(9495711744,116229706400971,116230096152156)]
theorem point_links_checked72416 : (cuts72416.take 1).map (fun c => (9495642113-1+2*2^10*c.k,116229616614065+c.lower,116230006365198+c.upper)) = pointBounds72416 := by
 decide +kernel
def cuts72417 : List PrefixCut := [⟨64,166202255,166202346⟩]
theorem checked72417 : checkPrefixCuts (2^48) 9495773185 10 Manual.Count131072.C072417.packed 64 cuts72417 = true := by
 decide +kernel
def cuts72418 : List PrefixCut := [⟨51,134068746,134068830⟩,
⟨64,169608720,169608828⟩]
theorem checked72418 : checkPrefixCuts (2^48) 9495904257 10 Manual.Count131072.C072418.packed 64 cuts72418 = true := by
 decide +kernel
def pointBounds72418 : List (Nat × Nat × Nat) := [(9496008704,116230086231695,116230475983099)]
theorem point_links_checked72418 : (cuts72418.take 1).map (fun c => (9495904257-1+2*2^10*c.k,116229952162949+c.lower,116230341914269+c.upper)) = pointBounds72418 := by
 decide +kernel
def cuts72419 : List PrefixCut := [⟨64,170199208,170199303⟩]
theorem checked72419 : checkPrefixCuts (2^48) 9496035329 10 Manual.Count131072.C072419.packed 64 cuts72419 = true := by
 decide +kernel
def cuts72420 : List PrefixCut := [⟨64,168714824,168714920⟩]
theorem checked72420 : checkPrefixCuts (2^48) 9496166401 10 Manual.Count131072.C072420.packed 64 cuts72420 = true := by
 decide +kernel
def cuts72421 : List PrefixCut := [⟨4,10789134,10789140⟩,
⟨64,168445732,168445833⟩]
theorem checked72421 : checkPrefixCuts (2^48) 9496297473 10 Manual.Count131072.C072421.packed 64 cuts72421 = true := by
 decide +kernel
def pointBounds72421 : List (Nat × Nat × Nat) := [(9496305664,116230471474835,116230861226460)]
theorem point_links_checked72421 : (cuts72421.take 1).map (fun c => (9496297473-1+2*2^10*c.k,116230460685701+c.lower,116230850437320+c.upper)) = pointBounds72421 := by
 decide +kernel
def cuts72422 : List PrefixCut := [⟨64,167732057,167732164⟩]
theorem checked72422 : checkPrefixCuts (2^48) 9496428545 10 Manual.Count131072.C072422.packed 64 cuts72422 = true := by
 decide +kernel
def cuts72423 : List PrefixCut := [⟨21,55989212,55989241⟩,
⟨64,171375391,171375486⟩]
theorem checked72423 : checkPrefixCuts (2^48) 9496559617 10 Manual.Count131072.C072423.packed 64 cuts72423 = true := by
 decide +kernel
def pointBounds72423 : List (Nat × Nat × Nat) := [(9496602624,116230852852702,116231242604558)]
theorem point_links_checked72423 : (cuts72423.take 1).map (fun c => (9496559617-1+2*2^10*c.k,116230796863490+c.lower,116231186615317+c.upper)) = pointBounds72423 := by
 decide +kernel
def cuts72424 : List PrefixCut := [⟨64,170424568,170424667⟩]
theorem checked72424 : checkPrefixCuts (2^48) 9496690689 10 Manual.Count131072.C072424.packed 64 cuts72424 = true := by
 decide +kernel
def cuts72425 : List PrefixCut := [⟨38,100742039,100742102⟩,
⟨64,169621973,169622078⟩]
theorem checked72425 : checkPrefixCuts (2^48) 9496821761 10 Manual.Count131072.C072425.packed 64 cuts72425 = true := by
 decide +kernel
def pointBounds72425 : List (Nat × Nat × Nat) := [(9496899584,116231239405488,116231629157572)]
theorem point_links_checked72425 : (cuts72425.take 1).map (fun c => (9496821761-1+2*2^10*c.k,116231138663449+c.lower,116231528415470+c.upper)) = pointBounds72425 := by
 decide +kernel
def cuts72426 : List PrefixCut := [⟨64,168641579,168641682⟩]
theorem checked72426 : checkPrefixCuts (2^48) 9496952833 10 Manual.Count131072.C072426.packed 64 cuts72426 = true := by
 decide +kernel
def cuts72427 : List PrefixCut := [⟨55,145018048,145018139⟩,
⟨64,168609619,168609726⟩]
theorem checked72427 : checkPrefixCuts (2^48) 9497083905 10 Manual.Count131072.C072427.packed 64 cuts72427 = true := by
 decide +kernel
def pointBounds72427 : List (Nat × Nat × Nat) := [(9497196544,116231621945049,116232011697369)]
theorem point_links_checked72427 : (cuts72427.take 1).map (fun c => (9497083905-1+2*2^10*c.k,116231476927001+c.lower,116231866679230+c.upper)) = pointBounds72427 := by
 decide +kernel
def cuts72428 : List PrefixCut := [⟨64,170266981,170267084⟩]
theorem checked72428 : checkPrefixCuts (2^48) 9497214977 10 Manual.Count131072.C072428.packed 64 cuts72428 = true := by
 decide +kernel
def cuts72429 : List PrefixCut := [⟨64,170649908,170650001⟩]
theorem checked72429 : checkPrefixCuts (2^48) 9497346049 10 Manual.Count131072.C072429.packed 64 cuts72429 = true := by
 decide +kernel
def cuts72430 : List PrefixCut := [⟨8,21338481,21338496⟩,
⟨64,166972613,166972721⟩]
theorem checked72430 : checkPrefixCuts (2^48) 9497477121 10 Manual.Count131072.C072430.packed 64 cuts72430 = true := by
 decide +kernel
def pointBounds72430 : List (Nat × Nat × Nat) := [(9497493504,116232007791990,116232397544537)]
theorem point_links_checked72430 : (cuts72430.take 1).map (fun c => (9497477121-1+2*2^10*c.k,116231986453509+c.lower,116232376206041+c.upper)) = pointBounds72430 := by
 decide +kernel
def cuts72431 : List PrefixCut := [⟨64,168926300,168926405⟩]
theorem checked72431 : checkPrefixCuts (2^48) 9497608193 10 Manual.Count131072.C072431.packed 64 cuts72431 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000075
