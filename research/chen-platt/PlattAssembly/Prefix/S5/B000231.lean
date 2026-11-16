import PlattAssemblyKernel
import PlattCertificates.Count131072.C047392
import PlattCertificates.Count131072.C047393
import PlattCertificates.Count131072.C047394
import PlattCertificates.Count131072.C047395
import PlattCertificates.Count131072.C047396
import PlattCertificates.Count131072.C047397
import PlattCertificates.Count131072.C047398
import PlattCertificates.Count131072.C047399
import PlattCertificates.Count131072.C047400
import PlattCertificates.Count131072.C047401
import PlattCertificates.Count131072.C047402
import PlattCertificates.Count131072.C047403
import PlattCertificates.Count131072.C047404
import PlattCertificates.Count131072.C047405
import PlattCertificates.Count131072.C047406
import PlattCertificates.Count131072.C047407
import PlattCertificates.Count131072.C047408
import PlattCertificates.Count131072.C047409
import PlattCertificates.Count131072.C047410
import PlattCertificates.Count131072.C047411
import PlattCertificates.Count131072.C047412
import PlattCertificates.Count131072.C047413
import PlattCertificates.Count131072.C047414
import PlattCertificates.Count131072.C047415
import PlattCertificates.Count131072.C047416
import PlattCertificates.Count131072.C047417
import PlattCertificates.Count131072.C047418
import PlattCertificates.Count131072.C047419
import PlattCertificates.Count131072.C047420
import PlattCertificates.Count131072.C047421
import PlattCertificates.Count131072.C047422
import PlattCertificates.Count131072.C047423
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000231
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47392 : List PrefixCut := [⟨64,262919215,262919368⟩]
theorem checked47392 : checkPrefixCuts (2^48) 6215696385 10 Manual.Count131072.C047392.packed 64 cuts47392 = true := by
 decide +kernel
def cuts47393 : List PrefixCut := [⟨4,17343597,17343607⟩,
⟨64,264498604,264498762⟩]
theorem checked47393 : checkPrefixCuts (2^48) 6215827457 10 Manual.Count131072.C047393.packed 64 cuts47393 = true := by
 decide +kernel
def pointBounds47393 : List (Nat × Nat × Nat) := [(6215835648,110989730386356,110990117127319)]
theorem point_links_checked47393 : (cuts47393.take 1).map (fun c => (6215827457-1+2*2^10*c.k,110989713042759+c.lower,110990099783712+c.upper)) = pointBounds47393 := by
 decide +kernel
def cuts47394 : List PrefixCut := [⟨35,144269589,144269669⟩,
⟨64,262908119,262908266⟩]
theorem checked47394 : checkPrefixCuts (2^48) 6215958529 10 Manual.Count131072.C047394.packed 64 cuts47394 = true := by
 decide +kernel
def pointBounds47394 : List (Nat × Nat × Nat) := [(6216030208,110990121810952,110990508552143)]
theorem point_links_checked47394 : (cuts47394.take 1).map (fun c => (6215958529-1+2*2^10*c.k,110989977541363+c.lower,110990364282474+c.upper)) = pointBounds47394 := by
 decide +kernel
def cuts47395 : List PrefixCut := [⟨64,261091309,261091464⟩]
theorem checked47395 : checkPrefixCuts (2^48) 6216089601 10 Manual.Count131072.C047395.packed 64 cuts47395 = true := by
 decide +kernel
def cuts47396 : List PrefixCut := [⟨2,8376929,8376933⟩,
⟨64,262897042,262897186⟩]
theorem checked47396 : checkPrefixCuts (2^48) 6216220673 10 Manual.Count131072.C047396.packed 64 cuts47396 = true := by
 decide +kernel
def pointBounds47396 : List (Nat × Nat × Nat) := [(6216224768,110990509917720,110990896659137)]
theorem point_links_checked47396 : (cuts47396.take 1).map (fun c => (6216220673-1+2*2^10*c.k,110990501540791+c.lower,110990888282204+c.upper)) = pointBounds47396 := by
 decide +kernel
def cuts47397 : List PrefixCut := [⟨33,135929089,135929170⟩,
⟨64,260491715,260491865⟩]
theorem checked47397 : checkPrefixCuts (2^48) 6216351745 10 Manual.Count131072.C047397.packed 64 cuts47397 = true := by
 decide +kernel
def pointBounds47397 : List (Nat × Nat × Nat) := [(6216419328,110990900366922,110991287108560)]
theorem point_links_checked47397 : (cuts47397.take 1).map (fun c => (6216351745-1+2*2^10*c.k,110990764437833+c.lower,110991151179390+c.upper)) = pointBounds47397 := by
 decide +kernel
def cuts47398 : List PrefixCut := [⟨64,259716466,259716616⟩]
theorem checked47398 : checkPrefixCuts (2^48) 6216482817 10 Manual.Count131072.C047398.packed 64 cuts47398 = true := by
 decide +kernel
def pointBounds47398 : List (Nat × Nat × Nat) := [(6216613888,110991284646014,110991671387871)]
theorem point_links_checked47398 : (cuts47398.take 1).map (fun c => (6216482817-1+2*2^10*c.k,110991024929548+c.lower,110991411671255+c.upper)) = pointBounds47398 := by
 decide +kernel
def cuts47399 : List PrefixCut := [⟨64,262699272,262699428⟩]
theorem checked47399 : checkPrefixCuts (2^48) 6216613889 10 Manual.Count131072.C047399.packed 64 cuts47399 = true := by
 decide +kernel
def cuts47400 : List PrefixCut := [⟨31,128676276,128676345⟩,
⟨64,264097341,264097488⟩]
theorem checked47400 : checkPrefixCuts (2^48) 6216744961 10 Manual.Count131072.C047400.packed 64 cuts47400 = true := by
 decide +kernel
def pointBounds47400 : List (Nat × Nat × Nat) := [(6216808448,110991676021562,110992062763644)]
theorem point_links_checked47400 : (cuts47400.take 1).map (fun c => (6216744961-1+2*2^10*c.k,110991547345286+c.lower,110991934087299+c.upper)) = pointBounds47400 := by
 decide +kernel
def cuts47401 : List PrefixCut := [⟨62,254629282,254629430⟩,
⟨64,262959882,262960035⟩]
theorem checked47401 : checkPrefixCuts (2^48) 6216876033 10 Manual.Count131072.C047401.packed 64 cuts47401 = true := by
 decide +kernel
def pointBounds47401 : List (Nat × Nat × Nat) := [(6217003008,110992066071909,110992452814217)]
theorem point_links_checked47401 : (cuts47401.take 1).map (fun c => (6216876033-1+2*2^10*c.k,110991811442627+c.lower,110992198184787+c.upper)) = pointBounds47401 := by
 decide +kernel
def cuts47402 : List PrefixCut := [⟨64,264448405,264448563⟩]
theorem checked47402 : checkPrefixCuts (2^48) 6217007105 10 Manual.Count131072.C047402.packed 64 cuts47402 = true := by
 decide +kernel
def cuts47403 : List PrefixCut := [⟨29,118617388,118617458⟩,
⟨64,259326920,259327072⟩]
theorem checked47403 : checkPrefixCuts (2^48) 6217138177 10 Manual.Count131072.C047403.packed 64 cuts47403 = true := by
 decide +kernel
def pointBounds47403 : List (Nat × Nat × Nat) := [(6217197568,110992457468302,110992844210843)]
theorem point_links_checked47403 : (cuts47403.take 1).map (fun c => (6217138177-1+2*2^10*c.k,110992338850914+c.lower,110992725593385+c.upper)) = pointBounds47403 := by
 decide +kernel
def cuts47404 : List PrefixCut := [⟨60,249180544,249180683⟩,
⟨64,264935253,264935400⟩]
theorem checked47404 : checkPrefixCuts (2^48) 6217269249 10 Manual.Count131072.C047404.packed 64 cuts47404 = true := by
 decide +kernel
def pointBounds47404 : List (Nat × Nat × Nat) := [(6217392128,110992847358378,110993234101140)]
theorem point_links_checked47404 : (cuts47404.take 1).map (fun c => (6217269249-1+2*2^10*c.k,110992598177834+c.lower,110992984920457+c.upper)) = pointBounds47404 := by
 decide +kernel
def cuts47405 : List PrefixCut := [⟨64,260311967,260312113⟩]
theorem checked47405 : checkPrefixCuts (2^48) 6217400321 10 Manual.Count131072.C047405.packed 64 cuts47405 = true := by
 decide +kernel
def cuts47406 : List PrefixCut := [⟨27,111230759,111230824⟩,
⟨64,265195698,265195854⟩]
theorem checked47406 : checkPrefixCuts (2^48) 6217531393 10 Manual.Count131072.C047406.packed 64 cuts47406 = true := by
 decide +kernel
def pointBounds47406 : List (Nat × Nat × Nat) := [(6217586688,110993234655813,110993621398794)]
theorem point_links_checked47406 : (cuts47406.take 1).map (fun c => (6217531393-1+2*2^10*c.k,110993123425054+c.lower,110993510167970+c.upper)) = pointBounds47406 := by
 decide +kernel
def cuts47407 : List PrefixCut := [⟨58,234723808,234723946⟩,
⟨64,259984078,259984232⟩]
theorem checked47407 : checkPrefixCuts (2^48) 6217662465 10 Manual.Count131072.C047407.packed 64 cuts47407 = true := by
 decide +kernel
def pointBounds47407 : List (Nat × Nat × Nat) := [(6217781248,110993623344560,110994010087770)]
theorem point_links_checked47407 : (cuts47407.take 1).map (fun c => (6217662465-1+2*2^10*c.k,110993388620752+c.lower,110993775363824+c.upper)) = pointBounds47407 := by
 decide +kernel
def cuts47408 : List PrefixCut := [⟨64,266904746,266904889⟩]
theorem checked47408 : checkPrefixCuts (2^48) 6217793537 10 Manual.Count131072.C047408.packed 64 cuts47408 = true := by
 decide +kernel
def cuts47409 : List PrefixCut := [⟨25,100766829,100766886⟩,
⟨64,256578044,256578195⟩]
theorem checked47409 : checkPrefixCuts (2^48) 6217924609 10 Manual.Count131072.C047409.packed 64 cuts47409 = true := by
 decide +kernel
def pointBounds47409 : List (Nat × Nat × Nat) := [(6217975808,110994016276405,110994403019831)]
theorem point_links_checked47409 : (cuts47409.take 1).map (fun c => (6217924609-1+2*2^10*c.k,110993915509576+c.lower,110994302252945+c.upper)) = pointBounds47409 := by
 decide +kernel
def cuts47410 : List PrefixCut := [⟨56,227149466,227149599⟩,
⟨64,258564385,258564537⟩]
theorem checked47410 : checkPrefixCuts (2^48) 6218055681 10 Manual.Count131072.C047410.packed 64 cuts47410 = true := by
 decide +kernel
def pointBounds47410 : List (Nat × Nat × Nat) := [(6218170368,110994399237086,110994785980739)]
theorem point_links_checked47410 : (cuts47410.take 1).map (fun c => (6218055681-1+2*2^10*c.k,110994172087620+c.lower,110994558831140+c.upper)) = pointBounds47410 := by
 decide +kernel
def cuts47411 : List PrefixCut := [⟨64,263809743,263809884⟩]
theorem checked47411 : checkPrefixCuts (2^48) 6218186753 10 Manual.Count131072.C047411.packed 64 cuts47411 = true := by
 decide +kernel
def cuts47412 : List PrefixCut := [⟨23,96460291,96460348⟩,
⟨64,264618981,264619137⟩]
theorem checked47412 : checkPrefixCuts (2^48) 6218317825 10 Manual.Count131072.C047412.packed 64 cuts47412 = true := by
 decide +kernel
def pointBounds47412 : List (Nat × Nat × Nat) := [(6218364928,110994790922039,110995177665909)]
theorem point_links_checked47412 : (cuts47412.take 1).map (fun c => (6218317825-1+2*2^10*c.k,110994694461748+c.lower,110995081205561+c.upper)) = pointBounds47412 := by
 decide +kernel
def cuts47413 : List PrefixCut := [⟨54,222156118,222156247⟩,
⟨64,263934428,263934580⟩]
theorem checked47413 : checkPrefixCuts (2^48) 6218448897 10 Manual.Count131072.C047413.packed 64 cuts47413 = true := by
 decide +kernel
def pointBounds47413 : List (Nat × Nat × Nat) := [(6218559488,110995181236847,110995567980945)]
theorem point_links_checked47413 : (cuts47413.take 1).map (fun c => (6218448897-1+2*2^10*c.k,110994959080729+c.lower,110995345824698+c.upper)) = pointBounds47413 := by
 decide +kernel
def cuts47414 : List PrefixCut := [⟨64,262706764,262706915⟩]
theorem checked47414 : checkPrefixCuts (2^48) 6218579969 10 Manual.Count131072.C047414.packed 64 cuts47414 = true := by
 decide +kernel
def cuts47415 : List PrefixCut := [⟨21,88578557,88578607⟩,
⟨64,267272714,267272870⟩]
theorem checked47415 : checkPrefixCuts (2^48) 6218711041 10 Manual.Count131072.C047415.packed 64 cuts47415 = true := by
 decide +kernel
def pointBounds47415 : List (Nat × Nat × Nat) := [(6218754048,110995574300478,110995961044800)]
theorem point_links_checked47415 : (cuts47415.take 1).map (fun c => (6218711041-1+2*2^10*c.k,110995485721921+c.lower,110995872466193+c.upper)) = pointBounds47415 := by
 decide +kernel
def cuts47416 : List PrefixCut := [⟨52,213451999,213452124⟩,
⟨64,262605186,262605339⟩]
theorem checked47416 : checkPrefixCuts (2^48) 6218842113 10 Manual.Count131072.C047416.packed 64 cuts47416 = true := by
 decide +kernel
def pointBounds47416 : List (Nat × Nat × Nat) := [(6218948608,110995966446634,110996353191187)]
theorem point_links_checked47416 : (cuts47416.take 1).map (fun c => (6218842113-1+2*2^10*c.k,110995752994635+c.lower,110996139739063+c.upper)) = pointBounds47416 := by
 decide +kernel
def cuts47417 : List PrefixCut := [⟨64,264545848,264545996⟩]
theorem checked47417 : checkPrefixCuts (2^48) 6218973185 10 Manual.Count131072.C047417.packed 64 cuts47417 = true := by
 decide +kernel
def cuts47418 : List PrefixCut := [⟨19,78118026,78118071⟩,
⟨64,267255793,267255949⟩]
theorem checked47418 : checkPrefixCuts (2^48) 6219104257 10 Manual.Count131072.C047418.packed 64 cuts47418 = true := by
 decide +kernel
def pointBounds47418 : List (Nat × Nat × Nat) := [(6219143168,110996358263695,110996745008469)]
theorem point_links_checked47418 : (cuts47418.take 1).map (fun c => (6219104257-1+2*2^10*c.k,110996280145669+c.lower,110996666890398+c.upper)) = pointBounds47418 := by
 decide +kernel
def cuts47419 : List PrefixCut := [⟨50,205880430,205880554⟩,
⟨64,264625202,264625362⟩]
theorem checked47419 : checkPrefixCuts (2^48) 6219235329 10 Manual.Count131072.C047419.packed 64 cuts47419 = true := by
 decide +kernel
def pointBounds47419 : List (Nat × Nat × Nat) := [(6219337728,110996753281892,110997140026901)]
theorem point_links_checked47419 : (cuts47419.take 1).map (fun c => (6219235329-1+2*2^10*c.k,110996547401462+c.lower,110996934146347+c.upper)) = pointBounds47419 := by
 decide +kernel
def cuts47420 : List PrefixCut := [⟨64,263804971,263805119⟩]
theorem checked47420 : checkPrefixCuts (2^48) 6219366401 10 Manual.Count131072.C047420.packed 64 cuts47420 = true := by
 decide +kernel
def cuts47421 : List PrefixCut := [⟨17,71007804,71007848⟩,
⟨64,262758527,262758678⟩]
theorem checked47421 : checkPrefixCuts (2^48) 6219497473 10 Manual.Count131072.C047421.packed 64 cuts47421 = true := by
 decide +kernel
def pointBounds47421 : List (Nat × Nat × Nat) := [(6219532288,110997146839439,110997533584676)]
theorem point_links_checked47421 : (cuts47421.take 1).map (fun c => (6219497473-1+2*2^10*c.k,110997075831635+c.lower,110997462576828+c.upper)) = pointBounds47421 := by
 decide +kernel
def cuts47422 : List PrefixCut := [⟨48,201160878,201160996⟩,
⟨64,267504806,267504964⟩]
theorem checked47422 : checkPrefixCuts (2^48) 6219628545 10 Manual.Count131072.C047422.packed 64 cuts47422 = true := by
 decide +kernel
def pointBounds47422 : List (Nat × Nat × Nat) := [(6219726848,110997539751040,110997926496502)]
theorem point_links_checked47422 : (cuts47422.take 1).map (fun c => (6219628545-1+2*2^10*c.k,110997338590162+c.lower,110997725335506+c.upper)) = pointBounds47422 := by
 decide +kernel
def cuts47423 : List PrefixCut := [⟨64,261616073,261616227⟩]
theorem checked47423 : checkPrefixCuts (2^48) 6219759617 10 Manual.Count131072.C047423.packed 64 cuts47423 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000231
