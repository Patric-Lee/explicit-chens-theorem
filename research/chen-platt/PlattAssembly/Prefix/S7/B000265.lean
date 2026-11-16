import PlattAssemblyKernel
import PlattCertificates.Count131072.C068480
import PlattCertificates.Count131072.C068481
import PlattCertificates.Count131072.C068482
import PlattCertificates.Count131072.C068483
import PlattCertificates.Count131072.C068484
import PlattCertificates.Count131072.C068485
import PlattCertificates.Count131072.C068486
import PlattCertificates.Count131072.C068487
import PlattCertificates.Count131072.C068488
import PlattCertificates.Count131072.C068489
import PlattCertificates.Count131072.C068490
import PlattCertificates.Count131072.C068491
import PlattCertificates.Count131072.C068492
import PlattCertificates.Count131072.C068493
import PlattCertificates.Count131072.C068494
import PlattCertificates.Count131072.C068495
import PlattCertificates.Count131072.C068496
import PlattCertificates.Count131072.C068497
import PlattCertificates.Count131072.C068498
import PlattCertificates.Count131072.C068499
import PlattCertificates.Count131072.C068500
import PlattCertificates.Count131072.C068501
import PlattCertificates.Count131072.C068502
import PlattCertificates.Count131072.C068503
import PlattCertificates.Count131072.C068504
import PlattCertificates.Count131072.C068505
import PlattCertificates.Count131072.C068506
import PlattCertificates.Count131072.C068507
import PlattCertificates.Count131072.C068508
import PlattCertificates.Count131072.C068509
import PlattCertificates.Count131072.C068510
import PlattCertificates.Count131072.C068511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000265
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68480 : List PrefixCut := [⟨63,178793695,178793797⟩,
⟨64,181458027,181458131⟩]
theorem checked68480 : checkPrefixCuts (2^48) 8979742721 10 Manual.Count131072.C068480.packed 64 cuts68480 = true := by
 decide +kernel
def pointBounds68480 : List (Nat × Nat × Nat) := [(8979871744,115544547910529,115544937257606)]
theorem point_links_checked68480 : (cuts68480.take 1).map (fun c => (8979742721-1+2*2^10*c.k,115544369116834+c.lower,115544758463809+c.upper)) = pointBounds68480 := by
 decide +kernel
def cuts68481 : List PrefixCut := [⟨64,179167181,179167291⟩]
theorem checked68481 : checkPrefixCuts (2^48) 8979873793 10 Manual.Count131072.C068481.packed 64 cuts68481 = true := by
 decide +kernel
def cuts68482 : List PrefixCut := [⟨64,180418350,180418461⟩]
theorem checked68482 : checkPrefixCuts (2^48) 8980004865 10 Manual.Count131072.C068482.packed 64 cuts68482 = true := by
 decide +kernel
def cuts68483 : List PrefixCut := [⟨9,25232032,25232045⟩,
⟨64,180164959,180165064⟩]
theorem checked68483 : checkPrefixCuts (2^48) 8980135937 10 Manual.Count131072.C068483.packed 64 cuts68483 = true := by
 decide +kernel
def pointBounds68483 : List (Nat × Nat × Nat) := [(8980154368,115544935392424,115545324739737)]
theorem point_links_checked68483 : (cuts68483.take 1).map (fun c => (8980135937-1+2*2^10*c.k,115544910160392+c.lower,115545299507692+c.upper)) = pointBounds68483 := by
 decide +kernel
def cuts68484 : List PrefixCut := [⟨64,180601154,180601258⟩]
theorem checked68484 : checkPrefixCuts (2^48) 8980267009 10 Manual.Count131072.C068484.packed 64 cuts68484 = true := by
 decide +kernel
def cuts68485 : List PrefixCut := [⟨19,52593864,52593897⟩,
⟨64,180410446,180410554⟩]
theorem checked68485 : checkPrefixCuts (2^48) 8980398081 10 Manual.Count131072.C068485.packed 64 cuts68485 = true := by
 decide +kernel
def pointBounds68485 : List (Nat × Nat × Nat) := [(8980436992,115545323520369,115545712867911)]
theorem point_links_checked68485 : (cuts68485.take 1).map (fun c => (8980398081-1+2*2^10*c.k,115545270926505+c.lower,115545660274014+c.upper)) = pointBounds68485 := by
 decide +kernel
def cuts68486 : List PrefixCut := [⟨64,178057124,178057223⟩]
theorem checked68486 : checkPrefixCuts (2^48) 8980529153 10 Manual.Count131072.C068486.packed 64 cuts68486 = true := by
 decide +kernel
def cuts68487 : List PrefixCut := [⟨29,80110756,80110804⟩,
⟨64,176518763,176518866⟩]
theorem checked68487 : checkPrefixCuts (2^48) 8980660225 10 Manual.Count131072.C068487.packed 64 cuts68487 = true := by
 decide +kernel
def pointBounds68487 : List (Nat × Nat × Nat) := [(8980719616,115545709504831,115546098852595)]
theorem point_links_checked68487 : (cuts68487.take 1).map (fun c => (8980660225-1+2*2^10*c.k,115545629394075+c.lower,115546018741791+c.upper)) = pointBounds68487 := by
 decide +kernel
def cuts68488 : List PrefixCut := [⟨64,177362413,177362516⟩]
theorem checked68488 : checkPrefixCuts (2^48) 8980791297 10 Manual.Count131072.C068488.packed 64 cuts68488 = true := by
 decide +kernel
def cuts68489 : List PrefixCut := [⟨39,108879620,108879683⟩,
⟨64,178143356,178143457⟩]
theorem checked68489 : checkPrefixCuts (2^48) 8980922369 10 Manual.Count131072.C068489.packed 64 cuts68489 = true := by
 decide +kernel
def pointBounds68489 : List (Nat × Nat × Nat) := [(8981002240,115546092154871,115546481502856)]
theorem point_links_checked68489 : (cuts68489.take 1).map (fun c => (8980922369-1+2*2^10*c.k,115545983275251+c.lower,115546372623173+c.upper)) = pointBounds68489 := by
 decide +kernel
def cuts68490 : List PrefixCut := [⟨64,177921369,177921479⟩]
theorem checked68490 : checkPrefixCuts (2^48) 8981053441 10 Manual.Count131072.C068490.packed 64 cuts68490 = true := by
 decide +kernel
def cuts68491 : List PrefixCut := [⟨49,137866129,137866211⟩,
⟨64,180770733,180770841⟩]
theorem checked68491 : checkPrefixCuts (2^48) 8981184513 10 Manual.Count131072.C068491.packed 64 cuts68491 = true := by
 decide +kernel
def pointBounds68491 : List (Nat × Nat × Nat) := [(8981284864,115546477206105,115546866554320)]
theorem point_links_checked68491 : (cuts68491.take 1).map (fun c => (8981184513-1+2*2^10*c.k,115546339339976+c.lower,115546728688109+c.upper)) = pointBounds68491 := by
 decide +kernel
def cuts68492 : List PrefixCut := [⟨64,180705423,180705527⟩]
theorem checked68492 : checkPrefixCuts (2^48) 8981315585 10 Manual.Count131072.C068492.packed 64 cuts68492 = true := by
 decide +kernel
def cuts68493 : List PrefixCut := [⟨59,161429160,161429263⟩,
⟨64,174685623,174685733⟩]
theorem checked68493 : checkPrefixCuts (2^48) 8981446657 10 Manual.Count131072.C068493.packed 64 cuts68493 = true := by
 decide +kernel
def pointBounds68493 : List (Nat × Nat × Nat) := [(8981567488,115546862245292,115547251593740)]
theorem point_links_checked68493 : (cuts68493.take 1).map (fun c => (8981446657-1+2*2^10*c.k,115546700816132+c.lower,115547090164477+c.upper)) = pointBounds68493 := by
 decide +kernel
def cuts68494 : List PrefixCut := [⟨64,178882488,178882590⟩]
theorem checked68494 : checkPrefixCuts (2^48) 8981577729 10 Manual.Count131072.C068494.packed 64 cuts68494 = true := by
 decide +kernel
def cuts68495 : List PrefixCut := [⟨64,178472477,178472587⟩]
theorem checked68495 : checkPrefixCuts (2^48) 8981708801 10 Manual.Count131072.C068495.packed 64 cuts68495 = true := by
 decide +kernel
def cuts68496 : List PrefixCut := [⟨5,14164868,14164878⟩,
⟨64,177028323,177028434⟩]
theorem checked68496 : checkPrefixCuts (2^48) 8981839873 10 Manual.Count131072.C068496.packed 64 cuts68496 = true := by
 decide +kernel
def pointBounds68496 : List (Nat × Nat × Nat) := [(8981850112,115547247021588,115547636370265)]
theorem point_links_checked68496 : (cuts68496.take 1).map (fun c => (8981839873-1+2*2^10*c.k,115547232856720+c.lower,115547622205387+c.upper)) = pointBounds68496 := by
 decide +kernel
def cuts68497 : List PrefixCut := [⟨64,180504223,180504322⟩]
theorem checked68497 : checkPrefixCuts (2^48) 8981970945 10 Manual.Count131072.C068497.packed 64 cuts68497 = true := by
 decide +kernel
def cuts68498 : List PrefixCut := [⟨15,41960583,41960605⟩,
⟨64,180971638,180971740⟩]
theorem checked68498 : checkPrefixCuts (2^48) 8982102017 10 Manual.Count131072.C068498.packed 64 cuts68498 = true := by
 decide +kernel
def pointBounds68498 : List (Nat × Nat × Nat) := [(8982132736,115547632349849,115548021698748)]
theorem point_links_checked68498 : (cuts68498.take 1).map (fun c => (8982102017-1+2*2^10*c.k,115547590389266+c.lower,115547979738143+c.upper)) = pointBounds68498 := by
 decide +kernel
def cuts68499 : List PrefixCut := [⟨64,182128449,182128549⟩]
theorem checked68499 : checkPrefixCuts (2^48) 8982233089 10 Manual.Count131072.C068499.packed 64 cuts68499 = true := by
 decide +kernel
def cuts68500 : List PrefixCut := [⟨25,67529735,67529776⟩,
⟨64,175482506,175482612⟩]
theorem checked68500 : checkPrefixCuts (2^48) 8982364161 10 Manual.Count131072.C068500.packed 64 cuts68500 = true := by
 decide +kernel
def pointBounds68500 : List (Nat × Nat × Nat) := [(8982415360,115548021019088,115548410368208)]
theorem point_links_checked68500 : (cuts68500.take 1).map (fun c => (8982364161-1+2*2^10*c.k,115547953489353+c.lower,115548342838432+c.upper)) = pointBounds68500 := by
 decide +kernel
def cuts68501 : List PrefixCut := [⟨64,179490940,179491041⟩]
theorem checked68501 : checkPrefixCuts (2^48) 8982495233 10 Manual.Count131072.C068501.packed 64 cuts68501 = true := by
 decide +kernel
def cuts68502 : List PrefixCut := [⟨35,99145061,99145121⟩,
⟨64,179049621,179049732⟩]
theorem checked68502 : checkPrefixCuts (2^48) 8982626305 10 Manual.Count131072.C068502.packed 64 cuts68502 = true := by
 decide +kernel
def pointBounds68502 : List (Nat × Nat × Nat) := [(8982697984,115548407607860,115548796957206)]
theorem point_links_checked68502 : (cuts68502.take 1).map (fun c => (8982626305-1+2*2^10*c.k,115548308462799+c.lower,115548697812085+c.upper)) = pointBounds68502 := by
 decide +kernel
def cuts68503 : List PrefixCut := [⟨64,178545648,178545748⟩]
theorem checked68503 : checkPrefixCuts (2^48) 8982757377 10 Manual.Count131072.C068503.packed 64 cuts68503 = true := by
 decide +kernel
def cuts68504 : List PrefixCut := [⟨45,126841676,126841749⟩,
⟨64,181582480,181582584⟩]
theorem checked68504 : checkPrefixCuts (2^48) 8982888449 10 Manual.Count131072.C068504.packed 64 cuts68504 = true := by
 decide +kernel
def pointBounds68504 : List (Nat × Nat × Nat) := [(8982980608,115548792899744,115549182249314)]
theorem point_links_checked68504 : (cuts68504.take 1).map (fun c => (8982888449-1+2*2^10*c.k,115548666058068+c.lower,115549055407565+c.upper)) = pointBounds68504 := by
 decide +kernel
def cuts68505 : List PrefixCut := [⟨64,178352436,178352541⟩]
theorem checked68505 : checkPrefixCuts (2^48) 8983019521 10 Manual.Count131072.C068505.packed 64 cuts68505 = true := by
 decide +kernel
def cuts68506 : List PrefixCut := [⟨55,154223258,154223348⟩,
⟨64,178255842,178255945⟩]
theorem checked68506 : checkPrefixCuts (2^48) 8983150593 10 Manual.Count131072.C068506.packed 64 cuts68506 = true := by
 decide +kernel
def pointBounds68506 : List (Nat × Nat × Nat) := [(8983263232,115549180216242,115549569566038)]
theorem point_links_checked68506 : (cuts68506.take 1).map (fun c => (8983150593-1+2*2^10*c.k,115549025992984+c.lower,115549415342690+c.upper)) = pointBounds68506 := by
 decide +kernel
def cuts68507 : List PrefixCut := [⟨64,176874595,176874696⟩]
theorem checked68507 : checkPrefixCuts (2^48) 8983281665 10 Manual.Count131072.C068507.packed 64 cuts68507 = true := by
 decide +kernel
def cuts68508 : List PrefixCut := [⟨64,178908608,178908711⟩]
theorem checked68508 : checkPrefixCuts (2^48) 8983412737 10 Manual.Count131072.C068508.packed 64 cuts68508 = true := by
 decide +kernel
def cuts68509 : List PrefixCut := [⟨1,2882569,2882571⟩,
⟨64,177464737,177464847⟩]
theorem checked68509 : checkPrefixCuts (2^48) 8983543809 10 Manual.Count131072.C068509.packed 64 cuts68509 = true := by
 decide +kernel
def pointBounds68509 : List (Nat × Nat × Nat) := [(8983545856,115549562914598,115549952264613)]
theorem point_links_checked68509 : (cuts68509.take 1).map (fun c => (8983543809-1+2*2^10*c.k,115549560032029+c.lower,115549949382042+c.upper)) = pointBounds68509 := by
 decide +kernel
def cuts68510 : List PrefixCut := [⟨64,179843338,179843443⟩]
theorem checked68510 : checkPrefixCuts (2^48) 8983674881 10 Manual.Count131072.C068510.packed 64 cuts68510 = true := by
 decide +kernel
def cuts68511 : List PrefixCut := [⟨11,32396591,32396610⟩,
⟨64,183945103,183945207⟩]
theorem checked68511 : checkPrefixCuts (2^48) 8983805953 10 Manual.Count131072.C068511.packed 64 cuts68511 = true := by
 decide +kernel
def pointBounds68511 : List (Nat × Nat × Nat) := [(8983828480,115549949736695,115550339086942)]
theorem point_links_checked68511 : (cuts68511.take 1).map (fun c => (8983805953-1+2*2^10*c.k,115549917340104+c.lower,115550306690332+c.upper)) = pointBounds68511 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000265
