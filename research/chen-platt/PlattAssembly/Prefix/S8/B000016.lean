import PlattAssemblyKernel
import PlattCertificates.Count131072.C070512
import PlattCertificates.Count131072.C070513
import PlattCertificates.Count131072.C070514
import PlattCertificates.Count131072.C070515
import PlattCertificates.Count131072.C070516
import PlattCertificates.Count131072.C070517
import PlattCertificates.Count131072.C070518
import PlattCertificates.Count131072.C070519
import PlattCertificates.Count131072.C070520
import PlattCertificates.Count131072.C070521
import PlattCertificates.Count131072.C070522
import PlattCertificates.Count131072.C070523
import PlattCertificates.Count131072.C070524
import PlattCertificates.Count131072.C070525
import PlattCertificates.Count131072.C070526
import PlattCertificates.Count131072.C070527
import PlattCertificates.Count131072.C070528
import PlattCertificates.Count131072.C070529
import PlattCertificates.Count131072.C070530
import PlattCertificates.Count131072.C070531
import PlattCertificates.Count131072.C070532
import PlattCertificates.Count131072.C070533
import PlattCertificates.Count131072.C070534
import PlattCertificates.Count131072.C070535
import PlattCertificates.Count131072.C070536
import PlattCertificates.Count131072.C070537
import PlattCertificates.Count131072.C070538
import PlattCertificates.Count131072.C070539
import PlattCertificates.Count131072.C070540
import PlattCertificates.Count131072.C070541
import PlattCertificates.Count131072.C070542
import PlattCertificates.Count131072.C070543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70512 : List PrefixCut := [⟨64,173765230,173765329⟩]
theorem checked70512 : checkPrefixCuts (2^48) 9246081025 10 Manual.Count131072.C070512.packed 64 cuts70512 = true := by
 decide +kernel
def cuts70513 : List PrefixCut := [⟨11,29741977,29741995⟩,
⟨64,174462912,174463014⟩]
theorem checked70513 : checkPrefixCuts (2^48) 9246212097 10 Manual.Count131072.C070513.packed 64 cuts70513 = true := by
 decide +kernel
def pointBounds70513 : List (Nat × Nat × Nat) := [(9246234624,115903305387535,115903694945433)]
theorem point_links_checked70513 : (cuts70513.take 1).map (fun c => (9246212097-1+2*2^10*c.k,115903275645558+c.lower,115903665203438+c.upper)) = pointBounds70513 := by
 decide +kernel
def cuts70514 : List PrefixCut := [⟨64,172146895,172146998⟩]
theorem checked70514 : checkPrefixCuts (2^48) 9246343169 10 Manual.Count131072.C070514.packed 64 cuts70514 = true := by
 decide +kernel
def cuts70515 : List PrefixCut := [⟨25,69192930,69192972⟩,
⟨64,172540195,172540302⟩]
theorem checked70515 : checkPrefixCuts (2^48) 9246474241 10 Manual.Count131072.C070515.packed 64 cuts70515 = true := by
 decide +kernel
def pointBounds70515 : List (Nat × Nat × Nat) := [(9246525440,115903691448295,115904081006422)]
theorem point_links_checked70515 : (cuts70515.take 1).map (fun c => (9246474241-1+2*2^10*c.k,115903622255365+c.lower,115904011813450+c.upper)) = pointBounds70515 := by
 decide +kernel
def cuts70516 : List PrefixCut := [⟨64,173664040,173664137⟩]
theorem checked70516 : checkPrefixCuts (2^48) 9246605313 10 Manual.Count131072.C070516.packed 64 cuts70516 = true := by
 decide +kernel
def cuts70517 : List PrefixCut := [⟨39,105627939,105627998⟩,
⟨64,176127237,176127339⟩]
theorem checked70517 : checkPrefixCuts (2^48) 9246736385 10 Manual.Count131072.C070517.packed 64 cuts70517 = true := by
 decide +kernel
def pointBounds70517 : List (Nat × Nat × Nat) := [(9246816256,115904074087539,115904463645887)]
theorem point_links_checked70517 : (cuts70517.take 1).map (fun c => (9246736385-1+2*2^10*c.k,115903968459600+c.lower,115904358017889+c.upper)) = pointBounds70517 := by
 decide +kernel
def cuts70518 : List PrefixCut := [⟨64,173506917,173507022⟩]
theorem checked70518 : checkPrefixCuts (2^48) 9246867457 10 Manual.Count131072.C070518.packed 64 cuts70518 = true := by
 decide +kernel
def cuts70519 : List PrefixCut := [⟨53,144800297,144800382⟩,
⟨64,175087301,175087407⟩]
theorem checked70519 : checkPrefixCuts (2^48) 9246998529 10 Manual.Count131072.C070519.packed 64 cuts70519 = true := by
 decide +kernel
def pointBounds70519 : List (Nat × Nat × Nat) := [(9247107072,115904462894051,115904852452632)]
theorem point_links_checked70519 : (cuts70519.take 1).map (fun c => (9246998529-1+2*2^10*c.k,115904318093754+c.lower,115904707652250+c.upper)) = pointBounds70519 := by
 decide +kernel
def cuts70520 : List PrefixCut := [⟨64,171462598,171462696⟩]
theorem checked70520 : checkPrefixCuts (2^48) 9247129601 10 Manual.Count131072.C070520.packed 64 cuts70520 = true := by
 decide +kernel
def cuts70521 : List PrefixCut := [⟨64,173195154,173195263⟩]
theorem checked70521 : checkPrefixCuts (2^48) 9247260673 10 Manual.Count131072.C070521.packed 64 cuts70521 = true := by
 decide +kernel
def cuts70522 : List PrefixCut := [⟨3,8431407,8431411⟩,
⟨64,174988562,174988663⟩]
theorem checked70522 : checkPrefixCuts (2^48) 9247391745 10 Manual.Count131072.C070522.packed 64 cuts70522 = true := by
 decide +kernel
def pointBounds70522 : List (Nat × Nat × Nat) := [(9247397888,115904846270214,115905235829027)]
theorem point_links_checked70522 : (cuts70522.take 1).map (fun c => (9247391745-1+2*2^10*c.k,115904837838807+c.lower,115905227397616+c.upper)) = pointBounds70522 := by
 decide +kernel
def cuts70523 : List PrefixCut := [⟨64,172642367,172642466⟩]
theorem checked70523 : checkPrefixCuts (2^48) 9247522817 10 Manual.Count131072.C070523.packed 64 cuts70523 = true := by
 decide +kernel
def cuts70524 : List PrefixCut := [⟨17,46721378,46721405⟩,
⟨64,177662065,177662165⟩]
theorem checked70524 : checkPrefixCuts (2^48) 9247653889 10 Manual.Count131072.C070524.packed 64 cuts70524 = true := by
 decide +kernel
def pointBounds70524 : List (Nat × Nat × Nat) := [(9247688704,115905232191114,115905621750150)]
theorem point_links_checked70524 : (cuts70524.take 1).map (fun c => (9247653889-1+2*2^10*c.k,115905185469736+c.lower,115905575028745+c.upper)) = pointBounds70524 := by
 decide +kernel
def cuts70525 : List PrefixCut := [⟨64,174159316,174159417⟩]
theorem checked70525 : checkPrefixCuts (2^48) 9247784961 10 Manual.Count131072.C070525.packed 64 cuts70525 = true := by
 decide +kernel
def cuts70526 : List PrefixCut := [⟨31,84035094,84035144⟩,
⟨64,174004664,174004766⟩]
theorem checked70526 : checkPrefixCuts (2^48) 9247916033 10 Manual.Count131072.C070526.packed 64 cuts70526 = true := by
 decide +kernel
def pointBounds70526 : List (Nat × Nat × Nat) := [(9247979520,115905621326211,115906010885471)]
theorem point_links_checked70526 : (cuts70526.take 1).map (fun c => (9247916033-1+2*2^10*c.k,115905537291117+c.lower,115905926850327+c.upper)) = pointBounds70526 := by
 decide +kernel
def cuts70527 : List PrefixCut := [⟨64,172267358,172267457⟩]
theorem checked70527 : checkPrefixCuts (2^48) 9248047105 10 Manual.Count131072.C070527.packed 64 cuts70527 = true := by
 decide +kernel
def cuts70528 : List PrefixCut := [⟨45,121894421,121894496⟩,
⟨64,173573639,173573739⟩]
theorem checked70528 : checkPrefixCuts (2^48) 9248178177 10 Manual.Count131072.C070528.packed 64 cuts70528 = true := by
 decide +kernel
def pointBounds70528 : List (Nat × Nat × Nat) := [(9248270336,115906005457560,115906395017046)]
theorem point_links_checked70528 : (cuts70528.take 1).map (fun c => (9248178177-1+2*2^10*c.k,115905883563139+c.lower,115906273122550+c.upper)) = pointBounds70528 := by
 decide +kernel
def cuts70529 : List PrefixCut := [⟨64,172658126,172658227⟩]
theorem checked70529 : checkPrefixCuts (2^48) 9248309249 10 Manual.Count131072.C070529.packed 64 cuts70529 = true := by
 decide +kernel
def cuts70530 : List PrefixCut := [⟨59,160177577,160177676⟩,
⟨64,173781768,173781877⟩]
theorem checked70530 : checkPrefixCuts (2^48) 9248440321 10 Manual.Count131072.C070530.packed 64 cuts70530 = true := by
 decide +kernel
def pointBounds70530 : List (Nat × Nat × Nat) := [(9248561152,115906389972481,115906779532192)]
theorem point_links_checked70530 : (cuts70530.take 1).map (fun c => (9248440321-1+2*2^10*c.k,115906229794904+c.lower,115906619354516+c.upper)) = pointBounds70530 := by
 decide +kernel
def cuts70531 : List PrefixCut := [⟨64,174327118,174327217⟩]
theorem checked70531 : checkPrefixCuts (2^48) 9248571393 10 Manual.Count131072.C070531.packed 64 cuts70531 = true := by
 decide +kernel
def cuts70532 : List PrefixCut := [⟨64,173533368,173533474⟩]
theorem checked70532 : checkPrefixCuts (2^48) 9248702465 10 Manual.Count131072.C070532.packed 64 cuts70532 = true := by
 decide +kernel
def cuts70533 : List PrefixCut := [⟨9,23799018,23799031⟩,
⟨64,171826642,171826742⟩]
theorem checked70533 : checkPrefixCuts (2^48) 9248833537 10 Manual.Count131072.C070533.packed 64 cuts70533 = true := by
 decide +kernel
def pointBounds70533 : List (Nat × Nat × Nat) := [(9248851968,115906775236176,115907164796115)]
theorem point_links_checked70533 : (cuts70533.take 1).map (fun c => (9248833537-1+2*2^10*c.k,115906751437158+c.lower,115907140997084+c.upper)) = pointBounds70533 := by
 decide +kernel
def cuts70534 : List PrefixCut := [⟨64,174745758,174745863⟩]
theorem checked70534 : checkPrefixCuts (2^48) 9248964609 10 Manual.Count131072.C070534.packed 64 cuts70534 = true := by
 decide +kernel
def cuts70535 : List PrefixCut := [⟨23,61869507,61869544⟩,
⟨64,175230205,175230306⟩]
theorem checked70535 : checkPrefixCuts (2^48) 9249095681 10 Manual.Count131072.C070535.packed 64 cuts70535 = true := by
 decide +kernel
def pointBounds70535 : List (Nat × Nat × Nat) := [(9249142784,115907159879065,115907549439233)]
theorem point_links_checked70535 : (cuts70535.take 1).map (fun c => (9249095681-1+2*2^10*c.k,115907098009558+c.lower,115907487569689+c.upper)) = pointBounds70535 := by
 decide +kernel
def cuts70536 : List PrefixCut := [⟨64,173736563,173736668⟩]
theorem checked70536 : checkPrefixCuts (2^48) 9249226753 10 Manual.Count131072.C070536.packed 64 cuts70536 = true := by
 decide +kernel
def cuts70537 : List PrefixCut := [⟨37,101733194,101733250⟩,
⟨64,174647044,174647148⟩]
theorem checked70537 : checkPrefixCuts (2^48) 9249357825 10 Manual.Count131072.C070537.packed 64 cuts70537 = true := by
 decide +kernel
def pointBounds70537 : List (Nat × Nat × Nat) := [(9249433600,115907548709520,115907938269913)]
theorem point_links_checked70537 : (cuts70537.take 1).map (fun c => (9249357825-1+2*2^10*c.k,115907446976326+c.lower,115907836536663+c.upper)) = pointBounds70537 := by
 decide +kernel
def cuts70538 : List PrefixCut := [⟨64,173883795,173883897⟩]
theorem checked70538 : checkPrefixCuts (2^48) 9249488897 10 Manual.Count131072.C070538.packed 64 cuts70538 = true := by
 decide +kernel
def cuts70539 : List PrefixCut := [⟨51,138855731,138855815⟩,
⟨64,174581234,174581338⟩]
theorem checked70539 : checkPrefixCuts (2^48) 9249619969 10 Manual.Count131072.C070539.packed 64 cuts70539 = true := by
 decide +kernel
def pointBounds70539 : List (Nat × Nat × Nat) := [(9249724416,115907934362896,115908323923523)]
theorem point_links_checked70539 : (cuts70539.take 1).map (fun c => (9249619969-1+2*2^10*c.k,115907795507165+c.lower,115908185067708+c.upper)) = pointBounds70539 := by
 decide +kernel
def cuts70540 : List PrefixCut := [⟨64,175369951,175370051⟩]
theorem checked70540 : checkPrefixCuts (2^48) 9249751041 10 Manual.Count131072.C070540.packed 64 cuts70540 = true := by
 decide +kernel
def cuts70541 : List PrefixCut := [⟨64,171928874,171928979⟩]
theorem checked70541 : checkPrefixCuts (2^48) 9249882113 10 Manual.Count131072.C070541.packed 64 cuts70541 = true := by
 decide +kernel
def cuts70542 : List PrefixCut := [⟨1,2890819,2890820⟩,
⟨64,174908543,174908637⟩]
theorem checked70542 : checkPrefixCuts (2^48) 9250013185 10 Manual.Count131072.C070542.packed 64 cuts70542 = true := by
 decide +kernel
def pointBounds70542 : List (Nat × Nat × Nat) := [(9250015232,115908320278043,115908709838896)]
theorem point_links_checked70542 : (cuts70542.take 1).map (fun c => (9250013185-1+2*2^10*c.k,115908317387224+c.lower,115908706948076+c.upper)) = pointBounds70542 := by
 decide +kernel
def cuts70543 : List PrefixCut := [⟨64,172410891,172410994⟩]
theorem checked70543 : checkPrefixCuts (2^48) 9250144257 10 Manual.Count131072.C070543.packed 64 cuts70543 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000016
