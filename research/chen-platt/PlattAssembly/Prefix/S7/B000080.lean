import PlattAssemblyKernel
import PlattCertificates.Count131072.C062560
import PlattCertificates.Count131072.C062561
import PlattCertificates.Count131072.C062562
import PlattCertificates.Count131072.C062563
import PlattCertificates.Count131072.C062564
import PlattCertificates.Count131072.C062565
import PlattCertificates.Count131072.C062566
import PlattCertificates.Count131072.C062567
import PlattCertificates.Count131072.C062568
import PlattCertificates.Count131072.C062569
import PlattCertificates.Count131072.C062570
import PlattCertificates.Count131072.C062571
import PlattCertificates.Count131072.C062572
import PlattCertificates.Count131072.C062573
import PlattCertificates.Count131072.C062574
import PlattCertificates.Count131072.C062575
import PlattCertificates.Count131072.C062576
import PlattCertificates.Count131072.C062577
import PlattCertificates.Count131072.C062578
import PlattCertificates.Count131072.C062579
import PlattCertificates.Count131072.C062580
import PlattCertificates.Count131072.C062581
import PlattCertificates.Count131072.C062582
import PlattCertificates.Count131072.C062583
import PlattCertificates.Count131072.C062584
import PlattCertificates.Count131072.C062585
import PlattCertificates.Count131072.C062586
import PlattCertificates.Count131072.C062587
import PlattCertificates.Count131072.C062588
import PlattCertificates.Count131072.C062589
import PlattCertificates.Count131072.C062590
import PlattCertificates.Count131072.C062591
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62560 : List PrefixCut := [⟨64,198826720,198826835⟩]
theorem checked62560 : checkPrefixCuts (2^48) 8203796481 10 Manual.Count131072.C062560.packed 64 cuts62560 = true := by
 decide +kernel
def cuts62561 : List PrefixCut := [⟨12,36780020,36780043⟩,
⟨64,197519780,197519891⟩]
theorem checked62561 : checkPrefixCuts (2^48) 8203927553 10 Manual.Count131072.C062561.packed 64 cuts62561 = true := by
 decide +kernel
def pointBounds62561 : List (Nat × Nat × Nat) := [(8203952128,114432464623872,114432853326492)]
theorem point_links_checked62561 : (cuts62561.take 1).map (fun c => (8203927553-1+2*2^10*c.k,114432427843852+c.lower,114432816546449+c.upper)) = pointBounds62561 := by
 decide +kernel
def cuts62562 : List PrefixCut := [⟨64,196041352,196041471⟩]
theorem checked62562 : checkPrefixCuts (2^48) 8204058625 10 Manual.Count131072.C062562.packed 64 cuts62562 = true := by
 decide +kernel
def cuts62563 : List PrefixCut := [⟨10,31083623,31083641⟩,
⟨64,196998841,196998955⟩]
theorem checked62563 : checkPrefixCuts (2^48) 8204189697 10 Manual.Count131072.C062563.packed 64 cuts62563 = true := by
 decide +kernel
def pointBounds62563 : List (Nat × Nat × Nat) := [(8204210176,114432852488607,114433241191452)]
theorem point_links_checked62563 : (cuts62563.take 1).map (fun c => (8204189697-1+2*2^10*c.k,114432821404984+c.lower,114433210107811+c.upper)) = pointBounds62563 := by
 decide +kernel
def cuts62564 : List PrefixCut := [⟨64,193118898,193119006⟩]
theorem checked62564 : checkPrefixCuts (2^48) 8204320769 10 Manual.Count131072.C062564.packed 64 cuts62564 = true := by
 decide +kernel
def cuts62565 : List PrefixCut := [⟨8,23432055,23432066⟩,
⟨64,194145037,194145146⟩]
theorem checked62565 : checkPrefixCuts (2^48) 8204451841 10 Manual.Count131072.C062565.packed 64 cuts62565 = true := by
 decide +kernel
def pointBounds62565 : List (Nat × Nat × Nat) := [(8204468224,114433234954778,114433623657838)]
theorem point_links_checked62565 : (cuts62565.take 1).map (fun c => (8204451841-1+2*2^10*c.k,114433211522723+c.lower,114433600225772+c.upper)) = pointBounds62565 := by
 decide +kernel
def cuts62566 : List PrefixCut := [⟨64,196406199,196406318⟩]
theorem checked62566 : checkPrefixCuts (2^48) 8204582913 10 Manual.Count131072.C062566.packed 64 cuts62566 = true := by
 decide +kernel
def cuts62567 : List PrefixCut := [⟨6,19074391,19074403⟩,
⟨64,199353389,199353505⟩]
theorem checked62567 : checkPrefixCuts (2^48) 8204713985 10 Manual.Count131072.C062567.packed 64 cuts62567 = true := by
 decide +kernel
def pointBounds62567 : List (Nat × Nat × Nat) := [(8204726272,114433621148350,114434009851639)]
theorem point_links_checked62567 : (cuts62567.take 1).map (fun c => (8204713985-1+2*2^10*c.k,114433602073959+c.lower,114433990777236+c.upper)) = pointBounds62567 := by
 decide +kernel
def cuts62568 : List PrefixCut := [⟨64,197875068,197875179⟩]
theorem checked62568 : checkPrefixCuts (2^48) 8204845057 10 Manual.Count131072.C062568.packed 64 cuts62568 = true := by
 decide +kernel
def cuts62569 : List PrefixCut := [⟨4,11938270,11938277⟩,
⟨64,197563149,197563269⟩]
theorem checked62569 : checkPrefixCuts (2^48) 8204976129 10 Manual.Count131072.C062569.packed 64 cuts62569 = true := by
 decide +kernel
def pointBounds62569 : List (Nat × Nat × Nat) := [(8204984320,114434011240686,114434399944197)]
theorem point_links_checked62569 : (cuts62569.take 1).map (fun c => (8204976129-1+2*2^10*c.k,114433999302416+c.lower,114434388005920+c.upper)) = pointBounds62569 := by
 decide +kernel
def cuts62570 : List PrefixCut := [⟨64,197491402,197491520⟩]
theorem checked62570 : checkPrefixCuts (2^48) 8205107201 10 Manual.Count131072.C062570.packed 64 cuts62570 = true := by
 decide +kernel
def cuts62571 : List PrefixCut := [⟨2,6311989,6311992⟩,
⟨64,197659764,197659876⟩]
theorem checked62571 : checkPrefixCuts (2^48) 8205238273 10 Manual.Count131072.C062571.packed 64 cuts62571 = true := by
 decide +kernel
def pointBounds62571 : List (Nat × Nat × Nat) := [(8205242368,114434400668956,114434789372701)]
theorem point_links_checked62571 : (cuts62571.take 1).map (fun c => (8205238273-1+2*2^10*c.k,114434394356967+c.lower,114434783060709+c.upper)) = pointBounds62571 := by
 decide +kernel
def cuts62572 : List PrefixCut := [⟨64,196421668,196421783⟩]
theorem checked62572 : checkPrefixCuts (2^48) 8205369345 10 Manual.Count131072.C062572.packed 64 cuts62572 = true := by
 decide +kernel
def pointBounds62572 : List (Nat × Nat × Nat) := [(8205500416,114434788438399,114435177142368)]
theorem point_links_checked62572 : (cuts62572.take 1).map (fun c => (8205369345-1+2*2^10*c.k,114434592016731+c.lower,114434980720585+c.upper)) = pointBounds62572 := by
 decide +kernel
def cuts62573 : List PrefixCut := [⟨64,196144108,196144224⟩]
theorem checked62573 : checkPrefixCuts (2^48) 8205500417 10 Manual.Count131072.C062573.packed 64 cuts62573 = true := by
 decide +kernel
def cuts62574 : List PrefixCut := [⟨62,192230565,192230680⟩,
⟨64,198027622,198027740⟩]
theorem checked62574 : checkPrefixCuts (2^48) 8205631489 10 Manual.Count131072.C062574.packed 64 cuts62574 = true := by
 decide +kernel
def pointBounds62574 : List (Nat × Nat × Nat) := [(8205758464,114435176813072,114435565517272)]
theorem point_links_checked62574 : (cuts62574.take 1).map (fun c => (8205631489-1+2*2^10*c.k,114434984582507+c.lower,114435373286592+c.upper)) = pointBounds62574 := by
 decide +kernel
def cuts62575 : List PrefixCut := [⟨64,198950599,198950709⟩]
theorem checked62575 : checkPrefixCuts (2^48) 8205762561 10 Manual.Count131072.C062575.packed 64 cuts62575 = true := by
 decide +kernel
def cuts62576 : List PrefixCut := [⟨60,184438054,184438164⟩,
⟨64,196306208,196306324⟩]
theorem checked62576 : checkPrefixCuts (2^48) 8205893633 10 Manual.Count131072.C062576.packed 64 cuts62576 = true := by
 decide +kernel
def pointBounds62576 : List (Nat × Nat × Nat) := [(8206016512,114435565998782,114435954703205)]
theorem point_links_checked62576 : (cuts62576.take 1).map (fun c => (8205893633-1+2*2^10*c.k,114435381560728+c.lower,114435770265041+c.upper)) = pointBounds62576 := by
 decide +kernel
def cuts62577 : List PrefixCut := [⟨64,197366414,197366524⟩]
theorem checked62577 : checkPrefixCuts (2^48) 8206024705 10 Manual.Count131072.C062577.packed 64 cuts62577 = true := by
 decide +kernel
def cuts62578 : List PrefixCut := [⟨58,179424397,179424501⟩,
⟨64,197740562,197740677⟩]
theorem checked62578 : checkPrefixCuts (2^48) 8206155777 10 Manual.Count131072.C062578.packed 64 cuts62578 = true := by
 decide +kernel
def pointBounds62578 : List (Nat × Nat × Nat) := [(8206274560,114435954657747,114436343362390)]
theorem point_links_checked62578 : (cuts62578.take 1).map (fun c => (8206155777-1+2*2^10*c.k,114435775233350+c.lower,114436163937889+c.upper)) = pointBounds62578 := by
 decide +kernel
def cuts62579 : List PrefixCut := [⟨64,196571217,196571327⟩]
theorem checked62579 : checkPrefixCuts (2^48) 8206286849 10 Manual.Count131072.C062579.packed 64 cuts62579 = true := by
 decide +kernel
def cuts62580 : List PrefixCut := [⟨56,170638144,170638240⟩,
⟨64,194818831,194818942⟩]
theorem checked62580 : checkPrefixCuts (2^48) 8206417921 10 Manual.Count131072.C062580.packed 64 cuts62580 = true := by
 decide +kernel
def pointBounds62580 : List (Nat × Nat × Nat) := [(8206532608,114436340183273,114436728888133)]
theorem point_links_checked62580 : (cuts62580.take 1).map (fun c => (8206417921-1+2*2^10*c.k,114436169545129+c.lower,114436558249893+c.upper)) = pointBounds62580 := by
 decide +kernel
def cuts62581 : List PrefixCut := [⟨64,196153335,196153446⟩]
theorem checked62581 : checkPrefixCuts (2^48) 8206548993 10 Manual.Count131072.C062581.packed 64 cuts62581 = true := by
 decide +kernel
def cuts62582 : List PrefixCut := [⟨54,166002491,166002588⟩,
⟨64,197487839,197487949⟩]
theorem checked62582 : checkPrefixCuts (2^48) 8206680065 10 Manual.Count131072.C062582.packed 64 cuts62582 = true := by
 decide +kernel
def pointBounds62582 : List (Nat × Nat × Nat) := [(8206790656,114436726519786,114437115224869)]
theorem point_links_checked62582 : (cuts62582.take 1).map (fun c => (8206680065-1+2*2^10*c.k,114436560517295+c.lower,114436949222281+c.upper)) = pointBounds62582 := by
 decide +kernel
def cuts62583 : List PrefixCut := [⟨64,196284289,196284405⟩]
theorem checked62583 : checkPrefixCuts (2^48) 8206811137 10 Manual.Count131072.C062583.packed 64 cuts62583 = true := by
 decide +kernel
def cuts62584 : List PrefixCut := [⟨52,161984481,161984574⟩,
⟨64,200499646,200499761⟩]
theorem checked62584 : checkPrefixCuts (2^48) 8206942209 10 Manual.Count131072.C062584.packed 64 cuts62584 = true := by
 decide +kernel
def pointBounds62584 : List (Nat × Nat × Nat) := [(8207048704,114437116273904,114437504979209)]
theorem point_links_checked62584 : (cuts62584.take 1).map (fun c => (8206942209-1+2*2^10*c.k,114436954289423+c.lower,114437342994635+c.upper)) = pointBounds62584 := by
 decide +kernel
def cuts62585 : List PrefixCut := [⟨64,195489194,195489308⟩]
theorem checked62585 : checkPrefixCuts (2^48) 8207073281 10 Manual.Count131072.C062585.packed 64 cuts62585 = true := by
 decide +kernel
def cuts62586 : List PrefixCut := [⟨50,152822356,152822443⟩,
⟨64,196137681,196137793⟩]
theorem checked62586 : checkPrefixCuts (2^48) 8207204353 10 Manual.Count131072.C062586.packed 64 cuts62586 = true := by
 decide +kernel
def pointBounds62586 : List (Nat × Nat × Nat) := [(8207306752,114437503100619,114437891806147)]
theorem point_links_checked62586 : (cuts62586.take 1).map (fun c => (8207204353-1+2*2^10*c.k,114437350278263+c.lower,114437738983704+c.upper)) = pointBounds62586 := by
 decide +kernel
def cuts62587 : List PrefixCut := [⟨64,197574959,197575072⟩]
theorem checked62587 : checkPrefixCuts (2^48) 8207335425 10 Manual.Count131072.C062587.packed 64 cuts62587 = true := by
 decide +kernel
def cuts62588 : List PrefixCut := [⟨48,149319444,149319528⟩,
⟨64,197811865,197811979⟩]
theorem checked62588 : checkPrefixCuts (2^48) 8207466497 10 Manual.Count131072.C062588.packed 64 cuts62588 = true := by
 decide +kernel
def pointBounds62588 : List (Nat × Nat × Nat) := [(8207564800,114437893310347,114438282016097)]
theorem point_links_checked62588 : (cuts62588.take 1).map (fun c => (8207466497-1+2*2^10*c.k,114437743990903+c.lower,114438132696569+c.upper)) = pointBounds62588 := by
 decide +kernel
def cuts62589 : List PrefixCut := [⟨64,199626281,199626400⟩]
theorem checked62589 : checkPrefixCuts (2^48) 8207597569 10 Manual.Count131072.C062589.packed 64 cuts62589 = true := by
 decide +kernel
def cuts62590 : List PrefixCut := [⟨46,140741286,140741365⟩,
⟨64,197394002,197394112⟩]
theorem checked62590 : checkPrefixCuts (2^48) 8207728641 10 Manual.Count131072.C062590.packed 64 cuts62590 = true := by
 decide +kernel
def pointBounds62590 : List (Nat × Nat × Nat) := [(8207822848,114438282170335,114438670876313)]
theorem point_links_checked62590 : (cuts62590.take 1).map (fun c => (8207728641-1+2*2^10*c.k,114438141429049+c.lower,114438530134948+c.upper)) = pointBounds62590 := by
 decide +kernel
def cuts62591 : List PrefixCut := [⟨64,199002645,199002758⟩]
theorem checked62591 : checkPrefixCuts (2^48) 8207859713 10 Manual.Count131072.C062591.packed 64 cuts62591 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000080
