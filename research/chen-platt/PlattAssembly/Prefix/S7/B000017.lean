import PlattAssemblyKernel
import PlattCertificates.Count131072.C060544
import PlattCertificates.Count131072.C060545
import PlattCertificates.Count131072.C060546
import PlattCertificates.Count131072.C060547
import PlattCertificates.Count131072.C060548
import PlattCertificates.Count131072.C060549
import PlattCertificates.Count131072.C060550
import PlattCertificates.Count131072.C060551
import PlattCertificates.Count131072.C060552
import PlattCertificates.Count131072.C060553
import PlattCertificates.Count131072.C060554
import PlattCertificates.Count131072.C060555
import PlattCertificates.Count131072.C060556
import PlattCertificates.Count131072.C060557
import PlattCertificates.Count131072.C060558
import PlattCertificates.Count131072.C060559
import PlattCertificates.Count131072.C060560
import PlattCertificates.Count131072.C060561
import PlattCertificates.Count131072.C060562
import PlattCertificates.Count131072.C060563
import PlattCertificates.Count131072.C060564
import PlattCertificates.Count131072.C060565
import PlattCertificates.Count131072.C060566
import PlattCertificates.Count131072.C060567
import PlattCertificates.Count131072.C060568
import PlattCertificates.Count131072.C060569
import PlattCertificates.Count131072.C060570
import PlattCertificates.Count131072.C060571
import PlattCertificates.Count131072.C060572
import PlattCertificates.Count131072.C060573
import PlattCertificates.Count131072.C060574
import PlattCertificates.Count131072.C060575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60544 : List PrefixCut := [⟨4,12479176,12479184⟩,
⟨64,203352280,203352396⟩]
theorem checked60544 : checkPrefixCuts (2^48) 7939555329 10 Manual.Count131072.C060544.packed 64 cuts60544 = true := by
 decide +kernel
def pointBounds60544 : List (Nat × Nat × Nat) := [(7939563520,114028224925617,114028613396560)]
theorem point_links_checked60544 : (cuts60544.take 1).map (fun c => (7939555329-1+2*2^10*c.k,114028212446441+c.lower,114028600917376+c.upper)) = pointBounds60544 := by
 decide +kernel
def cuts60545 : List PrefixCut := [⟨62,198456682,198456791⟩,
⟨64,204802422,204802535⟩]
theorem checked60545 : checkPrefixCuts (2^48) 7939686401 10 Manual.Count131072.C060545.packed 64 cuts60545 = true := by
 decide +kernel
def pointBounds60545 : List (Nat × Nat × Nat) := [(7939813376,114028614255403,114029002726563)]
theorem point_links_checked60545 : (cuts60545.take 1).map (fun c => (7939686401-1+2*2^10*c.k,114028415798721+c.lower,114028804269772+c.upper)) = pointBounds60545 := by
 decide +kernel
def cuts60546 : List PrefixCut := [⟨64,201147619,201147738⟩]
theorem checked60546 : checkPrefixCuts (2^48) 7939817473 10 Manual.Count131072.C060546.packed 64 cuts60546 = true := by
 decide +kernel
def cuts60547 : List PrefixCut := [⟨56,174592301,174592404⟩,
⟨64,200116242,200116361⟩]
theorem checked60547 : checkPrefixCuts (2^48) 7939948545 10 Manual.Count131072.C060547.packed 64 cuts60547 = true := by
 decide +kernel
def pointBounds60547 : List (Nat × Nat × Nat) := [(7940063232,114028996341063,114029384812449)]
theorem point_links_checked60547 : (cuts60547.take 1).map (fun c => (7939948545-1+2*2^10*c.k,114028821748762+c.lower,114029210220045+c.upper)) = pointBounds60547 := by
 decide +kernel
def cuts60548 : List PrefixCut := [⟨64,202878008,202878122⟩]
theorem checked60548 : checkPrefixCuts (2^48) 7940079617 10 Manual.Count131072.C060548.packed 64 cuts60548 = true := by
 decide +kernel
def cuts60549 : List PrefixCut := [⟨50,157783823,157783918⟩,
⟨64,201775757,201775874⟩]
theorem checked60549 : checkPrefixCuts (2^48) 7940210689 10 Manual.Count131072.C060549.packed 64 cuts60549 = true := by
 decide +kernel
def pointBounds60549 : List (Nat × Nat × Nat) := [(7940313088,114029382526835,114029770998446)]
theorem point_links_checked60549 : (cuts60549.take 1).map (fun c => (7940210689-1+2*2^10*c.k,114029224743012+c.lower,114029613214528+c.upper)) = pointBounds60549 := by
 decide +kernel
def cuts60550 : List PrefixCut := [⟨64,203615719,203615839⟩]
theorem checked60550 : checkPrefixCuts (2^48) 7940341761 10 Manual.Count131072.C060550.packed 64 cuts60550 = true := by
 decide +kernel
def cuts60551 : List PrefixCut := [⟨44,140976406,140976485⟩,
⟨64,204037749,204037865⟩]
theorem checked60551 : checkPrefixCuts (2^48) 7940472833 10 Manual.Count131072.C060551.packed 64 cuts60551 = true := by
 decide +kernel
def pointBounds60551 : List (Nat × Nat × Nat) := [(7940562944,114029771110894,114030159582726)]
theorem point_links_checked60551 : (cuts60551.take 1).map (fun c => (7940472833-1+2*2^10*c.k,114029630134488+c.lower,114030018606241+c.upper)) = pointBounds60551 := by
 decide +kernel
def cuts60552 : List PrefixCut := [⟨64,204778766,204778879⟩]
theorem checked60552 : checkPrefixCuts (2^48) 7940603905 10 Manual.Count131072.C060552.packed 64 cuts60552 = true := by
 decide +kernel
def cuts60553 : List PrefixCut := [⟨38,121121658,121121728⟩,
⟨64,204598140,204598259⟩]
theorem checked60553 : checkPrefixCuts (2^48) 7940734977 10 Manual.Count131072.C060553.packed 64 cuts60553 = true := by
 decide +kernel
def pointBounds60553 : List (Nat × Nat × Nat) := [(7940812800,114030160072661,114030548544713)]
theorem point_links_checked60553 : (cuts60553.take 1).map (fun c => (7940734977-1+2*2^10*c.k,114030038951003+c.lower,114030427422985+c.upper)) = pointBounds60553 := by
 decide +kernel
def cuts60554 : List PrefixCut := [⟨64,209131851,209131972⟩]
theorem checked60554 : checkPrefixCuts (2^48) 7940866049 10 Manual.Count131072.C060554.packed 64 cuts60554 = true := by
 decide +kernel
def cuts60555 : List PrefixCut := [⟨32,103075917,103075976⟩,
⟨64,203882485,203882603⟩]
theorem checked60555 : checkPrefixCuts (2^48) 7940997121 10 Manual.Count131072.C060555.packed 64 cuts60555 = true := by
 decide +kernel
def pointBounds60555 : List (Nat × Nat × Nat) := [(7941062656,114030555756911,114030944229192)]
theorem point_links_checked60555 : (cuts60555.take 1).map (fun c => (7940997121-1+2*2^10*c.k,114030452680994+c.lower,114030841153216+c.upper)) = pointBounds60555 := by
 decide +kernel
def cuts60556 : List PrefixCut := [⟨64,203879123,203879242⟩]
theorem checked60556 : checkPrefixCuts (2^48) 7941128193 10 Manual.Count131072.C060556.packed 64 cuts60556 = true := by
 decide +kernel
def cuts60557 : List PrefixCut := [⟨26,83117352,83117396⟩,
⟨64,204726419,204726533⟩]
theorem checked60557 : checkPrefixCuts (2^48) 7941259265 10 Manual.Count131072.C060557.packed 64 cuts60557 = true := by
 decide +kernel
def pointBounds60557 : List (Nat × Nat × Nat) := [(7941312512,114030943559954,114031332032457)]
theorem point_links_checked60557 : (cuts60557.take 1).map (fun c => (7941259265-1+2*2^10*c.k,114030860442602+c.lower,114031248915061+c.upper)) = pointBounds60557 := by
 decide +kernel
def cuts60558 : List PrefixCut := [⟨64,202738179,202738295⟩]
theorem checked60558 : checkPrefixCuts (2^48) 7941390337 10 Manual.Count131072.C060558.packed 64 cuts60558 = true := by
 decide +kernel
def cuts60559 : List PrefixCut := [⟨20,64932226,64932263⟩,
⟨64,207732334,207732449⟩]
theorem checked60559 : checkPrefixCuts (2^48) 7941521409 10 Manual.Count131072.C060559.packed 64 cuts60559 = true := by
 decide +kernel
def pointBounds60559 : List (Nat × Nat × Nat) := [(7941562368,114031332839426,114031721312152)]
theorem point_links_checked60559 : (cuts60559.take 1).map (fun c => (7941521409-1+2*2^10*c.k,114031267907200+c.lower,114031656379889+c.upper)) = pointBounds60559 := by
 decide +kernel
def cuts60560 : List PrefixCut := [⟨64,201880885,201881002⟩]
theorem checked60560 : checkPrefixCuts (2^48) 7941652481 10 Manual.Count131072.C060560.packed 64 cuts60560 = true := by
 decide +kernel
def cuts60561 : List PrefixCut := [⟨14,44586306,44586331⟩,
⟨64,202373750,202373859⟩]
theorem checked60561 : checkPrefixCuts (2^48) 7941783553 10 Manual.Count131072.C060561.packed 64 cuts60561 = true := by
 decide +kernel
def pointBounds60561 : List (Nat × Nat × Nat) := [(7941812224,114031722106725,114032110579671)]
theorem point_links_checked60561 : (cuts60561.take 1).map (fun c => (7941783553-1+2*2^10*c.k,114031677520419+c.lower,114032065993340+c.upper)) = pointBounds60561 := by
 decide +kernel
def cuts60562 : List PrefixCut := [⟨64,200633762,200633868⟩]
theorem checked60562 : checkPrefixCuts (2^48) 7941914625 10 Manual.Count131072.C060562.packed 64 cuts60562 = true := by
 decide +kernel
def cuts60563 : List PrefixCut := [⟨8,24596102,24596117⟩,
⟨64,202650572,202650692⟩]
theorem checked60563 : checkPrefixCuts (2^48) 7942045697 10 Manual.Count131072.C060563.packed 64 cuts60563 = true := by
 decide +kernel
def pointBounds60563 : List (Nat × Nat × Nat) := [(7942062080,114032105124033,114032493597184)]
theorem point_links_checked60563 : (cuts60563.take 1).map (fun c => (7942045697-1+2*2^10*c.k,114032080527931+c.lower,114032469001067+c.upper)) = pointBounds60563 := by
 decide +kernel
def cuts60564 : List PrefixCut := [⟨64,202824435,202824551⟩]
theorem checked60564 : checkPrefixCuts (2^48) 7942176769 10 Manual.Count131072.C060564.packed 64 cuts60564 = true := by
 decide +kernel
def cuts60565 : List PrefixCut := [⟨2,5741268,5741272⟩,
⟨64,204734826,204734942⟩]
theorem checked60565 : checkPrefixCuts (2^48) 7942307841 10 Manual.Count131072.C060565.packed 64 cuts60565 = true := by
 decide +kernel
def pointBounds60565 : List (Nat × Nat × Nat) := [(7942311936,114032491744206,114032880217582)]
theorem point_links_checked60565 : (cuts60565.take 1).map (fun c => (7942307841-1+2*2^10*c.k,114032486002938+c.lower,114032874476310+c.upper)) = pointBounds60565 := by
 decide +kernel
def cuts60566 : List PrefixCut := [⟨60,190803990,190804102⟩,
⟨64,204199852,204199971⟩]
theorem checked60566 : checkPrefixCuts (2^48) 7942438913 10 Manual.Count131072.C060566.packed 64 cuts60566 = true := by
 decide +kernel
def pointBounds60566 : List (Nat × Nat × Nat) := [(7942561792,114032881541754,114033270015354)]
theorem point_links_checked60566 : (cuts60566.take 1).map (fun c => (7942438913-1+2*2^10*c.k,114032690737764+c.lower,114033079211252+c.upper)) = pointBounds60566 := by
 decide +kernel
def cuts60567 : List PrefixCut := [⟨64,201325983,201326094⟩]
theorem checked60567 : checkPrefixCuts (2^48) 7942569985 10 Manual.Count131072.C060567.packed 64 cuts60567 = true := by
 decide +kernel
def cuts60568 : List PrefixCut := [⟨54,170456466,170456564⟩,
⟨64,203696976,203697093⟩]
theorem checked60568 : checkPrefixCuts (2^48) 7942701057 10 Manual.Count131072.C060568.packed 64 cuts60568 = true := by
 decide +kernel
def pointBounds60568 : List (Nat × Nat × Nat) := [(7942811648,114033266720065,114033655193881)]
theorem point_links_checked60568 : (cuts60568.take 1).map (fun c => (7942701057-1+2*2^10*c.k,114033096263599+c.lower,114033484737317+c.upper)) = pointBounds60568 := by
 decide +kernel
def cuts60569 : List PrefixCut := [⟨64,205500931,205501048⟩]
theorem checked60569 : checkPrefixCuts (2^48) 7942832129 10 Manual.Count131072.C060569.packed 64 cuts60569 = true := by
 decide +kernel
def cuts60570 : List PrefixCut := [⟨48,155354900,155354986⟩,
⟨64,206879573,206879687⟩]
theorem checked60570 : checkPrefixCuts (2^48) 7942963201 10 Manual.Count131072.C060570.packed 64 cuts60570 = true := by
 decide +kernel
def pointBounds60570 : List (Nat × Nat × Nat) := [(7943061504,114033660816406,114034049290444)]
theorem point_links_checked60570 : (cuts60570.take 1).map (fun c => (7942963201-1+2*2^10*c.k,114033505461506+c.lower,114033893935458+c.upper)) = pointBounds60570 := by
 decide +kernel
def cuts60571 : List PrefixCut := [⟨64,205352415,205352528⟩]
theorem checked60571 : checkPrefixCuts (2^48) 7943094273 10 Manual.Count131072.C060571.packed 64 cuts60571 = true := by
 decide +kernel
def cuts60572 : List PrefixCut := [⟨42,132423035,132423108⟩,
⟨64,202549618,202549727⟩]
theorem checked60572 : checkPrefixCuts (2^48) 7943225345 10 Manual.Count131072.C060572.packed 64 cuts60572 = true := by
 decide +kernel
def pointBounds60572 : List (Nat × Nat × Nat) := [(7943311360,114034050116529,114034438590781)]
theorem point_links_checked60572 : (cuts60572.take 1).map (fun c => (7943225345-1+2*2^10*c.k,114033917693494+c.lower,114034306167673+c.upper)) = pointBounds60572 := by
 decide +kernel
def cuts60573 : List PrefixCut := [⟨64,201199726,201199839⟩]
theorem checked60573 : checkPrefixCuts (2^48) 7943356417 10 Manual.Count131072.C060573.packed 64 cuts60573 = true := by
 decide +kernel
def cuts60574 : List PrefixCut := [⟨36,112150229,112150294⟩,
⟨64,202117715,202117829⟩]
theorem checked60574 : checkPrefixCuts (2^48) 7943487489 10 Manual.Count131072.C060574.packed 64 cuts60574 = true := by
 decide +kernel
def pointBounds60574 : List (Nat × Nat × Nat) := [(7943561216,114034433593067,114034822067533)]
theorem point_links_checked60574 : (cuts60574.take 1).map (fun c => (7943487489-1+2*2^10*c.k,114034321442838+c.lower,114034709917239+c.upper)) = pointBounds60574 := by
 decide +kernel
def cuts60575 : List PrefixCut := [⟨64,202433295,202433413⟩]
theorem checked60575 : checkPrefixCuts (2^48) 7943618561 10 Manual.Count131072.C060575.packed 64 cuts60575 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000017
