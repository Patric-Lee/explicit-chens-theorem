import PlattAssemblyKernel
import PlattCertificates.Count131072.C051696
import PlattCertificates.Count131072.C051697
import PlattCertificates.Count131072.C051698
import PlattCertificates.Count131072.C051699
import PlattCertificates.Count131072.C051700
import PlattCertificates.Count131072.C051701
import PlattCertificates.Count131072.C051702
import PlattCertificates.Count131072.C051703
import PlattCertificates.Count131072.C051704
import PlattCertificates.Count131072.C051705
import PlattCertificates.Count131072.C051706
import PlattCertificates.Count131072.C051707
import PlattCertificates.Count131072.C051708
import PlattCertificates.Count131072.C051709
import PlattCertificates.Count131072.C051710
import PlattCertificates.Count131072.C051711
import PlattCertificates.Count131072.C051712
import PlattCertificates.Count131072.C051713
import PlattCertificates.Count131072.C051714
import PlattCertificates.Count131072.C051715
import PlattCertificates.Count131072.C051716
import PlattCertificates.Count131072.C051717
import PlattCertificates.Count131072.C051718
import PlattCertificates.Count131072.C051719
import PlattCertificates.Count131072.C051720
import PlattCertificates.Count131072.C051721
import PlattCertificates.Count131072.C051722
import PlattCertificates.Count131072.C051723
import PlattCertificates.Count131072.C051724
import PlattCertificates.Count131072.C051725
import PlattCertificates.Count131072.C051726
import PlattCertificates.Count131072.C051727
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51696 : List PrefixCut := [⟨64,239132792,239132928⟩]
theorem checked51696 : checkPrefixCuts (2^48) 6779830273 10 Manual.Count131072.C051696.packed 64 cuts51696 = true := by
 decide +kernel
def cuts51697 : List PrefixCut := [⟨19,72361677,72361718⟩,
⟨64,242283331,242283466⟩]
theorem checked51697 : checkPrefixCuts (2^48) 6779961345 10 Manual.Count131072.C051697.packed 64 cuts51697 = true := by
 decide +kernel
def pointBounds51697 : List (Nat × Nat × Nat) := [(6780000256,112072041060630,112072428418753)]
theorem point_links_checked51697 : (cuts51697.take 1).map (fun c => (6779961345-1+2*2^10*c.k,112071968698953+c.lower,112072356057035+c.upper)) = pointBounds51697 := by
 decide +kernel
def cuts51698 : List PrefixCut := [⟨59,222268810,222268940⟩,
⟨64,241157741,241157882⟩]
theorem checked51698 : checkPrefixCuts (2^48) 6780092417 10 Manual.Count131072.C051698.packed 64 cuts51698 = true := by
 decide +kernel
def pointBounds51698 : List (Nat × Nat × Nat) := [(6780213248,112072433251094,112072820609441)]
theorem point_links_checked51698 : (cuts51698.take 1).map (fun c => (6780092417-1+2*2^10*c.k,112072210982284+c.lower,112072598340501+c.upper)) = pointBounds51698 := by
 decide +kernel
def cuts51699 : List PrefixCut := [⟨64,245013872,245014010⟩]
theorem checked51699 : checkPrefixCuts (2^48) 6780223489 10 Manual.Count131072.C051699.packed 64 cuts51699 = true := by
 decide +kernel
def cuts51700 : List PrefixCut := [⟨35,130641663,130641738⟩,
⟨64,237536811,237536946⟩]
theorem checked51700 : checkPrefixCuts (2^48) 6780354561 10 Manual.Count131072.C051700.packed 64 cuts51700 = true := by
 decide +kernel
def pointBounds51700 : List (Nat × Nat × Nat) := [(6780426240,112072827795560,112073215154131)]
theorem point_links_checked51700 : (cuts51700.take 1).map (fun c => (6780354561-1+2*2^10*c.k,112072697153897+c.lower,112073084512393+c.upper)) = pointBounds51700 := by
 decide +kernel
def cuts51701 : List PrefixCut := [⟨64,243302360,243302495⟩]
theorem checked51701 : checkPrefixCuts (2^48) 6780485633 10 Manual.Count131072.C051701.packed 64 cuts51701 = true := by
 decide +kernel
def cuts51702 : List PrefixCut := [⟨11,39602093,39602117⟩,
⟨64,237486103,237486245⟩]
theorem checked51702 : checkPrefixCuts (2^48) 6780616705 10 Manual.Count131072.C051702.packed 64 cuts51702 = true := by
 decide +kernel
def pointBounds51702 : List (Nat × Nat × Nat) := [(6780639232,112073217595161,112073604953951)]
theorem point_links_checked51702 : (cuts51702.take 1).map (fun c => (6780616705-1+2*2^10*c.k,112073177993068+c.lower,112073565351834+c.upper)) = pointBounds51702 := by
 decide +kernel
def cuts51703 : List PrefixCut := [⟨51,191986403,191986511⟩,
⟨64,240760855,240760992⟩]
theorem checked51703 : checkPrefixCuts (2^48) 6780747777 10 Manual.Count131072.C051703.packed 64 cuts51703 = true := by
 decide +kernel
def pointBounds51703 : List (Nat × Nat × Nat) := [(6780852224,112073607465574,112073994824590)]
theorem point_links_checked51703 : (cuts51703.take 1).map (fun c => (6780747777-1+2*2^10*c.k,112073415479171+c.lower,112073802838079+c.upper)) = pointBounds51703 := by
 decide +kernel
def cuts51704 : List PrefixCut := [⟨64,242956207,242956345⟩]
theorem checked51704 : checkPrefixCuts (2^48) 6780878849 10 Manual.Count131072.C051704.packed 64 cuts51704 = true := by
 decide +kernel
def cuts51705 : List PrefixCut := [⟨27,99663398,99663456⟩,
⟨64,240668521,240668658⟩]
theorem checked51705 : checkPrefixCuts (2^48) 6781009921 10 Manual.Count131072.C051705.packed 64 cuts51705 = true := by
 decide +kernel
def pointBounds51705 : List (Nat × Nat × Nat) := [(6781065216,112073998859631,112074386218872)]
theorem point_links_checked51705 : (cuts51705.take 1).map (fun c => (6781009921-1+2*2^10*c.k,112073899196233+c.lower,112074286555416+c.upper)) = pointBounds51705 := by
 decide +kernel
def cuts51706 : List PrefixCut := [⟨64,240331818,240331951⟩]
theorem checked51706 : checkPrefixCuts (2^48) 6781140993 10 Manual.Count131072.C051706.packed 64 cuts51706 = true := by
 decide +kernel
def cuts51707 : List PrefixCut := [⟨3,11207070,11207077⟩,
⟨64,241074298,241074431⟩]
theorem checked51707 : checkPrefixCuts (2^48) 6781272065 10 Manual.Count131072.C051707.packed 64 cuts51707 = true := by
 decide +kernel
def pointBounds51707 : List (Nat × Nat × Nat) := [(6781278208,112074391403642,112074778763102)]
theorem point_links_checked51707 : (cuts51707.take 1).map (fun c => (6781272065-1+2*2^10*c.k,112074380196572+c.lower,112074767556025+c.upper)) = pointBounds51707 := by
 decide +kernel
def cuts51708 : List PrefixCut := [⟨43,162373860,162373949⟩,
⟨64,239865957,239866092⟩]
theorem checked51708 : checkPrefixCuts (2^48) 6781403137 10 Manual.Count131072.C051708.packed 64 cuts51708 = true := by
 decide +kernel
def pointBounds51708 : List (Nat × Nat × Nat) := [(6781491200,112074783644730,112075171004405)]
theorem point_links_checked51708 : (cuts51708.take 1).map (fun c => (6781403137-1+2*2^10*c.k,112074621270870+c.lower,112075008630456+c.upper)) = pointBounds51708 := by
 decide +kernel
def cuts51709 : List PrefixCut := [⟨64,244219400,244219538⟩]
theorem checked51709 : checkPrefixCuts (2^48) 6781534209 10 Manual.Count131072.C051709.packed 64 cuts51709 = true := by
 decide +kernel
def cuts51710 : List PrefixCut := [⟨19,70019203,70019244⟩,
⟨64,239607636,239607770⟩]
theorem checked51710 : checkPrefixCuts (2^48) 6781665281 10 Manual.Count131072.C051710.packed 64 cuts51710 = true := by
 decide +kernel
def pointBounds51710 : List (Nat × Nat × Nat) := [(6781704192,112075175375430,112075562735330)]
theorem point_links_checked51710 : (cuts51710.take 1).map (fun c => (6781665281-1+2*2^10*c.k,112075105356227+c.lower,112075492716086+c.upper)) = pointBounds51710 := by
 decide +kernel
def cuts51711 : List PrefixCut := [⟨59,222171459,222171588⟩,
⟨64,240557600,240557740⟩]
theorem checked51711 : checkPrefixCuts (2^48) 6781796353 10 Manual.Count131072.C051711.packed 64 cuts51711 = true := by
 decide +kernel
def pointBounds51711 : List (Nat × Nat × Nat) := [(6781917184,112075567135322,112075954495444)]
theorem point_links_checked51711 : (cuts51711.take 1).map (fun c => (6781796353-1+2*2^10*c.k,112075344963863+c.lower,112075732323856+c.upper)) = pointBounds51711 := by
 decide +kernel
def cuts51712 : List PrefixCut := [⟨64,240054918,240055056⟩]
theorem checked51712 : checkPrefixCuts (2^48) 6781927425 10 Manual.Count131072.C051712.packed 64 cuts51712 = true := by
 decide +kernel
def cuts51713 : List PrefixCut := [⟨35,129820295,129820371⟩,
⟨64,238473184,238473319⟩]
theorem checked51713 : checkPrefixCuts (2^48) 6782058497 10 Manual.Count131072.C051713.packed 64 cuts51713 = true := by
 decide +kernel
def pointBounds51713 : List (Nat × Nat × Nat) := [(6782130176,112075955396676,112076342757023)]
theorem point_links_checked51713 : (cuts51713.take 1).map (fun c => (6782058497-1+2*2^10*c.k,112075825576381+c.lower,112076212936652+c.upper)) = pointBounds51713 := by
 decide +kernel
def cuts51714 : List PrefixCut := [⟨64,242245240,242245377⟩]
theorem checked51714 : checkPrefixCuts (2^48) 6782189569 10 Manual.Count131072.C051714.packed 64 cuts51714 = true := by
 decide +kernel
def cuts51715 : List PrefixCut := [⟨11,41957710,41957734⟩,
⟨64,237426471,237426606⟩]
theorem checked51715 : checkPrefixCuts (2^48) 6782320641 10 Manual.Count131072.C051715.packed 64 cuts51715 = true := by
 decide +kernel
def pointBounds51715 : List (Nat × Nat × Nat) := [(6782343168,112076348252515,112076735613082)]
theorem point_links_checked51715 : (cuts51715.take 1).map (fun c => (6782320641-1+2*2^10*c.k,112076306294805+c.lower,112076693655348+c.upper)) = pointBounds51715 := by
 decide +kernel
def cuts51716 : List PrefixCut := [⟨51,190236655,190236768⟩,
⟨64,238832852,238832995⟩]
theorem checked51716 : checkPrefixCuts (2^48) 6782451713 10 Manual.Count131072.C051716.packed 64 cuts51716 = true := by
 decide +kernel
def pointBounds51716 : List (Nat × Nat × Nat) := [(6782556160,112076733957931,112077121318722)]
theorem point_links_checked51716 : (cuts51716.take 1).map (fun c => (6782451713-1+2*2^10*c.k,112076543721276+c.lower,112076931081954+c.upper)) = pointBounds51716 := by
 decide +kernel
def cuts51717 : List PrefixCut := [⟨64,238869731,238869869⟩]
theorem checked51717 : checkPrefixCuts (2^48) 6782582785 10 Manual.Count131072.C051717.packed 64 cuts51717 = true := by
 decide +kernel
def cuts51718 : List PrefixCut := [⟨27,101630299,101630356⟩,
⟨64,242724489,242724626⟩]
theorem checked51718 : checkPrefixCuts (2^48) 6782713857 10 Manual.Count131072.C051718.packed 64 cuts51718 = true := by
 decide +kernel
def pointBounds51718 : List (Nat × Nat × Nat) := [(6782769152,112077123054158,112077510415174)]
theorem point_links_checked51718 : (cuts51718.take 1).map (fun c => (6782713857-1+2*2^10*c.k,112077021423859+c.lower,112077408784818+c.upper)) = pointBounds51718 := by
 decide +kernel
def cuts51719 : List PrefixCut := [⟨64,239358488,239358625⟩]
theorem checked51719 : checkPrefixCuts (2^48) 6782844929 10 Manual.Count131072.C051719.packed 64 cuts51719 = true := by
 decide +kernel
def cuts51720 : List PrefixCut := [⟨3,11536232,11536239⟩,
⟨64,239312364,239312498⟩]
theorem checked51720 : checkPrefixCuts (2^48) 6782976001 10 Manual.Count131072.C051720.packed 64 cuts51720 = true := by
 decide +kernel
def pointBounds51720 : List (Nat × Nat × Nat) := [(6782982144,112077515043068,112077902404308)]
theorem point_links_checked51720 : (cuts51720.take 1).map (fun c => (6782976001-1+2*2^10*c.k,112077503506836+c.lower,112077890868069+c.upper)) = pointBounds51720 := by
 decide +kernel
def cuts51721 : List PrefixCut := [⟨43,160175278,160175371⟩,
⟨64,239556714,239556854⟩]
theorem checked51721 : checkPrefixCuts (2^48) 6783107073 10 Manual.Count131072.C051721.packed 64 cuts51721 = true := by
 decide +kernel
def pointBounds51721 : List (Nat × Nat × Nat) := [(6783195136,112077902994478,112078290355938)]
theorem point_links_checked51721 : (cuts51721.take 1).map (fun c => (6783107073-1+2*2^10*c.k,112077742819200+c.lower,112078130180567+c.upper)) = pointBounds51721 := by
 decide +kernel
def cuts51722 : List PrefixCut := [⟨64,238888172,238888307⟩]
theorem checked51722 : checkPrefixCuts (2^48) 6783238145 10 Manual.Count131072.C051722.packed 64 cuts51722 = true := by
 decide +kernel
def cuts51723 : List PrefixCut := [⟨19,72242333,72242373⟩,
⟨64,239920922,239921060⟩]
theorem checked51723 : checkPrefixCuts (2^48) 6783369217 10 Manual.Count131072.C051723.packed 64 cuts51723 = true := by
 decide +kernel
def pointBounds51723 : List (Nat × Nat × Nat) := [(6783408128,112078293506419,112078680868101)]
theorem point_links_checked51723 : (cuts51723.take 1).map (fun c => (6783369217-1+2*2^10*c.k,112078221264086+c.lower,112078608625728+c.upper)) = pointBounds51723 := by
 decide +kernel
def cuts51724 : List PrefixCut := [⟨59,221368782,221368910⟩,
⟨64,240082251,240082390⟩]
theorem checked51724 : checkPrefixCuts (2^48) 6783500289 10 Manual.Count131072.C051724.packed 64 cuts51724 = true := by
 decide +kernel
def pointBounds51724 : List (Nat × Nat × Nat) := [(6783621120,112078682553790,112079069915698)]
theorem point_links_checked51724 : (cuts51724.take 1).map (fun c => (6783500289-1+2*2^10*c.k,112078461185008+c.lower,112078848546788+c.upper)) = pointBounds51724 := by
 decide +kernel
def cuts51725 : List PrefixCut := [⟨64,241114931,241115070⟩]
theorem checked51725 : checkPrefixCuts (2^48) 6783631361 10 Manual.Count131072.C051725.packed 64 cuts51725 = true := by
 decide +kernel
def cuts51726 : List PrefixCut := [⟨35,130907971,130908045⟩,
⟨64,240155954,240156090⟩]
theorem checked51726 : checkPrefixCuts (2^48) 6783762433 10 Manual.Count131072.C051726.packed 64 cuts51726 = true := by
 decide +kernel
def pointBounds51726 : List (Nat × Nat × Nat) := [(6783834112,112079073290161,112079460652293)]
theorem point_links_checked51726 : (cuts51726.take 1).map (fun c => (6783762433-1+2*2^10*c.k,112078942382190+c.lower,112079329744248+c.upper)) = pointBounds51726 := by
 decide +kernel
def cuts51727 : List PrefixCut := [⟨64,235919234,235919371⟩]
theorem checked51727 : checkPrefixCuts (2^48) 6783893505 10 Manual.Count131072.C051727.packed 64 cuts51727 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000053
