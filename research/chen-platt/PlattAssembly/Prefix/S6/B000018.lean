import PlattAssemblyKernel
import PlattCertificates.Count131072.C050576
import PlattCertificates.Count131072.C050577
import PlattCertificates.Count131072.C050578
import PlattCertificates.Count131072.C050579
import PlattCertificates.Count131072.C050580
import PlattCertificates.Count131072.C050581
import PlattCertificates.Count131072.C050582
import PlattCertificates.Count131072.C050583
import PlattCertificates.Count131072.C050584
import PlattCertificates.Count131072.C050585
import PlattCertificates.Count131072.C050586
import PlattCertificates.Count131072.C050587
import PlattCertificates.Count131072.C050588
import PlattCertificates.Count131072.C050589
import PlattCertificates.Count131072.C050590
import PlattCertificates.Count131072.C050591
import PlattCertificates.Count131072.C050592
import PlattCertificates.Count131072.C050593
import PlattCertificates.Count131072.C050594
import PlattCertificates.Count131072.C050595
import PlattCertificates.Count131072.C050596
import PlattCertificates.Count131072.C050597
import PlattCertificates.Count131072.C050598
import PlattCertificates.Count131072.C050599
import PlattCertificates.Count131072.C050600
import PlattCertificates.Count131072.C050601
import PlattCertificates.Count131072.C050602
import PlattCertificates.Count131072.C050603
import PlattCertificates.Count131072.C050604
import PlattCertificates.Count131072.C050605
import PlattCertificates.Count131072.C050606
import PlattCertificates.Count131072.C050607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50576 : List PrefixCut := [⟨64,244891965,244892108⟩]
theorem checked50576 : checkPrefixCuts (2^48) 6633029633 10 Manual.Count131072.C050576.packed 64 cuts50576 = true := by
 decide +kernel
def cuts50577 : List PrefixCut := [⟨16,61954224,61954261⟩,
⟨64,245184160,245184303⟩]
theorem checked50577 : checkPrefixCuts (2^48) 6633160705 10 Manual.Count131072.C050577.packed 64 cuts50577 = true := by
 decide +kernel
def pointBounds50577 : List (Nat × Nat × Nat) := [(6633193472,111799708203216,111800095406520)]
theorem point_links_checked50577 : (cuts50577.take 1).map (fun c => (6633160705-1+2*2^10*c.k,111799646248992+c.lower,111800033452259+c.upper)) = pointBounds50577 := by
 decide +kernel
def cuts50578 : List PrefixCut := [⟨54,209747876,209747994⟩,
⟨64,249125605,249125744⟩]
theorem checked50578 : checkPrefixCuts (2^48) 6633291777 10 Manual.Count131072.C050578.packed 64 cuts50578 = true := by
 decide +kernel
def pointBounds50578 : List (Nat × Nat × Nat) := [(6633402368,111800101181028,111800488384556)]
theorem point_links_checked50578 : (cuts50578.take 1).map (fun c => (6633291777-1+2*2^10*c.k,111799891433152+c.lower,111800278636562+c.upper)) = pointBounds50578 := by
 decide +kernel
def cuts50579 : List PrefixCut := [⟨64,245344194,245344333⟩]
theorem checked50579 : checkPrefixCuts (2^48) 6633422849 10 Manual.Count131072.C050579.packed 64 cuts50579 = true := by
 decide +kernel
def cuts50580 : List PrefixCut := [⟨28,107267610,107267674⟩,
⟨64,244745305,244745447⟩]
theorem checked50580 : checkPrefixCuts (2^48) 6633553921 10 Manual.Count131072.C050580.packed 64 cuts50580 = true := by
 decide +kernel
def pointBounds50580 : List (Nat × Nat × Nat) := [(6633611264,111800493170561,111800880374313)]
theorem point_links_checked50580 : (cuts50580.take 1).map (fun c => (6633553921-1+2*2^10*c.k,111800385902951+c.lower,111800773106639+c.upper)) = pointBounds50580 := by
 decide +kernel
def cuts50581 : List PrefixCut := [⟨64,241727875,241728013⟩]
theorem checked50581 : checkPrefixCuts (2^48) 6633684993 10 Manual.Count131072.C050581.packed 64 cuts50581 = true := by
 decide +kernel
def cuts50582 : List PrefixCut := [⟨2,7552593,7552598⟩,
⟨64,243632464,243632605⟩]
theorem checked50582 : checkPrefixCuts (2^48) 6633816065 10 Manual.Count131072.C050582.packed 64 cuts50582 = true := by
 decide +kernel
def pointBounds50582 : List (Nat × Nat × Nat) := [(6633820160,111800879928724,111801267132697)]
theorem point_links_checked50582 : (cuts50582.take 1).map (fun c => (6633816065-1+2*2^10*c.k,111800872376131+c.lower,111801259580099+c.upper)) = pointBounds50582 := by
 decide +kernel
def cuts50583 : List PrefixCut := [⟨40,150963149,150963234⟩,
⟨64,242227485,242227623⟩]
theorem checked50583 : checkPrefixCuts (2^48) 6633947137 10 Manual.Count131072.C050583.packed 64 cuts50583 = true := by
 decide +kernel
def pointBounds50583 : List (Nat × Nat × Nat) := [(6634029056,111801266971744,111801654175938)]
theorem point_links_checked50583 : (cuts50583.take 1).map (fun c => (6633947137-1+2*2^10*c.k,111801116008595+c.lower,111801503212704+c.upper)) = pointBounds50583 := by
 decide +kernel
def cuts50584 : List PrefixCut := [⟨64,242816678,242816815⟩]
theorem checked50584 : checkPrefixCuts (2^48) 6634078209 10 Manual.Count131072.C050584.packed 64 cuts50584 = true := by
 decide +kernel
def cuts50585 : List PrefixCut := [⟨14,53883185,53883215⟩,
⟨64,247351620,247351760⟩]
theorem checked50585 : checkPrefixCuts (2^48) 6634209281 10 Manual.Count131072.C050585.packed 64 cuts50585 = true := by
 decide +kernel
def pointBounds50585 : List (Nat × Nat × Nat) := [(6634237952,111801654935943,111802042140357)]
theorem point_links_checked50585 : (cuts50585.take 1).map (fun c => (6634209281-1+2*2^10*c.k,111801601052758+c.lower,111801988257142+c.upper)) = pointBounds50585 := by
 decide +kernel
def cuts50586 : List PrefixCut := [⟨52,196604959,196605073⟩,
⟨64,244164731,244164873⟩]
theorem checked50586 : checkPrefixCuts (2^48) 6634340353 10 Manual.Count131072.C050586.packed 64 cuts50586 = true := by
 decide +kernel
def pointBounds50586 : List (Nat × Nat × Nat) := [(6634446848,111802045009337,111802432213975)]
theorem point_links_checked50586 : (cuts50586.take 1).map (fun c => (6634340353-1+2*2^10*c.k,111801848404378+c.lower,111802235608902+c.upper)) = pointBounds50586 := by
 decide +kernel
def cuts50587 : List PrefixCut := [⟨64,248954016,248954160⟩]
theorem checked50587 : checkPrefixCuts (2^48) 6634471425 10 Manual.Count131072.C050587.packed 64 cuts50587 = true := by
 decide +kernel
def cuts50588 : List PrefixCut := [⟨26,101820275,101820334⟩,
⟨64,249882461,249882604⟩]
theorem checked50588 : checkPrefixCuts (2^48) 6634602497 10 Manual.Count131072.C050588.packed 64 cuts50588 = true := by
 decide +kernel
def pointBounds50588 : List (Nat × Nat × Nat) := [(6634655744,111802443343400,111802830548269)]
theorem point_links_checked50588 : (cuts50588.take 1).map (fun c => (6634602497-1+2*2^10*c.k,111802341523125+c.lower,111802728727935+c.upper)) = pointBounds50588 := by
 decide +kernel
def cuts50589 : List PrefixCut := [⟨64,243513910,243514051⟩]
theorem checked50589 : checkPrefixCuts (2^48) 6634733569 10 Manual.Count131072.C050589.packed 64 cuts50589 = true := by
 decide +kernel
def pointBounds50589 : List (Nat × Nat × Nat) := [(6634864640,111802834919496,111803222124590)]
theorem point_links_checked50589 : (cuts50589.take 1).map (fun c => (6634733569-1+2*2^10*c.k,111802591405586+c.lower,111802978610539+c.upper)) = pointBounds50589 := by
 decide +kernel
def cuts50590 : List PrefixCut := [⟨64,243084870,243085007⟩]
theorem checked50590 : checkPrefixCuts (2^48) 6634864641 10 Manual.Count131072.C050590.packed 64 cuts50590 = true := by
 decide +kernel
def cuts50591 : List PrefixCut := [⟨38,143854781,143854860⟩,
⟨64,243504299,243504434⟩]
theorem checked50591 : checkPrefixCuts (2^48) 6634995713 10 Manual.Count131072.C050591.packed 64 cuts50591 = true := by
 decide +kernel
def pointBounds50591 : List (Nat × Nat × Nat) := [(6635073536,111803221859147,111803609064457)]
theorem point_links_checked50591 : (cuts50591.take 1).map (fun c => (6634995713-1+2*2^10*c.k,111803078004366+c.lower,111803465209597+c.upper)) = pointBounds50591 := by
 decide +kernel
def cuts50592 : List PrefixCut := [⟨64,248887044,248887180⟩]
theorem checked50592 : checkPrefixCuts (2^48) 6635126785 10 Manual.Count131072.C050592.packed 64 cuts50592 = true := by
 decide +kernel
def cuts50593 : List PrefixCut := [⟨12,46069223,46069249⟩,
⟨64,246506547,246506686⟩]
theorem checked50593 : checkPrefixCuts (2^48) 6635257857 10 Manual.Count131072.C050593.packed 64 cuts50593 = true := by
 decide +kernel
def pointBounds50593 : List (Nat × Nat × Nat) := [(6635282432,111803616464932,111804003670460)]
theorem point_links_checked50593 : (cuts50593.take 1).map (fun c => (6635257857-1+2*2^10*c.k,111803570395709+c.lower,111803957601211+c.upper)) = pointBounds50593 := by
 decide +kernel
def cuts50594 : List PrefixCut := [⟨50,192416793,192416901⟩,
⟨64,245441181,245441318⟩]
theorem checked50594 : checkPrefixCuts (2^48) 6635388929 10 Manual.Count131072.C050594.packed 64 cuts50594 = true := by
 decide +kernel
def pointBounds50594 : List (Nat × Nat × Nat) := [(6635491328,111804009319049,111804396524798)]
theorem point_links_checked50594 : (cuts50594.take 1).map (fun c => (6635388929-1+2*2^10*c.k,111803816902256+c.lower,111804204107897+c.upper)) = pointBounds50594 := by
 decide +kernel
def cuts50595 : List PrefixCut := [⟨64,248745001,248745142⟩]
theorem checked50595 : checkPrefixCuts (2^48) 6635520001 10 Manual.Count131072.C050595.packed 64 cuts50595 = true := by
 decide +kernel
def cuts50596 : List PrefixCut := [⟨24,91496537,91496588⟩,
⟨64,246322252,246322393⟩]
theorem checked50596 : checkPrefixCuts (2^48) 6635651073 10 Manual.Count131072.C050596.packed 64 cuts50596 = true := by
 decide +kernel
def pointBounds50596 : List (Nat × Nat × Nat) := [(6635700224,111804402584975,111804789790945)]
theorem point_links_checked50596 : (cuts50596.take 1).map (fun c => (6635651073-1+2*2^10*c.k,111804311088438+c.lower,111804698294357+c.upper)) = pointBounds50596 := by
 decide +kernel
def cuts50597 : List PrefixCut := [⟨62,237791596,237791732⟩,
⟨64,246444647,246444788⟩]
theorem checked50597 : checkPrefixCuts (2^48) 6635782145 10 Manual.Count131072.C050597.packed 64 cuts50597 = true := by
 decide +kernel
def pointBounds50597 : List (Nat × Nat × Nat) := [(6635909120,111804795202286,111805182408482)]
theorem point_links_checked50597 : (cuts50597.take 1).map (fun c => (6635782145-1+2*2^10*c.k,111804557410690+c.lower,111804944616750+c.upper)) = pointBounds50597 := by
 decide +kernel
def cuts50598 : List PrefixCut := [⟨64,245633853,245633997⟩]
theorem checked50598 : checkPrefixCuts (2^48) 6635913217 10 Manual.Count131072.C050598.packed 64 cuts50598 = true := by
 decide +kernel
def cuts50599 : List PrefixCut := [⟨36,136027578,136027655⟩,
⟨64,246137983,246138125⟩]
theorem checked50599 : checkPrefixCuts (2^48) 6636044289 10 Manual.Count131072.C050599.packed 64 cuts50599 = true := by
 decide +kernel
def pointBounds50599 : List (Nat × Nat × Nat) := [(6636118016,111805185516768,111805572723190)]
theorem point_links_checked50599 : (cuts50599.take 1).map (fun c => (6636044289-1+2*2^10*c.k,111805049489190+c.lower,111805436695535+c.upper)) = pointBounds50599 := by
 decide +kernel
def cuts50600 : List PrefixCut := [⟨64,250713940,250714077⟩]
theorem checked50600 : checkPrefixCuts (2^48) 6636175361 10 Manual.Count131072.C050600.packed 64 cuts50600 = true := by
 decide +kernel
def cuts50601 : List PrefixCut := [⟨10,38384962,38384986⟩,
⟨64,243668273,243668411⟩]
theorem checked50601 : checkPrefixCuts (2^48) 6636306433 10 Manual.Count131072.C050601.packed 64 cuts50601 = true := by
 decide +kernel
def pointBounds50601 : List (Nat × Nat × Nat) := [(6636326912,111805584726075,111805971932723)]
theorem point_links_checked50601 : (cuts50601.take 1).map (fun c => (6636306433-1+2*2^10*c.k,111805546341113+c.lower,111805933547737+c.upper)) = pointBounds50601 := by
 decide +kernel
def cuts50602 : List PrefixCut := [⟨48,184497600,184497705⟩,
⟨64,245953780,245953921⟩]
theorem checked50602 : checkPrefixCuts (2^48) 6636437505 10 Manual.Count131072.C050602.packed 64 cuts50602 = true := by
 decide +kernel
def pointBounds50602 : List (Nat × Nat × Nat) := [(6636535808,111805974506986,111806361713853)]
theorem point_links_checked50602 : (cuts50602.take 1).map (fun c => (6636437505-1+2*2^10*c.k,111805790009386+c.lower,111806177216148+c.upper)) = pointBounds50602 := by
 decide +kernel
def cuts50603 : List PrefixCut := [⟨64,246924409,246924547⟩]
theorem checked50603 : checkPrefixCuts (2^48) 6636568577 10 Manual.Count131072.C050603.packed 64 cuts50603 = true := by
 decide +kernel
def cuts50604 : List PrefixCut := [⟨22,84653826,84653875⟩,
⟨64,242339091,242339230⟩]
theorem checked50604 : checkPrefixCuts (2^48) 6636699649 10 Manual.Count131072.C050604.packed 64 cuts50604 = true := by
 decide +kernel
def pointBounds50604 : List (Nat × Nat × Nat) := [(6636744704,111806367541401,111806754748491)]
theorem point_links_checked50604 : (cuts50604.take 1).map (fun c => (6636699649-1+2*2^10*c.k,111806282887575+c.lower,111806670094616+c.upper)) = pointBounds50604 := by
 decide +kernel
def cuts50605 : List PrefixCut := [⟨60,230841150,230841282⟩,
⟨64,246236064,246236204⟩]
theorem checked50605 : checkPrefixCuts (2^48) 6636830721 10 Manual.Count131072.C050605.packed 64 cuts50605 = true := by
 decide +kernel
def pointBounds50605 : List (Nat × Nat × Nat) := [(6636953600,111806756067816,111807143275128)]
theorem point_links_checked50605 : (cuts50605.take 1).map (fun c => (6636830721-1+2*2^10*c.k,111806525226666+c.lower,111806912433846+c.upper)) = pointBounds50605 := by
 decide +kernel
def cuts50606 : List PrefixCut := [⟨64,243262507,243262647⟩]
theorem checked50606 : checkPrefixCuts (2^48) 6636961793 10 Manual.Count131072.C050606.packed 64 cuts50606 = true := by
 decide +kernel
def cuts50607 : List PrefixCut := [⟨34,130662570,130662644⟩,
⟨64,245590216,245590354⟩]
theorem checked50607 : checkPrefixCuts (2^48) 6637092865 10 Manual.Count131072.C050607.packed 64 cuts50607 = true := by
 decide +kernel
def pointBounds50607 : List (Nat × Nat × Nat) := [(6637162496,111807145387807,111807532595341)]
theorem point_links_checked50607 : (cuts50607.take 1).map (fun c => (6637092865-1+2*2^10*c.k,111807014725237+c.lower,111807401932697+c.upper)) = pointBounds50607 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000018
