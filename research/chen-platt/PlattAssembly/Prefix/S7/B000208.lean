import PlattAssemblyKernel
import PlattCertificates.Count131072.C066656
import PlattCertificates.Count131072.C066657
import PlattCertificates.Count131072.C066658
import PlattCertificates.Count131072.C066659
import PlattCertificates.Count131072.C066660
import PlattCertificates.Count131072.C066661
import PlattCertificates.Count131072.C066662
import PlattCertificates.Count131072.C066663
import PlattCertificates.Count131072.C066664
import PlattCertificates.Count131072.C066665
import PlattCertificates.Count131072.C066666
import PlattCertificates.Count131072.C066667
import PlattCertificates.Count131072.C066668
import PlattCertificates.Count131072.C066669
import PlattCertificates.Count131072.C066670
import PlattCertificates.Count131072.C066671
import PlattCertificates.Count131072.C066672
import PlattCertificates.Count131072.C066673
import PlattCertificates.Count131072.C066674
import PlattCertificates.Count131072.C066675
import PlattCertificates.Count131072.C066676
import PlattCertificates.Count131072.C066677
import PlattCertificates.Count131072.C066678
import PlattCertificates.Count131072.C066679
import PlattCertificates.Count131072.C066680
import PlattCertificates.Count131072.C066681
import PlattCertificates.Count131072.C066682
import PlattCertificates.Count131072.C066683
import PlattCertificates.Count131072.C066684
import PlattCertificates.Count131072.C066685
import PlattCertificates.Count131072.C066686
import PlattCertificates.Count131072.C066687
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000208
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66656 : List PrefixCut := [⟨64,184682296,184682403⟩]
theorem checked66656 : checkPrefixCuts (2^48) 8740667393 10 Manual.Count131072.C066656.packed 64 cuts66656 = true := by
 decide +kernel
def cuts66657 : List PrefixCut := [⟨64,185226960,185227069⟩]
theorem checked66657 : checkPrefixCuts (2^48) 8740798465 10 Manual.Count131072.C066657.packed 64 cuts66657 = true := by
 decide +kernel
def cuts66658 : List PrefixCut := [⟨6,17260228,17260237⟩,
⟨64,184934366,184934468⟩]
theorem checked66658 : checkPrefixCuts (2^48) 8740929537 10 Manual.Count131072.C066658.packed 64 cuts66658 = true := by
 decide +kernel
def pointBounds66658 : List (Nat × Nat × Nat) := [(8740941824,115213173075952,115213562229659)]
theorem point_links_checked66658 : (cuts66658.take 1).map (fun c => (8740929537-1+2*2^10*c.k,115213155815724+c.lower,115213544969422+c.upper)) = pointBounds66658 := by
 decide +kernel
def cuts66659 : List PrefixCut := [⟨64,183128306,183128421⟩]
theorem checked66659 : checkPrefixCuts (2^48) 8741060609 10 Manual.Count131072.C066659.packed 64 cuts66659 = true := by
 decide +kernel
def cuts66660 : List PrefixCut := [⟨12,34100785,34100804⟩,
⟨64,183125571,183125673⟩]
theorem checked66660 : checkPrefixCuts (2^48) 8741191681 10 Manual.Count131072.C066660.packed 64 cuts66660 = true := by
 decide +kernel
def pointBounds66660 : List (Nat × Nat × Nat) := [(8741216256,115213557979181,115213947133115)]
theorem point_links_checked66660 : (cuts66660.take 1).map (fun c => (8741191681-1+2*2^10*c.k,115213523878396+c.lower,115213913032311+c.upper)) = pointBounds66660 := by
 decide +kernel
def cuts66661 : List PrefixCut := [⟨64,186761445,186761556⟩]
theorem checked66661 : checkPrefixCuts (2^48) 8741322753 10 Manual.Count131072.C066661.packed 64 cuts66661 = true := by
 decide +kernel
def cuts66662 : List PrefixCut := [⟨18,52389307,52389336⟩,
⟨64,183442075,183442189⟩]
theorem checked66662 : checkPrefixCuts (2^48) 8741453825 10 Manual.Count131072.C066662.packed 64 cuts66662 = true := by
 decide +kernel
def pointBounds66662 : List (Nat × Nat × Nat) := [(8741490688,115213946154719,115214335308876)]
theorem point_links_checked66662 : (cuts66662.take 1).map (fun c => (8741453825-1+2*2^10*c.k,115213893765412+c.lower,115214282919540+c.upper)) = pointBounds66662 := by
 decide +kernel
def cuts66663 : List PrefixCut := [⟨64,184373102,184373205⟩]
theorem checked66663 : checkPrefixCuts (2^48) 8741584897 10 Manual.Count131072.C066663.packed 64 cuts66663 = true := by
 decide +kernel
def cuts66664 : List PrefixCut := [⟨24,70386912,70386954⟩,
⟨64,183146797,183146903⟩]
theorem checked66664 : checkPrefixCuts (2^48) 8741715969 10 Manual.Count131072.C066664.packed 64 cuts66664 = true := by
 decide +kernel
def pointBounds66664 : List (Nat × Nat × Nat) := [(8741765120,115214331967501,115214721121888)]
theorem point_links_checked66664 : (cuts66664.take 1).map (fun c => (8741715969-1+2*2^10*c.k,115214261580589+c.lower,115214650734934+c.upper)) = pointBounds66664 := by
 decide +kernel
def cuts66665 : List PrefixCut := [⟨64,184431984,184432090⟩]
theorem checked66665 : checkPrefixCuts (2^48) 8741847041 10 Manual.Count131072.C066665.packed 64 cuts66665 = true := by
 decide +kernel
def cuts66666 : List PrefixCut := [⟨30,86644727,86644777⟩,
⟨64,183012517,183012623⟩]
theorem checked66666 : checkPrefixCuts (2^48) 8741978113 10 Manual.Count131072.C066666.packed 64 cuts66666 = true := by
 decide +kernel
def pointBounds66666 : List (Nat × Nat × Nat) := [(8742039552,115214715804097,115215104958704)]
theorem point_links_checked66666 : (cuts66666.take 1).map (fun c => (8741978113-1+2*2^10*c.k,115214629159370+c.lower,115215018313927+c.upper)) = pointBounds66666 := by
 decide +kernel
def cuts66667 : List PrefixCut := [⟨64,185392379,185392484⟩]
theorem checked66667 : checkPrefixCuts (2^48) 8742109185 10 Manual.Count131072.C066667.packed 64 cuts66667 = true := by
 decide +kernel
def cuts66668 : List PrefixCut := [⟨36,104125025,104125084⟩,
⟨64,183200207,183200312⟩]
theorem checked66668 : checkPrefixCuts (2^48) 8742240257 10 Manual.Count131072.C066668.packed 64 cuts66668 = true := by
 decide +kernel
def pointBounds66668 : List (Nat × Nat × Nat) := [(8742313984,115215101689291,115215490844118)]
theorem point_links_checked66668 : (cuts66668.take 1).map (fun c => (8742240257-1+2*2^10*c.k,115214997564266+c.lower,115215386719034+c.upper)) = pointBounds66668 := by
 decide +kernel
def cuts66669 : List PrefixCut := [⟨64,183712600,183712707⟩]
theorem checked66669 : checkPrefixCuts (2^48) 8742371329 10 Manual.Count131072.C066669.packed 64 cuts66669 = true := by
 decide +kernel
def cuts66670 : List PrefixCut := [⟨42,120058843,120058914⟩,
⟨64,183903012,183903119⟩]
theorem checked66670 : checkPrefixCuts (2^48) 8742502401 10 Manual.Count131072.C066670.packed 64 cuts66670 = true := by
 decide +kernel
def pointBounds66670 : List (Nat × Nat × Nat) := [(8742588416,115215484535916,115215873690967)]
theorem point_links_checked66670 : (cuts66670.take 1).map (fun c => (8742502401-1+2*2^10*c.k,115215364477073+c.lower,115215753632053+c.upper)) = pointBounds66670 := by
 decide +kernel
def cuts66671 : List PrefixCut := [⟨64,183288543,183288649⟩]
theorem checked66671 : checkPrefixCuts (2^48) 8742633473 10 Manual.Count131072.C066671.packed 64 cuts66671 = true := by
 decide +kernel
def cuts66672 : List PrefixCut := [⟨48,138760459,138760537⟩,
⟨64,184766771,184766877⟩]
theorem checked66672 : checkPrefixCuts (2^48) 8742764545 10 Manual.Count131072.C066672.packed 64 cuts66672 = true := by
 decide +kernel
def pointBounds66672 : List (Nat × Nat × Nat) := [(8742862848,115215870429087,115216259584358)]
theorem point_links_checked66672 : (cuts66672.take 1).map (fun c => (8742764545-1+2*2^10*c.k,115215731668628+c.lower,115216120823821+c.upper)) = pointBounds66672 := by
 decide +kernel
def cuts66673 : List PrefixCut := [⟨64,187017616,187017718⟩]
theorem checked66673 : checkPrefixCuts (2^48) 8742895617 10 Manual.Count131072.C066673.packed 64 cuts66673 = true := by
 decide +kernel
def cuts66674 : List PrefixCut := [⟨54,154305905,154306000⟩,
⟨64,182604231,182604342⟩]
theorem checked66674 : checkPrefixCuts (2^48) 8743026689 10 Manual.Count131072.C066674.packed 64 cuts66674 = true := by
 decide +kernel
def pointBounds66674 : List (Nat × Nat × Nat) := [(8743137280,115216257758920,115216646914416)]
theorem point_links_checked66674 : (cuts66674.take 1).map (fun c => (8743026689-1+2*2^10*c.k,115216103453015+c.lower,115216492608416+c.upper)) = pointBounds66674 := by
 decide +kernel
def cuts66675 : List PrefixCut := [⟨64,185531109,185531219⟩]
theorem checked66675 : checkPrefixCuts (2^48) 8743157761 10 Manual.Count131072.C066675.packed 64 cuts66675 = true := by
 decide +kernel
def cuts66676 : List PrefixCut := [⟨60,174228649,174228753⟩,
⟨64,185882437,185882548⟩]
theorem checked66676 : checkPrefixCuts (2^48) 8743288833 10 Manual.Count131072.C066676.packed 64 cuts66676 = true := by
 decide +kernel
def pointBounds66676 : List (Nat × Nat × Nat) := [(8743411712,115216645817004,115217034972730)]
theorem point_links_checked66676 : (cuts66676.take 1).map (fun c => (8743288833-1+2*2^10*c.k,115216471588355+c.lower,115216860743977+c.upper)) = pointBounds66676 := by
 decide +kernel
def cuts66677 : List PrefixCut := [⟨64,185654302,185654407⟩]
theorem checked66677 : checkPrefixCuts (2^48) 8743419905 10 Manual.Count131072.C066677.packed 64 cuts66677 = true := by
 decide +kernel
def cuts66678 : List PrefixCut := [⟨64,182818632,182818737⟩]
theorem checked66678 : checkPrefixCuts (2^48) 8743550977 10 Manual.Count131072.C066678.packed 64 cuts66678 = true := by
 decide +kernel
def cuts66679 : List PrefixCut := [⟨2,5601372,5601376⟩,
⟨64,186067233,186067340⟩]
theorem checked66679 : checkPrefixCuts (2^48) 8743682049 10 Manual.Count131072.C066679.packed 64 cuts66679 = true := by
 decide +kernel
def pointBounds66679 : List (Nat × Nat × Nat) := [(8743686144,115217031545098,115217420701045)]
theorem point_links_checked66679 : (cuts66679.take 1).map (fun c => (8743682049-1+2*2^10*c.k,115217025943726+c.lower,115217415099669+c.upper)) = pointBounds66679 := by
 decide +kernel
def cuts66680 : List PrefixCut := [⟨64,186225382,186225491⟩]
theorem checked66680 : checkPrefixCuts (2^48) 8743813121 10 Manual.Count131072.C066680.packed 64 cuts66680 = true := by
 decide +kernel
def cuts66681 : List PrefixCut := [⟨8,22340421,22340432⟩,
⟨64,182166599,182166703⟩]
theorem checked66681 : checkPrefixCuts (2^48) 8743944193 10 Manual.Count131072.C066681.packed 64 cuts66681 = true := by
 decide +kernel
def pointBounds66681 : List (Nat × Nat × Nat) := [(8743960576,115217420576762,115217809732932)]
theorem point_links_checked66681 : (cuts66681.take 1).map (fun c => (8743944193-1+2*2^10*c.k,115217398236341+c.lower,115217787392500+c.upper)) = pointBounds66681 := by
 decide +kernel
def cuts66682 : List PrefixCut := [⟨64,184127473,184127579⟩]
theorem checked66682 : checkPrefixCuts (2^48) 8744075265 10 Manual.Count131072.C066682.packed 64 cuts66682 = true := by
 decide +kernel
def cuts66683 : List PrefixCut := [⟨14,40333844,40333870⟩,
⟨64,185573227,185573340⟩]
theorem checked66683 : checkPrefixCuts (2^48) 8744206337 10 Manual.Count131072.C066683.packed 64 cuts66683 = true := by
 decide +kernel
def pointBounds66683 : List (Nat × Nat × Nat) := [(8744235008,115217804864257,115218194020652)]
theorem point_links_checked66683 : (cuts66683.take 1).map (fun c => (8744206337-1+2*2^10*c.k,115217764530413+c.lower,115218153686782+c.upper)) = pointBounds66683 := by
 decide +kernel
def cuts66684 : List PrefixCut := [⟨64,183059693,183059805⟩]
theorem checked66684 : checkPrefixCuts (2^48) 8744337409 10 Manual.Count131072.C066684.packed 64 cuts66684 = true := by
 decide +kernel
def cuts66685 : List PrefixCut := [⟨20,57972090,57972124⟩,
⟨64,183636352,183636462⟩]
theorem checked66685 : checkPrefixCuts (2^48) 8744468481 10 Manual.Count131072.C066685.packed 64 cuts66685 = true := by
 decide +kernel
def pointBounds66685 : List (Nat × Nat × Nat) := [(8744509440,115218191135423,115218580292051)]
theorem point_links_checked66685 : (cuts66685.take 1).map (fun c => (8744468481-1+2*2^10*c.k,115218133163333+c.lower,115218522319927+c.upper)) = pointBounds66685 := by
 decide +kernel
def cuts66686 : List PrefixCut := [⟨64,181058533,181058651⟩]
theorem checked66686 : checkPrefixCuts (2^48) 8744599553 10 Manual.Count131072.C066686.packed 64 cuts66686 = true := by
 decide +kernel
def cuts66687 : List PrefixCut := [⟨26,73517040,73517081⟩,
⟨64,183663016,183663118⟩]
theorem checked66687 : checkPrefixCuts (2^48) 8744730625 10 Manual.Count131072.C066687.packed 64 cuts66687 = true := by
 decide +kernel
def pointBounds66687 : List (Nat × Nat × Nat) := [(8744783872,115218571375258,115218960532121)]
theorem point_links_checked66687 : (cuts66687.take 1).map (fun c => (8744730625-1+2*2^10*c.k,115218497858218+c.lower,115218887015040+c.upper)) = pointBounds66687 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000208
