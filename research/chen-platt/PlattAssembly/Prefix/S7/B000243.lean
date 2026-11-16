import PlattAssemblyKernel
import PlattCertificates.Count131072.C067776
import PlattCertificates.Count131072.C067777
import PlattCertificates.Count131072.C067778
import PlattCertificates.Count131072.C067779
import PlattCertificates.Count131072.C067780
import PlattCertificates.Count131072.C067781
import PlattCertificates.Count131072.C067782
import PlattCertificates.Count131072.C067783
import PlattCertificates.Count131072.C067784
import PlattCertificates.Count131072.C067785
import PlattCertificates.Count131072.C067786
import PlattCertificates.Count131072.C067787
import PlattCertificates.Count131072.C067788
import PlattCertificates.Count131072.C067789
import PlattCertificates.Count131072.C067790
import PlattCertificates.Count131072.C067791
import PlattCertificates.Count131072.C067792
import PlattCertificates.Count131072.C067793
import PlattCertificates.Count131072.C067794
import PlattCertificates.Count131072.C067795
import PlattCertificates.Count131072.C067796
import PlattCertificates.Count131072.C067797
import PlattCertificates.Count131072.C067798
import PlattCertificates.Count131072.C067799
import PlattCertificates.Count131072.C067800
import PlattCertificates.Count131072.C067801
import PlattCertificates.Count131072.C067802
import PlattCertificates.Count131072.C067803
import PlattCertificates.Count131072.C067804
import PlattCertificates.Count131072.C067805
import PlattCertificates.Count131072.C067806
import PlattCertificates.Count131072.C067807
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000243
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67776 : List PrefixCut := [⟨64,181726794,181726893⟩]
theorem checked67776 : checkPrefixCuts (2^48) 8887468033 10 Manual.Count131072.C067776.packed 64 cuts67776 = true := by
 decide +kernel
def cuts67777 : List PrefixCut := [⟨64,180995679,180995784⟩]
theorem checked67777 : checkPrefixCuts (2^48) 8887599105 10 Manual.Count131072.C067777.packed 64 cuts67777 = true := by
 decide +kernel
def cuts67778 : List PrefixCut := [⟨5,14821576,14821586⟩,
⟨64,180961349,180961463⟩]
theorem checked67778 : checkPrefixCuts (2^48) 8887730177 10 Manual.Count131072.C067778.packed 64 cuts67778 = true := by
 decide +kernel
def pointBounds67778 : List (Nat × Nat × Nat) := [(8887740416,115417867897721,115418257170798)]
theorem point_links_checked67778 : (cuts67778.take 1).map (fun c => (8887730177-1+2*2^10*c.k,115417853076145+c.lower,115418242349212+c.upper)) = pointBounds67778 := by
 decide +kernel
def cuts67779 : List PrefixCut := [⟨64,180483652,180483754⟩]
theorem checked67779 : checkPrefixCuts (2^48) 8887861249 10 Manual.Count131072.C067779.packed 64 cuts67779 = true := by
 decide +kernel
def cuts67780 : List PrefixCut := [⟨13,36419434,36419454⟩,
⟨64,178169159,178169262⟩]
theorem checked67780 : checkPrefixCuts (2^48) 8887992321 10 Manual.Count131072.C067780.packed 64 cuts67780 = true := by
 decide +kernel
def pointBounds67780 : List (Nat × Nat × Nat) := [(8888018944,115418250940580,115418640213883)]
theorem point_links_checked67780 : (cuts67780.take 1).map (fun c => (8887992321-1+2*2^10*c.k,115418214521146+c.lower,115418603794429+c.upper)) = pointBounds67780 := by
 decide +kernel
def cuts67781 : List PrefixCut := [⟨64,180351656,180351759⟩]
theorem checked67781 : checkPrefixCuts (2^48) 8888123393 10 Manual.Count131072.C067781.packed 64 cuts67781 = true := by
 decide +kernel
def cuts67782 : List PrefixCut := [⟨21,58934352,58934385⟩,
⟨64,179905637,179905739⟩]
theorem checked67782 : checkPrefixCuts (2^48) 8888254465 10 Manual.Count131072.C067782.packed 64 cuts67782 = true := by
 decide +kernel
def pointBounds67782 : List (Nat × Nat × Nat) := [(8888297472,115418631976313,115419021249835)]
theorem point_links_checked67782 : (cuts67782.take 1).map (fun c => (8888254465-1+2*2^10*c.k,115418573041961+c.lower,115418962315450+c.upper)) = pointBounds67782 := by
 decide +kernel
def cuts67783 : List PrefixCut := [⟨64,182024704,182024809⟩]
theorem checked67783 : checkPrefixCuts (2^48) 8888385537 10 Manual.Count131072.C067783.packed 64 cuts67783 = true := by
 decide +kernel
def cuts67784 : List PrefixCut := [⟨29,80719557,80719603⟩,
⟨64,179995328,179995431⟩]
theorem checked67784 : checkPrefixCuts (2^48) 8888516609 10 Manual.Count131072.C067784.packed 64 cuts67784 = true := by
 decide +kernel
def pointBounds67784 : List (Nat × Nat × Nat) := [(8888576000,115419015691859,115419404965601)]
theorem point_links_checked67784 : (cuts67784.take 1).map (fun c => (8888516609-1+2*2^10*c.k,115418934972302+c.lower,115419324245998+c.upper)) = pointBounds67784 := by
 decide +kernel
def cuts67785 : List PrefixCut := [⟨64,183666003,183666117⟩]
theorem checked67785 : checkPrefixCuts (2^48) 8888647681 10 Manual.Count131072.C067785.packed 64 cuts67785 = true := by
 decide +kernel
def cuts67786 : List PrefixCut := [⟨37,105226726,105226788⟩,
⟨64,183409954,183410065⟩]
theorem checked67786 : checkPrefixCuts (2^48) 8888778753 10 Manual.Count131072.C067786.packed 64 cuts67786 = true := by
 decide +kernel
def pointBounds67786 : List (Nat × Nat × Nat) := [(8888854528,115419403860359,115419793134334)]
theorem point_links_checked67786 : (cuts67786.take 1).map (fun c => (8888778753-1+2*2^10*c.k,115419298633633+c.lower,115419687907546+c.upper)) = pointBounds67786 := by
 decide +kernel
def cuts67787 : List PrefixCut := [⟨64,183217274,183217375⟩]
theorem checked67787 : checkPrefixCuts (2^48) 8888909825 10 Manual.Count131072.C067787.packed 64 cuts67787 = true := by
 decide +kernel
def cuts67788 : List PrefixCut := [⟨45,127737498,127737570⟩,
⟨64,181599637,181599742⟩]
theorem checked67788 : checkPrefixCuts (2^48) 8889040897 10 Manual.Count131072.C067788.packed 64 cuts67788 = true := by
 decide +kernel
def pointBounds67788 : List (Nat × Nat × Nat) := [(8889133056,115419792998359,115420182272556)]
theorem point_links_checked67788 : (cuts67788.take 1).map (fun c => (8889040897-1+2*2^10*c.k,115419665260861+c.lower,115420054534986+c.upper)) = pointBounds67788 := by
 decide +kernel
def cuts67789 : List PrefixCut := [⟨64,182135265,182135371⟩]
theorem checked67789 : checkPrefixCuts (2^48) 8889171969 10 Manual.Count131072.C067789.packed 64 cuts67789 = true := by
 decide +kernel
def cuts67790 : List PrefixCut := [⟨53,148347051,148347137⟩,
⟨64,178934497,178934603⟩]
theorem checked67790 : checkPrefixCuts (2^48) 8889303041 10 Manual.Count131072.C067790.packed 64 cuts67790 = true := by
 decide +kernel
def pointBounds67790 : List (Nat × Nat × Nat) := [(8889411584,115420177342814,115420566617236)]
theorem point_links_checked67790 : (cuts67790.take 1).map (fun c => (8889303041-1+2*2^10*c.k,115420028995763+c.lower,115420418270099+c.upper)) = pointBounds67790 := by
 decide +kernel
def cuts67791 : List PrefixCut := [⟨64,180768352,180768454⟩]
theorem checked67791 : checkPrefixCuts (2^48) 8889434113 10 Manual.Count131072.C067791.packed 64 cuts67791 = true := by
 decide +kernel
def cuts67792 : List PrefixCut := [⟨61,170095217,170095318⟩,
⟨64,179119190,179119295⟩]
theorem checked67792 : checkPrefixCuts (2^48) 8889565185 10 Manual.Count131072.C067792.packed 64 cuts67792 = true := by
 decide +kernel
def pointBounds67792 : List (Nat × Nat × Nat) := [(8889690112,115420558793829,115420948068474)]
theorem point_links_checked67792 : (cuts67792.take 1).map (fun c => (8889565185-1+2*2^10*c.k,115420388698612+c.lower,115420777973156+c.upper)) = pointBounds67792 := by
 decide +kernel
def cuts67793 : List PrefixCut := [⟨64,184435909,184436019⟩]
theorem checked67793 : checkPrefixCuts (2^48) 8889696257 10 Manual.Count131072.C067793.packed 64 cuts67793 = true := by
 decide +kernel
def cuts67794 : List PrefixCut := [⟨64,181425268,181425376⟩]
theorem checked67794 : checkPrefixCuts (2^48) 8889827329 10 Manual.Count131072.C067794.packed 64 cuts67794 = true := by
 decide +kernel
def cuts67795 : List PrefixCut := [⟨5,14342930,14342938⟩,
⟨64,181390928,181391035⟩]
theorem checked67795 : checkPrefixCuts (2^48) 8889958401 10 Manual.Count131072.C067795.packed 64 cuts67795 = true := by
 decide +kernel
def pointBounds67795 : List (Nat × Nat × Nat) := [(8889968640,115420948021909,115421337296784)]
theorem point_links_checked67795 : (cuts67795.take 1).map (fun c => (8889958401-1+2*2^10*c.k,115420933678979+c.lower,115421322953846+c.upper)) = pointBounds67795 := by
 decide +kernel
def cuts67796 : List PrefixCut := [⟨64,179646878,179646983⟩]
theorem checked67796 : checkPrefixCuts (2^48) 8890089473 10 Manual.Count131072.C067796.packed 64 cuts67796 = true := by
 decide +kernel
def cuts67797 : List PrefixCut := [⟨13,35745418,35745441⟩,
⟨64,182113770,182113886⟩]
theorem checked67797 : checkPrefixCuts (2^48) 8890220545 10 Manual.Count131072.C067797.packed 64 cuts67797 = true := by
 decide +kernel
def pointBounds67797 : List (Nat × Nat × Nat) := [(8890247168,115421330462203,115421719737305)]
theorem point_links_checked67797 : (cuts67797.take 1).map (fun c => (8890220545-1+2*2^10*c.k,115421294716785+c.lower,115421683991864+c.upper)) = pointBounds67797 := by
 decide +kernel
def cuts67798 : List PrefixCut := [⟨64,179989848,179989958⟩]
theorem checked67798 : checkPrefixCuts (2^48) 8890351617 10 Manual.Count131072.C067798.packed 64 cuts67798 = true := by
 decide +kernel
def cuts67799 : List PrefixCut := [⟨21,59711086,59711122⟩,
⟨64,181886792,181886895⟩]
theorem checked67799 : checkPrefixCuts (2^48) 8890482689 10 Manual.Count131072.C067799.packed 64 cuts67799 = true := by
 decide +kernel
def pointBounds67799 : List (Nat × Nat × Nat) := [(8890525696,115421716531489,115422105806830)]
theorem point_links_checked67799 : (cuts67799.take 1).map (fun c => (8890482689-1+2*2^10*c.k,115421656820403+c.lower,115422046095708+c.upper)) = pointBounds67799 := by
 decide +kernel
def cuts67800 : List PrefixCut := [⟨64,181979081,181979190⟩]
theorem checked67800 : checkPrefixCuts (2^48) 8890613761 10 Manual.Count131072.C067800.packed 64 cuts67800 = true := by
 decide +kernel
def cuts67801 : List PrefixCut := [⟨29,82535558,82535602⟩,
⟨64,181596494,181596595⟩]
theorem checked67801 : checkPrefixCuts (2^48) 8890744833 10 Manual.Count131072.C067801.packed 64 cuts67801 = true := by
 decide +kernel
def pointBounds67801 : List (Nat × Nat × Nat) := [(8890804224,115422103221834,115422492497395)]
theorem point_links_checked67801 : (cuts67801.take 1).map (fun c => (8890744833-1+2*2^10*c.k,115422020686276+c.lower,115422409961793+c.upper)) = pointBounds67801 := by
 decide +kernel
def cuts67802 : List PrefixCut := [⟨64,183398364,183398474⟩]
theorem checked67802 : checkPrefixCuts (2^48) 8890875905 10 Manual.Count131072.C067802.packed 64 cuts67802 = true := by
 decide +kernel
def cuts67803 : List PrefixCut := [⟨37,104535535,104535597⟩,
⟨64,179026839,179026947⟩]
theorem checked67803 : checkPrefixCuts (2^48) 8891006977 10 Manual.Count131072.C067803.packed 64 cuts67803 = true := by
 decide +kernel
def pointBounds67803 : List (Nat × Nat × Nat) := [(8891082752,115422490216669,115422879492459)]
theorem point_links_checked67803 : (cuts67803.take 1).map (fun c => (8891006977-1+2*2^10*c.k,115422385681134+c.lower,115422774956862+c.upper)) = pointBounds67803 := by
 decide +kernel
def cuts67804 : List PrefixCut := [⟨64,182443217,182443322⟩]
theorem checked67804 : checkPrefixCuts (2^48) 8891138049 10 Manual.Count131072.C067804.packed 64 cuts67804 = true := by
 decide +kernel
def cuts67805 : List PrefixCut := [⟨45,127167318,127167392⟩,
⟨64,181649104,181649206⟩]
theorem checked67805 : checkPrefixCuts (2^48) 8891269121 10 Manual.Count131072.C067805.packed 64 cuts67805 = true := by
 decide +kernel
def pointBounds67805 : List (Nat × Nat × Nat) := [(8891361280,115422874318508,115423263594523)]
theorem point_links_checked67805 : (cuts67805.take 1).map (fun c => (8891269121-1+2*2^10*c.k,115422747151190+c.lower,115423136427131+c.upper)) = pointBounds67805 := by
 decide +kernel
def cuts67806 : List PrefixCut := [⟨64,181044943,181045047⟩]
theorem checked67806 : checkPrefixCuts (2^48) 8891400193 10 Manual.Count131072.C067806.packed 64 cuts67806 = true := by
 decide +kernel
def cuts67807 : List PrefixCut := [⟨53,149702739,149702825⟩,
⟨64,181137236,181137341⟩]
theorem checked67807 : checkPrefixCuts (2^48) 8891531265 10 Manual.Count131072.C067807.packed 64 cuts67807 = true := by
 decide +kernel
def pointBounds67807 : List (Nat × Nat × Nat) := [(8891639808,115423259547976,115423648824209)]
theorem point_links_checked67807 : (cuts67807.take 1).map (fun c => (8891531265-1+2*2^10*c.k,115423109845237+c.lower,115423499121384+c.upper)) = pointBounds67807 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000243
