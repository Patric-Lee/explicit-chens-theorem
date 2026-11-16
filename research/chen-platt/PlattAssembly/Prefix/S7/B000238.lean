import PlattAssemblyKernel
import PlattCertificates.Count131072.C067616
import PlattCertificates.Count131072.C067617
import PlattCertificates.Count131072.C067618
import PlattCertificates.Count131072.C067619
import PlattCertificates.Count131072.C067620
import PlattCertificates.Count131072.C067621
import PlattCertificates.Count131072.C067622
import PlattCertificates.Count131072.C067623
import PlattCertificates.Count131072.C067624
import PlattCertificates.Count131072.C067625
import PlattCertificates.Count131072.C067626
import PlattCertificates.Count131072.C067627
import PlattCertificates.Count131072.C067628
import PlattCertificates.Count131072.C067629
import PlattCertificates.Count131072.C067630
import PlattCertificates.Count131072.C067631
import PlattCertificates.Count131072.C067632
import PlattCertificates.Count131072.C067633
import PlattCertificates.Count131072.C067634
import PlattCertificates.Count131072.C067635
import PlattCertificates.Count131072.C067636
import PlattCertificates.Count131072.C067637
import PlattCertificates.Count131072.C067638
import PlattCertificates.Count131072.C067639
import PlattCertificates.Count131072.C067640
import PlattCertificates.Count131072.C067641
import PlattCertificates.Count131072.C067642
import PlattCertificates.Count131072.C067643
import PlattCertificates.Count131072.C067644
import PlattCertificates.Count131072.C067645
import PlattCertificates.Count131072.C067646
import PlattCertificates.Count131072.C067647
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000238
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67616 : List PrefixCut := [⟨37,106507030,106507092⟩,
⟨64,181966149,181966256⟩]
theorem checked67616 : checkPrefixCuts (2^48) 8866496513 10 Manual.Count131072.C067616.packed 64 cuts67616 = true := by
 decide +kernel
def pointBounds67616 : List (Nat × Nat × Nat) := [(8866572288,115388570110238,115388959366179)]
theorem point_links_checked67616 : (cuts67616.take 1).map (fun c => (8866496513-1+2*2^10*c.k,115388463603208+c.lower,115388852859087+c.upper)) = pointBounds67616 := by
 decide +kernel
def cuts67617 : List PrefixCut := [⟨64,182630106,182630214⟩]
theorem checked67617 : checkPrefixCuts (2^48) 8866627585 10 Manual.Count131072.C067617.packed 64 cuts67617 = true := by
 decide +kernel
def cuts67618 : List PrefixCut := [⟨45,125931604,125931677⟩,
⟨64,180024333,180024441⟩]
theorem checked67618 : checkPrefixCuts (2^48) 8866758657 10 Manual.Count131072.C067618.packed 64 cuts67618 = true := by
 decide +kernel
def pointBounds67618 : List (Nat × Nat × Nat) := [(8866850816,115388954131067,115389343387234)]
theorem point_links_checked67618 : (cuts67618.take 1).map (fun c => (8866758657-1+2*2^10*c.k,115388828199463+c.lower,115389217455557+c.upper)) = pointBounds67618 := by
 decide +kernel
def cuts67619 : List PrefixCut := [⟨64,183862729,183862831⟩]
theorem checked67619 : checkPrefixCuts (2^48) 8866889729 10 Manual.Count131072.C067619.packed 64 cuts67619 = true := by
 decide +kernel
def cuts67620 : List PrefixCut := [⟨53,150592710,150592802⟩,
⟨64,181542711,181542823⟩]
theorem checked67620 : checkPrefixCuts (2^48) 8867020801 10 Manual.Count131072.C067620.packed 64 cuts67620 = true := by
 decide +kernel
def pointBounds67620 : List (Nat × Nat × Nat) := [(8867129344,115389342679235,115389731935631)]
theorem point_links_checked67620 : (cuts67620.take 1).map (fun c => (8867020801-1+2*2^10*c.k,115389192086525+c.lower,115389581342829+c.upper)) = pointBounds67620 := by
 decide +kernel
def cuts67621 : List PrefixCut := [⟨64,179413231,179413331⟩]
theorem checked67621 : checkPrefixCuts (2^48) 8867151873 10 Manual.Count131072.C067621.packed 64 cuts67621 = true := by
 decide +kernel
def cuts67622 : List PrefixCut := [⟨61,171982796,171982908⟩,
⟨64,180267621,180267738⟩]
theorem checked67622 : checkPrefixCuts (2^48) 8867282945 10 Manual.Count131072.C067622.packed 64 cuts67622 = true := by
 decide +kernel
def pointBounds67622 : List (Nat × Nat × Nat) := [(8867407872,115389725025263,115390114281891)]
theorem point_links_checked67622 : (cuts67622.take 1).map (fun c => (8867282945-1+2*2^10*c.k,115389553042467+c.lower,115389942298983+c.upper)) = pointBounds67622 := by
 decide +kernel
def cuts67623 : List PrefixCut := [⟨64,182709135,182709236⟩]
theorem checked67623 : checkPrefixCuts (2^48) 8867414017 10 Manual.Count131072.C067623.packed 64 cuts67623 = true := by
 decide +kernel
def cuts67624 : List PrefixCut := [⟨64,181436753,181436860⟩]
theorem checked67624 : checkPrefixCuts (2^48) 8867545089 10 Manual.Count131072.C067624.packed 64 cuts67624 = true := by
 decide +kernel
def cuts67625 : List PrefixCut := [⟨5,13966329,13966338⟩,
⟨64,182322834,182322940⟩]
theorem checked67625 : checkPrefixCuts (2^48) 8867676161 10 Manual.Count131072.C067625.packed 64 cuts67625 = true := by
 decide +kernel
def pointBounds67625 : List (Nat × Nat × Nat) := [(8867686400,115390111422305,115390500679155)]
theorem point_links_checked67625 : (cuts67625.take 1).map (fun c => (8867676161-1+2*2^10*c.k,115390097455976+c.lower,115390486712817+c.upper)) = pointBounds67625 := by
 decide +kernel
def cuts67626 : List PrefixCut := [⟨64,182066204,182066311⟩]
theorem checked67626 : checkPrefixCuts (2^48) 8867807233 10 Manual.Count131072.C067626.packed 64 cuts67626 = true := by
 decide +kernel
def cuts67627 : List PrefixCut := [⟨13,37263566,37263589⟩,
⟨64,180920855,180920959⟩]
theorem checked67627 : checkPrefixCuts (2^48) 8867938305 10 Manual.Count131072.C067627.packed 64 cuts67627 = true := by
 decide +kernel
def pointBounds67627 : List (Nat × Nat × Nat) := [(8867964928,115390499108580,115390888365657)]
theorem point_links_checked67627 : (cuts67627.take 1).map (fun c => (8867938305-1+2*2^10*c.k,115390461845014+c.lower,115390851102068+c.upper)) = pointBounds67627 := by
 decide +kernel
def cuts67628 : List PrefixCut := [⟨64,184822209,184822315⟩]
theorem checked67628 : checkPrefixCuts (2^48) 8868069377 10 Manual.Count131072.C067628.packed 64 cuts67628 = true := by
 decide +kernel
def cuts67629 : List PrefixCut := [⟨21,57829773,57829803⟩,
⟨64,178471558,178471655⟩]
theorem checked67629 : checkPrefixCuts (2^48) 8868200449 10 Manual.Count131072.C067629.packed 64 cuts67629 = true := by
 decide +kernel
def pointBounds67629 : List (Nat × Nat × Nat) := [(8868243456,115390885417851,115391274675145)]
theorem point_links_checked67629 : (cuts67629.take 1).map (fun c => (8868200449-1+2*2^10*c.k,115390827588078+c.lower,115391216845342+c.upper)) = pointBounds67629 := by
 decide +kernel
def cuts67630 : List PrefixCut := [⟨64,182214139,182214246⟩]
theorem checked67630 : checkPrefixCuts (2^48) 8868331521 10 Manual.Count131072.C067630.packed 64 cuts67630 = true := by
 decide +kernel
def cuts67631 : List PrefixCut := [⟨29,81441638,81441687⟩,
⟨64,180084955,180085062⟩]
theorem checked67631 : checkPrefixCuts (2^48) 8868462593 10 Manual.Count131072.C067631.packed 64 cuts67631 = true := by
 decide +kernel
def pointBounds67631 : List (Nat × Nat × Nat) := [(8868521984,115391269715413,115391658972930)]
theorem point_links_checked67631 : (cuts67631.take 1).map (fun c => (8868462593-1+2*2^10*c.k,115391188273775+c.lower,115391577531243+c.upper)) = pointBounds67631 := by
 decide +kernel
def cuts67632 : List PrefixCut := [⟨64,181605728,181605833⟩]
theorem checked67632 : checkPrefixCuts (2^48) 8868593665 10 Manual.Count131072.C067632.packed 64 cuts67632 = true := by
 decide +kernel
def cuts67633 : List PrefixCut := [⟨37,105464668,105464724⟩,
⟨64,183951637,183951741⟩]
theorem checked67633 : checkPrefixCuts (2^48) 8868724737 10 Manual.Count131072.C067633.packed 64 cuts67633 = true := by
 decide +kernel
def pointBounds67633 : List (Nat × Nat × Nat) := [(8868800512,115391655429126,115392044686862)]
theorem point_links_checked67633 : (cuts67633.take 1).map (fun c => (8868724737-1+2*2^10*c.k,115391549964458+c.lower,115391939222138+c.upper)) = pointBounds67633 := by
 decide +kernel
def cuts67634 : List PrefixCut := [⟨64,180489565,180489668⟩]
theorem checked67634 : checkPrefixCuts (2^48) 8868855809 10 Manual.Count131072.C067634.packed 64 cuts67634 = true := by
 decide +kernel
def cuts67635 : List PrefixCut := [⟨45,128280217,128280290⟩,
⟨64,183343195,183343294⟩]
theorem checked67635 : checkPrefixCuts (2^48) 8868986881 10 Manual.Count131072.C067635.packed 64 cuts67635 = true := by
 decide +kernel
def pointBounds67635 : List (Nat × Nat × Nat) := [(8869079040,115392042685877,115392431943837)]
theorem point_links_checked67635 : (cuts67635.take 1).map (fun c => (8868986881-1+2*2^10*c.k,115391914405660+c.lower,115392303663547+c.upper)) = pointBounds67635 := by
 decide +kernel
def cuts67636 : List PrefixCut := [⟨64,183753073,183753173⟩]
theorem checked67636 : checkPrefixCuts (2^48) 8869117953 10 Manual.Count131072.C067636.packed 64 cuts67636 = true := by
 decide +kernel
def cuts67637 : List PrefixCut := [⟨53,150332725,150332814⟩,
⟨64,181433630,181433737⟩]
theorem checked67637 : checkPrefixCuts (2^48) 8869249025 10 Manual.Count131072.C067637.packed 64 cuts67637 = true := by
 decide +kernel
def pointBounds67637 : List (Nat × Nat × Nat) := [(8869357568,115392431834653,115392821092828)]
theorem point_links_checked67637 : (cuts67637.take 1).map (fun c => (8869249025-1+2*2^10*c.k,115392281501928+c.lower,115392670760014+c.upper)) = pointBounds67637 := by
 decide +kernel
def cuts67638 : List PrefixCut := [⟨64,182827298,182827405⟩]
theorem checked67638 : checkPrefixCuts (2^48) 8869380097 10 Manual.Count131072.C067638.packed 64 cuts67638 = true := by
 decide +kernel
def cuts67639 : List PrefixCut := [⟨61,174764009,174764110⟩,
⟨64,182761140,182761246⟩]
theorem checked67639 : checkPrefixCuts (2^48) 8869511169 10 Manual.Count131072.C067639.packed 64 cuts67639 = true := by
 decide +kernel
def pointBounds67639 : List (Nat × Nat × Nat) := [(8869636096,115392820526865,115393209785266)]
theorem point_links_checked67639 : (cuts67639.take 1).map (fun c => (8869511169-1+2*2^10*c.k,115392645762856+c.lower,115393035021156+c.upper)) = pointBounds67639 := by
 decide +kernel
def cuts67640 : List PrefixCut := [⟨64,179807141,179807248⟩]
theorem checked67640 : checkPrefixCuts (2^48) 8869642241 10 Manual.Count131072.C067640.packed 64 cuts67640 = true := by
 decide +kernel
def cuts67641 : List PrefixCut := [⟨64,181740254,181740357⟩]
theorem checked67641 : checkPrefixCuts (2^48) 8869773313 10 Manual.Count131072.C067641.packed 64 cuts67641 = true := by
 decide +kernel
def cuts67642 : List PrefixCut := [⟨5,15295635,15295643⟩,
⟨64,180975967,180976072⟩]
theorem checked67642 : checkPrefixCuts (2^48) 8869904385 10 Manual.Count131072.C067642.packed 64 cuts67642 = true := by
 decide +kernel
def pointBounds67642 : List (Nat × Nat × Nat) := [(8869914624,115393205367026,115393594625650)]
theorem point_links_checked67642 : (cuts67642.take 1).map (fun c => (8869904385-1+2*2^10*c.k,115393190071391+c.lower,115393579330007+c.upper)) = pointBounds67642 := by
 decide +kernel
def cuts67643 : List PrefixCut := [⟨64,182813798,182813901⟩]
theorem checked67643 : checkPrefixCuts (2^48) 8870035457 10 Manual.Count131072.C067643.packed 64 cuts67643 = true := by
 decide +kernel
def cuts67644 : List PrefixCut := [⟨13,37444605,37444627⟩,
⟨64,182335111,182335221⟩]
theorem checked67644 : checkPrefixCuts (2^48) 8870166529 10 Manual.Count131072.C067644.packed 64 cuts67644 = true := by
 decide +kernel
def pointBounds67644 : List (Nat × Nat × Nat) := [(8870193152,115393591305761,115393980564607)]
theorem point_links_checked67644 : (cuts67644.take 1).map (fun c => (8870166529-1+2*2^10*c.k,115393553861156+c.lower,115393943119980+c.upper)) = pointBounds67644 := by
 decide +kernel
def cuts67645 : List PrefixCut := [⟨64,182427617,182427728⟩]
theorem checked67645 : checkPrefixCuts (2^48) 8870297601 10 Manual.Count131072.C067645.packed 64 cuts67645 = true := by
 decide +kernel
def cuts67646 : List PrefixCut := [⟨21,59782618,59782652⟩,
⟨64,180838338,180838442⟩]
theorem checked67646 : checkPrefixCuts (2^48) 8870428673 10 Manual.Count131072.C067646.packed 64 cuts67646 = true := by
 decide +kernel
def pointBounds67646 : List (Nat × Nat × Nat) := [(8870471680,115393978406502,115394367665581)]
theorem point_links_checked67646 : (cuts67646.take 1).map (fun c => (8870428673-1+2*2^10*c.k,115393918623884+c.lower,115394307882929+c.upper)) = pointBounds67646 := by
 decide +kernel
def cuts67647 : List PrefixCut := [⟨64,184230893,184231005⟩]
theorem checked67647 : checkPrefixCuts (2^48) 8870559745 10 Manual.Count131072.C067647.packed 64 cuts67647 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000238
