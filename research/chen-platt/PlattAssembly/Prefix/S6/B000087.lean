import PlattAssemblyKernel
import PlattCertificates.Count131072.C052784
import PlattCertificates.Count131072.C052785
import PlattCertificates.Count131072.C052786
import PlattCertificates.Count131072.C052787
import PlattCertificates.Count131072.C052788
import PlattCertificates.Count131072.C052789
import PlattCertificates.Count131072.C052790
import PlattCertificates.Count131072.C052791
import PlattCertificates.Count131072.C052792
import PlattCertificates.Count131072.C052793
import PlattCertificates.Count131072.C052794
import PlattCertificates.Count131072.C052795
import PlattCertificates.Count131072.C052796
import PlattCertificates.Count131072.C052797
import PlattCertificates.Count131072.C052798
import PlattCertificates.Count131072.C052799
import PlattCertificates.Count131072.C052800
import PlattCertificates.Count131072.C052801
import PlattCertificates.Count131072.C052802
import PlattCertificates.Count131072.C052803
import PlattCertificates.Count131072.C052804
import PlattCertificates.Count131072.C052805
import PlattCertificates.Count131072.C052806
import PlattCertificates.Count131072.C052807
import PlattCertificates.Count131072.C052808
import PlattCertificates.Count131072.C052809
import PlattCertificates.Count131072.C052810
import PlattCertificates.Count131072.C052811
import PlattCertificates.Count131072.C052812
import PlattCertificates.Count131072.C052813
import PlattCertificates.Count131072.C052814
import PlattCertificates.Count131072.C052815
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000087
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52784 : List PrefixCut := [⟨64,233352668,233352806⟩]
theorem checked52784 : checkPrefixCuts (2^48) 6922436609 10 Manual.Count131072.C052784.packed 64 cuts52784 = true := by
 decide +kernel
def cuts52785 : List PrefixCut := [⟨24,87866975,87867025⟩,
⟨64,234364759,234364892⟩]
theorem checked52785 : checkPrefixCuts (2^48) 6922567681 10 Manual.Count131072.C052785.packed 64 cuts52785 = true := by
 decide +kernel
def pointBounds52785 : List (Nat × Nat × Nat) := [(6922616832,112330716895794,112331104400946)]
theorem point_links_checked52785 : (cuts52785.take 1).map (fun c => (6922567681-1+2*2^10*c.k,112330629028819+c.lower,112331016533921+c.upper)) = pointBounds52785 := by
 decide +kernel
def cuts52786 : List PrefixCut := [⟨64,236311987,236312118⟩]
theorem checked52786 : checkPrefixCuts (2^48) 6922698753 10 Manual.Count131072.C052786.packed 64 cuts52786 = true := by
 decide +kernel
def cuts52787 : List PrefixCut := [⟨2,7521901,7521905⟩,
⟨64,235900909,235901045⟩]
theorem checked52787 : checkPrefixCuts (2^48) 6922829825 10 Manual.Count131072.C052787.packed 64 cuts52787 = true := by
 decide +kernel
def pointBounds52787 : List (Nat × Nat × Nat) := [(6922833920,112331107227466,112331494732836)]
theorem point_links_checked52787 : (cuts52787.take 1).map (fun c => (6922829825-1+2*2^10*c.k,112331099705565+c.lower,112331487210931+c.upper)) = pointBounds52787 := by
 decide +kernel
def cuts52788 : List PrefixCut := [⟨44,161167914,161168005⟩,
⟨64,231911993,231912125⟩]
theorem checked52788 : checkPrefixCuts (2^48) 6922960897 10 Manual.Count131072.C052788.packed 64 cuts52788 = true := by
 decide +kernel
def pointBounds52788 : List (Nat × Nat × Nat) := [(6923051008,112331496774388,112331884279981)]
theorem point_links_checked52788 : (cuts52788.take 1).map (fun c => (6922960897-1+2*2^10*c.k,112331335606474+c.lower,112331723111976+c.upper)) = pointBounds52788 := by
 decide +kernel
def cuts52789 : List PrefixCut := [⟨64,235566715,235566849⟩]
theorem checked52789 : checkPrefixCuts (2^48) 6923091969 10 Manual.Count131072.C052789.packed 64 cuts52789 = true := by
 decide +kernel
def cuts52790 : List PrefixCut := [⟨22,81760207,81760254⟩,
⟨64,235033733,235033872⟩]
theorem checked52790 : checkPrefixCuts (2^48) 6923223041 10 Manual.Count131072.C052790.packed 64 cuts52790 = true := by
 decide +kernel
def pointBounds52790 : List (Nat × Nat × Nat) := [(6923268096,112331884845389,112332272351204)]
theorem point_links_checked52790 : (cuts52790.take 1).map (fun c => (6923223041-1+2*2^10*c.k,112331803085182+c.lower,112332190590950+c.upper)) = pointBounds52790 := by
 decide +kernel
def cuts52791 : List PrefixCut := [⟨64,238119096,238119232⟩]
theorem checked52791 : checkPrefixCuts (2^48) 6923354113 10 Manual.Count131072.C052791.packed 64 cuts52791 = true := by
 decide +kernel
def pointBounds52791 : List (Nat × Nat × Nat) := [(6923485184,112332276238011,112332663744054)]
theorem point_links_checked52791 : (cuts52791.take 1).map (fun c => (6923354113-1+2*2^10*c.k,112332038118915+c.lower,112332425624822+c.upper)) = pointBounds52791 := by
 decide +kernel
def cuts52792 : List PrefixCut := [⟨64,235756625,235756757⟩]
theorem checked52792 : checkPrefixCuts (2^48) 6923485185 10 Manual.Count131072.C052792.packed 64 cuts52792 = true := by
 decide +kernel
def cuts52793 : List PrefixCut := [⟨42,153794328,153794414⟩,
⟨64,233882084,233882215⟩]
theorem checked52793 : checkPrefixCuts (2^48) 6923616257 10 Manual.Count131072.C052793.packed 64 cuts52793 = true := by
 decide +kernel
def pointBounds52793 : List (Nat × Nat × Nat) := [(6923702272,112332665788964,112333053295225)]
theorem point_links_checked52793 : (cuts52793.take 1).map (fun c => (6923616257-1+2*2^10*c.k,112332511994636+c.lower,112332899500811+c.upper)) = pointBounds52793 := by
 decide +kernel
def cuts52794 : List PrefixCut := [⟨64,230788011,230788144⟩]
theorem checked52794 : checkPrefixCuts (2^48) 6923747329 10 Manual.Count131072.C052794.packed 64 cuts52794 = true := by
 decide +kernel
def cuts52795 : List PrefixCut := [⟨20,73418698,73418739⟩,
⟨64,231637344,231637475⟩]
theorem checked52795 : checkPrefixCuts (2^48) 6923878401 10 Manual.Count131072.C052795.packed 64 cuts52795 = true := by
 decide +kernel
def pointBounds52795 : List (Nat × Nat × Nat) := [(6923919360,112333050083429,112333437589909)]
theorem point_links_checked52795 : (cuts52795.take 1).map (fun c => (6923878401-1+2*2^10*c.k,112332976664731+c.lower,112333364171170+c.upper)) = pointBounds52795 := by
 decide +kernel
def cuts52796 : List PrefixCut := [⟨62,230779357,230779488⟩,
⟨64,237771372,237771508⟩]
theorem checked52796 : checkPrefixCuts (2^48) 6924009473 10 Manual.Count131072.C052796.packed 64 cuts52796 = true := by
 decide +kernel
def pointBounds52796 : List (Nat × Nat × Nat) := [(6924136448,112333439081432,112333826588133)]
theorem point_links_checked52796 : (cuts52796.take 1).map (fun c => (6924009473-1+2*2^10*c.k,112333208302075+c.lower,112333595808645+c.upper)) = pointBounds52796 := by
 decide +kernel
def cuts52797 : List PrefixCut := [⟨64,235612352,235612483⟩]
theorem checked52797 : checkPrefixCuts (2^48) 6924140545 10 Manual.Count131072.C052797.packed 64 cuts52797 = true := by
 decide +kernel
def cuts52798 : List PrefixCut := [⟨40,148210741,148210822⟩,
⟨64,236298955,236299084⟩]
theorem checked52798 : checkPrefixCuts (2^48) 6924271617 10 Manual.Count131072.C052798.packed 64 cuts52798 = true := by
 decide +kernel
def pointBounds52798 : List (Nat × Nat × Nat) := [(6924353536,112333829896540,112334217403458)]
theorem point_links_checked52798 : (cuts52798.take 1).map (fun c => (6924271617-1+2*2^10*c.k,112333681685799+c.lower,112334069192636+c.upper)) = pointBounds52798 := by
 decide +kernel
def cuts52799 : List PrefixCut := [⟨64,236213166,236213300⟩]
theorem checked52799 : checkPrefixCuts (2^48) 6924402689 10 Manual.Count131072.C052799.packed 64 cuts52799 = true := by
 decide +kernel
def cuts52800 : List PrefixCut := [⟨18,65566553,65566592⟩,
⟨64,234501467,234501601⟩]
theorem checked52800 : checkPrefixCuts (2^48) 6924533761 10 Manual.Count131072.C052800.packed 64 cuts52800 = true := by
 decide +kernel
def pointBounds52800 : List (Nat × Nat × Nat) := [(6924570624,112334219764473,112334607271612)]
theorem point_links_checked52800 : (cuts52800.take 1).map (fun c => (6924533761-1+2*2^10*c.k,112334154197920+c.lower,112334541705020+c.upper)) = pointBounds52800 := by
 decide +kernel
def cuts52801 : List PrefixCut := [⟨60,221002102,221002228⟩,
⟨64,235757114,235757248⟩]
theorem checked52801 : checkPrefixCuts (2^48) 6924664833 10 Manual.Count131072.C052801.packed 64 cuts52801 = true := by
 decide +kernel
def pointBounds52801 : List (Nat × Nat × Nat) := [(6924787712,112334609701489,112334997208849)]
theorem point_links_checked52801 : (cuts52801.take 1).map (fun c => (6924664833-1+2*2^10*c.k,112334388699387+c.lower,112334776206621+c.upper)) = pointBounds52801 := by
 decide +kernel
def cuts52802 : List PrefixCut := [⟨64,237094009,237094145⟩]
theorem checked52802 : checkPrefixCuts (2^48) 6924795905 10 Manual.Count131072.C052802.packed 64 cuts52802 = true := by
 decide +kernel
def cuts52803 : List PrefixCut := [⟨38,140921056,140921135⟩,
⟨64,237536616,237536750⟩]
theorem checked52803 : checkPrefixCuts (2^48) 6924926977 10 Manual.Count131072.C052803.packed 64 cuts52803 = true := by
 decide +kernel
def pointBounds52803 : List (Nat × Nat × Nat) := [(6925004800,112335002471566,112335389979149)]
theorem point_links_checked52803 : (cuts52803.take 1).map (fun c => (6924926977-1+2*2^10*c.k,112334861550510+c.lower,112335249058014+c.upper)) = pointBounds52803 := by
 decide +kernel
def cuts52804 : List PrefixCut := [⟨64,231353984,231354116⟩]
theorem checked52804 : checkPrefixCuts (2^48) 6925058049 10 Manual.Count131072.C052804.packed 64 cuts52804 = true := by
 decide +kernel
def cuts52805 : List PrefixCut := [⟨16,56862340,56862373⟩,
⟨64,232894118,232894250⟩]
theorem checked52805 : checkPrefixCuts (2^48) 6925189121 10 Manual.Count131072.C052805.packed 64 cuts52805 = true := by
 decide +kernel
def pointBounds52805 : List (Nat × Nat × Nat) := [(6925221888,112335387303450,112335774811253)]
theorem point_links_checked52805 : (cuts52805.take 1).map (fun c => (6925189121-1+2*2^10*c.k,112335330441110+c.lower,112335717948880+c.upper)) = pointBounds52805 := by
 decide +kernel
def cuts52806 : List PrefixCut := [⟨58,212283454,212283575⟩,
⟨64,235084503,235084637⟩]
theorem checked52806 : checkPrefixCuts (2^48) 6925320193 10 Manual.Count131072.C052806.packed 64 cuts52806 = true := by
 decide +kernel
def pointBounds52806 : List (Nat × Nat × Nat) := [(6925438976,112335775618682,112336163126705)]
theorem point_links_checked52806 : (cuts52806.take 1).map (fun c => (6925320193-1+2*2^10*c.k,112335563335228+c.lower,112335950843130+c.upper)) = pointBounds52806 := by
 decide +kernel
def cuts52807 : List PrefixCut := [⟨64,234063952,234064087⟩]
theorem checked52807 : checkPrefixCuts (2^48) 6925451265 10 Manual.Count131072.C052807.packed 64 cuts52807 = true := by
 decide +kernel
def cuts52808 : List PrefixCut := [⟨36,129852977,129853048⟩,
⟨64,232108688,232108816⟩]
theorem checked52808 : checkPrefixCuts (2^48) 6925582337 10 Manual.Count131072.C052808.packed 64 cuts52808 = true := by
 decide +kernel
def pointBounds52808 : List (Nat × Nat × Nat) := [(6925656064,112336162336660,112336549844902)]
theorem point_links_checked52808 : (cuts52808.take 1).map (fun c => (6925582337-1+2*2^10*c.k,112336032483683+c.lower,112336419991854+c.upper)) = pointBounds52808 := by
 decide +kernel
def cuts52809 : List PrefixCut := [⟨64,236249756,236249891⟩]
theorem checked52809 : checkPrefixCuts (2^48) 6925713409 10 Manual.Count131072.C052809.packed 64 cuts52809 = true := by
 decide +kernel
def cuts52810 : List PrefixCut := [⟨14,52223882,52223911⟩,
⟨64,234904148,234904281⟩]
theorem checked52810 : checkPrefixCuts (2^48) 6925844481 10 Manual.Count131072.C052810.packed 64 cuts52810 = true := by
 decide +kernel
def pointBounds52810 : List (Nat × Nat × Nat) := [(6925873152,112336553066009,112336940574472)]
theorem point_links_checked52810 : (cuts52810.take 1).map (fun c => (6925844481-1+2*2^10*c.k,112336500842127+c.lower,112336888350561+c.upper)) = pointBounds52810 := by
 decide +kernel
def cuts52811 : List PrefixCut := [⟨56,206086126,206086240⟩,
⟨64,234940347,234940478⟩]
theorem checked52811 : checkPrefixCuts (2^48) 6925975553 10 Manual.Count131072.C052811.packed 64 cuts52811 = true := by
 decide +kernel
def pointBounds52811 : List (Nat × Nat × Nat) := [(6926090240,112336941832401,112337329341082)]
theorem point_links_checked52811 : (cuts52811.take 1).map (fun c => (6925975553-1+2*2^10*c.k,112336735746275+c.lower,112337123254842+c.upper)) = pointBounds52811 := by
 decide +kernel
def cuts52812 : List PrefixCut := [⟨64,234245006,234245142⟩]
theorem checked52812 : checkPrefixCuts (2^48) 6926106625 10 Manual.Count131072.C052812.packed 64 cuts52812 = true := by
 decide +kernel
def cuts52813 : List PrefixCut := [⟨34,126508352,126508427⟩,
⟨64,237166553,237166691⟩]
theorem checked52813 : checkPrefixCuts (2^48) 6926237697 10 Manual.Count131072.C052813.packed 64 cuts52813 = true := by
 decide +kernel
def pointBounds52813 : List (Nat × Nat × Nat) := [(6926307328,112337331439980,112337718948889)]
theorem point_links_checked52813 : (cuts52813.take 1).map (fun c => (6926237697-1+2*2^10*c.k,112337204931628+c.lower,112337592440462+c.upper)) = pointBounds52813 := by
 decide +kernel
def cuts52814 : List PrefixCut := [⟨64,233707854,233707987⟩]
theorem checked52814 : checkPrefixCuts (2^48) 6926368769 10 Manual.Count131072.C052814.packed 64 cuts52814 = true := by
 decide +kernel
def cuts52815 : List PrefixCut := [⟨12,45635715,45635739⟩,
⟨64,235735284,235735417⟩]
theorem checked52815 : checkPrefixCuts (2^48) 6926499841 10 Manual.Count131072.C052815.packed 64 cuts52815 = true := by
 decide +kernel
def pointBounds52815 : List (Nat × Nat × Nat) := [(6926524416,112337721441750,112338108950879)]
theorem point_links_checked52815 : (cuts52815.take 1).map (fun c => (6926499841-1+2*2^10*c.k,112337675806035+c.lower,112338063315140+c.upper)) = pointBounds52815 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000087
