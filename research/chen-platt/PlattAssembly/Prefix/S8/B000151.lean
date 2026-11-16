import PlattAssemblyKernel
import PlattCertificates.Count131072.C074832
import PlattCertificates.Count131072.C074833
import PlattCertificates.Count131072.C074834
import PlattCertificates.Count131072.C074835
import PlattCertificates.Count131072.C074836
import PlattCertificates.Count131072.C074837
import PlattCertificates.Count131072.C074838
import PlattCertificates.Count131072.C074839
import PlattCertificates.Count131072.C074840
import PlattCertificates.Count131072.C074841
import PlattCertificates.Count131072.C074842
import PlattCertificates.Count131072.C074843
import PlattCertificates.Count131072.C074844
import PlattCertificates.Count131072.C074845
import PlattCertificates.Count131072.C074846
import PlattCertificates.Count131072.C074847
import PlattCertificates.Count131072.C074848
import PlattCertificates.Count131072.C074849
import PlattCertificates.Count131072.C074850
import PlattCertificates.Count131072.C074851
import PlattCertificates.Count131072.C074852
import PlattCertificates.Count131072.C074853
import PlattCertificates.Count131072.C074854
import PlattCertificates.Count131072.C074855
import PlattCertificates.Count131072.C074856
import PlattCertificates.Count131072.C074857
import PlattCertificates.Count131072.C074858
import PlattCertificates.Count131072.C074859
import PlattCertificates.Count131072.C074860
import PlattCertificates.Count131072.C074861
import PlattCertificates.Count131072.C074862
import PlattCertificates.Count131072.C074863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000151
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74832 : List PrefixCut := [⟨13,33619816,33619834⟩,
⟨64,161586547,161586636⟩]
theorem checked74832 : checkPrefixCuts (2^48) 9812312065 10 Manual.Count131072.C074832.packed 64 cuts74832 = true := by
 decide +kernel
def pointBounds74832 : List (Nat × Nat × Nat) := [(9812338688,116631341950259,116631731941228)]
theorem point_links_checked74832 : (cuts74832.take 1).map (fun c => (9812312065-1+2*2^10*c.k,116631308330443+c.lower,116631698321394+c.upper)) = pointBounds74832 := by
 decide +kernel
def cuts74833 : List PrefixCut := [⟨64,162932584,162932680⟩]
theorem checked74833 : checkPrefixCuts (2^48) 9812443137 10 Manual.Count131072.C074833.packed 64 cuts74833 = true := by
 decide +kernel
def cuts74834 : List PrefixCut := [⟨35,89296457,89296515⟩,
⟨64,162930407,162930506⟩]
theorem checked74834 : checkPrefixCuts (2^48) 9812574209 10 Manual.Count131072.C074834.packed 64 cuts74834 = true := by
 decide +kernel
def pointBounds74834 : List (Nat × Nat × Nat) := [(9812645888,116631722146031,116632112137225)]
theorem point_links_checked74834 : (cuts74834.take 1).map (fun c => (9812574209-1+2*2^10*c.k,116631632849574+c.lower,116632022840710+c.upper)) = pointBounds74834 := by
 decide +kernel
def cuts74835 : List PrefixCut := [⟨64,162842184,162842278⟩]
theorem checked74835 : checkPrefixCuts (2^48) 9812705281 10 Manual.Count131072.C074835.packed 64 cuts74835 = true := by
 decide +kernel
def cuts74836 : List PrefixCut := [⟨57,145744339,145744419⟩,
⟨64,163929991,163930080⟩]
theorem checked74836 : checkPrefixCuts (2^48) 9812836353 10 Manual.Count131072.C074836.packed 64 cuts74836 = true := by
 decide +kernel
def pointBounds74836 : List (Nat × Nat × Nat) := [(9812953088,116632104366504,116632494357913)]
theorem point_links_checked74836 : (cuts74836.take 1).map (fun c => (9812836353-1+2*2^10*c.k,116631958622165+c.lower,116632348613494+c.upper)) = pointBounds74836 := by
 decide +kernel
def cuts74837 : List PrefixCut := [⟨64,161891245,161891346⟩]
theorem checked74837 : checkPrefixCuts (2^48) 9812967425 10 Manual.Count131072.C074837.packed 64 cuts74837 = true := by
 decide +kernel
def cuts74838 : List PrefixCut := [⟨64,163782201,163782302⟩]
theorem checked74838 : checkPrefixCuts (2^48) 9813098497 10 Manual.Count131072.C074838.packed 64 cuts74838 = true := by
 decide +kernel
def cuts74839 : List PrefixCut := [⟨15,39037783,39037807⟩,
⟨64,163866069,163866171⟩]
theorem checked74839 : checkPrefixCuts (2^48) 9813229569 10 Manual.Count131072.C074839.packed 64 cuts74839 = true := by
 decide +kernel
def pointBounds74839 : List (Nat × Nat × Nat) := [(9813260288,116632487263385,116632877255029)]
theorem point_links_checked74839 : (cuts74839.take 1).map (fun c => (9813229569-1+2*2^10*c.k,116632448225602+c.lower,116632838217222+c.upper)) = pointBounds74839 := by
 decide +kernel
def cuts74840 : List PrefixCut := [⟨64,162831300,162831402⟩]
theorem checked74840 : checkPrefixCuts (2^48) 9813360641 10 Manual.Count131072.C074840.packed 64 cuts74840 = true := by
 decide +kernel
def cuts74841 : List PrefixCut := [⟨37,93188895,93188950⟩,
⟨64,162398894,162398991⟩]
theorem checked74841 : checkPrefixCuts (2^48) 9813491713 10 Manual.Count131072.C074841.packed 64 cuts74841 = true := by
 decide +kernel
def pointBounds74841 : List (Nat × Nat × Nat) := [(9813567488,116632868111866,116633258103745)]
theorem point_links_checked74841 : (cuts74841.take 1).map (fun c => (9813491713-1+2*2^10*c.k,116632774922971+c.lower,116633164914795+c.upper)) = pointBounds74841 := by
 decide +kernel
def cuts74842 : List PrefixCut := [⟨64,164261054,164261149⟩]
theorem checked74842 : checkPrefixCuts (2^48) 9813622785 10 Manual.Count131072.C074842.packed 64 cuts74842 = true := by
 decide +kernel
def cuts74843 : List PrefixCut := [⟨59,150864676,150864772⟩,
⟨64,163599177,163599280⟩]
theorem checked74843 : checkPrefixCuts (2^48) 9813753857 10 Manual.Count131072.C074843.packed 64 cuts74843 = true := by
 decide +kernel
def pointBounds74843 : List (Nat × Nat × Nat) := [(9813874688,116633252447595,116633642439707)]
theorem point_links_checked74843 : (cuts74843.take 1).map (fun c => (9813753857-1+2*2^10*c.k,116633101582919+c.lower,116633491574935+c.upper)) = pointBounds74843 := by
 decide +kernel
def cuts74844 : List PrefixCut := [⟨64,164256654,164256751⟩]
theorem checked74844 : checkPrefixCuts (2^48) 9813884929 10 Manual.Count131072.C074844.packed 64 cuts74844 = true := by
 decide +kernel
def cuts74845 : List PrefixCut := [⟨64,162246816,162246918⟩]
theorem checked74845 : checkPrefixCuts (2^48) 9814016001 10 Manual.Count131072.C074845.packed 64 cuts74845 = true := by
 decide +kernel
def cuts74846 : List PrefixCut := [⟨17,43450919,43450944⟩,
⟨64,164280944,164281043⟩]
theorem checked74846 : checkPrefixCuts (2^48) 9814147073 10 Manual.Count131072.C074846.packed 64 cuts74846 = true := by
 decide +kernel
def pointBounds74846 : List (Nat × Nat × Nat) := [(9814181888,116633635136485,116634025128828)]
theorem point_links_checked74846 : (cuts74846.take 1).map (fun c => (9814147073-1+2*2^10*c.k,116633591685566+c.lower,116633981677884+c.upper)) = pointBounds74846 := by
 decide +kernel
def cuts74847 : List PrefixCut := [⟨64,162414565,162414661⟩]
theorem checked74847 : checkPrefixCuts (2^48) 9814278145 10 Manual.Count131072.C074847.packed 64 cuts74847 = true := by
 decide +kernel
def cuts74848 : List PrefixCut := [⟨39,99518362,99518420⟩,
⟨64,163760336,163760433⟩]
theorem checked74848 : checkPrefixCuts (2^48) 9814409217 10 Manual.Count131072.C074848.packed 64 cuts74848 = true := by
 decide +kernel
def pointBounds74848 : List (Nat × Nat × Nat) := [(9814489088,116634017899437,116634407892008)]
theorem point_links_checked74848 : (cuts74848.take 1).map (fun c => (9814409217-1+2*2^10*c.k,116633918381075+c.lower,116634308373588+c.upper)) = pointBounds74848 := by
 decide +kernel
def cuts74849 : List PrefixCut := [⟨64,165220774,165220872⟩]
theorem checked74849 : checkPrefixCuts (2^48) 9814540289 10 Manual.Count131072.C074849.packed 64 cuts74849 = true := by
 decide +kernel
def cuts74850 : List PrefixCut := [⟨61,153718430,153718526⟩,
⟨64,161260907,161261007⟩]
theorem checked74850 : checkPrefixCuts (2^48) 9814671361 10 Manual.Count131072.C074850.packed 64 cuts74850 = true := by
 decide +kernel
def pointBounds74850 : List (Nat × Nat × Nat) := [(9814796288,116634401080615,116634791073419)]
theorem point_links_checked74850 : (cuts74850.take 1).map (fun c => (9814671361-1+2*2^10*c.k,116634247362185+c.lower,116634637354893+c.upper)) = pointBounds74850 := by
 decide +kernel
def cuts74851 : List PrefixCut := [⟨64,163266228,163266325⟩]
theorem checked74851 : checkPrefixCuts (2^48) 9814802433 10 Manual.Count131072.C074851.packed 64 cuts74851 = true := by
 decide +kernel
def cuts74852 : List PrefixCut := [⟨64,160310224,160310314⟩]
theorem checked74852 : checkPrefixCuts (2^48) 9814933505 10 Manual.Count131072.C074852.packed 64 cuts74852 = true := by
 decide +kernel
def cuts74853 : List PrefixCut := [⟨19,49583893,49583926⟩,
⟨64,165384026,165384127⟩]
theorem checked74853 : checkPrefixCuts (2^48) 9815064577 10 Manual.Count131072.C074853.packed 64 cuts74853 = true := by
 decide +kernel
def pointBounds74853 : List (Nat × Nat × Nat) := [(9815103488,116634781783437,116635171776465)]
theorem point_links_checked74853 : (cuts74853.take 1).map (fun c => (9815064577-1+2*2^10*c.k,116634732199544+c.lower,116635122192539+c.upper)) = pointBounds74853 := by
 decide +kernel
def cuts74854 : List PrefixCut := [⟨64,161395680,161395780⟩]
theorem checked74854 : checkPrefixCuts (2^48) 9815195649 10 Manual.Count131072.C074854.packed 64 cuts74854 = true := by
 decide +kernel
def cuts74855 : List PrefixCut := [⟨41,103466449,103466509⟩,
⟨64,161422190,161422284⟩]
theorem checked74855 : checkPrefixCuts (2^48) 9815326721 10 Manual.Count131072.C074855.packed 64 cuts74855 = true := by
 decide +kernel
def pointBounds74855 : List (Nat × Nat × Nat) := [(9815410688,116635162445699,116635552438955)]
theorem point_links_checked74855 : (cuts74855.take 1).map (fun c => (9815326721-1+2*2^10*c.k,116635058979250+c.lower,116635448972446+c.upper)) = pointBounds74855 := by
 decide +kernel
def cuts74856 : List PrefixCut := [⟨64,164574465,164574554⟩]
theorem checked74856 : checkPrefixCuts (2^48) 9815457793 10 Manual.Count131072.C074856.packed 64 cuts74856 = true := by
 decide +kernel
def cuts74857 : List PrefixCut := [⟨63,161446580,161446679⟩,
⟨64,164142118,164142218⟩]
theorem checked74857 : checkPrefixCuts (2^48) 9815588865 10 Manual.Count131072.C074857.packed 64 cuts74857 = true := by
 decide +kernel
def pointBounds74857 : List (Nat × Nat × Nat) := [(9815717888,116635546422485,116635936415963)]
theorem point_links_checked74857 : (cuts74857.take 1).map (fun c => (9815588865-1+2*2^10*c.k,116635384975905+c.lower,116635774969284+c.upper)) = pointBounds74857 := by
 decide +kernel
def cuts74858 : List PrefixCut := [⟨64,163824487,163824583⟩]
theorem checked74858 : checkPrefixCuts (2^48) 9815719937 10 Manual.Count131072.C074858.packed 64 cuts74858 = true := by
 decide +kernel
def cuts74859 : List PrefixCut := [⟨64,163248792,163248891⟩]
theorem checked74859 : checkPrefixCuts (2^48) 9815851009 10 Manual.Count131072.C074859.packed 64 cuts74859 = true := by
 decide +kernel
def cuts74860 : List PrefixCut := [⟨21,55973798,55973832⟩,
⟨64,165798697,165798797⟩]
theorem checked74860 : checkPrefixCuts (2^48) 9815982081 10 Manual.Count131072.C074860.packed 64 cuts74860 = true := by
 decide +kernel
def pointBounds74860 : List (Nat × Nat × Nat) := [(9816025088,116635932165100,116636322158808)]
theorem point_links_checked74860 : (cuts74860.take 1).map (fun c => (9815982081-1+2*2^10*c.k,116635876191302+c.lower,116636266184976+c.upper)) = pointBounds74860 := by
 decide +kernel
def cuts74861 : List PrefixCut := [⟨64,164391419,164391514⟩]
theorem checked74861 : checkPrefixCuts (2^48) 9816113153 10 Manual.Count131072.C074861.packed 64 cuts74861 = true := by
 decide +kernel
def cuts74862 : List PrefixCut := [⟨43,109937149,109937220⟩,
⟨64,162926845,162926945⟩]
theorem checked74862 : checkPrefixCuts (2^48) 9816244225 10 Manual.Count131072.C074862.packed 64 cuts74862 = true := by
 decide +kernel
def pointBounds74862 : List (Nat × Nat × Nat) := [(9816332288,116636316318567,116636706312507)]
theorem point_links_checked74862 : (cuts74862.take 1).map (fun c => (9816244225-1+2*2^10*c.k,116636206381418+c.lower,116636596375287+c.upper)) = pointBounds74862 := by
 decide +kernel
def cuts74863 : List PrefixCut := [⟨64,163498138,163498234⟩]
theorem checked74863 : checkPrefixCuts (2^48) 9816375297 10 Manual.Count131072.C074863.packed 64 cuts74863 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000151
