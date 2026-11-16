import PlattAssemblyKernel
import PlattCertificates.Count131072.C051792
import PlattCertificates.Count131072.C051793
import PlattCertificates.Count131072.C051794
import PlattCertificates.Count131072.C051795
import PlattCertificates.Count131072.C051796
import PlattCertificates.Count131072.C051797
import PlattCertificates.Count131072.C051798
import PlattCertificates.Count131072.C051799
import PlattCertificates.Count131072.C051800
import PlattCertificates.Count131072.C051801
import PlattCertificates.Count131072.C051802
import PlattCertificates.Count131072.C051803
import PlattCertificates.Count131072.C051804
import PlattCertificates.Count131072.C051805
import PlattCertificates.Count131072.C051806
import PlattCertificates.Count131072.C051807
import PlattCertificates.Count131072.C051808
import PlattCertificates.Count131072.C051809
import PlattCertificates.Count131072.C051810
import PlattCertificates.Count131072.C051811
import PlattCertificates.Count131072.C051812
import PlattCertificates.Count131072.C051813
import PlattCertificates.Count131072.C051814
import PlattCertificates.Count131072.C051815
import PlattCertificates.Count131072.C051816
import PlattCertificates.Count131072.C051817
import PlattCertificates.Count131072.C051818
import PlattCertificates.Count131072.C051819
import PlattCertificates.Count131072.C051820
import PlattCertificates.Count131072.C051821
import PlattCertificates.Count131072.C051822
import PlattCertificates.Count131072.C051823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51792 : List PrefixCut := [⟨64,240015851,240015987⟩]
theorem checked51792 : checkPrefixCuts (2^48) 6792413185 10 Manual.Count131072.C051792.packed 64 cuts51792 = true := by
 decide +kernel
def cuts51793 : List PrefixCut := [⟨11,42184632,42184655⟩,
⟨64,239638294,239638427⟩]
theorem checked51793 : checkPrefixCuts (2^48) 6792544257 10 Manual.Count131072.C051793.packed 64 cuts51793 = true := by
 decide +kernel
def pointBounds51793 : List (Nat × Nat × Nat) := [(6792566784,112095070059789,112095457431062)]
theorem point_links_checked51793 : (cuts51793.take 1).map (fun c => (6792544257-1+2*2^10*c.k,112095027875157+c.lower,112095415246407+c.upper)) = pointBounds51793 := by
 decide +kernel
def cuts51794 : List PrefixCut := [⟨51,188127086,188127192⟩,
⟨64,237354579,237354715⟩]
theorem checked51794 : checkPrefixCuts (2^48) 6792675329 10 Manual.Count131072.C051794.packed 64 cuts51794 = true := by
 decide +kernel
def pointBounds51794 : List (Nat × Nat × Nat) := [(6792779776,112095455640537,112095843012026)]
theorem point_links_checked51794 : (cuts51794.take 1).map (fun c => (6792675329-1+2*2^10*c.k,112095267513451+c.lower,112095654884834+c.upper)) = pointBounds51794 := by
 decide +kernel
def cuts51795 : List PrefixCut := [⟨64,240623514,240623647⟩]
theorem checked51795 : checkPrefixCuts (2^48) 6792806401 10 Manual.Count131072.C051795.packed 64 cuts51795 = true := by
 decide +kernel
def cuts51796 : List PrefixCut := [⟨27,99198345,99198403⟩,
⟨64,234444912,234445047⟩]
theorem checked51796 : checkPrefixCuts (2^48) 6792937473 10 Manual.Count131072.C051796.packed 64 cuts51796 = true := by
 decide +kernel
def pointBounds51796 : List (Nat × Nat × Nat) := [(6792992768,112095844689889,112096232061599)]
theorem point_links_checked51796 : (cuts51796.take 1).map (fun c => (6792937473-1+2*2^10*c.k,112095745491544+c.lower,112096132863196+c.upper)) = pointBounds51796 := by
 decide +kernel
def cuts51797 : List PrefixCut := [⟨64,239163997,239164132⟩]
theorem checked51797 : checkPrefixCuts (2^48) 6793068545 10 Manual.Count131072.C051797.packed 64 cuts51797 = true := by
 decide +kernel
def cuts51798 : List PrefixCut := [⟨3,12513306,12513312⟩,
⟨64,243054215,243054356⟩]
theorem checked51798 : checkPrefixCuts (2^48) 6793199617 10 Manual.Count131072.C051798.packed 64 cuts51798 = true := by
 decide +kernel
def pointBounds51798 : List (Nat × Nat × Nat) := [(6793205760,112096231613759,112096618985687)]
theorem point_links_checked51798 : (cuts51798.take 1).map (fun c => (6793199617-1+2*2^10*c.k,112096219100453+c.lower,112096606472375+c.upper)) = pointBounds51798 := by
 decide +kernel
def cuts51799 : List PrefixCut := [⟨43,161840182,161840273⟩,
⟨64,238864754,238864888⟩]
theorem checked51799 : checkPrefixCuts (2^48) 6793330689 10 Manual.Count131072.C051799.packed 64 cuts51799 = true := by
 decide +kernel
def pointBounds51799 : List (Nat × Nat × Nat) := [(6793418752,112096623994850,112097011367004)]
theorem point_links_checked51799 : (cuts51799.take 1).map (fun c => (6793330689-1+2*2^10*c.k,112096462154668+c.lower,112096849526731+c.upper)) = pointBounds51799 := by
 decide +kernel
def cuts51800 : List PrefixCut := [⟨64,238818719,238818852⟩]
theorem checked51800 : checkPrefixCuts (2^48) 6793461761 10 Manual.Count131072.C051800.packed 64 cuts51800 = true := by
 decide +kernel
def cuts51801 : List PrefixCut := [⟨19,73335150,73335189⟩,
⟨64,244075959,244076094⟩]
theorem checked51801 : checkPrefixCuts (2^48) 6793592833 10 Manual.Count131072.C051801.packed 64 cuts51801 = true := by
 decide +kernel
def pointBounds51801 : List (Nat × Nat × Nat) := [(6793631744,112097013173291,112097400545660)]
theorem point_links_checked51801 : (cuts51801.take 1).map (fun c => (6793592833-1+2*2^10*c.k,112096939838141+c.lower,112097327210471+c.upper)) = pointBounds51801 := by
 decide +kernel
def cuts51802 : List PrefixCut := [⟨59,219999863,219999989⟩,
⟨64,238892325,238892462⟩]
theorem checked51802 : checkPrefixCuts (2^48) 6793723905 10 Manual.Count131072.C051802.packed 64 cuts51802 = true := by
 decide +kernel
def pointBounds51802 : List (Nat × Nat × Nat) := [(6793844736,112097403913963,112097791286554)]
theorem point_links_checked51802 : (cuts51802.take 1).map (fun c => (6793723905-1+2*2^10*c.k,112097183914100+c.lower,112097571286565+c.upper)) = pointBounds51802 := by
 decide +kernel
def cuts51803 : List PrefixCut := [⟨64,241580705,241580843⟩]
theorem checked51803 : checkPrefixCuts (2^48) 6793854977 10 Manual.Count131072.C051803.packed 64 cuts51803 = true := by
 decide +kernel
def cuts51804 : List PrefixCut := [⟨35,130545261,130545335⟩,
⟨64,237598809,237598944⟩]
theorem checked51804 : checkPrefixCuts (2^48) 6793986049 10 Manual.Count131072.C051804.packed 64 cuts51804 = true := by
 decide +kernel
def pointBounds51804 : List (Nat × Nat × Nat) := [(6794057728,112097794932391,112098182305205)]
theorem point_links_checked51804 : (cuts51804.take 1).map (fun c => (6793986049-1+2*2^10*c.k,112097664387130+c.lower,112098051759870+c.upper)) = pointBounds51804 := by
 decide +kernel
def cuts51805 : List PrefixCut := [⟨64,243269979,243270115⟩]
theorem checked51805 : checkPrefixCuts (2^48) 6794117121 10 Manual.Count131072.C051805.packed 64 cuts51805 = true := by
 decide +kernel
def cuts51806 : List PrefixCut := [⟨11,42671191,42671216⟩,
⟨64,240448181,240448318⟩]
theorem checked51806 : checkPrefixCuts (2^48) 6794248193 10 Manual.Count131072.C051806.packed 64 cuts51806 = true := by
 decide +kernel
def pointBounds51806 : List (Nat × Nat × Nat) := [(6794270720,112098187927109,112098575300145)]
theorem point_links_checked51806 : (cuts51806.take 1).map (fun c => (6794248193-1+2*2^10*c.k,112098145255918+c.lower,112098532628929+c.upper)) = pointBounds51806 := by
 decide +kernel
def cuts51807 : List PrefixCut := [⟨51,191518380,191518489⟩,
⟨64,239904992,239905129⟩]
theorem checked51807 : checkPrefixCuts (2^48) 6794379265 10 Manual.Count131072.C051807.packed 64 cuts51807 = true := by
 decide +kernel
def pointBounds51807 : List (Nat × Nat × Nat) := [(6794483712,112098577222479,112098964595736)]
theorem point_links_checked51807 : (cuts51807.take 1).map (fun c => (6794379265-1+2*2^10*c.k,112098385704099+c.lower,112098773077247+c.upper)) = pointBounds51807 := by
 decide +kernel
def cuts51808 : List PrefixCut := [⟨64,242054523,242054660⟩]
theorem checked51808 : checkPrefixCuts (2^48) 6794510337 10 Manual.Count131072.C051808.packed 64 cuts51808 = true := by
 decide +kernel
def cuts51809 : List PrefixCut := [⟨27,101451890,101451945⟩,
⟨64,240724228,240724365⟩]
theorem checked51809 : checkPrefixCuts (2^48) 6794641409 10 Manual.Count131072.C051809.packed 64 cuts51809 = true := by
 decide +kernel
def pointBounds51809 : List (Nat × Nat × Nat) := [(6794696704,112098969115504,112099356488981)]
theorem point_links_checked51809 : (cuts51809.take 1).map (fun c => (6794641409-1+2*2^10*c.k,112098867663614+c.lower,112099255037036+c.upper)) = pointBounds51809 := by
 decide +kernel
def cuts51810 : List PrefixCut := [⟨64,239435411,239435548⟩]
theorem checked51810 : checkPrefixCuts (2^48) 6794772481 10 Manual.Count131072.C051810.packed 64 cuts51810 = true := by
 decide +kernel
def cuts51811 : List PrefixCut := [⟨3,12178772,12178779⟩,
⟨64,239886457,239886597⟩]
theorem checked51811 : checkPrefixCuts (2^48) 6794903553 10 Manual.Count131072.C051811.packed 64 cuts51811 = true := by
 decide +kernel
def pointBounds51811 : List (Nat × Nat × Nat) := [(6794909696,112099360002025,112099747375728)]
theorem point_links_checked51811 : (cuts51811.take 1).map (fun c => (6794903553-1+2*2^10*c.k,112099347823253+c.lower,112099735196949+c.upper)) = pointBounds51811 := by
 decide +kernel
def cuts51812 : List PrefixCut := [⟨43,161343936,161344029⟩,
⟨64,237479314,237479451⟩]
theorem checked51812 : checkPrefixCuts (2^48) 6795034625 10 Manual.Count131072.C051812.packed 64 cuts51812 = true := by
 decide +kernel
def pointBounds51812 : List (Nat × Nat × Nat) := [(6795122688,112099749053646,112100136427575)]
theorem point_links_checked51812 : (cuts51812.take 1).map (fun c => (6795034625-1+2*2^10*c.k,112099587709710+c.lower,112099975083546+c.upper)) = pointBounds51812 := by
 decide +kernel
def cuts51813 : List PrefixCut := [⟨64,237598967,237599105⟩]
theorem checked51813 : checkPrefixCuts (2^48) 6795165697 10 Manual.Count131072.C051813.packed 64 cuts51813 = true := by
 decide +kernel
def cuts51814 : List PrefixCut := [⟨19,69754477,69754517⟩,
⟨64,234984836,234984969⟩]
theorem checked51814 : checkPrefixCuts (2^48) 6795296769 10 Manual.Count131072.C051814.packed 64 cuts51814 = true := by
 decide +kernel
def pointBounds51814 : List (Nat × Nat × Nat) := [(6795335680,112100132542468,112100519916619)]
theorem point_links_checked51814 : (cuts51814.take 1).map (fun c => (6795296769-1+2*2^10*c.k,112100062787991+c.lower,112100450162102+c.upper)) = pointBounds51814 := by
 decide +kernel
def cuts51815 : List PrefixCut := [⟨59,221311593,221311721⟩,
⟨64,239909376,239909514⟩]
theorem checked51815 : checkPrefixCuts (2^48) 6795427841 10 Manual.Count131072.C051815.packed 64 cuts51815 = true := by
 decide +kernel
def pointBounds51815 : List (Nat × Nat × Nat) := [(6795548672,112100519084420,112100906458792)]
theorem point_links_checked51815 : (cuts51815.take 1).map (fun c => (6795427841-1+2*2^10*c.k,112100297772827+c.lower,112100685147071+c.upper)) = pointBounds51815 := by
 decide +kernel
def cuts51816 : List PrefixCut := [⟨64,238537897,238538033⟩]
theorem checked51816 : checkPrefixCuts (2^48) 6795558913 10 Manual.Count131072.C051816.packed 64 cuts51816 = true := by
 decide +kernel
def cuts51817 : List PrefixCut := [⟨35,132790600,132790678⟩,
⟨64,238781825,238781963⟩]
theorem checked51817 : checkPrefixCuts (2^48) 6795689985 10 Manual.Count131072.C051817.packed 64 cuts51817 = true := by
 decide +kernel
def pointBounds51817 : List (Nat × Nat × Nat) := [(6795761664,112100909010700,112101296385296)]
theorem point_links_checked51817 : (cuts51817.take 1).map (fun c => (6795689985-1+2*2^10*c.k,112100776220100+c.lower,112101163594618+c.upper)) = pointBounds51817 := by
 decide +kernel
def cuts51818 : List PrefixCut := [⟨64,241800741,241800877⟩]
theorem checked51818 : checkPrefixCuts (2^48) 6795821057 10 Manual.Count131072.C051818.packed 64 cuts51818 = true := by
 decide +kernel
def cuts51819 : List PrefixCut := [⟨11,39885489,39885512⟩,
⟨64,237612880,237613016⟩]
theorem checked51819 : checkPrefixCuts (2^48) 6795952129 10 Manual.Count131072.C051819.packed 64 cuts51819 = true := by
 decide +kernel
def pointBounds51819 : List (Nat × Nat × Nat) := [(6795974656,112101296688155,112101684062970)]
theorem point_links_checked51819 : (cuts51819.take 1).map (fun c => (6795952129-1+2*2^10*c.k,112101256802666+c.lower,112101644177458+c.upper)) = pointBounds51819 := by
 decide +kernel
def cuts51820 : List PrefixCut := [⟨51,192381527,192381636⟩,
⟨64,238726598,238726734⟩]
theorem checked51820 : checkPrefixCuts (2^48) 6796083201 10 Manual.Count131072.C051820.packed 64 cuts51820 = true := by
 decide +kernel
def pointBounds51820 : List (Nat × Nat × Nat) := [(6796187648,112101686797073,112102074172110)]
theorem point_links_checked51820 : (cuts51820.take 1).map (fun c => (6796083201-1+2*2^10*c.k,112101494415546+c.lower,112101881790474+c.upper)) = pointBounds51820 := by
 decide +kernel
def cuts51821 : List PrefixCut := [⟨64,240751340,240751476⟩]
theorem checked51821 : checkPrefixCuts (2^48) 6796214273 10 Manual.Count131072.C051821.packed 64 cuts51821 = true := by
 decide +kernel
def cuts51822 : List PrefixCut := [⟨27,99687005,99687063⟩,
⟨64,237640556,237640694⟩]
theorem checked51822 : checkPrefixCuts (2^48) 6796345345 10 Manual.Count131072.C051822.packed 64 cuts51822 = true := by
 decide +kernel
def pointBounds51822 : List (Nat × Nat × Nat) := [(6796400640,112102073580489,112102460955747)]
theorem point_links_checked51822 : (cuts51822.take 1).map (fun c => (6796345345-1+2*2^10*c.k,112101973893484+c.lower,112102361268684+c.upper)) = pointBounds51822 := by
 decide +kernel
def cuts51823 : List PrefixCut := [⟨64,236352141,236352277⟩]
theorem checked51823 : checkPrefixCuts (2^48) 6796476417 10 Manual.Count131072.C051823.packed 64 cuts51823 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000056
