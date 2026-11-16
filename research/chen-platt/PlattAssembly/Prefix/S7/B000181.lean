import PlattAssemblyKernel
import PlattCertificates.Count131072.C065792
import PlattCertificates.Count131072.C065793
import PlattCertificates.Count131072.C065794
import PlattCertificates.Count131072.C065795
import PlattCertificates.Count131072.C065796
import PlattCertificates.Count131072.C065797
import PlattCertificates.Count131072.C065798
import PlattCertificates.Count131072.C065799
import PlattCertificates.Count131072.C065800
import PlattCertificates.Count131072.C065801
import PlattCertificates.Count131072.C065802
import PlattCertificates.Count131072.C065803
import PlattCertificates.Count131072.C065804
import PlattCertificates.Count131072.C065805
import PlattCertificates.Count131072.C065806
import PlattCertificates.Count131072.C065807
import PlattCertificates.Count131072.C065808
import PlattCertificates.Count131072.C065809
import PlattCertificates.Count131072.C065810
import PlattCertificates.Count131072.C065811
import PlattCertificates.Count131072.C065812
import PlattCertificates.Count131072.C065813
import PlattCertificates.Count131072.C065814
import PlattCertificates.Count131072.C065815
import PlattCertificates.Count131072.C065816
import PlattCertificates.Count131072.C065817
import PlattCertificates.Count131072.C065818
import PlattCertificates.Count131072.C065819
import PlattCertificates.Count131072.C065820
import PlattCertificates.Count131072.C065821
import PlattCertificates.Count131072.C065822
import PlattCertificates.Count131072.C065823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000181
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65792 : List PrefixCut := [⟨64,185442569,185442677⟩]
theorem checked65792 : checkPrefixCuts (2^48) 8627421185 10 Manual.Count131072.C065792.packed 64 cuts65792 = true := by
 decide +kernel
def cuts65793 : List PrefixCut := [⟨35,101528947,101529005⟩,
⟨64,186353253,186353357⟩]
theorem checked65793 : checkPrefixCuts (2^48) 8627552257 10 Manual.Count131072.C065793.packed 64 cuts65793 = true := by
 decide +kernel
def pointBounds65793 : List (Nat × Nat × Nat) := [(8627623936,115052683457796,115053072518404)]
theorem point_links_checked65793 : (cuts65793.take 1).map (fun c => (8627552257-1+2*2^10*c.k,115052581928849+c.lower,115052970989399+c.upper)) = pointBounds65793 := by
 decide +kernel
def cuts65794 : List PrefixCut := [⟨64,185110688,185110797⟩]
theorem checked65794 : checkPrefixCuts (2^48) 8627683329 10 Manual.Count131072.C065794.packed 64 cuts65794 = true := by
 decide +kernel
def cuts65795 : List PrefixCut := [⟨39,114118663,114118733⟩,
⟨64,187032691,187032806⟩]
theorem checked65795 : checkPrefixCuts (2^48) 8627814401 10 Manual.Count131072.C065795.packed 64 cuts65795 = true := by
 decide +kernel
def pointBounds65795 : List (Nat × Nat × Nat) := [(8627894272,115053067511453,115053456572286)]
theorem point_links_checked65795 : (cuts65795.take 1).map (fun c => (8627814401-1+2*2^10*c.k,115052953392790+c.lower,115053342453553+c.upper)) = pointBounds65795 := by
 decide +kernel
def cuts65796 : List PrefixCut := [⟨64,187812817,187812922⟩]
theorem checked65796 : checkPrefixCuts (2^48) 8627945473 10 Manual.Count131072.C065796.packed 64 cuts65796 = true := by
 decide +kernel
def cuts65797 : List PrefixCut := [⟨43,128240881,128240956⟩,
⟨64,189506348,189506458⟩]
theorem checked65797 : checkPrefixCuts (2^48) 8628076545 10 Manual.Count131072.C065797.packed 64 cuts65797 = true := by
 decide +kernel
def pointBounds65797 : List (Nat × Nat × Nat) := [(8628164608,115053456479179,115053845540237)]
theorem point_links_checked65797 : (cuts65797.take 1).map (fun c => (8628076545-1+2*2^10*c.k,115053328238298+c.lower,115053717299281+c.upper)) = pointBounds65797 := by
 decide +kernel
def cuts65798 : List PrefixCut := [⟨64,185393057,185393163⟩]
theorem checked65798 : checkPrefixCuts (2^48) 8628207617 10 Manual.Count131072.C065798.packed 64 cuts65798 = true := by
 decide +kernel
def cuts65799 : List PrefixCut := [⟨47,136783885,136783964⟩,
⟨64,186140539,186140645⟩]
theorem checked65799 : checkPrefixCuts (2^48) 8628338689 10 Manual.Count131072.C065799.packed 64 cuts65799 = true := by
 decide +kernel
def pointBounds65799 : List (Nat × Nat × Nat) := [(8628434944,115053839921588,115054228982866)]
theorem point_links_checked65799 : (cuts65799.take 1).map (fun c => (8628338689-1+2*2^10*c.k,115053703137703+c.lower,115054092198902+c.upper)) = pointBounds65799 := by
 decide +kernel
def cuts65800 : List PrefixCut := [⟨64,188877905,188878008⟩]
theorem checked65800 : checkPrefixCuts (2^48) 8628469761 10 Manual.Count131072.C065800.packed 64 cuts65800 = true := by
 decide +kernel
def cuts65801 : List PrefixCut := [⟨51,149208251,149208339⟩,
⟨64,186297994,186298105⟩]
theorem checked65801 : checkPrefixCuts (2^48) 8628600833 10 Manual.Count131072.C065801.packed 64 cuts65801 = true := by
 decide +kernel
def pointBounds65801 : List (Nat × Nat × Nat) := [(8628705280,115054227364398,115054616425894)]
theorem point_links_checked65801 : (cuts65801.take 1).map (fun c => (8628600833-1+2*2^10*c.k,115054078156147+c.lower,115054467217555+c.upper)) = pointBounds65801 := by
 decide +kernel
def cuts65802 : List PrefixCut := [⟨64,186784459,186784569⟩]
theorem checked65802 : checkPrefixCuts (2^48) 8628731905 10 Manual.Count131072.C065802.packed 64 cuts65802 = true := by
 decide +kernel
def cuts65803 : List PrefixCut := [⟨55,160066080,160066174⟩,
⟨64,185574684,185574795⟩]
theorem checked65803 : checkPrefixCuts (2^48) 8628862977 10 Manual.Count131072.C065803.packed 64 cuts65803 = true := by
 decide +kernel
def pointBounds65803 : List (Nat × Nat × Nat) := [(8628975616,115054611304680,115055000366403)]
theorem point_links_checked65803 : (cuts65803.take 1).map (fun c => (8628862977-1+2*2^10*c.k,115054451238600+c.lower,115054840300229+c.upper)) = pointBounds65803 := by
 decide +kernel
def cuts65804 : List PrefixCut := [⟨64,188801199,188801308⟩]
theorem checked65804 : checkPrefixCuts (2^48) 8628994049 10 Manual.Count131072.C065804.packed 64 cuts65804 = true := by
 decide +kernel
def cuts65805 : List PrefixCut := [⟨59,172782525,172782625⟩,
⟨64,187395700,187395809⟩]
theorem checked65805 : checkPrefixCuts (2^48) 8629125121 10 Manual.Count131072.C065805.packed 64 cuts65805 = true := by
 decide +kernel
def pointBounds65805 : List (Nat × Nat × Nat) := [(8629245952,115054998397008,115055387458957)]
theorem point_links_checked65805 : (cuts65805.take 1).map (fun c => (8629125121-1+2*2^10*c.k,115054825614483+c.lower,115055214676332+c.upper)) = pointBounds65805 := by
 decide +kernel
def cuts65806 : List PrefixCut := [⟨64,186544793,186544898⟩]
theorem checked65806 : checkPrefixCuts (2^48) 8629256193 10 Manual.Count131072.C065806.packed 64 cuts65806 = true := by
 decide +kernel
def cuts65807 : List PrefixCut := [⟨63,185465574,185465683⟩,
⟨64,188172842,188172953⟩]
theorem checked65807 : checkPrefixCuts (2^48) 8629387265 10 Manual.Count131072.C065807.packed 64 cuts65807 = true := by
 decide +kernel
def pointBounds65807 : List (Nat × Nat × Nat) := [(8629516288,115055385020550,115055774082722)]
theorem point_links_checked65807 : (cuts65807.take 1).map (fun c => (8629387265-1+2*2^10*c.k,115055199554976+c.lower,115055588617039+c.upper)) = pointBounds65807 := by
 decide +kernel
def cuts65808 : List PrefixCut := [⟨64,188528772,188528881⟩]
theorem checked65808 : checkPrefixCuts (2^48) 8629518337 10 Manual.Count131072.C065808.packed 64 cuts65808 = true := by
 decide +kernel
def cuts65809 : List PrefixCut := [⟨64,184840200,184840311⟩]
theorem checked65809 : checkPrefixCuts (2^48) 8629649409 10 Manual.Count131072.C065809.packed 64 cuts65809 = true := by
 decide +kernel
def cuts65810 : List PrefixCut := [⟨3,8741270,8741276⟩,
⟨64,187740266,187740368⟩]
theorem checked65810 : checkPrefixCuts (2^48) 8629780481 10 Manual.Count131072.C065810.packed 64 cuts65810 = true := by
 decide +kernel
def pointBounds65810 : List (Nat × Nat × Nat) := [(8629786624,115055769838060,115056158900460)]
theorem point_links_checked65810 : (cuts65810.take 1).map (fun c => (8629780481-1+2*2^10*c.k,115055761096790+c.lower,115056150159184+c.upper)) = pointBounds65810 := by
 decide +kernel
def cuts65811 : List PrefixCut := [⟨64,187280784,187280893⟩]
theorem checked65811 : checkPrefixCuts (2^48) 8629911553 10 Manual.Count131072.C065811.packed 64 cuts65811 = true := by
 decide +kernel
def cuts65812 : List PrefixCut := [⟨7,19895562,19895573⟩,
⟨64,185810235,185810345⟩]
theorem checked65812 : checkPrefixCuts (2^48) 8630042625 10 Manual.Count131072.C065812.packed 64 cuts65812 = true := by
 decide +kernel
def pointBounds65812 : List (Nat × Nat × Nat) := [(8630056960,115056156013402,115056545076018)]
theorem point_links_checked65812 : (cuts65812.take 1).map (fun c => (8630042625-1+2*2^10*c.k,115056136117840+c.lower,115056525180445+c.upper)) = pointBounds65812 := by
 decide +kernel
def cuts65813 : List PrefixCut := [⟨64,185057259,185057363⟩]
theorem checked65813 : checkPrefixCuts (2^48) 8630173697 10 Manual.Count131072.C065813.packed 64 cuts65813 = true := by
 decide +kernel
def cuts65814 : List PrefixCut := [⟨11,30820860,30820881⟩,
⟨64,187043931,187044036⟩]
theorem checked65814 : checkPrefixCuts (2^48) 8630304769 10 Manual.Count131072.C065814.packed 64 cuts65814 = true := by
 decide +kernel
def pointBounds65814 : List (Nat × Nat × Nat) := [(8630327296,115056537806194,115056926869034)]
theorem point_links_checked65814 : (cuts65814.take 1).map (fun c => (8630304769-1+2*2^10*c.k,115056506985334+c.lower,115056896048153+c.upper)) = pointBounds65814 := by
 decide +kernel
def cuts65815 : List PrefixCut := [⟨64,186323596,186323708⟩]
theorem checked65815 : checkPrefixCuts (2^48) 8630435841 10 Manual.Count131072.C065815.packed 64 cuts65815 = true := by
 decide +kernel
def cuts65816 : List PrefixCut := [⟨15,44843785,44843811⟩,
⟨64,188310194,188310304⟩]
theorem checked65816 : checkPrefixCuts (2^48) 8630566913 10 Manual.Count131072.C065816.packed 64 cuts65816 = true := by
 decide +kernel
def pointBounds65816 : List (Nat × Nat × Nat) := [(8630597632,115056925196646,115057314259708)]
theorem point_links_checked65816 : (cuts65816.take 1).map (fun c => (8630566913-1+2*2^10*c.k,115056880352861+c.lower,115057269415897+c.upper)) = pointBounds65816 := by
 decide +kernel
def cuts65817 : List PrefixCut := [⟨64,188111669,188111777⟩]
theorem checked65817 : checkPrefixCuts (2^48) 8630697985 10 Manual.Count131072.C065817.packed 64 cuts65817 = true := by
 decide +kernel
def cuts65818 : List PrefixCut := [⟨19,55213225,55213257⟩,
⟨64,186934743,186934848⟩]
theorem checked65818 : checkPrefixCuts (2^48) 8630829057 10 Manual.Count131072.C065818.packed 64 cuts65818 = true := by
 decide +kernel
def pointBounds65818 : List (Nat × Nat × Nat) := [(8630867968,115057311987949,115057701051235)]
theorem point_links_checked65818 : (cuts65818.take 1).map (fun c => (8630829057-1+2*2^10*c.k,115057256774724+c.lower,115057645837978+c.upper)) = pointBounds65818 := by
 decide +kernel
def cuts65819 : List PrefixCut := [⟨64,186279675,186279781⟩]
theorem checked65819 : checkPrefixCuts (2^48) 8630960129 10 Manual.Count131072.C065819.packed 64 cuts65819 = true := by
 decide +kernel
def cuts65820 : List PrefixCut := [⟨23,68125734,68125776⟩,
⟨64,188429197,188429309⟩]
theorem checked65820 : checkPrefixCuts (2^48) 8631091201 10 Manual.Count131072.C065820.packed 64 cuts65820 = true := by
 decide +kernel
def pointBounds65820 : List (Nat × Nat × Nat) := [(8631138304,115057698114876,115058087178383)]
theorem point_links_checked65820 : (cuts65820.take 1).map (fun c => (8631091201-1+2*2^10*c.k,115057629989142+c.lower,115058019052607+c.upper)) = pointBounds65820 := by
 decide +kernel
def cuts65821 : List PrefixCut := [⟨64,187056680,187056785⟩]
theorem checked65821 : checkPrefixCuts (2^48) 8631222273 10 Manual.Count131072.C065821.packed 64 cuts65821 = true := by
 decide +kernel
def cuts65822 : List PrefixCut := [⟨27,78493820,78493867⟩,
⟨64,187640814,187640927⟩]
theorem checked65822 : checkPrefixCuts (2^48) 8631353345 10 Manual.Count131072.C065822.packed 64 cuts65822 = true := by
 decide +kernel
def pointBounds65822 : List (Nat × Nat × Nat) := [(8631408640,115058083968839,115058473032568)]
theorem point_links_checked65822 : (cuts65822.take 1).map (fun c => (8631353345-1+2*2^10*c.k,115058005475019+c.lower,115058394538701+c.upper)) = pointBounds65822 := by
 decide +kernel
def cuts65823 : List PrefixCut := [⟨64,188485838,188485951⟩]
theorem checked65823 : checkPrefixCuts (2^48) 8631484417 10 Manual.Count131072.C065823.packed 64 cuts65823 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000181
