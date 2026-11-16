import PlattAssemblyKernel
import PlattCertificates.Count131072.C074800
import PlattCertificates.Count131072.C074801
import PlattCertificates.Count131072.C074802
import PlattCertificates.Count131072.C074803
import PlattCertificates.Count131072.C074804
import PlattCertificates.Count131072.C074805
import PlattCertificates.Count131072.C074806
import PlattCertificates.Count131072.C074807
import PlattCertificates.Count131072.C074808
import PlattCertificates.Count131072.C074809
import PlattCertificates.Count131072.C074810
import PlattCertificates.Count131072.C074811
import PlattCertificates.Count131072.C074812
import PlattCertificates.Count131072.C074813
import PlattCertificates.Count131072.C074814
import PlattCertificates.Count131072.C074815
import PlattCertificates.Count131072.C074816
import PlattCertificates.Count131072.C074817
import PlattCertificates.Count131072.C074818
import PlattCertificates.Count131072.C074819
import PlattCertificates.Count131072.C074820
import PlattCertificates.Count131072.C074821
import PlattCertificates.Count131072.C074822
import PlattCertificates.Count131072.C074823
import PlattCertificates.Count131072.C074824
import PlattCertificates.Count131072.C074825
import PlattCertificates.Count131072.C074826
import PlattCertificates.Count131072.C074827
import PlattCertificates.Count131072.C074828
import PlattCertificates.Count131072.C074829
import PlattCertificates.Count131072.C074830
import PlattCertificates.Count131072.C074831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74800 : List PrefixCut := [⟨64,163119223,163119327⟩]
theorem checked74800 : checkPrefixCuts (2^48) 9808117761 10 Manual.Count131072.C074800.packed 64 cuts74800 = true := by
 decide +kernel
def cuts74801 : List PrefixCut := [⟨47,119841305,119841383⟩,
⟨64,163030953,163031053⟩]
theorem checked74801 : checkPrefixCuts (2^48) 9808248833 10 Manual.Count131072.C074801.packed 64 cuts74801 = true := by
 decide +kernel
def pointBounds74801 : List (Nat × Nat × Nat) := [(9808345088,116626362486244,116626752474221)]
theorem point_links_checked74801 : (cuts74801.take 1).map (fun c => (9808248833-1+2*2^10*c.k,116626242644939+c.lower,116626632632838+c.upper)) = pointBounds74801 := by
 decide +kernel
def cuts74802 : List PrefixCut := [⟨64,164234062,164234164⟩]
theorem checked74802 : checkPrefixCuts (2^48) 9808379905 10 Manual.Count131072.C074802.packed 64 cuts74802 = true := by
 decide +kernel
def cuts74803 : List PrefixCut := [⟨64,165236256,165236352⟩]
theorem checked74803 : checkPrefixCuts (2^48) 9808510977 10 Manual.Count131072.C074803.packed 64 cuts74803 = true := by
 decide +kernel
def cuts74804 : List PrefixCut := [⟨5,12282148,12282156⟩,
⟨64,162249614,162249715⟩]
theorem checked74804 : checkPrefixCuts (2^48) 9808642049 10 Manual.Count131072.C074804.packed 64 cuts74804 = true := by
 decide +kernel
def pointBounds74804 : List (Nat × Nat × Nat) := [(9808652288,116626747428358,116627137416563)]
theorem point_links_checked74804 : (cuts74804.take 1).map (fun c => (9808642049-1+2*2^10*c.k,116626735146210+c.lower,116627125134407+c.upper)) = pointBounds74804 := by
 decide +kernel
def cuts74805 : List PrefixCut := [⟨64,163883119,163883220⟩]
theorem checked74805 : checkPrefixCuts (2^48) 9808773121 10 Manual.Count131072.C074805.packed 64 cuts74805 = true := by
 decide +kernel
def cuts74806 : List PrefixCut := [⟨27,69759427,69759471⟩,
⟨64,163794846,163794949⟩]
theorem checked74806 : checkPrefixCuts (2^48) 9808904193 10 Manual.Count131072.C074806.packed 64 cuts74806 = true := by
 decide +kernel
def pointBounds74806 : List (Nat × Nat × Nat) := [(9808959488,116627131038370,116627521026813)]
theorem point_links_checked74806 : (cuts74806.take 1).map (fun c => (9808904193-1+2*2^10*c.k,116627061278943+c.lower,116627451267342+c.upper)) = pointBounds74806 := by
 decide +kernel
def cuts74807 : List PrefixCut := [⟨64,160722280,160722375⟩]
theorem checked74807 : checkPrefixCuts (2^48) 9809035265 10 Manual.Count131072.C074807.packed 64 cuts74807 = true := by
 decide +kernel
def cuts74808 : List PrefixCut := [⟨49,123904762,123904836⟩,
⟨64,162068778,162068876⟩]
theorem checked74808 : checkPrefixCuts (2^48) 9809166337 10 Manual.Count131072.C074808.packed 64 cuts74808 = true := by
 decide +kernel
def pointBounds74808 : List (Nat × Nat × Nat) := [(9809266688,116627509700831,116627899689502)]
theorem point_links_checked74808 : (cuts74808.take 1).map (fun c => (9809166337-1+2*2^10*c.k,116627385796069+c.lower,116627775784666+c.upper)) = pointBounds74808 := by
 decide +kernel
def cuts74809 : List PrefixCut := [⟨64,162353562,162353663⟩]
theorem checked74809 : checkPrefixCuts (2^48) 9809297409 10 Manual.Count131072.C074809.packed 64 cuts74809 = true := by
 decide +kernel
def cuts74810 : List PrefixCut := [⟨64,165077315,165077414⟩]
theorem checked74810 : checkPrefixCuts (2^48) 9809428481 10 Manual.Count131072.C074810.packed 64 cuts74810 = true := by
 decide +kernel
def cuts74811 : List PrefixCut := [⟨7,17905004,17905015⟩,
⟨64,162234444,162234544⟩]
theorem checked74811 : checkPrefixCuts (2^48) 9809559553 10 Manual.Count131072.C074811.packed 64 cuts74811 = true := by
 decide +kernel
def pointBounds74811 : List (Nat × Nat × Nat) := [(9809573888,116627893200728,116628283189634)]
theorem point_links_checked74811 : (cuts74811.take 1).map (fun c => (9809559553-1+2*2^10*c.k,116627875295724+c.lower,116628265284619+c.upper)) = pointBounds74811 := by
 decide +kernel
def cuts74812 : List PrefixCut := [⟨64,164412958,164413053⟩]
theorem checked74812 : checkPrefixCuts (2^48) 9809690625 10 Manual.Count131072.C074812.packed 64 cuts74812 = true := by
 decide +kernel
def cuts74813 : List PrefixCut := [⟨29,72995210,72995250⟩,
⟨64,163463903,163463997⟩]
theorem checked74813 : checkPrefixCuts (2^48) 9809821697 10 Manual.Count131072.C074813.packed 64 cuts74813 = true := by
 decide +kernel
def pointBounds74813 : List (Nat × Nat × Nat) := [(9809881088,116628274938336,116628664927466)]
theorem point_links_checked74813 : (cuts74813.take 1).map (fun c => (9809821697-1+2*2^10*c.k,116628201943126+c.lower,116628591932216+c.upper)) = pointBounds74813 := by
 decide +kernel
def cuts74814 : List PrefixCut := [⟨64,164006871,164006967⟩]
theorem checked74814 : checkPrefixCuts (2^48) 9809952769 10 Manual.Count131072.C074814.packed 64 cuts74814 = true := by
 decide +kernel
def cuts74815 : List PrefixCut := [⟨51,129717664,129717746⟩,
⟨64,162283153,162283253⟩]
theorem checked74815 : checkPrefixCuts (2^48) 9810083841 10 Manual.Count131072.C074815.packed 64 cuts74815 = true := by
 decide +kernel
def pointBounds74815 : List (Nat × Nat × Nat) := [(9810188288,116628659131564,116629049120926)]
theorem point_links_checked74815 : (cuts74815.take 1).map (fun c => (9810083841-1+2*2^10*c.k,116628529413900+c.lower,116628919403180+c.upper)) = pointBounds74815 := by
 decide +kernel
def cuts74816 : List PrefixCut := [⟨64,164174641,164174741⟩]
theorem checked74816 : checkPrefixCuts (2^48) 9810214913 10 Manual.Count131072.C074816.packed 64 cuts74816 = true := by
 decide +kernel
def cuts74817 : List PrefixCut := [⟨64,162307505,162307608⟩]
theorem checked74817 : checkPrefixCuts (2^48) 9810345985 10 Manual.Count131072.C074817.packed 64 cuts74817 = true := by
 decide +kernel
def cuts74818 : List PrefixCut := [⟨9,23412043,23412056⟩,
⟨64,164084194,164084291⟩]
theorem checked74818 : checkPrefixCuts (2^48) 9810477057 10 Manual.Count131072.C074818.packed 64 cuts74818 = true := by
 decide +kernel
def pointBounds74818 : List (Nat × Nat × Nat) := [(9810495488,116629041591242,116629431580838)]
theorem point_links_checked74818 : (cuts74818.take 1).map (fun c => (9810477057-1+2*2^10*c.k,116629018179199+c.lower,116629408168782+c.upper)) = pointBounds74818 := by
 decide +kernel
def cuts74819 : List PrefixCut := [⟨64,166578074,166578175⟩]
theorem checked74819 : checkPrefixCuts (2^48) 9810608129 10 Manual.Count131072.C074819.packed 64 cuts74819 = true := by
 decide +kernel
def cuts74820 : List PrefixCut := [⟨31,76804184,76804234⟩,
⟨64,160665649,160665748⟩]
theorem checked74820 : checkPrefixCuts (2^48) 9810739201 10 Manual.Count131072.C074820.packed 64 cuts74820 = true := by
 decide +kernel
def pointBounds74820 : List (Nat × Nat × Nat) := [(9810802688,116629425645651,116629815635482)]
theorem point_links_checked74820 : (cuts74820.take 1).map (fun c => (9810739201-1+2*2^10*c.k,116629348841467+c.lower,116629738831248+c.upper)) = pointBounds74820 := by
 decide +kernel
def cuts74821 : List PrefixCut := [⟨64,163274303,163274394⟩]
theorem checked74821 : checkPrefixCuts (2^48) 9810870273 10 Manual.Count131072.C074821.packed 64 cuts74821 = true := by
 decide +kernel
def cuts74822 : List PrefixCut := [⟨53,135759006,135759089⟩,
⟨64,163214734,163214833⟩]
theorem checked74822 : checkPrefixCuts (2^48) 9811001345 10 Manual.Count131072.C074822.packed 64 cuts74822 = true := by
 decide +kernel
def pointBounds74822 : List (Nat × Nat × Nat) := [(9811109888,116629808540425,116630198530479)]
theorem point_links_checked74822 : (cuts74822.take 1).map (fun c => (9811001345-1+2*2^10*c.k,116629672781419+c.lower,116630062771390+c.upper)) = pointBounds74822 := by
 decide +kernel
def cuts74823 : List PrefixCut := [⟨64,162007615,162007707⟩]
theorem checked74823 : checkPrefixCuts (2^48) 9811132417 10 Manual.Count131072.C074823.packed 64 cuts74823 = true := by
 decide +kernel
def cuts74824 : List PrefixCut := [⟨64,164587427,164587527⟩]
theorem checked74824 : checkPrefixCuts (2^48) 9811263489 10 Manual.Count131072.C074824.packed 64 cuts74824 = true := by
 decide +kernel
def cuts74825 : List PrefixCut := [⟨11,26852471,26852488⟩,
⟨64,160626231,160626329⟩]
theorem checked74825 : checkPrefixCuts (2^48) 9811394561 10 Manual.Count131072.C074825.packed 64 cuts74825 = true := by
 decide +kernel
def pointBounds74825 : List (Nat × Nat × Nat) := [(9811417088,116630189443666,116630579433945)]
theorem point_links_checked74825 : (cuts74825.take 1).map (fun c => (9811394561-1+2*2^10*c.k,116630162591195+c.lower,116630552581457+c.upper)) = pointBounds74825 := by
 decide +kernel
def cuts74826 : List PrefixCut := [⟨64,165300244,165300344⟩]
theorem checked74826 : checkPrefixCuts (2^48) 9811525633 10 Manual.Count131072.C074826.packed 64 cuts74826 = true := by
 decide +kernel
def cuts74827 : List PrefixCut := [⟨33,85833620,85833667⟩,
⟨64,165527537,165527633⟩]
theorem checked74827 : checkPrefixCuts (2^48) 9811656705 10 Manual.Count131072.C074827.packed 64 cuts74827 = true := by
 decide +kernel
def pointBounds74827 : List (Nat × Nat × Nat) := [(9811724288,116630574351290,116630964341797)]
theorem point_links_checked74827 : (cuts74827.take 1).map (fun c => (9811656705-1+2*2^10*c.k,116630488517670+c.lower,116630878508130+c.upper)) = pointBounds74827 := by
 decide +kernel
def cuts74828 : List PrefixCut := [⟨64,164406512,164406611⟩]
theorem checked74828 : checkPrefixCuts (2^48) 9811787777 10 Manual.Count131072.C074828.packed 64 cuts74828 = true := by
 decide +kernel
def cuts74829 : List PrefixCut := [⟨55,139905884,139905971⟩,
⟨64,163830576,163830678⟩]
theorem checked74829 : checkPrefixCuts (2^48) 9811918849 10 Manual.Count131072.C074829.packed 64 cuts74829 = true := by
 decide +kernel
def pointBounds74829 : List (Nat × Nat × Nat) := [(9812031488,116630958357603,116631348348345)]
theorem point_links_checked74829 : (cuts74829.take 1).map (fun c => (9811918849-1+2*2^10*c.k,116630818451719+c.lower,116631208442374+c.upper)) = pointBounds74829 := by
 decide +kernel
def cuts74830 : List PrefixCut := [⟨64,161476105,161476202⟩]
theorem checked74830 : checkPrefixCuts (2^48) 9812049921 10 Manual.Count131072.C074830.packed 64 cuts74830 = true := by
 decide +kernel
def cuts74831 : List PrefixCut := [⟨64,164572043,164572140⟩]
theorem checked74831 : checkPrefixCuts (2^48) 9812180993 10 Manual.Count131072.C074831.packed 64 cuts74831 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000150
