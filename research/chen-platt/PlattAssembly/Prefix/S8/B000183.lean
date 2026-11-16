import PlattAssemblyKernel
import PlattCertificates.Count131072.C075856
import PlattCertificates.Count131072.C075857
import PlattCertificates.Count131072.C075858
import PlattCertificates.Count131072.C075859
import PlattCertificates.Count131072.C075860
import PlattCertificates.Count131072.C075861
import PlattCertificates.Count131072.C075862
import PlattCertificates.Count131072.C075863
import PlattCertificates.Count131072.C075864
import PlattCertificates.Count131072.C075865
import PlattCertificates.Count131072.C075866
import PlattCertificates.Count131072.C075867
import PlattCertificates.Count131072.C075868
import PlattCertificates.Count131072.C075869
import PlattCertificates.Count131072.C075870
import PlattCertificates.Count131072.C075871
import PlattCertificates.Count131072.C075872
import PlattCertificates.Count131072.C075873
import PlattCertificates.Count131072.C075874
import PlattCertificates.Count131072.C075875
import PlattCertificates.Count131072.C075876
import PlattCertificates.Count131072.C075877
import PlattCertificates.Count131072.C075878
import PlattCertificates.Count131072.C075879
import PlattCertificates.Count131072.C075880
import PlattCertificates.Count131072.C075881
import PlattCertificates.Count131072.C075882
import PlattCertificates.Count131072.C075883
import PlattCertificates.Count131072.C075884
import PlattCertificates.Count131072.C075885
import PlattCertificates.Count131072.C075886
import PlattCertificates.Count131072.C075887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000183
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75856 : List PrefixCut := [⟨64,162717053,162717145⟩]
theorem checked75856 : checkPrefixCuts (2^48) 9946529793 10 Manual.Count131072.C075856.packed 64 cuts75856 = true := by
 decide +kernel
def cuts75857 : List PrefixCut := [⟨51,127115888,127115969⟩,
⟨64,159404016,159404116⟩]
theorem checked75857 : checkPrefixCuts (2^48) 9946660865 10 Manual.Count131072.C075857.packed 64 cuts75857 = true := by
 decide +kernel
def pointBounds75857 : List (Nat × Nat × Nat) := [(9946765312,116797752740923,116798142831909)]
theorem point_links_checked75857 : (cuts75857.take 1).map (fun c => (9946660865-1+2*2^10*c.k,116797625625035+c.lower,116798015715940+c.upper)) = pointBounds75857 := by
 decide +kernel
def cuts75858 : List PrefixCut := [⟨64,161297865,161297967⟩]
theorem checked75858 : checkPrefixCuts (2^48) 9946791937 10 Manual.Count131072.C075858.packed 64 cuts75858 = true := by
 decide +kernel
def cuts75859 : List PrefixCut := [⟨64,160078952,160079053⟩]
theorem checked75859 : checkPrefixCuts (2^48) 9946923009 10 Manual.Count131072.C075859.packed 64 cuts75859 = true := by
 decide +kernel
def cuts75860 : List PrefixCut := [⟨11,26344769,26344783⟩,
⟨64,161831249,161831345⟩]
theorem checked75860 : checkPrefixCuts (2^48) 9947054081 10 Manual.Count131072.C075860.packed 64 cuts75860 = true := by
 decide +kernel
def pointBounds75860 : List (Nat × Nat × Nat) := [(9947076608,116798132750637,116798522841859)]
theorem point_links_checked75860 : (cuts75860.take 1).map (fun c => (9947054081-1+2*2^10*c.k,116798106405868+c.lower,116798496497076+c.upper)) = pointBounds75860 := by
 decide +kernel
def cuts75861 : List PrefixCut := [⟨64,160216205,160216301⟩]
theorem checked75861 : checkPrefixCuts (2^48) 9947185153 10 Manual.Count131072.C075861.packed 64 cuts75861 = true := by
 decide +kernel
def cuts75862 : List PrefixCut := [⟨35,89105563,89105616⟩,
⟨64,161883587,161883685⟩]
theorem checked75862 : checkPrefixCuts (2^48) 9947316225 10 Manual.Count131072.C075862.packed 64 cuts75862 = true := by
 decide +kernel
def pointBounds75862 : List (Nat × Nat × Nat) := [(9947387904,116798517558885,116798907650338)]
theorem point_links_checked75862 : (cuts75862.take 1).map (fun c => (9947316225-1+2*2^10*c.k,116798428453322+c.lower,116798818544722+c.upper)) = pointBounds75862 := by
 decide +kernel
def cuts75863 : List PrefixCut := [⟨64,159334819,159334920⟩]
theorem checked75863 : checkPrefixCuts (2^48) 9947447297 10 Manual.Count131072.C075863.packed 64 cuts75863 = true := by
 decide +kernel
def cuts75864 : List PrefixCut := [⟨59,150136712,150136800⟩,
⟨64,162105692,162105788⟩]
theorem checked75864 : checkPrefixCuts (2^48) 9947578369 10 Manual.Count131072.C075864.packed 64 cuts75864 = true := by
 decide +kernel
def pointBounds75864 : List (Nat × Nat × Nat) := [(9947699200,116798899808440,116799289900127)]
theorem point_links_checked75864 : (cuts75864.take 1).map (fun c => (9947578369-1+2*2^10*c.k,116798749671728+c.lower,116799139763327+c.upper)) = pointBounds75864 := by
 decide +kernel
def cuts75865 : List PrefixCut := [⟨64,163857858,163857955⟩]
theorem checked75865 : checkPrefixCuts (2^48) 9947709441 10 Manual.Count131072.C075865.packed 64 cuts75865 = true := by
 decide +kernel
def cuts75866 : List PrefixCut := [⟨64,161195981,161196081⟩]
theorem checked75866 : checkPrefixCuts (2^48) 9947840513 10 Manual.Count131072.C075866.packed 64 cuts75866 = true := by
 decide +kernel
def cuts75867 : List PrefixCut := [⟨19,49034621,49034654⟩,
⟨64,162438820,162438925⟩]
theorem checked75867 : checkPrefixCuts (2^48) 9947971585 10 Manual.Count131072.C075867.packed 64 cuts75867 = true := by
 decide +kernel
def pointBounds75867 : List (Nat × Nat × Nat) := [(9948010496,116799285865880,116799675957805)]
theorem point_links_checked75867 : (cuts75867.take 1).map (fun c => (9947971585-1+2*2^10*c.k,116799236831259+c.lower,116799626923151+c.upper)) = pointBounds75867 := by
 decide +kernel
def cuts75868 : List PrefixCut := [⟨64,160908792,160908888⟩]
theorem checked75868 : checkPrefixCuts (2^48) 9948102657 10 Manual.Count131072.C075868.packed 64 cuts75868 = true := by
 decide +kernel
def cuts75869 : List PrefixCut := [⟨43,108308785,108308849⟩,
⟨64,161161315,161161410⟩]
theorem checked75869 : checkPrefixCuts (2^48) 9948233729 10 Manual.Count131072.C075869.packed 64 cuts75869 = true := by
 decide +kernel
def pointBounds75869 : List (Nat × Nat × Nat) := [(9948321792,116799668487656,116800058579813)]
theorem point_links_checked75869 : (cuts75869.take 1).map (fun c => (9948233729-1+2*2^10*c.k,116799560178871+c.lower,116799950270964+c.upper)) = pointBounds75869 := by
 decide +kernel
def cuts75870 : List PrefixCut := [⟨64,160508447,160508544⟩]
theorem checked75870 : checkPrefixCuts (2^48) 9948364801 10 Manual.Count131072.C075870.packed 64 cuts75870 = true := by
 decide +kernel
def cuts75871 : List PrefixCut := [⟨64,158214597,158214691⟩]
theorem checked75871 : checkPrefixCuts (2^48) 9948495873 10 Manual.Count131072.C075871.packed 64 cuts75871 = true := by
 decide +kernel
def cuts75872 : List PrefixCut := [⟨3,7667357,7667361⟩,
⟨64,159513978,159514072⟩]
theorem checked75872 : checkPrefixCuts (2^48) 9948626945 10 Manual.Count131072.C075872.packed 64 cuts75872 = true := by
 decide +kernel
def pointBounds75872 : List (Nat × Nat × Nat) := [(9948633088,116800047730587,116800437822970)]
theorem point_links_checked75872 : (cuts75872.take 1).map (fun c => (9948626945-1+2*2^10*c.k,116800040063230+c.lower,116800430155609+c.upper)) = pointBounds75872 := by
 decide +kernel
def cuts75873 : List PrefixCut := [⟨64,161520620,161520717⟩]
theorem checked75873 : checkPrefixCuts (2^48) 9948758017 10 Manual.Count131072.C075873.packed 64 cuts75873 = true := by
 decide +kernel
def cuts75874 : List PrefixCut := [⟨27,67391578,67391620⟩,
⟨64,160330235,160330328⟩]
theorem checked75874 : checkPrefixCuts (2^48) 9948889089 10 Manual.Count131072.C075874.packed 64 cuts75874 = true := by
 decide +kernel
def pointBounds75874 : List (Nat × Nat × Nat) := [(9948944384,116800428489406,116800818582018)]
theorem point_links_checked75874 : (cuts75874.take 1).map (fun c => (9948889089-1+2*2^10*c.k,116800361097828+c.lower,116800751190398+c.upper)) = pointBounds75874 := by
 decide +kernel
def cuts75875 : List PrefixCut := [⟨64,161488076,161488182⟩]
theorem checked75875 : checkPrefixCuts (2^48) 9949020161 10 Manual.Count131072.C075875.packed 64 cuts75875 = true := by
 decide +kernel
def cuts75876 : List PrefixCut := [⟨51,128244008,128244085⟩,
⟨64,160382600,160382695⟩]
theorem checked75876 : checkPrefixCuts (2^48) 9949151233 10 Manual.Count131072.C075876.packed 64 cuts75876 = true := by
 decide +kernel
def pointBounds75876 : List (Nat × Nat × Nat) := [(9949255680,116800811160147,116801201252993)]
theorem point_links_checked75876 : (cuts75876.take 1).map (fun c => (9949151233-1+2*2^10*c.k,116800682916139+c.lower,116801073008908+c.upper)) = pointBounds75876 := by
 decide +kernel
def cuts75877 : List PrefixCut := [⟨64,161059463,161059559⟩]
theorem checked75877 : checkPrefixCuts (2^48) 9949282305 10 Manual.Count131072.C075877.packed 64 cuts75877 = true := by
 decide +kernel
def cuts75878 : List PrefixCut := [⟨64,161764589,161764685⟩]
theorem checked75878 : checkPrefixCuts (2^48) 9949413377 10 Manual.Count131072.C075878.packed 64 cuts75878 = true := by
 decide +kernel
def cuts75879 : List PrefixCut := [⟨11,27837553,27837570⟩,
⟨64,159923609,159923702⟩]
theorem checked75879 : checkPrefixCuts (2^48) 9949544449 10 Manual.Count131072.C075879.packed 64 cuts75879 = true := by
 decide +kernel
def pointBounds75879 : List (Nat × Nat × Nat) := [(9949566976,116801193960344,116801584053417)]
theorem point_links_checked75879 : (cuts75879.take 1).map (fun c => (9949544449-1+2*2^10*c.k,116801166122791+c.lower,116801556215847+c.upper)) = pointBounds75879 := by
 decide +kernel
def cuts75880 : List PrefixCut := [⟨64,161222839,161222933⟩]
theorem checked75880 : checkPrefixCuts (2^48) 9949675521 10 Manual.Count131072.C075880.packed 64 cuts75880 = true := by
 decide +kernel
def cuts75881 : List PrefixCut := [⟨35,87753665,87753716⟩,
⟨64,159297040,159297134⟩]
theorem checked75881 : checkPrefixCuts (2^48) 9949806593 10 Manual.Count131072.C075881.packed 64 cuts75881 = true := by
 decide +kernel
def pointBounds75881 : List (Nat × Nat × Nat) := [(9949878272,116801575022904,116801965116198)]
theorem point_links_checked75881 : (cuts75881.take 1).map (fun c => (9949806593-1+2*2^10*c.k,116801487269239+c.lower,116801877362482+c.upper)) = pointBounds75881 := by
 decide +kernel
def cuts75882 : List PrefixCut := [⟨64,163255382,163255483⟩]
theorem checked75882 : checkPrefixCuts (2^48) 9949937665 10 Manual.Count131072.C075882.packed 64 cuts75882 = true := by
 decide +kernel
def cuts75883 : List PrefixCut := [⟨59,148628126,148628215⟩,
⟨64,161584204,161584301⟩]
theorem checked75883 : checkPrefixCuts (2^48) 9950068737 10 Manual.Count131072.C075883.packed 64 cuts75883 = true := by
 decide +kernel
def pointBounds75883 : List (Nat × Nat × Nat) := [(9950189568,116801958449787,116802348543314)]
theorem point_links_checked75883 : (cuts75883.take 1).map (fun c => (9950068737-1+2*2^10*c.k,116801809821661+c.lower,116802199915099+c.upper)) = pointBounds75883 := by
 decide +kernel
def cuts75884 : List PrefixCut := [⟨64,161921537,161921641⟩]
theorem checked75884 : checkPrefixCuts (2^48) 9950199809 10 Manual.Count131072.C075884.packed 64 cuts75884 = true := by
 decide +kernel
def cuts75885 : List PrefixCut := [⟨64,161919415,161919513⟩]
theorem checked75885 : checkPrefixCuts (2^48) 9950330881 10 Manual.Count131072.C075885.packed 64 cuts75885 = true := by
 decide +kernel
def cuts75886 : List PrefixCut := [⟨19,47494823,47494850⟩,
⟨64,162369878,162369968⟩]
theorem checked75886 : checkPrefixCuts (2^48) 9950461953 10 Manual.Count131072.C075886.packed 64 cuts75886 = true := by
 decide +kernel
def pointBounds75886 : List (Nat × Nat × Nat) := [(9950500864,116802342741640,116802732835404)]
theorem point_links_checked75886 : (cuts75886.take 1).map (fun c => (9950461953-1+2*2^10*c.k,116802295246817+c.lower,116802685340554+c.upper)) = pointBounds75886 := by
 decide +kernel
def cuts75887 : List PrefixCut := [⟨64,160670505,160670601⟩]
theorem checked75887 : checkPrefixCuts (2^48) 9950593025 10 Manual.Count131072.C075887.packed 64 cuts75887 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000183
