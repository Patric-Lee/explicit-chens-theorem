import PlattAssemblyKernel
import PlattCertificates.Count131072.C071856
import PlattCertificates.Count131072.C071857
import PlattCertificates.Count131072.C071858
import PlattCertificates.Count131072.C071859
import PlattCertificates.Count131072.C071860
import PlattCertificates.Count131072.C071861
import PlattCertificates.Count131072.C071862
import PlattCertificates.Count131072.C071863
import PlattCertificates.Count131072.C071864
import PlattCertificates.Count131072.C071865
import PlattCertificates.Count131072.C071866
import PlattCertificates.Count131072.C071867
import PlattCertificates.Count131072.C071868
import PlattCertificates.Count131072.C071869
import PlattCertificates.Count131072.C071870
import PlattCertificates.Count131072.C071871
import PlattCertificates.Count131072.C071872
import PlattCertificates.Count131072.C071873
import PlattCertificates.Count131072.C071874
import PlattCertificates.Count131072.C071875
import PlattCertificates.Count131072.C071876
import PlattCertificates.Count131072.C071877
import PlattCertificates.Count131072.C071878
import PlattCertificates.Count131072.C071879
import PlattCertificates.Count131072.C071880
import PlattCertificates.Count131072.C071881
import PlattCertificates.Count131072.C071882
import PlattCertificates.Count131072.C071883
import PlattCertificates.Count131072.C071884
import PlattCertificates.Count131072.C071885
import PlattCertificates.Count131072.C071886
import PlattCertificates.Count131072.C071887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71856 : List PrefixCut := [⟨64,170606099,170606200⟩]
theorem checked71856 : checkPrefixCuts (2^48) 9422241793 10 Manual.Count131072.C071856.packed 64 cuts71856 = true := by
 decide +kernel
def cuts71857 : List PrefixCut := [⟨46,123225661,123225735⟩,
⟨64,171559656,171559759⟩]
theorem checked71857 : checkPrefixCuts (2^48) 9422372865 10 Manual.Count131072.C071857.packed 64 cuts71857 = true := by
 decide +kernel
def pointBounds71857 : List (Nat × Nat × Nat) := [(9422467072,116134829224329,116135218919166)]
theorem point_links_checked71857 : (cuts71857.take 1).map (fun c => (9422372865-1+2*2^10*c.k,116134705998668+c.lower,116135095693431+c.upper)) = pointBounds71857 := by
 decide +kernel
def cuts71858 : List PrefixCut := [⟨64,169645441,169645540⟩]
theorem checked71858 : checkPrefixCuts (2^48) 9422503937 10 Manual.Count131072.C071858.packed 64 cuts71858 = true := by
 decide +kernel
def cuts71859 : List PrefixCut := [⟨62,165371423,165371518⟩,
⟨64,171226295,171226393⟩]
theorem checked71859 : checkPrefixCuts (2^48) 9422635009 10 Manual.Count131072.C071859.packed 64 cuts71859 = true := by
 decide +kernel
def pointBounds71859 : List (Nat × Nat × Nat) := [(9422761984,116135212575188,116135602270248)]
theorem point_links_checked71859 : (cuts71859.take 1).map (fun c => (9422635009-1+2*2^10*c.k,116135047203765+c.lower,116135436898730+c.upper)) = pointBounds71859 := by
 decide +kernel
def cuts71860 : List PrefixCut := [⟨64,170895315,170895419⟩]
theorem checked71860 : checkPrefixCuts (2^48) 9422766081 10 Manual.Count131072.C071860.packed 64 cuts71860 = true := by
 decide +kernel
def cuts71861 : List PrefixCut := [⟨64,170863084,170863179⟩]
theorem checked71861 : checkPrefixCuts (2^48) 9422897153 10 Manual.Count131072.C071861.packed 64 cuts71861 = true := by
 decide +kernel
def cuts71862 : List PrefixCut := [⟨14,36860708,36860729⟩,
⟨64,167246331,167246433⟩]
theorem checked71862 : checkPrefixCuts (2^48) 9423028225 10 Manual.Count131072.C071862.packed 64 cuts71862 = true := by
 decide +kernel
def pointBounds71862 : List (Nat × Nat × Nat) := [(9423056896,116135597049167,116135986744450)]
theorem point_links_checked71862 : (cuts71862.take 1).map (fun c => (9423028225-1+2*2^10*c.k,116135560188459+c.lower,116135949883721+c.upper)) = pointBounds71862 := by
 decide +kernel
def cuts71863 : List PrefixCut := [⟨64,171425857,171425966⟩]
theorem checked71863 : checkPrefixCuts (2^48) 9423159297 10 Manual.Count131072.C071863.packed 64 cuts71863 = true := by
 decide +kernel
def cuts71864 : List PrefixCut := [⟨30,81007528,81007572⟩,
⟨64,173633849,173633948⟩]
theorem checked71864 : checkPrefixCuts (2^48) 9423290369 10 Manual.Count131072.C071864.packed 64 cuts71864 = true := by
 decide +kernel
def pointBounds71864 : List (Nat × Nat × Nat) := [(9423351808,116135979868175,116136369563692)]
theorem point_links_checked71864 : (cuts71864.take 1).map (fun c => (9423290369-1+2*2^10*c.k,116135898860647+c.lower,116136288556120+c.upper)) = pointBounds71864 := by
 decide +kernel
def cuts71865 : List PrefixCut := [⟨64,170435401,170435503⟩]
theorem checked71865 : checkPrefixCuts (2^48) 9423421441 10 Manual.Count131072.C071865.packed 64 cuts71865 = true := by
 decide +kernel
def cuts71866 : List PrefixCut := [⟨46,121418091,121418159⟩,
⟨64,168820100,168820195⟩]
theorem checked71866 : checkPrefixCuts (2^48) 9423552513 10 Manual.Count131072.C071866.packed 64 cuts71866 = true := by
 decide +kernel
def pointBounds71866 : List (Nat × Nat × Nat) := [(9423646720,116136364347988,116136754043730)]
theorem point_links_checked71866 : (cuts71866.take 1).map (fun c => (9423552513-1+2*2^10*c.k,116136242929897+c.lower,116136632625571+c.upper)) = pointBounds71866 := by
 decide +kernel
def cuts71867 : List PrefixCut := [⟨64,171177372,171177477⟩]
theorem checked71867 : checkPrefixCuts (2^48) 9423683585 10 Manual.Count131072.C071867.packed 64 cuts71867 = true := by
 decide +kernel
def cuts71868 : List PrefixCut := [⟨62,163080732,163080833⟩,
⟨64,168606323,168606427⟩]
theorem checked71868 : checkPrefixCuts (2^48) 9423814657 10 Manual.Count131072.C071868.packed 64 cuts71868 = true := by
 decide +kernel
def pointBounds71868 : List (Nat × Nat × Nat) := [(9423941632,116136746008101,116137135704076)]
theorem point_links_checked71868 : (cuts71868.take 1).map (fun c => (9423814657-1+2*2^10*c.k,116136582927369+c.lower,116136972623243+c.upper)) = pointBounds71868 := by
 decide +kernel
def cuts71869 : List PrefixCut := [⟨64,170784327,170784423⟩]
theorem checked71869 : checkPrefixCuts (2^48) 9423945729 10 Manual.Count131072.C071869.packed 64 cuts71869 = true := by
 decide +kernel
def cuts71870 : List PrefixCut := [⟨64,170065150,170065245⟩]
theorem checked71870 : checkPrefixCuts (2^48) 9424076801 10 Manual.Count131072.C071870.packed 64 cuts71870 = true := by
 decide +kernel
def cuts71871 : List PrefixCut := [⟨14,37513172,37513194⟩,
⟨64,173049476,173049572⟩]
theorem checked71871 : checkPrefixCuts (2^48) 9424207873 10 Manual.Count131072.C071871.packed 64 cuts71871 = true := by
 decide +kernel
def pointBounds71871 : List (Nat × Nat × Nat) := [(9424236544,116137129896341,116137519592532)]
theorem point_links_checked71871 : (cuts71871.take 1).map (fun c => (9424207873-1+2*2^10*c.k,116137092383169+c.lower,116137482079338+c.upper)) = pointBounds71871 := by
 decide +kernel
def cuts71872 : List PrefixCut := [⟨64,170478527,170478630⟩]
theorem checked71872 : checkPrefixCuts (2^48) 9424338945 10 Manual.Count131072.C071872.packed 64 cuts71872 = true := by
 decide +kernel
def cuts71873 : List PrefixCut := [⟨30,80250726,80250774⟩,
⟨64,171372151,171372256⟩]
theorem checked71873 : checkPrefixCuts (2^48) 9424470017 10 Manual.Count131072.C071873.packed 64 cuts71873 = true := by
 decide +kernel
def pointBounds71873 : List (Nat × Nat × Nat) := [(9424531456,116137516161898,116137905858314)]
theorem point_links_checked71873 : (cuts71873.take 1).map (fun c => (9424470017-1+2*2^10*c.k,116137435911172+c.lower,116137825607540+c.upper)) = pointBounds71873 := by
 decide +kernel
def cuts71874 : List PrefixCut := [⟨64,172056681,172056776⟩]
theorem checked71874 : checkPrefixCuts (2^48) 9424601089 10 Manual.Count131072.C071874.packed 64 cuts71874 = true := by
 decide +kernel
def cuts71875 : List PrefixCut := [⟨46,122597503,122597574⟩,
⟨64,170292233,170292333⟩]
theorem checked71875 : checkPrefixCuts (2^48) 9424732161 10 Manual.Count131072.C071875.packed 64 cuts71875 = true := by
 decide +kernel
def pointBounds71875 : List (Nat × Nat × Nat) := [(9424826368,116137901937507,116138291634146)]
theorem point_links_checked71875 : (cuts71875.take 1).map (fun c => (9424732161-1+2*2^10*c.k,116137779340004+c.lower,116138169036572+c.upper)) = pointBounds71875 := by
 decide +kernel
def cuts71876 : List PrefixCut := [⟨64,169453649,169453753⟩]
theorem checked71876 : checkPrefixCuts (2^48) 9424863233 10 Manual.Count131072.C071876.packed 64 cuts71876 = true := by
 decide +kernel
def cuts71877 : List PrefixCut := [⟨62,163000596,163000692⟩,
⟨64,168226852,168226951⟩]
theorem checked71877 : checkPrefixCuts (2^48) 9424994305 10 Manual.Count131072.C071877.packed 64 cuts71877 = true := by
 decide +kernel
def pointBounds71877 : List (Nat × Nat × Nat) := [(9425121280,116138282086482,116138671783350)]
theorem point_links_checked71877 : (cuts71877.take 1).map (fun c => (9424994305-1+2*2^10*c.k,116138119085886+c.lower,116138508782658+c.upper)) = pointBounds71877 := by
 decide +kernel
def cuts71878 : List PrefixCut := [⟨64,171927660,171927756⟩]
theorem checked71878 : checkPrefixCuts (2^48) 9425125377 10 Manual.Count131072.C071878.packed 64 cuts71878 = true := by
 decide +kernel
def cuts71879 : List PrefixCut := [⟨64,170760589,170760697⟩]
theorem checked71879 : checkPrefixCuts (2^48) 9425256449 10 Manual.Count131072.C071879.packed 64 cuts71879 = true := by
 decide +kernel
def cuts71880 : List PrefixCut := [⟨14,38613425,38613446⟩,
⟨64,172848636,172848742⟩]
theorem checked71880 : checkPrefixCuts (2^48) 9425387521 10 Manual.Count131072.C071880.packed 64 cuts71880 = true := by
 decide +kernel
def pointBounds71880 : List (Nat × Nat × Nat) := [(9425416192,116138668614412,116139058311508)]
theorem point_links_checked71880 : (cuts71880.take 1).map (fun c => (9425387521-1+2*2^10*c.k,116138630000987+c.lower,116139019698062+c.upper)) = pointBounds71880 := by
 decide +kernel
def cuts71881 : List PrefixCut := [⟨64,170905146,170905247⟩]
theorem checked71881 : checkPrefixCuts (2^48) 9425518593 10 Manual.Count131072.C071881.packed 64 cuts71881 = true := by
 decide +kernel
def cuts71882 : List PrefixCut := [⟨30,80778211,80778260⟩,
⟨64,171171538,171171643⟩]
theorem checked71882 : checkPrefixCuts (2^48) 9425649665 10 Manual.Count131072.C071882.packed 64 cuts71882 = true := by
 decide +kernel
def pointBounds71882 : List (Nat × Nat × Nat) := [(9425711104,116139054532980,116139444230311)]
theorem point_links_checked71882 : (cuts71882.take 1).map (fun c => (9425649665-1+2*2^10*c.k,116138973754769+c.lower,116139363452051+c.upper)) = pointBounds71882 := by
 decide +kernel
def cuts71883 : List PrefixCut := [⟨64,170989973,170990077⟩]
theorem checked71883 : checkPrefixCuts (2^48) 9425780737 10 Manual.Count131072.C071883.packed 64 cuts71883 = true := by
 decide +kernel
def cuts71884 : List PrefixCut := [⟨46,124254424,124254503⟩,
⟨64,171704295,171704398⟩]
theorem checked71884 : checkPrefixCuts (2^48) 9425911809 10 Manual.Count131072.C071884.packed 64 cuts71884 = true := by
 decide +kernel
def pointBounds71884 : List (Nat × Nat × Nat) := [(9426006016,116139440170704,116139829868274)]
theorem point_links_checked71884 : (cuts71884.take 1).map (fun c => (9425911809-1+2*2^10*c.k,116139315916280+c.lower,116139705613771+c.upper)) = pointBounds71884 := by
 decide +kernel
def cuts71885 : List PrefixCut := [⟨64,170208836,170208939⟩]
theorem checked71885 : checkPrefixCuts (2^48) 9426042881 10 Manual.Count131072.C071885.packed 64 cuts71885 = true := by
 decide +kernel
def cuts71886 : List PrefixCut := [⟨62,165189881,165189983⟩,
⟨64,170475204,170475309⟩]
theorem checked71886 : checkPrefixCuts (2^48) 9426173953 10 Manual.Count131072.C071886.packed 64 cuts71886 = true := by
 decide +kernel
def pointBounds71886 : List (Nat × Nat × Nat) := [(9426300928,116139823019292,116140212717091)]
theorem point_links_checked71886 : (cuts71886.take 1).map (fun c => (9426173953-1+2*2^10*c.k,116139657829411+c.lower,116140047527108+c.upper)) = pointBounds71886 := by
 decide +kernel
def cuts71887 : List PrefixCut := [⟨64,167815272,167815376⟩]
theorem checked71887 : checkPrefixCuts (2^48) 9426305025 10 Manual.Count131072.C071887.packed 64 cuts71887 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000058
