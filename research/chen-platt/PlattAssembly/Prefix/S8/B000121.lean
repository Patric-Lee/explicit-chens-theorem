import PlattAssemblyKernel
import PlattCertificates.Count131072.C073872
import PlattCertificates.Count131072.C073873
import PlattCertificates.Count131072.C073874
import PlattCertificates.Count131072.C073875
import PlattCertificates.Count131072.C073876
import PlattCertificates.Count131072.C073877
import PlattCertificates.Count131072.C073878
import PlattCertificates.Count131072.C073879
import PlattCertificates.Count131072.C073880
import PlattCertificates.Count131072.C073881
import PlattCertificates.Count131072.C073882
import PlattCertificates.Count131072.C073883
import PlattCertificates.Count131072.C073884
import PlattCertificates.Count131072.C073885
import PlattCertificates.Count131072.C073886
import PlattCertificates.Count131072.C073887
import PlattCertificates.Count131072.C073888
import PlattCertificates.Count131072.C073889
import PlattCertificates.Count131072.C073890
import PlattCertificates.Count131072.C073891
import PlattCertificates.Count131072.C073892
import PlattCertificates.Count131072.C073893
import PlattCertificates.Count131072.C073894
import PlattCertificates.Count131072.C073895
import PlattCertificates.Count131072.C073896
import PlattCertificates.Count131072.C073897
import PlattCertificates.Count131072.C073898
import PlattCertificates.Count131072.C073899
import PlattCertificates.Count131072.C073900
import PlattCertificates.Count131072.C073901
import PlattCertificates.Count131072.C073902
import PlattCertificates.Count131072.C073903
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000121
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73872 : List PrefixCut := [⟨64,163104396,163104497⟩]
theorem checked73872 : checkPrefixCuts (2^48) 9686482945 10 Manual.Count131072.C073872.packed 64 cuts73872 = true := by
 decide +kernel
def cuts73873 : List PrefixCut := [⟨38,98564788,98564844⟩,
⟨64,166066098,166066190⟩]
theorem checked73873 : checkPrefixCuts (2^48) 9686614017 10 Manual.Count131072.C073873.packed 64 cuts73873 = true := by
 decide +kernel
def pointBounds73873 : List (Nat × Nat × Nat) := [(9686691840,116473601013035,116473990909677)]
theorem point_links_checked73873 : (cuts73873.take 1).map (fun c => (9686614017-1+2*2^10*c.k,116473502448247+c.lower,116473892344833+c.upper)) = pointBounds73873 := by
 decide +kernel
def cuts73874 : List PrefixCut := [⟨64,163826424,163826516⟩]
theorem checked73874 : checkPrefixCuts (2^48) 9686745089 10 Manual.Count131072.C073874.packed 64 cuts73874 = true := by
 decide +kernel
def cuts73875 : List PrefixCut := [⟨58,152317662,152317755⟩,
⟨64,167601628,167601731⟩]
theorem checked73875 : checkPrefixCuts (2^48) 9686876161 10 Manual.Count131072.C073875.packed 64 cuts73875 = true := by
 decide +kernel
def pointBounds73875 : List (Nat × Nat × Nat) := [(9686994944,116473984658431,116474374555294)]
theorem point_links_checked73875 : (cuts73875.take 1).map (fun c => (9686876161-1+2*2^10*c.k,116473832340769+c.lower,116474222237539+c.upper)) = pointBounds73875 := by
 decide +kernel
def cuts73876 : List PrefixCut := [⟨64,166872929,166873028⟩]
theorem checked73876 : checkPrefixCuts (2^48) 9687007233 10 Manual.Count131072.C073876.packed 64 cuts73876 = true := by
 decide +kernel
def cuts73877 : List PrefixCut := [⟨64,165766533,165766631⟩]
theorem checked73877 : checkPrefixCuts (2^48) 9687138305 10 Manual.Count131072.C073877.packed 64 cuts73877 = true := by
 decide +kernel
def cuts73878 : List PrefixCut := [⟨14,36291097,36291118⟩,
⟨64,168292168,168292269⟩]
theorem checked73878 : checkPrefixCuts (2^48) 9687269377 10 Manual.Count131072.C073878.packed 64 cuts73878 = true := by
 decide +kernel
def pointBounds73878 : List (Nat × Nat × Nat) := [(9687298048,116474368872956,116474758770047)]
theorem point_links_checked73878 : (cuts73878.take 1).map (fun c => (9687269377-1+2*2^10*c.k,116474332581859+c.lower,116474722478929+c.upper)) = pointBounds73878 := by
 decide +kernel
def cuts73879 : List PrefixCut := [⟨64,165180956,165181053⟩]
theorem checked73879 : checkPrefixCuts (2^48) 9687400449 10 Manual.Count131072.C073879.packed 64 cuts73879 = true := by
 decide +kernel
def cuts73880 : List PrefixCut := [⟨34,87572596,87572647⟩,
⟨64,165178705,165178805⟩]
theorem checked73880 : checkPrefixCuts (2^48) 9687531521 10 Manual.Count131072.C073880.packed 64 cuts73880 = true := by
 decide +kernel
def pointBounds73880 : List (Nat × Nat × Nat) := [(9687601152,116474753627579,116475143524898)]
theorem point_links_checked73880 : (cuts73880.take 1).map (fun c => (9687531521-1+2*2^10*c.k,116474666054983+c.lower,116475055952251+c.upper)) = pointBounds73880 := by
 decide +kernel
def cuts73881 : List PrefixCut := [⟨64,163985233,163985323⟩]
theorem checked73881 : checkPrefixCuts (2^48) 9687662593 10 Manual.Count131072.C073881.packed 64 cuts73881 = true := by
 decide +kernel
def cuts73882 : List PrefixCut := [⟨54,140652484,140652568⟩,
⟨64,166656020,166656119⟩]
theorem checked73882 : checkPrefixCuts (2^48) 9687793665 10 Manual.Count131072.C073882.packed 64 cuts73882 = true := by
 decide +kernel
def pointBounds73882 : List (Nat × Nat × Nat) := [(9687904256,116475135871405,116475525768947)]
theorem point_links_checked73882 : (cuts73882.take 1).map (fun c => (9687793665-1+2*2^10*c.k,116474995218921+c.lower,116475385116379+c.upper)) = pointBounds73882 := by
 decide +kernel
def cuts73883 : List PrefixCut := [⟨64,166247008,166247104⟩]
theorem checked73883 : checkPrefixCuts (2^48) 9687924737 10 Manual.Count131072.C073883.packed 64 cuts73883 = true := by
 decide +kernel
def cuts73884 : List PrefixCut := [⟨64,165983272,165983368⟩]
theorem checked73884 : checkPrefixCuts (2^48) 9688055809 10 Manual.Count131072.C073884.packed 64 cuts73884 = true := by
 decide +kernel
def cuts73885 : List PrefixCut := [⟨10,25799404,25799416⟩,
⟨64,165254697,165254791⟩]
theorem checked73885 : checkPrefixCuts (2^48) 9688186881 10 Manual.Count131072.C073885.packed 64 cuts73885 = true := by
 decide +kernel
def pointBounds73885 : List (Nat × Nat × Nat) := [(9688207360,116475519904625,116475909802386)]
theorem point_links_checked73885 : (cuts73885.take 1).map (fun c => (9688186881-1+2*2^10*c.k,116475494105221+c.lower,116475884002970+c.upper)) = pointBounds73885 := by
 decide +kernel
def cuts73886 : List PrefixCut := [⟨64,167344272,167344377⟩]
theorem checked73886 : checkPrefixCuts (2^48) 9688317953 10 Manual.Count131072.C073886.packed 64 cuts73886 = true := by
 decide +kernel
def cuts73887 : List PrefixCut := [⟨30,77512164,77512208⟩,
⟨64,165221174,165221266⟩]
theorem checked73887 : checkPrefixCuts (2^48) 9688449025 10 Manual.Count131072.C073887.packed 64 cuts73887 = true := by
 decide +kernel
def pointBounds73887 : List (Nat × Nat × Nat) := [(9688510464,116475904216354,116476294114346)]
theorem point_links_checked73887 : (cuts73887.take 1).map (fun c => (9688449025-1+2*2^10*c.k,116475826704190+c.lower,116476216602138+c.upper)) = pointBounds73887 := by
 decide +kernel
def cuts73888 : List PrefixCut := [⟨64,163330549,163330647⟩]
theorem checked73888 : checkPrefixCuts (2^48) 9688580097 10 Manual.Count131072.C073888.packed 64 cuts73888 = true := by
 decide +kernel
def cuts73889 : List PrefixCut := [⟨50,130442080,130442158⟩,
⟨64,166611183,166611288⟩]
theorem checked73889 : checkPrefixCuts (2^48) 9688711169 10 Manual.Count131072.C073889.packed 64 cuts73889 = true := by
 decide +kernel
def pointBounds73889 : List (Nat × Nat × Nat) := [(9688813568,116476285697993,116476675596209)]
theorem point_links_checked73889 : (cuts73889.take 1).map (fun c => (9688711169-1+2*2^10*c.k,116476155255913+c.lower,116476545154051+c.upper)) = pointBounds73889 := by
 decide +kernel
def cuts73890 : List PrefixCut := [⟨64,165911689,165911794⟩]
theorem checked73890 : checkPrefixCuts (2^48) 9688842241 10 Manual.Count131072.C073890.packed 64 cuts73890 = true := by
 decide +kernel
def cuts73891 : List PrefixCut := [⟨64,165793250,165793340⟩]
theorem checked73891 : checkPrefixCuts (2^48) 9688973313 10 Manual.Count131072.C073891.packed 64 cuts73891 = true := by
 decide +kernel
def cuts73892 : List PrefixCut := [⟨6,15338739,15338748⟩,
⟨64,164164171,164164266⟩]
theorem checked73892 : checkPrefixCuts (2^48) 9689104385 10 Manual.Count131072.C073892.packed 64 cuts73892 = true := by
 decide +kernel
def pointBounds73892 : List (Nat × Nat × Nat) := [(9689116672,116476668910774,116477058809221)]
theorem point_links_checked73892 : (cuts73892.take 1).map (fun c => (9689104385-1+2*2^10*c.k,116476653572035+c.lower,116477043470473+c.upper)) = pointBounds73892 := by
 decide +kernel
def cuts73893 : List PrefixCut := [⟨64,168664700,168664805⟩]
theorem checked73893 : checkPrefixCuts (2^48) 9689235457 10 Manual.Count131072.C073893.packed 64 cuts73893 = true := by
 decide +kernel
def cuts73894 : List PrefixCut := [⟨26,67192179,67192216⟩,
⟨64,165583168,165583268⟩]
theorem checked73894 : checkPrefixCuts (2^48) 9689366529 10 Manual.Count131072.C073894.packed 64 cuts73894 = true := by
 decide +kernel
def pointBounds73894 : List (Nat × Nat × Nat) := [(9689419776,116477053593085,116477443491760)]
theorem point_links_checked73894 : (cuts73894.take 1).map (fun c => (9689366529-1+2*2^10*c.k,116476986400906+c.lower,116477376299544+c.upper)) = pointBounds73894 := by
 decide +kernel
def cuts73895 : List PrefixCut := [⟨64,165290439,165290531⟩]
theorem checked73895 : checkPrefixCuts (2^48) 9689497601 10 Manual.Count131072.C073895.packed 64 cuts73895 = true := by
 decide +kernel
def cuts73896 : List PrefixCut := [⟨46,119739762,119739833⟩,
⟨64,166217766,166217865⟩]
theorem checked73896 : checkPrefixCuts (2^48) 9689628673 10 Manual.Count131072.C073896.packed 64 cuts73896 = true := by
 decide +kernel
def pointBounds73896 : List (Nat × Nat × Nat) := [(9689722880,116477437014275,116477826913176)]
theorem point_links_checked73896 : (cuts73896.take 1).map (fun c => (9689628673-1+2*2^10*c.k,116477317274513+c.lower,116477707173343+c.upper)) = pointBounds73896 := by
 decide +kernel
def cuts73897 : List PrefixCut := [⟨64,164704992,164705091⟩]
theorem checked73897 : checkPrefixCuts (2^48) 9689759745 10 Manual.Count131072.C073897.packed 64 cuts73897 = true := by
 decide +kernel
def cuts73898 : List PrefixCut := [⟨64,164412288,164412385⟩]
theorem checked73898 : checkPrefixCuts (2^48) 9689890817 10 Manual.Count131072.C073898.packed 64 cuts73898 = true := by
 decide +kernel
def cuts73899 : List PrefixCut := [⟨2,5315767,5315770⟩,
⟨64,165659115,165659213⟩]
theorem checked73899 : checkPrefixCuts (2^48) 9690021889 10 Manual.Count131072.C073899.packed 64 cuts73899 = true := by
 decide +kernel
def pointBounds73899 : List (Nat × Nat × Nat) := [(9690025984,116477817925326,116478207824454)]
theorem point_links_checked73899 : (cuts73899.take 1).map (fun c => (9690021889-1+2*2^10*c.k,116477812609559+c.lower,116478202508684+c.upper)) = pointBounds73899 := by
 decide +kernel
def cuts73900 : List PrefixCut := [⟨64,166412098,166412202⟩]
theorem checked73900 : checkPrefixCuts (2^48) 9690152961 10 Manual.Count131072.C073900.packed 64 cuts73900 = true := by
 decide +kernel
def cuts73901 : List PrefixCut := [⟨22,56990324,56990359⟩,
⟨64,165625586,165625693⟩]
theorem checked73901 : checkPrefixCuts (2^48) 9690284033 10 Manual.Count131072.C073901.packed 64 cuts73901 = true := by
 decide +kernel
def pointBounds73901 : List (Nat × Nat × Nat) := [(9690329088,116478201671096,116478591570458)]
theorem point_links_checked73901 : (cuts73901.take 1).map (fun c => (9690284033-1+2*2^10*c.k,116478144680772+c.lower,116478534580099+c.upper)) = pointBounds73901 := by
 decide +kernel
def cuts73902 : List PrefixCut := [⟨64,163502953,163503044⟩]
theorem checked73902 : checkPrefixCuts (2^48) 9690415105 10 Manual.Count131072.C073902.packed 64 cuts73902 = true := by
 decide +kernel
def cuts73903 : List PrefixCut := [⟨42,110578920,110578988⟩,
⟨64,167480060,167480163⟩]
theorem checked73903 : checkPrefixCuts (2^48) 9690546177 10 Manual.Count131072.C073903.packed 64 cuts73903 = true := by
 decide +kernel
def pointBounds73903 : List (Nat × Nat × Nat) := [(9690632192,116478584388231,116478974287824)]
theorem point_links_checked73903 : (cuts73903.take 1).map (fun c => (9690546177-1+2*2^10*c.k,116478473809311+c.lower,116478863708836+c.upper)) = pointBounds73903 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000121
