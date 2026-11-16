import PlattAssemblyKernel
import PlattCertificates.Count131072.C049920
import PlattCertificates.Count131072.C049921
import PlattCertificates.Count131072.C049922
import PlattCertificates.Count131072.C049923
import PlattCertificates.Count131072.C049924
import PlattCertificates.Count131072.C049925
import PlattCertificates.Count131072.C049926
import PlattCertificates.Count131072.C049927
import PlattCertificates.Count131072.C049928
import PlattCertificates.Count131072.C049929
import PlattCertificates.Count131072.C049930
import PlattCertificates.Count131072.C049931
import PlattCertificates.Count131072.C049932
import PlattCertificates.Count131072.C049933
import PlattCertificates.Count131072.C049934
import PlattCertificates.Count131072.C049935
import PlattCertificates.Count131072.C049936
import PlattCertificates.Count131072.C049937
import PlattCertificates.Count131072.C049938
import PlattCertificates.Count131072.C049939
import PlattCertificates.Count131072.C049940
import PlattCertificates.Count131072.C049941
import PlattCertificates.Count131072.C049942
import PlattCertificates.Count131072.C049943
import PlattCertificates.Count131072.C049944
import PlattCertificates.Count131072.C049945
import PlattCertificates.Count131072.C049946
import PlattCertificates.Count131072.C049947
import PlattCertificates.Count131072.C049948
import PlattCertificates.Count131072.C049949
import PlattCertificates.Count131072.C049950
import PlattCertificates.Count131072.C049951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000310
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49920 : List PrefixCut := [⟨14,54600548,54600581⟩,
⟨64,248280086,248280234⟩]
theorem checked49920 : checkPrefixCuts (2^48) 6547046401 10 Manual.Count131072.C049920.packed 64 cuts49920 = true := by
 decide +kernel
def pointBounds49920 : List (Nat × Nat × Nat) := [(6547075072,111636977423960,111637364534691)]
theorem point_links_checked49920 : (cuts49920.take 1).map (fun c => (6547046401-1+2*2^10*c.k,111636922823412+c.lower,111637309934110+c.upper)) = pointBounds49920 := by
 decide +kernel
def cuts49921 : List PrefixCut := [⟨50,194020432,194020544⟩,
⟨64,250080730,250080872⟩]
theorem checked49921 : checkPrefixCuts (2^48) 6547177473 10 Manual.Count131072.C049921.packed 64 cuts49921 = true := by
 decide +kernel
def pointBounds49921 : List (Nat × Nat × Nat) := [(6547279872,111637365123930,111637752234888)]
theorem point_links_checked49921 : (cuts49921.take 1).map (fun c => (6547177473-1+2*2^10*c.k,111637171103498+c.lower,111637558214344+c.upper)) = pointBounds49921 := by
 decide +kernel
def cuts49922 : List PrefixCut := [⟨64,245346790,245346929⟩]
theorem checked49922 : checkPrefixCuts (2^48) 6547308545 10 Manual.Count131072.C049922.packed 64 cuts49922 = true := by
 decide +kernel
def cuts49923 : List PrefixCut := [⟨22,86065829,86065878⟩,
⟨64,247061476,247061621⟩]
theorem checked49923 : checkPrefixCuts (2^48) 6547439617 10 Manual.Count131072.C049923.packed 64 cuts49923 = true := by
 decide +kernel
def pointBounds49923 : List (Nat × Nat × Nat) := [(6547484672,111637752596847,111638139708023)]
theorem point_links_checked49923 : (cuts49923.take 1).map (fun c => (6547439617-1+2*2^10*c.k,111637666531018+c.lower,111638053642145+c.upper)) = pointBounds49923 := by
 decide +kernel
def cuts49924 : List PrefixCut := [⟨58,227023978,227024107⟩,
⟨64,250323686,250323828⟩]
theorem checked49924 : checkPrefixCuts (2^48) 6547570689 10 Manual.Count131072.C049924.packed 64 cuts49924 = true := by
 decide +kernel
def pointBounds49924 : List (Nat × Nat × Nat) := [(6547689472,111638140616472,111638527727873)]
theorem point_links_checked49924 : (cuts49924.take 1).map (fun c => (6547570689-1+2*2^10*c.k,111637913592494+c.lower,111638300703766+c.upper)) = pointBounds49924 := by
 decide +kernel
def cuts49925 : List PrefixCut := [⟨64,249329960,249330101⟩]
theorem checked49925 : checkPrefixCuts (2^48) 6547701761 10 Manual.Count131072.C049925.packed 64 cuts49925 = true := by
 decide +kernel
def cuts49926 : List PrefixCut := [⟨30,116968414,116968477⟩,
⟨64,252462992,252463126⟩]
theorem checked49926 : checkPrefixCuts (2^48) 6547832833 10 Manual.Count131072.C049926.packed 64 cuts49926 = true := by
 decide +kernel
def pointBounds49926 : List (Nat × Nat × Nat) := [(6547894272,111638530214554,111638917326172)]
theorem point_links_checked49926 : (cuts49926.take 1).map (fun c => (6547832833-1+2*2^10*c.k,111638413246140+c.lower,111638800357695+c.upper)) = pointBounds49926 := by
 decide +kernel
def cuts49927 : List PrefixCut := [⟨64,250007717,250007862⟩]
theorem checked49927 : checkPrefixCuts (2^48) 6547963905 10 Manual.Count131072.C049927.packed 64 cuts49927 = true := by
 decide +kernel
def cuts49928 : List PrefixCut := [⟨2,7608479,7608483⟩,
⟨64,246735826,246735963⟩]
theorem checked49928 : checkPrefixCuts (2^48) 6548094977 10 Manual.Count131072.C049928.packed 64 cuts49928 = true := by
 decide +kernel
def pointBounds49928 : List (Nat × Nat × Nat) := [(6548099072,111638923325328,111639310437166)]
theorem point_links_checked49928 : (cuts49928.take 1).map (fun c => (6548094977-1+2*2^10*c.k,111638915716849+c.lower,111639302828683+c.upper)) = pointBounds49928 := by
 decide +kernel
def cuts49929 : List PrefixCut := [⟨38,146620646,146620735⟩,
⟨64,249997703,249997849⟩]
theorem checked49929 : checkPrefixCuts (2^48) 6548226049 10 Manual.Count131072.C049929.packed 64 cuts49929 = true := by
 decide +kernel
def pointBounds49929 : List (Nat × Nat × Nat) := [(6548303872,111639309073321,111639696185381)]
theorem point_links_checked49929 : (cuts49929.take 1).map (fun c => (6548226049-1+2*2^10*c.k,111639162452675+c.lower,111639549564646+c.upper)) = pointBounds49929 := by
 decide +kernel
def cuts49930 : List PrefixCut := [⟨64,249476905,249477054⟩]
theorem checked49930 : checkPrefixCuts (2^48) 6548357121 10 Manual.Count131072.C049930.packed 64 cuts49930 = true := by
 decide +kernel
def cuts49931 : List PrefixCut := [⟨10,38426907,38426932⟩,
⟨64,247666652,247666792⟩]
theorem checked49931 : checkPrefixCuts (2^48) 6548488193 10 Manual.Count131072.C049931.packed 64 cuts49931 = true := by
 decide +kernel
def pointBounds49931 : List (Nat × Nat × Nat) := [(6548508672,111639700354190,111640087466481)]
theorem point_links_checked49931 : (cuts49931.take 1).map (fun c => (6548488193-1+2*2^10*c.k,111639661927283+c.lower,111640049039549+c.upper)) = pointBounds49931 := by
 decide +kernel
def cuts49932 : List PrefixCut := [⟨46,182544631,182544735⟩,
⟨64,251315176,251315318⟩]
theorem checked49932 : checkPrefixCuts (2^48) 6548619265 10 Manual.Count131072.C049932.packed 64 cuts49932 = true := by
 decide +kernel
def pointBounds49932 : List (Nat × Nat × Nat) := [(6548713472,111640092138566,111640479251076)]
theorem point_links_checked49932 : (cuts49932.take 1).map (fun c => (6548619265-1+2*2^10*c.k,111639909593935+c.lower,111640296706341+c.upper)) = pointBounds49932 := by
 decide +kernel
def cuts49933 : List PrefixCut := [⟨64,251138194,251138333⟩]
theorem checked49933 : checkPrefixCuts (2^48) 6548750337 10 Manual.Count131072.C049933.packed 64 cuts49933 = true := by
 decide +kernel
def cuts49934 : List PrefixCut := [⟨18,71218663,71218703⟩,
⟨64,250402518,250402663⟩]
theorem checked49934 : checkPrefixCuts (2^48) 6548881409 10 Manual.Count131072.C049934.packed 64 cuts49934 = true := by
 decide +kernel
def pointBounds49934 : List (Nat × Nat × Nat) := [(6548918272,111640483265968,111640870378695)]
theorem point_links_checked49934 : (cuts49934.take 1).map (fun c => (6548881409-1+2*2^10*c.k,111640412047305+c.lower,111640799159992+c.upper)) = pointBounds49934 := by
 decide +kernel
def cuts49935 : List PrefixCut := [⟨54,209094705,209094821⟩,
⟨64,248162574,248162712⟩]
theorem checked49935 : checkPrefixCuts (2^48) 6549012481 10 Manual.Count131072.C049935.packed 64 cuts49935 = true := by
 decide +kernel
def pointBounds49935 : List (Nat × Nat × Nat) := [(6549123072,111640871544528,111641258657476)]
theorem point_links_checked49935 : (cuts49935.take 1).map (fun c => (6549012481-1+2*2^10*c.k,111640662449823+c.lower,111641049562655+c.upper)) = pointBounds49935 := by
 decide +kernel
def cuts49936 : List PrefixCut := [⟨64,250134609,250134753⟩]
theorem checked49936 : checkPrefixCuts (2^48) 6549143553 10 Manual.Count131072.C049936.packed 64 cuts49936 = true := by
 decide +kernel
def cuts49937 : List PrefixCut := [⟨26,101212845,101212901⟩,
⟨64,247336072,247336215⟩]
theorem checked49937 : checkPrefixCuts (2^48) 6549274625 10 Manual.Count131072.C049937.packed 64 cuts49937 = true := by
 decide +kernel
def pointBounds49937 : List (Nat × Nat × Nat) := [(6549327872,111641261959851,111641649073021)]
theorem point_links_checked49937 : (cuts49937.take 1).map (fun c => (6549274625-1+2*2^10*c.k,111641160747006+c.lower,111641547860120+c.upper)) = pointBounds49937 := by
 decide +kernel
def cuts49938 : List PrefixCut := [⟨62,241529318,241529460⟩,
⟨64,248577434,248577580⟩]
theorem checked49938 : checkPrefixCuts (2^48) 6549405697 10 Manual.Count131072.C049938.packed 64 cuts49938 = true := by
 decide +kernel
def pointBounds49938 : List (Nat × Nat × Nat) := [(6549532672,111641649612396,111642036725795)]
theorem point_links_checked49938 : (cuts49938.take 1).map (fun c => (6549405697-1+2*2^10*c.k,111641408083078+c.lower,111641795196335+c.upper)) = pointBounds49938 := by
 decide +kernel
def cuts49939 : List PrefixCut := [⟨64,247884854,247884996⟩]
theorem checked49939 : checkPrefixCuts (2^48) 6549536769 10 Manual.Count131072.C049939.packed 64 cuts49939 = true := by
 decide +kernel
def cuts49940 : List PrefixCut := [⟨34,132363671,132363747⟩,
⟨64,252993904,252994048⟩]
theorem checked49940 : checkPrefixCuts (2^48) 6549667841 10 Manual.Count131072.C049940.packed 64 cuts49940 = true := by
 decide +kernel
def pointBounds49940 : List (Nat × Nat × Nat) := [(6549737472,111642036909037,111642424022658)]
theorem point_links_checked49940 : (cuts49940.take 1).map (fun c => (6549667841-1+2*2^10*c.k,111641904545366+c.lower,111642291658911+c.upper)) = pointBounds49940 := by
 decide +kernel
def cuts49941 : List PrefixCut := [⟨64,249851729,249851877⟩]
theorem checked49941 : checkPrefixCuts (2^48) 6549798913 10 Manual.Count131072.C049941.packed 64 cuts49941 = true := by
 decide +kernel
def cuts49942 : List PrefixCut := [⟨6,22690107,22690119⟩,
⟨64,248342682,248342820⟩]
theorem checked49942 : checkPrefixCuts (2^48) 6549929985 10 Manual.Count131072.C049942.packed 64 cuts49942 = true := by
 decide +kernel
def pointBounds49942 : List (Nat × Nat × Nat) := [(6549942272,111642430081106,111642817194955)]
theorem point_links_checked49942 : (cuts49942.take 1).map (fun c => (6549929985-1+2*2^10*c.k,111642407390999+c.lower,111642794504836+c.upper)) = pointBounds49942 := by
 decide +kernel
def cuts49943 : List PrefixCut := [⟨42,163811488,163811582⟩,
⟨64,248509609,248509751⟩]
theorem checked49943 : checkPrefixCuts (2^48) 6550061057 10 Manual.Count131072.C049943.packed 64 cuts49943 = true := by
 decide +kernel
def pointBounds49943 : List (Nat × Nat × Nat) := [(6550147072,111642819545169,111643206659238)]
theorem point_links_checked49943 : (cuts49943.take 1).map (fun c => (6550061057-1+2*2^10*c.k,111642655733681+c.lower,111643042847656+c.upper)) = pointBounds49943 := by
 decide +kernel
def cuts49944 : List PrefixCut := [⟨64,248891359,248891507⟩]
theorem checked49944 : checkPrefixCuts (2^48) 6550192129 10 Manual.Count131072.C049944.packed 64 cuts49944 = true := by
 decide +kernel
def cuts49945 : List PrefixCut := [⟨14,52123884,52123915⟩,
⟨64,249659838,249659983⟩]
theorem checked49945 : checkPrefixCuts (2^48) 6550323201 10 Manual.Count131072.C049945.packed 64 cuts49945 = true := by
 decide +kernel
def pointBounds49945 : List (Nat × Nat × Nat) := [(6550351872,111643205258533,111643592372829)]
theorem point_links_checked49945 : (cuts49945.take 1).map (fun c => (6550323201-1+2*2^10*c.k,111643153134649+c.lower,111643540248914+c.upper)) = pointBounds49945 := by
 decide +kernel
def cuts49946 : List PrefixCut := [⟨50,193106960,193107068⟩,
⟨64,247248556,247248694⟩]
theorem checked49946 : checkPrefixCuts (2^48) 6550454273 10 Manual.Count131072.C049946.packed 64 cuts49946 = true := by
 decide +kernel
def pointBounds49946 : List (Nat × Nat × Nat) := [(6550556672,111643595901447,111643983015965)]
theorem point_links_checked49946 : (cuts49946.take 1).map (fun c => (6550454273-1+2*2^10*c.k,111643402794487+c.lower,111643789908897+c.upper)) = pointBounds49946 := by
 decide +kernel
def cuts49947 : List PrefixCut := [⟨64,248790496,248790635⟩]
theorem checked49947 : checkPrefixCuts (2^48) 6550585345 10 Manual.Count131072.C049947.packed 64 cuts49947 = true := by
 decide +kernel
def cuts49948 : List PrefixCut := [⟨22,84218099,84218146⟩,
⟨64,250676095,250676234⟩]
theorem checked49948 : checkPrefixCuts (2^48) 6550716417 10 Manual.Count131072.C049948.packed 64 cuts49948 = true := by
 decide +kernel
def pointBounds49948 : List (Nat × Nat × Nat) := [(6550761472,111643983051638,111644370166372)]
theorem point_links_checked49948 : (cuts49948.take 1).map (fun c => (6550716417-1+2*2^10*c.k,111643898833539+c.lower,111644285948226+c.upper)) = pointBounds49948 := by
 decide +kernel
def cuts49949 : List PrefixCut := [⟨58,223816773,223816900⟩,
⟨64,247620429,247620570⟩]
theorem checked49949 : checkPrefixCuts (2^48) 6550847489 10 Manual.Count131072.C049949.packed 64 cuts49949 = true := by
 decide +kernel
def pointBounds49949 : List (Nat × Nat × Nat) := [(6550966272,111644373326407,111644760441360)]
theorem point_links_checked49949 : (cuts49949.take 1).map (fun c => (6550847489-1+2*2^10*c.k,111644149509634+c.lower,111644536624460+c.upper)) = pointBounds49949 := by
 decide +kernel
def cuts49950 : List PrefixCut := [⟨64,247615455,247615594⟩]
theorem checked49950 : checkPrefixCuts (2^48) 6550978561 10 Manual.Count131072.C049950.packed 64 cuts49950 = true := by
 decide +kernel
def cuts49951 : List PrefixCut := [⟨30,116523218,116523283⟩,
⟨64,250746999,250747138⟩]
theorem checked49951 : checkPrefixCuts (2^48) 6551109633 10 Manual.Count131072.C049951.packed 64 cuts49951 = true := by
 decide +kernel
def pointBounds49951 : List (Nat × Nat × Nat) := [(6551171072,111644761268736,111645148383907)]
theorem point_links_checked49951 : (cuts49951.take 1).map (fun c => (6551109633-1+2*2^10*c.k,111644644745518+c.lower,111645031860624+c.upper)) = pointBounds49951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000310
