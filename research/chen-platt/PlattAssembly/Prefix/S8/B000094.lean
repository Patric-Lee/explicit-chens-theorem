import PlattAssemblyKernel
import PlattCertificates.Count131072.C073008
import PlattCertificates.Count131072.C073009
import PlattCertificates.Count131072.C073010
import PlattCertificates.Count131072.C073011
import PlattCertificates.Count131072.C073012
import PlattCertificates.Count131072.C073013
import PlattCertificates.Count131072.C073014
import PlattCertificates.Count131072.C073015
import PlattCertificates.Count131072.C073016
import PlattCertificates.Count131072.C073017
import PlattCertificates.Count131072.C073018
import PlattCertificates.Count131072.C073019
import PlattCertificates.Count131072.C073020
import PlattCertificates.Count131072.C073021
import PlattCertificates.Count131072.C073022
import PlattCertificates.Count131072.C073023
import PlattCertificates.Count131072.C073024
import PlattCertificates.Count131072.C073025
import PlattCertificates.Count131072.C073026
import PlattCertificates.Count131072.C073027
import PlattCertificates.Count131072.C073028
import PlattCertificates.Count131072.C073029
import PlattCertificates.Count131072.C073030
import PlattCertificates.Count131072.C073031
import PlattCertificates.Count131072.C073032
import PlattCertificates.Count131072.C073033
import PlattCertificates.Count131072.C073034
import PlattCertificates.Count131072.C073035
import PlattCertificates.Count131072.C073036
import PlattCertificates.Count131072.C073037
import PlattCertificates.Count131072.C073038
import PlattCertificates.Count131072.C073039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73008 : List PrefixCut := [⟨64,168591472,168591567⟩]
theorem checked73008 : checkPrefixCuts (2^48) 9573236737 10 Manual.Count131072.C073008.packed 64 cuts73008 = true := by
 decide +kernel
def cuts73009 : List PrefixCut := [⟨35,90616215,90616270⟩,
⟨64,166384026,166384125⟩]
theorem checked73009 : checkPrefixCuts (2^48) 9573367809 10 Manual.Count131072.C073009.packed 64 cuts73009 = true := by
 decide +kernel
def pointBounds73009 : List (Nat × Nat × Nat) := [(9573439488,116329564821999,116329954632649)]
theorem point_links_checked73009 : (cuts73009.take 1).map (fun c => (9573367809-1+2*2^10*c.k,116329474205784+c.lower,116329864016379+c.upper)) = pointBounds73009 := by
 decide +kernel
def cuts73010 : List PrefixCut := [⟨64,165470315,165470418⟩]
theorem checked73010 : checkPrefixCuts (2^48) 9573498881 10 Manual.Count131072.C073010.packed 64 cuts73010 = true := by
 decide +kernel
def cuts73011 : List PrefixCut := [⟨54,142594328,142594415⟩,
⟨64,168643339,168643443⟩]
theorem checked73011 : checkPrefixCuts (2^48) 9573629953 10 Manual.Count131072.C073011.packed 64 cuts73011 = true := by
 decide +kernel
def pointBounds73011 : List (Nat × Nat × Nat) := [(9573740544,116329948654453,116330338465337)]
theorem point_links_checked73011 : (cuts73011.take 1).map (fun c => (9573629953-1+2*2^10*c.k,116329806060125+c.lower,116330195870922+c.upper)) = pointBounds73011 := by
 decide +kernel
def cuts73012 : List PrefixCut := [⟨64,166494812,166494904⟩]
theorem checked73012 : checkPrefixCuts (2^48) 9573761025 10 Manual.Count131072.C073012.packed 64 cuts73012 = true := by
 decide +kernel
def cuts73013 : List PrefixCut := [⟨64,166022127,166022228⟩]
theorem checked73013 : checkPrefixCuts (2^48) 9573892097 10 Manual.Count131072.C073013.packed 64 cuts73013 = true := by
 decide +kernel
def cuts73014 : List PrefixCut := [⟨9,23049465,23049478⟩,
⟨64,167431034,167431132⟩]
theorem checked73014 : checkPrefixCuts (2^48) 9574023169 10 Manual.Count131072.C073014.packed 64 cuts73014 = true := by
 decide +kernel
def pointBounds73014 : List (Nat × Nat × Nat) := [(9574041600,116330330269868,116330720080975)]
theorem point_links_checked73014 : (cuts73014.take 1).map (fun c => (9574023169-1+2*2^10*c.k,116330307220403+c.lower,116330697031497+c.upper)) = pointBounds73014 := by
 decide +kernel
def cuts73015 : List PrefixCut := [⟨64,168193123,168193221⟩]
theorem checked73015 : checkPrefixCuts (2^48) 9574154241 10 Manual.Count131072.C073015.packed 64 cuts73015 = true := by
 decide +kernel
def cuts73016 : List PrefixCut := [⟨28,73908991,73909034⟩,
⟨64,168161414,168161519⟩]
theorem checked73016 : checkPrefixCuts (2^48) 9574285313 10 Manual.Count131072.C073016.packed 64 cuts73016 = true := by
 decide +kernel
def pointBounds73016 : List (Nat × Nat × Nat) := [(9574342656,116330716753551,116331106564884)]
theorem point_links_checked73016 : (cuts73016.take 1).map (fun c => (9574285313-1+2*2^10*c.k,116330642844560+c.lower,116331032655850+c.upper)) = pointBounds73016 := by
 decide +kernel
def cuts73017 : List PrefixCut := [⟨64,166894974,166895082⟩]
theorem checked73017 : checkPrefixCuts (2^48) 9574416385 10 Manual.Count131072.C073017.packed 64 cuts73017 = true := by
 decide +kernel
def cuts73018 : List PrefixCut := [⟨47,122678259,122678337⟩,
⟨64,167127876,167127982⟩]
theorem checked73018 : checkPrefixCuts (2^48) 9574547457 10 Manual.Count131072.C073018.packed 64 cuts73018 = true := by
 decide +kernel
def pointBounds73018 : List (Nat × Nat × Nat) := [(9574643712,116331100579207,116331490390788)]
theorem point_links_checked73018 : (cuts73018.take 1).map (fun c => (9574547457-1+2*2^10*c.k,116330977900948+c.lower,116331367712451+c.upper)) = pointBounds73018 := by
 decide +kernel
def cuts73019 : List PrefixCut := [⟨64,167037397,167037497⟩]
theorem checked73019 : checkPrefixCuts (2^48) 9574678529 10 Manual.Count131072.C073019.packed 64 cuts73019 = true := by
 decide +kernel
def cuts73020 : List PrefixCut := [⟨64,166564749,166564852⟩]
theorem checked73020 : checkPrefixCuts (2^48) 9574809601 10 Manual.Count131072.C073020.packed 64 cuts73020 = true := by
 decide +kernel
def cuts73021 : List PrefixCut := [⟨2,5732422,5732424⟩,
⟨64,168914224,168914322⟩]
theorem checked73021 : checkPrefixCuts (2^48) 9574940673 10 Manual.Count131072.C073021.packed 64 cuts73021 = true := by
 decide +kernel
def pointBounds73021 : List (Nat × Nat × Nat) := [(9574944768,116331484363392,116331874175206)]
theorem point_links_checked73021 : (cuts73021.take 1).map (fun c => (9574940673-1+2*2^10*c.k,116331478630970+c.lower,116331868442782+c.upper)) = pointBounds73021 := by
 decide +kernel
def cuts73022 : List PrefixCut := [⟨64,168735523,168735627⟩]
theorem checked73022 : checkPrefixCuts (2^48) 9575071745 10 Manual.Count131072.C073022.packed 64 cuts73022 = true := by
 decide +kernel
def cuts73023 : List PrefixCut := [⟨21,54794451,54794487⟩,
⟨64,169085964,169086070⟩]
theorem checked73023 : checkPrefixCuts (2^48) 9575202817 10 Manual.Count131072.C073023.packed 64 cuts73023 = true := by
 decide +kernel
def pointBounds73023 : List (Nat × Nat × Nat) := [(9575245824,116331871075168,116332260887218)]
theorem point_links_checked73023 : (cuts73023.take 1).map (fun c => (9575202817-1+2*2^10*c.k,116331816280717+c.lower,116332206092731+c.upper)) = pointBounds73023 := by
 decide +kernel
def cuts73024 : List PrefixCut := [⟨64,166908367,166908469⟩]
theorem checked73024 : checkPrefixCuts (2^48) 9575333889 10 Manual.Count131072.C073024.packed 64 cuts73024 = true := by
 decide +kernel
def cuts73025 : List PrefixCut := [⟨40,104294533,104294594⟩,
⟨64,167317630,167317729⟩]
theorem checked73025 : checkPrefixCuts (2^48) 9575464961 10 Manual.Count131072.C073025.packed 64 cuts73025 = true := by
 decide +kernel
def pointBounds73025 : List (Nat × Nat × Nat) := [(9575546880,116332256569581,116332646381864)]
theorem point_links_checked73025 : (cuts73025.take 1).map (fun c => (9575464961-1+2*2^10*c.k,116332152275048+c.lower,116332542087270+c.upper)) = pointBounds73025 := by
 decide +kernel
def cuts73026 : List PrefixCut := [⟨64,167815066,167815172⟩]
theorem checked73026 : checkPrefixCuts (2^48) 9575596033 10 Manual.Count131072.C073026.packed 64 cuts73026 = true := by
 decide +kernel
def cuts73027 : List PrefixCut := [⟨59,156437192,156437286⟩,
⟨64,169341262,169341363⟩]
theorem checked73027 : checkPrefixCuts (2^48) 9575727105 10 Manual.Count131072.C073027.packed 64 cuts73027 = true := by
 decide +kernel
def pointBounds73027 : List (Nat × Nat × Nat) := [(9575847936,116332643844936,116333033657457)]
theorem point_links_checked73027 : (cuts73027.take 1).map (fun c => (9575727105-1+2*2^10*c.k,116332487407744+c.lower,116332877220171+c.upper)) = pointBounds73027 := by
 decide +kernel
def cuts73028 : List PrefixCut := [⟨64,167986833,167986932⟩]
theorem checked73028 : checkPrefixCuts (2^48) 9575858177 10 Manual.Count131072.C073028.packed 64 cuts73028 = true := by
 decide +kernel
def cuts73029 : List PrefixCut := [⟨64,169483602,169483703⟩]
theorem checked73029 : checkPrefixCuts (2^48) 9575989249 10 Manual.Count131072.C073029.packed 64 cuts73029 = true := by
 decide +kernel
def cuts73030 : List PrefixCut := [⟨14,37153223,37153246⟩,
⟨64,166659539,166659641⟩]
theorem checked73030 : checkPrefixCuts (2^48) 9576120321 10 Manual.Count131072.C073030.packed 64 cuts73030 = true := by
 decide +kernel
def pointBounds73030 : List (Nat × Nat × Nat) := [(9576148992,116333031372664,116333421185415)]
theorem point_links_checked73030 : (cuts73030.take 1).map (fun c => (9576120321-1+2*2^10*c.k,116332994219441+c.lower,116333384032169+c.upper)) = pointBounds73030 := by
 decide +kernel
def cuts73031 : List PrefixCut := [⟨64,163864932,163865027⟩]
theorem checked73031 : checkPrefixCuts (2^48) 9576251393 10 Manual.Count131072.C073031.packed 64 cuts73031 = true := by
 decide +kernel
def cuts73032 : List PrefixCut := [⟨33,86619720,86619774⟩,
⟨64,167654313,167654417⟩]
theorem checked73032 : checkPrefixCuts (2^48) 9576382465 10 Manual.Count131072.C073032.packed 64 cuts73032 = true := by
 decide +kernel
def pointBounds73032 : List (Nat × Nat × Nat) := [(9576450048,116333411363632,116333801176611)]
theorem point_links_checked73032 : (cuts73032.take 1).map (fun c => (9576382465-1+2*2^10*c.k,116333324743912+c.lower,116333714556837+c.upper)) = pointBounds73032 := by
 decide +kernel
def cuts73033 : List PrefixCut := [⟨64,164742208,164742307⟩]
theorem checked73033 : checkPrefixCuts (2^48) 9576513537 10 Manual.Count131072.C073033.packed 64 cuts73033 = true := by
 decide +kernel
def cuts73034 : List PrefixCut := [⟨52,138023155,138023236⟩,
⟨64,168854777,168854877⟩]
theorem checked73034 : checkPrefixCuts (2^48) 9576644609 10 Manual.Count131072.C073034.packed 64 cuts73034 = true := by
 decide +kernel
def pointBounds73034 : List (Nat × Nat × Nat) := [(9576751104,116333795163588,116334184976797)]
theorem point_links_checked73034 : (cuts73034.take 1).map (fun c => (9576644609-1+2*2^10*c.k,116333657140433+c.lower,116334046953561+c.upper)) = pointBounds73034 := by
 decide +kernel
def cuts73035 : List PrefixCut := [⟨64,169352117,169352218⟩]
theorem checked73035 : checkPrefixCuts (2^48) 9576775681 10 Manual.Count131072.C073035.packed 64 cuts73035 = true := by
 decide +kernel
def cuts73036 : List PrefixCut := [⟨64,166293164,166293261⟩]
theorem checked73036 : checkPrefixCuts (2^48) 9576906753 10 Manual.Count131072.C073036.packed 64 cuts73036 = true := by
 decide +kernel
def cuts73037 : List PrefixCut := [⟨7,18751188,18751200⟩,
⟨64,168495162,168495264⟩]
theorem checked73037 : checkPrefixCuts (2^48) 9577037825 10 Manual.Count131072.C073037.packed 64 cuts73037 = true := by
 decide +kernel
def pointBounds73037 : List (Nat × Nat × Nat) := [(9577052160,116334180391679,116334570205117)]
theorem point_links_checked73037 : (cuts73037.take 1).map (fun c => (9577037825-1+2*2^10*c.k,116334161640491+c.lower,116334551453917+c.upper)) = pointBounds73037 := by
 decide +kernel
def cuts73038 : List PrefixCut := [⟨64,167934443,167934538⟩]
theorem checked73038 : checkPrefixCuts (2^48) 9577168897 10 Manual.Count131072.C073038.packed 64 cuts73038 = true := by
 decide +kernel
def cuts73039 : List PrefixCut := [⟨26,67625736,67625778⟩,
⟨64,167785199,167785297⟩]
theorem checked73039 : checkPrefixCuts (2^48) 9577299969 10 Manual.Count131072.C073039.packed 64 cuts73039 = true := by
 decide +kernel
def pointBounds73039 : List (Nat × Nat × Nat) := [(9577353216,116334565695832,116334955509497)]
theorem point_links_checked73039 : (cuts73039.take 1).map (fun c => (9577299969-1+2*2^10*c.k,116334498070096+c.lower,116334887883719+c.upper)) = pointBounds73039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000094
