import PlattAssemblyKernel
import PlattCertificates.Count131072.C063072
import PlattCertificates.Count131072.C063073
import PlattCertificates.Count131072.C063074
import PlattCertificates.Count131072.C063075
import PlattCertificates.Count131072.C063076
import PlattCertificates.Count131072.C063077
import PlattCertificates.Count131072.C063078
import PlattCertificates.Count131072.C063079
import PlattCertificates.Count131072.C063080
import PlattCertificates.Count131072.C063081
import PlattCertificates.Count131072.C063082
import PlattCertificates.Count131072.C063083
import PlattCertificates.Count131072.C063084
import PlattCertificates.Count131072.C063085
import PlattCertificates.Count131072.C063086
import PlattCertificates.Count131072.C063087
import PlattCertificates.Count131072.C063088
import PlattCertificates.Count131072.C063089
import PlattCertificates.Count131072.C063090
import PlattCertificates.Count131072.C063091
import PlattCertificates.Count131072.C063092
import PlattCertificates.Count131072.C063093
import PlattCertificates.Count131072.C063094
import PlattCertificates.Count131072.C063095
import PlattCertificates.Count131072.C063096
import PlattCertificates.Count131072.C063097
import PlattCertificates.Count131072.C063098
import PlattCertificates.Count131072.C063099
import PlattCertificates.Count131072.C063100
import PlattCertificates.Count131072.C063101
import PlattCertificates.Count131072.C063102
import PlattCertificates.Count131072.C063103
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000096
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63072 : List PrefixCut := [⟨64,198676868,198676976⟩]
theorem checked63072 : checkPrefixCuts (2^48) 8270905345 10 Manual.Count131072.C063072.packed 64 cuts63072 = true := by
 decide +kernel
def cuts63073 : List PrefixCut := [⟨56,170325949,170326045⟩,
⟨64,195134466,195134578⟩]
theorem checked63073 : checkPrefixCuts (2^48) 8271036417 10 Manual.Count131072.C063073.packed 64 cuts63073 = true := by
 decide +kernel
def pointBounds63073 : List (Nat × Nat × Nat) := [(8271151104,114533056481587,114533445242040)]
theorem point_links_checked63073 : (cuts63073.take 1).map (fun c => (8271036417-1+2*2^10*c.k,114532886155638+c.lower,114533274915995+c.upper)) = pointBounds63073 := by
 decide +kernel
def cuts63074 : List PrefixCut := [⟨64,193668053,193668170⟩]
theorem checked63074 : checkPrefixCuts (2^48) 8271167489 10 Manual.Count131072.C063074.packed 64 cuts63074 = true := by
 decide +kernel
def cuts63075 : List PrefixCut := [⟨55,165998747,165998848⟩,
⟨64,193835136,193835251⟩]
theorem checked63075 : checkPrefixCuts (2^48) 8271298561 10 Manual.Count131072.C063075.packed 64 cuts63075 = true := by
 decide +kernel
def pointBounds63075 : List (Nat × Nat × Nat) := [(8271411200,114533440956904,114533829717591)]
theorem point_links_checked63075 : (cuts63075.take 1).map (fun c => (8271298561-1+2*2^10*c.k,114533274958157+c.lower,114533663718743+c.upper)) = pointBounds63075 := by
 decide +kernel
def cuts63076 : List PrefixCut := [⟨64,196452341,196452458⟩]
theorem checked63076 : checkPrefixCuts (2^48) 8271429633 10 Manual.Count131072.C063076.packed 64 cuts63076 = true := by
 decide +kernel
def cuts63077 : List PrefixCut := [⟨54,165074715,165074813⟩,
⟨64,195054035,195054151⟩]
theorem checked63077 : checkPrefixCuts (2^48) 8271560705 10 Manual.Count131072.C063077.packed 64 cuts63077 = true := by
 decide +kernel
def pointBounds63077 : List (Nat × Nat × Nat) := [(8271671296,114533830320349,114534219081265)]
theorem point_links_checked63077 : (cuts63077.take 1).map (fun c => (8271560705-1+2*2^10*c.k,114533665245634+c.lower,114534054006452+c.upper)) = pointBounds63077 := by
 decide +kernel
def cuts63078 : List PrefixCut := [⟨64,197092645,197092759⟩]
theorem checked63078 : checkPrefixCuts (2^48) 8271691777 10 Manual.Count131072.C063078.packed 64 cuts63078 = true := by
 decide +kernel
def cuts63079 : List PrefixCut := [⟨53,161190316,161190415⟩,
⟨64,192904099,192904217⟩]
theorem checked63079 : checkPrefixCuts (2^48) 8271822849 10 Manual.Count131072.C063079.packed 64 cuts63079 = true := by
 decide +kernel
def pointBounds63079 : List (Nat × Nat × Nat) := [(8271931392,114534218582630,114534607343777)]
theorem point_links_checked63079 : (cuts63079.take 1).map (fun c => (8271822849-1+2*2^10*c.k,114534057392314+c.lower,114534446153362+c.upper)) = pointBounds63079 := by
 decide +kernel
def cuts63080 : List PrefixCut := [⟨64,195691274,195691382⟩]
theorem checked63080 : checkPrefixCuts (2^48) 8271953921 10 Manual.Count131072.C063080.packed 64 cuts63080 = true := by
 decide +kernel
def cuts63081 : List PrefixCut := [⟨52,161593577,161593670⟩,
⟨64,198954773,198954887⟩]
theorem checked63081 : checkPrefixCuts (2^48) 8272084993 10 Manual.Count131072.C063081.packed 64 cuts63081 = true := by
 decide +kernel
def pointBounds63081 : List (Nat × Nat × Nat) := [(8272191488,114534607581264,114534996342631)]
theorem point_links_checked63081 : (cuts63081.take 1).map (fun c => (8272084993-1+2*2^10*c.k,114534445987687+c.lower,114534834748961+c.upper)) = pointBounds63081 := by
 decide +kernel
def cuts63082 : List PrefixCut := [⟨64,199291871,199291988⟩]
theorem checked63082 : checkPrefixCuts (2^48) 8272216065 10 Manual.Count131072.C063082.packed 64 cuts63082 = true := by
 decide +kernel
def cuts63083 : List PrefixCut := [⟨51,154749282,154749373⟩,
⟨64,193198117,193198229⟩]
theorem checked63083 : checkPrefixCuts (2^48) 8272347137 10 Manual.Count131072.C063083.packed 64 cuts63083 = true := by
 decide +kernel
def pointBounds63083 : List (Nat × Nat × Nat) := [(8272451584,114534998983613,114535387745209)]
theorem point_links_checked63083 : (cuts63083.take 1).map (fun c => (8272347137-1+2*2^10*c.k,114534844234331+c.lower,114535232995836+c.upper)) = pointBounds63083 := by
 decide +kernel
def cuts63084 : List PrefixCut := [⟨64,194351886,194352002⟩]
theorem checked63084 : checkPrefixCuts (2^48) 8272478209 10 Manual.Count131072.C063084.packed 64 cuts63084 = true := by
 decide +kernel
def cuts63085 : List PrefixCut := [⟨50,154370128,154370214⟩,
⟨64,197717269,197717380⟩]
theorem checked63085 : checkPrefixCuts (2^48) 8272609281 10 Manual.Count131072.C063085.packed 64 cuts63085 = true := by
 decide +kernel
def pointBounds63085 : List (Nat × Nat × Nat) := [(8272711680,114535386154462,114535774916281)]
theorem point_links_checked63085 : (cuts63085.take 1).map (fun c => (8272609281-1+2*2^10*c.k,114535231784334+c.lower,114535620546067+c.upper)) = pointBounds63085 := by
 decide +kernel
def cuts63086 : List PrefixCut := [⟨64,194515840,194515952⟩]
theorem checked63086 : checkPrefixCuts (2^48) 8272740353 10 Manual.Count131072.C063086.packed 64 cuts63086 = true := by
 decide +kernel
def cuts63087 : List PrefixCut := [⟨49,150792776,150792865⟩,
⟨64,197166630,197166744⟩]
theorem checked63087 : checkPrefixCuts (2^48) 8272871425 10 Manual.Count131072.C063087.packed 64 cuts63087 = true := by
 decide +kernel
def pointBounds63087 : List (Nat × Nat × Nat) := [(8272971776,114535774810219,114536163572264)]
theorem point_links_checked63087 : (cuts63087.take 1).map (fun c => (8272871425-1+2*2^10*c.k,114535624017443+c.lower,114536012779399+c.upper)) = pointBounds63087 := by
 decide +kernel
def cuts63088 : List PrefixCut := [⟨64,197980057,197980167⟩]
theorem checked63088 : checkPrefixCuts (2^48) 8273002497 10 Manual.Count131072.C063088.packed 64 cuts63088 = true := by
 decide +kernel
def cuts63089 : List PrefixCut := [⟨48,146535183,146535266⟩,
⟨64,194472597,194472705⟩]
theorem checked63089 : checkPrefixCuts (2^48) 8273133569 10 Manual.Count131072.C063089.packed 64 cuts63089 = true := by
 decide +kernel
def pointBounds63089 : List (Nat × Nat × Nat) := [(8273231872,114536165699313,114536554461576)]
theorem point_links_checked63089 : (cuts63089.take 1).map (fun c => (8273133569-1+2*2^10*c.k,114536019164130+c.lower,114536407926310+c.upper)) = pointBounds63089 := by
 decide +kernel
def cuts63090 : List PrefixCut := [⟨64,196000508,196000619⟩]
theorem checked63090 : checkPrefixCuts (2^48) 8273264641 10 Manual.Count131072.C063090.packed 64 cuts63090 = true := by
 decide +kernel
def cuts63091 : List PrefixCut := [⟨47,143706775,143706861⟩,
⟨64,196405646,196405762⟩]
theorem checked63091 : checkPrefixCuts (2^48) 8273395713 10 Manual.Count131072.C063091.packed 64 cuts63091 = true := by
 decide +kernel
def pointBounds63091 : List (Nat × Nat × Nat) := [(8273491968,114536553344010,114536942106495)]
theorem point_links_checked63091 : (cuts63091.take 1).map (fun c => (8273395713-1+2*2^10*c.k,114536409637235+c.lower,114536798399634+c.upper)) = pointBounds63091 := by
 decide +kernel
def cuts63092 : List PrefixCut := [⟨64,195994299,195994411⟩]
theorem checked63092 : checkPrefixCuts (2^48) 8273526785 10 Manual.Count131072.C063092.packed 64 cuts63092 = true := by
 decide +kernel
def cuts63093 : List PrefixCut := [⟨46,138327021,138327099⟩,
⟨64,193881925,193882033⟩]
theorem checked63093 : checkPrefixCuts (2^48) 8273657857 10 Manual.Count131072.C063093.packed 64 cuts63093 = true := by
 decide +kernel
def pointBounds63093 : List (Nat × Nat × Nat) := [(8273752064,114536940364201,114537329126906)]
theorem point_links_checked63093 : (cuts63093.take 1).map (fun c => (8273657857-1+2*2^10*c.k,114536802037180+c.lower,114537190799807+c.upper)) = pointBounds63093 := by
 decide +kernel
def cuts63094 : List PrefixCut := [⟨64,193062389,193062502⟩]
theorem checked63094 : checkPrefixCuts (2^48) 8273788929 10 Manual.Count131072.C063094.packed 64 cuts63094 = true := by
 decide +kernel
def cuts63095 : List PrefixCut := [⟨45,138662846,138662924⟩,
⟨64,199522971,199523084⟩]
theorem checked63095 : checkPrefixCuts (2^48) 8273920001 10 Manual.Count131072.C063095.packed 64 cuts63095 = true := by
 decide +kernel
def pointBounds63095 : List (Nat × Nat × Nat) := [(8274012160,114537327644340,114537716407266)]
theorem point_links_checked63095 : (cuts63095.take 1).map (fun c => (8273920001-1+2*2^10*c.k,114537188981494+c.lower,114537577744342+c.upper)) = pointBounds63095 := by
 decide +kernel
def cuts63096 : List PrefixCut := [⟨64,194314941,194315051⟩]
theorem checked63096 : checkPrefixCuts (2^48) 8274051073 10 Manual.Count131072.C063096.packed 64 cuts63096 = true := by
 decide +kernel
def cuts63097 : List PrefixCut := [⟨44,134508230,134508303⟩,
⟨64,195434470,195434577⟩]
theorem checked63097 : checkPrefixCuts (2^48) 8274182145 10 Manual.Count131072.C063097.packed 64 cuts63097 = true := by
 decide +kernel
def pointBounds63097 : List (Nat × Nat × Nat) := [(8274272256,114537717327636,114538106090780)]
theorem point_links_checked63097 : (cuts63097.take 1).map (fun c => (8274182145-1+2*2^10*c.k,114537582819406+c.lower,114537971582477+c.upper)) = pointBounds63097 := by
 decide +kernel
def cuts63098 : List PrefixCut := [⟨64,197982695,197982811⟩]
theorem checked63098 : checkPrefixCuts (2^48) 8274313217 10 Manual.Count131072.C063098.packed 64 cuts63098 = true := by
 decide +kernel
def cuts63099 : List PrefixCut := [⟨43,132156809,132156884⟩,
⟨64,195156156,195156268⟩]
theorem checked63099 : checkPrefixCuts (2^48) 8274444289 10 Manual.Count131072.C063099.packed 64 cuts63099 = true := by
 decide +kernel
def pointBounds63099 : List (Nat × Nat × Nat) := [(8274532352,114538108393380,114538497156749)]
theorem point_links_checked63099 : (cuts63099.take 1).map (fun c => (8274444289-1+2*2^10*c.k,114537976236571+c.lower,114538364999865+c.upper)) = pointBounds63099 := by
 decide +kernel
def cuts63100 : List PrefixCut := [⟨64,197942412,197942528⟩]
theorem checked63100 : checkPrefixCuts (2^48) 8274575361 10 Manual.Count131072.C063100.packed 64 cuts63100 = true := by
 decide +kernel
def cuts63101 : List PrefixCut := [⟨42,125689573,125689644⟩,
⟨64,192870886,192870993⟩]
theorem checked63101 : checkPrefixCuts (2^48) 8274706433 10 Manual.Count131072.C063101.packed 64 cuts63101 = true := by
 decide +kernel
def pointBounds63101 : List (Nat × Nat × Nat) := [(8274792448,114538495024712,114538883788305)]
theorem point_links_checked63101 : (cuts63101.take 1).map (fun c => (8274706433-1+2*2^10*c.k,114538369335139+c.lower,114538758098661+c.upper)) = pointBounds63101 := by
 decide +kernel
def cuts63102 : List PrefixCut := [⟨64,193786258,193786370⟩]
theorem checked63102 : checkPrefixCuts (2^48) 8274837505 10 Manual.Count131072.C063102.packed 64 cuts63102 = true := by
 decide +kernel
def cuts63103 : List PrefixCut := [⟨41,124154922,124154996⟩,
⟨64,192626677,192626794⟩]
theorem checked63103 : checkPrefixCuts (2^48) 8274968577 10 Manual.Count131072.C063103.packed 64 cuts63103 = true := by
 decide +kernel
def pointBounds63103 : List (Nat × Nat × Nat) := [(8275052544,114538880147205,114539268911020)]
theorem point_links_checked63103 : (cuts63103.take 1).map (fun c => (8274968577-1+2*2^10*c.k,114538755992283+c.lower,114539144756024+c.upper)) = pointBounds63103 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000096
