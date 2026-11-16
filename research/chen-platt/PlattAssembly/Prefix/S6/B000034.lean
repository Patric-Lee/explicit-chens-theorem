import PlattAssemblyKernel
import PlattCertificates.Count131072.C051088
import PlattCertificates.Count131072.C051089
import PlattCertificates.Count131072.C051090
import PlattCertificates.Count131072.C051091
import PlattCertificates.Count131072.C051092
import PlattCertificates.Count131072.C051093
import PlattCertificates.Count131072.C051094
import PlattCertificates.Count131072.C051095
import PlattCertificates.Count131072.C051096
import PlattCertificates.Count131072.C051097
import PlattCertificates.Count131072.C051098
import PlattCertificates.Count131072.C051099
import PlattCertificates.Count131072.C051100
import PlattCertificates.Count131072.C051101
import PlattCertificates.Count131072.C051102
import PlattCertificates.Count131072.C051103
import PlattCertificates.Count131072.C051104
import PlattCertificates.Count131072.C051105
import PlattCertificates.Count131072.C051106
import PlattCertificates.Count131072.C051107
import PlattCertificates.Count131072.C051108
import PlattCertificates.Count131072.C051109
import PlattCertificates.Count131072.C051110
import PlattCertificates.Count131072.C051111
import PlattCertificates.Count131072.C051112
import PlattCertificates.Count131072.C051113
import PlattCertificates.Count131072.C051114
import PlattCertificates.Count131072.C051115
import PlattCertificates.Count131072.C051116
import PlattCertificates.Count131072.C051117
import PlattCertificates.Count131072.C051118
import PlattCertificates.Count131072.C051119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51088 : List PrefixCut := [⟨25,94186761,94186813⟩,
⟨64,243237317,243237452⟩]
theorem checked51088 : checkPrefixCuts (2^48) 6700138497 10 Manual.Count131072.C051088.packed 64 cuts51088 = true := by
 decide +kernel
def pointBounds51088 : List (Nat × Nat × Nat) := [(6700189696,111924751827343,111925139101792)]
theorem point_links_checked51088 : (cuts51088.take 1).map (fun c => (6700138497-1+2*2^10*c.k,111924657640582+c.lower,111925044914979+c.upper)) = pointBounds51088 := by
 decide +kernel
def cuts51089 : List PrefixCut := [⟨64,242938494,242938632⟩]
theorem checked51089 : checkPrefixCuts (2^48) 6700269569 10 Manual.Count131072.C051089.packed 64 cuts51089 = true := by
 decide +kernel
def pointBounds51089 : List (Nat × Nat × Nat) := [(6700400640,111925143816393,111925531091063)]
theorem point_links_checked51089 : (cuts51089.take 1).map (fun c => (6700269569-1+2*2^10*c.k,111924900877899+c.lower,111925288152431+c.upper)) = pointBounds51089 := by
 decide +kernel
def cuts51090 : List PrefixCut := [⟨64,245034141,245034280⟩]
theorem checked51090 : checkPrefixCuts (2^48) 6700400641 10 Manual.Count131072.C051090.packed 64 cuts51090 = true := by
 decide +kernel
def cuts51091 : List PrefixCut := [⟨39,148790895,148790977⟩,
⟨64,243727127,243727266⟩]
theorem checked51091 : checkPrefixCuts (2^48) 6700531713 10 Manual.Count131072.C051091.packed 64 cuts51091 = true := by
 decide +kernel
def pointBounds51091 : List (Nat × Nat × Nat) := [(6700611584,111925537641429,111925924916320)]
theorem point_links_checked51091 : (cuts51091.take 1).map (fun c => (6700531713-1+2*2^10*c.k,111925388850534+c.lower,111925776125343+c.upper)) = pointBounds51091 := by
 decide +kernel
def cuts51092 : List PrefixCut := [⟨64,242630204,242630343⟩]
theorem checked51092 : checkPrefixCuts (2^48) 6700662785 10 Manual.Count131072.C051092.packed 64 cuts51092 = true := by
 decide +kernel
def cuts51093 : List PrefixCut := [⟨14,53137730,53137759⟩,
⟨64,241953346,241953481⟩]
theorem checked51093 : checkPrefixCuts (2^48) 6700793857 10 Manual.Count131072.C051093.packed 64 cuts51093 = true := by
 decide +kernel
def pointBounds51093 : List (Nat × Nat × Nat) := [(6700822528,111925928345595,111926315620711)]
theorem point_links_checked51093 : (cuts51093.take 1).map (fun c => (6700793857-1+2*2^10*c.k,111925875207865+c.lower,111926262482952+c.upper)) = pointBounds51093 := by
 decide +kernel
def cuts51094 : List PrefixCut := [⟨53,199943987,199944099⟩,
⟨64,242494676,242494811⟩]
theorem checked51094 : checkPrefixCuts (2^48) 6700924929 10 Manual.Count131072.C051094.packed 64 cuts51094 = true := by
 decide +kernel
def pointBounds51094 : List (Nat × Nat × Nat) := [(6701033472,111926317105198,111926704380532)]
theorem point_links_checked51094 : (cuts51094.take 1).map (fun c => (6700924929-1+2*2^10*c.k,111926117161211+c.lower,111926504436433+c.upper)) = pointBounds51094 := by
 decide +kernel
def cuts51095 : List PrefixCut := [⟨64,243792088,243792222⟩]
theorem checked51095 : checkPrefixCuts (2^48) 6701056001 10 Manual.Count131072.C051095.packed 64 cuts51095 = true := by
 decide +kernel
def cuts51096 : List PrefixCut := [⟨28,107781126,107781184⟩,
⟨64,242359202,242359337⟩]
theorem checked51096 : checkPrefixCuts (2^48) 6701187073 10 Manual.Count131072.C051096.packed 64 cuts51096 = true := by
 decide +kernel
def pointBounds51096 : List (Nat × Nat × Nat) := [(6701244416,111926711229101,111927098504650)]
theorem point_links_checked51096 : (cuts51096.take 1).map (fun c => (6701187073-1+2*2^10*c.k,111926603447975+c.lower,111926990723466+c.upper)) = pointBounds51096 := by
 decide +kernel
def cuts51097 : List PrefixCut := [⟨64,243152488,243152625⟩]
theorem checked51097 : checkPrefixCuts (2^48) 6701318145 10 Manual.Count131072.C051097.packed 64 cuts51097 = true := by
 decide +kernel
def cuts51098 : List PrefixCut := [⟨3,11886586,11886594⟩,
⟨64,244029775,244029911⟩]
theorem checked51098 : checkPrefixCuts (2^48) 6701449217 10 Manual.Count131072.C051098.packed 64 cuts51098 = true := by
 decide +kernel
def pointBounds51098 : List (Nat × Nat × Nat) := [(6701455360,111927100846251,111927488122022)]
theorem point_links_checked51098 : (cuts51098.take 1).map (fun c => (6701449217-1+2*2^10*c.k,111927088959665+c.lower,111927476235428+c.upper)) = pointBounds51098 := by
 decide +kernel
def cuts51099 : List PrefixCut := [⟨42,161241846,161241938⟩,
⟨64,243437005,243437144⟩]
theorem checked51099 : checkPrefixCuts (2^48) 6701580289 10 Manual.Count131072.C051099.packed 64 cuts51099 = true := by
 decide +kernel
def pointBounds51099 : List (Nat × Nat × Nat) := [(6701666304,111927494231286,111927881507277)]
theorem point_links_checked51099 : (cuts51099.take 1).map (fun c => (6701580289-1+2*2^10*c.k,111927332989440+c.lower,111927720265339+c.upper)) = pointBounds51099 := by
 decide +kernel
def cuts51100 : List PrefixCut := [⟨64,242970236,242970373⟩]
theorem checked51100 : checkPrefixCuts (2^48) 6701711361 10 Manual.Count131072.C051100.packed 64 cuts51100 = true := by
 decide +kernel
def cuts51101 : List PrefixCut := [⟨17,62117286,62117322⟩,
⟨64,240277512,240277647⟩]
theorem checked51101 : checkPrefixCuts (2^48) 6701842433 10 Manual.Count131072.C051101.packed 64 cuts51101 = true := by
 decide +kernel
def pointBounds51101 : List (Nat × Nat × Nat) := [(6701877248,111927881513967,111928268790178)]
theorem point_links_checked51101 : (cuts51101.take 1).map (fun c => (6701842433-1+2*2^10*c.k,111927819396681+c.lower,111928206672856+c.upper)) = pointBounds51101 := by
 decide +kernel
def cuts51102 : List PrefixCut := [⟨56,214738054,214738173⟩,
⟨64,244556660,244556796⟩]
theorem checked51102 : checkPrefixCuts (2^48) 6701973505 10 Manual.Count131072.C051102.packed 64 cuts51102 = true := by
 decide +kernel
def pointBounds51102 : List (Nat × Nat × Nat) := [(6702088192,111928274412247,111928661688676)]
theorem point_links_checked51102 : (cuts51102.take 1).map (fun c => (6701973505-1+2*2^10*c.k,111928059674193+c.lower,111928446950503+c.upper)) = pointBounds51102 := by
 decide +kernel
def cuts51103 : List PrefixCut := [⟨64,243165958,243166093⟩]
theorem checked51103 : checkPrefixCuts (2^48) 6702104577 10 Manual.Count131072.C051103.packed 64 cuts51103 = true := by
 decide +kernel
def cuts51104 : List PrefixCut := [⟨31,117843479,117843549⟩,
⟨64,242069298,242069438⟩]
theorem checked51104 : checkPrefixCuts (2^48) 6702235649 10 Manual.Count131072.C051104.packed 64 cuts51104 = true := by
 decide +kernel
def pointBounds51104 : List (Nat × Nat × Nat) := [(6702299136,111928665240290,111929052516941)]
theorem point_links_checked51104 : (cuts51104.take 1).map (fun c => (6702235649-1+2*2^10*c.k,111928547396811+c.lower,111928934673392+c.upper)) = pointBounds51104 := by
 decide +kernel
def cuts51105 : List PrefixCut := [⟨64,241476611,241476753⟩]
theorem checked51105 : checkPrefixCuts (2^48) 6702366721 10 Manual.Count131072.C051105.packed 64 cuts51105 = true := by
 decide +kernel
def cuts51106 : List PrefixCut := [⟨6,23097517,23097529⟩,
⟨64,242857752,242857894⟩]
theorem checked51106 : checkPrefixCuts (2^48) 6702497793 10 Manual.Count131072.C051106.packed 64 cuts51106 = true := by
 decide +kernel
def pointBounds51106 : List (Nat × Nat × Nat) := [(6702510080,111929054040237,111929441317112)]
theorem point_links_checked51106 : (cuts51106.take 1).map (fun c => (6702497793-1+2*2^10*c.k,111929030942720+c.lower,111929418219583+c.upper)) = pointBounds51106 := by
 decide +kernel
def cuts51107 : List PrefixCut := [⟨45,169489458,169489555⟩,
⟨64,242726996,242727134⟩]
theorem checked51107 : checkPrefixCuts (2^48) 6702628865 10 Manual.Count131072.C051107.packed 64 cuts51107 = true := by
 decide +kernel
def pointBounds51107 : List (Nat × Nat × Nat) := [(6702721024,111929443289930,111929830567032)]
theorem point_links_checked51107 : (cuts51107.take 1).map (fun c => (6702628865-1+2*2^10*c.k,111929273800472+c.lower,111929661077477+c.upper)) = pointBounds51107 := by
 decide +kernel
def cuts51108 : List PrefixCut := [⟨64,240496602,240496742⟩]
theorem checked51108 : checkPrefixCuts (2^48) 6702759937 10 Manual.Count131072.C051108.packed 64 cuts51108 = true := by
 decide +kernel
def cuts51109 : List PrefixCut := [⟨20,75923220,75923264⟩,
⟨64,243431399,243431537⟩]
theorem checked51109 : checkPrefixCuts (2^48) 6702891009 10 Manual.Count131072.C051109.packed 64 cuts51109 = true := by
 decide +kernel
def pointBounds51109 : List (Nat × Nat × Nat) := [(6702931968,111929832947290,111930220224617)]
theorem point_links_checked51109 : (cuts51109.take 1).map (fun c => (6702891009-1+2*2^10*c.k,111929757024070+c.lower,111930144301353+c.upper)) = pointBounds51109 := by
 decide +kernel
def cuts51110 : List PrefixCut := [⟨59,225706220,225706350⟩,
⟨64,243678561,243678701⟩]
theorem checked51110 : checkPrefixCuts (2^48) 6703022081 10 Manual.Count131072.C051110.packed 64 cuts51110 = true := by
 decide +kernel
def pointBounds51110 : List (Nat × Nat × Nat) := [(6703142912,111930226161689,111930613439240)]
theorem point_links_checked51110 : (cuts51110.take 1).map (fun c => (6703022081-1+2*2^10*c.k,111930000455469+c.lower,111930387732890+c.upper)) = pointBounds51110 := by
 decide +kernel
def cuts51111 : List PrefixCut := [⟨64,244933512,244933649⟩]
theorem checked51111 : checkPrefixCuts (2^48) 6703153153 10 Manual.Count131072.C051111.packed 64 cuts51111 = true := by
 decide +kernel
def cuts51112 : List PrefixCut := [⟨34,130842014,130842088⟩,
⟨64,242913231,242913369⟩]
theorem checked51112 : checkPrefixCuts (2^48) 6703284225 10 Manual.Count131072.C051112.packed 64 cuts51112 = true := by
 decide +kernel
def pointBounds51112 : List (Nat × Nat × Nat) := [(6703353856,111930619909556,111931007187328)]
theorem point_links_checked51112 : (cuts51112.take 1).map (fun c => (6703284225-1+2*2^10*c.k,111930489067542+c.lower,111930876345240+c.upper)) = pointBounds51112 := by
 decide +kernel
def cuts51113 : List PrefixCut := [⟨64,238625585,238625718⟩]
theorem checked51113 : checkPrefixCuts (2^48) 6703415297 10 Manual.Count131072.C051113.packed 64 cuts51113 = true := by
 decide +kernel
def cuts51114 : List PrefixCut := [⟨9,33885040,33885059⟩,
⟨64,247732384,247732522⟩]
theorem checked51114 : checkPrefixCuts (2^48) 6703546369 10 Manual.Count131072.C051114.packed 64 cuts51114 = true := by
 decide +kernel
def pointBounds51114 : List (Nat × Nat × Nat) := [(6703564800,111931004491398,111931391769386)]
theorem point_links_checked51114 : (cuts51114.take 1).map (fun c => (6703546369-1+2*2^10*c.k,111930970606358+c.lower,111931357884327+c.upper)) = pointBounds51114 := by
 decide +kernel
def cuts51115 : List PrefixCut := [⟨48,180127789,180127890⟩,
⟨64,239246067,239246203⟩]
theorem checked51115 : checkPrefixCuts (2^48) 6703677441 10 Manual.Count131072.C051115.packed 64 cuts51115 = true := by
 decide +kernel
def pointBounds51115 : List (Nat × Nat × Nat) := [(6703775744,111931398466531,111931785744739)]
theorem point_links_checked51115 : (cuts51115.take 1).map (fun c => (6703677441-1+2*2^10*c.k,111931218338742+c.lower,111931605616849+c.upper)) = pointBounds51115 := by
 decide +kernel
def cuts51116 : List PrefixCut := [⟨64,242138445,242138581⟩]
theorem checked51116 : checkPrefixCuts (2^48) 6703808513 10 Manual.Count131072.C051116.packed 64 cuts51116 = true := by
 decide +kernel
def cuts51117 : List PrefixCut := [⟨23,88633171,88633222⟩,
⟨64,243855172,243855311⟩]
theorem checked51117 : checkPrefixCuts (2^48) 6703939585 10 Manual.Count131072.C051117.packed 64 cuts51117 = true := by
 decide +kernel
def pointBounds51117 : List (Nat × Nat × Nat) := [(6703986688,111931788356425,111932175634855)]
theorem point_links_checked51117 : (cuts51117.take 1).map (fun c => (6703939585-1+2*2^10*c.k,111931699723254+c.lower,111932087001633+c.upper)) = pointBounds51117 := by
 decide +kernel
def cuts51118 : List PrefixCut := [⟨62,235915254,235915385⟩,
⟨64,243472529,243472664⟩]
theorem checked51118 : checkPrefixCuts (2^48) 6704070657 10 Manual.Count131072.C051118.packed 64 cuts51118 = true := by
 decide +kernel
def pointBounds51118 : List (Nat × Nat × Nat) := [(6704197632,111932179493680,111932566772329)]
theorem point_links_checked51118 : (cuts51118.take 1).map (fun c => (6704070657-1+2*2^10*c.k,111931943578426+c.lower,111932330856944+c.upper)) = pointBounds51118 := by
 decide +kernel
def cuts51119 : List PrefixCut := [⟨64,246532635,246532773⟩]
theorem checked51119 : checkPrefixCuts (2^48) 6704201729 10 Manual.Count131072.C051119.packed 64 cuts51119 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000034
