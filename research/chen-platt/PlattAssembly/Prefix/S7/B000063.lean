import PlattAssemblyKernel
import PlattCertificates.Count131072.C062016
import PlattCertificates.Count131072.C062017
import PlattCertificates.Count131072.C062018
import PlattCertificates.Count131072.C062019
import PlattCertificates.Count131072.C062020
import PlattCertificates.Count131072.C062021
import PlattCertificates.Count131072.C062022
import PlattCertificates.Count131072.C062023
import PlattCertificates.Count131072.C062024
import PlattCertificates.Count131072.C062025
import PlattCertificates.Count131072.C062026
import PlattCertificates.Count131072.C062027
import PlattCertificates.Count131072.C062028
import PlattCertificates.Count131072.C062029
import PlattCertificates.Count131072.C062030
import PlattCertificates.Count131072.C062031
import PlattCertificates.Count131072.C062032
import PlattCertificates.Count131072.C062033
import PlattCertificates.Count131072.C062034
import PlattCertificates.Count131072.C062035
import PlattCertificates.Count131072.C062036
import PlattCertificates.Count131072.C062037
import PlattCertificates.Count131072.C062038
import PlattCertificates.Count131072.C062039
import PlattCertificates.Count131072.C062040
import PlattCertificates.Count131072.C062041
import PlattCertificates.Count131072.C062042
import PlattCertificates.Count131072.C062043
import PlattCertificates.Count131072.C062044
import PlattCertificates.Count131072.C062045
import PlattCertificates.Count131072.C062046
import PlattCertificates.Count131072.C062047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62016 : List PrefixCut := [⟨64,197801115,197801228⟩]
theorem checked62016 : checkPrefixCuts (2^48) 8132493313 10 Manual.Count131072.C062016.packed 64 cuts62016 = true := by
 decide +kernel
def cuts62017 : List PrefixCut := [⟨32,100335679,100335739⟩,
⟨64,198974658,198974776⟩]
theorem checked62017 : checkPrefixCuts (2^48) 8132624385 10 Manual.Count131072.C062017.packed 64 cuts62017 = true := by
 decide +kernel
def pointBounds62017 : List (Nat × Nat × Nat) := [(8132689920,114324858318267,114325246959085)]
theorem point_links_checked62017 : (cuts62017.take 1).map (fun c => (8132624385-1+2*2^10*c.k,114324757982588+c.lower,114325146623346+c.upper)) = pointBounds62017 := by
 decide +kernel
def cuts62018 : List PrefixCut := [⟨64,199490578,199490697⟩]
theorem checked62018 : checkPrefixCuts (2^48) 8132755457 10 Manual.Count131072.C062018.packed 64 cuts62018 = true := by
 decide +kernel
def cuts62019 : List PrefixCut := [⟨29,91610939,91610990⟩,
⟨64,200214185,200214298⟩]
theorem checked62019 : checkPrefixCuts (2^48) 8132886529 10 Manual.Count131072.C062019.packed 64 cuts62019 = true := by
 decide +kernel
def pointBounds62019 : List (Nat × Nat × Nat) := [(8132945920,114325248058763,114325636699809)]
theorem point_links_checked62019 : (cuts62019.take 1).map (fun c => (8132886529-1+2*2^10*c.k,114325156447824+c.lower,114325545088819+c.upper)) = pointBounds62019 := by
 decide +kernel
def cuts62020 : List PrefixCut := [⟨64,201110767,201110885⟩]
theorem checked62020 : checkPrefixCuts (2^48) 8133017601 10 Manual.Count131072.C062020.packed 64 cuts62020 = true := by
 decide +kernel
def cuts62021 : List PrefixCut := [⟨26,81537016,81537061⟩,
⟨64,198892622,198892731⟩]
theorem checked62021 : checkPrefixCuts (2^48) 8133148673 10 Manual.Count131072.C062021.packed 64 cuts62021 = true := by
 decide +kernel
def pointBounds62021 : List (Nat × Nat × Nat) := [(8133201920,114325639309792,114326027951063)]
theorem point_links_checked62021 : (cuts62021.take 1).map (fun c => (8133148673-1+2*2^10*c.k,114325557772776+c.lower,114325946414002+c.upper)) = pointBounds62021 := by
 decide +kernel
def cuts62022 : List PrefixCut := [⟨64,195843946,195844062⟩]
theorem checked62022 : checkPrefixCuts (2^48) 8133279745 10 Manual.Count131072.C062022.packed 64 cuts62022 = true := by
 decide +kernel
def cuts62023 : List PrefixCut := [⟨23,73021066,73021105⟩,
⟨64,199232283,199232394⟩]
theorem checked62023 : checkPrefixCuts (2^48) 8133410817 10 Manual.Count131072.C062023.packed 64 cuts62023 = true := by
 decide +kernel
def pointBounds62023 : List (Nat × Nat × Nat) := [(8133457920,114326025530410,114326414171900)]
theorem point_links_checked62023 : (cuts62023.take 1).map (fun c => (8133410817-1+2*2^10*c.k,114325952509344+c.lower,114326341150795+c.upper)) = pointBounds62023 := by
 decide +kernel
def cuts62024 : List PrefixCut := [⟨64,199332878,199332996⟩]
theorem checked62024 : checkPrefixCuts (2^48) 8133541889 10 Manual.Count131072.C062024.packed 64 cuts62024 = true := by
 decide +kernel
def cuts62025 : List PrefixCut := [⟨20,61771778,61771816⟩,
⟨64,197737802,197737922⟩]
theorem checked62025 : checkPrefixCuts (2^48) 8133672961 10 Manual.Count131072.C062025.packed 64 cuts62025 = true := by
 decide +kernel
def pointBounds62025 : List (Nat × Nat × Nat) := [(8133713920,114326412846283,114326801488001)]
theorem point_links_checked62025 : (cuts62025.take 1).map (fun c => (8133672961-1+2*2^10*c.k,114326351074505+c.lower,114326739716185+c.upper)) = pointBounds62025 := by
 decide +kernel
def cuts62026 : List PrefixCut := [⟨64,196904076,196904191⟩]
theorem checked62026 : checkPrefixCuts (2^48) 8133804033 10 Manual.Count131072.C062026.packed 64 cuts62026 = true := by
 decide +kernel
def cuts62027 : List PrefixCut := [⟨17,51907405,51907433⟩,
⟨64,197904443,197904559⟩]
theorem checked62027 : checkPrefixCuts (2^48) 8133935105 10 Manual.Count131072.C062027.packed 64 cuts62027 = true := by
 decide +kernel
def pointBounds62027 : List (Nat × Nat × Nat) := [(8133969920,114326797623788,114327186265731)]
theorem point_links_checked62027 : (cuts62027.take 1).map (fun c => (8133935105-1+2*2^10*c.k,114326745716383+c.lower,114327134358298+c.upper)) = pointBounds62027 := by
 decide +kernel
def cuts62028 : List PrefixCut := [⟨64,197762839,197762953⟩]
theorem checked62028 : checkPrefixCuts (2^48) 8134066177 10 Manual.Count131072.C062028.packed 64 cuts62028 = true := by
 decide +kernel
def cuts62029 : List PrefixCut := [⟨14,43808454,43808478⟩,
⟨64,201773665,201773775⟩]
theorem checked62029 : checkPrefixCuts (2^48) 8134197249 10 Manual.Count131072.C062029.packed 64 cuts62029 = true := by
 decide +kernel
def pointBounds62029 : List (Nat × Nat × Nat) := [(8134225920,114327185192119,114327573834288)]
theorem point_links_checked62029 : (cuts62029.take 1).map (fun c => (8134197249-1+2*2^10*c.k,114327141383665+c.lower,114327530025810+c.upper)) = pointBounds62029 := by
 decide +kernel
def cuts62030 : List PrefixCut := [⟨64,197756468,197756586⟩]
theorem checked62030 : checkPrefixCuts (2^48) 8134328321 10 Manual.Count131072.C062030.packed 64 cuts62030 = true := by
 decide +kernel
def cuts62031 : List PrefixCut := [⟨11,35363988,35364010⟩,
⟨64,197199645,197199763⟩]
theorem checked62031 : checkPrefixCuts (2^48) 8134459393 10 Manual.Count131072.C062031.packed 64 cuts62031 = true := by
 decide +kernel
def pointBounds62031 : List (Nat × Nat × Nat) := [(8134481920,114327576277786,114327964920181)]
theorem point_links_checked62031 : (cuts62031.take 1).map (fun c => (8134459393-1+2*2^10*c.k,114327540913798+c.lower,114327929556171+c.upper)) = pointBounds62031 := by
 decide +kernel
def cuts62032 : List PrefixCut := [⟨64,197784708,197784814⟩]
theorem checked62032 : checkPrefixCuts (2^48) 8134590465 10 Manual.Count131072.C062032.packed 64 cuts62032 = true := by
 decide +kernel
def cuts62033 : List PrefixCut := [⟨8,23494504,23494519⟩,
⟨64,195428615,195428731⟩]
theorem checked62033 : checkPrefixCuts (2^48) 8134721537 10 Manual.Count131072.C062033.packed 64 cuts62033 = true := by
 decide +kernel
def pointBounds62033 : List (Nat × Nat × Nat) := [(8134737920,114327959392655,114328348035267)]
theorem point_links_checked62033 : (cuts62033.take 1).map (fun c => (8134721537-1+2*2^10*c.k,114327935898151+c.lower,114328324540748+c.upper)) = pointBounds62033 := by
 decide +kernel
def cuts62034 : List PrefixCut := [⟨64,199681382,199681499⟩]
theorem checked62034 : checkPrefixCuts (2^48) 8134852609 10 Manual.Count131072.C062034.packed 64 cuts62034 = true := by
 decide +kernel
def cuts62035 : List PrefixCut := [⟨5,15777840,15777850⟩,
⟨64,201165962,201166077⟩]
theorem checked62035 : checkPrefixCuts (2^48) 8134983681 10 Manual.Count131072.C062035.packed 64 cuts62035 = true := by
 decide +kernel
def pointBounds62035 : List (Nat × Nat × Nat) := [(8134993920,114328346785988,114328735428828)]
theorem point_links_checked62035 : (cuts62035.take 1).map (fun c => (8134983681-1+2*2^10*c.k,114328331008148+c.lower,114328719650978+c.upper)) = pointBounds62035 := by
 decide +kernel
def cuts62036 : List PrefixCut := [⟨64,198671542,198671662⟩]
theorem checked62036 : checkPrefixCuts (2^48) 8135114753 10 Manual.Count131072.C062036.packed 64 cuts62036 = true := by
 decide +kernel
def cuts62037 : List PrefixCut := [⟨2,5605107,5605110⟩,
⟨64,197595770,197595882⟩]
theorem checked62037 : checkPrefixCuts (2^48) 8135245825 10 Manual.Count131072.C062037.packed 64 cuts62037 = true := by
 decide +kernel
def pointBounds62037 : List (Nat × Nat × Nat) := [(8135249920,114328736450759,114329125093827)]
theorem point_links_checked62037 : (cuts62037.take 1).map (fun c => (8135245825-1+2*2^10*c.k,114328730845652+c.lower,114329119488717+c.upper)) = pointBounds62037 := by
 decide +kernel
def cuts62038 : List PrefixCut := [⟨63,196381657,196381766⟩,
⟨64,199426309,199426420⟩]
theorem checked62038 : checkPrefixCuts (2^48) 8135376897 10 Manual.Count131072.C062038.packed 64 cuts62038 = true := by
 decide +kernel
def pointBounds62038 : List (Nat × Nat × Nat) := [(8135505920,114329124823079,114329513466365)]
theorem point_links_checked62038 : (cuts62038.take 1).map (fun c => (8135376897-1+2*2^10*c.k,114328928441422+c.lower,114329317084599+c.upper)) = pointBounds62038 := by
 decide +kernel
def cuts62039 : List PrefixCut := [⟨64,198731159,198731270⟩]
theorem checked62039 : checkPrefixCuts (2^48) 8135507969 10 Manual.Count131072.C062039.packed 64 cuts62039 = true := by
 decide +kernel
def cuts62040 : List PrefixCut := [⟨60,186445924,186446031⟩,
⟨64,198208980,198209093⟩]
theorem checked62040 : checkPrefixCuts (2^48) 8135639041 10 Manual.Count131072.C062040.packed 64 cuts62040 = true := by
 decide +kernel
def pointBounds62040 : List (Nat × Nat × Nat) := [(8135761920,114329513044814,114329901688320)]
theorem point_links_checked62040 : (cuts62040.take 1).map (fun c => (8135639041-1+2*2^10*c.k,114329326598890+c.lower,114329715242289+c.upper)) = pointBounds62040 := by
 decide +kernel
def cuts62041 : List PrefixCut := [⟨64,197583045,197583162⟩]
theorem checked62041 : checkPrefixCuts (2^48) 8135770113 10 Manual.Count131072.C062041.packed 64 cuts62041 = true := by
 decide +kernel
def cuts62042 : List PrefixCut := [⟨57,175126957,175127061⟩,
⟨64,196334378,196334494⟩]
theorem checked62042 : checkPrefixCuts (2^48) 8135901185 10 Manual.Count131072.C062042.packed 64 cuts62042 = true := by
 decide +kernel
def pointBounds62042 : List (Nat × Nat × Nat) := [(8136017920,114329897517872,114330286161605)]
theorem point_links_checked62042 : (cuts62042.take 1).map (fun c => (8135901185-1+2*2^10*c.k,114329722390915+c.lower,114330111034544+c.upper)) = pointBounds62042 := by
 decide +kernel
def cuts62043 : List PrefixCut := [⟨64,200897864,200897978⟩]
theorem checked62043 : checkPrefixCuts (2^48) 8136032257 10 Manual.Count131072.C062043.packed 64 cuts62043 = true := by
 decide +kernel
def cuts62044 : List PrefixCut := [⟨54,165434712,165434799⟩,
⟨64,196639420,196639522⟩]
theorem checked62044 : checkPrefixCuts (2^48) 8136163329 10 Manual.Count131072.C062044.packed 64 cuts62044 = true := by
 decide +kernel
def pointBounds62044 : List (Nat × Nat × Nat) := [(8136273920,114330285057869,114330673701815)]
theorem point_links_checked62044 : (cuts62044.take 1).map (fun c => (8136163329-1+2*2^10*c.k,114330119623157+c.lower,114330508267016+c.upper)) = pointBounds62044 := by
 decide +kernel
def cuts62045 : List PrefixCut := [⟨64,196117328,196117442⟩]
theorem checked62045 : checkPrefixCuts (2^48) 8136294401 10 Manual.Count131072.C062045.packed 64 cuts62045 = true := by
 decide +kernel
def cuts62046 : List PrefixCut := [⟨51,157680334,157680417⟩,
⟨64,198985473,198985577⟩]
theorem checked62046 : checkPrefixCuts (2^48) 8136425473 10 Manual.Count131072.C062046.packed 64 cuts62046 = true := by
 decide +kernel
def pointBounds62046 : List (Nat × Nat × Nat) := [(8136529920,114330670060239,114331058704397)]
theorem point_links_checked62046 : (cuts62046.take 1).map (fun c => (8136425473-1+2*2^10*c.k,114330512379905+c.lower,114330901023980+c.upper)) = pointBounds62046 := by
 decide +kernel
def cuts62047 : List PrefixCut := [⟨64,198947691,198947807⟩]
theorem checked62047 : checkPrefixCuts (2^48) 8136556545 10 Manual.Count131072.C062047.packed 64 cuts62047 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000063
