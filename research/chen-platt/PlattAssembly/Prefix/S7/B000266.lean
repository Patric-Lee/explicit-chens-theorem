import PlattAssemblyKernel
import PlattCertificates.Count131072.C068512
import PlattCertificates.Count131072.C068513
import PlattCertificates.Count131072.C068514
import PlattCertificates.Count131072.C068515
import PlattCertificates.Count131072.C068516
import PlattCertificates.Count131072.C068517
import PlattCertificates.Count131072.C068518
import PlattCertificates.Count131072.C068519
import PlattCertificates.Count131072.C068520
import PlattCertificates.Count131072.C068521
import PlattCertificates.Count131072.C068522
import PlattCertificates.Count131072.C068523
import PlattCertificates.Count131072.C068524
import PlattCertificates.Count131072.C068525
import PlattCertificates.Count131072.C068526
import PlattCertificates.Count131072.C068527
import PlattCertificates.Count131072.C068528
import PlattCertificates.Count131072.C068529
import PlattCertificates.Count131072.C068530
import PlattCertificates.Count131072.C068531
import PlattCertificates.Count131072.C068532
import PlattCertificates.Count131072.C068533
import PlattCertificates.Count131072.C068534
import PlattCertificates.Count131072.C068535
import PlattCertificates.Count131072.C068536
import PlattCertificates.Count131072.C068537
import PlattCertificates.Count131072.C068538
import PlattCertificates.Count131072.C068539
import PlattCertificates.Count131072.C068540
import PlattCertificates.Count131072.C068541
import PlattCertificates.Count131072.C068542
import PlattCertificates.Count131072.C068543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000266
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68512 : List PrefixCut := [⟨64,177738928,177739036⟩]
theorem checked68512 : checkPrefixCuts (2^48) 8983937025 10 Manual.Count131072.C068512.packed 64 cuts68512 = true := by
 decide +kernel
def cuts68513 : List PrefixCut := [⟨21,58995095,58995130⟩,
⟨64,181245331,181245438⟩]
theorem checked68513 : checkPrefixCuts (2^48) 8984068097 10 Manual.Count131072.C068513.packed 64 cuts68513 = true := by
 decide +kernel
def pointBounds68513 : List (Nat × Nat × Nat) := [(8984111104,115550338019230,115550727369705)]
theorem point_links_checked68513 : (cuts68513.take 1).map (fun c => (8984068097-1+2*2^10*c.k,115550279024135+c.lower,115550668374575+c.upper)) = pointBounds68513 := by
 decide +kernel
def cuts68514 : List PrefixCut := [⟨64,178141036,178141135⟩]
theorem checked68514 : checkPrefixCuts (2^48) 8984199169 10 Manual.Count131072.C068514.packed 64 cuts68514 = true := by
 decide +kernel
def cuts68515 : List PrefixCut := [⟨31,86061930,86061979⟩,
⟨64,180112176,180112277⟩]
theorem checked68515 : checkPrefixCuts (2^48) 8984330241 10 Manual.Count131072.C068515.packed 64 cuts68515 = true := by
 decide +kernel
def pointBounds68515 : List (Nat × Nat × Nat) := [(8984393728,115550724472432,115551113823127)]
theorem point_links_checked68515 : (cuts68515.take 1).map (fun c => (8984330241-1+2*2^10*c.k,115550638410502+c.lower,115551027761148+c.upper)) = pointBounds68515 := by
 decide +kernel
def cuts68516 : List PrefixCut := [⟨64,178762415,178762518⟩]
theorem checked68516 : checkPrefixCuts (2^48) 8984461313 10 Manual.Count131072.C068516.packed 64 cuts68516 = true := by
 decide +kernel
def cuts68517 : List PrefixCut := [⟨41,114442923,114442986⟩,
⟨64,179261065,179261167⟩]
theorem checked68517 : checkPrefixCuts (2^48) 8984592385 10 Manual.Count131072.C068517.packed 64 cuts68517 = true := by
 decide +kernel
def pointBounds68517 : List (Nat × Nat × Nat) := [(8984676352,115551111728016,115551501078929)]
theorem point_links_checked68517 : (cuts68517.take 1).map (fun c => (8984592385-1+2*2^10*c.k,115550997285093+c.lower,115551386635943+c.upper)) = pointBounds68517 := by
 decide +kernel
def cuts68518 : List PrefixCut := [⟨64,180135636,180135741⟩]
theorem checked68518 : checkPrefixCuts (2^48) 8984723457 10 Manual.Count131072.C068518.packed 64 cuts68518 = true := by
 decide +kernel
def cuts68519 : List PrefixCut := [⟨51,140034040,140034121⟩,
⟨64,176874940,176875046⟩]
theorem checked68519 : checkPrefixCuts (2^48) 8984854529 10 Manual.Count131072.C068519.packed 64 cuts68519 = true := by
 decide +kernel
def pointBounds68519 : List (Nat × Nat × Nat) := [(8984958976,115551496715834,115551886066972)]
theorem point_links_checked68519 : (cuts68519.take 1).map (fun c => (8984854529-1+2*2^10*c.k,115551356681794+c.lower,115551746032851+c.upper)) = pointBounds68519 := by
 decide +kernel
def cuts68520 : List PrefixCut := [⟨64,178250751,178250859⟩]
theorem checked68520 : checkPrefixCuts (2^48) 8984985601 10 Manual.Count131072.C068520.packed 64 cuts68520 = true := by
 decide +kernel
def cuts68521 : List PrefixCut := [⟨61,171262402,171262497⟩,
⟨64,180253064,180253164⟩]
theorem checked68521 : checkPrefixCuts (2^48) 8985116673 10 Manual.Count131072.C068521.packed 64 cuts68521 = true := by
 decide +kernel
def pointBounds68521 : List (Nat × Nat × Nat) := [(8985241600,115551883069887,115552272421253)]
theorem point_links_checked68521 : (cuts68521.take 1).map (fun c => (8985116673-1+2*2^10*c.k,115551711807485+c.lower,115552101158756+c.upper)) = pointBounds68521 := by
 decide +kernel
def cuts68522 : List PrefixCut := [⟨64,178621472,178621578⟩]
theorem checked68522 : checkPrefixCuts (2^48) 8985247745 10 Manual.Count131072.C068522.packed 64 cuts68522 = true := by
 decide +kernel
def cuts68523 : List PrefixCut := [⟨64,178524887,178524991⟩]
theorem checked68523 : checkPrefixCuts (2^48) 8985378817 10 Manual.Count131072.C068523.packed 64 cuts68523 = true := by
 decide +kernel
def cuts68524 : List PrefixCut := [⟨7,19641024,19641036⟩,
⟨64,181842753,181842858⟩]
theorem checked68524 : checkPrefixCuts (2^48) 8985509889 10 Manual.Count131072.C068524.packed 64 cuts68524 = true := by
 decide +kernel
def pointBounds68524 : List (Nat × Nat × Nat) := [(8985524224,115552268847932,115552658199525)]
theorem point_links_checked68524 : (cuts68524.take 1).map (fun c => (8985509889-1+2*2^10*c.k,115552249206908+c.lower,115552638558489+c.upper)) = pointBounds68524 := by
 decide +kernel
def cuts68525 : List PrefixCut := [⟨64,179083527,179083635⟩]
theorem checked68525 : checkPrefixCuts (2^48) 8985640961 10 Manual.Count131072.C068525.packed 64 cuts68525 = true := by
 decide +kernel
def cuts68526 : List PrefixCut := [⟨17,47331244,47331270⟩,
⟨64,178266486,178266586⟩]
theorem checked68526 : checkPrefixCuts (2^48) 8985772033 10 Manual.Count131072.C068526.packed 64 cuts68526 = true := by
 decide +kernel
def pointBounds68526 : List (Nat × Nat × Nat) := [(8985806848,115552657464432,115553046816252)]
theorem point_links_checked68526 : (cuts68526.take 1).map (fun c => (8985772033-1+2*2^10*c.k,115552610133188+c.lower,115552999484982+c.upper)) = pointBounds68526 := by
 decide +kernel
def cuts68527 : List PrefixCut := [⟨64,180111973,180112075⟩]
theorem checked68527 : checkPrefixCuts (2^48) 8985903105 10 Manual.Count131072.C068527.packed 64 cuts68527 = true := by
 decide +kernel
def cuts68528 : List PrefixCut := [⟨27,75333014,75333060⟩,
⟨64,178699805,178699915⟩]
theorem checked68528 : checkPrefixCuts (2^48) 8986034177 10 Manual.Count131072.C068528.packed 64 cuts68528 = true := by
 decide +kernel
def pointBounds68528 : List (Nat × Nat × Nat) := [(8986089472,115553043844661,115553433196703)]
theorem point_links_checked68528 : (cuts68528.take 1).map (fun c => (8986034177-1+2*2^10*c.k,115552968511647+c.lower,115553357863643+c.upper)) = pointBounds68528 := by
 decide +kernel
def cuts68529 : List PrefixCut := [⟨64,177318993,177319095⟩]
theorem checked68529 : checkPrefixCuts (2^48) 8986165249 10 Manual.Count131072.C068529.packed 64 cuts68529 = true := by
 decide +kernel
def cuts68530 : List PrefixCut := [⟨37,101171837,101171896⟩,
⟨64,176971850,176971955⟩]
theorem checked68530 : checkPrefixCuts (2^48) 8986296321 10 Manual.Count131072.C068530.packed 64 cuts68530 = true := by
 decide +kernel
def pointBounds68530 : List (Nat × Nat × Nat) := [(8986372096,115553425702282,115553815054549)]
theorem point_links_checked68530 : (cuts68530.take 1).map (fun c => (8986296321-1+2*2^10*c.k,115553324530445+c.lower,115553713882653+c.upper)) = pointBounds68530 := by
 decide +kernel
def cuts68531 : List PrefixCut := [⟨64,179725614,179725720⟩]
theorem checked68531 : checkPrefixCuts (2^48) 8986427393 10 Manual.Count131072.C068531.packed 64 cuts68531 = true := by
 decide +kernel
def cuts68532 : List PrefixCut := [⟨47,128825746,128825824⟩,
⟨64,177687085,177687192⟩]
theorem checked68532 : checkPrefixCuts (2^48) 8986558465 10 Manual.Count131072.C068532.packed 64 cuts68532 = true := by
 decide +kernel
def pointBounds68532 : List (Nat × Nat × Nat) := [(8986654720,115553810053655,115554199406152)]
theorem point_links_checked68532 : (cuts68532.take 1).map (fun c => (8986558465-1+2*2^10*c.k,115553681227909+c.lower,115554070580328+c.upper)) = pointBounds68532 := by
 decide +kernel
def cuts68533 : List PrefixCut := [⟨64,178498840,178498946⟩]
theorem checked68533 : checkPrefixCuts (2^48) 8986689537 10 Manual.Count131072.C068533.packed 64 cuts68533 = true := by
 decide +kernel
def cuts68534 : List PrefixCut := [⟨57,159954559,159954656⟩,
⟨64,179373222,179373329⟩]
theorem checked68534 : checkPrefixCuts (2^48) 8986820609 10 Manual.Count131072.C068534.packed 64 cuts68534 = true := by
 decide +kernel
def pointBounds68534 : List (Nat × Nat × Nat) := [(8986937344,115554197368393,115554586721122)]
theorem point_links_checked68534 : (cuts68534.take 1).map (fun c => (8986820609-1+2*2^10*c.k,115554037413834+c.lower,115554426766466+c.upper)) = pointBounds68534 := by
 decide +kernel
def cuts68535 : List PrefixCut := [⟨64,175079739,175079842⟩]
theorem checked68535 : checkPrefixCuts (2^48) 8986951681 10 Manual.Count131072.C068535.packed 64 cuts68535 = true := by
 decide +kernel
def cuts68536 : List PrefixCut := [⟨64,178741612,178741710⟩]
theorem checked68536 : checkPrefixCuts (2^48) 8987082753 10 Manual.Count131072.C068536.packed 64 cuts68536 = true := by
 decide +kernel
def cuts68537 : List PrefixCut := [⟨3,7986466,7986470⟩,
⟨64,180085711,180085816⟩]
theorem checked68537 : checkPrefixCuts (2^48) 8987213825 10 Manual.Count131072.C068537.packed 64 cuts68537 = true := by
 decide +kernel
def pointBounds68537 : List (Nat × Nat × Nat) := [(8987219968,115554578594873,115554967947817)]
theorem point_links_checked68537 : (cuts68537.take 1).map (fun c => (8987213825-1+2*2^10*c.k,115554570608407+c.lower,115554959961347+c.upper)) = pointBounds68537 := by
 decide +kernel
def cuts68538 : List PrefixCut := [⟨64,177139125,177139226⟩]
theorem checked68538 : checkPrefixCuts (2^48) 8987344897 10 Manual.Count131072.C068538.packed 64 cuts68538 = true := by
 decide +kernel
def cuts68539 : List PrefixCut := [⟨13,36642672,36642693⟩,
⟨64,176572810,176572914⟩]
theorem checked68539 : checkPrefixCuts (2^48) 8987475969 10 Manual.Count131072.C068539.packed 64 cuts68539 = true := by
 decide +kernel
def pointBounds68539 : List (Nat × Nat × Nat) := [(8987502592,115554964475915,115555353829082)]
theorem point_links_checked68539 : (cuts68539.take 1).map (fun c => (8987475969-1+2*2^10*c.k,115554927833243+c.lower,115555317186389+c.upper)) = pointBounds68539 := by
 decide +kernel
def cuts68540 : List PrefixCut := [⟨64,180735505,180735609⟩]
theorem checked68540 : checkPrefixCuts (2^48) 8987607041 10 Manual.Count131072.C068540.packed 64 cuts68540 = true := by
 decide +kernel
def cuts68541 : List PrefixCut := [⟨23,64169707,64169747⟩,
⟨64,181390534,181390645⟩]
theorem checked68541 : checkPrefixCuts (2^48) 8987738113 10 Manual.Count131072.C068541.packed 64 cuts68541 = true := by
 decide +kernel
def pointBounds68541 : List (Nat × Nat × Nat) := [(8987785216,115555349311265,115555738664659)]
theorem point_links_checked68541 : (cuts68541.take 1).map (fun c => (8987738113-1+2*2^10*c.k,115555285141558+c.lower,115555674494912+c.upper)) = pointBounds68541 := by
 decide +kernel
def cuts68542 : List PrefixCut := [⟨64,181262641,181262746⟩]
theorem checked68542 : checkPrefixCuts (2^48) 8987869185 10 Manual.Count131072.C068542.packed 64 cuts68542 = true := by
 decide +kernel
def cuts68543 : List PrefixCut := [⟨33,95014642,95014702⟩,
⟨64,180821570,180821683⟩]
theorem checked68543 : checkPrefixCuts (2^48) 8988000257 10 Manual.Count131072.C068543.packed 64 cuts68543 = true := by
 decide +kernel
def pointBounds68543 : List (Nat × Nat × Nat) := [(8988067840,115555742809375,115556132163005)]
theorem point_links_checked68543 : (cuts68543.take 1).map (fun c => (8988000257-1+2*2^10*c.k,115555647794733+c.lower,115556037148303+c.upper)) = pointBounds68543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000266
