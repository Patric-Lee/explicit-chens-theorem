import PlattAssemblyKernel
import PlattCertificates.Count131072.C070096
import PlattCertificates.Count131072.C070097
import PlattCertificates.Count131072.C070098
import PlattCertificates.Count131072.C070099
import PlattCertificates.Count131072.C070100
import PlattCertificates.Count131072.C070101
import PlattCertificates.Count131072.C070102
import PlattCertificates.Count131072.C070103
import PlattCertificates.Count131072.C070104
import PlattCertificates.Count131072.C070105
import PlattCertificates.Count131072.C070106
import PlattCertificates.Count131072.C070107
import PlattCertificates.Count131072.C070108
import PlattCertificates.Count131072.C070109
import PlattCertificates.Count131072.C070110
import PlattCertificates.Count131072.C070111
import PlattCertificates.Count131072.C070112
import PlattCertificates.Count131072.C070113
import PlattCertificates.Count131072.C070114
import PlattCertificates.Count131072.C070115
import PlattCertificates.Count131072.C070116
import PlattCertificates.Count131072.C070117
import PlattCertificates.Count131072.C070118
import PlattCertificates.Count131072.C070119
import PlattCertificates.Count131072.C070120
import PlattCertificates.Count131072.C070121
import PlattCertificates.Count131072.C070122
import PlattCertificates.Count131072.C070123
import PlattCertificates.Count131072.C070124
import PlattCertificates.Count131072.C070125
import PlattCertificates.Count131072.C070126
import PlattCertificates.Count131072.C070127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70096 : List PrefixCut := [⟨31,85622190,85622242⟩,
⟨64,175592226,175592332⟩]
theorem checked70096 : checkPrefixCuts (2^48) 9191555073 10 Manual.Count131072.C070096.packed 64 cuts70096 = true := by
 decide +kernel
def pointBounds70096 : List (Nat × Nat × Nat) := [(9191618560,115830606324460,115830995839589)]
theorem point_links_checked70096 : (cuts70096.take 1).map (fun c => (9191555073-1+2*2^10*c.k,115830520702270+c.lower,115830910217347+c.upper)) = pointBounds70096 := by
 decide +kernel
def cuts70097 : List PrefixCut := [⟨64,172251859,172251957⟩]
theorem checked70097 : checkPrefixCuts (2^48) 9191686145 10 Manual.Count131072.C070097.packed 64 cuts70097 = true := by
 decide +kernel
def cuts70098 : List PrefixCut := [⟨44,120590162,120590233⟩,
⟨64,175801563,175801665⟩]
theorem checked70098 : checkPrefixCuts (2^48) 9191817217 10 Manual.Count131072.C070098.packed 64 cuts70098 = true := by
 decide +kernel
def pointBounds70098 : List (Nat × Nat × Nat) := [(9191907328,115830989136517,115831378651869)]
theorem point_links_checked70098 : (cuts70098.take 1).map (fun c => (9191817217-1+2*2^10*c.k,115830868546355+c.lower,115831258061636+c.upper)) = pointBounds70098 := by
 decide +kernel
def cuts70099 : List PrefixCut := [⟨64,175707203,175707308⟩]
theorem checked70099 : checkPrefixCuts (2^48) 9191948289 10 Manual.Count131072.C070099.packed 64 cuts70099 = true := by
 decide +kernel
def cuts70100 : List PrefixCut := [⟨57,156260322,156260406⟩,
⟨64,175214750,175214846⟩]
theorem checked70100 : checkPrefixCuts (2^48) 9192079361 10 Manual.Count131072.C070100.packed 64 cuts70100 = true := by
 decide +kernel
def pointBounds70100 : List (Nat × Nat × Nat) := [(9192196096,115831376315443,115831765831015)]
theorem point_links_checked70100 : (cuts70100.take 1).map (fun c => (9192079361-1+2*2^10*c.k,115831220055121+c.lower,115831609570609+c.upper)) = pointBounds70100 := by
 decide +kernel
def cuts70101 : List PrefixCut := [⟨64,172456374,172456475⟩]
theorem checked70101 : checkPrefixCuts (2^48) 9192210433 10 Manual.Count131072.C070101.packed 64 cuts70101 = true := by
 decide +kernel
def cuts70102 : List PrefixCut := [⟨64,173984933,173985032⟩]
theorem checked70102 : checkPrefixCuts (2^48) 9192341505 10 Manual.Count131072.C070102.packed 64 cuts70102 = true := by
 decide +kernel
def cuts70103 : List PrefixCut := [⟨6,15738746,15738757⟩,
⟨64,171594099,171594201⟩]
theorem checked70103 : checkPrefixCuts (2^48) 9192472577 10 Manual.Count131072.C070103.packed 64 cuts70103 = true := by
 decide +kernel
def pointBounds70103 : List (Nat × Nat × Nat) := [(9192484864,115831757449924,115832146965719)]
theorem point_links_checked70103 : (cuts70103.take 1).map (fun c => (9192472577-1+2*2^10*c.k,115831741711178+c.lower,115832131226962+c.upper)) = pointBounds70103 := by
 decide +kernel
def cuts70104 : List PrefixCut := [⟨64,176950072,176950168⟩]
theorem checked70104 : checkPrefixCuts (2^48) 9192603649 10 Manual.Count131072.C070104.packed 64 cuts70104 = true := by
 decide +kernel
def cuts70105 : List PrefixCut := [⟨19,49756223,49756249⟩,
⟨64,172262822,172262919⟩]
theorem checked70105 : checkPrefixCuts (2^48) 9192734721 10 Manual.Count131072.C070105.packed 64 cuts70105 = true := by
 decide +kernel
def pointBounds70105 : List (Nat × Nat × Nat) := [(9192773632,115832140011572,115832529527580)]
theorem point_links_checked70105 : (cuts70105.take 1).map (fun c => (9192734721-1+2*2^10*c.k,115832090255349+c.lower,115832479771331+c.upper)) = pointBounds70105 := by
 decide +kernel
def cuts70106 : List PrefixCut := [⟨64,175781519,175781614⟩]
theorem checked70106 : checkPrefixCuts (2^48) 9192865793 10 Manual.Count131072.C070106.packed 64 cuts70106 = true := by
 decide +kernel
def cuts70107 : List PrefixCut := [⟨32,88609350,88609402⟩,
⟨64,177585480,177585582⟩]
theorem checked70107 : checkPrefixCuts (2^48) 9192996865 10 Manual.Count131072.C070107.packed 64 cuts70107 = true := by
 decide +kernel
def pointBounds70107 : List (Nat × Nat × Nat) := [(9193062400,115832526909040,115832916425266)]
theorem point_links_checked70107 : (cuts70107.take 1).map (fun c => (9192996865-1+2*2^10*c.k,115832438299690+c.lower,115832827815864+c.upper)) = pointBounds70107 := by
 decide +kernel
def cuts70108 : List PrefixCut := [⟨64,172531024,172531131⟩]
theorem checked70108 : checkPrefixCuts (2^48) 9193127937 10 Manual.Count131072.C070108.packed 64 cuts70108 = true := by
 decide +kernel
def cuts70109 : List PrefixCut := [⟨45,122775682,122775753⟩,
⟨64,172957203,172957309⟩]
theorem checked70109 : checkPrefixCuts (2^48) 9193259009 10 Manual.Count131072.C070109.packed 64 cuts70109 = true := by
 decide +kernel
def pointBounds70109 : List (Nat × Nat × Nat) := [(9193351168,115832911191876,115833300708330)]
theorem point_links_checked70109 : (cuts70109.take 1).map (fun c => (9193259009-1+2*2^10*c.k,115832788416194+c.lower,115833177932577+c.upper)) = pointBounds70109 := by
 decide +kernel
def cuts70110 : List PrefixCut := [⟨64,176383823,176383923⟩]
theorem checked70110 : checkPrefixCuts (2^48) 9193390081 10 Manual.Count131072.C070110.packed 64 cuts70110 = true := by
 decide +kernel
def cuts70111 : List PrefixCut := [⟨58,158409550,158409640⟩,
⟨64,175003553,175003654⟩]
theorem checked70111 : checkPrefixCuts (2^48) 9193521153 10 Manual.Count131072.C070111.packed 64 cuts70111 = true := by
 decide +kernel
def pointBounds70111 : List (Nat × Nat × Nat) := [(9193639936,115833296166770,115833685683449)]
theorem point_links_checked70111 : (cuts70111.take 1).map (fun c => (9193521153-1+2*2^10*c.k,115833137757220+c.lower,115833527273809+c.upper)) = pointBounds70111 := by
 decide +kernel
def cuts70112 : List PrefixCut := [⟨64,174021367,174021469⟩]
theorem checked70112 : checkPrefixCuts (2^48) 9193652225 10 Manual.Count131072.C070112.packed 64 cuts70112 = true := by
 decide +kernel
def cuts70113 : List PrefixCut := [⟨64,173590264,173590364⟩]
theorem checked70113 : checkPrefixCuts (2^48) 9193783297 10 Manual.Count131072.C070113.packed 64 cuts70113 = true := by
 decide +kernel
def cuts70114 : List PrefixCut := [⟨7,19103963,19103974⟩,
⟨64,174445028,174445129⟩]
theorem checked70114 : checkPrefixCuts (2^48) 9193914369 10 Manual.Count131072.C070114.packed 64 cuts70114 = true := by
 decide +kernel
def pointBounds70114 : List (Nat × Nat × Nat) := [(9193928704,115833679476367,115834068993270)]
theorem point_links_checked70114 : (cuts70114.take 1).map (fun c => (9193914369-1+2*2^10*c.k,115833660372404+c.lower,115834049889296+c.upper)) = pointBounds70114 := by
 decide +kernel
def cuts70115 : List PrefixCut := [⟨64,172758716,172758822⟩]
theorem checked70115 : checkPrefixCuts (2^48) 9194045441 10 Manual.Count131072.C070115.packed 64 cuts70115 = true := by
 decide +kernel
def cuts70116 : List PrefixCut := [⟨20,54861019,54861051⟩,
⟨64,174991090,174991195⟩]
theorem checked70116 : checkPrefixCuts (2^48) 9194176513 10 Manual.Count131072.C070116.packed 64 cuts70116 = true := by
 decide +kernel
def pointBounds70116 : List (Nat × Nat × Nat) := [(9194217472,115834062437167,115834451954298)]
theorem point_links_checked70116 : (cuts70116.take 1).map (fun c => (9194176513-1+2*2^10*c.k,115834007576148+c.lower,115834397093247+c.upper)) = pointBounds70116 := by
 decide +kernel
def cuts70117 : List PrefixCut := [⟨64,176274388,176274487⟩]
theorem checked70117 : checkPrefixCuts (2^48) 9194307585 10 Manual.Count131072.C070117.packed 64 cuts70117 = true := by
 decide +kernel
def cuts70118 : List PrefixCut := [⟨33,91656789,91656842⟩,
⟨64,177894378,177894476⟩]
theorem checked70118 : checkPrefixCuts (2^48) 9194438657 10 Manual.Count131072.C070118.packed 64 cuts70118 = true := by
 decide +kernel
def pointBounds70118 : List (Nat × Nat × Nat) := [(9194506240,115834450498415,115834840015771)]
theorem point_links_checked70118 : (cuts70118.take 1).map (fun c => (9194438657-1+2*2^10*c.k,115834358841626+c.lower,115834748358929+c.upper)) = pointBounds70118 := by
 decide +kernel
def cuts70119 : List PrefixCut := [⟨64,177555097,177555198⟩]
theorem checked70119 : checkPrefixCuts (2^48) 9194569729 10 Manual.Count131072.C070119.packed 64 cuts70119 = true := by
 decide +kernel
def cuts70120 : List PrefixCut := [⟨46,125787070,125787133⟩,
⟨64,174705611,174705704⟩]
theorem checked70120 : checkPrefixCuts (2^48) 9194700801 10 Manual.Count131072.C070120.packed 64 cuts70120 = true := by
 decide +kernel
def pointBounds70120 : List (Nat × Nat × Nat) := [(9194795008,115834840078171,115835229595736)]
theorem point_links_checked70120 : (cuts70120.take 1).map (fun c => (9194700801-1+2*2^10*c.k,115834714291101+c.lower,115835103808603+c.upper)) = pointBounds70120 := by
 decide +kernel
def cuts70121 : List PrefixCut := [⟨64,176111269,176111374⟩]
theorem checked70121 : checkPrefixCuts (2^48) 9194831873 10 Manual.Count131072.C070121.packed 64 cuts70121 = true := by
 decide +kernel
def cuts70122 : List PrefixCut := [⟨59,158660212,158660310⟩,
⟨64,172374135,172374243⟩]
theorem checked70122 : checkPrefixCuts (2^48) 9194962945 10 Manual.Count131072.C070122.packed 64 cuts70122 = true := by
 decide +kernel
def pointBounds70122 : List (Nat × Nat × Nat) := [(9195083776,115835223768193,115835613285991)]
theorem point_links_checked70122 : (cuts70122.take 1).map (fun c => (9194962945-1+2*2^10*c.k,115835065107981+c.lower,115835454625681+c.upper)) = pointBounds70122 := by
 decide +kernel
def cuts70123 : List PrefixCut := [⟨64,175708289,175708390⟩]
theorem checked70123 : checkPrefixCuts (2^48) 9195094017 10 Manual.Count131072.C070123.packed 64 cuts70123 = true := by
 decide +kernel
def cuts70124 : List PrefixCut := [⟨64,174267097,174267204⟩]
theorem checked70124 : checkPrefixCuts (2^48) 9195225089 10 Manual.Count131072.C070124.packed 64 cuts70124 = true := by
 decide +kernel
def cuts70125 : List PrefixCut := [⟨8,21243702,21243713⟩,
⟨64,175305353,175305450⟩]
theorem checked70125 : checkPrefixCuts (2^48) 9195356161 10 Manual.Count131072.C070125.packed 64 cuts70125 = true := by
 decide +kernel
def pointBounds70125 : List (Nat × Nat × Nat) := [(9195372544,115835608701204,115835998219231)]
theorem point_links_checked70125 : (cuts70125.take 1).map (fun c => (9195356161-1+2*2^10*c.k,115835587457502+c.lower,115835976975518+c.upper)) = pointBounds70125 := by
 decide +kernel
def cuts70126 : List PrefixCut := [⟨64,175302849,175302952⟩]
theorem checked70126 : checkPrefixCuts (2^48) 9195487233 10 Manual.Count131072.C070126.packed 64 cuts70126 = true := by
 decide +kernel
def cuts70127 : List PrefixCut := [⟨21,58250074,58250113⟩,
⟨64,174963668,174963775⟩]
theorem checked70127 : checkPrefixCuts (2^48) 9195618305 10 Manual.Count131072.C070127.packed 64 cuts70127 = true := by
 decide +kernel
def pointBounds70127 : List (Nat × Nat × Nat) := [(9195661312,115835996315778,115836385834033)]
theorem point_links_checked70127 : (cuts70127.take 1).map (fun c => (9195618305-1+2*2^10*c.k,115835938065704+c.lower,115836327583920+c.upper)) = pointBounds70127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000003
