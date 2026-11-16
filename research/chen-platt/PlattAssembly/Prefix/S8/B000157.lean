import PlattAssemblyKernel
import PlattCertificates.Count131072.C075024
import PlattCertificates.Count131072.C075025
import PlattCertificates.Count131072.C075026
import PlattCertificates.Count131072.C075027
import PlattCertificates.Count131072.C075028
import PlattCertificates.Count131072.C075029
import PlattCertificates.Count131072.C075030
import PlattCertificates.Count131072.C075031
import PlattCertificates.Count131072.C075032
import PlattCertificates.Count131072.C075033
import PlattCertificates.Count131072.C075034
import PlattCertificates.Count131072.C075035
import PlattCertificates.Count131072.C075036
import PlattCertificates.Count131072.C075037
import PlattCertificates.Count131072.C075038
import PlattCertificates.Count131072.C075039
import PlattCertificates.Count131072.C075040
import PlattCertificates.Count131072.C075041
import PlattCertificates.Count131072.C075042
import PlattCertificates.Count131072.C075043
import PlattCertificates.Count131072.C075044
import PlattCertificates.Count131072.C075045
import PlattCertificates.Count131072.C075046
import PlattCertificates.Count131072.C075047
import PlattCertificates.Count131072.C075048
import PlattCertificates.Count131072.C075049
import PlattCertificates.Count131072.C075050
import PlattCertificates.Count131072.C075051
import PlattCertificates.Count131072.C075052
import PlattCertificates.Count131072.C075053
import PlattCertificates.Count131072.C075054
import PlattCertificates.Count131072.C075055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75024 : List PrefixCut := [⟨48,122775650,122775732⟩,
⟨64,162632406,162632509⟩]
theorem checked75024 : checkPrefixCuts (2^48) 9837477889 10 Manual.Count131072.C075024.packed 64 cuts75024 = true := by
 decide +kernel
def pointBounds75024 : List (Nat × Nat × Nat) := [(9837576192,116662760099670,116663150109487)]
theorem point_links_checked75024 : (cuts75024.take 1).map (fun c => (9837477889-1+2*2^10*c.k,116662637324020+c.lower,116663027333755+c.upper)) = pointBounds75024 := by
 decide +kernel
def cuts75025 : List PrefixCut := [⟨64,163059406,163059500⟩]
theorem checked75025 : checkPrefixCuts (2^48) 9837608961 10 Manual.Count131072.C075025.packed 64 cuts75025 = true := by
 decide +kernel
def cuts75026 : List PrefixCut := [⟨64,163371976,163372072⟩]
theorem checked75026 : checkPrefixCuts (2^48) 9837740033 10 Manual.Count131072.C075026.packed 64 cuts75026 = true := by
 decide +kernel
def cuts75027 : List PrefixCut := [⟨7,18254035,18254048⟩,
⟨64,164285347,164285444⟩]
theorem checked75027 : checkPrefixCuts (2^48) 9837871105 10 Manual.Count131072.C075027.packed 64 cuts75027 = true := by
 decide +kernel
def pointBounds75027 : List (Nat × Nat × Nat) := [(9837885440,116663144641843,116663534651884)]
theorem point_links_checked75027 : (cuts75027.take 1).map (fun c => (9837871105-1+2*2^10*c.k,116663126387808+c.lower,116663516397836+c.upper)) = pointBounds75027 := by
 decide +kernel
def cuts75028 : List PrefixCut := [⟨64,161794032,161794123⟩]
theorem checked75028 : checkPrefixCuts (2^48) 9838002177 10 Manual.Count131072.C075028.packed 64 cuts75028 = true := by
 decide +kernel
def cuts75029 : List PrefixCut := [⟨30,76161182,76161228⟩,
⟨64,163508484,163508581⟩]
theorem checked75029 : checkPrefixCuts (2^48) 9838133249 10 Manual.Count131072.C075029.packed 64 cuts75029 = true := by
 decide +kernel
def pointBounds75029 : List (Nat × Nat × Nat) := [(9838194688,116663528628369,116663918638631)]
theorem point_links_checked75029 : (cuts75029.take 1).map (fun c => (9838133249-1+2*2^10*c.k,116663452467187+c.lower,116663842477403+c.upper)) = pointBounds75029 := by
 decide +kernel
def cuts75030 : List PrefixCut := [⟨64,163649368,163649461⟩]
theorem checked75030 : checkPrefixCuts (2^48) 9838264321 10 Manual.Count131072.C075030.packed 64 cuts75030 = true := by
 decide +kernel
def cuts75031 : List PrefixCut := [⟨53,134637143,134637224⟩,
⟨64,162931927,162932026⟩]
theorem checked75031 : checkPrefixCuts (2^48) 9838395393 10 Manual.Count131072.C075031.packed 64 cuts75031 = true := by
 decide +kernel
def pointBounds75031 : List (Nat × Nat × Nat) := [(9838503936,116663914262182,116664304272669)]
theorem point_links_checked75031 : (cuts75031.take 1).map (fun c => (9838395393-1+2*2^10*c.k,116663779625039+c.lower,116664169635445+c.upper)) = pointBounds75031 := by
 decide +kernel
def cuts75032 : List PrefixCut := [⟨64,162729514,162729608⟩]
theorem checked75032 : checkPrefixCuts (2^48) 9838526465 10 Manual.Count131072.C075032.packed 64 cuts75032 = true := by
 decide +kernel
def cuts75033 : List PrefixCut := [⟨64,162870379,162870473⟩]
theorem checked75033 : checkPrefixCuts (2^48) 9838657537 10 Manual.Count131072.C075033.packed 64 cuts75033 = true := by
 decide +kernel
def cuts75034 : List PrefixCut := [⟨12,30639873,30639891⟩,
⟨64,161723877,161723972⟩]
theorem checked75034 : checkPrefixCuts (2^48) 9838788609 10 Manual.Count131072.C075034.packed 64 cuts75034 = true := by
 decide +kernel
def pointBounds75034 : List (Nat × Nat × Nat) := [(9838813184,116664298796732,116664688807443)]
theorem point_links_checked75034 : (cuts75034.take 1).map (fun c => (9838788609-1+2*2^10*c.k,116664268156859+c.lower,116664658167552+c.upper)) = pointBounds75034 := by
 decide +kernel
def cuts75035 : List PrefixCut := [⟨64,164382263,164382360⟩]
theorem checked75035 : checkPrefixCuts (2^48) 9838919681 10 Manual.Count131072.C075035.packed 64 cuts75035 = true := by
 decide +kernel
def cuts75036 : List PrefixCut := [⟨35,89828576,89828630⟩,
⟨64,163178555,163178649⟩]
theorem checked75036 : checkPrefixCuts (2^48) 9839050753 10 Manual.Count131072.C075036.packed 64 cuts75036 = true := by
 decide +kernel
def pointBounds75036 : List (Nat × Nat × Nat) := [(9839122432,116664684091575,116665074102514)]
theorem point_links_checked75036 : (cuts75036.take 1).map (fun c => (9839050753-1+2*2^10*c.k,116664594262999+c.lower,116664984273884+c.upper)) = pointBounds75036 := by
 decide +kernel
def cuts75037 : List PrefixCut := [⟨64,162203742,162203836⟩]
theorem checked75037 : checkPrefixCuts (2^48) 9839181825 10 Manual.Count131072.C075037.packed 64 cuts75037 = true := by
 decide +kernel
def cuts75038 : List PrefixCut := [⟨58,149614590,149614681⟩,
⟨64,165090874,165090972⟩]
theorem checked75038 : checkPrefixCuts (2^48) 9839312897 10 Manual.Count131072.C075038.packed 64 cuts75038 = true := by
 decide +kernel
def pointBounds75038 : List (Nat × Nat × Nat) := [(9839431680,116665069259886,116665459271050)]
theorem point_links_checked75038 : (cuts75038.take 1).map (fun c => (9839312897-1+2*2^10*c.k,116664919645296+c.lower,116665309656369+c.upper)) = pointBounds75038 := by
 decide +kernel
def cuts75039 : List PrefixCut := [⟨64,164230476,164230568⟩]
theorem checked75039 : checkPrefixCuts (2^48) 9839443969 10 Manual.Count131072.C075039.packed 64 cuts75039 = true := by
 decide +kernel
def cuts75040 : List PrefixCut := [⟨64,162912402,162912501⟩]
theorem checked75040 : checkPrefixCuts (2^48) 9839575041 10 Manual.Count131072.C075040.packed 64 cuts75040 = true := by
 decide +kernel
def cuts75041 : List PrefixCut := [⟨17,42136602,42136625⟩,
⟨64,161336906,161336993⟩]
theorem checked75041 : checkPrefixCuts (2^48) 9839706113 10 Manual.Count131072.C075041.packed 64 cuts75041 = true := by
 decide +kernel
def pointBounds75041 : List (Nat × Nat × Nat) := [(9839740928,116665454015650,116665844027035)]
theorem point_links_checked75041 : (cuts75041.take 1).map (fun c => (9839706113-1+2*2^10*c.k,116665411879048+c.lower,116665801890410+c.upper)) = pointBounds75041 := by
 decide +kernel
def cuts75042 : List PrefixCut := [⟨64,164395529,164395628⟩]
theorem checked75042 : checkPrefixCuts (2^48) 9839837185 10 Manual.Count131072.C075042.packed 64 cuts75042 = true := by
 decide +kernel
def cuts75043 : List PrefixCut := [⟨40,100146614,100146677⟩,
⟨64,161847498,161847600⟩]
theorem checked75043 : checkPrefixCuts (2^48) 9839968257 10 Manual.Count131072.C075043.packed 64 cuts75043 = true := by
 decide +kernel
def pointBounds75043 : List (Nat × Nat × Nat) := [(9840050176,116665837758097,116666227769708)]
theorem point_links_checked75043 : (cuts75043.take 1).map (fun c => (9839968257-1+2*2^10*c.k,116665737611483+c.lower,116666127623031+c.upper)) = pointBounds75043 := by
 decide +kernel
def cuts75044 : List PrefixCut := [⟨64,165106282,165106374⟩]
theorem checked75044 : checkPrefixCuts (2^48) 9840099329 10 Manual.Count131072.C075044.packed 64 cuts75044 = true := by
 decide +kernel
def cuts75045 : List PrefixCut := [⟨63,161156707,161156797⟩,
⟨64,163588058,163588149⟩]
theorem checked75045 : checkPrefixCuts (2^48) 9840230401 10 Manual.Count131072.C075045.packed 64 cuts75045 = true := by
 decide +kernel
def pointBounds75045 : List (Nat × Nat × Nat) := [(9840359424,116666225721970,116666615733802)]
theorem point_links_checked75045 : (cuts75045.take 1).map (fun c => (9840230401-1+2*2^10*c.k,116666064565263+c.lower,116666454577005+c.upper)) = pointBounds75045 := by
 decide +kernel
def cuts75046 : List PrefixCut := [⟨64,159495520,159495612⟩]
theorem checked75046 : checkPrefixCuts (2^48) 9840361473 10 Manual.Count131072.C075046.packed 64 cuts75046 = true := by
 decide +kernel
def cuts75047 : List PrefixCut := [⟨64,162611182,162611276⟩]
theorem checked75047 : checkPrefixCuts (2^48) 9840492545 10 Manual.Count131072.C075047.packed 64 cuts75047 = true := by
 decide +kernel
def cuts75048 : List PrefixCut := [⟨22,56491506,56491541⟩,
⟨64,163123877,163123977⟩]
theorem checked75048 : checkPrefixCuts (2^48) 9840623617 10 Manual.Count131072.C075048.packed 64 cuts75048 = true := by
 decide +kernel
def pointBounds75048 : List (Nat × Nat × Nat) := [(9840668672,116666606751529,116666996763583)]
theorem point_links_checked75048 : (cuts75048.take 1).map (fun c => (9840623617-1+2*2^10*c.k,116666550260023+c.lower,116666940272042+c.upper)) = pointBounds75048 := by
 decide +kernel
def cuts75049 : List PrefixCut := [⟨64,164408818,164408919⟩]
theorem checked75049 : checkPrefixCuts (2^48) 9840754689 10 Manual.Count131072.C075049.packed 64 cuts75049 = true := by
 decide +kernel
def cuts75050 : List PrefixCut := [⟨45,116297620,116297687⟩,
⟨64,165178904,165179000⟩]
theorem checked75050 : checkPrefixCuts (2^48) 9840885761 10 Manual.Count131072.C075050.packed 64 cuts75050 = true := by
 decide +kernel
def pointBounds75050 : List (Nat × Nat × Nat) := [(9840977920,116666994090338,116667384102625)]
theorem point_links_checked75050 : (cuts75050.take 1).map (fun c => (9840885761-1+2*2^10*c.k,116666877792718+c.lower,116667267804938+c.upper)) = pointBounds75050 := by
 decide +kernel
def cuts75051 : List PrefixCut := [⟨64,162430908,162431005⟩]
theorem checked75051 : checkPrefixCuts (2^48) 9841016833 10 Manual.Count131072.C075051.packed 64 cuts75051 = true := by
 decide +kernel
def cuts75052 : List PrefixCut := [⟨64,159969011,159969098⟩]
theorem checked75052 : checkPrefixCuts (2^48) 9841147905 10 Manual.Count131072.C075052.packed 64 cuts75052 = true := by
 decide +kernel
def cuts75053 : List PrefixCut := [⟨4,10582534,10582540⟩,
⟨64,163198811,163198909⟩]
theorem checked75053 : checkPrefixCuts (2^48) 9841278977 10 Manual.Count131072.C075053.packed 64 cuts75053 = true := by
 decide +kernel
def pointBounds75053 : List (Nat × Nat × Nat) := [(9841287168,116667375954075,116667765966581)]
theorem point_links_checked75053 : (cuts75053.take 1).map (fun c => (9841278977-1+2*2^10*c.k,116667365371541+c.lower,116667755384041+c.upper)) = pointBounds75053 := by
 decide +kernel
def cuts75054 : List PrefixCut := [⟨64,162510216,162510314⟩]
theorem checked75054 : checkPrefixCuts (2^48) 9841410049 10 Manual.Count131072.C075054.packed 64 cuts75054 = true := by
 decide +kernel
def cuts75055 : List PrefixCut := [⟨27,69413683,69413724⟩,
⟨64,162851264,162851364⟩]
theorem checked75055 : checkPrefixCuts (2^48) 9841541121 10 Manual.Count131072.C075055.packed 64 cuts75055 = true := by
 decide +kernel
def pointBounds75055 : List (Nat × Nat × Nat) := [(9841596416,116667760494251,116668150506988)]
theorem point_links_checked75055 : (cuts75055.take 1).map (fun c => (9841541121-1+2*2^10*c.k,116667691080568+c.lower,116668081093264+c.upper)) = pointBounds75055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000157
