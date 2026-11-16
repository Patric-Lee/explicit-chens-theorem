import PlattAssemblyKernel
import PlattCertificates.Count131072.C070000
namespace ChenEffective.PlattWindow.AssemblyPilot.C070000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts : List PrefixCut := [⟨64,175127620,175127725⟩]
theorem checked : checkPrefixCuts (2^48) 9178972161 10 Manual.Count131072.C070000.packed 64 cuts = true := by
 decide +kernel
end ChenEffective.PlattWindow.AssemblyPilot.C070000
