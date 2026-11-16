import PlattAssemblyKernel
import PlattCertificates.Count131072.C010000
namespace ChenEffective.PlattWindow.AssemblyPilot.C010000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts : List PrefixCut := [⟨22,222025959,222026152⟩,
⟨63,639946958,639947518⟩,
⟨104,1071770496,1071771433⟩,
⟨128,1333170282,1333171445⟩]
theorem checked : checkPrefixCuts (2^48) 1314652161 9 Manual.Count131072.C010000.packed 128 cuts = true := by
 decide +kernel
end ChenEffective.PlattWindow.AssemblyPilot.C010000
