import PlattGlobalGridKernel

namespace ChenEffective.PlattWindow

-- Seam duplication is allowed; a missing or changed numerical bound is not.
example : checkPointCover [(4,1,2),(8,3,4)] [(4,1,2),(4,1,2),(8,3,4)]=true := by
  decide +kernel
example : checkPointCover [(4,1,2),(8,3,4)] [(4,1,3)]=false := by decide +kernel
example : checkPointCover [(4,1,2),(8,3,4)] [(6,1,2)]=false := by decide +kernel
example : checkPointCover [] [(4,1,2)]=false := by decide +kernel

private def c : AssemblyCell := ⟨4,8,1,4,10,20⟩
private def r : LogCertificate.LogRow := ⟨4,0,0,0,0,0,10,11⟩
private def t : LogCertificate.LogRow := ⟨8,0,0,0,0,0,19,20⟩
example : checkGridLinks [c] [(4,1,2),(8,3,4)] [r,t]=true := by decide +kernel
example : checkGridLinks [c] [(4,2,2),(8,3,4)] [r,t]=false := by decide +kernel
example : checkGridLinks [c] [(4,1,2),(8,3,5)] [r,t]=false := by decide +kernel
example : checkGridLinks [c] [(4,1,2),(8,3,4)] [t,r]=false := by decide +kernel
example : checkGridLinks [c] [(4,1,2)] [r,t]=false := by decide +kernel

end ChenEffective.PlattWindow
