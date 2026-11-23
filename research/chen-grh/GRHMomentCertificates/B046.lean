import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B046
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 1766927946675279032645010049330862796410090122160539077538505298387533828

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 6891 4 16) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 16) 53 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B046
