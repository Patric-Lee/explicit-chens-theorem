import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B024
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 110681590363639250948

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 1157 4 5) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 5) 23 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B024
