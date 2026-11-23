import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 6

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 123 4 1) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 1) 6 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B001
