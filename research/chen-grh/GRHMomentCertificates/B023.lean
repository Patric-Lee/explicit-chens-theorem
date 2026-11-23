import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B023
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 12885164038

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 1091 4 3) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 3) 13 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B023
