import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 7

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 171 4 1) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 1) 7 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B003
