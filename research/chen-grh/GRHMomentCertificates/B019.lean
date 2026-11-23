import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B019
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 262148

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 843 4 2) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 2) 8 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B019
