import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B022
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 25770065925

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 1025 4 3) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 3) 15 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B022
