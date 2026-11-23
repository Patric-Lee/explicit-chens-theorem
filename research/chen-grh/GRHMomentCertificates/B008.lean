import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B008
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 327685

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 325 4 2) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 2) 10 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B008
