import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B036
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 20769583582205492095137336982110212

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 3365 4 8) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 8) 32 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B036
