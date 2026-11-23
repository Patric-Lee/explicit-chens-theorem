import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B029
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 3626869693408702477238274

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 1937 4 6) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 6) 24 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B029
