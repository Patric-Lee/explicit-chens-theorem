import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B034
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 316916276889857552395620646915

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 2917 4 7) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 7) 25 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B034
