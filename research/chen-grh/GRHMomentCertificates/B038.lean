import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B038
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 25961721983206365374815079980335108

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 3845 4 8) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 8) 33 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B038
