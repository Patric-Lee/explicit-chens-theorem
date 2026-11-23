import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B043
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 80881074161255897877630160987644249361053586213281460012374361899014

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 5477 4 15) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 15) 59 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B043
