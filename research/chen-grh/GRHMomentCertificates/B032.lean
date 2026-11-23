import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B032
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 475376228714291534068965507075

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 2501 4 7) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 7) 30 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B032
