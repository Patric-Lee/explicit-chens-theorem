import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B040
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 1361150237108877316465425381152230932483

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 4357 4 9) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 9) 33 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B040
