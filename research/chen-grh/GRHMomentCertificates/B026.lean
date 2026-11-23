import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B026
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 73788665157583765509

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 1445 4 5) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 5) 24 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B026
