import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B042
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 1645535943308792216651193878913666578489083807191560928580927490

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 5043 4 14) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 14) 50 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B042
