import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B027
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 4835795513586273015234567

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 1601 4 6) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 6) 27 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B027
