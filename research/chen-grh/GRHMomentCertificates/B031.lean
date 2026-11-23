import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B031
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 158459951879775339824445456387

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 2305 4 7) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 7) 27 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B031
