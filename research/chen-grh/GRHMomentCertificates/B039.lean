import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B039
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 1020867870108711899450499538886332907523

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 4097 4 9) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 9) 33 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B039
