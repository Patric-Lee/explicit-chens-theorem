import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B059
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 40223832973019262140097518877030864331473079830626055982616429333372253942650150661419863629418537768308950374440779978308114787661142167376634714033225733

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 16643 4 33) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 33) 108 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B059
