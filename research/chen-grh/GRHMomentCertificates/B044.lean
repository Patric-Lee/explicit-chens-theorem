import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B044
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 80881896913534462699679934354522157814240956988803928659325601579010

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 5931 4 15) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 15) 55 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B044
