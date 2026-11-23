import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B047
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 463177191265470159134495587931831915871058320155520447469502185374502699139074

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 7397 4 17) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 17) 64 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B047
