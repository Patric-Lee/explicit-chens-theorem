import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B049
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 22765998464105470598146698241981959269384896303362819283341821965325456401208967169

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 8465 4 18) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 18) 64 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B049
