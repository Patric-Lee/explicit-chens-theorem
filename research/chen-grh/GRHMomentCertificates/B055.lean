import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B055
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 5087882161424953775974359611026313628058464372213113219610712848136567701246245683749802231476868327633937082392885705409701432808177667

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 12771 4 29) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 29) 97 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B055
