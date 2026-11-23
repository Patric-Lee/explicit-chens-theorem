import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B045
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 7067496100957105449232209192121577836124047308475746926425106135579230210

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 6401 4 16) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 16) 55 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B045
