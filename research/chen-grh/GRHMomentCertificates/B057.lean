import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B057
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 9365388556163260083702782906939097560428862228331764012640066526253504004479744460507431506950834303541643619881063102692356699337915614250532867

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 14643 4 31) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 31) 107 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B057
