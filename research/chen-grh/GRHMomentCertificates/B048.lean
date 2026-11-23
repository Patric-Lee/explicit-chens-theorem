import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B048
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 347383335181088773956732886840490733539611504018718310648217699365757388914693

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 7923 4 17) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 17) 58 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B048
