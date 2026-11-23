import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B050
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 2486631359497035292619302206003902204247353344453518600100576725482118800368404265041924

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 9027 4 19) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 19) 69 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B050
