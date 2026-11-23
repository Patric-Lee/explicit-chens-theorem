import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B054
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 22181865254279667508322476387320776206541928914346648712891672057282344266563016849180113435493672291969933663652997126846337581060

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 11883 4 28) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 28) 100 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B054
