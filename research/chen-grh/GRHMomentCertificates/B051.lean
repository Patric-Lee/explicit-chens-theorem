import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B051
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 1492007652328546312292176227806626653488832431102036241366883067102338857666500855267333

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 9605 4 19) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 19) 68 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B051
