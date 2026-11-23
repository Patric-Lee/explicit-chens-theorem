import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B041
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 822783664552411147317467386185299993597441406627709396906672133

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 4625 4 14) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 14) 53 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B041
