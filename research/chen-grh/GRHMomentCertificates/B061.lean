import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B061
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 6421142716273792517301556778859403347133414600441821378906057691304281496531684038015692405968893926427016173271947820569594825653227201134676750890842467710936499197655659607331687535330807023943272473100292

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 18771 4 44) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 44) 142 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B061
