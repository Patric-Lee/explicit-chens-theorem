import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B058
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 818353895614040587932425619016014394965248626286501912496979087488424147140921068536372347704456786991088833822525724692037050618518412595362795945989

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 15627 4 32) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 32) 104 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B058
