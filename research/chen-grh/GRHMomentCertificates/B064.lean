import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B064
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 3105107253601166598490772440258580951675455783629187097125369845811549110975859186565844029928900960612400689009920801069311870125315222048574069231655642904241870998293882109467297532104349895825540432877649460677760092205142441986

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 23105 4 49) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 49) 151 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B064
