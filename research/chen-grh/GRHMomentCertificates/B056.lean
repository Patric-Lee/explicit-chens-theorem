import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B056
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 238171966887905939595237971814102090325283351360088147847148609641979165671082586455655780257723183550020853825313123789201473310069688041478

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 13691 4 30) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 30) 98 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B056
