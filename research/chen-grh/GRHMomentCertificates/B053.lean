import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B053
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 507701313188033701340960806370711800110187241026785954802321630605597536072891107502153824127094907224086878421139010019983363

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 11027 4 27) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 27) 88 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B053
