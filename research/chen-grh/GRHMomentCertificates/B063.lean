import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B063
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 722980667763698300176887670136204016703263834221670462858992745513803675913799788797797521697996853250399459746212511985299734752136248540672225104964400007288478423818965299446404927046420974890322537481647306383569453059

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 21611 4 47) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 47) 154 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B063
