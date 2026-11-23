import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B052
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 5164657366002301809347866165302455608433368051602676056727796798810125341934335066368843163276471024433499915668689256450

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 10203 4 26) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 26) 85 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B052
