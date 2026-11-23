import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B066
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 1310998317953753388650497668874150973412276270418220493838159402993913422208227817072623843285602925017008710968937405891349197236271755709628542683149445598269568823645387399898197257335428889583343542658486892678229942225880706104046388710080517

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 26245 4 52) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 52) 162 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B066
