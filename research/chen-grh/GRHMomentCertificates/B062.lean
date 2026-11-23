import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B062
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 16547377605315015616349597134606178831913863094930925000801488080890842821426632827792062093968237847196073492055615914361755388689203535490443134566636973248862270395003461142815995206465458212385540321311929944637443

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 20165 4 46) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 46) 148 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B062
