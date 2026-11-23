import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B065
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 305242134740093591768253472833906486815480013018452277832935534043581495621623674744436088642568357432207809955324890636016126669230751743546910685636364867310650969663406924735397967719188118142785556328555122262732665106485951047401475

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 24651 4 50) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 50) 155 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B065
