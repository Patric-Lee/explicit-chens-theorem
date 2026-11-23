import GRHMomentCountKernel
namespace ChenEffective.GRHSub12.MomentCertificates.B060
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : Nat := 2636122525527714062618162460689117961624546325910047012567086900838810131458845833679682317850652987479670117449749139021385265389772550023028449352277152759810

theorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 17691 4 34) packed = true := by
  decide +kernel

theorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed 34) 110 = true := by
  decide +kernel
end ChenEffective.GRHSub12.MomentCertificates.B060
