import GRHQuarterMomentKernel
namespace ChenEffective.H10Band.QuarterCert.C507
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def packed : Nat := 26961180814400127468762805780958453050938485662394792004781695172611
def data : List (Nat×Nat) := [(4471997,11293133),(4472006,11293064),(4472015,11292996),(4472024,11292928),(4472033,11292860),(4472042,11292792),(4472051,11292724),(4472060,11292655),(4472069,11292587),(4472078,11292519),(4472087,11292451),(4472095,11292390),(4472104,11292322),(4472113,11292254),(4472122,11292186),(4472131,11292118)]
theorem counts_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts 3999505 4 16) packed=true := by
  decide +kernel
theorem bounds_checked : QuarterCert.boundsCheck 3999505 4 3 16 data=true := by
  decide +kernel
theorem weighted_checked : Nat.beq (QuarterCert.weightedSum 4 packed data) 406536821=true := by
  decide +kernel
end ChenEffective.H10Band.QuarterCert.C507
