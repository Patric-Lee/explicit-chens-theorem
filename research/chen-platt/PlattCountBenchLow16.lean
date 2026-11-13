import PlattReciprocalKernel
namespace ChenEffective.PlattWindow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem count_Low16 : Nat.beq (segmentCounts 4000001 4 16) 3533694129968144798784240887527775161068196164453387032060155775848546304 = true := by
  decide +kernel
theorem reject_Low16 : Nat.beq (segmentCounts 4000001 4 16) 3533694129968144798784240887527775161068196164453387032060155775848546305 = false := by
  rw [Nat.eq_of_beq_eq_true count_Low16]
  decide +kernel
#print axioms count_Low16
end ChenEffective.PlattWindow
