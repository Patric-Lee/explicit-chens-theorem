import PlattReciprocalKernel
namespace ChenEffective.PlattWindow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem count_High16 : Nat.beq (segmentCounts 9999999489 4 16) 53920304716717807410125601674716827961906535688991144791615073157122 = true := by
  decide +kernel
theorem reject_High16 : Nat.beq (segmentCounts 9999999489 4 16) 53920304716717807410125601674716827961906535688991144791615073157123 = false := by
  rw [Nat.eq_of_beq_eq_true count_High16]
  decide +kernel
#print axioms count_High16
end ChenEffective.PlattWindow
