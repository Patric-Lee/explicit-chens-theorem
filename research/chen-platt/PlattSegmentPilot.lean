import PlattSegmentArithmetic
import PlattSegmentPilotData

/-! A complete small certificate, from kernel sieve through integer
arithmetic to an inequality for the genuine reciprocal-prime sum.
This is a pilot, not the full finite window. -/
namespace ChenEffective.PlattWindow
open AnalyticNumberTheory.Mertens
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pilot_reciprocal_bound :
    (19271268501:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum 4004096-primeReciprocalSum 4000000) ∧
    (2:ℝ)^48*(primeReciprocalSum 4004096-primeReciprocalSum 4000000) ≤ (19271422716:ℝ) := by
  have hc : segmentCounts 4000001 4 128=pilotPacked :=
    Nat.eq_of_beq_eq_true count_Low128
  have hp : Nat.beq (segmentFixed (2^48) 4000001 4 pilotPacked 128).1 19271268501=true ∧
      Nat.beq (segmentFixed (2^48) 4000001 4 pilotPacked 128).2 19271422716=true := by
    simpa only [Bool.and_eq_true] using pilot_arithmetic_checked
  have ha : segmentFixed (2^48) 4000001 4 pilotPacked 128=(19271268501,19271422716) :=
    Prod.ext (Nat.eq_of_beq_eq_true hp.1) (Nat.eq_of_beq_eq_true hp.2)
  have h := segment_reciprocal_certificate (scale:=2^48)
    (by norm_num : 4000001%2=1) (by norm_num : 3 ≤ 4000001)
    (by norm_num [PsiFinite.baseCover] : 4000001+2*2^4*128-1 ≤ PsiFinite.baseCover) hc ha
  norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul,Nat.reducePow,Nat.cast_pow,Nat.cast_ofNat] at h ⊢
  exact h

#print axioms pilot_arithmetic_checked
#print axioms pilot_reciprocal_bound
end ChenEffective.PlattWindow
