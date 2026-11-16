import PlattAssemblySoundness
import PlattAssemblyPilot.C010000
namespace ChenEffective.PlattWindow.AssemblyPilot.C010000
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000
theorem cuts_sound (c : PrefixCut) (hc : c ∈ cuts) :
 (c.lower:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum (1314652161-1+2*2^9*c.k)-primeReciprocalSum (1314652161-1)) ∧
 (2:ℝ)^48*(primeReciprocalSum (1314652161-1+2*2^9*c.k)-primeReciprocalSum (1314652161-1)) ≤ (c.upper:ℝ) := by
 have h := checked_prefix_cut checked hc
 have hcount := Nat.eq_of_beq_eq_true Manual.Count131072.C010000.count_checked
 have hh := segment_prefix_reciprocal_certificate (scale:=2^48)
  (by norm_num : 1314652161%2=1) (by norm_num : 3≤1314652161)
  (by norm_num [PsiFinite.baseCover] : 1314652161+2*2^9*128-1≤PsiFinite.baseCover) h.1 hcount h.2
 simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
#print axioms cuts_sound
end ChenEffective.PlattWindow.AssemblyPilot.C010000
