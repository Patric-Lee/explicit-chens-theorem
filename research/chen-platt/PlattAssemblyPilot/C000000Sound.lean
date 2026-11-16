import PlattAssemblySoundness
import PlattAssemblyPilot.C000000
namespace ChenEffective.PlattWindow.AssemblyPilot.C000000
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000
theorem cuts_sound (c : PrefixCut) (hc : c ∈ cuts) :
 (c.lower:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum (4000001-1+2*2^4*c.k)-primeReciprocalSum (4000001-1)) ∧
 (2:ℝ)^48*(primeReciprocalSum (4000001-1+2*2^4*c.k)-primeReciprocalSum (4000001-1)) ≤ (c.upper:ℝ) := by
 have h := checked_prefix_cut checked hc
 have hcount := Nat.eq_of_beq_eq_true Manual.Count131072.C000000.count_checked
 have hh := segment_prefix_reciprocal_certificate (scale:=2^48)
  (by norm_num : 4000001%2=1) (by norm_num : 3≤4000001)
  (by norm_num [PsiFinite.baseCover] : 4000001+2*2^4*4096-1≤PsiFinite.baseCover) h.1 hcount h.2
 simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
#print axioms cuts_sound
end ChenEffective.PlattWindow.AssemblyPilot.C000000
