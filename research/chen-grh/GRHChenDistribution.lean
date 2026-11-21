import GRHWeightedDistribution
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969Ordinary418Specialization

/-! Connection to the project's actual reduced Chen distribution sum.
There is no assumed BV estimate here: the bound is supplied by the proved
GRH character estimates and the exact combined-modulus reindexing. -/
namespace ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.Richert1969
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem combined_modulus_squarefree {N d : ℕ} {ε : ℝ}
    (hd : d ∈ chenReducedCombinedModuli N ε) : Squarefree d := by
  rcases Finset.mem_biUnion.mp hd with ⟨q,hq,hmImage⟩
  rcases Finset.mem_image.mp hmImage with ⟨r,hr,rfl⟩
  have hqSource := (Finset.mem_filter.mp hq).1
  have hqPrime := (Finset.mem_filter.mp hqSource).2.1
  have hrDiv : r ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hr).1
  have hrSquarefree := (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd hrDiv
  have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hqSource hrDiv
  exact (Nat.squarefree_mul hcop).mpr ⟨hqPrime.squarefree,hrSquarefree⟩

theorem chen_weighted_distribution {N : ℕ} (hN : GRH14.targetCutoff ≤ N) :
    jurkatRichertSourceReducedWeightedBVSum N (1/500:ℝ) ≤
      (1e-12:ℝ)*N/(Real.log N)^2 := by
  let D := LiuWeight.liuSourceDEpsilon N (1/500:ℝ)
  let S := chenReducedCombinedModuli N (1/500:ℝ)
  have hL := GRH14.target_log_lower hN
  have hN1 : (1:ℝ) ≤ N := by
    have hn : 1 ≤ N := by
      by_contra hh
      have hz : N=0 := by omega
      subst N
      norm_num at hL
    exact_mod_cast hn
  have hD : 1 ≤ D := by
    unfold D LiuWeight.liuSourceDEpsilon
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (by norm_num : (0:ℝ) ≤ 1/2-(1/500:ℝ))
  have hlevel : (D:ℝ) ≤ (N:ℝ)^(249/500:ℝ) := by
    dsimp only [D,LiuWeight.liuSourceDEpsilon]
    norm_num only [show (1/2-(1/500:ℝ))=(249/500:ℝ) by norm_num]
    exact Nat.floor_le (by positivity)
  have hS : S ⊆ Finset.Icc 1 D := by
    intro d hd
    have hs := combined_modulus_squarefree hd
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hs.ne_zero,
      chenReducedCombinedModuli_le_liuSourceDEpsilon hd⟩
  apply (chenReducedWeightedBVSum_le_combinedMass N (1/500:ℝ)).trans
  simpa only [threeOmegaErrorMass] using
    weighted_AP_numerical hN hD hlevel S hS (fun d hd => combined_modulus_squarefree hd)

#print axioms combined_modulus_squarefree
#print axioms chen_weighted_distribution
end ChenEffective.GRH
