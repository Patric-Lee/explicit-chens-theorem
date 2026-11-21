import GRHPrefix
import GRHPrincipalPrefix
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrincipalLambdaGlobalReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVPayload

/-! A numerical reduced-residue Chebyshev estimate from the actual
character transforms. Principal bad prime powers are retained explicitly
before absorption. No primitivity or low-conductor restriction remains. -/
namespace ChenEffective.GRH
open Real Finset
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem chebyshev_AP_numerical {N q a : ℕ} (hN : 2 ≤ N)
    (hL : (10:ℝ) ≤ Real.log N) (hq : 0 < q) (ha : a.Coprime q) :
    ‖lambdaAPMainError N q a‖ ≤
      (10^15:ℝ)*(Real.log q+Real.log N)^3*(N:ℝ)^(501/1000:ℝ) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let A := Real.log (q:ℝ)+Real.log N
  let Y := (N:ℝ)^(501/1000:ℝ)
  let C := (10^13:ℝ)*A^2*Y
  let B := (10^14:ℝ)*A^2*Y+6*A^3
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
  have hA : 10 ≤ A := by dsimp only [A]; linarith only [hL,hlq]
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hLA : Real.log (N:ℝ) ≤ A := by dsimp only [A]; linarith only [hlq]
  have hqA : Real.log (q:ℝ) ≤ A := by dsimp only [A]; linarith only [hL]
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1 (by norm_num)
  have hY0 : 0 ≤ Y := by linarith only [hY1]
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hlogq : (Nat.log2 q:ℝ) ≤ 2*A := by
    by_cases hq2 : 2 ≤ q
    · exact (natLog2_cast_le_two_log hq2).trans (by linarith only [hqA])
    · have hqeq : q=1 := by omega
      subst q
      norm_num
      linarith only [hA0]
  have hlogN : (Nat.log2 N+1:ℝ) ≤ 3*A := by
    have hh := natLog2_cast_le_two_log hN
    linarith only [hh,hLA,hA]
  have hbad : (Nat.log2 q:ℝ)*(Nat.log2 N+1:ℝ)*Real.log (N:ℝ) ≤ 6*A^3 := by
    calc
      _ ≤ (2*A)*(3*A)*A := by gcongr
      _ = _ := by ring
  have hprincipal : ‖principalLambdaMainError N q‖ ≤ B := by
    have hp := principal_prefix_numerical hN1 hL
    simp only [Nat.floor_natCast] at hp
    rw [lambdaCharacterPrefix_one] at hp
    change ‖principalLambdaMainError N 1‖ ≤ _ at hp
    have hbig : ‖principalLambdaMainError N 1‖ ≤ (10^14:ℝ)*A^2*Y := by
      exact hp.trans (by dsimp only [Y]; gcongr)
    exact (norm_principalLambdaMainError_le_global_add_bad hq le_rfl hN).trans (add_le_add hbig hbad)
  have hsum : (∑ χ ∈ nonprincipalCharacters q, ‖lambdaCharacterPrefix N q χ‖) ≤
      ((nonprincipalCharacters q).card:ℝ)*C := by
    calc
      _ ≤ ∑ _χ ∈ nonprincipalCharacters q, C := by
        apply Finset.sum_le_sum
        intro χ hχ
        have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
        have hh := nonprincipal_prefix_numerical χ hχ1 hN1 hL
        simpa only [Nat.floor_natCast] using hh
      _ = _ := by simp
  have hchars : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    have hh := charOrthSum hq (1:ZMod q) 1
    have he : ((Fintype.card (DirichletCharacter ℂ q):ℕ):ℂ) = (q.totient:ℂ) := by simpa using hh
    exact_mod_cast he
  have hcard : ((nonprincipalCharacters q).card:ℝ) ≤ q.totient := by
    exact_mod_cast (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (by simpa using hchars)
  have hφ0 : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ1 : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hi : (q.totient:ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hφ1
  have hc : (q.totient:ℝ)⁻¹*((nonprincipalCharacters q).card:ℝ) ≤ 1 := by
    calc
      _ ≤ (q.totient:ℝ)⁻¹*q.totient := mul_le_mul_of_nonneg_left hcard (inv_nonneg.mpr hφ0.le)
      _ = _ := inv_mul_cancel₀ hφ0.ne'
  have hap : ‖lambdaAPMainError N q a‖ ≤ B+C := by
    calc
      _ ≤ (q.totient:ℝ)⁻¹*(B+((nonprincipalCharacters q).card:ℝ)*C) :=
        (norm_lambdaAPMainError_le_principal_add_nonprincipal hq ha N).trans
          (mul_le_mul_of_nonneg_left (add_le_add hprincipal hsum) (inv_nonneg.mpr hφ0.le))
      _ = (q.totient:ℝ)⁻¹*B+
          ((q.totient:ℝ)⁻¹*((nonprincipalCharacters q).card:ℝ))*C := by ring
      _ ≤ 1*B+1*C := add_le_add (mul_le_mul_of_nonneg_right hi hB0) (mul_le_mul_of_nonneg_right hc hC0)
      _ = _ := by ring
  have hpow : A^2*Y ≤ A^3*Y := by
    apply mul_le_mul_of_nonneg_right _ hY0
    nlinarith only [mul_nonneg (sq_nonneg A) (show 0 ≤ A-1 by linarith only [hA])]
  have hYpow : A^3 ≤ A^3*Y := by nlinarith only [mul_nonneg (pow_nonneg hA0 3) (sub_nonneg.mpr hY1)]
  change _ ≤ (10^15:ℝ)*A^3*Y
  dsimp only [B,C] at hap
  nlinarith only [hap,hpow,hYpow,show 0 ≤ A^3*Y by positivity]

#print axioms chebyshev_AP_numerical
end ChenEffective.GRH
