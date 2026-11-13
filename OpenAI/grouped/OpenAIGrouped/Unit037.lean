import OpenAIGrouped.Unit036
import OpenAIGrouped.Unit035
import OpenAIGrouped.Unit007
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import OpenAIGrouped.Unit034

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/ExponentImprovement.lean; sha256: 106f3dd90a3569bba528e6f366f2b6ec06a8699b5d7a24fb3e371eb49d085b38 -/
section Source1480
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def enlargementExponent (ξ : ℝ) : ℝ := (6*ξ-5)/(3*ξ-1)

lemma enlargement_bounds (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    1 ≤ enlargementExponent ξ ∧ enlargementExponent ξ ≤ SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 0 < 3*ξ-1 := by linarith
  constructor
  · unfold enlargementExponent
    apply (one_le_div hd).mpr
    linarith
  · unfold enlargementExponent SevenEighths.HeathBrownIteration.step
    exact div_le_div_of_nonneg_right (by linarith) hd.le

lemma enlargement_cross_identity (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    (enlargementExponent ξ+1)*(2/3 : ℝ) = SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 3*ξ-1 ≠ 0 := by linarith
  unfold enlargementExponent SevenEighths.HeathBrownIteration.step
  apply (eq_div_iff hd).mpr
  have hc := div_mul_cancel₀ (6*ξ-5) hd
  nlinarith [hc]

lemma enlargement_secondary_identity (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    enlargementExponent ξ*(1-ξ)+(2*ξ-1) = SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 3*ξ-1 ≠ 0 := by linarith
  unfold enlargementExponent SevenEighths.HeathBrownIteration.step
  apply (eq_div_iff hd).mpr
  have hc := div_mul_cancel₀ (6*ξ-5) hd
  nlinarith [hc]

theorem enlarged_improved_shape (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    let T := max M (N^(enlargementExponent ξ))
    T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤
      3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ)) := by
  let α := enlargementExponent ξ
  let β := SevenEighths.HeathBrownIteration.step ξ
  let T := max M (N^α)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hαβ : α ≤ β := (enlargement_bounds ξ hξ).2
  have hNb : 0 ≤ N^β := Real.rpow_nonneg hN0.le _
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have ht : T ≤ M+N^β := by
    apply max_le
    · exact le_add_of_nonneg_right hNb
    · exact (Real.rpow_le_rpow_of_exponent_le hN hαβ).trans (le_add_of_nonneg_left hM0.le)
  have hnx : (N^α*N)^(2/3 : ℝ) = N^β := by
    conv_lhs => arg 1; arg 2; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN0, ← Real.rpow_mul hN0.le, enlargement_cross_identity ξ hξ]
  have htc : (T*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ)+N^β := by
    by_cases hm : M ≤ N^α
    · dsimp only [T]
      rw [max_eq_right hm, hnx]
      exact le_add_of_nonneg_left hcross
    · dsimp only [T]
      rw [max_eq_left (le_of_not_ge hm)]
      exact le_add_of_nonneg_right hNb
  have hts : T^(1-ξ)*N^(2*ξ-1) ≤ N^β := by
    have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 α)
      (le_max_right M (N^α)) (show 1-ξ ≤ 0 by linarith)
    calc
      _ ≤ (N^α)^(1-ξ)*N^(2*ξ-1) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN0.le _)
      _ = N^β := by
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, enlargement_secondary_identity ξ hξ]
  change T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤ 3*(M+N^β+(M*N)^(2/3 : ℝ))
  linarith

theorem HasCubicExponent.improve {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) < ξ) (hξ2 : ξ ≤ 2) :
    HasCubicExponent (SevenEighths.HeathBrownIteration.step ξ) := by
  intro ε hε
  let θ := min (ε/14) (1/4 : ℝ)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθsmall : θ < 1/2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθε : 7*θ ≤ ε := by
    have hh : θ ≤ ε/14 := min_le_left _ _
    linarith
  obtain ⟨C,hC,hb⟩ := h.full_improved hξ.le hξ2 θ hθ hθsmall
  refine ⟨3*C, by positivity, ?_⟩
  intro M N hM hN
  let T := max M (N^(enlargementExponent ξ))
  have hT : 1 ≤ T := hM.trans (le_max_left _ _)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hp : N^(7*θ) ≤ (M*N)^ε :=
    (Real.rpow_le_rpow_of_exponent_le hN hθε).trans
      (Real.rpow_le_rpow hN0.le (by nlinarith) hε.le)
  have ht := enlarged_improved_shape M N ξ hM hN hξ.le
  have hshape : 0 ≤ M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ) := by positivity
  calc
    _ ≤ sieveNorm T N := sieveNorm_mono (le_max_left _ _) le_rfl
    _ ≤ elementSieveNorm T N := sieveNorm_le_elementSieveNorm T N
    _ ≤ C*N^(7*θ)*(T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1)) := hb T N hT hN
    _ ≤ C*N^(7*θ)*(3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ C*(M*N)^ε*(3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (by positivity)
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI

end Source1480

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Sharp.lean; sha256: eb34bc19b68ab284c2396efb8171037a4d5a3d5534e35690b3c304956a2d59bb -/
section Source1481
namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

theorem hasCubicExponent_four_thirds : HasCubicExponent (4/3 : ℝ) := by
  intro ε hε
  obtain ⟨ξ, hξ, hξ2, hξε, hx⟩ := SevenEighths.HeathBrownIteration.finite_improvement
    hasCubicExponent_initial (fun x hx hx2 hp => hp.improve hx hx2)
    (show 0 < ε/2 by positivity)
  obtain ⟨C,hC,hb⟩ := hx (ε/2) (by positivity)
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN : 0 < M*N := mul_pos hM0 hN0
  have hp : 1 ≤ N^(ε/2) := Real.one_le_rpow hN (by positivity)
  have hNpow : N^ξ ≤ N^(4/3 : ℝ)*N^(ε/2) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN hξε.le
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg hMN.le _
  have hs : M+N^ξ+(M*N)^(2/3 : ℝ) ≤
      N^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := by
    nlinarith [mul_nonneg hM0.le (sub_nonneg.mpr hp),
      mul_nonneg hcross (sub_nonneg.mpr hp)]
  have hnp : N^(ε/2) ≤ (M*N)^(ε/2) :=
    Real.rpow_le_rpow hN0.le (by nlinarith) (by positivity)
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^ξ+(M*N)^(2/3 : ℝ)) := hb M N hM hN
    _ ≤ C*(M*N)^(ε/2)*(N^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnp (by positivity)) (by positivity)
    _ = _ := by
      have he : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add hMN]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := by ring
        _ = _ := by rw [he]

lemma four_thirds_le_cross (M N : ℝ) (_hM : 1 ≤ M) (hN : 1 ≤ N) (hNM : N ≤ M) :
    N^(4/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  have hN0 : 0 ≤ N := by linarith
  calc
    N^(4/3 : ℝ) = (N*N)^(2/3 : ℝ) := by
      rw [Real.mul_rpow hN0 hN0, ← Real.rpow_add (by linarith : 0 < N)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hN0 hN0)
      (mul_le_mul_of_nonneg_right hNM hN0) (by norm_num)

theorem sieveNorm_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N)^ε*(M+N+(M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := hasCubicExponent_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (mul_nonneg hM0 hN0) _
  by_cases hNM : N ≤ M
  · have hh := four_thirds_le_cross M N hM hN hNM
    calc
      _ ≤ C*(M*N)^ε*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := hb M N hM hN
      _ ≤ C*(M*N)^ε*(2*(M+N+(M*N)^(2/3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  · have hMN := le_of_not_ge hNM
    have hh := four_thirds_le_cross N M hN hM hMN
    have hs : N+M^(4/3 : ℝ)+(N*M)^(2/3 : ℝ) ≤
        2*(M+N+(M*N)^(2/3 : ℝ)) := by
      rw [mul_comm N M] at hh ⊢
      linarith
    calc
      _ = sieveNorm N M := sieveNorm_reciprocity M N
      _ ≤ C*(N*M)^ε*(N+M^(4/3 : ℝ)+(N*M)^(2/3 : ℝ)) := hb N M hN hM
      _ ≤ C*(N*M)^ε*(2*(M+N+(M*N)^(2/3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [mul_comm N M]; ring

end
end SevenEighths.CubicSieve

end OAI

end Source1481

/- Original source: OAI/NumberTheory/DirichletL/Descent/Sharp.lean; sha256: 2a51870c9215041ac9fd9366adfdcd2ef974aca2b338078000b5aa66f76dd708 -/
section Source1482
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_sharp_cubic_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      (K * N * B) ^ (ε / 2) * CubicSieve.sieveNorm N (2 * L) ≤
        C * (K * N * B * L) ^ ε * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := CubicSieve.sieveNorm_sharp (ε / 2) (by positivity)
  refine ⟨2 * C * (2 : ℝ) ^ (ε / 2), by positivity, ?_⟩
  intro K N B L hK hN hB hL
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  let Q := K * N * B * L
  have hQ0 : 0 < Q := by dsimp only [Q]; positivity
  have hKNB : K * N * B ≤ Q := le_mul_of_one_le_right (by positivity) hL
  have hNL : N * L ≤ Q := by
    have hKB : 1 ≤ K * B := one_le_mul_of_one_le_of_one_le hK hB
    have hh := le_mul_of_one_le_left (by positivity : 0 ≤ N * L) hKB
    convert hh using 1 ; dsimp only [Q] ; ring
  have hdouble (t : ℝ) : (N * (2 * L)) ^ t = (2 : ℝ) ^ t * (N * L) ^ t := by
    rw [show N * (2 * L) = 2 * (N * L) by ring, Real.mul_rpow (by norm_num) (by positivity)]
  have h23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have hshape : N + 2 * L + (N * (2 * L)) ^ (2 / 3 : ℝ) ≤
      2 * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
    rw [hdouble]
    have hh := mul_le_mul_of_nonneg_right h23 (Real.rpow_nonneg (by positivity : 0 ≤ N * L) (2 / 3 : ℝ))
    linarith
  have hcost : (K * N * B) ^ (ε / 2) * (N * L) ^ (ε / 2) ≤ Q ^ ε := by
    calc
      _ ≤ Q ^ (ε / 2) * Q ^ (ε / 2) := by
        exact mul_le_mul (Real.rpow_le_rpow (by positivity) hKNB (by positivity))
          (Real.rpow_le_rpow (by positivity) hNL (by positivity))
          (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hQ0.le _)
      _ = _ := by rw [← Real.rpow_add hQ0]; congr 1; ring
  have hh := hb N (2 * L) hN (by linarith)
  calc
    _ ≤ (K * N * B) ^ (ε / 2) *
        (C * (N * (2 * L)) ^ (ε / 2) * (N + 2 * L + (N * (2 * L)) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by positivity) _)
    _ ≤ (K * N * B) ^ (ε / 2) *
        (C * (N * (2 * L)) ^ (ε / 2) * (2 * (N + L + (N * L) ^ (2 / 3 : ℝ)))) := by
      gcongr
    _ = (2 * C * (2 : ℝ) ^ (ε / 2)) *
        ((K * N * B) ^ (ε / 2) * (N * L) ^ (ε / 2)) * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
      rw [hdouble]
      ring
    _ ≤ _ := by gcongr

theorem supportedHybridRow_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C * (K * N * B * L) ^ ε * (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C0, hC0, he⟩ := supportedHybridRow_energy_sieve_norm (ε / 2) (by positivity)
  obtain ⟨C1, hC1, hc⟩ := hybrid_sharp_cubic_factor ε hε
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro K N B L hK hN hB hL rows S Pset a beta hrows hS hP ha hbeta
  apply (he K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta).trans
  have hh := mul_le_mul_of_nonneg_left (hc K N B L hK hN hB hL)
    (show 0 ≤ C0 * (K + N * B) * B by positivity)
  convert hh using 1 <;> ring

theorem hybridRow_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B * L) ^ ε * (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C0, hC0, he⟩ := hybridRow_energy_sieve_norm (ε / 2) (by positivity)
  obtain ⟨C1, hC1, hc⟩ := hybrid_sharp_cubic_factor ε hε
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro K N B L hK hN hB hL rows nset bset Pset a beta hrows hn hb hP ha hbeta
  apply (he K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta).trans
  have hh := mul_le_mul_of_nonneg_left (hc K N B L hK hN hB hL)
    (show 0 ≤ C0 * (K + N * B) * B by positivity)
  convert hh using 1 <;> ring

end
end SevenEighths.InverseMoment

end OAI

end Source1482

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Energy.lean; sha256: a549a0cc0b93eb4ed9fd88168a2ff616341877e43704fc86dd5596926f46cd8e -/
section Source1483
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualRowPhaseExtension (F : PrimeFamily φ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (u : Eisˣ) (m : ℕ) (K : Ideal Eis) : ℂ :=
  if hK : Admissible K then actualRowPhase F K hK jF s u m else 0

def reflectedBranchHybridRow (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) : ℂ :=
  ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF κ s u m*
    actualRowPhaseExtension F jF s u m K)*
    hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m)
      (frozenBranchColumn F jF e A) K

lemma hybridRow_frozenColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (Pset nset bset : Finset (Ideal Eis))
    (aP : Ideal Eis → ℂ) (K : Ideal Eis) :
    hybridRow Pset nset bset aP (frozenBranchColumn F jF e A) K =
      (frozenBranchScale F jF e:ℂ)*hybridRow Pset nset bset aP (normalizedFrozenColumn F jF e A) K := by
  unfold hybridRow hybridInner
  simp_rw [frozenBranchColumn_eq_normalized]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem actual_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∑ K ∈ rows, ‖reflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Y*B*L)^ε*(X+Y*B)*B*(Y+L+(Y*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S hrows hrowcop _hproducts hScop hSN hSchar hn hb hP
  have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m‖ ≤ 1 :=
    (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2
  have hcolumn : ∀ n b, ‖normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m) n b‖ ≤ 1 :=
    normalizedFrozenColumn_norm_le_one F jF e _ (actualCuspColumn_norm_le_one D0 s hc u m)
  have hh := he X Y B L hX hY hB hL rows nset bset Pset
    (fun P => actualSlotPhase F (S P) jF s u m)
    (normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m)) hrows hn hb hP hslot
    (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m)
          (normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m)) K‖^2) ≤ _)
  rw [reflectedBranchHybridRow,hybridRow_frozenColumn]
  have hp := frozenBranchScale_pos F jF e
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK)
  rw [norm_mul,norm_mul (frozenBranchScale F jF e:ℂ) _,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow,mul_pow]
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖^2 ≤ 1 := by
    have hpos := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*actualRowPhaseExtension F jF s u m K)
    nlinarith
  exact (mul_le_mul_of_nonneg_right hs (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq (one_mul _)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1483

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SourceSum.lean; sha256: 972c0d8f29c440371c9e830be36717d8ce06fd0a9531b3bf08cdfb742674abfc -/
section Source1484
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : Eis} {mode : Bool}

theorem masked_actual_coefficient (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (P : Ideal Eis) (hprod : (∏ i, S.ideal i) = P) (jF : φ → ℕ)
    (D : IsCoprime K P → ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (hcop : IsCoprime K P → Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ h, (D h).fixedFactor = D0.fixedFactor)
    (hA : ∀ h u m n b, actualCuspColumn (D h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (if h : IsCoprime K P then actualMixedCoefficient F K hK S jF (D h) s hc u m n b else 0) =
      ∑ e : φ → Fin 3,
        ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
          actualRowPhaseExtension F jF s u m K)*
        (actualSlotPhase F S jF s u m / (Real.sqrt (Ideal.absNorm P:ℝ):ℂ))*
        (if IsCoprime K P then 1 else 0)*
        (frozenBranchColumn F jF e (actualCuspColumn D0 s hc u m) n b*
          quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
          (if IsCoprime P b then 1 else 0)) := by
  by_cases hKP : IsCoprime K P
  · rw [dite_eq_left hKP]
    have hh := actualMixedCoefficient_common_branches F K hK S jF (D hKP) s hc (hcop hKP)
      D0.fixedFactor (actualCuspColumn D0 s hc) (hκ hKP) (hA hKP) u m n b hb
    rw [hprod] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro e he
    rw [actualRowPhaseExtension,dite_eq_left hK,frozenBranchColumn_eq_normalized]
    simp only [ite_eq_left hKP,div_eq_mul_inv]
    ring
  · simp only [dite_eq_right hKP,ite_eq_right hKP,mul_zero,zero_mul,Finset.sum_const_zero]

def actualPhysicalReflectedRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) : ℂ :=
  ∑ P : Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    if h : IsCoprime K P.val then actualMixedCoefficient F K hK (S P.val) jF (D P h) s hc u m n b else 0

theorem actualPhysicalReflectedRow_eq_branches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (hcop : ∀ P : Pset, IsCoprime K P.val →
      Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ P h, (D P h).fixedFactor = D0.fixedFactor)
    (hA : ∀ P h u m n b, actualCuspColumn (D P h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0) (u : Eisˣ) (m : ℕ) :
    actualPhysicalReflectedRow F K hK S jF Pset nset bset D s hc u m =
      ∑ e : φ → Fin 3, reflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) u m Pset nset bset K := by
  unfold actualPhysicalReflectedRow
  have he (P : Pset) (n : Ideal Eis) (b : Ideal Eis) (hb' : b ∈ bset) :=
    masked_actual_coefficient F K hK (S P.val) P.val (hprod P.val P.property) jF
      (D P) (hcop P) G0 D0 s hc (hκ P) (hA P) u m n b (hb b hb')
  simp_rw [reflectedBranchHybridRow,hybridRow,hybridInner,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort Pset]
  apply Finset.sum_congr rfl
  intro P hP
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb'
  rw [he P n b hb']
  apply Finset.sum_congr rfl
  intro e he'
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1484

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Extraction.lean; sha256: 2636d26a2c1cd9c5f7e0049c886dafd100b978182ba3efa48f6d3b5337e5ddb2 -/
section Source1485
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ]

lemma frozenBranchColumn_divisibility (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : frozenBranchColumn F jF e A n b ≠ 0) :
    frozenExtracted F jF e 1 ∣ n ∧ frozenExtracted F jF e 2 ∣ b ∧
      ∀ i, jF i=4 → e i=2 → primaryGenerator n ∉ F.ideal i := by
  have hcp : Pairwise (fun i k => IsCoprime (Ideal.span {F.generator i}) (Ideal.span {F.generator k})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hh := reflectedBranch_divisibility (fun i => Ideal.span {F.generator i}) F.generator_good hcp
    jF e (primaryGenerator n) (primaryGenerator b) (mul_ne_zero_iff.mp hz).2
  simpa only [frozenExtracted,(primaryGenerator_spec n hn).1,(primaryGenerator_spec b hb).1,
    PrimeFamily.generator_span] using hh

lemma frozenBranchColumn_zero_of_not_dvd (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : ¬ frozenExtracted F jF e 1 ∣ n ∨ ¬ frozenExtracted F jF e 2 ∣ b) :
    frozenBranchColumn F jF e A n b = 0 := by
  by_contra hh
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b hn hb hh
  exact hz.elim (fun h => h hd1) (fun h => h hd2)

theorem frozenBranchColumn_dual_reindex (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A W : Ideal Eis → Ideal Eis → ℂ) (nset bset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0) :
    (∑ n ∈ nset, ∑ b ∈ bset, frozenBranchColumn F jF e A n b*W n b) =
      ∑ n ∈ quotientSupport (frozenExtracted F jF e 1) nset,
        ∑ b ∈ quotientSupport (frozenExtracted F jF e 2) bset,
          frozenBranchColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)*
            W ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b) := by
  classical
  have hfilter :
      (∑ n ∈ nset, ∑ b ∈ bset, frozenBranchColumn F jF e A n b*W n b) =
      ∑ n ∈ nset with frozenExtracted F jF e 1 ∣ n,
        ∑ b ∈ bset with frozenExtracted F jF e 2 ∣ b, frozenBranchColumn F jF e A n b*W n b := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn'
    by_cases hd1 : frozenExtracted F jF e 1 ∣ n
    · rw [ite_eq_left hd1]
      apply Finset.sum_congr rfl
      intro b hb'
      by_cases hd2 : frozenExtracted F jF e 2 ∣ b
      · rw [ite_eq_left hd2]
      · rw [ite_eq_right hd2,frozenBranchColumn_zero_of_not_dvd F hF jF e A n b (hn n hn') (hb b hb') (Or.inr hd2),zero_mul]
    · rw [ite_eq_right hd1]
      apply Finset.sum_eq_zero
      intro b hb'
      rw [frozenBranchColumn_zero_of_not_dvd F hF jF e A n b (hn n hn') (hb b hb') (Or.inl hd1),zero_mul]
  rw [hfilter,sum_quotientSupport]
  apply Finset.sum_congr rfl
  intro n hn'
  exact sum_quotientSupport _ _ _

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1485

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ExtractedKernel.lean; sha256: 5c9d4ed85a3e7a94c9c42e1a872b33482b66b3e867358a12011d3cf313fb30da -/
section Source1486
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def extractedRowFactor (D1 D2 K : Ideal Eis) : ℂ := quadraticRow K (primaryGenerator (D1*D2))
def extractedSlotFactor (D1 D2 P : Ideal Eis) : ℂ :=
  inverseCubicKernel P D1 * (if IsCoprime P D2 then 1 else 0)

lemma extractedRowFactor_norm_le_one (D1 D2 K : Ideal Eis) : ‖extractedRowFactor D1 D2 K‖ ≤ 1 :=
  quadraticRow_norm_le_one K _

lemma extractedSlotFactor_norm_le_one (D1 D2 P : Ideal Eis) : ‖extractedSlotFactor D1 D2 P‖ ≤ 1 := by
  unfold extractedSlotFactor
  split_ifs
  · simpa only [mul_one] using inverseCubicKernel_norm_le_one P D1
  · simp

lemma coprime_product_mask (P D b : Ideal Eis) :
    (if IsCoprime P (D*b) then (1:ℂ) else 0) =
      (if IsCoprime P D then 1 else 0)*(if IsCoprime P b then 1 else 0) := by
  by_cases hD : IsCoprime P D <;> by_cases hb : IsCoprime P b
  · simp [hD,hb,hD.mul_right hb]
  · have hn : ¬IsCoprime P (D*b) := fun h => hb (h.of_isCoprime_of_dvd_right (dvd_mul_left _ _))
    simp [hD,hb,hn]
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
    simp [hD,hb,hn]
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
    simp [hD,hb,hn]

theorem forced_dual_kernel_factor (D1 D2 K P n b : Ideal Eis)
    (hK : Admissible K) (hP : primaryGenerator P ≠ 0) :
    quadraticRow K (primaryGenerator ((D1*n)*(D2*b)))*inverseCubicKernel P (D1*n)*
      (if IsCoprime P (D2*b) then 1 else 0)*(if IsCoprime K P then 1 else 0) =
      (extractedRowFactor D1 D2 K*extractedSlotFactor D1 D2 P)*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
        (if IsCoprime P b then 1 else 0)*(if IsCoprime K P then 1 else 0) := by
  rw [show (D1*n)*(D2*b)=(D1*D2)*(n*b) by ring,primaryGenerator_mul,
    canonical_quadraticRow_argument_mul K hK,inverseCubicKernel_mul_right P D1 n hP,
    coprime_product_mask]
  unfold extractedRowFactor extractedSlotFactor
  ring

def extractedFrozenColumn {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  normalizedFrozenColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)

lemma extractedFrozenColumn_norm_le_one {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ)
    (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) : ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
  normalizedFrozenColumn_norm_le_one F jF e A hA _ _

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1486

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ExtractedRow.lean; sha256: 73df1424ebcb53259599e3e8d01c666fb12335b32d1f2a953677c2fde4472f47 -/
section Source1487
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ]

lemma hybridInner_frozen_dual_reindex (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (nset bset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (K P : Ideal Eis) :
    hybridInner nset bset (frozenBranchColumn F jF e A) K P =
      ∑ n ∈ quotientSupport (frozenExtracted F jF e 1) nset,
        ∑ b ∈ quotientSupport (frozenExtracted F jF e 2) bset,
          frozenBranchColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)*
            quadraticRow K (primaryGenerator (((frozenExtracted F jF e 1)*n)*((frozenExtracted F jF e 2)*b)))*
            inverseCubicKernel P ((frozenExtracted F jF e 1)*n)*
            (if IsCoprime P ((frozenExtracted F jF e 2)*b) then 1 else 0) := by
  simpa only [hybridInner,mul_assoc] using frozenBranchColumn_dual_reindex F hF jF e A
    (fun n b => quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*(if IsCoprime P b then 1 else 0))
    nset bset hn hb

theorem hybridRow_frozen_extraction (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (nset bset Pset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (aP : Ideal Eis → ℂ) (K : Ideal Eis) (hK : Admissible K)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0) :
    hybridRow Pset nset bset aP (frozenBranchColumn F jF e A) K =
      ((frozenBranchScale F jF e:ℂ)*extractedRowFactor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2) K)*
        hybridRow Pset (quotientSupport (frozenExtracted F jF e 1) nset)
          (quotientSupport (frozenExtracted F jF e 2) bset)
          (fun P => aP P*extractedSlotFactor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2) P)
          (extractedFrozenColumn F jF e A) K := by
  unfold hybridRow
  simp_rw [hybridInner_frozen_dual_reindex F hF jF e A nset bset hn hb]
  simp only [hybridInner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP'
  apply Finset.sum_congr rfl
  intro n hn'
  apply Finset.sum_congr rfl
  intro b hb'
  rw [frozenBranchColumn_eq_normalized]
  have hh := forced_dual_kernel_factor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2)
    K P n b hK (hP P hP')
  have he := congrArg (fun z : ℂ => aP P/(Real.sqrt (Ideal.absNorm P:ℝ):ℂ)*
    (frozenBranchScale F jF e:ℂ)*extractedFrozenColumn F jF e A n b*z) hh
  convert he using 1 <;> simp only [extractedFrozenColumn,div_eq_mul_inv] <;> ring

lemma quotientSupport_norm_div (D : Ideal Eis) (hD : D ≠ 0) (S : Finset (Ideal Eis)) (Y : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ Y) (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J:ℝ) ≤ Y/(Ideal.absNorm D:ℝ) := by
  have hpos : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hh := hS (D*J) ((mem_quotientSupport D J hD S).mp hJ)
  rw [map_mul,Nat.cast_mul] at hh
  exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hh)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1487

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ExtractedEnergy.lean; sha256: e3df6f6a09c46334b2a05af8d5227e14e4c3b8f9bfbba0cb701006474cc024cf -/
section Source1488
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : Eis} {mode : Bool}

def extractedDualScale (D : Ideal Eis) (Y : ℝ) : ℝ := max 1 (Y/(Ideal.absNorm D:ℝ))

theorem frozen_hybrid_energy_extracted (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y B L : ℝ, 1 ≤ X → 1 ≤ L →
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ → ℕ) (e : φ → Fin 3), ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0) (u : Eisˣ) (m : ℕ)
      (rows nset bset Pset : Finset (Ideal Eis)) (aP : Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ P ∈ Pset, ‖aP P‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖hybridRow Pset nset bset aP
        (frozenBranchColumn F jF e (actualCuspColumn D0 s hc u m)) K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hL F hF jF e ι _ G0 D0 s hc u m rows nset bset Pset aP hrows hn hb hP ha
  let D1 := frozenExtracted F jF e 1
  let D2 := frozenExtracted F jF e 2
  let Yq := extractedDualScale D1 Y
  let Bq := extractedDualScale D2 B
  have hD1 : D1 ≠ 0 := frozenExtracted_ne_zero F jF e 1
  have hD2 : D2 ≠ 0 := frozenExtracted_ne_zero F jF e 2
  have hnq : ∀ n ∈ quotientSupport D1 nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Yq := by
    intro n hn'
    exact ⟨quotientSupport_cubic_admissible D1 hD1 nset (fun n h => (hn n h).1) n hn',
      (quotientSupport_norm_div D1 hD1 nset Y (fun n h => (hn n h).2) n hn').trans (le_max_right _ _)⟩
  have hbq : ∀ b ∈ quotientSupport D2 bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ Bq := by
    intro b hb'
    have hsource := hb (D2*b) ((mem_quotientSupport D2 b hD2 bset).mp hb')
    rw [primaryGenerator_mul] at hsource
    exact ⟨(mul_ne_zero_iff.mp hsource.1).2,
      (quotientSupport_norm_div D2 hD2 bset B (fun b h => (hb b h).2) b hb').trans (le_max_right _ _)⟩
  have hacoeff : ∀ P ∈ Pset, ‖aP P*extractedSlotFactor D1 D2 P‖ ≤ 1 := by
    intro P hP'
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha P hP')).trans (extractedSlotFactor_norm_le_one D1 D2 P)
  have hcolumn : ∀ n b, ‖extractedFrozenColumn F jF e (actualCuspColumn D0 s hc u m) n b‖ ≤ 1 :=
    extractedFrozenColumn_norm_le_one F jF e _ (actualCuspColumn_norm_le_one D0 s hc u m)
  have hh := he X Yq Bq L hX (le_max_left _ _) (le_max_left _ _) hL rows
    (quotientSupport D1 nset) (quotientSupport D2 bset) Pset
    (fun P => aP P*extractedSlotFactor D1 D2 P)
    (extractedFrozenColumn F jF e (actualCuspColumn D0 s hc u m))
    hrows hnq hbq hP hacoeff (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset (quotientSupport D1 nset) (quotientSupport D2 bset)
          (fun P => aP P*extractedSlotFactor D1 D2 P)
          (extractedFrozenColumn F jF e (actualCuspColumn D0 s hc u m)) K‖^2) ≤ _)
  rw [hybridRow_frozen_extraction F hF jF e _ nset bset Pset
    (fun n h => (hn n h).1.2) (fun b h => (hb b h).1) aP K (hrows K hK).1
    (fun P h => (hP P h).1.2)]
  have hp := frozenBranchScale_pos F jF e
  have hs := extractedRowFactor_norm_le_one D1 D2 K
  have hs2 : ‖extractedRowFactor D1 D2 K‖^2 ≤ 1 := by
    have h0 := norm_nonneg (extractedRowFactor D1 D2 K)
    nlinarith
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow]
  change (frozenBranchScale F jF e)^2*‖extractedRowFactor D1 D2 K‖^2* _ ≤ _
  calc
    _ ≤ ((frozenBranchScale F jF e)^2*1)*_ := by gcongr
    _ = _ := by rw [mul_one]

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1488

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ActualExtractedEnergy.lean; sha256: 0c35c6516192bb3ae29d3f3c9a05bfff6cef31d84c24288a0488dc6e55938e7b -/
section Source1489
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem actual_reflected_branch_energy_extracted (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖reflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := frozen_hybrid_energy_extracted (φ := φ) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX _hY _hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S hrows hrowcop _hproducts hScop hSN hSchar hn hb hP
  have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m‖ ≤ 1 :=
    (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    (he X Y B L hX hL F hF jF e G0 D0 s hc u m rows nset bset Pset
      (fun P => actualSlotPhase F (S P) jF s u m) hrows hn hb hP hslot)
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK)
  have hphase0 := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K)
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖^2 ≤ 1 := by nlinarith
  rw [reflectedBranchHybridRow,norm_mul,mul_pow]
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1489

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SourceFamily.lean; sha256: d9c8e4dfb38cd495859bffa58ab49a7b22fdc100663582207d10e29c037326e6 -/
section Source1490
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def SourcePair (rows Pset : Finset (Ideal Eis)) :=
  {x : rows × Pset // IsCoprime x.1.val x.2.val}

variable {φ σ : Type*} [Fintype φ] [Fintype σ]

theorem exists_source_pair_templates (F : PrimeFamily φ)
    (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
    (hrows : ∀ K ∈ rows, Admissible K)
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hScop : ∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i)) :
    ∃ E : ∀ x : SourcePair rows Pset,
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)).generator N a c mode,
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (A : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ q, ‖κ q‖ ≤ 1) ∧ (∀ q u m n b, ‖A q u m n b‖ ≤ 1) ∧
        (∀ x, (E x).fixedFactor = κ (separateSector N (primaryGenerator x.val.1.val)
          (primaryGenerator x.val.2.val))) ∧
        ∀ x u m n b, actualCuspColumn (E x) s hc u m n b =
          A (separateSector N (primaryGenerator x.val.1.val) (primaryGenerator x.val.2.val)) u m n b := by
  let G := fun x : SourcePair rows Pset =>
    F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)
  have hpair (x : SourcePair rows Pset) : Pairwise (Function.onFun IsCoprime (G x).ideal) := by
    apply F.reflected_pairwise x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val) hF
    · intro i k hik
      change IsCoprime ((F.sum (S x.val.2.val)).ideal (Sum.inr i))
        ((F.sum (S x.val.2.val)).ideal (Sum.inr k))
      exact hScop x.val.2.val x.val.2.property (Sum.inr_injective.ne hik)
    · rw [hprod _ x.val.2.property]
      exact x.property
    · exact (hrowcop _ x.val.1.property).1
    · intro f i
      change IsCoprime ((F.sum (S x.val.2.val)).ideal (Sum.inl f))
        ((F.sum (S x.val.2.val)).ideal (Sum.inr i))
      exact hScop x.val.2.val x.val.2.property (Sum.inl_ne_inr : (Sum.inl f : φ ⊕ σ) ≠ Sum.inr i)
  have hNp (x : SourcePair rows Pset) : ∀ i, IsCoprime (Ideal.span {N}) ((G x).ideal i) :=
    F.reflected_period _ _ _ N hNF (hrowcop _ x.val.1.property).2 (hSN _ x.val.2.property)
  apply canonical_bounded_cusp_templates G N a c mode s hc hN hbase hac hpair hNp
    (∏ i, F.ideal i) (fun x => x.val.1.val) (fun x => x.val.2.val)
  intro x
  rw [PrimeFamily.reflected_product,hprod _ x.val.2.property]

theorem source_templates_equal_to_representative {α : Type*} {ι : α → Type*}
    [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    {N a c : Eis} {mode : Bool}
    (E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    {Q : Type*} (q : α → Q) (κ : Q → ℂ) (A : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hκ : ∀ x, (E x).fixedFactor = κ (q x))
    (hA : ∀ x u m n b, actualCuspColumn (E x) s hc u m n b = A (q x) u m n b)
    (x0 x : α) (hq : q x = q x0) :
    (E x).fixedFactor = (E x0).fixedFactor ∧
      ∀ u m n b, actualCuspColumn (E x) s hc u m n b = actualCuspColumn (E x0) s hc u m n b := by
  constructor
  · rw [hκ x,hκ x0,hq]
  · intro u m n b
    rw [hA x u m n b,hA x0 u m n b,hq]

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1490

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Shape.lean; sha256: bd46e2483b90a22f208eebff854c84028391322a81446560e58c2ca84ac34102 -/
section Source1491
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CubicKubota ConcreteTraceCRT CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def shapeArgument (z : Eis) : ℂ := ((Ideal.absNorm (Ideal.span {z}):ℝ):ℂ)/(eisEmbedding z)^2

lemma shapeArgument_mul (x y : Eis) : shapeArgument (x*y) = shapeArgument x*shapeArgument y := by
  unfold shapeArgument
  rw [← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,Complex.ofReal_mul,map_mul,mul_pow]
  exact mul_div_mul_comm _ _ _ _

lemma shapeArgument_norm (z : Eis) (hz : z ≠ 0) : ‖shapeArgument z‖ = 1 := by
  have hne : ‖eisEmbedding z‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hz))
  rw [shapeArgument,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ← eisEmbedding_norm_sq_eq_absNorm_span]
  exact div_self hne

lemma stratumShapeFactor_mul {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r P : Eis) :
    s.stratumShapeFactor (c*r*P) = s.stratumShapeFactor c*shapeArgument r*shapeArgument P := by
  have he (z : Eis) : s.stratumShapeFactor z =
      (-star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2)*shapeArgument z := by
    unfold FixedCuspShape.stratumShapeFactor shapeArgument
    ring
  rw [he (c*r*P),he c,shapeArgument_mul,shapeArgument_mul]
  ring

lemma actual_shape_separation {φ σ : Type*} [Fintype φ] [Fintype σ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H)
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    s.stratumShapeFactor (c*∏ i, (F.reflected K hK S).generator i) =
      s.stratumShapeFactor (c*primaryGenerator (∏ i, F.ideal i))*
        shapeArgument (primaryGenerator K)*shapeArgument (primaryGenerator (∏ i, S.ideal i)) := by
  rw [(F.reflected K hK S).generator_product,F.reflected_product K hK S,
    primaryGenerator_mul,primaryGenerator_mul]
  rw [show c*(primaryGenerator (∏ i, F.ideal i)*primaryGenerator K*primaryGenerator (∏ i, S.ideal i)) =
    (c*primaryGenerator (∏ i, F.ideal i))*primaryGenerator K*primaryGenerator (∏ i, S.ideal i) by ring]
  exact stratumShapeFactor_mul s _ _ _

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1491

/- Original source: OAI/NumberTheory/DirichletL/Reflection/WeightedEnergy.lean; sha256: 417d1b0d5e7de4e82d725097a7f162449a51dc3b6902aaebdc9304dd11f1ee48 -/
section Source1492
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : Eis} {mode : Bool}

theorem bounded_column_hybrid_energy_extracted (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y B L : ℝ, 1 ≤ X → 1 ≤ L →
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ),
      (∀ n b, ‖A n b‖ ≤ 1) →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (aP : Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ P ∈ Pset, ‖aP P‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖hybridRow Pset nset bset aP
        (frozenBranchColumn F jF e A) K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hL F hF jF e A hA rows nset bset Pset aP hrows hn hb hP ha
  let D1 := frozenExtracted F jF e 1
  let D2 := frozenExtracted F jF e 2
  let Yq := extractedDualScale D1 Y
  let Bq := extractedDualScale D2 B
  have hD1 : D1 ≠ 0 := frozenExtracted_ne_zero F jF e 1
  have hD2 : D2 ≠ 0 := frozenExtracted_ne_zero F jF e 2
  have hnq : ∀ n ∈ quotientSupport D1 nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Yq := by
    intro n hn'
    exact ⟨quotientSupport_cubic_admissible D1 hD1 nset (fun n h => (hn n h).1) n hn',
      (quotientSupport_norm_div D1 hD1 nset Y (fun n h => (hn n h).2) n hn').trans (le_max_right _ _)⟩
  have hbq : ∀ b ∈ quotientSupport D2 bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ Bq := by
    intro b hb'
    have hsource := hb (D2*b) ((mem_quotientSupport D2 b hD2 bset).mp hb')
    rw [primaryGenerator_mul] at hsource
    exact ⟨(mul_ne_zero_iff.mp hsource.1).2,
      (quotientSupport_norm_div D2 hD2 bset B (fun b h => (hb b h).2) b hb').trans (le_max_right _ _)⟩
  have hacoeff : ∀ P ∈ Pset, ‖aP P*extractedSlotFactor D1 D2 P‖ ≤ 1 := by
    intro P hP'
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha P hP')).trans (extractedSlotFactor_norm_le_one D1 D2 P)
  have hcolumn : ∀ n b, ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
    extractedFrozenColumn_norm_le_one F jF e A hA
  have hh := he X Yq Bq L hX (le_max_left _ _) (le_max_left _ _) hL rows
    (quotientSupport D1 nset) (quotientSupport D2 bset) Pset
    (fun P => aP P*extractedSlotFactor D1 D2 P)
    (extractedFrozenColumn F jF e A)
    hrows hnq hbq hP hacoeff (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset (quotientSupport D1 nset) (quotientSupport D2 bset)
          (fun P => aP P*extractedSlotFactor D1 D2 P)
          (extractedFrozenColumn F jF e A) K‖^2) ≤ _)
  rw [hybridRow_frozen_extraction F hF jF e _ nset bset Pset
    (fun n h => (hn n h).1.2) (fun b h => (hb b h).1) aP K (hrows K hK).1
    (fun P h => (hP P h).1.2)]
  have hp := frozenBranchScale_pos F jF e
  have hs := extractedRowFactor_norm_le_one D1 D2 K
  have hs2 : ‖extractedRowFactor D1 D2 K‖^2 ≤ 1 := by
    have h0 := norm_nonneg (extractedRowFactor D1 D2 K)
    nlinarith
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow]
  change (frozenBranchScale F jF e)^2*‖extractedRowFactor D1 D2 K‖^2* _ ≤ _
  calc
    _ ≤ ((frozenBranchScale F jF e)^2*1)*_ := by gcongr
    _ = _ := by rw [mul_one]

lemma actualCuspWeightedColumn_norm_le_one {ι : Type*} [Fintype ι]
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (w : Ideal Eis → Ideal Eis → ℂ)
    (hw : ∀ n b, ‖w n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖actualCuspColumn D0 s hc u m n b*w n b‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (actualCuspColumn_norm_le_one D0 s hc u m n b)).trans (hw n b)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1492

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ActualWeightedEnergy.lean; sha256: b2ea7ce16eb0200ce84c6d1c0f2adb341a5bae2155df4e76ba27d552fc747235 -/
section Source1493
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def weightedReflectedBranchHybridRow (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) : ℂ :=
  ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF κ s u m*
    actualRowPhaseExtension F jF s u m K*r K)*
    hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m*aw P)
      (frozenBranchColumn F jF e (fun n b => A n b*w n b)) K

theorem actual_weighted_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := bounded_column_hybrid_energy_extracted (φ := φ) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX _hY _hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop _hproducts hScop hSN hSchar hn hb hP hr haw hw
  have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m*aw P‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2).trans
      (haw P hP)
  have hcol := actualCuspWeightedColumn_norm_le_one G0 D0 s hc u m w hw
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    (he X Y B L hX hL F hF jF e (fun n b => actualCuspColumn D0 s hc u m n b*w n b) hcol
      rows nset bset Pset (fun P => actualSlotPhase F (S P) jF s u m*aw P) hrows hn hb hP hslot)
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK))).trans (hr K hK)
  have hphase0 := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K)
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K‖^2 ≤ 1 := by nlinarith
  rw [weightedReflectedBranchHybridRow,norm_mul,mul_pow]
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1493

/- Original source: OAI/NumberTheory/DirichletL/Reflection/WeightedSourceSum.lean; sha256: 8a8effafa9862c77004892d06ff3f6e6c31b12d68ee9dddfdd90f5efb6259b14 -/
section Source1494
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : Eis} {mode : Bool}

def weightedPhysicalReflectedRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∑ P : Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    r K*aw P.val*w n b*(if h : IsCoprime K P.val then
      actualMixedCoefficient F K hK (S P.val) jF (D P h) s hc u m n b else 0)

theorem weightedPhysicalReflectedRow_eq_branches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (hcop : ∀ P : Pset, IsCoprime K P.val →
      Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ P h, (D P h).fixedFactor = D0.fixedFactor)
    (hA : ∀ P h u m n b, actualCuspColumn (D P h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) :
    weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc r aw w u m =
      ∑ e : φ → Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K := by
  unfold weightedPhysicalReflectedRow
  have he (P : Pset) (n : Ideal Eis) (b : Ideal Eis) (hb' : b ∈ bset) :=
    masked_actual_coefficient F K hK (S P.val) P.val (hprod P.val P.property) jF
      (D P) (hcop P) G0 D0 s hc (hκ P) (hA P) u m n b (hb b hb')
  simp_rw [weightedReflectedBranchHybridRow,hybridRow,hybridInner,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort Pset]
  apply Finset.sum_congr rfl
  intro P hP
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb'
  rw [he P n b hb',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he'
  unfold frozenBranchColumn
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1494

/- Original source: OAI/NumberTheory/DirichletL/Descent/SlotProducts.lean; sha256: 1ac5909236389b88d7698a901f54b4f73b88a29d918382b835a298e4e450c55c -/
section Source1495
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def slotTupleProduct (p : ι → Ideal Eis) : Ideal Eis := ∏ i, p i

theorem slotTupleProduct_injective_on
    (L : ι → Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P) :
    Set.InjOn (slotTupleProduct (ι := ι)) {p | ∀ i, p i ∈ L i} := by
  intro p hpL q hqL he
  funext i
  change (∏ i, p i) = ∏ i, q i at he
  have hdiv : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j, hj, hd⟩ := ((hp i (p i) (hpL i)).dvd_finsetProd_iff q).mp hdiv
  have hpq : p i = q j := associated_iff_eq.mp
    ((hp i (p i) (hpL i)).associated_of_dvd (hp j (q j) (hqL j)) hd)
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hL hne) (hpL i) (hpq.symm ▸ hqL j)
  simpa only [← hij] using hpq

omit [DecidableEq ι] in
theorem slotTupleProduct_admissible
    (L : ι → Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P)
    (hgen : ∀ i, ∀ P ∈ L i, primaryGenerator P ≠ 0)
    (p : ι → Ideal Eis) (hpL : ∀ i, p i ∈ L i) :
    CubicSieve.Admissible (slotTupleProduct p) := by
  constructor
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      have hpi := hp i (p i) (hpL i)
      have hpj := hp j (p j) (hpL j)
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime hpi).isMaximal hpi.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime hpj).isMaximal hpj.ne_zero
      apply (Ideal.isCoprime_of_isMaximal ?_).isRelPrime
      intro he
      exact Finset.disjoint_left.mp (hL hij) (hpL i) (he.symm ▸ hpL j)
    · intro i hi
      exact (hp i (p i) (hpL i)).squarefree
  · change primaryGeneratorHom (∏ i, p i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hgen i (p i) (hpL i))

def slotProductCoefficient (tuples : Finset (ι → Ideal Eis))
    (a : (ι → Ideal Eis) → ℂ) (P : Ideal Eis) : ℂ :=
  ∑ p ∈ tuples, if slotTupleProduct p = P then a p else 0

omit [DecidableEq ι] in
theorem slotProductCoefficient_at_product
    (tuples : Finset (ι → Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)))
    (a : (ι → Ideal Eis) → ℂ) (p : ι → Ideal Eis) (hp : p ∈ tuples) :
    slotProductCoefficient tuples a (slotTupleProduct p) = a p := by
  unfold slotProductCoefficient
  rw [Finset.sum_eq_single p]
  · simp
  · intro q hq hqp
    exact ite_eq_right (fun he => hqp (hinj hq hp he))
  · exact fun hn => (hn hp).elim

omit [DecidableEq ι] in
theorem active_slot_hybrid_reindex
    (tuples : Finset (ι → Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)))
    (nset bset : Finset (Ideal Eis)) (a : (ι → Ideal Eis) → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    (∑ p ∈ tuples, a p / (Real.sqrt (Ideal.absNorm (slotTupleProduct p) : ℝ) : ℂ) *
      (if IsCoprime k (slotTupleProduct p) then 1 else 0) *
        hybridInner nset bset beta k (slotTupleProduct p)) =
      hybridRow (tuples.image slotTupleProduct) nset bset (slotProductCoefficient tuples a) beta k := by
  rw [hybridRow, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro p hp
  rw [slotProductCoefficient_at_product tuples hinj a p hp]

theorem active_slot_hybrid_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B V : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (L : ι → Finset (Ideal Eis)),
      Pairwise (fun i j => Disjoint (L i) (L j)) →
      (∀ i, ∀ P ∈ L i, Prime P) → (∀ i, ∀ P ∈ L i, primaryGenerator P ≠ 0) →
    ∀ (tuples : Finset (ι → Ideal Eis)), (∀ p ∈ tuples, ∀ i, p i ∈ L i) →
      (∀ p ∈ tuples, V ≤ (Ideal.absNorm (slotTupleProduct p) : ℝ) ∧
        (Ideal.absNorm (slotTupleProduct p) : ℝ) ≤ 2 * V) →
    ∀ (rows nset bset : Finset (Ideal Eis)) (a : (ι → Ideal Eis) → ℂ)
      (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ p ∈ tuples, ‖a p‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ tuples,
        a p / (Real.sqrt (Ideal.absNorm (slotTupleProduct p) : ℝ) : ℂ) *
        (if IsCoprime k (slotTupleProduct p) then 1 else 0) *
          hybridInner nset bset beta k (slotTupleProduct p)‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * V) := by
  obtain ⟨C, hC, he⟩ := hybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B V hK hN hB L hL hp hgen tuples htuples hnorm rows nset bset a beta
    hrows hn hb ha hbeta
  have hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)) :=
    (slotTupleProduct_injective_on L hL hp).mono htuples
  have hP : ∀ P ∈ tuples.image slotTupleProduct,
      CubicSieve.Admissible P ∧ V ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * V := by
    intro P hP
    obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨slotTupleProduct_admissible L hL hp hgen p (htuples p hpT), hnorm p hpT⟩
  have hcoeff : ∀ P ∈ tuples.image slotTupleProduct, ‖slotProductCoefficient tuples a P‖ ≤ 1 := by
    intro P hP
    obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.mp hP
    rw [slotProductCoefficient_at_product tuples hinj a p hpT]
    exact ha p hpT
  simp_rw [active_slot_hybrid_reindex tuples hinj nset bset a beta]
  exact he K N B V hK hN hB rows nset bset (tuples.image slotTupleProduct)
    (slotProductCoefficient tuples a) beta hrows hn hb hP hcoeff hbeta

end
end SevenEighths.InverseMoment

end OAI

end Source1495

/- Original source: OAI/NumberTheory/DirichletL/Descent/CommonMeasure.lean; sha256: 8508f4b31a8921ade61f0cfe0015d5bdeedd49fcbb03e9f1aae8c425dbd0c7c8 -/
section Source1496
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open MeasureTheory CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem common_measure_energy {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (b : Ω → ℂ) (φ : κ → Ω → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖) μ)
    (hφ : ∀ k, Integrable (fun t => b t * φ k t) μ)
    (hbound : ∀ t, (∑ k, ‖φ k t‖ ^ 2) ≤ E) :
    (∑ k, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) ≤ E * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : Ω → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t * φ k t)
  have hF (t : Ω) : ‖F t‖ ≤ ‖b t‖ * Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE]
    change (∑ k, ‖b t * φ k t‖ ^ 2) ≤ ‖b t‖ ^ 2 * E
    simp only [norm_mul, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫ t, F t ∂μ) = e.symm (fun k => ∫ t, b t * φ k t ∂μ) := by
    rw [show F = (fun t => e.symm (fun k => b t * φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t, b t * φ k t ∂μ)‖ ≤
      (∫ t, ‖b t‖ ∂μ) * Real.sqrt E := by
    rw [← he, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE] at hs
  simpa [e, mul_comm] using hs

theorem integrated_hybridRow_energy {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ v ∈ bset, primaryGenerator v ≠ 0 ∧ (Ideal.absNorm v : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
    ∀ (μ : Measure Ω) (b : Ω → ℂ)
      (a : Ω → Ideal Eis → ℂ) (beta : Ω → Ideal Eis → Ideal Eis → ℂ)
      (rowPhase : Ideal Eis → Ω → ℂ) (m : ℂ),
      Integrable b μ →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => a t P) μ) →
      (∀ n ∈ nset, ∀ v ∈ bset, AEStronglyMeasurable (fun t => beta t n v) μ) →
      (∀ k ∈ rows, AEStronglyMeasurable (rowPhase k) μ) →
      (∀ t, ∀ P ∈ Pset, ‖a t P‖ ≤ 1) →
      (∀ t, ∀ n ∈ nset, ∀ v ∈ bset, ‖beta t n v‖ ≤ 1) →
      (∀ k ∈ rows, ∀ t, ‖rowPhase k t‖ ≤ 1) →
      (∑ k ∈ rows, ‖m * ∫ t, b t * (rowPhase k t *
        hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2) ≤
      ‖m‖ ^ 2 * (C * (K * N * B) ^ ε * (K + N * B) * B *
        CubicSieve.sieveNorm N (2 * L)) * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  obtain ⟨C, hC, he⟩ := hybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B L hK hN hB rows nset bset Pset hrows hn hv hP μ b a beta phase m
    hb haM hbetaM hphaseM ha hbeta hphase
  let E := C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L)
  have hE : 0 ≤ E := by
    have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
    dsimp only [E]
    positivity
  let φ : rows → Ω → ℂ := fun k t => phase k t * hybridRow Pset nset bset (a t) (beta t) k
  have hbound (t : Ω) : (∑ k, ‖φ k t‖ ^ 2) ≤ E := by
    calc
      _ ≤ ∑ k : rows, ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hphase k k.property t)
      _ = ∑ k ∈ rows, ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2 := by
        exact Finset.sum_coe_sort rows (fun k : Ideal Eis => ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2)
      _ ≤ E := he K N B L hK hN hB rows nset bset Pset (a t) (beta t)
        hrows hn hv hP (ha t) (hbeta t)
  have hφM (k : rows) : AEStronglyMeasurable (φ k) μ := by
    apply (hphaseM k k.property).mul
    unfold hybridRow
    apply Finset.aestronglyMeasurable_fun_sum
    intro P hPS
    simp only [div_eq_mul_inv]
    apply ((haM P hPS).mul_const _ |>.mul_const _).mul
    unfold hybridInner
    apply Finset.aestronglyMeasurable_fun_sum
    intro n hns
    apply Finset.aestronglyMeasurable_fun_sum
    intro v hvs
    exact (((hbetaM n hns v hvs).mul_const _).mul_const _).mul_const _
  have hpoint (k : rows) (t : Ω) : ‖φ k t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖φ j t‖)
      (Finset.mem_univ k)).trans (hbound t)
  have hint (k : rows) : Integrable (fun t => b t * φ k t) μ :=
    hb.mul_bdd (hφM k) (Filter.Eventually.of_forall (hpoint k))
  have hm := mul_le_mul_of_nonneg_left
    (common_measure_energy μ b φ E hE hb.norm hint hbound) (sq_nonneg ‖m‖)
  simp only [norm_mul, mul_pow, ← Finset.mul_sum] at hm ⊢
  rw [mul_assoc]
  rw [show (∑ k : rows, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) =
      ∑ k ∈ rows, ‖∫ t, b t * (phase k t * hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2 from
    Finset.sum_coe_sort rows (fun k : Ideal Eis =>
      ‖∫ t, b t * (phase k t * hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2)] at hm
  exact hm

end
end SevenEighths.InverseMoment

end OAI

end Source1496

/- Original source: OAI/NumberTheory/DirichletL/Reflection/WeightedMeasurable.lean; sha256: 1545cd8bb6074c2a89164d78e52dcabc8f94c77deb8c597035730ac96009f8c0 -/
section Source1497
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

lemma weightedReflectedBranchHybridRow_aestronglyMeasurable
    (μ : Measure Ω) (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ)
    (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ)
    (u : Eisˣ) (m : ℕ) (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis)
    (hr : AEStronglyMeasurable (fun t => r t K) μ)
    (ha : ∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ)
    (hw : ∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) :
    AEStronglyMeasurable (fun t => weightedReflectedBranchHybridRow F jF e S s κ A
      (r t) (aw t) (w t) u m Pset nset bset K) μ := by
  unfold weightedReflectedBranchHybridRow
  apply (hr.const_mul _).mul
  unfold hybridRow
  apply Finset.aestronglyMeasurable_fun_sum
  intro P hP
  simp only [div_eq_mul_inv]
  apply (((ha P hP).const_mul _).mul_const _ |>.mul_const _).mul
  unfold hybridInner
  apply Finset.aestronglyMeasurable_fun_sum
  intro n hn
  apply Finset.aestronglyMeasurable_fun_sum
  intro b hb
  unfold frozenBranchColumn
  exact (((((hw n hn b hb).const_mul _).mul_const _).mul_const _).mul_const _).mul_const _

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1497

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CommonMeasure.lean; sha256: 7f00c590a7d9bc54a12fe747d9a89f8146cad289d12df5b6686004ac14942795 -/
section Source1498
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem integrated_actual_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2) ≤
      ‖scalar‖^2*((frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := actual_weighted_reflected_branch_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
  let Bq := extractedDualScale (frozenExtracted F jF e 2) B
  let E : ℝ := (frozenBranchScale F jF e)^2*
    (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ)))
  have hYq : 1 ≤ Yq := le_max_left _ _
  have hBq : 1 ≤ Bq := le_max_left _ _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let ψ : rows → Ω → ℂ := fun K t => weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
    (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val
  have hbound (t : Ω) : (∑ K, ‖ψ K t‖^2) ≤ E := by
    change (∑ K : rows, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val‖^2) ≤ E
    rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K‖^2)]
    exact he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
      G0 D0 u m rows nset bset Pset S (r t) (aw t) (w t)
      hrows hrowcop hproducts hScop hSN hSchar hn hb hP (hr t) (haw t) (hw t)
  have hψM (K : rows) : AEStronglyMeasurable (ψ K) μ :=
    weightedReflectedBranchHybridRow_aestronglyMeasurable μ F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K.val
      (hrM K.val K.property) hawM hwM
  have hpoint (K : rows) (t : Ω) : ‖ψ K t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j t‖) (Finset.mem_univ K)).trans (hbound t)
  have hint (K : rows) : Integrable (fun t => density t*ψ K t) μ :=
    hdensity.mul_bdd (hψM K) (Filter.Eventually.of_forall (hpoint K))
  have hh := mul_le_mul_of_nonneg_left
    (common_measure_energy μ density ψ E hE hdensity.norm hint hbound) (sq_nonneg ‖scalar‖)
  have hsum : (∑ K : rows, ‖∫ t, density t*ψ K t ∂μ‖^2) =
      ∑ K ∈ rows, ‖∫ t, density t*weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2 :=
    Finset.sum_coe_sort rows (fun K : Ideal Eis =>
      ‖∫ t, density t*weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2)
  rw [hsum] at hh
  simp only [norm_mul,mul_pow,← Finset.mul_sum]
  simpa only [E,Yq,Bq,mul_assoc] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1498

/- Original source: OAI/NumberTheory/DirichletL/Descent/Widths.lean; sha256: 6b7d67df4751dcec7b2cbf008eef2551f33577a0e100989aae7af900ca65e771 -/
section Source1499
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma actual_ideal_norm_pos (I : Ideal Eis) (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))

theorem actual_residual_norm_width (I Q : Ideal Eis) (hI : I ≠ 0) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
      (Ideal.absNorm (rowPowerfulPart I) : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have hm : 1 ≤ (Ideal.absNorm (rowMaskPart I Q) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz =>
      squarefreeMaskPart_ne_zero (rowSimplePart I) Q (Ideal.absNorm_eq_zero_iff.mp hz))
  have he := congrArg (fun J : Ideal Eis => (Ideal.absNorm J : ℝ))
    (row_powerful_mask_residual_product I Q hI)
  simp only [map_mul, Nat.cast_mul] at he
  calc
    _ ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm (rowMaskPart I Q) : ℝ) * (Ideal.absNorm (rowResidualPart I Q) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
          (Ideal.absNorm (rowPowerfulPart I) : ℝ) by positivity)
      nlinarith [hh]
    _ = _ := he

theorem actual_common_width_charge {ι : Type*} [Fintype ι]
    (I F Q : Ideal Eis) (hI : I ≠ 0) (hQ : Q ≠ 0)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * Q)
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I Q) (e : ι → Fin 3) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm Q : ℝ) := by
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hm := actual_ideal_norm_pos (rowMaskPart I Q)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)
  have he := rowResidualPart_norm I Q hI
  calc
    _ ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
        ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowMaskPart I Q) : ℝ)^2 * (Ideal.absNorm Q : ℝ)) :=
      mul_le_mul_of_nonneg_left (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
        (sq_nonneg _)
    _ = _ := by rw [he]; field_simp

theorem actual_common_width_charge_label_puncture {ι : Type*} [Fintype ι]
    (I F rho S : Ideal Eis) (hI : I ≠ 0) (hF : F ≠ 0) (hrho : rho ≠ 0) (hS : S ≠ 0)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (S * F * rho))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (S * F * rho)) (e : ι → Fin 3) :
    (Ideal.absNorm (rowResidualPart I (S * F * rho)) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm S : ℝ) *
        ((Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ)) *
        (Ideal.absNorm F : ℝ) * (Ideal.absNorm rho : ℝ) := by
  convert actual_common_width_charge I F (S * F * rho) hI
    (mul_ne_zero (mul_ne_zero hS hF) hrho) P hcop hpool hres e using 1
  simp only [map_mul, Nat.cast_mul]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source1499

/- Original source: OAI/NumberTheory/DirichletL/Descent/Basic.lean; sha256: 1378e578d6059a8499e4619e162d1ca7ea94e5b08cf1f80b94a5dfe580983cf6 -/
section Source1500
namespace OAI

namespace SevenEighths.InverseMoment

def MarkedMargins (m r z c : ℝ) : Prop :=
  r + 2 * z ≤ m - c ∧ 2 * r + 8 * z ≤ 3 * m - c

def CanonicalMargins (F M Q z c : ℝ) : Prop :=
  c ≤ F - M - Q - z ∧ c ≤ 4 * F - 3 * M - 6 * z

theorem markedMargins_of_strict {m r z : ℝ}
    (h₁ : r + 2 * z < m) (h₂ : 2 * r + 8 * z < 3 * m) :
    ∃ c > 0, MarkedMargins m r z c := by
  refine ⟨min (m - r - 2 * z) (3 * m - 2 * r - 8 * z), ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · constructor
    · have := min_le_left (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith
    · have := min_le_right (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith

theorem markedMargins_subcollection {m r z z' c : ℝ}
    (h : MarkedMargins m r z c) (hz : z' ≤ z) :
    MarkedMargins m r z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

theorem canonicalMargins_subcollection {F M Q z z' c : ℝ}
    (h : CanonicalMargins F M Q z c) (hz : z' ≤ z) :
    CanonicalMargins F M Q z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

theorem canonicalMargins_weaken {F M Q z c c' : ℝ}
    (h : CanonicalMargins F M Q z c) (hc : c' ≤ c) :
    CanonicalMargins F M Q z c' := by
  exact ⟨hc.trans h.1, hc.trans h.2⟩

def decrease (ell A t g theta V : ℝ) : ℝ := ell + A + t + g - theta + V

def childF (F ell A t g theta V j delta : ℝ) : ℝ :=
  F - decrease ell A t g theta V - 2 * ell + j + delta

def childM (M ell A t g theta V j eta : ℝ) : ℝ :=
  M - 2 * decrease ell A t g theta V - 2 * ell + j + eta

theorem canonical_transition (F M ell A t g theta V j : ℝ) :
    childF F ell A t g theta V j 0 - childM M ell A t g theta V j 0 =
      F - M + decrease ell A t g theta V ∧
    4 * childF F ell A t g theta V j 0 -
      3 * childM M ell A t g theta V j 0 =
      4 * F - 3 * M + 2 * (A + t + g - theta + V) + j := by
  constructor <;> unfold childF childM decrease <;> ring

theorem child_margins_sharp {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    c + delta - 5 * eta ≤
      childF F ell A t g theta V j delta -
      childM M ell A t g theta V j eta - Q' - z ∧
    c + 4 * delta - 7 * eta ≤
      4 * childF F ell A t g theta V j delta -
      3 * childM M ell A t g theta V j eta - 6 * z := by
  obtain ⟨h₁, h₂⟩ := h
  unfold childF childM decrease at *
  constructor <;> linarith

theorem child_margins {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q' z (c - 7 * eta) := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := delta) h hA ht hV hj hgt hQ
  constructor <;> linarith

theorem child_row_decrease {M ell A t g theta V j eta d : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hgt : -2 * eta ≤ g - theta)
    (hj : j ≤ 2 * ell + 3 * eta) (hterminal : d ≤ ell + V)
    (heta : eta ≤ d / 16) :
    3 * d / 2 ≤ M - childM M ell A t g theta V j eta := by
  unfold childM decrease
  linarith

theorem childF_upper {F ell A t g theta V j delta eta : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hell : 0 ≤ ell) (hV : 0 ≤ V)
    (hgt : -2 * eta ≤ g - theta) (hj : j ≤ 2 * ell + 3 * eta)
    (hdelta : delta ≤ 6 * eta) :
    childF F ell A t g theta V j delta ≤ F + 11 * eta := by
  unfold childF decrease
  linarith

theorem clipping_bounds {N eta : ℝ} (heta : 0 ≤ eta) (hN : -6 * eta ≤ N) :
    0 ≤ max 0 N - N ∧ max 0 N - N ≤ 6 * eta := by
  constructor
  · exact sub_nonneg.mpr (le_max_right 0 N)
  · rcases le_total 0 N with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

theorem step_energy_exponent {F Fc kappa lambda count delta eta tau pi eps : ℝ}
    (hid : kappa + lambda + count + 2 * Fc = F)
    (hdelta : delta ≤ 6 * eta) :
    kappa + lambda + count + 2 * (Fc + delta) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      F + 40 * eta + tau + pi + eps := by
  linarith

def initialF (r z G P delta : ℝ) : ℝ := r + z - 2 * G - P + delta

def initialM (m r z G P eta tau : ℝ) : ℝ :=
  2 * (r + z - 2 * G) - m - 2 * P + 6 * eta + tau

theorem initial_margins_sharp {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta) :
    c₁ + delta - 9 * eta - tau ≤
      initialF r z G P delta - initialM m r z G P eta tau - Q - (z - G) ∧
    c₂ + 4 * delta - 22 * eta - 3 * tau ≤
      4 * initialF r z G P delta - 3 * initialM m r z G P eta tau -
        6 * (z - G) := by
  unfold initialF initialM
  constructor <;> linarith

theorem initial_margins {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta)
    (hc : 0 ≤ min c₁ c₂) (hdelta : 0 ≤ delta) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    CanonicalMargins (initialF r z G P delta)
      (initialM m r z G P eta tau) Q (z - G) (3 * min c₁ c₂ / 4) := by
  obtain ⟨ha, hb⟩ := initial_margins_sharp (delta := delta) (tau := tau) h₁ h₂ hG hP hQ
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith

theorem initial_prefactor_identity (m r z G P : ℝ) :
    (m - 2 * (r + z - 2 * G) + P) + P +
      2 * initialF r z G P 0 = m := by
  unfold initialF
  ring

theorem initial_energy_exponent {m delta eta pi eps : ℝ}
    (hdelta : delta ≤ 3 * eta) :
    m + 3 * eta + 2 * eta + 2 * delta + pi + eps ≤
      m + 11 * eta + pi + eps := by
  linarith

theorem total_step_loss {D eta tau pi eps : ℝ}
    (h₁ : D * eta ≤ eps / 160) (h₂ : D * tau ≤ eps / 4)
    (h₃ : D * pi ≤ eps / 4) :
    D * (40 * eta + tau + pi) ≤ 3 * eps / 4 := by
  nlinarith

theorem depth_margin {c D h eta : ℝ} (heta : 0 ≤ eta) (hh : h ≤ D)
    (hbudget : D * eta ≤ c / 14) : c / 2 ≤ c - 7 * h * eta := by
  have := mul_le_mul_of_nonneg_right hh heta
  nlinarith

end SevenEighths.InverseMoment

end OAI

end Source1500

/- Original source: OAI/NumberTheory/DirichletL/Inversion/TerminalWidths.lean; sha256: 036914430149334df2c08329b0a2a8973528dd0af98cbe021268170489ee9eda -/
section Source1501
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseTerminalWidths
open ActualEisensteinCubic CompletedGauss UniqueFactorizationMonoid
open InverseMoment CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma norm_one_le (I : Ideal O) (hI : I ≠ 0) : (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem physical_residual_width (I Q : Ideal O) (hI : I ≠ 0)
    (Z M O₀ H Ck CO CH : ℝ) (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hres : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)) :
    H ≤ M - O₀ + Real.log (CH * Ck * CO) / Real.log Z := by
  have hz0 : 0 < Z := by linarith
  have hp := (div_le_iff₀ hCO).mp hpow
  have hr := (div_le_iff₀ hCH).mp hres
  have hs : Z ^ (H + O₀) ≤ (CH * Ck * CO) * Z ^ M := by
    calc
      _ = Z ^ H * Z ^ O₀ := Real.rpow_add hz0 _ _
      _ ≤ ((Ideal.absNorm (rowResidualPart I Q) : ℝ) * CH) *
          ((Ideal.absNorm (rowPowerfulPart I) : ℝ) * CO) :=
        mul_le_mul hr hp (Real.rpow_nonneg hz0.le _) (by positivity)
      _ = (CH * CO) * ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowResidualPart I Q) : ℝ)) := by ring
      _ ≤ (CH * CO) * (Ideal.absNorm I : ℝ) :=
        mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using actual_residual_norm_width I Q hI) (by positivity)
      _ ≤ (CH * CO) * (Ck * Z ^ M) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  have hl := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz0 _) hs
  rw [Real.logb_rpow hz0 (ne_of_gt hZ), Real.logb_mul (by positivity) (by positivity),
    Real.logb_rpow hz0 (ne_of_gt hZ)] at hl
  unfold Real.logb at hl
  linarith

theorem constant_log_error (C η : ℝ) (_hC : 0 < C) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → Real.log C / Real.log Z ≤ η := by
  refine ⟨max 2 (Real.exp (Real.log C / η)), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z hZ
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have he : Real.exp (Real.log C / η) ≤ Z := (le_max_right _ _).trans hZ
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  apply (div_le_iff₀ (Real.log_pos hz)).mpr
  have hh := (div_le_iff₀ hη).mp hl
  nlinarith

def activeCharge (j : ℕ) (e : Fin 3) : ℤ :=
  if j = 4 then (if e = 2 then -2 else 1) else if j = 0 then 1 else 2

theorem activeCharge_le_two (j : ℕ) (e : Fin 3) : activeCharge j e ≤ 2 := by
  unfold activeCharge
  split_ifs <;> norm_num

theorem activeCharge_le_one (j : ℕ) (e : Fin 3) (hj : j = 0 ∨ j = 4) :
    activeCharge j e ≤ 1 := by
  rcases hj with rfl | rfl
  · simp [activeCharge]
  · simp only [activeCharge, ite_true]
    split_ifs <;> norm_num

theorem reflectionLocalCost_eq_charge (q : ℝ) (_hq : 0 < q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e = q ^ (activeCharge j e : ℝ) := by
  unfold reflectionLocalCost activeCharge
  split_ifs <;> norm_num [Real.rpow_neg, Real.rpow_two]

theorem surviving_local_piece (P : Ideal O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (j : ℕ) (e : Fin 3) (n b : O)
    (hne : reflectedLocalPiece P hg j e n b ≠ 0) :
    (j ≠ 4 → e = 0) ∧ (j = 4 → e = 1 → n ∈ P) ∧
      (j = 4 → e = 2 → n ∉ P ∧ b ∈ P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hj
    by_contra he
    exact hne (by simp [reflectedLocalPiece, hj, he])
  · intro hj he
    by_contra hn
    exact hne (by simp [reflectedLocalPiece, exceptionalPiece, hj, he, hn])
  · intro hj he
    by_contra hn
    exact hne (by simp [reflectedLocalPiece, exceptionalPiece, hj, he, hn])

def normWidth (Z : ℝ) (I : Ideal O) : ℝ := Real.logb Z (Ideal.absNorm I : ℝ)

def reflectionWidth {ι : Type*} [Fintype ι] (Z : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * normWidth Z (∏ i, P i) - normWidth Z (reflectionExtractedDivisor P j e 1) -
    normWidth Z (reflectionExtractedDivisor P j e 0) -
      4 * normWidth Z (reflectionExtractedDivisor P j e 2)

theorem reflectionConductorCost_pos {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    0 < reflectionConductorCost P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost
  positivity

theorem logb_reflectionConductorCost {ι : Type*} [Fintype ι]
    (Z : ℝ) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    Real.logb Z (reflectionConductorCost P j e) = reflectionWidth Z P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost reflectionWidth normWidth
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (hd 1).ne' (hd 0).ne', Real.logb_pow, Real.logb_pow]
  norm_num
  ring

theorem reflection_charge_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z : ℝ) (hZ : 1 < Z) :
    2 * normWidth Z (rowResidualPart I (B * F * R)) +
      reflectionWidth Z P (fun i => completedLocalExponent I F (P i)) e ≤
      normWidth Z B + 2 * normWidth Z I - normWidth Z (rowPowerfulPart I) +
        normWidth Z F + normWidth Z R := by
  have hi := actual_ideal_norm_pos I hI
  have hf := actual_ideal_norm_pos F hF
  have hb := actual_ideal_norm_pos B hB
  have hr := actual_ideal_norm_pos R hR
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hx := actual_ideal_norm_pos (rowResidualPart I (B * F * R))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) (B * F * R))
  have hc := reflectionConductorCost_pos P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e
  have hh := Real.logb_le_logb_of_le hZ (mul_pos (sq_pos_of_pos hx) hc)
    (actual_common_width_charge_label_puncture I F R B hI hF hR hB P hcop hpool hres e)
  rw [Real.logb_mul (by positivity) hc.ne', Real.logb_pow,
    logb_reflectionConductorCost Z P (fun i => NeZero.ne (P i)),
    Real.logb_mul (by positivity) hr.ne', Real.logb_mul (by positivity) hf.ne',
    Real.logb_mul hb.ne' (by positivity), Real.logb_div (by positivity) hp.ne',
    Real.logb_pow] at hh
  unfold normWidth
  norm_num at hh ⊢
  linarith

theorem normWidth_upper (I : Ideal O) (hI : I ≠ 0) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : (Ideal.absNorm I : ℝ) ≤ C * Z ^ E) :
    normWidth Z I ≤ E + Real.logb Z C := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (actual_ideal_norm_pos I hI) h
  rw [Real.logb_mul hC.ne' (by positivity), Real.logb_rpow hz0 (ne_of_gt hZ)] at hh
  unfold normWidth
  linarith

theorem normWidth_lower (I : Ideal O) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : Z ^ E / C ≤ (Ideal.absNorm I : ℝ)) :
    E - Real.logb Z C ≤ normWidth Z I := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (div_pos (Real.rpow_pos_of_pos hz0 E) hC) h
  rwa [Real.logb_div (by positivity) hC.ne', Real.logb_rpow hz0 (ne_of_gt hZ)] at hh

def terminalDualWidth {ι : Type*} [Fintype ι] (Z H za Nstar : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * H + 2 * normWidth Z (∏ i, P i) + 2 * za - Nstar -
    normWidth Z (reflectionExtractedDivisor P j e 1) -
      3 * normWidth Z (reflectionExtractedDivisor P j e 2)

def widthConstant (B : Ideal O) (Ck CO CH Cf : ℝ) : ℝ :=
  CH ^ 2 * (Ideal.absNorm B : ℝ) * Ck ^ 2 * CO * Cf

theorem logb_widthConstant (Z : ℝ) (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH) (hf : 0 < Cf) :
    Real.logb Z (widthConstant B Ck CO CH Cf) =
      2 * Real.logb Z CH + normWidth Z B + 2 * Real.logb Z Ck +
        Real.logb Z CO + Real.logb Z Cf := by
  have hb := actual_ideal_norm_pos B hB
  unfold widthConstant normWidth
  rw [Real.logb_mul (by positivity) hf.ne', Real.logb_mul (by positivity) ho.ne',
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) hb.ne',
    Real.logb_pow, Real.logb_pow]
  norm_num

theorem terminal_common_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0) -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  have hb := reflection_charge_width I F B R hI hF hB hR P hcop hpool hres e Z hZ
  have h₁ := normWidth_upper I hI Z Ck M hZ hCk hk
  have h₂ := normWidth_lower (rowPowerfulPart I) Z CO O₀ hZ hCO hpow
  have h₃ := normWidth_lower (rowResidualPart I (B * F * R)) Z CH H hZ hCH hrow
  have h₄ := normWidth_upper F hF Z Cf V hZ hCf hf
  change _ ≤ 2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
    Real.logb Z (widthConstant B Ck CO CH Cf)
  rw [logb_widthConstant Z B hB Ck CO CH Cf hCk hCO hCH hCf]
  unfold terminalDualWidth reflectionWidth at *
  linarith

theorem normWidth_nonneg (Z : ℝ) (hZ : 1 < Z) (I : Ideal O) (hI : I ≠ 0) :
    0 ≤ normWidth Z I := Real.logb_nonneg hZ (norm_one_le I hI)

theorem rpow_reflectionWidth {ι : Type*} [Fintype ι]
    (Z : ℝ) (hZ : 1 < Z) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0)
    (j : ι → ℕ) (e : ι → Fin 3) :
    Z ^ reflectionWidth Z P j e = reflectionConductorCost P j e := by
  rw [← logb_reflectionConductorCost Z P hP j e]
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ) (reflectionConductorCost_pos P hP j e)

theorem width_error_threshold (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η := by
  have hb := actual_ideal_norm_pos B hB
  obtain ⟨a, ha, h₁⟩ := constant_log_error (CH * Ck * CO) η (by positivity) hη
  obtain ⟨b, hb', h₂⟩ := constant_log_error (widthConstant B Ck CO CH Cf) η
    (by unfold widthConstant; positivity) hη
  exact ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ =>
    ⟨h₁ Z ((le_max_left _ _).trans hZ), h₂ Z ((le_max_right _ _).trans hZ)⟩⟩

theorem canonical_active_pool (I Q Q₀ : Ideal O) (hI : I ≠ 0) (hQ : Q ≠ 0)
    (e : FreeReflection.pool I Q Q₀ → Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    P.val ∣ I * Q ∧ ¬ P.val ∣ rowResidualPart I Q ∧
      ConcretePrimeRowBridge.goodLambda ∉ P.val ∧
        ringChar (O ⧸ P.val) ≠ 2 ∧ ¬ Q₀ ≤ P.val := by
  let p : FreeReflection.pool I Q Q₀ :=
    ⟨P.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩
  exact ⟨FreeReflection.pool_divides I Q Q₀ hI hQ p,
    FreeReflection.pool_nonresidual I Q Q₀ p, FreeReflection.pool_good I Q Q₀ p,
    FreeReflection.pool_odd I Q Q₀ p, FreeReflection.pool_free I Q Q₀ p⟩

theorem surviving_inactive_exponent (I F Q Q₀ : Ideal O)
    (e : FreeReflection.pool I Q Q₀ → Fin 6)
    (hne : FreeReflection.reflectionSixInactiveWeight I F Q Q₀ e ≠ 0)
    (P : FreeReflection.pool I Q Q₀) (hP : ¬ reflectionSixActive (e P)) :
    completedLocalExponent I F P.val = 0 := by
  have he : reflectionSixValid e := by
    by_contra he
    exact hne (by simp [FreeReflection.reflectionSixInactiveWeight, he])
  have hp : FreeReflection.reflectionInactiveStratumWeight I F Q Q₀ (reflectionSixSupport e) ≠ 0 := by
    simpa only [FreeReflection.reflectionSixInactiveWeight, ite_eq_left he] using hne
  rw [FreeReflection.reflectionInactiveStratumWeight_formula] at hp
  have hm : P ∈ (Finset.univ : Finset (FreeReflection.pool I Q Q₀)) \ reflectionSixSupport e := by
    simp [reflectionSixSupport, hP]
  have ht := (Finset.prod_ne_zero_iff.mp hp) P hm
  by_contra hj
  exact ht (by simp [hj])

theorem surviving_reflected_branch {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
    (I F : Ideal O) (e : ι → Fin 3) (n b : O)
    (hne : reflectedBranch P hg (fun i => completedLocalExponent I F (P i)) e n b ≠ 0) :
    ∀ i, (completedLocalExponent I F (P i) ≠ 4 → e i = 0) ∧
      (completedLocalExponent I F (P i) = 4 → e i = 1 → n ∈ P i) ∧
      (completedLocalExponent I F (P i) = 4 → e i = 2 → n ∉ P i ∧ b ∈ P i) := by
  intro i
  apply surviving_local_piece (P i) (hg i) _ (e i) n b
  exact (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)

theorem canonical_terminal_common_width
    (I F B R Q₀ : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6)
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    let P := fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val
    let j := fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e =>
      completedLocalExponent I F p.val
    let l := FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e
    terminalDualWidth Z H za Nstar P j l -
      normWidth Z (reflectionExtractedDivisor P j l 0) -
      normWidth Z (reflectionExtractedDivisor P j l 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  let Q := B * F * R
  have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hB hF) hR
  let A := FreeReflection.reflectionActivePool I Q Q₀ e
  let : ∀ p : A, p.val.IsMaximal := fun p => FreeReflection.pool_maximal I Q Q₀
    ⟨p.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e p.property⟩
  have hcop : Pairwise (fun p q : A => IsCoprime p.val q.val) := by
    intro p q hpq
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
  exact terminal_common_width I F B R hI hF hB hR (fun p : A => p.val) hcop
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).1)
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).2.1)
    (FreeReflection.reflectionActiveLabel I Q Q₀ e)
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf

def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))

def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2

theorem hybridSaving_nonneg {v za : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ za) :
    0 ≤ hybridSaving v za := by unfold hybridSaving; positivity

theorem hybridSaving_half {v za : ℝ} (hv : 0 ≤ v)
    (hu : hybridSaving v za ≠ za) : v / 2 ≤ hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v + za) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v + za) / 3) with hz | hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      linarith

theorem terminal_width_from_invariant
    {F₀ N V M Q z₀ c O₀ za Nstar hhat d η Td S₀ B₀ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hF : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hwidth : Td - S₀ - B₀ ≤ 2 * M - O₀ + Q + V - Nstar + 2 * za + η) :
    Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η := by
  have hi := hinv.1
  linarith

theorem reflected_row_bound {O₀ H S₀ B₀ za v ell el Td M η : ℝ}
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hrow : v + ell ≤ H) (hH : H ≤ M - O₀ + η) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ M + za + 5 * η / 3 := by
  have hu := hybridSaving_nonneg hv hz
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_left hrow]
  linarith

theorem reflected_column_full_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hl : 0 ≤ ell) (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za = za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) + 5 * η / 3 + τ := by
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol, hu]
  linarith

theorem reflected_column_partial_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za ≠ za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) / 2 + za + 7 * η / 6 + τ / 2 := by
  have hu' := hybridSaving_half hv hu
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol]
  linarith

theorem reflected_terminal_cases
    {F₀ M Q z₀ c O₀ H S₀ B₀ za v ell el Td d η τ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η) :
    (v + ell ≤ H → reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - c + 5 * η / 3) ∧
    (H ≤ v + ell → hybridSaving v za = za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - 2 * c + 5 * d + 17 * η / 3 + τ) ∧
    (H ≤ v + ell → hybridSaving v za ≠ za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        F₀ - M / 4 - 3 * c / 4 + 5 * d / 2 + 19 * η / 6 + τ / 2) := by
  obtain ⟨hi₁, hi₂⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro hrow
    have hb := reflected_row_bound hO hS hB hz hv hl he hrow hH (Td := Td)
    linarith
  · intro hcol hu
    have hb := reflected_column_full_bound hl he hcol hu hret (O₀ := O₀) (S₀ := S₀) (B₀ := B₀)
    linarith
  · intro hcol hu
    have hb := reflected_column_partial_bound hS hB hv hl he hcol hu hret (O₀ := O₀)
    linarith

theorem reflected_terminal_saving
    {F₀ M Q z₀ c cstar O₀ H S₀ B₀ za v ell el Td d η τ π : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td + π ≤ F₀ - cstar / 4 := by
  obtain ⟨hr, hf, hp⟩ := reflected_terminal_cases hinv hQ hO hS hB hz hzcap hv hl he hret hH hT
  rcases le_total (v + ell) H with h | h
  · have := hr h
    linarith
  · by_cases hu : hybridSaving v za = za
    · have := hf h hu
      linarith
    · have := hp h hu
      linarith

def ramifiedWidth (Z : ℝ) (m : ℕ) : ℝ := ((m : ℝ) - 4) * Real.logb Z 3

theorem rpow_ramifiedWidth (Z : ℝ) (hZ : 1 < Z) (m : ℕ) :
    Z ^ ramifiedWidth Z m = (3 : ℝ) ^ ((m : ℝ) - 4) := by
  unfold ramifiedWidth
  rw [mul_comm, Real.rpow_mul (by linarith : 0 ≤ Z),
    Real.rpow_logb (by linarith : 0 < Z) (ne_of_gt hZ) (by norm_num : (0 : ℝ) < 3)]

theorem fractionalThetaPoint_norm_width (Z : ℝ) (hZ : 1 < Z)
    (u : Oˣ) (m : ℕ) (n b : O) :
    ‖fractionalThetaPoint u m n b‖ ^ 2 =
      Z ^ ramifiedWidth Z m * ‖ConcreteTraceCRT.eisEmbedding n‖ ^ 2 *
        (‖ConcreteTraceCRT.eisEmbedding b‖ ^ 2) ^ 3 := by
  rw [rpow_ramifiedWidth Z hZ]
  exact fractionalThetaPoint_norm_sq u m n b

theorem ramified_width_threshold (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨Z₀, hZ₀, hlog⟩ := constant_log_error ((3 : ℝ) ^ (4 : ℕ)) η (by norm_num) hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ m
  have hz := hZ₀.trans_le hZ
  have hl := hlog Z hZ
  change Real.logb Z ((3 : ℝ) ^ (4 : ℕ)) ≤ η at hl
  rw [Real.logb_pow] at hl
  have hn : 0 ≤ Real.logb Z 3 := Real.logb_nonneg hz (by norm_num)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold ramifiedWidth
  norm_num at hl
  nlinarith

theorem terminal_error_threshold (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η ∧
      ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨a, ha, h₁⟩ := width_error_threshold B hB Ck CO CH Cf η hk ho hh hf hη
  obtain ⟨b, hb, h₂⟩ := ramified_width_threshold η hη
  refine ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ => ?_⟩
  exact ⟨(h₁ Z ((le_max_left _ _).trans hZ)).1,
    (h₁ Z ((le_max_left _ _).trans hZ)).2, h₂ Z ((le_max_right _ _).trans hZ)⟩

theorem actual_terminal_saving {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤
      terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
      za v ell el (terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e) + π ≤
        F₀ - cstar / 4 := by
  have hH := physical_residual_width I (B * F * R) hI Z M O₀ H Ck CO CH hZ hCk hCO hCH hk hpow hrow
  have hT := terminal_common_width I F B R hI hF hB hR P hcop hpool hres e
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf
  have hT' := terminal_width_from_invariant (O₀ := O₀) (za := za) (η := η)
    (Td := terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e)
    (S₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
    (B₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
    hinv hF₀ hscale hV hh (hT.trans (by linarith))
  exact reflected_terminal_saving hinv (normWidth_nonneg Z hZ R hR) hM hO
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    hz hzcap hv hl he hret (by linarith) hT' hc hmargin hd hη hτ hπ

theorem residual_admissible_of_fixed_bad (I F B R : Ideal O)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ B) :
    Admissible (rowResidualPart I (B * F * R)) := by
  apply rowResidualPart_admissible
  intro P hP
  exact (hbad P hP).trans ((dvd_mul_right B F).trans (dvd_mul_right (B * F) R))

def canonicalDualWidth (I F B R Q₀ : Ideal O)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6)
    (Z H za Nstar : ℝ) : ℝ :=
  terminalDualWidth Z H za Nstar
    (fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val)
    (fun p => completedLocalExponent I F p.val)
    (FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e)

def canonicalExtractedWidth (I F B R Q₀ : Ideal O)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6) (Z : ℝ) (a : Fin 3) : ℝ :=
  normWidth Z (reflectionExtractedDivisor
    (fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val)
    (fun p => completedLocalExponent I F p.val)
    (FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e) a)

theorem canonical_terminal_saving
    (I F B R Q₀ : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ B)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6) (m : ℕ)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (herr : Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η ∧
      ∀ a : ℕ, -η ≤ ramifiedWidth Z a)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (hret : v + 3 * ell + ramifiedWidth Z m ≤ canonicalDualWidth I F B R Q₀ e Z H za Nstar + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    Admissible (rowResidualPart I (B * F * R)) ∧
    reflectedExponent O₀ H (canonicalExtractedWidth I F B R Q₀ e Z 0)
      (canonicalExtractedWidth I F B R Q₀ e Z 2) za v ell (ramifiedWidth Z m)
      (canonicalDualWidth I F B R Q₀ e Z H za Nstar) + π ≤ F₀ - cstar / 4 := by
  refine ⟨residual_admissible_of_fixed_bad I F B R hbad, ?_⟩
  let Q := B * F * R
  have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hB hF) hR
  let A := FreeReflection.reflectionActivePool I Q Q₀ e
  let : ∀ p : A, p.val.IsMaximal := fun p => FreeReflection.pool_maximal I Q Q₀
    ⟨p.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e p.property⟩
  have hcop : Pairwise (fun p q : A => IsCoprime p.val q.val) := by
    intro p q hpq
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
  exact actual_terminal_saving I F B R hI hF hB hR (fun p : A => p.val) hcop
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).1)
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).2.1)
    (FreeReflection.reflectionActiveLabel I Q Q₀ e)
    Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell (ramifiedWidth Z m) d η τ π Ck CO CH Cf
    hZ hCk hCO hCH hCf hk hpow hrow hf herr.1 herr.2.1 hinv hF₀ hscale hV hh hM hO hz hzcap
    hv hl (herr.2.2 m) hret hc hmargin hd hη hτ hπ

end SevenEighths.InverseTerminalWidths

end

end OAI

end Source1501

/- Original source: OAI/NumberTheory/DirichletL/Inversion/KernelSourceUniform.lean; sha256: 61f1b6a4ca9e5d5000557221035f410f3ff61d6ebb1b25da6e45c284a5c09dc2 -/
section Source1502
namespace OAI

namespace SevenEighths.InverseKernelSourceUniform

open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory LocalLogFourier
noncomputable section

def smallScalar (R : ℝ) : ℝ := min 1 (R ^ (1/4 : ℝ))

lemma smallScalar_pos {R : ℝ} (hR : 0 < R) : 0 < smallScalar R :=
  lt_min zero_lt_one (Real.rpow_pos_of_pos hR _)

def canonicalDensity (U : ℝ → ℂ) (V : 𝓢(ℝ, ℂ)) (R t : ℝ) : ℂ :=
  ((smallScalar R : ℝ) : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * CubicReflectionKernel.paperKernel V (R * Real.exp s))) t

theorem paperKernel_window_source_bound (a b : ℝ) (ha : 0 < a) (K : ℕ) (L : ℝ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R → ∀ j ≤ K, ∀ s : ℝ, |s| ≤ L →
      ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R * Real.exp s)‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * smallScalar R := by
  choose orders c hc hb using fun j : Fin (K+1) =>
    CubicReflectionKernel.paperKernel_euler_source_power_decay a b ha 0 j.val
  let S := Finset.univ.biUnion orders
  let D := (∑ j : Fin (K+1), c j) + 1
  let E := (Real.exp L) ^ (1/4 : ℝ)
  have hD : 0 < D := by
    have hh := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc j).le)
    dsimp only [D]
    linarith
  have hE : 0 < E := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcD (j : Fin (K+1)) : c j ≤ D := by
    have hh := Finset.single_le_sum
      (fun q (_ : q ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc q).le) (Finset.mem_univ j)
    dsimp only [D]
    linarith
  refine ⟨S, D*(1+E), by positivity, ?_⟩
  intro V hV R hR j hj s hs
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let q : Fin (K+1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
  have hsource : c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V ≤ D*Q := by
    have hsub : orders q ⊆ S := Finset.subset_biUnion_of_mem orders (Finset.mem_univ q)
    exact mul_le_mul (hcD q) (Seminorm.le_def.mp (Finset.sup_mono hsub) V)
      (by positivity) hD.le
  have hsmall := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).1
  have hlarge := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).2
  have hsmall' : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤
      D*(1+E)*Q * R^(1/4 : ℝ) := by
    have he : (Real.exp s)^(1/4 : ℝ) ≤ E :=
      Real.rpow_le_rpow (by positivity) (Real.exp_le_exp.mpr ((le_abs_self s).trans hs)) (by norm_num)
    rw [Real.mul_rpow hR.le (Real.exp_pos _).le] at hsmall
    calc
      _ ≤ (c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V) *
          (R^(1/4 : ℝ) * (Real.exp s)^(1/4 : ℝ)) := hsmall
      _ ≤ (D*Q) * (R^(1/4 : ℝ) * E) := mul_le_mul hsource
          (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hR.le _)) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hQ (Real.rpow_nonneg hR.le (1/4 : ℝ))]
  have hlarge' : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤ D*(1+E)*Q := by
    have hh : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤ D*Q := by
      apply (le_trans ?_ hsource)
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hlarge
    exact hh.trans (by nlinarith [mul_nonneg (mul_nonneg hD.le hE.le) hQ])
  change _ ≤ D*(1+E)*Q * min 1 (R^(1/4 : ℝ))
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ D*(1+E)*Q), mul_one]
  exact le_min hlarge' hsmall'

private theorem localized_source_seminorm
    (V F : ℝ → ℂ) (R L CW CF : ℝ) (n k : ℕ)
    (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (hF : ContDiffOn ℝ ∞ F (Set.Ioi 0)) (hR : 0 < R)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s, ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s, (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) → |s| ≤ L)
    (hEuler : ∀ i ≤ n, ∀ s, |s| ≤ L → ‖eulerDeriv F i (R * Real.exp s)‖ ≤ CF) :
    (SchwartzMap.seminorm ℝ k n) (positiveLogProfile V F R hVc hVs hF hR) ≤
      L ^ k * derivativeConstant n CW CF := by
  let g := positiveLogProfile V F R hVc hVs hF hR
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have hG : ContDiff ℝ ∞ G := by
    apply hF.comp_contDiff (by fun_prop)
    intro z
    exact mul_pos hR (Real.exp_pos _)
  have hgeq : (g : ℝ → ℂ) = fun z => V z * G z := by
    funext z
    exact positiveLogProfile_apply V F R z hVc hVs hF hR
  have hD : 0 ≤ derivativeConstant n CW CF := derivativeConstant_nonneg _ _ _ hCW hCF
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (mul_nonneg (pow_nonneg hL _) hD)
  intro s
  have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by simp)
  by_cases hs : ∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0
  · have hwindow' := hwindow s hs
    have hraw : ‖iteratedDeriv n g s‖ ≤ derivativeConstant n CW CF := by
      rw [hgeq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      apply hprod.trans
      unfold derivativeConstant
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hGi : ‖iteratedFDeriv ℝ (n - i) G s‖ ≤ CF := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, show (G : ℝ → ℂ) = fun z => F (R * Real.exp z) from rfl,
          iteratedDeriv_log_eq_euler]
        exact hEuler (n - i) (Nat.sub_le _ _) s hwindow'
      gcongr
      exact hVderiv i hi' s
    have hsk : ‖s‖ ^ k ≤ L ^ k := by simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg s) hwindow' k
    exact mul_le_mul hsk hraw (norm_nonneg _) (pow_nonneg hL _)
  · have hz (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i V s‖ = 0 := by
      by_contra hne
      exact hs ⟨i, hi, hne⟩
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
        ‖iteratedFDeriv ℝ (n - i) G s‖) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      ring
    have hgzero : ‖iteratedDeriv n g s‖ = 0 := by
      rw [hgeq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact le_antisymm (hprod.trans_eq hsum) (norm_nonneg _)
    rw [hgzero, mul_zero]
    positivity

theorem source_uniform_separation {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (J : ℕ) :
    ∃ (U : ℝ → ℂ) (S : Finset (ℕ × ℕ)) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * CubicReflectionKernel.paperKernel V
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * FourierBridge.logPhase t (slope i * y i)) *
            canonicalDensity U V R t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V) := by
  let T := ∑ i, |slope i| * M i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i))
  let K := J + (volume : Measure ℝ).integrablePower
  let L := T+1
  have hL : 0 ≤ L := by dsimp only [L]; linarith
  obtain ⟨U, CW, hUc, hUs, hUone, hCW, hUderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  obtain ⟨S, CF, hCF, hkernel⟩ := paperKernel_window_source_bound a b ha K L
  let P0 := momentConstant K L CW CF
  let B0 := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P0 +
    FourierBridge.coefficientMomentBound J P0)
  let B1 := FourierBridge.fourierPointBound J P0
  have hP0 : 0 ≤ P0 := momentConstant_nonneg K L CW CF hL hCW hCF.le
  have hB0 : 0 ≤ B0 := mul_nonneg (by positivity) (add_nonneg
    (FourierBridge.coefficientMomentBound_nonneg 0 P0 hP0)
    (FourierBridge.coefficientMomentBound_nonneg J P0 hP0))
  have hB1 : 0 ≤ B1 := FourierBridge.fourierPointBound_nonneg J P0 hP0
  refine ⟨U, S, B0+B1, add_nonneg hB0 hB1, hUc, hUs, ?_⟩
  intro V hV R hR
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let m := smallScalar R
  have hm : 0 < m := smallScalar_pos hR
  have hF := CubicReflectionKernel.paperKernel_compact_source_smooth V a b ha hV (V.smooth ⊤)
  let g := positiveLogProfile U (CubicReflectionKernel.paperKernel V) R hUc hUs hF hR
  let B : 𝓢(ℝ, ℂ) := ((m : ℂ)⁻¹) • (𝓕 g)
  have hcan (t : ℝ) : B t = canonicalDensity U V R t := by
    rfl
  have hnorm (t : ℝ) : ‖B t‖ = m⁻¹ * ‖(𝓕 g) t‖ := by
    simp only [B, smul_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  have hP : 0 ≤ P0*Q := mul_nonneg hP0 hQ
  have hsource (n : ℕ) (hn : n ≤ K) : m⁻¹ *
      ((SchwartzMap.seminorm ℝ 0 n) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P0*Q := by
    have hsemi (k : ℕ) : (SchwartzMap.seminorm ℝ k n) g ≤
        L^k * derivativeConstant n CW (CF*Q*m) := by
      apply localized_source_seminorm U (CubicReflectionKernel.paperKernel V)
        R L CW (CF*Q*m) n k hUc hUs hF hR hL hCW (by positivity)
      · intro i hi
        exact hUderiv i (hi.trans hn)
      · intro s hs
        exact (hwindow s (by obtain ⟨i, hi, hz⟩ := hs; exact ⟨i, hi.trans hn, hz⟩)).2.2
      · intro i hi s hs
        exact hkernel V hV R hR i (hi.trans hn) s hs
    have hd : derivativeConstant n CW (CF*Q*m) = derivativeConstant n CW CF * Q * m := by
      simp only [derivativeConstant, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hs : (SchwartzMap.seminorm ℝ 0 n) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g ≤ (P0*Q)*m := by
      calc
        _ ≤ L^0 * derivativeConstant n CW (CF*Q*m) +
            L^(volume : Measure ℝ).integrablePower * derivativeConstant n CW (CF*Q*m) :=
          add_le_add (hsemi 0) (hsemi _)
        _ = ((1+L^(volume : Measure ℝ).integrablePower)*derivativeConstant n CW CF)*Q*m := by
          rw [hd]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (momentConstant_dominates K n L CW CF hL hCW hCF.le hn) hQ) hm.le
    exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hm.le)).trans_eq (by field_simp)
  have hB0Q : (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 (P0*Q) +
      FourierBridge.coefficientMomentBound J (P0*Q)) = B0*Q := by
    dsimp only [B0]
    unfold FourierBridge.coefficientMomentBound
    ring
  have hB1Q : FourierBridge.fourierPointBound J (P0*Q) = B1*Q := by
    dsimp only [B1]
    unfold FourierBridge.fourierPointBound FourierBridge.fourierSeminormBound
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ i, windows i (y i)) ≠ 0 → U (∑ i, slope i*y i) = 1 :=
      FourierBridge.coupled_cutoff_active windows U slope y M hwindows (by simpa [T] using hUone)
    have hsep := coupled_positive_log_separation windows (CubicReflectionKernel.paperKernel V)
      U R slope y hUc hUs hF hR hactive
    rw [hsep, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [← hcan]
    dsimp only [B]
    simp only [smul_apply, smul_eq_mul]
    have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
    change _ = (m : ℂ)*_
    field_simp
    rfl
  · simp_rw [← hcan, hnorm]
    exact AnalyticBridge.schwartz_fourier_one_plus_integrable g J |>.const_mul m⁻¹ |>.congr
      (Filter.Eventually.of_forall (fun t => by dsimp only; ring))
  · simp_rw [← hcan, hnorm]
    have hh := FourierBridge.uniform_fourier_one_plus_moment g J m⁻¹ (P0*Q)
      (inv_nonneg.mpr hm.le) hP hsource
    rw [hB0Q] at hh
    have he : (∫ t : ℝ, (1+‖t‖)^J * (m⁻¹ * ‖(𝓕 g) t‖)) =
        m⁻¹ * ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 g) t‖ := by
      simp_rw [← mul_assoc, mul_comm ((1+‖_‖)^J) m⁻¹, mul_assoc]
      rw [integral_const_mul]
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB1) hQ)
  · intro t
    rw [← hcan, hnorm]
    have hh := FourierBridge.uniform_fourier_pointwise g J m⁻¹ (P0*Q)
      (inv_nonneg.mpr hm.le) hP (fun i hi => hsource i (hi.trans (by dsimp only [K]; omega))) t
    rw [hB1Q] at hh
    have he : (1+‖t‖)^J*(m⁻¹*‖(𝓕 g) t‖) = m⁻¹*(1+‖t‖)^J*‖(𝓕 g) t‖ := by ring
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB0) hQ)

def twistedDensity (U W : ℝ → ℂ) (θ R t : ℝ) : ℂ :=
  (smallScalar R : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * CubicReflectionKernel.paperKernel
      (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s))) t

theorem normTwistedSource_uniform_separation {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (W : ℝ → ℂ) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ → ℂ) (n : ℕ) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * CubicReflectionKernel.paperKernel
          (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * FourierBridge.logPhase t (slope i * y i)) *
            twistedDensity U W θ R t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖) ≤ C * (1 + ‖θ‖)^n ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖ ≤ C * (1 + ‖θ‖)^n) := by
  obtain ⟨U, orders, C, hC, hUc, hUs, hsep⟩ :=
    source_uniform_separation a b ha windows slope M hM hwindows J
  let V := CompletedGauss.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    CompletedGauss.Vstar_support W a b hsupp
  obtain ⟨G, hG, hbound⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  obtain ⟨n, D, hD, hpoly⟩ := hbound orders
  refine ⟨U, n, C*D, mul_nonneg hC hD.le, hUc, hUs, ?_⟩
  intro θ R hR
  have hcan : canonicalDensity U (G θ) R = twistedDensity U W θ R := by
    unfold canonicalDensity twistedDensity
    rw [hlink θ]
  obtain ⟨heq, hi, hm, hp⟩ := hsep (G θ) (hGs θ) R hR
  rw [hcan] at heq hi hm hp
  rw [hlink θ] at heq
  have hb : C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G θ) ≤
      C*D * (1+‖θ‖)^n :=
    (mul_le_mul_of_nonneg_left (hpoly θ) hC).trans_eq (by ring)
  exact ⟨heq, hi, hm.trans hb, fun t => (hp t).trans hb⟩

theorem fourier_joint_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (fun p : α × ℝ => (𝓕 (f p.1)) p.2) := by
  simp_rw [Real.fourier_eq']
  apply StronglyMeasurable.integral_prod_right
  have he : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(-2 * Real.pi * inner ℝ p.1 p.2) : ℂ) * Complex.I)) := by
    fun_prop
  exact (he.stronglyMeasurable.comp_measurable
    (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).smul
    (hf.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem paperKernel_joint_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (a b : ℝ) (ha : 0 < a) (V : α → 𝓢(ℝ, ℂ))
    (hV : ∀ θ, Function.support (V θ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hf : StronglyMeasurable (fun p : α × ℝ => V p.1 (Real.exp p.2))) :
    StronglyMeasurable (fun p : α × Set.Ioi (0 : ℝ) =>
      CubicReflectionKernel.paperKernel (V p.1) p.2) := by
  let f : α → ℝ → ℂ := fun θ s => V θ (Real.exp s)
  let g : α → ℝ → ℂ := fun θ u => CubicReflectionKernel.axisMultiplier u * (𝓕 (f θ)) u
  have hfF := fourier_joint_stronglyMeasurable f hf
  have hg : StronglyMeasurable (Function.uncurry g) :=
    (CubicReflectionKernel.axisMultiplier_continuous.stronglyMeasurable.comp_measurable
      measurable_snd).mul hfF
  have hgF := fourier_joint_stronglyMeasurable g hg
  have harg : Measurable (fun p : α × Set.Ioi (0 : ℝ) =>
      (p.1, Real.log (CubicReflectionKernel.paperScale * (p.2 : ℝ)))) :=
    measurable_fst.prodMk (Real.measurable_log.comp
      (measurable_const.mul (measurable_subtype_coe.comp measurable_snd)))
  convert hgF.comp_measurable harg using 1
  funext p
  let L := CubicReflectionKernel.logSchwartz (V p.1) a b ha (hV p.1) ((V p.1).smooth ⊤)
  exact CubicReflectionKernel.paperKernel_eq_logFourier (V p.1) L
    (fun _ => rfl) p.2 p.2.property

private theorem twistedDensity_measurable_of_profile
    (U W : ℝ → ℂ) (R : ℝ)
    (hprofile : StronglyMeasurable (fun p : ℝ × ℝ =>
      U p.2 * CubicReflectionKernel.paperKernel
        (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W p.1)) (R * Real.exp p.2))) :
    StronglyMeasurable (fun p : ℝ × ℝ => twistedDensity U W p.1 R p.2) := by
  unfold twistedDensity
  exact stronglyMeasurable_const.mul (fourier_joint_stronglyMeasurable
    (fun θ s => U s * CubicReflectionKernel.paperKernel
      (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s)) hprofile)

private theorem exists_measurable_twisted_source
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ G : ℝ → 𝓢(ℝ, ℂ),
      (∀ θ, (G θ : ℝ → ℂ) = CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) ∧
      (∀ θ, Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b) ∧
      StronglyMeasurable (fun p : ℝ × ℝ => G p.1 (Real.exp p.2)) := by
  let V := CompletedGauss.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    CompletedGauss.Vstar_support W a b hsupp
  obtain ⟨G, hG, _⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  have hf : StronglyMeasurable (fun p : ℝ × ℝ => G p.1 (Real.exp p.2)) := by
    simp_rw [hG, CompletedHeight.normTwistedSource, Real.log_exp]
    apply Continuous.stronglyMeasurable
    unfold FourierBridge.logPhase
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(2*Real.pi*p.1*p.2) : ℂ)*Complex.I))).mul
      (V.continuous.comp (Real.continuous_exp.comp continuous_snd))
  exact ⟨G, hlink, hGs, hf⟩

theorem twistedDensity_joint_stronglyMeasurable
    (U W : ℝ → ℂ) (hU : Measurable U)
    (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (R : ℝ) (hR : 0 < R) :
    StronglyMeasurable (fun p : ℝ × ℝ => twistedDensity U W p.1 R p.2) := by
  obtain ⟨G, hlink, hGs, hf⟩ := exists_measurable_twisted_source W a b ha hsupp hW
  have hkernel := paperKernel_joint_stronglyMeasurable a b ha G hGs hf
  have harg : Measurable (fun p : ℝ × ℝ =>
      (p.1, (⟨R * Real.exp p.2, mul_pos hR (Real.exp_pos _)⟩ : Set.Ioi (0 : ℝ)))) :=
    measurable_fst.prodMk ((measurable_const.mul (Real.measurable_exp.comp measurable_snd)).subtype_mk)
  have hcomposed := hkernel.comp_measurable harg
  change StronglyMeasurable (fun p : ℝ × ℝ =>
    CubicReflectionKernel.paperKernel (G p.1) (R * Real.exp p.2)) at hcomposed
  have hprofile : StronglyMeasurable (fun p : ℝ × ℝ =>
      U p.2 * CubicReflectionKernel.paperKernel
        (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W p.1)) (R*Real.exp p.2)) := by
    have hprofileG : StronglyMeasurable (fun p : ℝ × ℝ =>
        U p.2 * CubicReflectionKernel.paperKernel (G p.1) (R * Real.exp p.2)) :=
      (hU.stronglyMeasurable.comp_measurable measurable_snd).mul
        hcomposed
    convert hprofileG using 1
    exact funext (fun p => congrArg
      (fun V : ℝ → ℂ => U p.2 * CubicReflectionKernel.paperKernel V (R * Real.exp p.2))
      (hlink p.1).symm)
  exact twistedDensity_measurable_of_profile U W R hprofile

end
end SevenEighths.InverseKernelSourceUniform

end OAI

end Source1502

/- Original source: OAI/NumberTheory/DirichletL/Inversion/ReflectedNormalization.lean; sha256: 5c4190a479edbb701a423948de5ad0b0b290cb7e3c8fdf4486c37dd430aefef2 -/
section Source1503
namespace OAI

namespace SevenEighths.InverseReflectedNormalization
open InverseTerminalWidths
noncomputable section

def outsideScalar (Z v ell el S₀ B₀ Td : ℝ) : ℝ :=
  Z ^ (-v/2-ell-el/3-(S₀+B₀)/2) *
    InverseKernelSourceUniform.smallScalar (Z ^ (v+3*ell+el-Td))

theorem smallScalar_rpow {Z : ℝ} (hZ : 1 ≤ Z) (d : ℝ) :
    InverseKernelSourceUniform.smallScalar (Z ^ (-d)) = Z ^ (-max 0 d/4) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold InverseKernelSourceUniform.smallScalar
  rw [← Real.rpow_mul hZ0.le]
  by_cases hd : 0 ≤ d
  · rw [max_eq_right hd, min_eq_right]
    · congr 1; ring
    · calc
        Z ^ (-d * (1/4:ℝ)) ≤ Z ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
        _ = 1 := Real.rpow_zero _
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [max_eq_left hd', neg_zero, zero_div, Real.rpow_zero, min_eq_left]
    calc
      1 = Z ^ (0:ℝ) := (Real.rpow_zero _).symm
      _ ≤ Z ^ (-d*(1/4:ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem outsideScalar_square {Z : ℝ} (hZ : 1 ≤ Z) (v ell el S₀ B₀ Td : ℝ) :
    outsideScalar Z v ell el S₀ B₀ Td ^ 2 =
      Z ^ (-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold outsideScalar
  rw [show v+3*ell+el-Td = -(Td-v-3*ell-el) by ring, smallScalar_rpow hZ,
    ← Real.rpow_add hZ0, ← Real.rpow_mul_natCast hZ0.le]
  congr 1
  ring

theorem row_shape {Z : ℝ} (hZ : 1 ≤ Z) (H v ell : ℝ) :
    Z^H + Z^v*Z^ell ≤ 2*Z^(max H (v+ell)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  rw [← Real.rpow_add hZ0]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_left H (v+ell))
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_right H (v+ell))
  linarith

theorem cubic_shape {Z : ℝ} (hZ : 1 ≤ Z) (v za : ℝ) :
    Z^v + Z^za + (Z^v*Z^za)^(2/3:ℝ) ≤ 3*Z^(v+za-hybridSaving v za) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hv : hybridSaving v za ≤ v := min_le_left _ _
  have hz : hybridSaving v za ≤ za := (min_le_right _ _).trans (min_le_left _ _)
  have ht : hybridSaving v za ≤ (v+za)/3 := (min_le_right _ _).trans (min_le_right _ _)
  rw [← Real.rpow_add hZ0, ← Real.rpow_mul hZ0.le]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (show v ≤ v+za-hybridSaving v za by linarith)
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (show za ≤ v+za-hybridSaving v za by linarith)
  have h3 := Real.rpow_le_rpow_of_exponent_le hZ (show (v+za)*(2/3:ℝ) ≤ v+za-hybridSaving v za by linarith)
  linarith

theorem reflected_exponent_identity (H v ell el S₀ B₀ Td za ε : ℝ) :
    (-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) +
      (H+v+ell+za)*ε + max H (v+ell) + ell + (v+za-hybridSaving v za) =
    reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za) := by
  unfold reflectedExponent
  ring

theorem normalized_hybrid_shape {Z : ℝ} (hZ : 1 ≤ Z)
    (H v ell el S₀ B₀ Td za ε : ℝ) :
    (outsideScalar Z v ell el S₀ B₀ Td)^2 *
      ((Z^H*Z^v*Z^ell*Z^za)^ε * (Z^H+Z^v*Z^ell)*Z^ell*
        (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ))) ≤
      6*Z^(reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hp : (Z^H*Z^v*Z^ell*Z^za)^ε = Z^((H+v+ell+za)*ε) := by
    rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0,
      ← Real.rpow_mul hZ0.le]
  have hb := mul_le_mul (row_shape hZ H v ell) (cubic_shape hZ v za)
    (by positivity : 0 ≤ Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (outsideScalar Z v ell el S₀ B₀ Td)^2 *
      (Z^H*Z^v*Z^ell*Z^za)^ε * Z^ell by positivity)
  calc
    _ ≤ (outsideScalar Z v ell el S₀ B₀ Td)^2 *
        (Z^H*Z^v*Z^ell*Z^za)^ε * Z^ell *
        ((2*Z^(max H (v+ell)))*(3*Z^(v+za-hybridSaving v za))) := by
      nlinarith only [hh]
    _ = 6*Z^(reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) := by
      rw [outsideScalar_square hZ,hp]
      calc
        _ = 6*(Z^(-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) *
          Z^((H+v+ell+za)*ε) * Z^(max H (v+ell)) * Z^ell *
          Z^(v+za-hybridSaving v za)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0,
            ← Real.rpow_add hZ0,reflected_exponent_identity]

end
end SevenEighths.InverseReflectedNormalization

end OAI

end Source1503

/- Original source: OAI/NumberTheory/DirichletL/Reflection/NormalizedEnergy.lean; sha256: 6bd4c3338098c66ac6e2a5fe6850838d5e9bc42b12c32cfe9e202b25cc3704cd -/
section Source1504
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open InverseReflectedNormalization InverseTerminalWidths MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem normalized_actual_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z H v ell el S₀ B₀ Td za : ℝ), 1 ≤ Z →
    ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      X = Z^H → extractedDualScale (frozenExtracted F jF e 1) Y = Z^v →
      extractedDualScale (frozenExtracted F jF e 2) B = Z^ell → L = Z^za →
      ‖scalar‖*frozenBranchScale F jF e = outsideScalar Z v ell el S₀ B₀ Td →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2) ≤
      (6*C)*Z^(InverseTerminalWidths.reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) *
        (∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := integrated_actual_reflected_branch_energy (Ω := Ω) (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro Z H v ell el S₀ B₀ Td za hZ X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
    hscaleX hscaleY hscaleB hscaleL hscalar
  have hh := he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  dsimp only at hh
  rw [hscaleX,hscaleY,hscaleB,hscaleL] at hh
  have hs : ‖scalar‖^2*(frozenBranchScale F jF e)^2 =
      outsideScalar Z v ell el S₀ B₀ Td ^2 := by rw [← mul_pow,hscalar]
  have heq : ‖scalar‖^2*((frozenBranchScale F jF e)^2*
      (C*(Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
        (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)))) =
      C*((outsideScalar Z v ell el S₀ B₀ Td)^2 *
        ((Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
          (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)))) := by
    calc
      _ = (‖scalar‖^2*(frozenBranchScale F jF e)^2)*
        (C*(Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
          (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ))) := by ring
      _ = _ := by rw [hs]; ring
  rw [heq] at hh
  apply hh.trans
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (normalized_hybrid_shape hZ H v ell el S₀ B₀ Td za ε) hC.le)
    (sq_nonneg (∫ t, ‖density t‖ ∂μ))
  convert hbnd using 1 ; ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1504

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Denominator.lean; sha256: 18ee2369599f649f5a0010a00b5048ef3a54f2bff497d40710035099a81f9444 -/
section Source1505
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma sqrt_extraction_identity (A B C r U V : ℝ)
    (hA : 0<A) (hB : 0<B) (hC : 0<C) (hr : 0<r) (hU : 0<U) (hV : 0<V) :
    (Real.sqrt A*Real.sqrt B/Real.sqrt C) /
      (r*Real.sqrt (A*U)*(B*V)) =
      1/(r*Real.sqrt U*V*Real.sqrt (C*B)) := by
  rw [Real.sqrt_mul hA.le,Real.sqrt_mul hC.le]
  have hsa := (Real.sqrt_pos.mpr hA).ne'
  have hsb := (Real.sqrt_pos.mpr hB).ne'
  have hsc := (Real.sqrt_pos.mpr hC).ne'
  have hsu := (Real.sqrt_pos.mpr hU).ne'
  field_simp
  nlinarith [Real.sq_sqrt hB.le]

def extractedOutsideScalar (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) : ℝ :=
  smallScalar R / (r*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
    ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B))

theorem extractedOutsideScalar_scale (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) (hr : 0<r) (hU : 0<U) (hB : 0<B) :
    extractedOutsideScalar F jF e r U B R * frozenBranchScale F jF e =
      smallScalar R / (r*Real.sqrt U*B*
        Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 0):ℝ)*
          (Ideal.absNorm (frozenExtracted F jF e 2):ℝ))) := by
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  unfold extractedOutsideScalar frozenBranchScale
  have hh := sqrt_extraction_identity _ _ _ r U B (hn 1) (hn 2) (hn 0) hr hU hB
  calc
    _ = smallScalar R * ((Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 0):ℝ))/
      (r*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
        ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B))) := by ring
    _ = _ := by rw [hh]; ring

lemma power_normalizer {Z : ℝ} (hZ : 1≤Z) (v ell el S₀ B₀ Td : ℝ) :
    smallScalar (Z^(v+3*ell+el-Td)) /
      (Z^(el/3)*Real.sqrt (Z^v)*Z^ell*Real.sqrt (Z^S₀*Z^B₀)) =
      outsideScalar Z v ell el S₀ B₀ Td := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_add hZ0,
    ← Real.rpow_mul hZ0.le,← Real.rpow_mul hZ0.le,
    ← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0]
  unfold outsideScalar
  rw [div_eq_mul_inv,← Real.rpow_neg hZ0.le]
  have he : -(el/3+v*(1/2:ℝ)+ell+(S₀+B₀)*(1/2:ℝ)) =
      -v/2-ell-el/3-(S₀+B₀)/2 := by ring
  rw [he,mul_comm]

theorem extractedOutsideScalar_log_widths (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (Z r U B R : ℝ) (hZ : 1<Z) (hr : 0<r) (hU : 0<U) (hB : 0<B) (hR : 0<R) :
    extractedOutsideScalar F jF e r U B R * frozenBranchScale F jF e =
      outsideScalar Z (Real.logb Z U) (Real.logb Z B) (3*Real.logb Z r)
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) := by
  have hz0 : 0<Z := lt_trans zero_lt_one hZ
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  rw [extractedOutsideScalar_scale F jF e r U B R hr hU hB]
  symm
  rw [← power_normalizer hZ.le]
  unfold InverseTerminalWidths.normWidth
  rw [show 3*Real.logb Z r/3=Real.logb Z r by ring,
    show Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-
      (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R)=Real.logb Z R by ring]
  rw [Real.rpow_logb hz0 (ne_of_gt hZ) hr,Real.rpow_logb hz0 (ne_of_gt hZ) hU,
    Real.rpow_logb hz0 (ne_of_gt hZ) hB,Real.rpow_logb hz0 (ne_of_gt hZ) hR,
    Real.rpow_logb hz0 (ne_of_gt hZ) (hn 0),Real.rpow_logb hz0 (ne_of_gt hZ) (hn 2)]

lemma extractedOutsideScalar_pos (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) (hr : 0<r) (hU : 0<U) (hB : 0<B) (hR : 0<R) :
    0 < extractedOutsideScalar F jF e r U B R := by
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact div_pos (smallScalar_pos hR)
    (mul_pos (mul_pos hr (Real.sqrt_pos.mpr (mul_pos (hn 1) hU))) (mul_pos (hn 2) hB))

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1505

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelGeometry.lean; sha256: 8d494a6aef9bce07d9838cda09d7050f97efbbcd7a75b90580655e22562ce00d -/
section Source1506
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma PrimeFamily.product_span {ι : Type*} [Fintype ι] (G : PrimeFamily ι) :
    Ideal.span {∏ i, G.generator i} = ∏ i, G.ideal i := by
  have hf (T : Finset ι) : Ideal.span {∏ i ∈ T, G.generator i} = ∏ i ∈ T, G.ideal i := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi,← Ideal.span_singleton_mul_span_singleton,
        G.generator_span,ih]
  exact hf Finset.univ

lemma reflected_conductor_norm {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ) =
      (Ideal.absNorm (Ideal.span {c}*(∏ i, F.ideal i)):ℝ)*
        (Ideal.absNorm K:ℝ)*(Ideal.absNorm (∏ i, S.ideal i):ℝ) := by
  rw [← Ideal.span_singleton_mul_span_singleton,PrimeFamily.product_span,F.reflected_product]
  simp only [map_mul,Nat.cast_mul]
  ring

def kernelSlope : Fin 4 → ℝ := ![-2,-2,1,3]
def kernelLogCoordinates (QK QP Qn Qb k p n b : ℝ) : Fin 4 → ℝ :=
  ![Real.log (k/QK),Real.log (p/QP),Real.log (n/Qn),Real.log (b/Qb)]
def kernelCenter (C QK QP Qn Qb : ℝ) : ℝ := C*Qn*Qb^3/(QK^2*QP^2)

lemma kernelLogCoordinates_exp (QK QP Qn Qb k p n b : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb)
    (hk : 0<k) (hp : 0<p) (hn : 0<n) (hb : 0<b) :
    Real.exp (∑ i, kernelSlope i * kernelLogCoordinates QK QP Qn Qb k p n b i) =
      (n/Qn)*(b/Qb)^3/((k/QK)^2*(p/QP)^2) := by
  simp only [kernelSlope,kernelLogCoordinates,Fin.sum_univ_succ,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,one_mul]
  rw [show -2*Real.log (k/QK)+(-2*Real.log (p/QP)+(Real.log (n/Qn)+3*Real.log (b/Qb))) =
    -(2*Real.log (k/QK)) + -(2*Real.log (p/QP)) + Real.log (n/Qn) + 3*Real.log (b/Qb) by ring]
  simp only [Real.exp_add,Real.exp_neg]
  rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,show (3:ℝ)=((3:ℕ):ℝ) by norm_num,
    Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log (div_pos hk hQK),Real.exp_log (div_pos hp hQP),
    Real.exp_log (div_pos hn hQn),Real.exp_log (div_pos hb hQb)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem actual_annular_kernel_identity (C QK QP Qn Qb k p n b : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb)
    (hk : 0<k) (hp : 0<p) (hn : 0<n) (hb : 0<b) :
    C*n*b^3/(k^2*p^2) = kernelCenter C QK QP Qn Qb *
      Real.exp (∑ i, kernelSlope i * kernelLogCoordinates QK QP Qn Qb k p n b i) := by
  rw [kernelLogCoordinates_exp _ _ _ _ _ _ _ _ hQK hQP hQn hQb hk hp hn hb]
  unfold kernelCenter
  field_simp

def fixedKernelCoefficient (X tau r : ℝ) (C D1 D2 : Ideal Eis) : ℝ :=
  X/(27*tau^2*(Ideal.absNorm C:ℝ)^2)*r^3*
    (Ideal.absNorm D1:ℝ)*(Ideal.absNorm D2:ℝ)^3

lemma source_kernel_argument_factor {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (c : Eis) (X tau r : ℝ) (D1 D2 n b : Ideal Eis) :
    (X/(27*tau^2*(Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      r^3*(Ideal.absNorm (D1*n):ℝ)*(Ideal.absNorm (D2*b):ℝ)^3 =
    fixedKernelCoefficient X tau r (Ideal.span {c}*(∏ i, F.ideal i)) D1 D2 *
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 /
      ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2) := by
  rw [reflected_conductor_norm]
  simp only [fixedKernelCoefficient,map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

theorem source_kernel_argument_annuli {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (c : Eis) (X tau r : ℝ) (D1 D2 n b : Ideal Eis)
    (hn : n≠0) (hb : b≠0) (QK QP Qn Qb : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb) :
    (X/(27*tau^2*(Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      r^3*(Ideal.absNorm (D1*n):ℝ)*(Ideal.absNorm (D2*b):ℝ)^3 =
    kernelCenter (fixedKernelCoefficient X tau r (Ideal.span {c}*(∏ i, F.ideal i)) D1 D2)
      QK QP Qn Qb * Real.exp (∑ i, kernelSlope i *
        kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
          (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i) := by
  rw [source_kernel_argument_factor]
  have hn0 (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply actual_annular_kernel_identity _ _ _ _ _ _ _ _ _ hQK hQP hQn hQb
    (hn0 K hK.1) _ (hn0 n hn) (hn0 b hb)
  apply hn0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1506

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelSeparation.lean; sha256: fe8ed3d4e305b689c8bcde896d3ee57c85a68ccb04b8bc767758ae69f6e7d4a0 -/
section Source1507
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section

def kernelCoordinateWeight (w : ℝ→ℂ) (slope Q t q : ℝ) : ℂ :=
  w (Real.log (q/Q))*logPhase t (slope*Real.log (q/Q))

def kernelDualWeight (windows : Fin 4→ℝ→ℂ) (Qn Qb t n b : ℝ) : ℂ :=
  kernelCoordinateWeight (windows 2) 1 Qn t n * kernelCoordinateWeight (windows 3) 3 Qb t b

lemma kernelCoordinateWeight_norm (w : ℝ→ℂ) (slope Q t q : ℝ) :
    ‖kernelCoordinateWeight w slope Q t q‖ = ‖w (Real.log (q/Q))‖ := by
  simp only [kernelCoordinateWeight,norm_mul,logPhase_norm,mul_one]

lemma kernelDualWeight_norm_le_one (windows : Fin 4→ℝ→ℂ)
    (hw : ∀ i y, ‖windows i y‖≤1) (Qn Qb t n b : ℝ) :
    ‖kernelDualWeight windows Qn Qb t n b‖≤1 := by
  rw [kernelDualWeight,norm_mul,kernelCoordinateWeight_norm,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ _)).trans (hw _ _)

lemma kernelCoordinateWeight_continuous (w : ℝ→ℂ) (slope Q q : ℝ) :
    Continuous (fun t => kernelCoordinateWeight w slope Q t q) :=
  (logPhase_continuous_left _).const_mul _

lemma kernel_mode_separation (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb k p n b t : ℝ) :
    (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i) *
      logPhase t (kernelSlope i*kernelLogCoordinates QK QP Qn Qb k p n b i)) =
    kernelCoordinateWeight (windows 0) (-2) QK t k *
      kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b := by
  simp only [kernelCoordinateWeight,kernelDualWeight,kernelSlope,kernelLogCoordinates,
    Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  norm_num
  ring

theorem reflected_kernel_uniform_separation (a b : ℝ) (ha : 0<a)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter C QK QP Qn Qb
      (∀ k p n q : ℝ, 0<k → 0<p → 0<n → 0<q →
        (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n q i)) *
          CubicReflectionKernel.paperKernel (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
            (C*n*q^3/(k^2*p^2)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (kernelCoordinateWeight (windows 0) (-2) QK t k *
            kernelCoordinateWeight (windows 1) (-2) QP t p *
            kernelDualWeight windows Qn Qb t n q) * twistedDensity U W θ R t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := normTwistedSource_uniform_separation
    a b ha windows kernelSlope M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  obtain ⟨he,hi,hm,hp⟩ := hsep θ _ hR
  refine ⟨?_,hi,hm,hp⟩
  intro k p n q hk hp hn hq
  rw [actual_annular_kernel_identity C QK QP Qn Qb k p n q hQK hQP hQn hQb hk hp hn hq]
  rw [he]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [kernel_mode_separation])

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1507

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelWeights.lean; sha256: 01aa099f8a8cbbc8c6beffbfeaea0708f47c61cf069d6751b27a401a467737af -/
section Source1508
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section

def reciprocalWindow (w : ℝ→ℂ) (α M : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (-α*M):ℂ)*(w y*(Real.exp (-α*y):ℂ))

lemma reciprocalWindow_norm_le_one (w : ℝ→ℂ) (α M : ℝ) (hα : 0≤α)
    (hw : ∀ y, ‖w y‖≤1) (hs : ∀ y, w y≠0 → -M≤y) (y : ℝ) :
    ‖reciprocalWindow w α M y‖≤1 := by
  by_cases hy : w y=0
  · simp [reciprocalWindow,hy]
  · have he : Real.exp (-α*M)*Real.exp (-α*y) ≤ 1 := by
      rw [← Real.exp_add,← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα (show 0≤M+y by linarith [hs y hy])]
    simp only [reciprocalWindow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-α*M)*(1*Real.exp (-α*y)) := by gcongr; exact hw y
      _ ≤ 1 := by simpa only [one_mul] using he

lemma reciprocalWindow_support (w : ℝ→ℂ) (α M y : ℝ) :
    reciprocalWindow w α M y≠0 → w y≠0 := by
  intro h hw
  apply h
  simp [reciprocalWindow,hw]

lemma reciprocalWindow_reconstruct (w : ℝ→ℂ) (α M y : ℝ) :
    w y*(Real.exp (-α*y):ℂ) =
      (Real.exp (α*M):ℂ)*reciprocalWindow w α M y := by
  unfold reciprocalWindow
  rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp

lemma reciprocal_norm_log (Q q : ℝ) (hQ : 0<Q) (hq : 0<q) :
    Real.exp (-(1/2:ℝ)*Real.log (q/Q)) = Real.sqrt Q/Real.sqrt q := by
  rw [show -(1/2:ℝ)*Real.log (q/Q) = Real.log (q/Q)*(-(1/2:ℝ)) by ring,
    ← Real.rpow_def_of_pos (div_pos hq hQ),Real.div_rpow hq.le hQ.le,
    Real.rpow_neg hq.le,Real.rpow_neg hQ.le,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow]
  field_simp

lemma reciprocal_cube_log (Q q : ℝ) (hQ : 0<Q) (hq : 0<q) :
    Real.exp (-Real.log (q/Q)) = Q/q := by
  rw [Real.exp_neg,Real.exp_log (div_pos hq hQ),inv_div]

def reciprocalKernelWindows (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) : Fin 4→ℝ→ℂ :=
  ![windows 0,windows 1,reciprocalWindow (windows 2) (1/2) (M 2),
    reciprocalWindow (windows 3) 1 (M 3)]

lemma reciprocalKernelWindows_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1)
    (hs : ∀ i y, windows i y≠0 → |y|≤M i) :
    ∀ i y, ‖reciprocalKernelWindows windows M i y‖≤1 := by
  intro i y
  fin_cases i
  · exact hw 0 y
  · exact hw 1 y
  · exact reciprocalWindow_norm_le_one _ _ _ (by norm_num) (hw 2)
      (fun y hy => (abs_le.mp (hs 2 y hy)).1) y
  · exact reciprocalWindow_norm_le_one _ _ _ (by norm_num) (hw 3)
      (fun y hy => (abs_le.mp (hs 3 y hy)).1) y

lemma reciprocalKernelWindows_support (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hs : ∀ i y, windows i y≠0 → |y|≤M i) :
    ∀ i y, reciprocalKernelWindows windows M i y≠0 → |y|≤M i := by
  intro i y hy
  fin_cases i
  · exact hs 0 y hy
  · exact hs 1 y hy
  · exact hs 2 y (reciprocalWindow_support _ _ _ _ hy)
  · exact hs 3 y (reciprocalWindow_support _ _ _ _ hy)

lemma reciprocal_window_product (windows : Fin 4→ℝ→ℂ) (M y : Fin 4→ℝ) :
    (∏ i, windows i (y i)) *
      ((Real.exp (-(1/2:ℝ)*y 2):ℂ)*(Real.exp (-y 3):ℂ)) =
    (Real.exp (M 2/2+M 3):ℂ)*(∏ i, reciprocalKernelWindows windows M i (y i)) := by
  have h2 := reciprocalWindow_reconstruct (windows 2) (1/2) (M 2) (y 2)
  have h3 := reciprocalWindow_reconstruct (windows 3) 1 (M 3) (y 3)
  have hp : (Real.exp (M 2/2+M 3):ℂ) =
      (Real.exp ((1/2:ℝ)*M 2):ℂ)*(Real.exp (1*M 3):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  rw [hp]
  simp only [reciprocalKernelWindows,Fin.prod_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  simp only [one_mul,neg_one_mul] at h3 ⊢
  change (windows 0 (y 0)*(windows 1 (y 1)*(windows 2 (y 2)*windows 3 (y 3)))) *
    ((Real.exp (-(1/2:ℝ)*y 2):ℂ)*(Real.exp (-y 3):ℂ)) =
    ((Real.exp ((1/2:ℝ)*M 2):ℂ)*(Real.exp (M 3):ℂ))*
      (windows 0 (y 0)*(windows 1 (y 1)*
        (reciprocalWindow (windows 2) (1/2) (M 2) (y 2)*
         reciprocalWindow (windows 3) 1 (M 3) (y 3))))
  calc
    _ = windows 0 (y 0)*windows 1 (y 1)*
      (windows 2 (y 2)*(Real.exp (-(1/2:ℝ)*y 2):ℂ))*
      (windows 3 (y 3)*(Real.exp (-y 3):ℂ)) := by ring
    _ = _ := by rw [h2,h3]; ring

theorem reciprocal_source_window_identity (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (QK QP Qn Qb k p n b r : ℝ) (hQn : 0<Qn) (hQb : 0<Qb)
    (hn : 0<n) (hb : 0<b) (hr : 0<r) :
    (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i)) /
      ((r*Real.sqrt n*b:ℝ):ℂ) =
    ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb):ℝ):ℂ) *
      (∏ i, reciprocalKernelWindows windows M i (kernelLogCoordinates QK QP Qn Qb k p n b i)) := by
  have hp := reciprocal_window_product windows M (kernelLogCoordinates QK QP Qn Qb k p n b)
  change (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i))*
      ((Real.exp (-(1/2:ℝ)*Real.log (n/Qn)):ℂ)*(Real.exp (-Real.log (b/Qb)):ℂ)) = _ at hp
  rw [reciprocal_norm_log Qn n hQn hn,reciprocal_cube_log Qb b hQb hb] at hp
  have he := congrArg (fun z : ℂ => z/((r*Real.sqrt Qn*Qb:ℝ):ℂ)) hp
  have hn0 := (Real.sqrt_pos.mpr hn).ne'
  have hQn0 := (Real.sqrt_pos.mpr hQn).ne'
  simp only [Complex.ofReal_mul,Complex.ofReal_div] at he ⊢
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hbC : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hQbC : (Qb:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQb.ne'
  have hnC : (Real.sqrt n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn0
  have hQnC : (Real.sqrt Qn:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQn0
  convert he using 1 <;> field_simp

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1508

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelIntegral.lean; sha256: eff61daa998b963f22d2222a53b0c7ec078e03bb543feffef2c9b2b4b6101c87 -/
section Source1509
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section

lemma reflected_density_integrable (U W : ℝ→ℂ) (hU : Measurable U)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (θ R : ℝ) (hR : 0<R) (J : ℕ)
    (hi : Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖)) :
    Integrable (twistedDensity U W θ R) := by
  have hm := (twistedDensity_joint_stronglyMeasurable U W hU a b ha hWs hW R hR).comp_measurable
    (measurable_const.prodMk measurable_id : Measurable (fun t : ℝ => (θ,t)))
  apply hi.mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg t]))

lemma kernel_mode_integrable (density : ℝ→ℂ) (hi : Integrable density)
    (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb k p n b : ℝ) :
    Integrable (fun t : ℝ => density t *
      (kernelCoordinateWeight (windows 0) (-2) QK t k *
        kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b)) := by
  have hc : Continuous (fun t : ℝ => kernelCoordinateWeight (windows 0) (-2) QK t k *
      kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b) :=
    ((kernelCoordinateWeight_continuous _ _ _ _).mul (kernelCoordinateWeight_continuous _ _ _ _)).mul
      ((kernelCoordinateWeight_continuous _ _ _ _).mul (kernelCoordinateWeight_continuous _ _ _ _))
  apply hi.mul_bdd (c := ‖windows 0 (Real.log (k/QK))‖*‖windows 1 (Real.log (p/QP))‖*
    (‖windows 2 (Real.log (n/Qn))‖*‖windows 3 (Real.log (b/Qb))‖)) hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  exact le_of_eq (by simp only [kernelDualWeight,norm_mul,kernelCoordinateWeight_norm])

theorem kernel_finite_contraction {κ : Type*} (source : Finset κ) (coeff value : κ→ℂ)
    (density : ℝ→ℂ) (hi : Integrable density) (scalar : ℂ)
    (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ) (k p n b : κ→ℝ)
    (he : ∀ j ∈ source, value j = scalar*∫ t : ℝ,
      (kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j))*density t) :
    (∑ j ∈ source, coeff j*value j) = scalar*∫ t : ℝ, density t*
      ∑ j ∈ source, coeff j*(kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j)) := by
  have hint (j : κ) : Integrable (fun t : ℝ => density t*
      (coeff j*(kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j)))) := by
    convert (kernel_mode_integrable density hi windows QK QP Qn Qb (k j) (p j) (n j) (b j)).const_mul (coeff j) using 1
    funext t
    ring
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum source (fun j _ => hint j),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  rw [← mul_assoc,mul_comm (coeff j) scalar,mul_assoc]
  apply congrArg (fun z : ℂ => scalar*z)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; ring)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1509

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelSource.lean; sha256: ee287429f1f161640909574538355738a42e557cfd8aef4c86829868b0400580 -/
section Source1510
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section
universe u

theorem reflected_finite_source_uniform
    (a b : ℝ) (ha : 0<a) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb r : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb → 0<r →
      let R := kernelCenter C QK QP Qn Qb
      (∀ {κ : Type u} (source : Finset κ) (coeff : κ→ℂ) (k p n q : κ→ℝ),
        (∀ j ∈ source, 0<k j ∧ 0<p j ∧ 0<n j ∧ 0<q j) →
        (∑ j ∈ source, coeff j *
          ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (k j) (p j) (n j) (q j) i)) /
            ((r*Real.sqrt (n j)*q j:ℝ):ℂ) *
            CubicReflectionKernel.paperKernel (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
              (C*n j*(q j)^3/((k j)^2*(p j)^2)))) =
        ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            ∑ j ∈ source, coeff j *
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (k j)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (p j)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (n j) (q j))) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_kernel_uniform_separation
    a b ha (reciprocalKernelWindows windows M) M hM
      (reciprocalKernelWindows_support windows M hwindows) W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb r hC hQK hQP hQn hQb hr
  obtain ⟨he,hi,hm,hp⟩ := hsep θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  have hdi := reflected_density_integrable U W hUs.continuous.measurable
    a b ha hWsupport hW θ _ hR J hi
  refine ⟨?_,hdi,hi,hm,hp⟩
  intro κ source coeff k p n q hn
  apply kernel_finite_contraction source coeff _ _ hdi _
    (reciprocalKernelWindows windows M) QK QP Qn Qb k p n q
  intro j hj
  rw [reciprocal_source_window_identity windows M QK QP Qn Qb
    (k j) (p j) (n j) (q j) r hQn hQb (hn j hj).2.2.1 (hn j hj).2.2.2 hr]
  rw [mul_assoc,he (k j) (p j) (n j) (q j) (hn j hj).1 (hn j hj).2.1 (hn j hj).2.2.1 (hn j hj).2.2.2,
    Complex.ofReal_mul]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1510

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelActual.lean; sha256: 57c08464f359de2e4d5a4c348345837326c232a3ef779f0c072f035062873b4b -/
section Source1511
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma fixedKernelCoefficient_pos (X tau r : ℝ) (C D1 D2 : Ideal Eis)
    (hX : 0<X) (htau : 0<tau) (hr : 0<r) (hC : C≠0) (hD1 : D1≠0) (hD2 : D2≠0) :
    0<fixedKernelCoefficient X tau r C D1 D2 := by
  have hn (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hCn := hn C hC
  have h1 := hn D1 hD1
  have h2 := hn D2 hD2
  unfold fixedKernelCoefficient
  positivity

def actualKernelCoefficient (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (m : ℕ) (X : ℝ) : ℝ :=
  fixedKernelCoefficient X (sourceCuspScale s.index) (ramifiedScale 1 completedRamifiedStep m)
    (Ideal.span {c}*(∏ i, F.ideal i)) 1 1

lemma actualKernelCoefficient_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c≠0) (m : ℕ) (X : ℝ) (hX : 0<X) : 0<actualKernelCoefficient F s m X := by
  apply fixedKernelCoefficient_pos _ _ _ _ _ _ hX (sourceCuspScale_pos _)
    (ramifiedScale_pos _ _ (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _) _ one_ne_zero one_ne_zero
  apply mul_ne_zero
  · exact Ideal.span_singleton_eq_bot.not.mpr hc
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i))

theorem actual_theta_kernel_argument (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (m : ℕ) (X : ℝ) (n b : Ideal Eis) :
    (X/(27*(sourceCuspScale s.index)^2*
      (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 =
    actualKernelCoefficient F s m X*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3/
      ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2) := by
  simpa only [one_mul,actualKernelCoefficient] using source_kernel_argument_factor F K hK S c
    X (sourceCuspScale s.index) (ramifiedScale 1 completedRamifiedStep m) 1 1 n b

def actualKernelSourceTerm (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  actualMixedCoefficient F K hK S jF D s hc u m n b *
    ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
      (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
      ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
      CubicReflectionKernel.paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
        ((X/(27*(sourceCuspScale s.index)^2*
          (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3))

theorem actualKernelSourceTerm_numeric (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) :
    actualKernelSourceTerm F K hK S jF D s hc u m n b windows QK QP Qn Qb W θ X =
    actualMixedCoefficient F K hK S jF D s hc u m n b *
      ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
        (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
        CubicReflectionKernel.paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
          (actualKernelCoefficient F s m X*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3/
            ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2))) := by
  unfold actualKernelSourceTerm
  rw [actual_theta_kernel_argument]

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1511

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelActualSource.lean; sha256: 15992ec55191a036f7f6d5bc27e1d7c4a9fe0a67eea80c3295ca26287ebfe32f -/
section Source1512
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
universe u
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem actual_reflected_finite_source_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ {κ : Type u} (source : Finset κ) (weight : κ→ℂ)
        (K : κ→Ideal Eis) (hK : ∀ j, Admissible (K j)) (S : κ→PrimeFamily σ) (jF : φ→ℕ)
        (D : ∀ j, ControlledStratumArithmetic (F.reflected (K j) (hK j) (S j)).generator N a c mode)
        (n b : κ→Ideal Eis), (∀ j ∈ source, n j≠0 ∧ b j≠0) →
        (∑ j ∈ source, weight j*actualKernelSourceTerm F (K j) (hK j) (S j) jF (D j) s hc
          unit m (n j) (b j) windows QK QP Qn Qb W θ X) =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            ∑ j ∈ source, (weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))*
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm (K j):ℝ)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm (∏ i, (S j).ideal i):ℝ)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm (n j):ℝ) (Ideal.absNorm (b j):ℝ))) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_finite_source_uniform.{u}
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep θ (actualKernelCoefficient F s m X) QK QP Qn Qb
    (ramifiedScale 1 completedRamifiedStep m) (actualKernelCoefficient_pos F s hc m X hX)
    hQK hQP hQn hQb hr
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro κ source weight K hK S jF D n b hn
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpos (j : κ) (hj : j ∈ source) : (0:ℝ)<Ideal.absNorm (K j) ∧
      (0:ℝ)<Ideal.absNorm (∏ i, (S j).ideal i) ∧ (0:ℝ)<Ideal.absNorm (n j) ∧ (0:ℝ)<Ideal.absNorm (b j) :=
    ⟨hnorm _ (hK j).1,hnorm _ (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne ((S j).ideal i))),
      hnorm _ (hn j hj).1,hnorm _ (hn j hj).2⟩
  have hh := he source (fun j => weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))
    (fun j => (Ideal.absNorm (K j):ℝ)) (fun j => (Ideal.absNorm (∏ i, (S j).ideal i):ℝ))
    (fun j => (Ideal.absNorm (n j):ℝ)) (fun j => (Ideal.absNorm (b j):ℝ)) hpos
  simpa only [actualKernelSourceTerm_numeric,mul_assoc] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1512

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CoprimeSource.lean; sha256: 9a9d0966ad18dd5ce71f5df23dd809ff5104528c75dc300cbac4cc7dd12b5ffa -/
section Source1513
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

abbrev CoprimeSourceIndex (K : Ideal Eis) (Pset nset bset : Finset (Ideal Eis)) :=
  {P : Pset // IsCoprime K P.val} × (nset × bset)

instance (K : Ideal Eis) (Pset nset bset : Finset (Ideal Eis)) :
    Fintype (CoprimeSourceIndex K Pset nset bset) := inferInstanceAs
      (Fintype ({P : Pset // IsCoprime K P.val} × (nset × bset)))

theorem weightedPhysicalReflectedRow_eq_coprime_source
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (r aw : Ideal Eis→ℂ) (w : Ideal Eis→Ideal Eis→ℂ) (u : Eisˣ) (m : ℕ) :
    weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc r aw w u m =
      ∑ x : CoprimeSourceIndex K Pset nset bset,
        r K*aw x.1.val.val*w x.2.1.val x.2.2.val*
          actualMixedCoefficient F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc u m x.2.1.val x.2.2.val := by
  unfold weightedPhysicalReflectedRow CoprimeSourceIndex
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr_set {P : Pset | IsCoprime K P.val}
  · intro P hP
    simp only [Set.mem_ofPred_eq] at hP
    simp only [dite_eq_left hP]
    rw [Finset.sum_coe_sort nset (fun n : Ideal Eis => ∑ b : bset,
      r K*aw P.val*w n b.val*actualMixedCoefficient F K hK (S P.val) jF (D P hP) s hc u m n b.val)]
    apply Finset.sum_congr rfl
    intro n hn
    exact (Finset.sum_coe_sort bset (fun b : Ideal Eis =>
      r K*aw P.val*w n b*actualMixedCoefficient F K hK (S P.val) jF (D P hP) s hc u m n b)).symm
  · intro P hP
    simp only [Set.mem_ofPred_eq] at hP
    simp only [dite_eq_right hP,mul_zero,Finset.sum_const_zero]

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1513

/- Original source: OAI/NumberTheory/DirichletL/Reflection/PhysicalIntegral.lean; sha256: 84d0b9d7bb9de6e258c58920d0410d83d969f4f0b4a5e1334d575f5a1e0778ad -/
section Source1514
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def finitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

def weightedFinitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    (r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val)*actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

theorem weighted_finite_physical_row_common_measure
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := actual_reflected_finite_source_uniform
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀
  let T := CoprimeSourceIndex K Pset nset bset
  have hh := he (Finset.univ : Finset T) (fun x => r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val) (fun _ => K) (fun _ => hK)
    (fun x => S x.1.val.val) jF (fun x => D x.1.val x.1.property)
    (fun x => x.2.1.val) (fun x => x.2.2.val)
    (fun x _ => ⟨hn _ x.2.1.property,hb _ x.2.2.property⟩)
  unfold weightedFinitePhysicalKernelRow
  rw [hh]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [T]
  congr 1
  rw [weightedPhysicalReflectedRow_eq_coprime_source]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hprod x.1.val.val x.1.val.property]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1514

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SumEnergy.lean; sha256: e78644eda4911862f23e6ac77c16a37f81e27d5e0695840beb6d1ff62ed8f842 -/
section Source1515
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem summed_actual_weighted_reflected_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (Fintype.card (φ→Fin 3):ℝ) * ∑ e : φ→Fin 3,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := actual_weighted_reflected_branch_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw
  calc
    _ ≤ ∑ K ∈ rows, (Fintype.card (φ→Fin 3):ℝ)*
        ∑ e : φ→Fin 3, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      apply Finset.sum_le_sum
      intro K hK
      simpa only [Finset.card_univ] using CubicEisenstein.norm_sum_sq_le_card Finset.univ
        (fun e : φ→Fin 3 => weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K)
    _ = (Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3, ∑ K ∈ rows,
        ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he'
      exact he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
        G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1515

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SumMeasure.lean; sha256: b0d24a20f189bb8aad2a7716d32a8e7045853f87d9a90404fe4807f7d5fa089e -/
section Source1516
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem integrated_summed_actual_reflected_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2) ≤
      ‖scalar‖^2*((Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := summed_actual_weighted_reflected_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  let E : ℝ := (Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ)))
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro e he
    have hYq : 0 ≤ extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
    have hBq : 0 ≤ extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
    positivity
  let ψ : rows → Ω → ℂ := fun K t => (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)
  have hbound (t : Ω) : (∑ K, ‖ψ K t‖^2) ≤ E := by
    change (∑ K : rows, ‖(∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)‖^2) ≤ E
    rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K)‖^2)]
    exact he X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
      G0 D0 u m rows nset bset Pset S (r t) (aw t) (w t)
      hrows hrowcop hproducts hScop hSN hSchar hn hb hP (hr t) (haw t) (hw t)
  have hψM (K : rows) : AEStronglyMeasurable (ψ K) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro e he
    exact weightedReflectedBranchHybridRow_aestronglyMeasurable μ F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K.val
      (hrM K.val K.property) hawM hwM
  have hpoint (K : rows) (t : Ω) : ‖ψ K t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j t‖) (Finset.mem_univ K)).trans (hbound t)
  have hint (K : rows) : Integrable (fun t => density t*ψ K t) μ :=
    hdensity.mul_bdd (hψM K) (Filter.Eventually.of_forall (hpoint K))
  have hh := mul_le_mul_of_nonneg_left
    (common_measure_energy μ density ψ E hE hdensity.norm hint hbound) (sq_nonneg ‖scalar‖)
  have hsum : (∑ K : rows, ‖∫ t, density t*ψ K t ∂μ‖^2) =
      ∑ K ∈ rows, ‖∫ t, density t*(∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2 :=
    Finset.sum_coe_sort rows (fun K : Ideal Eis =>
      ‖∫ t, density t*(∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2)
  rw [hsum] at hh
  simp only [norm_mul,mul_pow,← Finset.mul_sum]
  simpa only [E,mul_assoc] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1516

/- Original source: OAI/NumberTheory/DirichletL/Reflection/PhysicalBranchMeasure.lean; sha256: c8c7143b3a21be8a8882d59cd500d87779e3c8c88b793ea1cf26e1a902fd9ecb -/
section Source1517
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem weighted_finite_physical_row_branch_measure
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
          (D0 : ControlledStratumArithmetic G0.generator N a c mode),
        (∀ P : Pset, IsCoprime K P.val → Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal)) →
        (∀ P hp, (D P hp).fixedFactor=D0.fixedFactor) →
        (∀ P hp u m n b, actualCuspColumn (D P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
        (∀ b ∈ bset, primaryGenerator b≠0) →
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
              (actualCuspColumn D0 s hc unit m)
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m Pset nset bset K)) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := weighted_finite_physical_row_common_measure
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀ ι _ G0 D0 hcop hκ hA hbgen
  rw [he K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact weightedPhysicalReflectedRow_eq_branches F K hK S jF Pset nset bset hprod D hcop
    G0 D0 s hc hκ hA hbgen _ _ _ unit m

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1517

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelAdmissible.lean; sha256: 085208cf422d3d7408004422a8db8427d04775a7eeea70dd051b8abda0b7c3b6 -/
section Source1518
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory FourierBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma weightedKernelCoordinate_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (i : Fin 4) (slope Q t q : ℝ) :
    ‖a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q‖≤1 := by
  rw [norm_mul,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (reciprocalKernelWindows_norm windows M hw hs i _)

lemma weightedKernelDual_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1) (hs : ∀ i y, windows i y≠0 → |y|≤M i)
    (a : ℂ) (ha : ‖a‖≤1) (Qn Qb t n b : ℝ) :
    ‖a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b‖≤1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans
    (kernelDualWeight_norm_le_one _ (reciprocalKernelWindows_norm windows M hw hs) Qn Qb t n b)

lemma weightedKernelCoordinate_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (i : Fin 4) (slope Q q : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelCoordinateWeight (reciprocalKernelWindows windows M i) slope Q t q) :=
  ((kernelCoordinateWeight_continuous _ _ _ _).const_mul a).aestronglyMeasurable

lemma weightedKernelDual_measurable (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (a : ℂ) (Qn Qb n b : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      a*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t n b) := by
  exact (((kernelCoordinateWeight_continuous _ _ _ _).mul
    (kernelCoordinateWeight_continuous _ _ _ _)).const_mul a).aestronglyMeasurable

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1518

/- Original source: OAI/NumberTheory/DirichletL/Reflection/PhysicalEnergy.lean; sha256: 1396d12023eca8b066ebc92e6d770d7e6d55624d26065c86d31262413fb2706d -/
section Source1519
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem finite_physical_source_energy
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C₀ C : ℝ), 0≤C₀ ∧ 0<C ∧
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
      let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      scalar^2*((Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨C,hC,henergy⟩ := integrated_summed_actual_reflected_energy
    (Ω := ℝ) (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode) ε hε
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsource⟩ := weighted_finite_physical_row_branch_measure
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW 0
  refine ⟨degree,C₀,C,hC₀,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
  let density := twistedDensity U W θ R
  let r := fun t K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ)
  let aw := fun t P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ)
  let w := fun t n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)
  obtain ⟨hsource',hdi,_,hl1,_⟩ := hsource F s hc u m θ T QK QP Qn Qb hT hQK hQP hQn hQb
  have hpair (K : rows) (P : Pset) (hKP : IsCoprime K.val P.val) :
      Pairwise (Function.onFun IsCoprime (F.reflected K.val (hrows K.val K.property).1 (S P.val)).ideal) := by
    apply F.reflected_pairwise _ _ _ hF
    · intro i j hij
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inr i)) ((F.sum (S P.val)).ideal (Sum.inr j))
      exact hScop P.val P.property (Sum.inr_injective.ne hij)
    · rw [hproducts P.val P.property]
      exact hKP
    · exact (hrowcop K.val K.property).1
    · intro f i
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inl f)) ((F.sum (S P.val)).ideal (Sum.inr i))
      exact hScop P.val P.property (Sum.inl_ne_inr : (Sum.inl f : φ⊕σ)≠Sum.inr i)
  have hn0 : ∀ n ∈ nset, n≠0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hb0 : ∀ b ∈ bset, b≠0 := by
    intro b hb' hbzero
    exact (hb b hb').1 (by rw [hbzero,primaryGenerator_zero])
  have hidentity (K : rows) :
      weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀ =
      (scalar:ℂ)*∫ t : ℝ, density t*∑ e : φ→Fin 3,
        weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
          (r t) (aw t) (w t) u m Pset nset bset K.val :=
    hsource' K.val (hrows K.val K.property).1 S jF Pset nset bset (D K) hproducts hn0 hb0 r₀ aw₀ w₀
      G0 D0 (hpair K) (hκ K) (hA K) (fun b hb' => (hb b hb').1)
  have hh := henergy X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S volume density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdi
    (fun K hK => weightedKernelCoordinate_measurable windows M (r₀ K) 0 (-2) QK _)
    (fun P hP => weightedKernelCoordinate_measurable windows M (aw₀ P) 1 (-2) QP _)
    (fun n hn b hb => weightedKernelDual_measurable windows M (w₀ n b) Qn Qb _ _)
    (fun t K hK => weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (hr₀ K hK) _ _ _ _ _)
    (fun t P hP => weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (haw₀ P hP) _ _ _ _ _)
    (fun t n b => weightedKernelDual_norm windows M hwindowNorm hwindows _ (hw₀ n b) _ _ _ _ _)
  have hR : 0<R := by
    have hCC := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hscalar : 0<scalar := by
    have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
    have hs := smallScalar_pos hR
    dsimp only [scalar]
    positivity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscalar] at hh
  have hl1' : (∫ t : ℝ, ‖density t‖)≤C₀*(1+‖θ‖)^degree := by
    simpa only [pow_zero,one_mul] using hl1
  have hsquare : (∫ t : ℝ, ‖density t‖)^2≤(C₀*(1+‖θ‖)^degree)^2 :=
    (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)).mpr hl1'
  simp_rw [hidentity]
  rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(scalar:ℂ)*∫ t : ℝ, density t*∑ e : φ→Fin 3,
    weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
      (r t) (aw t) (w t) u m Pset nset bset K‖^2)]
  apply hh.trans
  apply mul_le_mul_of_nonneg_left hsquare
  apply mul_nonneg (sq_nonneg _)
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro e he
  have hYq : 0≤extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
  have hBq : 0≤extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
  positivity

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1519
