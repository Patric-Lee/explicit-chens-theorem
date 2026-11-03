import NumericalHatCompact
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13BridgeAssembly

open scoped Classical BigOperators Interval
open Set Filter MeasureTheory Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open BridgeAssembly Section10Lemma1017Comparison
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem numerical_hat_upper_two {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {s : ℝ} (hs : 1 ≤ s) : H.T sign s ≤ 2 := by
  have hs0 : 0 < s := by linarith only [hs]
  have hw : weightedHat H sign s ≤ 2 := by
    cases sign with
    | plus =>
        by_cases hh : s ≤ 3
        · rw [hH.initial_plus s hs0 (by linarith only [hh])]
          norm_num
        · have hmono := weightedHat_antitoneOn_Icc_closed hH .plus
            (s := (3 : ℝ)) (M := s) (by norm_num [ErrorSign.epsilon])
          have hbound := hmono ⟨by norm_num, le_of_not_ge hh⟩ ⟨le_of_not_ge hh, le_rfl⟩ (le_of_not_ge hh)
          have hinit := hH.initial_plus 3 (by norm_num) (by norm_num)
          linarith only [hbound, hinit]
    | minus =>
        by_cases hh : s ≤ 2
        · rw [hH.initial_minus s hs0 hh]
        · have hmono := weightedHat_antitoneOn_Icc_closed hH .minus
            (s := (2 : ℝ)) (M := s) (by norm_num [ErrorSign.epsilon])
          have hbound := hmono ⟨le_rfl, le_of_not_ge hh⟩ ⟨le_of_not_ge hh, le_rfl⟩ (le_of_not_ge hh)
          rw [hH.initial_minus 2 (by norm_num) (le_refl _)] at hbound
          exact hbound
  have hT0 := (hH.positive sign s hs0).le
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs 2) hT0
  dsimp [weightedHat] at hw
  norm_num only [one_pow, one_mul] at hh
  exact hh.trans hw

noncomputable def numericalHatEta : ℝ := 1 - 1 / 25600000000

theorem numerical_hat_comparison_seed {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {s : ℝ} (hs : s ∈ Icc (3 : ℝ) 4) :
    |section13Phat H s| ≤ numericalHatEta * section13Qhat H s := by
  have hlp := numerical_hat_compact hH (m := 4) (by norm_num) .plus (by linarith only [hs.1]) hs.2
  have hlm := numerical_hat_compact hH (m := 4) (by norm_num) .minus (by linarith only [hs.1]) hs.2
  norm_num [compactHatLower] at hlp hlm
  have hup := numerical_hat_upper_two hH .plus (by linarith only [hs.1])
  have hum := numerical_hat_upper_two hH .minus (by linarith only [hs.1])
  unfold section13Phat section13Qhat numericalHatEta
  rw [abs_le]
  constructor <;> nlinarith only [hlp, hlm, hup, hum]

theorem global_comparison_from_seed {P Q : ℝ → ℝ} (h : SignedPQData P Q) {η : ℝ}
    (hη : 0 < η) (hseed : ∀ t ∈ Icc (3 : ℝ) 4, |P t| ≤ η * Q t) :
    ∀ s, 3 ≤ s → |P s| ≤ η * Q s := by
  have hcovered : ∀ n : ℕ, ∀ t ∈ Icc (3 : ℝ) (4 + n), |P t| ≤ η * Q t := by
    intro n
    induction n with
    | zero => simpa using hseed
    | succ n ih =>
        have ha : (4 : ℝ) ≤ 4 + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
        have hprev : ∀ t ∈ Icc ((4 + (n : ℝ)) - 1) (4 + n), |P t| ≤ η * Q t := by
          intro t ht
          apply ih t
          constructor
          · linarith [ht.1, Nat.cast_nonneg (α := ℝ) n]
          · exact ht.2
        have hnext := propagate_one_unit h hη ha hprev
        intro t ht
        rw [Nat.cast_succ] at ht
        by_cases hta : t ≤ 4 + (n : ℝ)
        · exact ih t ⟨ht.1, hta⟩
        · exact hnext t ⟨le_of_not_ge hta, by linarith only [ht.2]⟩
  intro s hs
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge (s - 4)
  exact hcovered n s ⟨hs, by linarith only [hn]⟩

theorem numerical_hat_comparison {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 3 ≤ s) : |section13Phat H s| ≤ numericalHatEta * section13Qhat H s := by
  have hseed : ∀ t ∈ Icc (3 : ℝ) 4,
      |clampTwo (section13Phat H) t| ≤ numericalHatEta * clampTwo (section13Qhat H) t := by
    intro t ht
    rw [clampTwo_eq (by linarith only [ht.1] : 2 ≤ t), clampTwo_eq (by linarith only [ht.1] : 2 ≤ t)]
    exact numerical_hat_comparison_seed hH.toSection13HatContract ht
  have hh := global_comparison_from_seed (section13_signedPQData hH)
    (show 0 < numericalHatEta by norm_num [numericalHatEta]) hseed s hs
  simpa only [clampTwo_eq (by linarith only [hs] : 2 ≤ s)] using hh

theorem numerical_Qhat_le_hat {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {s : ℝ} (hs : 3 ≤ s) :
    section13Qhat H s ≤ 51200000000 * H.T sign s := by
  have hc := section13_comparison_of_P_abs_le
    (show 0 ≤ numericalHatEta by norm_num [numericalHatEta])
    (show numericalHatEta < 1 by norm_num [numericalHatEta]) (numerical_hat_comparison hH hs)
  cases sign with
  | plus =>
      have hh := hc.1
      norm_num [numericalHatEta] at hh
      nlinarith only [hh]
  | minus =>
      have hh := hc.2.2.1
      norm_num [numericalHatEta] at hh
      nlinarith only [hh]

#print axioms numerical_hat_comparison
#print axioms numerical_Qhat_le_hat
end ChenEffective
