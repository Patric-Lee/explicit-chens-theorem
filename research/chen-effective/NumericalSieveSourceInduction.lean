import NumericalSieveSourceAnalytic

namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- Uniform domination of the actual finite source layers, at the exact
natural-ceiling cutoff. The only analytic input is the relative Euler-product
condition; the layer induction and all endpoint transport are proved here. -/
theorem actual_source_layer_domination {S : BoundingSieve} {ε : ℝ}
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1 / 10000) (hrelative : HasRelativeSieveProduct S ε)
    (n : ℕ) : ∀ D z : ℕ, ∀ s : ℝ,
      1 < D → s ∈ closedDomain 2 n → z = ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      suzukiSourceV S n D z ≤ suzukiVProduct S ((D : ℝ) ^ (1 / s)) * sourceLayerEnvelope n ε s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D z s hD hs hz
    have hDr : (1 : ℝ) < D := by exact_mod_cast hD
    have hs0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hs
    have hV := (suzukiVProduct_pos S ((D : ℝ) ^ (1 / s))).le
    cases n with
    | zero =>
      change 0 ≤ _
      exact mul_nonneg hV (sourceLayerEnvelope_nonneg 0 hε hs)
    | succ n =>
      cases n with
      | zero =>
        have hs1 : 1 ≤ s := by
          have hh := hs
          norm_num only [closedDomain, Set.mem_Ici, eps] at hh
          linarith
        exact actual_source_base_domination hD hs1 hε hrelative hz
      | succ m =>
        let a : ℝ := max s (2 + (eps (m + 2) : ℝ))
        let σ : ℝ := ((m + 1 : ℕ) : ℝ) + 3
        let x : ℝ := (D : ℝ) ^ (1 / s)
        let v : ℝ := (D : ℝ) ^ (1 / a)
        let w : ℝ := (D : ℝ) ^ (1 / σ)
        have hσ : 0 < σ := by dsimp [σ]; positivity
        have ha : 0 < a := hs0.trans_le (le_max_left _ _)
        have hx : 0 < x := by dsimp [x]; positivity
        have hvx : v ≤ x := rpow_one_div_mono_of_le hDr.le hs0 (le_max_left _ _)
        by_cases hσs : σ ≤ s
        · have hzero : suzukiSourceV S (m + 2) D z = 0 := by
            have hh : 3 ≤ σ := by
              have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
              dsimp [σ]; push_cast; linarith
            have hs2 : 2 ≤ s := by linarith
            have hnFloor : m + 2 ≤ ⌊s - 2⌋₊ := by
              apply Nat.le_floor
              push_cast
              dsimp [σ] at hσs
              push_cast at hσs
              linarith
            exact suzukiSourceV_eq_zero_below_natCeil_rpow S hD hs2 hz hnFloor
          rw [hzero]
          exact mul_nonneg hV (sourceLayerEnvelope_nonneg (m + 2) hε hs)
        have has : a ≤ σ := by
          apply max_le (le_of_not_ge hσs)
          have he : (eps (m + 2) : ℝ) ≤ 1 := by
            exact_mod_cast (show eps (m + 2) ≤ 1 by unfold eps; omega)
          have hσ3 : 3 ≤ σ := by
            have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
            dsimp [σ]; push_cast; linarith
          linarith
        have hw : 1 < w := one_lt_rpow hDr (one_div_pos.mpr hσ)
        have hwv : w ≤ v := rpow_one_div_mono_of_le hDr.le ha has
        have hIH : ∀ D' z' : ℕ, ∀ s' : ℝ, 1 < D' → s' ∈ closedDomain 2 (m + 1) →
            z' = ⌈(D' : ℝ) ^ (1 / s')⌉₊ →
            suzukiSourceV S (m + 1) D' z' ≤ suzukiVProduct S ((D' : ℝ) ^ (1 / s')) *
              sourceLayerEnvelope (m + 1) ε s' := ih (m + 1) (by omega)
        have hAtom := actual_source_successor_atom_bound (S := S) (n := m + 1)
          (D := D) (z := z) (x := x) (w := w) (v := v)
          (H := sourceLayerTest (m + 1) ε) (by omega) hx hz hvx
          (fun p hp => actual_source_carrier_geometry (by omega : 0 < m + 1) hD hs hp)
          (fun p hp => actual_source_inner_transport (by omega : 0 < m + 1) hD hε hs hp hIH)
          (fun p _ => sourceLayerTest_nonneg (m + 1) hε _)
        have hMiddle := sieve_relative_middle_prime_sum (S := S) (D := (D : ℝ))
          (w := w) (v := v) (z := x) (s := s) (a := a) (σ := σ)
          hDr hw hwv hvx hs0 ha has rfl rfl rfl hε
          (sourceLayerTest_continuous (m + 1) ε)
          (fun t _ => sourceLayerTest_nonneg (m + 1) hε t)
          (fun t _ u _ htu => sourceLayerTest_antitone (m + 1) hε htu)
          hrelative
        have hAnalytic := source_analytic_successor (n := m + 1) (by omega) hε hεcap hs has
        exact hAtom.trans (mul_le_mul_of_nonneg_left (hMiddle.trans hAnalytic) hV)

#print axioms actual_source_layer_domination
end ChenEffective
